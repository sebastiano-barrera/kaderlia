-module(dht).
-compile([export_all, debug_info]).


element_or(N, Tuple, Default) ->
    if N >= 1 andalso N =< size(Tuple) -> element(N, Tuple);
       true -> Default
    end.


%% Some notes:
%%
%% === Protocol
%%   All requests MUST be of the form {self(), ReqId, Msg, Args} where
%%   ReqId is the request identifier (generated by random_node_id/0),
%%   Msg is an atom, and Args can be anything.
%%   Responses to ANY request MUST always be of the form:
%%   {SrcPid, res, ReqId, Data}.
%%

%%
%%	System parameters
%%
-define(BUCKET_SIZE, 20).
-define(KEYSPACE_BITS, 32).
-define(LOOKUP_REQS, 3).    % This is α in the paper
-define(LOOKUP_TIMEOUT_MS, 1000).


%%
%%	Keys
%%

%% hamming(A, B) ->
%%     true = bit_size(A) == bit_size(B),
%%     hamming(A, B, bit_size(A) - 1, 0).

%% hamming(_, _, -1, Sum) -> Sum;
%% hamming(A, B, Pos, Sum) ->
%%     case {A, B} of
%%         {<<_:Pos, Bit:1, _/bits>>,
%%          <<_:Pos, Bit:1, _/bits>>} ->
%%             hamming(A, B, Pos-1, Sum);
%%         {_,_} ->
%% 	    hamming(A, B, Pos-1, Sum+1)
%%     end.

%% Return the node id with distance 1 from the given Id.
adjacent_id(Id) ->
    PrefixSize = bit_size(Id) - 1,
    <<Prefix:PrefixSize/bits, LSB:1/integer>> = Id,
    <<Prefix/bits, bnot LSB:1>>.

key_for(Value) -> crypto:hash(sha256, Value).

key_distance(<<A : ?KEYSPACE_BITS/unsigned-integer>>,
	     <<B : ?KEYSPACE_BITS/unsigned-integer>>) ->
    A bxor B.

key_bucket(A, B) -> 1 + binary:longest_common_prefix([A, B]).

random_node_id() ->
    0 = ?KEYSPACE_BITS rem 8,
    crypto:strong_rand_bytes(?KEYSPACE_BITS div 8).

random_req_id() ->
    crypto:strong_rand_bytes(32).


%%
%%	Peer state
%%

-record(peer_state, {node_id, routing_tbl,
		     store = dict:new(),
		     old_reqs = []}).

%% Managing "old requests": after a request has been replied to, the
%% `close_request` function should be called with the request's id, so
%% that any later response is discarded.
discard_responses_for(ReqId, Timeout) ->
    receive {_, res, ReqId, _} -> discard_responses_for(ReqId, Timeout)
    after Timeout -> ok
    end.

discard_old_responses(State) ->
    OldReqs = State#peer_state.old_reqs,
    lists:foreach(fun(ReqId) -> discard_responses_for(ReqId, 0) end, OldReqs),
    ok.

close_request(State, ReqId) ->
    OldReqs = State#peer_state.old_reqs,
    NewState = State#peer_state{old_reqs=[ReqId | OldReqs]},
    discard_old_responses(NewState),
    NewState.

create_peer() ->
    Id = random_node_id(),
    ?KEYSPACE_BITS = bit_size(Id),

    %% The initial routing table is a KEYSPACE_BITS-tuple filled with
    %% empty lists.
    RoutingTbl = list_to_tuple(lists:duplicate(?KEYSPACE_BITS, [])),
    #peer_state{node_id = Id,
		routing_tbl = RoutingTbl}.


%%
%%	Routing table
%%

%% Add a record to the routing table
discover_neighbor(State, {NId, NPid}) ->
    case State of
	%% Don't add self
	#peer_state { node_id = NId } -> State;
	#peer_state { node_id = Me, routing_tbl = Tbl } ->
	    %% io:format("~p: discovered ~p (~p)~n", [Me, NId, NPid]),
	    Index = key_bucket(Me, NId),
	    Bucket = element(Index, Tbl),
	    NewBucket = lists:keystore(NId, 1, Bucket, {NId, NPid}),
	    State#peer_state{
	      routing_tbl = setelement(Index, Tbl, NewBucket) }
    end.

discover_neighbors(State, Peers) ->
    lists:foldl(fun(P, S) -> discover_neighbor(S, P) end, State, Peers).


%% Extract routes that satisfy the predicate Pred from routing table
%% Tbl, staring at bucket BucketIndex and progressively widening the
%% range of examined buckets until N routes (or all of them) are
%% collected.
get_n_routes(N, Tbl, BucketIndex, Pred) ->
    get_n_routes(N, Tbl, BucketIndex, BucketIndex, Pred).

get_n_routes(N, _, _, _, _) when N =< 0 -> [];
get_n_routes(_, _, Lower, Upper, _)
  when Lower < 1 andalso Upper > ?KEYSPACE_BITS ->
    [];
get_n_routes(N, Tbl, Lower, Upper, Pred) ->
    Unfiltered =
	case {Lower, Upper} of
	    {I, I} -> element_or(I, Tbl, []);
	    {L, U} -> element_or(L, Tbl, []) ++ element_or(U, Tbl, [])
	end,
    Routes = lists:filter(Pred, Unfiltered),
    Len = length(Routes),
    if Len >= N -> Routes;
       true     -> Routes ++ get_n_routes(N - Len, Tbl, Lower-1, Upper+1, Pred)
    end.


best_k_routes(K, Tbl, Me, Target) ->
    best_k_routes(K, Tbl, Me, Target, fun(_) -> true end).

best_k_routes(K, Tbl, Me, Me, Pred) ->
    FakeTarget = adjacent_id(Me),
    [ {0, Me, self()} | best_k_routes(K, Tbl, Me, FakeTarget, Pred) ];

best_k_routes(K, Tbl, Me, Target, Pred) ->
    BucketIndex = key_bucket(Me, Target),
    Routes = get_n_routes(K, Tbl, BucketIndex, Pred),
    false = lists:any(fun({Id, _}) -> Id == Me end, Routes),
    Ranked = lists:sort([ {key_distance(Id, Target), Id, Pid}
			  || {Id, Pid} <- Routes ]),
    lists:sublist(Ranked, K).


%%
%%	Node lookup
%%

%% TODO: Check: is it ok to use the same ReqId for all requests?

-record(lookup, { state, k, req_id, target,
		  best_k = gb_sets:new(),
		  queried = gb_sets:new(),
		  replied = gb_sets:new() }).

find_k_nodes(State, K, Target) ->
    ReqId = random_req_id(),

    #peer_state{routing_tbl = Tbl, node_id = Me} = State,
    InitHits = best_k_routes(?LOOKUP_REQS, Tbl, Me, Target),

    Lookup = #lookup{state = State, k = K, req_id = ReqId, target = Target},
    {Result, State1} = find_k_nodes_loop(Lookup, InitHits),

    State2 = close_request(State1, ReqId),
    {Result, State2}.

find_k_nodes_loop(Lookup, Hits) ->
    %% Hits is a list of {distance to target, id, pid}, ordered by 1st
    %% element, like the ones best_k_routes/4 returns.
    %%
    %% The lookup terminates when the list of the K nodes nearest
    %% hasn't changed and all of them have replied

    #lookup{ state = State, k = K, req_id = ReqId, target = Target,
	     best_k = OldBestK, replied = Replied,
	     queried = Queried } = Lookup,

    NewPeers = [ {Id, Pid} || {_, Id, Pid} <- Hits ],
    NewState =
	#peer_state { node_id = Me, routing_tbl = Tbl } =
	discover_neighbors(State, NewPeers),
    NewBestK = best_k_routes(K, Tbl, Me, Target),

    %% RepliesPending = [ Id || {_, Id, _} <- NewBestK,
    %% 			     not gb_sets:is_element(Id, Replied) ],
    RepliesPending = gb_sets:to_list(gb_sets:subtract(Queried, Replied)),

    if NewBestK == OldBestK andalso RepliesPending == [] ->
	    {NewBestK, NewState};
       true ->
	    %% Nodes to be queried = best α nodes not yet queried
	    QueryRoutes =
		best_k_routes(?LOOKUP_REQS, Tbl, Me, Target,
			      fun({Id, _}) ->
				      not gb_sets:is_element(Id, Queried)
			      end),

	    NewQueried =
		lists:foldl(fun({_, Id, _}, S) -> gb_sets:add(Id, S) end,
			    Queried, QueryRoutes),

	    [ Pid ! {self(), {NodeId, ReqId}, route, Target}
	      || {_, NodeId, Pid} <- QueryRoutes ],

	    receive
		{_, res, {SrcId, ReqId}, RecvRoutes} ->
		    RecvHits = [ {key_distance(Me, Id), Id, Pid}
				 || {Id, Pid} <- RecvRoutes ],
		    find_k_nodes_loop(
		      Lookup#lookup{
			state = NewState,
			best_k = NewBestK,
			queried = NewQueried,
			replied = gb_sets:add_element(SrcId, Replied) },
		      RecvHits)
	    after
		?LOOKUP_TIMEOUT_MS -> {NewBestK, NewState}
	    end
    end.

find_node(State, Target) ->
    {Results, NewState} = find_k_nodes(State, ?BUCKET_SIZE, Target),
    [ Best | _ ] = Results,
    case Best of
	{0, Target, Pid} -> {Pid, NewState};
	_ -> find_node(State, Target)
    end.


%%
%%	Entry point:  the peer's main loop
%%

peer(InitState, {_, NPid}) ->
    #peer_state{node_id = Me} = InitState,
    State = case dht:query(NPid, [route, Me], 100) of
		timeout -> InitState;
		Hits ->
		    Neighbors = [ {Id, Pid} || {_, Id, Pid} <- Hits ],
		    discover_neighbors(InitState, Neighbors)
	    end,
    peer_loop(State).

peer(InitState) -> peer_loop(InitState).


peer_loop(State) ->
    Me = State#peer_state.node_id,
    receive
	{Src, ReqId, ping, NId} ->
	    NewState = discover_neighbor(State, {NId, Src}),
	    Src ! {self(), res, ReqId, {pong, Me}},
	    peer_loop(NewState);

	{Src, res, ReqId, {pong, NId}} ->
	    NewState = discover_neighbor(State, {NId, Src}),
	    peer_loop(close_request(NewState, ReqId));

	{Src, ReqId, store, {Key, Value}} ->
	    State1 = discover_neighbor(State, Src),
	    %% TODO Discard old values? It is possible to deplete
	    %% system memory by flooding the peer with store requests
	    Store = dict:append(Key, Value, State1#peer_state.store),
	    State2 = State#peer_state{store = Store},
	    Src ! {self(), res, ReqId, ok},
	    peer_loop(State2);

	{Src, ReqId, route, Target} ->
	    Tbl = State#peer_state.routing_tbl,
	    Routes = best_k_routes(?BUCKET_SIZE, Tbl, Me, Target),
	    NextHops = [ {Id, Pid} || {_, Id, Pid} <- Routes ],
	    Src ! {self(), res, ReqId, NextHops},
	    peer_loop(State);

	%% TODO: Remove all of the following. They're here only for debugging
	{Src, ReqId, debug_find_node, Target} ->
	    {Result, NewState} = find_k_nodes(State, ?BUCKET_SIZE, Target),
	    Src ! {self(), res, ReqId, Result},
	    peer_loop(NewState);

	{Src, ReqId, debug_inspect} ->
	    Src ! {self(), res, ReqId, State},
	    peer_loop(State);

	{Src, ReqId, debug_terminate} ->
	    TermPid = whereis(terminator),
	    case Src of
		TermPid ->
		    Src ! {self(), res, ReqId, ok},
		    terminated;
		_ ->
		    Src ! {self(), res, ReqId, lol_no},
		    peer_loop(State)
	    end
    end.


%%
%%	Testing
%%

pair_discover([ {IdA, PidA} | Tail = [ {_, PidB} | _ ] ]) ->
    ReqId = random_req_id(),
    PidB ! {PidA, ReqId, ping, IdA},
    pair_discover(Tail);
pair_discover(_) -> ok.

start_linear_network(N) when N > 0 ->
    Peers = [ create_peer() || _ <- lists:seq(1, N) ],
    Network  = [ {Id, spawn(?MODULE, peer, [Peer])}
		 || #peer_state{ node_id = Id } = Peer <- Peers ],
    pair_discover(Network),
    Network.


start_random_network(N) when N >= 1 ->
    Net = lists:map(fun(_) ->
			    S = create_peer(),
			    Id = S#peer_state.node_id,
			    Pid = spawn(?MODULE, peer, [S]),
			    {Id, Pid}
		    end, lists:seq(1, N)),
    NLinks = N*N div 6,
    [ begin
	  {IdA, PidA} = lists:nth(rand:uniform(N), Net),
	  {_, PidB} = lists:nth(rand:uniform(N), Net),
	  ReqId = random_req_id(),
	  PidA ! {PidB, ReqId, ping, IdA}
      end || _ <- lists:seq(1, NLinks) ],
    Net.


terminate_network(Net) ->
    ReqId = random_req_id(),
    lists:foreach(fun({_, Pid}) ->
			  Pid ! {self(), ReqId, debug_terminate}
		  end, Net),
    lists:map(fun({_, Pid}) ->
		      receive {Pid, res, ReqId, Res} -> Res
		      after 100 -> timeout
		      end
	      end, Net).

test_query(Net) ->
    N = length(Net),
    {TIdx, SIdx} = {1, N},  %% rand:uniform(N)
    {Target, _} = lists:nth(TIdx, Net),
    {SrcId, Pid} = lists:nth(SIdx, Net),
    io:format("test query: ~p~n"
	      "         -> ~p~n", [SrcId, Target]),
    query(Pid, [debug_find_node, Target], 1000).

query(Pid, Msg, Timeout) ->
    ReqId = random_req_id(),
    ActualMsg = list_to_tuple([self(), ReqId | Msg]),
    Pid ! ActualMsg,
    receive {Pid, res, ReqId, Res} -> Res
    after Timeout -> timeout end.

run_test(NetworkSize) ->
    Net = start_random_network(NetworkSize),
    Result = test_query(Net),
    terminate_network(Net),
    Result.
