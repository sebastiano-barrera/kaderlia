-module(dht).
-compile([export_all, debug_info]).


-define(BUCKET_SIZE, 5).
-define(KEYSPACE_BITS, 256).
-define(N_LOOKUP_REQUESTS, 3).
-define(LOOKUP_TIMEOUT_MS, 1000).

-record(peer_state, {node_id, routing_tbl, store, old_reqs=[]}).


hamming(A, B) ->
    true = bit_size(A) == bit_size(B),
    hamming(A, B, bit_size(A) - 1, 0).

hamming(_, _, -1, Sum) -> Sum;
hamming(A, B, Pos, Sum) ->
    case {A, B} of
        {<<_:Pos, Bit:1, _/bitstring>>,
         <<_:Pos, Bit:1, _/bitstring>>} ->
            hamming(A, B, Pos-1, Sum);
        {_,_} ->
	    hamming(A, B, Pos-1, Sum+1)
    end.

%%
%% Responses to ANY request MUST always be of the form:
%%  {SrcPid, res, ReqId, ResponseData}
%%

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


key_for(Value) -> crypto:hash(sha256, Value).

key_dist(Key, NodeId) -> hamming(Key, NodeId).

node_dist(A, B) -> node_dist(A, B, ?KEYSPACE_BITS - 1).
node_dist(A, B, Pos) ->
    case {A, B} of
	{<<_:Pos, Bit:1, _/bitstring>>,
	 <<_:Pos, Bit:1, _/bitstring>>} ->
	    node_dist(A, B, Pos-1);
	_ -> Pos+1
    end.


neighbor_dist({Id, Pid}, Target) ->
    {node_dist(Id, Target), Id, Pid}.


random_node_id() ->
    crypto:strong_rand_bytes(?KEYSPACE_BITS div 8).
random_req_id() ->
    crypto:strong_rand_bytes(32).


create_peer() ->
    Id = random_node_id(),
    ?KEYSPACE_BITS = bit_size(Id),

    %% The initial routing table is a KEYSPACE_BITS-tuple filled with
    %% empty lists.
    RoutingTbl = list_to_tuple(lists:duplicate(?KEYSPACE_BITS, [])),
    #peer_state{node_id = Id,
		routing_tbl = RoutingTbl,
		store = dict:new()}.

discover_neighbor(State, {NId, NPid}) ->
    #peer_state{routing_tbl=Tbl,
		node_id=Me} = State,
    %% io:format("~p: discovered ~p (~p)~n", [Me, NId, NPid]),
    if Me == NId -> State;
       true ->
	    Dist = node_dist(Me, NId),
	    List = [ {NId, NPid} | element(Dist, Tbl) ],
	    State#peer_state{routing_tbl=setelement(Dist, Tbl, List)}
    end.


best_k_routes(Me, Tbl, Target) ->
    MaxDist = 256, %% node_dist(Me, Target),
    best_k_routes(Me, Tbl, Target, MaxDist).

best_k_routes(_, _, _, 0) -> [];
best_k_routes(Me, Tbl, Target, Dist) ->
    List = element(Dist, Tbl),
    if length(List) >= ?BUCKET_SIZE -> List;
       true -> MoreRoutes = best_k_routes(Me, Tbl, Target, Dist-1),
	       lists:append(List, MoreRoutes)
    end.


%% TODO: Check: is it ok to use the same ReqId for all requests?

find_node(State, Target) ->
    Tbl = State#peer_state.routing_tbl,
    Peers = [ neighbor_dist(Neighbor, Target)
	      || Neighbor <- lists:flatten(tuple_to_list(Tbl)) ],
    ReqId = random_req_id(),

    {Result, State1} = find_node_loop(State, Target, ReqId, Peers, sets:new()),
    State2 = close_request(State1, ReqId),
    {Result, State2}.


%% Results is list of tuples of the form {distance to target, id, pid}
find_node_loop(State, _, _, [], _) -> {not_found, State};
find_node_loop(State, Target, ReqId, RawResults, Seen) ->
    NewState = lists:foldl(fun({_, Id, Pid}, S) ->
				   discover_neighbor(S, {Id, Pid})
			   end, State, RawResults),

    %% Remove already-queried nodes, and get the K best among the
    %% remaining ones.
    Results = lists:sublist(
		lists:sort([ R || {_, Id, _} = R <- RawResults,
				  not sets:is_element(Id, Seen) ]),
		?BUCKET_SIZE),

    %% Add peers to be queried in the 'seen' list
    NewSeen = lists:foldl(fun({_, Id, _}, Set) -> sets:add_element(Id, Set) end,
			  Seen, Results),

    %% Send the query
    lists:foreach(fun({_, _, Pid}) ->
			  Pid ! {self(), ReqId, route, Target}
		  end, Results),

    receive
	{_, res, ReqId, NewResults} ->
	    case lists:keyfind(Target, 1, NewResults) of
		false ->
		    %% Not found: keep searching
		    %% Add distance information
		    NewResults1 = Results ++
			[ neighbor_dist(N, Target) || N <- NewResults ],
		    find_node_loop(NewState, Target, ReqId, NewResults1, NewSeen);
		%% Found! Return final result
		FinalRes -> {FinalRes, NewState}
	    end
    after
	?LOOKUP_TIMEOUT_MS ->
	    find_node_loop(NewState, Target, ReqId, Results, NewSeen)
    end.



peer(#peer_state{node_id = Me} = InitState, {_, NPid}) ->
    ReqId = random_req_id(),
    NPid ! {self(), ReqId, ping, Me},
    peer_loop(InitState).

peer(InitState) -> peer_loop(InitState).


peer_loop(State) ->
    Me = State#peer_state.node_id,
    receive
	{Src, ReqId, ping, NId} ->
	    NewState = discover_neighbor(State, {NId, Src}),
	    Src ! {self(), res, ReqId, {pong, Me}},
	    peer_loop(NewState);

	{Src, res, _, {pong, NId}} ->
	    NewState = discover_neighbor(State, {NId, Src}),
	    peer_loop(NewState);

	{Src, ReqId, route, Me} ->
	    %% It's us! Publish our process id
	    %% io:format("find_node: ~20p: it's us!~n", [Me]),
	    Src ! {self(), res, ReqId, [{Me, self()}]},
	    peer_loop(State);

	{Src, ReqId, route, Target} ->
	    Tbl = State#peer_state.routing_tbl,
	    NextHops = best_k_routes(Me, Tbl, Target),
	    %% io:format("find_node: ~p~n        -> ~p:~n ~p~n", [Me, Target, NextHops]),
	    Src ! {self(), res, ReqId, NextHops},
	    peer_loop(State);

	%% TODO: Remove all of the following. They're here only for debugging
	{Src, ReqId, debug_find_node, Target} ->
	    {Result, NewState} = find_node(State, Target),
	    Src ! {self(), res, ReqId, Result},
	    peer_loop(NewState);

	{Src, ReqId, debug_inspect} ->
	    Src ! {self(), res, ReqId, State},
	    peer_loop(State);

	{Src, ReqId, debug_route, Target} ->
	    Tbl = State#peer_state.routing_tbl,
	    Routes = best_k_routes(Me, Tbl, Target),
	    Src ! {self(), res, ReqId, Routes},
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

start_linear_network(0) -> [];
start_linear_network(N) when N > 0 ->
    InitState = create_peer(),
    Id = InitState#peer_state.node_id,

    NetworkTail = start_linear_network(N-1),
    Pid = case NetworkTail of
	      [Partner | _] -> spawn(?MODULE, peer, [InitState, Partner]);
	      _ -> spawn(?MODULE, peer, [InitState])
	  end,

    [{Id, Pid} | NetworkTail].


start_random_network(N) when N >= 1 ->
    Net = lists:map(fun(_) ->
			    S = create_peer(),
			    Id = S#peer_state.node_id,
			    Pid = spawn(?MODULE, peer, [S]),
			    {Id, Pid}
		    end, lists:seq(1, N)),
    NLinks = N*N div 2,
    lists:foreach(fun(_) ->
			  {IdA, PidA} = lists:nth(rand:uniform(N), Net),
			  {_, PidB} = lists:nth(rand:uniform(N), Net),
			  ReqId = random_req_id(),
			  PidA ! {PidB, ReqId, ping, IdA}
		  end, lists:seq(1, NLinks)),
    Net.


terminate_network(Net) ->
    ReqId = random_req_id(),
    lists:foreach(fun({_, Pid}) ->
			  Pid ! {self(), ReqId, debug_terminate}
		  end, Net),
    lists:map(fun({_, Pid}) ->
		      receive {Pid, res, ReqId, Res} -> Res
		      after 2 * ?LOOKUP_TIMEOUT_MS -> timeout
		      end
	      end, Net).

test_query(Net) ->
    N = length(Net),
    {Target, _} = lists:nth(rand:uniform(N), Net),
    {SrcId, Pid} = lists:nth(rand:uniform(N), Net),
    io:format("test query: ~p~n"
	      "         -> ~p", [SrcId, Target]),
    query(Pid, [debug_find_node, Target], 1000).

query(Pid, Msg, Timeout) ->
    ReqId = random_req_id(),
    ActualMsg = list_to_tuple([self(), ReqId | Msg]),
    Pid ! ActualMsg,
    receive Res -> Res
    after Timeout -> timeout end.

run_test(NetworkSize) ->
    Net = start_random_network(NetworkSize),
    Result = test_query(Net),
    terminate_network(Net),
    Result.
