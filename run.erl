-module(run).
-compile(export_all).
-export([string/1, file/1, main/1, view/1]).

print(X) -> io:format("~p~n", [X]).

%% build the project
main(["build"]) ->
	leex:file(scanner),
	yecc:file(parser);
main([Fname]) -> file(Fname);
main(["scan", Fname]) ->
	{ok, Binary} = file:read_file(Fname),
	print(scanner:string(binary_to_list(Binary))).

%% run a file name
file(Atom) when is_atom(Atom) ->
    file(atom_to_list(Atom) ++ ".abc");
file(Fname) ->
    {ok, Binary} = file:read_file(Fname),
    string(binary_to_list(Binary)).

%% my inspecting function
view(Atom) when is_atom(Atom) ->
    view(atom_to_list(Atom) ++ ".abc");
view(Fname) ->
    {ok, Binary} = file:read_file(Fname),
    view1(binary_to_list(Binary)).
view1(Code) ->
    {ok, Tree} = parser:scan_and_parse(Code),
    Tree.

%% translate the code
string(String) when is_list(String) ->
    {ok, Tree} = parser:scan_and_parse(String),
    catch ets:delete(system),
    CompDefs = [X || X <- Tree, element(1,X) == comp],
    I = lists:seq(0,length(CompDefs) - 1),
    Comps = lists:zip(I,CompDefs),

    Comp_inits = [X || X <- Tree, element(1,X) == comp_init],

    ets:new(system,[named_table]),
    ets:insert(system, {attributes, #{}}),
    [Sys] = [Y || {sys,Y} <- Tree],
    %% storing AbC components definitions into State and init
    lists:map(fun({I1,{comp,CName,[{attributes, Att_List}, {behaviour, Behaviour, Init}]}}) ->
		      ets:new(CName,[named_table]),
		      ets:insert(CName,Init),
		      lists:map(fun({def,Proc,Args,Code}) ->
					ets:insert(CName,{Proc,{proc,Args,Code}})
				end, Behaviour),

		      %% Create the attributes list from component definitions
		      %% Assinging component indexes to each attribute name
		      Acc = ets:lookup_element(system, attributes, 2),
		      Map = lists:foldl(fun(X,M) ->
					  case maps:is_key(X,M) of
					    true -> List = maps:get(X,M),
						    maps:put(X,[I1|List],M);
					    false -> maps:put(X,[I1],M)
					  end
				  end, Acc, Att_List),
		      ets:insert(system, {attributes, Map})
		      end, Comps),
    Att = ets:lookup_element(system, attributes, 2),
    Data = lists:foldl(fun({comp_init,CInit,{comp,_,Decl}=Body},Acc) ->
			ets:insert(system,{CInit,Body}),
			[Decl | Acc]
		end, [], Comp_inits),
    print(Data),
    ets:insert(system, {data, Data}),
    %% support code declaration instead of via SYS ::=
    %% FUTURE    if Sys == [] -> init(Comp_inits) ; true ->
    init(Sys,Att).

init(Code,Att) ->
    LineSep = io_lib:nl(),
    Class = "Class System is\nSignals:\n\tallowsend(i:int);\n\tbroadcast(tgt,msg,j:int);\nVars:\n\tRANDOMQUEUE;\n\treceiving:bool := false;\n\ttarget :int[];\n\tpc :int[];\n\tbound : obj[];\n\t-- attributes\n\t" ++ string:join(maps:keys(Att),";\n\t") ++ ";",
    Trans ="\nState Top Defers allowsend(i)\nTransitions:\n\tinit -> SYS { -/\n\tfor i in 0..pc.length-1 {\n\t\tself.allowsend(i);\n\t}}",
    put(token,#{}),
    Print = [Class, Trans, LineSep],
    file:write_file("foo.umc", Print, [append]),
    run_chunk(Code).

%% translate each component.
run_chunk(Code) ->
    run(Code, []).
run([], PcList) ->
    Finished = "end System;\n\n",
    LineSep = io_lib:nl(),
    Pc = build_pc_list(PcList),
    Token = get(token),
    TokenDef = if Token =/= [] ->
		       string:join(maps:keys(Token), ", ") ++ " : Token; \n\n";
		  true -> ""
	       end,
    Data = ets:lookup_element(system, data, 2),
    Temp1 = [proplists:get_keys(X) || X <- Data],

    %% Get union of the attribute set
    Atts = sets:to_list(sets:from_list(lists:umerge(Temp1))),

    %% Build the attribute environment declaration
    Decl = lists:foldr(fun(X,Sum) ->
			Array = lists:foldl(fun(Comp, Acc) ->
						     case proplists:get_value(X,Comp) of
							 undefined ->
							     ["null" | Acc];
							 Val -> [Val | Acc]
						     end
					     end, [], Data),
			      [X ++ " -> [" ++ string:join(Array, ",") ++ "]" | Sum]
		end, [], Atts),

    Object = "OO : System (" ++ string:join(Decl, ", ") ++
	if Decl == [] -> ""; true -> ", " end ++ "pc => " ++ Pc ++  ");",
    Abstraction = "Abstractions {
    Action broadcast($1,$2,$3) -> send($1,$2)
    Action received($1,$2) -> received($1,$2)\n}\n\n",
    Print = [Finished, LineSep, Object, LineSep, Abstraction, TokenDef],
    file:write_file("foo.umc", Print, [append]),
    finished;

run([{comp_call, Name, _} | Rest], PcList) ->
    {comp, CName, _Data}  = ets:lookup_element(system,Name,2),
    %% get behaviour of component, which is a process name
    Behaviour = ets:lookup_element(CName,init,2),
    State = ets:new(Name,[named_table]),
    catch ets:delete(procs_info),

    %% this table is for storing process information, helpful for process call or recursion
    %% Pcname (belong to Component),
    %% PcIndex - increasing when component spawn more processes
    %% and Pc_value - the initial value decide the action to be executed
    ets:new(procs_info,[named_table]),
    put(root,Name),
    ets:insert(State,{parents,[Name]}),
    I = length(PcList),
    % number of processes of this call, init = 1
    ets:insert(State,{num_procs,1}),
    Pcname = "pc"++"["++integer_to_list(I)++"]",
    Boundname = "bound"++"["++integer_to_list(I)++"]",
    %% main process index and counter
    %% force using Component name as process name in the begining
    Process = #{code_def => CName, parent => [], rec => {}, g_index => I, v_name => [], aware => [], update => [], b_name => Boundname, pc_name => Pcname, pc_index => 0, pc_value => 1},
    %% there is no parent in the first time
    ets:insert(State,{state,Process}),
    Print = "\n\n ---------- COMPONENT " ++ atom_to_list(Name) ++ " ------------ \n\n",
    file:write_file("foo.umc", Print, [append]),
    call(Behaviour, State),
    Pc = ets:lookup_element(State,num_procs,2),
    run(Rest, [Pc | PcList]).

%% sys calls
call({proc, _ArgNames, Code}, State) ->
    eval(Code, State, {[],1});
call(Code, State) ->
    eval(Code, State, {[],1}).

%% exp calls
call({proc, _ArgNames, Code}, State, Entry) ->
    eval(Code, State, Entry).

%% call to this function whenever there is a process call
eval({call, Name, _}, State, {_, Evalue} = Entry) ->
    M = ets:lookup_element(State, state, 2),
    #{code_def := Def, pc_name := Pcname, pc_index := I} = M,
    %%print(M),
    Code = ets:lookup_element(Def, Name, 2),
    Pc = Pcname ++ "[" ++ integer_to_list(I) ++ "]",
    P = ets:lookup_element(State,parents,2),
    %% Store information of the process
    ets:insert(procs_info, {Name, {Name, Pc, I, Evalue}}),
    %%print(Name),
    ets:insert(State,{parents,[Name | P]}),
    %% update proc_name - which is the name of the current process  that executes code
    %%ets:insert(State,{state,M#{proc_name => Name, rec => {Pc,I,Evalue}}}),
    ets:insert(State,{state,M#{proc_name => Name}}),
    call(Code, State, Entry);

eval({p_awareness,Pred,Process},State,Entry) ->
    M = ets:lookup_element(State,state,2),
    #{aware := PAware, v_name := Vars, g_index := I, b_name := Boundname, pc_index := PIndex} = M,
    Bound = Boundname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    P = build_pred(local, Pred, I, Vars, Bound),
    ets:insert(State,{state,M#{aware => [P|PAware]}}),
    %%print(P),
    eval(Process, State, Entry);

eval({p_update,Assingments,Process},State,Entry) ->
    M = ets:lookup_element(State,state,2),
    #{update := Upd, v_name := Vars, g_index := I, b_name := Boundname, pc_index := PIndex} = M,
    Bound = Boundname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    A = build_assign(Assingments, I, Vars, Bound),
    ets:insert(State,{state,M#{update => Upd ++ A}}),
    eval(Process, State, Entry);

eval({prefix, Left, {call,Name,_}=Right}, State, Entry) ->
    print("Prefix"),
    print("\n\n"),
    Parents = ets:lookup_element(State,parents,2),
    case lists:member(Name,Parents) of
	true ->
	    print("PCALL or RECURSION"),
	    Rec = ets:lookup_element(procs_info, Name, 2),
	    M = ets:lookup_element(State, state, 2),
	    ets:insert(State,{state,M#{rec => Rec}}),
	    eval(Left, State, Entry);
       false ->
	    eval(Left, State, Entry),
	    #{pc_value := Global} = ets:lookup_element(State, state, 2),
	    eval(Right, State, {[], Global})
    end;

eval({prefix, Left, Right}, State, Entry) ->
    eval(Left, State, Entry),
    #{pc_value := Global} = ets:lookup_element(State, state, 2),
    eval(Right, State, {[], Global});

eval({choice, Left, Right}, State, Entry) ->
    eval(Left, State, Entry),
    eval(Right, State, Entry);

eval({par, Left, Right}, State, {_, 1} = Entry) -> % spawn process with no prefix action is treated as a simpler case
    print("Parallel at root "),
    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),

    P2 = NumProcs,

    ets:insert(Root, {num_procs, P2+1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,parents,2),

    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State2 = ets:new(list_to_atom(Child2),[]),

    Process2 = Map#{pc_index := P2, pc_value := 1},

    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {parents, Parents}),


    eval(Left, State, Entry),
    eval(Right, State2, Entry);

eval({par, Left, Right}, State, {Parent, _Value}) ->
    print("Parallel "),
    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),
    #{pc_name := Pcname, pc_value := Global, pc_index := PIndex}  =  Map,

    P1 = NumProcs,

    P2 = P1 + 1,

    ets:insert(Root, {num_procs, P2 + 1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,parents,2),
    Child1 = atom_to_list(ParentName) ++ integer_to_list(P1),
    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State1 = ets:new(list_to_atom(Child1),[]),
    State2 = ets:new(list_to_atom(Child2),[]),

    Process1 = Map#{pc_index := P1, pc_value := 1},
    Process2 = Map#{pc_index := P2, pc_value := 1},
    ets:insert(State1, {state, Process1}),
    ets:insert(State1, {parents, Parents}),
    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {parents, Parents}),
    Entry1 = {[{Pcname, PIndex, Global} | Parent], 1},
    Entry2 = {[{Pcname, PIndex, Global} | Parent], 1},
    eval(Left, State1, Entry1),
    eval(Right, State2, Entry2);


eval({bang, {call,Name,_Args}, Time}, State, Entry) ->
    print("Bang!"),
    Current = get(Name),
    %%print(Current),
    Test = case Current of
	       undefined ->
		   put(Name,Time);
	       0 -> 0;
	      _ ->
		   put(Name, Current - 1),
		   Current - 1
	   end,
    if Test == 0 ->
	    erase(Name),
	    print("Stop Bang!"),
	    %%do not count this process
	    Root = get(root),
	    NumProcs = ets:lookup_element(Root,num_procs,2),
	    ets:insert(Root,{num_procs, NumProcs - 1}),
	    eval(nil,State,Entry);
       true ->
	    #{code_def := Def} = ets:lookup_element(State, state, 2),
	    {proc, _Args, Code} = ets:lookup_element(Def,Name,2),
	    eval(Code, State, Entry)
    end;
eval(nil, _, _) ->
    print("STOP");
eval(Act, State, Entry) ->
    create_trans(Act, State, Entry).

create_trans({output, Exps, Pred}, State, {Parent, Value}) ->
    Map = ets:lookup_element(State,state,2),
    #{update := Upd, aware := Aware, rec := Rec, g_index := SIndex, v_name := Vars, pc_name := Pcname, pc_value := Global, pc_index := PIndex, b_name := Boundname}  =  Map,

    Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n\t") ++ ";\n" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,

    Cond1 = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

    Bound = Boundname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Cname = get(root),
    Sname = atom_to_list(Cname)++".s"++integer_to_list(SIndex),

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    Guards1 = "\tallowsend(i)[receiving = false and i = " ++ integer_to_list(SIndex) ++ " and " ++  PAware  ++ Cond1 ++ "]/\n",
    SndP = build_pred(local,Pred,SIndex,Vars,Bound),
    Msg = build_outE(Exps,SIndex,Vars,Bound),
    Target = "\tfor j in 0..pc.length-1 {\n\t\tif " ++ SndP ++ " then \n\t\t\t{target[j]:=1;} else {target[j]:=0;}\n\t};\n\treceiving=true;\n",
    Output = "\tself.broadcast(target," ++ Msg ++ "," ++ integer_to_list(SIndex) ++ ");\n\t",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Actions1 = Target ++ Output ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ ";\n}\n",

    Guards2 = "\tbroadcast(tgt,msg,j)[" ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ "]/\n",
    print("DEtermine REC"),
    print(Rec),
    print(Global),
    {RecString,RecVal} = case Rec of
		    {} -> {integer_to_list(Global+2),Global+2}; % no process call or nil process
		    {SomeName, Pc, PIndex, MyVal} ->
			#{proc_name := Proc_Name} = Map,
			if SomeName == Proc_Name -> {"1",Global+1};
			   true ->  {integer_to_list(MyVal),Global+1}
			   %integer_to_list(Global+2)
			end;
		    {SomeName, Pc, PIndex, MyVal} ->
			#{proc_name := Proc_Name} = Map,
			if SomeName == Proc_Name -> {"1",Global+1};
			   true ->  {integer_to_list(MyVal),Global+1}
			   %integer_to_list(Global+2)
			end;
		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> {"1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal),Global+1}; true -> {integer_to_list(Global+2),Global+2} end
		    %%{Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> "1"; true -> integer_to_list(Global+2) end ++ ";\n\t" ++ Mypc ++ " = " ++ integer_to_list(MyVal)
		end,
    Actions2 = "\treceiving=false;\n\tself.allowsend(" ++ integer_to_list(SIndex) ++ ");\n\t"
	++ Pc ++ " = "
	++ RecString ++ ";\n}\n",
    NewMap = Map#{rec => {}, pc_value => RecVal, aware => [], update => []},
    ets:insert(State, {state, NewMap}),

    Signal = " \n ----- Send ----- \n",
    Print = [Signal, Trans, Guards1, Assigns, Actions1, Trans, Guards2, Actions2],
    file:write_file("foo.umc", Print, [append]);

create_trans({input, Pred, Vars}, State, {Parent, Value}) ->

    VIndex = lists:seq(0,length(Vars) - 1),
    Vars1 = lists:zip(Vars,VIndex),

    Map = ets:lookup_element(State,state,2),
    #{update := Upd, aware := Aware, rec := Rec, g_index := SIndex, b_name := Boundname, pc_name := Pcname, pc_value := Global, pc_index := PIndex}  =  Map,

    Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n") ++ ";\n\t" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,

    Cond = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

    Bound = Boundname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Received = "OUT.received("++ integer_to_list(SIndex) ++ ",msg);\n\t",
    Cname = get(root),
    Sname = atom_to_list(Cname)++".s"++integer_to_list(SIndex),

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    RcvP = build_pred(remote,Pred,SIndex,Vars1,Bound),

    AllowedRcv = "tgt[" ++ integer_to_list(SIndex) ++ "] = 1 and ",
    Guards = "\tbroadcast(tgt,msg,j)[" ++ AllowedRcv ++ PAware ++ RcvP ++ " and " ++ Cond ++ "]/\n\t",

    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    RecString = case Rec of
		    {} -> integer_to_list(Global+1); % no process call or nil process
		    {SomeName, Pc, PIndex, MyVal} ->
			#{proc_name := Proc_Name} = Map,
			if SomeName == Proc_Name -> "1";
			   true ->  integer_to_list(MyVal)
			   %integer_to_list(Global+2)
			end;
		    {SomeName, Pc, PIndex, MyVal} ->
			#{proc_name := Proc_Name} = Map,
			if SomeName == Proc_Name -> "1";
			   true ->  integer_to_list(MyVal)
			   %integer_to_list(Global+2)
			end;
		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> "1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal); true -> integer_to_list(Global+1) end
		end,

    %% RecString = case Rec of
    %% 		    {_, _, 0} -> integer_to_list(Global+1);
    %% 		    {Pc, _, 1} -> "1";
    %% 		    {Pc, _, _} -> integer_to_list(Global+1);
    %% 		    {Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> "1" ++ ";\n\t" ++ Mypc ++ " = " ++ integer_to_list(MyVal); true -> integer_to_list(Global+1) end
    %% 		end,
    Actions = Received ++ Bound ++ " = msg;\n\t" ++ Pc ++ " = " ++ RecString ++ ";\n}\n",
    Signal = " \n ----- Receive ----- \n",
    Print = [Signal,Trans,Guards, Assigns,Actions],
    NewMap =  Map#{rec => {}, v_name => Vars1, pc_value => Global + 1, aware => [], update => []},
    ets:insert(State, {state, NewMap}),
    file:write_file("foo.umc", Print, [append]).

%% create_trans(Act, State, {Parent, Value}) ->
%%     Map = ets:lookup_element(State,state,2),
%%     #{g_index := SIndex, pc_name := Pcname, pc_value := Global, pc_index := PIndex}  =  Map,
%%     NewMap = Map#{pc_value => Global + 1},
%%     ets:insert(State, {state, NewMap}),

%%     Cond = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

%%     Cname = get(root),
%%     Sname = atom_to_list(Cname)++".s"++integer_to_list(SIndex),

%%     Trans = "  SYS."++Sname ++ " -> " ++ Sname ++ " {",
%%     Guards = "-[" ++ Cond ++ "]/",

%%     Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
%%     Actions = "OUT." ++ atom_to_list(Act) ++ ";\n" ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ ";\n}\n",

%%     Print = [Trans,Guards,Actions],
%%     file:write_file("foo.umc", Print, [append]).

recursive_trans(State, {Parent, Value}) ->
    Map = ets:lookup_element(State,state,2),
    #{g_index := SIndex, pc_name := Pcname, pc_index := PIndex}  = Map,
    Cname = get(root),
    Sname = atom_to_list(Cname)++".s"++integer_to_list(SIndex),

    Cond = build_pc_guard({Parent, {Pcname, PIndex, Value}}),
    Trans = "  SYS." ++ Sname ++ " -> " ++ Sname ++ " {",
    Guards = "-[" ++ Cond ++ "]/",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Actions = Pc ++ " = 1;}",
    LineSep = io_lib:nl(),
    Print = [Trans,Guards,Actions, LineSep],
    file:write_file("foo.umc", Print, [append]).

build_pc_guard({[],{Pcname, Pinstance, Value}}) ->
    Pcname ++ "[" ++ integer_to_list(Pinstance) ++ "] = " ++ integer_to_list(Value);
build_pc_guard({Parent, {Pcname, P2, V2}}) ->
    build_parent(Parent) ++ " and " ++ Pcname ++ "[" ++ integer_to_list(P2) ++ "] = " ++ integer_to_list(V2).

build_parent(L) ->
    build_parent(L,[]).

build_parent([],L) ->
    string:join(L," and ");
build_parent([{Pcname,P,V}|T],L) ->
    String = Pcname ++ "[" ++ integer_to_list(P) ++ "] = " ++ integer_to_list(V),
    build_parent(T,[String|L]).


build_pc_list(L) ->
    build_pc_list(L,[]).

build_pc_list([],L) ->
    "[" ++ string:join(L,",") ++ "]";
build_pc_list([H|T],L) ->
    print("NUM PROCS: "),
    print(H),
    H1 = lists:seq(1,H),
    S = ["1" || _ <- H1],
    String = "[" ++ string:join(S, ",") ++ "]",
    build_pc_list(T,[String | L]).

%% build_sndpred(Pred,I,Vars) ->
%%     "(" ++ eval1(Pred,I,Vars) ++ ")".
%% build_rcvpred(Pred,I,Vars) ->
%%     "("++eval2(Pred,I,Vars)++")".
build_outE(Exps,SIndex, Vars, Bound) ->
    I = integer_to_list(SIndex),
    eval3(Exps, I, [],Vars,Bound).
build_pred(Type, Pred, SIndex, Vars,Bound) ->
    I = integer_to_list(SIndex),
    "("++eval1(Type, Pred, I, Vars,Bound)++")".
build_assign(Assignments, SIndex, Vars,Bound) ->
    I = integer_to_list(SIndex),
    evala(Assignments, I, [], Vars,Bound).

eval1(Type,{head,Name}, I,Vars,Bound) -> eval1(Type,Name,I,Vars,Bound) ++ ".head";
eval1(Type,{tail,Name}, I,Vars,Bound) -> eval1(Type,Name,I,Vars,Bound) ++ ".tail";
eval1(Type,{selector,List,Index}, I,Vars,Bound) -> eval1(Type,List,I,Vars,Bound) ++ "[" ++ eval1(Type,Index,I,Vars,Bound) ++ "]";
eval1(_,"true", _,_,_) -> "true";
eval1(_,"false", _,_,_) -> "false";
eval1(_,{self,Att}, I, _,_) -> Att ++ "[" ++ I ++ "]";
eval1(_,{att,Att}, _,_,_) -> Att ++ "[j]";
eval1(_,{const,C}, _,_,_) -> C;
eval1(_,{token,T}, _,_,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
eval1(local,{var,Name}, _, Vars, Bound) ->
    I1 = proplists:get_value(Name,Vars),
    Bound ++ "["++integer_to_list(I1)++"]";
eval1(remote,{var,Name}, _, Vars,_) ->
    I1 = proplists:get_value(Name,Vars),
    "msg["++integer_to_list(I1)++"]";
eval1(Type,{assign, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " := " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{eq, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " = " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{ge, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " > " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{le, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " < " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{intersect, Left, Right}, Index, Vars,Bound) ->
    eval1(Type,Left, Index, Vars,Bound) ++ " and " ++ eval1(Type,Right, Index, Vars,Bound);
eval1(Type,{union, Left, Right}, Index, Vars,Bound) ->
    eval1(Type,Left, Index, Vars,Bound) ++ " or " ++ eval1(Type,Right, Index, Vars,Bound);
eval1(Type,{negation, Right}, Index, Vars,Bound) ->
    " not " ++ eval1(Type,Right, Index, Vars,Bound).

eval3([],_,S, _,_) -> "[" ++ string:join(lists:reverse(S),",") ++ "]";
eval3([H|T], I, S, Vars,Bound) ->
    Temp = evale(H,I,Vars,Bound),
    eval3(T,I,[Temp|S], Vars,Bound).

%%%% TODO HERE BOUND? run:evale({{att,"partner"},{var,"y"}},2,[{"x",0},{"y",1}])
evale({head,Name}, I,Vars,Bound) -> evale(Name,I,Vars,Bound) ++ ".head";
evale({tail,Name}, I,Vars,Bound) -> evale(Name,I,Vars,Bound) ++ ".tail";
evale({selector,List,Index}, I,Vars,Bound) -> evale(List,I,Vars,Bound) ++ "[" ++ evale(Index,I,Vars,Bound) ++ "]";
evale({self,Att}, I,_, _) -> Att ++ "[" ++ I ++ "]";
evale({att,Att}, _,_, _) -> Att ++ "[j]";
evale({const,C}, _,_, _) -> C;
evale({token,T}, _,_, _) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
evale({var,Name}, _, Vars, Bound) ->
    I1 = proplists:get_value(Name,Vars),
    Bound ++ "[" ++ integer_to_list(I1) ++ "]".

evalp({head,Att}, I, Vars,Bound) -> evalp(Att,I,Vars,Bound) ++ ".head";
evalp({tail,Att}, I, Vars,Bound) -> evalp(Att,I,Vars,Bound) ++ ".tail";
evalp({selector,List,Index}, I,Vars,Bound) -> evalp(List,I,Vars,Bound) ++ "[" ++ evalp(Index,I,Vars,Bound) ++ "]";
evalp({self,Att}, I,_,_) -> Att ++ "[" ++ I ++ "]";
evalp({att,Att}, _,_,_) -> Att ++ "[j]";
evalp({const,C}, _,_,_) -> C;
evalp({token,T}, _,_, _) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
evalp({var,Name}, _, Vars,Bound) ->
    I1 = proplists:get_value(Name,Vars),
    Bound ++ "[" ++ integer_to_list(I1) ++ "]".

evala([],_,S,_,_) -> lists:reverse(S);
evala([H|T], I, S, Vars,Bound) ->
    Temp = eval1(local,H,I,Vars,Bound),
    evala(T,I,[Temp|S], Vars,Bound).
