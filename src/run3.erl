%% FOR stable marriage
-module(run3).
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
file([Atom]) when is_atom(Atom) ->
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
    ets:new(system,[named_table]),
    ets:insert(system, {attributes, #{}}),

    %% component definitions
    CompDefs = [X || X <- Tree, element(1,X) == comp],
    print(CompDefs),
    %% component indexes
    I = lists:seq(0,length(CompDefs) - 1),
    Comps = lists:zip(I,CompDefs),

    %% component instantiations
    Comp_inits = [X || X <- Tree, element(1,X) == comp_init],

    %% Considering those components are declared under SYS
    Sys = [Y || {sys,Y} <- Tree],
    %% storing components behaviour definitions and inits into their own table
    Template = lists:map(fun({I1,{comp,CName,[{attributes, Att_List}, {behaviour, Behaviour, Init}]}}) ->
		      %% each component has an information table
		      ets:new(CName,[named_table]),

		      %% store the init behaviour of component definition CName
		      ets:insert(CName,Init),
		      %% store process definitions of this component definition
		      lists:map(fun({def,Proc,Args,Code}) ->
					ets:insert(CName,{Proc,{proc,Args,Code}})
				end, Behaviour),
		      %% Create the attributes list from component definitions
		      %% Assigning component indexes to each attribute name
		      Acc = ets:lookup_element(system, attributes, 2),
		      Map = lists:foldl(fun(X,M) ->
					  case maps:is_key(X,M) of
					    true -> List = maps:get(X,M),
						    maps:put(X,[I1|List],M);
					    false -> maps:put(X,[I1],M)
					  end
				  end, Acc, Att_List),
				 ets:insert(system, {attributes, Map}),
				 CName
			 end, Comps),
    %% Collect attribute environments of all compnents
    AttEnv = ets:lookup_element(system, attributes, 2),
    Data = lists:foldl(fun({comp_init,CInit,{comp,_,Decl}=Body},Acc) ->
			ets:insert(system,{CInit,Body}),
			[Decl | Acc]
		end, [], Comp_inits),
    print(AttEnv),
    print(Data),
    %% keep initialization data for attribute environments in order to output to UMC specfication
    ets:insert(system, {data, Data}),
    %% support code declaration instead of via SYS ::=
    %% FUTURE
    template(Template,AttEnv),
    case Sys of
	[] -> init(Comp_inits);
	[SYS] ->
	    init(SYS)
    end.

init(SYS) ->
    init(SYS,[]).

init([],PcList) ->
    Finished = "end System;\n\n",
    LineSep = io_lib:nl(),
    Pc = build_pc_list(PcList),
    Pchoice = build_choice_list(length(PcList)),
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
							 Val ->
							     Val2 = data_eval(Val),
							     [Val2 | Acc]
						     end
					     end, [], Data),
			      [X ++ " -> [" ++ string:join(Array, ",") ++ "]" | Sum]
		end, [], Atts),
    Token = get(token),
    TokenDef = if Token =/= #{} ->
		       string:join(maps:keys(Token), ", ") ++ " : Token; \n\n";
		  true -> ""
	       end,

    Object = "OO : System (" ++ string:join(Decl, ", ") ++
	if Decl == [] -> ""; true -> ", " end ++ "pc => " ++ Pc ++  ", my =>" ++ Pchoice ++ ", par =>" ++ Pchoice ++ ");",
    Abstraction = "Abstractions {
    State partner=$1 -> matched($1)
    State pc=$1 -> pc($1)
    State bound=$1 -> bound($1)
    Action broadcast($1,$2,$3) -> send($1,$2,$3)
    Action received($1,$2) -> received($1,$2)\n}\n\n",
    Print = [Finished, LineSep, Object, LineSep, Abstraction, TokenDef],
    file:write_file("foo.umc", Print, [append]),
    ok;
init([{comp_init,Name,_}|Rest],PcList) ->
    {comp, CName, _Data}  = ets:lookup_element(system,Name,2),
    Print = "---------- COMPONENT " ++ atom_to_list(Name) ++ " ------------ \n",
    I = length(PcList),
    Code = atom_to_list(CName)++"("++integer_to_list(I)++","++atom_to_list(Name)++")\n",
    file:write_file("foo.umc", [Print,Code], [append]),
    Pc = ets:lookup_element(CName,num_procs,2),
    init(Rest,[Pc|PcList]);
init([{comp_call,Name,_}|Rest],PcList) ->
    {comp, CName, _Data}  = ets:lookup_element(system,Name,2),
    Print = "---------- COMPONENT " ++ atom_to_list(Name) ++ " ------------ \n",
    I = length(PcList),
    Code = atom_to_list(CName)++"("++integer_to_list(I)++","++atom_to_list(Name)++")\n",
    file:write_file("foo.umc", [Print,Code], [append]),
    Pc = ets:lookup_element(CName,num_procs,2),
    init(Rest,[Pc|PcList]).

template(Code,AttEnv) ->
    LineSep = io_lib:nl(),
    Class = "Class System with niceparallelism is\nSignals:\n\tallowsend(i:int);\n\tbroadcast(tgt,msg,j:int);\nVars:\n\tRANDOMQUEUE;\n\treceiving:bool := false;\n\tpc :int[];\n\tbound : obj[];\n\tmy;\n\tpar;\n\t-- attributes\n\t" ++ string:join(maps:keys(AttEnv),";\n\t") ++ ";",
    Trans ="\nState Top Defers allowsend(i)\nTransitions:\n\tinit -> SYS { -/\n\tfor i in 0..pc.length-1 {\n\t\tself.allowsend(i);\n\t}}",
    put(token,#{}),
    Print = [Class, Trans, LineSep],
    file:write_file("foo.umc", Print, [append]),
    translate(Code).

%% finish translating, output the tail of UMC specification
translate([]) ->
    finished;
%% translate each component
%%run([{comp_call, Name, _} | Rest], PcList) ->
translate([CName|Rest]) ->
    %% From system call, gets the name of component (CName) from component instance name (Name)
    %%{comp, CName, _Data}  = ets:lookup_element(system,Name,2),
    Name = CName,
    State = Name,
    %% gets the behaviour of component, which is a process
    %% can be a process name or a process expression
    InitBehaviour = ets:lookup_element(CName,init,2),
    %%State = ets:new(Name,[named_table]),

    catch ets:delete(procs_info),
    %% this table is for storing processese information of one component, helpful for process call or recursion
    %% Pcname (belong to Component),
    %% PcIndex - increasing when component spawn more processes
    %% and Pc_value - the initial value decide the action to be executed
    ets:new(procs_info,[named_table]),
    %% root is the name of component instance
    put(root,Name),
    put(parchoice_id,undefined),
    %%ets:insert(State,{parents,[Name]}),
    ets:insert(State,{visited,[]}),


    % number of processes of this component instance, init = 1
    ets:insert(State,{num_procs,1}),
    Pcname = "pc[$1]",
    Boundname = "bound[$1]",
    %% main process index and counter
    %% force using Component name as process name in the begining

    %% Note that bound index is different from Pc index, they increase their values differently
    %% comp_index is for bound ?
    %% there is no parent in the first time
    Process = #{code_def => CName, parent => [], rec => {}, comp_index => "$1", v_name => [], aware => [], update => [], b_name => Boundname, bound_index => 0, pc_name => Pcname, pc_index => 0, pc_value => 1, next_is_nil => false, use_var => true},

    ets:insert(State,{state,Process}),
    Print = "\n\n ---------- COMPONENT TEMPLATE " ++ atom_to_list(Name) ++ " ------------ \n\n",
    Print2 = "define(" ++ atom_to_list(Name) ++ ",",
    file:write_file("foo.umc", [Print,Print2], [append]),
    %% translate the behaviour of the component here
    call(InitBehaviour, State),
    file:write_file("foo.umc", [")\n"], [append]),
    %% obtaining the pc value after transforming this component
    translate(Rest).

%% sys calls
%% Entry = {[parent process],entry value for transition}
call(Code, State) ->
    eval(Code, State, {[],1, false}).

%% call to this function whenever there is a process call
%% exp calls
eval({proc, _ArgNames, Code}, State, Entry) ->
    eval(Code, State, Entry);
eval({call, Name, _}, State, {_, Evalue, _} = Entry) ->
    M = ets:lookup_element(State, state, 2),
    #{code_def := Def, pc_name := Pcname, pc_index := I} = M,
    Code = ets:lookup_element(Def, Name, 2),
    io:format("Make a call to ~p ~n",[Name]),
    print(Code),
    Pc = Pcname ++ "[" ++ integer_to_list(I) ++ "]",
    P = ets:lookup_element(State,visited,2),
    %% Store information of the process
    ets:insert(procs_info, {Name, {Name, Pc, I, Evalue}}),
    %% print(Name),
    Visited = [Name|P],
    ets:insert(State,{visited,Visited}),
    %% update proc_name - which is the name of the current process  that executes code
    %% ets:insert(State,{state,M#{proc_name => Name, rec => {Pc,I,Evalue}}}),
    ets:insert(State,{state,M#{parent => Visited}}),
    eval(Code, State, Entry);
eval({prefix, Left, {call,Name,Args}=Right}, State, Entry) ->
    io:format("Prefix action ~p . ~p with Entry ~p~n",[Left,Right,Entry]),
    Parents = ets:lookup_element(State,visited,2),
    print(Parents),
    case lists:member(Name,Parents) of
	true ->
	    print("PCALL or RECURSION"),
	    Rec = ets:lookup_element(procs_info, Name, 2),
	    M = ets:lookup_element(State, state, 2),
	    io:format("Info of ~p is ~p~n",[Name,Rec]),
	    ets:insert(State,{state,M#{rec => Rec}}),
	    eval(Left, State, Entry);
       false ->
	    eval(Left, State, Entry),
	    #{pc_value := Global} = ets:lookup_element(State, state, 2),
	    eval(Right, State, {[], Global, false})
    end;

%% prefix for nil process
eval({prefix, Left, nil}, State, Entry) ->
    M = ets:lookup_element(State, state, 2),
    ets:insert(State,{state,M#{next_is_nil => true}}),
    eval(Left, State, Entry);

%% prefix for other process
eval({prefix, Left, Right}, State, Entry) ->
    eval(Left, State, Entry),
    #{pc_value := Global} = ets:lookup_element(State, state, 2),
    eval(Right, State, {[], Global, false});

eval({p_awareness,Pred,Process},State,Entry) ->
    M = ets:lookup_element(State,state,2),
    #{aware := PAware, v_name := Vars, comp_index := I, b_name := Boundname, bound_index := BIndex} = M,
    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    P = build_pred(local, Pred, I, Vars, Bound),
    ets:insert(State,{state,M#{aware => [P|PAware]}}),
    %%print(P),
    eval(Process, State, Entry);

eval({p_update,Assingments,Process},State,Entry) ->
    M = ets:lookup_element(State,state,2),
    #{update := Upd, v_name := Vars, comp_index := I, b_name := Boundname, bound_index := BIndex} = M,
    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    A = build_assign(Assingments, I, Vars, Bound),
    ets:insert(State,{state,M#{update => Upd ++ A}}),
    eval(Process, State, Entry);

eval({choice, Left, Right}, State, Entry) ->
    eval(Left, State, Entry),
    eval(Right, State, Entry);

eval({pchoice,{prefix,{output,Exp1,Pred1},Cs1},{prefix,{output,Exp2,Pred2},Cs2}}, State, Entry) ->
    % number of branches w.r.t priority choice of this component
    Pchoice = get(pchoice_id),
    if Pchoice == undefined ->
	    put(pchoice_id,0);
       true -> put(pchoice_id,Pchoice+1)
    end,
    eval({prefix,{poutput,Exp1,Pred1},Cs1}, State, Entry),
    eval({prefix,{poutput,Exp2,Pred2},Cs2}, State, Entry);

%% Suport priority choice with awareness operator
eval({pchoice,{p_awareness,Aware1, {prefix,{output,Exp1,Pred1},Cs1}},{p_awareness,Aware2,{prefix,{output,Exp2,Pred2},Cs2}}}, State, Entry) ->
    % number of branches w.r.t priority choice of this component
    Pchoice = get(pchoice_id),
    if Pchoice == undefined ->
	    put(pchoice_id,0);
       true -> put(pchoice_id,Pchoice+1)
    end,
    eval({p_awareness,Aware1, {prefix,{poutput,Exp1,Pred1},Cs1} }, State, Entry),
    eval({p_awareness,Aware2, {prefix,{poutput,Exp2,Pred2},Cs2} }, State, Entry);

eval({par, Left, {bang,{call,Name,_},_}=Right}, State, {Parent,Val,Sib} = Entry) ->
    Parents = ets:lookup_element(State,visited,2),
    io:format("Enter par with bang, select, parent = ~p, entry = ~p~n",[Parents,Entry]),
    [H|T] = Parents,
    Sibbling = if Sib == false -> 0; true -> Sib+1 end,
%%    Appear = get_appearance(Name,Parents),
    case lists:member(Name,Parents) of
	true ->
	    #{pc_value := Pvalue} = ets:lookup_element(State,state,2),
	    if Pvalue == 1 ->
		    eval({parroot,Left,Right},State,{Parent,Val,Sibbling});
	       true ->
		    eval({parbang,Left,Right},State,{Parent,Val,Sibbling})
	    end;
	false ->
	    eval({parnorm,Left,Right},State,Entry)
    end;

eval({parroot, Left, {bang,{call,Name,_},_} = Right}, State, {Parent, Val, Sib} = Entry) -> % spawn process with no prefix action is treated as a simpler case
    io:format("Parallel at root with bang with Entry ~p ~n",[Entry]),
    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),
    #{bound_index := BIndex, pc_index := PIndex}  =  Map,
    P2 = NumProcs,
    ets:insert(Root, {num_procs, P2+1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,visited,2),

    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State2 = ets:new(list_to_atom(Child2),[]),

    Process2 = Map#{pc_index := P2, bound_index := BIndex + 1, pc_value := 1, update := [], aware := []},

    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {visited, Parents}),

    App = get_apperance(Name,Parents),

    ParentEntry = if App > 1 -> []; true -> Parent end,
    ValEntry = if App > 1 -> 1; true -> Val end,
    %% ParentEntry = Parent,
    %% ValEntry = Val,
    eval(Left, State, {ParentEntry,ValEntry,Sib}),
    eval(Right, State2, {ParentEntry,ValEntry,Sib});

eval({parnorm, Left, Right}, State, {_, 1, _} = Entry) -> % spawn process with no prefix action is treated as a simpler case
    print("Parallel at root "),
    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),
    #{bound_index := BIndex}  =  Map,

    P2 = NumProcs,

    ets:insert(Root, {num_procs, P2+1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,visited,2),

    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State2 = ets:new(list_to_atom(Child2),[]),

    Process2 = Map#{pc_index := P2, bound_index := BIndex + 1, pc_value := 1, update := [], aware := []},

    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {visited, Parents}),


    eval(Left, State, Entry),
    eval(Right, State2, Entry);

eval({parbang, Left, {bang,_,_} = Right}, State, {Parent, _Value, Sib}) ->
    print("Parallel with bang"),
    print(_Value),
    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),
    #{pc_name := Pcname, pc_value := Global, bound_index := BIndex, pc_index := PIndex}  =  Map,

    P1 = NumProcs,

    P2 = P1 + 1,
    io:format("Pass ~p to LEFT ~n",[Sib]),
    io:format("Pass ~p to Right ~n",[P1]),
    ets:insert(Root, {num_procs, P2 + 1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,visited,2),
    Child1 = atom_to_list(ParentName) ++ integer_to_list(P1),
    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State1 = ets:new(list_to_atom(Child1),[]),
    State2 = ets:new(list_to_atom(Child2),[]),

    Process1 = Map#{pc_index := P1, bound_index := BIndex, pc_value := 1},
    Process2 = Map#{pc_index := P2, bound_index := BIndex + 1, pc_value := 1},
    ets:insert(State1, {state, Process1}),
    ets:insert(State1, {visited, Parents}),
    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {visited, Parents}),
    Entry1 = {[{Pcname, PIndex, Global} | Parent], 1, Sib},
    Entry2 = {[{Pcname, PIndex, Global} | Parent], 1, Sib},
    eval(Left, State1, Entry1),
    eval(Right, State2, Entry2);

eval({par, Left, Right}, State, {Parent, _Value, _}) ->
    print("Parallel "),
    print(_Value),
    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),
    #{pc_name := Pcname, pc_value := Global, bound_index := BIndex, pc_index := PIndex}  =  Map,

    P1 = NumProcs,

    P2 = P1 + 1,

    print("BOUND INDEX LEFT"),
    print(BIndex),
    print("BOUND INDEX RIGHT"),
    print(BIndex + 1),
    ets:insert(Root, {num_procs, P2 + 1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,visited,2),
    Child1 = atom_to_list(ParentName) ++ integer_to_list(P1),
    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State1 = ets:new(list_to_atom(Child1),[]),
    State2 = ets:new(list_to_atom(Child2),[]),

    Process1 = Map#{pc_index := P1, bound_index := BIndex, pc_value := 1},
    Process2 = Map#{pc_index := P2, bound_index := BIndex + 1, pc_value := 1},
    ets:insert(State1, {state, Process1}),
    ets:insert(State1, {visited, Parents}),
    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {visited, Parents}),
    Entry1 = {[{Pcname, PIndex, Global} | Parent], 1, false},
    Entry2 = {[{Pcname, PIndex, Global} | Parent], 1, false},
    eval(Left, State1, Entry1),
    eval(Right, State2, Entry2);

%% bang directly (no parents) ,e.g.: P = a |^n P
%% need to accumulate parallel instances
%% eval({bang, {call,Name,_Args}, Time}, State, {_,1}=Entry) ->
%%     Current = get(Name),
%%     %%print(Current),
%%     Test = case Current of
%% 	       undefined ->
%% 		   put(Name,Time),
%% 		   Time;
%% 	       0 -> 0;
%% 	      _ ->
%% 		   put(Name, Current - 1),
%% 		   Current - 1
%% 	   end,
%%     if Test == 0 ->
%% 	    erase(Name),
%% 	    %%do not count this process
%% 	    Root = get(root),
%% 	    NumProcs = ets:lookup_element(Root,num_procs,2),
%% 	    ets:insert(Root,{num_procs, NumProcs - 1}),
%% 	    eval(nil,State,Entry);
%%        true ->
%% 	    #{code_def := Def, pc_index := PIndex, pc_name := Pcname} = ets:lookup_element(State, state, 2),
%% 	    {proc, _Args, Code} = ets:lookup_element(Def,Name,2),
%% 	    Entry2 = {[{Pcname, PIndex, par}], 1},
%% 	    eval(Code, State, Entry2)
%%     end;
%% bang with parent, e.g., P = a.(Q |^n P).
eval({bang, {call,Name,_Args}=Body, Time}, State, Entry) ->
    print("Bang with !"),
    print(Entry),
    Current = get(Name),
    M = ets:lookup_element(State, state, 2),
    #{code_def := Def, pc_index := PIndex} = M,
    %%{proc, _Args, Code} = ets:lookup_element(Def,Name,2),
    print(Current),
    print(PIndex),

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
	    eval(Body, State, Entry)
    end;
eval(nil, _, _) ->
    print("STOP");
eval(Act, State, Entry) ->
    create_trans(Act, State, Entry).

%% Behavioral mappings for two
create_trans({output, empty, empty}, State, {Parent, Value, Sibbling}) -> %% empty send ()@(ff)
    Map = ets:lookup_element(State,state,2),
    #{update := Upd, aware := Aware, rec := Rec, comp_index := SIndex, pc_name := Pcname, pc_value := Global, pc_index := PIndex, bound_index := BIndex, b_name := Boundname, next_is_nil := Nil, use_var := UseVar}  =  Map,
    print(Upd),
    print(Aware),
    Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n\t") ++ ";\n" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,
    Sib = if Sibbling == false -> "";true -> " and " ++ Pcname ++ "[" ++ integer_to_list(Sibbling) ++ "] != 1" end,
    Cond1 = build_pc_guard({Parent, {Pcname, PIndex, Value}}),
    Sname = "$2.s"++SIndex,

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    Guards1 = "\tallowsend(i)[receiving = false and i = " ++ SIndex ++ " and " ++  PAware  ++ Cond1 ++ Sib ++ "]/\n",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    Clear = if Nil == true -> "\n\t"++ Pc ++ ":= 0; " ++ Bound ++ ":= 0;"; true -> "" end,
    Clear2 = if UseVar == false -> "\n\t"++ Bound ++ ":= 0;"; true -> "" end,
    print("DEtermine REC"),
    print(Rec),
    print(Global),
    #{parent := Parents} = Map,
    RecString = case Rec of
		    {} -> integer_to_list(Global+1); % no process call or nil process
		    {SomeName, Pc, PIndex, MyVal} ->
			case SomeName == lists:nth(1,lists:reverse(Parents)) of
			    true -> "1";
			    false ->  integer_to_list(MyVal)
			end;
		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> "1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal); true -> integer_to_list(Global+1) end
		end,
    Actions1 = "\tself.allowsend(" ++ SIndex ++ ");\n\t" ++ Pc ++ " = " ++ RecString ++ ";\n" ++ Clear ++ Clear2 ++ "}\n",
    NewMap = Map#{rec => {}, pc_value => Global+1, aware => [], update => [], next_is_nil => false},
    ets:insert(State, {state, NewMap}),
    Signal = " \n -----Empty Send ----- \n",
    Print = [Signal, Trans, Guards1, Assigns, Actions1],%, Trans, Guards2, Actions2],
    file:write_file("foo.umc", Print, [append]);

%% create_trans({output, Exps, Pred}, State, {Parent, Value}) -> %normal send
%%     Map = ets:lookup_element(State,state,2),
%%     #{update := Upd, aware := Aware, rec := Rec, comp_index := SIndex, v_name := Vars, pc_name := Pcname, pc_value := Global, pc_index := PIndex, bound_index := BIndex, b_name := Boundname}  =  Map,
%%     print(Upd),
%%     print(Aware),
%%     Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n\t") ++ ";\n" end,
%%     PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,

%%     Cond1 = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

%%     Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
%%     Sname = "$2.s"++SIndex,

%%     Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
%%     Guards1 = "\tallowsend(i)[receiving = false and i = " ++ SIndex ++ " and " ++  PAware  ++ Cond1 ++ "]/\n",
%%     SndP = build_pred(local,Pred,SIndex,Vars,Bound),
%%     Msg = build_outE(Exps,SIndex,Vars,Bound),
%%     Target = "\tfor j in 0..pc.length-1 {\n\t\tif " ++ SndP ++
%% 	" then \n\t\t\t{target[j]:=1;} else {target[j]:=0;}\n\t};\n\treceiving=true;\n\tif target.length > 0 then { \n",
%%     Output = "\t\tself.broadcast(target," ++ Msg ++ "," ++ SIndex ++ ");\n\t\t",
%%     Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",


%%     Guards2 = "\tbroadcast(tgt,msg,j)[" ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ "]/\n",
%%     print("DEtermine REC"),
%%     print(Rec),
%%     print(Global),
%%     {RecString,RecVal} = case Rec of
%% 		    {} -> {integer_to_list(Global+2),Global+2}; % no process call or nil process
%% 		    {SomeName, Pc, PIndex, MyVal} ->
%% 			#{proc_name := Proc_Name} = Map,
%% 			if SomeName == Proc_Name -> {"1",Global+1};
%% 			   true ->  {integer_to_list(MyVal),Global+1}
%% 			   %integer_to_list(Global+2)
%% 			end;
%% 		    {SomeName, Pc, PIndex, MyVal} ->
%% 			#{proc_name := Proc_Name} = Map,
%% 			if SomeName == Proc_Name -> {"1",Global+1};
%% 			   true ->  {integer_to_list(MyVal),Global+1}
%% 			   %integer_to_list(Global+2)
%% 			end;
%% 		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> {"1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal),Global+1}; true -> {integer_to_list(Global+2),Global+2} end
%% 		    %%{Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> "1"; true -> integer_to_list(Global+2) end ++ ";\n\t" ++ Mypc ++ " = " ++ integer_to_list(MyVal)
%% 		end,
%%     Actions1 = Target ++ Output ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ ";\n\t} else {\n\t\t" ++ Pc ++ " = " ++ RecString ++ ";\n\t\treceiving=false;\n\t\tself.allowsend(" ++ SIndex ++ ");\n\t}\n}\n",
%%     Actions2 = "\treceiving=false;\n\tself.allowsend(" ++ SIndex ++ ");\n\t"
%% 	++ Pc ++ " = "
%% 	++ RecString ++ ";\n}\n",
%%     NewMap = Map#{rec => {}, pc_value => RecVal, aware => [], update => []},
%%     ets:insert(State, {state, NewMap}),

%%     Signal = " \n ----- Send ----- \n",
%%     Print = [Signal, Trans, Guards1, Assigns, Actions1, Trans, Guards2, Actions2],
%%     file:write_file("foo.umc", Print, [append]);
create_trans({output, Exps, Pred}, State, {Parent, Value, Sibbling}) -> %normal send
    Map = ets:lookup_element(State,state,2),
    #{update := Upd, aware := Aware, rec := Rec, comp_index := SIndex, v_name := Vars, pc_name := Pcname, pc_value := Global, pc_index := PIndex, bound_index := BIndex, b_name := Boundname, next_is_nil := Nil, use_var := UseVar}  =  Map,
    print("Send"),
    {CurrentChoice, NextChoice} =
	if Sibbling =/= false ->
	   S1 = " and par[$1]["++integer_to_list(Sibbling) ++ "] = 1",
	   S2 = "\n\t\tpar[$1]["++integer_to_list(Sibbling+1)++"] = 1;\n\t\t",
	   {S1,S2};
       true -> {"",""}
    end,
    Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n\t") ++ ";\n" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,
    Cond1 = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    Sname = "$2.s"++SIndex,

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    Guards1 = "\tallowsend(i)[receiving = false and i = " ++ SIndex ++ " and " ++  PAware  ++ Cond1 ++ CurrentChoice ++ "]/\n",
    Msg = build_outE(Exps,SIndex,Vars,Bound),
    SndP = build_pred(local,Pred,SIndex,Vars,Bound),


    %%% if there any membership predicate
    MPred = get_membership_predicate(),
    Selected = case MPred of
		   [] -> "target[j] := 1";
		   [Ele,Vec] -> "counter :int :=0; \n\tfor z in 0.."++Vec++".length-1 {if (" ++ Ele ++ " = " ++ Vec ++ "[z]) then { counter := counter +1;}};\n\t\tif (counter = 0) then {target[j]:=1;} else {target[j] := 0;}"
	       end,
    Target = "\ttarget:int[];\n\tfor j in 0..pc.length-1 {\n\t\tif " ++ SndP ++ " then \n\t\t\t{"++ Selected ++ "\n\t} else {target[j]:=0;}\n\t};\n",
    Output = "\treceiving=true;\n\tif target.length > 0 then { \n\t\tself.broadcast(target," ++ Msg ++ "," ++ SIndex ++ ");\n\t\t",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Clear = if Nil == true -> "\n\t"++ Pc ++ ":= 0; " ++ Bound ++ ":= 0;"; true -> "" end,
    Clear2 = if UseVar == false -> "\n\t"++ Bound ++ ":= 0;"; true -> "" end,
    Guards2 = "\tbroadcast(tgt,msg,j)[" ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ "]/\n",
    print("DEtermine REC"),
    print(Rec),
    print(Global),
    print(Map),
    #{parent := Parents} = Map,
    {RecString,RecVal} = case Rec of
		    {} -> {integer_to_list(Global+2),Global+2}; % no process call or nil process
		    {SomeName, Pc, PIndex, MyVal} ->
			case SomeName == lists:nth(1,lists:reverse(Parents)) of
			    true -> {"1",Global+1};
			    false ->  {integer_to_list(MyVal),Global+1}
			end;
		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> {"1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal),Global+1}; true -> {integer_to_list(Global+2),Global+2} end
		end,
    Actions1 = Target ++ Output ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ ";\n\t} else {\n\t\t" ++ NextChoice ++ Pc ++ " = " ++ RecString ++ ";\n\t\treceiving=false;\n\t\tself.allowsend(" ++ SIndex ++ ");\n\t" ++ Clear ++ Clear2 ++ "}\n}\n",
    Actions2 = "\treceiving=false;\n\tself.allowsend(" ++ SIndex ++ ");\n\t"
	++ Pc ++ " = "
	++ RecString ++ ";\n" ++ Clear ++ Clear2 ++ "}\n",
    NewMap = Map#{rec => {}, pc_value => RecVal, aware => [], update => [], next_is_nil => false},
    ets:insert(State, {state, NewMap}),

    Signal = " \n ----- Send ----- \n",
    Print = [Signal, Trans, Guards1, Assigns, Actions1, Trans, Guards2, Actions2],
    file:write_file("foo.umc", Print, [append]);

create_trans({poutput, Exps, Pred}, State, {Parent, Value, Sibbling}) -> %send and check if it is succesful
    Map = ets:lookup_element(State,state,2),
    #{update := Upd, aware := Aware, rec := Rec, comp_index := SIndex, v_name := Vars, pc_name := Pcname, pc_value := Global, pc_index := PIndex, bound_index := BIndex, b_name := Boundname, next_is_nil := Nil, use_var := UseVar}  =  Map,
    print("Priority Send"),

    ChoiceId = get(pchoice_id),
    print(ChoiceId),
    CurrentChoice = "my[$1]["++integer_to_list(ChoiceId) ++ "] = 1",
    NextChoice = "my[$1]["++integer_to_list(ChoiceId) ++ "] = 0;\n\t\tmy[$1]["++integer_to_list(ChoiceId+1)++"] = 1;\n\t\t",
    put(pchoice_id,ChoiceId+1),

    Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n\t") ++ ";\n" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,
    %% schedule parallel instance
    Sib = if Sibbling == false -> "";true -> " and " ++ Pcname ++ "[" ++ integer_to_list(Sibbling) ++ "] != 1" end,

    Cond1 = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Clear = if Nil == true -> "\n\t"++ Pc ++ ":= 0; " ++ Bound ++ ":= 0;"; true -> "" end,
    %%Clear2 = if UseVar == false -> "\n\t"++ Bound ++ ":= 0;"; true -> "" end,
    Sname = "$2.s"++SIndex,

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    Guards1 = "\tallowsend(i)[receiving = false and i = " ++ SIndex ++ " and " ++  PAware  ++ Cond1 ++ " and " ++ CurrentChoice ++ Sib ++ "]/\n",
    Msg = build_outE(Exps,SIndex,Vars,Bound),
    SndP = build_pred(local,Pred,SIndex,Vars,Bound),

    %%% if there any membership predicate
    MPred = get_membership_predicate(),
    Selected = case MPred of
		   [] -> "target[j] := 1";
		   [Ele,Vec] -> "counter :int :=0; \n\tfor z in 0.."++Vec++".length-1 {if (" ++ Ele ++ " = " ++ Vec ++ "[z]) then { counter := counter +1;}};\n\t\tif (counter = 0) then {target[j]:=1;} else {target[j] := 0;}"
	       end,
    Target = "\ttarget:int[];\n\tfor j in 0..pc.length-1 {\n\t\tif " ++ SndP ++ " then \n\t\t\t{"++ Selected ++ "\n\t} else {target[j]:=0;}\n\t};\n",
    Output = "\treceiving=true;\n\tif target.length > 0 then { \n\t\tself.broadcast(target," ++ Msg ++ "," ++ SIndex ++ ");\n\t\t",


    Guards2 = "\tbroadcast(tgt,msg,j)[" ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ "]/\n",
    print("DEtermine REC"),
    print(Rec),
    print(Global),
    #{parent := Parents} = Map,
    {RecString,RecVal} = case Rec of
		    {} -> {integer_to_list(Global+2),Global+2}; % no process call or nil process
		    {SomeName, Pc, PIndex, MyVal} ->
				 case SomeName == lists:nth(1,lists:reverse(Parents)) of
				     true -> {"1",Global+1};
				     false ->  {integer_to_list(MyVal),Global+1}
				 end;
		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> {"1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal),Global+1}; true -> {integer_to_list(Global+2),Global+2} end
		end,
    Actions1 = Target ++ Output ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ ";\n\t} else {\n\t\t" ++ NextChoice ++  Pc ++ " = " ++ integer_to_list(Value) ++ ";\n\t\treceiving=false;\n\t\tself.allowsend(" ++ SIndex ++ ");\n\t" ++ Clear ++ "\n}}\n",

    Actions2 = "\treceiving=false;\n\tself.allowsend(" ++ SIndex ++ ");\n\t"
	++ Pc ++ " = "
	++ RecString ++ ";\n" ++ Clear ++ "}\n",
    NewMap = Map#{rec => {}, pc_value => RecVal, aware => [], update => [], next_is_nil => false},
    ets:insert(State, {state, NewMap}),
    Signal = " \n ----- Send ----- \n",
    Print = [Signal, Trans, Guards1, Assigns, Actions1, Trans, Guards2, Actions2],
    file:write_file("foo.umc", Print, [append]);

%% create_trans({output, Exps, Pred}, State, {Parent, Value}) -> % send takes into account priority
%%     Map = ets:lookup_element(State,state,2),
%%     #{update := Upd, aware := Aware, rec := Rec, comp_index := SIndex, v_name := Vars, pc_name := Pcname, pc_value := Global, pc_index := PIndex, bound_index := BIndex, b_name := Boundname}  =  Map,
%%     print(Upd),
%%     print(Aware),
%%     Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n\t") ++ ";\n" end,
%%     PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,

%%     Cond1 = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

%%     Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
%%     Sname = "$2.s"++SIndex,

%%     Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
%%     Guards1 = "\tallowsend(i)[receiving = false and i = " ++ SIndex ++ " and " ++  PAware  ++ Cond1 ++ "]/\n",
%%     SndP = build_pred(local,Pred,SIndex,Vars,Bound),
%%     Msg = build_outE(Exps,SIndex,Vars,Bound),
%%     Target = "\ttarget:int[];\n\tfor j in 0..pc.length-1 {\n\t\tif " ++ SndP ++ " then \n\t\t\t{target[j]:=1;} else {target[j]:=0;}\n\t};\n\treceiving=true;\n\tif target.length > 0 then { \n",
%%     Output = "\t\tself.broadcast(target," ++ Msg ++ "," ++ SIndex ++ ");\n\t\t",
%%     Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",


%%     Guards2 = "\tbroadcast(tgt,msg,j)[" ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ "]/\n",
%%     print("DEtermine REC"),
%%     print(Rec),
%%     print(Global),
%%     {RecString,RecVal} = case Rec of
%% 		    {} -> {integer_to_list(Global+2),Global+2}; % no process call or nil process
%% 		    {SomeName, Pc, PIndex, MyVal} ->
%% 			#{proc_name := Proc_Name} = Map,
%% 			if SomeName == Proc_Name -> {"1",Global+1};
%% 			   true ->  {integer_to_list(MyVal),Global+1}
%% 			   %integer_to_list(Global+2)
%% 			end;
%% 		    {SomeName, Pc, PIndex, MyVal} ->
%% 			#{proc_name := Proc_Name} = Map,
%% 			if SomeName == Proc_Name -> {"1",Global+1};
%% 			   true ->  {integer_to_list(MyVal),Global+1}
%% 			   %integer_to_list(Global+2)
%% 			end;
%% 		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> {"1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal),Global+1}; true -> {integer_to_list(Global+2),Global+2} end
%% 		    %%{Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> "1"; true -> integer_to_list(Global+2) end ++ ";\n\t" ++ Mypc ++ " = " ++ integer_to_list(MyVal)
%% 		end,
%%     Actions1 = Target ++ Output ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ ";\n\t} else {\n\t\t" ++ Pc ++ " = " ++ RecString ++ ";\n\t\treceiving=false;\n\t\tself.allowsend(" ++ SIndex ++ ");\n\t}\n}\n",
%%     Actions2 = "\treceiving=false;\n\tself.allowsend(" ++ SIndex ++ ");\n\t"
%% 	++ Pc ++ " = "
%% 	++ RecString ++ ";\n}\n",
%%     NewMap = Map#{rec => {}, pc_value => RecVal, aware => [], update => []},
%%     ets:insert(State, {state, NewMap}),

%%     Signal = " \n ----- Send ----- \n",
%%     Print = [Signal, Trans, Guards1, Assigns, Actions1, Trans, Guards2, Actions2],
%%     file:write_file("foo.umc", Print, [append]);



create_trans({input, Pred, Vars}, State, {Parent, Value, Sibbling}) ->

    VIndex = lists:seq(0,length(Vars) - 1),
    Vars1 = lists:zip(Vars,VIndex),

    Map = ets:lookup_element(State,state,2),
    #{update := Upd, aware := Aware, rec := Rec, comp_index := SIndex, b_name := Boundname, bound_index := BIndex, pc_name := Pcname, pc_value := Global, pc_index := PIndex, use_var := UseVar}  =  Map,
    print(Upd),
    print(Aware),
    {CurrentChoice, NextChoice} =
	if Sibbling =/= false ->
	   S1 = " and par[$1]["++integer_to_list(Sibbling) ++ "] = 1",
	   S2 = "\n\t\tpar[$1]["++integer_to_list(Sibbling+1)++"] = 1;\n\t\t",
	   {S1,S2};
       true -> {"",""}
    end,
    Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n") ++ ";\n\t" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,

    Cond = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    Received = "OUT.received("++ SIndex ++ ",msg);\n\t",
    Sname = "$2.s"++SIndex,

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    RcvP = build_pred(remote,Pred,SIndex,Vars1,Bound),

    AllowedRcv = "tgt[" ++ SIndex ++ "] = 1 and ",
    Guards = "\tbroadcast(tgt,msg,j)[" ++ AllowedRcv ++ PAware ++ RcvP ++ " and " ++ Cond ++ CurrentChoice ++ "]/\n\t",
    Clear2 = if UseVar == false -> "\n\t"++ Bound ++ ":= 0;"; true -> "" end,
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    #{parent := Parents} = Map,
    RecString = case Rec of
		    {} -> integer_to_list(Global+1); % no process call or nil process
		    {SomeName, Pc, PIndex, MyVal} ->
			case SomeName == lists:nth(1,lists:reverse(Parents)) of
			    true -> "1";
			    false ->  integer_to_list(MyVal)
			   %integer_to_list(Global+2)
			end;
		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> "1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal); true -> integer_to_list(Global+1) end
		end,
    Actions = Received ++ Bound ++ " = msg;\n\t" ++ Clear2 ++ NextChoice ++ Pc ++ " = " ++ RecString ++ ";\n}\n",
    Signal = " \n ----- Receive ----- \n",
    Print = [Signal,Trans,Guards, Assigns,Actions],
    NewMap =  Map#{rec => {}, v_name => Vars1, pc_value => Global + 1, aware => [], update => []},
    ets:insert(State, {state, NewMap}),
    file:write_file("foo.umc", Print, [append]).


build_pc_guard({[],{Pcname, Pinstance, Value}}) ->
    Pcname ++ "[" ++ integer_to_list(Pinstance) ++ "] = " ++ integer_to_list(Value);
	%%++ if Pinstance > 0 -> " and " ++ Pcname ++ "[" ++ integer_to_list(Pinstance-1) ++ "] != 1"; true -> "" end;
build_pc_guard({Parent, {Pcname, P2, V2}}) ->
    build_parent(Parent) ++ " and " ++ Pcname ++ "[" ++ integer_to_list(P2) ++ "] = " ++ integer_to_list(V2).
	%% if P2 > 0 -> " and " ++ Pcname ++ "[" ++ integer_to_list(P2-1) ++ "] != 1"; true -> "" end.

build_parent(L) ->
    build_parent(L,[]).

build_parent([],L) ->
    string:join(L," and ");
%% nice parallelism
build_parent([{Pcname,P,par}|T],L) ->
    String = string:join([Pcname ++ "[" ++ integer_to_list(X) ++ "] != 1" || X <- lists:seq(0,P-1)]," and "),
    build_parent(T,[String|L]);
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


build_choice_list(N) ->
    L = lists:seq(1,N),
    S = ["[1]" || _ <- L],
    "[" ++ string:join(S,",") ++ "]".

%% build_sndpred(Type,Pred,I,Vars,Bound) ->
%%      "(" ++ eval1(Type,Pred,I,Vars,Bound) ++ ")".
%% build_rcvpred(Pred,I,Vars) ->
%%     "("++eval2(Pred,I,Vars)++")".
build_outE(Exps,I, Vars, Bound) ->
    eval3(Exps, I, [],Vars,Bound).
build_pred(Type, Pred, I, Vars,Bound) ->
    L = "("++eval1(Type, Pred, I, Vars,Bound)++")",
    re:replace(L, ":int", "", [global, {return, list}]).
build_assign(Assignments, I, Vars,Bound) ->
    %% Clean dynamic variables created before
    erase(dynamic_vars),
    evala(Assignments, I, [], Vars,Bound).

eval1(Type, {parenthesis,Pred}, I, Vars,Bound) ->
    "(" ++ eval1(Type,Pred,I,Vars,Bound) ++ ")";
eval1(Type, {bracket,Exp}, I, Vars,Bound) ->
    "[" ++ eval1(Type,Exp,I,Vars,Bound) ++ "]";
eval1(Type,{head,Name}, I,Vars,Bound) -> eval1(Type,Name,I,Vars,Bound) ++ ".head";
eval1(Type,{tail,Name}, I,Vars,Bound) -> eval1(Type,Name,I,Vars,Bound) ++ ".tail";
%% NEED TO REVIEW
%% this is for selector of remote attributes, e.g, a[i]
eval1(Type,{selector,List,Index}, I,Vars,Bound) -> eval1(newselector,List,I,Vars,Bound) ++ "[" ++ eval1(Type,Index,I,Vars,Bound) ++ "]";
eval1(_,"true", _,_,_) -> "true";
eval1(_,"false", _,_,_) -> "false";
eval1(_,{self,Att}, I, _,_) -> Att ++ "[" ++ I ++ "]";
eval1(newselector,{att,Att},_,_,_) -> Att;
eval1(_,{att,Att}, _,_,_) -> Att ++ "[j]";
eval1(_,{const,C}, _,_,_) -> C;
eval1(_,{token,T}, _,_,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
eval1(local,[{var,Name}|T]=List, _, Vars, Bound) ->
    io:format("All Vars are ~p~n",[Vars]),
    List2 = [proplists:get_value(X,Vars) || {var,X} <- List],
    S = [Bound ++ "["++integer_to_list(I1)++"]" || I1 <- List2],
    string:join(S,",");

eval1(local,{var,Name}, _, Vars, Bound) ->
    io:format("All Vars are ~p~n",[Vars]),
    I1 = proplists:get_value(Name,Vars),
    case I1 of
	undefined ->
	    get_var_name(Name);
	_ ->
	    Bound ++ "["++integer_to_list(I1)++"]"
    end;
eval1(remote,{var,Name}, _, Vars,_) ->
    I1 = proplists:get_value(Name,Vars),
    "msg["++integer_to_list(I1)++"]";
eval1(Type,{concat,Left,Right}, I,Vars,Bound) -> eval1(Type,Left,I,Vars,Bound) ++ "+"  ++ eval1(Type,Right,I,Vars,Bound);
eval1(Type,{assign, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " := " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{eq, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " = " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{diff, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " != " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{ge, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " > " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{le, Left, Right}, I, Vars,Bound) ->
    eval1(Type,Left, I,Vars,Bound) ++ " < " ++ eval1(Type,Right, I, Vars,Bound);
eval1(Type,{intersect, Left, Right}, Index, Vars,Bound) ->
    eval1(Type,Left, Index, Vars,Bound) ++ " and " ++ eval1(Type,Right, Index, Vars,Bound);
eval1(Type,{union, Left, Right}, Index, Vars,Bound) ->
    eval1(Type,Left, Index, Vars,Bound) ++ " or " ++ eval1(Type,Right, Index, Vars,Bound);
eval1(Type,{notmember, Left, Right}, Index, Vars,Bound) ->
    L= eval1(Type,Left, Index, Vars,Bound),
    R = eval1(Type,Right, Index, Vars,Bound),
    put(notmember,[L,R]),
    "true";
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

%% detech token, const in attribute environment declaration
data_eval({token,T}) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
data_eval({const,C}) ->
    C;
% an array of single elements
data_eval(List) when is_list(List) ->
    Array = [data_eval(X) || X <- List],
    "[" ++ string:join(Array,",") ++ "]";
data_eval(Other) -> Other.

get_membership_predicate() ->
  M = get(notmember),
  if M == undefined ->  [];
     true -> erase(notmember),M
  end.
get_var_name(Name) ->
  M = get(dynamic_vars),
  if M == undefined ->
	  put(dynamic_vars,[{Name,Name}]),
	  Name ++ ":int";
     true ->
	  case lists:keyfind(Name,1,M) of
	      false ->
		  put(dynamic_vars,[{Name,Name}|M]),
		  Name ++ ":int";
	      {Name,Name} -> Name
	  end
  end.
get_apperance(E,List) ->
    lists:sum([1 || X <- List, X == E]).
