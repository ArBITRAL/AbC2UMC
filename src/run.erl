%% FOR stable marriage
-module(run).
-compile(export_all).
-export([string/1, file/1, main/1, view/1]).

-record(state,{parent, entry, sib, next_is_nil,update, aware, recursive, exit_point_id, first_act, recstring, g_aware, p_action,use_var,last_sib}).

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
view([Atom]) when is_atom(Atom) ->
    view(atom_to_list(Atom) ++ ".abc");
view(Fname) ->
    {ok, Binary} = file:read_file(Fname),
    view1(binary_to_list(Binary)).
view1(Code) ->
    {ok, Tree} = parser:scan_and_parse(Code),
    io:format("~p~n",[Tree]).

%% translate the code
string(String) when is_list(String) ->
    {ok, Tree} = parser:scan_and_parse(String),
    catch ets:delete(system),
    ets:new(system,[named_table]),
    ets:insert(system, {attributes, #{}}),

    %% component definitions
    CompDefs = [X || X <- Tree, element(1,X) == comp],

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
    init(SYS,[],[]).

init([],PcList,ParList) ->
    Finished = "end System;\n\n",
    LineSep = io_lib:nl(),
    Pc = build_pc_list(PcList),
    Pchoice = build_choice_list(length(PcList)),
    print(ParList),
    Parchoice = build_par_list(ParList),
    Data = ets:lookup_element(system, data, 2),
    Temp1 = [proplists:get_keys(X) || X <- Data],
    Completeness = build_observation(length(PcList)),
    %% Get union of the attribute set
    Atts = sets:to_list(sets:from_list(lists:umerge(Temp1))),

    %% Build the attribute environment declaration
    Decl = lists:foldr(fun(X,Sum) ->
			Array = lists:foldl(fun(Comp, Acc) ->
						     case proplists:get_value(X,Comp) of
							 undefined ->
							     ["[]" | Acc];
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
	%if Decl == [] -> ""; true -> ", " end ++ "pc => " ++ Pc ++  ", my =>" ++ Pchoice ++ ", par =>" ++ Parchoice ++ ");",
	if Decl == [] -> ""; true -> ", " end ++ "pc => " ++ Pc ++  ", my =>" ++ Pchoice ++ ");",
    Abstraction = "Abstractions {
    State partner=$1 -> matched($1)
    State level=$1 -> level($1)
    State total=$1 -> total($1)
    State partner=$v and $v[0]= $2 and id[0]!=0 and id[0]=$1 ->  haspartner($1,$2)
    State partner=$v and $v[1]= $2 and id[1]!=0 and id[1]=$1 ->  haspartner($1,$2)
    State partner=$v and $v[2]= $2 and id[2]!=0 and id[2]=$1 ->  haspartner($1,$2)
    State partner=$v and $v[3]= $2 and id[3]!=0 and id[3]=$1 ->  haspartner($1,$2)
    State partner=$v and $v[4]= $2 and id[4]!=0 and id[4]=$1 ->  haspartner($1,$2)
    State partner=$v and $v[5]= $2 and id[5]!=0 and id[5]=$1 ->  haspartner($1,$2)
    State partner=$v and $v[6]= $2 and id[6]!=0 and id[6]=$1 ->  haspartner($1,$2)
    State partner=$v and $v[7]= $2 and id[7]!=0 and id[7]=$1 ->  haspartner($1,$2)
    Action m_decrease -> m_decreased
    Action w_decrease -> w_decreased
    Action m_increase -> m_increased
    Action w_increase -> w_increased
    Action sending($1,$2) -> send($1,$2)
    Action received($1,$2,$3) -> received($1,$2,$3)\n   "++Completeness++"\n}\n\n",

    Print = [Finished, LineSep, Object, LineSep, Abstraction, TokenDef],
    file:write_file("foo.umc", Print, [append]),
    ok;
init([{comp_init,Name,_}|Rest],PcList,ParList) ->
    {comp, CName, _Data}  = ets:lookup_element(system,Name,2),
    Print = "---------- COMPONENT " ++ atom_to_list(Name) ++ " ------------ \n",
    I = length(PcList),
    Code = atom_to_list(CName)++"("++integer_to_list(I)++","++atom_to_list(Name)++")\n",
    file:write_file("foo.umc", [Print,Code], [append]),
    Pc = ets:lookup_element(CName,num_procs,2),
    ParvectorName = atom_to_list(CName) ++ "par_vector",
    ParVector = get(ParvectorName),
    print(ParVector),
    init(Rest,[Pc|PcList],[ParVector|ParList] );
init([{comp_call,Name,_}|Rest],PcList,ParList) ->
    {comp, CName, _Data}  = ets:lookup_element(system,Name,2),
    Print = "---------- COMPONENT " ++ atom_to_list(Name) ++ " ------------ \n",
    I = length(PcList),
    Code = atom_to_list(CName)++"("++integer_to_list(I)++","++atom_to_list(Name)++")\n",
    file:write_file("foo.umc", [Print,Code], [append]),
    Pc = ets:lookup_element(CName,num_procs,2),
    ParvectorName = atom_to_list(CName) ++ "par_vector",
    ParVector = get(ParvectorName),
    %% print(ParVector),
    init(Rest,[Pc|PcList],[ParVector|ParList]).

template(Code,AttEnv) ->
    LineSep = io_lib:nl(),
    Class = "Class System with niceparallelism is\nSignals:\n\tallowsend(i:int);\n\tbroadcast(tgt,msg,j:int);\nVars:\n\tRANDOMQUEUE;\n\treceiving:bool := false;\n\tpc :int[];\n\tbound : obj[];\n\tmy;\n\ttable:int[];\n\ttotal:int :=0;\n\t\n\t-- attributes\n\t" ++ string:join(maps:keys(AttEnv),";\n\t") ++ ";",
    Init = "
  \ttable[0][0][0][0] := 4;
  \ttable[0][0][0][1] := 3;
  \ttable[0][0][1][0] := 2;
  \ttable[0][0][1][1] := 1;

  \ttable[0][1][0][0] := 3;
  \ttable[0][1][0][1] := 4;
  \ttable[0][1][1][0] := 1;
  \ttable[0][1][1][1] := 2;

  \ttable[1][0][0][0] := 2;
  \ttable[1][0][0][1] := 1;
  \ttable[1][0][1][0] := 4;
  \ttable[1][0][1][1] := 3;

  \ttable[1][1][0][0] := 1;
  \ttable[1][1][0][1] := 2;
  \ttable[1][1][1][0] := 3;
  \ttable[1][1][1][1] := 4;",
    Trans ="\nState Top Defers allowsend(i)\nTransitions:\ninit -> SYS { -/\t" ++ Init ++ "\n\n\tfor i in 0..pc.length-1 {\n\t\tself.allowsend(i);\n\t}}",
    put(token,#{}),
    Print = [Class, Trans, LineSep],
    file:write_file("foo.umc", Print, [append]),
    translate(Code).

%% finish translating, output the tail of UMC specification
translate([]) ->
    finished;
%% translate each component type!
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
    catch ets:delete(exit_point),
    %% this table is for storing processese information of one component, helpful for process call or recursion
    %% Pcname (belong to Component),
    %% PcIndex - increasing when component spawn more processes
    %% and Pc_value - the initial value decide the action to be executed
    ets:new(procs_info,[named_table]),
    ets:new(exit_point,[named_table]),
    %% root is the name of component instance
    put(root,Name),
    put(parchoice_id,undefined),
    ParvectorName = atom_to_list(Name) ++ "par_vector",
    put(ParvectorName,[]),
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
    Process = #{code_def => CName, parent => [], rec => {}, comp_index => "$1", v_name => [], b_name => Boundname, bound_index => 0, pc_name => Pcname, pc_index => 0, pc_value => 1, bindings => [], arg_bindings => []},
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
    LocalState = #state{parent = [], entry = 1, sib = false, next_is_nil = false, update = [], aware = [], recursive = false, exit_point_id = [], recstring = false, g_aware = [], p_action = false, use_var = true, last_sib = false},
    eval(Code, State, LocalState).

%% call to this function whenever there is a process call
%% exp calls
eval({proc, Args, Code}, State, LocalState) ->
    %%io:format("Eval with formal params ~p ~n",[Args]),
    M = ets:lookup_element(State, state, 2),
    ArgBindings =
	if Args =/= [] ->
		#{bindings := Bindings} = M,
		select_bindings(Args,Bindings);
       true -> []
    end,
    ets:insert(State,{state,M#{arg_bindings => ArgBindings}}),
    eval(Code, State, LocalState);
eval({call, Name, Args}, State, Local = #state{entry = Evalue, recursive = Recursive}) ->
    M = ets:lookup_element(State, state, 2),
    #{bindings := Bindings} = M,
    #{code_def := Def, pc_name := Pcname, pc_index := I} = M,
    Code = ets:lookup_element(Def, Name, 2),
    Pc = Pcname ++ "[" ++ integer_to_list(I) ++ "]",
    P = ets:lookup_element(State,visited,2),
    Exist = ets:lookup(procs_info,Name),
    %% Rec1 is to detech if there any recursive call to a process name , e.g., X = a.(b.X + X)
    {Rec1, Reset,ExitPointId} =
	case Exist of
	    [] ->
		if Recursive == false ->
			ets:insert(procs_info, {Name, {Name, Pc, I, Evalue}}),
		        ets:insert(exit_point,{{Name, Pc, I, Evalue},[]});
		   true -> ok
		end,
		{false,Evalue,{Name, Pc, I, Evalue}};
	    [{Name,ExistTuple}] ->
		ExistIndex = element(3,ExistTuple),
		Rec2 =
		    if ExistIndex == I ->
			    true;
		       true ->
			    ets:insert(exit_point,{{Name, Pc, I, Evalue},[]}),
			    ets:insert(procs_info, {Name, {Name, Pc, I, Evalue}}),
			    false
		end,
		{Rec2,element(4,ExistTuple),ExistTuple}
    end,
    Visited = if Recursive == halfway -> P ; true -> [Name|P] end,
    ets:insert(State,{visited,Visited}),
    NewLocal = if Recursive == true ->
       		       Local#state{first_act = true};
    		  true ->
    		       Local#state{exit_point_id = ExitPointId,first_act=true,recursive = Rec1}
    	     end,
    Rec = if Rec1 == true ->
		  ets:lookup_element(procs_info, Name, 2);
	     true -> {}
	  end,
    io:format("~n~n~n  ========= Make a call to ~p ~n with info ~p ~n",
	      [Name,ets:tab2list(State)]),
    NewBindings = if Args =/= [] -> filter_bindings(Args,Bindings); true -> [] end,
    %% New process shall not have v_name anymore, v_name is for input variable bindings
    ets:insert(State,{state,M#{parent => Visited,
			       bindings => NewBindings, v_name => []}}),
    %%io:format("State ~p, local state ~p~n",[ets:lookup_element(State,state,2),NewLocal]),
    eval(Code, State, NewLocal);

eval({prefix, Left, {call,Name,Args}=Right}, State, Local = #state{recursive = Recursive, exit_point_id = EPI}) ->
    M = ets:lookup_element(State, state, 2),
    Parents = ets:lookup_element(State,visited,2),
    %%io:format("VISITED ~p ~n",[Parents]),
    NewLocal = if Args == [] -> Local#state{use_var = false}; true -> Local#state{use_var = true} end,
    case lists:member(Name,Parents) of
	true ->
	    Rec = ets:lookup_element(procs_info, Name, 2),
	    ets:insert(State,{state,M#{rec => Rec}}),
	    eval(Left, State, NewLocal);
       false ->
	    eval(Left, State, NewLocal),
	    #{pc_value := Global} = ets:lookup_element(State, state, 2),
	    %%ets:insert(exit_point,{EPI,Global}),
	    eval(Right, State, Local#state{parent = [], entry = Global, sib = false, g_aware = [], p_action = false, aware = [], update = [], first_act = false})
    end;

%% prefix for nil process
eval({prefix, Left, nil}, State, Local) ->
    eval(Left, State, Local#state{next_is_nil = true});

%% prefix for other process
eval({prefix, Left, Right}, State, Local = #state{recursive = Recursive, exit_point_id = Name}) ->
    eval(Left, State, Local),
    %%io:format("Eval code prefix ~p ~p ~n, ",[Left,Right]),
    #{pc_value := Global} = ets:lookup_element(State, state, 2),
    if Recursive == true ->
	    stop;
       true ->
	   %% ets:insert(exit_point,{Name,[integer_to_list(Global)]}),
	    eval(Right, State, Local#state{parent = [], entry = Global, sib = false, g_aware = [], p_action = false, aware = [], update = [], first_act = false})
    end;

%% Recursion with aware and update
eval({p_awareness,Pred,{call,Name,_}=Code},State,Local) ->
    M = ets:lookup_element(State,state,2),
    #{code_def := Def, v_name := Vars, comp_index := I, arg_bindings := ArgBindings, b_name := Boundname, bound_index := BIndex} = M,
    Parents = ets:lookup_element(State,visited,2),
    NewState = case lists:member(Name,Parents) of
	true ->
	    Local#state{recursive = true};
       false ->
	    Local
    end,
    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    P = build_pred(local, Pred, I, Vars, Bound, Local#state.update,ArgBindings),
    eval(Code, State, NewState#state{aware = [P|NewState#state.aware]});

eval({p_update,Assingments,{call,Name,Args}=Code},State,Local) ->

    M = ets:lookup_element(State,state,2),
    #{code_def := Def,v_name := Vars, arg_bindings := ArgBindings, comp_index := I, b_name := Boundname, bound_index := BIndex} = M,
    Parents = ets:lookup_element(State,visited,2),
    NewState =
	case lists:member(Name,Parents) of
	    true ->
		Local#state{recursive = true};
	    false ->
		Local#state{recursive = halfway}
	end,
    NewLocal = if Args == [] -> NewState#state{use_var = false}; true -> NewState#state{use_var = true} end,
    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    A = build_assign(Assingments, I, Vars, Bound, Local#state.update, ArgBindings),
    eval(Code, State, NewLocal#state{update = NewState#state.update ++ A});

eval({p_awareness,Pred,Process},State,Local) ->
    M = ets:lookup_element(State,state,2),
    #{v_name := Vars, arg_bindings := ArgBindings, comp_index := I, b_name := Boundname, bound_index := BIndex} = M,
    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    %P = build_pred(local, Pred, I, Vars, Bound),
    %% term can appear in Vars (i.e., from input action, or from Args of process, or from previous update
    P = build_awarepred(Pred, I, Vars, Bound, Local#state.update, ArgBindings),
    eval(Process, State, Local#state{aware = [P|Local#state.aware]});

eval({p_update,Assingments,Process},State,Local) ->
    M = ets:lookup_element(State,state,2),
    #{v_name := Vars, comp_index := I, arg_bindings := ArgBindings, b_name := Boundname, bound_index := BIndex} = M,
    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    A = build_assign(Assingments, I, Vars, Bound, Local#state.update, ArgBindings),
    eval(Process, State, Local#state{update = Local#state.update ++ A});

eval({choice, Left, Right}, State, Local) ->
    #{pc_value := PcIndex} = ets:lookup_element(State,state,2),
    eval(Left, State, Local),
    #{pc_value := PcIndex1} = ets:lookup_element(State,state,2),
    eval(Right, State, Local);

%% eval({pchoice,{prefix,{poutput,Exp1,Pred1},Cs1},{prefix,{output,Exp2,Pred2},Cs2}}, State, Local = #state{recursive = Recursive}) ->
%%     % number of branches w.r.t priority choice of this component
%%     Pchoice = get(pchoice_id),
%%     if Pchoice == undefined ->
%% 	    put(pchoice_id,0);
%%        true -> put(pchoice_id,Pchoice+1)
%%     end,
%%     eval({prefix,{poutput,Exp1,Pred1},Cs1}, State, Local),
%%     eval({prefix,{poutput,Exp2,Pred2},Cs2}, State, Local);

%% Suport priority choice with awareness operator
%eval({pchoice,{g_awareness,GAware,Left},Right}, State, Local) ->
eval({pchoice,{g_awareness,GAware,{prefix,{output,Exp1,Pred1},Cs1}},{prefix,{output,Exp2,Pred2},Cs2}},State,Local) ->
    % number of branches w.r.t priority choice of this component
    Pchoice = get(pchoice_id),
    if Pchoice == undefined ->
	    put(pchoice_id,0);
       true ->
	    if Local#state.recursive == true ->
		    put(pchoice_id,0);
	       true ->
		    ok
	    end
    end,
    eval({prefix,{poutput,Exp1,Pred1},Cs1}, State, Local#state{g_aware = GAware}),
    eval({prefix,{output,Exp2,Pred2},Cs2}, State, Local#state{p_action = true});

eval({pchoice,{g_awareness,GAware,{prefix,{output,Exp1,Pred1},Cs1}},Right},State,Local) ->
    % number of branches w.r.t priority choice of this component
    Pchoice = get(pchoice_id),
    if Pchoice == undefined ->
	    put(pchoice_id,0);
       true ->
	    if Local#state.recursive == true ->
		    put(pchoice_id,0);
	       true ->
		    ok
	    end
    end,
    eval({prefix,{poutput,Exp1,Pred1},Cs1}, State, Local#state{g_aware = GAware}),
    eval(Right, State, Local#state{p_action = true});

eval({par, Left, {bang,{call,Name,_},_}=Right}, State, Local = #state{parent = Parent,entry = Val,sib = Sib}) ->
    Parents = ets:lookup_element(State,visited,2),
    [H|T] = Parents,
    %Sibbling = if Sib == false -> 0; true -> Sib+1 end,
    case lists:member(Name,Parents) of
	true ->
	    #{pc_value := Pvalue} = ets:lookup_element(State,state,2),
	    if Pvalue == 1 ->
		    %%disable sibling, use pc[1] != 1, pc[2] != 1 instead
	    	    %%eval({parroot,Left,Right},State,Local#state{sib = Sibbling});
		    eval({parroot,Left,Right},State,Local#state{sib = false});
	       true ->
		    %%eval({parbang,Left,Right},State,Local#state{sib =Sibbling});
		    eval({parbang,Left,Right},State,Local#state{sib =false})
	    end;
	false ->
	    ok
    end;

eval({parroot, Left, {bang,{call,Name,_},_} = Right}, State, Local = #state{parent = Parent, entry = Val, sib = Sib}) -> % spawn process with no prefix action is treated as a simpler case
    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),
    #{bound_index := BIndex, pc_index := PIndex, pc_name := Pcname}  =  Map,
    P2 = NumProcs,
    ets:insert(Root, {num_procs, P2+1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,visited,2),

    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State2 = ets:new(list_to_atom(Child2),[]),

    Process2 = Map#{pc_index := P2, bound_index := P2, pc_value := 1},

    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {visited, Parents}),

    App = get_apperance(Name,Parents),

    ParentEntry = if App > 1 -> []; true -> Parent end,
    ValEntry = if App > 1 -> 1; true -> Val end,
    %% ParentEntry = Parent,
    %% ValEntry = Val,
    eval(Left, State, Local#state{parent = ParentEntry,entry = ValEntry, update = []}),
    eval(Right, State2, Local#state{parent = ParentEntry,entry = ValEntry, update = [], aware = [Pcname++"["++integer_to_list(PIndex)++"]!=1" | Local#state.aware]});

eval({par, Left, Right}, State, Local=#state{entry = 1}) -> % spawn process with no prefix action is treated as a simpler case
    print("Parallel at root"),
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

    Process2 = Map#{pc_index := P2, bound_index := P2, pc_value := 1},

    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {visited, Parents}),


    eval(Left, State, Local),
    eval(Right, State2, Local);

eval({parbang, Left, {bang,_,_} = Right}, State, Local = #state{parent = Parent, sib = Sib}) ->
    print("Parallel with bang"),

    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),
    #{pc_name := Pcname, pc_value := Global, bound_index := BIndex, pc_index := PIndex}  =  Map,

    P1 = NumProcs,

    P2 = P1 + 1,
    ets:insert(Root, {num_procs, P2 + 1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,visited,2),
    Child1 = atom_to_list(ParentName) ++ integer_to_list(P1),
    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State1 = ets:new(list_to_atom(Child1),[]),
    State2 = ets:new(list_to_atom(Child2),[]),

    Process1 = Map#{pc_index := P1, bound_index := P1 , pc_value := 1},
    Process2 = Map#{pc_index := P2, bound_index := P2, pc_value := 1},
    ets:insert(State1, {state, Process1}),
    ets:insert(State1, {visited, Parents}),
    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {visited, Parents}),
    %% Entry1 = {[{Pcname, PIndex, Global} | Parent], 1, Sib},
    %% Entry2 = {[{Pcname, PIndex, Global} | Parent], 1, Sib},
    eval(Left, State1, Local#state{parent = [{Pcname, PIndex, Global} | Parent], entry = 1}),
    eval(Right, State2, Local#state{parent = [{Pcname, PIndex, Global} | Parent], aware = [Pcname++"["++integer_to_list(PIndex)++"]!=1" |Local#state.aware], entry = 1});

eval({par, Left, Right}, State, Local = #state{parent = Parent}) ->
    %%io:format("Normal parallel with parents ~p",[Parent]),
    Root = get(root),
    NumProcs = ets:lookup_element(Root,num_procs,2),

    Map = ets:lookup_element(State,state,2),
    #{pc_name := Pcname, pc_value := Global, bound_index := BIndex, pc_index := PIndex}  =  Map,

    P1 = NumProcs,

    P2 = P1 + 1,
    ets:insert(Root, {num_procs, P2 + 1}),

    ParentName = proplists:get_value(name,ets:info(State)),

    Parents = ets:lookup_element(State,visited,2),
    Child1 = atom_to_list(ParentName) ++ integer_to_list(P1),
    Child2 = atom_to_list(ParentName) ++ integer_to_list(P2),

    State1 = ets:new(list_to_atom(Child1),[]),
    State2 = ets:new(list_to_atom(Child2),[]),

    Process1 = Map#{pc_index := P1, bound_index := BIndex , pc_value := 1},
    Process2 = Map#{pc_index := P2, bound_index := BIndex + 1, pc_value := 1},
    ets:insert(State1, {state, Process1}),
    ets:insert(State1, {visited, Parents}),
    ets:insert(State2, {state, Process2}),
    ets:insert(State2, {visited, Parents}),
    %% Entry1 = {[{Pcname, PIndex, Global} | Parent], 1, false},
    %% Entry2 = {[{Pcname, PIndex, Global} | Parent], 1, false},
    eval(Left, State1, Local#state{parent = [{Pcname, PIndex, Global} | Parent] ,entry = 1, sib = false}),
    eval(Right, State2, Local#state{parent = [{Pcname, PIndex, Global} | Parent] ,entry = 1, sib = false});

eval({bang, {call,Name,_Args}=Body, Time}, State, Entry) ->
    Current = get(Name),
    Local = if (Time == 1 orelse Current == 2) ->
		    Entry#state{last_sib = true};
	       true -> Entry end,
    M = ets:lookup_element(State, state, 2),
    #{code_def := Def, pc_index := PIndex} = M,
    Test = case Current of
	       undefined ->
		   put(Name,Time);
	       0 -> 0;
	       _ ->
		   put(Name, Current - 1),
		   Current - 1
	   end,
    case Test of
	0 ->
	    erase(Name),
	    %%do not count this process
	    Root = get(root),
	    NumProcs = ets:lookup_element(Root,num_procs,2),
	    ets:insert(Root,{num_procs, NumProcs - 1}),
	    TotalPar = get(parchoice_id),
	    ParvectorName = atom_to_list(Def) ++ "par_vector",
	    ParVector = get(ParvectorName),
	    if TotalPar == undefined ->
		    put(ParvectorName,[Time+1|[0]]),
		    put(parchoice_id,Time+1);
	       true ->
		    put(ParvectorName,[TotalPar + Time + 1|ParVector]),
		    put(parchoice_id,TotalPar + Time + 1)
	    end,
	    io:format("par vector ~p~n",[get(ParvectorName)]),
	    eval(nil,State,Entry);
	_ ->
	    eval(Body, State, Local)
    end;
eval(nil, _, _) ->
    print("STOP");
eval(Act, State, Entry) ->
    create_trans(Act, State, Entry).

%% Behavioral mappings for two
create_trans({output, empty, empty}, State,
	     Local = #state{parent = Parent,
			    entry = Value,
			    sib = Sibbling,
			    update = Upd,
			    aware = Aware,
			    next_is_nil = Nil,
			    recursive = Recursive,
			    use_var = UseVar}) -> %% empty send ()@(ff)
    %%io:format("Translate an empty send whose first_act is ~p ~n",[Local#state.first_act]),
    Map = ets:lookup_element(State,state,2),
    #{rec := Rec, comp_index := SIndex, pc_name := Pcname, pc_value := Global, pc_index := PIndex, bound_index := BIndex, b_name := Boundname}  =  Map,
    Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n\t") ++ ";\n" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,
    Sib = if Sibbling == false -> "";true -> " and " ++ Pcname ++ "[" ++ integer_to_list(Sibbling) ++ "] != 1" end,
    Cond1 = build_pc_guard({Parent, {Pcname, PIndex, Value}}),
    Sname = "$2.s0",%++SIndex,

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    Guards1 = "\tallowsend(i)[receiving = false and i = " ++ SIndex ++ " and " ++  PAware  ++ Cond1 ++ Sib ++ "]/\n",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    Clear = if Nil == true -> "\n\t"++ Pc ++ " = 0; " ++ Bound ++ " := 0; --not used these variables\n\t"; true -> "" end,
    Clear2 = if UseVar == false -> Bound ++ " := 0; --not used these variables\n\t"; true -> "" end,
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
    NewMap = Map#{rec => {}, pc_value => Global+1},
    ets:insert(State, {state, NewMap}),
    Signal = " \n -----Empty Send ----- \n",
    Print = [Signal, Trans, Guards1, Assigns, Actions1],%, Trans, Guards2, Actions2],
    file:write_file("foo.umc", Print, [append]);

create_trans({output, Exps, Pred}, State,
	     Local=#state {parent = Parent,
			   entry = Value, sib = Sibbling, update = Upd, aware = Aware,
			   next_is_nil = Nil, recursive = Recursive, recstring = RecTest,
			  p_action = PAction, use_var = UseVar, last_sib = LastSib}) -> %normal send
    %%io:format("Translate action ~p@~p whose first_act is ~p, exit_point_id  = ~p, recursive = ~p ~n",[Exps,Pred,Local#state.first_act,Local#state.exit_point_id,Recursive]),
    Map = ets:lookup_element(State,state,2),
    #{rec := Rec, comp_index := SIndex, v_name := Vars, pc_name := Pcname, pc_value := Global, pc_index := PIndex, bound_index := BIndex, b_name := Boundname, arg_bindings := ArgBindings}  =  Map,
    TotalPar = get(parchoice_id),
    Padding = if TotalPar == undefined -> 0; true -> TotalPar end,
    {CurrentChoice, NextChoice} =
	if Sibbling =/= false ->
	   S1 = " and par[$1]["++integer_to_list(Sibbling+Padding) ++ "] = 1",
	   S2 = if LastSib == true -> "";
		   true ->
			"\n\tpar[$1]["++integer_to_list(Sibbling+1+Padding)++"] = 1;\n\t"
		end,
	   {S1,S2};
       true -> {"",""}
    end,
    CurrentPChoice =
	if PAction == true ->
	    ChoiceId = get(pchoice_id),
	    " and my[$1]["++integer_to_list(ChoiceId) ++ "] = 1";
	   true -> ""
	end,
    Assigns = if Upd == [] -> ""; true -> "\t" ++ string:join(Upd,";\n\t") ++ ";\n" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,
    Cond1 = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",
    Sname = "$2.s0",%++SIndex,

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    Guards1 = "\tallowsend(i)[receiving = false and i = " ++ SIndex ++ " and " ++  PAware  ++ Cond1 ++ CurrentChoice ++ CurrentPChoice ++ "]/\n",
    MsgList = build_outE(Exps,SIndex,Vars,Bound),
    Msg = "[" ++ string:join(MsgList,",") ++ "]",
    SndP = build_pred(local,Pred,SIndex,Vars,Bound,Upd,ArgBindings),
    %%% if there any membership predicate
    MPred = get_notmembership_predicate(),
    Selected = case MPred of
		   [] -> "target[j] := 1";
		   [Ele,Vec] -> "counter :int :=0; \n\tfor z in 0.."++Vec++".length-1 {if (" ++ Ele ++ " = " ++ Vec ++ "[z]) then { counter := counter +1;}};\n\t\tif (counter = 0) then {target[j]:=1;} else {target[j] := 0;}"
	       end,
    Target = "\ttarget:int[];\n\tfor j in 0..pc.length-1 {\n\t\tif " ++ SndP ++ " then \n\t\t\t{"++ Selected ++ "\n\t} else {target[j]:=0;}\n\t};\n",
    Output = "\treceiving=true;\n\tif target.length > 0 then { \n\t\tself.broadcast(target," ++ Msg ++ "," ++ SIndex ++ "); OUT.sending(id[$1],"++lists:nth(1,MsgList)++");\n\t\t",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",
    Clear = if Nil == true -> "\n\t"++ Pc ++ ":= 0; " ++ Bound ++ ":= 0; --not used these variables\n\t"; true -> "" end,
    Clear2 = if UseVar == false -> "\t"++ Bound ++ " = 0;\n"; true -> "" end,
    Guards2 = "\tbroadcast(tgt,msg,j)[" ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ "]/\n",
    #{parent := Parents} = Map,
    {RecStringTest,RecVal} = case Rec of
		    {} -> {integer_to_list(Global+2),Global+2}; % no process call or nil process
		    {SomeName, Pc, PIndex, MyVal} ->
			case SomeName == lists:nth(1,lists:reverse(Parents)) of
			    true -> {"1",Global+1};
			    false ->  {integer_to_list(MyVal),Global+1}
			end;
		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> {"1; " ++ Mypc ++ " = " ++  integer_to_list(MyVal),Global+1}; true -> {integer_to_list(Global+2),Global+2} end
		end,

    %% Recstring is different if there is Recursive from <pi>P or [a:=e]p
    %%io:format("previous exit point ~p~n",[ets:tab2list(exit_point)]),
    RecString = if  Recursive == false ->
			RecStringTest;
		    true ->
			AccI = ets:lookup_element(exit_point,Local#state.exit_point_id,2),
			%%io:format("AccI = ~p~n",[AccI]),
			ets:insert(exit_point,{Local#state.exit_point_id,
					       if AccI =/= [] -> lists:droplast(AccI);
						  true -> [] end}),

			if AccI =/= [] -> lists:last(AccI);
			    true -> RecStringTest
			end
		end,
    Actions1 = Target ++ Output ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ ";\n\t} else {\n\t\t" ++ NextChoice ++ Pc ++ " = " ++ RecString ++ ";\n\t\treceiving=false;\n\t\tself.allowsend(" ++ SIndex ++ ");\n\t" ++ Clear ++ Clear2 ++ "\t}\n}\n",
    Actions2 = "\treceiving=false;\n\tself.allowsend(" ++ SIndex ++ ");\n\t"
	++ Pc ++ " = "
	++ RecString ++ ";\n" ++ Clear ++ Clear2 ++ "}\n",
    NewMap = Map#{rec => {}, pc_value => if Recursive == true -> Global; true -> RecVal end},
    ets:insert(State, {state, NewMap}),

    Signal = " \n ----- Send ----- \n",
    Print = [Signal, Trans, Guards1, Assigns, Actions1, Trans, Guards2, Actions2],
    %%io:format("EXIT POINT ~p / GLOBAL ~p~n", [RecString,Global]),
    if Local#state.first_act == true andalso Recursive == false ->
	    %% NewKey = {element(1,Local#state.exit_point_id),element(1,Local#state.exit_point_id),element(1,Local#state.exit_point_id),RecString},
	    Acc = ets:lookup_element(exit_point,Local#state.exit_point_id,2),
	    %%io:format("Gonna concat RecString ~p with Acc ~p ~n",[RecString,Acc]),
	    ets:insert(exit_point,{Local#state.exit_point_id,[RecString|Acc]});
       true -> ok
    end,
    %%io:format("updated exit point ~p~n",[ets:lookup_element(exit_point,Local#state.exit_point_id,2)]),
    file:write_file("foo.umc", Print, [append]);

create_trans({poutput, Exps, Pred}, State,
	     Local = #state{parent = Parent,
		  entry = Value,
		  sib = Sibbling, last_sib = LastSib, update = Upd, aware = Aware, next_is_nil = Nil,
	    g_aware = GAware, p_action = PAction, use_var = UseVar, first_act = FirstAct}) -> %send and check if it is succesful
    Map = ets:lookup_element(State,state,2),
    #{rec := Rec, comp_index := SIndex, v_name := Vars, pc_name := Pcname, pc_value := Global, pc_index := PIndex, bound_index := BIndex, b_name := Boundname, arg_bindings := ArgBindings}  =  Map,
    %%io:format("Priority Send with ~p~n",[GAware]),

    ChoiceId = get(pchoice_id),
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
    Clear = if Nil == true -> "\n\t"++ Pc ++ ":= 0; " ++ Bound ++ ":= 0; --not used these variables\n\t"; true -> "" end,
    Clear2 = if UseVar == false -> "\t"++ Bound ++ ":= 0; --not used these variables\n\t"; true -> "" end,
    Sname = "$2.s0",%++SIndex,

    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    Guards1 = "\tallowsend(i)[receiving = false and i = " ++ SIndex ++ " and " ++  PAware  ++ Cond1 ++ " and " ++ CurrentChoice ++ Sib ++ "]/\n",
    MsgList = build_outE(Exps,SIndex,Vars,Bound),
    Msg = "[" ++ string:join(MsgList,",") ++ "]",
    SndP = build_pred(local,Pred,SIndex,Vars,Bound,Upd,ArgBindings),
    GlobalAware = build_pred(local,GAware,SIndex,Vars,Bound,Upd,ArgBindings),

    %%% if there any membership predicate
    MPred = get_notmembership_predicate(),
    Selected = case MPred of
		   [] -> "target[j] := 1";
		   [Ele,Vec] -> "counter :int :=0; \n\t\t\tfor z in 0.."++Vec++".length-1 {if (" ++ Ele ++ " = " ++ Vec ++ "[z]) then { counter := counter +1;}};\n\t\t\tif (counter = 0) then {target[j]:=1;} else {target[j] := 0;}"
	       end,

    TestGlobal = "\ttarget:int[];\n\tfor j in 0..pc.length-1 {\n\t\tif " ++ GlobalAware ++ " then {\n\t\t\t"++ Selected ++ "\n\t\t} else {target[j]:=0;}\n\t};\n",
    StartResults = "\tif target.length > 0 then {\n\t\ttarget:=[];",
    EndResults = "\t} else {\n\t\t" ++ NextChoice ++ Pc ++ " = " ++ integer_to_list(Value) ++ ";\n\t\tself.allowsend(" ++ SIndex ++ ");\n\t" ++ Clear ++ Clear2 ++ "}\n}\n",

    Target = "\t\n\t\tfor j in 0..pc.length-1 {\n\t\tif " ++ SndP ++ " then {\n\t\t\t"++ Selected ++ "\n\t\t\t} else {target[j]:=0;}\n\t\t};\n",
    Output = "\t\treceiving=true;\n\t\tif target.length > 0 then {\n\t\t\tself.broadcast(target," ++ Msg ++ "," ++ SIndex ++ ");OUT.sending(id[$1],"++lists:nth(1,MsgList)++");\n\t\t\t",
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
    Actions1 = Target ++ Output ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ ";\n\t\t} else {\n\t\t\t"++ Pc ++ " = " ++ RecString ++ ";\n\t\t\treceiving=false;\n\t\t\tself.allowsend(" ++ SIndex ++ ");\n\t\t" ++ Clear ++ Clear2 ++ "}\n",
    Guards2 = "\tbroadcast(tgt,msg,j)[" ++ Pc ++ " = " ++ integer_to_list(Global + 1) ++ "]/\n",
    Actions2 = "\treceiving=false;\n\tself.allowsend(" ++ SIndex ++ ");\n\t"
	++ Pc ++ " = "
	++ RecString ++ ";\n" ++ Clear ++ Clear2 ++ "}\n",
    NewMap = Map#{rec => {}, pc_value => RecVal},
    ets:insert(State, {state, NewMap}),
    Signal = " \n ----- Send ----- \n",
    Print = [Signal, Trans, Guards1, TestGlobal, StartResults, Assigns, Actions1, EndResults, Trans, Guards2, Actions2],
    file:write_file("foo.umc", Print, [append]);


create_trans({input, Pred, Vars}, State,
	     Local = #state{parent = Parent, entry = Value, sib = Sibbling,last_sib = LastSib,
		    update = Upd, aware = Aware, next_is_nil = Nil, use_var = UseVar,
		    recursive = Recursive, first_act = FirstAct}) ->
    Map = ets:lookup_element(State,state,2),
    #{rec := Rec, comp_index := SIndex, b_name := Boundname, bound_index := BIndex, pc_name := Pcname, pc_value := Global, pc_index := PIndex, arg_bindings := ArgBindings}  =  Map,
    TotalPar = get(parchoice_id),
    Padding = if TotalPar == undefined -> 0; true -> TotalPar end,
    {CurrentChoice, NextChoice} =
	if Sibbling =/= false ->
	   S1 = " and par[$1]["++integer_to_list(Sibbling+Padding) ++ "] = 1",
	   S2 = if LastSib == true -> "";
		   true ->
			"par[$1]["++integer_to_list(Sibbling+1+Padding)++"] = 1; -- next parallel branch \n\t"
		end,
	   {S1,S2};
       true -> {"",""}
    end,
    Assigns = if Upd == [] -> ""; true -> string:join(Upd,";\n") ++ ";\n\t" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,

    Cond = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",

    VIndex = lists:seq(0,length(Vars) - 1),
    Vars1 = lists:zip(Vars,VIndex),
    %% build mapping for variables
    Vars2 = [Bound ++ "[" ++ integer_to_list(X) ++ "]" || X <- VIndex],
    Vars3 = lists:zip(Vars,Vars2),

    Received = "OUT.received(id["++ SIndex ++ "],msg[0],msg[1]);\n\t",
    %Sname = "$2.s"++SIndex,
    Sname = "$2.s0",
    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    RcvP = build_recvpred(remote,Pred,SIndex,Vars1++ArgBindings,Bound,Upd),
    %%io:format("Input action ~p@~p, Bindinsg = ~p, use_var= ~p, Nil = ~p~n",[Pred,Vars,Vars3,UseVar,Nil]),
    AllowedRcv = "tgt[" ++ SIndex ++ "] = 1 and ",
    Guards = "\tbroadcast(tgt,msg,j)[" ++ AllowedRcv ++ PAware ++ RcvP ++ " and " ++ Cond ++ CurrentChoice ++ "]/\n\t",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",

    Clear = if Nil == true -> "\n\t"++ Pc ++ ":= 0; " ++ Bound ++ ":= 0;"; true -> "" end,
    Clear2 = if Nil == false andalso UseVar == false -> Bound ++ ":= 0; -- not use these variables \n\t"; true -> "" end,
    #{parent := Parents} = Map,
    RecStringTest = case Rec of
		    {} -> integer_to_list(Global+1); % no process call or nil process
		    {SomeName, Pc, PIndex, MyVal} ->
			case SomeName == lists:nth(1,lists:reverse(Parents)) of
			    true -> "1";
			    false ->  integer_to_list(MyVal)
			   %integer_to_list(Global+2)
			end;
		    {_Somename,Mypc, MyIndex, MyVal} -> if MyIndex < PIndex -> "1" ++ ";\n\t" ++ Mypc ++ " = " ++  integer_to_list(MyVal); true -> integer_to_list(Global+1) end
		end,
    %%io:format("previous exit point ~p~n",[ets:tab2list(exit_point)]),
    RecString = if  Recursive == false ->
			RecStringTest;
		    true ->
			AccI = ets:lookup_element(exit_point,Local#state.exit_point_id,2),
			%%io:format("AccI = ~p~n",[AccI]),
			ets:insert(exit_point,{Local#state.exit_point_id,
					       if AccI =/= [] -> lists:droplast(AccI);
						  true -> [] end}),

			if AccI =/= [] -> lists:last(AccI);
			    true -> RecStringTest
			end
		end,
    Actions = Received ++ Bound ++ " = msg;\n\t" ++ NextChoice ++ Pc ++ " = " ++ RecString ++ ";" ++ Clear ++ Clear2 ++"\n}\n",
    Signal = " \n ----- Receive ----- \n",
    Print = [Signal,Trans,Guards, Assigns,Actions],
    NewMap =  Map#{rec => {}, v_name => Vars1, bindings => Vars3, pc_value => Global + 1},
    ets:insert(State, {state, NewMap}),
    %%io:format("EXIT POINT ~p / GLOBAL ~p~n", [RecString,Global]),
    if Local#state.first_act == true andalso Recursive == false ->
	    %% NewKey = {element(1,Local#state.exit_point_id),element(1,Local#state.exit_point_id),element(1,Local#state.exit_point_id),RecString},
	    Acc = ets:lookup_element(exit_point,Local#state.exit_point_id,2),
	    %%io:format("Gonna concat RecString ~p with Acc ~p ~n",[RecString,Acc]),
	    ets:insert(exit_point,{Local#state.exit_point_id,[RecString|Acc]});
       true -> ok
    end,
    %%io:format("updated exit point ~p~n",[ets:lookup_element(exit_point,Local#state.exit_point_id,2)]),
    file:write_file("foo.umc", Print, [append]);

%% Inplace update at input action
create_trans({inplace_input, Pred, Inplace, Vars}, State,
	     #state{parent = Parent, entry = Value, sib = Sibbling,last_sib = LastSib,
		    update = Upd, aware = Aware, next_is_nil = Nil, use_var = UseVar}) ->
    Map = ets:lookup_element(State,state,2),
    #{rec := Rec, comp_index := SIndex, b_name := Boundname, bound_index := BIndex, pc_name := Pcname, pc_value := Global, pc_index := PIndex, arg_bindings := ArgBindings}  =  Map,
    TotalPar = get(parchoice_id),
    Padding = if TotalPar == undefined -> 0; true -> TotalPar end,
    {CurrentChoice, NextChoice} =
	if Sibbling =/= false ->
	   S1 = " and par[$1]["++integer_to_list(Sibbling+Padding) ++ "] = 1",
	   S2 = if LastSib == true -> "";
		   true ->
			"par[$1]["++integer_to_list(Sibbling+1+Padding)++"] = 1; -- next parallel branch \n\t"
		end,
	   {S1,S2};
       true -> {"",""}
    end,
    A = build_inplace_update(Inplace, SIndex, Vars),

    Assigns = if Upd == [] -> string:join(A,";\n") ++ ";\n\t"; true -> string:join(A,";\n") ++ ";\n\t" ++ string:join(Upd,";\n") ++ ";\n\t" end,
    PAware = if Aware == [] -> ""; true -> string:join(Aware," and ") ++ " and " end,


    Cond = build_pc_guard({Parent, {Pcname, PIndex, Value}}),

    Bound = Boundname ++ "[" ++ integer_to_list(BIndex) ++ "]",

    VIndex = lists:seq(0,length(Vars) - 1),
    Vars1 = lists:zip(Vars,VIndex),
    %% build mapping for variables
    Vars2 = [Bound ++ "[" ++ integer_to_list(X) ++ "]" || X <- VIndex],
    Vars3 = lists:zip(Vars,Vars2),

    Received = "OUT.received(id["++ SIndex ++ "],msg[0],msg[1]);\n\t",
    %Sname = "$2.s"++SIndex,
    Sname = "$2.s0",
    Trans = "SYS."++Sname ++ " -> " ++ Sname ++ " {\n",
    RcvP = build_recvpred(remote,Pred,SIndex,Vars1++ArgBindings,Bound,Upd),

    AllowedRcv = "tgt[" ++ SIndex ++ "] = 1 and ",
    Guards = "\tbroadcast(tgt,msg,j)[" ++ AllowedRcv ++ PAware ++ RcvP ++ " and " ++ Cond ++ CurrentChoice ++ "]/\n\t",
    Pc = Pcname ++ "[" ++ integer_to_list(PIndex) ++ "]",

    Clear = if Nil == true -> "\n\t"++ Pc ++ ":= 0; " ++ Bound ++ ":= 0;"; true -> "" end,
    Clear2 = if Nil == false andalso UseVar == false -> Bound ++ ":= 0; -- not use these variables \n\t"; true -> "" end,
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
    Actions = Received ++ Bound ++ " = msg;\n\t" ++ NextChoice ++ Pc ++ " = " ++ RecString ++ ";" ++ Clear ++ Clear2 ++"\n}\n",
    Signal = " \n ----- Receive ----- \n",
    Print = [Signal,Trans,Guards, Assigns,Actions],
    NewMap =  Map#{rec => {}, v_name => Vars1, bindings => Vars3, pc_value => Global + 1},
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
%% nice parallelism, does not work because of interfere
build_parent([{Pcname,P,par}|T],L) ->
    String = string:join([Pcname ++ "[" ++ integer_to_list(X) ++ "] != 1" || X <- lists:seq(0,P-1)]," and "),
    build_parent(T,[String|L]);
%% normal way  works
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


build_par_list(List) ->
    build_par_list(List,[]).

build_par_list([],Acc) ->
    io:format("PAR LIST ~p~n",[Acc]),
    "[" ++ string:join(Acc,",") ++ "]";
build_par_list([H|T],Acc) ->
    String =
	if length(H) =< 1 -> "[1]"; %% only one parallle |^, simply set the first par[$1] to 1
	   true -> %% set more 1s
		H1 = lists:droplast(lists:reverse(H)),
		%%print(H1),
		S = lists:map(fun(X) ->
				      case lists:member(X,H1) of
					  true ->
					      "1";
					  false ->
					      "0"
				      end
			      end,
			      lists:seq(0,lists:max(H1))),
		"[" ++ string:join(S,",") ++ "]"
	end,
    build_par_list(T,[String|Acc]).


%% build_sndpred(Type,Pred,I,Vars,Bound) ->
%%      "(" ++ eval1(Type,Pred,I,Vars,Bound) ++ ")".
%% build_rcvpred(Pred,I,Vars) ->
%%     "("++eval2(Pred,I,Vars)++")".
build_outE(Exps,I, Vars, Bound) ->
    eval3(Exps, I, [],Vars,Bound).
build_pred(Type, Pred, I, Vars,Bound,U,A) ->
    L = "("++eval1(Type, Pred, I, Vars++A,Bound, U)++")",
    re:replace(L, ":int", "", [global, {return, list}]).

build_recvpred(Type, Pred, I, V,B,U) ->
    %%io:format("Build Receving predicate ~p~n with Vars ~p Bound ~p Update ~p~n",[Pred,V,B,U]),
    A = [re:replace(Z, ":int", "", [global, {return, list}]) || Z <- U],
    U1 = [re:split(X," := ",[{return, list}]) || X <- A],
    U2 = [{X,Y} || [X,Y] <- U1],
    List = "("++eval1(Type, Pred, I, V,B,U2)++")",
    MPred = get_notmembership_predicate(),
    Member = case MPred of [L,R] ->
		     Temp = [L ++ "!=" ++R++"["++integer_to_list(Int)++"]" || Int <- lists:seq(0,7)],
		     " and " ++ string:join(Temp, " and ");
		     [] -> "" end,
    re:replace(List++Member, ":int", "", [global, {return, list}]).


build_awarepred(Pred, I, V, B, U, Args) ->
    A = [re:split(X," := ",[{return, list}]) || X <- U],
    U2 = [{X,Y} || [X,Y] <- A],
    List = "("++evala(Pred, I, V++Args, B, U2)++")".

build_assign(Assignments,I,V,B,U,Args) ->
    %%io:format("Build update commands ~p~n with Vars ~p Bound ~p (comp index = ~p) ~n",[Assignments,V,B,I]),
    %% Clean dynamic variables created before
    erase(dynamic_vars),
    evalu(Assignments,I,[],V,B,U,Args).

build_inplace_update(Assignments,I,Msg) ->
    eval_inplace_u(Assignments,I,Msg,[]).


eval_inplace_u([],_,_,Acc) -> lists:reverse(Acc);
eval_inplace_u([H|T], I, Msg, Acc) ->
    Temp = eval1(inplace,H,I,Msg,[],[]),
    eval_inplace_u(T,I,Msg,[Temp|Acc]).


evalu([],_,S,_,_,_,_) -> lists:reverse(S);
evalu([H|T], I, S, V,B,U,A) ->
    %%io:format("Build update for ~p~n with Vars ~p Bound ~p args = ~p) ~n",[H,V,B,A]),
    Temp = eval1(local,H,I,V++A,B,U),
    evalu(T,I,[Temp|S],V,B,U,A).


eval1(Type, {parenthesis,Pred}, I, Vars, Bound, U) ->
    "(" ++ eval1(Type,Pred,I,Vars, Bound, U) ++ ")";
eval1(Type, {bracket,Exp}, I, Vars, Bound, U) ->
    "[" ++ eval1(Type,Exp,I,Vars, Bound, U) ++ "]";
eval1(Type,{head,Name}, I,Vars, Bound, U) -> eval1(Type,Name,I,Vars, Bound, U) ++ ".head";
eval1(Type,{tail,Name}, I,Vars, Bound, U) -> eval1(Type,Name,I,Vars, Bound, U) ++ ".tail";
%% NEED TO REVIEW
%% this is for selector of remote attributes, e.g, a[i]
eval1(Type,{selector,List,Index}, I,Vars, Bound, U) -> eval1(Type,List,I,Vars, Bound, U) ++ "[" ++ eval1(Type,Index,I,Vars, Bound, U) ++ "]";
eval1(_,"true", _,_,_,_) -> "true";
eval1(_,"false", _,_,_,_) -> "false";
eval1(_,{att,Att}, _,_,_,_) -> Att ++ "[j]";
eval1(_,{self,Att}, I, _,_,U) ->
    Left = Att ++ "[" ++ I ++ "]",
    R = proplists:get_value(Left,U),
    if R == undefined -> Left; true -> R end;

eval1(_,{const,C}, _,_,_,_) -> C;
eval1(_,[], _,_,_,_) -> "[]";
eval1(_,{token,T}, _,_,_,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
eval1(Type,[{self,Att}=Term], I, Vs, Bound,U) ->
    "[" ++ eval1(Type,Term, I, Vs, Bound,U) ++ "]";

eval1(local,[{var,Name}], _, Vs, Bound,U) ->
    I1 = proplists:get_value(Name,Vs),
    case I1 of
	undefined ->
	    "[" ++ get_var_name(Name) ++ "]";
	Int when is_integer(Int)->
	    "[" ++ Bound ++ "["++integer_to_list(Int)++"]]";
	Other -> "[" ++ Other ++ "]"
    end;

eval1(local,[H|T]=List,I,Vs,B,U) when T =/= [] ->
    S = [eval1(local,Name,I,Vs,B,U) || Name <- List],
    io:format("S ~p~n",[S]),
    "[" ++ string:join(S,",") ++ "]";

eval1(local,{var,Name}, _, Vs,Bound,U) ->
    I1 = proplists:get_value(Name,Vs),
    case I1 of
	undefined ->
	    get_var_name(Name);
	Int when is_integer(Int)->
	    Bound ++ "["++integer_to_list(Int) ++ "]";
	Other -> Other
    end;
eval1(remote,{var,Name}, _, Vars,_,U) ->
    I1 = proplists:get_value(Name,Vars++U),
    if is_integer(I1) -> "msg["++integer_to_list(I1)++"]";
       true  -> I1
    end;


eval1(inplace,{var,Name}, _, Msg,_,_) ->
    Vars = lists:zip(Msg,lists:seq(0,length(Msg)-1)),
    I1 = proplists:get_value(Name,Vars),
    if is_integer(I1) -> "msg["++integer_to_list(I1)++"]";
       true  -> I1
    end;

eval1(inplace,[{var,Name}], _, Msg,_,_) ->
    Vars = lists:zip(Msg,lists:seq(0,length(Msg)-1)),
    I1 = proplists:get_value(Name,Vars),
    if is_integer(I1) -> "[msg["++integer_to_list(I1)++"]]";
       true  -> I1
    end;
eval1(inplace,[H|T]=List,I,Msg,Foo,Bar) when T =/= [] ->
    %% S = [eval1(inplace,Name,I,Msg,Foo,Bar) || Name <- List],
    %% "[" ++ string:join(S,",") ++ "]";
    %% Dueto m4 macro, need to fix
    "msg";


eval1(Type,{concat,{_,LName}=Left,[{_,E}]=Right}, I,Vars, Bound, U) ->
    LHS = eval1(Type,Left,I,Vars, Bound, U),
    RHS = eval1(Type,Right,I,Vars, Bound, U),
    LHSH = LHS ++ "[v1]",
    LHST = LHS ++ "[v2]",
    Sort =
	if LName == E ->
	  ";\n\t if " ++ LHS ++ ".length > 1 then {
      for v1 in 0.."++ LHS ++".length - 1 {
      for v2 in v1+1.." ++ LHS ++ ".length-1 {
      if "++LHSH++" > "++LHST++" then {
        temp:int := "++LHSH++";"
        ++LHSH++":="++LHST++";"
        ++LHST++":=temp;}}
      }}"; true -> "" end,
    LHS ++ "+" ++ RHS ++ Sort;

eval1(Type,{concat,Left,Right}, I,Vars, Bound, U) -> eval1(Type,Left,I,Vars, Bound, U) ++ "+"  ++ eval1(Type,Right,I,Vars, Bound, U);
eval1(Type,{subtract,{_,LName}=Left,[{_,E}=V]}, I,Vars, Bound, U) ->
    LHS = eval1(Type,Left,I,Vars, Bound, U),
    LHSH = LHS ++ ".head",
    LHST = LHS ++ ".tail",
    C = eval1(Type,V,I,Vars, Bound, U),
    LHSH1 = LHS ++ "[v1]",
    LHST1 = LHS ++ "[v2]",
    Sort =  if LName  == E ->
       ";\n\tif " ++ LHS ++ ".length > 1 then {
      for v1 in 0.."++ LHS ++".length - 1 {
      for v2 in v1+1.." ++ LHS ++ ".length-1 {
      if "++LHSH1++" > "++LHST1++" then {
        temp:int := "++LHSH1++";"
        ++LHSH1++":="++LHST1++";"
        ++LHST1++":=temp;}}
      }}"; true -> "" end,

    UmCcode = %% stupid LHS here but works
     LHS++";\n\ttmp :obj:= [];
         while " ++ LHS ++" != [] {
           if ("++LHSH++" != "++C++") then {tmp := tmp + ["++LHSH++"];  " ++ LHS ++ ":= " ++LHST++"; }
           else {"++LHS ++ ":= "++LHST++";}
         };
        "++LHS++" := tmp" ++ Sort;

eval1(Type,{subtract,Left,Right}, I,Vars, Bound, U) ->
    eval1(Type,Left,I,Vars, Bound, U) ++ "-"  ++ eval1(Type,Right,I,Vars, Bound, U);
eval1(Type,{assign, Left, Right}, I, Vars, Bound, U) ->
    eval1(Type,Left, I,Vars, Bound, U) ++ " := " ++ eval1(Type,Right, I, Vars, Bound, U);
eval1(Type,{eq, Left, Right}, I, Vars, Bound, U) ->
    eval1(Type,Left, I,Vars, Bound, U) ++ " = " ++ eval1(Type,Right, I, Vars, Bound, U);
eval1(Type,{diff, Left, Right}, I, Vars, Bound, U) ->
    eval1(Type,Left, I,Vars, Bound, U) ++ " != " ++ eval1(Type,Right, I, Vars, Bound, U);
eval1(Type,{ge, Left, Right}, I, Vars, Bound, U) ->
    eval1(Type,Left, I,Vars, Bound, U) ++ " > " ++ eval1(Type,Right, I, Vars, Bound, U);
eval1(Type,{le, Left, Right}, I, Vars, Bound, U) ->
    eval1(Type,Left, I,Vars, Bound, U) ++ " < " ++ eval1(Type,Right, I, Vars, Bound, U);
eval1(Type,{intersect, Left, Right}, Index, Vars, Bound, U) ->
    eval1(Type,Left, Index, Vars, Bound, U) ++ " and " ++ eval1(Type,Right, Index, Vars, Bound, U);
eval1(Type,{union, Left, Right}, Index, Vars, Bound, U) ->
    eval1(Type,Left, Index, Vars, Bound, U) ++ " or " ++ eval1(Type,Right, Index, Vars, Bound, U);
eval1(Type,{notmember, Left, Right}, Index, Vars, Bound, U) ->
    L= eval1(Type,Left, Index, Vars, Bound, U),
    R = eval1(Type,Right, Index, Vars, Bound, U),
    put(notmember,[L,R]),
    "true";
eval1(Type,{ismember, Left, Right}, Index, Vars, Bound, U) ->
    L= eval1(Type,Left, Index, Vars, Bound, U),
    R = eval1(Type,Right, Index, Vars, Bound, U),
    Temp = [L ++ "=" ++R++"["++integer_to_list(Int)++"]" || Int <- lists:seq(0,7)],
    Member = "(false or " ++ string:join(Temp, " or ") ++ ")",
    re:replace(Member, ":int", "", [global, {return, list}]);

eval1(Type,{negation, Right}, Index, Vars, Bound, U) ->
    " not " ++ eval1(Type,Right, Index, Vars, Bound, U).

eval3([],_,S, _,_) -> %
    %"[" ++ string:join(lists:reverse(S),",") ++ "]";
    lists:reverse(S);
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


%% evalaware([],_,_,_,_,Acc) -> lists:reverse(Acc);
%% evalaware([H|T], I, Vars,Bound,PreUpdate,Acc) ->
%%     Temp = evala(H,I,Vars,Bound,PreUpdate),
%%     evalaware(T,I,Vars,Bound,PreUpdate,[Temp|Acc]).

evala({parenthesis,P},I,B,V,U) ->
    "(" ++ evala(P,I,V,B,U) ++ ")";
evala({bracket,E}, I, V,B,U) ->
    "[" ++ evala(E,I,V,B,U) ++ "]";
evala({head,Name}, I,V,B,U) -> evala(Name,I,V,B,U) ++ ".head";
evala({tail,Name}, I,V,B,U) -> evala(Name,I,V,B,U) ++ ".tail";
evala({selector,List,Index}, I,Vars,Bound,U) -> evala(List,I,Vars,Bound,U) ++ "[" ++ evala(Index,I,Vars,Bound,U) ++ "]";
evala("true", _,_,_,_) -> "true";
evala("false", _,_,_,_) -> "false";
evala({self,Att}, I, _,_,U) ->
    Left = Att ++ "[" ++ I ++ "]",
    R = proplists:get_value(Left,U),
    if R == undefined -> Left; true -> R end;

evala({att,Att}, _,_,_,_) -> Att ++ "[j]";
evala({const,C}, _,_,_,_) -> C;
evala([], _,_,_,_) -> "[]";
evala({token,T}, _,_,_,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
%% evala([{var,Name}|T]=List1, _, Vars, Bound,U) ->
%%     %% List2 = [proplists:get_value(X,Vars) || {var,X} <- List1],
%%     %% S = [Bound ++ "["++integer_to_list(I1)++"]" || I1 <- List2],
%%     %% string:join(S,",");
%%     "[" ++ Bound ++ "]";
evala({var,Name}, _, Vars, Bound,_) ->
    I1 = proplists:get_value(Name,Vars),
    case I1 of
	undefined ->
	    get_var_name(Name);
	Int when is_integer(Int)->
	    Bound ++ "["++integer_to_list(Int) ++ "]";
	Other -> Other
    end;
evala({concat,Left,Right}, I,Vars,Bound,U) -> evala(Left,I,Vars,Bound,U) ++ "+"  ++ evala(Right,I,Vars,Bound,U);
evala({assign, Left, Right}, I, Vars,Bound,U) ->
    evala(Left, I,Vars,Bound,U) ++ " := " ++ evala(Right, I, Vars,Bound,U);
evala({eq, Left, Right}, I, Vars,Bound,U) ->
    evala(Left, I,Vars,Bound,U) ++ " = " ++ evala(Right, I, Vars,Bound,U);
evala({diff, Left, Right}, I, Vars,Bound,U) ->
    evala(Left, I,Vars,Bound,U) ++ " != " ++ evala(Right, I, Vars,Bound,U);
evala({ge, Left, Right}, I, Vars,Bound,U) ->
    evala(Left, I,Vars,Bound,U) ++ " > " ++ evala(Right, I, Vars,Bound,U);
evala({le, Left, Right}, I, Vars,Bound,U) ->
    evala(Left, I,Vars,Bound,U) ++ " < " ++ evala(Right, I, Vars,Bound,U);
evala({intersect, Left, Right}, Index, Vars,Bound,U) ->
    evala(Left, Index, Vars,Bound,U) ++ " and " ++ evala(Right, Index, Vars,Bound,U);
evala({union, Left, Right}, Index, Vars,Bound,U) ->
    evala(Left, Index, Vars,Bound,U) ++ " or " ++ evala(Right, Index, Vars,Bound,U);
evala({notmember, Left, Right}, Index, Vars,Bound,U) ->
    L= evala(Left, Index, Vars,Bound,U),
    R = evala(Right, Index, Vars,Bound,U),
    Temp = [L ++ "!=" ++R++"["++integer_to_list(Int)++"]" || Int <- lists:seq(0,7)],
    Member = "(" ++ string:join(Temp, " and ") ++ ")",
    re:replace(Member, ":int", "", [global, {return, list}]);

evala({ismember, Left, Right}, Index, Vars,Bound,U) ->
    L= evala(Left, Index, Vars,Bound,U),
    R = evala(Right, Index, Vars,Bound,U),
    Temp = [L ++ "=" ++R++"["++integer_to_list(Int)++"]" || Int <- lists:seq(0,7)],
    Member = "(false or " ++ string:join(Temp, " or ") ++ ")",
    re:replace(Member, ":int", "", [global, {return, list}]);

evala({negation, Right}, Index, Vars,Bound,U) ->
    " not " ++ evala(Right, Index, Vars,Bound,U).




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
  M = get(ismember),
  if M == undefined ->  [];
     true -> erase(ismember),M
  end.

get_notmembership_predicate() ->
  M = get(notmember),
  if M == undefined ->  [];
     true -> erase(notmember),M
  end.
get_var_name(Name) ->
  M = get(dynamic_vars),
  if M == undefined ->
	  %% detech umc varibales
	  case string:str(Name,"umc") of
	      1 -> Name -- "umc";
	      0 ->
		  put(dynamic_vars,[{Name,Name}]),
		  Name ++ ":int"
	  end;
     true ->
	  case lists:keyfind(Name,1,M) of
	      false ->
		  case string:str(Name,"umc") of
		      1 -> Name -- "umc";
		      0 ->
			  put(dynamic_vars,[{Name,Name}|M]),
			  Name ++ ":int"
		  end;
	      {Name,Name} -> Name
	  end
  end.
get_apperance(E,List) ->
    lists:sum([1 || X <- List, X == E]).

remove_dups([])    -> [];
remove_dups([{Fi,Se,Th,_}=H|T]) -> [H | [X || {Fi1,Se1,Th1,_}=X <- remove_dups(T), {Fi1,Se1,Th1} /= {Fi,Se,Th}]].

filter_bindings(Vars,Bindings) ->
    %% simplest case, Vars \in Bindings
    Name = [X || {var,X} <- Vars],
    L = [{X,proplists:get_value(X,Bindings)} || X <- Name].

select_bindings(Args,Bindings) ->
    Vals = [X || {_,X} <- Bindings],
    lists:zip(Args,Vals).

build_observation(L) ->
    S = ["partner["++integer_to_list(I)++"] != 0" || I <- lists:seq(0,L-1)],
    "State " ++ string:join(S, " and ") ++ "  -> completeness".
