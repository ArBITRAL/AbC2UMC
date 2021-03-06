Nonterminals lines line subsystem system process assignments
assignment action rpred spred apred expr vars arg_list arg_def_list
att_list att_init pcall init_list compinit compcall p_expr op_expr exprs.

Terminals
	'+' '-' '++' '--' '(' ')' '>' '<' '/=' '>=' '<=' '=' ':' ':=' '::=' 'and' 'or' 'not' '|' '||' '.' ',' '|^' '@' '[' ']' '{' '}' '->' '=>' 'notin' 'in' '*' '/'
	int self atom true false tt ff name literal func param 'component' 'attributes' 'observables' 'behaviour' 'let' 'init' 'end' 'hd' 'tl' 'min' 'max' 'nil' 'SYS' 'umc'.

Rootsymbol lines.

Left 1 '|^'.
Right 2 '|'.
Left 3 '+' '-' '++' '--'.
Left 4 '*' '/' '.' '>' '<' '[' ']'.
%Left 5 '_'.
Left 5 'or'.
Left 6 'and'.
Right 7 'not'.
Left 8 '/=' '>=' '<=' '='.

lines -> line lines : ['$1' | '$2'].
lines -> line : ['$1'].

% add the support of writing umc code which is helpful some difficulties in modelling complex operations (sort, max, min)
line -> 'umc' '.' : umc_code.
%
line -> 'component' name lines 'end' : {comp, v('$2'), '$3'}.
line -> 'attributes' ':' att_list : {attrs, '$3'}.
line -> 'observables' ':' att_list : {obsrs, '$3'}.
line -> 'behaviour' ':' 'let' '{' lines '}' 'init' process : {beh, '$5', {init_beh, '$8'}}.
line -> name ':' compinit : {comp_init, v('$1'), '$3'}.

compinit -> name : {comp, v('$1'), []}.
compinit -> name '(' init_list ')' : {comp, v('$1'), '$3'}.

init_list -> att_init : ['$1'].
init_list -> att_init ',' init_list : ['$1' | '$3'].

att_init -> literal '->' expr : {v('$1'),'$3'}.
att_init -> literal '=' expr : {v('$1'),'$3'}.
att_init -> literal '=>' expr : {v('$1'),'$3'}.

line -> name ':=' process : {def, v('$1'), [], '$3'}.
%% dealing special case with bang right away
%% if $1 == $6 return $3
line -> name ':=' process '|^' int name : {def, v('$1'), [], same('$1','$6', '$3'), list_to_integer(v('$5'))}.

line -> name '(' arg_def_list ')' ':=' process : {def, v('$1'), '$3', '$6'}.
%% if $1 == $9 return $6
line -> name ':=' action '.' '(' process  '|^' int name ')' : {def, v('$1'), [], same('$1','$9', {prefix,{'$3',[]},'$6'}), list_to_integer(v('$8'))}.

line -> name ':=' action '.' '[' assignments ']' '(' process  '|^' int name ')' : {def, v('$1'), [], same('$1','$12', {prefix,{'$3', '$6'},'$9'}), list_to_integer(v('$11'))}.

line -> name ':=' '<' apred '>' action '.' '(' process  '|^' int name ')' : {def, v('$1'), [], same('$1','$12', {p_awareness, '$4', {prefix, {'$6',[]}, '$9'}}), list_to_integer(v('$11'))}.

line -> name ':=' '<' apred '>' action '.' '[' assignments ']' '(' process  '|^' int name ')' : {def, v('$1'), [], same('$1','$15', {p_awareness, '$4', {prefix, {'$6','$9'},'$12'}}), list_to_integer(v('$14'))}.

line -> system : '$1'.

system -> 'SYS' '::=' subsystem : {sys,'$3'}.
subsystem -> compcall : ['$1'].
subsystem -> compcall '||' subsystem : ['$1' | '$3'].

compcall -> name : {comp_call, v('$1'), []}.
compcall -> name '(' init_list ')' : {comp_call, v('$1'), '$3'}.

process -> action '.' process : {prefix, {'$1', []}, '$3'}. % prefix , no update
%process -> '[' assignments ']' process : {p_update, '$2', '$4'}.
process -> action '.' '[' assignments ']' process : {prefix, {'$1', '$4'}, '$6'}. % prefix, and update
process -> '<' apred '>' process : {p_awareness, '$2', '$4'}.
process -> process '|' process : {par, '$1', '$3'}.
process -> process '+' process : {choice, '$1', '$3'}.
process -> 'nil' : 'nil'.
process -> pcall : '$1'.
process -> '(' process ')' : '$2'.
%%process -> pred '?' process '_' process : {pchoice, {g_awareness,'$1','$3'}, '$5'}.

action ->  '(' ')' '@' '(' false ')': {output, empty, empty}.
%action ->  '(' exprs ')' '@' '(' false ')': {output, empty, empty}.
%action -> 'set' '(' assignment2 ')' : '$3'.
action ->  '(' exprs ')' '@' '(' spred ')': {output, '$2', '$6'}.
action ->  '(' rpred ')' '(' vars ')': {input, '$2', '$5'}.


%% Awareness predicate

apred -> '(' apred ')' : {parenthesis,'$2'}.
apred -> p_expr : '$1'.
apred -> apred 'and' apred : {intersect, '$1', '$3'}.
apred -> apred 'or' apred : {union, '$1', '$3'}.
apred -> 'not' apred : {negation, '$2'}.

%% Sending predicate
spred -> '(' spred ')' : {parenthesis,'$2'}.
spred -> p_expr : '$1'.
spred -> spred 'and' spred : {intersect, '$1', '$3'}.
spred -> spred 'or' spred : {union, '$1', '$3'}.
spred -> 'not' spred : {negation, '$2'}.

%% Receiving predicate

rpred -> '(' rpred ')' : {parenthesis,'$2'}.
rpred -> p_expr : '$1'.
rpred -> rpred 'and' rpred : {intersect, '$1', '$3'}.
rpred -> rpred 'or' rpred : {union, '$1', '$3'}.
rpred -> 'not' rpred : {negation, '$2'}.

p_expr -> expr '>=' expr : {geq, '$1', '$3'}.
p_expr -> expr '<=' expr : {leq, '$1', '$3'}.
p_expr -> expr '=' expr : {eq, '$1', '$3'}.
p_expr -> expr '>' expr : {ge, '$1', '$3'}.
p_expr -> expr '<' expr : {le, '$1', '$3'}.
p_expr -> expr '/=' expr : {diff, '$1', '$3'}.
p_expr -> expr 'in' expr : {ismember, '$1', '$3'}.
p_expr -> expr 'notin' expr : {notmember, '$1', '$3'}.
p_expr -> true : "true".
p_expr -> false : "false".

exprs -> expr : ['$1'].
exprs -> expr ',' exprs : ['$1' | '$3'].

expr -> int : {const,v('$1')}.
expr -> '-' int : {minusconst,v('$2')}.
expr -> tt : "true".
expr -> ff : "false".
expr -> atom : {token, v('$1')}.
expr -> func : {func, v('$1')}.
expr -> param : {param, v('$1')}.
expr -> literal : v_or_a('$1').
expr -> self : {self, v('$1')}.
expr -> op_expr : '$1'.
expr -> '|' expr '|' : {length, '$2'}.
expr -> expr '[' expr ']' : {selector, '$1', '$3'}.
expr -> expr '.' 'hd' : {head, '$1'}.
expr -> expr '.' 'tl' : {tail, '$1'}.
expr -> expr '.' 'min' : {min, '$1'}.
expr -> expr '.' 'max' : {max, '$1'}.
%expr -> '[' exprs ']' : {bracket, '$2'}.
expr -> '[' ']' : empty_vector.
expr -> '{' '}' : empty_set.
expr -> '[' exprs ']' : {bracket, '$2'}.
expr -> '{' exprs '}' : {bracket2, '$2'}.
expr -> '(' exprs ')' : '$2'.


op_expr -> expr '++' expr : {'++','$1','$3'}.
op_expr -> expr '--' expr : {'--','$1','$3'}.
op_expr -> expr '+' expr : {'+','$1','$3'}.
op_expr -> expr '-' expr : {'-','$1','$3'}.
op_expr -> expr '/' expr : {'/','$1','$3'}.
op_expr -> expr '*' expr : {'*','$1','$3'}.

assignments -> assignment : ['$1'].
assignments -> assignment ',' assignments : ['$1' | '$3'].

assignment -> expr ':=' expr : {assign, '$1', '$3'}.

%assignment2 -> expr ',' expr : {assign, '$1', '$3'}.

vars -> literal : [v('$1')].
vars -> literal ',' vars : [v('$1') | '$3'].

pcall -> name : {call, v('$1'), []}.
pcall -> name '(' arg_list ')': {call, v('$1'), '$3'}.

arg_def_list -> literal ',' arg_def_list : [v('$1') | '$3'].
arg_def_list -> literal : [v('$1')].

arg_list -> expr ',' arg_list : ['$1' | '$3'].
arg_list -> expr : ['$1'].

att_list -> literal : [p('$1')].
att_list -> literal ',' att_list : [p('$1') | '$3'].

Erlang code.

-export([scan_and_parse/1]).

v({_, _, Value}) -> Value.
p({_, _, A}) -> put(A,A), A. % make attributes become global
v_or_a({_, _, V}) ->
    case get(V) of
	undefined ->
	    {var, V};
	V ->
	    {att, V}
    end.

scan_and_parse(Code) ->
    case scanner:string(Code) of
	{ok, Tokens, _} ->
	    %io:format("TOKEN ~p~n",[Tokens]),
	    parse(Tokens);
	Err -> Err
    end.

same(A,B,C) ->
    case v(A) == v(B) of
	true -> C;
	false ->
	    io:format("Error at bang operator !!~n"),
	    nil
    end.
