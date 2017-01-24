Nonterminals lines line subsystem system process assignments assignment action pred exps exp vars var att base arg_list arg_def_list att_list pcall init_list init data array compinit compcall.

Terminals
	'+' '(' ')' '>' '<' '<>' '>=' '<=' '=' ':' ':=' '::=' 'and' 'or' 'not' '|' '||' '.' ',' '^' '@' '$' '[' ']' '{' '}' '->' '=>'
	int self true false name literal token 'component' 'attributes' 'behaviour' 'let' 'in' 'end' 'head' 'tail' 'nil' 'SYS'.

Rootsymbol lines.

Left 100 '|'.
Left 200 '+'.
Left 300 '.'.
Left 400 'or'.
Left 500 'and'.
Right 600 'not'.
Left 700 '>' '<' '<>' '>=' '<=' '='.

lines -> line lines : ['$1' | '$2'].
lines -> line : ['$1'].

line -> 'component' name lines 'end' : {comp, v('$2'), '$3'}.
line -> 'attributes' ':' att_list : {attributes, '$3'}.
line -> 'behaviour' ':' 'let' '{' lines '}' 'in' process : {behaviour, '$5', {init, '$8'}}.
line -> name ':' compinit : {comp_init, v('$1'), '$3'}.

compinit -> name : {comp, v('$1'), []}.
compinit -> name '(' init_list ')' : {comp, v('$1'), '$3'}.

init_list -> init : ['$1'].
init_list -> init ',' init_list : ['$1' | '$3'].

init -> literal '->' data : {v('$1'),'$3'}.
init -> literal '=' data : {v('$1'),'$3'}.
init -> literal '=>' data : {v('$1'),'$3'}.

data -> literal : v('$1').
data -> int : v('$1').
data -> '[' array ']' : v1('$2').

array -> literal : [v('$1')].
array -> literal ',' array : [v('$1') | '$3'].
array -> int : [v('$1')].
array -> int ',' array : [v('$1') | '$3'].


line -> name ':=' process : {def, v('$1'), [], '$3'}.
line -> name '(' arg_def_list ')' ':=' process : {def, v('$1'), '$3', '$6'}.
line -> system : '$1'.

system -> 'SYS' '::=' subsystem : {sys,'$3'}.
subsystem -> compcall : ['$1'].
subsystem -> compcall '||' subsystem : ['$1' | '$3'].

compcall -> name : {comp_call, v('$1'), []}.
compcall -> name '(' init_list ')' : {comp_call, v('$1'), '$3'}.



process -> '(' process ')' : '$2'.
process -> '[' assignments']' process : {p_update, '$2', '$4'}.
process -> '<' pred '>' process : {p_awareness, '$2', '$4'}.
process -> action '.' process : {prefix, '$1', '$3'}.
process -> process '+' process : {choice, '$1', '$3'}.
process -> process '|' process : {par, '$1', '$3'}.
process -> process '|' '^' int process: {par, '$1', {bang, '$5', list_to_integer(v('$4'))}}.
process -> 'nil' : 'nil'.
process -> pcall : '$1'.


assignments -> assignment : ['$1'].
assignments -> assignment ',' assignments : ['$1' | '$3'].

assignment -> exp ':=' exp : {assign, '$1', '$3'}.

action ->  '(' exps ')' '@' '(' pred ')': {output, '$2', '$6'}.
action ->  '(' pred ')' '(' vars ')': {input, '$2', '$5'}.

exps -> exp : ['$1'].
exps -> exp ',' exps : ['$1' | '$3'].

vars -> var : [v('$1')].
vars -> var ',' vars : [v('$1') | '$3'].

base -> var : {var, v('$1')}.
base -> int : {const,v('$1')}.
base -> token : {token,v('$1')}.
base -> self : {self, v('$1')}.
base -> att : '$1'.

exp -> base : '$1'.
exp -> base '.' 'head' : {head, '$1'}.
exp -> base '.' 'tail' : {tail, '$1'}.
exp -> exp '[' exp ']' : {selector, '$1', '$3'}.

var -> '$' literal : '$2'.
att -> literal : {att,v('$1')}.

pred -> true : "true".
pred -> false : "false".
pred -> '(' pred ')' : '$2'.
pred -> exp '>=' exp : {geq, '$1', '$3'}.
pred -> exp '<=' exp : {leq, '$1', '$3'}.
pred -> exp '=' exp : {eq, '$1', '$3'}.
pred -> exp '>' exp : {ge, '$1', '$3'}.
pred -> exp '<' exp : {le, '$1', '$3'}.
pred -> exp '<>' exp : {diff, '$1', '$3'}.

pred -> pred 'and' pred : {intersect, '$1', '$3'}.
pred -> pred 'or' pred : {union, '$1', '$3'}.
pred -> 'not' pred : {negation, '$2'}.

pcall -> name : {call, v('$1'), []}.
pcall -> name '(' arg_list ')': {call, v('$1'), '$3'}.

arg_def_list -> literal ',' arg_def_list : [v('$1') | '$3'].
arg_def_list -> literal : [v('$1')].

arg_list -> literal ',' arg_list : ['$1' | '$3'].
arg_list -> literal : ['$1'].

att_list -> literal ',' att_list : [v('$1') | '$3'].
att_list -> literal : [v('$1')].

Erlang code.

-export([scan_and_parse/1]).

v({_, _, Value}) -> Value.
v1(Array) -> "[" ++ string:join(Array,",") ++ "]".


scan_and_parse(Code) ->
	case scanner:string(Code) of
		{ok, Tokens, _} -> parse(Tokens);
		Err -> Err
	end.
