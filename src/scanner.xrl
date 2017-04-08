Definitions.

INT = [0-9]*
OP = \+|\_|(\?)|\-|\-\-|\*|\/|\(|\)|\||\|\||\.|(and)|(or)|(not)|(:=)|(::=)|=|<|<=|==|=>|\{|\}|\:|\-\>|>|<>|\^|\,|\@|\$|\[|\]
ATOM = [a-z][0-9a-zA-Z_]*
PNAME = [A-Z][0-9a-zA-Z_]*

Rules.

tt          :   {token,{true,TokenLine,TokenChars}}.
ff          :   {token,{false,TokenLine,TokenChars}}.
true        :   {token,{true,TokenLine,TokenChars}}.
false       :   {token,{false,TokenLine,TokenChars}}.
{INT}       :   {token, {int, TokenLine, TokenChars}}.
{OP}	    :   {token, {list_to_atom(TokenChars), TokenLine}}.

{PNAME}	    : Atom = list_to_atom(TokenChars),
                        {token, case reserved_word(Atom) of
                                true -> {Atom, TokenLine};
                                false -> {name, TokenLine, list_to_atom(TokenChars)}
                        end}.

{ATOM}	    :   Atom = list_to_atom(TokenChars),
                        {token, case reserved_word(Atom) of
                                true -> {Atom, TokenLine};
                                false -> {literal, TokenLine, TokenChars}
                        end}.
_{ATOM}	        : {token, {token, TokenLine, strip(TokenChars,TokenLen)}}.
(this.){ATOM}	: {token, {self, TokenLine, strip2(TokenChars,TokenLen)}}.

\s|\n|\t	: skip_token.

\-\-.*           : skip_token.


Erlang code.

strip(TokenChars,TokenLen) ->
    lists:sublist(TokenChars, 2, TokenLen - 1).

strip2(TokenChars,TokenLen) ->
    lists:sublist(TokenChars, 6, TokenLen - 4).

reserved_word('SYS') -> true;
reserved_word('component') -> true;
reserved_word('attributes') -> true;
reserved_word('behaviour') -> true;
reserved_word('end') -> true;
reserved_word('let') -> true;
reserved_word('in') -> true;
reserved_word('notin') -> true;
reserved_word('head') -> true;
reserved_word('tail') -> true;
reserved_word('nil') -> true;
reserved_word(_) -> false.
