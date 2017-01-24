-module(env).
-export([new/0, new/1, pop/1, store/3, update/3, fetch/2]).

%%
% stores a list of dicts

new() -> [dict:new()].
new(Env) -> [dict:new() | Env].

pop([_ | []]) -> erlang:error("Env stack underflow");
pop([_ | Env]) -> Env.

store(Name, Value, [Current | Rest]) ->
	[dict:store(Name, Value, Current) | Rest].

update(Name, Value, [Current | Rest]) ->
	case dict:is_key(Name, Current) of
		true -> [dict:store(Name, Value, Current) | Rest];
		false -> [Current | update(Name, Value, Rest)]
	end;
update(_, _, []) -> erlang:error("Invalid name for update").

fetch(Name, [Current | Rest]) ->
	case dict:is_key(Name, Current) of
		true -> dict:fetch(Name, Current);
		false -> fetch(Name, Rest)
	end;
fetch(Name, []) -> erlang:error("Undefined variable: " ++ Name).

