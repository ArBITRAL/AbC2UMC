-module(input).
-compile(export_all).


printm(Object,File) ->
    lists:foldl(fun(X,Id) ->
			IdString = integer_to_list(Id),
			Data = "C"++IdString++": Man (id -> " ++ IdString ++ ", prefs -> ",
			file:write_file(File,[Data,io_lib:fwrite("~p",[X]),")\n"],[append]),
			Id + 1
		end, 1,
		Object).

printw(Object,File) ->
    N = length(Object),
    lists:foldl(fun(X,Id) ->
			IdString = integer_to_list(Id+N),
			Data = "C"++IdString++": Woman (id -> " ++ IdString ++ ", prefs -> ",
			file:write_file(File,[Data,io_lib:fwrite("~p",[X]),")\n"],[append]),
			Id + 1
		end, 1,
		Object).


uniform([Input,File]) ->
    N = list_to_integer(Input),
    Mid = lists:seq(1,N),
    Wid = lists:seq(1,N),
    M = m(Mid,N),
    W = w(Wid,N),
    printm(M,File),
    printw(W,File).


symetric([Input,File]) ->
    N = list_to_integer(Input),
    Mid = lists:seq(1,N),
    Wid = lists:seq(1,N),
    M = sm(Mid,N),
    W = sw(Wid,N),
    printm(M,File),
    printw(W,File).

uncoord([Input,File]) ->
    N = list_to_integer(Input),
    Mid = lists:seq(1,N),
    Wid = lists:seq(1,N),
    M = um(Mid,N),
    W = uw(Wid,N),
    printm(M,File),
    printw(W,File).

um(Mid,N) ->
    um(Mid,N,[]).

um([],_,Acc) ->
    lists:reverse(Acc);
um([H|T],N,Acc) ->
    First = [X+N || X <- lists:seq(H+1,N)],
    Second = [X+N || X <- lists:seq(1,H)],
    Acc2 = First ++ Second,
    um(T,N,[Acc2|Acc]).


uw(Wid,N) ->
    uw(Wid,N,[]).

uw([],_,Acc) ->
    lists:reverse(Acc);
uw([H|T],N,Acc) ->
    First = lists:reverse(lists:seq(1,H-1)),
    Second = lists:reverse(lists:seq(H,N)),
    Acc2 = [0|First] ++ Second,
    uw(T,N,[Acc2|Acc]).


m(Mid,N) ->
    m(Mid,N,[]).

m([],_,Acc) ->
    lists:reverse(Acc);
m([_|T],N,Acc) ->
    Acc2 = [X+N || X <- lists:seq(1,N)],
    m(T,N,[Acc2|Acc]).


w(Wid,N) ->
    w(Wid,N,[]).

w([],_,Acc) ->
    lists:reverse(Acc);
w([_|T],N,Acc) ->
    Acc2 = [0|lists:reverse(lists:seq(1,N))],
    w(T,N,[Acc2|Acc]).



sm(Mid,N) ->
    sm(Mid,N,[]).

sm([],_,Acc) ->
    lists:reverse(Acc);
sm([H|T],N,Acc) ->
    First = [X+N || X <- lists:seq(H,N)],
    Second = [X+N || X <- lists:seq(1,H-1)],
    Acc2 = First ++ Second,
    sm(T,N,[Acc2|Acc]).


sw(Wid,N) ->
    sw(Wid,N,[]).

sw([],_,Acc) ->
    lists:reverse(Acc);
sw([H|T],N,Acc) ->
    First = lists:reverse(lists:seq(1,H-1)),
    Second = lists:reverse(lists:seq(H,N)),
    Acc2 = [0|First] ++ Second,
    sw(T,N,[Acc2|Acc]).
