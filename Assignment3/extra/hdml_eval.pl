% Definiujemy moduł zawierający rozwiązanie.
% Należy zmienić nazwę modułu na {imie}_{nazwisko}_eval gdzie za
% {imie} i {nazwisko} należy podstawić odpowiednio swoje imię
% i nazwisko bez wielkich liter oraz znaków diakrytycznych
:- module(hdml_eval, [run/5]).

:- op(200, fx, ~).
:- op(500, xfy, v).

arithmetic_op(Op) :- member(Op, ['+', '-', '*', '/', '%']).

calculate('/', X, Y, Z) :- !, Z is X div Y.
calculate('%', X, Y, Z) :- !, Z is X mod Y.
calculate(Op, X, Y, Z) :-
    Expr =.. [Op, X, Y],
    Z is Expr.

do_arithmetic(_, Op, X, Y, Z) :-
    number(X),
    number(Y), !,
    calculate(Op, X, Y, Z).
do_arithmetic(Pos, _, _, _, _) :- throw(runtime_error("cannot calculate non numbers", Pos)).

comparative_op(Op) :- member(Op, ['=', '<>', '<', '>', '<=', '>=']).

cmp('=', X, Y, 1) :- X = Y, !.
cmp('>', X, Y, 1) :- X > Y, !.
cmp('<', X, Y, 1) :- X < Y, !.
cmp('<>', X, Y, 1) :- X \= Y, !.
cmp('>=', X, Y, 1) :- X >= Y, !.
cmp('<=', X, Y, 1) :- X =< Y, !.
cmp(_, _, _, 0).

do_comparison(_, Op, X, Y, Z) :-
    number(X),
    number(Y), !,
    cmp(Op, X, Y, Z).
do_comparison(Pos, _, _, _, _) :- throw(runtime_error("cannot compare non numbers", Pos)).

logical_op(Op) :- member(Op, ['&', '|', '^']).

do_logical(Pos, [X1 | X], [Y1 | Y], Op, [Z1 | Z]) --> !,
    { gensym(wire, Z1) },
    (   { Op = '&' }, !, [Z1 v ~X1 v ~Y1, ~Z1 v X1, ~Z1 v Y1];
        { Op = '|' }, !, [Z1 v ~X1, Z1 v ~Y1, ~Z1 v X1 v Y1];
                         [~Z1 v X1 v Y1, ~Z1 v ~X1 v ~Y1, Z1 v X1 v ~Y1, Z1 v ~X1 v Y1] ),
    do_logical(Pos, X, Y, Op, Z).
do_logical(_, [], [], _, []) --> !.
do_logical(Pos, _, _, _, _) --> { throw(runtime_error("cannot perform logical operation", Pos)) }.

negate(Pos, [X1 | X], [Y1 | Y]) --> !,
    { gensym(wire, Y1) },
    [X1 v Y1, ~X1 v ~Y1],
    negate(Pos, X, Y).
negate(_, [], []) --> !.
negate(Pos, _, _) --> { throw(runtime_error("cannot perform logical operation", Pos)) }.

find_function(_, [def(Name, Pattern, Expr) | _], Name, Pattern, Expr).
find_function(Pos, [_ | Program], Name, Pattern, Expr) :- find_function(Pos, Program, Name, Pattern, Expr).
find_function(Pos, [], _, _, _) :- throw(runtime_error("no function with given name", Pos)).

empty_env(Env) :- empty_assoc(Env).

extend_env(Env, X, Val, Env1) :- put_assoc(X, Env, Val, Env1).

get_value(_, X, Env, Val) :- get_assoc(X, Env, Val), !.
get_value(Pos, _, _, _) :- throw(runtime_error("variable not set", Pos)).

shorten(_, X, 0, X) :- !.
shorten(Pos, [_ | T], N, S) :- N > 0, !, N1 is N - 1, shorten(Pos, T, N1, S).
shorten(Pos, _, _) :- throw(runtime_error("cannot select bits", Pos)).

get_bits(_, _, 0, []) :- !.
get_bits(Pos, [H | T], N, [H | S]) :- N > 0, !, N1 is N - 1, get_bits(Pos, T, N1, S).
get_bits(Pos, _, _) :- throw(runtime_error("cannot select bits", Pos)).

select_bits(Pos, Bits, N, M, Val) :-
    number(N),
    number(M), !,
    shorten(Pos, Bits, N, Bits1),
    M1 is M - N + 1,
    get_bits(Pos, Bits1, M1, Val).
select_bits(Pos, _, _, _, _) :- throw(runtime_error("cannot select bits", Pos)).

podstaw(_, wildcard(_), _, Env, Env) :- !.
podstaw(_, var(_, X), Val, Env, Env1) :- !, extend_env(Env, X, Val, Env1).
podstaw(_, pair(Pos, P1, P2), (V1, V2), Env, EnvOut) :- !,
    podstaw(Pos, P1, V1, Env, Env1),
    podstaw(Pos, P2, V2, Env1, EnvOut).
podstaw(Pos, _, _, _, _) :- throw(runtime_error("cannot perform assignment", Pos)).

eval(num(_, N), _, _, N) --> [].
eval(empty(_), _, _, []) --> [].
eval(var(Pos, X), _, Env, Val) --> { get_value(Pos, X, Env, Val) }.

eval(bit(Pos, Expr), P, Env, [Val]) -->
    eval(Expr, P, Env, Val1),
    { gensym(wire, Val) },
    (
        { Val1 = 0 }, !, [~Val];
        { Val1 = 1 }, !, [Val];
        { throw(runtime_error("cannot instantiate bit", Pos)) }
    ).
eval(bitsel(Pos, E1, E2), P, Env, Val) -->
    eval(E1, P, Env, Bits),
    eval(E2, P, Env, N),
    { select_bits(Pos, Bits, N, N, Val) }.
eval(bitsel(Pos, E1, E2, E3), P, Env, Val) -->
    eval(E1, P, Env, Bits),
    eval(E2, P, Env, N),
    eval(E3, P, Env, M),
    { select_bits(Pos, Bits, M, N, Val) }.

eval(pair(_, E1, E2), P, Env, (Val1, Val2)) -->
    eval(E1, P, Env, Val1),
    eval(E2, P, Env, Val2).

eval(op(Pos, Op, E), P, Env, Val) -->
    eval(E, P, Env, Val1),
    (
        { Op = '#' }, !, { (is_list(Val1) -> length(Val1, Val); throw(runtime_error("cannot get lenght of non-list", Pos))) };
        { Op = '-' }, !, { (number(Val1) -> Val is -Val1; throw(runtime_error("cannot negate non number", Pos))) };
        { Op = '~' }, negate(Pos, Val1, Val)
    ).

eval(op(Pos, Op, E1, E2), P, Env, Val) -->
    eval(E1, P, Env, Val1),
    eval(E2, P, Env, Val2),
    (
        { Op = '@' }, !, {
            (is_list(Val1), is_list(Val2) ->
                append(Val2, Val1, Val);
                throw(runtime_error("cannot append non-lists", Pos))
            )
        };
        { arithmetic_op(Op) }, !, { do_arithmetic(Pos, Op, Val1, Val2, Val) };
        { comparative_op(Op) }, !, { do_comparison(Pos, Op, Val1, Val2, Val) };
        { logical_op(Op) }, do_logical(Pos, Val1, Val2, Op, Val)
    ).

eval(if(Pos, E1, E2, E3), P, Env, Val) -->
    eval(E1, P, Env, Cond),
    ({ number(Cond) } ->
        ({ Cond = 0 } -> eval(E3, P, Env, Val); eval(E2, P, Env, Val));
        { throw(runtime_error("cannot if non number", Pos)) }
    ).

eval(let(Pos, Pattern, E1, E2), Program, Env, Val) -->
    eval(E1, Program, Env, Val1),
    { podstaw(Pos, Pattern, Val1, Env, Env1) },
    eval(E2, Program, Env1, Val).

eval(call(Pos, Name, Args), Program, Env, Val) -->
    { find_function(Pos, Program, Name, Pattern, Expr) },
    eval(Args, Program, Env, ArgsVal),
    { empty_env(Env2), podstaw(Pos, Pattern, ArgsVal, Env2, Env1) }, !,
    eval(Expr, Program, Env1, Val).

run(Program, FName, Arg, Value, Clauses) :-
    find_function(test, Program, FName, Pattern, Expr),
    empty_env(Env1),
    podstaw(test, Pattern, Arg, Env1, Env), !,
    eval(Expr, Program, Env, Value, Clauses, []).
