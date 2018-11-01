% Definiujemy moduł zawierający rozwiązanie.
% Należy zmienić nazwę modułu na {imie}_{nazwisko} gdzie za
% {imie} i {nazwisko} należy podstawić odpowiednio swoje imię
% i nazwisko bez wielkich liter oraz znaków diakrytycznych
:- module(jakub_zadrozny, [resolve/4, prove/2]).

% definiujemy operatory ~/1 oraz v/2
:- op(200, fx, ~).
:- op(500, xfy, v).

format([], [] - []) :- !.
format(~X v Y, Pos - [X | Neg]) :- !, transform(Y, Pos - Neg).
format(~X, [] - [X]) :- !.
format(X v Y, [X | Pos] - Neg) :- !, transform(Y, Pos - Neg).
format(X, [X] - []).

is_sublist([], _).
is_sublist([H | T1], [H | T2]) :- !, is_sublist(T1, T2).
is_sublist([H1 | T1], [_ | T2]) :- is_sublist([H1 | T1], T2).

is_subclause(clause(Pos1 - Neg1, _, _, _), clause(Pos2 - Neg2, _, _, _)) :-
    is_sublist(Pos1, Pos2),
    is_sublist(Neg1, Neg2).

get_length(Pos - Neg, N) :-
    length(Pos, N1),
    length(Neg, N2),
    N is N1 + N2.

build_terms([], []).
build_terms([H | T], [clause(H, L, _, axiom) | S]) :-
    get_length(H, L),
    build_terms(T, S).

transform(C, Pos - Neg) :-
    format(C, Pos1 - Neg1),
    sort(Pos1, Pos),
    sort(Neg1, Neg).

transform_all([], []).
transform_all([H | T], [Pos - Neg | S]) :-
    transform(H, Pos - Neg),
    transform_all(T, S).

create_clause([X] - [], X) :- !.
create_clause([] - [X], ~X) :- !.
create_clause([H | T] - Neg, H v X) :- create_clause(T - Neg, X).
create_clause([] - [H | T], ~H v X) :- create_clause([] - T, X).
create_clause([] - [], []).

check_taut(clause(Pos - Neg, _, _, _)) :-
    member(X, Pos),
    once(member(X, Neg)).

resolve_all(_, [], Acc, Acc).

resolve_all(C, [H | T], Acc, Ans) :-
    C = clause(Pos1 - Neg1, _, _, _),
    H = clause(Pos2 - Neg2, _, _, _),
    member(X, Pos1),
    once(member(X, Neg2)),
    !, resolve1(X, Pos1 - Neg1, Pos2 - Neg2, Pos - Neg),
    get_length(Pos - Neg, Len),
    R = clause(Pos - Neg, Len, _, from(X, C, H)),
    (Len = 0 -> Ans = [R | Acc], true;
        resolve_all(C, T, [R | Acc], Ans)).

resolve_all(C, [H | T], Acc, Ans) :-
    C = clause(Pos1 - Neg1, _, _, _),
    H = clause(Pos2 - Neg2, _, _, _),
    member(X, Neg1),
    once(member(X, Pos2)),
    !, resolve1(X, Pos2 - Neg2, Pos1 - Neg1, Pos - Neg),
    get_length(Pos - Neg, Len),
    R = clause(Pos - Neg, Len, _, from(X, H, C)),
    (Len = 0 -> Ans = [R | Acc], true;
        resolve_all(C, T, [R | Acc], Ans)).

resolve_all(C, [_ | T], Acc, Ans) :- resolve_all(C, T, Acc, Ans).

resolve_all(C, A, Ans) :- resolve_all(C, A, [], Ans).

filter_set([], _, []).
filter_set([H | T], C, Ans) :-
    is_subclause(C, H), !,
    filter_set(T, C, Ans).
filter_set([H | T], C, [H | Ans]) :- filter_set(T, C, Ans).

% check_subclause(C1, C2, A, B, A, B) :- is_subclause(C1, C2), !.
% check_subclause(_, C2, A, B, SA, SB) :- add_to_set(A, B, C2, SA, SB).
%
% add_to_set([A | TA], [B | TB], C, [A | SA], SB) :-
%     A = clause(_, LA, _, _),
%     B = clause(_, LB, _, _),
%     C = clause(_, LC, _, _),
%     LA =< LB, LA =< LC, !,
%     check_subclause(A, C, TA, [B | TB], SA, SB).
% add_to_set([A | TA], [B | TB], C, SA, [B | SB]) :-
%     A = clause(_, LA, _, _),
%     B = clause(_, LB, _, _),
%     C = clause(_, LC, _, _),
%     LB < LA, LB =< LC, !,
%     check_subclause(B, C, [A | TA], TB, SA, SB).
% add_to_set([A | TA], [], C, [A | SA], SB) :-
%     A = clause(_, LA, _, _),
%     C = clause(_, LC, _, _),
%     LA =< LC, !,
%     check_subclause(A, C, TA, [], SA, SB).
% add_to_set([], [B | TB], C, [], [B | SB]) :-
%     B = clause(_, LB, _, _),
%     C = clause(_, LC, _, _),
%     LB =< LC, !,
%     check_subclause(B, C, [], TB, [], SB).

add_to_set([A | TA], B, C, [A | SA], SB) :-
    A = clause(_, LA, _, _),
    C = clause(_, LC, _, _),
    LA =< LC, !,
    (is_subclause(A, C) -> SA = TA, SB = B;
        add_to_set(TA, B, C, SA, SB)).
add_to_set(A, [B | TB], C, SA, [B | SB]) :-
    B = clause(_, LB, _, _),
    C = clause(_, LC, _, _),
    LB =< LC, !,
    (is_subclause(B, C) -> SA = A, SB = TB;
        add_to_set(A, TB, C, SA, SB)).

add_to_set(A, B, C, SA, [C | SB]) :-
    filter_set(A, C, SA),
    filter_set(B, C, SB).

add_to_sorted([H | T], C, [H | S]) :-
    H = clause(_, LH, _, _),
    C = clause(_, LC, _, _),
    LH < LC, !,
    add_to_sorted(T, C, S).
add_to_sorted(T, C, [C | T]).

smart_add([], A, B, A, B).
smart_add([H | T], A, B, NewA, NewB) :-
    (check_taut(H) -> A1 = A, B1 = B;
        add_to_set(A, B, H, A1, B1)),
    smart_add(T, A1, B1, NewA, NewB).

find_resolvents(A, [], A) :- !.
find_resolvents(A, [H | B], Ans) :-
    resolve_all(H, A, Res),
    (Res = [C | _], C = clause([] - [], _, _, _) -> Ans = [C | A];
        add_to_sorted(A, H, A1),
        smart_add(Res, A1, B, NewA, NewB),
        find_resolvents(NewA, NewB, Ans)).

obtain_proof(clause(_, _, X, _), N, N, End, End) :- nonvar(X), !.
obtain_proof(clause(C, _, X, axiom), N, N1, End1, End2) :-
    !, X = N,
    N1 is N + 1,
    create_clause(C, Clause),
    End1 = [(Clause, axiom) | End2].
obtain_proof(clause(C, _, X, from(Var, C1, C2)), N, M, End1, End) :-
    obtain_proof(C1, N, N1, End1, End2),
    obtain_proof(C2, N1, N2, End2, End3),
    C1 = clause(_, _, X1, _),
    C2 = clause(_, _, X2, _),
    X = N2, M is N2 + 1,
    create_clause(C, Clause),
    End3 = [(Clause, (Var, X1, X2)) | End].

merge_select(Var, [Var | T], X, S) :- !, merge_select(Var, T, X, S).
merge_select(Var, X, [Var | T], S) :- !, merge_select(Var, X, T, S).
merge_select(_, [], X, X) :- !.
merge_select(_, X, [], X) :- !.
merge_select(Var, [H | T1], [H | T2], [H | S]) :- !, merge_select(Var, T1, T2, S).
merge_select(Var, [H1 | T1], [H2 | T2], [H1 | S]) :- H1 @< H2, !, merge_select(Var, T1, [H2 | T2], S).
merge_select(Var, X, [H2 | T2], [H2 | S]) :- merge_select(Var, X, T2, S).

resolve1(Var, Pos1 - Neg1, Pos2 - Neg2, Pos - Neg) :-
    merge_select(Var, Pos1, Pos2, Pos),
    merge_select(Var, Neg1, Neg2, Neg).

append_select(_, [], X, X).
append_select(Var, [Var | T], X, Y) :- !, append_select(Var, T, X, Y).
append_select(Var, [H | T], X, [H | Y]) :- append_select(Var, T, X, Y).


% PREDYKAT RESOLVE
resolve(Var, C1, C2, Ans) :-
    transform(C1, Pos1 - Neg1),
    transform(C2, Pos2 - Neg2),
    append_select(Var, Pos1, Pos2, Pos3),
    append_select(Var, Neg2, Neg1, Neg3),
    sort(Pos3, Pos),
    sort(Neg3, Neg),
    create_clause(Pos - Neg, Ans).


% GLOWNY PREDYKAT
prove(Raw, Proof) :-
    transform_all(Raw, Clauses),
    build_terms(Clauses, Terms),
    smart_add(Terms, [], [], _, B),
    B = [clause(_, L, _, _) | _],
    (L = 0 -> B = [H | _];
        \+once(check_sat(B)),
        find_resolvents([], B, [H | _]),
        H = clause([] - [], _, _, _)),
    obtain_proof(H, 1, _, Proof, []).


% Sprawdzanie spelnialnosci
already_done(Pos - _, Sigma) :-
    member(X, Pos),
    member((X, t), Sigma), !.
already_done(_ - Neg, Sigma) :-
    member(X, Neg),
    member((X, f), Sigma).

satisfy([H | T] - Neg, Acc, Sigma) :-
    member((H, _), Acc), !,
    satisfy(T - Neg, Acc, Sigma).
satisfy([H | _] - _, Acc, [(H, t) | Acc]).
satisfy([H | T] - Neg, Acc, Sigma) :-
    satisfy(T - Neg, [(H, f) | Acc], Sigma).

satisfy([] - [H | T], Acc, Sigma) :-
    member((H, _), Acc), !,
    satisfy([] - T, Acc, Sigma).
satisfy([] - [H | _], Acc, [(H, f) | Acc]).
satisfy([] - [H | T], Acc, Sigma) :-
    satisfy([] - T, [(H, t) | Acc], Sigma).

check_sat([], _).
check_sat([H | T], Sigma) :-
    H = clause(C, _, _, _),
    already_done(C, Sigma), !,
    check_sat(T, Sigma).
check_sat([H | T], Sigma) :-
    H = clause(C, _, _, _),
    satisfy(C, Sigma, Sigma1),
    check_sat(T, Sigma1).

check_sat(Set) :-
    check_sat(Set, []).
