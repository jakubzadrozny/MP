% Definiujemy moduł zawierający rozwiązanie.
% Należy zmienić nazwę modułu na {imie}_{nazwisko} gdzie za
% {imie} i {nazwisko} należy podstawić odpowiednio swoje imię
% i nazwisko bez znaków diakrytycznych
:- module(jakub_zadrozny, [solve/2]).

% definiujemy operatory ~/1 oraz v/2
:- op(200, fx, ~).
:- op(500, xfy, v).

transform_clause([], _, _) :- !, false.
transform_clause(X v Y, Acc, List) :-
    member(X, Acc),
    !,
    transform_clause(Y, Acc, List).
transform_clause(X v Y, Acc, List) :-
    !,
    transform_clause(Y, [X | Acc], List).
transform_clause(X, Acc, Acc) :-
    member(X, Acc),
    !.
transform_clause(X, Acc, [X | Acc]).

transform_clause(Clause, List) :-
    transform_clause(Clause, [], List).

transform_clauses([], []).
transform_clauses([H1 | T1], [H2 | T2]) :-
    transform_clause(H1, H2),
    transform_clauses(T1, T2).

filter_clauses([], []).
filter_clauses([H | T], S) :-
    member(~X, H),
    member(X, H),
    !,
    filter_clauses(T, S).
filter_clauses([H | T], [H | S]) :-
    filter_clauses(T, S).

get_variables_from_list([], Acc, Acc).
get_variables_from_list([~First | Rest], Acc, Variables) :-
    member(First, Acc),
    !,
    get_variables_from_list(Rest, Acc, Variables).
get_variables_from_list([~First | Rest], Acc, Variables) :-
    !,
    get_variables_from_list(Rest, [First | Acc], Variables).
get_variables_from_list([First | Rest], Acc, Variables) :-
    member(First, Acc),
    !,
    get_variables_from_list(Rest, Acc, Variables).
get_variables_from_list([First | Rest], Acc, Variables) :-
    get_variables_from_list(Rest, [First | Acc], Variables).

get_variables([], Acc, Acc).
get_variables([First | Rest], Acc, Variables) :-
    get_variables_from_list(First, Acc, Acc1),
    get_variables(Rest, Acc1, Variables).

get_variables(List, Variables) :-
    get_variables(List, [], Variables).

already_done(Clause, Sigma) :-
    member(~X, Clause),
    member((X, f), Sigma),
    !.
already_done(Clause, Sigma) :-
    member(X, Clause),
    member((X, t), Sigma),
    !.

satisfy([~H | T], Acc, Sigma) :-
    member((H, t), Acc),
    !,
    satisfy(T, Acc, Sigma).
satisfy([~H | _], Acc, [(H, f) | Acc]).
satisfy([~H | T], Acc, Sigma) :-
    !,
    satisfy(T, [(H, t) | Acc], Sigma).

satisfy([H | T], Acc, Sigma) :-
    member((H, f), Acc),
    !,
    satisfy(T, Acc, Sigma).
satisfy([H | _], Acc, [(H, t) | Acc]).
satisfy([H | T], Acc, Sigma) :-
    satisfy(T, [(H, f) | Acc], Sigma).

generate_sigma([], Sigma, Sigma).
generate_sigma([H | T], Acc, Sigma) :-
    already_done(H, Acc),
    !,
    generate_sigma(T, Acc, Sigma).
generate_sigma([H | T], Acc, Sigma) :-
    satisfy(H, Acc, Acc1),
    generate_sigma(T, Acc1, Sigma).

generate_sigma(Clauses, Sigma) :-
    generate_sigma(Clauses, [], Sigma).

correct_sigma([], Sigma, Sigma).
correct_sigma([First | Rest], Sigma, Correct) :-
    member((First, _), Sigma),
    !,
    correct_sigma(Rest, Sigma, Correct).
correct_sigma([First | Rest], Sigma, Correct) :-
    correct_sigma(Rest, [(First, x) | Sigma], Correct).

append_lengths([], []).
append_lengths([H1 | T1], [[N1 | H1] | T2]) :-
    length(H1, N1),
    append_lengths(T1, T2).

remove_lengths([], []).
remove_lengths([[_ | T1] | T2], [T1 | T3]) :-
    remove_lengths(T2, T3).

cmp(<, [H1 | _], [H2 | _]) :- H1 =< H2.
cmp(>, [H1 | _], [H2 | _]) :- H1 > H2.

sort_clauses(Raw, Sorted) :-
    append_lengths(Raw, Lengths),
    predsort(cmp, Lengths, MidSorted),
    remove_lengths(MidSorted, Sorted).

% Główny predykat rozwiązujący zadanie.
% UWAGA: to nie jest jeszcze rozwiązanie; należy zmienić jego
% definicję.
solve(Raw, Solution) :-
    transform_clauses(Raw, Unfiltered),
    get_variables(Unfiltered, Variables),
    filter_clauses(Unfiltered, Filtered),
    sort_clauses(Filtered, Clauses),
    generate_sigma(Clauses, Sigma),
    correct_sigma(Variables, Sigma, Solution).
