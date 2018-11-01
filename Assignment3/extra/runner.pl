% Program do weryfikowania układów cyfrowych
%
% Program uruchamiamy poleceniem:
%
% $ swipl -f verify.pl -t main PROGRAM TEST_SUITE
%
% gdzie:
% PROGRAM      jest ścieżką do programu w~języku HDML
% TEST_SUITE   jest ścieżką do pliku z testami
%
% plik z testami zawiera ciąg prologowych faktów postaci
% test(-Name, -FuncName, -Arg, -Result),
% gdzie:
% Name:     nazwa testu
% FuncName: atom reprezentujący nazwę testowanej funkcji w~programie
% Arg:      argument dla funkcji. Argumenty mają taki sam format jak wartości
%           w interpreterze języka HDML, z tą różnicą, że sygnały mogą być
%           nie tylko atomami, ale też liczbami 0 lub 1 (oznaczjącymi wartość
%           danego sygnału).
% Result    oczekiwana wartość funkcji. Przyjmujemy taki sam format danych
%           jak w~przypadku argumentu.
%
% UWAGA: do poprawnego działania programu wymagane jest poprawne rozwiązanie
% pracowni 1 lub 2, oraz pracowni 3 wraz z zadaniem dodatkowym
% zmodyfikuj 2 następne wiersze:
:- use_module(hdml_parser). % rozwiązanie pracowni 3
:- use_module(hdml_eval).   % rozwiązanie zadania dodatkowego

% oraz odkomentuk i zmodyfiku jeden z następnych dwóch wierszy
% :- use_module(sat_solver).     % rozwiązanie pracowni 1
% :- use_module('theorem_prover.pl'). % rozwiązanie pracowni 2

:- op(200, fx, ~).
:- op(500, xfy, v).

run_program(Path, FuncName, Arg, Result) :-
  % collect_vars((Arg, ExpectedResult), Vars),
  % translate_value(Arg, VArg),
  parse_program(Path, Program),
  eval_program(Program, FuncName, Arg, Res, Clauses),
  Result = (Res, Clauses).
  % print(Result).
  % print(Clauses).
  % compare_results(ExpectedResult, Result, AllClauses, ArgClauses),
  % solve_clauses(Vars, AllClauses).

% main(ProgramPath, FuncName, Arg) :-
  % ( current_prolog_flag(argv, [ProgramPath, TestPath]) ->
    %   read_file_to_terms(TestPath, Tests, []),
    %   member(test(TestName, FuncName, Arg), Tests),
    %   format("Running test: ~w~n", [ TestName ]),
    %   run_program(ProgramPath, FuncName, Arg).
    %   fail
  % ; format("Usage: swipl -f verify.pl -t main PROGRAM TEST_SUITE~n")
  % ).
% main.

% =============================================================================
% Predykaty pomocnicze:

% collect_vars(Arg, Vars) :-
%   phrase(collect_vars(Arg), AllVars),
%   sort(AllVars, Vars).
%
% collect_vars(X) --> { number(X), ! }.
% collect_vars([]) --> {}.
% collect_vars([H|T]) -->
%   ( { atom(H) } -> [ H ]
%   ; { true }
%   ), collect_vars(T).
% collect_vars((V1, V2)) --> collect_vars(V1), collect_vars(V2).
%
translate_value(N, N) :- number(N), !.
translate_value((V1, V2), (W1, W2)) :- !,
  translate_value(V1, W1),
  translate_value(V2, W2).
translate_value(BS, SS) :- translate_bitvec(BS, SS).

translate_bitvec([], []).
translate_bitvec([B|BS], [S|SS]) :-
  translate_bit(B, S),
  translate_bitvec(BS, SS).

translate_bit(A, A) :- atom(A), !.
translate_bit(0, A) :- gensym(aux_wire, A).
translate_bit(1, A) :- gensym(aux_wire, A).
%
% compare_results(ExpectedResult, Result, AllClauses, TailClauses) :-
%   gensym(aux_wire, A),
%   ( phrase(compare_values(ExpectedResult, Result, CmpClause, A),
%       AllClauses, [ ~(A), CmpClause | TailClauses ]), !
%   ; format("Results do not match~n"), fail
%   ).
%
% compare_values(N, M, C, C) --> { number(N), !, N = M }.
% compare_values((V1, V2), (W1, W2), C1, C3) --> !,
%   compare_values(V1, W1, C1, C2),
%   compare_values(V2, W2, C2, C3).
% compare_values(BS, SS, C1, C2) --> compare_bitvec(BS, SS, C1, C2).
%
% compare_bitvec([], [], C, C) --> {}.
% compare_bitvec([B|BS], [S|SS], C1, C3) -->
%   compare_bit(B, S, C1, C2),
%   compare_bitvec(BS, SS, C2, C3).
%
% compare_bit(A, B, v(X, C), C) --> { atom(A), !, gensym(aux_wire, X) },
%   [ v(~(X), v(A, B)), v(~(X), v(~(A), ~(B))) ].
% compare_bit(0, B, v(B, C), C) --> {}.
% compare_bit(1, B, v(~(B), C), C) --> {}.

% =============================================================================
% Parsowanie i uruchamianie

parse_program(Path, Program) :-
  read_file_to_codes(Path, Codes, []),
  catch(
      ( parse(Path, Codes, Program) -> true
      ; format("Syntax error~n"), fail),
    syntax_error(Reason, Pos),
    (print_error(Pos, "Syntax error:", Reason), fail)).


eval_program(Program, FuncName, Arg, Result, Clauses) :-
  catch(
      ( run(Program, FuncName, Arg, Result, Clauses) -> true
      ; format("Runtime error~n"), fail),
    runtime_error(Reason, Pos),
    (print_error(Pos, "Runtime error:", Reason), fail)).

print_error(no, Level, Reason) :-
  format("~s: ~w~n", [ Level, Reason]).
print_error(file(Path, Line, LinePos, _), Level, Reason) :-
  format("~w:~w:~w: ~s: ~w~n", [ Path, Line, LinePos, Level, Reason]).
print_error(file(Path, Line, LinePos, CNum, Length), Level, Reason) :-
  ( Length =< 1 -> print_error(file(Path, Line, LinePos, CNum), Level, Reason)
  ; LinePos2 is LinePos + Length - 1,
    format("~w:~w:~w-~w: ~s: ~w~n",
      [ Path, Line, LinePos, LinePos2, Level, Reason])
  ).

% =============================================================================
% Weryfikacja

% solve_clauses(Vars, Clauses) :-
%   ( current_predicate(solve/2) -> find_counterexample(Vars, Clauses)
%   ; current_predicate(prove/2) -> find_proof(Clauses)
%   ; format("No solver to prove correctness~n")
%   ).
%
% find_counterexample(Vars, Clauses) :-
%   ( solve(Clauses, Valuation) ->
%     format("Counter-example found: ~n"),
%     maplist(print_valuation(Valuation), Vars)
%   ; format("OK~n")
%   ).
%
% print_valuation(Valuation, X) :-
%   member((X, V), Valuation),
%   ( V = t -> format("~w~t~8|=  1~n", [ X ])
%   ; V = f -> format("~w~t~8|=  0~n", [ X ])
%   ; true
%   ).
%
% find_proof(Clauses) :-
%   ( prove(Clauses, _) -> format("OK~n")
%   ; format("No proof has been found~n")
%   ).
