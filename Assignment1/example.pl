% Definiujemy moduł zawierający rozwiązanie.
% Należy zmienić nazwę modułu na {imie}_{nazwisko} gdzie za
% {imie} i {nazwisko} należy podstawić odpowiednio swoje imię
% i nazwisko bez wielkich liter oraz znaków diakrytycznych
:- module(imie_nazwisko, [resolve/4, prove/2]).

% definiujemy operatory ~/1 oraz v/2
:- op(200, fx, ~).
:- op(500, xfy, v).

% Szukanie rezolwenty.
% UWAGA: to nie jest jeszcze rozwiązanie; należy zmienić definicję
% tego predykatu
resolve(q, p v q, ~q v r, r v p).

% Główny predykat rozwiązujący zadanie.
% UWAGA: to nie jest jeszcze rozwiązanie; należy zmienić jego
% definicję.
prove(Clauses, Proof) :-
  Clauses = [p v q v ~r, ~p v q, r v q, ~q, p],
  Proof   = [(p v q v ~r, axiom), (~p v q, axiom), (q v ~r, o(p, 1, 2)),
    (r v q, axiom), (q, o(r, 4, 3)), (~q, axiom), ([], o(q, 5, 6))].
