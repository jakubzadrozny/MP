% Definiujemy moduł zawierający rozwiązanie.
% Należy zmienić nazwę modułu na {imie}_{nazwisko} gdzie za
% {imie} i {nazwisko} należy podstawić odpowiednio swoje imię
% i nazwisko bez wielkich liter oraz znaków diakrytycznych
:- module(hdml_parser, [parse/3]).

% start_pos(_, no) :- !.
start_pos(F, file(F, 1, 1, 0)).

change_pos(no, _, no).
change_pos(file(F, Line, LinePos, CharNo), N, file(F, Line, LinePos1, CharNo1)) :-
    LinePos1 is LinePos + N,
    CharNo1 is CharNo + N.

update_pos(no, _, no).
update_pos(file(F, Line, _, CharNo), C, file(F, Line1, 1, CharNo)) :-
    code_type(C, newline), !,
    Line1 is Line + 1.
% update_pos(file(F, Line, LinePos, CharNo), C, file(F, Line, LinePos1, CharNo)) :-
%     code_type(C, space), !,
%     LinePos1 is LinePos + 1.
update_pos(file(F, Line, LinePos, CharNo), _, file(F, Line, LinePos1, CharNo1)) :-
    LinePos1 is LinePos + 1,
    CharNo1 is CharNo + 1.

lexer(Tokens, Pos) -->
    white_space(Pos, Pos1),
    comment(Pos1, Pos2), !,
    lexer(Tokens, Pos2).
lexer(Tokens, Pos) -->
    white_space(Pos, Pos1),
    ( operator(Token, Pos1, Pos2), ! ;
      number(Token, Pos1, Pos2), !;
      identifier(Token, Pos1, Pos2) ),
    !, { Tokens = [token(Token, Pos1) | Rest] },
    lexer(Rest, Pos2).
lexer([token(tokEOF, Pos)], Pos) --> white_space(Pos, _).

white_space(Pos, Pos1) --> [C], { code_type(C, space), update_pos(Pos, C, Pos2) }, !, white_space(Pos2, Pos1).
white_space(Pos, Pos) --> [].

comment(Pos, Pos1) --> `(*`, { change_pos(Pos, 2, Pos2) }, end_comment(Pos2, Pos1).
end_comment(Pos, Pos1) --> `*)`, !, { change_pos(Pos, 2, Pos1) }.
end_comment(Pos, Pos1) --> `(*`, !, { change_pos(Pos, 2, Pos2) }, end_comment(Pos2, Pos3), end_comment(Pos3, Pos1).
end_comment(Pos, Pos1) --> [X], !, { update_pos(Pos, X, Pos2) }, end_comment(Pos2, Pos1).
end_comment(Pos, Pos) --> [].

operator_podwojny(Token) --> [X, Y], { member(([X, Y], Token), [
    (`<>`, tokDiff),
    (`..`, tokDots),
    (`<=`, tokLeq),
    (`>=`, tokGeq) ]) }.

operator_pojedynczy(Token) --> [X], { member(([X], Token), [
    (`(`, tokLParen),
    (`)`, tokRParen),
    (`[`, tokLBracket),
    (`]`, tokRBracket),
    (`,`, tokComma),
    (`=`, tokEq),
    (`<`, tokLess),
    (`>`, tokGreater),
    (`^`, tokPower),
    (`|`, tokLine),
    (`+`, tokPlus),
    (`-`, tokMinus),
    (`&`, tokAnd),
    (`*`, tokTimes),
    (`/`, tokDiv),
    (`%`, tokPercent),
    (`@`, tokAt),
    (`#`, tokHash),
    (`~`, tokTylda) ])}.

operator(Token, Pos, Pos1) --> operator_podwojny(Token), !, { change_pos(Pos, 2, Pos1) }.
operator(Token, Pos, Pos1) --> operator_pojedynczy(Token), { change_pos(Pos, 1, Pos1) }.

digits(Dig, Pos, Pos1) --> [D],
    { code_type(D, digit), Dig = [D | Rest], change_pos(Pos, 1, Pos2) }, !,
    digits(Rest, Pos2, Pos1).
digits([], Pos, Pos) --> [].

number(tokNum(Num), Pos, Pos1) --> digits(Dig, Pos, Pos1), { Dig \= [], number_chars(Num, Dig) }.

characters(Chars, Pos, Pos1) --> [C],
    { (code_type(C, csym); C = 39), Chars = [C | Rest], change_pos(Pos, 1, Pos2) }, !,
    characters(Rest, Pos2, Pos1).
characters([], Pos, Pos) --> [].

identifier(Token, Pos, Pos1) -->
    [Start], { code_type(Start, csymf), change_pos(Pos, 1, Pos2) },
    characters(Chars, Pos2, Pos1),
    { keyword([Start | Chars], Token) -> true;
        atom_codes(Id, [Start | Chars]),
        Token = tokIdent(Id) }.

keyword(Chars, Token) :- member((Chars, Token), [
    (`def`, tokDef),
    (`else`, tokElse),
    (`if`, tokIf),
    (`in`, tokIn),
    (`let`, tokLet),
    (`then`, tokThen),
    (`_`, tokUnderscore) ]).

token_string(tokIdent(_), "identifier") :- !.
token_string(tokNum(_), "number") :- !.
token_string(Tok, Str) :- atom_string(Tok, Str).

demand_token(Tok) --> [token(Tok, _)], !.
demand_token(tokEOF) --> [token(_, Pos)], !, { throw(syntax_error("unexpected token - definition ended", Pos)) }.
demand_token(Tok) --> [token(tokEOF, Pos)], !,
    { token_string(Tok, Str), string_concat("unexpected end of file - missing token", Str, Msg), throw(syntax_error(Msg, Pos)) }.
demand_token(Tok) --> [token(_, Pos)],
    { token_string(Tok, Str), string_concat("missing token ", Str, Msg), throw(syntax_error(Msg, Pos)) }.

demand(Goal) --> call(Goal), !.
demand(_) --> [token(tokEOF, Pos)], !, { throw(syntax_error("unexpected end of file - missing expression", Pos)) }.
demand(_) --> [token(_, Pos)], { throw(syntax_error("missing expression", Pos)) }.

program(Program) --> definicje(Program).

definicje([Def | Rest]) --> definicja(Def), !, definicje(Rest).
definicje([]) --> demand_token(tokEOF).

definicja(def(Name, P, E)) -->
    [token(tokDef, _)],
    demand_token(tokIdent(Name)),
    demand_token(tokLParen),
    demand(wzorzec(P)),
    demand_token(tokRParen),
    demand_token(tokEq),
    demand(wyrazenie(E)).

prosty_wzorzec(wildcard(Pos)) --> [token(tokUnderscore, Pos)], !.
prosty_wzorzec(X) --> zmienna(X), !.
prosty_wzorzec(X) --> [token(tokLParen, _)], wzorzec(X), demand_token(tokRParen).

wzorzec(Wz) --> prosty_wzorzec(X),
    ([token(tokComma, Pos)] -> { Wz = pair(Pos, X, Y) }, demand(wzorzec(Y)) ; { Wz = X }).

wyrazenie(if(Pos, E1, E2, E3)) -->
    [token(tokIf, Pos)], !,
    demand(wyrazenie(E1)),
    demand_token(tokThen),
    demand(wyrazenie(E2)),
    demand_token(tokElse),
    demand(wyrazenie(E3)).
wyrazenie(let(Pos, P, E1, E2)) -->
    [token(tokLet, Pos)], !,
    demand(wzorzec(P)),
    demand_token(tokEq),
    demand(wyrazenie(E1)),
    demand_token(tokIn),
    demand(wyrazenie(E2)).
wyrazenie(X) --> wyrazenie_op(X).

wyrazenie_op(Wyr) --> wyrazenie_cmp(X),
    ([token(tokComma, Pos)] -> { Wyr = pair(Pos, X, Y) }, demand(wyrazenie_op(Y)); { Wyr = X }).

wyrazenie_cmp(Wyr) --> wyrazenie_malpa(X),
    (operator_cmp(Op, Pos) -> { Wyr = op(Pos, Op, X, Y) }, demand(wyrazenie_malpa(Y)); { Wyr = X }).

wyrazenie_malpa(Wyr) --> wyrazenie_add(X),
    ([token(tokAt, Pos)] -> { Wyr = op(Pos, @, X, Y) }, demand(wyrazenie_malpa(Y)); { Wyr = X }).

wyrazenie_add(Wyr) --> wyrazenie_mult(X), wyrazenie_add(X, Wyr).
wyrazenie_add(Acc, Wyr) -->
    operator_add(Op, Pos), !,
    demand(wyrazenie_mult(X)),
    wyrazenie_add(op(Pos, Op, Acc, X), Wyr).
wyrazenie_add(Acc, Acc) --> [].

wyrazenie_mult(Wyr) --> wyrazenie_unarne(X), wyrazenie_mult(X, Wyr).
wyrazenie_mult(Acc, Wyr) -->
    operator_mult(Op, Pos), !,
    demand(wyrazenie_unarne(X)),
    wyrazenie_mult(op(Pos, Op, Acc, X), Wyr).
wyrazenie_mult(Acc, Acc) --> [].

wyrazenie_unarne(op(Pos, Op, X)) --> operator_unarny(Op, Pos), !, demand(wyrazenie_unarne(X)).
wyrazenie_unarne(X) --> wyrazenie_proste(X).

wyrazenie_nawiasowe(X) --> wyrazenie_atomowe(X), !.
wyrazenie_nawiasowe(X) --> [token(tokLParen, _)], wyrazenie(X), demand_token(tokRParen).

wyrazenie_proste(Wyr) --> wyrazenie_nawiasowe(X), wyrazenie_proste(X, Wyr).
wyrazenie_proste(Acc, Wyr) -->
    [token(tokLBracket, Pos)], !,
    demand(wyrazenie(X)),
    ([token(tokRBracket, _)] -> wyrazenie_proste(bitsel(Pos, Acc, X), Wyr);
        demand_token(tokDots),
        demand(wyrazenie(Y)),
        demand_token(tokRBracket),
        wyrazenie_proste(bitsel(Pos, Acc, X, Y), Wyr)).
wyrazenie_proste(Acc, Acc) --> [].

wyrazenie_atomowe(X) --> funkcja(X), !.
wyrazenie_atomowe(X) --> zmienna(X), !.
wyrazenie_atomowe(X) --> liczba(X), !.
wyrazenie_atomowe(X) --> pusty(X), !.
wyrazenie_atomowe(X) --> jeden_bit(X).

zmienna(var(Pos, X)) --> [token(tokIdent(X), Pos)].
funkcja(call(Pos, Name, E)) -->
    [token(tokIdent(Name), Pos), token(tokLParen, _)],
    demand(wyrazenie(E)),
    demand_token(tokRParen).
liczba(num(Pos, N)) --> [token(tokNum(N), Pos)].
pusty(empty(Pos)) --> [token(tokLBracket, Pos), token(tokRBracket, _)].
jeden_bit(bit(Pos, E)) --> [token(tokLBracket, Pos)], wyrazenie(E), [token(tokRBracket, _)].

operator_cmp(Op, Pos) --> [token(Tok, Pos)], { member((Tok, Op), [
    (tokEq, '='),
    (tokDiff, '<>'),
    (tokLess, '<'),
    (tokGreater, '>'),
    (tokLeq, '<='),
    (tokGeq, '>=') ]) }.

operator_add(Op, Pos) --> [token(Tok, Pos)], { member((Tok, Op), [
    (tokLine, '|'),
    (tokPower, '^'),
    (tokPlus, '+'),
    (tokMinus, '-') ]) }.

operator_mult(Op, Pos) --> [token(Tok, Pos)], { member((Tok, Op), [
    (tokAnd, '&'),
    (tokTimes, '*'),
    (tokDiv, '/'),
    (tokPercent, '%') ]) }.

operator_unarny(Op, Pos) --> [token(Tok, Pos)], { member((Tok, Op), [
    (tokMinus, '-'),
    (tokHash, '#'),
    (tokTylda, '~') ]) }.

parse(Path, Codes, Program) :-
    start_pos(Path, Pos),
    phrase(lexer(Tokens, Pos), Codes),
    phrase(program(Program), Tokens).
