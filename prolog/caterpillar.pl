/*  Caterpillar certificates in Prolog (SWI-Prolog).

    This file covers the run-sequence combinatorics and the finite base of Proposition E (THEOREM.md).
    It mirrors the Lean development in ../lean.

    - A run sequence is a list over x, y, z with no two equal neighbours.
    - chain/3 and cat/3 relate a sequence S and an entry letter E (none or a letter) to a derivation
      term. They are the logical definitions: they CHECK a given derivation and SEARCH for one.
    - construct/3 follows the induction proof of Proposition E, without search, and uses the search
      only for the base of 4 and 5 runs. Its output is re-checked by cat/3.

    Usage:   swipl -q -g main -t halt caterpillar.pl
*/

:- module(caterpillar, [valid/1, failure/2, cat/3, chain/3, construct/3, runs/2, main/0]).

letter(x). letter(y). letter(z).

third(A, B, C) :- letter(C), C \== A, C \== B, A \== B.

noadj([]).
noadj([_]).
noadj([A, B | T]) :- A \== B, noadj([B | T]).

allthree(S) :- memberchk(x, S), memberchk(y, S), memberchk(z, S).

valid(S) :- noadj(S), allthree(S), length(S, N), N >= 4.

%% cond(+EntryOpt, +PeeledLetter, +NextNode): condition (C1).
cond(none, _, _).
cond(some(A), B, Rest) :- A \== B, third(A, B, C), memberchk(C, Rest).

two_or_more([_, _ | _]).

%% chain(?S, +E, ?Derivation): conditions (C1), (C2), no move required.
chain([U, V], some(A), bottom) :- A \== U, A \== V, U \== V.
chain([C | T], E, l(D)) :-
    two_or_more(T), cond(E, C, T), chain(T, some(C), D).
chain(S, E, r(D)) :-
    append(T, [C], S), two_or_more(T), cond(E, C, T), chain(T, some(C), D).
chain([P | MP], E, d(D)) :-
    append(M, [P], MP), two_or_more(M), cond(E, P, M), chain(M, some(P), D).

%% chainL / chainR: after a left (right) Moufang pattern, the next step is L (R) or the bottom.
chain_l(S, E, bottom) :- S = [_, _], chain(S, E, bottom).
chain_l([C | T], E, l(D)) :- two_or_more(T), cond(E, C, T), chain(T, some(C), D).
chain_r(S, E, bottom) :- S = [_, _], chain(S, E, bottom).
chain_r(S, E, r(D)) :- append(T, [C], S), two_or_more(T), cond(E, C, T), chain(T, some(C), D).

%% cat(?S, +E, ?Derivation): certificate with a Moufang move.
cat([C | T], E, passL(D)) :-
    two_or_more(T), cond(E, C, T), cat(T, some(C), D).
cat(S, E, passR(D)) :-
    append(T, [C], S), two_or_more(T), cond(E, C, T), cat(T, some(C), D).
cat([P | MP], E, passD(D)) :-
    append(M, [P], MP), two_or_more(M), cond(E, P, M), cat(M, some(P), D).
cat([P | MP], E, moveD(D)) :-                         % middle Moufang x((BC)x) -> (xB)(Cx)
    append(M, [P], MP), two_or_more(M), cond(E, P, M), chain(M, some(P), D).
cat([X, Y, X | T], E, moveL(D)) :-                    % left Moufang x(Y(xC)) -> ((xY)x)C
    cond(E, X, [Y, X | T]), cond(some(X), Y, [X | T]), chain_l([X | T], some(Y), D).
cat(S, E, moveR(D)) :-                                % right Moufang ((Cx)Y)x -> C(x(Yx))
    append(T, [X, Y, X], S),
    append(T, [X, Y], TXY), append(T, [X], TX),
    cond(E, X, TXY), cond(some(X), Y, TX), chain_r(TX, some(Y), D).

%% failure(+S, +E): the excluded entries of Proposition E.
failure(S, some(P)) :- S = [P | _], last(S, P), !.
failure(S, some(P)) :- S = [P | _], append(Init, [_], S), \+ allthree(Init), !.
failure(S, some(P)) :- last(S, P), S = [_ | Tail], \+ allthree(Tail), !.

entry(none). entry(some(L)) :- letter(L).

/* ---------------- construct/3: the induction proof of Proposition E, as a program ---------------- */

construct(S, E, D) :-                                 % base: 4 or 5 runs, by search
    length(S, N), N =< 5, !, once(cat(S, E, D)).
construct(S, E, D) :-
    S = [C0 | Tail], append(Init, [CL], S), append(M, [CL], Tail),
    (   C0 == CL
    ->  (   allthree(M)                                       % Case 2a: D step
        ->  cond(E, C0, M), construct(M, some(C0), D1), D = passD(D1)
        ;   cond(E, C0, Tail), construct(Tail, some(C0), D1), D = passL(D1)   % Case 2b: L step
        )
    ;   (   E \== some(C0), allthree(Tail)                    % Case 1: L step if possible
        ->  cond(E, C0, Tail), construct(Tail, some(C0), D1), D = passL(D1)
        ;   E \== some(CL), allthree(Init)                    %         else R step
        ->  cond(E, CL, Init), construct(Init, some(CL), D1), D = passR(D1)
        ;   throw(error(proof_gap(S, E), _))                  % excluded by the proof: never reached
        )
    ).

/* ---------------- words and run sequences ---------------- */

runs([], []).
runs([A | T], R) :- runs(T, R0), ( R0 = [A | _] -> R = R0 ; R = [A | R0] ).

interval_word(W) :- runs(W, R), is_set(R).

/* ---------------- checks ---------------- */

seq(N, S) :- length(S, N), maplist(letter, S), valid(S).

%% Base of Proposition E: for 4 and 5 runs, Good(S, E) <=> not failure(S, E).
check_base :-
    forall(( member(N, [4, 5]), seq(N, S), entry(E) ),
           (   failure(S, E) -> \+ cat(S, E, _)
           ;   once(cat(S, E, _)) -> true
           ;   format("BASE FAILS ~w ~w~n", [S, E]), fail )),
    aggregate_all(count, (member(N, [4, 5]), seq(N, _), entry(_)), K),
    format("base R in {4,5}: ~d (sequence, entry) pairs, Good <=> not failure: ok~n", [K]).

%% The induction, run as a program: construct/3 succeeds and cat/3 re-checks its derivation.
check_construct(Max) :-
    forall(( between(4, Max, N), seq(N, S), entry(E), \+ failure(S, E) ),
           (   construct(S, E, D), cat(S, E, D) -> true
           ;   format("CONSTRUCT FAILS ~w ~w~n", [S, E]), fail )),
    aggregate_all(count, (between(4, Max, N), seq(N, S), entry(E), \+ failure(S, E)), K),
    format("construct/3 + cat/3 check, 4..~d runs: ~d certificates verified~n", [Max, K]).

%% Exact characterisation (sanity): search finds a certificate iff not failure.
check_characterisation(Max) :-
    forall(( between(6, Max, N), seq(N, S), entry(E) ),
           ( ( once(cat(S, E, _)) -> G = true ; G = false ),
             ( failure(S, E) -> F = true ; F = false ),
             ( G \== F -> true ; format("CHAR FAILS ~w ~w~n", [S, E]), fail ) )),
    format("characterisation Good <=> not failure, 6..~d runs: ok~n", [Max]).

%% Words: every non-interval word over x, y, z with all three letters has a valid run sequence.
check_words(Max) :-
    forall(( between(1, Max, N), length(W, N), maplist(letter, W), allthree(W), \+ interval_word(W) ),
           ( runs(W, R), valid(R), construct(R, none, D), cat(R, none, D) -> true
           ; format("WORD FAILS ~w~n", [W]), fail )),
    format("words of length <= ~d: every non-interval 3-letter word certified via its run sequence~n", [Max]).

main :-
    check_base,
    check_construct(12),
    check_characterisation(9),
    check_words(9).
