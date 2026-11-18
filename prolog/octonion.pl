:- encoding(utf8).
/*  Integer octonions in Prolog (SWI-Prolog), with the repository's Cayley–Dickson table
    (e_i e_j = sgn(i,j) e_{i xor j}).

    The identities the theorem needs are checked by *polarisation on the basis*. This is a complete check,
    not sampling: the product is bilinear by definition, so every identity used here is linear in some
    arguments and quadratic in one. Such an identity holds for all octonions iff it holds when
    - each linear argument ranges over the basis e_0..e_7, and
    - the quadratic argument ranges over e_i and e_i + e_j.
    Lemma W's determinant identity is trilinear, so the basis alone suffices for it.
    Random large-integer tests are added as an independent sanity check.

    Usage:   swipl -q -g main -t halt octonion.pl
*/

:- module(octonion, [omul/3, oadd/3, osub/3, assoc/4, unit/2, zero/1, oeq/2, main/0]).

sgn_row(0, [1, 1, 1, 1, 1, 1, 1, 1]).
sgn_row(1, [1, -1, 1, -1, 1, -1, -1, 1]).
sgn_row(2, [1, -1, -1, 1, 1, 1, -1, -1]).
sgn_row(3, [1, 1, -1, -1, 1, -1, 1, -1]).
sgn_row(4, [1, -1, -1, -1, -1, 1, 1, 1]).
sgn_row(5, [1, 1, -1, 1, -1, -1, -1, 1]).
sgn_row(6, [1, 1, 1, -1, -1, 1, -1, -1]).
sgn_row(7, [1, -1, 1, 1, -1, -1, 1, -1]).

sgn(I, J, S) :- sgn_row(I, Row), nth0(J, Row, S).

zero([0, 0, 0, 0, 0, 0, 0, 0]).
unit(I, U) :- numlist(0, 7, Ks), maplist(unit_entry(I), Ks, U).
unit_entry(I, K, V) :- ( K =:= I -> V = 1 ; V = 0 ).

oadd(A, B, C) :- maplist([X, Y, Z]>>(Z is X + Y), A, B, C).
osub(A, B, C) :- maplist([X, Y, Z]>>(Z is X - Y), A, B, C).
oeq(A, B) :- A == B.

%% (ab)_k = sum_i sgn(i, i xor k) a_i b_{i xor k}
omul(A, B, C) :- numlist(0, 7, Ks), maplist(omul_comp(A, B), Ks, C).
omul_comp(A, B, K, CK) :-
    aggregate_all(sum(T), ( between(0, 7, I), J is I xor K, sgn(I, J, S),
                            nth0(I, A, AI), nth0(J, B, BJ), T is S * AI * BJ ), CK).

assoc(A, B, C, D) :- omul(A, B, AB), omul(AB, C, L), omul(B, C, BC), omul(A, BC, R), osub(L, R, D).

/* identities: argument roles (quad / lin), and LHS - RHS */
roles(moufang_left, [quad, lin, lin]).
roles(moufang_right, [quad, lin, lin]).
roles(moufang_middle, [quad, lin, lin]).
roles(left_alternative, [quad, lin]).
roles(right_alternative, [quad, lin]).
roles(flexible, [quad, lin]).

identity(moufang_left,  [quad, lin, lin], [A, B, C], D) :-
    omul(A, C, AC), omul(B, AC, BAC), omul(A, BAC, L),
    omul(A, B, AB), omul(AB, A, ABA), omul(ABA, C, R), osub(L, R, D).
identity(moufang_right, [quad, lin, lin], [A, B, C], D) :-
    omul(C, A, CA), omul(CA, B, CAB), omul(CAB, A, L),
    omul(B, A, BA), omul(A, BA, ABA), omul(C, ABA, R), osub(L, R, D).
identity(moufang_middle, [quad, lin, lin], [A, B, C], D) :-
    omul(A, B, AB), omul(C, A, CA), omul(AB, CA, L),
    omul(B, C, BC), omul(BC, A, BCA), omul(A, BCA, R), osub(L, R, D).
identity(left_alternative, [quad, lin], [A, B], D) :-
    omul(A, A, AA), omul(AA, B, L), omul(A, B, AB), omul(A, AB, R), osub(L, R, D).
identity(right_alternative, [quad, lin], [A, B], D) :-
    omul(B, A, BA), omul(BA, A, L), omul(A, A, AA), omul(B, AA, R), osub(L, R, D).
identity(flexible, [quad, lin], [A, B], D) :-
    omul(A, B, AB), omul(AB, A, L), omul(B, A, BA), omul(A, BA, R), osub(L, R, D).

%% the substitution values for one role
role_value(lin, U) :- between(0, 7, I), unit(I, U).
role_value(quad, U) :- between(0, 7, I), unit(I, U).
role_value(quad, U) :- between(0, 7, I), between(0, 7, J), I < J, unit(I, UI), unit(J, UJ), oadd(UI, UJ, U).

check_identity(Name) :-
    roles(Name, Roles),
    aggregate_all(count, maplist(role_value, Roles, _), Cases),
    forall(( maplist(role_value, Roles, Vals), identity(Name, Roles, Vals, D) ),
           ( zero(D) -> true ; format("IDENTITY FAILS ~w ~w~n", [Name, Vals]), fail )),
    format("~w: polarised basis check, ~d cases: ok~n", [Name, Cases]).

random_oct(O) :- length(O, 8), maplist([X]>>(random_between(-1000000, 1000000, X)), O).

check_random(N) :-
    forall(( between(1, N, _), roles(Name, Roles), length(Roles, K), length(Vals, K),
             maplist(random_oct, Vals) ),
           ( identity(Name, Roles, Vals, D), zero(D) -> true ; format("RANDOM FAILS~n"), fail )),
    format("random 7-digit integer octonions: ~d rounds of all identities: ok~n", [N]).

%% Lemma W core: for X, Y, Z in span(e1, e2, e4), [X,Y,Z] = det * [e1,e2,e4]; trilinear, basis suffices.
sp([X0, X1, X2], [0, X0, X1, 0, X2, 0, 0, 0]).
det3([A0, A1, A2], [B0, B1, B2], [C0, C1, C2], D) :-
    D is A0*(B1*C2 - B2*C1) - A1*(B0*C2 - B2*C0) + A2*(B0*C1 - B1*C0).
coord_basis([1, 0, 0]). coord_basis([0, 1, 0]). coord_basis([0, 0, 1]).

scale(D, E, V) :- V is D * E.

check_lemmaW :-
    unit(1, E1), unit(2, E2), unit(4, E4), assoc(E1, E2, E4, E124),
    format("[e1,e2,e4] = ~w~n", [E124]),
    \+ zero(E124),
    forall(( coord_basis(X), coord_basis(Y), coord_basis(Z) ),
           ( sp(X, SX), sp(Y, SY), sp(Z, SZ), assoc(SX, SY, SZ, Lhs), det3(X, Y, Z, D),
             maplist(scale(D), E124, Rhs), Lhs == Rhs )),
    format("Lemma W core [X,Y,Z] = det(X,Y,Z)[e1,e2,e4] on span(e1,e2,e4): ok (27 basis triples, trilinear)~n").

%% the check has teeth: plain associativity is NOT an octonion identity and the same search finds that
check_not_associative :-
    unit(1, E1), unit(2, E2), unit(4, E4), assoc(E1, E2, E4, D), \+ zero(D),
    format("negative control: associativity fails on (e1, e2, e4), as it must~n").

main :-
    forall(roles(Name, _), check_identity(Name)),
    check_not_associative,
    check_random(200),
    check_lemmaW.
