:- encoding(utf8).
/*  The algebraic lemmas, checked in Prolog against the repository's integer octonions (octonion.pl).

    - Lemma W, expansion step: substitute each letter by a truncated series 1 + θq + θ²r + θ³t
      (q = v¹e1 + v²e2 + v³e4 from the letter's count coordinates; r, t arbitrary octonions, which covers
      exp(θq) and any higher-order terms). The local associator of three bracketings A, B, C has zero
      θ⁰, θ¹, θ² coefficients and θ³ coefficient 2·det(counts)·e7.
    - L1: norm multiplicativity, no zero divisors, and context cancellation C[S1] = C[S2] ⟺ S1 = S2.
    - Artin / Lemma V: all bracketings of a word over two octonion values agree; three values do not.
    - K, octonion side: setting killed letters to 1 gives the value of the restricted bracketing.

    Random tests with a fixed seed; each check has a negative control.

    Usage:   swipl -q -g main -t halt algebra.pl
*/

:- use_module(octonion, [omul/3, oadd/3, osub/3, assoc/4, unit/2, zero/1]).

/* ---------------- utilities ---------------- */

rnd_oct(B, O) :- length(O, 8), maplist(rnd_int(B), O).
rnd_int(B, X) :- L is -B, random_between(L, B, X).
rnd_nonzero(B, O) :- rnd_oct(B, O0), ( zero(O0) -> rnd_nonzero(B, O) ; O = O0 ).
oscale(K, A, B) :- maplist(mulk(K), A, B).
mulk(K, X, Y) :- Y is K * X.

%% all bracketings of the positions Ps (a list)
tree([P], leaf(P)) :- !.
tree(Ps, node(L, R)) :- append(As, Bs, Ps), As \= [], Bs \= [], tree(As, L), tree(Bs, R).

%% a random bracketing of the positions Ps
rtree([P], leaf(P)) :- !.
rtree(Ps, node(L, R)) :- length(Ps, N), N1 is N - 1, random_between(1, N1, K),
    length(As, K), append(As, Bs, Ps), rtree(As, L), rtree(Bs, R).

leaves(leaf(I), [I]).
leaves(node(L, R), Is) :- leaves(L, A), leaves(R, B), append(A, B, Is).

%% value of a bracketing; Val maps letters to octonions
ev(W, Val, leaf(I), V) :- nth0(I, W, C), memberchk(C-V, Val).
ev(W, Val, node(L, R), V) :- ev(W, Val, L, A), ev(W, Val, R, B), omul(A, B, V).

rand_word(Letters, N, W) :- length(W, N), maplist(rand_letter(Letters), W).
rand_letter(Ls, C) :- random_member(C, Ls).

/* ---------------- Lemma W: truncated series ---------------- */

%% series [S0, S1, S2, S3] with octonion coefficients; product truncated after θ³
smul([P0, P1, P2, P3], [Q0, Q1, Q2, Q3], [R0, R1, R2, R3]) :-
    omul(P0, Q0, R0),
    omul(P0, Q1, A1), omul(P1, Q0, B1), oadd(A1, B1, R1),
    omul(P0, Q2, A2), omul(P1, Q1, B2), omul(P2, Q0, C2), oadd(A2, B2, D2), oadd(D2, C2, R2),
    omul(P0, Q3, A3), omul(P1, Q2, B3), omul(P2, Q1, C3), omul(P3, Q0, D3),
    oadd(A3, B3, E3), oadd(C3, D3, F3), oadd(E3, F3, R3).
ssub(P, Q, R) :- maplist(osub, P, Q, R).
sassoc(P, Q, R, D) :- smul(P, Q, PQ), smul(PQ, R, L), smul(Q, R, QR), smul(P, QR, Rt), ssub(L, Rt, D).

sev(W, Sub, leaf(I), S) :- nth0(I, W, C), memberchk(C-S, Sub).
sev(W, Sub, node(L, R), S) :- sev(W, Sub, L, A), sev(W, Sub, R, B), smul(A, B, S).

%% q for letter x, y, z: e1, e2, e4; any other letter: 0
qof(x, Q) :- unit(1, Q).
qof(y, Q) :- unit(2, Q).
qof(z, Q) :- unit(4, Q).
qof(C, Q) :- \+ memberchk(C, [x, y, z]), zero(Q).

count_letter(W, T, C, K) :- leaves(T, Is), aggregate_all(count, (member(I, Is), nth0(I, W, C)), K).
cvec(W, T, [X, Y, Z]) :- count_letter(W, T, x, X), count_letter(W, T, y, Y), count_letter(W, T, z, Z).
det3([A0, A1, A2], [B0, B1, B2], [C0, C1, C2], D) :-
    D is A0*(B1*C2 - B2*C1) - A1*(B0*C2 - B2*C0) + A2*(B0*C1 - B1*C0).

%% split positions 0..N-1 (N >= 3) into three nonempty consecutive segments, bracket each at random
three_trees(N, TA, TB, TC) :-
    N2 is N - 2, N1 is N - 1, random_between(1, N2, I), I1 is I + 1, random_between(I1, N1, J),
    numlist(0, N1, Ps), length(As, I), append(As, Rest, Ps), K is J - I, length(Bs, K), append(Bs, Cs, Rest),
    rtree(As, TA), rtree(Bs, TB), rtree(Cs, TC).

lemmaW_round(Ok) :-
    random_between(3, 8, N), rand_word([x, y, z, d], N, W),
    three_trees(N, TA, TB, TC),
    unit(0, One),
    findall(C-[One, Q, R, T], ( member(C, [x, y, z, d]), qof(C, Q), rnd_oct(50, R), rnd_oct(50, T) ), Sub),
    sev(W, Sub, TA, PA), sev(W, Sub, TB, PB), sev(W, Sub, TC, PC),
    sassoc(PA, PB, PC, [D0, D1, D2, D3]),
    cvec(W, TA, VA), cvec(W, TB, VB), cvec(W, TC, VC), det3(VA, VB, VC, Det),
    unit(7, E7), K is 2 * Det, oscale(K, E7, Want),
    ( zero(D0), zero(D1), zero(D2), D3 == Want -> Ok = true ; Ok = false ).

check_lemmaW(N) :-
    unit(1, E1), unit(2, E2), unit(4, E4), assoc(E1, E2, E4, E124), unit(7, E7), oscale(2, E7, E124),
    findall(Ok, (between(1, N, _), lemmaW_round(Ok)), Oks),
    ( memberchk(false, Oks) -> format("Lemma W expansion: FAILED~n"), fail ; true ),
    format("Lemma W expansion: θ⁰..θ² coefficients vanish and θ³ = 2·det·e7, ~d random rounds: ok~n", [N]),
    % negative control: without the det factor the θ³ claim fails on (x)(y)(z)
    Sub = [x-[O, E1, R0, R0], y-[O, E2, R0, R0], z-[O, E4, R0, R0]], unit(0, O), zero(R0),
    sev([x, y, z], Sub, leaf(0), PA), sev([x, y, z], Sub, leaf(1), PB), sev([x, y, z], Sub, leaf(2), PC),
    sassoc(PA, PB, PC, [_, _, _, D3]), \+ zero(D3),
    format("  control: the θ³ coefficient of [x, y, z] is nonzero (det = 1)~n").

/* ---------------- L1: division algebra ---------------- */

conj([A0 | As], [A0 | Bs]) :- maplist([X, Y]>>(Y is -X), As, Bs).
norm(A, N) :- foldl([X, S0, S]>>(S is S0 + X * X), A, 0, N).

check_division(N) :-
    forall(between(1, N, _),
           ( rnd_oct(1000, A), rnd_oct(1000, B), omul(A, B, AB), norm(A, NA), norm(B, NB), norm(AB, NAB),
             NAB =:= NA * NB,
             conj(A, CA), omul(A, CA, ACA), unit(0, U), oscale(NA, U, ACA),
             ( zero(AB) -> ( zero(A) ; zero(B) ) ; true ) )),
    format("L1: N(ab) = N(a)N(b), a·ā = N(a), no zero divisors, ~d random pairs: ok~n", [N]).

%% contexts: hole, inL(C, R), inR(L, C)
fill(hole, S, S).
fill(inL(C, R), S, node(T, R)) :- fill(C, S, T).
fill(inR(L, C), S, node(L, T)) :- fill(C, S, T).

check_context(N) :-
    findall(E1-E2, ( between(1, N, _), context_round(E1, E2) ), Ps),
    ( forall(member(E1-E2, Ps), E1 == E2) -> true ; format("context cancellation: FAILED~n"), fail ),
    aggregate_all(count, member(true-true, Ps), NT),
    format("L1: C[S1] = C[S2] ⟺ S1 = S2 for nonzero letter values, ~d random cases (~d equal pairs): ok~n", [N, NT]).

%% S1, S2 bracket the same leaves; half the rounds use two letters (Artin makes S1 = S2)
context_round(E1, E2) :-
    random_between(4, 8, N), ( maybe -> Ls = [x, y] ; Ls = [x, y, z] ), rand_word(Ls, N, W),
    N1 is N - 1, numlist(0, N1, Ps),
    random_between(0, N1, I0), random_between(I0, N1, J0), ( J0 - I0 < 2 -> I = 0, J = N1 ; I = I0, J = J0 ),
    findall(P, (member(P, Ps), P >= I, P =< J), Mid), rtree(Mid, S1), rtree(Mid, S2),
    findall(P, (member(P, Ps), P < I), Pre), findall(P, (member(P, Ps), P > J), Post),
    append(Pre, [h | Post], Outer), rtree(Outer, OT), ctx_of(OT, C),
    findall(L-V, ( member(L, [x, y, z]), rnd_nonzero(9, V) ), Val),
    fill(C, S1, F1), fill(C, S2, F2),
    ev(W, Val, F1, V1), ev(W, Val, F2, V2), ev(W, Val, S1, U1), ev(W, Val, S2, U2),
    ( V1 == V2 -> E1 = true ; E1 = false ), ( U1 == U2 -> E2 = true ; E2 = false ).

ctx_of(leaf(h), hole) :- !.
ctx_of(node(L, R), C) :- ( leaves(L, Ls), memberchk(h, Ls) -> ctx_of(L, C0), C = inL(C0, R) ; ctx_of(R, C0), C = inR(L, C0) ).

/* ---------------- Artin's theorem / Lemma V ---------------- */

check_artin :-
    rnd_oct(30, U), rnd_oct(30, V),
    forall(( between(3, 7, N), rand_word([u, v], N, W) ),
           ( N1 is N - 1, numlist(0, N1, Ps), findall(X, (tree(Ps, T), ev(W, [u-U, v-V], T, X)), Xs),
             sort(Xs, [_]) )),
    forall(( between(1, 20, _), random_between(3, 7, N), rand_word([u, v], N, W) ),
           ( N1 is N - 1, numlist(0, N1, Ps), findall(X, (tree(Ps, T), ev(W, [u-U, v-V], T, X)), Xs),
             sort(Xs, [_]) )),
    format("Artin: every bracketing of a word over two random octonions has the same value (n ≤ 7): ok~n"),
    rnd_oct(30, Z),
    findall(X, (tree([0, 1, 2], T), ev([u, v, z], [u-U, v-V, z-Z], T, X)), Ys), sort(Ys, Ys1), length(Ys1, 2),
    format("  control: with a third generic value the two bracketings of uvz differ~n").

/* ---------------- K, octonion side ---------------- */

restrict(W, K, leaf(I), R) :- nth0(I, W, C), ( memberchk(C, K) -> R = none ; R = leaf(I) ).
restrict(W, K, node(L, Rt), R) :-
    restrict(W, K, L, A), restrict(W, K, Rt, B),
    ( A == none -> R = B ; B == none -> R = A ; R = node(A, B) ).

check_kill(N) :-
    unit(0, One),
    forall(between(1, N, _),
           ( random_between(2, 8, M), rand_word([a, b, c, d], M, W), M1 is M - 1, numlist(0, M1, Ps),
             rtree(Ps, T), random_member(K, [[a], [b], [a, c], [d], [a, b, c, d]]),
             findall(L-V, ( member(L, [a, b, c, d]), ( memberchk(L, K) -> V = One ; rnd_oct(20, V) ) ), Val),
             ev(W, Val, T, X), restrict(W, K, T, R),
             ( R == none -> X == One ; ev(W, Val, R, Y), X == Y ) )),
    format("K: killed letters set to 1 give the restricted bracketing's value, ~d random cases: ok~n", [N]).

main :-
    set_stream(user_output, encoding(utf8)),
    set_random(seed(2026)),
    check_lemmaW(300),
    check_division(300),
    check_context(300),
    check_artin,
    check_kill(300).
