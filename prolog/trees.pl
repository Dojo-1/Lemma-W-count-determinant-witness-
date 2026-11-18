/*  G3 end to end in Prolog: from a word to two bracketings, and every link checked independently.

    For a non-interval word over x, y, z:
    1. Proposition E: construct/3 (caterpillar.pl) builds a run-level certificate.
    2. Translation: glue_cat/6 turns it into bracketings T0 and T1 and a chain of path nodes.
       This mirrors the Lean `glue_cat`.
    3. The independent checks:
       (a) mouf/3: T1 is obtained from T0 by one left, right or middle Moufang move, and the repeated
           variable is a single letter;
       (b) pchain/3: the chain satisfies the position-level conditions of Lemma Cat, and its nodes are
           nodes of T0;
       (c) certified/4: for every chain node, every compatible rotation that would delete it has det != 0.
           This checks Lemma Cat's conclusion by brute force over all rotation sites;
       (d) the stable-set argument of Lemma R': no tree D_N-reachable from T0 lacks a chain node. Here it
           is checked by exhaustive breadth-first search over D_N-flips (n <= 8), with no use of R';
       (e) Moufang equality: T0 and T1 evaluate to the same octonion under random integer octonions for
           the letters (octonion.pl), while some D_N-crossing is witnessed.

    Usage:   swipl -q -g main -t halt trees.pl
*/

:- encoding(utf8).
:- use_module(caterpillar, [construct/3]).
:- use_module(octonion, [omul/3]).

/* ---------------- trees ---------------- */

span(leaf(I), I, I).
span(node(L, R), Lo, Hi) :- span(L, Lo, _), span(R, _, Hi).

wf(leaf(_)).
wf(node(L, R)) :- wf(L), wf(R), span(L, _, H), span(R, Lo, _), Lo =:= H + 1.

subs(leaf(I), [I-I]).
subs(node(L, R), [Lo-Hi | S]) :- span(node(L, R), Lo, Hi), subs(L, SL), subs(R, SR), append(SL, SR, S).

combL(_, 0, T, T) :- !.
combL(O, N, T, node(leaf(O), T1)) :- O1 is O + 1, N1 is N - 1, combL(O1, N1, T, T1).

combR(T, _, 0, T) :- !.
combR(T, O, N, T1) :- O1 is O + 1, N1 is N - 1, combR(node(T, leaf(O)), O1, N1, T1).

runtree(O, N, T) :- N1 is N - 1, Last is O + N - 1, combL(O, N1, leaf(Last), T).

tot(RL, T) :- aggregate_all(sum(N), member(_-N, RL), T).

/* ---------------- run-length encoding ---------------- */

rle([], []).
rle([A | W], R) :- rle(W, R0), ( R0 = [A-K | Rest] -> K1 is K + 1, R = [A-K1 | Rest] ; R = [A-1 | R0] ).

/* ---------------- translation (mirrors Lean glue_chain / glue_cat) ---------------- */

%% glue_chain(+D, +RL, +O, -T, -Nodes): Nodes = chain nodes strictly below the current node.
glue_chain(bottom, [_-N1, _-N2], O, T, []) :- N is N1 + N2, runtree(O, N, T).
glue_chain(l(D), [C-N | RL], O, T, [J1-J2-C | Ns]) :-
    O1 is O + N, glue_chain(D, RL, O1, T1, Ns), combL(O, N, T1, T),
    tot(RL, K), J1 = O1, J2 is O1 + K - 1.
glue_chain(r(D), RLc, O, T, [O-J2-C | Ns]) :-
    append(RL, [C-N], RLc), glue_chain(D, RL, O, T1, Ns),
    tot(RL, K), OR is O + K, combR(T1, OR, N, T), J2 is O + K - 1.
glue_chain(d(D), [P-N1 | Rest], O, T, [J1-J2-P | Ns]) :-
    append(RM, [P-N2], Rest), J1 is O + N1, glue_chain(D, RM, J1, T1, Ns),
    tot(RM, K), OR is J1 + K, combR(T1, OR, N2, T2), combL(O, N1, T2, T), J2 is J1 + K - 1.

%% glue_cat(+D, +RL, +O, -T0, -T1, -Nodes)
glue_cat(passL(D), [C-N | RL], O, T, T1, [J1-J2-C | Ns]) :-
    J1 is O + N, glue_cat(D, RL, J1, Ta, Tb, Ns), combL(O, N, Ta, T), combL(O, N, Tb, T1),
    tot(RL, K), J2 is J1 + K - 1.
glue_cat(passR(D), RLc, O, T, T1, [O-J2-C | Ns]) :-
    append(RL, [C-N], RLc), glue_cat(D, RL, O, Ta, Tb, Ns),
    tot(RL, K), OR is O + K, combR(Ta, OR, N, T), combR(Tb, OR, N, T1), J2 is O + K - 1.
glue_cat(passD(D), [P-N1 | Rest], O, T, T1, [J1-J2-P | Ns]) :-
    append(RM, [P-N2], Rest), J1 is O + N1, glue_cat(D, RM, J1, Ta, Tb, Ns),
    tot(RM, K), OR is J1 + K, J2 is J1 + K - 1,
    combR(Ta, OR, N2, Ua), combL(O, N1, Ua, T), combR(Tb, OR, N2, Ub), combL(O, N1, Ub, T1).
glue_cat(moveD(Dc), [P-N1 | Rest], O, T, T1, [J1-J2-P | Ns]) :-
    append(RM, [P-N2], Rest), J1 is O + N1, glue_chain(Dc, RM, J1, Tm, Ns), Tm = node(B, C),
    tot(RM, K), J2 is J1 + K - 1, XL is J1 - 1, XR is J1 + K, XR1 is XR + 1,
    N1m is N1 - 1, N2m is N2 - 1,
    combR(node(leaf(XL), node(node(B, C), leaf(XR))), XR1, N2m, Ua), combL(O, N1m, Ua, T),
    combR(node(node(leaf(XL), B), node(C, leaf(XR))), XR1, N2m, Ub), combL(O, N1m, Ub, T1).
glue_cat(moveL(DL), [X-N1, Y-N2, X-N3 | RT], O, T, T1, [O2-E-X, O3-E-Y | Lr]) :-
    O2 is O + N1, O3 is O2 + N2, O4 is O3 + N3, tot(RT, K), E is O4 + K - 1,
    (   DL = bottom -> RT = [_-N4], runtree(O4, N4, R), Lr = []
    ;   DL = l(Dt), glue_chain(Dt, RT, O4, R, Lt), Lr = [O4-E-X | Lt] ),
    O31 is O3 + 1, N3m is N3 - 1, combL(O31, N3m, R, C), runtree(O2, N2, Yt), XL is O2 - 1, N1m is N1 - 1,
    combL(O, N1m, node(leaf(XL), node(Yt, node(leaf(O3), C))), T),
    combL(O, N1m, node(node(node(leaf(XL), Yt), leaf(O3)), C), T1).
glue_cat(moveR(DR), RLc, O, T, T1, [O-OC1-X, O-OB1-Y | Lr]) :-
    append(RT, [X-N3, Y-N2, X-N1], RLc),
    tot(RT, K), OA is O + K, OB is OA + N3, OC is OB + N2, OC1 is OC - 1, OB1 is OB - 1, OA1 is OA - 1,
    (   DR = bottom -> RT = [_-N4], runtree(O, N4, R), Lr = []
    ;   DR = r(Dt), glue_chain(Dt, RT, O, R, Lt), Lr = [O-OA1-X | Lt] ),
    N3m is N3 - 1, combR(R, OA, N3m, C), runtree(OB, N2, Yt), OC2 is OC + 1, N1m is N1 - 1,
    combR(node(node(node(C, leaf(OB1)), Yt), leaf(OC)), OC2, N1m, T),
    combR(node(C, node(leaf(OB1), node(Yt, leaf(OC)))), OC2, N1m, T1).

/* ---------------- (a) Moufang moves ---------------- */

letter_at(W, I, C) :- nth0(I, W, C).

mouf(W, node(leaf(X), node(Y, node(leaf(X1), C))), node(node(node(leaf(X), Y), leaf(X1)), C)) :-
    letter_at(W, X, L), letter_at(W, X1, L).
mouf(W, node(node(node(C, leaf(X)), Y), leaf(X1)), node(C, node(leaf(X), node(Y, leaf(X1))))) :-
    letter_at(W, X, L), letter_at(W, X1, L).
mouf(W, node(leaf(X), node(node(B, C), leaf(X1))), node(node(leaf(X), B), node(C, leaf(X1)))) :-
    letter_at(W, X, L), letter_at(W, X1, L).
mouf(W, node(L, R), node(L1, R)) :- mouf(W, L, L1).
mouf(W, node(L, R), node(L, R1)) :- mouf(W, R, R1).

/* ---------------- counts, determinants, laminarity ---------------- */

cnt(W, Lo, Hi, [CX, CY, CZ]) :-
    findall(C, (between(Lo, Hi, P), nth0(P, W, C)), Cs),
    aggregate_all(count, member(x, Cs), CX), aggregate_all(count, member(y, Cs), CY),
    aggregate_all(count, member(z, Cs), CZ).

det3([A0, A1, A2], [B0, B1, B2], [C0, C1, C2], D) :-
    D is A0*(B1*C2 - B2*C1) - A1*(B0*C2 - B2*C0) + A2*(B0*C1 - B1*C0).

lam(A-B, C-D) :- ( A =< C, D =< B ; C =< A, B =< D ; B < C ; D < A ), !.

/* ---------------- (b) position-level chain (Lean PChain) ---------------- */

ssub(J1-J2, P1-P2) :- P1 =< J1, J2 =< P2, (P1 < J1 ; J2 < P2), J1 =< J2.
side_letter(W, P1-P2, J1-J2, A) :-
    forall(( between(P1, P2, P), (P < J1 ; J2 < P) ), letter_at(W, P, A)).
third(A, B, C) :- member(C, [x, y, z]), C \== A, C \== B, !.

pchain(W, P, [J-A]) :- !,
    ssub(J, P), side_letter(W, P, J, A), J = J1-J2,
    once(( between(J1, J2, Q), Q < J2,
           forall(between(J1, Q, P1), letter_at(W, P1, U)), letter_at(W, J1, U),
           Q1 is Q + 1, letter_at(W, Q1, V), forall(between(Q1, J2, P2), letter_at(W, P2, V)),
           A \== U, A \== V, U \== V )).
pchain(W, P, [J-A, J1-B | Rest]) :-
    ssub(J, P), side_letter(W, P, J, A), A \== B, third(A, B, C),
    J1 = L1-H1, once(( between(L1, H1, Q), letter_at(W, Q, C) )),
    pchain(W, J, [J1-B | Rest]).

/* ---------------- (c) Lemma Cat's conclusion, by brute force ---------------- */

certified(W, Root, S, J) :-
    Root = R1-R2,
    \+ ( between(R1, R2, X0), between(X0, R2, X1), Y0 is X1 + 1, between(Y0, R2, Y1),
         Z0 is Y1 + 1, between(Z0, R2, Z1),
         ( J == X0-Y1, Cre = Y0-Z1 ; J == Y0-Z1, Cre = X0-Y1 ),
         forall(member(K, S), ( lam(X0-X1, K), lam(Y0-Y1, K), lam(Z0-Z1, K), lam(X0-Z1, K) )),
         forall(( member(K, S), K \== J ), lam(Cre, K)),
         cnt(W, X0, X1, CX), cnt(W, Y0, Y1, CY), cnt(W, Z0, Z1, CZ), det3(CX, CY, CZ, 0) ).

/* ---------------- (d) exact D_N-components (n <= 8) ---------------- */

rot(node(node(A, B), C), node(A, node(B, C)), A, B, C).
rot(node(A, node(B, C)), node(node(A, B), C), A, B, C).
rot(node(L, R), node(L1, R), A, B, C) :- rot(L, L1, A, B, C).
rot(node(L, R), node(L, R1), A, B, C) :- rot(R, R1, A, B, C).

dn_step(W, T, T1) :-
    rot(T, T1, A, B, C), span(A, A1, A2), span(B, B1, B2), span(C, C1, C2),
    cnt(W, A1, A2, NA), cnt(W, B1, B2, NB), cnt(W, C1, C2, NC), det3(NA, NB, NC, 0).

component(W, T0, Comp) :- bfs(W, [T0], [T0], Comp).
bfs(_, [], Seen, Seen).
bfs(W, [T | Q], Seen, Comp) :-
    findall(U, (dn_step(W, T, U), \+ memberchk(U, Seen)), Us0), sort(Us0, Us),
    append(Seen, Us, Seen1), append(Q, Us, Q1), bfs(W, Q1, Seen1, Comp).

/* ---------------- (e) octonion evaluation ---------------- */

eval(leaf(I), W, Val, V) :- nth0(I, W, C), memberchk(C-V, Val).
eval(node(L, R), W, Val, V) :- eval(L, W, Val, VL), eval(R, W, Val, VR), omul(VL, VR, V).

random_oct(O) :- length(O, 8), maplist([X]>>(random_between(-1000, 1000, X)), O).

/* ---------------- the pipeline ---------------- */

pipeline(W, Exact) :-
    length(W, N), Root = 0-NR, NR is N - 1,
    rle(W, RL), findall(L, member(L-_, RL), Seq),
    construct(Seq, none, D),
    glue_cat(D, RL, 0, T0, T1, Chain0),
    findall(J1-J2-A, member(J1-J2-A, Chain0), Chain1),
    findall((J1-J2)-A, member(J1-J2-A, Chain1), Chain),
    findall(J, member(J-_, Chain), S),
    ( wf(T0), span(T0, 0, NR)                      -> true ; throw(bad_tree(W)) ),
    ( mouf(W, T0, T1)                              -> true ; throw(not_moufang(W)) ),
    subs(T0, S0), ( forall(member(J, S), memberchk(J, S0)) -> true ; throw(chain_not_in_T0(W)) ),
    subs(T1, S1), ( member(J, S), \+ memberchk(J, S1) -> true ; throw(no_missing_node(W)) ),
    ( pchain(W, Root, Chain)                       -> true ; throw(pchain_fails(W)) ),
    ( forall(member(J, S), certified(W, Root, S, J)) -> true ; throw(not_certified(W)) ),
    (   Exact == true
    ->  component(W, T0, Comp), ( \+ memberchk(T1, Comp) -> true ; throw(same_component(W)) ),
        ( forall(member(T, Comp), (subs(T, ST), forall(member(J, S), memberchk(J, ST))))
          -> true ; throw(stable_set_lost(W)) )
    ;   true ),
    forall(between(1, 3, _),
           ( maplist([L, L-V]>>random_oct(V), [x, y, z], Val),
             eval(T0, W, Val, V0), eval(T1, W, Val, V1), ( V0 == V1 -> true ; throw(moufang_unequal(W)) ) )).

noninterval3(N, W) :-
    length(W, N), W = [x | _], maplist([C]>>member(C, [x, y, z]), W),
    canonical(W), memberchk(y, W), memberchk(z, W),
    rle(W, RL), findall(L, member(L-_, RL), Seq), \+ is_set(Seq).

%% canonical letter naming: first occurrences in the order x, y, z
canonical(W) :- exclude([C]>>(C == none), W, _), first_occ(W, [], Order), prefix(Order, [x, y, z]).
first_occ([], Acc, Order) :- reverse(Acc, Order).
first_occ([C | W], Acc, Order) :- ( memberchk(C, Acc) -> first_occ(W, Acc, Order) ; first_occ(W, [C | Acc], Order) ).

check(Max, ExactMax) :-
    forall(between(4, Max, N),
           ( aggregate_all(count, noninterval3(N, _), K),
             ( N =< ExactMax -> E = true ; E = false ),
             forall(noninterval3(N, W), pipeline(W, E)),
             ( E == true -> Note = "including exact D_N-component search" ; Note = "certificates only" ),
             format("n=~d: ~d non-interval 3-letter words: Moufang pair, chain, Lemma Cat brute force, octonion equality ok (~s)~n",
                    [N, K, Note]) )).

%% negative controls: the brute-force checks can fail
controls :-
    ( \+ certified([x, y, x, y], 0-3, [1-3], 1-3) -> true ; throw(control_certified) ),
    W = [x, y, x, z],
    ( \+ mouf(W, node(leaf(0), node(leaf(1), node(leaf(2), leaf(3)))), node(node(leaf(0), leaf(1)), node(leaf(2), leaf(3))))
      -> true ; throw(control_mouf) ),
    format("negative controls: a node in a two-letter region is not certified; a plain rotation is not a Moufang move~n").

main :- controls, check(10, 9).
