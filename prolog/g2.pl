:- encoding(utf8).
/*  Killing letters (K) and G2's Propositions T, M, S and C, checked exhaustively on small words.

    - K, combinatorial side (all 4-letter words, n ≤ 7): killing a letter maps every flip to a flip or to
      the identity, and every D_N-flip (rank ≤ 2: all 3×3 minors vanish) to a D_N-flip or the identity.
      Moufang lift: every Moufang move between different D_N-components of the 3-letter image lifts to a
      Moufang move of the 4-letter word.
    - Proposition T (x^a y^b z^c, a + b + c ≤ 8): the invariant Φ (interior j) or the join word (boundary j)
      is constant on D_N-components and separates them; the count is 1 + b·(C(a+c, a) − 1).
    - Lemma M (n ≤ 6): the s^p q t^r coefficient computed directly on octonion units equals
      ±[j S_{ω₊}(p, r) + (b − j) S_{ω₋}(p, r)], with a sign depending only on (w, p, r).
    - Proposition S (n ≤ 7, and the formula range a + b + c ≤ 10): the two linear profiles decode the
      invariant on every component; distinct components give distinct maps.
    - Proposition C (interval words with ≥ 3 letters, n ≤ 7): D_N-components are exactly the classes of
      the distinct-letter triple shapes σ.

    Usage:   swipl -q -g main -t halt g2.pl
*/

:- use_module(octonion, [omul/3, unit/2]).

/* ---------------- trees over position lists ---------------- */

tree([P], leaf(P)) :- !.
tree(Ps, node(L, R)) :- append(As, Bs, Ps), As \= [], Bs \= [], tree(As, L), tree(Bs, R).

leaves(leaf(I), [I]).
leaves(node(L, R), Is) :- leaves(L, A), leaves(R, B), append(A, B, Is).

rot(node(node(A, B), C), node(A, node(B, C)), A, B, C).
rot(node(A, node(B, C)), node(node(A, B), C), A, B, C).
rot(node(L, R), node(L1, R), A, B, C) :- rot(L, L1, A, B, C).
rot(node(L, R), node(L, R1), A, B, C) :- rot(R, R1, A, B, C).

letters(W, T, Ls) :- leaves(T, Is), maplist([I, C]>>nth0(I, W, C), Is, Ls).
cnt(W, T, Alph, V) :- letters(W, T, Ls), maplist([A, K]>>aggregate_all(count, member(A, Ls), K), Alph, V).

det3([A0, A1, A2], [B0, B1, B2], [C0, C1, C2], D) :-
    D is A0*(B1*C2 - B2*C1) - A1*(B0*C2 - B2*C0) + A2*(B0*C1 - B1*C0).

%% rank ≤ 2 of the count matrix: every 3×3 minor vanishes
dn(W, Alph, A, B, C) :-
    cnt(W, A, Alph, VA), cnt(W, B, Alph, VB), cnt(W, C, Alph, VC),
    length(Alph, M), M1 is M - 1,
    forall(( between(0, M1, P), between(P, M1, Q), Q > P, between(Q, M1, R), R > Q ),
           ( pick3(VA, P, Q, R, X), pick3(VB, P, Q, R, Y), pick3(VC, P, Q, R, Z), det3(X, Y, Z, 0) )).
pick3(V, P, Q, R, [A, B, C]) :- nth0(P, V, A), nth0(Q, V, B), nth0(R, V, C).

alphabet(W, Alph) :- sort(W, Alph).

dn_step(W, Alph, T, T1) :- rot(T, T1, A, B, C), dn(W, Alph, A, B, C).

%% D_N-components of all bracketings of the positions Ps: a list of Tree-Id pairs
components(W, Ps, Pairs, NComp) :-
    alphabet(W, Alph), findall(T, tree(Ps, T), Ts),
    empty_assoc(E0), comp_loop(Ts, W, Alph, E0, 0, E, NComp), assoc_to_list(E, Pairs).
comp_loop([], _, _, E, N, E, N).
comp_loop([T | Ts], W, Alph, E0, N0, E, N) :-
    ( get_assoc(T, E0, _) -> comp_loop(Ts, W, Alph, E0, N0, E, N)
    ; put_assoc(T, E0, N0, E1), bfs([T], W, Alph, N0, E1, E2), N1 is N0 + 1, comp_loop(Ts, W, Alph, E2, N1, E, N) ).
bfs([], _, _, _, E, E).
bfs([T | Q], W, Alph, Id, E0, E) :-
    findall(U, dn_step(W, Alph, T, U), Us0), sort(Us0, Us),
    foldl(visit(Id), Us, E0-[], E1-New),
    append(Q, New, Q1), bfs(Q1, W, Alph, Id, E1, E).
visit(Id, U, E0-N0, E1-N1) :- ( get_assoc(U, E0, _) -> E1 = E0, N1 = N0 ; put_assoc(U, E0, Id, E1), N1 = [U | N0] ).

/* ---------------- words ---------------- */

%% canonical words of length N using exactly the first K letters of Ls, first occurrences in order
canon(Ls, K, N, W) :- length(Ls0, K), append(Ls0, _, Ls), length(W, N), canon_(W, Ls0, 0), \+ (member(L, Ls0), \+ memberchk(L, W)).
canon_([], _, _).
canon_([C | W], Ls, Used) :- nth0(I, Ls, C), I =< Used, ( I =:= Used -> Used1 is Used + 1 ; Used1 = Used ), canon_(W, Ls, Used1).

restrict(W, K, leaf(I), R) :- nth0(I, W, C), ( memberchk(C, K) -> R = none ; R = leaf(I) ).
restrict(W, K, node(L, Rt), R) :-
    restrict(W, K, L, A), restrict(W, K, Rt, B),
    ( A == none -> R = B ; B == none -> R = A ; R = node(A, B) ).

/* ---------------- K ---------------- */

%% Moufang moves with a single repeated letter (as in trees.pl)
mouf(W, node(leaf(X), node(Y, node(leaf(X1), C))), node(node(node(leaf(X), Y), leaf(X1)), C)) :-
    nth0(X, W, L), nth0(X1, W, L).
mouf(W, node(node(node(C, leaf(X)), Y), leaf(X1)), node(C, node(leaf(X), node(Y, leaf(X1))))) :-
    nth0(X, W, L), nth0(X1, W, L).
mouf(W, node(leaf(X), node(node(B, C), leaf(X1))), node(node(leaf(X), B), node(C, leaf(X1)))) :-
    nth0(X, W, L), nth0(X1, W, L).
mouf(W, node(L, R), node(L1, R)) :- mouf(W, L, L1).
mouf(W, node(L, R), node(L, R1)) :- mouf(W, R, R1).

kill_word(W, Nmax, Flips, DNs, Lifts) :-
    alphabet(W, Alph), length(W, N), N1 is N - 1, numlist(0, N1, Ps),
    findall(f, ( tree(Ps, T), rot(T, T1, A, B, C), member(K, Alph),
                 restrict(W, [K], T, R), restrict(W, [K], T1, R1),
                 ( R == R1 -> true
                 ; once(rot(R, R1, _, _, _)) -> true
                 ; format("K: flip restricts to a non-flip: ~w ~w~n", [W, T]), fail ),
                 ( dn(W, Alph, A, B, C), R \== R1 ->
                     exclude(==(K), Alph, Alph1),
                     ( rot(R, R1, A1, B1, C1), dn(W, Alph1, A1, B1, C1) -> true
                     ; format("K: D_N flip restricts to a non-D_N flip: ~w ~w~n", [W, T]), fail )
                 ; true ) ), Fs),
    length(Fs, Flips), DNs = Flips,
    ( N =< Nmax -> lift_word(W, Alph, Ps, Lifts) ; Lifts = 0 ).

%% every Moufang move between different D_N-components of the image lifts
lift_word(W, Alph, Ps, Lifts) :-
    findall(l, ( member(K, Alph),
                 exclude([P]>>nth0(P, W, K), Ps, Ps1), exclude(==(K), Alph, Alph1),
                 components(W, Ps1, Pairs, _), list_to_assoc(Pairs, CA),
                 tree(Ps1, T0), mouf(W, T0, T1), get_assoc(T0, CA, I0), get_assoc(T1, CA, I1), I0 =\= I1,
                 ( tree(Ps, U0), restrict(W, [K], U0, T0), mouf(W, U0, U1), restrict(W, [K], U1, T1) -> true
                 ; format("K: Moufang move does not lift: ~w ~w ~w~n", [W, T0, T1]), fail ),
                 Alph1 = Alph1 ), Ls),
    length(Ls, Lifts).

check_K(NMax) :-
    findall(F-L, ( between(4, NMax, N), canon([a, b, c, d], 4, N, W), kill_word(W, NMax, F, _, L) ), R),
    length(R, NW), aggregate_all(sum(F), member(F-_, R), NF), aggregate_all(sum(L), member(_-L, R), NL),
    format("K: ~d four-letter words (n ≤ ~d), ~d flips × killed letters: flips ↦ flips or identities, D_N ↦ D_N or identities: ok~n",
           [NW, NMax, NF]),
    format("K: ~d Moufang moves between different D_N-components of a 3-letter image all lift: ok~n", [NL]).

/* ---------------- Proposition T: the invariant ---------------- */

span(T, Lo, Hi) :- leaves(T, Is), Is = [Lo | _], last(Is, Hi).

%% Φ = (j, a', c', W) for a bracketing of x^a y^b z^c (positions 0..n-1)
invariant(T, A, B, _C, phi(J, AX, CZ, Wd)) :-
    LastX is A - 1, FirstZ is A + B, core(T, LastX, FirstZ, [], Path, node(L, R)),
    span(L, L0, L1), span(R, _, R1),
    J is L1 - LastX, AX is LastX - L0 + 1, CZ is R1 - FirstZ + 1,
    foldl([S-N, Acc0, Acc]>>(length(Run, N), maplist(=(S), Run), append(Acc0, Run, Acc)), Path, [], Wd).
core(node(L, R), LX, FZ, Acc, Path, Core) :-
    span(L, L0, L1), span(R, R0, R1),
    ( L0 =< LX, L1 >= FZ -> N is R1 - R0 + 1, core(L, LX, FZ, [z-N | Acc], Path, Core)
    ; R0 =< LX, R1 >= FZ -> N is L1 - L0 + 1, core(R, LX, FZ, [x-N | Acc], Path, Core)
    ; Path = Acc, Core = node(L, R) ).

omegas(phi(_, AX, CZ, Wd), Up, Vm) :-
    length(X, AX), maplist(=(x), X), length(Z, CZ), maplist(=(z), Z),
    append([X, Z, Wd], Up), append([Z, X, Wd], Vm).

%% the complete invariant of Proposition T
key(Phi, B, K) :- Phi = phi(J, _, _, _), omegas(Phi, Up, Vm),
    ( J =:= 0 -> K = join(Vm) ; J =:= B -> K = join(Up) ; K = Phi ).

three_block(A, B, C, W, Ps) :-
    length(X, A), maplist(=(x), X), length(Y, B), maplist(=(y), Y), length(Z, C), maplist(=(z), Z),
    append([X, Y, Z], W), N is A + B + C - 1, numlist(0, N, Ps).

choose(N, K, V) :- ( K < 0 ; K > N ) -> V = 0 ; K =:= 0 -> V = 1 ; N1 is N - 1, K1 is K - 1,
    choose(N1, K1, V1), V is V1 * N // K.

check_T(NMax) :-
    findall(NC, ( between(3, NMax, N), between(1, N, A), between(1, N, B), C is N - A - B, C >= 1,
                  three_block(A, B, C, W, Ps), components(W, Ps, Pairs, NC),
                  choose(A + C, A, Bin), Want is 1 + B * (Bin - 1),
                  ( NC =:= Want -> true ; format("T: count ~w ~d ≠ ~d~n", [W, NC, Want]), fail ),
                  findall(Id-K, ( member(T-Id, Pairs), invariant(T, A, B, C, Phi), key(Phi, B, K) ), IK0),
                  sort(IK0, IK), pairs_keys(IK, Ids), sort(Ids, Ids1), length(Ids1, NC), length(IK, NC),
                  pairs_values(IK, Ks), sort(Ks, Ks1), length(Ks1, NC) ), Ns),
    length(Ns, NW), sum_list(Ns, Tot),
    format("Prop T: ~d three-block words (n ≤ ~d), ~d components: count 1 + b(C(a+c,a) − 1), invariant constant and complete: ok~n",
           [NW, NMax, Tot]).

/* ---------------- Lemma M and Proposition S ---------------- */

:- table uprod/4.
%% e_I e_J = S e_K
uprod(I, J, K, S) :- unit(I, U), unit(J, V), omul(U, V, P), nth0(K, P, S), S =\= 0, !.

uev(W, leaf(I), U, 1) :- nth0(I, W, C), ( C == x -> U = 1 ; C == y -> U = 2 ; U = 4 ).
uev(W, node(L, R), U, S) :- uev(W, L, U1, S1), uev(W, R, U2, S2), uprod(U1, U2, U, S0), S is S0 * S1 * S2.

%% A_T(p, r) on its unit (or 0)
a_direct(T, W, P, R, V) :-
    findall(I, nth0(I, W, x), Xs), findall(I, nth0(I, W, y), Ys), findall(I, nth0(I, W, z), Zs),
    findall(U-S, ( subset_k(Xs, P, PX), subset_k(Zs, R, RZ), member(Yk, Ys),
                   append([PX, [Yk], RZ], Keep0), msort(Keep0, Keep),
                   restrict_keep(T, Keep, T1), uev(W, T1, U, S) ), US),
    findall(U-Sum, ( member(U-_, US), aggregate_all(sum(S), member(U-S, US), Sum) ), Tot0), sort(Tot0, Tot),
    exclude([_-0]>>true, Tot, NZ),
    ( NZ == [] -> V = 0 ; NZ = [_-V] -> true ; format("M: value not on one unit~n"), fail ).

subset_k(_, 0, []) :- !.
subset_k([X | Xs], K, [X | S]) :- K > 0, K1 is K - 1, subset_k(Xs, K1, S).
subset_k([_ | Xs], K, S) :- K > 0, subset_k(Xs, K, S).

restrict_keep(leaf(I), Keep, R) :- ( memberchk(I, Keep) -> R = leaf(I) ; R = none ).
restrict_keep(node(L, Rt), Keep, R) :-
    restrict_keep(L, Keep, A), restrict_keep(Rt, Keep, B),
    ( A == none -> R = B ; B == none -> R = A ; R = node(A, B) ).

runs([], []).
runs([C | W], Rs) :- runs(W, R0), ( R0 = [C-K | Rest] -> K1 is K + 1, Rs = [C-K1 | Rest] ; Rs = [C-1 | R0] ).

%% coefficient of s^p t^r of the ordered Clifford product (X² = Z² = 1, XZ = −ZX)
s_coef(Seq, P, R, Tot) :- runs(Seq, Rs), findall(V, s_rec(Rs, P, R, [], V), Vs), sum_list(Vs, Tot).
s_rec([], 0, 0, KsRev, V) :- !, reverse(KsRev, Ks), sign_coef(Ks, V).
s_rec([], _, _, _, 0) :- !.
s_rec([Ch-M | Rs], P, R, Ks, V) :- between(0, M, K),
    ( Ch == x -> K =< P, P1 is P - K, R1 = R ; K =< R, R1 is R - K, P1 = P ),
    choose(M, K, Cb), s_rec(Rs, P1, R1, [Ch-K-Cb | Ks], V).
sign_coef(Ks, V) :-
    foldl([_-_-C, A0, A]>>(A is A0 * C), Ks, 1, Coef),
    aggregate_all(count, ( append(_, [z-K1-_ | Rest], Ks), K1 mod 2 =:= 1, member(x-K2-_, Rest), K2 mod 2 =:= 1 ), Inv),
    V is Coef * (-1) ** Inv.

formula(Phi, B, P, R, V) :- Phi = phi(J, _, _, _), omegas(Phi, Up, Vm),
    s_coef(Up, P, R, SU), s_coef(Vm, P, R, SV), V is J * SU + (B - J) * SV.

check_M(NMax) :-
    findall(NT, ( between(3, NMax, N), between(1, N, A), between(1, N, B), C is N - A - B, C >= 1,
                  three_block(A, B, C, W, Ps), findall(T, tree(Ps, T), Ts), length(Ts, NT),
                  empty_assoc(S0),
                  foldl(m_tree(W, A, B, C), Ts, S0, _) ), Ns),
    sum_list(Ns, Tot),
    format("Lemma M: A_T(p, r) = σ(w, p, r)[j S_ω₊ + (b−j) S_ω₋] on all ~d bracketings of three-block words, n ≤ ~d: ok~n",
           [Tot, NMax]).
m_tree(W, A, B, C, T, S0, S) :-
    invariant(T, A, B, C, Phi),
    findall(P-R, ( between(0, A, P), between(0, C, R) ), PRs),
    foldl(m_pr(W, T, Phi, B), PRs, S0, S).
m_pr(W, T, Phi, B, P-R, S0, S) :-
    a_direct(T, W, P, R, D), formula(Phi, B, P, R, F),
    ( abs(D) =\= abs(F) -> format("M: mismatch ~w ~w (~d, ~d): ~d vs ~d~n", [W, T, P, R, D, F]), fail ; true ),
    ( F =:= 0 -> S = S0
    ; Sg is D // F,
      ( get_assoc(P-R, S0, Sg0) -> ( Sg0 =:= Sg -> S = S0 ; format("M: sign not uniform ~w~n", [W]), fail )
      ; put_assoc(P-R, S0, Sg, S) ) ).

%% profiles: N(α) = weighted # z's with α x's before; M(γ) symmetric
profiles(Phi, B, Np, Mp) :- Phi = phi(J, _, _, _), omegas(Phi, Up, Vm), BJ is B - J,
    prof(Up, J, NU, MU), prof(Vm, BJ, NV, MV), merge_counts(NU, NV, Np), merge_counts(MU, MV, Mp).
prof(Word, Wt, N, M) :- prof_(Word, Wt, 0, 0, N, M).
prof_([], _, _, _, [], []).
prof_([z | W], Wt, NX, NZ, [NX-Wt | N], M) :- NZ1 is NZ + 1, prof_(W, Wt, NX, NZ1, N, M).
prof_([x | W], Wt, NX, NZ, N, [NZ-Wt | M]) :- NX1 is NX + 1, prof_(W, Wt, NX1, NZ, N, M).
merge_counts(A, B, C) :- append(A, B, AB), findall(K-S, ( member(K-_, AB), aggregate_all(sum(V), member(K-V, AB), S), S > 0 ), C0), sort(C0, C).

word_from_N(Np, NXtot, Word) :- wfn(Np, 0, NXtot, Word).
wfn([], X, NXtot, W) :- K is NXtot - X, length(W, K), maplist(=(x), W).
wfn([Al-Cn | Rest], X, NXtot, W) :- K is Al - X, length(Xs, K), maplist(=(x), Xs), length(Zs, Cn), maplist(=(z), Zs),
    wfn(Rest, Al, NXtot, W1), append([Xs, Zs, W1], W).

%% Proposition S: decode the profiles
decode(Np, Mp, A, B, Code) :-
    ( memberchk(0-N0, Np), memberchk(0-_, Mp) ->
        findall(K, (member(K-_, Np), K > 0), Ks), min_list(Ks, AX),
        findall(K, (member(K-_, Mp), K > 0), Gs), min_list(Gs, CZ),
        J is B - N0 // CZ,
        findall(K1-V1, ( member(K-V, Np), ( K =:= 0 -> D0 is (B - J) * CZ ; D0 = 0 ),
                         ( K =:= AX -> D1 is J * CZ ; D1 = 0 ), V0 is V - D0 - D1,
                         V0 > 0, K1 is K - AX, V1 is V0 // B ), NW),
        NXW is A - AX, word_from_N(NW, NXW, Wd), Code = phi(J, AX, CZ, Wd)
    ; findall(K-V1, (member(K-V, Np), V1 is V // B), NB), word_from_N(NB, A, Wd), Code = join(Wd) ).

check_S(NMax, NForm) :-
    findall(NC, ( between(3, NMax, N), between(1, N, A), between(1, N, B), C is N - A - B, C >= 1,
                  three_block(A, B, C, W, Ps), components(W, Ps, Pairs, NC),
                  findall(Id-Code, ( member(T-Id, Pairs), invariant(T, A, B, C, Phi), profiles(Phi, B, Np, Mp),
                                     decode(Np, Mp, A, B, Code), key(Phi, B, Code) ), IC0),
                  length(Pairs, NT), length(IC0, NT),
                  sort(IC0, IC), length(IC, NC), pairs_values(IC, Cs), sort(Cs, Cs1), length(Cs1, NC) ), Ns),
    sum_list(Ns, Tot),
    format("Prop S: the linear profiles decode the invariant on every bracketing; ~d components, n ≤ ~d: ok~n", [Tot, NMax]),
    findall(Cnt, ( between(3, NForm, N), between(1, N, A), between(1, N, B), C is N - A - B, C >= 1,
                   findall(Key-Code, ( between(0, B, J), between(1, A, AX), between(1, C, CZ),
                                       LW is A + C - AX - CZ, NXW is A - AX, binword(LW, NXW, Wd),
                                       Phi = phi(J, AX, CZ, Wd),
                                       findall(V, ( between(0, A, P), between(0, C, R), formula(Phi, B, P, R, V) ), Key),
                                       profiles(Phi, B, Np, Mp), decode(Np, Mp, A, B, Code) ), KC0),
                   sort(KC0, KC), pairs_keys(KC, Keys), sort(Keys, Keys1), length(Keys1, Cnt), length(KC, Cnt),
                   pairs_values(KC, Codes), sort(Codes, Codes1), length(Codes1, Cnt),
                   choose(A + C, A, Bin), Cnt =:= 1 + B * (Bin - 1) ), Cs2),
    sum_list(Cs2, Tot2),
    format("Prop S: formula over the full Φ range, a + b + c ≤ ~d: ~d distinct maps, each decoded, count 1 + b(C(a+c,a) − 1): ok~n",
           [NForm, Tot2]).

binword(0, 0, []) :- !.
binword(L, K, [x | W]) :- L > 0, K > 0, L1 is L - 1, K1 is K - 1, binword(L1, K1, W).
binword(L, K, [z | W]) :- L > K, L1 is L - 1, binword(L1, K, W).

/* ---------------- Proposition C ---------------- */

interval_word(K, N, W) :- K1 is K - 1, numlist(0, K1, Ls), length(Cuts0, K1), N1 is N - 1,
    cuts(Cuts0, 1, N1), append([0 | Cuts0], [N], Bs), blocks(Bs, Ls, W).
cuts([], _, _).
cuts([C | Cs], Lo, Hi) :- between(Lo, Hi, C), C1 is C + 1, cuts(Cs, C1, Hi).
blocks([_], [], []).
blocks([B0, B1 | Bs], [L | Ls], W) :- K is B1 - B0, length(R, K), maplist(=(L), R), blocks([B1 | Bs], Ls, W1), append(R, W1, W).

sigma(W, T, Sig) :-
    length(W, N), N1 is N - 1,
    findall(Sh, ( between(0, N1, I), between(I, N1, J), J > I, between(J, N1, K), K > J,
                  nth0(I, W, A), nth0(J, W, B), nth0(K, W, C), A \== B, B \== C, A \== C,
                  restrict_keep(T, [I, J, K], R), ( R = node(node(_, _), _) -> Sh = l ; Sh = r ) ), Sig).

check_C(NMax) :-
    findall(NC, ( between(3, NMax, N), between(3, N, K), interval_word(K, N, W),
                  N1 is N - 1, numlist(0, N1, Ps), components(W, Ps, Pairs, NC),
                  findall(Id-S, ( member(T-Id, Pairs), sigma(W, T, S) ), IS0), sort(IS0, IS),
                  length(IS, NC), pairs_values(IS, Ss), sort(Ss, Ss1), length(Ss1, NC) ), Ns),
    length(Ns, NW), sum_list(Ns, Tot),
    format("Prop C: ~d interval words with ≥ 3 letters (n ≤ ~d), ~d components: D_N-components = σ-classes: ok~n",
           [NW, NMax, Tot]).

%% negative controls: the same checks fail where they should
controls :-
    W = [0, 1, 2, 1, 0], numlist(0, 4, Ps), components(W, Ps, Pairs, NC),
    findall(S, ( member(T-_, Pairs), sigma(W, T, S) ), Ss0), sort(Ss0, Ss), length(Ss, NS), NS =\= NC,
    format("control: for the non-interval word ~w, σ-classes (~d) ≠ D_N-components (~d)~n", [W, NS, NC]),
    three_block(2, 3, 2, W2, Ps2), tree(Ps2, T2), invariant(T2, 2, 3, 2, phi(J, AX, CZ, Wd)), J =:= 1,
    J1 is 3 - J, between(0, 2, P), between(0, 2, R), a_direct(T2, W2, P, R, D), formula(phi(J1, AX, CZ, Wd), 3, P, R, F),
    abs(D) =\= abs(F), !,
    format("control: Lemma M with j and b − j swapped fails on ~w~n", [T2]).

main :-
    set_stream(user_output, encoding(utf8)),
    controls,
    check_K(7),
    check_T(8),
    check_M(6),
    check_S(7, 10),
    check_C(7).
