:- encoding(utf8).
/*  The last three steps of G2, as Prolog programs that follow the Lean proofs (Coeff.lean, Profiles.lean,
    G2Final.lean), with independent checks.

    - Moment as coefficient: the substituted map is computed as an honest octonion polynomial
      (term-list multiplication of 1 + s e₁, 1 + q e₂, 1 + t e₄ along the bracketing); its s^p q t^r coefficient
      equals the moment (sum over restricted bracketings). The polynomial also agrees with direct evaluation
      at random integer points.
    - Moments to profiles: from the polynomial's coefficients alone, κ(p, r) = coefficient on E(p, r) / σ(p, r);
      Σ_p κ(p,1) m^p (m+1)^{a−p} read in base u = 2m+1 gives the profile N, and Σ_r κ(1,r) m^r (m+1)^{c−r}
      gives the full M profile (digit e ↔ γ = c − e). These equal the profiles of the invariant, decode to
      the key, and different components give different decoded keys.
    - Final assembly (Lean `G2Final.g2`): for every pair of bracketings of an interval word lying in different
      D_N-components: find a triple with distinct letters whose shapes differ, kill the other letters,
      renumber, take the Kronecker valuation of the three-block word, pull it back, and check by direct
      octonion evaluation that the two bracketings take different values.

    Usage:   swipl -q -g run -t halt assembly.pl
*/

:- ensure_loaded(g2).
:- use_module(octonion, [omul/3, oadd/3, unit/2, zero/1]).

/* ---------------- octonion polynomials ---------------- */

oscale(K, A, B) :- maplist([X, Y]>>(Y is K * X), A, B).
osum(L, S) :- zero(Z), foldl([X, A0, A]>>oadd(A0, X, A), L, Z, S).

letter_poly(x, [O-e(0, 0, 0), E-e(1, 0, 0)]) :- unit(0, O), unit(1, E).
letter_poly(y, [O-e(0, 0, 0), E-e(0, 1, 0)]) :- unit(0, O), unit(2, E).
letter_poly(z, [O-e(0, 0, 0), E-e(0, 0, 1)]) :- unit(0, O), unit(4, E).

pmul(P1, P2, P) :-
    findall(C-e(I, J, L), ( member(C1-e(I1, J1, L1), P1), member(C2-e(I2, J2, L2), P2),
                            omul(C1, C2, C), I is I1 + I2, J is J1 + J2, L is L1 + L2 ), P).

poly(W, leaf(I), P) :- nth0(I, W, C), letter_poly(C, P).
poly(W, node(L, R), P) :- poly(W, L, P1), poly(W, R, P2), pmul(P1, P2, P).

coef(P, E, C) :- findall(X, member(X-E, P), Xs), osum(Xs, C).

ipow(_, 0, 1) :- !.
ipow(B, N, V) :- N1 is N - 1, ipow(B, N1, V1), V is V1 * B.

eval_poly(P, S, Q, T, V) :-
    findall(Y, ( member(C-e(I, J, L), P), K is S ^ I * Q ^ J * T ^ L, oscale(K, C, Y) ), Ys), osum(Ys, V).

%% direct evaluation with letter values
evv(W, Val, leaf(I), V) :- nth0(I, W, C), memberchk(C-V, Val).
evv(W, Val, node(L, R), V) :- evv(W, Val, L, A), evv(W, Val, R, B), omul(A, B, V).

subst_val(S, Q, T, [x-X, y-Y, z-Z]) :-
    unit(0, O), unit(1, E1), unit(2, E2), unit(4, E4),
    oscale(S, E1, S1), oadd(O, S1, X), oscale(Q, E2, Q2), oadd(O, Q2, Y), oscale(T, E4, T4), oadd(O, T4, Z).

%% the moment as in Lean: sum over p x-leaves, one y-leaf and r z-leaves of the restricted value at units
moment(W, T, P, R, M) :-
    findall(I, nth0(I, W, x), Xs), findall(I, nth0(I, W, y), Ys), findall(I, nth0(I, W, z), Zs),
    unit(1, E1), unit(2, E2), unit(4, E4),
    findall(V, ( subset_k(Xs, P, PX), member(Yk, Ys), subset_k(Zs, R, RZ),
                 append([PX, [Yk], RZ], K0), msort(K0, Keep), restrict_keep(T, Keep, T1),
                 evv(W, [x-E1, y-E2, z-E4], T1, V) ), Vs),
    osum(Vs, M).

check_coef(NMax) :-
    set_random(seed(7)),
    findall(1, ( between(3, NMax, N), between(1, N, A), between(1, N, B), C is N - A - B, C >= 1,
                 three_block(A, B, C, W, Ps), tree(Ps, T), poly(W, T, Pl),
                 forall(( between(0, A, P), between(0, C, R) ),
                        ( coef(Pl, e(P, 1, R), Co), moment(W, T, P, R, Mo),
                          ( Co == Mo -> true ; format("coef ≠ moment ~w ~w~n", [T, P-R]), fail ) )),
                 forall(between(1, 3, _),
                        ( random_between(-9, 9, S), random_between(-9, 9, Q), random_between(-9, 9, Tt),
                          subst_val(S, Q, Tt, Val), evv(W, Val, T, V1), eval_poly(Pl, S, Q, Tt, V2),
                          ( V1 == V2 -> true ; format("expansion fails ~w~n", [T]), fail ) )) ), L),
    length(L, NL),
    format("Moment as coefficient: the s^p q t^r coefficient of the substituted polynomial = the moment, and the polynomial = the map at random points, on all ~d bracketings of three-block words, n ≤ ~d: ok~n",
           [NL, NMax]).

/* ---------------- moments to profiles ---------------- */

negpow(N, S) :- ( N mod 2 =:= 0 -> S = 1 ; S = -1 ).
%% E(p, r) = e₁^{p mod 2} e₄^{r mod 2} e₂ as a signed unit, and σ(p, r)
eunit(P, R, IE, SgE) :-
    ( P mod 2 =:= 1 -> IP = 1 ; IP = 0 ), ( R mod 2 =:= 1 -> IR = 4 ; IR = 0 ),
    uprod(IP, IR, IB, SB), uprod(IB, 2, IE, SE), SgE is SB * SE.
kappa(Pl, P, R, K) :-
    coef(Pl, e(P, 1, R), Co), eunit(P, R, IE, SgE), Ex is R + P // 2 + R // 2, negpow(Ex, Sig),
    nth0(IE, Co, X), K is X * Sig * SgE.

%% base-u digits of a nonnegative integer, lowest first, exactly Len of them
digits(_, _, 0, []) :- !.
digits(V, U, Len, [D | Ds]) :- D is V mod U, V1 is V // U, Len1 is Len - 1, digits(V1, U, Len1, Ds).

hsum(Ks, M, Deg, S) :- findall(X, ( nth0(P, Ks, K), X is K * M ^ P * (M + 1) ^ (Deg - P) ), Xs), sum_list(Xs, S).

to_pairs(Ds, Ps) :- findall(I-D, ( nth0(I, Ds, D), D > 0 ), Ps).

check_profiles(NMax) :-
    findall(NC, ( between(3, NMax, N), between(1, N, A), between(1, N, B), C is N - A - B, C >= 1,
                  three_block(A, B, C, W, Ps), components(W, Ps, Pairs, NC),
                  M is B * (A + C) + 1, U is 2 * M + 1,
                  findall(Id-Code, ( member(T-Id, Pairs), poly(W, T, Pl),
                                     findall(K, ( between(0, A, P), kappa(Pl, P, 1, K) ), K1s),
                                     findall(K, ( between(0, C, R), kappa(Pl, 1, R, K) ), K2s),
                                     hsum(K1s, M, A, S1), A1 is A + 1, digits(S1, U, A1, ND),
                                     hsum(K2s, M, C, S2), C1 is C + 1, digits(S2, U, C1, MD),
                                     reverse(MD, MDr),           % digit e ↔ γ = c − e
                                     to_pairs(ND, Np), to_pairs(MDr, Mp),
                                     invariant(T, A, B, C, Phi), profiles(Phi, B, Np0, Mp0),
                                     ( Np == Np0, Mp == Mp0 -> true ; format("profiles differ ~w~n", [T]), fail ),
                                     decode(Np, Mp, A, B, Code), key(Phi, B, Code) ), IC0),
                  sort(IC0, IC), length(IC, NC), pairs_values(IC, Cs), sort(Cs, Cs1), length(Cs1, NC) ), Ns),
    sum_list(Ns, Tot),
    format("Moments to profiles: from the coefficients alone, the homogeneous sums give N and M in base 2m+1, equal to the invariant's profiles, decoding to the key; ~d components separated, n ≤ ~d: ok~n",
           [Tot, NMax]).

/* ---------------- the final assembly ---------------- */

idx(L, I, K) :- include([X]>>(X < I), L, F), length(F, K).
rn(L, leaf(I), leaf(K)) :- idx(L, I, K).
rn(L, node(A, B), node(A1, B1)) :- rn(L, A, A1), rn(L, B, B1).

kron_val(A, B, C, Val) :-
    N is A + B + C, M is 2 ^ (N + 2) + 1, Q is M ^ (N + 1), T is M ^ ((N + 1) * (N + 1)), subst_val(M, Q, T, Val).

%% the separating valuation of G2Final.g2
g2_witness(W, T, T2, Val) :-
    sigma_triples(W, T, T2, P, Q, R), !,
    nth0(P, W, U), nth0(Q, W, V), nth0(R, W, X),
    alphabet(W, Alph), exclude([Lt]>>memberchk(Lt, [U, V, X]), Alph, Others),
    restrict(W, Others, T, S), restrict(W, Others, T2, S2),
    lvs_(S, L),
    include([I]>>(nth0(I, W, U)), L, LU), include([I]>>(nth0(I, W, V)), L, LV), include([I]>>(nth0(I, W, X)), L, LX),
    length(LU, A), length(LV, B), length(LX, C),
    rn(L, S, RS), rn(L, S2, RS2), RS \== RS2,
    kron_val(A, B, C, [x-KX, y-KY, z-KZ]), unit(0, One),
    findall(Lt-O, ( member(Lt, Alph), ( Lt == U -> O = KX ; Lt == V -> O = KY ; Lt == X -> O = KZ ; O = One ) ), Val).
sigma_triples(W, T, T2, P, Q, R) :-
    lvs_(T, L), member(P, L), member(Q, L), P < Q, member(R, L), Q < R,
    nth0(P, W, U), nth0(Q, W, V), nth0(R, W, X), U \== V, V \== X, U \== X,
    restrict_keep(T, [P, Q, R], A), restrict_keep(T2, [P, Q, R], B), A \== B.
lvs_(leaf(I), [I]).
lvs_(node(L, R), Is) :- lvs_(L, A), lvs_(R, B), append(A, B, Is).

check_assembly(NMax) :-
    findall(1, ( between(3, NMax, N), between(3, N, K), interval_word(K, N, W),
                 N1 is N - 1, numlist(0, N1, Ps), components(W, Ps, Pairs, _),
                 member(T-I, Pairs), member(T2-I2, Pairs), I < I2,
                 ( g2_witness(W, T, T2, Val) -> true ; format("no witness ~w~n", [W]), fail ),
                 evv(W, Val, T, V1), evv(W, Val, T2, V2),
                 ( V1 \== V2 -> true ; format("G2 valuation fails ~w ~w ~w~n", [W, T, T2]), fail ) ), L),
    length(L, NL),
    format("Final assembly (G2Final.g2): ~d pairs in different D_N-components of interval words (≥ 3 letters, n ≤ ~d) separated by the pulled-back Kronecker valuation: ok~n",
           [NL, NMax]).

%% control: bracketings in the same component take equal values at every such valuation
control_same(NMax) :-
    findall(1, ( between(3, NMax, N), between(3, N, K), interval_word(K, N, W),
                 N1 is N - 1, numlist(0, N1, Ps), components(W, Ps, Pairs, _),
                 member(T-I, Pairs), member(T2-I, Pairs), T @< T2,
                 alphabet(W, Alph), length(Alph, NA), NA >= 3, Alph = [U, V, X | _],
                 kron_val(2, 2, 2, [x-KX, y-KY, z-KZ]), unit(0, One),
                 findall(Lt-O, ( member(Lt, Alph), ( Lt == U -> O = KX ; Lt == V -> O = KY ; Lt == X -> O = KZ ; O = One ) ), Val),
                 evv(W, Val, T, V1), evv(W, Val, T2, V2),
                 ( V1 == V2 -> true ; format("control: same component, different values ~w~n", [W]), fail ) ), L),
    length(L, NL),
    format("control: ~d pairs in the same D_N-component take equal values, as the converse direction predicts (n ≤ ~d)~n", [NL, NMax]).

run :-
    set_stream(user_output, encoding(utf8)),
    control_same(5),
    check_coef(7),
    check_profiles(7),
    check_assembly(6).
