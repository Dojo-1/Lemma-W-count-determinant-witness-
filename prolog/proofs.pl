:- encoding(utf8).
/*  The four remaining G2/K arguments as Prolog programs that follow the Lean proofs step by step.
    Each program constructs the object the proof constructs; an independent checker then validates it.

    - K's Moufang lift (Lean `lift_mouf`): the lifted pair is built by the gap-absorption construction
      (pivot splits, `wrapL`/`wrapR`), not by search. Checked: both lifts restrict to the given pair,
      they are related by a Moufang move, and (for moves between different components of the image)
      they lie in different D_N-components of the word.
    - Proposition C (⇐) (Lean `propC_backward`): the induction on root splits as a path builder
      (equal splits; case B, case C, two-letter case by rotation to a comb). Checked: every step of the
      produced path is a D_N-flip, and it joins the two given bracketings.
    - Proposition T (Lean `sh_sub`, `cx_omega`, `β_eq_ωq`, `propT`): shapes are read off cx(q, r); cx is
      read off the absorption word ω_q; ω_q = ω₊ or ω₋; same key ⟺ same component.
    - Lemma M (Lean `walk`, `lemmaM`): every restriction evaluates to (−1)^{#z} e^{ω} e₂ (the walk), and
      the moment equals σ(p, r)·[j S(ω₊) + (b−j) S(ω₋)]·E(p, r) exactly (sign and unit included).

    Usage:   swipl -q -g run -t halt proofs.pl
*/

:- ensure_loaded(g2).

/* ---------------- shared ---------------- */

lvs(leaf(I), [I]).
lvs(node(L, R), Is) :- lvs(L, A), lvs(R, B), append(A, B, Is).

rc(I, [], leaf(I)).
rc(I, [J | R], node(leaf(I), C)) :- rc(J, R, C).
wrapL([], T, T).
wrapL([I | R], T, node(C, T)) :- rc(I, R, C).
wrapR([], T, T).
wrapR([I | R], T, node(T, C)) :- rc(I, R, C).

alive(W, K, I) :- nth0(I, W, C), \+ memberchk(C, K).

%% L = Q ++ [A | R], A alive (positions are distinct, so the split is unique)
pivot(L, A, Q, R) :- append(Q, [A | R], L), !.

/* ---------------- K: the Moufang lift, constructively ---------------- */

%% Moufang moves with their derivation
moufd(W, node(leaf(X), node(Y, node(leaf(X1), C))), node(node(node(leaf(X), Y), leaf(X1)), C), left(X, X1, Y, C)) :-
    nth0(X, W, L), nth0(X1, W, L).
moufd(W, node(node(node(C, leaf(X)), Y), leaf(X1)), node(C, node(leaf(X), node(Y, leaf(X1)))), right(X, X1, C, Y)) :-
    nth0(X, W, L), nth0(X1, W, L).
moufd(W, node(leaf(X), node(node(B, C), leaf(X1))), node(node(leaf(X), B), node(C, leaf(X1))), middle(X, X1, B, C)) :-
    nth0(X, W, L), nth0(X1, W, L).
moufd(W, node(L, R), node(L1, R), inL(D, R)) :- moufd(W, L, L1, D).
moufd(W, node(L, R), node(L, R1), inR(L, D)) :- moufd(W, R, R1, D).

%% lift_tree(+T', +L, -T): a bracketing of L restricting to T' (Lean `lift_tree`)
lift_tree(leaf(I), L, T) :- pivot(L, I, P, R), wrapL(P, leaf(I), T0), wrapR(R, T0, T).
lift_tree(node(A, B), L, node(TA, TB)) :-
    lvs(B, [B0 | _]), pivot(L, B0, Q, R), lift_tree(A, Q, TA), lift_tree(B, [B0 | R], TB).

%% lift_mouf(+Derivation, +L, -T0, -T1) (Lean `lift_mouf`)
lift_mouf(left(X, X1, Y, C), L, T0, T1) :-
    pivot(L, X, P, L1), pivot(L1, X1, Q, R), lift_tree(Y, Q, TY), lift_tree(C, R, TC),
    wrapL(P, node(leaf(X), node(TY, node(leaf(X1), TC))), T0),
    wrapL(P, node(node(node(leaf(X), TY), leaf(X1)), TC), T1).
lift_mouf(right(X, X1, C, Y), L, T0, T1) :-
    pivot(L, X, Q, L1), pivot(L1, X1, Q2, S), lift_tree(C, Q, TC), lift_tree(Y, Q2, TY),
    wrapR(S, node(node(node(TC, leaf(X)), TY), leaf(X1)), T0),
    wrapR(S, node(TC, node(leaf(X), node(TY, leaf(X1)))), T1).
lift_mouf(middle(X, X1, B, C), L, T0, T1) :-
    pivot(L, X, P, L1), pivot(L1, X1, Q, S), lvs(C, [C0 | _]), pivot(Q, C0, QB, QC0),
    lift_tree(B, QB, TB), lift_tree(C, [C0 | QC0], TC),
    wrapR(S, node(leaf(X), node(node(TB, TC), leaf(X1))), M0), wrapL(P, M0, T0),
    wrapR(S, node(node(leaf(X), TB), node(TC, leaf(X1))), M1), wrapL(P, M1, T1).
lift_mouf(inL(D, R), L, node(T0, TR), node(T1, TR)) :-
    lvs(R, [R0 | _]), pivot(L, R0, L1, L2), lift_mouf(D, L1, T0, T1), lift_tree(R, [R0 | L2], TR).
lift_mouf(inR(Lt, D), L, node(TL, T0), node(TL, T1)) :-
    moufd_first(D, F), pivot(L, F, L1, L2), lift_tree(Lt, L1, TL), lift_mouf(D, [F | L2], T0, T1).

%% first leaf of the left tree of a derivation
moufd_first(left(X, _, _, _), X).
moufd_first(right(_, _, C, _), F) :- lvs(C, [F | _]).
moufd_first(middle(X, _, _, _), X).
moufd_first(inL(D, _), F) :- moufd_first(D, F).
moufd_first(inR(L, _), F) :- lvs(L, [F | _]).

restrictK(W, K, T, R) :- restrict(W, K, T, R).

check_lift(NMax) :-
    findall(N-Cross, ( between(4, NMax, N), canon([a, b, c, d], 4, N, W), alphabet(W, Alph),
                 N1 is N - 1, numlist(0, N1, Ps),
                 components(W, Ps, PairsW, _), list_to_assoc(PairsW, CW),
                 member(K, Alph), include(alive(W, [K]), Ps, Ps1),
                 components(W, Ps1, Pairs1, _), list_to_assoc(Pairs1, C1),
                 tree(Ps1, T0p), moufd(W, T0p, T1p, D),
                 ( lift_mouf(D, Ps, T0, T1) -> true ; format("lift failed: ~w ~w~n", [W, D]), fail ),
                 ( lvs(T0, Ps), restrictK(W, [K], T0, T0p), restrictK(W, [K], T1, T1p), mouf(W, T0, T1) -> true
                 ; format("lift wrong: ~w ~w~n", [W, D]), fail ),
                 get_assoc(T0p, C1, I0), get_assoc(T1p, C1, I1),
                 ( I0 =\= I1 -> Cross = 1,
                     get_assoc(T0, CW, J0), get_assoc(T1, CW, J1),
                     ( J0 =\= J1 -> true ; format("lift joins components: ~w~n", [W]), fail )
                 ; Cross = 0 ) ), R),
    length(R, NM), aggregate_all(sum(X), member(_-X, R), NX),
    format("K lift (constructive): ~d Moufang moves of 3-letter images of 4-letter words (n ≤ ~d) lifted by gap absorption; ~d cross components and their lifts cross too: ok~n",
           [NM, NMax, NX]).

/* ---------------- Proposition C (⇐): the induction as a path builder ---------------- */

letters_of(W, Ps, Ls) :- maplist([P, C]>>nth0(P, W, C), Ps, Ls).
one_letter(W, Ps) :- letters_of(W, Ps, Ls), sort(Ls, S), length(S, N), N =< 1.

%% path(+W, +T, +T2, -Path): a list of bracketings from T to T2 (Lean `propC_backward`)
path(_, leaf(I), leaf(I), [leaf(I)]) :- !.
path(W, node(L, R), node(L2, R2), Path) :-
    lvs(L, XL), lvs(L2, XL2), length(XL, NL), length(XL2, NL2),
    (   NL =:= NL2 -> eq_split(W, L, R, L2, R2, Path)
    ;   NL < NL2 -> uneq(W, L, R, L2, R2, Path)
    ;   uneq(W, L2, R2, L, R, P0), reverse(P0, Path) ).

eq_split(W, L, R, L2, R2, Path) :-
    path(W, L, L2, PL), maplist([X, node(X, R)]>>true, PL, P1),
    path(W, R, R2, PR), maplist([Y, node(L2, Y)]>>true, PR, [_ | P2]),
    append(P1, P2, Path).

uneq(W, L, R, L2, R2, Path) :-
    lvs(L, X), lvs(L2, XL2), append(X, M, XL2), lvs(R2, Z), M = [M0 | MR], rc(M0, MR, P),
    append(X, M, XM), append(M, Z, MZ),
    (   one_letter(W, XM) ->                                   % case B
        path(W, R, node(P, R2), PR), maplist([Y, node(L, Y)]>>true, PR, P1),
        path(W, node(L, P), L2, PL), maplist([V, node(V, R2)]>>true, PL, P2),
        append(P1, P2, Path)
    ;   one_letter(W, MZ) ->                                   % case C (built from T2, reversed)
        path(W, L2, node(L, P), PL), maplist([V, node(V, R2)]>>true, PL, Q1),
        path(W, node(P, R2), R, PR), maplist([Y, node(L, Y)]>>true, PR, Q2),
        append(Q1, Q2, Q), reverse(Q, Path)
    ;   append(X, MZ, All), letters_of(W, All, Ls), sort(Ls, S), length(S, NS), NS =< 2 ->   % case A
        to_rc(node(L, R), P1), to_rc(node(L2, R2), P2), reverse(P2, [_ | P2r]), append(P1, P2r, Path)
    ;   format("Prop C: no case applies~n"), fail ).

%% rotations to the right comb (Lean `to_rc`, `merge_rc`)
to_rc(leaf(I), [leaf(I)]).
to_rc(node(L, R), Path) :-
    to_rc(L, PL), last(PL, CL), maplist([X, node(X, R)]>>true, PL, P1),
    to_rc(R, PR), maplist([Y, node(CL, Y)]>>true, PR, [_ | P2]),
    last(PR, CR), merge_rc(CL, CR, P3), append([P1, P2, P3], Path0), dedup_adj(Path0, Path).
merge_rc(leaf(I), C, [node(leaf(I), C)]).
merge_rc(node(leaf(I), Rest), C, [node(node(leaf(I), Rest), C) | Path]) :-
    merge_rc(Rest, C, P), maplist([Y, node(leaf(I), Y)]>>true, P, Path).
dedup_adj([], []).
dedup_adj([X], [X]).
dedup_adj([X, Y | T], R) :- ( X == Y -> dedup_adj([Y | T], R) ; R = [X | R1], dedup_adj([Y | T], R1) ).

valid_path(_, _, [_]) :- !.
valid_path(W, Alph, [T, U | Rest]) :-
    ( dn_step(W, Alph, T, U) -> true ; format("Prop C: not a D_N step ~w -> ~w~n", [T, U]), fail ),
    valid_path(W, Alph, [U | Rest]).

check_C_path(NMax) :-
    findall(NP, ( between(3, NMax, N), between(3, N, K), interval_word(K, N, W), alphabet(W, Alph),
                  N1 is N - 1, numlist(0, N1, Ps), findall(S-T, ( tree(Ps, T), sigma(W, T, S) ), ST),
                  findall(1, ( member(S-T, ST), member(S-T2, ST), T @< T2,
                               path(W, T, T2, Path), Path = [T | _], last(Path, T2),
                               valid_path(W, Alph, Path) ), L), length(L, NP) ), Ns),
    sum_list(Ns, Tot),
    format("Prop C (⇐) (constructive): ~d pairs with equal σ joined by the induction's path, every step a D_N-flip (interval words, n ≤ ~d): ok~n",
           [Tot, NMax]).

/* ---------------- Proposition T: σ through cx and the absorption words ---------------- */

span2(T, Lo, Hi) :- lvs(T, Is), Is = [Lo | _], last(Is, Hi).
%% the child of lca(q, r) containing q
subq(leaf(I), _, _, leaf(I)).
subq(node(L, R), Q, Rr, S) :- span2(L, _, LH), span2(R, RL, _),
    ( Rr =< LH -> subq(L, Q, Rr, S) ; RL =< Q -> subq(R, Q, Rr, S) ; S = L ).
cx(A, T, Q, Rr, X) :- subq(T, Q, Rr, S), span2(S, Lo, _), X is max(0, A - Lo).

%% absorption list of leaf k (Lean `ablP`), and its letters (y dropped)
ablp(_, leaf(_), []).
ablp(K, node(L, R), Ab) :- lvs(L, XL), ( memberchk(K, XL) -> ablp(K, L, A0), lvs(R, XR), append(A0, XR, Ab)
                                       ; ablp(K, R, A0), append(A0, XL, Ab) ).
lw(A, B, Ps, Ws) :- foldl([P, Acc0, Acc]>>( P < A -> append(Acc0, [x], Acc) ; P >= A + B -> append(Acc0, [z], Acc) ; Acc = Acc0 ),
    Ps, [], Ws).
omq(A, B, T, Q, Om) :- invariant(T, A, B, _, Phi), omegas(Phi, Up, Vm), Phi = phi(J, _, _, _),
    ( Q < A + J -> Om = Up ; Om = Vm ).
%% x's before the t-th z
xb(Om, Tz, N) :- xb_(Om, Tz, 0, N).
xb_([x | Om], Tz, Acc, N) :- !, Acc1 is Acc + 1, xb_(Om, Tz, Acc1, N).
xb_([z | _], 0, Acc, Acc) :- !.
xb_([z | Om], Tz, Acc, N) :- !, Tz1 is Tz - 1, xb_(Om, Tz1, Acc, N).
xb_([], _, Acc, Acc).

check_T_cx(NMax) :-
    findall(1, ( between(3, NMax, N), between(1, N, A), between(1, N, B), C is N - A - B, C >= 1,
                 three_block(A, B, C, _W, Ps), tree(Ps, T), AB is A + B, AB1 is AB - 1, N1 is N - 1,
                 between(A, AB1, Q),
                 ablp(Q, T, Ab), lw(A, B, Ab, Beta), omq(A, B, T, Q, Om),
                 ( Beta == Om -> true ; format("T: absorption word ≠ ω_q ~w ~w~n", [T, Q]), fail ),
                 forall(between(AB, N1, Rr),
                        ( cx(A, T, Q, Rr, X), Tz is Rr - AB, xb(Om, Tz, X2),
                          ( X =:= X2 -> true ; format("T: cx ≠ xb ~w~n", [T]), fail ),
                          A1 is A - 1,
                          forall(between(0, A1, P),
                                 ( restrict_keep(T, [P, Q, Rr], Rt), ( Rt = node(node(_, _), _) -> Sh = 1 ; Sh = 0 ),
                                   ( P >= A - X -> Sh2 = 1 ; Sh2 = 0 ),
                                   ( Sh =:= Sh2 -> true ; format("T: shape ≠ cx ~w~n", [T]), fail ) )) )) ), L),
    length(L, NL),
    format("Prop T: shapes = cx(q, r), cx = x's before the z in ω_q, absorption word = ω₊/ω₋, on ~d (tree, y-leaf) pairs, n ≤ ~d: ok~n",
           [NL, NMax]).

/* ---------------- Lemma M: the walk and the exact moment ---------------- */

negpow(N, S) :- ( N mod 2 =:= 0 -> S = 1 ; S = -1 ).
%% e^{ω} for a word in x, z (units e1, e4): signed unit
wprod([], 0, 1).
wprod([L | Om], U, S) :- wprod(Om, U0, S0), ( L == x -> E = 1 ; E = 4 ), uprod(E, U0, U, S1), S is S1 * S0.
inv([], 0).
inv([x | Om], N) :- inv(Om, N).
inv([z | Om], N) :- inv(Om, N0), aggregate_all(count, member(x, Om), K), N is N0 + K.

%% Lean `Ssum`
ssum([], P, R, V) :- ( P =:= 0, R =:= 0 -> V = 1 ; V = 0 ).
ssum([x | Om], P, R, V) :- ssum(Om, P, R, V0), ( P > 0 -> P1 is P - 1, ssum(Om, P1, R, V1) ; V1 = 0 ), V is V0 + V1.
ssum([z | Om], P, R, V) :- ssum(Om, P, R, V0), ( R > 0 -> R1 is R - 1, ssum(Om, P, R1, V1), negpow(P, Sg) ; V1 = 0, Sg = 1 ),
    V is V0 + Sg * V1.

check_M_exact(NMax) :-
    findall(1, ( between(3, NMax, N), between(1, N, A), between(1, N, B), C is N - A - B, C >= 1,
                 three_block(A, B, C, W, Ps), tree(Ps, T), invariant(T, A, B, C, Phi), Phi = phi(J, _, _, _),
                 omegas(Phi, Up, Vm),
                 findall(I, nth0(I, W, x), Xs), findall(I, nth0(I, W, y), Ys), findall(I, nth0(I, W, z), Zs),
                 between(0, A, P), between(0, C, R),
                 findall(U-S, ( subset_k(Xs, P, PX), subset_k(Zs, R, RZ), member(Yk, Ys),
                                append([PX, [Yk], RZ], K0), msort(K0, Keep), restrict_keep(T, Keep, T1),
                                uev(W, T1, U, S),
                                % the walk: (−1)^{#z} e^{ω} e₂
                                ablp(Yk, T1, Ab), lw(A, B, Ab, Om), wprod(Om, U0, S0), uprod(U0, 2, U2, S2),
                                negpow(R, Sz), Sw is Sz * S0 * S2,
                                ( U2 =:= U, Sw =:= S -> true ; format("M: walk fails ~w~n", [T1]), fail ) ), US),
                 % σ(p, r)·[j S(ω₊) + (b−j) S(ω₋)]·E(p, r)
                 PP is P mod 2, RR is R mod 2, ( PP =:= 1 -> IP = 1 ; IP = 0 ), ( RR =:= 1 -> IR = 4 ; IR = 0 ),
                 uprod(IP, IR, IB, SB), uprod(IB, 2, IE, SE),
                 Ex is R + P // 2 + R // 2, negpow(Ex, Sig),
                 ssum(Up, P, R, SU), ssum(Vm, P, R, SV), Coef is Sig * SB * SE * (J * SU + (B - J) * SV),
                 aggregate_all(sum(S), member(IE-S, US), Tot),
                 ( forall(member(U-_, US), U =:= IE) -> true ; format("M: units differ~n"), fail ),
                 ( Tot =:= Coef -> true ; format("M: moment ~w (~d,~d): ~d vs ~d~n", [T, P, R, Tot, Coef]), fail ) ), L),
    length(L, NL),
    format("Lemma M (exact, sign and unit included): walk on every restriction; moment = σ·[j S(ω₊) + (b−j) S(ω₋)]·E on ~d (tree, p, r), n ≤ ~d: ok~n",
           [NL, NMax]).

%% control: on a non-interval word the path builder must fail for some σ-equal pair
control_C :-
    W = [0, 1, 2, 1, 0], alphabet(W, Alph), numlist(0, 4, Ps),
    findall(S-T, ( tree(Ps, T), sigma(W, T, S) ), ST),
    member(S-T, ST), member(S-T2, ST), T @< T2,
    \+ with_output_to(string(_), ( path(W, T, T2, P), valid_path(W, Alph, P) )), !,
    format("control: on the non-interval word ~w the path builder fails for a σ-equal pair, as it must~n", [W]).

run :-
    set_stream(user_output, encoding(utf8)),
    control_C,
    check_lift(7),
    check_C_path(7),
    check_T_cx(8),
    check_M_exact(7).
