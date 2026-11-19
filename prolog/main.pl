:- encoding(utf8).
/*  The closed loop (Lean WExist.lean, Main.lean, Count.lean), as checks.

    1. Lemma W over ℤ (Lean `WExist.lemmaW_exists`): for every flip (AB)C ↔ A(BC) whose count matrix has a
       nonzero 3×3 minor det on letters p, q, r, the valuation p ↦ 1 + M e₁, q ↦ 1 + M e₂, r ↦ 1 + M e₄,
       other letters ↦ 1, with M = 2|det| + 1, gives a nonzero associator whose e₇ coordinate is
       2·det·M³ modulo M⁴. Hence (`kerflip_dn`) a flip that keeps the map is a D_N-flip; checked directly too.
    2. The "only if" direction (Lean `MainThm.not_kerconn`): every word with ≥ 3 letters that is not an
       interval word has a Moufang pair of bracketings in different D_N-components. Its two ends are
       equal maps (Moufang), and no map-preserving flip path joins them.
    3. The "if" renumbering (Lean `rk`, `rk_iff`): for interval words the run index is monotone and has the
       same equalities as the letters.
    4. The count (Lean `Count`): over restricted growth strings, two-letter words 2ⁿ⁻¹, interval words 2ⁿ⁻¹,
       both n, all-zero words 1; good words 2ⁿ − n; Bell(n) − 2ⁿ + n with a disconnected class.

    Usage:   swipl -q -g run_main -t halt main.pl
*/

:- ensure_loaded(closure).

scal(K, A, B) :- maplist([X, Y]>>(Y is K * X), A, B).

wexist_val(Alph, P, Q, R, M, Val) :-
    unit(0, One), unit(1, E1), unit(2, E2), unit(4, E4),
    scal(M, E1, M1), scal(M, E2, M2), scal(M, E4, M4),
    oadd(One, M1, VP), oadd(One, M2, VQ), oadd(One, M4, VR),
    findall(L-V, ( member(L, Alph), ( L == P -> V = VP ; L == Q -> V = VQ ; L == R -> V = VR ; V = One ) ), Val).

nz_minor(W, Alph, A, B, C, P, Q, R, D) :-
    cnt(W, A, Alph, VA), cnt(W, B, Alph, VB), cnt(W, C, Alph, VC),
    length(Alph, NA), NA1 is NA - 1,
    between(0, NA1, I), between(I, NA1, J), J > I, between(J, NA1, K), K > J,
    pick3(VA, I, J, K, X), pick3(VB, I, J, K, Y), pick3(VC, I, J, K, Z), det3(X, Y, Z, D), D =\= 0, !,
    nth0(I, Alph, P), nth0(J, Alph, Q), nth0(K, Alph, R).

check_wexist(NMax) :-
    findall(1, ( between(3, NMax, N), between(3, N, Kl), canon([a, b, c, d, e, f, g], Kl, N, W),
                 alphabet(W, Alph), N1 is N - 1, numlist(0, N1, Ps), tree(Ps, T), rot(T, _, A, B, C),
                 \+ dn(W, Alph, A, B, C),
                 nz_minor(W, Alph, A, B, C, P, Q, R, D),
                 M is 2 * abs(D) + 1, wexist_val(Alph, P, Q, R, M, Val),
                 evv(W, Val, A, VA), evv(W, Val, B, VB), evv(W, Val, C, VC), octonion:assoc(VA, VB, VC, X),
                 nth0(7, X, X7), M4 is M ^ 4,
                 ( zero(Z), X \== Z, (X7 - 2 * D * M ^ 3) mod M4 =:= 0 -> true
                 ; format("FAIL Lemma W witness ~w ~w~n", [W, T]), fail ) ), L),
    length(L, NL),
    format("Lemma W over Z: ~d rank-3 flips (n ≤ ~d), each with a nonzero associator at M = 2|det|+1, e7 ≡ 2·det·M³ (mod M⁴)~n", [NL, NMax]).

%% map-preserving flips are D_N-flips: equality at sampled valuations implies rank ≤ 2
check_kerflip(NMax) :-
    findall(1, ( between(3, NMax, N), between(1, N, Kl), canon([a, b, c, d, e, f, g], Kl, N, W),
                 alphabet(W, Alph), samples(S), rand_vals(Alph, S, Vals),
                 N1 is N - 1, numlist(0, N1, Ps), tree(Ps, T), rot(T, U, A, B, C),
                 signature(W, Vals, T, G), signature(W, Vals, U, G),
                 ( dn(W, Alph, A, B, C) -> true ; format("FAIL kerflip ~w~n", [W]), fail ) ), L),
    length(L, NL),
    format("kerflip_dn: ~d flips that keep the sampled values (n ≤ ~d), all D_N-flips~n", [NL, NMax]).

/* ---- only if: a Moufang pair across D_N-components ---- */

check_only_if(NMax) :-
    forall(between(3, NMax, N),
      ( findall(W, ( between(3, N, Kl), canon([a, b, c, d, e, f, g], Kl, N, W), \+ is_interval(W) ), Ws),
        length(Ws, NW),
        include(mouf_cross, Ws, Ok), length(Ok, NOk),
        bell_num(N, B), F is B - 2 ^ N + N,
        format("only if, n = ~d: ~d/~d non-interval words with ≥ 3 letters have a Moufang pair in different D_N-components, equal at sampled valuations (Bell − 2ⁿ + n = ~d)~n",
               [N, NOk, NW, F]),
        NOk =:= NW, NW =:= F )).

mouf_cross(W) :-
    length(W, N), N1 is N - 1, numlist(0, N1, Ps), components(W, Ps, Pairs, _),
    alphabet(W, Alph), samples(S), rand_vals(Alph, S, Vals),
    member(T-I, Pairs), mouf(W, T, T1), memberchk(T1-J, Pairs), I =\= J,
    signature(W, Vals, T, G), signature(W, Vals, T1, G), !.

/* ---- the run renumbering of interval words ---- */

rk_list(W, R) :- W = [_ | _], rk_(W, _, 0, R).
rk_([], _, _, []).
rk_([X | Xs], Prev, K0, [K | Ks]) :- ( var(Prev) -> K = K0 ; X == Prev -> K = K0 ; K is K0 + 1 ), rk_(Xs, X, K, Ks).

check_rk(NMax) :-
    findall(1, ( between(1, NMax, N), between(1, N, K), interval_word(K, N, W0), shuffle_letters(W0, W),
                 rk_list(W, R), msort(R, R),
                 forall(( nth0(P, W, X), nth0(Q, W, Y) ), ( nth0(P, R, RP), nth0(Q, R, RQ), ( X == Y -> RP == RQ ; RP \== RQ ) )) ), L),
    length(L, NL),
    format("rk: ~d interval words (n ≤ ~d, letters renamed) — run index monotone, same equalities as the letters~n", [NL, NMax]).
shuffle_letters(W0, W) :- maplist([X, Y]>>(Y is 7 * X + 3), W0, W).   % injective for every length

/* ---- the count over restricted growth strings ---- */

nl_rgs([], 0).
nl_rgs(W, K) :- W = [_ | _], max_list(W, M), K is M + 1.
rgs(0, [[]]).
rgs(N, L) :- N > 0, N1 is N - 1, rgs(N1, L1),
    findall(W2, ( member(W, L1), nl_rgs(W, K), between(0, K, C), append(W, [C], W2) ), L).
sorted_w(W) :- msort(W, W).
bell_num(N, B) :- rgs(N, L), length(L, B).

check_count(NMax) :-
    forall(between(1, NMax, N),
      ( rgs(N, L), length(L, B),
        aggregate_all(count, (member(W, L), nl_rgs(W, K), K =< 2), CT),
        aggregate_all(count, (member(W, L), sorted_w(W)), CI),
        aggregate_all(count, (member(W, L), nl_rgs(W, K), K =< 2, sorted_w(W)), CTI),
        aggregate_all(count, (member(W, L), nl_rgs(W, 1)), CZ),
        aggregate_all(count, (member(W, L), \+ (nl_rgs(W, K), K =< 2), \+ sorted_w(W)), Bad),
        P is 2 ^ (N - 1),
        ( CT =:= P, CI =:= P, CTI =:= N, CZ =:= 1, Bad =:= B - 2 ^ N + N -> true
        ; format("FAIL count n = ~d~n", [N]), fail ),
        format("  n = ~d: Bell ~d, two-letter ~d, interval ~d, both ~d, all-zero ~d, disconnected ~d = Bell − 2ⁿ + n~n",
               [N, B, CT, CI, CTI, CZ, Bad]) )).

/* ---- canonical representatives and Stirling numbers (Lean Canon.lean) ---- */

canon_word(W, C) :- cw_(W, [], C).
cw_([], _, []).
cw_([X | Xs], Seen, [I | Is]) :-
    ( nth0(I, Seen, X) -> Seen1 = Seen ; length(Seen, I), append(Seen, [X], Seen1) ), cw_(Xs, Seen1, Is).

check_canon(NMax) :-
    forall(between(1, NMax, N),
      ( rgs(N, L), list_to_ord_set(L, LS), length(L, B), length(LS, B),
        N1 is N - 1,
        findall(C, ( length(W, N), maplist([X]>>between(0, N1, X), W), canon_word(W, C) ), Cs0),
        sort(Cs0, Cs),
        ( Cs == LS -> true ; format("FAIL canon n = ~d~n", [N]), fail ),
        format("  n = ~d: ~d words over ~d letters fall into ~d renaming classes, one per restricted growth string~n",
               [N, N ** N, N, B]) )).

stirling_num(N, K, S) :- rgs(N, L), aggregate_all(count, (member(W, L), nl_rgs(W, K)), S).

check_stirling(NMax) :-
    findall(1, ( between(1, NMax, N), N1 is N + 1, between(0, N1, K), K1 is K + 1,
                 stirling_num(N1, K1, A), stirling_num(N, K1, B), stirling_num(N, K, C),
                 ( A =:= K1 * B + C -> true ; format("FAIL Stirling ~d ~d~n", [N, K]), fail ) ), L),
    length(L, NL),
    format("Stirling recurrence S(n+1,k+1) = (k+1)S(n,k+1) + S(n,k): ~d cases, n ≤ ~d~n", [NL, NMax]).

run_main :-
    set_stream(user_output, encoding(utf8)),
    set_random(seed(20261119)),
    check_wexist(6),
    check_kerflip(6),
    check_only_if(6),
    check_rk(8),
    format("count over restricted growth strings:~n"),
    check_count(10),
    format("canonical representatives:~n"),
    check_canon(6),
    check_stirling(8).
