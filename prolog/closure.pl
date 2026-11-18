:- encoding(utf8).
/*  Closure (Lean Closure.lean), with the main-theorem pattern as a finite sweep.

    - Converse of G2 (Lean `reach_ev`): for every interval word, bracketings in the same D_N-component take
      equal values at every sampled integer valuation.
    - G2 as an equivalence (Lean `g2_iff`): bracketings in different D_N-components are separated, certified
      exactly by the G2Final witness valuation (`g2_witness` in assembly.pl).
    - Kernel classes flip-connected (Lean `kernel_flip_connected`, `kernel_flip_connected_two`): for interval
      words and for words with at most two letters, each class of equal values is connected by flips whose
      two ends take equal values.
    - Main-theorem sweep (not yet a Lean statement): over all words with n ≤ NMax, the kernel classes are
      flip-connected exactly when the word has at most two letters or is an interval word. Here "equal maps"
      is approximated by equality at S random integer valuations (a difference is exact; an equality is
      evidence, not proof).

    Usage:   swipl -q -g run_closure -t halt closure.pl
*/

:- ensure_loaded(assembly).

samples(8).

rand_oct(O) :- length(O, 8), maplist([X]>>(random_between(-3, 3, X)), O).
rand_vals(Alph, S, Vals) :-
    length(Vals, S), maplist([Val]>>(findall(L-O, (member(L, Alph), rand_oct(O)), Val)), Vals).

signature(W, Vals, T, Sig) :- maplist([Val, V]>>evv(W, Val, T, V), Vals, Sig).

is_interval(W) :- clumped(W, Rs), is_set(Rs).
clumped([], []).
clumped([X | Xs], [X | Rs]) :- skip(X, Xs, Ys), clumped(Ys, Rs).
skip(X, [X | Xs], Ys) :- !, skip(X, Xs, Ys).
skip(_, Ys, Ys).

%% kernel classes and whether each is connected by value-preserving flips
kernel_check(W, Conn, NClasses) :-
    alphabet(W, Alph), samples(S), rand_vals(Alph, S, Vals),
    length(W, N), N1 is N - 1, numlist(0, N1, Ps),
    findall(Sig-T, ( tree(Ps, T), signature(W, Vals, T, Sig) ), ST0), keysort(ST0, ST),
    group_pairs_by_key(ST, Groups), length(Groups, NClasses),
    ( forall(member(Sig-Cls, Groups), class_connected(W, Vals, Sig, Cls)) -> Conn = true ; Conn = false ).

class_connected(_, _, _, [_]) :- !.
class_connected(W, Vals, Sig, [T0 | Ts]) :-
    list_to_ord_set([T0 | Ts], All), kreach([T0], W, Vals, Sig, [T0], Seen), ord_subtract(All, Seen, []).
kreach([], _, _, _, S, S).
kreach([T | Q], W, Vals, Sig, S0, S) :-
    findall(U, ( rot(T, U, _, _, _), \+ memberchk(U, S0), signature(W, Vals, U, Sig) ), Us0), sort(Us0, Us),
    ord_union(S0, Us, S1), append(Q, Us, Q1), kreach(Q1, W, Vals, Sig, S1, S).

/* ---- converse and equivalence on interval words ---- */

check_iff(NMax) :-
    findall(r(Same, Sep), ( between(3, NMax, N), between(1, N, K), interval_word(K, N, W),
              alphabet(W, Alph), samples(S), rand_vals(Alph, S, Vals),
              N1 is N - 1, numlist(0, N1, Ps), components(W, Ps, Pairs, _),
              findall(1, ( member(T-I, Pairs), member(T2-I, Pairs), T @< T2,
                           ( signature(W, Vals, T, G), signature(W, Vals, T2, G) -> true
                           ; format("FAIL converse ~w~n", [W]), fail ) ), L1), length(L1, Same),
              findall(1, ( member(T-I, Pairs), member(T2-J, Pairs), I < J,
                           ( g2_witness(W, T, T2, Val), evv(W, Val, T, V1), evv(W, Val, T2, V2), V1 \== V2 -> true
                           ; format("FAIL separation ~w~n", [W]), fail ) ), L2), length(L2, Sep) ), Rs),
    foldl([r(A, B), X0-Y0, X-Y]>>(X is X0 + A, Y is Y0 + B), Rs, 0-0, SA-SB),
    format("g2_iff: interval words n ≤ ~d — ~d same-component pairs take equal values; ~d different-component pairs separated by the G2 witness~n",
           [NMax, SA, SB]).

/* ---- main-theorem sweep ---- */

sweep(NMax) :-
    findall(W-Pred-Conn, ( between(3, NMax, N), between(1, N, K), canon([a, b, c, d, e, f, g], K, N, W),
              length(W, _), alphabet(W, Alph), length(Alph, NA),
              ( (NA =< 2 ; is_interval(W)) -> Pred = true ; Pred = false ),
              kernel_check(W, Conn, _) ), Rs),
    length(Rs, NW),
    include([_-P-C]>>(P == C), Rs, Ok), length(Ok, NOk),
    include([_-true-_]>>true, Rs, Pos), length(Pos, NPos),
    ( NOk =:= NW -> true ; forall((member(W-P-C, Rs), P \== C), format("MISMATCH ~w predicted ~w got ~w~n", [W, P, C])) ),
    format("main sweep: ~d/~d words (n ≤ ~d, all canonical words) agree: kernel classes flip-connected ⟺ ≤ 2 letters or interval (~d connected, ~d not)~n",
           [NOk, NW, NMax, NPos, NW - NPos]),
    forall(between(3, NMax, N),
           ( aggregate_all(count, (member(W-_-false, Rs), length(W, N)), Bad), bell(N, B), F is B - 2 ^ N + N,
             format("  n = ~d: ~d words with a disconnected kernel class; Bell(n) − 2^n + n = ~d~n", [N, Bad, F]),
             Bad =:= F )).

bell(N, B) :- bell_row(N, [1], R), R = [B | _].
bell_row(0, R, R) :- !.
bell_row(N, [H | T], R) :- last([H | T], L), foldl([X, A0-Acc, A-[A | Acc]]>>(A is A0 + X), [H | T], L-[L], _-Rev),
    reverse(Rev, Row), N1 is N - 1, bell_row(N1, Row, R).

run_closure :-
    set_stream(user_output, encoding(utf8)),
    set_random(seed(20261118)),
    check_iff(6),
    sweep(6).
