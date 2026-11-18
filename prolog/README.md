# Prolog formalization (SWI-Prolog)

`swipl -q -g main -t halt caterpillar.pl`

The same objects as the Lean development, written as logic programs:

- `valid/1`, `failure/2`, `cond/3`: run sequences, the excluded entries and condition (C1).
- `chain/3` and `cat/3`: the certificate relation, with derivation terms built from the constructors
  `bottom`, `l`, `r`, `d`, `passL`, `passR`, `passD`, `moveD`, `moveL`, `moveR`. The same relation
  **checks** a given derivation and **searches** for one.
- `construct/3`: the **induction proof of Proposition E written as a program**. It follows the case
  analysis (L, R or D peel) with no search, and calls the search only for the base of 4 and 5 runs.
  The proof says the gap branch is unreachable, and it raises an error if it ever were reached.
- `runs/2`, `interval_word/1`: words to run sequences.

`main` runs four checks:
1. the base, exhaustively: 240 (sequence, entry) pairs with 4 or 5 runs, Good ⇔ not failure;
2. `construct/3` on every non-excluded pair with 4–12 runs (44,670 certificates), each re-checked by
   `cat/3`;
3. the exact characterization, as a sanity check, for 6–9 runs;
4. every non-interval 3-letter word of length ≤ 9, certified through its run sequence.

Prolog runs the constructive proof and checks its output. It is not a proof assistant: the statement for
all lengths is the Lean theorem `Caterpillar.propE`.
