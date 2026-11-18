# Prolog formalization (SWI-Prolog)

Three programs. Each one checks independently what the Lean development proves:

```bash
swipl -q -g main -t halt caterpillar.pl   # run-sequence combinatorics, finite base, constructive Prop. E
swipl -q -g main -t halt octonion.pl      # octonion identities and Lemma W's core
swipl -q -g main -t halt trees.pl         # G3 end to end, from words to bracketings
```

## `caterpillar.pl`: Proposition E

The definitions are the same as in Lean, written as logic programs:
- `valid/1`, `failure/2`, `cond/3`;
- the certificate relations `chain/3` and `cat/3`. Their derivation terms use the constructors `bottom`, `l`, `r`, `d`, `passL`, `passR`, `passD`, `moveD`, `moveL`, `moveR`. The same relation checks a given derivation and searches for one.

`construct/3` is the induction proof of Proposition E written as a program: it follows the case analysis without search.

Checks:
- the base, exhaustively (240 cases);
- all 44,670 constructed certificates up to 12 runs, each re-checked by `cat/3`;
- the exact characterization up to 9 runs;
- every non-interval word of length ≤ 9.

## `octonion.pl`: the octonion identities

Integer octonions use the repository's Cayley–Dickson table.

**Identity checks.** Moufang left, right and middle, left and right alternative, and flexible. The check is **complete, not sampled**. The product is bilinear, and each identity is linear in some arguments and quadratic in one. So it holds everywhere iff it holds when the linear arguments range over the basis `e_i` and the quadratic one over `e_i` and `e_i + e_j`. That is 2,304 cases for each Moufang identity. Random 7-digit tests run on top, plus a negative control: associativity fails, so the check can fail.

**Lemma W core.** `[X,Y,Z] = det(X,Y,Z)·[e₁,e₂,e₄]` on `span(e₁,e₂,e₄)`. The identity is trilinear, so the 27 basis triples are a complete check. Also `[e₁,e₂,e₄] = 2e₇`.

## `trees.pl`: G3 end to end

For each non-interval 3-letter word, `construct/3` builds the run-level certificate and `glue_cat/6` turns it into bracketings `T₀`, `T₁` and a chain of path nodes. This mirrors the Lean `glue_cat`. Each link is then checked independently:

- **(a)** `mouf/3`: `T₁` comes from `T₀` by one left, right or middle Moufang move with a single repeated letter.
- **(b)** `pchain/3`: the position-level chain conditions of Lemma Cat hold, and the chain nodes are nodes of `T₀`.
- **(c)** `certified/4`: **Lemma Cat's conclusion by brute force.** Every compatible rotation that would delete a chain node has determinant ≠ 0.
- **(d)** **Exact D_N-component search** by breadth-first search, with no use of Lemma R′. `T₁` is not reachable, and every reachable tree keeps all chain nodes, which is Lemma R′'s conclusion.
- **(e)** `T₀` and `T₁` evaluate to the same octonion under random integer octonions for x, y, z.

Results (`../data/prolog_trees.log`):

| Lengths | Checks | Words |
|---|---|---|
| n ≤ 9 | (a)–(e), including the exact component search | 4,330 |
| n = 10 | (a)–(c) and (e) | 9,294 |

Negative controls confirm that `certified/4` and `mouf/3` can fail.

Prolog executes and checks. It is not a proof assistant: the all-length statements are the Lean theorems `Caterpillar.propE`, `Caterpillar.g3_trees` and `Octonion.moufang_*`.
