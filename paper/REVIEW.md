# Pre-release review round

The draft was refereed by an independent AI reviewer that had not seen how the paper was produced. It
rechecked the main claims with its own code: the main theorem for all words with n ≤ 7, Proposition T for
a+b+c ≤ 8, Lemma W, Lemma I and Table 1. It recommended minor revision. This file lists every point it
raised and what changed. This was an AI review. It is not a substitute for human refereeing.

## Major issues

| # | Issue | Resolution |
|---|---|---|
| 1 | Proposition T: the component count was not formalized (`propT_count` proves only a binomial identity), the completeness half of the proof was a sketch, and the list of rotations missed the core-splitting rotation. | Proposition T now states only the classification, which is proved in Lean (`PropT.propT`); the paper says it relies on that formal proof. The count moved to a remark, marked as not formalized and not used for the main theorem. The core-splitting rotation was added. Table 2 and the introduction were corrected. |
| 2 | Lemma M compared octonion coefficients with Clifford coefficients. | The paper now defines integer coefficients Γ_ω(p,r) and states μ_T(p,r) = ε[jΓ₊ + (b−j)Γ₋]·E_{p,r}, matching `LemmaM.lemmaM`. In the proof, "right siblings contain only z's" now says it holds after unchosen leaves are set to 1, and the absorption order is credited to the definition of the core. |
| 3 | The definition of the caterpillar tree T₀ conflicted with M-left/M-mid, and the M-left condition was wrong. | T₀ keeps the block Y and the pattern x((BC)x) as single subtrees. M-left now requires only that the next step be L or the bottom. |
| 4 | The abstract claimed "preserves the map iff rank ≤ 2" for all words; counterexample xyzyx. | The abstract now states one direction in general and the converse for interval words, and the introduction gives the counterexample. |
| 5 | The formalization claims went too far, the trusted base was incomplete, there was no axiom log for every cited name, and Table 2 had no Lemma I row. | The claims are now precise and the trusted base lists every definition file. `data/lean_axioms.log` holds `#print axioms` for all 40 names in Table 2. Table 2 gained a Lemma I row (`propC_forward`, `dn_assoc_zero`) and lists `lemmaV_powers_AC/BC`. |
| 6 | The remark on split octonions was wrong, and the sedenion remark was unsupported. | Both algebras are real forms of 𝕆⊗ℂ, so split octonions have the same kernel classes and the theorems hold for them verbatim. The sedenion claim was removed. |
| 7 | Corollary 4.6 was proved via G2, its novelty was not checked, and the related work was thin. | Corollary 4.6 now has the two-line direct proof and is marked "expected to be known". Moufang (1935) and Zhevlakov–Slin'ko–Shestakov–Shirshov were added. |

## Minor issues

- Notation clashes were removed:
  - ν for the norm form;
  - 𝒞 for contexts;
  - τ for triple shapes;
  - κ for the core;
  - h for the caterpillar length;
  - 𝒮 for self-certifying sets;
  - supp for supports;
  - Γ_ω for Clifford coefficients;
  - ε_{p,r} for signs;
  - ζ, ξ for profiles;
  - β for the Kronecker base;
  - η for entry letters;
  - α, β, γ for peeled letters;
  - u for the peeled run in M-left;
  - i₁ < i₂ < i₃ for leaf triples.
- Lemma I is reworded; the case that is not triangular is now spelled out with a displayed matrix.
- The "Fact" in Proposition E is restated as "at least one of the two is valid".
- The converse in G2 cites Lemma I directly, and the redundant sentence in Lemma Cat was removed.
- Proposition S notes that ζ(0) and ξ(0) are never both zero, because b ≥ 1.
- "26,439 words" is now "with 3 ≤ n ≤ 9". "Independent Prolog" is now "a second implementation, developed in the same AI-assisted process".
- In Table 1 the column header is "≤ 2 letters" and the table sits next to the proof.
- The quoted Lean statement shows `@decide … (Classical.propDecidable _)`.
- Bibliography: [Lean] is cited; the HL key is corrected; Moufang and ZSSS are added.
- Figure 1 is referenced, displayed matrices replace the inline ones, the Lean quotations no longer overflow, and Inconsolata is used for code.
