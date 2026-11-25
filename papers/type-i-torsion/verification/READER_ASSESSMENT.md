# Type I reader assessment

The pilot measures whether a reader can reconstruct the mathematical argument and transfer it to a new example. This record concerns the explanation. Formal evidence is recorded in the [Lean crosswalk](LEAN.md) and [Modal receipts](MODAL.md).

## Procedure

1. Freeze the exact theorem, the candidate reading files and the questions. Give the reader only the exact target and seven top-level steps, with the detailed blocks closed. Ask for the chain of implications, the common witness and the hypotheses used at the row, seed and order joins. Save the reader's first response before revealing the next layer.
2. Give the reader the expanded proof map. Ask them to rederive the load-bearing estimates and the Gram, integrality and first-crossing arguments without opening Lean tactics. Record any conclusions they still have to assume.
3. Ask for the two-row transfer before giving its answer. Look for the unit-determinant argument, the two scalar layers, the length bound and a separate finiteness premise. A reader may attempt this during the first phase.

For a comparison with an earlier guide, fix both versions and the rubric in advance. Use readers unfamiliar with the answer key and save first-pass responses separately from later revisions. Score mathematical correctness and the ability to identify the hypotheses separately. [Exact target and overview](../reading/PROOF_MAP.md#dependency-map) · [Questions and transfer task](../reading/EXPLAINED.md#reconstruct-the-proof)

## Recorded AI-reader passes

An earlier repository note reports that a separate Codex reader recovered the proof and answered four questions, and asked that the guide name the prime of the same place in the multiplier condition. The note is the available evidence for that report. [Earlier repository note](https://github.com/CheyLoveday/RH-public/blob/9f1832f773c1a801580d9bb6b80d9449ccf252c7/papers/type-i-torsion/reading/PROOF_MAP.md#reader-reconstruction)

For this revision a fresh Codex reader received the first-pass instructions without the authoring conversation, proof leaves, Lean source or transfer answer. It read the exact target and seven top-level steps, and the six questions and two-row exercise. The input files had these SHA-256 digests.

| File | SHA-256 |
| --- | --- |
| `PROOF_MAP.md` | `fe33808fae5055273b2050474763028159b7bd31a52d5288062479641b3da881` |
| `EXPLAINED.md` | `770a668ee1cd157f3b88c6690706ecdfc6e0f7fd99fbb92fcce1ef31a1ff5a6b` |

### First pass

The reader recovered all seven obligations and kept the member, word and place fixed. It derived the scalar-layer surjection, identified both denominator branches, explained how membership in the same prime could destroy local survival, and distinguished production inhabitation from the indexed theorem. It argued correctly that the maximal ideal is closed under the integral combinations used in unit extraction, while flagging the chart-span assertion as inferred.

The reader identified the repeated-flag condition but could not derive the Frobenius congruence from the overview. It also flagged the weight and slot-identification estimates, the literal comap and finiteness argument, and the precise served equivalence needed to clear the global denominator. Its first account of the multiplier used an invertibility intuition. The second pass tests the actual two-multiplier argument.

The transfer answer gave $p^TA/U\twoheadrightarrow(p^TO/p^{T+1}O)^2$ via the invertible joint readout and obtained $\ell_O(A/U)\ge erT+2e$. It supplied a killing-power containment for finiteness and gave $U=0$ as a case allowed by the row hypotheses.

### Second pass and revision

With the detailed map and still without Lean or the answer key, the reader recovered the normalized pair-weight lower bound and all three exclusion charges. It accounted for the $3/32$ leading and $1/8$ residual budgets, derived the rational Gram representative and gave a separate argument for integrality on the native generators. Its revised account of exact order used the two multipliers outside the same prime and contradicted the preceding exponent directly.

The reader still needed intermediate steps for the depth budgets and complementary-minor normalization. The editor added both, and the reader checked those passages on proof-map SHA-256 `fc52c0dee67df35a50ce7ac6cf1ea19145d3590f2d1c4dbf4e61d7f617a0466a`. The follow-up confirmed the leading terms, residual envelope and one power of $p$ per minor. It asked for the window comparison and the product of slot scalars to be explicit. These are now written out. [Finite cutoff](../reading/PROOF_MAP.md#lp2-1) · [Incoming normalization](../reading/PROOF_MAP.md#lp3-4)

## Assessment limits

This was a single AI-reader reconstruction and transfer exercise. Independent human reconstruction, a matched comparison and an estimate of learning improvement are outstanding.
