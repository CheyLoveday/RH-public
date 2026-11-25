# Completed Modal checks

The Type I proof was built and audited on Modal through the ODproof-managed Lean 4.37.0-rc1 research route. Two proof targets have different evidence. The completed six-checker result covers the **fixed-place quotient core**. The **integrated production proof** has a successful kernel build and type and axiom audit. [Published run record](run.json) · [Fixed-place replay receipt](modal-checks.json)

## Fixed-place quotient core

The replay target is `servedWord_fromNativeAdjacentCapacity_withSeedBridge`. It takes one fixed word and served place with the selected orbit, the adjacent capacities, the omission depth and the chart-unit interface. It returns the row-induced local excess and the comparison result for one class. The replay input was 686,426,131 bytes, with SHA-256 `b688ef2c8296ff7a38eaa136f4e7b5ddea96b5f1a0029b3f4dc58224684b7c28`. [Checked source](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/TypeINativeQuotientCore.lean#L17)

| Checker | Exit | Source of result |
| --- | --- | --- |
| `leanchecker` | 0 | Earlier compatible result on the same export digest |
| `leanchecker-paranoid` | 0 | Ran on the Modal completion worker |
| `lean4lean` | 0 | Ran on the Modal completion worker |
| `nanoda` | 0 | Ran on the Modal completion worker |
| `con-leche` | 0 | Ran on the Modal completion worker |
| `con-ron` | 0 | Ran on the Modal completion worker |

The public receipt records matching input hashes, tool hashes and log hashes. The large core export and raw replay logs are retained privately. This evidence applies to the local theorem with the supplied inputs, particularly [the quotient and order steps](../reading/PROOF_MAP.md#lp5).

## Integrated production proof

| Stage | Observed result |
| --- | --- |
| Native Lean build | **PASS**. The selector and depth modules, direct seed bridge, indexed theorem and inhabited caller built in the pinned environment. |
| Type and transitive axiom audit | **PASS**. Five endpoint types were read back. Each of the eleven audited declarations uses only `propext`, `Classical.choice` and `Quot.sound`. |
| Separate statement reference | The reference built and exported successfully. |
| Integrated solution export | Stopped on request. The retained partial export is 19,444,007,303 bytes. |
| Integrated replays and reference comparison | **NOT_RUN**. They were cancelled before execution. |

The integrated theorem obtains the earlier core inputs through [arithmetic selection and depth](../reading/PROOF_MAP.md#lp1), [the actual seed bridge](../reading/PROOF_MAP.md#lp4) and [the original production construction](../reading/PROOF_MAP.md#lp7). ODproof verified the proof checkpoint after the worker stopped. [Integrated run record](run.json) · [Public type and axiom log](integrated-types-and-axioms.txt) · [Lean correspondence and reproduction](LEAN.md)
