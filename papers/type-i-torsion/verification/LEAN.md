# Lean verification

**Status as of 25 November 2026.** The mathematical statement is [Theorem A and its production corollary](../manuscript/paper_github.md#main-result). The scopes below distinguish the fixed-place theorem from the selection of its inputs on the original family. The public issue comment records the initial seven replayed modules. Later continuation results are identified as such. [Public progress record](https://github.com/leanprover-community/riemann-hypothesis/issues/77#issuecomment-7167482262)

## Environment

- Lean `leanprover/lean4:v4.37.0-rc1`, compiler commit `0b77e12952ad39077d80d8bd6b66d601f225c321`.
- Upstream `9282d3a102c4aff0e6026746db2a8990f5d9cddd` and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. [Upstream toolchain](https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/lean-toolchain) · [Lake manifest](https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/lake-manifest.json)
- The transitive audits for the checked declarations recorded `propext`, `Classical.choice` and `Quot.sound`.
- The six named export checks were `leanchecker`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche` and `con-ron`. The checks ran on the managed Lean 4.37 research route.

## Theorem-to-Lean crosswalk

| Mathematics | Lean declaration or stage | Checked scope and evidence |
| --- | --- | --- |
| Integral row on the native Weyl lattice | `exists_native_typeI_separating_row`, r6 | Native build, type and axiom audit, six replays. Rank one and adjacent capacities are supplied. |
| Literal first span and empty subset | `literalFirstSpan_eval_mem_prime_power` and `literalNP_pow_mem_of_empty_word`, r1 | Native build, type and axiom audit, six replays. The row test accounts for both branches. |
| First excess and length | `literal_local_excess_of_primitive_row`, r4, and `literal_local_length_lower_of_primitive_row`, r3 | Native builds, type and axiom audits, six replays per export. A primitive row and the unit at this chart are supplied. |
| Comparison and exact same-place order | `ramifiedComparisonAt_mk` and `exists_same_place_order_of_primitive_row`, r2 | Native build, type and axiom audit, six replays. The checked comparison lands in `A_w / U_w`. The article gives the elementary injection into the ambient quotient. |
| Fixed-place assembly | `servedWord_fromNativeAdjacentCapacity_withSeedBridge`, r1 | Native build, type and axiom audit. The continuation reports six replays of the matching export. The chosen local data and chart-unit interface are inputs. |
| Direct seed bridge | `servedWord_fromNativeAdjacentCapacity` consuming `F6SeedBridge` | The continuation reports a passing native build and transitive axiom audit. |
| Finite-depth and selection inputs | `TypeIFiniteDepth` and the finite tent and character identities | The continuation reports compilation of the finite-depth module and these identities. The indexed selector is in progress. |
| Theorem A and production corollary | Original-family selection and inhabited production caller | End-to-end Lean verification is in progress. The paper uses the original design supplier and `FamCore.exists_pt`. |

The date-stamped evidence for pending stages should be updated as their exact declarations and replay records become available. The manuscript, local formal checks and production application are cited at their respective scopes.
