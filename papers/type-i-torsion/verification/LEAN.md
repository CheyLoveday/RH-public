# Lean verification

**The indexed Type I theorem and the inhabited production corollary passed the Lean kernel build and exact type and transitive axiom audit on 25 November 2026.** One class has exact order $p^{T+1}$ in the original word quotient and at the selected served place. The checked row yields the first extra local layer and the finite length lower bound. [Theorem A and Proposition B](../manuscript/paper_github.md#main-result) · [Integrated audit output](integrated-types-and-axioms.txt) · [Run record](run.json)

## Checked statements

The declarations named below are in `GlobalTheory.EX.TypeIProduction`.

| Manuscript | Lean and scope |
| --- | --- |
| [§2. Integral Frobenius separation](../manuscript/paper_github.md#separation) | `servedWord_fromNativeAdjacentCapacity` builds the primitive row and obtains a unit on the actual compared numerator through `F6SeedBridge`. It uses the literal first-span argument and the native local denominator. [Fixed-fibre assembly](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/TypeINativeQuotient.lean#L17) |
| [§3. Local excess and same-place order](../manuscript/paper_github.md#same-place-order) | `TypeIAtOriginalWordWithRow` gives the row-induced first-layer surjection, noncontainment and finite length at least $e_wT\operatorname{rank}_{O_w}(A_w)+e_w$. It gives the comparison formula on representatives and both exact orders for the same class. [Endpoint type](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/TypeIIndexedTargets.lean#L66) |
| [§4. Prime selection and depth](../manuscript/paper_github.md#selection) | `family_typeI_prime_pair`, `family_typeI_depth_at_pair` and `native_adjacent_capacity_of_depth` supply the selected prime, adjacent top pair and depth inequalities used by the indexed proof. [Prime selector](../lean/src/Formalism/SharpRestriction/GrowthBounds/TypeIPrimeSelection.lean#L1463) · [Depth proof](../lean/src/Formalism/SharpRestriction/GrowthBounds/TypeIFiniteDepth.lean#L1450) |
| [Theorem A](../manuscript/paper_github.md#main-result) | `indexed_typeI_same_place_with_row` and `indexed_typeI_same_place` fix the member and word before selecting the prime and place. They use the original `FamP` inputs and `F.ex` comparison. [Indexed theorem](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/TypeIIndexedTargets.lean#L122) |
| [Production corollary](../manuscript/paper_github.md#main-result) | `production_window_with_typeI_row` calls the proved indexed theorem on the word supplied by `FamCore.exists_pt` and the source `u₀`. `production_typeI_inhabited_member` also constructs the original hypothesis bundle and distinguished host, and returns an inhabited member and word above any prescribed real lower bound. [Production caller](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/TypeIProductionCaller.lean#L33) · [Inhabited member](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/TypeIProductionCaller.lean#L111) |

Two translations connect the literal Lean endpoints to the paper. First, the Lean result records $Z<p<2Z$, where $Z=(X')^{3/4}$. The checked `family_typeI_window_scales` gives $2Z<X'$ eventually, so one can take the larger family threshold in Theorem A and in the production window. Second, Lean returns the local order in $A_w/U_w$ with the native `NP` comap. The injection into the ambient served quotient $Q_w=M_w/\mathrm{NP}_w$ in §1 preserves exact additive order. [Scale lemma](../lean/src/Formalism/SharpRestriction/GrowthBounds/TypeIPrimeSelection.lean#L890) · [Ambient quotient in §1](../manuscript/paper_github.md#main-result)

## Evidence and scope

The native build and integrated audit both exited zero. The audit prints the five public endpoint types and their supporting definitions, and reports the transitive axiom sets of eleven declarations. Each set contains only `propext`, `Classical.choice` and `Quot.sound`. The proof overlay, audit input and recorded output are published with this version. [Audit input](../lean/TypeIIntegratedAudit.lean) · [Audit output](integrated-types-and-axioms.txt)

Earlier runs completed all six export replays for seven fixed-place modules. The fixed-place assembly export with its chart-unit interface supplied also has six passing replays. The integrated solution export was stopped before completion. The six integrated replays and independent comparison were cancelled before execution. The independent reference compiled and exported. [Earlier fixed-place progress](https://github.com/leanprover-community/riemann-hypothesis/issues/77#issuecomment-7167482262) · [Integrated run record](run.json)

## Reproduction

The checked environment used Lean `leanprover/lean4:v4.37.0-rc1` at `0b77e12952ad39077d80d8bd6b66d601f225c321`, upstream `9282d3a102c4aff0e6026746db2a8990f5d9cddd` and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. Use the upstream `lean-toolchain` and Lake manifest at that revision. The overlay supplies new files and leaves the pinned upstream files in place. [Upstream toolchain](https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/lean-toolchain) · [Lake manifest](https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/lake-manifest.json)

From the root of this repository, verify the overlay and point `overlay` at it. Then build in a separate pinned checkout in an isolated Linux environment with the matching Lean dependencies and no credentials visible to the Lean process. A fresh build can require a substantial upstream dependency build.

```sh
overlay="$PWD/papers/type-i-torsion/lean"
(cd "$overlay" && shasum -a 256 -c SHA256SUMS)

git clone https://github.com/leanprover-community/riemann-hypothesis.git
cd riemann-hypothesis
git checkout --detach 9282d3a102c4aff0e6026746db2a8990f5d9cddd
cp -R "$overlay/src/." src/
cp "$overlay/TypeIIntegratedAudit.lean" .

lake --no-cache build \
  +Formalism.SharpRestriction.GrowthBounds.TypeIFiniteDepth:olean \
  +Formalism.SharpRestriction.GrowthBounds.TypeIPrimeSelection:olean \
  +Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.TypeINativeQuotient:olean \
  +Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.TypeIIndexedTargets:olean \
  +Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.TypeIProductionCaller:olean
lake env lean TypeIIntegratedAudit.lean
```
