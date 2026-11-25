# Extra Type I torsion via integral Frobenius separation

**Chey Loveday · 25 November 2026 · Research draft v0.1.1 with proof clarifications**

Under the original family hypotheses in Alpöge’s construction, a single class has exact additive order $p^{T+1}$ in the original word quotient and retains that exact order at the selected served place $w\mid p$. Here $T$ is the cutoff for that fibre. At the same place, the ramified local quotient has at least $v_{O_w}(p)$ more length than the scalar contribution. The production corollary supplies a member and word beyond any prescribed lower bound. The witness is existential.

The indexed theorem and the inhabited production caller passed the **Lean 4.37.0-rc1 kernel build and transitive axiom audit**. The six independent replays of the integrated proof and the reference comparison have **not run**. The completed six-checker replay covers the fixed-place quotient core. [Verification status](papers/type-i-torsion/verification/MODAL.md#integrated-production-proof) · [Original discussion on #77](https://github.com/leanprover-community/riemann-hypothesis/issues/77)

## Start here

- **Read the manuscript.** [PDF](papers/type-i-torsion/manuscript/paper.pdf) · [GitHub reading copy](papers/type-i-torsion/manuscript/paper_github.md)
- **Check the theorem and quotients.** [Theorem A, local excess and production corollary](papers/type-i-torsion/manuscript/paper_github.md#main-result)
- **Understand why it works.** [Illustrated guide (download HTML)](papers/type-i-torsion/reading/EXPLAINED_ILLUSTRATED.html) · [GitHub reader guide](papers/type-i-torsion/reading/EXPLAINED.md) · [Lamport Plus proof map](papers/type-i-torsion/reading/PROOF_MAP.md#dependency-map) · [Reader pilot](papers/type-i-torsion/reading/EXPLAINED.md#reconstruct-the-proof)
- **Inspect the formal result.** [Indexed theorem](papers/type-i-torsion/lean/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/TypeIIndexedTargets.lean#L122) · [Production caller](papers/type-i-torsion/lean/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/TypeIProductionCaller.lean#L111) · [Verification and reproduction](papers/type-i-torsion/verification/LEAN.md) · [Completed Modal checks](papers/type-i-torsion/verification/MODAL.md)

## How the proof works

The arithmetic selection fixes a word before choosing a prime, a served place and two adjacent top slots. The Frobenius relation between the slots produces a coefficient row that reads a unit on a ramified seed and sends the literal first span of `NP` into $p^{T+1}O_w$. The quotient comparison uses that same seed, word and place. Its local survival test, together with the global annihilator, gives the two exact orders for one class.

## Sources and reproduction

| Location | Contents |
| --- | --- |
| [Manuscript source](papers/type-i-torsion/manuscript/paper.md) | Editable Pandoc Markdown. The PDF and GitHub reading copy are generated from this source. |
| [Explanation source](papers/type-i-torsion/reading/EXPLAINED.md) | The editable reader guide. The standalone HTML adds the proof diagram and highlighted worked example. Use GitHub’s raw download button and open the file locally. |
| [Lean source overlay](papers/type-i-torsion/lean) | The 38-file source overlay from the checked run at its original relative paths, the audit input and the source checksums. |
| [Verification record](papers/type-i-torsion/verification/LEAN.md) | Exact declarations and scope, pinned environment, build and axiom results, and reproduction commands. |

Run `make` with Python 3, Pandoc and Tectonic to regenerate the reading copies. Run `make check-reading` for the GitHub manuscript and `make check-guide` for the illustrated HTML to compare each with fresh generation. The Lean instructions use a separate checkout of the pinned upstream dependency. [Reproduction](papers/type-i-torsion/verification/LEAN.md#reproduction)

The maintained illustrated guide links to `main`. For a release, generate and verify a separate copy from the release checkout. Set `revision` to the full commit SHA served by GitHub for that edition, and set `output` to a separate file path.

```sh
python3 scripts/illustrated_guide.py --revision "$revision" --output "$output"
python3 scripts/illustrated_guide.py --revision "$revision" --output "$output" --check
```

## Version history and citation

Version 0.1.1 publishes the checked Lean sources and integrated audit. The current manuscript spells out the family parameters and joint witnesses. Its proof uses the constant shear from Lean for the output unit and clarifies the nonempty-orbit condition, the extraction of the ramified seed and the short-order exclusion. [Tagged v0.1.1 edition](https://github.com/CheyLoveday/RH-public/releases/tag/v0.1.1) · [Previous research draft](https://github.com/CheyLoveday/RH-public/releases/tag/v0.1.0)

Chey Loveday. *Extra Type I torsion via integral Frobenius separation*. GitHub research draft v0.1.1, 25 November 2026.
