# RH-public

## Extra Type I torsion via integral Frobenius separation

Under the original production hypotheses in Alpöge’s construction, the paper argument gives a class of exact additive order $p^{T+1}$ in the original word quotient. Its image in the full served quotient at the selected place has the same exact order. The same coefficient row gives an extra local layer of length at least $v_{O_w}(p)$ beyond the scalar contribution.

This is a research draft about the Type I lattice quotient. The witness is supplied by an existence argument. The fixed-place Lean results have passed their scoped checks. End-to-end formal verification of prime selection, the depth bounds and the inhabited production corollary is in progress. [Discussion and public progress update on #77](https://github.com/leanprover-community/riemann-hypothesis/issues/77#issuecomment-7167482262)

## Start here

- **Read the manuscript.** [PDF](papers/type-i-torsion/manuscript/paper.pdf) · [GitHub reading copy](papers/type-i-torsion/manuscript/paper_github.md)
- **Find the exact result.** [Source quotients and Theorem A](papers/type-i-torsion/manuscript/paper_github.md#main-result) · [Arithmetic selection and production corollary](papers/type-i-torsion/manuscript/paper_github.md#selection)
- **Follow the proof.** [Integral separating row](papers/type-i-torsion/manuscript/paper_github.md#separation) · [Local excess and preservation of order](papers/type-i-torsion/manuscript/paper_github.md#same-place-order)
- **Inspect formal coverage.** [Lean evidence and theorem crosswalk](papers/type-i-torsion/verification/LEAN.md)
- **Work from the editable manuscript.** [Pandoc Markdown source](papers/type-i-torsion/manuscript/paper.md)

The PDF is the fixed reading version. The GitHub copy is generated for on-site reading. The Pandoc source is the editable publication authority.

## Rebuild the reading copies

Run `make` from the repository root with Python 3, Pandoc and Tectonic installed. It generates `paper_github.md` and `paper.pdf` from `paper.md`. The GitHub copy records its source digest and exact generation command. Run `make check-reading` to compare a fresh reading copy with the committed one. Use the toolchain and source pins in the verification note when inspecting Lean coverage. [Lean evidence](papers/type-i-torsion/verification/LEAN.md)

Chey Loveday, *Extra Type I torsion via integral Frobenius separation*, research draft, 25 November 2026.
