# Why one extra power of $p$ survives

The Type I estimate in Alpöge’s construction leaves room for extra torsion. The paper shows that the arithmetic actually uses some of that room. For each sufficiently large member of an original family and each word in that member, it selects a prime $p$ and a place $w$ above it. One class in the original word quotient has exact additive order $p^{T+1}$, and its image at $w$ has that same order. Here $T$ is the cutoff for the chosen fibre. The production corollary supplies a member and word beyond any prescribed bound. [Exact statement and hypotheses](../manuscript/paper_github.md#main-result)

## The idea

A quotient forgets whatever lies in its denominator. To prove that a vector survives, find a measurement that vanishes on the denominator but takes a nonzero value on the vector. Here the measurement is an integral linear functional, called a **row**, used modulo $p^{T+1}$. It takes a unit value on the image of a ramified form. Multiplying that form by $p^T$ gives a reading of $p^T$ times a unit, which is still nonzero modulo $p^{T+1}$.

The hard part is making this measurement on the **same word and place** where the source comparison and denominator are defined. The final step needs a global killing power as well as local survival. These are two different pieces of the proof.

## Travel through the proof

| Question | Answer | Details |
| --- | --- | --- |
| Where does the place come from? | Fix the word first. Count pairs of top positions whose difference is the Frobenius step of an eligible prime. The lower bound for these pairs survives the source exclusions. The selected prime gives a supported place for the word. | [Select the fibre](PROOF_MAP.md#lp1) |
| Why does the row see a difference? | At two adjacent slots, Frobenius relates the coefficients of a line and a complementary hyperplane. For every incoming neighbour the relevant contraction contains a factor $p$. At a chosen output vector, the same contraction reads a unit. Enough labelled factors let the proof repeat the contraction $T+1$ times. | [Depth](PROOF_MAP.md#lp2) · [Integral Frobenius row](PROOF_MAP.md#lp3) |
| How does the unit get into the ramified lattice? | Restrict to one adelic class inside the original integral word lattice. Apply one sign difference in each tame coordinate. Full norms cancel, and freeness moves every nonempty sign term off the chosen class. The readout at that class survives intact. | [Ramified seed](PROOF_MAP.md#lp4) |
| Why does this test every term of the denominator? | A term retaining the selected orbit contains its neighbour operator. A term omitting it already contains a high enough scalar power. The row sees a multiple of $p^{T+1}$ in either case. | [Denominator and length](PROOF_MAP.md#lp5) |
| Why do both orders equal the same power? | Find the first power that kills the seed at this place. The served comparison gives a multiplier outside the prime of that same place that makes this power zero globally. If that multiplier also made the previous power zero locally, the comparison would give a second multiplier outside the same prime. Their product would contradict the choice of first power. | [Transport exact order](PROOF_MAP.md#lp6) |
| Does the family actually supply a word? | The original design and host construction gives the family. Its inhabited window supplies a member above the proof threshold and the source supplies a distinguished word there. | [Apply the production construction](PROOF_MAP.md#lp7) |

## What one extra layer means

For a model calculation, take the ring $O=\mathbb Z_{(p)}$ and the lattice $A=O$. The scalar quotient $A/p^TA$ has length $T$. If the actual denominator is $U=p^{T+1}A$, there is one further layer $p^TA/U$. It has length one and the image of $1$ in $A/U$ has order $p^{T+1}$.

In the paper, $A_w$ can have higher rank. The row gives a **surjection from the extra layer** $p^TA_w/U_w$ onto $p^TO_w/p^{T+1}O_w$. This proves a lower bound on the size of the layer without describing its entire structure. Over a local ring where the rational prime $p$ has valuation $e_w$, the target has length $e_w$. The global word quotient and its comparison require the separate argument in the last two rows of the proof route. [Precise local length argument](PROOF_MAP.md#lp5)

## Reconstruct the proof

Try these before opening the detailed steps.

1. Starting from a unit reading, explain why the row detects survival at $p^T$ even if $T>0$ and reducing the reading directly modulo $p$ gives zero.
2. Explain why the denominator proof needs both the retained-orbit and omitted-orbit cases. Which case still needs a calculation if the omitted-orbit scalar is too small?
3. Explain where the same served prime enters the argument that clearing the global denominator preserves local survival. What fails if the multiplier can belong to that prime?
4. Locate the step that rules out a vacuous family statement with no sufficiently large member.

**Transfer exercise.** Let $O$ be a discrete valuation ring in which $p$ has valuation $e>0$. Let $A$ be free of rank $r$ over $O$ and $U\subseteq p^TA$. Suppose two rows on $A$ take $U$ into $p^{T+1}O$ and their readouts on two vectors of $A$ form a matrix with unit determinant. Work out a lower bound on the length of $A/U$ and identify which part comes from the two rows. Explain which further premise would give finiteness if you are only given these two rows. This is a model question about the method. The paper constructs one row on the selected fibre.

[Detailed Lamport Plus proof map](PROOF_MAP.md) · [Lean crosswalk](../verification/LEAN.md) · [Completed Modal checks](../verification/MODAL.md)
