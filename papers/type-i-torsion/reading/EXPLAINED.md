# Why one extra power of $p$ survives

The Type I estimate in Alpöge’s construction leaves room for extra torsion. The paper shows that the arithmetic actually uses some of that room. For each sufficiently large member of an original family and each word in that member, it selects a prime $p$ and a place $w$ above it. One class in the original word quotient has exact additive order $p^{T+1}$, and its image at $w$ has that same order. Here $T$ is the cutoff for the chosen fibre. The production corollary supplies a member and word beyond any prescribed bound. [Exact statement and hypotheses](../manuscript/paper_github.md#main-result)

## Glossary

- **Word.** A piece of the source indexing data that determines the global lattice quotient being studied. The proof fixes it before choosing a prime.
- **Served place.** A place $w$ above $p$ where the source supplies the comparison for that word.
- **Lattice.** A module of integral vectors inside a vector space over a fraction field. The local lattices here use the coefficient ring $O_w$.
- **Torsion.** A class annihilated by some positive integer. Its additive order is the least positive integer that annihilates it.
- **Frobenius.** In the calculation modulo $p$, the map raising coordinates to their $p$th powers. It relates the constant frames of consecutive slots.
- **Cutoff.** The exponent $T$ that determines the scalar layer $p^TA_w$ in the local denominator. The proof detects survival inside this layer.

## The idea

A quotient forgets whatever lies in its denominator. To prove that a vector survives, find a measurement that vanishes on the denominator but takes a nonzero value on the vector. Here the measurement is an integral linear functional, called a **row**, used modulo $p^{T+1}$. It takes a unit value on the image of a ramified form. Multiplying that form by $p^T$ gives a reading of $p^T$ times a unit, which is still nonzero modulo $p^{T+1}$.

The hard part is making this measurement on the **same word and place** where the source comparison and denominator are defined. The final step needs a global killing power as well as local survival. These are two different pieces of the proof.

## Follow one word and place

The member $(x,i)$ and word $u$ are fixed first. Once the proof chooses $p$ and a supported place $w\mid p$ for that word, every local calculation uses that same $w$.

1. **Select the fibre.** Fix $u$. Choose $p,w$ and an adjacent pair of top slots on a rank-one orbit at $w$. [Selection](PROOF_MAP.md#lp1) · [Depth](PROOF_MAP.md#lp2)
2. **Join the row and the seed.** On this word, construct a ramified seed $b\in A_u$. Its compared numerator $a_w=c_w(b)$ is in $A_w$. The row $\lambda$ at this place reads a unit on $a_w$. [Row](PROOF_MAP.md#lp3) · [Seed](PROOF_MAP.md#lp4)
3. **Read the extra layer.** At the same place the row sends the actual denominator $U_w$ into $p^{T+1}O_w$. The reading of $p^Ta_w$ is $p^T$ times a unit and survives modulo $p^{T+1}$. [Literal denominator](PROOF_MAP.md#lp5)
4. **Follow one class.** The served comparison uses this same word and place to produce one class $z$ killed by $p^{T+1}$ globally. Its $p^T$ multiple survives at $w$. Its order and its image’s order are both $p^{T+1}$. [Exact order](PROOF_MAP.md#lp6)

## What one extra layer means

**Worked model.** Take $p=3$, $T=2$, $O=\mathbb Z_{(3)}$, $A=O$, and $U=27O$. Use the identity as the row. It reads $1$ on the seed $a=1$ and takes $U$ into $27O$. This model illustrates the local quotient step. The paper supplies its production fibre by a separate existence argument.

| Multiply the seed by | $1$ | $3$ | $9$ | $27$ |
| --- | --- | --- | --- | --- |
| In the scalar quotient $A/9A$ | $1$ | $3$ | $0$ | $0$ |
| In the actual quotient $A/U$ | $1$ | $3$ | **$9$** | $0$ |

The extra layer is the kernel of the projection from the actual quotient to the scalar quotient.

$$
0\longrightarrow 9O/27O\longrightarrow O/27O\longrightarrow O/9O\longrightarrow 0 .
$$

The extra layer has the three classes $[0],[9],[18]$ and length one over $O$. Its generator $[9]$ has additive order $3$, while the seed class $[1]$ in the actual quotient has additive order $27$. The scalar quotient has length two, and the actual quotient has length three.

In the paper, the lattice $A_w$ can have higher rank. The row gives a **surjection from the extra layer** $p^TA_w/U_w$ onto $p^TO_w/p^{T+1}O_w$. The target has length $e_w=v_{O_w}(p)$, which gives a lower bound on the extra length. The global order uses the separate served comparison argument shown in the last step of the diagram. [Local length](PROOF_MAP.md#lp5) · [Global order](PROOF_MAP.md#lp6)

## Travel through the proof

| Question | Answer | Details |
| --- | --- | --- |
| Where does the place come from? | Fix the word first. Count pairs of top positions whose difference is the Frobenius step of an eligible prime. The family size bound $n\ge x^2$ makes the number of short-order steps small compared with the number of top positions. The pair count survives this and the other source exclusions. The selected prime gives a supported place for the word. | [Select the fibre](PROOF_MAP.md#lp1) |
| Why does the row see a difference? | At two adjacent slots, Frobenius relates the coefficients of a line and a complementary hyperplane. For every incoming neighbour the relevant contraction contains a factor $p$. At a chosen output vector, the same contraction reads a unit. Enough labelled factors let the proof repeat the contraction $T+1$ times. | [Depth](PROOF_MAP.md#lp2) · [Integral Frobenius row](PROOF_MAP.md#lp3) |
| How does the unit get into the ramified lattice? | Restrict to one adelic class inside the original integral word lattice. Apply one sign difference in each tame coordinate. Full norms cancel, and freeness moves every nonempty sign term off the chosen class. The readout at that class survives intact. The resulting global forms span the local chart values over the coefficient ring, so a row that takes a unit value there must read a unit on at least one actual global ramified form. | [Ramified seed](PROOF_MAP.md#lp4) |
| Why does this test every term of the denominator? | A term retaining the selected orbit contains its neighbour operator. A term omitting it already contains a high enough scalar power. The row sees a multiple of $p^{T+1}$ in either case. | [Denominator and length](PROOF_MAP.md#lp5) |
| Why do both orders equal the same power? | Find the first power that kills the seed at this place. The selected orbit makes the orbit set nonempty, so the served equivalence applies. It gives a multiplier outside the prime of that same place that makes this power zero globally. If that multiplier also made the previous power zero locally, the comparison would give a second multiplier outside the same prime. Their product would contradict the choice of first power. | [Transport exact order](PROOF_MAP.md#lp6) |
| Does the family actually supply a word? | The original design and host construction gives the family. Its inhabited window supplies a member above the proof threshold and the source supplies a distinguished word there. | [Apply the production construction](PROOF_MAP.md#lp7) |

## How to find the separating row

**Work back from the first missing layer.** If the scalar cutoff is $T$, a row that reads a unit on a numerator $a_w$ will read a nonzero value on $p^Ta_w$ modulo $p^{T+1}$. The literal denominator is indexed by subsets of orbits. Choose one orbit and ask for two bounds. A term omitting it needs $T+1$ powers of $p$ from its scalar, while a term retaining it needs those powers from the row on its neighbour operator. This gives the prime search a target. Look among eligible steps for a pair of top positions with enough factors and enough omission depth. Counting pairs in the fixed member measures this directly. The production window supplies a member and word to which that search applies. [Selection and depth](PROOF_MAP.md#lp1) · [Denominator](PROOF_MAP.md#lp5) · [Production](PROOF_MAP.md#lp7)

**Turn the edge relation into a coefficient.** Modulo $p$, the normalized incoming line and hyperplane are orthogonal at each slot. Across the next slot the constant frames have been raised to the $p$th power. Contracting the $p$th powers of the first vector's coordinates with the second vector restores the orthogonality identity even when the two flags vary independently. To realize the powers in the labelled coefficients, take $p$ copies of the same flag within the first slot. Each disjoint contraction supplies one power of $p$. To see how the row can read a unit on the output, keep the standard hyperplane and shear the line from $e_1$ to $e_1+e_k$. The last dual coordinate then reads $1$. [Frobenius contraction and output unit](PROOF_MAP.md#lp3)

**Move the test to a word class.** To get a unit on an actual global form, it suffices that the compared ramified numerators span the chart lattice. If every such numerator read into the maximal ideal, the entire span would read there. The integral masking and sign differences supply this spanning family. Once the row gives local survival and the denominator gives eventual vanishing, look for the first crossing between them. The multiplier supplied there clears the global denominator, and the preceding local power can only vanish if a second multiplier contradicts minimality. [Ramified seed](PROOF_MAP.md#lp4) · [Exact order](PROOF_MAP.md#lp6)

[Backward argument and counterexamples](DISCOVERY.md)

## Reconstruct the proof

For the Lamport Plus reader pilot, start with the exact statement and the seven steps in the proof map, with its detailed blocks closed. Answer the questions, then use the guide and open the detailed blocks to check your reconstruction. Record the hypothesis that rules out each failure. Try the transfer exercise before opening its answer. [Exact statement](../manuscript/paper_github.md#main-result) · [Proof map](PROOF_MAP.md#dependency-map) · [Assessment procedure](../verification/READER_ASSESSMENT.md)

1. Starting from a unit reading, explain why the row detects survival at $p^T$ even if $T>0$ and reducing the reading directly modulo $p$ gives zero.
2. Explain why the denominator proof needs both the retained-orbit and omitted-orbit cases. Which case still needs a calculation if the omitted-orbit scalar is too small?
3. Explain where the same served prime enters the argument that clearing the global denominator preserves local survival. What fails if the multiplier can belong to that prime?
4. Locate the step that rules out a vacuous family statement with no sufficiently large member.
5. Explain why the two slots may have independent flag variables but the $p$ copies in a contraction cannot be replaced by independent flags in the first slot.
6. Explain how a unit readout on the local lattice implies a unit readout on an actual ramified numerator. What property of the maximal ideal does the argument use?

**Transfer exercise.** Let $O$ be a discrete valuation ring in which $p$ has valuation $e>0$. Let $A$ be free of rank $r$ over $O$ and $U\subseteq p^TA$. Suppose two rows on $A$ take $U$ into $p^{T+1}O$ and their readouts on two vectors of $A$ form a matrix with unit determinant. Work out a lower bound on the length of $A/U$ and identify which part comes from the two rows. Explain which further premise would give finiteness if you are only given these two rows. This is a model question about the method. The paper constructs one row on the selected fibre.

[Transfer exercise answer](DISCOVERY.md#transfer-exercise-answer) · [Detailed proof map](PROOF_MAP.md) · [Lean crosswalk](../verification/LEAN.md) · [Completed Modal checks](../verification/MODAL.md)
