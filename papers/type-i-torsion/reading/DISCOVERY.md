# How to discover the Type I separating row

Use this companion to work out why the proof asks for a particular certificate and where a plausible shortcut fails. The finished argument is in the [proof map](PROOF_MAP.md#dependency-map).

## Work backward from the target

Read down to find the obligations. Read back up to assemble the proof once each obligation has been supplied.

| Start with | Ask for | What meets the request |
| --- | --- | --- |
| One class of order $p^{T+1}$ globally and at $w$ | A global killing power $p^{T+1}$ and local survival at $p^T$ for that class | First find a seed surviving at $p^T$ with a later local killing power. Use the first crossing and a prime-avoiding multiplier to turn the seed into the desired class. [LP6](PROOF_MAP.md#lp6) |
| Survival of the same seed | $p^Ta_w\notin P_w$ for a compared ramified numerator $a_w$ | Seek an integral row with $\lambda(a_w)$ a unit and $\lambda(P_w)\subseteq p^{T+1}O_w$. Modulo $p^{T+1}$ the row distinguishes $p^Ta_w$ from the denominator. [LP5](PROOF_MAP.md#lp5) |
| Divisibility on the whole first span | One argument for a retained orbit and one for an omitted orbit | Read the retained neighbour by a contraction and charge the omitted orbit to the source scalar depth. [LP5.1](PROOF_MAP.md#lp5-1) |
| A contraction that distinguishes input from output | An identity on every incoming flag and a unit on one allowed output flag | Start from $V^{\mathsf T}U=0$ modulo $p$. Frobenius carries the constant frames to the next slot. Use $p$ copies of the same flag to realize it in the labelled coordinates. Break the orthogonality at the standard output by the line shear. [LP3.4](PROOF_MAP.md#lp3-4) · [LP3.5](PROOF_MAP.md#lp3-5) |
| Enough copies and scalar depth on one fibre | $pR\le m_s$, $R\le m_{s^+}$ and $R\le\lceil\mathrm{Sv}(v)\rceil$ for $R=T+1$ | Search for a long inert step connecting two top positions. Pair weights count such opportunities before good-orbit and level exclusions. The depth proof compares the full cutoff with both signed weights and the first excluded odd visit. [LP1](PROOF_MAP.md#lp1) · [LP2](PROOF_MAP.md#lp2) |

Two forward observations close gaps in this route. The actual divided words give coefficient vectors in the column space of the rational matrix, where the Gram pairing turns the labelled weight into a well-defined row. The native Weyl generators then give integrality. At the chosen chart, the evaluations of actual global ramified forms span the local Weyl lattice. Since the nonunits form an ideal, this span is enough to move a local unit into an actual global numerator. [Gram and integrality](PROOF_MAP.md#lp3-2) · [Global seed](PROOF_MAP.md#lp4-4)

## Compare two proof choices

- **Recover a labelled pairing from polynomial coefficients.** The paper picks independent coefficient columns and inverts their rational Gram matrix to recover the entire vector in the column space. The Lean proof instead solves the Gram equation for the particular labelled weight and recovers only its pairing. Both need the restriction to coefficient vectors that actually come from words or linear combinations of them. [Paper §2](../manuscript/paper_github.md#separation) · [LP3.2](PROOF_MAP.md#lp3-2)
- **Find a class with exact order.** The paper chooses the least local killing exponent $j$. Starting the test at the surviving exponent $T$ puts that same crossing at $k+1=j-T$. The prime-avoiding multiplier there gives $[cp^kb]$. An arbitrary global element of order $p^{T+1}$ need not retain that order under comparison. [LP6](PROOF_MAP.md#lp6)

## Test the tempting shortcuts

| Tempting implication | Small counterexample | Premise the proof uses |
| --- | --- | --- |
| Divisibility of the denominator alone gives an extra layer. | Take $O=\mathbb Z_{(3)}$, $A=O$, $T=2$, $U=9O$ and $\lambda(x)=3x$. Then $\lambda(U)\subseteq27O$, while $9A/U=0$. | A unit on an actual numerator. [LP4.4](PROOF_MAP.md#lp4-4) |
| Bounding retained-orbit terms suffices. | In the same ring at $T=2$, take retained generator $27$ and omitted generator $9$. Their span is $9O$, so there is no extra layer. | The omitted scalar needs its own power bound. [LP2.3](PROOF_MAP.md#lp2-3) |
| A spanning image contains every primitive local vector. | The image $\mathbb Z\subset\mathbb Z_{(3)}$ spans because it contains $1$. The unit $1/2$ has no preimage in $\mathbb Z$. | Use the maximal ideal to extract a unit on some generator of the span. [LP4.4](PROOF_MAP.md#lp4-4) |
| A labelled weight descends on arbitrary label vectors. | With $Q_1=Q_2=X$, the vector $(1,-1)$ represents zero, but pairing with $(1,0)$ gives $1$. | Restrict to the column space of the coefficient matrix and prove the Gram identity there. [LP3.2](PROOF_MAP.md#lp3-2) |
| Independent annihilating covectors can replace the repeated copies. | Over $\mathbb F_3$, $(1,-1,0)$ and $(1,0,-1)$ both annihilate $(1,1,1)$. The coordinatewise product of the first, second and first again is $(1,0,0)$, which pairs to $1$. | Within each group take $p$ copies of a single generic flag. [LP3.4](PROOF_MAP.md#lp3-4) |

### Replay the model checks

This Python 3 command checks the examples above and the matched unit-row model with denominator $27O$. It uses exact integers and fractions. The checks concern the displayed models.

~~~sh
python3 - <<'PY'
from fractions import Fraction
from math import gcd, prod

p, T = 3, 2
scalar, next_layer = p**T, p**(T + 1)

# The nonprimitive row passes the denominator test and fails the seed test.
assert (p * scalar) % next_layer == 0
assert (p * scalar) % next_layer == (p * next_layer) % next_layer
assert {scalar * x % scalar for x in range(p)} == {0}

# The same scalar multiples survive using a unit row and denominator 27O.
assert {scalar * x % next_layer for x in range(p)} == {0, 9, 18}

# An omitted generator changes the actual denominator.
assert gcd(next_layer, scalar) == scalar

# The local unit 1/2 lies outside the global image Z.
half = Fraction(1, 2)
assert gcd(half.numerator, p) == gcd(half.denominator, p) == 1
assert half.denominator != 1

# A relation in the full label space, and a compatible vector in the span.
assert sum((1, -1)) == 0 and (1, -1)[0] == 1
assert Fraction(1, 2) * sum((3, 3)) == 3

# Each covector annihilates the line. Repetition and mixing differ.
v, w = (1, -1, 0), (1, 0, -1)
assert sum(v) % p == sum(w) % p == sum(x**p for x in v) % p == 0
assert sum(prod(coordinates) for coordinates in zip(v, w, v)) % p == 1
print("Type I model controls passed")
PY
~~~

## Transfer exercise answer

Let $\lambda_1,\lambda_2$ be the rows in the [exercise](EXPLAINED.md#reconstruct-the-proof). Their readout matrix on the two supplied vectors is invertible over $O$, so the joint row maps $A$ onto $O^2$. Restrict to $p^TA$ and reduce both coordinates modulo $p^{T+1}$. The hypothesis on $U$ gives the surjection

$$
p^TA/U\twoheadrightarrow (p^TO/p^{T+1}O)^2 .
$$

This target has length $2e$. The quotient $A/p^TA$ has length $erT$, so $\ell_O(A/U)\ge erT+2e$, allowing infinite length. A containment $p^BA\subseteq U$ for some $B\ge T$ gives finite length. For example, the two row hypotheses allow $U=0$, even when the readout matrix is the identity. [One-row exact sequence](PROOF_MAP.md#lp5-3)
