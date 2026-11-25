# Extra Type I torsion via integral Frobenius separation

Chey Loveday · 25 November 2026 · Research draft

> Generated GitHub reading copy. Edit the [Pandoc source](paper.md).
> Source: `papers/type-i-torsion/manuscript/paper.md`. SHA-256: `3cadfd65aaa3c12e432e8239ee045c548c3a937e5e44af78e0baaa3d9d836ba7`.
> Generate from the repository root with `python3 scripts/github_reading.py`.

<a name="abstract"></a>

## Abstract

We study the extra-torsion question for the Type I lattice quotient in Alpöge’s construction. Under the original production hypotheses, the paper argument selects an eligible prime and a served place after the family member and word have been fixed. It constructs one class of exact additive order $`p^{T+1}`$ in the original word quotient whose image has that same order at the selected place, where $`T`$ is the source cutoff. A coefficient functional built from two adjacent Frobenius slots reads a unit on a ramified seed and separates it from the literal denominator. It also detects a full extra local layer. Lean verification covers the fixed-place argument. Formal verification of the arithmetic selection and inhabited production application is in progress.

<a name="main-result"></a>

## 1. The source quotients and the main result

Issue [#77][issue] asks whether the length of the Type I local quotient can exceed the scalar contribution determined by its cutoff. The question belongs to the lattice arithmetic used by Alpöge’s construction. We work with upstream revision `9282d3a1` throughout.

Fix a source member $`D,L`$ and a word $`u`$ of $`D`$. Write $`A_u=\mathrm{DV.MramL}(D,u)`$ and $`N_u=L.\mathrm{NuLat}(u)`$ in the original word space. Let $`\iota_u`$ denote the inclusion from $`A_u`$. Define

$$
 C_u=A_u/\iota_u^{-1}(N_u).
$$

The inverse image is the native comap. In particular, an element of $`A_u`$ represents zero precisely when its ambient value belongs to $`N_u`$.

At a supported served place $`w\mid p`$, let $`O_w`$ be the coefficient discrete valuation ring, $`M_w`$ the integral model, and $`V_{\mathrm{ram},w}`$ the ramified subspace. Write $`A_w=M_w\cap V_{\mathrm{ram},w}`$, put $`T=(\lceil\tau_P\rceil).\mathrm{toNat}`$, and let $`P_w`$ be the literal first span in `NP`. The source defines

$$
 \mathrm{NP}_w=P_w\cap p^TM_w\cap V_{\mathrm{ram},w}.
$$

The ramified subspace is linear over the local fraction field. Division by the nonzero scalar $`p^T`$ therefore gives $`p^TM_w\cap V_{\mathrm{ram},w}=p^TA_w`$. The comap $`U_w`$ of $`\mathrm{NP}_w`$ to $`A_w`$ consequently identifies with $`P_w\cap p^TA_w`$. The inclusion of $`A_w`$ in $`M_w`$ induces an injection $`A_w/U_w\hookrightarrow Q_w`$, where $`Q_w=M_w/\mathrm{NP}_w`$. [Source denominator and length][np] · [Ramified span][served]

The given comparison on numerators, written $`c_w`$, takes $`A_u`$ into $`A_w`$. For any numerator $`b`$, the served equivalence identifies $`c_w(b)\in\mathrm{NP}_w`$ with the existence of an integral multiplier outside the prime of $`w`$ that sends $`b`$ into $`N_u`$. Taking the multiplier $`1`$ proves descent to an additive map $`C_u\to A_w/U_w`$. Write $`\overline{\mathrm{cmp}}_w:C_u\to Q_w`$ for its composite with the injection. The order of its image can equivalently be computed in $`A_w/U_w`$. [Source comparison and localization predicate][served]

**Theorem A (selected Type I torsion).** Let $`0<\varepsilon<1/52`$ and let $`F:\mathrm{FamP}(\varepsilon)`$ satisfy `ChosenE`, `ChosenWall`, `TuSize` and `GroupCompatibilityFamily`, using the comparison in `F.ex`. There exists $`x_0>F.x_1`$ such that for each $`x\in F.\mathrm{Win}`$ with $`x\ge x_0`$, each $`i:F.\mathrm{Ix}(x)`$ and each word $`u`$ of $`D=F.D(x,i)`$, the following holds. With $`L=F.L(x,i)`$ there is a prime $`p`$ satisfying `Cand`, $`p_0\le p<X'`$ and $`p\notin L.\mathrm{drop}`$. There is a supported served place $`w\mid p`$, off the word’s level prime, with the native `GIdx` data, and a selected rank-one orbit with two distinct adjacent top slots. On that same fibre there is a class $`z\in C_u`$ with

$$
 \mathrm{addOrderOf}(z)
 =\mathrm{addOrderOf}(\overline{\mathrm{cmp}}_w(z))
 =p^{T+1}.
$$

[Source Type I branch and original selection][typei] · [Family data][family]

**Proposition B (local excess).** On the witnesses in Theorem A there is an $`O_w`$-linear surjection

$$
 \frac{p^TA_w}{P_w\cap p^TA_w}\twoheadrightarrow\frac{p^TO_w}{p^{T+1}O_w}.
$$

Thus $`p^TA_w\nsubseteq P_w`$. The finite length of $`A_w/U_w`$ is at least $`e_wT\mathrm{rank}_{O_w}(A_w)+e_w`$, where $`e_w=v_{O_w}(p)>0`$.

**Production corollary.** Under the established inputs of the source design and host construction, there is an inhabited member beyond every prescribed lower bound, and a word for which Theorem A and Proposition B hold. The proof supplies the prime, place, adjacent slots, depth inequalities and separating row. The witness is selected existentially.

<a name="separation"></a>

## 2. Integral Frobenius separation

In this section fix the word, its served place and a selected orbit $`v`$ of rank one with cyclically adjacent top slots $`s,s^+`$. Put $`R=T+1`$. Let $`m_s,m_{s^+}`$ be the signed multiplicities at height one on an even slot and height $`k-1`$ on an odd slot. The arithmetic argument in Section 4 supplies $`pR\le m_s`$, $`R\le m_{s^+}`$ and $`R\le\lceil\mathrm{Sv}(v)\rceil`$. Fix the standard output tuple in the native model and its component under the group comparison. [Native signed weights][weights] · [Slot ties and period][slots]

**Ordered coefficient lifts.** Give each copy of an initial minor its own label, and let $`Q(X)`$ be the vector of products of these minors in the independent slot variables. Write $`Q(X)=\sum_\alpha q_\alpha X^\alpha`$ and $`\Phi(c)=c^{\mathsf T}Q(X)`$. The rational span of the integer vectors $`q_\alpha`$ admits a left inverse to $`\Phi`$: if $`C`$ has independent columns $`q_{\alpha_i}`$ spanning that space, recover $`c`$ by applying $`C(C^{\mathsf T}C)^{-1}`$ to the selected coefficients of $`\Phi(c)`$. This recovery is over the fraction field. Integrality will come from the source generators.

Cauchy–Binet identifies the action of matrix substitution on the labelled coordinates. For the source row letters $`T_i=I+t_iE_{a_i b_i}`$, the generator with divided degrees $`d_i`$ lifts to the coefficient of $`t_1^{d_1}\cdots t_\ell^{d_\ell}`$ in the ordered product expression $`Q(T_1\cdots T_\ell)`$, taken block by block. The transpose in the row substitution is the transpose in the Cauchy–Binet action on coefficients. The source frame identity gives the integral Weyl lattice as the integral span of these divided-word generators, with the specified determinant twists. The lifted coefficients are integral before applying any functional. [Native divided words][words] · [Frame lattice and determinant twist][frame]

**One functional for all incoming terms.** A rank-one predecessor has a basis $`gD_p`$ with $`D_p=\mathrm{diag}(p,1,\ldots,1)`$ over the unramified coefficient ring. In slot $`j`$ write $`g_j`$ for its Frobenius frame and $`E_p=\mathrm{diag}(1,p,\ldots,p)`$. The normalized height-one line and signed volume-dual hyperplane are represented by the matrices

$$
 U_j=g_j^{-\mathsf T}E_p,\qquad V_j=(\det g_j)^{-1}g_jD_p .
$$

The factor $`p^{\mathrm{ArV}(v)}`$ and the source determinant twist give one $`p`$ for each labelled inverse-transpose minor. Equivalently, $`p`$ times that minor equals a unit determinant factor times a signed complementary minor of $`g_jD_p`$. In particular,

$$
 V_j^{\mathsf T}U_j=p(\det g_j)^{-1}I .
$$

Here the next-slot matrices are entrywise $`p`$th powers modulo rational $`p`$, including at the cyclic wrap. Thus the contraction between the line at $`s`$ raised entrywise to its $`p`$th power and the hyperplane at $`s^+`$ vanishes modulo $`p`$. If $`s`$ is the hyperplane slot, the transposed contraction gives the same conclusion. [Native rank-one edge basis][edge] · [Frobenius congruence][frob]

Choose $`R`$ disjoint groups of $`p`$ labelled factors at $`s`$ and one at $`s^+`$. Contract each group diagonally and take the product on the labelled tensor coordinates. Within a group the $`p`$ repeated factors come from the same generic flag. This makes the reduction of their coordinate product the entrywise Frobenius power. The product of the $`R`$ contractions is divisible by $`p^R`$ on the normalized generic incoming polynomial. Ordered substitution and coefficient extraction preserve this divisibility. At the standard output use the standard flag in the even slot and a determinant-one signed permutation in the odd slot whose first $`k-1`$ columns span $`e_2,\ldots,e_k`$. The marked coordinates are $`e_1`$ and $`\pm e_1^*`$. Choose a unit coordinate on each unused factor. Native frame covariance supplies an integral output vector on which this same functional takes value $`\pm1`$. An overall sign gives value $`1`$. [Native frame covariance][frame]

**The ramified numerator and the literal span.** Use the original comparison on that same component and standard tuple. The chart evaluation identifies the integral coefficient values with restriction at one adelic class. Masking to that class preserves the integral word lattice. Applying all tame sign differences gives a ramified numerator $`b\in A_u`$. Every nonempty product of distinct coordinate signs moves the class by freeness, and its contribution on that class vanishes. Each full tame norm vanishes on the difference in its coordinate by reindexing the residue units. The other coordinates commute with that norm. Thus the seed has the same restriction as the supported input, so its chart value remains a unit. [Seed construction in #77][seed] · [Free action on classes][free]

The coefficient functional on model values defines a row $`\lambda:M_w\to O_w`$ by evaluation on the chosen chart. The normalized test applies to every predecessor of that chart in the actual neighbour sum, with its character and coefficient action. It yields $`\lambda(Y_vM_w)\subseteq p^RO_w`$. A generator of $`P_w`$ that retains the selected orbit contains at least one factor $`Y_v`$. Commutation and preservation of $`M_w`$ put this term in $`Y_vM_w`$. If it omits the selected orbit, the source scalar contains at least $`p^R`$. Taking the span gives

$$
 a_w=c_w(b)\in A_w,\qquad
 \lambda(a_w)\in O_w^\times,\qquad
 \lambda(P_w)\subseteq p^RO_w .
$$

[Original neighbour sum][sum] · [Integral preservation][preserve] · [Commuting operators][commute] · [Literal subset span][np]

<a name="same-place-order"></a>

## 3. The extra layer and exact order

**Local excess.** The row restricted to $`p^TA_w`$ descends to the quotient by $`U_w`$ and takes values in $`p^TO_w/p^{T+1}O_w`$. It is onto, since $`p^Ta_w`$ reads $`p^T`$ times a unit. This proves Proposition B’s surjection. The same unit readout puts $`p^Ta_w`$ outside $`P_w`$.

The kernel of $`A_w/U_w\to A_w/p^TA_w`$ is $`p^TA_w/U_w`$. Since $`A_w`$ is finite free over the DVR, $`A_w/p^TA_w`$ has length $`e_wT\mathrm{rank}_{O_w}(A_w)`$. The surjection contributes at least $`e_w`$ more, because multiplication by $`p^T`$ identifies the target with $`O_w/pO_w`$. The empty subset in the literal span gives a sufficiently large power of $`p`$ that annihilates the ramified quotient, giving finite length.

**Preserving the order at $`w`$.** Write $`B`$ for the larger of $`T`$ and the sum of the rounded omission weights. The empty retained subset puts $`p^B a_w`$ in $`\mathrm{NP}_w`$. Let $`j`$ be the least exponent with $`p^j a_w\in\mathrm{NP}_w`$. The unit row and its divisibility on the denominator give $`j\ge R`$. The served equivalence gives an integral scalar $`c`$ outside the prime $`\mathfrak q`$ of $`w`$ such that $`cp^jb\in N_u`$. Set

$$
 z=[cp^{j-R}b]\quad\text{in }C_u .
$$

Then $`p^R z=0`$. If the local image of $`p^{R-1}z`$ vanished, the same equivalence would give another scalar $`c'\notin\mathfrak q`$ with $`c'cp^{j-1}b\in N_u`$. The product $`c'c`$ is outside $`\mathfrak q`$, contradicting minimality of $`j`$. Thus the $`p^{R-1}`$ multiple is nonzero locally and globally, while $`p^R`$ kills both. Primality of $`p`$ gives exact order $`p^R`$ in both quotients, for the single class $`z`$. [Actual served equivalence][served]

<a name="selection"></a>

## 4. Arithmetic selection and the production corollary

All estimates in this section are uniform over the member and the already fixed word of the family. Set $`Z=(X')^{3/4}`$. The prime selection uses a finite difference of the source character sum. For a scale $`Y`$, set

$$
 \Delta_Y f=\frac{f(2Y)-2f(3Y/2)+f(Y)}{Y}.
$$

Applied to the raw sum $`\sum_n\Lambda(n)\chi(n)(y/n-1)_+`$, this gives the unramified-prime weight

$$
 w_p=\frac{\log p}{Zp}\max(0,\min(p-Z,2Z-p)).
$$

The principal term is $`c_0=\log(32/27)>0`$, obtained from $`\Delta_Z(y\log y)`$. The prime number theorem bounds the centered remainder. The nonprincipal centerings are linear and vanish under $`\Delta_Y`$. [Character sum and centering][char] · [Principal estimate][pnt]

Use the pinned contour estimate with height $`x^{14}`$. The conductor bound $`\log(2M)=O_F(x^{21\varepsilon/100})`$ and $`\log y\asymp_F x^{\varepsilon/3}`$ for $`Z\le y\le2X'`$ bound the normalized ordinary and truncation errors by $`O_F(x^{-13})`$. If there is an exceptional real zero $`\beta`$, its term is proportional to $`F_\beta(y)=y^\beta/(\beta(\beta-1))`$. The shape of the stencil gives $`\Delta_Y F_\beta=c_\beta Y^{\beta-1}`$, with $`c_\beta`$ uniformly bounded by the integral of $`F_\beta''`$ over the unit stencil. The source thin estimate at the three upper nodes bounds $`\Delta_{X'}F_\beta`$ by $`O_F(x^{-13})`$. The scaling identity

$$
 |\Delta_ZF_\beta|=|c_\beta|^{1/4}|\Delta_{X'}F_\beta|^{3/4}
$$

therefore bounds it by $`O_F(x^{-39/4})`$ at the lower scale. Proper prime powers and ramified primes contribute $`O_F(Z^{-1/2}\log^2(2Z)+Z^{-1}\log(2M))`$. Consequently all nonprincipal sums are $`O_F(x^{-9})`$ uniformly. [Native contour][contour] · [Source thin estimate][thin]

Let the Artin group of the host have order $`4n`$, where $`n=|D.R.A|`$, and write $`g_p`$ for the Artin class of $`p`$. Character orthogonality now gives weight $`c_0/(4n)+o_F(1/n)`$ in every class, since $`n\le x^3`$ eventually. For the set $`S`$ of $`m`$ top positions write $`C(h)=|\{t\in S:t+h\in S\}|`$. One has $`\sum_h C(h)=m^2`$ and $`C(h)\le m`$. A cyclic subgroup of bounded index gives $`O_F(x^{\varepsilon/2})`$ elements of order less than $`x^{\varepsilon/4}`$, by summing the bound for solutions of $`rh=0`$ over those $`r`$. The source lower bound $`m\ge nx^{-\varepsilon/8}/2`$ shows that discarding these differences loses less than half the ordered pairs. The Artin class with two negative signs gives the inert case and the actual step $`h_p`$. Thus the remaining normalized pair weight $`\sum_p w_p C(h_p)/m`$ is bounded below by a positive constant times $`x^{-\varepsilon/8}`$. [Host Artin law][artin] · [Finite cyclic frame][cyclic] · [Family top and size bounds][sizes]

The source share and bad-top cuts charge $`O_F(x^{-9})`$ and $`O_F(x^{-2+\varepsilon})`$ to this normalized pair weight. Write $`Q=(D.\mathrm{mem}(u)).A.T`$ and $`\mu=D.R.m`$. The level-size fields give $`Q>2Z`$ and $`\log Q=O_F(\mu x^\varepsilon)`$. Deleting divisors of $`Q-1`$ costs $`O_F(\log Q/Z)`$. These losses are smaller than the lower bound. On $`(Z,2Z)`$, the source scales also give $`p_0<p<X'(1-\rho_B)`$ and $`p^2>X'(1+\rho_B)`$ eventually. No positive power lies in the band. The surviving step has even order and its pair lies on one selected orbit. The native selection and support conditions give `Cand` and `GIdx` at a supported place above $`p`$ on the original word. The selected orbit excludes `noGain`, and the source characterization of `L.drop` gives $`p\notin L.\mathrm{drop}`$. The source ties identify the adjacent top positions with $`s,s^+`$, including the last-to-first edge. [Wall and share hypotheses][wall] · [Bad-top estimate][bad] · [Original selection][typei] · [Group and support inputs][gidx]

For the depth tests put $`a=x\exp(x^\varepsilon)`$ and $`b'=a/X'`$. Summing the source Type I cutoff over the selected orbits counts at most $`n`$ top slots and gives, with $`N_1=O_\varepsilon(\log x)`$,

$$
 T\ll_F \mu n b'+\mu nN_1\left(\frac{a}{p^2}
         +\frac{\mathcal L a}{pk}\right)+\exp(o(x^\varepsilon)),
$$

where $`\mathcal L`$ is the source logarithmic factor. The band bound gives $`8n\mathcal L/k\le x^{-2}`$. The other terms divided by $`a/p`$ tend to zero on this interval. Consequently $`R=T+1\le a/(4p)`$ eventually. At a top position each relevant signed multiplicity is at least $`a-c_G\ge a/2`$ eventually, giving both capacities. The chosen adjacent pair excludes the first odd visit at one lift. In the odd-visit sum, let $`A_0`$ be the nonnegative contribution of unexcluded visits and $`d_{s,1}`$ the positive part of this one excluded visit. For the source displacement $`\Delta`$, the formulas give $`g_0=A_0-\Delta`$ and $`g_U+\Delta\ge A_0+d_{s,1}`$. Thus $`g_U-\mathrm{Pr}-(g_0)_+\ge d_{s,1}-\Delta-\mathrm{Pr}`$. The cap at the adjacent top is at most $`2b'+b'/x+\eta+c_G`$, and the penalty and displacement are $`o(a/p)`$ by the family sizes. Since the first visit has size $`(a_s-2c_G)/p`$, this lift contributes at least $`a/(2p)`$ eventually. The other lifts enter the omission weight through nonnegative terms. Taking the source ceiling gives $`R\le\lceil\mathrm{Sv}(v)\rceil`$. [Full Type I cutoff and signed data][cutoff] · [Band estimate][band] · [Gain and omissions][gain]

Apply Sections 2 and 3 to the resulting adjacent pair, place and word and its single unit seed. This proves Theorem A and Proposition B with the same witnesses. For the production corollary, use the original design supplier under its established `HypsAlt` and host inputs. Its duty and selected-group data supply the family hypotheses. For a prescribed lower bound $`y`$, apply `FamCore.exists_pt` at $`\max(y,x_0)`$, choose an index provided by that inhabited window and choose the source word $`D.u_0`$. Theorem A at that word returns $`p,w,z`$. This is an existence argument without a numerical neighbour matrix. [Design supplier and original call][design] · [Inhabited windows][window]

<a name="verification"></a>

## 5. Formal verification and scope

The paper result above concerns the original quotients. The fixed-place Lean proof consumes the selected local data, and the indexed-family theorem supplies those data in the paper argument. The formal verification record is dated separately. See [Lean evidence and theorem crosswalk](../verification/LEAN.md) and the [public update on #77][update].

I used AI assistance in developing the proof and its Lean formalization.

[issue]: https://github.com/leanprover-community/riemann-hypothesis/issues/77
[update]: https://github.com/leanprover-community/riemann-hypothesis/issues/77#issuecomment-7167482262
[seed]: https://github.com/leanprover-community/riemann-hypothesis/issues/77#issuecomment-7146180600
[np]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L479-L505
[served]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/LocalRingCardinality/DataLatDefs.lean#L67-L83
[typei]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L262-L333
[family]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/ParConsts.lean#L65-L121
[slots]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L456-L477
[weights]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L103-L178
[words]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/GradedWeylDivisibility/StatementA.lean#L74-L116
[frame]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/DeterminantTwistRowActionMem.lean#L17-L55
[edge]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/LatticeSystems.lean#L2142-L2169
[frob]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L61-L78
[free]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/GroupActionMulSingleEqDilation.lean#L795-L806
[sum]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/LatticeSystems.lean#L510-L525
[preserve]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/LocalToGlobal/GroupLattices/FockModels/OperatorsPreserveLattices.lean#L336-L345
[commute]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/LatticeSystems.lean#L634-L651
[char]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/FiltrationCocycleLiftCriterion.lean#L51-L65
[pnt]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/ZeroFreeRegion/LogDerivRegion.lean#L960-L969
[contour]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean#L1337-L1354
[thin]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GlobalSchurBounds/Chosen.lean#L79-L122
[artin]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean#L103-L159
[cyclic]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L340-L357
[sizes]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/ElevenLe.lean#L51-L155
[wall]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GlobalSchurBounds/WeightVectorSmallSharesEight.lean#L52-L64
[bad]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean#L1422-L1425
[gidx]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/LocalRingCardinality/Lemmas.lean#L1393-L1447
[cutoff]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L216-L255
[band]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L94-L110
[gain]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L260-L297
[design]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean#L929-L979
[window]: https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/src/Formalism/SharpRestriction/FamCore.lean#L150-L154
