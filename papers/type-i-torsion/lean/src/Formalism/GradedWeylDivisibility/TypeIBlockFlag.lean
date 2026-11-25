import Formalism.GradedWeylDivisibility.TypeIFlagFrames
import Mathlib.RingTheory.MvPolynomial.Basic

open scoped BigOperators Matrix Classical
open Matrix MvPolynomial

namespace Formalism.GradedWeylDivisibility.TypeI

noncomputable section

/-- Assemble the slot polynomials by the source's disjoint variable tags. -/
def packFlagBlocks {ι : Type*} [Fintype ι] {σ : ι → Type*} {K : Type*} [CommRing K]
    (P : ∀ i, MvPolynomial (σ i) K) : MvPolynomial (Σ i, σ i) K :=
  ∏ i, MvPolynomial.rename (Sigma.mk i) (P i)

private theorem prod_monomial_block {ι σ K : Type*} [Fintype ι] [CommRing K]
    (a : ι → σ →₀ ℕ) (b : ι → K) (s : Finset ι) :
    (∏ i ∈ s, MvPolynomial.monomial (a i) (b i)) =
      MvPolynomial.monomial (∑ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, hs, MvPolynomial.monomial_mul_monomial]

private theorem sigma_mk_injective {ι : Type*} {σ : ι → Type*} (i : ι) :
    Function.Injective (Sigma.mk i : σ i → Σ j, σ j) := by
  intro a b h
  cases h
  rfl

private theorem flagBlock_exponent {ι : Type*} [Fintype ι] {σ : ι → Type*}
    (a : ∀ i, σ i →₀ ℕ) (i : ι) :
    (∑ j, (a j).mapDomain (Sigma.mk j)).comapDomain (Sigma.mk i)
      ((sigma_mk_injective i).injOn) = a i := by
  classical
  ext u
  simp only [Finsupp.comapDomain_apply, Finsupp.finsetSum_apply]
  rw [Fintype.sum_eq_single i]
  · exact Finsupp.mapDomain_apply_of_injective (sigma_mk_injective i) (a i) u
  · intro j hji
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x, hx⟩
    exact hji (congrArg Sigma.fst hx)

/-- Extend a product of slot specializations to a single linear map in the
disjoint variables. The premise and result are over the same coefficient ring. -/
theorem exists_linear_specialization_on_flag_blocks
    {ι : Type*} [Fintype ι] {σ : ι → Type*} {K : Type*} [CommRing K]
    (ψ : ∀ i, MvPolynomial (σ i) K →ₗ[K] K) :
    ∃ Ψ : MvPolynomial (Σ i, σ i) K →ₗ[K] K,
      ∀ P : ∀ i, MvPolynomial (σ i) K,
        Ψ (packFlagBlocks P) = ∏ i, ψ i (P i) := by
  classical
  let val : ((Σ i, σ i) →₀ ℕ) → K :=
    fun a => ∏ i, ψ i (monomial (a.comapDomain (Sigma.mk i) (sigma_mk_injective i).injOn) 1)
  let Ψ := (MvPolynomial.basisMonomials (Σ i, σ i) K).constr K val
  have hΨ (a : (Σ i, σ i) →₀ ℕ) (c : K) : Ψ (monomial a c) = c * val a := by
    have hc : monomial a c = c • monomial a (1 : K) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hc, map_smul]
    change c * Ψ (monomial a 1) = c * val a
    congr 1
    exact Module.Basis.constr_basis _ _ _ _
  have hmon (a : ∀ i, σ i →₀ ℕ) (c : ι → K) :
      Ψ (packFlagBlocks (fun i => monomial (a i) (c i))) =
        ∏ i, ψ i (monomial (a i) (c i)) := by
    unfold packFlagBlocks
    simp only [MvPolynomial.rename_monomial]
    rw [prod_monomial_block, hΨ]
    simp only [val, flagBlock_exponent]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [show monomial (a i) (c i) = c i • monomial (a i) 1 by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  refine ⟨Ψ, ?_⟩
  intro P
  let T (i : ι) := (P i).support
  have hP (i : ι) : P i = ∑ a : (↑(T i) : Type _), monomial a.1 ((P i).coeff a.1) :=
    (P i).as_sum.trans (Finset.sum_attach (T i) _).symm
  have hh : packFlagBlocks P = ∑ a : ∀ i, (↑(T i) : Type _),
      packFlagBlocks (fun i => monomial (a i).1 ((P i).coeff (a i).1)) := by
    unfold packFlagBlocks
    conv_lhs => enter [2, i]; rw [hP i, map_sum]
    rw [Fintype.prod_sum]
  rw [hh, map_sum]
  simp only [hmon]
  calc
    _ = ∏ i, ∑ a : (↑(T i) : Type _), ψ i (monomial a.1 ((P i).coeff a.1)) :=
      (Fintype.prod_sum (fun i (a : (↑(T i) : Type _)) => ψ i (monomial a.1 ((P i).coeff a.1)))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      conv_rhs => rw [hP i, map_sum]

/-- A single coefficient row for all native word generators when their variables
are packed by slot. Each word and its frame stay fixed throughout its block. -/
theorem exists_polarized_row_on_flag_blocks
    {ι : Type*} [Fintype ι] {n : ℕ} {K : Type*} [Field K] (f : ℚ →+* K)
    (ν : ι → Fin n → ℕ) (l : (∀ i, FlagLabels (ν i)) → ℚ) :
    ∃ Λ : MvPolynomial (Σ _i : ι, Fin n × Fin n) K →ₗ[K] K,
      ∀ (U : ι → Matrix (Fin n) (Fin n) K) (w : ι → List (Fin n × Fin n × ℕ)),
        Λ (packFlagBlocks (fun i => rowAct K (U i)ᵀ (applyWord K (w i) (hw K le_rfl (ν i))))) =
          ∑ I : ∀ i, FlagLabels (ν i), f (l I) *
            ∏ i, (flagProducts (ν i) (wordFlag (U i) (w i)) (I i)).coeff (wordExponent (w i)) := by
  classical
  let q (I : ∀ i, FlagLabels (ν i)) :=
    packFlagBlocks (fun i => flagProducts (ν i) (rowVariables ℚ n n) (I i))
  obtain ⟨Λ, hΛ⟩ := exists_polarized_substitution_functional q l f
  refine ⟨Λ, ?_⟩
  intro U w
  let a (i : ι) : RowPolynomial K n n →ₐ[K] MvPolynomial (WordParameter (w i).length) K :=
    aeval fun x : Fin n × Fin n => (wordFlag (U i) (w i)) x.1 x.2
  let ψ (i : ι) := (MvPolynomial.lcoeff K (wordExponent (w i))).comp (a i).toLinearMap
  obtain ⟨Ψ, hΨ⟩ := exists_linear_specialization_on_flag_blocks ψ
  let P (i : ι) (I : FlagLabels (ν i)) := flagProducts (ν i) (rowVariables K n n) I
  let c (i : ι) (I : FlagLabels (ν i)) :=
    (flagProducts (ν i) (wordFlag (U i) (w i)) I).coeff (wordExponent (w i))
  have hψ (i : ι) (I : FlagLabels (ν i)) : ψ i (P i I) = c i I := by
    change ((a i).toRingHom (flagProducts (ν i) (rowVariables K n n) I)).coeff (wordExponent (w i)) = _
    rw [map_flagProducts (a i).toRingHom]
    have hvars : (rowVariables K n n).map (a i).toRingHom = wordFlag (U i) (w i) := by
      apply Matrix.ext
      intro j k
      change a i (X (j,k)) = _
      exact aeval_X _ _
    rw [hvars]
  have hq (I : ∀ i, FlagLabels (ν i)) : MvPolynomial.map f (q I) =
      packFlagBlocks (fun i => P i (I i)) := by
    unfold q packFlagBlocks
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [MvPolynomial.map_rename, map_flagProducts]
    have hvars : (rowVariables ℚ n n).map (MvPolynomial.map f) = rowVariables K n n := by
      apply Matrix.ext
      intro j k
      exact MvPolynomial.map_X f (j,k)
    rw [hvars]
  have hprod : packFlagBlocks (fun i => rowAct K (U i)ᵀ (applyWord K (w i) (hw K le_rfl (ν i)))) =
      ∑ I : ∀ i, FlagLabels (ν i), (∏ i, c i (I i)) • packFlagBlocks (fun i => P i (I i)) := by
    unfold packFlagBlocks
    simp only [rowAct_applyWord_hw_eq_labelled_coefficients, map_sum, map_smul]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro I _
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, Finset.prod_mul_distrib, map_prod]
    rfl
  rw [hprod]
  simpa only [hq, hΨ, hψ] using hΛ Ψ

end

end Formalism.GradedWeylDivisibility.TypeI
