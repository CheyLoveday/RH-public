module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Rank

open scoped BigOperators Matrix
open Matrix

namespace Formalism.GradedWeylDivisibility.TypeI

public section

/-- Over the rationals the transpose and the Gram matrix have the same image.
This is the representing equation for extracting a coefficient on a span. -/
theorem exists_rational_gram_representative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (l : ι → ℚ) :
    ∃ z : κ → ℚ, (Aᵀ * A) *ᵥ z = Aᵀ *ᵥ l := by
  have hle : LinearMap.range (Aᵀ * A).mulVecLin ≤ LinearMap.range Aᵀ.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    exact ⟨A *ᵥ x, Matrix.mulVec_mulVec x Aᵀ A⟩
  have hdim : Module.finrank ℚ (LinearMap.range (Aᵀ * A).mulVecLin) =
      Module.finrank ℚ (LinearMap.range Aᵀ.mulVecLin) := by
    rw [Matrix.finrank_range_mulVecLin, Matrix.finrank_range_mulVecLin,
      Matrix.rank_transpose_mul_self, Matrix.rank_transpose]
  have hrange := Submodule.eq_of_le_of_finrank_eq hle hdim
  have hm : Aᵀ *ᵥ l ∈ LinearMap.range (Aᵀ * A).mulVecLin := by
    rw [hrange]
    exact ⟨l, rfl⟩
  exact hm

/-- A rational Gram representative gives a functional that recovers the desired
labelled pairing on every coefficient vector after scalar extension. -/
theorem exists_polarized_coeff_functional
    {ι κ σ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (q : ι → MvPolynomial σ ℚ) (mon : κ → σ →₀ ℕ)
    (l : ι → ℚ) (f : ℚ →+* K) :
    let B : Matrix ι κ K := Matrix.of fun i j => f ((q i).coeff (mon j))
    ∃ Λ : MvPolynomial σ K →ₗ[K] K, ∀ x : κ → K,
      Λ (∑ i, (B *ᵥ x) i • (q i).map f) = (f ∘ l) ⬝ᵥ (B *ᵥ x) := by
  classical
  dsimp only
  let A : Matrix ι κ ℚ := Matrix.of fun i j => (q i).coeff (mon j)
  let B : Matrix ι κ K := A.map f
  change ∃ Λ : MvPolynomial σ K →ₗ[K] K, ∀ x : κ → K,
    Λ (∑ i, (B *ᵥ x) i • (q i).map f) = (f ∘ l) ⬝ᵥ (B *ᵥ x)
  obtain ⟨z, hz⟩ := exists_rational_gram_representative A l
  have ht : Aᵀ.map f = Bᵀ := rfl
  have hg : (Bᵀ * B) *ᵥ (f ∘ z) = Bᵀ *ᵥ (f ∘ l) := by
    funext j
    have hj := congrArg f (congrFun hz j)
    rw [RingHom.map_mulVec, RingHom.map_mulVec, Matrix.map_mul, ht] at hj
    exact hj
  refine ⟨∑ j, f (z j) • MvPolynomial.lcoeff K (mon j), ?_⟩
  intro x
  let P := ∑ i, (B *ᵥ x) i • (q i).map f
  have hc : (fun j => P.coeff (mon j)) = Bᵀ *ᵥ (B *ᵥ x) := by
    funext j
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  change (∑ j, f (z j) • MvPolynomial.lcoeff K (mon j)) P = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  change (f ∘ z) ⬝ᵥ (fun j => P.coeff (mon j)) = _
  have hs : (Bᵀ * B)ᵀ = Bᵀ * B := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hc, Matrix.mulVec_mulVec, ← hs, Matrix.dotProduct_transpose_mulVec, hg,
    ← Matrix.dotProduct_transpose_mulVec, Matrix.transpose_transpose]

/-- One functional works for all specializations, including simultaneous word
coefficients. The finite rational matrix uses the union of the polynomial
supports, so it retains all linear relations among the labelled products. -/
theorem exists_polarized_substitution_functional
    {ι σ K : Type*} [Fintype ι] [Field K]
    (q : ι → MvPolynomial σ ℚ) (l : ι → ℚ) (f : ℚ →+* K) :
    ∃ Λ : MvPolynomial σ K →ₗ[K] K, ∀ ψ : MvPolynomial σ K →ₗ[K] K,
      Λ (∑ i, ψ ((q i).map f) • (q i).map f) = ∑ i, f (l i) * ψ ((q i).map f) := by
  classical
  let S := Finset.univ.biUnion (fun i => (q i).support)
  let mon : (↑S : Type _) → σ →₀ ℕ := Subtype.val
  obtain ⟨Λ, hΛ⟩ := exists_polarized_coeff_functional q mon l f
  refine ⟨Λ, ?_⟩
  intro ψ
  let x : (↑S : Type _) → K := fun j => ψ (MvPolynomial.monomial (mon j) 1)
  let B : Matrix ι (↑S : Type _) K := Matrix.of fun i j => f ((q i).coeff (mon j))
  have hspan (i : ι) : (q i).map f =
      ∑ j : (↑S : Type _), f ((q i).coeff (mon j)) • MvPolynomial.monomial (mon j) 1 := by
    have hsub : (q i).support ⊆ S := by
      intro j hj
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩
    have hfull : (q i).map f =
        ∑ j ∈ S, f ((q i).coeff j) • MvPolynomial.monomial j 1 := by
      calc
        (q i).map f = ∑ j ∈ (q i).support, f ((q i).coeff j) • MvPolynomial.monomial j 1 := by
          conv_lhs => rw [MvPolynomial.as_sum (q i)]
          simp only [map_sum, MvPolynomial.map_monomial, MvPolynomial.smul_monomial,
            smul_eq_mul, mul_one]
        _ = ∑ j ∈ S, f ((q i).coeff j) • MvPolynomial.monomial j 1 :=
          Finset.sum_subset hsub fun j _ hj => by
            rw [MvPolynomial.notMem_support_iff.mp hj, map_zero, zero_smul]
    exact hfull.trans (Finset.sum_attach S _).symm
  have hx (i : ι) : (B *ᵥ x) i = ψ ((q i).map f) := by
    rw [hspan i, map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  change (∀ y : (↑S : Type _) → K,
    Λ (∑ i, (B *ᵥ y) i • (q i).map f) = (f ∘ l) ⬝ᵥ (B *ᵥ y)) at hΛ
  simpa only [dotProduct, Function.comp_apply, hx] using hΛ x

end

end Formalism.GradedWeylDivisibility.TypeI
