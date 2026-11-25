import Formalism.GradedWeylDivisibility.TypeIFlagWord
import Formalism.GradedWeylDivisibility.TypeIPolarizedKernel

open scoped BigOperators Matrix
open Matrix MvPolynomial

namespace Formalism.GradedWeylDivisibility.TypeI

noncomputable section

/-- The common flag for all labels after applying the source row action in
the output frame. The order is frame times the ordered word matrix. -/
def wordFlag {n : ℕ} {R : Type*} [CommRing R]
    (U : Matrix (Fin n) (Fin n) R) (w : List (Fin n × Fin n × ℕ)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (WordParameter w.length) R) :=
  U.map C * orderedMatrix R w

private theorem map_rowVariables_orderedEval {n : ℕ} {R : Type*} [CommRing R]
    (w : List (Fin n × Fin n × ℕ)) :
    (rowVariables R n n).map (orderedEval R w) =
      ((orderedMatrix R w).map (MvPolynomial.map (MvPolynomial.C : R →+* RowPolynomial R n n)))ᵀ *
        (rowVariables R n n).map MvPolynomial.C := by
  ext i j
  simp only [rowVariables, Matrix.map_apply, Matrix.of_apply, orderedEval, MvPolynomial.eval₂Hom_X']

private theorem map_orderedEval_at_frame {n : ℕ} {R : Type*} [CommRing R]
    (U : Matrix (Fin n) (Fin n) R) (w : List (Fin n × Fin n × ℕ)) :
    (rowVariables R n n).map ((MvPolynomial.map (rowAct R (n := n) Uᵀ).toRingHom).comp (orderedEval R w)) =
      ((wordFlag U w).map (MvPolynomial.map (MvPolynomial.C : R →+* RowPolynomial R n n)))ᵀ *
        (rowVariables R n n).map MvPolynomial.C := by
  let c : R →+* RowPolynomial R n n := MvPolynomial.C
  let j : RowPolynomial R n n →+* MvPolynomial (WordParameter w.length) (RowPolynomial R n n) := C
  let B := (orderedMatrix R w).map (MvPolynomial.map c)
  let Z := (rowVariables R n n).map j
  let ψ := (rowAct R (n := n) Uᵀ).toRingHom
  let φ := MvPolynomial.map (σ := WordParameter w.length) ψ
  have hc : ψ.comp c = c := by
    apply RingHom.ext
    intro r
    change (rowAct R (n := n) Uᵀ) (C r) = C r
    simp only [rowAct, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  have hB : Bᵀ.map φ = Bᵀ := by
    apply Matrix.ext
    intro i k
    change MvPolynomial.map ψ (MvPolynomial.map c ((orderedMatrix R w) k i)) = _
    rw [MvPolynomial.map_map, hc]
    rfl
  have hZ : Z.map φ = (U.map (j.comp c))ᵀ * Z := by
    apply Matrix.ext
    intro i k
    change φ (j (X (i,k))) = _
    rw [MvPolynomial.map_C]
    change j (rowAct R Uᵀ (X (i,k))) = _
    simp only [rowAct, aeval_X, map_sum, map_mul, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, RingHom.comp_apply, Z, j, c, rowVariables, Matrix.of_apply]
  have hU : (U.map (C : R →+* MvPolynomial (WordParameter w.length) R)).map
      (MvPolynomial.map c) = U.map (j.comp c) := by
    apply Matrix.ext
    intro i k
    exact MvPolynomial.map_C _ _
  change ((rowVariables R n n).map (orderedEval R w)).map φ =
    ((wordFlag U w).map (MvPolynomial.map c))ᵀ * Z
  rw [map_rowVariables_orderedEval]
  change (Bᵀ * Z).map φ = _
  rw [Matrix.map_mul, hB, hZ, ← Matrix.mul_assoc, ← Matrix.transpose_mul, wordFlag,
    Matrix.map_mul, hU]

/-- Expansion of the actual integral-Weyl generators in any inverse-transpose
frame. The word variables remain shared by every label in its flag. -/
theorem rowAct_applyWord_hw_eq_labelled_coefficients {n : ℕ} {R : Type*} [CommRing R]
    (ν : Fin n → ℕ) (U : Matrix (Fin n) (Fin n) R) (w : List (Fin n × Fin n × ℕ)) :
    rowAct R Uᵀ (applyWord R w (hw R le_rfl ν)) =
      ∑ I : FlagLabels ν, (flagProducts ν (wordFlag U w) I).coeff (wordExponent w) •
        flagProducts ν (rowVariables R n n) I := by
  let ψ := (rowAct R (n := n) Uᵀ).toRingHom
  let E := (MvPolynomial.map (σ := WordParameter w.length) ψ).comp (orderedEval R w)
  have hW : E (hw R le_rfl ν) =
      ∑ I : FlagLabels ν, MvPolynomial.map (MvPolynomial.C : R →+* RowPolynomial R n n)
        (flagProducts ν (wordFlag U w) I) * C (flagProducts ν (rowVariables R n n) I) := by
    rw [hw_eq_labelled_initial_product]
    unfold leadingFlagProduct
    rw [map_prod]
    simp only [map_leadingFlagMinor]
    rw [show (rowVariables R n n).map E = _ from map_orderedEval_at_frame U w]
    change leadingFlagProduct ν (_ * _) = _
    rw [labelled_flag_product_transpose_mul]
    simp only [← map_flagProducts]
  rw [applyWord_eq_ordered_coeff]
  change ψ ((orderedEval R w (hw R le_rfl ν)).coeff (wordExponent w)) = _
  rw [← MvPolynomial.coeff_map, ← show E (hw R le_rfl ν) =
    MvPolynomial.map ψ (orderedEval R w (hw R le_rfl ν)) from rfl, hW, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_comm]

/-- One rational row computes its labelled pairing on every actual word
generator, even after the source action in an arbitrary frame. -/
theorem exists_polarized_row_on_framed_word
    {n : ℕ} {K : Type*} [Field K] (f : ℚ →+* K) (ν : Fin n → ℕ)
    (l : FlagLabels ν → ℚ) :
    ∃ Λ : RowPolynomial K n n →ₗ[K] K,
      ∀ (U : Matrix (Fin n) (Fin n) K) (w : List (Fin n × Fin n × ℕ)),
        Λ (rowAct K Uᵀ (applyWord K w (hw K le_rfl ν))) =
          ∑ I : FlagLabels ν, f (l I) *
            (flagProducts ν (wordFlag U w) I).coeff (wordExponent w) := by
  obtain ⟨Λ, hΛ⟩ := exists_polarized_substitution_functional
    (fun I => flagProducts ν (rowVariables ℚ n n) I) l f
  refine ⟨Λ, ?_⟩
  intro U w
  let a : RowPolynomial K n n →ₐ[K] MvPolynomial (WordParameter w.length) K :=
    aeval fun x : Fin n × Fin n => (wordFlag U w) x.1 x.2
  let ψ := (MvPolynomial.lcoeff K (wordExponent w)).comp a.toLinearMap
  have hrat (I : FlagLabels ν) :
      MvPolynomial.map f (flagProducts ν (rowVariables ℚ n n) I) =
        flagProducts ν (rowVariables K n n) I := by
    rw [map_flagProducts]
    congr 1
    ext i j
    simp only [rowVariables, Matrix.map_apply, Matrix.of_apply, MvPolynomial.map_X]
  have hψ (I : FlagLabels ν) :
      ψ (flagProducts ν (rowVariables K n n) I) =
        (flagProducts ν (wordFlag U w) I).coeff (wordExponent w) := by
    change (a.toRingHom (flagProducts ν (rowVariables K n n) I)).coeff (wordExponent w) = _
    rw [map_flagProducts a.toRingHom]
    have hvars : (rowVariables K n n).map a.toRingHom = wordFlag U w := by
      apply Matrix.ext
      intro i j
      change a (X (i,j)) = _
      exact aeval_X _ _
    rw [hvars]
  rw [rowAct_applyWord_hw_eq_labelled_coefficients]
  simpa only [hrat, hψ] using hΛ ψ

end

end Formalism.GradedWeylDivisibility.TypeI
