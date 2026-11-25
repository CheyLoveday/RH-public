import Formalism.GradedWeylDivisibility.TypeIOrderedWord
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment

open scoped BigOperators Matrix
open Matrix MvPolynomial

namespace Formalism.GradedWeylDivisibility.TypeI

noncomputable section

/-- A height-indexed increasing set of row indices for an initial minor. -/
abbrev FlagRows (n height : ℕ) := {I : Finset (Fin n) // I.card = height}

def flagMinor {n height : ℕ} {R : Type*} [CommRing R] (h : height ≤ n)
    (X : Matrix (Fin n) (Fin n) R) (I : FlagRows n height) : R :=
  (X.submatrix (I.1.orderEmbOfFin I.2) (Fin.castLE h)).det

def leadingFlagMinor {n height : ℕ} {R : Type*} [CommRing R] (h : height ≤ n)
    (X : Matrix (Fin n) (Fin n) R) : R :=
  (X.submatrix (Fin.castLE h) (Fin.castLE h)).det

theorem map_flagMinor {n height : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : height ≤ n) (X : Matrix (Fin n) (Fin n) R) (I : FlagRows n height) :
    f (flagMinor h X I) = flagMinor h (X.map f) I := by
  unfold flagMinor
  rw [RingHom.map_det]
  rfl

theorem map_leadingFlagMinor {n height : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : height ≤ n) (X : Matrix (Fin n) (Fin n) R) :
    f (leadingFlagMinor h X) = leadingFlagMinor h (X.map f) := by
  unfold leadingFlagMinor
  rw [RingHom.map_det]
  rfl

/-- Use the same initial columns on each side of Cauchy–Binet. -/
theorem leading_flag_minor_transpose_mul {n height : ℕ} {R : Type*} [CommRing R]
    (h : height ≤ n) (A B : Matrix (Fin n) (Fin n) R) :
    leadingFlagMinor h (Aᵀ * B) = ∑ I : FlagRows n height, flagMinor h A I * flagMinor h B I := by
  let a := A.submatrix id (Fin.castLE h)
  let b := B.submatrix id (Fin.castLE h)
  have hab : (Aᵀ * B).submatrix (Fin.castLE h) (Fin.castLE h) = aᵀ * b := by
    ext i j
    simp only [a, b, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id_eq]
  unfold leadingFlagMinor
  rw [hab, Formalism.HermitianLatticeCounting.P.ge_cauchyBinet]
  apply Finset.sum_congr rfl
  intro I _
  rw [mul_comm]
  have ht : aᵀ.submatrix id (I.1.orderEmbOfFin I.2) =
      (A.submatrix (I.1.orderEmbOfFin I.2) (Fin.castLE h))ᵀ := rfl
  have hb : b.submatrix (I.1.orderEmbOfFin I.2) id =
      B.submatrix (I.1.orderEmbOfFin I.2) (Fin.castLE h) := rfl
  rw [ht, hb, Matrix.det_transpose]
  rfl

/-- Keep a separate label for every copy, including repeated heights. -/
abbrev FlagCopies {n : ℕ} (ν : Fin n → ℕ) :=
  Σ s : Fin n, Fin (ν s - nuNext ν s)

abbrev FlagLabels {n : ℕ} (ν : Fin n → ℕ) :=
  ∀ b : FlagCopies ν, FlagRows n (b.1.val + 1)

def flagProducts {n : ℕ} {R : Type*} [CommRing R] (ν : Fin n → ℕ)
    (X : Matrix (Fin n) (Fin n) R) (I : FlagLabels ν) : R :=
  ∏ b : FlagCopies ν, flagMinor (Nat.succ_le_of_lt b.1.isLt) X (I b)

def leadingFlagProduct {n : ℕ} {R : Type*} [CommRing R] (ν : Fin n → ℕ)
    (X : Matrix (Fin n) (Fin n) R) : R :=
  ∏ b : FlagCopies ν, leadingFlagMinor (Nat.succ_le_of_lt b.1.isLt) X

theorem map_flagProducts {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ν : Fin n → ℕ) (X : Matrix (Fin n) (Fin n) R) (I : FlagLabels ν) :
    f (flagProducts ν X I) = flagProducts ν (X.map f) I := by
  unfold flagProducts
  simp only [map_prod, map_flagMinor]

/-- Polarization at a fixed height profile. Both copies of each factor use their
own common flag matrix, including all the repeated labels. -/
theorem labelled_flag_product_transpose_mul {n : ℕ} {R : Type*} [CommRing R]
    (ν : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    leadingFlagProduct ν (Aᵀ * B) = ∑ I : FlagLabels ν, flagProducts ν A I * flagProducts ν B I := by
  classical
  simp only [leadingFlagProduct, leading_flag_minor_transpose_mul, Fintype.prod_sum,
    Finset.prod_mul_distrib, flagProducts]

theorem hw_eq_labelled_initial_product (R : Type*) [CommRing R] {n : ℕ} (ν : Fin n → ℕ) :
    hw R le_rfl ν = leadingFlagProduct ν (rowVariables R n n) := by
  unfold leadingFlagProduct hw
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro s _
  change _ = ∏ _j : Fin (ν s - nuNext ν s),
    leadingFlagMinor (Nat.succ_le_of_lt s.isLt) (rowVariables R n n)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

private theorem coeff_C_flagProducts {n : ℕ} {R : Type*} [CommRing R]
    (ν : Fin n → ℕ) (w : List (Fin n × Fin n × ℕ)) (I : FlagLabels ν) :
    flagProducts ν ((rowVariables R n n).map
      (MvPolynomial.C : RowPolynomial R n n →+* MvPolynomial (WordParameter w.length) (RowPolynomial R n n))) I =
      C (flagProducts ν (rowVariables R n n) I) :=
  (map_flagProducts _ _ _ _).symm

/-- Ordered matrix substitution in the literal highest-weight polynomial. -/
theorem orderedEval_hw_eq_labelled_sum {n : ℕ} {R : Type*} [CommRing R]
    (ν : Fin n → ℕ) (w : List (Fin n × Fin n × ℕ)) :
    orderedEval (n := n) R w (hw R le_rfl ν) =
      ∑ I : FlagLabels ν,
        MvPolynomial.map (MvPolynomial.C : R →+* RowPolynomial R n n)
          (flagProducts ν (orderedMatrix R w) I) *
        C (flagProducts ν (rowVariables R n n) I) := by
  rw [hw_eq_labelled_initial_product]
  unfold leadingFlagProduct
  rw [map_prod]
  simp only [map_leadingFlagMinor]
  have hv : (rowVariables R n n).map (orderedEval R w) =
      ((orderedMatrix R w).map (MvPolynomial.map (MvPolynomial.C : R →+* RowPolynomial R n n)))ᵀ *
        (rowVariables R n n).map MvPolynomial.C := by
    ext i j
    simp only [rowVariables, Matrix.map_apply, Matrix.of_apply, orderedEval, MvPolynomial.eval₂Hom_X']
  rw [hv]
  change leadingFlagProduct ν (_ * _) = _
  rw [labelled_flag_product_transpose_mul]
  simp only [← map_flagProducts]

/-- Expand the exact divided-word output in the labelled initial minors of the
original chart. Every factor in a slot uses the same ordered parameter matrix. -/
theorem applyWord_hw_eq_labelled_coefficients {n : ℕ} {R : Type*} [CommRing R]
    (ν : Fin n → ℕ) (w : List (Fin n × Fin n × ℕ)) :
    applyWord R w (hw R le_rfl ν) =
      ∑ I : FlagLabels ν, (flagProducts ν (orderedMatrix R w) I).coeff (wordExponent w) •
        flagProducts ν (rowVariables R n n) I := by
  rw [applyWord_eq_ordered_coeff, orderedEval_hw_eq_labelled_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_comm]

end

end Formalism.GradedWeylDivisibility.TypeI
