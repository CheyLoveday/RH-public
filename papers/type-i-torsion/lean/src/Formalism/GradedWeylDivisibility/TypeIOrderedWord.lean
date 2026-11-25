import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Matrix.Basis

noncomputable section

namespace Formalism.GradedWeylDivisibility.TypeI

open Matrix MvPolynomial

abbrev RowPolynomial (R : Type*) [CommRing R] (r n : ℕ) := MvPolynomial (Fin r × Fin n) R

def rowVariables (R : Type*) [CommRing R] (r n : ℕ) :
    Matrix (Fin r) (Fin n) (RowPolynomial R r n) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

def letterMatrix {A : Type*} [CommRing A] {r : ℕ} (a b : Fin r) (t : A) :
    Matrix (Fin r) (Fin r) A :=
  1 + Matrix.single a b t

private theorem letterMatrix_transpose_mul_apply {A : Type*} [CommRing A] {r n : ℕ}
    (a b i : Fin r) (j : Fin n) (t : A) (Z : Matrix (Fin r) (Fin n) A) :
    ((letterMatrix a b t)ᵀ * Z) i j =
      Z i j + if i = b then t * Z a j else 0 := by
  rw [letterMatrix, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
    Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  by_cases h : i = b
  · subst i
    simp
  · simp [h, Matrix.single_mul_apply_of_ne b a i j h Z]

/-- The literal source substitution uses the transpose, including when the
letter's two row indices coincide. -/
theorem rowGen_eq_transpose_eval₂ {R : Type*} [CommRing R] {r n : ℕ}
    (a b : Fin r) :
    (rowGen R (n := n) a b).toRingHom =
      MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun v =>
        ((letterMatrix a b (Polynomial.X : Polynomial (RowPolynomial R r n)))ᵀ *
          (rowVariables R r n).map Polynomial.C) v.1 v.2) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change rowGen R a b (MvPolynomial.C c) = _
    rw [rowGen, MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C]
    rfl
  · intro v
    change rowGen R a b (MvPolynomial.X v) = _
    simp only [rowGen, MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X',
      letterMatrix_transpose_mul_apply, Matrix.map_apply, rowVariables, Matrix.of_apply]

theorem rowDiv_eq_transpose_coeff {R : Type*} [CommRing R] {r n : ℕ}
    (a b : Fin r) (k : ℕ) (F : RowPolynomial R r n) :
    rowDiv R a b k F =
      (MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun v =>
        ((letterMatrix a b (Polynomial.X : Polynomial (RowPolynomial R r n)))ᵀ *
          (rowVariables R r n).map Polynomial.C) v.1 v.2) F).coeff k := by
  unfold rowDiv
  exact congrArg (fun f : RowPolynomial R r n →+* Polynomial (RowPolynomial R r n) =>
    (f F).coeff k) (rowGen_eq_transpose_eval₂ a b)

/-- The new parameter is `none`. Each earlier parameter in the tail has its
own `some` index. -/
abbrev WordParameter : ℕ → Type
  | 0 => Empty
  | k + 1 => Option (WordParameter k)

def wordExponent {r : ℕ} : (w : List (Fin r × Fin r × ℕ)) → WordParameter w.length →₀ ℕ
  | [] => 0
  | a :: w => (wordExponent w).optionElim a.2.2

/-- The ordered product (T₁ ⋯ T_ℓ). In the recursive definition the head
multiplies the tail on the left. -/
def orderedMatrix (R : Type*) [CommRing R] {r : ℕ} :
    (w : List (Fin r × Fin r × ℕ)) →
      Matrix (Fin r) (Fin r) (MvPolynomial (WordParameter w.length) R)
  | [] => 1
  | a :: w => letterMatrix a.1 a.2.1 (MvPolynomial.X none) *
      (orderedMatrix R w).map (MvPolynomial.rename Option.some).toRingHom

def orderedEval (R : Type*) [CommRing R] {r n : ℕ}
    (w : List (Fin r × Fin r × ℕ)) :
    RowPolynomial R r n →+* MvPolynomial (WordParameter w.length) (RowPolynomial R r n) :=
  let c : R →+* RowPolynomial R r n := MvPolynomial.C
  let j : RowPolynomial R r n →+* MvPolynomial (WordParameter w.length) (RowPolynomial R r n) :=
    MvPolynomial.C
  let B := (orderedMatrix R w).map (MvPolynomial.map (σ := WordParameter w.length) c)
  let Z := (rowVariables R r n).map j
  MvPolynomial.eval₂Hom (j.comp c) (fun v : Fin r × Fin n => (Bᵀ * Z) v.1 v.2)

private def addRowParameter {S σ : Type*} [CommRing S] (f : S →+* Polynomial S) :
    MvPolynomial σ S →+* MvPolynomial (Option σ) S :=
  (MvPolynomial.optionEquivRight S σ).symm.toRingHom.comp (MvPolynomial.map f)

private theorem optionRight_monomial {S σ : Type*} [CommRing S]
    (e : Option σ →₀ ℕ) (c : S) :
    MvPolynomial.optionEquivRight S σ (MvPolynomial.monomial e c) =
      MvPolynomial.monomial e.some (Polynomial.monomial (e none) c) := by
  classical
  rw [MvPolynomial.optionEquivRight_apply, MvPolynomial.aeval_monomial,
    Finsupp.prod_option_index e _ (fun _ => pow_zero _) (fun _ i j => pow_add _ i j)]
  change MvPolynomial.C (Polynomial.C c) *
      (MvPolynomial.C (Polynomial.X : Polynomial S) ^ e none *
        e.some.prod (fun i d => (MvPolynomial.X i : MvPolynomial σ (Polynomial S)) ^ d)) = _
  rw [← mul_assoc, ← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial,
    MvPolynomial.monomial_eq]

private theorem optionRight_coeff_coeff {S σ : Type*} [CommRing S]
    (F : MvPolynomial (Option σ) S) (d : σ →₀ ℕ) (k : ℕ) :
    ((MvPolynomial.optionEquivRight S σ F).coeff d).coeff k =
      F.coeff (d.optionElim k) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add F H hF hH =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, hF, hH]
  | monomial e c =>
      rw [optionRight_monomial]
      have he : e = d.optionElim k ↔ e.some = d ∧ e none = k := by
        constructor
        · rintro rfl
          simp
        · rintro ⟨hs, hk⟩
          rw [← hs, ← hk, Finsupp.optionElim_some]
      by_cases hs : e.some = d <;> by_cases hk : e none = k <;>
        simp [MvPolynomial.coeff_monomial, Polynomial.coeff_monomial, he, hs, hk]

private theorem coeff_addRowParameter {S σ : Type*} [CommRing S]
    (f : S →+* Polynomial S) (F : MvPolynomial σ S) (d : σ →₀ ℕ) (k : ℕ) :
    (addRowParameter f F).coeff (d.optionElim k) = (f (F.coeff d)).coeff k := by
  have h : MvPolynomial.optionEquivRight S σ (addRowParameter f F) = MvPolynomial.map f F :=
    (MvPolynomial.optionEquivRight S σ).apply_symm_apply _
  rw [← optionRight_coeff_coeff (addRowParameter f F) d k, h, MvPolynomial.coeff_map]

private theorem map_letterMatrix {A B : Type*} [CommRing A] [CommRing B] {r : ℕ}
    (f : A →+* B) (a b : Fin r) (t : A) :
    (letterMatrix a b t).map f = letterMatrix a b (f t) := by
  apply Matrix.ext
  intro i j
  simp only [letterMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add, apply_ite, map_zero, map_one]
  split <;> simp_all

private theorem row_parameter_map_constants {R σ : Type*} [CommRing R] {r n : ℕ}
    (a b : Fin r) :
    (addRowParameter (σ := σ) (rowGen R (n := n) a b).toRingHom).comp
        (MvPolynomial.map MvPolynomial.C) =
      (MvPolynomial.map MvPolynomial.C).comp (MvPolynomial.rename Option.some).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    apply (MvPolynomial.optionEquivRight (RowPolynomial R r n) σ).injective
    simp [addRowParameter, MvPolynomial.optionEquivRight_C, rowGen, MvPolynomial.aeval_C] <;> rfl
  · intro v
    apply (MvPolynomial.optionEquivRight (RowPolynomial R r n) σ).injective
    simp [addRowParameter, MvPolynomial.optionEquivRight_X_some]

private theorem row_parameter_map_variables {R σ : Type*} [CommRing R] {r n : ℕ}
    (a b : Fin r) :
    ((rowVariables R r n).map (MvPolynomial.C (σ := σ))).map
        (addRowParameter (rowGen R (n := n) a b).toRingHom) =
      (letterMatrix a b (MvPolynomial.X (none : Option σ)))ᵀ *
        (rowVariables R r n).map MvPolynomial.C := by
  apply Matrix.ext
  intro i j
  apply (MvPolynomial.optionEquivRight (RowPolynomial R r n) σ).injective
  rw [letterMatrix_transpose_mul_apply]
  by_cases h : i = b <;>
    simp [h, addRowParameter, Matrix.map_apply, rowVariables, rowGen] <;> exact mul_comm _ _

theorem orderedEval_cons {R : Type*} [CommRing R] {r n : ℕ}
    (a : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) (F : RowPolynomial R r n) :
    orderedEval R (a :: w) F =
      addRowParameter (rowGen R (n := n) a.1 a.2.1).toRingHom (orderedEval R w F) := by
  let f := addRowParameter (σ := WordParameter w.length) (rowGen R (n := n) a.1 a.2.1).toRingHom
  have h : orderedEval R (n := n) (a :: w) = f.comp (orderedEval R w) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [orderedEval, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      apply (MvPolynomial.optionEquivRight (RowPolynomial R r n) (WordParameter w.length)).injective
      simp [f, addRowParameter, rowGen]
    · intro ij
      simp only [orderedEval, MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
      let ρ := (MvPolynomial.rename (R := R) (σ := WordParameter w.length) Option.some).toRingHom
      let φ := MvPolynomial.map (σ := WordParameter w.length)
        (MvPolynomial.C : R →+* RowPolynomial R r n)
      let ψ := MvPolynomial.map (σ := Option (WordParameter w.length))
        (MvPolynomial.C : R →+* RowPolynomial R r n)
      let W := orderedMatrix R w
      have hmap : ((W.map φ)ᵀ).map f = ((W.map ρ).map ψ)ᵀ := by
        apply Matrix.ext
        intro i j
        exact DFunLike.congr_fun (row_parameter_map_constants (R := R) (σ := WordParameter w.length)
          (n := n) a.1 a.2.1) (W j i)
      have hvars : ((rowVariables R r n).map
          (MvPolynomial.C (σ := WordParameter w.length))).map f =
          (letterMatrix a.1 a.2.1 (MvPolynomial.X (none : Option (WordParameter w.length))))ᵀ *
            (rowVariables R r n).map MvPolynomial.C :=
        row_parameter_map_variables (R := R) (σ := WordParameter w.length) (n := n) a.1 a.2.1
      have hm :
          (((letterMatrix a.1 a.2.1 (MvPolynomial.X (none : Option (WordParameter w.length))) *
                W.map ρ).map ψ)ᵀ * (rowVariables R r n).map MvPolynomial.C) =
            (((W.map φ)ᵀ * (rowVariables R r n).map MvPolynomial.C).map f) := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, map_letterMatrix, ψ,
          MvPolynomial.map_X, hmap, hvars, Matrix.mul_assoc]
      exact congrArg (fun M : Matrix (Fin r) (Fin n)
        (MvPolynomial (Option (WordParameter w.length)) (RowPolynomial R r n)) => M ij.1 ij.2) hm
  exact DFunLike.congr_fun h F

theorem orderedEval_nil {R : Type*} [CommRing R] {r n : ℕ} (F : RowPolynomial R r n) :
    orderedEval R ([] : List (Fin r × Fin r × ℕ)) F = MvPolynomial.C F := by
  have h : orderedEval R (n := n) ([] : List (Fin r × Fin r × ℕ)) = MvPolynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [orderedEval]
    · intro v
      simp [orderedEval, orderedMatrix, rowVariables, Matrix.map_one]
  exact DFunLike.congr_fun h F

/-- The actual right fold extracts the simultaneous coefficient of the ordered
symbolic product. Each letter, including a repeated or diagonal letter, uses an
independent parameter. -/
theorem applyWord_eq_ordered_coeff {R : Type*} [CommRing R] {r n : ℕ}
    (w : List (Fin r × Fin r × ℕ)) (F : RowPolynomial R r n) :
    applyWord R w F = (orderedEval R w F).coeff (wordExponent w) := by
  induction w with
  | nil =>
      change F = (orderedEval R ([] : List (Fin r × Fin r × ℕ)) F).coeff 0
      rw [orderedEval_nil (R := R) (r := r) (n := n) F, MvPolynomial.coeff_zero_C]
  | cons a w ih =>
      change (rowGen R a.1 a.2.1 (applyWord R w F)).coeff a.2.2 =
        (orderedEval R (a :: w) F).coeff ((wordExponent w).optionElim a.2.2)
      rw [ih, orderedEval_cons]
      exact (coeff_addRowParameter (rowGen R (n := n) a.1 a.2.1).toRingHom
        (orderedEval R w F) (wordExponent w) a.2.2).symm

theorem rowDiv_X_one {R : Type*} [CommRing R] {r n : ℕ} (a b i : Fin r) (j : Fin n) :
    rowDiv R a b 1 (MvPolynomial.X (i, j)) =
      if i = b then (MvPolynomial.X (a, j) : RowPolynomial R r n) else 0 := by
  by_cases h : i = b <;> simp [rowDiv, rowGen, h]

theorem rowDiv_diagonal_X_one {R : Type*} [CommRing R] {r n : ℕ} (a : Fin r) (j : Fin n) :
    rowDiv R a a 1 (MvPolynomial.X (a, j)) = (MvPolynomial.X (a, j) : RowPolynomial R r n) := by
  simp [rowDiv_X_one]

private theorem rowDiv_zero {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    rowDiv R (n := n) a b k 0 = 0 := by
  simp [rowDiv]

/-- Reversing the two elementary letters changes this coefficient. -/
theorem source_word_order_control (R : Type*) [CommRing R] :
    let x : RowPolynomial R 2 1 := MvPolynomial.X (0, 0)
    applyWord R [(0, 1, 1), (1, 0, 1)] x = x ∧
      applyWord R [(1, 0, 1), (0, 1, 1)] x = 0 := by
  simp [applyWord, rowDiv_X_one, rowDiv_zero]

end Formalism.GradedWeylDivisibility.TypeI
