import Formalism.GradedWeylDivisibility.TypeIFlagFrames
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators Matrix
open Matrix

namespace Formalism.GradedWeylDivisibility.TypeI

noncomputable section

private theorem card_minor_mul {n h : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin h) (Fin n) K) (B : Matrix (Fin n) (Fin h) K) :
    (A * B).det = ∑ J : FlagRows n h,
      (B.submatrix (J.1.orderEmbOfFin J.2) id).det *
        (A.submatrix id (J.1.orderEmbOfFin J.2)).det :=
  Formalism.HermitianLatticeCounting.P.ge_cauchyBinet A B

/-- A common rational denominator occurs in a single column. One copy of
the scalar therefore clears every chosen minor, including after flag substitution. -/
theorem scaled_rank_one_minor_has_lift {n h : ℕ} {W K : Type*} [CommRing W] [CommRing K]
    (f : W →+* K) (p : W) (u : Kˣ) (hu : f p = ↑u) (o : Fin n)
    (A X : Matrix (Fin n) (Fin n) W) (hh : h ≤ n) (I : FlagRows n h) :
    ∃ c : W, f c = f p * flagMinor hh
      (A.map f * diagonal (fun j => if j = o then (↑u⁻¹ : K) else 1) * X.map f) I := by
  classical
  let a := A.submatrix (I.1.orderEmbOfFin I.2) id
  let b := X.submatrix id (Fin.castLE hh)
  let d : Fin n → K := fun j => if j = o then (↑u⁻¹ : K) else 1
  have hab : (A.map f * diagonal d * X.map f).submatrix
      (I.1.orderEmbOfFin I.2) (Fin.castLE hh) = (a.map f * diagonal d) * b.map f := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply, a, b, id_eq]
  change ∃ c : W, f c = f p * ((A.map f * diagonal d * X.map f).submatrix
    (I.1.orderEmbOfFin I.2) (Fin.castLE hh)).det
  rw [hab, card_minor_mul, Finset.mul_sum]
  let B (J : FlagRows n h) := (b.submatrix (J.1.orderEmbOfFin J.2) id).det
  let C (J : FlagRows n h) := (a.submatrix id (J.1.orderEmbOfFin J.2)).det
  refine ⟨∑ J : FlagRows n h, B J * (if o ∈ J.1 then C J else p * C J), ?_⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro J _
  let e := J.1.orderEmbOfFin J.2
  have he (j : Fin h) : e j ∈ J.1 := Finset.orderEmbOfFin_mem J.1 J.2 j
  have ha : (a.map f * diagonal d).submatrix id e =
      (a.submatrix id e).map f * diagonal (fun j => d (e j)) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, Matrix.map_apply, id_eq]
  have hb : (b.map f).submatrix e id = (b.submatrix e id).map f := rfl
  change f (B J * (if o ∈ J.1 then C J else p * C J)) =
    f p * (((b.map f).submatrix e id).det * ((a.map f * diagonal d).submatrix id e).det)
  have hdetB : ((b.submatrix e id).map f).det = f (B J) := (f.map_det _).symm
  have hdetC : ((a.submatrix id e).map f).det = f (C J) := (f.map_det _).symm
  rw [ha, hb, Matrix.det_mul, Matrix.det_diagonal, hdetB, hdetC, map_mul]
  change f (B J) * f (if o ∈ J.1 then C J else p * C J) =
    f p * (f (B J) * (f (C J) * ∏ j, d (e j)))
  by_cases ho : o ∈ J.1
  · let j := (J.1.orderIsoOfFin J.2).symm ⟨o,ho⟩
    have hj : e j = o := congrArg Subtype.val ((J.1.orderIsoOfFin J.2).apply_symm_apply ⟨o,ho⟩)
    have hprod : ∏ t, d (e t) = (↑u⁻¹ : K) := by
      rw [Fintype.prod_eq_single j]
      · simp [d, hj]
      · intro t hne
        have hnot : e t ≠ o := fun ht => hne (e.injective (ht.trans hj.symm))
        simp [d, hnot]
    rw [if_pos ho, hprod, hu]
    symm
    calc
      _ = (f (B J) * f (C J)) * ((↑u : K) * ↑u⁻¹) := by ring
      _ = _ := by simp
  · have hprod : ∏ t, d (e t) = 1 := by
      apply Finset.prod_eq_one
      intro t _
      have hne : e t ≠ o := fun ht => ho (ht ▸ he t)
      simp [d, hne]
    rw [if_neg ho, hprod, map_mul]
    ring

def lineRows {n : ℕ} (i : Fin n) : FlagRows n 1 :=
  ⟨{i}, Finset.card_singleton i⟩

def hyperplaneRows {m : ℕ} (i : Fin (m + 1)) : FlagRows (m + 1) m :=
  ⟨({i}ᶜ : Finset _), by simp [Finset.card_compl]⟩

theorem lineRows_minor_eq {m : ℕ} {K : Type*} [CommRing K]
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)) :
    flagMinor (by omega : 1 ≤ m + 1) X (lineRows i) = X i 0 := by
  unfold flagMinor
  rw [Matrix.det_fin_one]
  have hi : (lineRows i).1.orderEmbOfFin (lineRows i).2 0 = i := by
    have h := Finset.orderEmbOfFin_mem (lineRows i).1 (lineRows i).2 (0 : Fin 1)
    exact Finset.mem_singleton.mp h
  change X ((lineRows i).1.orderEmbOfFin (lineRows i).2 0) 0 = _
  rw [hi]

/-- The full vector of signed codimension-one minors of the same flag. -/
def cofactorFlag {m : ℕ} {K : Type*} [CommRing K]
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Fin (m + 1) → K :=
  fun i => X.adjugate (Fin.last m) i

theorem cofactorFlag_eq_signed_minor {m : ℕ} {K : Type*} [CommRing K]
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)) :
    cofactorFlag X i = (-1 : K) ^ (i.val + m) *
      flagMinor (Nat.le_succ m) X (hyperplaneRows i) := by
  unfold cofactorFlag flagMinor
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  congr 1
  congr 1
  apply Matrix.ext
  intro a b
  have hr : (hyperplaneRows i).1.orderEmbOfFin (hyperplaneRows i).2 = Fin.succAboveOrderEmb i :=
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb i
  simp only [Matrix.submatrix_apply, hr, Fin.succAboveOrderEmb_apply, Fin.succAbove_last]
  rfl

theorem cofactorFlag_mul {m : ℕ} {K : Type*} [CommRing K]
    (A X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    cofactorFlag (A * X) = A.adjugateᵀ *ᵥ cofactorFlag X := by
  funext i
  unfold cofactorFlag
  rw [Matrix.adjugate_mul_distrib, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The line and dual hyperplane frames are integral after taking one
rational scalar per labelled minor. The output is valid before taking any word coefficient. -/
theorem normalized_line_cofactor {m : ℕ} {W K R : Type*} [CommRing W] [Field K] [CommRing R]
    (f : W →+* K) (g : K →+* R) (p : W) (hp : f p ≠ 0) (d : Wˣ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) W) (hd : A.det = p * ↑d)
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    let B := ((A.map f)⁻¹ᵀ).map g
    g (f p) • (B * X).col 0 =
        ((↑d⁻¹ : W) • A.adjugateᵀ).map (g.comp f) *ᵥ X.col 0 ∧
      g (f p) • cofactorFlag (B * X) =
        ((↑d⁻¹ : W) • A).map (g.comp f) *ᵥ cofactorFlag X := by
  dsimp only
  let B := A.map f
  have hdB : B.det = f p * f ↑d := by
    have hp' : B.det = f A.det := (f.map_det A).symm
    rw [hp', hd, map_mul]
  have hu : f (↑d⁻¹ : W) * f ↑d = 1 := by rw [← map_mul]; simp
  have hdu : f (↑d : W) ≠ 0 := fun h => by simp [h] at hu
  have hB : IsUnit B.det := by
    rw [hdB]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero hp hdu)
  have hscalar : f p * B.det⁻¹ = f (↑d⁻¹ : W) := by
    rw [hdB, eq_inv_of_mul_eq_one_left hu, _root_.mul_inv_rev]
    field_simp
  have hinv : B⁻¹ = B.det⁻¹ • B.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  have hline : f p • B⁻¹ᵀ = ((↑d⁻¹ : W) • A.adjugateᵀ).map f := by
    rw [hinv, Matrix.transpose_smul, smul_smul, hscalar]
    apply Matrix.ext
    intro i j
    change f (↑d⁻¹ : W) * (A.map f).adjugate j i = f ((↑d⁻¹ : W) * A.adjugate j i)
    have hm : (A.map f).adjugate = A.adjugate.map f := (f.map_adjugate A).symm
    simp only [map_mul, hm, Matrix.map_apply]
  have hdetI : B⁻¹.det = B.det⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hadjI : B⁻¹.adjugate = B.det⁻¹ • B := by
    calc
      B⁻¹.adjugate = B⁻¹.adjugate * (B⁻¹ * B) := by rw [Matrix.nonsing_inv_mul B hB, mul_one]
      _ = B.det⁻¹ • B := by rw [← mul_assoc, Matrix.adjugate_mul, hdetI, Matrix.smul_mul, one_mul]
  have hdual : f p • (B⁻¹ᵀ).adjugateᵀ = ((↑d⁻¹ : W) • A).map f := by
    rw [← Matrix.adjugate_transpose, Matrix.transpose_transpose, hadjI, smul_smul, hscalar]
    apply Matrix.ext
    intro i j
    exact (f.map_mul _ _).symm
  let C := (B⁻¹ᵀ).map g
  have hline' : g (f p) • C = ((↑d⁻¹ : W) • A.adjugateᵀ).map (g.comp f) := by
    apply Matrix.ext
    intro i j
    exact (g.map_mul _ _).symm.trans (congrArg g (congrFun (congrFun hline i) j))
  have hdual' : g (f p) • C.adjugateᵀ = ((↑d⁻¹ : W) • A).map (g.comp f) := by
    have hmap : C.adjugate = (B⁻¹ᵀ).adjugate.map g :=
      (RingHom.map_adjugate g _).symm
    rw [hmap]
    apply Matrix.ext
    intro i j
    exact (g.map_mul _ _).symm.trans (congrArg g (congrFun (congrFun hdual i) j))
  constructor
  · change g (f p) • (C * X).col 0 = _
    have hc : (C * X).col 0 = C *ᵥ X.col 0 := rfl
    rw [hc, ← Matrix.smul_mulVec, hline']
  · change g (f p) • cofactorFlag (C * X) = _
    rw [cofactorFlag_mul, ← Matrix.smul_mulVec, hdual']

end

end Formalism.GradedWeylDivisibility.TypeI
