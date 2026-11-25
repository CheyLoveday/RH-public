import Formalism.GradedWeylDivisibility.TypeINormalizedFlags
import Formalism.SharpRestriction.GrowthBounds.TypeIWeylFrameSpan
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope

open scoped BigOperators Matrix
open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

theorem flagCopies_card_eq {m : ℕ} (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) :
    Fintype.card (FlagCopies ν) = ν 0 := by
  rw [Fintype.card_sigma]
  have h := congrArg (fun f : Fin (m+1) → ℕ => f 0) (hw_weight_eq ν hν)
  simpa only [Finset.sum_apply, Pi.smul_apply, initW, Fin.val_zero, Nat.zero_lt_succ,
    if_true, smul_eq_mul, mul_one, Fintype.card_fin] using h

def rankOnePole {n : ℕ} {K : Type*} [Zero K] [One K] (o : Fin n) (a : K) :
    Matrix (Fin n) (Fin n) K := diagonal fun i => if i = o then a else 1

theorem rank_one_frame_det {n : ℕ} {K : Type*} [CommRing K] (o : Fin n) (a : K)
    (g : Matrix (Fin n) (Fin n) K) :
    (g * rankOnePole o a).det = a * g.det := by
  rw [Matrix.det_mul, rankOnePole, Matrix.det_diagonal]
  have h : ∏ i : Fin n, (if i = o then a else 1) = a := by
    rw [Fintype.prod_eq_single o]
    · simp
    · intro i hi
      simp [hi]
  rw [h, mul_comm]

private theorem rankOnePole_inv {n : ℕ} {K : Type*} [Field K]
    (o : Fin n) (a : K) (ha : a ≠ 0) : (rankOnePole o a)⁻¹ = rankOnePole o a⁻¹ := by
  apply Matrix.inv_eq_left_inv
  unfold rankOnePole
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
  funext i
  by_cases hi : i = o <;> simp [hi, ha]

private theorem inv_map_matrix_of_isUnit {n : ℕ} {W K : Type*} [CommRing W] [Field K]
    (f : W →+* K) (B : Matrix (Fin n) (Fin n) W) (hB : IsUnit B.det) :
    (B.map f)⁻¹ = B⁻¹.map f := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul B hB, Matrix.map_one _ (map_zero _) (map_one _)]

/-- In the actual ordered word ring, a rational factor clears a minor of a
rank-one inverse-transpose frame. -/
theorem scaled_word_minor_has_lift {n h : ℕ} {W K : Type*} [CommRing W] [Field K]
    (f : W →+* K) (p : W) (hp : f p ≠ 0) (o : Fin n)
    (g : Matrix (Fin n) (Fin n) W) (hg : IsUnit g.det)
    (w : List (Fin n × Fin n × ℕ)) (hh : h ≤ n) (I : FlagRows n h) :
    let A := g.map f * rankOnePole o (f p)
    ∃ c : MvPolynomial (WordParameter w.length) W,
      MvPolynomial.map f c =
        MvPolynomial.C (f p) * flagMinor hh (wordFlag A⁻¹ᵀ w) I := by
  intro A
  let ψ : W →+* MvPolynomial (WordParameter w.length) W := MvPolynomial.C
  let φ : K →+* MvPolynomial (WordParameter w.length) K := MvPolynomial.C
  let q := MvPolynomial.map (σ := WordParameter w.length) f
  let up := Units.map φ.toMonoidHom (Units.mk0 (f p) hp)
  have hup : q (ψ p) = (↑up : MvPolynomial (WordParameter w.length) K) := MvPolynomial.map_C _ _
  have hinv : A⁻¹ᵀ = (g⁻¹ᵀ).map f * rankOnePole o (f p)⁻¹ := by
    change (g.map f * rankOnePole o (f p))⁻¹ᵀ = _
    rw [Matrix.mul_inv_rev, rankOnePole_inv o _ hp, Matrix.transpose_mul, inv_map_matrix_of_isUnit f g hg]
    simp only [rankOnePole, Matrix.diagonal_transpose]
    rfl
  obtain ⟨c,hc⟩ := scaled_rank_one_minor_has_lift q (ψ p) up hup o
    ((g⁻¹ᵀ).map ψ) (orderedMatrix W w) hh I
  have hG : ((g⁻¹ᵀ).map ψ).map q = ((g⁻¹ᵀ).map f).map φ := by
    apply Matrix.ext
    intro i j
    exact MvPolynomial.map_C f _
  have hU : (↑up⁻¹ : MvPolynomial (WordParameter w.length) K) = φ (f p)⁻¹ := rfl
  have hD : diagonal (fun j => if j = o then
        (↑up⁻¹ : MvPolynomial (WordParameter w.length) K) else 1) =
      (rankOnePole o (f p)⁻¹).map φ := by
    apply Matrix.ext
    intro i j
    simp only [rankOnePole, Matrix.map_apply, Matrix.diagonal_apply, apply_ite,
      map_one, map_zero, hU]
    by_cases hij : i = j
    · subst j
      by_cases hio : i = o <;> simp only [hio, ite_true, ite_false]
    · simp only [hij, ite_false]
  have hCp : q (ψ p) = MvPolynomial.C (f p) := MvPolynomial.map_C f p
  refine ⟨c,?_⟩
  rw [hc, hinv, wordFlag, Matrix.map_mul, map_orderedMatrix f w, hG, hD, hCp]

/-- The number of labelled factors accounts for the entire rational-prime
normalization after the determinant twist of the source slot. -/
theorem scaled_framed_word_coeff_has_lift {m : ℕ} {W K : Type*}
    [CommRing W] [Field K]
    (f : W →+* K) (p : W) (hp : f p ≠ 0) (o : Fin (m + 1))
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) W) (hg : IsUnit g.det)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : List (Fin (m + 1) × Fin (m + 1) × ℕ)) (I : FlagLabels (nuOf lam)) :
    let A := g.map f * rankOnePole o (f p)
    ∃ c : W, f c =
      (f p) ^ lam 0 * A.det ^ (-(lam (Fin.last m))) *
        (flagProducts (nuOf lam) (wordFlag A⁻¹ᵀ w) I).coeff (wordExponent w) := by
  classical
  intro A
  let ν := nuOf lam
  have hν : Antitone ν := fun i j hij => Int.toNat_le_toNat (by have := hlam hij; omega)
  have hN : (Fintype.card (FlagCopies ν) : ℤ) = lam 0 - lam (Fin.last m) := by
    rw [flagCopies_card_eq ν hν]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr (hlam (Fin.zero_le _)))
  let d := hg.unit
  let φ : K →+* MvPolynomial (WordParameter w.length) K := MvPolynomial.C
  have hd : f (↑d : W) ≠ 0 := (d.isUnit.map f).ne_zero
  have hdet : A.det = f p * f (↑d : W) := by
    dsimp [A,d]
    rw [rank_one_frame_det, ← show f g.det = (g.map f).det from f.map_det g]
  have hscalar :
      (f p)^lam 0 * A.det^(-(lam (Fin.last m))) =
        (f (↑d : W))^(-(lam (Fin.last m))) * (f p)^(Fintype.card (FlagCopies ν)) := by
    rw [hdet, mul_zpow]
    calc
      _ = (f (↑d : W))^(-(lam (Fin.last m))) *
          ((f p)^lam 0 * (f p)^(-(lam (Fin.last m)))) := by ring
      _ = _ := by rw [← zpow_add₀ hp, ← zpow_natCast, hN, sub_eq_add_neg]
  have hUnit :
      f (↑(d ^ (-(lam (Fin.last m)))) : W) = (f (↑d : W))^(-(lam (Fin.last m))) := by
    change (↑(Units.map f.toMonoidHom (d ^ (-(lam (Fin.last m))))) : K) = _
    rw [map_zpow]
    exact Units.val_zpow_eq_zpow_val _ _
  choose c hc using fun b : FlagCopies ν =>
    scaled_word_minor_has_lift f p hp o g hg w (Nat.succ_le_of_lt b.1.isLt) (I b)
  let J := ∏ b, c b
  have hpoly : MvPolynomial.map f J =
      φ ((f p)^(Fintype.card (FlagCopies ν))) * flagProducts ν (wordFlag A⁻¹ᵀ w) I := by
    unfold J flagProducts
    simp only [map_prod, hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, map_pow]
    rfl
  refine ⟨(↑(d ^ (-(lam (Fin.last m)))) : W) * J.coeff (wordExponent w),?_⟩
  rw [map_mul, hUnit, ← MvPolynomial.coeff_map, hpoly, MvPolynomial.coeff_C_mul, hscalar]
  rw [mul_assoc]

end

end GlobalTheory.EX.TypeIProduction
