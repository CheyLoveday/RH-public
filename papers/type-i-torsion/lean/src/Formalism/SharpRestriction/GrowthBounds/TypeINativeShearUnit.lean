import Formalism.SharpRestriction.GrowthBounds.TypeIFixedNativeWeight

open scoped BigOperators Matrix Classical
open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- A constant integral change of frame in the line slot. Its inverse
transpose is the unit-producing shear. -/
def constantShearFrame {p : ℕ} (G : GAtP p) (line : NativeFlagSlot G)
    (u : Fin G.P.nV) (s : Fin (G.P.n' u)) :
    Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf :=
  if (⟨u,s⟩ : NativeFlagSlot G) = line then Matrix.transvection 0 (Fin.last G.P.m) (-1) else 1

theorem constant_shear_frames {p : ℕ} (G : GAtP p) (line : NativeFlagSlot G)
    (hm : 0 < G.P.m) :
    let g := constantShearFrame G line
    (∀ u s, (g u s).det = 1) ∧
    (∀ u s, extO G.O (G.P.ι u) (G.P.σ u) s.val (typeIStandardTuple G u) =
      colSpan G.O (g u s)) ∧
    ∀ b : NativeFlagSlot G, (g b.1 b.2)⁻¹ᵀ =
      if b = line then lineShear G.Kf 1 else 1 := by
  classical
  intro g
  have hn : (0 : Fin (G.P.m+1)) ≠ Fin.last G.P.m := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero,Fin.val_last] at hv
    omega
  let B : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf := Matrix.transvection 0 (Fin.last G.P.m) (-1)
  let C : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf := Matrix.transvection 0 (Fin.last G.P.m) 1
  have hInv : B * C = 1 := by
    unfold B C
    rw [Matrix.transvection_mul_transvection_same _ _ hn]
    simp
  have hInv' : B⁻¹ = C := Matrix.inv_eq_right_inv hInv
  have hTrans : Cᵀ = lineShear G.Kf 1 := by
    dsimp only [C]
    rw [Matrix.transvection,Matrix.transpose_add,Matrix.transpose_one,Matrix.transpose_single]
    rfl
  have hEnt (c : G.O) (i j : Fin (G.P.m+1)) :
      Matrix.transvection 0 (Fin.last G.P.m) (algebraMap G.O G.Kf c) i j ∈
        Set.range (algebraMap G.O G.Kf) := by
    refine ⟨Matrix.transvection 0 (Fin.last G.P.m) c i j,?_⟩
    by_cases he : i = j <;> by_cases hi : (0 : Fin (G.P.m+1)) = i <;>
      by_cases hj : Fin.last G.P.m = j <;>
      simp [Matrix.transvection,Matrix.single_apply,he,hi,hj]
    all_goals split <;> simp [*]
  have hLe (A D : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)
      (hD : ∀ i j, D i j ∈ Set.range (algebraMap G.O G.Kf)) :
      colSpan G.O (A * D) ≤ colSpan G.O A := by
    unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨j,rfl⟩
    choose z hz using hD
    have hcol : (fun i => (A * D) i j) = ∑ k, z k j • (fun i => A i k) := by
      funext i
      rw [Finset.sum_apply,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Pi.smul_apply,Algebra.smul_def,hz,mul_comm]
    change (fun i => (A * D) i j) ∈ _
    rw [hcol]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩)
  have hSpan : colSpan G.O B = colSpan G.O (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf) := by
    apply le_antisymm
    · have h := hLe 1 B (fun i j => by simpa [B] using hEnt (-1) i j)
      simpa only [Matrix.one_mul] using h
    · have h := hLe B C (fun i j => by simpa [C] using hEnt 1 i j)
      simpa only [hInv] using h
  refine ⟨?_,?_,?_⟩
  · intro u s
    by_cases hs : (⟨u,s⟩ : NativeFlagSlot G) = line
    · simpa [g,constantShearFrame,hs] using Matrix.det_transvection_of_ne _ _ hn (-1 : G.Kf)
    · simp [g,constantShearFrame,hs]
  · intro u s
    rw [standard_slot_frame G u s]
    by_cases hs : (⟨u,s⟩ : NativeFlagSlot G) = line
    · simpa [g,constantShearFrame,hs,B] using hSpan.symm
    · simp [g,constantShearFrame,hs]
  · rintro ⟨u,s⟩
    by_cases hs : (⟨u,s⟩ : NativeFlagSlot G) = line
    · simpa [g,constantShearFrame,hs,B,hInv'] using hTrans
    · simp [g,constantShearFrame,hs]

/-- At empty literal words the labelled readout of the constant shear is
the exact product of the corresponding scalar minors. -/
theorem native_constant_shear_word_coefficient {p : ℕ} (G : GAtP p)
    (line : NativeFlagSlot G) (hm : 0 < G.P.m) (b : NativeFlagSlot G)
    (I : FlagLabels (NativeFlagWeight G b)) :
    let U : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf :=
      if b = line then lineShear G.Kf 1 else 1
    (flagProducts (NativeFlagWeight G b) (wordFlag (constantShearFrame G line b.1 b.2)⁻¹ᵀ []) I).coeff
      (wordExponent ([] : List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ))) =
      flagProducts (NativeFlagWeight G b) U I := by
  intro U
  have h := (constant_shear_frames G line hm).2.2 b
  rw [h,wordFlag]
  change (flagProducts (NativeFlagWeight G b) (U.map MvPolynomial.C * 1) I).coeff 0 = _
  rw [Matrix.mul_one, ← map_flagProducts]
  simp

end

end GlobalTheory.EX.TypeIProduction
