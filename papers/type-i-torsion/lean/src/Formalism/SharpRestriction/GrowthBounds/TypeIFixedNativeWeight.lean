import Formalism.SharpRestriction.GrowthBounds.TypeINativeMarkedCoordinates
import Formalism.GradedWeylDivisibility.TypeIPackedWordMinors
import Mathlib.Algebra.Ring.ULift

open scoped BigOperators Matrix Classical
open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

universe u

abbrev NativeFlatRows {p : ℕ} (G : GAtP p) :=
  (b : NativeMinorLabel G) → FlagRows (G.P.m+1) (b.2.1.val+1)

/-- A single integer weight works on the standard shear and on every
integral lift of the complete normalized products at the chosen orbit.
Each X is the shared polynomial flag in its source slot. -/
theorem exists_fixed_native_weight {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) (R : ℕ) (hm : 0 < G.P.m)
    (hc : TypeIAdjacentCapacity G v s R) :
    let s₀ : NativeFlagSlot G := ⟨v,s⟩
    let s₁ : NativeFlagSlot G := ⟨v,posAdd s 1⟩
    let line := if IsTypeV s then s₀ else s₁
    ∃ l : NativeFlatRows G → ℤ,
      (let X₀ (b : NativeFlagSlot G) : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf :=
          if b = line then lineShear G.Kf 1 else 1
       ∑ I : NativeFlatRows G, (l I : G.Kf) *
         ∏ b : NativeMinorLabel G, flagMinor (Nat.succ_le_of_lt b.2.1.isLt) (X₀ b.1) (I b) = 1) ∧
      ∀ {σ : Type u} (a : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.W v)) (ha : IsUnit a.det)
        (X : NativeFlagSlot G → Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (MvPolynomial σ (G.P.W v))),
        let W := G.P.W v
        let f : W →+* G.Kf := (algebraMap G.O G.Kf).comp (G.P.j v)
        let q := MvPolynomial.map (σ := σ) f
        let frame (b : NativeFlagSlot G) :
            Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (MvPolynomial σ G.Kf) :=
          if h : b.1 = v then
            (((a.map (integralFrobeniusIter G v b.2.val)).map f * rankOnePole 0 (p : G.Kf))⁻¹ᵀ).map
              (MvPolynomial.C : G.Kf →+* MvPolynomial σ G.Kf) * (X b).map q
          else (X b).map q
        let scale (b : NativeFlagSlot G) : MvPolynomial σ G.Kf := if b.1 = v then C (p : G.Kf) else 1
        ∀ (F : (b : NativeMinorLabel G) →
            FlagRows (G.P.m+1) (b.2.1.val+1) → MvPolynomial σ W),
          Function.Injective q →
          (∀ b I, q (F b I) = scale b.1 * flagMinor (Nat.succ_le_of_lt b.2.1.isLt) (frame b.1) I) →
          (C (p : W))^R ∣ ∑ I : NativeFlatRows G, (l I : MvPolynomial σ W) * ∏ b, F b (I b) := by
  classical
  intro s₀ s₁ line
  have hp : p ≠ 0 := (G.P.setting v).prime.ne_zero
  have hne : s₀ ≠ s₁ := by
    intro h
    exact adjacent_native_slots_ne G v s (eq_of_heq (Sigma.mk.inj h).2)
  obtain ⟨e,he₀,he₁,hLeft,hRight⟩ := choose_marked_native_heights G v s R hm hc
  let b := decide (IsTypeV s)
  obtain ⟨l, hl⟩ := exists_fixed_marked_minor_weight
    (fun j : NativeMinorLabel G => j.2.1.val+1) (fun j => Nat.succ_le_of_lt j.2.1.isLt)
    Sigma.fst s₀ s₁ p R b e he₀ he₁
    (by simpa [b] using hLeft) (by
      by_cases hs : IsTypeV s
      · simpa [b,hs] using hRight
      · simpa [b,hs] using hRight)
  have hDec : (fun a b : NativeMinorLabel G => Classical.propDecidable (a = b)) =
      (fun a b : NativeMinorLabel G => Sigma.instDecidableEqSigma a b) :=
    Subsingleton.elim _ _
  refine ⟨l,?_,?_⟩
  · intro X₀
    let U := ULift.{u} G.Kf
    let XU (j : NativeFlagSlot G) : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) U :=
      if j = line then lineShear U 1 else 1
    let down : U →+* G.Kf := {
      toFun := ULift.down
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    have hmap (j : NativeFlagSlot G) : (XU j).map down = X₀ j := by
      by_cases hj : j = line
      · apply Matrix.ext
        intro i k
        by_cases hik : i = k <;> by_cases hi : Fin.last G.P.m = i <;>
          by_cases hk : (0 : Fin (G.P.m+1)) = k <;>
          simp [XU,X₀,hj,letterMatrix,Matrix.one_apply,Matrix.single_apply,hik,hi,hk]
      · simp [XU,X₀,hj,Matrix.map_one _ (map_zero _) (map_one _)]
    suffices hsum : (∑ I : NativeFlatRows G, (l I : U) *
        ∏ j : NativeMinorLabel G,
          flagMinor (Nat.succ_le_of_lt j.2.1.isLt) (XU j.1) (I j)) = 1 by
      simpa only [map_sum,map_prod,map_mul,map_intCast,map_one,map_flagMinor,hmap] using congrArg down hsum
    let F (j : NativeMinorLabel G) (I : FlagRows _ (j.2.1.val+1)) :=
      flagMinor (Nat.succ_le_of_lt j.2.1.isLt) (XU j.1) I
    let x (i : Fin (G.P.m+1)) := if b then XU s₀ i 0 else cofactorFlag (XU s₀) i
    let y (i : Fin (G.P.m+1)) := if !b then XU s₁ i 0 else cofactorFlag (XU s₁) i
    have hF (j : NativeMinorLabel G) (I : FlagRows _ (j.2.1.val+1)) :
        F j I = (1 : U) * flagMinor (Nat.succ_le_of_lt j.2.1.isLt) (XU j.1) I := by
      simp only [F,one_mul]
    have hEq := hl (RingHom.id U) Function.injective_id XU (fun _ => 1) F x y
      (fun j I => hF j I) (fun i => (one_mul (x i)).symm) (fun i => (one_mul (y i)).symm)
    change (∑ I, (l I : U) * ∏ j : NativeMinorLabel G, F j (I j)) = 1
    rw [hDec] at hEq
    refine hEq.trans ?_
    have hPair : powerPair p x y = 1 := by
      obtain ⟨hl₀,hl₁⟩ := unit_letter_line_pairings hm p hp (1 : U)
      have hcol : (lineShear (m := G.P.m) U 1).col 0 = (fun i => lineShear U 1 i 0) := rfl
      rw [hcol] at hl₀ hl₁
      by_cases hs : IsTypeV s
      · simpa [x,y,XU,b,line,hs,hne.symm] using hl₀
      · simpa [x,y,XU,b,line,hs,hne] using hl₁
    have hDefault (j : NativeMinorLabel G) :
        F j (standardFlagRows (Nat.succ_le_of_lt j.2.1.isLt)) = 1 := by
      by_cases hj : j.1 = line
      · simpa [F,XU,hj] using unit_letter_leading_minor hm (Nat.succ_le_of_lt j.2.1.isLt) (1 : U)
      · simpa [F,XU,hj] using standardFlagMinor_eq_one
          (K := U) (Nat.succ_le_of_lt j.2.1.isLt)
    simp only [hPair,one_pow,hDefault,Finset.prod_const_one,mul_one]
  · intro σ a ha X W f q frame scale F hq hF
    let A := a * rankOnePole 0 (p : W)
    let d : W := ↑ha.unit⁻¹
    let U := d • A.adjugateᵀ
    let V := d • A
    let lift (t : Fin (G.P.n' v)) :=
      (MvPolynomial.C : W →+* MvPolynomial σ W).comp (integralFrobeniusIter G v t.val)
    let x := if b then U.map (lift s) *ᵥ (X s₀).col 0 else V.map (lift s) *ᵥ cofactorFlag (X s₀)
    let y := if !b then U.map (lift (posAdd s 1)) *ᵥ (X s₁).col 0
      else V.map (lift (posAdd s 1)) *ᵥ cofactorFlag (X s₁)
    have hX := normalized_native_marked_coordinates G v s a ha (X s₀)
    have hY := normalized_native_marked_coordinates G v (posAdd s 1) a ha (X s₁)
    have hPair := native_adjacent_normalized_contractions_dvd G v s a ha (X s₀) (X s₁)
    have hx (i : Fin (G.P.m+1)) :
        q (x i) = scale s₀ * (if b then frame s₀ i 0 else cofactorFlag (frame s₀) i) := by
      by_cases hs : IsTypeV s
      · simpa [x,b,hs,scale,frame,s₀,W,f,q,lift,U,V,A,d] using hX.1 i
      · simpa [x,b,hs,scale,frame,s₀,W,f,q,lift,U,V,A,d] using hX.2 i
    have hy (i : Fin (G.P.m+1)) :
        q (y i) = scale s₁ * (if !b then frame s₁ i 0 else cofactorFlag (frame s₁) i) := by
      by_cases hs : IsTypeV s
      · simpa [y,b,hs,scale,frame,s₁,W,f,q,lift,U,V,A,d] using hY.2 i
      · simpa [y,b,hs,scale,frame,s₁,W,f,q,lift,U,V,A,d] using hY.1 i
    have hsum := hl q hq frame scale F x y hF hx hy
    rw [hDec] at hsum
    have hDvd : C (p : W) ∣ powerPair p x y := by
      by_cases hs : IsTypeV s
      · simpa [x,y,b,hs,W,lift,U,V,A,d] using hPair.1
      · simpa [x,y,b,hs,W,lift,U,V,A,d] using hPair.2
    refine (congrArg (fun z => (C (p : W))^R ∣ z) hsum).mpr ?_
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hDvd R) _

end

end GlobalTheory.EX.TypeIProduction
