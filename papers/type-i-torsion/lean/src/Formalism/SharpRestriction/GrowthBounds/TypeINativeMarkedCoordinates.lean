import Formalism.SharpRestriction.GrowthBounds.TypeIMarkedWeight

open scoped BigOperators Matrix
open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- The integral vectors in the adjacent Frobenius contraction are the
normalized marked coordinates of the actual inverse-transpose edge frame.
The polynomial flag is arbitrary and is reused across all its marked copies. -/
theorem normalized_native_marked_coordinates {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) {σ : Type*}
    (a : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.W v)) (ha : IsUnit a.det)
    (X : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (MvPolynomial σ (G.P.W v))) :
    let W := G.P.W v
    let f : W →+* G.Kf := (algebraMap G.O G.Kf).comp (G.P.j v)
    let q := MvPolynomial.map (σ := σ) f
    let A := a * rankOnePole 0 (p : W)
    let d : W := ↑ha.unit⁻¹
    let U := d • A.adjugateᵀ
    let V := d • A
    let φ := (MvPolynomial.C : W →+* MvPolynomial σ W).comp (integralFrobeniusIter G v s.val)
    let A' := (a.map (integralFrobeniusIter G v s.val)).map f * rankOnePole 0 (p : G.Kf)
    let frame := (A'⁻¹ᵀ).map (MvPolynomial.C : G.Kf →+* MvPolynomial σ G.Kf) * X.map q
    (∀ i, q ((U.map φ *ᵥ X.col 0) i) = C (p : G.Kf) * frame i 0) ∧
      (∀ i, q ((V.map φ *ᵥ cofactorFlag X) i) = C (p : G.Kf) * cofactorFlag frame i) := by
  classical
  intro W f q A d U V φ A' frame
  let F := integralFrobeniusIter G v s.val
  let c : G.Kf →+* MvPolynomial σ G.Kf := MvPolynomial.C
  let Aₛ := A.map F
  let u := Units.map F.toMonoidHom ha.unit
  have ha₀ : A.det = (p : W) * (ha.unit : W) := by
    change (a * rankOnePole 0 (p : W)).det = _
    rw [rank_one_frame_det,IsUnit.unit_spec]
  have hp : f (p : W) = (p : G.Kf) := map_natCast f p
  have hAₛ : Aₛ.det = (p : W) * (u : W) := by
    calc
      Aₛ.det = F A.det := (F.map_det A).symm
      _ = (p : W) * (u : W) := by
        rw [ha₀,map_mul,map_natCast]
        rfl
  have hPole : (rankOnePole (0 : Fin (G.P.m+1)) (p : W)).map (f.comp F) =
      rankOnePole 0 (p : G.Kf) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = 0 <;> simp [rankOnePole, Matrix.diagonal_apply,hi]
    · simp [rankOnePole, Matrix.diagonal_apply,hij]
  have hFrame : Aₛ.map f = A' := by
    change ((a * rankOnePole 0 (p : W)).map F).map f =
      (a.map F).map f * rankOnePole 0 (p : G.Kf)
    rw [Matrix.map_mul,Matrix.map_mul]
    exact congrArg (fun B => (a.map F).map f * B) hPole
  have hpK : (p : G.Kf) ≠ 0 := by simpa only [map_natCast] using kp_p_ne_zero G v
  obtain ⟨hLine,hDual⟩ := normalized_line_cofactor f c (p : W)
    (hp.symm ▸ hpK) u Aₛ hAₛ (X.map q)
  have hU : (U.map φ).map q = ((↑u⁻¹ : W) • Aₛ.adjugateᵀ).map (c.comp f) := by
    apply Matrix.ext
    intro i j
    change q (C (F (d * A.adjugate j i))) = C (f ((↑u⁻¹ : W) * Aₛ.adjugate j i))
    have hv : F (A.adjugate j i) = Aₛ.adjugate j i :=
      congrArg (fun M => M j i) (F.map_adjugate A)
    rw [show q = MvPolynomial.map f from rfl, MvPolynomial.map_C, map_mul F, hv]
    rfl
  have hV : (V.map φ).map q = ((↑u⁻¹ : W) • Aₛ).map (c.comp f) := by
    apply Matrix.ext
    intro i j
    change q (C (F (d * A i j))) = C (f ((↑u⁻¹ : W) * (A.map F) i j))
    rw [show q = MvPolynomial.map f from rfl, MvPolynomial.map_C, map_mul F]
    rfl
  have hC : (fun i => q (cofactorFlag X i)) = cofactorFlag (X.map q) := by
    funext i
    change q (X.adjugate (Fin.last G.P.m) i) = (X.map q).adjugate (Fin.last G.P.m) i
    exact congrArg (fun M => M (Fin.last G.P.m) i) (q.map_adjugate X)
  constructor
  · intro i
    have h := congrFun hLine i
    rw [hFrame,hp] at h
    change C (p : G.Kf) * frame i 0 = _ at h
    rw [RingHom.map_mulVec,hU]
    exact h.symm
  · intro i
    have h := congrFun hDual i
    rw [hFrame,hp] at h
    change C (p : G.Kf) * cofactorFlag frame i = _ at h
    rw [RingHom.map_mulVec,hV]
    change ((_ *ᵥ fun i => q (cofactorFlag X i)) i) = _
    rw [hC]
    exact h.symm

end

end GlobalTheory.EX.TypeIProduction
