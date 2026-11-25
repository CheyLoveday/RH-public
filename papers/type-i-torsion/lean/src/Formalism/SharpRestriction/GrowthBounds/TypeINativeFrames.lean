import Formalism.SharpRestriction.GrowthBounds.TypeIAdjacentNativeRow
import Formalism.SharpRestriction.GrowthBounds.TypeIMinorNormalization

open scoped BigOperators Matrix
open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

private def integralFrobenius {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) : G.P.W v →+* G.P.W v := by
  let f := algebraMap (G.P.W v) (G.P.Qq v)
  let F (a : G.P.W v) := a^p + (p : G.P.W v) * Classical.choose ((G.P.setting v).frob a)
  have h (a : G.P.W v) : f (F a) = G.P.σ v (f a) :=
    (Classical.choose_spec ((G.P.setting v).frob a)).symm
  letI := (G.P.setting v).frac_alt
  have hi := IsFractionRing.injective (G.P.W v) (G.P.Qq v)
  refine {toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_}
  · apply hi
    change f (F 1) = f 1
    simp only [h,map_one]
  · intro a b
    apply hi
    change f (F (a*b)) = f (F a * F b)
    simp only [h, map_mul]
  · apply hi
    change f (F 0) = f 0
    simp only [h, map_zero]
  · intro a b
    apply hi
    change f (F (a+b)) = f (F a + F b)
    simp only [h, map_add]

private theorem integralFrobenius_apply {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (a : G.P.W v) :
    algebraMap (G.P.W v) (G.P.Qq v) (integralFrobenius G v a) =
      G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) a) :=
  (Classical.choose_spec ((G.P.setting v).frob a)).symm

def integralFrobeniusIter {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) :
    ℕ → G.P.W v →+* G.P.W v
  | 0 => RingHom.id _
  | n+1 => (integralFrobenius G v).comp (integralFrobeniusIter G v n)

theorem integralFrobeniusIter_apply {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (n : ℕ)
    (a : G.P.W v) :
    algebraMap (G.P.W v) (G.P.Qq v) (integralFrobeniusIter G v n a) =
      (G.P.σ v ^ n) (algebraMap (G.P.W v) (G.P.Qq v) a) := by
  induction n with
  | zero => simp [integralFrobeniusIter]
  | succ n ih =>
    rw [integralFrobeniusIter, RingHom.comp_apply, integralFrobenius_apply, ih,
      pow_succ', RingAut.mul_apply]

/-- The actual rank-one predecessor has the same integral frame in each slot
after lifting the corresponding power of the given Frobenius. -/
theorem rank_one_predecessor_slot_frames {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (hr : G.P.r = 1) (L' : Submodule (G.P.W v) (Fin (G.P.m+1) → G.P.Qq v))
    (he : IsEdge p (G.P.n' v) G.P.r ⟨L',typeIStandardTuple G v⟩) :
    let φ := (algebraMap G.O G.Kf).comp (G.P.j v)
    ∃ g : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.W v), IsUnit g.det ∧
      ∀ s : Fin (G.P.n' v),
        let A := (g.map (integralFrobeniusIter G v s.val)).map φ * rankOnePole 0 (p : G.Kf)
        IsUnit A.det ∧ extO G.O (G.P.ι v) (G.P.σ v) s.val L' = colSpan G.O A := by
  intro φ
  classical
  obtain ⟨g,hg,hL⟩ := exists_integral_rankOne_edge_frame G v hr _ he rfl
  refine ⟨g,hg,?_⟩
  intro s A
  let f : G.P.W v →+* G.P.Qq v := algebraMap _ _
  let ψ : G.P.Qq v →+* G.Kf := (G.P.ι v).comp ((G.P.σ v ^ s.val : G.P.Qq v ≃+* G.P.Qq v) : _ →+* _)
  let B := g.map f * rankOneDiagonal (k := G.P.m+1) (p : G.P.Qq v)
  have hzero (i : Fin (G.P.m+1)) : i.val < 1 ↔ i = 0 := by
    constructor
    · intro h
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    · rintro rfl
      simp
  have hD : rankOneDiagonal (k := G.P.m+1) (p : G.P.Qq v) = rankOnePole 0 (p : G.P.Qq v) := by
    unfold rankOneDiagonal rankOnePole
    congr 1
    funext i
    simp only [hzero]
  have ht : la_tw (G.P.ι v) (G.P.σ v) s.val B = A := by
    change B.map ψ = _
    unfold B A
    rw [Matrix.map_mul]
    congr 1
    · apply Matrix.ext
      intro i j
      change G.P.ι v ((G.P.σ v ^ s.val) (f (g i j))) = φ (integralFrobeniusIter G v s.val (g i j))
      rw [← integralFrobeniusIter_apply G v s.val]
      exact (G.P.setting v).ι_comp _
    · apply Matrix.ext
      intro i j
      change ψ (rankOneDiagonal (k := G.P.m+1) (p : G.P.Qq v) i j) = _
      by_cases hij : i = j
      · subst j
        simp only [rankOneDiagonal, rankOnePole, Matrix.diagonal_apply_eq, hzero]
        by_cases hz : i = 0 <;> simp [hz]
      · simp [rankOneDiagonal, rankOnePole, Matrix.diagonal_apply, hij]
  have hunit : IsUnit A.det := by
    rw [← ht]
    have hdet : B.det ≠ 0 := by
      unfold B
      rw [hD, rank_one_frame_det]
      exact mul_ne_zero (kp_p_ne_zero G v ∘ fun h => by simpa using congrArg (G.P.ι v) h)
        ((show IsUnit (g.map f).det from (f.map_det g) ▸ hg.map f).ne_zero)
    exact la_tw_det _ _ _ _ (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨hunit,?_⟩
  change L' = colSpan (G.P.W v) B at hL
  rw [hL, la_extO_G, ht]

private theorem reduce_integralFrobenius_adjacent {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) (a : G.P.W v) :
    let q : G.P.W v →+* PrimeResidue (G.P.W v) p := Ideal.Quotient.mk (Ideal.span {(p : G.P.W v)})
    q (integralFrobeniusIter G v (posAdd s 1).val a) =
      q (integralFrobeniusIter G v s.val a)^p :=
  adjacent_integral_lifts_reduce G v s _ _
    _ (integralFrobeniusIter_apply G v s.val a).symm
    (integralFrobeniusIter_apply G v (posAdd s 1).val a).symm

/-- Both contractions reduce to zero on adjacent slots of a native integral
edge frame, including cyclic wrap. The flags may be polynomial matrices. -/
theorem native_adjacent_normalized_contractions_dvd {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) {σ : Type*}
    (g : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.W v)) (hg : IsUnit g.det)
    (X X' : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (MvPolynomial σ (G.P.W v))) :
    let W := G.P.W v
    let A := g * rankOnePole 0 (p : W)
    let d : W := ↑hg.unit⁻¹
    let U := d • A.adjugateᵀ
    let V := d • A
    let lift (t : Fin (G.P.n' v)) := (MvPolynomial.C : W →+* MvPolynomial σ W).comp
      (integralFrobeniusIter G v t.val)
    C (p : W) ∣ powerPair p ((U.map (lift s)) *ᵥ X.col 0)
        ((V.map (lift (posAdd s 1))) *ᵥ cofactorFlag X') ∧
      C (p : W) ∣ powerPair p ((V.map (lift s)) *ᵥ cofactorFlag X)
        ((U.map (lift (posAdd s 1))) *ᵥ X'.col 0) := by
  intro W A d U V lift
  classical
  have hA : A.det = (p : W) * g.det := rank_one_frame_det 0 _ _
  have hunit : d * g.det = 1 := by
    change (↑hg.unit⁻¹ : W) * g.det = 1
    calc
      (↑hg.unit⁻¹ : W) * g.det = (↑hg.unit⁻¹ : W) * ↑hg.unit :=
        congrArg ((↑hg.unit⁻¹ : W) * ·) hg.unit_spec.symm
      _ = 1 := by simp
  have hprod : Vᵀ * U = ((p : W) * d) • (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) W) :=
    normalized_pairing A (p : W) g.det d hA hunit
  let ρ : MvPolynomial σ W →+* MvPolynomial σ (PrimeResidue W p) := reduceCoefficients p
  let q : W →+* PrimeResidue W p := Ideal.Quotient.mk (Ideal.span {(p : W)})
  have hp : ρ (C (p : W)) = 0 := by
    have hq : q (p : W) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    change MvPolynomial.map q (C (p : W)) = 0
    rw [MvPolynomial.map_C, hq, map_zero]
  have hreduce : ((V.map (lift s))ᵀ * U.map (lift s)).map ρ = 0 := by
    change ((Vᵀ.map (lift s)) * U.map (lift s)).map ρ = 0
    rw [← Matrix.map_mul, hprod]
    apply Matrix.ext
    intro i j
    change ρ (lift s ((p : W) * d * (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) W) i j)) = _
    have hcast : lift s (p : W) = C (p : W) := by simp [lift]
    simp only [map_mul, hcast, hp, zero_mul, Matrix.zero_apply]
  have hnext (a : W) : ρ (lift (posAdd s 1) a) = ρ (lift s a)^p := by
    change MvPolynomial.map q (C (integralFrobeniusIter G v (posAdd s 1).val a)) =
      (MvPolynomial.map q (C (integralFrobeniusIter G v s.val a)))^p
    rw [MvPolynomial.map_C, MvPolynomial.map_C]
    exact (congrArg (MvPolynomial.C (σ := σ))
      (reduce_integralFrobenius_adjacent G v s a)).trans (map_pow _ _ _)
  exact adjacent_polynomial_contractions_dvd p (G.P.setting v).prime (G.P.setting v).p_unif.1
    (U.map (lift s)) (V.map (lift s)) (U.map (lift (posAdd s 1))) (V.map (lift (posAdd s 1)))
    (X.col 0) (cofactorFlag X) (X'.col 0) (cofactorFlag X')
    hreduce (fun i j => hnext (U i j)) (fun i j => hnext (V i j))

end

end GlobalTheory.EX.TypeIProduction
