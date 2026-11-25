import Formalism.SharpRestriction.GrowthBounds.TypeINativeCoefficient
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCZ

open scoped BigOperators Matrix Classical
open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

theorem standard_slot_frame {p : ℕ} (G : GAtP p) (u : Fin G.P.nV) (s : Fin (G.P.n' u)) :
    extO G.O (G.P.ι u) (G.P.σ u) s.val (typeIStandardTuple G u) =
      colSpan G.O (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf) := by
  rw [typeIStandardTuple, la_extO_G]
  have h : la_tw (G.P.ι u) (G.P.σ u) s.val
      (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.Qq u)) = 1 := by
    unfold la_tw
    exact map_one _
  rw [h]

/-- The integer-labelled reader is integral on the genuine standard lattice
and on every normalized incoming rank-one generator, with the full source
ArV scalar and all determinant twists accounted for. -/
theorem native_row_on_normalized_incoming_generators {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (hr : G.P.r = 1) (l : NativeFlagLabels G → ℤ) :
    ∃ (Λ : G.P.Xsp →ₗ[G.Kf] G.Kf)
      (row : ↥(G.P.HtupW (typeIStandardTuple G)) →ₗ[G.O] G.O),
      (∀ F : ↥(G.P.HtupW (typeIStandardTuple G)), algebraMap G.O G.Kf (row F) = Λ F.1) ∧
      ∀ L' (_ : IsEdge p (G.P.n' v) G.P.r ⟨L',typeIStandardTuple G v⟩),
        ∀ F ∈ G.P.HtupW (Function.update (typeIStandardTuple G) v L'),
          Λ (((p : G.Kf)^G.P.ArV v) • F) ∈ Set.range (algebraMap G.O G.Kf) := by
  classical
  haveI : IsFractionRing G.O G.Kf := (G.P.setting v).frac_O
  haveI : CharZero G.Kf :=
    (Formalism.MainNotions.ColumnSystems.Pf.settingCZ p (G.P.n' v) (G.P.W v) (G.P.Qq v)
      G.O G.Kf (G.P.ι v) (G.P.σ v) (G.P.j v) G.P.w (G.P.setting v)).1
  obtain ⟨Λ,row,hrow,hformula⟩ := exists_native_integral_label_row G l
  refine ⟨Λ,row,hrow,?_⟩
  intro L' he
  let f := algebraMap G.O G.Kf
  let j := G.P.j v
  let φ := f.comp j
  obtain ⟨a,ha,hA⟩ := rank_one_predecessor_slot_frames G v hr L' he
  let framesAt (s : Fin (G.P.n' v)) :=
    (a.map (integralFrobeniusIter G v s.val)).map φ * rankOnePole 0 (p : G.Kf)
  let g : ∀ u : Fin G.P.nV, Fin (G.P.n' u) → Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf :=
    Function.update (fun _ _ => 1) v framesAt
  have hg (u : Fin G.P.nV) (s : Fin (G.P.n' u)) :
      IsUnit (g u s).det ∧ extO G.O (G.P.ι u) (G.P.σ u) s.val
        (Function.update (typeIStandardTuple G) v L' u) = colSpan G.O (g u s) := by
    by_cases hu : u = v
    · subst u
      have htu : Function.update (typeIStandardTuple G) v L' v = L' := Function.update_self _ _ _
      rw [htu]
      simpa only [g, Function.update_self, framesAt, φ, f, j] using hA s
    · have htu : Function.update (typeIStandardTuple G) v L' u = typeIStandardTuple G u :=
        Function.update_of_ne hu _ _
      rw [htu]
      simpa only [g, Function.update_of_ne hu, Matrix.det_one, isUnit_one, true_and] using
        standard_slot_frame G u s
  have hSpan := HtupW_eq_span_framed_words G (Function.update (typeIStandardTuple G) v L') g
    (fun u s => (hg u s).1) (fun u s => (hg u s).2)
  let r : G.Kf := (p : G.Kf)^G.P.ArV v
  let Ψ := (r • Λ).restrictScalars G.O
  have hspan : Submodule.span G.O (Set.range (framedTupleWord G g)) ≤
      (Algebra.linearMap G.O G.Kf).range.comap Ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨w,rfl⟩
    change r * Λ (framedTupleWord G g w) ∈ (Algebra.linearMap G.O G.Kf).range
    rw [hformula]
    let power (b : NativeFlagSlot G) : G.Kf :=
      if b.1 = v then (p : G.Kf)^(lamAt (G.P.lam0 b.1) b.2 0) else 1
    let twist (b : NativeFlagSlot G) : G.Kf :=
      (g b.1 b.2).det ^ (-(lamAt (G.P.lam0 b.1) b.2 (Fin.last G.P.m)))
    let val (b : NativeFlagSlot G) (I : FlagLabels (NativeFlagWeight G b)) :=
      (flagProducts (NativeFlagWeight G b) (wordFlag (g b.1 b.2)⁻¹ᵀ (w b.1 b.2)) I).coeff
        (wordExponent (w b.1 b.2))
    have hp : (p : G.Kf) ≠ 0 := by simpa only [map_natCast] using kp_p_ne_zero G v
    have hsum (s : Finset (Fin (G.P.n' v))) :
        (∏ t ∈ s, (p : G.Kf)^(lamAt (G.P.lam0 v) t 0)) =
          (p : G.Kf)^(∑ t ∈ s, lamAt (G.P.lam0 v) t 0) := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hp]
    have hpow : (∏ b, power b) = r := by
      unfold power r
      rw [Fintype.prod_sigma, Fintype.prod_eq_single v]
      · simp only [ite_true, arV_rankOne_eq_sum_first G v hr]
        exact hsum _
      · intro u hu
        simp [hu]
    have hcoeff (b : NativeFlagSlot G) (I : FlagLabels (NativeFlagWeight G b)) :
        ∃ c : G.O, f c = power b * twist b * val b I := by
      obtain ⟨u,s⟩ := b
      by_cases hu : u = v
      · subst u
        let a' := a.map (integralFrobeniusIter G v s.val)
        have hdet : IsUnit a'.det := by
          have h := (integralFrobeniusIter G v s.val).map_det a
          exact h ▸ ha.map _
        have hpφ : φ (p : G.P.W v) = (p : G.Kf) := map_natCast φ p
        obtain ⟨c,hc⟩ := scaled_framed_word_coeff_has_lift φ (p : G.P.W v)
          (hpφ.symm ▸ hp) 0 a' hdet (lamAt (G.P.lam0 v) s)
          (kp_lamAt_antitone _ (G.P.dom v) s) (w v s) I
        refine ⟨j c,?_⟩
        change φ c = _
        simpa only [power,twist,val,g,Function.update_self,framesAt,a',ite_true,hpφ] using hc
      · let u0 := (flagProducts (NativeFlagWeight G ⟨u,s⟩) (orderedMatrix G.O (w u s)) I).coeff
          (wordExponent (w u s))
        refine ⟨u0,?_⟩
        have hone : (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)⁻¹ = 1 :=
          Matrix.inv_eq_left_inv (by simp)
        simp only [power, twist, val, g, Function.update_of_ne hu, hu, ite_false, Matrix.det_one,
          _root_.one_zpow, one_mul, hone, Matrix.transpose_one, wordFlag,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
        dsimp only [u0]
        rw [← MvPolynomial.coeff_map, map_flagProducts, map_orderedMatrix]
    choose c hc using hcoeff
    refine ⟨∑ I : NativeFlagLabels G, (l I : G.O) * ∏ b, c b (I b),?_⟩
    change f _ = r * ((∏ b, twist b) * ∑ I : NativeFlagLabels G,
      (l I : G.Kf) * ∏ b, val b (I b))
    simp only [map_sum,map_mul,map_intCast,map_prod,hc,Finset.prod_mul_distrib,hpow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    ring
  intro F hF
  rw [hSpan] at hF
  have h := hspan hF
  change (r • Λ) F ∈ LinearMap.range (Algebra.linearMap G.O G.Kf) at h
  obtain ⟨b,hb⟩ := h
  refine ⟨b,?_⟩
  change algebraMap G.O G.Kf b = r • Λ F at hb
  simpa only [r, map_smul] using hb

end

end GlobalTheory.EX.TypeIProduction
