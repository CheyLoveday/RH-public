import Formalism.SharpRestriction.GrowthBounds.TypeICommonWordReadout

open scoped BigOperators Matrix Classical
open Matrix
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- One depth-R coefficient row, with a native unit and rational-prime
divisibility on the whole normalized incoming rank-one lattice. -/
theorem exists_native_typeI_separating_row {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) (R : ℕ) (hm : 0 < G.P.m) (hr : G.P.r = 1)
    (hc : TypeIAdjacentCapacity G v s R) :
    ∃ (Λ : G.P.Xsp →ₗ[G.Kf] G.Kf)
      (row : ↥(G.P.HtupW (typeIStandardTuple G)) →ₗ[G.O] G.O),
      (∀ F : ↥(G.P.HtupW (typeIStandardTuple G)), algebraMap G.O G.Kf (row F) = Λ F.1) ∧
      (∃ F : ↥(G.P.HtupW (typeIStandardTuple G)), row F = 1) ∧
      ∀ L' (_ : IsEdge p (G.P.n' v) G.P.r ⟨L',typeIStandardTuple G v⟩),
        ∀ F ∈ G.P.HtupW (Function.update (typeIStandardTuple G) v L'),
          Λ (((p : G.Kf)^G.P.ArV v) • F) ∈
            (algebraMap G.O G.Kf '' (Ideal.span {(p : G.O)^R} : Set G.O)) := by
  classical
  haveI : IsFractionRing G.O G.Kf := (G.P.setting v).frac_O
  haveI : CharZero G.Kf :=
    (Formalism.MainNotions.ColumnSystems.Pf.settingCZ p (G.P.n' v) (G.P.W v) (G.P.Qq v)
      G.O G.Kf (G.P.ι v) (G.P.σ v) (G.P.j v) G.P.w (G.P.setting v)).1
  let line : NativeFlagSlot G := if IsTypeV s then ⟨v,s⟩ else ⟨v,posAdd s 1⟩
  obtain ⟨l,hUnit,hDvd⟩ := exists_common_word_readout G v s R hm hc
  obtain ⟨Λ,row,hrow,hword⟩ := exists_native_integral_label_row G l
  refine ⟨Λ,row,hrow,?_,?_⟩
  · let g := constantShearFrame G line
    let w : NativeWords G := fun _ _ => []
    have hG := constant_shear_frames G line hm
    have hSpan := HtupW_eq_span_framed_words G (typeIStandardTuple G) g
      (fun u t => (hG.1 u t).symm ▸ isUnit_one) hG.2.1
    let F := framedTupleWord G g w
    have hF : F ∈ G.P.HtupW (typeIStandardTuple G) := by
      rw [hSpan]
      exact Submodule.subset_span ⟨w,rfl⟩
    refine ⟨⟨F,hF⟩,?_⟩
    apply IsFractionRing.injective G.O G.Kf
    rw [hrow,map_one]
    change Λ (framedTupleWord G g w) = 1
    rw [hword]
    simpa only [g,w,hG.1,_root_.one_zpow,Finset.prod_const_one,one_mul] using hUnit
  · intro L' he
    let f := algebraMap G.O G.Kf
    let j := G.P.j v
    let φ := f.comp j
    obtain ⟨a,ha,hA⟩ := rank_one_predecessor_slot_frames G v hr L' he
    let g := nativeEdgeFrames G v a
    let L'' : G.P.Tup := Function.update (typeIStandardTuple G) v L'
    have hSelf : L'' v = L' := by
      change Function.update (typeIStandardTuple G) v L' v = L'
      simp [Function.update]
    have hOther (u : Fin G.P.nV) (hu : u ≠ v) : L'' u = typeIStandardTuple G u := by
      change Function.update (typeIStandardTuple G) v L' u = typeIStandardTuple G u
      simp [Function.update, hu]
    have hg (u : Fin G.P.nV) (t : Fin (G.P.n' u)) :
        IsUnit (g u t).det ∧ extO G.O (G.P.ι u) (G.P.σ u) t.val
          (L'' u) = colSpan G.O (g u t) := by
      by_cases hu : u = v
      · subst u
        rw [hSelf]
        simpa only [g,nativeEdgeFrames,Function.update_self] using hA t
      · rw [hOther u hu]
        simpa only [g,nativeEdgeFrames,Function.update_of_ne hu,Matrix.det_one,isUnit_one,true_and] using
          standard_slot_frame G u t
    have hSpan := HtupW_eq_span_framed_words G L'' g
      (fun u t => (hg u t).1) (fun u t => (hg u t).2)
    let r : G.Kf := (p : G.Kf)^G.P.ArV v
    let Ψ := (r • Λ).restrictScalars G.O
    let I : Submodule G.O G.Kf :=
      Submodule.map (Algebra.linearMap G.O G.Kf) (Ideal.span {(p : G.O)^R})
    have hspan : Submodule.span G.O (Set.range (framedTupleWord G g)) ≤ I.comap Ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨w,rfl⟩
      change r * Λ (framedTupleWord G g w) ∈ I
      let W := G.P.W v
      let scale (b : NativeFlagSlot G) : G.Kf := if b.1 = v then (p : G.Kf) else 1
      let twist (b : NativeFlagSlot G) : G.Kf :=
        (g b.1 b.2).det ^ (-(lamAt (G.P.lam0 b.1) b.2 (Fin.last G.P.m)))
      let power (b : NativeFlagSlot G) : G.Kf :=
        if b.1 = v then (p : G.Kf)^(lamAt (G.P.lam0 b.1) b.2 0) else 1
      let val (b : NativeFlagSlot G) (A : FlagLabels (NativeFlagWeight G b)) :=
        (flagProducts (NativeFlagWeight G b) (wordFlag (g b.1 b.2)⁻¹ᵀ (w b.1 b.2)) A).coeff
          (wordExponent (w b.1 b.2))
      have hp : (p : G.Kf) ≠ 0 := by simpa only [map_natCast] using kp_p_ne_zero G v
      have hPow : (∏ b, power b) = r := by
        unfold power r
        rw [Fintype.prod_sigma, Fintype.prod_eq_single v]
        · simp only [ite_true, arV_rankOne_eq_sum_first G v hr]
          have hProduct (A : Finset (Fin (G.P.n' v))) :
              (∏ t ∈ A, (p : G.Kf)^(lamAt (G.P.lam0 v) t 0)) =
                (p : G.Kf)^(∑ t ∈ A, lamAt (G.P.lam0 v) t 0) := by
            induction A using Finset.induction_on with
            | empty => simp
            | @insert t A ht ih =>
              rw [Finset.prod_insert ht, Finset.sum_insert ht, ih, zpow_add₀ hp]
          exact hProduct Finset.univ
        · intro u hu
          simp [hu]
      have hfactor (b : NativeFlagSlot G) : ∃ u : W,
          φ u * (scale b)^(Fintype.card (FlagCopies (NativeFlagWeight G b))) =
            power b * twist b := by
        obtain ⟨u,t⟩ := b
        by_cases hu : u = v
        · subst u
          let a' := a.map (integralFrobeniusIter G v t.val)
          have ha' : IsUnit a'.det :=
            ((integralFrobeniusIter G v t.val).map_det a) ▸ ha.map _
          let d := ha'.unit
          let lam := lamAt (G.P.lam0 v) t
          let ν := nuOf lam
          have hν : Antitone ν := by
            intro i j hij
            change (lam j - lam (Fin.last G.P.m)).toNat ≤ (lam i - lam (Fin.last G.P.m)).toNat
            exact Int.toNat_le_toNat (sub_le_sub_right (kp_lamAt_antitone _ (G.P.dom v) t hij) _)
          have hN : (Fintype.card (FlagCopies ν) : ℤ) = lam 0 - lam (Fin.last G.P.m) := by
            rw [flagCopies_card_eq ν hν]
            exact Int.toNat_of_nonneg (sub_nonneg.mpr (kp_lamAt_antitone _ (G.P.dom v) t (Fin.zero_le _)))
          refine ⟨(↑(d ^ (-(lam (Fin.last G.P.m)))) : W),?_⟩
          simp only [scale,power,twist,g,nativeEdgeFrames,Function.update_self,ite_true]
          change φ (↑(d ^ (-(lam (Fin.last G.P.m)))) : W) * (p : G.Kf)^(Fintype.card (FlagCopies ν)) =
            (p : G.Kf)^lam 0 * ((a'.map φ * rankOnePole 0 (p : G.Kf)).det)^(-(lam (Fin.last G.P.m)))
          have hUnit :
              φ (↑(d ^ (-(lam (Fin.last G.P.m)))) : W) =
                (φ (↑d : W))^(-(lam (Fin.last G.P.m))) := by
            change (↑(Units.map (φ : W →* G.Kf) (d ^ (-(lam (Fin.last G.P.m))))) : G.Kf) = _
            simp only [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
            rfl
          rw [hUnit,rank_one_frame_det,← show φ a'.det = (a'.map φ).det from φ.map_det a',
            ← ha'.unit_spec,mul_zpow]
          calc
            _ = (φ (↑d : W))^(-(lam (Fin.last G.P.m))) *
                ((p : G.Kf)^lam 0 * (p : G.Kf)^(-(lam (Fin.last G.P.m)))) := by
                rw [← zpow_add₀ hp, ← zpow_natCast, hN, sub_eq_add_neg]
            _ = _ := by
              let a₀ : G.Kf := (φ (↑d : W))^(-(lam (Fin.last G.P.m)))
              let b₀ : G.Kf := (p : G.Kf)^lam 0
              let c₀ : G.Kf := (p : G.Kf)^(-(lam (Fin.last G.P.m)))
              change a₀ * (b₀ * c₀) = b₀ * (c₀ * a₀)
              exact (mul_comm a₀ (b₀ * c₀)).trans (mul_assoc b₀ c₀ a₀)
        · refine ⟨1,?_⟩
          simp [scale,power,twist,g,nativeEdgeFrames,hu]
      choose d hd using hfactor
      obtain ⟨J,hJ,hvalue⟩ := hDvd a ha w
      have hvalue' : φ J =
          (∏ b : NativeFlagSlot G, (scale b)^(Fintype.card (FlagCopies (NativeFlagWeight G b)))) *
            ∑ A : NativeFlagLabels G, (l A : G.Kf) * ∏ b, val b (A b) := hvalue
      have hscaled : φ ((∏ b, d b) * J) = r * Λ (framedTupleWord G g w) := by
        rw [map_mul,hvalue',hword]
        change _ = r * ((∏ b, twist b) * ∑ A : NativeFlagLabels G, (l A : G.Kf) * ∏ b, val b (A b))
        rw [← mul_assoc, map_prod, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun b _ => hd b),
          Finset.prod_mul_distrib,hPow,mul_assoc]
      have hJV : (p : W)^R ∣ (∏ b, d b) * J := dvd_mul_of_dvd_right hJ _
      have hO : (p : G.O)^R ∣ j ((∏ b, d b) * J) := by simpa only [map_pow,map_natCast] using map_dvd j hJV
      change r * Λ (framedTupleWord G g w) ∈
        Submodule.map (Algebra.linearMap G.O G.Kf) (Ideal.span {(p : G.O)^R})
      refine Submodule.mem_map.mpr ⟨j ((∏ b, d b) * J), Ideal.mem_span_singleton.mpr hO, ?_⟩
      exact hscaled
    intro F hF
    change F ∈ G.P.HtupW L'' at hF
    rw [hSpan] at hF
    have h : (r • Λ) F ∈ I := hspan hF
    change (r • Λ) F ∈
      Submodule.map (Algebra.linearMap G.O G.Kf) (Ideal.span {(p : G.O)^R}) at h
    obtain ⟨y,hy,heq⟩ := Submodule.mem_map.mp h
    refine ⟨y,hy,?_⟩
    change f y = Λ (r • F)
    rw [map_smul]
    exact heq

end

end GlobalTheory.EX.TypeIProduction
