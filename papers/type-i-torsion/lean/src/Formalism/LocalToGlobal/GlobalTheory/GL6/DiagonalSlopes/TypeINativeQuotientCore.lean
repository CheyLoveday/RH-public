import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.TypeISamePlaceOrder
import Formalism.SharpRestriction.GrowthBounds.TypeILocalLength
import Formalism.SharpRestriction.GrowthBounds.TypeINativeSeparatingRow

open scoped BigOperators Pointwise
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G
open Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- The fixed-place assembly through the exact chart unit interface supplied
by the seed bridge. The native row and both literal quotient conclusions are
constructed on the same source data. -/
theorem servedWord_fromNativeAdjacentCapacity_withSeedBridge {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (hs : c.NuServedDef X Y K)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (t₀ : HH D) (ht₀ : t₀ ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w)) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let v := Y.vOf u w hg t₀
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let Aw := G.M ⊓ Y.Vram u w hg
    let U := (NP X Y K u w hg).comap Aw.subtype
    let P := literalFirstSpan X Y K u w hg
    let Au := DV.MramL D u
    let Uu := (L.NuLat u).comap Au.subtype
    let e := (IsDiscreteValuationRing.addVal G.O (p : G.O)).toNat
    let l := typeIStandardTuple G
    letI : IsFractionRing G.O G.Kf := (G.P.setting v).frac_O
    ∀ (s : Fin (G.P.n' v)) (i : G.comp), 0 < G.P.m → G.P.r = 1 →
      TypeIAdjacentCapacity G v s (T+1) →
      T+1 ≤ ⌈Sv X K (aL L) (bL L) p t₀⌉.toNat →
      (∀ (coeff : ↥(G.P.HtupW l) →ₗ[G.O] G.O) (ξ : ↥(G.P.HtupW l)),
        IsUnit (coeff ξ) → ∃ a : Au, ∃ ha : c.cmpN u w hg a.1 i l ∈ G.P.HtupW l,
          IsUnit (coeff ⟨_, ha⟩)) →
      ∃ (row : Aw →ₗ[G.O] G.O) (a : Au) (z : ↥Au ⧸ Uu),
        let cmp := ramifiedComparisonAt X Y K c hv hs u w hg (Finset.ne_empty_of_mem ht₀)
        IsUnit (row (ramifiedNumeratorAt c Y hv u w hg a)) ∧
        (U = P.comap Aw.subtype ⊓ ((p : G.O)^T • ⊤)) ∧
        FirstScalarLayerSurjection (p : G.O) T U row ∧
        ¬ (Aw.map (((p : G.O)^T) • LinearMap.id) ≤ P) ∧
        0 < e ∧ ((e * Module.finrank G.O Aw * T + e : ℕ) : ℕ∞) ≤ Module.length G.O (↥Aw ⧸ U) ∧
        Module.length G.O (↥Aw ⧸ U) ≠ ⊤ ∧
        (∀ b : Au, cmp (Uu.mkQ b) = U.mkQ (ramifiedNumeratorAt c Y hv u w hg b)) ∧
        (p^(T+1) : ℕ) • z = 0 ∧ (p^T : ℕ) • cmp z ≠ 0 ∧
        addOrderOf z = p^(T+1) ∧ addOrderOf (cmp z) = p^(T+1) := by
  classical
  intro p G v T Aw U P Au Uu e l s i hmG hr hc hCut hSeed
  letI : IsFractionRing G.O G.Kf := (G.P.setting v).frac_O
  have hmD : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hl : G.P.IsLatTup l := typeIStandardTuple_isLatTup G
  obtain ⟨Λ,coeff,hΛ,⟨ξ,hξ⟩,hEdges⟩ :=
    exists_native_typeI_separating_row G v s (T+1) hmG hr hc
  have hξUnit : IsUnit (coeff ξ) := by rw [hξ]; exact isUnit_one
  obtain ⟨a,haMem,haCoeff⟩ :=
    hSeed coeff ξ hξUnit
  let ev₀ : G.Fn →ₗ[G.O] G.P.Xsp :=
    { toFun := fun F => F i l
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ev : Aw →ₗ[G.O] G.P.HtupW l :=
    (ev₀.comp Aw.subtype).codRestrict _ (fun b =>
      ((jd_fmem G G.P.HtupW b.1).mp b.2.1 i).1 l hl)
  let row : Aw →ₗ[G.O] G.O := coeff.comp ev
  have ha : IsUnit (row (ramifiedNumeratorAt c Y hv u w hg a)) := haCoeff
  have hInt (F : G.P.Xsp) (hF : F ∈ G.P.HtupW l) :
      Λ F ∈ Set.range (algebraMap G.O G.Kf) :=
    ⟨coeff ⟨F,hF⟩, hΛ ⟨F,hF⟩⟩
  have hP (b : Aw) (hb : b.1 ∈ P) : row b ∈ Ideal.span {(p : G.O)^(T+1)} := by
    obtain ⟨y,hy,hval⟩ := literalFirstSpan_eval_mem_prime_power
      X Y K u w hg hmD t₀ ht₀ i l hl (T+1) hCut Λ hInt hEdges b.1 hb
    have hEq : y = row b := IsFractionRing.injective G.O G.Kf
      (hval.trans (hΛ (ev b)).symm)
    exact hEq ▸ hy
  obtain ⟨hU,hSurj,hNon,hFin⟩ :=
    literal_local_excess_of_primitive_row X Y K c hv u w hg t₀ ht₀ row _ ha hP
  obtain ⟨hPos,hLen,_⟩ :=
    literal_local_length_lower_of_primitive_row X Y K c hv u w hg t₀ ht₀ row _ ha hP
  have hNP (b : Aw) (hb : b.1 ∈ NP X Y K u w hg) : row b ∈ Ideal.span {(p : G.O)^(T+1)} :=
    hP b (literalNP_le_firstSpan X Y K u w hg hb)
  obtain ⟨z,hKill,hSurvive,hGlobal,hLocal⟩ :=
    exists_same_place_order_of_primitive_row X Y K c hv hs u w hg t₀ ht₀ a row ha hNP
  exact ⟨row,a,z,ha,hU,hSurj,hNon,hPos,hLen,hFin,
    fun b => ramifiedComparisonAt_mk X Y K c hv hs u w hg (Finset.ne_empty_of_mem ht₀) b,
    hKill,hSurvive,hGlobal,hLocal⟩

end

end GlobalTheory.EX.TypeIProduction
