import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.F6SeedBridge
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.TypeINativeQuotientCore

open scoped BigOperators Pointwise
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G
open Formalism.MainNotions.G.LatticeSystems
open Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Matrix
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- On one fixed served place and word, the adjacent-pair capacity and literal
depth test give the row, its ramified unit seed, the first excess and the same
exact order through comparison. -/
theorem servedWord_fromNativeAdjacentCapacity {D : D7} {L : SizeData₂ D} {Gt : GatTies D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (hs : c.NuServedDef X Y K) (H : GroupCompatibilityAll D Gt c)
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
    letI : IsFractionRing G.O G.Kf := (G.P.setting v).frac_O
    ∀ (s : Fin (G.P.n' v)), G.P.r = 1 → TypeIAdjacentCapacity G v s (T+1) →
      T+1 ≤ ⌈Sv X K (aL L) (bL L) p t₀⌉.toNat →
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
  intro p G v T Aw U P Au Uu e s hr hc hCut
  letI : IsFractionRing G.O G.Kf := (G.P.setting v).frac_O
  have hmG : 0 < G.P.m := by
    have hdim : G.P.m + 1 = D.R.k := Gt.gat_k u w hg
    have := D.R.five_le_k
    omega
  let i : G.comp := Classical.choice (nonempty_component_of_groupCompatibility H u w hg)
  let l := typeIStandardTuple G
  have hl : G.P.IsLatTup l := typeIStandardTuple_isLatTup G
  let g (j : Fin G.P.nV) : GL (Fin (G.P.m + 1)) (G.P.Qq j) := 1
  have hFrame (j : Fin G.P.nV) : l j =
      colSpan (G.P.W j) (g j : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.Qq j)) := rfl
  refine servedWord_fromNativeAdjacentCapacity_withSeedBridge X Y K c hv hs u w hg t₀ ht₀
    s i hmG hr hc hCut ?_
  intro coeff ξ hu
  exact exists_word_numerator_unit H u w hg i l hl g hFrame coeff ξ hu

end

end GlobalTheory.EX.TypeIProduction
