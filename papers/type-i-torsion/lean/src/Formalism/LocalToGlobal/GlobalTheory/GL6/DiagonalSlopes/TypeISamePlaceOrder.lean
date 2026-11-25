import Formalism.SharpRestriction.GrowthBounds.TypeILiteralNP
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
import Mathlib.GroupTheory.OrderOfElement

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions.G
open Formalism.MainNotions.G.LatticeSystems
open NumberField

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

def ramifiedNumeratorAt {D : D7} (c : LatCmp D) (Y : LatInst D) (hv : c.VramDef Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf] :
    ↥(DV.MramL D u) →+ ↥((D.gat u w hg).M ⊓ Y.Vram u w hg) where
  toFun a := ⟨c.cmpN u w hg a.1, by
    rw [c.M_inf_Vram Y hv u w hg]
    exact Submodule.subset_span ⟨a.1,a.2,rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add (c.cmpN u w hg) a.1 b.1)

/-- The actual comparison in the full local ramified quotient. -/
def ramifiedComparisonAt {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (hs : c.NuServedDef X Y K) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅) :
    let Au := DV.MramL D u
    let Uu := (L.NuLat u).comap Au.subtype
    let Aw := (D.gat u w hg).M ⊓ Y.Vram u w hg
    let Uw := (NP X Y K u w hg).comap Aw.subtype
    (↥Au ⧸ Uu) →+ (↥Aw ⧸ Uw) := by
  intro Au Uu Aw Uw
  let f := Uw.mkQ.toAddMonoidHom.comp (ramifiedNumeratorAt c Y hv u w hg)
  apply QuotientAddGroup.lift Uu.toAddSubgroup f
  intro a ha
  have hl := GlobalTheory.EX.Led.inLoc_of_mem (D.plEq w) (L.NuLat u) a.1 ha
  have hp := (hs u w hg hVV a.1).mp hl
  change Uw.mkQ (ramifiedNumeratorAt c Y hv u w hg a) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hp

theorem ramifiedComparisonAt_mk {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (hs : c.NuServedDef X Y K) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅)
    (a : DV.MramL D u) :
    ramifiedComparisonAt X Y K c hv hs u w hg hVV
      (((L.NuLat u).comap (DV.MramL D u).subtype).mkQ a) =
        ((NP X Y K u w hg).comap ((D.gat u w hg).M ⊓ Y.Vram u w hg).subtype).mkQ
          (ramifiedNumeratorAt c Y hv u w hg a) := rfl

private theorem exists_first_crossing (P : ℕ → Prop) (h0 : ¬ P 0)
    (B : ℕ) (hB : P B) : ∃ k, ¬ P k ∧ P (k+1) := by
  classical
  induction B with
  | zero => exact False.elim (h0 hB)
  | succ b ih =>
    by_cases hb : P b
    · exact ih hb
    · exact ⟨b,hb,hB⟩

/-- Transfer the first strict surviving power to the literal word quotient
and keep its exact order through comparison at this very place. -/
theorem exists_same_place_order_of_seed {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (hs : c.NuServedDef X Y K) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅) :
    let p := D.what₂.places.resChar w
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let Au := DV.MramL D u
    let Uu := (L.NuLat u).comap Au.subtype
    let compare := ramifiedComparisonAt X Y K c hv hs u w hg hVV
    ∀ (a : Au), (p^T : ℕ) • c.cmpN u w hg a.1 ∉ NP X Y K u w hg →
      ∃ z : ↥Au ⧸ Uu, (p^(T+1) : ℕ) • z = 0 ∧ (p^T : ℕ) • compare z ≠ 0 ∧
        addOrderOf z = p^(T+1) ∧ addOrderOf (compare z) = p^(T+1) := by
  intro p T Au Uu compare a ha
  let G := D.gat u w hg
  let bnd := ∑ t ∈ VV X K (aL L) (bL L) p, ⌈Sv X K (aL L) (bL L) p t⌉.toNat
  let P (k : ℕ) := InLoc (D.plEq w) (L.NuLat u)
    ((p^k : ℕ) • ((p^T : ℕ) • (a.1 : (D.div.Nu u).V)))
  have h0 : ¬ P 0 := by
    intro h
    have hk := (hs u w hg hVV _).mp h
    change c.cmpN u w hg ((p^0 : ℕ) • ((p^T : ℕ) • a.1)) ∈ NP X Y K u w hg at hk
    rw [map_nsmul, map_nsmul, pow_zero, one_nsmul] at hk
    exact ha hk
  have hB : P bnd := by
    apply (hs u w hg hVV _).mpr
    change c.cmpN u w hg ((p^bnd : ℕ) • ((p^T : ℕ) • a.1)) ∈ NP X Y K u w hg
    rw [map_nsmul, map_nsmul, smul_smul, ← pow_add]
    have hmem := literalNP_pow_mem_of_empty_word X Y K u w hg
      (c.cmpN u w hg a.1) (ramifiedNumeratorAt c Y hv u w hg a).2 (bnd+T)
      (by change bnd ≤ bnd + T; omega) (by change T ≤ bnd + T; omega)
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hmem
  obtain ⟨k,hk,hk1⟩ := exists_first_crossing P h0 bnd hB
  let b : Au := (p^k : ℕ) • a
  have hShift (j : ℕ) : (p^(T+j) : ℕ) • b.1 =
      (p^(k+j) : ℕ) • ((p^T : ℕ) • a.1) := by
    change (p^(T+j) : ℕ) • ((p^k : ℕ) • a.1) = _
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add]
    rw [show T+j+k = k+j+T by omega]
  obtain ⟨c0,hc0,hmem⟩ := hk1
  have hcleared : c0 • ((p^(T+1) : ℕ) • b.1) ∈ L.NuLat u := by
    rw [hShift]
    exact hmem
  let a' : Au := c0 • b
  let z := Uu.mkQ a'
  have hkill : (p^(T+1) : ℕ) • z = 0 := by
    change (p^(T+1) : ℕ) • Uu.mkQ a' = 0
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (p^(T+1) : ℕ) • (c0 • b.1) ∈ L.NuLat u
    exact smul_comm (p^(T+1) : ℕ) c0 b.1 ▸ hcleared
  have hsurvive : (p^T : ℕ) • compare z ≠ 0 := by
    intro hz
    change (p^T : ℕ) • (ramifiedComparisonAt X Y K c hv hs u w hg hVV) (Uu.mkQ a') = 0 at hz
    rw [← map_nsmul, ← map_nsmul, ramifiedComparisonAt_mk] at hz
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    change c.cmpN u w hg ((p^T : ℕ) • a'.1) ∈ NP X Y K u w hg at hz
    obtain ⟨c1,hc1,hmem1⟩ := (hs u w hg hVV _).mpr hz
    apply hk
    refine ⟨c1*c0, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hc1 hc0, ?_⟩
    change c1 • ((p^T : ℕ) • (c0 • b.1)) ∈ L.NuLat u at hmem1
    have hShiftZero : (p^T : ℕ) • b.1 = (p^k : ℕ) • (p^T : ℕ) • a.1 := by
      simpa only [Nat.add_zero] using hShift 0
    rw [smul_comm (p^T : ℕ) c0, ← mul_smul, hShiftZero] at hmem1
    exact hmem1
  have hp : Fact p.Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hkillLocal : (p^(T+1) : ℕ) • compare z = 0 := by
    rw [← map_nsmul, hkill, map_zero]
  have hsurviveGlobal : (p^T : ℕ) • z ≠ 0 := by
    intro hz
    apply hsurvive
    rw [← map_nsmul, hz, map_zero]
  exact ⟨z,hkill,hsurvive,addOrderOf_eq_prime_pow hsurviveGlobal hkill,
    addOrderOf_eq_prime_pow hsurvive hkillLocal⟩

/-- The source integral row provides the original surviving seed at the cutoff. -/
theorem exists_same_place_order_of_primitive_row {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (hs : c.NuServedDef X Y K) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (t₀ : HH D) (ht₀ : t₀ ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w)) :
    let p := D.what₂.places.resChar w
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let Au := DV.MramL D u
    let Uu := (L.NuLat u).comap Au.subtype
    let G := D.gat u w hg
    let Aw := G.M ⊓ Y.Vram u w hg
    let compare := ramifiedComparisonAt X Y K c hv hs u w hg (Finset.ne_empty_of_mem ht₀)
    ∀ (a : Au) (row : Aw →ₗ[G.O] G.O),
      IsUnit (row (ramifiedNumeratorAt c Y hv u w hg a)) →
      (∀ b : Aw, b.1 ∈ NP X Y K u w hg →
        row b ∈ Ideal.span {(p : G.O)^(T+1)}) →
      ∃ z : ↥Au ⧸ Uu, (p^(T+1) : ℕ) • z = 0 ∧ (p^T : ℕ) • compare z ≠ 0 ∧
        addOrderOf z = p^(T+1) ∧ addOrderOf (compare z) = p^(T+1) := by
  intro p T Au Uu G Aw compare a row ha hrow
  apply exists_same_place_order_of_seed X Y K c hv hs u w hg (Finset.ne_empty_of_mem ht₀) a
  intro h
  let b := ramifiedNumeratorAt c Y hv u w hg a
  have hm := hrow ((p^T : ℕ) • b) h
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul G.O, Nat.cast_pow, smul_eq_mul] at hm
  obtain ⟨d,hd⟩ := Ideal.mem_span_singleton.mp hm
  let v := Y.vOf u w hg t₀
  have hp0 : (p : G.O) ≠ 0 := c.resChar_ne_zero_O u w hg
  have hpnu : ¬ IsUnit (p : G.O) := ja_p_nonunit G v
  have hu : row b = (p : G.O) * d :=
    mul_left_cancel₀ (pow_ne_zero T hp0) (by simpa only [pow_succ, mul_assoc] using hd)
  exact hpnu (isUnit_iff_dvd_one.mpr
    ((show (p : G.O) ∣ row b from ⟨d,hu⟩).trans (isUnit_iff_dvd_one.mp ha)))

end

end GlobalTheory.EX.TypeIProduction
