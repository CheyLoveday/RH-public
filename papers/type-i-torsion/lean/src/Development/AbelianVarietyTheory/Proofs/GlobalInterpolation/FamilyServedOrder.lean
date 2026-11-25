module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen

@[expose] public section

noncomputable section

namespace GlobalTheory.EX.TypeIProduction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.Inhab
open NumberField

/-- The absolute norm of a nonzero integral multiplier kills every numerator class. -/
theorem wordOrder_dvd_absNorm {D : D7} {L : SizeData₂ D} (u : D.what₂.Word)
    (c : 𝓞 D.what₂.LL) (hc : c ≠ 0)
    (h : ∀ y ∈ DV.MramL D u, c • y ∈ L.NuLat u) :
    let A := DV.MramL D u
    let U := (L.NuLat u).comap A.subtype
    let d := Ideal.absNorm (Ideal.span {c})
    d ≠ 0 ∧ ∀ z : A, addOrderOf (U.mkQ z) ∣ d := by
  intro A U d
  have hd : d ≠ 0 := fun hz =>
    hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {c}))
  refine ⟨hd, fun z => addOrderOf_dvd_of_nsmul_eq_zero ?_⟩
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change d • z.1 ∈ L.NuLat u
  rw [← Nat.cast_smul_eq_nsmul (𝓞 D.what₂.LL), ha, mul_comm c a, mul_smul]
  exact (L.NuLat u).smul_mem a (h z.1 z.2)

theorem wordOrder_ne_zero_of_nuCommens {D : D7} {L : SizeData₂ D}
    (h : Formalism.MainNotions.Lnk.NuCommens D L) (u : D.what₂.Word) :
    let A := DV.MramL D u
    let U := (L.NuLat u).comap A.subtype
    ∀ z : A, addOrderOf (U.mkQ z) ≠ 0 := by
  intro A U z hz
  obtain ⟨_, c, hc, hA⟩ := h u
  obtain ⟨hd, hdiv⟩ := wordOrder_dvd_absNorm u c hc hA
  have hzdiv : addOrderOf (U.mkQ z) ∣ Ideal.absNorm (Ideal.span {c}) := hdiv z
  rw [hz, zero_dvd_iff] at hzdiv
  exact hd hzdiv

private theorem addOrderOf_unit_mod_prime_power {O : Type*} [CommRing O] [IsDomain O]
    (p : ℕ) (hp : p.Prime) (hp0 : (p : O) ≠ 0) (hpnu : ¬ IsUnit (p : O))
    (R : ℕ) (a : O) (ha : IsUnit a) :
    addOrderOf (Ideal.Quotient.mk (Ideal.span {((p : O) ^ R)}) a) = p ^ R := by
  cases R with
  | zero =>
    have hzero : Ideal.Quotient.mk (Ideal.span {((p : O) ^ 0)}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)
    rw [hzero, addOrderOf_zero, pow_zero]
  | succ r =>
    let I : Ideal O := Ideal.span {((p : O) ^ (r + 1))}
    let q := Ideal.Quotient.mk I a
    change addOrderOf q = p ^ (r + 1)
    have hkill : (p ^ (r + 1)) • q = 0 := by
      change (p ^ (r + 1)) • Ideal.Quotient.mk I a = 0
      rw [← map_nsmul]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (p ^ (r + 1) : ℕ) • a ∈ Ideal.span {((p : O) ^ (r + 1))}
      rw [nsmul_eq_mul, Nat.cast_pow]
      exact Ideal.mem_span_singleton.mpr ⟨a, rfl⟩
    have hsurvives : (p ^ r) • q ≠ 0 := by
      intro hz
      change (p ^ r) • Ideal.Quotient.mk I a = 0 at hz
      rw [← map_nsmul] at hz
      have hdmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
      change (p ^ r : ℕ) • a ∈ Ideal.span {((p : O) ^ (r + 1))} at hdmem
      rw [nsmul_eq_mul, Nat.cast_pow] at hdmem
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hdmem
      have hab : a = (p : O) * b :=
        mul_left_cancel₀ (pow_ne_zero r hp0) (by simpa only [pow_succ, mul_assoc] using hb)
      exact hpnu (isUnit_iff_dvd_one.mpr
        ((show (p : O) ∣ a from ⟨b, hab⟩).trans (isUnit_iff_dvd_one.mp ha)))
    have : Fact p.Prime := ⟨hp⟩
    exact addOrderOf_eq_prime_pow hsurvives hkill

/-- Restrict the given comparison on a global word to its ramified numerator. -/
def wordRamifiedImage {D : D7} (cmp : LatCmp D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ↥(DV.MramL D u) →+ ↥(D.gat u w hg).M where
  toFun a := ⟨cmp.cmp u w hg (D.nuIn u a.1), by
    rw [← cmp.cmp_M u w hg]
    exact Submodule.subset_span ⟨D.nuIn u a.1, a.2, rfl⟩⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- Descent on the word and place of an arbitrary family member. Every source projection is
an argument of this theorem, including the served predicate on the same comparison. -/
theorem servedData_primePowerOrders {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (cmp : LatCmp D)
    (served : cmp.NuServedDef X Y K) (u : D.what₂.Word) :
    let A := DV.MramL D u
    let U := (L.NuLat u).comap A.subtype
    ∀ (w : {w : D.what₂.places.Pl //
          w ∈ L.supp ∧ D.what₂.places.resChar w ≠ (D.mem u).A.T})
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w.1))
      (_orbit : {t₀ : HH D // t₀ ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w.1)}),
    let p := D.what₂.places.resChar w.1
    let G := D.gat u w.1 hg
    let cmpA := wordRamifiedImage cmp u w.1 hg
    ∀ (R : ℕ) (row : ↥G.M →ₗ[G.O] G.O) (z : ↥A) (_hN : L.NuLat u ≤ A),
    let I : Ideal G.O := Ideal.span {((p : G.O) ^ R)}
    ∀ (_hRow : ∀ b : ↥G.M, b.1 ∈ NP X Y K u w.1 hg → row b ∈ I)
      (_hUnit : IsUnit (row (cmpA z))),
    let q := U.mkQ z
    let m := addOrderOf q
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    ∀ (_hFinite : m ≠ 0),
      U.map A.subtype = L.NuLat u ∧
      ∃ read : (↥A ⧸ U) →+ (G.O ⧸ I),
        (∀ a : ↥A, read (U.mkQ a) = Ideal.Quotient.mk I (row (cmpA a))) ∧
        addOrderOf (read q) = p ^ R ∧ p ^ R ∣ m ∧
        addOrderOf ((m / p ^ R) • q) = p ^ R ∧
        (T + 1 ≤ R → addOrderOf ((m / p ^ (T + 1)) • q) = p ^ (T + 1)) := by
  intro A U w hg orbit p G cmpA R row z hN I hRow hUnit q m T hFinite
  have hRaw : U.map A.subtype = L.NuLat u := by
    change ((L.NuLat u).comap A.subtype).map A.subtype = L.NuLat u
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hN]
  let residueRow : ↥A →+ (G.O ⧸ I) :=
    (Ideal.Quotient.mk I).toAddMonoidHom.comp (row.toAddMonoidHom.comp cmpA)
  have hkernel : U.toAddSubgroup ≤ residueRow.ker := by
    intro a ha
    have haN : a.1 ∈ L.NuLat u := ha
    have hloc := GlobalTheory.EX.Led.inLoc_of_mem (D.plEq w.1) (L.NuLat u) a.1 haN
    have hNP := (served u w.1 hg (Finset.ne_empty_of_mem orbit.2) a.1).mp hloc
    change Ideal.Quotient.mk I (row (cmpA a)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hRow (cmpA a) hNP)
  let read : (↥A ⧸ U) →+ (G.O ⧸ I) :=
    QuotientAddGroup.lift U.toAddSubgroup residueRow hkernel
  have hread (a : ↥A) : read (U.mkQ a) = Ideal.Quotient.mk I (row (cmpA a)) := rfl
  let v := Y.vOf u w.1 hg orbit.1
  have hp : p.Prime := D.what₂.places.resChar_prime w.1
  have hp0 : (p : G.O) ≠ 0 := by
    intro h
    exact LatticeSystems.kp_p_ne_zero G v (by rw [h, map_zero])
  have hpnu : ¬ IsUnit (p : G.O) := LatticeSystems.ja_p_nonunit G v
  have horder : addOrderOf (read q) = p ^ R := by
    change addOrderOf (read (U.mkQ z)) = _
    rw [hread z]
    exact addOrderOf_unit_mod_prime_power p hp hp0 hpnu R _ hUnit
  have hkill : m • read q = 0 := by
    rw [← map_nsmul, show m • q = 0 from addOrderOf_nsmul_eq_zero q, map_zero]
  have hdiv : p ^ R ∣ m := by
    rw [← horder]
    exact addOrderOf_dvd_of_nsmul_eq_zero hkill
  have hexact (i : ℕ) (hi : i ≤ R) : addOrderOf ((m / p ^ i) • q) = p ^ i := by
    let qMul := Multiplicative.ofAdd q
    change orderOf (qMul ^ (orderOf qMul / p ^ i)) = p ^ i
    exact orderOf_pow_orderOf_div hFinite ((pow_dvd_pow p hi).trans hdiv)
  exact ⟨hRaw, read, hread, horder, hdiv, hexact R le_rfl, hexact (T + 1)⟩

end GlobalTheory.EX.TypeIProduction
