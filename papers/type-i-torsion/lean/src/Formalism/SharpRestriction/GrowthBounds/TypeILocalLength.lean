import Formalism.SharpRestriction.GrowthBounds.TypeILocalExcess
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree
import Formalism.SubspaceCounting.SubspaceCountingProofs.LengthLayers

open scoped BigOperators Pointwise
open Formalism.BasicNotions Formalism.MainNotions.G
open Formalism.NG.QuotientPowerLengths
open IsDiscreteValuationRing

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- Multiplication by p^T identifies the successive scalar layer with O/(p). -/
def ringScalarLayer_equiv {O : Type*} [CommRing O] [IsDomain O]
    (p : O) (hp : p ≠ 0) (T : ℕ) :
    let I : Ideal O := Ideal.span {p^T}
    let J : Ideal O := Ideal.span {p^(T+1)}
    (O ⧸ Ideal.span {p}) ≃ₗ[O] (↥I ⧸ Submodule.comap I.subtype (J : Submodule O O)) := by
  intro I J
  let φ : O →ₗ[O] I :=
    (LinearMap.mulLeft O (p^T)).codRestrict I (fun a => Ideal.mem_span_singleton.mpr ⟨a,rfl⟩)
  let f := (Submodule.comap I.subtype (J : Submodule O O)).mkQ.comp φ
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨b,rfl⟩ := Submodule.mkQ_surjective _ a
    obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp b.2
    exact ⟨c, congrArg (Submodule.comap I.subtype (J : Submodule O O)).mkQ (Subtype.ext hc.symm)⟩
  have hker : f.ker = (Ideal.span {p} : Submodule O O) := by
    apply Submodule.ext
    intro a
    change (Submodule.comap I.subtype (J : Submodule O O)).mkQ (φ a) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change p^T*a ∈ J ↔ a ∈ Ideal.span {p}
    simp only [J, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨b,mul_left_cancel₀ (pow_ne_zero _ hp) (by simpa only [pow_succ,mul_assoc] using hb)⟩
    · rintro ⟨b,rfl⟩
      exact ⟨b,by rw [pow_succ,mul_assoc]⟩
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective f hsurj)

private theorem smulRange_eq_smul_top {O M : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module O M] (a : O) :
    smulRange M a = a • (⊤ : Submodule O M) := by
  ext x
  simp only [mem_smulRange, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

private theorem smulRange_ring_eq {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (a : O) :
    smulRange O a = (Ideal.span {a} : Submodule O O) := by
  ext b
  rw [mem_smulRange]
  exact ⟨fun ⟨c,hc⟩ => Ideal.mem_span_singleton.mpr ⟨c,hc.symm⟩,
    fun h => let ⟨c,hc⟩ := Ideal.mem_span_singleton.mp h; ⟨c,hc.symm⟩⟩

/-- The quotient length contribution is the full valuation e of the rational
prime. The source of the lower bound is the first-layer surjection. -/
theorem successive_scalar_length_lower_bound
    {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [Module.Finite O A] [Module.IsTorsionFree O A]
    (p : O) (hp : p ≠ 0) (T : ℕ) (U : Submodule O A)
    (hU : U ≤ p^T • ⊤) :
    let V : Submodule O A := p^T • ⊤
    let I : Ideal O := Ideal.span {p^T}
    let J : Ideal O := Ideal.span {p^(T+1)}
    let e := (addVal O p).toNat
    ∀ f : (↥V ⧸ U.comap V.subtype) →ₗ[O] (↥I ⧸ Submodule.comap I.subtype (J : Submodule O O)),
      Function.Surjective f →
      ((e * Module.finrank O A * T + e : ℕ) : ℕ∞) ≤ Module.length O (A ⧸ U) := by
  intro V I J e f hf
  have hFinite : addVal O p ≠ ⊤ := fun h => hp (addVal_eq_top_iff.mp h)
  have hNat : addVal O p = (e : ℕ∞) := (ENat.natCast_toNat hFinite).symm
  have hV : Module.length O (A ⧸ V) =
      ((e * Module.finrank O A * T : ℕ) : ℕ∞) := by
    change Module.length O (A ⧸ p^T • (⊤ : Submodule O A)) = _
    rw [← smulRange_eq_smul_top, length_quot_smulRange_free, addVal_pow, hNat]
    simp only [nsmul_eq_mul, Nat.cast_mul]
    let r : ℕ∞ := Module.finrank O A
    let t : ℕ∞ := T
    let v : ℕ∞ := e
    change r * (t * v) = v * r * t
    calc
      r * (t * v) = (r * t) * v := (mul_assoc r t v).symm
      _ = v * (r * t) := mul_comm _ _
      _ = v * r * t := (mul_assoc v r t).symm
  have hS : Module.length O (↥I ⧸ Submodule.comap I.subtype (J : Submodule O O)) = (e : ℕ∞) := by
    rw [← (ringScalarLayer_equiv p hp T).length_eq, ← smulRange_ring_eq,
      length_quot_smulRange_free, Module.finrank_self, Nat.cast_one, one_mul, hNat]
  have hres := Module.length_le_of_surjective f hf
  rw [hS] at hres
  let q : V →ₗ[O] V.map U.mkQ :=
    (U.mkQ.comp V.subtype).codRestrict _ (fun x => Submodule.mem_map_of_mem x.2)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x,hx,hxy⟩ := Submodule.mem_map.mp y.2
    exact ⟨⟨x,hx⟩, Subtype.ext hxy⟩
  have hker : q.ker = U.comap V.subtype := by
    ext x
    change q x = 0 ↔ (x : A) ∈ U
    constructor
    · intro h
      exact (Submodule.Quotient.mk_eq_zero U).mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero U).mpr h
  let E := (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective q hq)
  rw [Formalism.G0.LengthLayersP.length_quot_eq_add hU, ← E.length_eq, hV]
  rw [Nat.cast_add]
  let n : ℕ∞ := (e * Module.finrank O A * T : ℕ)
  calc
    n + (e : ℕ∞) ≤ n + Module.length O (↥V ⧸ U.comap V.subtype) := add_le_add_right hres n
    _ = _ := add_comm _ _

private theorem successive_scalar_length_lower_bound_of_row
    {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [Module.Finite O A] [Module.IsTorsionFree O A]
    (p : O) (hp : p ≠ 0) (T : ℕ) (U : Submodule O A)
    (hU : U ≤ p^T • ⊤) (row : A →ₗ[O] O) (h : FirstScalarLayerSurjection p T U row) :
    let e := (addVal O p).toNat
    ((e * Module.finrank O A * T + e : ℕ) : ℕ∞) ≤ Module.length O (A ⧸ U) := by
  unfold FirstScalarLayerSurjection at h
  obtain ⟨f,hf,_⟩ := h
  exact successive_scalar_length_lower_bound p hp T U hU f hf

/-- Specialize the first-layer lower bound at the same source place and row. -/
theorem literal_local_length_lower_of_primitive_row {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (hv : c.VramDef Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (t₀ : HH D) (ht₀ : t₀ ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w)) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let A := G.M ⊓ Y.Vram u w hg
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let U := (NP X Y K u w hg).comap A.subtype
    let P := literalFirstSpan X Y K u w hg
    let e := (addVal G.O (p : G.O)).toNat
    ∀ (row : A →ₗ[G.O] G.O) (a : A), IsUnit (row a) →
      (∀ b : A, b.1 ∈ P → row b ∈ Ideal.span {(p : G.O)^(T+1)}) →
      0 < e ∧ ((e * Module.finrank G.O A * T + e : ℕ) : ℕ∞) ≤
        Module.length G.O (↥A ⧸ U) ∧ Module.length G.O (↥A ⧸ U) ≠ ⊤ := by
  intro p G A T U P e row a ha hrow
  have hfg : A.FG := by
    change ((D.gat u w hg).M ⊓ Y.Vram u w hg).FG
    rw [c.M_inf_Vram Y hv u w hg]
    exact FBC.fg_span_image (D.plEq w) (c.embW u w hg) (c.embW_val u w hg)
      (c.cmpN u w hg) (c.cmpN_smul u w hg) _ (D.MramL_fg u)
  haveI : Module.Finite G.O A := Module.Finite.iff_fg.2 hfg
  let v := Y.vOf u w hg t₀
  haveI : Module.IsTorsionFree G.O A := ⟨fun b hb x y hxy => by
    have h0 : b • (x - y) = 0 := by rw [smul_sub]; exact sub_eq_zero.mpr hxy
    have h1 : x - y = 0 := Subtype.ext
      (LatticeSystems.fn_torsion G v b hb.ne_zero (x - y).1 (congrArg Subtype.val h0))
    exact sub_eq_zero.mp h1⟩
  have hp := c.resChar_ne_zero_O u w hg
  have hunit := LatticeSystems.ja_p_nonunit G v
  have hpos : 0 < e := by
    apply ENat.toNat_pos
    · exact fun h => hunit (addVal_eq_zero_iff.mp h)
    · exact fun h => hp (addVal_eq_top_iff.mp h)
  obtain ⟨hEq,hFirst,_,hFin⟩ :=
    literal_local_excess_of_primitive_row X Y K c hv u w hg t₀ ht₀ row a ha hrow
  have hEq' : U = P.comap A.subtype ⊓ ((p : G.O)^T • ⊤) := hEq
  have hle : U ≤ (p : G.O)^T • ⊤ := hEq'.le.trans inf_le_right
  exact ⟨hpos,successive_scalar_length_lower_bound_of_row (p : G.O) hp T U hle row hFirst,hFin⟩

end

end GlobalTheory.EX.TypeIProduction
