import Formalism.SharpRestriction.GrowthBounds.TypeILiteralNP
import Formalism.LocalRingCardinality.Lemmas
import Mathlib.RingTheory.Length

open scoped BigOperators Pointwise
open Formalism.BasicNotions Formalism.MainNotions.G

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- A surjective row map to the successive scalar layer, with its
representative formula on the residual source submodule. -/
def FirstScalarLayerSurjection {O A : Type*} [CommRing O] [AddCommGroup A] [Module O A]
    (p : O) (T : ℕ) (U : Submodule O A) (row : A →ₗ[O] O) : Prop :=
    let V : Submodule O A := (p^T) • ⊤
    let I : Ideal O := Ideal.span {p^T}
    let J : Ideal O := Ideal.span {p^(T+1)}
    ∃ f : (↥V ⧸ U.comap V.subtype) →ₗ[O]
        (↥I ⧸ Submodule.comap I.subtype (J : Submodule O O)),
      Function.Surjective f ∧
      ∀ b : V, ∃ c : I, c.1 = row b.1 ∧
        f ((U.comap V.subtype).mkQ b) = (Submodule.comap I.subtype (J : Submodule O O)).mkQ c

/-- The first residual quotient maps onto the literal successive scalar layer. -/
theorem firstScalarLayer_surjective {O A : Type*} [CommRing O] [AddCommGroup A] [Module O A]
    (p : O) (T : ℕ) (U : Submodule O A) (row : A →ₗ[O] O) (a : A)
    (ha : IsUnit (row a)) (hU : ∀ b ∈ U, row b ∈ Ideal.span {p^(T+1)}) :
    FirstScalarLayerSurjection p T U row := by
  unfold FirstScalarLayerSurjection
  intro V I J
  have hI (b : V) : row b.1 ∈ I := by
    obtain ⟨z,_,hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp b.2
    exact Ideal.mem_span_singleton.mpr
      ⟨row z, by rw [← hz, map_smul, smul_eq_mul]⟩
  let φ : V →ₗ[O] I := (row.comp V.subtype).codRestrict I hI
  have hφ : Function.Surjective φ := by
    intro c
    obtain ⟨d,hd⟩ := Ideal.mem_span_singleton.mp c.2
    let e : O := ↑ha.unit⁻¹
    have he : e * row a = 1 := by
      calc
        e * row a = e * (↑ha.unit : O) := congrArg (fun c => e * c) ha.unit_spec.symm
        _ = 1 := Units.inv_mul _
    let x := (d * e) • a
    refine ⟨⟨p^T • x,(Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x,Submodule.mem_top,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change row (p^T • x) = c.1
    calc
      row (p^T • x) = p^T * ((d * e) * row a) := by
        simp only [x, map_smul, smul_eq_mul]
      _ = p^T * d := by rw [mul_assoc, he, mul_one]
      _ = c.1 := hd.symm
  let ρ := (Submodule.comap I.subtype (J : Submodule O O)).mkQ.comp φ
  have hKer : U.comap V.subtype ≤ ρ.ker := by
    intro b hb
    change (Submodule.comap I.subtype (J : Submodule O O)).mkQ (φ b) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hU b.1 hb
  let f := (U.comap V.subtype).liftQ ρ hKer
  refine ⟨f, ?_, fun b => ⟨φ b, rfl, rfl⟩⟩
  intro y
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨b,rfl⟩ := hφ c
  exact ⟨(U.comap V.subtype).mkQ b,rfl⟩

/-- Saturation from the actual fraction-field ramified span resolves the
second and third intersections in the literal NP definition. -/
theorem literalNP_comap_eq_inf_scalar {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (hv : c.VramDef Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let A := G.M ⊓ Y.Vram u w hg
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let U := (NP X Y K u w hg).comap A.subtype
    let P := literalFirstSpan X Y K u w hg
    let V : Submodule G.O A := (p : G.O)^T • ⊤
    (p : G.Kf) ≠ 0 → U = P.comap A.subtype ⊓ V := by
  intro p G A T U P V hp
  ext a
  constructor
  · intro ha
    have hp' : a.1 ∈ P := literalNP_le_firstSpan X Y K u w hg ha
    obtain ⟨b,hb,he⟩ := Submodule.mem_map.mp (show a.1 ∈
      G.M.map (((p : G.O)^T) • LinearMap.id) from ha.1.2)
    have hO : ((p : G.O)^T) • b = a.1 := he
    have hK : ((p : G.Kf)^T) • b = a.1 := by
      simpa only [Algebra.smul_def, map_pow, map_natCast] using hO
    let S := Submodule.span G.Kf (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))
    have hs : (Y.Vram u w hg : Set G.Fn) = S := hv u w hg
    have haS : a.1 ∈ S := by
      change a.1 ∈ (S : Set G.Fn)
      rw [← hs]
      exact a.2.2
    have hbS : b ∈ S := by
      have hx := S.smul_mem (((p : G.Kf)^T)⁻¹) haS
      rw [← hK, inv_smul_smul₀ (pow_ne_zero _ hp)] at hx
      exact hx
    have hbV : b ∈ Y.Vram u w hg := by
      change b ∈ (Y.Vram u w hg : Set G.Fn)
      rw [hs]
      exact hbS
    have hbA : b ∈ A := ⟨hb,hbV⟩
    refine ⟨hp', (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨⟨b,hbA⟩, Submodule.mem_top, Subtype.ext hO⟩⟩
  · rintro ⟨hP,hV⟩
    obtain ⟨b,_,he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hV
    refine ⟨⟨hP,Submodule.mem_map.mpr ⟨b.1,b.2.1,?_⟩⟩, a.2.2⟩
    exact congrArg Subtype.val he

/-- At one actual served place, the source row detects a nonzero first-layer
quotient and gives the literal full-quotient finiteness on that same data. -/
theorem literal_local_excess_of_primitive_row {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (hv : c.VramDef Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (t₀ : HH D) (ht₀ : t₀ ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w)) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let A := G.M ⊓ Y.Vram u w hg
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let U : Submodule G.O A := (NP X Y K u w hg).comap A.subtype
    let V : Submodule G.O A := ((p : G.O)^T) • ⊤
    let P := literalFirstSpan X Y K u w hg
    let J : Ideal G.O := Ideal.span {(p : G.O)^(T+1)}
    ∀ (row : A →ₗ[G.O] G.O) (a : A), IsUnit (row a) →
      (∀ b : A, b.1 ∈ P → row b ∈ J) →
      (U = P.comap A.subtype ⊓ V) ∧
      FirstScalarLayerSurjection (p : G.O) T U row ∧
      ¬ (A.map (((p : G.O)^T) • LinearMap.id) ≤ P) ∧
      Module.length G.O (↥A ⧸ U) ≠ ⊤ := by
  intro p G A T U V P J row a ha hrow
  let v := Y.vOf u w hg t₀
  have hp : (p : G.Kf) ≠ 0 := by
    simpa only [map_natCast] using LatticeSystems.kp_p_ne_zero G v
  have hpO : (p : G.O) ≠ 0 := c.resChar_ne_zero_O u w hg
  have hpnu : ¬ IsUnit (p : G.O) := LatticeSystems.ja_p_nonunit G v
  have hEq := literalNP_comap_eq_inf_scalar X Y K c hv u w hg hp
  refine ⟨hEq, ?_, ?_, c.length_quotient_ne_top₂ X Y K hv u w hg⟩
  · apply firstScalarLayer_surjective (p : G.O) T U row a ha
    intro b hb
    exact hrow b (literalNP_le_firstSpan X Y K u w hg hb)
  · intro hP
    let b : A := (p : G.O)^T • a
    have hmem : b.1 ∈ P := hP (Submodule.mem_map.mpr ⟨a.1,a.2,rfl⟩)
    have hdiv := hrow b hmem
    change row ((p : G.O)^T • a) ∈ J at hdiv
    rw [map_smul, smul_eq_mul] at hdiv
    obtain ⟨d,hd⟩ := Ideal.mem_span_singleton.mp hdiv
    have h := mul_left_cancel₀ (pow_ne_zero T hpO) (by
      simpa only [pow_succ, mul_assoc] using hd) 
    exact hpnu (isUnit_iff_dvd_one.mpr
      ((show (p : G.O) ∣ row a from ⟨d,h⟩).trans (isUnit_iff_dvd_one.mp ha)))

end

end GlobalTheory.EX.TypeIProduction
