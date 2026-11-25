import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.TypeISamePlaceOrder
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.TypeINativeQuotient
import Formalism.SharpRestriction.GrowthBounds.TypeIPrimeSelection
import Formalism.SharpRestriction.GrowthBounds.TypeILocalLength
import Formalism.SharpRestriction.GrowthBounds.TypeIAdjacentNativeRow

open scoped BigOperators Pointwise Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G
open Formalism.MainNotions.Pk Formalism.MainNotions.Lnk
open Filter

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- The complete same-member, same-word and same-place conclusion. -/
def TypeIAtOriginalWord {eps : ℝ} (F : FamP eps) (x : ℝ) (hx : F.x1 < x) (i : F.Ix x)
    (u : (F.D x i).what₂.Word) : Prop :=
  let D := F.D x i
  let L := F.L x i
  let X := F.Gx x i
  let Y := F.Gy x i
  let K := F.GK
  let ex := F.ex x hx i
  let Z := L.sc.X' ^ (3/4 : ℝ)
  ∃ p : ℕ, Cand D L K p ∧ L.sc.p0 D.R.k ≤ p ∧ Z < p ∧ (p : ℝ) < 2*Z ∧ p ∉ L.drop ∧
    ∃ (w : D.what₂.places.Pl) (_hp : D.what₂.places.resChar w = p)
      (_hw : w ∈ L.supp) (_hoff : p ≠ (D.mem u).A.T)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
      (t₀ : HH D) (ht₀ : t₀ ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w)),
    let G := D.gat u w hg
    let v := Y.vOf u w hg t₀
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let P := literalFirstSpan X Y K u w hg
    let A := G.M ⊓ Y.Vram u w hg
    let U := (NP X Y K u w hg).comap A.subtype
    let V : Submodule G.O A := ((p : G.O)^T) • ⊤
    let I : Ideal G.O := Ideal.span {(p : G.O)^T}
    let J : Ideal G.O := Ideal.span {(p : G.O)^(T+1)}
    let e := (IsDiscreteValuationRing.addVal G.O (p : G.O)).toNat
    let A₀ := DV.MramL D u
    let U₀ := (L.NuLat u).comap A₀.subtype
    haveI : IsFractionRing G.O G.Kf := (G.P.setting v).frac_O
    ∃ s : Fin (G.P.n' v), s ≠ posAdd s 1 ∧
      s ∈ (Y.Fl u w hg).TT v ∧ posAdd s 1 ∈ (Y.Fl u w hg).TT v ∧
      G.P.r = 1 ∧ TypeIAdjacentCapacity G v s (T+1) ∧
      T + 1 ≤ ⌈Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t₀⌉.toNat ∧
      U = P.comap A.subtype ⊓ V ∧
      (∃ f : (↥V ⧸ U.comap V.subtype) →ₗ[G.O] (↥I ⧸ Submodule.comap I.subtype (J : Submodule G.O G.O)), Function.Surjective f) ∧
      ¬ (A.map (((p : G.O)^T) • (LinearMap.id : G.Fn →ₗ[G.O] G.Fn)) ≤ P) ∧
      0 < e ∧ ((e*Module.finrank G.O A*T+e : ℕ) : ℕ∞) ≤ Module.length G.O (↥A ⧸ U) ∧
      Module.length G.O (↥A ⧸ U) ≠ ⊤ ∧
      let cmp := ramifiedComparisonAt X Y K ex.cmp ex.lat.vram ex.lat.served u w hg
        (Finset.ne_empty_of_mem ht₀)
      (∀ a : A₀, cmp (U₀.mkQ a) = U.mkQ (ramifiedNumeratorAt ex.cmp Y ex.lat.vram u w hg a)) ∧
      ∃ z : ↥A₀ ⧸ U₀, (p^(T+1) : ℕ) • z = 0 ∧ (p^T : ℕ) • cmp z ≠ 0 ∧
        addOrderOf z = p^(T+1) ∧ addOrderOf (cmp z) = p^(T+1)

/-- Target family theorem, with the original index and word chosen before p. -/
def TypeIIndexedFamilyConclusion {eps : ℝ} (F : FamP eps) : Prop :=
  ∃ x₀ : ℝ, F.x1 < x₀ ∧ ∀ (x : ℝ), x₀ ≤ x → ∀ (hx : F.x1 < x) (i : F.Ix x)
    (u : (F.D x i).what₂.Word), TypeIAtOriginalWord F x hx i u

/-- The fixed word and place carry the actual adjacent labels and the row
that induces the first scalar-layer map. -/
def TypeIAtOriginalWordWithRow {eps : ℝ} (F : FamP eps) (x : ℝ) (hx : F.x1 < x) (i : F.Ix x)
    (u : (F.D x i).what₂.Word) : Prop :=
  let D := F.D x i
  let L := F.L x i
  let X := F.Gx x i
  let Y := F.Gy x i
  let K := F.GK
  let ex := F.ex x hx i
  let Z := L.sc.X' ^ (3/4 : ℝ)
  ∃ p : ℕ, Cand D L K p ∧ L.sc.p0 D.R.k ≤ p ∧ Z < p ∧ (p : ℝ) < 2*Z ∧ p ∉ L.drop ∧
    ∃ (w : D.what₂.places.Pl) (_hp : D.what₂.places.resChar w = p)
      (_hw : w ∈ L.supp) (_hoff : p ≠ (D.mem u).A.T)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
      (t₀ : HH D) (ht₀ : t₀ ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w)),
    let G := D.gat u w hg
    let v := Y.vOf u w hg t₀
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let P := literalFirstSpan X Y K u w hg
    let A := G.M ⊓ Y.Vram u w hg
    let U := (NP X Y K u w hg).comap A.subtype
    let V : Submodule G.O A := ((p : G.O)^T) • ⊤
    let e := (IsDiscreteValuationRing.addVal G.O (p : G.O)).toNat
    let A₀ := DV.MramL D u
    let U₀ := (L.NuLat u).comap A₀.subtype
    haveI : IsFractionRing G.O G.Kf := (G.P.setting v).frac_O
    ∃ (t : HH D) (_ : t ∈ topsOn X p t₀) (_ : t+hP D p ∈ D.host.TT),
    ∃ s : Fin (G.P.n' v), s ≠ posAdd s 1 ∧
      s ∈ (Y.Fl u w hg).TT v ∧ posAdd s 1 ∈ (Y.Fl u w hg).TT v ∧
      t₀+s.val • hP D p = t ∧ t₀+(posAdd s 1).val • hP D p = t+hP D p ∧
      G.P.r = 1 ∧ TypeIAdjacentCapacity G v s (T+1) ∧
      T + 1 ≤ ⌈Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t₀⌉.toNat ∧
      U = P.comap A.subtype ⊓ V ∧
      (∃ (row : ↥A →ₗ[G.O] G.O) (a : ↥A₀),
        IsUnit (row (ramifiedNumeratorAt ex.cmp Y ex.lat.vram u w hg a)) ∧
          FirstScalarLayerSurjection (O := G.O) (A := ↥A) (p : G.O) T U row) ∧
      ¬ (A.map (((p : G.O)^T) • (LinearMap.id : G.Fn →ₗ[G.O] G.Fn)) ≤ P) ∧
      0 < e ∧ ((e*Module.finrank G.O A*T+e : ℕ) : ℕ∞) ≤ Module.length G.O (↥A ⧸ U) ∧
      Module.length G.O (↥A ⧸ U) ≠ ⊤ ∧
      let cmp := ramifiedComparisonAt X Y K ex.cmp ex.lat.vram ex.lat.served u w hg
        (Finset.ne_empty_of_mem ht₀)
      (∀ a : A₀, cmp (U₀.mkQ a) = U.mkQ (ramifiedNumeratorAt ex.cmp Y ex.lat.vram u w hg a)) ∧
      ∃ z : ↥A₀ ⧸ U₀, (p^(T+1) : ℕ) • z = 0 ∧ (p^T : ℕ) • cmp z ≠ 0 ∧
        addOrderOf z = p^(T+1) ∧ addOrderOf (cmp z) = p^(T+1)


theorem original_word_of_row_witness {eps : ℝ} (F : FamP eps) (x : ℝ) (hx : F.x1 < x)
    (i : F.Ix x) (u : (F.D x i).what₂.Word) (h : TypeIAtOriginalWordWithRow F x hx i u) :
    TypeIAtOriginalWord F x hx i u := by
  unfold TypeIAtOriginalWordWithRow at h
  unfold TypeIAtOriginalWord
  obtain ⟨p,hc,hType,hLo,hHi,hDrop,w,hChar,hSupport,hOff,hg,t₀,h₀,t,_,_,s,hs,hT,hT',_,_,hr,hCap,hDepth,
    hU,⟨row,a,ha,hSurj⟩,hNon,hPos,hLen,hFin,hCmp,z,hKill,hLive,hOrd,hOrd'⟩ := h
  obtain ⟨f,hf,_⟩ := hSurj
  exact ⟨p,hc,hType,hLo,hHi,hDrop,w,hChar,hSupport,hOff,hg,t₀,h₀,s,hs,hT,hT',hr,hCap,hDepth,
    hU,⟨f,hf⟩,hNon,hPos,hLen,hFin,hCmp,z,hKill,hLive,hOrd,hOrd'⟩

theorem indexed_typeI_same_place_with_row {eps : ℝ} (heps : 0 < eps) (heps' : eps < 1/52)
    (F : FamP eps) (C₀ CH : ℝ) (hChosen : ChosenE F C₀ CH) (hWall : ChosenWall F)
    (hTu : TuSize F) (hGrp : Formalism.L2.G.GroupCompatibilityFamily F) :
    ∃ x₀ : ℝ, F.x1 < x₀ ∧ ∀ (x : ℝ), x₀ ≤ x → ∀ (hx : F.x1 < x) (i : F.Ix x)
      (u : (F.D x i).what₂.Word), TypeIAtOriginalWordWithRow F x hx i u := by
  classical
  obtain ⟨xG,hGrp⟩ := hGrp
  have hAll : ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x) (u : (F.D x i).what₂.Word),
      TypeIAtOriginalWordWithRow F x hx i u := by
    filter_upwards [family_typeI_prime_pair F heps heps' hChosen hWall hTu,
      family_typeI_depth_at_pair F heps heps',family_index_scale_eventually F heps,eventually_ge_atTop xG]
      with x hSelect hDepth hIndex hxG
    intro hx i u
    let D := F.D x i
    let L := F.L x i
    let X := F.Gx x i
    let Y := F.Gy x i
    let K := F.GK
    let ex := F.ex x hx i
    obtain ⟨p,hc,hType,hLo,hHi,hOff,_,hDrop,hEven,t₀,h₀,t,ht,ht'⟩ := hSelect hx i u
    obtain ⟨w,hChar,hSupp,hg⟩ :=
      served_place_of_candidate F x hx i u p (hIndex hx i) hc hOff
    subst p
    let p := D.what₂.places.resChar w
    have hInert : IsResidueClassZero D p := hc.2.2.1
    have hStep : hP D p ≠ 0 := HEv.ne_zero hEven
    obtain ⟨hReal,hCG,hOm⟩ := hDepth hx i p hc.1 hInert hLo hHi hType t₀ t h₀ ht ht' hStep
    have hTie := F.latTied x hx i
    obtain ⟨hr,s,hs,hT,hT',hsLabel,hsLabel'⟩ :=
      native_slots_of_inert_top_pair X Y hTie u w hg t₀ t hInert hType ht ht' hStep
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    have hRep : t₀ ∈ reps X p := AuxBlock8.Pf.VV_subset_reps X K _ _ p h₀
    have hCap := native_adjacent_capacity_of_depth (F.params x hx i) X Y hTie u w hg t₀
      hRep hEven s (T+1) hT hT' hReal hCG
    obtain ⟨hG⟩ := hGrp x hxG i hx
    obtain ⟨row,a,z,ha,hU,hSurj,hNon,hPos,hLen,hFin,hCmp,hKill,hLive,hOrd,hOrd'⟩ :=
      servedWord_fromNativeAdjacentCapacity X Y K ex.cmp ex.lat.vram ex.lat.served hG u w hg t₀ h₀
        s hr hCap hOm
    exact ⟨p,hc,hType,hLo,hHi,hDrop,w,rfl,hSupp,hOff,hg,t₀,h₀,t,ht,ht',s,hs,hT,hT',hsLabel,hsLabel',
      hr,hCap,hOm,hU,⟨row,a,ha,hSurj⟩,hNon,hPos,hLen,hFin,hCmp,z,hKill,hLive,hOrd,hOrd'⟩
  obtain ⟨x₀,h⟩ := eventually_atTop.mp hAll
  have h₁ : F.x1 < F.x1+1 := by linarith
  refine ⟨max x₀ (F.x1+1),h₁.trans_le (le_max_right _ _),?_⟩
  intro x hx
  exact h x ((le_max_left _ _).trans hx)

theorem indexed_typeI_same_place {eps : ℝ} (heps : 0 < eps) (heps' : eps < 1/52)
    (F : FamP eps) (C₀ CH : ℝ) (hChosen : ChosenE F C₀ CH) (hWall : ChosenWall F)
    (hTu : TuSize F) (hGrp : Formalism.L2.G.GroupCompatibilityFamily F) :
    TypeIIndexedFamilyConclusion F := by
  obtain ⟨x₀,hx₀,h⟩ := indexed_typeI_same_place_with_row heps heps' F C₀ CH hChosen hWall hTu hGrp
  exact ⟨x₀,hx₀,fun x hx hxi i u => original_word_of_row_witness F x hxi i u (h x hx hxi i u)⟩

end

end GlobalTheory.EX.TypeIProduction
