import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SupportedSeed
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.GroupActionMulSingleEqDilation
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdmissibleStabilisersOfCompatibleForms
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IsUnitDetBlockPreimage
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.LocalRingCardinality.Lemmas

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms

/-- A single adelic class is the support of a global integral word vector with the prescribed
restriction of any global integral word vector. This uses rational and integral coefficient
criteria at every place and every local basis, before choosing any comparison place. -/
theorem exists_integral_singleClass {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u)
    (C : (D.mem u).C.cls 0) (b : ↥(((D.fm u).lat 0).L)) :
    ∃ bC : ↥(((D.fm u).lat 0).L),
      (D.fm u).emb 0 bC.1 C = (D.fm u).emb 0 b.1 C ∧
      ∀ d ≠ C, (D.fm u).emb 0 bC.1 d = 0 := by
  classical
  let f := (D.fm u).emb 0 b.1
  let masked := fun d : (D.mem u).C.cls 0 => if d = C then f d else 0
  have hrat := (Tf.val0.rat f).mp ⟨b.1, rfl⟩
  have hmu : f ∈ (D.mem u).A.Mu0 := by
    rw [← (D.fm u).Fi_zero]
    exact hrat.1
  have hS := admissible_stabilisers_of_compatible_forms Tf
  have hval := (mem_forms_level_zero_iff Tf hS f).mp hmu
  have hmask : masked ∈ (D.fm u).Fi 0 := by
    rw [(D.fm u).Fi_zero]
    apply (mem_forms_level_zero_iff Tf hS masked).mpr
    intro d
    by_cases hd : d = C
    · simpa only [masked, if_pos hd] using hval d
    · simpa only [masked, if_neg hd] using (levelZeroValues Tf).zero_mem
  obtain ⟨x, hx⟩ := (Tf.val0.rat masked).mpr ⟨hmask, by
    intro d
    by_cases hd : d = C
    · simpa only [masked, if_pos hd] using hrat.2 d
    · refine ⟨0, (RatSpan D _).zero_mem, fun z => ?_⟩
      simp [masked, hd]⟩
  have hxint : x ∈ ((D.fm u).lat 0).L := by
    apply (Tf.val0.lat x).mpr
    intro w d B hB
    rw [hx]
    by_cases hd : d = C
    · simpa only [masked, if_pos hd, f] using (Tf.val0.lat b.1).mp b.2 w d B hB
    · refine ⟨0, (IntSpan D w _).zero_mem, fun z => ?_⟩
      simp [masked, hd]
  refine ⟨⟨x, hxint⟩, ?_, ?_⟩
  · rw [hx]
    simp [masked, f]
  · intro d hd
    rw [hx]
    simp [masked, hd]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms
open Formalism.L2.G.Cmp Formalism.UG Matrix
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/-- The away-from-p representative of the identity adelic double class supplies a component
at the actual word and place, even though a bare GAtP has only a Fintype of components. -/
theorem nonempty_component_of_groupCompatibility {D : D7} {Gt : GatTies D} {cmp : LatCmp D}
    (H : GroupCompatibilityAll D Gt cmp) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Nonempty (D.gat u w hg).comp := by
  obtain ⟨i, _⟩ := (H.herm.g u w hg).yG_bij.2 (Quotient.mk'' 1)
  exact ⟨i⟩

theorem trivStab_of_groupCompatibility {D : D7} {Gt : GatTies D} {cmp : LatCmp D}
    (H : GroupCompatibilityAll D Gt cmp) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (D.gat u w hg).TrivStab := by
  have ht := gatE_of_gatIs D H.herm.lev0
    (fun v => Triv.trivStabU (H.herm.lev0 v) D.host.g_prime D.host.g_ne) H.gat
  exact (ht u w hg).1

/-- Pick one chart before quantifying over the two global vectors. Equality of the entire
frame function there forces equality of the comparison polynomials on the chosen tuple. -/
theorem exists_common_chart_comparison {D : D7} {Gt : GatTies D} {cmp : LatCmp D}
    (H : GroupCompatibilityAll D Gt cmp) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    let G := D.gat u w hg
    ∀ (i : G.comp) (L : G.P.Tup), G.P.IsLatTup L →
    ∀ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    (∀ v, L v = colSpan (G.P.W v)
      (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    ∃ C : (D.mem u).C.cls 0, ∀ x y : ((D.fm u).lat 0).V,
      (D.fm u).emb 0 x C = (D.fm u).emb 0 y C →
      cmp.cmp u w hg x i L = cmp.cmp u w hg y i L := by
  intro G i L hL g hLg
  let A := locAt H.herm u w hg H.cmp.B
  let pos := Gt.gat_pos u w hg
  let K := H.cmp.tie u w hg
  obtain ⟨C, γ, κ, hγ, hpt⟩ := ptEx_rec H.herm H.forms u w hg H.cmp.B i g
  refine ⟨C, fun x y hxy => ?_⟩
  have hz : evC G.P A.rk pos (gramC (gramN D 0 (Nat.zero_le _)) (embT D))
      (crdB (embT D) A.B)
      (MvPolynomial.map D.what₂.embLL (K.val x i L) -
       MvPolynomial.map D.what₂.embLL (K.val y i L)) = 0 := by
    funext z
    obtain ⟨z', ht⟩ := frames_tr (embT D) (embT_conj D) γ hγ z
    rw [map_sub, Pi.sub_apply, K.val_emb x i L g hLg C γ hγ κ hpt z z' ht,
      K.val_emb y i L g hLg C γ hγ κ hpt z z' ht]
    simp only [hxy, sub_self, Pi.zero_apply]
  have hmap := evInj_pf (embT D) G A pos
    (J := gramN D 0 (Nat.zero_le _)) _ hz
  have heq := MvPolynomial.map_injective D.what₂.embLL D.what₂.embLL.injective
    (sub_eq_zero.1 hmap)
  rw [K.val_cmp x i L hL, K.val_cmp y i L hL, heq]

/-- The native delta realizes every prescribed integral Weyl coefficient. -/
theorem exists_model_evaluation {p : ℕ} (G : GAtP p) (hfree : G.TrivStab)
    (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) (ξ : ↥(G.P.HtupW L)) :
    ∃ F : ↥G.M, F.1 i L = ξ.1 := by
  refine ⟨⟨LatticeSystems.delta G i L ξ.1, ?_⟩, LatticeSystems.jd_self G hfree i L ξ.1 hL⟩
  exact LatticeSystems.jd_mem G hfree G.P.HtupW (equivSys_HtupW G) i L hL ξ.1 ξ.2

/-- At the frame fixed before the word vector is chosen, projection to one adelic class and
the full product of integral tame differences preserve its complete comparison coefficient. -/
theorem exists_common_chart_ramified {D : D7} {Gt : GatTies D} {cmp : LatCmp D}
    (H : GroupCompatibilityAll D Gt cmp) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    let G := D.gat u w hg
    ∀ (i : G.comp) (L : G.P.Tup), G.P.IsLatTup L →
    ∀ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    (∀ v, L v = colSpan (G.P.W v)
      (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    ∃ C : (D.mem u).C.cls 0, ∀ b : ↥(((D.fm u).lat 0).L),
      ∃ bC : ↥(((D.fm u).lat 0).L), ∃ φ : ↥((D.fm u).ramL),
        (∀ d ≠ C, (D.fm u).emb 0 bC.1 d = 0) ∧
        (D.fm u).emb 0 bC.1 C = (D.fm u).emb 0 b.1 C ∧
        (D.fm u).emb 0 φ.1 C = (D.fm u).emb 0 bC.1 C ∧
        cmp.cmp u w hg φ.1 i L = cmp.cmp u w hg b.1 i L := by
  classical
  intro G i L hL g hLg
  obtain ⟨C, readC⟩ := exists_common_chart_comparison H u w hg i L hL g hLg
  refine ⟨C, fun b => ?_⟩
  let Tf := H.forms u
  obtain ⟨bC, hbC, hoff⟩ := exists_integral_singleClass Tf C b
  let js := (Finset.univ : Finset (D.mem u).A.vT).toList
  have hall (j : (D.mem u).A.vT) : j ∈ js := Finset.mem_toList.mpr (Finset.mem_univ j)
  obtain ⟨hφ, heq⟩ := integralSignDifferences_ramL_restrict Tf C bC hoff js
    (Finset.nodup_toList _) hall
  exact ⟨bC, ⟨(integralSignDifferences js bC).1, hφ⟩, hoff, hbC, heq, readC _ _ (heq.trans hbC)⟩

/-- The integral ramified word lattice spans every coefficient in the prescribed output fibre
after applying the very comparison at the chosen word and place. -/
theorem span_ramified_comparison_evaluation {D : D7} {Gt : GatTies D} {cmp : LatCmp D}
    (H : GroupCompatibilityAll D Gt cmp) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    let G := D.gat u w hg
    ∀ (i : G.comp) (L : G.P.Tup), G.P.IsLatTup L →
    ∀ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    (∀ v, L v = colSpan (G.P.W v)
      (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    Submodule.span G.O ((fun x => cmp.cmp u w hg x i L) '' ((D.fm u).ramL : Set _))
      = G.P.HtupW L := by
  intro G i L hL g hLg
  have hfree := trivStab_of_groupCompatibility H u w hg
  let ev : G.Fn →ₗ[G.O] G.P.Xsp :=
    { toFun := fun F => F i L
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : G.M.map ev = G.P.HtupW L := by
    apply le_antisymm
    · rintro _ ⟨F, hF, rfl⟩
      exact ((LatticeSystems.jd_fmem G G.P.HtupW F).mp hF i).1 L hL
    · intro ξ hξ
      obtain ⟨F, he⟩ := exists_model_evaluation G hfree i L hL ⟨ξ, hξ⟩
      exact ⟨F.1, F.2, he⟩
  obtain ⟨C, hr⟩ := exists_common_chart_ramified H u w hg i L hL g hLg
  have himage :
      (fun x => cmp.cmp u w hg x i L) '' ((D.fm u).ramL : Set _)
      = (fun x => cmp.cmp u w hg x i L) '' (((D.fm u).lat 0).L : Set _) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx.1, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨bC, φ, _, _, _, he⟩ := hr ⟨x, hx⟩
      exact ⟨φ.1, φ.2, he⟩
  rw [himage, ← hev, ← cmp.cmp_M u w hg, Submodule.map_span, Set.image_image] <;> rfl

private theorem exists_unit_on_spanning_set {R V : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup V] [Module R V] (s : Set V) (H : Submodule R V)
    (hs : Submodule.span R s = H) (row : H →ₗ[R] R) (ξ : H) (hu : IsUnit (row ξ)) :
    ∃ v : s, ∃ hv : v.1 ∈ H, IsUnit (row ⟨v.1, hv⟩) := by
  classical
  by_contra h
  let J := Submodule.comap row (IsLocalRing.maximalIdeal R : Submodule R R)
  have hle : H ≤ J.map H.subtype := by
    refine hs.ge.trans (Submodule.span_le.mpr ?_)
    intro v hv
    have hvH : v ∈ H := hs.le (Submodule.subset_span hv)
    have hnu : ¬IsUnit (row ⟨v, hvH⟩) := fun ha => h ⟨⟨v, hv⟩, hvH, ha⟩
    refine ⟨⟨v, hvH⟩, ?_, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  obtain ⟨t, ht, he⟩ := hle ξ.2
  have htξ : t = ξ := Subtype.ext he
  subst t
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp ht)) hu

/-- Supply a unit on one coefficient of the output Weyl lattice. The resulting vector
is in the actual global numerator used by the served denominator test. -/
theorem exists_word_numerator_unit {D : D7} {Gt : GatTies D} {cmp : LatCmp D}
    (H : GroupCompatibilityAll D Gt cmp) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    let G := D.gat u w hg
    ∀ (i : G.comp) (L : G.P.Tup), G.P.IsLatTup L →
    ∀ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    (∀ v, L v = colSpan (G.P.W v)
      (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    ∀ (row : (G.P.HtupW L) →ₗ[G.O] G.O) (ξ : G.P.HtupW L), IsUnit (row ξ) →
    ∃ z : ↥(DV.MramL D u), ∃ hz : cmp.cmp u w hg (D.nuIn u z.1) i L ∈ G.P.HtupW L,
      IsUnit (row ⟨_, hz⟩) := by
  intro G i L hL g hLg row ξ hu
  have hs := span_ramified_comparison_evaluation H u w hg i L hL g hLg
  obtain ⟨⟨v, φ, hφ, he⟩, hv, hvu⟩ := exists_unit_on_spanning_set _ _ hs row ξ hu
  subst v
  rw [← D.MramL_map u] at hφ
  obtain ⟨z, hz, hez⟩ := hφ
  change D.nuIn u z = φ at hez
  subst φ
  exact ⟨⟨z, hz⟩, hv, hvu⟩

end Formalism.L2.G
