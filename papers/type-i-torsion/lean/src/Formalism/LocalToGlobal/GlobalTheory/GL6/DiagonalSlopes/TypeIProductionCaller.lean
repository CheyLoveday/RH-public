import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.TypeIIndexedTargets
import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps

open scoped BigOperators Pointwise Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G
open Formalism.MainNotions.Pk Formalism.MainNotions.Lnk

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

def TypeIProductionConclusion {N : FamClass → Prop} {DR : GlobalTheory.Fc.R1.DefiniteSideType}
    (H : GlobalTheory.Fc.HypsAlt N DR) (la : ℝ) (Q : UpperTheory.Top.FReq) : Prop :=
  ∃ eps₀ : ℝ, 0 < eps₀ ∧
    ∀ eps : ℝ, 0 < eps → eps ≤ eps₀ → eps < 1/52 → ∀ K : TransportedAlt,
      ∃ (F : FamP eps) (CH : ℝ), H.𝒜 F ∧ Q.cls la F ∧ 0 ≤ CH ∧ F.Large K CH ∧
        ChosenE F 3 CH ∧ TuSize F ∧ DGamSize F ∧
        ∀ y : ℝ, ∃ (x : ℝ) (_ : y ≤ x) (hx : F.x1 < x) (_ : x ∈ F.Win) (i : F.Ix x)
          (u : (F.D x i).what₂.Word), TypeIAtOriginalWord F x hx i u

def TypeIProductionConclusionWithRow {N : FamClass → Prop} {DR : GlobalTheory.Fc.R1.DefiniteSideType}
    (H : GlobalTheory.Fc.HypsAlt N DR) (la : ℝ) (Q : UpperTheory.Top.FReq) : Prop :=
  ∃ eps₀ : ℝ, 0 < eps₀ ∧
    ∀ eps : ℝ, 0 < eps → eps ≤ eps₀ → eps < 1/52 → ∀ K : TransportedAlt,
      ∃ (F : FamP eps) (CH : ℝ), H.𝒜 F ∧ Q.cls la F ∧ 0 ≤ CH ∧ F.Large K CH ∧
        ChosenE F 3 CH ∧ TuSize F ∧ DGamSize F ∧
        ∀ y : ℝ, ∃ (x : ℝ) (_ : y ≤ x) (hx : F.x1 < x) (_ : x ∈ F.Win) (i : F.Ix x)
          (u : (F.D x i).what₂.Word), TypeIAtOriginalWordWithRow F x hx i u

/-- Apply the indexed Type I theorem to the genuine design and window supplier. -/
theorem production_window_with_typeI_row
    {N : FamClass → Prop} {DR : GlobalTheory.Fc.R1.DefiniteSideType}
    (H : GlobalTheory.Fc.HypsAlt N DR) (la : ℝ) (Q : UpperTheory.Top.FReq)
    (hla : 1 < la) (hH : GlobalTheory.EX.HostExW la Q.req) :
    TypeIProductionConclusionWithRow H la Q := by
  let sel : Formalism.L2.TwistSelection H.𝒜 :=
    fun {eps} F hc => GlobalTheory.Fc.familySelection H.σ F hc
  have hsub : ∀ {eps : ℝ} (F : FamP eps), WithTw (WithSm (Formalism.L2.Top3.WithChN fun F => H.𝒜 F ∧ Q.cls la F)) F →
        WithTw (WithSm (Formalism.L2.Top3.WithChN H.𝒜)) F :=
    fun _ hc => ⟨⟨⟨hc.1.1.1.1, hc.1.1.2⟩, hc.1.2⟩, hc.2⟩
  have hE := GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin
    (fun F => H.𝒜 F ∧ Q.cls la F) H.cT (fun hM => H.hEx hM la Q hla hH)
    (fun F hc => sel F hc.1) (fun F hc => H.hduty F hc.1)
    (Pk.Closed.sub H.hTu hsub) (Pk.Closed.sub H.hn4 hsub) H.hLit
  obtain ⟨eps₀,heps₀,hE⟩ := hE
  refine ⟨eps₀,heps₀,?_⟩
  intro eps heps hlim hlt K
  obtain ⟨F,CH,hCls,hCH,hLarge,hCE,hTu,hDG⟩ := hE eps heps hlim K
  have hc : H.𝒜 F ∧ Q.cls la F := hCls.1.1.1
  obtain ⟨_,_,_,_,hWall,_,_⟩ := H.hduty F hc.1
  have hGrp := Formalism.L2.DIV.LinkGCl.gTiedF_of_sel_alt F (sel F hc.1)
  obtain ⟨x₀,_,hTerm⟩ := indexed_typeI_same_place_with_row heps hlt F 3 CH hCE hWall hTu hGrp
  refine ⟨F,CH,hc.1,hc.2,hCH,hLarge,hCE,hTu,hDG,?_⟩
  intro y
  obtain ⟨x,hy,hx,hw,⟨i⟩⟩ := F.toFamCore.exists_pt (max y x₀)
  let u := (F.D x i).u₀
  exact ⟨x,(le_max_left y x₀).trans hy,hx,hw,i,u,hTerm x ((le_max_right y x₀).trans hy) hx i u⟩

theorem production_window_of_indexed_typeI
    {N : FamClass → Prop} {DR : GlobalTheory.Fc.R1.DefiniteSideType}
    (H : GlobalTheory.Fc.HypsAlt N DR) (la : ℝ) (Q : UpperTheory.Top.FReq)
    (hla : 1 < la) (hH : GlobalTheory.EX.HostExW la Q.req) :
    TypeIProductionConclusion H la Q := by
  obtain ⟨eps₀,h₀,hF⟩ := production_window_with_typeI_row H la Q hla hH
  refine ⟨eps₀,h₀,fun eps hp hle hlt K => ?_⟩
  obtain ⟨F,CH,hCls,hQ,hCH,hLarge,hCE,hTu,hDG,hMember⟩ := hF eps hp hle hlt K
  refine ⟨F,CH,hCls,hQ,hCH,hLarge,hCE,hTu,hDG,fun y => ?_⟩
  obtain ⟨x,hxy,hx,hW,i,u,h⟩ := hMember y
  exact ⟨x,hxy,hx,hW,i,u,original_word_of_row_witness F x hx i u h⟩


/-- The upstream hypotheses assembled in the production character caller. -/
theorem production_typeI_supplier :
    Nonempty (GlobalTheory.Fc.HypsAlt GlobalTheory.Fc.S0.NL GlobalTheory.Fc.DefiniteSideCondition) := by
  let h := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements :=
    { caraianiLocalGlobalDual := h
      localLanglandsExists := UpperTheory.Zero.LLC.recTExists
      galoisRepOfPolarizedPairLit := h }
  let P := UpperTheory.LiteratureTheorems.published_results_eigen O
  let hΘ := UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O
  let hL := UpperTheory.LiteratureTheorems.local_langlands_gl_recT_exists_of_literature O
  have hVol := SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
    (UpperTheory.LiteratureTheorems.resolution_char_zero_of_literature O)
    (UpperTheory.LiteratureTheorems.principalisation_char_zero_of_literature O)
    PositivityTheory.Tls2.Pl.poincareLelong
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright
    (UpperTheory.LiteratureTheorems.fargues_exact_of_literature O)
    (UpperTheory.LiteratureTheorems.zarhin_statement O)
    (UpperTheory.LiteratureTheorems.nef_rr_of_literature O)
    (UpperTheory.LiteratureTheorems.toroidal_for_fan_ks_of_literature O)
    (UpperTheory.LiteratureTheorems.semi_abelian_lie_seminegative_of_literature O)
    (UpperTheory.LiteratureTheorems.point_separation_pair_of_literature O)
    (UpperTheory.LiteratureTheorems.published_results_arithmetic O)
    (UpperTheory.LiteratureTheorems.grothendieck_deformation_of_literature O)
  exact UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P
    (UpperTheory.LiteratureTheorems.published_results_first O) hΘ.1 hΘ.2 hVol hL
    (fun cDep => UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
      (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))

theorem production_typeI_distinguished_host :
    GlobalTheory.EX.HostExW (3/2 : ℝ) (UpperTheory.Top.GChi Formalism.HC.PChar.one).req := by
  exact UpperTheory.Top.supplyChi Formalism.HC.PChar.one
    (UpperTheory.One.vwin_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter Formalism.HC.PChar.one)

/-- The original production supplier and its distinguished host realize the
full Type I conclusion at a member above any prescribed scale. -/
theorem production_typeI_inhabited_member (y : ℝ) :
    ∃ (H : GlobalTheory.Fc.HypsAlt GlobalTheory.Fc.S0.NL GlobalTheory.Fc.DefiniteSideCondition)
      (eps : ℝ) (_ : 0 < eps) (_ : eps < 1/52) (F : FamP eps) (CH : ℝ),
      H.𝒜 F ∧ (UpperTheory.Top.GChi Formalism.HC.PChar.one).cls (3/2:ℝ) F ∧
      0 ≤ CH ∧ ChosenE F 3 CH ∧ TuSize F ∧ DGamSize F ∧
      ∃ (x : ℝ) (_ : y ≤ x) (hx : F.x1 < x) (_ : x ∈ F.Win) (i : F.Ix x)
        (u : (F.D x i).what₂.Word), TypeIAtOriginalWordWithRow F x hx i u := by
  obtain ⟨H⟩ := production_typeI_supplier
  let Q := UpperTheory.Top.GChi Formalism.HC.PChar.one
  obtain ⟨eps₀,heps₀,hFamily⟩ :=
    production_window_with_typeI_row H (3/2:ℝ) Q (by norm_num) production_typeI_distinguished_host
  let eps := min (eps₀/2) (1/104)
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  have heps₁ : eps ≤ eps₀ := (min_le_left _ _).trans (by linarith)
  have heps₂ : eps < 1/52 := (min_le_right _ _).trans_lt (by norm_num)
  have K : TransportedAlt := by constructor <;> exact 0
  obtain ⟨F,CH,hF,hQ,hCH,_,hCE,hTu,hDG,hMember⟩ := hFamily eps heps heps₁ heps₂ K
  exact ⟨H,eps,heps,heps₂,F,CH,hF,hQ,hCH,hCE,hTu,hDG,hMember y⟩

end

end GlobalTheory.EX.TypeIProduction
