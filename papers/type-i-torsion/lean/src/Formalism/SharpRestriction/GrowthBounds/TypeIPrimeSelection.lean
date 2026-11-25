
import Formalism.SharpRestriction.GrowthBounds.TypeIFiniteDepth
import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
import Formalism.SharpRestriction.GlobalSchurBounds.FrameCodeOfAdditive
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
import Formalism.SharpRestriction.GlobalSchurBounds.LossesSmallShares
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
import Formalism.LocalRingCardinality.Lemmas

import Formalism.ZeroFreeRegion.LogDerivRegion

import Mathlib.NumberTheory.Chebyshev
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPowEqOneLeOfIsCyclicUnits

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions
open Formalism.MainNotions.G
open Formalism.MainNotions.GlobalTheoryTheory
open Filter

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

theorem raw_schi_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) (hy : 0 ≤ y) :
    Formalism.ZeroFreeDirichlet.Schi χ y = sumLamChi χ y := by
  unfold Formalism.ZeroFreeDirichlet.Schi sumLamChi
  refine Finset.sum_congr rfl ?_
  intro n hn
  have h₁ : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h₁)
  have hn₁ : (n : ℝ) ≤ y :=
    (Nat.cast_le.2 (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hy)
  have hpos : 0 ≤ y / (n : ℝ) - 1 := by
    rw [sub_nonneg, le_div_iff₀ hn₀]
    simpa using hn₁
  rw [max_eq_left hpos]

open Classical in
theorem nonprincipal_centered_schi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (y : ℝ) (hy : 0 ≤ y) :
    gChi χ y = Formalism.ZeroFreeDirichlet.Schi χ y -
      Formalism.ZeroFreeDirichlet.negLD χ 1 * (y : ℂ) := by
  rw [gChi, ite_eq_right hχ, raw_schi_eq χ y hy]
  unfold Formalism.ZeroFreeDirichlet.negLD logDerivativeAtOne
  ring

theorem host_primitive_nonprincipal (D : D7) (φ : AddChar (LnkBr.MM D) ℂ) (hφ : φ ≠ 0) :
    let ψ := LnkBr.cOf D φ
    let χ := ZetaZeroFreeRegion.prim D ψ
    IsCharED D χ.2 ∧ χ.2 ≠ 1 ∧ (χ.1 : ℕ) ∣ D.host.condN := by
  intro ψ χ
  have hc : IsCharED D χ.2 := ConductorDivisibility.jnt_prim_isCharED D ψ
  refine ⟨hc, ?_, ?_⟩
  · intro h
    exact hφ ((LnkBr.cOf_eq_one_iff D φ).1 ((LnkBr.prim_one_iff D ψ).1 h))
  · exact ShortIntervalPrimes.level_dvd_condN D χ.2 hc

theorem host_primitive_unramified (D : D7) (φ : AddChar (LnkBr.MM D) ℂ)
    (p : ℕ) (hp : ZetaZeroFreeRegion.Unram D p) :
    let χ := ZetaZeroFreeRegion.prim D (LnkBr.cOf D φ)
    χ.2 (p : ZMod χ.1) = φ (LnkBr.tE D (frob D p)) := by
  intro χ
  exact (LnkBr.prim_spec D (LnkBr.cOf D φ)).2 p hp

theorem served_place_of_candidate {eps : ℝ} (F : FamP eps) (x : ℝ) (hx : F.x1 < x) (i : F.Ix x)
    (u : (F.D x i).what₂.Word) (p : ℕ)
    (hSmall : 3 ≤ (F.L x i).sc.x ^ ((F.L x i).sc.ez/5))
    (hc : Cand (F.D x i) (F.L x i) F.GK p)
    (hoff : p ≠ ((F.D x i).mem u).A.T) :
    ∃ (w : (F.D x i).what₂.places.Pl), (F.D x i).what₂.places.resChar w = p ∧ w ∈ (F.L x i).supp ∧
      GIdx (F.D x i).host ((F.D x i).mem u).A.T ((F.D x i).what₂.places.resChar w) := by
  let D := F.D x i
  let L := F.L x i
  letI : Fact p.Prime := ⟨hc.1⟩
  obtain ⟨⟨w, hw⟩⟩ := Examples₂.PlOver.plNe D p
  refine ⟨w, hw, ?_, ?_⟩
  · apply F.supp_sat x hx i
    change ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n
    rw [hw]
    exact hc.2.1.le.trans (GlobalTheory.EX.Led.X'_le_X'' L.sc D.R)
  · change GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)
    rw [hw]
    exact gIdx_of_cand (F.params x hx i) F.GK hSmall u p hc hoff

theorem orbit_of_retained_adjacent_top {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (K : Consts) (p : ℕ) (t : G.HH D)
    (hc : Cand D L K p) (hSig : Sig X K (aL L) (bL L) p ≤ L.sc.x ^ (-L.sc.eps))
    (ht : t ∈ D.host.TT) (ht' : t + hP D p ∈ D.host.TT)
    (hGood : Good X p (X.bs (stepP D p) t)) :
    ∃ t₀ ∈ VV X K (aL L) (bL L) p, t ∈ topsOn X p t₀ ∧ t + hP D p ∈ topsOn X p t₀ := by
  classical
  let t₀ := X.bs (stepP D p) t
  have hReps : t₀ ∈ reps X p := Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hGoodReps : t₀ ∈ goodReps X p := Finset.mem_filter.mpr ⟨hReps, hGood⟩
  refine ⟨t₀, served_orbits_in_set X K (aL L) (bL L) p hc hSig hGoodReps,
    Finset.mem_filter.mpr ⟨ht, rfl⟩, Finset.mem_filter.mpr ⟨ht', ?_⟩⟩
  have hInert := hc.2.2.1
  have he := AuxBlock8.Pf.St.frobenius_step_large_order hInert
  change X.bs (stepP D p) (t + hP D p) = X.bs (stepP D p) t
  rw [he]
  exact X.bs_step _ _


/-- Transfer the real exceptional-zero contribution from the original thin
scale to the lower Type I window, with a bound uniform as beta tends to one. -/
theorem exceptional_power_transfer (X y β η : ℝ)
    (hX : 1 < X) (hy : X ^ (3/4 : ℝ) ≤ y)
    (hβ₁ : 1/2 ≤ β) (hβ₂ : β < 1) (hη₀ : 0 ≤ η) (hη : η ≤ Real.exp (-1))
    (hAtX : X ^ (β-1) / (β * (1-β)) ≤ η) :
    y ^ (β-1) / (β * (1-β)) ≤ η ^ (3/4 : ℝ) * (2 * Real.log X) := by
  have hX₀ : 0 < X := zero_lt_one.trans hX
  have hb₀ : 0 < β := by linarith
  have hb₁ : 0 < 1-β := by linarith
  have hden : 0 < β * (1-β) := mul_pos hb₀ hb₁
  have hden' : β * (1-β) ≤ 1 := by
    calc β * (1-β) ≤ 1 * (1-β) := mul_le_mul_of_nonneg_right hβ₂.le hb₁.le
      _ ≤ 1 := by linarith
  have hPow : X ^ (β-1) ≤ η :=
    ((div_le_iff₀ hden).mp hAtX).trans (by simpa using mul_le_mul_of_nonneg_left hden' hη₀)
  have hgExp : Real.exp (Real.log X * (β-1)) ≤ Real.exp (-1) := by
    rw [← Real.rpow_def_of_pos hX₀]
    exact hPow.trans hη
  have hgap : 1 ≤ (1-β) * Real.log X := by
    have h := Real.exp_le_exp.mp hgExp
    nlinarith only [h]
  have hgap₂ : 1 ≤ (2*β) * ((1-β) * Real.log X) := by
    simpa only [one_mul] using mul_le_mul (show 1 ≤ 2*β by linarith) hgap zero_le_one (by positivity)
  have hDiv : 1 / (β * (1-β)) ≤ 2*Real.log X := by
    rw [div_le_iff₀ hden]
    linarith only [hgap₂]
  have hPowY : y ^ (β-1) ≤ η ^ (3/4 : ℝ) := by
    calc
      _ ≤ (X ^ (3/4 : ℝ)) ^ (β-1) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hX₀ _) hy (by linarith)
      _ = (X ^ (β-1)) ^ (3/4 : ℝ) := by rw [← Real.rpow_mul hX₀.le, ← Real.rpow_mul hX₀.le, mul_comm]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hX₀.le _) hPow (by norm_num)
  have hy₀ : 0 < y := (Real.rpow_pos_of_pos hX₀ _).trans_le hy
  rw [div_eq_mul_one_div]
  exact mul_le_mul hPowY hDiv (by positivity) (by positivity)

theorem normalized_exceptional_term (y β : ℝ) (hy : 0 < y) (hβ₁ : 1/2 ≤ β) (hβ₂ : β < 1) :
    ‖(y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ)-1))‖ / y =
      y ^ (β-1) / (β*(1-β)) := by
  have hb : (0 : ℝ) < β := by linarith
  have hb' : 0 < 1-β := by linarith
  have hcast : (β : ℂ)-1 = ((β-1 : ℝ) : ℂ) := by push_cast <;> rfl
  rw [norm_div, norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.ofReal_re, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hb, abs_of_neg (by linarith : β-1 < 0), Real.rpow_sub hy, Real.rpow_one]
  field_simp [hy.ne', hb.ne', hb'.ne', sub_ne_zero.mpr hβ₂.ne]
  <;> ring


open Formalism.ZeroFreeDirichlet in
def contourRelativeError (c C C₀ y T L : ℝ) : ℝ :=
  2 * Real.pi * Real.exp 1 * (Real.log y + C₀) / T +
  6 * Real.exp 1 * (C * L^2 + 1) / T^2 +
  ((C * L^2 + 24 * L / c) * (8 * L / c) * (2 * T) + 8 * L / c) *
    Real.exp (-(c / (4*L)) * Real.log y)

open Formalism.ZeroFreeDirichlet in
theorem centered_character_contour_relative :
    ∃ c C C₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ C₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∃ B : Finset ℝ, B.card ≤ 1 ∧ (∀ β ∈ B, 1/2 ≤ β ∧ β < 1) ∧
        ∀ y T : ℝ, 2 ≤ y → 1 ≤ T →
        ‖gChi χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ)*((β : ℂ)-1))‖ / y ≤
          contourRelativeError c C C₀ y T (Real.log ((q : ℝ)*(T+2))) := by
  classical
  obtain ⟨cZ, hcZ, hZ⟩ := zFRDirichlet
  let c : ℝ := min cZ (1/20)
  have hc : 0 < c := lt_min hcZ (by norm_num)
  have hc₂ : c ≤ 1/20 := min_le_right _ _
  obtain ⟨CD, hCD⟩ := logDerivRegionChi c hc hc₂
  obtain ⟨C₀, hC₀, hR⟩ := l_log_deriv_right
  let C : ℝ := max CD 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨c, C, C₀, hc, hC, hC₀, ?_⟩
  intro q _ χ hχ
  obtain ⟨B, hE⟩ := exists_exceptional_zero_set cZ c (min_le_left _ _) hZ q χ
  refine ⟨B, hE.1, ?_, ?_⟩
  · intro β hβ
    obtain ⟨_, hreg, hz, _⟩ := hE.2.1 β hβ
    refine ⟨half_le_of_real_in_region hc₂ hreg, ?_⟩
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by simpa using not_lt.mp h) hz
  · intro y T hy hT
    let L : ℝ := Real.log ((q : ℝ)*(T+2))
    have hypos : 0 < y := by linarith
    have hTpos : 0 < T := by linarith
    have hq : 1 ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hL : 0 < L := by
      apply Real.log_pos
      have hT' : 1 < T+2 := by linarith
      exact hT'.trans_le (le_mul_of_one_le_left (by positivity) hq)
    have hD : ∀ s : ℂ, InRegion (c/2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤
          C * Real.log ((q : ℝ) * (|s.im| + 2))^2 := by
      intro s hs hBs
      exact (hCD q χ B hχ hE s hs hBs).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    obtain ⟨σ, hσ, hbound⟩ := chebyshev_character_explicit_general
      perron_formula_character rectangle_contour_shift_character c C C₀ hc hc₂ hC hC₀
      χ B hχ hE hD (hR q χ) y T L hy hT rfl
    have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hv : y ^ σ / y ≤ Real.exp (-(c/(4*L)) * Real.log y) := by
      rw [← Real.rpow_sub_one hypos.ne', Real.rpow_def_of_pos hypos, Real.exp_le_exp]
      have he : σ - 1 ≤ -(c/(4*L)) := by linarith only [hσ]
      nlinarith only [mul_le_mul_of_nonneg_left he hlog]
    let A := 2 * Real.pi * Real.exp 1 * (Real.log y + C₀) / T +
      6 * Real.exp 1 * (C * L^2 + 1) / T^2
    let W := (C * L^2 + 24 * L / c) * (8 * L / c) * (2*T) + 8*L/c
    have hW : 0 ≤ W := by unfold W; positivity
    rw [nonprincipal_centered_schi χ hχ y hypos.le]
    change _ ≤ A + W * Real.exp (-(c/(4*L))* Real.log y)
    calc
      _ ≤ (2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T +
          (C * L^2 + 1) * (Real.exp 1 * y) / T^2 * 3 +
          (C * L^2 + 1) * (Real.exp 1 * y) / T^2 * 3 +
          (C * L^2 + 24 * L / c) * y^σ * (8 * L / c) * (2*T) +
          y^σ * (8*L/c)) / y := div_le_div_of_nonneg_right hbound hypos.le
      _ = A + W * (y^σ/y) := by
        unfold A W
        field_simp [hypos.ne', hTpos.ne', hc.ne']
        <;> ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hW)


theorem family_host_log_conductor_bound {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      Real.log ((F.D x i).host.condN : ℝ) ≤ 4 * x ^ (eps/4) := by
  let C := max F.Co 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  have hα : 0 < eps/4 := by positivity
  have hCev := (tendsto_rpow_atTop hα).eventually_ge_atTop (Real.log C)
  have hLog := AuxBlock8.Pf.ev_log 3 (eps/4) hα
  filter_upwards [hCev, hLog, eventually_gt_atTop (1 : ℝ)] with x hLc hLx hx1
  intro hx i
  let D := F.D x i
  let L := F.L x i
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hX : L.sc.x = x := F.L_x x i hx
  have hE : L.sc.eps = eps := F.L_eps x i
  obtain ⟨hN, _, _, _, _, _, hQD, _⟩ := F.sizes x hx i
  have hn := hN.2
  change (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8*L.sc.eps + L.sc.eps/100) at hn
  rw [hX, hE] at hn
  have hn' := hn.trans (Real.rpow_le_rpow_of_exponent_le hx1.le
    (by linarith only [heps'] : 2 + 8*eps + eps/100 ≤ 3))
  have hq0 : 0 < (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.pos
  have hd0 : 0 < (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.pos
  have hQ0 : 0 < (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
  have hQ : (D.host.QS : ℝ) ≤ C * x ^ (3 : ℝ) :=
    (F.QS_le_Co x i hx).trans (mul_le_mul (le_max_left _ _) hn' (by positivity) hC.le)
  have hQlog := Real.log_le_log hQ0 hQ
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0] at hQlog
  have hq := hQD.2.2.1
  have hd := hQD.2.2.2.2.1
  change Real.log (D.host.q : ℝ) ≤ L.sc.x ^ (L.sc.eps/5 + L.sc.eps/100) at hq
  change Real.log (D.host.d : ℝ) ≤ L.sc.x ^ (L.sc.eps/5 + L.sc.eps/100) at hd
  rw [hX, hE] at hq hd
  have hr := Real.rpow_le_rpow_of_exponent_le hx1.le
    (by linarith only [heps] : eps/5 + eps/100 ≤ eps/4)
  change Real.log (((D.host.QS * D.host.q * D.host.d : ℕ)) : ℝ) ≤ _
  push_cast
  rw [Real.log_mul (mul_ne_zero hQ0.ne' hq0.ne') hd0.ne', Real.log_mul hQ0.ne' hq0.ne']
  linarith only [hQlog, hq.trans hr, hd.trans hr, hLc, hLx]

theorem family_index_scale_eventually {eps : ℝ} (F : FamP eps) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      3 ≤ (F.L x i).sc.x ^ ((F.L x i).sc.ez/5) := by
  obtain ⟨i₀⟩ := F.Ix_zero
  have hJ := (F.L 0 i₀).sc.one_le_J
  rw [F.L_J 0 i₀] at hJ
  have ha : 0 < (eps/F.J)/5 := by positivity
  have hf := (tendsto_rpow_atTop ha).eventually_ge_atTop 3
  filter_upwards [hf] with x hx
  intro hxi i
  rw [Scale.ez, F.L_x x i hxi, F.L_eps x i, F.L_J x i]
  exact hx


theorem uniform_contour_relative_error (eps c C C₀ : ℝ)
    (heps : 0 < eps) (heps' : eps < 1/52) (hc : 0 < c) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ x : ℝ in atTop, ∀ y L : ℝ, 0 < L → L ≤ 6*x^(eps/4) →
        (3/4)*x^(eps/3) ≤ Real.log y → Real.log y ≤ 2*x^(eps/3) →
        contourRelativeError c C C₀ y (x^(14:ℝ)) L ≤ A*x^(-13:ℝ) := by
  let A₁ := 2 * Real.pi * Real.exp 1 * (2+C₀)
  let A₂ := 6 * Real.exp 1 * (36*C+1)
  let A₃ := (36*C+144/c)*(48/c)*2 + 48/c
  have hA₁ : 0 ≤ A₁ := by unfold A₁; positivity
  have hA₂ : 0 ≤ A₂ := by unfold A₂; positivity
  have hA₃ : 0 ≤ A₃ := by unfold A₃; positivity
  refine ⟨A₁ + A₂ + A₃, by positivity, ?_⟩
  have hEv := exp_neg_rpow_eventually_le_rpow (c/32) (eps/12) 29 (by positivity) (by positivity)
  filter_upwards [hEv, eventually_ge_atTop (1:ℝ)] with x hEv hx
  intro y L hL hL' hy hy'
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  let r := x^(eps/4)
  let T := x^(14:ℝ)
  have hr : 1 ≤ r := Real.one_le_rpow hx (by positivity)
  have hT : 1 ≤ T := Real.one_le_rpow hx (by norm_num)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hsq : r^2 = x^(eps/2) := by
    unfold r
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    push_cast
    ring
  have hcube : r^3 = x^(3*eps/4) := by
    unfold r
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    push_cast
    ring
  have hSqx : r^2 ≤ x := by
    rw [hsq]
    exact (Real.rpow_le_rpow_of_exponent_le hx (by linarith only [heps'] : eps/2 ≤ 1)).trans (Real.rpow_one x).le
  have hCubex : r^3 ≤ x := by
    rw [hcube]
    exact (Real.rpow_le_rpow_of_exponent_le hx (by linarith only [heps'] : 3*eps/4 ≤ 1)).trans (Real.rpow_one x).le
  have hExpx : x^(eps/3) ≤ x :=
    (Real.rpow_le_rpow_of_exponent_le hx (by linarith only [heps'] : eps/3 ≤ 1)).trans (Real.rpow_one x).le
  have hLog : Real.log y + C₀ ≤ (2+C₀)*x := by
    have h₁ := mul_le_mul_of_nonneg_left hExpx (by norm_num : (0:ℝ) ≤ 2)
    have h₂ := mul_le_mul_of_nonneg_left hx hC₀
    linarith only [hy', h₁, h₂]
  have hLsq : L^2 ≤ 36*r^2 := by
    have hh := pow_le_pow_left₀ hL.le hL' 2
    nlinarith only [hh]
  have hLsq' : L^2 ≤ 36*x := hLsq.trans (by gcongr)
  have hH : C*L^2 + 1 ≤ (36*C+1)*x := by
    have hh := mul_le_mul_of_nonneg_left hLsq' hC
    linarith only [hh, hx]
  have hpowT : T ≤ T^2 := by nlinarith [mul_le_mul_of_nonneg_left hT hTpos.le]
  have h13 : x/T = x^(-13:ℝ) := by
    calc
      _ = x^(1:ℝ)/x^(14:ℝ) := by rw [Real.rpow_one] <;> rfl
      _ = _ := by rw [← Real.rpow_sub hxpos]; norm_num
  have hFirst : 2*Real.pi*Real.exp 1*(Real.log y+C₀)/T ≤ A₁*x^(-13:ℝ) := by
    rw [← h13]
    calc
      _ ≤ 2*Real.pi*Real.exp 1*((2+C₀)*x)/T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLog (by positivity)) hTpos.le
      _ = _ := by unfold A₁; ring
  have hSecond : 6*Real.exp 1*(C*L^2+1)/T^2 ≤ A₂*x^(-13:ℝ) := by
    rw [← h13]
    calc
      _ ≤ 6*Real.exp 1*((36*C+1)*x)/T^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH (by positivity)) (by positivity)
      _ = A₂*(x/T^2) := by unfold A₂; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hxpos.le hTpos hpowT) hA₂
  have hRleSq : r ≤ r^2 := by nlinarith [mul_le_mul_of_nonneg_left hr (zero_le_one.trans hr)]
  have ht₁ : C*L^2 + 24*L/c ≤ (36*C+144/c)*r^2 := by
    have hh₁ := mul_le_mul_of_nonneg_left hLsq hC
    have hh₂ : 24*L/c ≤ (144/c)*r := calc
      _ ≤ 24*(6*r)/c :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL' (by norm_num)) hc.le
      _ = _ := by ring
    have hh₃ := mul_le_mul_of_nonneg_left hRleSq (show 0 ≤ 144/c by positivity)
    calc
      _ ≤ C*(36*r^2) + (144/c)*r^2 := add_le_add hh₁ (hh₂.trans hh₃)
      _ = _ := by ring
  have ht₂ : 8*L/c ≤ (48/c)*r := calc
    _ ≤ 8*(6*r)/c :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL' (by norm_num)) hc.le
    _ = _ := by ring
  let W := (C*L^2+24*L/c)*(8*L/c)*(2*T)+8*L/c
  have hW : 0 ≤ W := by unfold W; positivity
  have hWr : W ≤ A₃*(r^3*T) := by
    have h₁ := mul_le_mul ht₁ ht₂ (by positivity) (by positivity : 0 ≤ (36*C+144/c)*r^2)
    have h₂ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ 2*T by positivity)
    have h₃ : r ≤ r^3*T := calc
      r ≤ r^3 := by nlinarith [mul_le_mul_of_nonneg_left hr (show 0 ≤ r^2 by positivity), hRleSq]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hT
    have h₄ := ht₂.trans (mul_le_mul_of_nonneg_left h₃ (show 0 ≤ 48/c by positivity))
    unfold W A₃
    linarith only [h₂, h₄]
  have hWx : W ≤ A₃*(x*T) :=
    hWr.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCubex hTpos.le) hA₃)
  have hprod : x^(eps/12)*r = x^(eps/3) := by
    unfold r
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hML : x^(eps/12)*L ≤ 8*Real.log y := by
    calc
      _ ≤ x^(eps/12)*(6*r) := mul_le_mul_of_nonneg_left hL' (by positivity)
      _ = 6*x^(eps/3) := by rw [← hprod]; ring
      _ ≤ _ := by linarith only [hy]
  have hArg : (c/32)*x^(eps/12) ≤ (c/(4*L))*Real.log y := by
    rw [show c/(4*L)*Real.log y = (c*Real.log y)/(4*L) by ring,
      le_div_iff₀ (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hML (show 0 ≤ c/8 by positivity)
    linarith only [hh]
  have hDecay : Real.exp (-(c/(4*L))*Real.log y) ≤ x^(-29:ℝ) := by
    refine (Real.exp_le_exp.mpr ?_).trans hEv
    linarith only [hArg]
  have hpow : x*T*x^(-29:ℝ) ≤ x^(-13:ℝ) := by
    calc
      _ = x^(1:ℝ)*x^(14:ℝ)*x^(-29:ℝ) := by rw [Real.rpow_one] <;> rfl
      _ = x^(-14:ℝ) := by rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hThird : W*Real.exp (-(c/(4*L))*Real.log y) ≤ A₃*x^(-13:ℝ) := by
    calc
      _ ≤ (A₃*(x*T))*x^(-29:ℝ) := mul_le_mul hWx hDecay (by positivity) (by positivity)
      _ = A₃*(x*T*x^(-29:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hA₃
  change _ ≤ (A₁+A₂+A₃)*x^(-13:ℝ)
  unfold contourRelativeError
  change _ + _ + W * Real.exp (-(c/(4*L))*Real.log y) ≤ _
  linarith only [hFirst, hSecond, hThird]


theorem family_typeI_contour_scales {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      ∀ q : ℕ, 0 < q → q ≤ (F.D x i).host.condN →
      let L := (F.L x i).sc
      let Z := L.X' ^ (3/4 : ℝ)
      let T := x^(14:ℝ)
      let logQ := Real.log ((q : ℝ)*(T+2))
      1 ≤ T ∧ 0 < logQ ∧ logQ ≤ 6*x^(eps/4) ∧
        ∀ y : ℝ, Z ≤ y → y ≤ 2*L.X' →
          2 ≤ y ∧ (3/4)*x^(eps/3) ≤ Real.log y ∧ Real.log y ≤ 2*x^(eps/3) := by
  have hα : 0 < eps/4 := by positivity
  have hβ : 0 < eps/3 := by positivity
  have hC := family_host_log_conductor_bound F heps heps'
  have hlogT := AuxBlock8.Pf.ev_log 14 (eps/4) hα
  have hlog3 := (tendsto_rpow_atTop hα).eventually_ge_atTop (Real.log 3)
  have hE := (tendsto_rpow_atTop hβ).eventually_ge_atTop 16
  filter_upwards [hC, hlogT, hlog3, hE, eventually_ge_atTop (1:ℝ)] with x hC htlog h3 he hx
  intro hxi i q hq hq'
  intro L Z T logQ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hT : 1 ≤ T := Real.one_le_rpow hx (by norm_num)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqOne : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hTplus : 0 < T+2 := by linarith
  have hlogQpos : 0 < logQ := by
    apply Real.log_pos
    exact (show 1 < T+2 by linarith).trans_le (le_mul_of_one_le_left hTplus.le hqOne)
  have hqLog := (Real.log_le_log hqpos (show (q : ℝ) ≤ ((F.D x i).host.condN : ℝ) by exact_mod_cast hq')).trans
    (hC hxi i)
  have hLt : Real.log (T+2) ≤ Real.log 3 + 14*Real.log x := by
    calc
      _ ≤ Real.log (3*T) := Real.log_le_log hTplus (by linarith)
      _ = _ := by
        rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hTpos.ne']
        change _ = Real.log 3 + 14*Real.log x
        rw [show Real.log T = 14*Real.log x by
          change Real.log (x^(14:ℝ)) = _; rw [Real.log_rpow hxpos] <;> ring]
  have hLogBound : logQ ≤ 6*x^(eps/4) := by
    change Real.log ((q : ℝ)*(T+2)) ≤ _
    rw [Real.log_mul hqpos.ne' hTplus.ne']
    linarith only [hqLog, hLt, htlog, h3]
  refine ⟨hT, hlogQpos, hLogBound, ?_⟩
  intro y hy hy'
  have hX : L.X' = Real.exp (x^(eps/3)) := by
    change (F.L x i).sc.X' = _
    rw [Scale.X', F.L_x x i hxi, F.L_eps x i]
  have hZ : Z = Real.exp ((3/4)*x^(eps/3)) := by
    change L.X' ^ (3/4:ℝ) = _
    rw [hX, mul_comm, Real.exp_mul]
  have hZpos : 0 < Z := by rw [hZ]; positivity
  have hypos := hZpos.trans_le hy
  have hy2 : 2 ≤ y := by
    refine le_trans ?_ hy
    rw [hZ]
    have hh := Real.add_one_le_exp ((3/4)*x^(eps/3))
    linarith only [he, hh]
  have hXpos : 0 < L.X' := by rw [hX]; positivity
  have hZlog := Real.log_le_log hZpos hy
  rw [hZ, Real.log_exp] at hZlog
  have hylog := Real.log_le_log hypos hy'
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hXpos.ne', hX, Real.log_exp] at hylog
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  exact ⟨hy2, hZlog, by linarith only [hylog, he, hlog2]⟩


private theorem normalized_norm_sub_le (a b : ℂ) (y : ℝ) (hy : 0 ≤ y) :
    ‖a-b‖/y ≤ ‖a‖/y + ‖b‖/y := by
  rw [← add_div]
  exact div_le_div_of_nonneg_right (norm_sub_le _ _) hy

/-- Uniform transfer of the original thin estimate to every lower Type I
stencil node. The character and interval point may depend on the member. -/
theorem family_typeI_nonprincipal_estimate {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) (c₆ : ℝ) (hc₆ : 0 < c₆)
    (hThin : ChosenThin F c₆) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        IsCharED (F.D x i) χ → χ ≠ 1 →
        let X := (F.L x i).sc.X'
        let Z := X ^ (3/4:ℝ)
        ∀ y : ℝ, Z ≤ y → y ≤ 2*X → ‖gChi χ y‖/y ≤ K*x^(-9:ℝ) := by
  classical
  obtain ⟨c,C,C₀,hc,hC,hC₀,hContour⟩ := centered_character_contour_relative
  obtain ⟨A,hA,hUniform⟩ := uniform_contour_relative_error eps c C C₀ heps heps' hc hC hC₀
  let A' := 2 * (A+1)^(3/4:ℝ)
  have hA' : 0 ≤ A' := by unfold A'; positivity
  refine ⟨A+A', by positivity, ?_⟩
  obtain ⟨lower,hThin⟩ := hThin
  have hSc := family_typeI_contour_scales F heps heps'
  have hE := exp_neg_rpow_eventually_le_rpow c₆ (eps/8) 13 hc₆ (by positivity)
  have hSmall := AuxBlock8.Pf.ev_pow ((A+1)*Real.exp 1) (-13) 0 (by norm_num)
  filter_upwards [hUniform,hSc,hE,hSmall,eventually_ge_atTop lower,eventually_ge_atTop (1:ℝ)]
    with x hU hSc hE hSmall hxLower hxOne
  intro hxi i q inst χ hED hχ X Z y hy hy'
  let T := x^(14:ℝ)
  let L := Real.log ((q:ℝ)*(T+2))
  let η := (A+1)*x^(-13:ℝ)
  have hxpos : 0 < x := zero_lt_one.trans_le hxOne
  have hqpos := Nat.pos_of_ne_zero (NeZero.ne q)
  have hDiv : q ∣ (F.D x i).host.condN := ShortIntervalPrimes.level_dvd_condN _ χ hED
  have hqLe := Nat.le_of_dvd (F.D x i).host.condN_pos hDiv
  obtain ⟨hT,hLpos,hLbound,hNodes⟩ := hSc hxi i q hqpos hqLe
  have hXexp : X = Real.exp (x^(eps/3)) := by
    change (F.L x i).sc.X' = _
    rw [Scale.X', F.L_x x i hxi, F.L_eps x i]
  have hXgt : 1 < X := by
    rw [hXexp]
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have hXpos : 0 < X := zero_lt_one.trans hXgt
  have hZle : Z ≤ X :=
    (Real.rpow_le_rpow_of_exponent_le hXgt.le (by norm_num : (3/4:ℝ) ≤ 1)).trans (Real.rpow_one X).le
  have hy2 : 2 ≤ y := (hNodes y hy hy').1
  have hypos : 0 < y := by linarith
  have hX₂ : X ≤ 2*X := by linarith
  obtain ⟨B,hB,hβ,hBound⟩ := hContour q χ hχ
  let E (v : ℝ) : ℂ := ∑ β ∈ B, (v:ℂ)^(β:ℂ)/((β:ℂ)*((β:ℂ)-1))
  have hRel (v : ℝ) (hv : Z ≤ v) (hv' : v ≤ 2*X) :
      ‖gChi χ v+E v‖/v ≤ A*x^(-13:ℝ) := by
    obtain ⟨hv2, hvl, hvu⟩ := hNodes v hv hv'
    exact (hBound v T hv2 hT).trans (hU v L hLpos hLbound hvl hvu)
  have hLarge := hThin x hxLower i q χ hED X (by rw [← hXexp]; linarith)
  change ‖gChi χ X‖ ≤ X*Real.exp (-(c₆*x^(eps/8))) at hLarge
  have hLarge' : ‖gChi χ X‖/X ≤ x^(-13:ℝ) := by
    have hh : ‖gChi χ X‖/X ≤ Real.exp (-(c₆*x^(eps/8))) := by
      apply (div_le_iff₀ hXpos).mpr
      simpa only [mul_comm] using hLarge
    exact hh.trans (by simpa only [neg_mul] using hE)
  have hAtX : ‖E X‖/X ≤ η := by
    have hh := normalized_norm_sub_le (gChi χ X + E X) (gChi χ X) X hXpos.le
    rw [show gChi χ X + E X - gChi χ X = E X by abel] at hh
    refine hh.trans ((add_le_add (hRel X hZle hX₂) hLarge').trans_eq ?_)
    unfold η
    ring
  have hη₀ : 0 ≤ η := by unfold η; positivity
  have hη : η ≤ Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hh : η*Real.exp 1 = ((A+1)*Real.exp 1)*x^(-13:ℝ) := by unfold η; ring
    rw [hh]
    simpa only [Real.rpow_zero] using hSmall
  have hScale : η^(3/4:ℝ)*(2*Real.log X) ≤ A'*x^(-9:ℝ) := by
    rw [hXexp, Real.log_exp]
    unfold η
    rw [Real.mul_rpow (by positivity : 0 ≤ A+1) (by positivity : 0 ≤ x^(-13:ℝ)),
      ← Real.rpow_mul hxpos.le]
    have heq : x^((-13:ℝ)*(3/4))*x^(eps/3) = x^((-13:ℝ)*(3/4)+eps/3) :=
      (Real.rpow_add hxpos _ _).symm
    calc
      _ = A'*(x^((-13:ℝ)*(3/4))*x^(eps/3)) := by unfold A'; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (heq.le.trans
        (Real.rpow_le_rpow_of_exponent_le hxOne (by linarith only [heps']))) hA'
  have hEbound : ‖E y‖/y ≤ A'*x^(-9:ℝ) := by
    rcases B.eq_empty_or_nonempty with hB₀ | ⟨β,hβB⟩
    · simp [E,hB₀] <;> positivity
    · have hBS : B = {β} :=
        (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hβB) (by simpa using hB)).symm
      have hh := hβ β hβB
      have hAtX' : X ^ (β-1) / (β*(1-β)) ≤ η := by
        simpa only [E,hBS,Finset.sum_singleton,normalized_exceptional_term X β hXpos hh.1 hh.2] using hAtX
      have hY := exceptional_power_transfer X y β η hXgt hy hh.1 hh.2 hη₀ hη hAtX'
      simpa only [E,hBS,Finset.sum_singleton,normalized_exceptional_term y β hypos hh.1 hh.2] using hY.trans hScale
  have hMain : ‖gChi χ y+E y‖/y ≤ A*x^(-9:ℝ) :=
    (hRel y hy hy').trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hxOne (by norm_num)) hA)
  have hFinal := normalized_norm_sub_le (gChi χ y + E y) (E y) y hypos.le
  rw [add_sub_cancel_right] at hFinal
  exact hFinal.trans ((add_le_add hMain hEbound).trans_eq (by ring))


def typeITentWeight (Z : ℝ) (n : ℕ) : ℝ :=
  (abelian₂ n) * halfStepTent Z n / Z

theorem typeI_raw_stencil (Z : ℝ) (hZ : 0 < Z) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∑ n ∈ Finset.Icc 1 ⌊2*Z⌋₊, (typeITentWeight Z n : ℂ) * χ (n : ZMod q) =
      (sumLamChi χ (2*Z) - 2*sumLamChi χ (3*Z/2) + sumLamChi χ Z) / (Z : ℂ) := by
  rw [half_step_raw_character_sum χ Z hZ.le, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  unfold typeITentWeight
  push_cast
  ring

open Classical in
theorem typeI_nonprincipal_stencil (Z E : ℝ) (hZ : 0 < Z) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (h₁ : ‖gChi χ Z‖/Z ≤ E) (h₂ : ‖gChi χ (3*Z/2)‖/(3*Z/2) ≤ E)
    (h₃ : ‖gChi χ (2*Z)‖/(2*Z) ≤ E) :
    ‖∑ n ∈ Finset.Icc 1 ⌊2*Z⌋₊, (typeITentWeight Z n : ℂ) * χ (n : ZMod q)‖ ≤ 6*E := by
  have hZ₂ : 0 < 2*Z := by positivity
  have hZₘ : 0 < 3*Z/2 := by positivity
  have h₁' := (div_le_iff₀ hZ).mp h₁
  have h₂' := (div_le_iff₀ hZₘ).mp h₂
  have h₃' := (div_le_iff₀ hZ₂).mp h₃
  have heq : sumLamChi χ (2*Z) - 2*sumLamChi χ (3*Z/2) + sumLamChi χ Z =
      gChi χ (2*Z) - 2*gChi χ (3*Z/2) + gChi χ Z := by
    simp only [gChi, ite_eq_right hχ, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [typeI_raw_stencil Z hZ χ, heq, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  apply (div_le_iff₀ hZ).mpr
  have hB := norm_add_le (gChi χ (2*Z) - 2*gChi χ (3*Z/2)) (gChi χ Z)
  have hC := norm_sub_le (gChi χ (2*Z)) (2*gChi χ (3*Z/2))
  rw [norm_mul] at hC
  have hD : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [hD] at hC
  linarith only [hB,hC,h₁',h₂',h₃']

theorem typeI_principal_stencil (Z : ℝ) (hZ : 0 < Z) :
    ∑ n ∈ Finset.Icc 1 ⌊2*Z⌋₊, typeITentWeight Z n =
      Real.log (32/27) + (Formalism.Gz (2*Z) - 2*Formalism.Gz (3*Z/2) + Formalism.Gz Z) / Z := by
  let χ : DirichletCharacter ℂ 1 := 1
  have hχ (n : ℕ) : χ (n : ZMod 1) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  have hSz (y : ℝ) (hy : 0 ≤ y) : sumLamChi χ y = (Formalism.Sz y : ℂ) := by
    rw [← raw_schi_eq χ y hy]
    unfold Formalism.Sz Formalism.ZeroFreeDirichlet.Schi
    push_cast
    simp only [hχ, mul_one]
  have hχraw := typeI_raw_stencil Z hZ χ
  simp_rw [hχ, mul_one] at hχraw
  rw [hSz _ (by positivity), hSz _ (by positivity), hSz _ hZ.le] at hχraw
  have hreal : ∑ n ∈ Finset.Icc 1 ⌊2*Z⌋₊, typeITentWeight Z n =
      (Formalism.Sz (2*Z) - 2*Formalism.Sz (3*Z/2) + Formalism.Sz Z) / Z := by
    exact_mod_cast hχraw
  rw [hreal]
  have hf (y : ℝ) :
      Formalism.Sz y = Formalism.Gz y + y*Real.log y - (1+Real.eulerMascheroniConstant)*y := by
    unfold Formalism.Gz
    ring
  rw [hf (2*Z), hf (3*Z/2), hf Z]
  calc
    _ = ((2*Z)*Real.log (2*Z)-2*((3*Z/2)*Real.log (3*Z/2))+Z*Real.log Z)/Z +
          (Formalism.Gz (2*Z)-2*Formalism.Gz (3*Z/2)+Formalism.Gz Z)/Z := by ring
    _ = _ := by rw [half_step_log_main Z hZ]

theorem typeI_principal_node_estimate {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ y : ℝ,
      2 ≤ y → (3/4)*x^(eps/3) ≤ Real.log y → |Formalism.Gz y|/y ≤ K*x^(-13:ℝ) := by
  obtain ⟨c,C,hc,hPNT⟩ := Formalism.ZF.gzPNT
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨K,hK,?_⟩
  have hε := exp_neg_rpow_eventually_le_rpow (c/2) (eps/6) 13 (by positivity) (by positivity)
  filter_upwards [hε,eventually_ge_atTop (1:ℝ)] with x hx hx₁
  intro y hy hylog
  have hx₀ : 0 < x := zero_lt_one.trans_le hx₁
  have hy₀ : 0 < y := by linarith
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hs : (x^(eps/6))^2 = x^(eps/3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx₀.le]
    congr 1
    push_cast
    ring
  have hroot : (1/2)*x^(eps/6) ≤ Real.sqrt (Real.log y) := by
    apply (Real.le_sqrt (by positivity) hl).mpr
    rw [mul_pow, hs]
    have hpow : 0 ≤ x^(eps/3) := by positivity
    nlinarith only [hylog,hpow]
  have hexp : Real.exp (-c*Real.sqrt (Real.log y)) ≤ x^(-13:ℝ) := by
    refine (Real.exp_le_exp.mpr ?_).trans hx
    nlinarith only [mul_le_mul_of_nonneg_left hroot hc.le]
  calc
    _ ≤ K*Real.exp (-c*Real.sqrt (Real.log y)) := by
      apply (div_le_iff₀ hy₀).mpr
      refine (hPNT y hy).trans ?_
      calc
        C*y*Real.exp (-c*Real.sqrt (Real.log y)) ≤ K*y*Real.exp (-c*Real.sqrt (Real.log y)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hy₀.le)
            (Real.exp_pos _).le
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hK


open Classical in
def typeIWindowPrimes (Z : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊2*Z⌋₊).filter fun p => p.Prime ∧ Z < (p:ℝ) ∧ (p:ℝ) < 2*Z

theorem mem_typeIWindowPrimes {Z : ℝ} (hZ : 0 ≤ Z) {p : ℕ} :
    p ∈ typeIWindowPrimes Z ↔ p.Prime ∧ Z < (p:ℝ) ∧ (p:ℝ) < 2*Z := by
  classical
  rw [typeIWindowPrimes, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact Finset.mem_Icc.mpr ⟨h.1.one_lt.le, (Nat.le_floor_iff (by positivity)).mpr h.2.2.le⟩

theorem half_step_tent_zero_outside (Z n : ℝ) (hZ : 0 ≤ Z) (hn : 0 < n)
    (h : ¬ (Z < n ∧ n < 2*Z)) : halfStepTent Z n = 0 := by
  rw [half_step_tent_eq Z n hZ hn]
  have hm : min (n-Z) (2*Z-n) ≤ 0 := by
    by_contra! hh
    obtain ⟨h₁,h₂⟩ := lt_min_iff.mp hh
    exact h ⟨by linarith, by linarith⟩
  rw [max_eq_left hm, zero_div]

theorem typeI_weight_nonnegative (Z : ℝ) (hZ : 0 < Z) (n : ℕ) (hn : 0 < n) :
    0 ≤ typeITentWeight Z n := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [typeITentWeight, half_step_tent_eq Z n hZ.le hn']
  exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (div_nonneg (le_max_left _ _) hn'.le)) hZ.le

theorem typeI_weight_le_prime_charge (Z : ℝ) (hZ : 0 < Z) (p : ℕ) (hp : p.Prime) :
    typeITentWeight Z p ≤ Real.log p / (2*p) := by
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hΛ := ArithmeticFunction.vonMangoldt_apply_prime hp
  unfold typeITentWeight abelian₂
  rw [hΛ, mul_div_assoc]
  exact (mul_le_mul_of_nonneg_left (half_step_tent_le_half_inv Z p hZ hp')
    (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))).trans_eq (by ring)

open Classical in
theorem typeI_remove_nonprime_weight (Z : ℝ) (hZ : 0 < Z)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊2*Z⌋₊, (typeITentWeight Z n:ℂ)*χ (n : ZMod q)) -
       ∑ p ∈ typeIWindowPrimes Z, (typeITentWeight Z p:ℂ)*χ (p : ZMod q)‖ ≤
      (Chebyshev.psi (2*Z) - Chebyshev.theta (2*Z))/(2*Z) := by
  let A := Finset.Icc 1 ⌊2*Z⌋₊
  let f (n : ℕ) := (typeITentWeight Z n:ℂ)*χ (n : ZMod q)
  have hPrime : ∑ p ∈ typeIWindowPrimes Z, f p = ∑ p ∈ A.filter Nat.Prime, f p := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, ((Finset.mem_filter.mp hn).2).1⟩
    · intro n hn hn'
      obtain ⟨hIn,hp⟩ := Finset.mem_filter.mp hn
      have hn₀ : 0 < n := hp.pos
      have hn'₀ : 0 < (n:ℝ) := by exact_mod_cast hn₀
      have hOut : ¬ (Z < (n:ℝ) ∧ (n:ℝ) < 2*Z) := fun h =>
        hn' ((mem_typeIWindowPrimes hZ.le).mpr ⟨hp,h⟩)
      simp [f,typeITentWeight,half_step_tent_zero_outside Z n hZ.le hn'₀ hOut]
  have heq : (∑ n ∈ A, f n) - (∑ p ∈ A.filter Nat.Prime, f p) =
      ∑ n ∈ A.filter (fun n => ¬n.Prime), f n := by
    rw [← Finset.sum_filter_add_sum_filter_not A Nat.Prime f]
    abel
  change ‖(∑ n ∈ A, f n) - ∑ p ∈ typeIWindowPrimes Z, f p‖ ≤ _
  rw [hPrime, heq, Chebyshev.psi_sub_theta_eq_sum_not_prime]
  have hA : Finset.Ioc 0 ⌊2*Z⌋₊ = A := by
    ext n
    simp [A, Finset.mem_Ioc, Finset.mem_Icc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  rw [hA, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn₁ : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hn₀ : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn₁
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast hn₀
  have hwt : typeITentWeight Z n ≤ abelian₂ n/(2*Z) := by
    by_cases hwindow : Z < (n:ℝ) ∧ (n:ℝ) < 2*Z
    · have hlow : 0 < 2*Z := by positivity
      have hInv : 1 / (2*(n:ℝ)) ≤ 1/(2*Z) :=
        one_div_le_one_div_of_le hlow (by linarith [hwindow.1])
      unfold typeITentWeight
      rw [mul_div_assoc, div_eq_mul_one_div (abelian₂ n)]
      exact mul_le_mul_of_nonneg_left ((half_step_tent_le_half_inv Z n hZ hnpos).trans hInv)
        ArithmeticFunction.vonMangoldt_nonneg
    · rw [typeITentWeight, half_step_tent_zero_outside Z n hZ.le hnpos hwindow]
      simp only [mul_zero, zero_div]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hnw := typeI_weight_nonnegative Z hZ n hn₀
  calc
    ‖f n‖ = typeITentWeight Z n * ‖χ (n : ZMod q)‖ := by
      simp only [f, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnw]
    _ ≤ typeITentWeight Z n := mul_le_of_le_one_right hnw (DirichletCharacter.norm_le_one χ _)
    _ ≤ _ := hwt

theorem family_typeI_nonprime_tail {eps : ℝ} (F : FamP eps) (heps : 0 < eps) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let Z := (F.L x i).sc.X' ^ (3/4:ℝ)
      (Chebyshev.psi (2*Z)-Chebyshev.theta (2*Z))/(2*Z) ≤ K*x^(-13:ℝ) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨K,hK,?_⟩
  have hE := exp_neg_rpow_eventually_le_rpow (3/8) (eps/3) 13 (by norm_num) (by positivity)
  filter_upwards [hE] with x hE
  intro hxi i Z
  have hZ : Z = Real.exp ((3/4)*x^(eps/3)) := by
    change (F.L x i).sc.X' ^ (3/4:ℝ) = _
    rw [Scale.X', F.L_x x i hxi, F.L_eps x i, mul_comm, Real.exp_mul]
  have hZ₀ : 0 < Z := by rw [hZ]; positivity
  have h₂ : 0 < 2*Z := by positivity
  have hS : Real.sqrt (2*Z) ≤ 2*Z*Real.exp (-(3/8)*x^(eps/3)) := by
    have hA := Real.sqrt_le_sqrt (show Z ≤ 2*Z by linarith)
    have hB : Real.sqrt Z * Real.exp (-(3/8)*x^(eps/3)) = 1 := by
      have hh : Real.sqrt Z = Real.exp ((3/8)*x^(eps/3)) := by
        rw [Real.sqrt_eq_rpow, hZ, ← Real.exp_mul]
        congr 1
        ring
      rw [hh, ← Real.exp_add]
      convert Real.exp_zero using 2 <;> ring
    calc
      _ = (Real.sqrt (2*Z))^2 / Real.sqrt (2*Z) := by
        field_simp [Real.sqrt_pos.2 h₂ |>.ne']
      _ = 2*Z / Real.sqrt (2*Z) := by rw [Real.sq_sqrt h₂.le]
      _ ≤ 2*Z / Real.sqrt Z := div_le_div_of_nonneg_left h₂.le (Real.sqrt_pos.2 hZ₀) hA
      _ = _ := by rw [div_eq_iff (Real.sqrt_pos.2 hZ₀).ne']; rw [mul_assoc, mul_comm _ (Real.sqrt Z), hB, mul_one]
  apply (div_le_iff₀ h₂).mpr
  calc
    _ ≤ C*Real.sqrt (2*Z) := hC _
    _ ≤ K*Real.sqrt (2*Z) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    _ ≤ K*(2*Z*Real.exp (-(3/8)*x^(eps/3))) := mul_le_mul_of_nonneg_left hS hK
    _ ≤ K*(2*Z*x^(-13:ℝ)) := by gcongr
    _ = _ := by ring

theorem family_typeI_window_unramified {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x) (p : ℕ),
      p ∈ typeIWindowPrimes ((F.L x i).sc.X' ^ (3/4:ℝ)) →
        ZetaZeroFreeRegion.Unram (F.D x i) p := by
  have hC := family_host_log_conductor_bound F heps heps'
  have hS := AuxBlock8.Pf.ev_pow 8 (eps/4) (eps/3) (by linarith)
  filter_upwards [hC,hS,eventually_ge_atTop (1:ℝ)] with x hC hS hx₁
  intro hx i p hp
  let Z := (F.L x i).sc.X' ^ (3/4:ℝ)
  let M := (F.D x i).host.condN
  have hZ : Z = Real.exp ((3/4)*x^(eps/3)) := by
    change (F.L x i).sc.X' ^ (3/4:ℝ) = _
    rw [Scale.X', F.L_x x i hx, F.L_eps x i, mul_comm, Real.exp_mul]
  have hZ₀ : 0 < Z := by rw [hZ]; positivity
  have hM₀ : 0 < (M:ℝ) := by exact_mod_cast (F.D x i).host.condN_pos
  have hM : (M:ℝ) < Z := by
    rw [hZ, ← Real.log_lt_log_iff hM₀ (Real.exp_pos _), Real.log_exp]
    have hh := hC hx i
    change Real.log (M:ℝ) ≤ _ at hh
    have hpos : 0 < x^(eps/4) := Real.rpow_pos_of_pos (zero_lt_one.trans_le hx₁) _
    linarith only [hh,hpos,hS]
  obtain ⟨hPrime,hlo,_⟩ := (mem_typeIWindowPrimes hZ₀.le).mp hp
  apply (LnkBr.unram_iff _ p).mpr
  refine ⟨hPrime,fun h => ?_⟩
  have hh : (p:ℝ) ≤ (M:ℝ) := by exact_mod_cast Nat.le_of_dvd (F.D x i).host.condN_pos h
  exact (hM.trans hlo).not_ge hh

open Classical in
/-- The Fourier inversion identity with the constant character isolated. -/
theorem weighted_host_class_lower {ι H : Type*} [AddCommGroup H] [Fintype H]
    (S : Finset ι) (cls : ι → H) (w : ι → ℝ) (g : H) (E : ℝ) (hE : 0 ≤ E)
    (h : ∀ φ : AddChar H ℂ, φ ≠ 0 →
      ‖∑ a ∈ S, (w a:ℂ) * φ (cls a)‖ ≤ E) :
    (∑ a ∈ S, w a) - (Fintype.card H:ℝ)*E ≤
      (Fintype.card H:ℝ) * ∑ a ∈ S.filter (fun a => cls a = g), w a := by
  classical
  let f (φ : AddChar H ℂ) := φ (-g) * ∑ a ∈ S, (w a:ℂ) * φ (cls a)
  let D : Finset (AddChar H ℂ) := Finset.univ.erase 0
  have hf := weighted_host_class_fourier S cls (fun a => (w a:ℂ)) g
  change _ = ∑ φ, f φ at hf
  have hf₀ : f 0 = (↑(∑ a ∈ S, w a):ℂ) := by simp [f]
  have hSplit : (∑ φ, f φ) = (∑ φ ∈ D, f φ) + f 0 :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ (0:AddChar H ℂ))).symm
  rw [hSplit,hf₀] at hf
  have hreal := congrArg Complex.re hf
  simp only [← Complex.ofReal_sum] at hreal
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_im, zero_mul, sub_zero] at hreal
  have hN : ‖∑ φ ∈ D, f φ‖ ≤ (Fintype.card H:ℝ)*E := by
    calc
      _ ≤ ∑ φ ∈ D, ‖f φ‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ D, E := Finset.sum_le_sum fun φ hφ => by
        have hne : φ ≠ 0 := (Finset.mem_erase.mp hφ).1
        unfold f
        rw [norm_mul, φ.norm_apply, one_mul]
        exact h φ hne
      _ = (D.card:ℝ)*E := by simp
      _ ≤ (Fintype.card H:ℝ)*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact_mod_cast (Finset.card_le_univ D).trans_eq AddChar.card_eq
  have hRe := Complex.abs_re_le_norm (∑ φ ∈ D, f φ)
  linarith only [hreal,hN,hRe,neg_abs_le (∑ φ ∈ D, f φ).re]

theorem family_typeI_window_scales {eps : ℝ} (F : FamP eps) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let X := (F.L x i).sc.X'
      let Z := X ^ (3/4:ℝ)
      2 ≤ Z ∧ 2*Z < X ∧ Real.log Z = (3/4)*x^(eps/3) := by
  have hE := (tendsto_rpow_atTop (show 0 < eps/3 by positivity)).eventually_ge_atTop 16
  filter_upwards [hE] with x hE
  intro hx i X Z
  have hX : X = Real.exp (x^(eps/3)) := by
    change (F.L x i).sc.X' = _
    rw [Scale.X', F.L_x x i hx, F.L_eps x i]
  have hZ : Z = Real.exp ((3/4)*x^(eps/3)) := by
    change X ^ (3/4:ℝ) = _
    rw [hX, mul_comm, Real.exp_mul]
  have h₁ := Real.add_one_le_exp ((3/4)*x^(eps/3))
  have h₂ := Real.add_one_le_exp ((1/4)*x^(eps/3))
  have h₂' : 2 < Real.exp ((1/4)*x^(eps/3)) := by linarith only [h₂,hE]
  have hProd : Z*Real.exp ((1/4)*x^(eps/3)) = X := by
    rw [hZ,hX,← Real.exp_add]
    congr 1
    ring
  refine ⟨?_, ?_, by rw [hZ,Real.log_exp]⟩
  · rw [hZ]
    linarith only [h₁,hE]
  · rw [← hProd, mul_comm 2]
    exact mul_lt_mul_of_pos_left h₂' (by rw [hZ]; positivity)

theorem family_typeI_total_prime_weight {eps : ℝ} (F : FamP eps) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let Z := (F.L x i).sc.X' ^ (3/4:ℝ)
      (3/4)*Real.log (32/27) ≤ ∑ p ∈ typeIWindowPrimes Z, typeITentWeight Z p := by
  obtain ⟨K,hK,hNode⟩ := typeI_principal_node_estimate heps
  obtain ⟨L,_,hTail⟩ := family_typeI_nonprime_tail F heps
  have hC : 0 < Real.log (32/27) := Real.log_pos (by norm_num)
  have hSmall := AuxBlock8.Pf.ev_pow ((6*K+L)/(Real.log (32/27)/4)) (-13) 0 (by norm_num)
  filter_upwards [hNode,hTail,hSmall,family_typeI_window_scales F heps,eventually_ge_atTop (1:ℝ)]
    with x hNode hTail hSmall hScale hx₁
  intro hx i Z
  obtain ⟨hZ,_,hl⟩ := hScale hx i
  have hZ₀ : 0 < Z := by linarith
  have hM₀ : 0 < 3*Z/2 := by positivity
  have hR₀ : 0 < 2*Z := by positivity
  have hL := (div_le_iff₀ hZ₀).mp (hNode Z hZ hl.ge)
  have hM := (div_le_iff₀ hM₀).mp
    (hNode (3*Z/2) (by linarith) (hl.ge.trans (Real.log_le_log hZ₀ (by linarith))))
  have hR := (div_le_iff₀ hR₀).mp
    (hNode (2*Z) (by linarith) (hl.ge.trans (Real.log_le_log hZ₀ (by linarith))))
  have hStencil : -(6*K*x^(-13:ℝ)) ≤
      (Formalism.Gz (2*Z)-2*Formalism.Gz (3*Z/2)+Formalism.Gz Z)/Z := by
    apply (le_div_iff₀ hZ₀).mpr
    nlinarith only [hL,hM,hR,neg_abs_le (Formalism.Gz (2*Z)),
      le_abs_self (Formalism.Gz (3*Z/2)),neg_abs_le (Formalism.Gz Z)]
  let χ : DirichletCharacter ℂ 1 := 1
  have hχ (n : ℕ) : χ (n : ZMod 1) = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
  have hRm := typeI_remove_nonprime_weight Z hZ₀ χ
  simp only [hχ,mul_one,← Complex.ofReal_sum,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hRm
  have hTot := typeI_principal_stencil Z hZ₀
  have hTail' := hTail hx i
  change (Chebyshev.psi (2*Z)-Chebyshev.theta (2*Z))/(2*Z) ≤ _ at hTail'
  change (6*K+L)/(_/4) * x^(-13:ℝ) ≤ x^(0:ℝ) at hSmall
  rw [Real.rpow_zero, div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < Real.log (32/27)/4),
    one_mul] at hSmall
  have hRaw := le_abs_self ((∑ n ∈ Finset.Icc 1 ⌊2*Z⌋₊, typeITentWeight Z n) -
    ∑ p ∈ typeIWindowPrimes Z, typeITentWeight Z p)
  linarith only [hStencil,hRm,hTot,hTail',hSmall,hRaw]

theorem family_typeI_nonprincipal_prime_weight {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) (c₆ : ℝ) (hc₆ : 0 < c₆) (hThin : ChosenThin F c₆) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let Z := (F.L x i).sc.X' ^ (3/4:ℝ)
      ∀ φ : AddChar (LnkBr.MM D) ℂ, φ ≠ 0 →
        ‖∑ p ∈ typeIWindowPrimes Z, (typeITentWeight Z p:ℂ) * φ (LnkBr.tE D (frob D p))‖ ≤ K*x^(-9:ℝ) := by
  obtain ⟨A,hA,hNode⟩ := family_typeI_nonprincipal_estimate F heps heps' c₆ hc₆ hThin
  obtain ⟨B,hB,hTail⟩ := family_typeI_nonprime_tail F heps
  refine ⟨6*A+B,by positivity,?_⟩
  filter_upwards [hNode,hTail,family_typeI_window_scales F heps,
    family_typeI_window_unramified F heps heps',eventually_ge_atTop (1:ℝ)]
    with x hNode hTail hScale hUnram hx₁
  intro hx i D Z φ hφ
  let X := (F.L x i).sc.X'
  let χ := ZetaZeroFreeRegion.prim D (LnkBr.cOf D φ)
  have hq : 0 < (χ.1:ℕ) := χ.1.property
  letI : NeZero (χ.1:ℕ) := ⟨hq.ne'⟩
  obtain ⟨hED,hχ,_⟩ := host_primitive_nonprincipal D φ hφ
  obtain ⟨hZ,hZX,_⟩ := hScale hx i
  have hZ₀ : 0 < Z := by linarith
  have hZX' : 2*Z < X := hZX
  have hNode' := hNode hx i χ.1 χ.2 hED hχ
  have hh₁ : ‖gChi χ.2 Z‖/Z ≤ A*x^(-9:ℝ) := hNode' Z le_rfl (by linarith)
  have hh₂ : ‖gChi χ.2 (3*Z/2)‖/(3*Z/2) ≤ A*x^(-9:ℝ) :=
    hNode' (3*Z/2) (by linarith) (by linarith)
  have hh₃ : ‖gChi χ.2 (2*Z)‖/(2*Z) ≤ A*x^(-9:ℝ) :=
    hNode' (2*Z) (by linarith) (by linarith)
  have hRaw := typeI_nonprincipal_stencil Z (A*x^(-9:ℝ)) hZ₀ χ.2 hχ hh₁ hh₂ hh₃
  have hRm := typeI_remove_nonprime_weight Z hZ₀ χ.2
  have hTail' := hTail hx i
  change (Chebyshev.psi (2*Z)-Chebyshev.theta (2*Z))/(2*Z) ≤ _ at hTail'
  have hR := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num : (-13:ℝ) ≤ -9)) hB
  have hEq : ∑ p ∈ typeIWindowPrimes Z, (typeITentWeight Z p:ℂ) * φ (LnkBr.tE D (frob D p)) =
      ∑ p ∈ typeIWindowPrimes Z, (typeITentWeight Z p:ℂ) * χ.2 (p : ZMod χ.1) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [host_primitive_unramified D φ p (hUnram hx i p hp)]
  rw [hEq]
  let M := ∑ n ∈ Finset.Icc 1 ⌊2*Z⌋₊, (typeITentWeight Z n:ℂ) * χ.2 (n : ZMod χ.1)
  let N := ∑ p ∈ typeIWindowPrimes Z, (typeITentWeight Z p:ℂ) * χ.2 (p : ZMod χ.1)
  change ‖M‖ ≤ _ at hRaw
  change ‖M-N‖ ≤ _ at hRm
  change ‖N‖ ≤ _
  have hN := norm_sub_le M (M-N)
  rw [sub_sub_cancel] at hN
  linarith only [hN,hRaw,hRm,hTail',hR]

open Classical in
theorem family_typeI_host_class_weight {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) (c₆ : ℝ) (hc₆ : 0 < c₆) (hThin : ChosenThin F c₆) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let Z := (F.L x i).sc.X' ^ (3/4:ℝ)
      ∀ g : LnkBr.MM D, Real.log (32/27)/(8*(D.R.n:ℝ)) ≤
        ∑ p ∈ (typeIWindowPrimes Z).filter (fun p => LnkBr.tE D (frob D p) = g), typeITentWeight Z p := by
  obtain ⟨K,hK,hNon⟩ := family_typeI_nonprincipal_prime_weight F heps heps' c₆ hc₆ hThin
  have hc : 0 < Real.log (32/27) := half_step_log_main_pos
  have hSmall := AuxBlock8.Pf.ev_pow (16*K/Real.log (32/27)) (-6) 0 (by norm_num)
  filter_upwards [hNon,family_typeI_total_prime_weight F heps,hSmall,eventually_ge_atTop (1:ℝ)]
    with x hNon hTot hSmall hx₁
  intro hx i D Z g
  have hx₀ : 0 < x := zero_lt_one.trans_le hx₁
  have hn₀ : 0 < (D.R.n:ℝ) := by exact_mod_cast D.R.ord_pos
  have hn : (D.R.n:ℝ) ≤ x^(3:ℝ) := by
    have hn' := (F.sizes x hx i).1.2
    change (D.R.n:ℝ) ≤ (F.L x i).sc.x^(2+8*(F.L x i).sc.eps+(F.L x i).sc.eps/100) at hn'
    rw [F.L_x x i hx, F.L_eps x i] at hn'
    exact hn'.trans (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith only [heps']))
  have hcard : Fintype.card (LnkBr.MM D) = 4*D.R.n := by
    change Fintype.card (Formalism.D5.E0 × D.R.A) = _
    rw [Fintype.card_prod, D.R.card_A]
    change (Fintype.card (ZMod 2 × ZMod 2))*D.R.n = _
    norm_num [Fintype.card_prod,ZMod.card]
  have hFourier := weighted_host_class_lower (typeIWindowPrimes Z)
    (fun p => LnkBr.tE D (frob D p)) (typeITentWeight Z) g (K*x^(-9:ℝ))
    (by positivity) (hNon hx i)
  rw [hcard, Nat.cast_mul, Nat.cast_ofNat] at hFourier
  have hError : 4*(D.R.n:ℝ)*(K*x^(-9:ℝ)) ≤ Real.log (32/27)/4 := by
    rw [Real.rpow_zero, div_mul_eq_mul_div, div_le_iff₀ hc, one_mul] at hSmall
    calc
      _ ≤ 4*x^(3:ℝ)*(K*x^(-9:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
      _ = 4*K*x^(-6:ℝ) := by
        calc
          _ = 4*K*(x^(3:ℝ)*x^(-9:ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hx₀]; norm_num
      _ ≤ _ := by linarith only [hSmall]
  have hSum := hTot hx i
  change (3/4)*Real.log (32/27) ≤ ∑ p ∈ typeIWindowPrimes Z, typeITentWeight Z p at hSum
  have hB : Real.log (32/27)/2 ≤
      (4*(D.R.n:ℝ))*∑ p ∈ (typeIWindowPrimes Z).filter (fun p => LnkBr.tE D (frob D p) = g), typeITentWeight Z p := by
    have hMid : Real.log (32/27)/2 ≤ (∑ p ∈ typeIWindowPrimes Z, typeITentWeight Z p) -
        4*(D.R.n:ℝ)*(K*x^(-9:ℝ)) := by linarith only [hError,hSum]
    refine hMid.trans (hFourier.trans_eq ?_)
    apply congrArg (fun a : ℝ => 4*(D.R.n:ℝ)*a)
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter]
  apply (div_le_iff₀ (by positivity : 0 < 8*(D.R.n:ℝ))).mpr
  calc
    _ = 2*(Real.log (32/27)/2) := by ring
    _ ≤ _ := by convert mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring

open Classical in
def adjacentTopCount {A : Type*} [AddCommGroup A] (S : Finset A) (h : A) : ℕ :=
  (S.filter (fun t => t+h ∈ S)).card

theorem adjacentTopCount_le {A : Type*} [AddCommGroup A] (S : Finset A) (h : A) :
    adjacentTopCount S h ≤ S.card := by
  classical
  exact Finset.card_filter_le _ _

theorem sum_adjacentTopCount {A : Type*} [AddCommGroup A] [Fintype A] (S : Finset A) :
    ∑ h : A, adjacentTopCount S h = S.card^2 := by
  classical
  have hCount (t : A) : ∑ h : A, (if t+h ∈ S then (1:ℕ) else 0) = S.card := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    apply Finset.card_bij (fun h _ => t+h)
    · intro h hh
      exact (Finset.mem_filter.mp hh).2
    · intro h _ j _ e
      exact add_left_cancel e
    · intro a ha
      refine ⟨a-t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [sub_eq_add_neg, add_left_comm] using ha
      · simp [sub_eq_add_neg, add_left_comm]
  simp only [adjacentTopCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [hCount, Finset.sum_const, smul_eq_mul, pow_two, Nat.mul_one]

open Classical in
theorem native_short_order_count (D : D7) (B : ℕ) :
    ((Finset.univ : Finset (G.HH D)).filter (fun h => addOrderOf h ≤ B)).card ≤ D.R.o * B^2 := by
  let H := Subgroup.zpowers (Multiplicative.ofAdd D.R.a0)
  have hH : H = D.R.A0.toSubgroup := rfl
  have hIndex : H.index = D.R.o := by rw [hH, AddSubgroup.index_toSubgroup, D.R.index_A0_eq_o]
  let S (r : ℕ) : Finset (G.HH D) := Finset.univ.filter (fun h => r • h = 0)
  have hS (r : ℕ) (hr : 0 < r) : (S r).card ≤ D.R.o * r := by
    have ht := GlobalTheory.card_pow_eq_one_le_index_mul H hr
    rw [hIndex] at ht
    have hcard : (S r).card = Nat.card {h : Multiplicative (G.HH D) // h ^ r = 1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply congrArg Finset.card
      ext h
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      change r • h = 0 ↔ Multiplicative.ofAdd h ∈
        ((Finset.univ : Finset (Multiplicative (G.HH D))).filter (fun z => z^r=1))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    exact hcard.trans_le ht
  let I := Finset.Icc 1 B
  have hsub : ((Finset.univ : Finset (G.HH D)).filter (fun h => addOrderOf h ≤ B)) ⊆ I.biUnion S := by
    intro h hh
    refine Finset.mem_biUnion.mpr ⟨addOrderOf h, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · exact Finset.mem_Icc.mpr ⟨addOrderOf_pos h, (Finset.mem_filter.mp hh).2⟩
    · exact addOrderOf_nsmul_eq_zero h
  calc
    _ ≤ (I.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ I, (S r).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ I, D.R.o * B := by
      refine Finset.sum_le_sum fun r hr => ?_
      obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hr
      exact (hS r h₁).trans (Nat.mul_le_mul_left _ h₂)
    _ = D.R.o*B^2 := by simp [I,Nat.card_Icc,pow_two] <;> ring

theorem native_inert_artin_class (D : D7) (p : ℕ) (h : ZetaZeroFreeRegion.Unram D p)
    (g : G.HH D) (hClass : LnkBr.tE D (frob D p) = ((1,1),g)) :
    IsResidueClassZero D p ∧ hP D p = g := by
  let a : D.R.GG := (Formalism.FrobeniusOrbits.c0,D.R.iota g)
  have hcode : LnkBr.tE D a = ((1,1),g) := by
    change ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (-1)),
      Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (-1))), D.R.iotaInv (D.R.iota g)) = _
    rw [Formalism.HC.Frame.iotaInv_iota]
    congr 2 <;> decide
  have hf : frob D p = a := (LnkBr.tE D).injective (hClass.trans hcode.symm)
  obtain ⟨hp,hdiv⟩ := (LnkBr.unram_iff D p).mp h
  obtain ⟨P,hP,hOver,σ,hσ,hF⟩ := Lnk.frob_mem D p hp
  letI : Fact p.Prime := ⟨hp⟩
  have hh : (D.host.galE σ).1 = Formalism.FrobeniusOrbits.c0 := by
    rw [hF,hf]
  have hSigns := ((D.host.hostClasses p hdiv P σ hσ).2.2).mp hh
  refine ⟨(primeClass_eq_inert_iff_symbols hp).mpr ⟨hdiv,hSigns⟩,?_⟩
  rw [Lnk.hP_eq D h,hf]
  exact Formalism.HC.Frame.iotaInv_iota _ _

open Classical in
theorem family_typeI_short_orders {eps : ℝ} (F : FamP eps) (heps : 0 < eps)
    (heps' : eps < 1/52) (hTT : ChosenTT F) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let N := ((Finset.univ : Finset (G.HH D)).filter
        (fun h => (addOrderOf h:ℝ) < x^(eps/4))).card
      0 < D.host.TT.card ∧ 2*(N:ℝ) ≤ D.host.TT.card ∧
        x^(-eps/8)*(D.R.n:ℝ)/2 ≤ D.host.TT.card := by
  obtain ⟨x₀,hTT⟩ := hTT
  let C := max F.Co 0
  have hC : 0 ≤ C := le_max_right _ _
  have hSmall := AuxBlock8.Pf.ev_pow (16*C) (eps/2) 1 (by linarith)
  filter_upwards [hSmall,eventually_ge_atTop (1:ℝ),eventually_ge_atTop x₀]
    with x hSmall hx₁ hx₀
  intro hx i D N
  let L := F.L x i
  let u := x^(eps/4)
  let B := ⌈u⌉₊
  have hu : 1 ≤ u := Real.one_le_rpow hx₁ (by positivity)
  have hux : 0 < x := zero_lt_one.trans_le hx₁
  have hB : (B:ℝ) ≤ 2*u := by
    have h := Nat.ceil_lt_add_one (zero_le_one.trans hu)
    linarith
  have hSub : N ≤ ((Finset.univ : Finset (G.HH D)).filter (fun h => addOrderOf h ≤ B)).card := by
    apply Finset.card_le_card
    intro t ht
    obtain ⟨_, h⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact_mod_cast (h.le.trans (Nat.le_ceil u))
  have hN' : (N:ℝ) ≤ (D.R.o:ℝ)*(B:ℝ)^2 := by
    exact_mod_cast hSub.trans (native_short_order_count D B)
  have hN : (N:ℝ) ≤ 4*C*x^(eps/2) := by
    calc
      _ ≤ C*(2*u)^2 := hN'.trans (mul_le_mul
        ((F.o_le_Co x i hx).trans (le_max_left _ _))
        (pow_le_pow_left₀ (by positivity) hB 2) (by positivity) hC)
      _ = _ := by
        have hh : u^2 = x^(eps/2) := by
          unfold u
          rw [← Real.rpow_natCast, ← Real.rpow_mul hux.le]
          congr 1
          push_cast
          ring
        rw [mul_pow,hh]
        ring
  have hTT' := (hTT x hx₀ i).1
  change L.sc.delta1*(D.R.n:ℝ)/2 ≤ D.host.TT.card at hTT'
  rw [Scale.delta1, F.L_x x i hx, F.L_eps x i, ← neg_div] at hTT'
  have hn : x^(2:ℝ) ≤ (D.R.n:ℝ) := by
    have hn' := (F.sizes x hx i).1.1
    change L.sc.x^(2+8*L.sc.eps-L.sc.eps/100) ≤ (D.R.n:ℝ) at hn'
    rw [F.L_x x i hx,F.L_eps x i] at hn'
    exact (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)).trans hn'
  have hM : x/2 ≤ (D.host.TT.card:ℝ) := by
    calc
      _ = x^(1:ℝ)/2 := by rw [Real.rpow_one]
      _ ≤ x^(2-eps/8)/2 := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith only [heps'])) (by norm_num)
      _ = x^(-eps/8)*x^(2:ℝ)/2 := by
        rw [← Real.rpow_add hux]
        congr 2
        ring
      _ ≤ _ := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) (by norm_num)).trans hTT'
  rw [Real.rpow_one] at hSmall
  have hN₂ : 2*(N:ℝ) ≤ D.host.TT.card := by linarith only [hSmall,hN,hM]
  refine ⟨?_,hN₂,hTT'⟩
  exact_mod_cast (show 0 < (D.host.TT.card:ℝ) by linarith only [hM,hx₁])

open Classical in
theorem sum_long_adjacentTopCount {A : Type*} [AddCommGroup A] [Fintype A]
    (S : Finset A) (b : ℝ)
    (hSmall : 2*(((Finset.univ : Finset A).filter (fun h => (addOrderOf h:ℝ) < b)).card:ℝ) ≤ S.card) :
    (S.card:ℝ)^2/2 ≤
      ∑ h ∈ (Finset.univ : Finset A).filter (fun h => b ≤ (addOrderOf h:ℝ)), (adjacentTopCount S h:ℝ) := by
  let f (h : A) := (adjacentTopCount S h:ℝ)
  let J := (Finset.univ : Finset A).filter (fun h => (addOrderOf h:ℝ)<b)
  have hJ : ∑ h ∈ J, f h ≤ (J.card:ℝ)*S.card := by
    calc
      _ ≤ ∑ _ ∈ J, (S.card:ℝ) := Finset.sum_le_sum fun h _ => by
        change (adjacentTopCount S h:ℝ) ≤ (S.card:ℝ)
        exact_mod_cast adjacentTopCount_le S h
      _ = _ := by simp [nsmul_eq_mul]
  have hTot : (∑ h : A, f h) = (S.card:ℝ)^2 := by
    dsimp [f]
    exact_mod_cast sum_adjacentTopCount S
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun h => (addOrderOf h:ℝ)<b) f] at hTot
  simp only [not_lt] at hTot
  have hSplit : (∑ h ∈ J, f h) + (∑ h ∈ (Finset.univ : Finset A).filter
      (fun h => b ≤ (addOrderOf h:ℝ)), f h) = (S.card:ℝ)^2 := hTot
  have hM := mul_le_mul_of_nonneg_right hSmall (by positivity : (0:ℝ) ≤ S.card)
  nlinarith only [hJ,hSplit,hM]

open Classical in
theorem weighted_long_adjacentTopCount {ι B A : Type*} [AddCommGroup A] [Fintype A]
    (P : Finset ι) (S : Finset A) (cls : ι → B × A) (sign : B) (b C : ℝ) (w : ι → ℝ)
    (hC : 0 ≤ C)
    (hSmall : 2*(((Finset.univ : Finset A).filter (fun h => (addOrderOf h:ℝ) < b)).card:ℝ) ≤ S.card)
    (hWeight : ∀ h : A, C ≤ ∑ p ∈ P.filter (fun p => cls p = (sign,h)), w p) :
    C*((S.card:ℝ)^2/2) ≤
      ∑ p ∈ P.filter (fun p => (cls p).1 = sign ∧ b ≤ (addOrderOf (cls p).2:ℝ)),
        w p * (adjacentTopCount S (cls p).2:ℝ) := by
  let J := (Finset.univ : Finset A).filter (fun h => b ≤ (addOrderOf h:ℝ))
  let L := J.image (fun h => (sign,h))
  let f (p : ι) := w p * (adjacentTopCount S (cls p).2:ℝ)
  let P' := P.filter (fun p => (cls p).1 = sign ∧ b ≤ (addOrderOf (cls p).2:ℝ))
  have hP' : P' = P.filter (fun p => cls p ∈ L) := by
    ext p
    simp only [P',L,J,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Prod.ext_iff]
    constructor
    · rintro ⟨hp,hsign,hb⟩
      exact ⟨hp,(cls p).2,hb,hsign.symm,rfl⟩
    · rintro ⟨hp,h,hb,hsign,he⟩
      exact ⟨hp,hsign.symm,he ▸ hb⟩
  calc
    _ ≤ C*∑ h ∈ J, (adjacentTopCount S h:ℝ) :=
      mul_le_mul_of_nonneg_left (sum_long_adjacentTopCount S b hSmall) hC
    _ = ∑ h ∈ J, C*(adjacentTopCount S h:ℝ) := Finset.mul_sum _ _ _
    _ ≤ ∑ h ∈ J, ∑ p ∈ P.filter (fun p => cls p = (sign,h)), f p := by
      refine Finset.sum_le_sum (fun h _ => ?_)
      calc
        _ ≤ (∑ p ∈ P.filter (fun p => cls p = (sign,h)), w p) * (adjacentTopCount S h:ℝ) :=
          mul_le_mul_of_nonneg_right (hWeight h) (by positivity)
        _ = _ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hr : (cls p).2 = h := congrArg Prod.snd (Finset.mem_filter.mp hp).2
          simp [f,hr]
    _ = ∑ g ∈ L, ∑ p ∈ P.filter (fun p => cls p = g), f p := by
      symm
      exact Finset.sum_image (fun i _ j _ e => congrArg Prod.snd e)
    _ = ∑ p ∈ P', f p := by
      rw [hP']
      exact Finset.sum_fiberwise_eq_sum_filter P L cls f

open Classical in
theorem typeI_level_factor_weight (Z : ℝ) (hZ : 0 < Z) (P : Finset ℕ)
    (hP : P ⊆ typeIWindowPrimes Z) (Q : ℕ) (hQ : 1 < Q) :
    (∑ p ∈ P.filter (fun p => p ∣ Q-1), typeITentWeight Z p) ≤
      Real.log (Q:ℝ)/(2*Z) := by
  have hQ' : 0 < Q-1 := by omega
  have hSub : P.filter (fun p => p ∣ Q-1) ⊆ (Q-1).primeFactors := by
    intro p hp
    obtain ⟨hp', hd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨((mem_typeIWindowPrimes hZ.le).mp (hP hp')).1,hd,hQ'.ne'⟩
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => p ∣ Q-1), Real.log (p:ℝ)/(2*Z) := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      obtain ⟨hp',hpLo,_⟩ := (mem_typeIWindowPrimes hZ.le).mp (hP (Finset.mem_filter.mp hp).1)
      exact (typeI_weight_le_prime_charge Z hZ p hp').trans
        (div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity) (by linarith))
    _ ≤ ∑ p ∈ (Q-1).primeFactors, Real.log (p:ℝ)/(2*Z) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub
        (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (by positivity))
    _ ≤ _ := by
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (J.sum_log_primeFactors_le (Q-1) hQ').trans
        (Real.log_le_log (by exact_mod_cast hQ') (by exact_mod_cast Nat.sub_le Q 1))

theorem family_typeI_level_scale {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) (hTu : TuSize F) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let Z := (F.L x i).sc.X' ^ (3/4:ℝ)
      ∀ u : D.what₂.Word,
        let Q := (D.mem u).A.T
        2*Z < (Q:ℝ) ∧ Real.log (Q:ℝ)/(2*Z) ≤ (max F.CTu 0)*x^(-5:ℝ) := by
  obtain ⟨x₀,hTu⟩ := hTu
  have hE := exp_neg_rpow_eventually_le_rpow (3/4) (eps/3) 12 (by norm_num) (by positivity)
  filter_upwards [family_typeI_window_scales F heps,hE,eventually_ge_atTop x₀,eventually_ge_atTop (1:ℝ)]
    with x hSc hE hx₀ hx₁
  intro hx i D Z u Q
  let L := F.L x i
  have hxPos : 0 < x := zero_lt_one.trans_le hx₁
  have hmx : (D.R.m:ℝ) ≤ x^(6:ℝ) := by
    have hm : (D.R.m:ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.m ≤ D.R.k by have := D.R.m_add_three_le_k; omega)
    have hk := AuxBlock8.Pf.k_le_x_pow_six L (F.sizes x hx i)
    rw [F.L_x x i hx] at hk
    exact hm.trans hk
  have hL : L.sc.L = x^eps := by rw [Scale.L,F.L_x x i hx,F.L_eps x i]
  have hX : L.sc.X' = Real.exp (x^(eps/3)) := by rw [Scale.X',F.L_x x i hx,F.L_eps x i]
  have hZ : Z = Real.exp ((3/4)*x^(eps/3)) := by
    change L.sc.X' ^ (3/4:ℝ) = _
    rw [hX,mul_comm,Real.exp_mul]
  obtain ⟨Ge,hLog⟩ := hTu x hx₀ i
  have hGe : L.sc.b ^ ((D.R.m:ℝ)/2) ≤ (Q:ℝ) := Ge u
  have h₁ : 1 ≤ (D.R.m:ℝ)/2 := by
    have h : (2:ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    linarith
  have hB : L.sc.X' ≤ L.sc.b ^ ((D.R.m:ℝ)/2) := by
    rw [hX,Scale.b,← Real.exp_mul,hL]
    apply Real.exp_le_exp.mpr
    exact (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)).trans
      (le_mul_of_one_le_right (by positivity) h₁)
  have h₀ : 0 < Z := by rw [hZ]; positivity
  refine ⟨(hSc hx i).2.1.trans_le (hB.trans hGe),?_⟩
  have hQ : Real.log (Q:ℝ) ≤ (max F.CTu 0)*x^(7:ℝ) := by
    have hPower : L.sc.L ≤ x^(1:ℝ) := by rw [hL]; exact Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)
    calc
      _ ≤ F.CTu*(D.R.m:ℝ)*L.sc.L := hLog u
      _ ≤ (max F.CTu 0)*x^(6:ℝ)*x^(1:ℝ) := by
        have hL₀ : 0 ≤ L.sc.L := by rw [hL]; positivity
        exact mul_le_mul (mul_le_mul (le_max_left _ _) hmx (Nat.cast_nonneg _) (le_max_right _ _))
          hPower hL₀ (mul_nonneg (le_max_right _ _) (by positivity))
      _ = _ := by rw [mul_assoc,← Real.rpow_add hxPos]; norm_num
  have hInv : 1/(2*Z) ≤ x^(-12:ℝ) := by
    calc
      _ ≤ 1/Z := one_div_le_one_div_of_le h₀ (by linarith)
      _ = Real.exp (-(3/4)*x^(eps/3)) := by rw [one_div,hZ,← Real.exp_neg,neg_mul]
      _ ≤ _ := hE
  rw [div_eq_mul_one_div]
  calc
    _ ≤ ((max F.CTu 0)*x^(7:ℝ))*x^(-12:ℝ) :=
      mul_le_mul hQ hInv (by positivity)
        (mul_nonneg (le_max_right _ _) (by positivity))
    _ = _ := by rw [mul_assoc,← Real.rpow_add hxPos]; norm_num

open Classical in
theorem typeI_prime_pair_losses {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts)
    (hK : K.Nonneg) (hKap : KapIDef X K) (Z : ℝ) (hZ : 0 < Z) (P : Finset ℕ)
    (hWindow : P ⊆ typeIWindowPrimes Z) (hCand : ∀ p ∈ P, Cand D L K p)
    (hWall : ChW_at X K) (hBad : ChBadp_at X) (Q : ℕ) (hQ : 1 < Q)
    (hNone : ¬ ∃ p ∈ P, ∃ t ∈ D.host.TT, t+hP D p ∈ D.host.TT ∧
      Sig X K (aL L) (bL L) p ≤ L.sc.x^(-L.sc.eps) ∧ Good X p (X.bs (stepP D p) t) ∧ ¬ p ∣ Q-1) :
    ∑ p ∈ P, typeITentWeight Z p * (adjacentTopCount D.host.TT (hP D p):ℝ) ≤
      (D.host.TT.card:ℝ)*(L.sc.x^(-9:ℝ)+L.sc.x^(-2+L.sc.eps)+Real.log (Q:ℝ)/(2*Z)) := by
  let m := (D.host.TT.card:ℝ)
  let w := typeITentWeight Z
  let share (p : ℕ) := L.sc.x^(-L.sc.eps) < Sig X K (aL L) (bL L) p
  let f (p : ℕ) := if share p then w p else 0
  let g (p : ℕ) := if p ∣ Q-1 then w p else 0
  let b (p : ℕ) := Real.log (p:ℝ) / (p:ℝ) * ((badTops X p).card:ℝ)
  have hm : 0 ≤ m := by unfold m; positivity
  have hf (p : ℕ) (hp : p ∈ P) : 0 ≤ f p := by
    have hprime := ((mem_typeIWindowPrimes hZ.le).mp (hWindow hp)).1
    unfold f
    split <;> first | exact typeI_weight_nonnegative Z hZ p hprime.pos | exact le_rfl
  have hg (p : ℕ) (hp : p ∈ P) : 0 ≤ g p := by
    have hprime := ((mem_typeIWindowPrimes hZ.le).mp (hWindow hp)).1
    unfold g
    split <;> first | exact typeI_weight_nonnegative Z hZ p hprime.pos | exact le_rfl
  have hb (p : ℕ) : 0 ≤ b p := by unfold b; positivity
  have hCsub : P ⊆ cands L K := by
    intro p hp
    have h := hCand p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Nat.lt_ceil).mpr h.2.1),h⟩
  have hBsub : P ⊆ largeOrderResiduePrimes L := by
    intro p hp
    obtain ⟨hp',hPX,hInert,hOrd,_⟩ := hCand p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Nat.lt_ceil).mpr hPX),hp',hInert,hOrd⟩
  have hShare : ∑ p ∈ P, f p ≤ L.sc.x^(-9:ℝ) := by
    let charge (p : ℕ) := Real.log (p:ℝ)/(p:ℝ) *
      ((if share p then 2 else 0)+4*Sig X K (aL L) (bL L) p)
    have hSig (p : ℕ) := Lnk.Sig_nonneg X K hK hKap (aL L) (bL L) p
    have hCharge (p : ℕ) : 0 ≤ charge p := by
      have hh : 0 ≤ (if share p then (2:ℝ) else 0) := by split <;> norm_num
      unfold charge
      exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
        (add_nonneg hh (mul_nonneg (by norm_num) (hSig p)))
    refine (Finset.sum_le_sum (fun p hp => ?_)).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg hCsub (fun _ _ _ => hCharge _)).trans hWall)
    by_cases h : share p
    · have hp' := ((mem_typeIWindowPrimes hZ.le).mp (hWindow hp)).1
      have hl : 0 ≤ Real.log (p:ℝ)/(p:ℝ) := by positivity
      unfold f charge
      rw [if_pos h,if_pos h]
      refine (typeI_weight_le_prime_charge Z hZ p hp').trans ?_
      calc
        _ = (Real.log (p:ℝ)/(p:ℝ))*(1/2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hSig p]) hl
    · unfold f
      rw [if_neg h]
      exact hCharge p
  have hLevel : ∑ p ∈ P, g p ≤ Real.log (Q:ℝ)/(2*Z) := by
    unfold g
    rw [← Finset.sum_filter]
    exact typeI_level_factor_weight Z hZ P hWindow Q hQ
  have hBad' : ∑ p ∈ P, b p ≤ m*L.sc.x^(-2+L.sc.eps) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun _ _ _ => hb _)).trans hBad
  have hPoint (p : ℕ) (hp : p ∈ P) :
      w p * (adjacentTopCount D.host.TT (hP D p):ℝ) ≤ m*f p + b p + m*g p := by
    have hp' := ((mem_typeIWindowPrimes hZ.le).mp (hWindow hp)).1
    have hw : 0 ≤ w p := typeI_weight_nonnegative Z hZ p hp'.pos
    have hC : (adjacentTopCount D.host.TT (hP D p):ℝ) ≤ m := by
      change (adjacentTopCount D.host.TT (hP D p):ℝ) ≤ (D.host.TT.card:ℝ)
      exact_mod_cast adjacentTopCount_le D.host.TT (hP D p)
    have hCW := mul_le_mul_of_nonneg_left hC hw
    by_cases hs : share p
    · have hf' : f p = w p := if_pos hs
      rw [hf']
      nlinarith only [hCW,hb p,mul_nonneg hm (hg p hp)]
    by_cases hd : p ∣ Q-1
    · have hg' : g p = w p := if_pos hd
      rw [hg']
      nlinarith only [hCW,hb p,mul_nonneg hm (hf p hp)]
    have hc : (adjacentTopCount D.host.TT (hP D p):ℝ) ≤ (badTops X p).card := by
      apply Nat.cast_le.mpr
      unfold adjacentTopCount
      apply Finset.card_le_card
      intro t ht
      have ht' : t ∈ D.host.TT ∧ t+hP D p ∈ D.host.TT := by
        simpa only [Finset.mem_filter] using ht
      unfold badTops
      simp only [Finset.mem_filter]
      exact ⟨ht'.1,fun hGood => hNone ⟨p,hp,t,ht'.1,ht'.2,le_of_not_gt hs,hGood,hd⟩⟩
    have hLog : w p ≤ Real.log (p:ℝ)/(p:ℝ) := by
      refine (typeI_weight_le_prime_charge Z hZ p hp').trans ?_
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
        (by exact_mod_cast hp'.pos) (by have hh : (0:ℝ) ≤ p := Nat.cast_nonneg p; linarith)
    have hh : w p * (adjacentTopCount D.host.TT (hP D p):ℝ) ≤ b p :=
      mul_le_mul hLog hc (by positivity) (by positivity)
    linarith only [hh,mul_nonneg hm (hf p hp),mul_nonneg hm (hg p hp)]
  refine (Finset.sum_le_sum hPoint).trans ?_
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hh₁ := mul_le_mul_of_nonneg_left hShare hm
  have hh₂ := mul_le_mul_of_nonneg_left hLevel hm
  linarith only [hh₁,hh₂,hBad']

open Classical in
theorem family_typeI_prime_pair {eps C₀ CH : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) (hChosen : ChosenE F C₀ CH)
    (hWall : ChosenWall F) (hTu : TuSize F) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let L := F.L x i
      let X := F.Gx x i
      let Z := L.sc.X' ^ (3/4:ℝ)
      ∀ u : D.what₂.Word, ∃ p : ℕ, Cand D L F.GK p ∧ L.sc.p0 D.R.k ≤ (p:ℝ) ∧
        Z < (p:ℝ) ∧ (p:ℝ) < 2*Z ∧ p ≠ (D.mem u).A.T ∧ ¬ p ∣ (D.mem u).A.T-1 ∧
        p ∉ L.drop ∧ Even (addOrderOf (hP D p)) ∧
        ∃ t₀ ∈ VV X F.GK (aL L) (bL L) p, ∃ t ∈ topsOn X p t₀,
          t+hP D p ∈ D.host.TT := by
  obtain ⟨C₅,c₆,Cb,_,hc₆,hCb,_,hTT,hBad,_,hThin,_,_⟩ := hChosen
  obtain ⟨xWall,hWall⟩ := hWall
  obtain ⟨xBad,hBad⟩ := Lnk.chosenBadp_of_old F Cb hCb.le hTT hBad
  let c := Real.log (32/27)
  have hc : 0 < c := half_step_log_main_pos
  let C := max F.CTu 0
  have hc128 : 0 < c/128 := by positivity
  have h₁ := AuxBlock8.Pf.ev_pow (1/(c/128)) (-9) (-eps/8) (by linarith only [heps'])
  have h₂ := AuxBlock8.Pf.ev_pow (1/(c/128)) (-2+eps) (-eps/8) (by linarith only [heps'])
  have h₃ := AuxBlock8.Pf.ev_pow (C/(c/128)) (-5) (-eps/8) (by linarith only [heps'])
  filter_upwards [family_typeI_host_class_weight F heps heps' c₆ hc₆ hThin,
    family_typeI_short_orders F heps heps' hTT, family_typeI_window_unramified F heps heps',
    family_typeI_window_scales F heps, typeI_interval_guards F heps, family_typeI_level_scale F heps heps' hTu,
    eventually_ge_atTop xWall,eventually_ge_atTop xBad,eventually_ge_atTop (1:ℝ),h₁,h₂,h₃]
    with x hWeight hSmall hUnram hScale hGuard hLevel hxWall hxBad hx₁ h₁ h₂ h₃
  intro hx i D L X Z u
  let K := F.GK
  let S := D.host.TT
  let m := (S.card:ℝ)
  let n := (D.R.n:ℝ)
  let Q := (D.mem u).A.T
  let cls (p : ℕ) : LnkBr.MM D := LnkBr.tE D (frob D p)
  let sign : Formalism.D5.E0 := (1,1)
  let b := x^(eps/4)
  let P := (typeIWindowPrimes Z).filter (fun p => (cls p).1 = sign ∧ b ≤ (addOrderOf (cls p).2:ℝ))
  have hPsub : P ⊆ typeIWindowPrimes Z := Finset.filter_subset _ _
  have hZ2 : 2 ≤ Z := (hScale hx i).1
  have hZ₀ : 0 < Z := by linarith
  have hn : 0 < n := by
    change 0 < (D.R.n:ℝ)
    exact_mod_cast D.R.ord_pos
  obtain ⟨hm,hSmall',hTop⟩ := hSmall hx i
  have hm' : 0 < m := by
    change 0 < (S.card:ℝ)
    exact_mod_cast hm
  have hCl (p : ℕ) (hp : p ∈ P) :
      IsResidueClassZero D p ∧ hP D p = (cls p).2 ∧ L.sc.x^(L.sc.eps/4) ≤ (addOrderOf (hP D p):ℝ) := by
    obtain ⟨hW,hs,hb⟩ := Finset.mem_filter.mp hp
    have hCls : cls p = ((1,1),(cls p).2) := Prod.ext hs rfl
    obtain ⟨hI,hd⟩ := native_inert_artin_class D p (hUnram hx i p hW) (cls p).2 hCls
    refine ⟨hI,hd,?_⟩
    rw [F.L_x x i hx,F.L_eps x i,hd]
    exact hb
  have hCand (p : ℕ) (hp : p ∈ P) : Cand D L K p := by
    obtain ⟨hp',hl,hr⟩ := (mem_typeIWindowPrimes hZ₀.le).mp (hPsub hp)
    obtain ⟨_,hX,hBand⟩ := hGuard hx i p hl hr
    exact ⟨hp',hX,(hCl p hp).1,(hCl p hp).2.2,fun _ => hBand⟩
  have hC : 0 ≤ c/(8*n) := by positivity
  have hLower' := weighted_long_adjacentTopCount (typeIWindowPrimes Z) S cls sign b
    (c/(8*n)) (typeITentWeight Z) hC hSmall' (fun t => by
      refine (hWeight hx i (sign,t)).trans_eq ?_
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext p
      simp only [Finset.mem_filter, cls, Z, L, D])
  have hLower : c/(8*n)*(m^2/2) ≤ ∑ p ∈ P, typeITentWeight Z p * (adjacentTopCount S (hP D p):ℝ) := by
    refine hLower'.trans_eq ?_
    refine Finset.sum_congr (by ext p; simp only [P,Finset.mem_filter]) ?_
    intro p hp
    have hMem : p ∈ P := Finset.mem_filter.mpr (Finset.mem_filter.mp hp)
    rw [(hCl p hMem).2.1]
  have hNormalized : c/32*x^(-eps/8) ≤ c*m/(16*n) := by
    apply (le_div_iff₀ (by positivity : 0 < 16*n)).mpr
    have hh := mul_le_mul_of_nonneg_left hTop hc.le
    calc
      _ = c*(x^(-eps/8)*n/2) := by ring
      _ ≤ _ := hh
  have hMain : m*(c/32*x^(-eps/8)) ≤ ∑ p ∈ P,
      typeITentWeight Z p * (adjacentTopCount S (hP D p):ℝ) := by
    refine (mul_le_mul_of_nonneg_left hNormalized hm'.le).trans ?_
    have hEq : m*(c*m/(16*n)) = c/(8*n)*(m^2/2) := by ring
    exact hEq.le.trans hLower
  obtain ⟨hq,hLogQ⟩ := hLevel hx i u
  have hQ : 1 < Q := by
    have h : (1:ℝ) < (Q:ℝ) := by linarith
    exact_mod_cast h
  have hBound₁ : x^(-9:ℝ) ≤ c/128*x^(-eps/8) := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hc128,one_mul] at h₁
    simpa only [mul_comm] using h₁
  have hBound₂ : x^(-2+eps) ≤ c/128*x^(-eps/8) := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hc128,one_mul] at h₂
    simpa only [mul_comm] using h₂
  have hBound₃ : C*x^(-5:ℝ) ≤ c/128*x^(-eps/8) := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hc128] at h₃
    simpa only [mul_comm] using h₃
  have hStrict : L.sc.x^(-9:ℝ)+L.sc.x^(-2+L.sc.eps)+Real.log (Q:ℝ)/(2*Z) <
      c/32*x^(-eps/8) := by
    rw [F.L_x x i hx,F.L_eps x i]
    have hpos : 0 < c/128*x^(-eps/8) := mul_pos hc128 (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx₁) _)
    linarith only [hBound₁,hBound₂,hBound₃,hLogQ,hpos]
  have hExist : ∃ p ∈ P, ∃ t ∈ D.host.TT, t+hP D p ∈ D.host.TT ∧
      Sig X K (aL L) (bL L) p ≤ L.sc.x^(-L.sc.eps) ∧ Good X p (X.bs (stepP D p) t) ∧ ¬ p ∣ Q-1 := by
    by_contra hNone
    have hLoss := typeI_prime_pair_losses X K F.GK_nonneg (F.ex x hx i).kapI_def
      Z hZ₀ P hPsub hCand (hWall x hxWall i) (hBad x hxBad i) Q hQ hNone
    exact (mul_lt_mul_of_pos_left hStrict hm').not_ge (hMain.trans hLoss)
  obtain ⟨p,hp,t,ht,ht',hSig,hGood,hNdiv⟩ := hExist
  obtain ⟨_,hl,hr⟩ := (mem_typeIWindowPrimes hZ₀.le).mp (hPsub hp)
  have hTypeI := (hGuard hx i p hl hr).1
  have hNotLevel : p ≠ Q := by
    intro he
    rw [he] at hr
    exact hq.not_gt hr
  obtain ⟨t₀,h₀,hT,_⟩ := orbit_of_retained_adjacent_top X K p t (hCand p hp) hSig ht ht' hGood
  have hEven := UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p (hCl p hp).2.2
  exact ⟨p,hCand p hp,hTypeI,hl,hr,hNotLevel,hNdiv,(same_word_cand_and_not_drop F x hx i p t₀ h₀).2,
    hEven,t₀,h₀,t,hT,ht'⟩

end

end GlobalTheory.EX.TypeIProduction
