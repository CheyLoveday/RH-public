import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum

import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion

import Formalism.SharpRestriction.GrowthBounds.TypeIAdjacentNativeRow
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudBoundOfPropAndWeylDimension

import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- The literal cutoff is already a natural number in a nonempty served fibre. -/
theorem tauP_natural_exact {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts)
    (p : ℕ) (h : VV X K (aL L) (bL L) p ≠ ∅) :
    ⌈tauP X K (aL L) (bL L) p⌉.toNat =
      X.ep p + ∑ t ∈ VV X K (aL L) (bL L) p,
        D.R.m * (⌈tv X K (aL L) (bL L) p t⌉₊ + Dp K L p + 1) := by
  let B : ℕ := X.ep p + ∑ t ∈ VV X K (aL L) (bL L) p,
        D.R.m * (⌈tv X K (aL L) (bL L) p t⌉₊ + Dp K L p + 1)
  have hB : tauP X K (aL L) (bL L) p = (B : ℝ) := by
    unfold tauP
    rw [if_neg h]
    dsimp [B]
    push_cast
    rfl
  rw [hB]
  simp only [Int.ceil_natCast, Int.toNat_natCast] <;> rfl

/-- Any one lift contribution with enough margin forces the actual omitted
orbit exponent, including both ceiling operations. -/
theorem omission_ceiling_at_least {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts)
    (p : ℕ) (t : HH D) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (R : ℕ)
    (h : (R : ℝ) ≤ gU X K (aL L) (bL L) p j t - Pr X K (bL L) p j t -
      max (g0 X K (aL L) (bL L) p j t) 0) :
    R ≤ ⌈Sv X K (aL L) (bL L) p t⌉.toNat := by
  let f (i : ℕ) := max 0 (gU X K (aL L) (bL L) p i t - Pr X K (bL L) p i t -
      max (g0 X K (aL L) (bL L) p i t) 0)
  have hR : (R : ℝ) ≤ f j := by
    unfold f
    exact h.trans (le_max_right _ _)
  have hnonneg : ∀ i ∈ SizeData₂.lifts D, 0 ≤ f i := by
    intro i _
    unfold f
    exact le_max_left 0 _
  have hsingle : f j ≤ ∑ i ∈ SizeData₂.lifts D, f i :=
    Finset.single_le_sum hnonneg hj
  have hsum : (R : ℝ) ≤ ∑ i ∈ SizeData₂.lifts D, f i := hR.trans hsingle
  have hi := Int.ceil_mono hsum
  rw [Int.ceil_natCast] at hi
  unfold Sv
  change R ≤ ⌈((⌈∑ i ∈ SizeData₂.lifts D, f i⌉ : ℤ) : ℝ)⌉.toNat
  rw [Int.ceil_intCast]
  exact Int.toNat_le_toNat hi

/-- An actual nonempty served orbit supplies the candidate test and discharges
the source drop predicate on that same indexed member. -/
theorem same_word_cand_and_not_drop {eps : ℝ} (F : FamP eps) (x : ℝ) (hx : F.x1 < x)
    (i : F.Ix x) (p : ℕ)
    (t : HH (F.D x i))
    (ht : t ∈ VV (F.Gx x i) F.GK (aL (F.L x i)) (bL (F.L x i)) p) :
    Cand (F.D x i) (F.L x i) F.GK p ∧ p ∉ (F.L x i).drop := by
  have hVV := Finset.ne_empty_of_mem ht
  have hc := (GlobalTheory.EX.Led.cand_of_VV (F.Gx x i) F.GK _ _ p hVV).1
  refine ⟨hc,?_⟩
  intro hd
  exact GlobalTheory.EX.Led.not_noGain (F.Gx x i) F.GK F.Cr p hVV
    (((F.drop_iff x hx i p hc.1).mp hd).1)

def halfStepTent (Z n : ℝ) : ℝ :=
  max 0 (2*Z/n-1) - 2*max 0 ((3*Z/2)/n-1) + max 0 (Z/n-1)

private theorem mul_pos_part (n a : ℝ) (hn : 0 < n) :
    max 0 (a/n-1) * n = max 0 (a-n) := by
  have hEq : (a/n-1)*n = a-n := by field_simp
  by_cases h : a ≤ n
  · have h' : a/n - 1 ≤ 0 := by
      have h'' : a/n ≤ 1 := (div_le_iff₀ hn).mpr (by simpa using h)
      linarith
    rw [max_eq_left h',max_eq_left (sub_nonpos.mpr h),zero_mul]
  · have h' : 0 ≤ a/n - 1 := by
      have h'' : 1 ≤ a/n := (le_div_iff₀ hn).mpr (by simpa using le_of_lt (lt_of_not_ge h))
      linarith
    rw [max_eq_right h', max_eq_right (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h))), hEq]

/-- The half-step second difference is the tent on the exact open interval. -/
theorem half_step_tent_eq (Z n : ℝ) (hZ : 0 ≤ Z) (hn : 0 < n) :
    halfStepTent Z n = max 0 (min (n-Z) (2*Z-n)) / n := by
  apply (eq_div_iff hn.ne').mpr
  unfold halfStepTent
  rw [add_mul,sub_mul,mul_assoc,mul_pos_part n (2*Z) hn,
    mul_pos_part n (3*Z/2) hn,mul_pos_part n Z hn]
  by_cases h1 : n ≤ Z
  · rw [max_eq_right (by linarith : 0 ≤ 2*Z-n),
      max_eq_right (by linarith : 0 ≤ 3*Z/2 - n),
      max_eq_right (by linarith : 0 ≤ Z-n),
      min_eq_left (by linarith : n-Z ≤ 2*Z-n), max_eq_left (by linarith : n-Z ≤ 0)]
    ring
  by_cases h2 : n ≤ 3*Z/2
  · have h1' := le_of_lt (lt_of_not_ge h1)
    rw [max_eq_right (by linarith : 0 ≤ 2*Z-n),
      max_eq_right (by linarith : 0 ≤ 3*Z/2 - n),
      max_eq_left (by linarith : Z-n ≤ 0),
      min_eq_left (by linarith : n-Z ≤ 2*Z-n), max_eq_right (by linarith : 0 ≤ n-Z)]
    ring
  by_cases h3 : n ≤ 2*Z
  · have h1' := le_of_lt (lt_of_not_ge h1)
    have h2' := le_of_lt (lt_of_not_ge h2)
    rw [max_eq_right (by linarith : 0 ≤ 2*Z-n),
      max_eq_left (by linarith : 3*Z/2 - n ≤ 0),
      max_eq_left (by linarith : Z-n ≤ 0),
      min_eq_right (by linarith : 2*Z-n ≤ n-Z), max_eq_right (by linarith : 0 ≤ 2*Z-n)]
    ring
  · have h1' := le_of_lt (lt_of_not_ge h1)
    have h2' := le_of_lt (lt_of_not_ge h2)
    have h3' := le_of_lt (lt_of_not_ge h3)
    rw [max_eq_left (by linarith : 2*Z-n ≤ 0),
      max_eq_left (by linarith : 3*Z/2 - n ≤ 0),
      max_eq_left (by linarith : Z-n ≤ 0),
      min_eq_right (by linarith : 2*Z-n ≤ n-Z), max_eq_left (by linarith : 2*Z-n ≤ 0)]
    ring

theorem half_step_tent_pos_iff (Z n : ℝ) (hZ : 0 ≤ Z) (hn : 0 < n) :
    0 < halfStepTent Z n ↔ Z < n ∧ n < 2*Z := by
  rw [half_step_tent_eq Z n hZ hn]
  constructor
  · intro h
    have hs : 0 < max 0 (min (n-Z) (2*Z-n)) := by
      have hmul := (lt_div_iff₀ hn).mp h
      simpa using hmul
    rcases lt_max_iff.mp hs with h0 | hm
    · exact False.elim (lt_irrefl _ h0)
    · have h1 := (lt_min_iff.mp hm).1
      have h2 := (lt_min_iff.mp hm).2
      exact ⟨by linarith,by linarith⟩
  · rintro ⟨h1,h2⟩
    apply div_pos _ hn
    exact lt_of_lt_of_le (lt_min (by linarith) (by linarith)) (le_max_right _ _)


/-- The first odd visit is excluded on the actual inert orbit when the next
top differs from the starting top. -/
theorem excluded_first_of_adjacent {D : D7} {p : ℕ} (hp : IsResidueClassZero D p)
    (t : HH D) (ht : t + hP D p ∈ D.host.TT) (hh : hP D p ≠ 0) :
    Excl D p t 1 := by
  refine ⟨by decide, t + hP D p, ht, ?_, ?_⟩
  · intro h
    apply hh
    exact add_left_cancel (h.trans (add_zero t).symm)
  · refine ⟨by decide, ?_, fun e he he' => ?_⟩
    · rw [Formalism.MainNotions.AuxBlock8.Pf.St.partner_of_central hp]
      simp
    · omega

/-- A single excluded visit contributes its entire positive part to the
source omission lower bound, with both the orbit loss and penalty retained. -/
theorem omission_gain_ge_first_excluded {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t₀ t : HH D)
    (hp : (2 : ℝ) ≤ p) (ht : t ∈ topsOn X p t₀) (he : Excl D p t 1)
    (ha : ∀ s ∈ topsOn X p t₀, 0 ≤ al L a s)
    (hc : ∀ s ∈ topsOn X p t₀, ∀ e, 0 ≤ capU X b p j s e)
    (hd : 0 ≤ dl X K p t₀) :
    max 0 (al L a t / (p : ℝ) - capU X b p j t 1) - dl X K p t₀ - Pr X K b p j t₀ ≤
      gU X K a b p j t₀ - Pr X K b p j t₀ - max (g0 X K a b p j t₀) 0 := by
  classical
  let S := topsOn X p t₀
  let q (s : HH D) (e : ℕ) := max 0 (al L a s / (p : ℝ)^e - capU X b p j s e)
  let old (s : HH D) (e : ℕ) := if Odd e ∧ ¬ Excl D p s e then q s e else 0
  let all (s : HH D) (e : ℕ) := if Odd e then q s e else 0
  let atom (s : HH D) (e : ℕ) := if s = t ∧ e = 1 then q s e else 0
  let cap (s : HH D) (e : ℕ) := if Odd e then min (al L a s / (p : ℝ)^e) (capU X b p j s e) else 0
  have hq₀ (s : HH D) (e : ℕ) : 0 ≤ q s e := le_max_left _ _
  have hq₁ (s : HH D) (hs : s ∈ S) (e : ℕ) : q s e ≤ al L a s / (p : ℝ)^e :=
    max_le (div_nonneg (ha s hs) (by positivity)) (sub_le_self _ (hc s hs e))
  have hOld (s : HH D) (hs : s ∈ S) : Summable (old s) :=
    Formalism.MainNotions.AuxBlock8.Pf.summable_if_of_le p (al L a s) hp _
      (fun e => Odd e ∧ ¬ Excl D p s e) (hq₀ s) (hq₁ s hs)
  have hAll (s : HH D) (hs : s ∈ S) : Summable (all s) :=
    Formalism.MainNotions.AuxBlock8.Pf.summable_if_of_le p (al L a s) hp _
      Odd (hq₀ s) (hq₁ s hs)
  have hAtom (s : HH D) (hs : s ∈ S) : Summable (atom s) :=
    Formalism.MainNotions.AuxBlock8.Pf.summable_if_of_le p (al L a s) hp _
      (fun e => s = t ∧ e = 1) (hq₀ s) (hq₁ s hs)
  have hPair (s : HH D) (e : ℕ) : old s e + atom s e ≤ all s e := by
    by_cases h : s = t ∧ e = 1
    · obtain ⟨rfl, rfl⟩ := h
      simp [old, atom, all, he, show Odd (1 : ℕ) by decide]
    · by_cases ho : Odd e
      · by_cases hz : Excl D p s e
        · simpa [old, atom, all, h, ho, hz] using hq₀ s e
        · simp [old, atom, all, h, ho, hz]
      · simp [old, atom, all, h, ho]
  have hAt (s : HH D) : (∑' e, atom s e) = if s = t then q t 1 else 0 := by
    by_cases hs : s = t
    · subst s
      rw [if_pos rfl, tsum_eq_single 1]
      · simp [atom]
      · intro e h
        simp [atom, h]
    · simp [atom, hs]
  have hOldAdd :
      (∑ s ∈ S, ∑' e, old s e) + q t 1 ≤ ∑ s ∈ S, ∑' e, all s e := by
    have hSum (s : HH D) (hs : s ∈ S) :
        (∑' e, old s e) + (∑' e, atom s e) ≤ ∑' e, all s e := by
      rw [← (hOld s hs).tsum_add (hAtom s hs)]
      exact ((hOld s hs).add (hAtom s hs)).tsum_le_tsum (hPair s) (hAll s hs)
    have h := Finset.sum_le_sum hSum
    rw [Finset.sum_add_distrib] at h
    simp_rw [hAt] at h
    simpa [ht, S] using h
  have hCap (s : HH D) (hs : s ∈ S) : 0 ≤ ∑' e, cap s e := by
    apply tsum_nonneg
    intro e
    by_cases h : Odd e
    · simpa [cap, h] using le_min (div_nonneg (ha s hs) (by positivity : 0 ≤ (p : ℝ)^e)) (hc s hs e)
    · simp [cap, h]
  have hCapSum :
      (∑ s ∈ S.filter (fun s => ¬ IsV X p s), ∑' e, cap s e) ≤ ∑ s ∈ S, ∑' e, cap s e :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun s hs _ => hCap s hs)
  have hAllCap :
      (∑ s ∈ S, ∑' e, all s e) + (∑ s ∈ S, ∑' e, cap s e) = gam p * ∑ s ∈ S, al L a s := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact Formalism.MainNotions.AuxBlock8.Pf.tsum_pos_add_min
      p (al L a s) hp (ha s hs) _ (hc s hs) Odd (fun _ => Iff.rfl)
  have hMax : max ((∑ s ∈ S, ∑' e, old s e) - dl X K p t₀) 0 ≤ ∑ s ∈ S, ∑' e, old s e :=
    max_le (sub_le_self _ hd) (Finset.sum_nonneg fun s _ => tsum_nonneg fun e => by
      by_cases h : Odd e ∧ ¬ Excl D p s e <;> simp [old, h, hq₀])
  change _ ≤ gam p * (∑ s ∈ S, al L a s) -
    (∑ s ∈ S.filter (fun s => ¬ IsV X p s), ∑' e, cap s e) - dl X K p t₀ -
    Pr X K b p j t₀ - max ((∑ s ∈ S, ∑' e, old s e) - dl X K p t₀) 0
  have htq : q t 1 = max 0 (al L a t / (p : ℝ) - capU X b p j t 1) := by simp [q]
  linarith only [hOldAdd, hCapSum, hAllCap, hMax, htq]

theorem half_step_tent_le_half_inv (Z n : ℝ) (hZ : 0 < Z) (hn : 0 < n) :
    halfStepTent Z n / Z ≤ 1 / (2 * n) := by
  rw [half_step_tent_eq Z n hZ.le hn]
  have h₁ := min_le_left (n - Z) (2*Z - n)
  have h₂ := min_le_right (n - Z) (2*Z - n)
  have hmin : min (n-Z) (2*Z-n) ≤ Z/2 := by linarith
  have hmax : max 0 (min (n-Z) (2*Z-n)) ≤ Z/2 := max_le (by positivity) hmin
  calc
    _ ≤ (Z/2)/n/Z := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmax hn.le) hZ.le
    _ = _ := by field_simp [hn.ne', hZ.ne']

theorem native_band_controls_La {D : D7} (L : SizeData₂ D) (K : Consts)
    (hK : K.Nonneg) (hρ : rhoB D K L.sc ≤ L.sc.x ^ (-2 : ℝ)) :
    8 * (D.R.n : ℝ) * La K L.sc / D.R.k ≤ L.sc.x ^ (-2 : ℝ) := by
  have hLa : 0 ≤ La K L.sc := Formalism.MainNotions.AuxBlock8.Pf.La_nonneg K hK L.sc
  have hr : 0 ≤ K.rho := hK.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hCN⟩ := hK
  have hx : 0 < L.sc.x := zero_lt_one.trans L.sc.one_lt_alt
  have hδ : 1 ≤ L.sc.delta1 * L.sc.x ^ L.sc.eps := by
    unfold Scale.delta1
    rw [← Real.rpow_add hx]
    exact Real.one_le_rpow L.sc.one_lt_alt.le (by linarith [L.sc.eps_pos])
  have hz : 0 ≤ 8 * (D.R.n : ℝ) * La K L.sc / D.R.k := by positivity
  have hmul := mul_le_mul_of_nonneg_left hδ hz
  have hEq : 4 * Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc / D.R.k =
      (8 * (D.R.n : ℝ) * La K L.sc / D.R.k) * (L.sc.delta1 * L.sc.x ^ L.sc.eps) := by
    unfold Nstar
    ring
  have hrest : 0 ≤ K.rho * K.CN * Real.log L.sc.x * La K L.sc / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hr hCN)
      (Real.log_nonneg L.sc.one_lt_alt.le)) hLa) (by positivity)
  unfold rhoB at hρ
  rw [hEq] at hρ
  linarith only [hmul, hrest, hρ]

theorem not_in_band_of_between_first_two_powers {D : D7} (K : Consts) (s : Scale)
    (p : ℕ) (hp : 1 ≤ (p : ℝ)) (h₁ : (p : ℝ) < s.X' * (1 - rhoB D K s))
    (h₂ : s.X' * (1 + rhoB D K s) < (p : ℝ)^2) : ¬ InBand D K s p := by
  rintro ⟨_, _, d, hd, hLo, hHi⟩
  by_cases h : d = 1
  · subst d
    rw [pow_one] at hLo
    exact h₁.not_ge hLo
  · have hd' : 2 ≤ d := by omega
    exact (h₂.trans_le (pow_le_pow_right₀ hp hd')).not_ge hHi

/-- Specialize the finite omitted-visit estimate to the actual top weights and
rational prime on the chosen orbit. -/
theorem omission_ceiling_of_inert_adjacent {D : D7} {L : SizeData₂ D}
    (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg)
    (p j : ℕ) (hp : p.Prime) (hInert : IsResidueClassZero D p)
    (hj : j ∈ SizeData₂.lifts D) (t₀ t : HH D)
    (ht : t ∈ topsOn X p t₀) (ht' : t + hP D p ∈ D.host.TT)
    (hstep : hP D p ≠ 0) (R : ℕ)
    (hR : (R : ℝ) ≤ al L (aL L) t / (p : ℝ) - capU X (bL L) p j t 1 -
      dl X K p t₀ - Pr X K (bL L) p j t₀) :
    R ≤ ⌈Sv X K (aL L) (bL L) p t₀⌉.toNat := by
  have hB (s : HH D) (hs : s ∈ D.host.TT) : L.sc.b' ≤ (bL L s : ℝ) := by
    rw [bL, dif_pos hs]
    exact L.bT_ge ⟨s, hs⟩
  have he := excluded_first_of_adjacent hInert t ht' hstep
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hA (s : HH D) (hs : s ∈ topsOn X p t₀) : 0 ≤ al L (aL L) s :=
    (Formalism.MainNotions.AuxBlock8.Pf.a_bounds P (aL L) (bL L)
      (Formalism.MainNotions.AuxBlock8.Pf.inWin_sizeData L) s
      (Formalism.MainNotions.AuxBlock8.Pf.mem_TT_of_topsOn X p t₀ s hs)).2.2.2.1
  have hC (s : HH D) (_ : s ∈ topsOn X p t₀) (e : ℕ) : 0 ≤ capU X (bL L) p j s e :=
    (Formalism.MainNotions.AuxBlock8.Pf.capU_bounds P X (bL L) hB p j hj s e).1
  have hD := Formalism.MainNotions.AuxBlock8.Pf.dl_nonneg X K hK p hp t₀
  refine omission_ceiling_at_least X K p t₀ j hj R
    (le_trans ?_ (omission_gain_ge_first_excluded X K (aL L) (bL L) p j t₀ t hp' ht he hA hC hD))
  linarith only [hR, le_max_right 0 (al L (aL L) t / (p : ℝ) - capU X (bL L) p j t 1)]

open Formalism.MainNotions.GlobalTheoryTheory

/-- Extend the smoothed sum by zero up to a common upper cutoff. -/
private theorem sumLamChi_extend {q : ℕ} (χ : DirichletCharacter ℂ q)
    (y u : ℝ) (hy : 0 ≤ y) (hu : y ≤ u) :
    sumLamChi χ y =
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod q) *
        ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  unfold sumLamChi
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_mono hu)) ?_
  intro n hn hny
  have h₁ : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h₁)
  have hlt : y < (n : ℝ) := by
    by_contra! h
    exact hny (Finset.mem_Icc.mpr ⟨h₁, (Nat.le_floor_iff hy).2 h⟩)
  have hzero : y / (n : ℝ) - 1 ≤ 0 := by
    have : y / (n : ℝ) ≤ 1 := (div_le_iff₀ hnp).2 (by linarith)
    linarith
  simp [max_eq_right hzero]

/-- Apply the half-step stencil to the literal raw Mangoldt sum. -/
theorem half_step_raw_character_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Z : ℝ) (hZ : 0 ≤ Z) :
    sumLamChi χ (2*Z) - 2 * sumLamChi χ (3*Z/2) + sumLamChi χ Z =
      ∑ n ∈ Finset.Icc 1 ⌊2*Z⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod q) *
        (halfStepTent Z n : ℂ) := by
  rw [sumLamChi_extend χ (3*Z/2) (2*Z) (by positivity) (by linarith),
    sumLamChi_extend χ Z (2*Z) hZ (by linarith)]
  unfold sumLamChi
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  unfold halfStepTent
  simp only [max_comm]
  push_cast
  ring

/-- The principal mass is the stencil of the raw sum's logarithmic main term. -/
theorem half_step_log_main (Z : ℝ) (hZ : 0 < Z) :
    ((2*Z) * Real.log (2*Z) - 2 * ((3*Z/2) * Real.log (3*Z/2)) +
      Z * Real.log Z) / Z = Real.log (32/27) := by
  have hmid : 3*Z/2 = (3/2 : ℝ)*Z := by ring
  have hlog : Real.log (32/27) = 2*Real.log 2 - 3*Real.log (3/2) := by
    rw [show (32/27 : ℝ) = (2:ℝ)^2 / ((3/2 : ℝ)^3) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [hmid, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hZ.ne',
    Real.log_mul (by norm_num : (3/2:ℝ) ≠ 0) hZ.ne', hlog]
  field_simp [hZ.ne']
  <;> ring

theorem half_step_log_main_pos : 0 < Real.log (32/27) :=
  Real.log_pos (by norm_num)

open Classical in
/-- Raw weighted class mass by orthogonality on the same finite host group. -/
theorem weighted_host_class_fourier {ι H : Type*} [AddCommGroup H] [Fintype H]
    (S : Finset ι) (cls : ι → H) (w : ι → ℂ) (g : H) :
    (Fintype.card H : ℂ) * ∑ a ∈ S.filter (fun a => cls a = g), w a =
      ∑ φ : AddChar H ℂ, φ (-g) * (∑ a ∈ S, w a * φ (cls a)) := by
  classical
  calc
    _ = ∑ a ∈ S, w a * ∑ φ : AddChar H ℂ, φ (cls a - g) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.sum_apply_eq_ite]
      by_cases h : cls a = g
      · simp [h, mul_comm]
      · simp [h, sub_ne_zero.mpr h]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun φ _ => Finset.sum_congr rfl fun a _ => ?_
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring


open Formalism.GradedWeylDivisibility

/-- The two consecutive top labels of the original orbit become two cyclically
adjacent top slots in the actual model for this word and place. -/
theorem native_slots_of_inert_top_pair {D : D7} {L : SizeData₂ D} {Gt : GatTies D}
    (X : Inst D L) (Y : LatInst D) (hTie : LatTied Gt X Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (t₀ t : Formalism.MainNotions.G.HH D) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let v := Y.vOf u w hg t₀
    IsResidueClassZero D p → (L.sc.p0 D.R.k ≤ (p : ℝ)) →
    t ∈ topsOn X p t₀ → t + hP D p ∈ D.host.TT → hP D p ≠ 0 →
    G.P.r = 1 ∧
      ∃ s : Fin (G.P.n' v), s ≠ posAdd s 1 ∧
        s ∈ (Y.Fl u w hg).TT v ∧ posAdd s 1 ∈ (Y.Fl u w hg).TT v ∧
        t₀ + s.val • hP D p = t ∧ t₀ + (posAdd s 1).val • hP D p = t + hP D p := by
  classical
  intro p G v hInert hTypeI ht ht' hne
  have hbt : X.bs (stepP D p) t = t₀ := (Finset.mem_filter.mp ht).2
  have hrep : t₀ ∈ reps X p := by
    unfold reps
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, hbt⟩
  obtain ⟨_, _, _, hr, _, _, hpoints⟩ := hTie u w hg
  obtain ⟨hn, hslots⟩ := hpoints t₀ hrep
  change G.P.n' v = addOrderOf (hP D p) at hn
  have hr' : G.P.r = 1 := by
    change G.P.r = if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1 at hr
    simpa only [ite_eq_right (not_lt_of_ge hTypeI)] using hr
  have hstep := Formalism.MainNotions.AuxBlock8.Pf.St.frobenius_step_large_order hInert
  obtain ⟨j, hj⟩ := X.bs_orb (hP D p) t
  have hbt' := hbt
  rw [hstep] at hbt'
  rw [hbt'] at hj
  have hpos : 0 < G.P.n' v := by rw [hn]; exact addOrderOf_pos _
  let s : Fin (G.P.n' v) := ⟨j % G.P.n' v, Nat.mod_lt _ hpos⟩
  have hs : t₀ + s.val • hP D p = t := by
    change t₀ + (j % G.P.n' v) • hP D p = t
    rw [hn, mod_addOrderOf_nsmul, hj]
  have hs' : t₀ + (posAdd s 1).val • hP D p = t + hP D p := by
    change t₀ + ((s.val + 1) % G.P.n' v) • hP D p = _
    rw [congrArg (fun n : ℕ => (s.val + 1) % n) hn,
      mod_addOrderOf_nsmul, add_nsmul, one_nsmul, ← add_assoc, hs]
  refine ⟨hr', s, ?_, ?_, ?_, hs, hs'⟩
  · intro h
    have heq := congrArg (fun s : Fin (G.P.n' v) => t₀ + s.val • hP D p) h
    rw [hs, hs'] at heq
    exact hne (add_left_cancel (heq.symm.trans (add_zero t).symm))
  · apply (hslots s).2.1.mpr
    rw [hs]
    exact (Finset.mem_filter.mp ht).1
  · apply (hslots (posAdd s 1)).2.1.mpr
    rwa [hs']

private theorem adjacent_multiplicity_eq {m : ℕ} (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    ((nuOf lam i - nuNext (nuOf lam) i : ℕ) : ℤ) = lam i - lam ⟨i.val+1, hi⟩ := by
  let j : Fin (m + 1) := ⟨i.val+1, hi⟩
  have hij : i ≤ j := Nat.le_succ _
  have hiL := hlam (Fin.le_last i)
  have hjL := hlam (Fin.le_last j)
  have hji := hlam hij
  unfold nuNext
  rw [dite_eq_left hi]
  change (((lam i - lam (Fin.last m)).toNat - (lam j - lam (Fin.last m)).toNat : ℕ) : ℤ) =
    lam i - lam j
  omega

open Classical in
theorem native_top_marked_capacity {p : ℕ} {G : GAtP p}
    (Fl : Fills G) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (hs : s ∈ Fl.TT v)
    (hm : 2 ≤ G.P.m) (R : ℕ) (hR : (R : ℤ) ≤ Fl.a v s - (Fl.c : ℤ)) :
    R ≤ if IsTypeV s then typeIFirstMultiplicity G v s else typeILastProperMultiplicity G v s := by
  classical
  let m := G.P.m
  let k : Fin (m + 1) := ⟨1, by omega⟩
  have hA := ((Fl.base v s).1 hs).1
  have hBound := ((Fl.base v s).1 hs).2.2 k (by change 0 < 1; decide) (by change 1 < m; omega)
  have hk := (le_abs_self _).trans hBound
  have hlam := Formalism.MainNotions.flipOneThree.Pf.lamAt_anti _ (G.P.dom v) s
  by_cases h : IsTypeV s
  · rw [ite_eq_left h]
    have hi : (0 : Fin (m + 1)).val + 1 < m + 1 := by change 1 < m + 1; omega
    have heq := adjacent_multiplicity_eq (lamAt (G.P.lam0 v) s) hlam 0 hi
    change (typeIFirstMultiplicity G v s : ℤ) = _ at heq
    change Even s.val at h
    rw [lamAt, ite_eq_left h] at heq
    change (typeIFirstMultiplicity G v s : ℤ) = G.P.lam0 v s 0 - G.P.lam0 v s k at heq
    omega
  · rw [ite_eq_right h]
    let i : Fin (m + 1) := ⟨m-1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    have hi : i.val+1 < m+1 := by change m-1+1 < m+1; omega
    have jlast : (⟨i.val+1, hi⟩ : Fin (m+1)) = Fin.last m := by
      apply Fin.ext
      change m-1+1 = m
      omega
    have hir : i.rev = k := by
      apply Fin.ext
      rw [Fin.val_rev]
      change m + 1 - ((m - 1) + 1) = 1
      omega
    have hjr : (Fin.last m).rev = (0 : Fin (m+1)) := by simp
    have heq := adjacent_multiplicity_eq (lamAt (G.P.lam0 v) s) hlam i hi
    change (typeILastProperMultiplicity G v s : ℤ) = _ at heq
    rw [jlast] at heq
    change ¬ Even s.val at h
    rw [lamAt, ite_eq_right h] at heq
    change _ = -G.P.lam0 v s i.rev - -G.P.lam0 v s (Fin.last m).rev at heq
    rw [hir, hjr] at heq
    omega


open Filter

private theorem typeI_exponential_gaps (e : ℝ) (he : 16 ≤ e) :
    4 * Real.exp (e * (3/4)) < Real.exp e ∧
      2 * Real.exp e < (Real.exp (e * (3/4)))^2 := by
  have h₁ : 4 < Real.exp (e/4) := by
    have := Real.add_one_le_exp (e/4)
    linarith
  have h₂ : 2 < Real.exp (e/2) := by
    have := Real.add_one_le_exp (e/2)
    linarith
  constructor
  · calc
      4 * Real.exp (e*(3/4)) < Real.exp (e/4) * Real.exp (e*(3/4)) :=
        mul_lt_mul_of_pos_right h₁ (Real.exp_pos _)
      _ = Real.exp e := by rw [← Real.exp_add]; congr 1; ring
  · calc
      2 * Real.exp e < Real.exp (e/2) * Real.exp e :=
        mul_lt_mul_of_pos_right h₂ (Real.exp_pos _)
      _ = (Real.exp (e*(3/4)))^2 := by rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The original half-step interval lies above the Type I cutoff and strictly
between the forbidden band for the first power and all higher powers. -/
theorem typeI_interval_guards {eps : ℝ} (F : FamP eps) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let L := F.L x i
      let Z := L.sc.X' ^ (3/4 : ℝ)
      ∀ p : ℕ, Z < (p : ℝ) → (p : ℝ) < 2*Z →
        L.sc.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < L.sc.X' ∧ ¬ InBand D F.GK L.sc p := by
  have ha : 0 < eps/3 := by positivity
  have hev := (tendsto_rpow_atTop ha).eventually_ge_atTop 16
  have hlog := Formalism.MainNotions.AuxBlock8.Pf.ev_log (152/3) (eps/3) ha
  filter_upwards [hev, hlog, eventually_ge_atTop (2 : ℝ)] with x he hlog hx2
  intro hx i D L Z p hp₁ hp₂
  have hx0 : 0 < x := by linarith
  have hxL : L.sc.x = x := F.L_x x i hx
  have heL : L.sc.eps = eps := F.L_eps x i
  let e := x ^ (eps/3)
  have hX : L.sc.X' = Real.exp e := by rw [Scale.X', hxL, heL]
  have hZ : Z = Real.exp (e*(3/4)) := by change L.sc.X' ^ (3/4 : ℝ) = _; rw [hX, Real.exp_mul]
  have hZpos : 0 < Z := by rw [hZ]; positivity
  have hgap := typeI_exponential_gaps e he
  rw [← hZ, ← hX] at hgap
  have hρ := F.rho_le x hx i
  change rhoB D F.GK L.sc ≤ x ^ (-2 : ℝ) at hρ
  have hrpow : x ^ (-2 : ℝ) = (x^2)⁻¹ := by rw [Real.rpow_neg hx0.le]; norm_num
  rw [hrpow] at hρ
  have hxSq : 4 ≤ x^2 := by nlinarith [sq_nonneg (x-2)]
  have hinv : (x^2)⁻¹ ≤ 1/4 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hxSq
  have hρ' : rhoB D F.GK L.sc ≤ 1/4 := hρ.trans hinv
  have hXpos : 0 < L.sc.X' := by rw [hX]; positivity
  have hk := Formalism.MainNotions.AuxBlock8.Pf.k_le_x_pow_six L (F.sizes x hx i)
  rw [hxL] at hk
  have h12 : (x ^ (6 : ℝ)) ^ (2 : ℕ) = x ^ (12 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hcut : L.sc.p0 D.R.k ≤ x ^ (38 : ℝ) := by
    unfold Scale.p0 Scale.A
    rw [hxL]
    calc
      _ ≤ (x ^ (6 : ℝ))^2 * x ^ (26 : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hk _) (by positivity)
      _ = _ := by rw [h12, ← Real.rpow_add hx0]; norm_num
  have hzcut : x ^ (38 : ℝ) ≤ Z := by
    rw [hZ]
    apply Formalism.MainNotions.AuxBlock8.Pf.xpow_le_exp _ _ _ hx0
    change 38 * Real.log x ≤ x ^ (eps/3) * (3/4)
    linarith only [hlog]
  have hpbelow : (p : ℝ) < L.sc.X' := hp₂.trans (by linarith [hgap.1, hZpos])
  have hpband : (p : ℝ) < L.sc.X' * (1 - rhoB D F.GK L.sc) := by
    calc
      _ < L.sc.X' * (1/2) := hp₂.trans (by linarith [hgap.1])
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hXpos.le
  have hpsq : L.sc.X' * (1 + rhoB D F.GK L.sc) < (p : ℝ)^2 := by
    calc
      _ ≤ L.sc.X' * 2 := mul_le_mul_of_nonneg_left (by linarith) hXpos.le
      _ < Z^2 := by linarith [hgap.2]
      _ ≤ _ := pow_le_pow_left₀ hZpos.le hp₁.le 2
  have hpone : 1 ≤ (p : ℝ) := by
    have hz₁ : 1 ≤ Z := by
      rw [hZ, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by change 0 ≤ (x ^ (eps/3))*(3/4); positivity)
    exact hz₁.trans hp₁.le
  exact ⟨(hcut.trans hzcut).trans hp₁.le, hpbelow,
    not_in_band_of_between_first_two_powers F.GK L.sc p hpone hpband hpsq⟩

theorem native_top_bottom_le_two {D : D7} {L : SizeData₂ D} (hS : SizesAt L)
    (t : G.HH D) (ht : t ∈ D.host.TT) : (bL L t : ℝ) ≤ 2*L.sc.b' := by
  obtain ⟨_,_,_,_,_,_,_,_,hLa,hρ,hBot,_⟩ := hS
  have hLa₀ := (Real.rpow_nonneg L.sc.x_pos.le L.sc.eps).trans hLa.1
  have hrest : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / (D.R.k:ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg L.sc.x_pos.le _) (Real.log_nonneg L.sc.one_lt_alt.le)) hLa₀) (Nat.cast_nonneg _)
  have hx : L.sc.x^(-2:ℝ) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by norm_num : (-2:ℝ) ≤ 0)
  have hFirst : szNst L * L.sc.x^L.sc.eps * L.LaG / (D.R.k:ℝ) ≤ 1 := by
    have hh := hρ.trans hx
    have hEq : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k:ℝ) =
        4*(szNst L * L.sc.x^L.sc.eps * L.LaG / (D.R.k:ℝ)) := by ring
    rw [hEq] at hh
    linarith only [hrest,hh]
  rw [bL,dif_pos ht]
  have h := hBot ⟨t,ht⟩
  calc
    _ ≤ L.sc.b' + szNst L * L.sc.x^L.sc.eps * L.LaG * L.sc.b' / (D.R.k:ℝ) := h
    _ = L.sc.b' + (szNst L * L.sc.x^L.sc.eps * L.LaG / (D.R.k:ℝ))*L.sc.b' := by ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hFirst L.sc.b'_pos.le
      linarith only [hh]

def typeIRoundingCost {D : D7} (L : SizeData₂ D) (K : Consts) (p d : ℕ) : ℝ :=
  K.kappaThresholdTwo * (Qp L.sc p * c6f K L p d +
    (D.R.k:ℝ) * Qp L.sc p + (D.R.k:ℝ) * Real.logb p L.sc.a + cG L)

def typeILeadingCost {D : D7} (L : SizeData₂ D) (K : Consts) (p : ℕ) : ℝ :=
  2*L.sc.b' + K.kappaThresholdOne * (N1 L.sc:ℝ) *
    (L.sc.a/(p:ℝ)^2 + La K L.sc * L.sc.a / ((p:ℝ)*(D.R.k:ℝ)))

theorem native_cutoff_upper {D : D7} {L : SizeData₂ D} (hS : SizesAt L) (X : Inst D L)
    (K : Consts) (hK : K.Nonneg) (p : ℕ) (hp : p.Prime)
    (hI : IsResidueClassZero D p) (hTypeI : L.sc.p0 D.R.k ≤ (p:ℝ))
    (hVV : VV X K (aL L) (bL L) p ≠ ∅) :
    let d := addOrderOf (hP D p)
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    (T:ℝ)+1 ≤ (X.ep p:ℝ)+1 + (D.R.m:ℝ)*(D.R.n:ℝ)*
      (typeILeadingCost L K p + typeIRoundingCost L K p d + 2*(d:ℝ)*cG L + (DIf K L p d:ℝ)+2) := by
  classical
  intro d T
  let S := VV X K (aL L) (bL L) p
  let A := typeILeadingCost L K p + typeIRoundingCost L K p d
  let B := 2*(d:ℝ)*cG L + (DIf K L p d:ℝ)+2
  have hlog := (AuxBlock8.Pf.logb_facts L.sc p hp).1
  have hLa := AuxBlock8.Pf.La_nonneg K hK L.sc
  have hK1 : 0 ≤ K.kappaThresholdOne := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := hK
    assumption
  have hK2 : 0 ≤ K.kappaThresholdTwo := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := hK
    assumption
  have hcg : 0 ≤ cG L := by
    unfold cG
    rw [L.Sc_eq]
    exact mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (by exact_mod_cast D.s.Del_pos.le)))
  have hQ : 0 ≤ Qp L.sc p := by unfold Qp; positivity
  have hNplus : 0 ≤ NplusF L.sc d :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (Real.rpow_nonneg L.sc.x_pos.le _)
  have h6 : 0 ≤ c6f K L p d := by unfold c6f; positivity
  have hA : 0 ≤ A := by
    have ha := L.sc.a_pos.le
    have hb := L.sc.b'_pos.le
    unfold A typeILeadingCost typeIRoundingCost
    positivity
  have hB : 0 ≤ B := by unfold B; positivity
  have hS' (t : G.HH D) (ht : t ∈ S) :
      (⌈tv X K (aL L) (bL L) p t⌉₊:ℝ) + (Dp K L p:ℝ)+1 ≤
        (Nv X p t:ℝ)*A+B := by
    let U := topsPos D p t
    have hU : U.card = Nv X p t := (AuxBlock8.Pf.Nv_eq X p hI t
      (AuxBlock8.Pf.VV_subset_reps X K _ _ p ht)).symm
    have hFirst (y : Fin d) (hy : y ∈ U.filter (fun y => ¬ IsTypeV y)) :
        (if dMinus U y = 0 then (0:ℝ) else
          min ((wPos D p t (bL L) y : ℤ):ℝ)
            (((wPos D p t (aL L) (posAdd y (d-dMinus U y)):ℤ):ℝ)/(p:ℝ)^dMinus U y)) ≤ 2*L.sc.b' := by
      by_cases hh : dMinus U y = 0
      · rw [if_pos hh]
        exact mul_nonneg (by norm_num) L.sc.b'_pos.le
      · rw [if_neg hh]
        have ht : t + (y:ℕ) • hP D p ∈ D.host.TT :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
        apply (min_le_left _ _).trans
        unfold wPos
        exact native_top_bottom_le_two hS _ ht
    have htv : tv X K (aL L) (bL L) p t ≤ (Nv X p t:ℝ)*A+2*(d:ℝ)*cG L := by
      rw [tv,if_neg (not_lt.mpr hTypeI)]
      change tIf K L p d U (wPos D p t (aL L)) (wPos D p t (bL L)) ≤ _
      unfold tIf
      have hh : (∑ y ∈ U.filter (fun y => ¬ IsTypeV y),
        if dMinus U y = 0 then 0 else min (wPos D p t (bL L) y:ℝ)
          ((wPos D p t (aL L) (posAdd y (d-dMinus U y)):ℝ) / (p:ℝ)^dMinus U y)) ≤
            (Nv X p t:ℝ)*(2*L.sc.b') := by
        calc
          _ ≤ ∑ y ∈ U.filter (fun y => ¬ IsTypeV y), 2*L.sc.b' :=
            Finset.sum_le_sum hFirst
          _ ≤ _ := by
            simp only [Finset.sum_const,nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast (Finset.card_filter_le _ _).trans_eq hU)
              (mul_nonneg (by norm_num) L.sc.b'_pos.le)
      rw [hU]
      unfold A typeILeadingCost typeIRoundingCost
      linarith only [hh]
    have htv₀ : 0 ≤ (Nv X p t:ℝ)*A+2*(d:ℝ)*cG L := by positivity
    have hc₁ : (⌈tv X K (aL L) (bL L) p t⌉₊:ℝ) ≤
        (⌈(Nv X p t:ℝ)*A+2*(d:ℝ)*cG L⌉₊:ℝ) := Nat.cast_le.mpr (Nat.ceil_mono htv)
    have hc := hc₁.trans (Nat.ceil_lt_add_one htv₀).le
    have hCl : ¬ IsSg D p := fun h => by have hh := hI.symm.trans h; cases hh
    have hDp : Dp K L p = DIf K L p d := by rw [Dp,if_neg (not_lt.mpr hTypeI),nP,if_neg hCl]
    rw [hDp]
    unfold B
    linarith only [hc]
  have hSum : (∑ t ∈ S, (Nv X p t:ℝ)) ≤ (D.R.n:ℝ) := by
    have hCount := (AuxBlock8.Pf.sum_Nv_le X p S).trans (Finset.card_le_univ D.host.TT)
    change (∑ t ∈ S, Nv X p t) ≤ Fintype.card D.R.A at hCount
    rw [D.R.card_A] at hCount
    exact_mod_cast hCount
  have hCard : (S.card:ℝ) ≤ (D.R.n:ℝ) := by
    have hc : S.card ≤ Fintype.card D.R.A := Finset.card_le_univ S
    exact_mod_cast hc.trans_eq D.R.card_A
  have hU : ∑ t ∈ S, ((Nv X p t:ℝ)*A+B) ≤ (D.R.n:ℝ)*(A+B) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (D.R.n:ℝ)*A+(D.R.n:ℝ)*B :=
        add_le_add (mul_le_mul_of_nonneg_right hSum hA) (mul_le_mul_of_nonneg_right hCard hB)
      _ = _ := by ring
  have hFinal := (Finset.sum_le_sum fun t ht =>
    mul_le_mul_of_nonneg_left (hS' t ht) (by positivity : 0 ≤ (D.R.m:ℝ))).trans
      ((show (∑ t ∈ S, (D.R.m:ℝ)*((Nv X p t:ℝ)*A+B)) =
          (D.R.m:ℝ)*∑ t ∈ S, ((Nv X p t:ℝ)*A+B) by rw [Finset.mul_sum]).le.trans
        (mul_le_mul_of_nonneg_left hU (by positivity)))
  have hAB : A+B = typeILeadingCost L K p + typeIRoundingCost L K p d +
      2*(d:ℝ)*cG L + (DIf K L p d:ℝ)+2 := by dsimp [A,B]; ring
  rw [← hAB]
  change (↑(⌈tauP X K (aL L) (bL L) p⌉.toNat):ℝ)+1 ≤ _
  rw [tauP_natural_exact X K p hVV]
  push_cast
  change (X.ep p:ℝ)+(∑ t ∈ S, (D.R.m:ℝ)*((⌈tv X K (aL L) (bL L) p t⌉₊:ℝ)+(Dp K L p:ℝ)+1))+1 ≤ _
  linarith only [hFinal]
theorem exp_neg_rpow_eventually_le_rpow (c α N : ℝ) (hc : 0 < c) (hα : 0 < α) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-c*x^α) ≤ x^(-N) := by
  have h := AuxBlock8.Pf.ev_log (N/c) α hα
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  rw [Real.rpow_def_of_pos hxpos (-N), Real.exp_le_exp]
  have h₁ := mul_le_mul_of_nonneg_left hx hc.le
  have h₂ : c * (N/c * Real.log x) = N * Real.log x := by field_simp [hc.ne']
  rw [h₂] at h₁
  linarith only [h₁]


theorem family_typeI_basic_sizes {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let L := F.L x i
      (D.R.n:ℝ) ≤ x^(3:ℝ) ∧ (D.R.m:ℝ) ≤ x ∧ (D.R.k:ℝ) ≤ x^(6:ℝ) ∧
        (N1 L.sc:ℝ) ≤ x^(1/2:ℝ) := by
  have hN1 := AuxBlock8.Pf.ev_log (AuxBlock8.Pf.cNE eps) (1/2) (by norm_num)
  filter_upwards [hN1,eventually_ge_atTop (Real.exp 1),eventually_ge_atTop (1:ℝ)] with x hN1 hxE hx₁
  intro hx i D L
  have hxpos : 0 < x := zero_lt_one.trans_le hx₁
  have hS := F.sizes x hx i
  have hNx := hS.1.2
  change (D.R.n:ℝ) ≤ L.sc.x^(2+8*L.sc.eps+L.sc.eps/100) at hNx
  rw [F.L_x x i hx,F.L_eps x i] at hNx
  have hn : (D.R.n:ℝ) ≤ x^(3:ℝ) := hNx.trans
    (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith only [heps']))
  have hm := hS.2.1.2
  change (D.R.m:ℝ) ≤ L.sc.x^(L.sc.eps/100) * Real.sqrt (L.sc.x*L.sc.x^(-(L.sc.eps/8))) at hm
  rw [F.L_x x i hx,F.L_eps x i] at hm
  have hδ : x^(-(eps/8)) ≤ 1 := by
    simpa only [Real.rpow_zero] using (Real.rpow_le_rpow_of_exponent_le hx₁
      (show -(eps/8) ≤ 0 by linarith))
  have hm' : (D.R.m:ℝ) ≤ x := by
    calc
      _ ≤ x^(eps/100)*Real.sqrt (x*1) := hm.trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_left hδ hxpos.le)) (by positivity))
      _ = x^(eps/100+1/2) := by rw [mul_one,Real.sqrt_eq_rpow,← Real.rpow_add hxpos]
      _ ≤ _ := by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hx₁ (show eps/100+1/2 ≤ 1 by linarith only [heps'])
  have hk := AuxBlock8.Pf.k_le_x_pow_six L hS
  rw [F.L_x x i hx] at hk
  have hN := AuxBlock8.Pf.first_count_le_log L.sc (by rw [F.L_x x i hx]; exact hxE)
  rw [F.L_x x i hx,F.L_eps x i] at hN
  exact ⟨hn,hm',hk,hN.trans hN1⟩

theorem typeI_prime_cutoff_scales {eps : ℝ} (F : FamP eps) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let L := F.L x i
      let Z := L.sc.X' ^ (3/4:ℝ)
      ∀ p : ℕ, p.Prime → Z < (p:ℝ) → (p:ℝ) < 2*Z →
        (p:ℝ)/L.sc.X' ≤ 2*Real.exp (-(1/4)*x^(eps/3)) ∧
        1/(p:ℝ) ≤ Real.exp (-(3/4)*x^(eps/3)) ∧ (p:ℝ) < L.sc.X' := by
  filter_upwards [typeI_interval_guards F heps] with x hGuard
  intro hx i L Z p hp hLo hHi
  let e := x^(eps/3)
  have hX : L.sc.X' = Real.exp e := by unfold e; rw [Scale.X',F.L_x x i hx,F.L_eps x i]
  have hZ : Z = Real.exp ((3/4)*e) := by
    change L.sc.X' ^ (3/4:ℝ) = _
    rw [hX,mul_comm,Real.exp_mul]
  have hZ₀ : 0 < Z := by rw [hZ]; positivity
  have hX₀ : 0 < L.sc.X' := by rw [hX]; positivity
  refine ⟨?_,?_,(hGuard hx i p hLo hHi).2.1⟩
  · calc
      _ ≤ 2*Z/L.sc.X' := div_le_div_of_nonneg_right hHi.le hX₀.le
      _ = _ := by
        rw [hZ,hX,mul_div_assoc,← Real.exp_sub]
        congr 2
        ring
  · calc
      _ ≤ 1/Z := one_div_le_one_div_of_le hZ₀ hLo.le
      _ = _ := by rw [one_div,hZ,← Real.exp_neg,neg_mul]

theorem family_typeI_leading_small {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let L := F.L x i
      let Z := L.sc.X' ^ (3/4:ℝ)
      ∀ p : ℕ, p.Prime → Z < (p:ℝ) → (p:ℝ) < 2*Z →
        (D.R.m:ℝ)*(D.R.n:ℝ)*typeILeadingCost L F.GK p ≤ (3/32)*(L.sc.a/(p:ℝ)) := by
  let K := F.GK.kappaThresholdOne
  have hK : 0 ≤ K := F.GK_nonneg.2.2.2.2.2.2.2.2.1
  have hE₁ := exp_neg_rpow_eventually_le_rpow (1/4) (eps/3) 9 (by norm_num) (by positivity)
  have hE₂ := exp_neg_rpow_eventually_le_rpow (3/4) (eps/3) 9 (by norm_num) (by positivity)
  have hB₁ := AuxBlock8.Pf.ev_pow 128 (-5) 0 (by norm_num)
  have hB₂ := AuxBlock8.Pf.ev_pow (32*K) (-4) 0 (by norm_num)
  have hB₃ := AuxBlock8.Pf.ev_pow (4*K) (-1/2) 0 (by norm_num)
  filter_upwards [family_typeI_basic_sizes F heps heps',typeI_prime_cutoff_scales F heps,
    hE₁,hE₂,hB₁,hB₂,hB₃,eventually_ge_atTop (1:ℝ)]
    with x hSize hWin hE₁ hE₂ hB₁ hB₂ hB₃ hx₁
  intro hx i D L Z p hp hlo hhi
  obtain ⟨hn,hμ,_,hN₁⟩ := hSize hx i
  obtain ⟨hPX,hInv,_⟩ := hWin hx i p hp hlo hhi
  have x0 : 0 < x := zero_lt_one.trans_le hx₁
  let μ := (D.R.m:ℝ)
  let n := (D.R.n:ℝ)
  let N := (N1 L.sc:ℝ)
  let a := L.sc.a
  have ha : 0 < a := L.sc.a_pos
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hk₀ : 0 < (D.R.k:ℝ) := by exact_mod_cast (show 0 < D.R.k by have := D.R.five_le_k; omega)
  have hX : 0 < L.sc.X' := zero_lt_one.trans_le L.sc.one_le_X'
  have hLa := AuxBlock8.Pf.La_nonneg F.GK F.GK_nonneg L.sc
  have hBand := native_band_controls_La L F.GK F.GK_nonneg
    (by rw [F.L_x x i hx]; exact F.rho_le x hx i)
  rw [F.L_x x i hx] at hBand
  have hA : 0 ≤ n * La F.GK L.sc / (D.R.k:ℝ) := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hLa) hk₀.le
  have hA' : n * La F.GK L.sc / (D.R.k:ℝ) ≤ x^(-2:ℝ)/8 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<8)).mpr
    convert hBand using 1 <;> dsimp [n] <;> ring
  have hμn : μ*n ≤ x^(4:ℝ) := by
    calc
      _ ≤ x*x^(3:ℝ) := mul_le_mul hμ hn (Nat.cast_nonneg _) x0.le
      _ = _ := by nth_rw 1 [← Real.rpow_one x]; rw [← Real.rpow_add x0]; norm_num
  have hμnN : μ*n*N ≤ x^(5:ℝ) := by
    have hNx : N ≤ x := hN₁.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num : (1/2:ℝ) ≤ 1))
    calc
      _ ≤ x^(4:ℝ)*x := mul_le_mul hμn hNx (Nat.cast_nonneg _) (by positivity)
      _ = _ := by nth_rw 2 [← Real.rpow_one x]; rw [← Real.rpow_add x0]; norm_num
  have hμN : μ*N ≤ x^(3/2:ℝ) := by
    calc
      _ ≤ x*x^(1/2:ℝ) := mul_le_mul hμ hN₁ (Nat.cast_nonneg _) x0.le
      _ = _ := by nth_rw 1 [← Real.rpow_one x]; rw [← Real.rpow_add x0]; norm_num
  simp only [Real.rpow_zero] at hB₁ hB₂ hB₃
  have hFirst : 2*μ*n*((p:ℝ)/L.sc.X') ≤ 1/32 := by
    have hpX := hPX.trans (mul_le_mul_of_nonneg_left hE₁ (by norm_num))
    calc
      _ = 2*((μ*n)*((p:ℝ)/L.sc.X')) := by ring
      _ ≤ 2*(x^(4:ℝ)*(2*x^(-9:ℝ))) := mul_le_mul_of_nonneg_left
        (mul_le_mul hμn hpX (by positivity) (by positivity)) (by norm_num)
      _ = 4*x^(-5:ℝ) := by
        calc
          _ = 4*(x^(4:ℝ)*x^(-9:ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add x0]; norm_num
      _ ≤ _ := by linarith only [hB₁]
  have hSecond : K*(μ*n*N)*(1/(p:ℝ)) ≤ 1/32 := by
    calc
      _ = K*((μ*n*N)*(1/(p:ℝ))) := by ring
      _ ≤ K*(x^(5:ℝ)*x^(-9:ℝ)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hμnN (hInv.trans hE₂) (by positivity) (by positivity)) hK
      _ = K*x^(-4:ℝ) := by rw [← Real.rpow_add x0]; norm_num
      _ ≤ _ := by linarith only [hB₂]
  have hThird : K*(μ*N)*(n*La F.GK L.sc/(D.R.k:ℝ)) ≤ 1/32 := by
    calc
      _ = K*((μ*N)*(n*La F.GK L.sc/(D.R.k:ℝ))) := by ring
      _ ≤ K*(x^(3/2:ℝ)*(x^(-2:ℝ)/8)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hμN hA' hA (by positivity)) hK
      _ = K*x^(-1/2:ℝ)/8 := by
        rw [← mul_div_assoc, ← Real.rpow_add x0]
        norm_num
        <;> ring
      _ ≤ _ := by linarith only [hB₃]
  have hEq : μ*n*typeILeadingCost L F.GK p =
      (a/(p:ℝ))*(2*μ*n*((p:ℝ)/L.sc.X') + K*(μ*n*N)*(1/(p:ℝ)) +
        K*(μ*N)*(n*La F.GK L.sc/(D.R.k:ℝ))) := by
    unfold typeILeadingCost Scale.b'
    change μ*n*(2*(a/L.sc.X')+K*N*(a/(p:ℝ)^2+La F.GK L.sc*a/((p:ℝ)*(D.R.k:ℝ)))) = _
    field_simp [hp₀.ne',hk₀.ne',hX.ne']
    <;> ring
  rw [hEq,mul_comm (3/32:ℝ)]
  exact mul_le_mul_of_nonneg_left (by linarith only [hFirst,hSecond,hThird]) (div_nonneg ha.le hp₀.le)

theorem native_first_cap_upper {D : D7} {L : SizeData₂ D} (hS : SizesAt L)
    (X : Inst D L) (p j : ℕ) (hI : IsResidueClassZero D p) (hj : j ∈ SizeData₂.lifts D)
    (t : G.HH D) (ht : t+hP D p ∈ D.host.TT) :
    capU X (bL L) p j t 1 ≤ 2*L.sc.b'+L.sc.b'/L.sc.x+L.etaSz+cG L := by
  have hPartner : partner D p t 1 = (false,t+hP D p) := by
    rw [AuxBlock8.Pf.St.partner_of_central hI]
    simp
  have hOff := (X.off_top j (false,t+hP D p) ⟨rfl,ht⟩).2
  have hBot := native_top_bottom_le_two hS (t+hP D p) ht
  have hJ := AuxBlock8.Pf.kaJ_nonneg (D := D) j hj
  unfold capU fillG fill
  rw [hPartner]
  simp only [Prod.fst,Prod.snd,ht,and_true,ite_true]
  linarith only [hOff,hBot,hJ]

open Classical in
theorem native_first_penalty_upper {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (K : Consts) (p j : ℕ) (hI : IsResidueClassZero D p)
    (hTypeI : L.sc.p0 D.R.k ≤ (p:ℝ)) (hj : j ∈ SizeData₂.lifts D)
    (t₀ : G.HH D) (hEta : 0 ≤ L.etaSz) :
    Pr X K (bL L) p j t₀ ≤
      (Nv X p t₀:ℝ)*(L.sc.b'/L.sc.x+L.etaSz) +
        K.Pr1*(addOrderOf (hP D p):ℝ)*(L.sc.w'' D.R.n+L.etaSz+cG L+Nm D) := by
  let S := (topsOn X p t₀).filter (fun s => ¬ IsV X p s)
  let u := L.sc.b'/L.sc.x+L.etaSz
  have hu : 0 ≤ u := add_nonneg (div_nonneg L.sc.b'_pos.le L.sc.x_pos.le) hEta
  have hJ := AuxBlock8.Pf.kaJ_nonneg (D := D) j hj
  have hSub : ∑ s ∈ S, (fillG X (bL L) j (false,s) - (bL L s:ℝ)) ≤ (Nv X p t₀:ℝ)*u := by
    calc
      _ ≤ ∑ _ ∈ S, u := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        have hT : s ∈ D.host.TT := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
        have hOff := (X.off_top j (false,s) ⟨rfl,hT⟩).2
        unfold fillG fill
        simp only [Prod.fst,Prod.snd,hT,and_true,ite_true]
        unfold u
        linarith only [hOff,hJ]
      _ = (S.card:ℝ)*u := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        apply Nat.cast_le.mpr
        exact Finset.card_filter_le _ _) hu
  rw [Pr,if_pos hTypeI,AuxBlock8.Pf.St.partner_count_of_central hI]
  exact add_le_add hSub le_rfl

structure TypeIResidualScales {D : D7} (L : SizeData₂ D) (K : Consts) (p : ℕ) (U : ℝ) : Prop where
  large : 40 ≤ U
  sizeM : (D.R.m:ℝ) ≤ U
  sizeN : (D.R.n:ℝ) ≤ U
  sizeK : (D.R.k:ℝ) ≤ U
  order : (addOrderOf (hP D p):ℝ) ≤ U
  count : (N1 L.sc:ℝ) ≤ U
  loga : Real.logb p L.sc.a ≤ U
  loga2 : Real.logb p (2*L.sc.a) ≤ U
  scaleA : (L.sc.x^(Scale.A/2))^2 ≤ U
  conductorHeight : Qp L.sc p ≤ U
  eta : L.etaSz ≤ U
  nm : Nm D ≤ U
  cGUpper : cG L ≤ U^3
  boundDI : K.DI ≤ U
  boundKTwo : K.kappaThresholdTwo ≤ U

theorem family_typeI_residual_scales {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let L := F.L x i
      let Z := L.sc.X' ^ (3/4:ℝ)
      ∀ p : ℕ, p.Prime → Z < (p:ℝ) → (p:ℝ) < 2*Z →
        TypeIResidualScales L F.GK p (Real.exp (x^(eps/2))) := by
  let B := max 40 (max F.GK.DI F.GK.kappaThresholdTwo)
  have hU := (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (show 0 < eps/2 by positivity))).eventually_ge_atTop B
  have hX := AuxBlock8.Pf.ev_log 80 (eps/2) (by positivity)
  have hG := AuxBlock8.Pf.ev_log (AuxBlock8.Pf.cGE eps) (eps/24) (by positivity)
  filter_upwards [hU,hX,hG,family_typeI_basic_sizes F heps heps',typeI_prime_cutoff_scales F heps,
    eventually_ge_atTop (Real.exp 1),eventually_ge_atTop (2:ℝ)]
      with x hU hX hG hSize hWin hxexp hx₂
  intro hx i L Z p hp hlo hhi
  let D := F.D x i
  let U := Real.exp (x^(eps/2))
  have hx₁ : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hU₀ : 0 ≤ U := (Real.exp_pos _).le
  have hBig : 40 ≤ U := (le_max_left _ _).trans hU
  have hXp : x^(80:ℝ) ≤ U := AuxBlock8.Pf.xpow_le_exp _ _ _ hx0 hX
  have hPow (a : ℝ) (ha : a ≤ 80) : x^a ≤ U :=
    (Real.rpow_le_rpow_of_exponent_le hx₁ ha).trans hXp
  obtain ⟨hn,hμ,hk,hN⟩ := hSize hx i
  have hmU : (D.R.m:ℝ) ≤ U := hμ.trans (by simpa only [Real.rpow_one] using hPow 1 (by norm_num))
  have hnU : (D.R.n:ℝ) ≤ U := hn.trans (hPow 3 (by norm_num))
  have hkU : (D.R.k:ℝ) ≤ U := hk.trans (hPow 6 (by norm_num))
  have hNU : (N1 L.sc:ℝ) ≤ U := hN.trans (hPow (1/2) (by norm_num))
  have hdU : (addOrderOf (hP D p):ℝ) ≤ U := by
    have hd : addOrderOf (hP D p) ≤ D.R.n :=
      Nat.le_of_dvd D.R.ord_pos (D.R.addOrderOf_dvd_ord _)
    exact (Nat.cast_le.mpr hd).trans hnU
  have hScale : (L.sc.x^(Scale.A/2))^2 ≤ U := by
    rw [F.L_x x i hx,← Real.rpow_natCast,← Real.rpow_mul hx0.le]
    norm_num [Scale.A]
    <;> exact (Real.rpow_natCast x 26).ge.trans (hPow 26 (by norm_num))
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hplog : (1/2:ℝ) ≤ Real.log (p:ℝ) := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact (show (1/2:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans
      (Real.log_le_log (by norm_num) hp2)
  have hlogX : Real.log L.sc.X' = x^(eps/3) := by rw [Scale.X',F.L_x x i hx,F.L_eps x i,Real.log_exp]
  have hlogp : Real.log (p:ℝ) ≤ x^(eps/3) := by
    rw [← hlogX]
    exact Real.log_le_log hp₀ (hWin hx i p hp hlo hhi).2.2.le
  have hGp := AuxBlock8.Pf.Gp_le L.sc (by rw [F.L_x x i hx]; exact hxexp)
  rw [F.L_x x i hx,F.L_eps x i] at hGp
  have hHeight : (Gp L.sc:ℝ)*Real.log (p:ℝ) ≤ x^(eps/2) := by
    calc
      _ ≤ (x^(eps/24)*x^(eps/8))*x^(eps/3) := mul_le_mul
        (hGp.trans (mul_le_mul_of_nonneg_right hG (by positivity))) hlogp (by linarith) (by positivity)
      _ = _ := by rw [← Real.rpow_add hx0,← Real.rpow_add hx0]; congr 1; ring
  have hQ : Qp L.sc p ≤ U := by
    unfold Qp
    rw [← Real.exp_log hp₀,← Real.exp_natCast_mul]
    exact Real.exp_le_exp.mpr hHeight
  have hL : L.sc.L = x^eps := by rw [Scale.L,F.L_x x i hx,F.L_eps x i]
  have hlogA : Real.log L.sc.a ≤ 2*x := by
    rw [Scale.a,Scale.b,Real.log_mul L.sc.x_pos.ne' (Real.exp_pos _).ne',Real.log_exp,
      F.L_x x i hx,hL]
    have hLex : x^eps ≤ x := by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx₁ (show eps ≤ 1 by linarith only [heps'])
    linarith only [Real.log_le_sub_one_of_pos hx0,hLex]
  have hlogb : Real.logb p L.sc.a ≤ 4*x := by
    unfold Real.logb
    apply (div_le_iff₀ (by linarith : 0 < Real.log (p:ℝ))).mpr
    have hm := mul_le_mul_of_nonneg_left hplog (show 0 ≤ 4*x by positivity)
    linarith only [hlogA,hm]
  have hLog₂ : Real.logb p (2*L.sc.a) ≤ U := by
    refine ((AuxBlock8.Pf.logb_facts L.sc p hp).2.2.trans
      (mul_le_mul_of_nonneg_left hlogb (by norm_num))).trans ?_
    have hh : (2:ℝ)*(4*x) ≤ x^(4:ℝ) := by
      rw [show x^(4:ℝ) = x^(4:ℕ) from Real.rpow_natCast x 4]
      have h := pow_le_pow_left₀ (show 0 ≤ (2:ℝ) by norm_num) hx₂ 3
      have hh := mul_le_mul_of_nonneg_right h hx0.le
      norm_num at hh
      nlinarith only [hh]
    exact hh.trans (hPow 4 (by norm_num))
  have hLog₁ : Real.logb p L.sc.a ≤ U := by
    have ha := AuxBlock8.Pf.two_le_a L.sc
    exact (Real.logb_le_logb_of_le (by exact_mod_cast hp.one_lt) (by linarith : 0 < L.sc.a)
      (by linarith : L.sc.a ≤ 2*L.sc.a)).trans hLog₂
  obtain ⟨_,_,_,_,hST,_,_,_,_,_,_,_,_,hEta,_,_,hDel,_⟩ := F.sizes x hx i
  have hEta₀ : 0 < L.etaSz := lt_of_lt_of_le (zero_lt_one.trans_le hST.1) hEta.1
  have hEta' : Real.log L.etaSz ≤ x^(eps/2) := by
    have hh := hEta.2.2.1
    rw [F.L_x x i hx,F.L_eps x i] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith))
  have hEU : L.etaSz ≤ U := by
    rw [← Real.exp_log hEta₀]
    exact Real.exp_le_exp.mpr hEta'
  have hD₀ : 0 < (D.s.Del:ℝ) := by exact_mod_cast D.s.Del_pos
  have hD' : Real.log (D.s.Del:ℝ) ≤ x^(eps/2) := by
    have hh := hDel.2.2.1
    rw [F.L_x x i hx,F.L_eps x i] at hh
    exact (hh.trans (by have h := Real.rpow_nonneg hx0.le (eps/4); linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hx₁ (show eps/4 ≤ eps/2 by linarith))
  have hDU : (D.s.Del:ℝ) ≤ U := by
    rw [← Real.exp_log hD₀]
    exact Real.exp_le_exp.mpr hD'
  have hNm : Nm D ≤ U := by
    have hm : (1:ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by have h := D.R.two_le_m; omega)
    have hh : 1 ≤ (D.R.m:ℝ)^10 := one_le_pow₀ hm
    exact ((le_mul_of_one_le_right (Nat.cast_nonneg _) hh).trans hDel.1).trans hDU
  have hCG : cG L ≤ U^3 := by
    unfold cG
    rw [L.Sc_eq]
    calc
      _ = 16*(D.R.k:ℝ)*(D.s.Del:ℝ) := by ring
      _ ≤ U*U*U := mul_le_mul (mul_le_mul (by linarith) hkU (Nat.cast_nonneg _) hU₀)
        hDU hD₀.le (by positivity)
      _ = _ := by ring
  exact ⟨hBig,hmU,hnU,hkU,hdU,hNU,hLog₁,hLog₂,hScale,hQ,hEU,hNm,hCG,
    (le_max_left _ _).trans ((le_max_right _ _).trans hU),
    (le_max_right _ _).trans ((le_max_right _ _).trans hU)⟩

theorem native_cutoff_residual_upper {D : D7} {L : SizeData₂ D} (X : Inst D L)
    (K : Consts) (hK : K.Nonneg) (hEp : EpDef X 1) (p : ℕ) (hp : p.Prime)
    (U : ℝ) (hR : TypeIResidualScales L K p U) :
    let d := addOrderOf (hP D p)
    (X.ep p:ℝ)+1+(D.R.m:ℝ)*(D.R.n:ℝ)*
      (typeIRoundingCost L K p d + 2*(d:ℝ)*cG L + (DIf K L p d:ℝ)+2) ≤ U^24 := by
  intro d
  have hU₁ : 1 ≤ U := by linarith [hR.large]
  have hU₀ : 0 ≤ U := zero_le_one.trans hU₁
  have hPow {i j : ℕ} (h : i ≤ j) : U^i ≤ U^j := pow_le_pow_right₀ hU₁ h
  have hDI : 0 ≤ K.DI := hK.2.2.2.2.2.2.2.1
  have hK₂ : 0 ≤ K.kappaThresholdTwo := hK.2.2.2.2.2.2.2.2.2.1
  have hCG : 0 ≤ cG L := by
    unfold cG
    rw [L.Sc_eq]
    have hD : 0 ≤ (D.s.Del:ℝ) := by exact_mod_cast D.s.Del_pos.le
    positivity
  have hQ : 0 ≤ Qp L.sc p := by unfold Qp; positivity
  have hLog := (AuxBlock8.Pf.logb_facts L.sc p hp).1
  have hNPlus₀ : 0 ≤ NplusF L.sc d := by
    unfold NplusF Scale.delta1
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Real.rpow_nonneg L.sc.x_pos.le _)
  have hNPlus : NplusF L.sc d ≤ U^2 := by
    have hδ : L.sc.delta1 ≤ 1 := by
      unfold Scale.delta1
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le
        (show -(L.sc.eps/8) ≤ 0 by linarith [L.sc.eps_pos])
    unfold NplusF
    calc
      _ ≤ 40*(d:ℝ)*1 := mul_le_mul_of_nonneg_left hδ (by positivity)
      _ ≤ U*U := by rw [mul_one]; exact mul_le_mul hR.large hR.order (Nat.cast_nonneg _) hU₀
      _ = _ := by ring
  have hN5 : (N1 L.sc:ℝ)^5+(D.R.k:ℝ)^3 ≤ U^6 := by
    have hn := pow_le_pow_left₀ (Nat.cast_nonneg _) hR.count 5
    have hk := (pow_le_pow_left₀ (Nat.cast_nonneg _) hR.sizeK 3).trans (hPow (show 3≤5 by decide))
    have hm := mul_le_mul_of_nonneg_right (show 2≤U by linarith [hR.large]) (pow_nonneg hU₀ 5)
    nlinarith only [hn,hk,hm]
  let V := K.DI * NplusF L.sc d * (L.sc.x^(Scale.A/2))^2 *
    ((N1 L.sc:ℝ)^5+(D.R.k:ℝ)^3) * Real.logb p L.sc.a
  have hV₀ : 0 ≤ V := by unfold V; positivity
  have hV : V ≤ U^11 := by
    calc
      _ ≤ U*(U^2)*U*(U^6)*U := by
        unfold V
        gcongr
        all_goals first | exact hR.boundDI | exact hNPlus | exact hR.scaleA | exact hN5 | exact hR.loga | positivity
      _ = _ := by ring
  have hDIf : (DIf K L p d:ℝ) ≤ U^12 := by
    change (⌈V⌉₊:ℝ) ≤ _
    have hh := (Nat.ceil_lt_add_one hV₀).le
    have hU11 : 1 ≤ U^11 := one_le_pow₀ hU₁
    have hm := mul_le_mul_of_nonneg_right (show 2≤U by linarith [hR.large]) (pow_nonneg hU₀ 11)
    nlinarith only [hh,hV,hU11,hm]
  have h6 : c6f K L p d ≤ U^15 := by
    have h1 : 8*((DIf K L p d:ℝ)+1) ≤ U^14 := by
      have hD : (DIf K L p d:ℝ)+1 ≤ U^13 := by
        have hh := one_le_pow₀ (n:=12) hU₁
        have hm := mul_le_mul_of_nonneg_right (show 2≤U by linarith [hR.large]) (pow_nonneg hU₀ 12)
        nlinarith only [hDIf,hh,hm]
      calc
        _ ≤ U*U^13 := mul_le_mul (by linarith [hR.large]) hD (by positivity) hU₀
        _ = _ := by ring
    have h2 : K.kappaThresholdTwo*NplusF L.sc d*(D.R.k:ℝ)*Real.logb p L.sc.a ≤ U^14 := by
      refine le_trans ?_ (hPow (show 5≤14 by decide))
      calc
        _ ≤ U*U^2*U*U := mul_le_mul
          (mul_le_mul (mul_le_mul hR.boundKTwo hNPlus hNPlus₀ hU₀) hR.sizeK (Nat.cast_nonneg _) (by positivity))
          hR.loga hLog (by positivity)
        _ = _ := by ring
    have h3 : 4*NplusF L.sc d*cG L ≤ U^14 := by
      refine le_trans ?_ (hPow (show 6≤14 by decide))
      calc
        _ ≤ U*U^2*U^3 := mul_le_mul (mul_le_mul (by linarith [hR.large]) hNPlus hNPlus₀ hU₀)
          hR.cGUpper hCG (by positivity)
        _ = _ := by ring
    have h4 : 2*(d:ℝ)*cG L ≤ U^5 := by
      calc
        _ ≤ U*U*U^3 := mul_le_mul (mul_le_mul (by linarith [hR.large]) hR.order (Nat.cast_nonneg _) hU₀)
          hR.cGUpper hCG (by positivity)
        _ = _ := by ring
    have hh := h4.trans (hPow (show 5≤14 by decide))
    unfold c6f
    have hm := mul_le_mul_of_nonneg_right (show 4≤U by linarith [hR.large]) (pow_nonneg hU₀ 14)
    nlinarith only [h1,h2,h3,hh,hm]
  have h6₀ : 0 ≤ c6f K L p d := by unfold c6f; positivity
  have hRound : typeIRoundingCost L K p d ≤ U^18 := by
    have h1 : Qp L.sc p*c6f K L p d ≤ U^16 := by
      calc
        _ ≤ U*U^15 := mul_le_mul hR.conductorHeight h6 h6₀ hU₀
        _ = _ := by ring
    have h2 : (D.R.k:ℝ)*Qp L.sc p ≤ U^16 := by
      exact (mul_le_mul hR.sizeK hR.conductorHeight hQ hU₀).trans
        (by rw [← pow_two]; exact hPow (by decide))
    have h3 : (D.R.k:ℝ)*Real.logb p L.sc.a ≤ U^16 := by
      exact (mul_le_mul hR.sizeK hR.loga hLog hU₀).trans
        (by rw [← pow_two]; exact hPow (by decide))
    have h4 := hR.cGUpper.trans (hPow (show 3≤16 by decide))
    have hSum : Qp L.sc p*c6f K L p d+(D.R.k:ℝ)*Qp L.sc p+
        (D.R.k:ℝ)*Real.logb p L.sc.a+cG L ≤ U^17 := by
      have hm := mul_le_mul_of_nonneg_right (show 4≤U by linarith [hR.large]) (pow_nonneg hU₀ 16)
      nlinarith only [h1,h2,h3,h4,hm]
    unfold typeIRoundingCost
    calc
      _ ≤ U*U^17 := mul_le_mul hR.boundKTwo hSum (by positivity) hU₀
      _ = _ := by ring
  have hTail : typeIRoundingCost L K p d+2*(d:ℝ)*cG L+(DIf K L p d:ℝ)+2 ≤ U^19 := by
    have h2 : 2*(d:ℝ)*cG L ≤ U^18 := by
      refine le_trans ?_ (hPow (show 5≤18 by decide))
      calc
        _ ≤ U*U*U^3 := mul_le_mul (mul_le_mul (by linarith [hR.large]) hR.order (Nat.cast_nonneg _) hU₀)
          hR.cGUpper hCG (by positivity)
        _ = _ := by ring
    have h3 := hDIf.trans (hPow (show 12≤18 by decide))
    have h4 : (2:ℝ) ≤ U^18 := calc
      _ ≤ U := by linarith [hR.large]
      _ = U^1 := by rw [pow_one]
      _ ≤ _ := hPow (show 1≤18 by decide)
    have hm := mul_le_mul_of_nonneg_right (show 4≤U by linarith [hR.large]) (pow_nonneg hU₀ 18)
    nlinarith only [hRound,h2,h3,h4,hm]
  have hTail₀ : 0 ≤ typeIRoundingCost L K p d + 2*(d:ℝ)*cG L + (DIf K L p d:ℝ)+2 := by
    unfold typeIRoundingCost
    positivity
  have hMult : (D.R.m:ℝ)*(D.R.n:ℝ)*
      (typeIRoundingCost L K p d+2*(d:ℝ)*cG L+(DIf K L p d:ℝ)+2) ≤ U^21 := by
    calc
      _ ≤ U*U*U^19 := mul_le_mul (mul_le_mul hR.sizeM hR.sizeN (Nat.cast_nonneg _) hU₀)
        hTail hTail₀ (by positivity)
      _ = _ := by ring
  have hf : (D.R.f:ℝ) ≤ U^2 := by
    rw [Ranks.f,Nat.cast_mul,Nat.cast_ofNat,pow_two]
    exact mul_le_mul (by linarith [hR.large]) hR.sizeN (Nat.cast_nonneg _) hU₀
  have he := (hEp.lt p (by positivity)).le
  have hRaw : (1:ℝ)*(D.R.f:ℝ)*(D.R.k:ℝ)^2*Real.logb p L.sc.a ≤ U^5 := by
    rw [one_mul]
    calc
      _ ≤ U^2*U^2*U := mul_le_mul (mul_le_mul hf
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hR.sizeK 2) (by positivity) (by positivity)) hR.loga hLog (by positivity)
      _ = _ := by ring
  have hEpU : (X.ep p:ℝ)+1 ≤ U^21 := by
    refine le_trans ?_ (hPow (show 6≤21 by decide))
    have h1 := one_le_pow₀ (n:=5) hU₁
    have hm := mul_le_mul_of_nonneg_right (show 3≤U by linarith [hR.large]) (pow_nonneg hU₀ 5)
    linarith only [he,hRaw,h1,hm,show U*U^5=U^6 by ring]
  refine le_trans ?_ (hPow (show 22≤24 by decide))
  have hm := mul_le_mul_of_nonneg_right (show 2≤U by linarith [hR.large]) (pow_nonneg hU₀ 21)
  linarith only [hEpU,hMult,hm,show U*U^21=U^22 by ring]

theorem family_typeI_envelope_small {eps : ℝ} (F : FamP eps) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let L := F.L x i
      let Z := L.sc.X' ^ (3/4:ℝ)
      ∀ p : ℕ, p.Prime → Z < (p:ℝ) → (p:ℝ) < 2*Z →
        (Real.exp (x^(eps/2)))^24 ≤ (L.sc.a/(p:ℝ))/8 := by
  have hBig := AuxBlock8.Pf.ev_pow 64 (eps/2) eps (by linarith)
  filter_upwards [hBig,typeI_prime_cutoff_scales F heps,eventually_ge_atTop (1:ℝ)]
    with x hBig hWin hx₁
  intro hx i L Z p hp hlo hhi
  have hx₀ : 0 < x := zero_lt_one.trans_le hx₁
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hpX := (hWin hx i p hp hlo hhi).2.2
  have hW := Real.rpow_le_rpow_of_exponent_le hx₁ (show eps/3 ≤ eps/2 by linarith)
  have hOne : 1 ≤ x^(eps/2) := Real.one_le_rpow hx₁ (by positivity)
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
    linarith
  have hLog8 : Real.log 8 ≤ 3 := by
    rw [show (8:ℝ) = 2^3 by norm_num,Real.log_pow]
    norm_num
    linarith
  have hX : L.sc.X' = Real.exp (x^(eps/3)) := by rw [Scale.X',F.L_x x i hx,F.L_eps x i]
  have hA : L.sc.a = x*Real.exp (x^eps) := by rw [Scale.a,Scale.b,Scale.L,F.L_x x i hx,F.L_eps x i]
  have hB : (Real.exp (x^(eps/2)))^24*8*L.sc.X' ≤ L.sc.a := by
    calc
      _ = Real.exp ((24:ℝ)*x^(eps/2)+Real.log 8+x^(eps/3)) := by
        rw [hX,Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : 0<(8:ℝ))]
        rw [← Real.exp_natCast_mul]
        norm_num
      _ ≤ Real.exp (x^eps) := Real.exp_le_exp.mpr (by linarith only [hOne,hW,hLog8,hBig])
      _ ≤ _ := by
        rw [hA]
        exact le_mul_of_one_le_left (Real.exp_pos _).le hx₁
  apply (le_div_iff₀ (by norm_num : 0<(8:ℝ))).mpr
  apply (le_div_iff₀ hp₀).mpr
  exact (mul_le_mul_of_nonneg_left hpX.le (by positivity)).trans hB

theorem family_typeI_full_cutoff {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let L := F.L x i
      let X := F.Gx x i
      let Z := L.sc.X' ^ (3/4:ℝ)
      ∀ p : ℕ, p.Prime → IsResidueClassZero D p → Z < (p:ℝ) → (p:ℝ) < 2*Z →
        L.sc.p0 D.R.k ≤ (p:ℝ) → VV X F.GK (aL L) (bL L) p ≠ ∅ →
        ((⌈tauP X F.GK (aL L) (bL L) p⌉.toNat:ℕ):ℝ)+1 ≤ (L.sc.a/(p:ℝ))/4 := by
  filter_upwards [family_typeI_leading_small F heps heps',
    family_typeI_residual_scales F heps heps',family_typeI_envelope_small F heps]
    with x hLead hR hEnv
  intro hx i D L X Z p hp hI hlo hhi hType hVV
  have hCut := native_cutoff_upper (F.sizes x hx i) X F.GK F.GK_nonneg p hp hI hType hVV
  have hEp : EpDef X 1 := by
    simpa only [F.fixed.2.2.2.1] using (F.ex x hx i).ep_def
  let U := Real.exp (x^(eps/2))
  have hRes := native_cutoff_residual_upper X F.GK F.GK_nonneg hEp p hp U (hR hx i p hp hlo hhi)
  have hSmall := hEnv hx i p hp hlo hhi
  have hLead' := hLead hx i p hp hlo hhi
  dsimp only at hCut hRes
  have hAP : 0 ≤ L.sc.a/(p:ℝ) := div_nonneg L.sc.a_pos.le (Nat.cast_nonneg _)
  linarith only [hCut,hRes,hSmall,hLead',hAP]

theorem native_omission_residual_upper {D : D7} {L : SizeData₂ D} (X : Inst D L)
    (K : Consts) (p : ℕ) (hp : p.Prime) (hI : IsResidueClassZero D p)
    (hPr1 : K.Pr1 = 1) (hDl1 : K.dl1 = 5) (hDl2 : K.dl2 = 4)
    (U : ℝ) (hR : TypeIResidualScales L K p U) (t₀ : G.HH D) (hEta : 0 ≤ L.etaSz) :
    L.etaSz+cG L + (Nv X p t₀:ℝ)*L.etaSz +
      K.Pr1*(addOrderOf (hP D p):ℝ)*(L.etaSz+cG L+Nm D) + dl X K p t₀ ≤ U^24 := by
  let d := (addOrderOf (hP D p):ℝ)
  let N := (Nv X p t₀:ℝ)
  have hU₁ : 1 ≤ U := by linarith [hR.large]
  have hU₀ : 0 ≤ U := zero_le_one.trans hU₁
  have hPow {i j : ℕ} (h : i ≤ j) : U^i ≤ U^j := pow_le_pow_right₀ hU₁ h
  have hCG : 0 ≤ cG L := by
    unfold cG
    rw [L.Sc_eq]
    have hD : 0 ≤ (D.s.Del:ℝ) := by exact_mod_cast D.s.Del_pos.le
    positivity
  have hNm : 0 ≤ Nm D := Nat.cast_nonneg _
  have hNV : N ≤ U := by
    have hN' : Nv X p t₀ ≤ D.R.n := by
      unfold Nv
      exact (Finset.card_le_univ _).trans_eq D.R.card_A
    exact (Nat.cast_le.mpr hN').trans hR.sizeN
  have hLog := (AuxBlock8.Pf.logb_facts L.sc p hp).2.1
  have hD : dl X K p t₀ ≤ U^6 := by
    unfold dl
    rw [hDl1,hDl2,AuxBlock8.Pf.St.partner_count_of_central hI]
    have h1 : 5*d*Nm D^2*Real.logb p (2*L.sc.a) ≤ U^5 := by
      calc
        _ ≤ U*U*U^2*U := by
          gcongr
          all_goals first | exact hR.order | exact hR.nm | exact hR.loga2 | linarith [hR.large] | positivity
        _ = _ := by ring
    have h2 : 4*N*Real.logb p (2*L.sc.a)^2 ≤ U^5 := by
      refine le_trans ?_ (hPow (show 4≤5 by decide))
      calc
        _ ≤ U*U*U^2 := by
          gcongr
          all_goals first | exact hNV | exact hR.loga2 | linarith [hR.large] | positivity
        _ = _ := by ring
    have hh := mul_le_mul_of_nonneg_right (show 2≤U by linarith [hR.large]) (pow_nonneg hU₀ 5)
    change 5*d*Nm D^2*Real.logb p (2*L.sc.a) + 4*N*Real.logb p (2*L.sc.a)^2 ≤ _
    nlinarith only [h1,h2,hh]
  have hE : L.etaSz ≤ U^6 := hR.eta.trans (by
    calc U = U^1 := by rw [pow_one]
         _ ≤ U^6 := hPow (show 1≤6 by decide))
  have hCGU : cG L ≤ U^6 := hR.cGUpper.trans (hPow (show 3≤6 by decide))
  have hNVU : N*L.etaSz ≤ U^6 := (mul_le_mul hNV hR.eta hEta hU₀).trans (by
    rw [← pow_two]
    exact hPow (show 2≤6 by decide))
  have hPr : K.Pr1*d*(L.etaSz+cG L+Nm D) ≤ U^6 := by
    rw [hPr1,one_mul]
    have hA : L.etaSz+cG L+Nm D ≤ U^4 := by
      have h1 := hR.eta.trans (by calc U = U^1 := by rw [pow_one]
                                     _ ≤ U^3 := hPow (show 1≤3 by decide))
      have h2 := hR.nm.trans (by calc U = U^1 := by rw [pow_one]
                                    _ ≤ U^3 := hPow (show 1≤3 by decide))
      have h3 := mul_le_mul_of_nonneg_right (show 3≤U by linarith [hR.large]) (pow_nonneg hU₀ 3)
      nlinarith only [h1,h2,hR.cGUpper,h3]
    calc
      _ ≤ U*U^4 := mul_le_mul hR.order hA (by positivity) hU₀
      _ = U^5 := by ring
      _ ≤ _ := hPow (show 5≤6 by decide)
  refine le_trans ?_ (hPow (show 7≤24 by decide))
  have hM := mul_le_mul_of_nonneg_right (show 5≤U by linarith [hR.large]) (pow_nonneg hU₀ 6)
  change L.etaSz+cG L+N*L.etaSz+K.Pr1*d*(L.etaSz+cG L+Nm D)+dl X K p t₀ ≤ _
  nlinarith only [hE,hCGU,hNVU,hPr,hD,hM]

theorem family_typeI_omission_margin {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let L := F.L x i
      let X := F.Gx x i
      let Z := L.sc.X' ^ (3/4:ℝ)
      ∀ (p : ℕ), p.Prime → IsResidueClassZero D p → Z < (p:ℝ) → (p:ℝ) < 2*Z →
        L.sc.p0 D.R.k ≤ (p:ℝ) → ∀ (t₀ t : G.HH D), t+hP D p ∈ D.host.TT →
        cG L ≤ L.sc.a/8 ∧
          capU X (bL L) p 1 t 1 + dl X F.GK p t₀ + Pr X F.GK (bL L) p 1 t₀ ≤ (L.sc.a/(p:ℝ))/4 := by
  have hE := exp_neg_rpow_eventually_le_rpow (1/4) (eps/3) 9 (by norm_num) (by positivity)
  have hSmall := AuxBlock8.Pf.ev_pow 80 (-6) 0 (by norm_num)
  filter_upwards [family_typeI_basic_sizes F heps heps',typeI_prime_cutoff_scales F heps,
    family_typeI_residual_scales F heps heps',family_typeI_envelope_small F heps,
    hE,hSmall,eventually_ge_atTop (1:ℝ)]
    with x hSize hWin hR hEnv hE hSmall hx₁
  intro hx i D L X Z p hp hI hlo hhi hType t₀ t ht
  let U := Real.exp (x^(eps/2))
  let n := (D.R.n:ℝ)
  let d := (addOrderOf (hP D p):ℝ)
  let N := (Nv X p t₀:ℝ)
  have hx₀ := zero_lt_one.trans_le hx₁
  have hAP := div_pos L.sc.a_pos (show 0 < (p:ℝ) by exact_mod_cast hp.pos)
  have hp₁ : 1 ≤ (p:ℝ) := by exact_mod_cast hp.one_lt.le
  have hK := F.fixed
  have hP1 : F.GK.Pr1 = 1 := hK.1
  have hD1 : F.GK.dl1 = 5 := hK.2.1
  have hD2 : F.GK.dl2 = 4 := hK.2.2.1
  have hS := F.sizes x hx i
  obtain ⟨_,_,_,_,hST,_,_,_,_,_,_,_,_,hEta,_,_⟩ := F.sizes x hx i
  have hEta₀ : 0 ≤ L.etaSz := (zero_le_one.trans hST.1).trans hEta.1
  have hj : (1:ℕ) ∈ SizeData₂.lifts D := by
    unfold SizeData₂.lifts
    exact Finset.mem_Icc.mpr ⟨le_rfl,(show 1≤2 by decide).trans D.R.two_le_m⟩
  have hCap := native_first_cap_upper hS X p 1 hI hj t ht
  have hPr := native_first_penalty_upper X F.GK p 1 hI hType hj t₀ hEta₀
  have hRs := hR hx i p hp hlo hhi
  have hRes := native_omission_residual_upper X F.GK p hp hI hP1 hD1 hD2 U hRs t₀ hEta₀
  have hSmallU := hEnv hx i p hp hlo hhi
  have hcG : cG L ≤ L.sc.a/8 := by
    have hU₁ : 1 ≤ U := by linarith [hRs.large]
    exact (hRs.cGUpper.trans (pow_le_pow_right₀ hU₁ (show 3≤24 by decide))).trans
      (hSmallU.trans (div_le_div_of_nonneg_right (div_le_self L.sc.a_pos.le hp₁) (by norm_num)))
  refine ⟨hcG,?_⟩
  have hn := (hSize hx i).1
  have hd : d ≤ n := by
    change (addOrderOf (hP D p):ℝ) ≤ (D.R.n:ℝ)
    exact_mod_cast Nat.le_of_dvd D.R.ord_pos (D.R.addOrderOf_dvd_ord _)
  have hN : N ≤ n := by
    change (Nv X p t₀:ℝ) ≤ (D.R.n:ℝ)
    exact_mod_cast (show Nv X p t₀ ≤ D.R.n from (Finset.card_le_univ _).trans_eq D.R.card_A)
  have hW : L.sc.w'' D.R.n ≤ L.sc.b' := L.sc.w''_le_b' _ D.R.one_le_n
  have hBX : L.sc.b'/L.sc.x ≤ L.sc.b' := div_le_self L.sc.b'_pos.le L.sc.one_lt_alt.le
  have hLeading : 2*L.sc.b'+L.sc.b'/L.sc.x + N*(L.sc.b'/L.sc.x)+d*L.sc.w'' D.R.n ≤
      5*x^(3:ℝ)*L.sc.b' := by
    have hN' := mul_le_mul hN hBX (div_nonneg L.sc.b'_pos.le L.sc.x_pos.le) (Nat.cast_nonneg _)
    have hW₀ : 0 ≤ L.sc.w'' D.R.n :=
      div_nonneg L.sc.b'_pos.le (mul_nonneg L.sc.x_pos.le (Nat.cast_nonneg _))
    have hd' := mul_le_mul hd hW hW₀ (Nat.cast_nonneg _)
    have hZ := mul_le_mul_of_nonneg_right hn L.sc.b'_pos.le
    have hx3 := Real.one_le_rpow hx₁ (by norm_num : (0:ℝ)≤3)
    have hx3' := mul_le_mul_of_nonneg_right hx3 L.sc.b'_pos.le
    nlinarith only [hN',hd',hZ,hBX,hx3']
  have hWin' := (hWin hx i p hp hlo hhi).1
  have hLead : 5*x^(3:ℝ)*L.sc.b' ≤ (L.sc.a/(p:ℝ))/8 := by
    have hBound : 5*x^(3:ℝ)*((p:ℝ)/L.sc.X') ≤ 1/8 := by
      calc
        _ ≤ 5*x^(3:ℝ)*(2*x^(-9:ℝ)) := mul_le_mul_of_nonneg_left
          (hWin'.trans (mul_le_mul_of_nonneg_left hE (by norm_num))) (by positivity)
        _ = 10*x^(-6:ℝ) := by
          calc
            _ = 10*(x^(3:ℝ)*x^(-9:ℝ)) := by ring
            _ = _ := by rw [← Real.rpow_add hx₀]; norm_num
        _ ≤ _ := by rw [Real.rpow_zero] at hSmall; linarith only [hSmall]
    have hEq : 5*x^(3:ℝ)*L.sc.b' = (L.sc.a/(p:ℝ))*(5*x^(3:ℝ)*((p:ℝ)/L.sc.X')) := by
      unfold Scale.b'
      have hp0 : (p:ℝ) ≠ 0 := by positivity
      field_simp [hp0]
    rw [hEq,div_eq_mul_one_div (L.sc.a/(p:ℝ))]
    exact mul_le_mul_of_nonneg_left hBound hAP.le
  rw [hP1,one_mul] at hPr hRes
  change Pr X F.GK (bL L) p 1 t₀ ≤
    N*(L.sc.b'/L.sc.x+L.etaSz)+d*(L.sc.w'' D.R.n+L.etaSz+cG L+Nm D) at hPr
  change L.etaSz+cG L+N*L.etaSz+d*(L.etaSz+cG L+Nm D)+dl X F.GK p t₀ ≤ U^24 at hRes
  nlinarith only [hCap,hPr,hRes,hSmallU,hLeading,hLead]

theorem family_typeI_depth_at_pair {eps : ℝ} (F : FamP eps)
    (heps : 0 < eps) (heps' : eps < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : F.x1 < x) (i : F.Ix x),
      let D := F.D x i
      let L := F.L x i
      let X := F.Gx x i
      let Z := L.sc.X' ^ (3/4:ℝ)
      ∀ (p : ℕ), p.Prime → IsResidueClassZero D p → Z < (p:ℝ) → (p:ℝ) < 2*Z →
        L.sc.p0 D.R.k ≤ (p:ℝ) →
        ∀ (t₀ t : G.HH D), t₀ ∈ VV X F.GK (aL L) (bL L) p →
          t ∈ topsOn X p t₀ → t+hP D p ∈ D.host.TT → hP D p ≠ 0 →
          let T := ⌈tauP X F.GK (aL L) (bL L) p⌉.toNat
          ((T+1:ℕ):ℝ) ≤ (L.sc.a/(p:ℝ))/4 ∧ cG L ≤ L.sc.a/8 ∧
            T+1 ≤ ⌈Sv X F.GK (aL L) (bL L) p t₀⌉.toNat := by
  filter_upwards [family_typeI_full_cutoff F heps heps',family_typeI_omission_margin F heps heps']
    with x hCut hOm
  intro hx i D L X Z p hp hI hlo hhi hType t₀ t ht₀ ht ht' hstep T
  have hR : ((T+1:ℕ):ℝ) ≤ (L.sc.a/(p:ℝ))/4 := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      hCut hx i p hp hI hlo hhi hType (Finset.ne_empty_of_mem ht₀)
  obtain ⟨hcG,hMargin⟩ := hOm hx i p hp hI hlo hhi hType t₀ t ht'
  refine ⟨hR,hcG,?_⟩
  have hp₀ : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hA : L.sc.a ≤ (aL L t:ℝ) :=
    (AuxBlock8.Pf.a_bounds (F.params x hx i) (aL L) (bL L)
      (AuxBlock8.Pf.inWin_sizeData L) t (AuxBlock8.Pf.mem_TT_of_topsOn X p t₀ t ht)).1
  have hPos : 0 ≤ L.sc.a/(p:ℝ) := div_nonneg L.sc.a_pos.le hp₀.le
  have hAl : (3/4)*(L.sc.a/(p:ℝ)) ≤ al L (aL L) t/(p:ℝ) := by
    have hA' := div_le_div_of_nonneg_right hA hp₀.le
    have hG : cG L/(p:ℝ) ≤ (L.sc.a/(p:ℝ))/8 :=
      (div_le_div_of_nonneg_right hcG hp₀.le).trans_eq (by ring)
    unfold al
    rw [sub_div,mul_div_assoc]
    linarith only [hG,hA']
  have hj : (1:ℕ) ∈ SizeData₂.lifts D := by
    unfold SizeData₂.lifts
    exact Finset.mem_Icc.mpr ⟨le_rfl,(show 1≤2 by decide).trans D.R.two_le_m⟩
  apply omission_ceiling_of_inert_adjacent (F.params x hx i) X F.GK F.GK_nonneg p 1 hp hI hj t₀ t ht ht' hstep
  linarith only [hR,hMargin,hAl,hPos]

open Classical in
theorem native_adjacent_capacity_of_depth {D : D7} {L : SizeData₂ D} {Gt : GatTies D}
    (P : ParameterChoice' D L) (X : Inst D L) (Y : LatInst D) (hTie : LatTied Gt X Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t₀ : G.HH D) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let v := Y.vOf u w hg t₀
    (t₀ ∈ reps X p) → Even (addOrderOf (hP D p)) →
    ∀ (s : Fin (G.P.n' v)) (R : ℕ),
      s ∈ (Y.Fl u w hg).TT v → posAdd s 1 ∈ (Y.Fl u w hg).TT v →
      (R:ℝ) ≤ (L.sc.a/(p:ℝ))/4 → cG L ≤ L.sc.a/8 →
      TypeIAdjacentCapacity G v s R := by
  intro p G v hRep hEven s R hs hs' hR hCG
  let Fl := Y.Fl u w hg
  have hPrime : p.Prime := D.what₂.places.resChar_prime w
  have hp : 0 < (p:ℝ) := by exact_mod_cast hPrime.pos
  have hm : 2 ≤ G.P.m := by
    have h := Gt.gat_k u w hg
    change G.P.m+1 = D.R.k at h
    have hk := D.R.five_le_k
    omega
  obtain ⟨_,_,hC,_,_,_,hTie'⟩ := hTie u w hg
  obtain ⟨hN,hSlots⟩ := hTie' t₀ hRep
  change G.P.n' v = addOrderOf (hP D p) at hN
  have hEvenN : Even (G.P.n' v) := hN ▸ hEven
  have hParity : IsTypeV (posAdd s 1) ↔ ¬ IsTypeV s := by
    change Even ((s.val+1)%(G.P.n' v)) ↔ ¬ Even s.val
    have hh : Even (G.P.n' v * ((s.val+1)/(G.P.n' v))) := hEvenN.mul_right _
    have hMod := Nat.mod_add_div (s.val+1) (G.P.n' v)
    have hEq : Even (s.val+1) ↔ Even ((s.val+1)%(G.P.n' v)) := by
      calc
        _ ↔ Even (((s.val+1)%(G.P.n' v)) + (G.P.n' v)*((s.val+1)/(G.P.n' v))) :=
          Iff.of_eq (congrArg Even hMod).symm
        _ ↔ _ := by rw [Nat.even_add]; simp only [hh, iff_true]
    exact hEq.symm.trans Nat.even_add_one
  have hRP : ((p*R:ℕ):ℝ) ≤ L.sc.a/4 := by
    have h := (le_div_iff₀ hp).mp ((le_div_iff₀ (by norm_num : (0:ℝ)<4)).mp hR)
    push_cast
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    linarith only [h]
  have hRcast : R ≤ p*R := by
    simpa only [one_mul] using Nat.mul_le_mul_right R hPrime.one_lt.le
  have hMarked (j : Fin (G.P.n' v)) (hj : j ∈ Fl.TT v) :
      p*R ≤ if IsTypeV j then typeIFirstMultiplicity G v j else typeILastProperMultiplicity G v j := by
    let t := t₀ + j.val • hP D p
    have ht : t ∈ D.host.TT := (hSlots j).2.1.mp hj
    have hA : L.sc.a ≤ (Fl.a v j:ℝ) := by
      rw [(hSlots j).2.2.1 hj |>.1]
      exact (AuxBlock8.Pf.a_bounds P (aL L) (bL L) (AuxBlock8.Pf.inWin_sizeData L) t ht).1
    have hc : (Fl.c:ℝ) ≤ cG L := hC
    have hh : ((p*R:ℕ):ℤ) ≤ Fl.a v j - (Fl.c:ℤ) := by
      have hh : ((p*R:ℕ):ℝ) ≤ (Fl.a v j:ℝ) - (Fl.c:ℝ) := by
        linarith only [hRP,hA,hc,hCG,L.sc.a_pos.le]
      exact_mod_cast hh
    exact native_top_marked_capacity Fl v j hj hm (p*R) hh
  have h1 := hMarked s hs
  have h2 := hRcast.trans (hMarked (posAdd s 1) hs')
  unfold TypeIAdjacentCapacity
  by_cases h : IsTypeV s
  · have hh : ¬ IsTypeV (posAdd s 1) := fun h' => (hParity.mp h') h
    simp only [ite_eq_left h,ite_eq_right hh] at h1 h2 ⊢
    exact ⟨h1,h2⟩
  · have hh : IsTypeV (posAdd s 1) := hParity.mpr h
    simp only [ite_eq_right h,ite_eq_left hh] at h1 h2 ⊢
    exact ⟨h1,h2⟩

end

end GlobalTheory.EX.TypeIProduction
