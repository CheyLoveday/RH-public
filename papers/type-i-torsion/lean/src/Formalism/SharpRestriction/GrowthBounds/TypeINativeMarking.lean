import Formalism.GradedWeylDivisibility.TypeIUnitLetter

open scoped BigOperators Classical
open Formalism.MainNotions.G
open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

abbrev NativeMinorLabel {p : ℕ} (G : GAtP p) := Σ slot : NativeFlagSlot G, FlagCopies (NativeFlagWeight G slot)

theorem adjacent_native_slots_ne {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    s ≠ posAdd s 1 := by
  intro h
  have e := congrArg Fin.val h
  change s.val = (s.val+1) % G.P.n' v at e
  have htwo := (G.P.setting v).two_le
  by_cases hlt : s.val + 1 < G.P.n' v
  · rw [Nat.mod_eq_of_lt hlt] at e
    omega
  · have hEq : s.val+1 = G.P.n' v := by have := s.isLt; omega
    rw [hEq, Nat.mod_self] at e
    omega

/-- The native capacity guards allocate the repeated factors before any
predecessor or word is chosen. The heights record the two source orientations. -/
theorem choose_marked_native_heights {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) (R : ℕ) (hm : 0 < G.P.m) (hc : TypeIAdjacentCapacity G v s R) :
    let s₀ : NativeFlagSlot G := ⟨v,s⟩
    let s₁ : NativeFlagSlot G := ⟨v,posAdd s 1⟩
    ∃ e : ((Fin p × Fin R) ⊕ Fin R) ↪ NativeMinorLabel G,
      (∀ b, (e (.inl b)).1 = s₀) ∧ (∀ b, (e (.inr b)).1 = s₁) ∧
      (∀ b, (e (.inl b)).2.1.val+1 = if IsTypeV s then 1 else G.P.m) ∧
      (∀ b, (e (.inr b)).2.1.val+1 = if IsTypeV s then G.P.m else 1) := by
  classical
  intro s₀ s₁
  have hne : s₀ ≠ s₁ := by
    intro h
    have heq : s = posAdd s 1 := eq_of_heq (Sigma.mk.inj h).2
    exact adjacent_native_slots_ne G v s heq
  let hL : Fin (G.P.m+1) := ⟨G.P.m-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  by_cases hs : IsTypeV s
  · have hcap₀ :
        p*R ≤ NativeFlagWeight G s₀ 0 - nuNext (NativeFlagWeight G s₀) 0 :=
      (show p*R ≤ typeIFirstMultiplicity G v s ∧
          R ≤ typeILastProperMultiplicity G v (posAdd s 1) by
        simpa only [TypeIAdjacentCapacity, ite_eq_left hs] using hc).1
    have hcap₁ :
        R ≤ NativeFlagWeight G s₁ hL - nuNext (NativeFlagWeight G s₁) hL :=
      (show p*R ≤ typeIFirstMultiplicity G v s ∧
          R ≤ typeILastProperMultiplicity G v (posAdd s 1) by
        simpa only [TypeIAdjacentCapacity, ite_eq_left hs] using hc).2
    obtain ⟨e,h₀,ha,h₁,hb⟩ := choose_disjoint_marked_labels
      (NativeFlagWeight G) s₀ s₁ hne 0 hL p R hcap₀ hcap₁
    refine ⟨e,h₀,h₁,?_,?_⟩
    · intro b
      rw [ha b, ite_eq_left hs, Fin.val_zero, zero_add]
    · intro b
      rw [hb b, ite_eq_left hs]
      change G.P.m-1+1 = G.P.m
      omega
  · have hcap :
        p*R ≤ typeILastProperMultiplicity G v s ∧
          R ≤ typeIFirstMultiplicity G v (posAdd s 1) := by
      simpa only [TypeIAdjacentCapacity, ite_eq_right hs] using hc
    obtain ⟨e,h₀,ha,h₁,hb⟩ := choose_disjoint_marked_labels
      (NativeFlagWeight G) s₀ s₁ hne hL 0 p R hcap.1 hcap.2
    refine ⟨e,h₀,h₁,?_,?_⟩
    · intro b
      rw [ha b, ite_eq_right hs]
      change G.P.m-1+1 = G.P.m
      omega
    · intro b
      rw [hb b, ite_eq_right hs, Fin.val_zero, zero_add]

/-- Assemble one dependent choice of row labels, with prescribed entries at
each marked position and the unmarked entries retained. -/
theorem label_choices_at_marks {α β γ : Type*} {I : β → Type*} (e : α ↪ β)
    (marked : γ → ∀ a, I (e a)) (defaultLabel : ∀ b, I b) :
    ∃ choice : γ → ∀ b, I b,
      (∀ c a, choice c (e a) = marked c a) ∧
      ∀ c b, b ∉ Set.range e → choice c b = defaultLabel b := by
  classical
  let choice (c : γ) (b : β) : I b :=
    if h : b ∈ Set.range e then
      (Classical.choose_spec h) ▸ marked c (Classical.choose h)
    else defaultLabel b
  refine ⟨choice,?_,?_⟩
  · intro c a
    let ha : e a ∈ Set.range e := ⟨a,rfl⟩
    change choice c (e a) = _
    unfold choice
    rw [dite_eq_left ha]
    have transport_eq (x y : α) (he : e x = e y) :
        he ▸ marked c x = marked c y := by
      have he' := e.injective he
      subst y
      rfl
    exact transport_eq _ _ (Classical.choose_spec ha)
  · intro c b h
    simp only [choice, dite_eq_right h]

/-- A coefficient in each independent word block is a single linear readout.
Rational-prime divisibility transfers from the full packed sum before any
coefficient is extracted. -/
theorem marked_normalized_word_coeff_dvd
    {ι τ W : Type*} [Fintype ι] [Fintype τ] [CommRing W]
    (σ : ι → Type*) (p : W) (R : ℕ) (l : τ → ℤ)
    (F : (i : ι) → τ → MvPolynomial (σ i) W) (exponent : ∀ i, σ i →₀ ℕ)
    (hpol : (C p)^R ∣
      ∑ I : τ, (l I : W) • packFlagBlocks (fun i => F i I)) :
    p^R ∣ ∑ I : τ, (l I : W) * ∏ i, (F i I).coeff (exponent i) := by
  let ψ (i : ι) := MvPolynomial.lcoeff W (exponent i)
  obtain ⟨Ψ,hΨ⟩ := exists_linear_specialization_on_flag_blocks ψ
  obtain ⟨q,hq⟩ := hpol
  refine ⟨Ψ q,?_⟩
  have hread := congrArg Ψ hq
  rw [← map_pow C, ← MvPolynomial.algebraMap_eq, ← Algebra.smul_def,
    map_smul,smul_eq_mul] at hread
  simpa only [map_sum, map_smul, smul_eq_mul, hΨ, ψ, MvPolynomial.lcoeff_apply] using hread

end

end GlobalTheory.EX.TypeIProduction
