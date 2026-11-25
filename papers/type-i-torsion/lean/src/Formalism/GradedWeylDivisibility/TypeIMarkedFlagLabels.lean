import Formalism.GradedWeylDivisibility.TypeIBlockFlag
import Formalism.SharpRestriction.GrowthBounds.TypeIAdjacentContractions

open scoped BigOperators Matrix Classical
open Matrix
open GlobalTheory.EX.TypeIProduction

namespace Formalism.GradedWeylDivisibility.TypeI

noncomputable section

/-- Allocate the marked positions directly in the actual height-copy index.
The two chosen slots are fixed before making the allocation. -/
theorem choose_disjoint_marked_labels {ι : Type*} {n : ℕ} (ν : ι → Fin n → ℕ)
    (s t : ι) (hst : s ≠ t) (a b : Fin n) (p R : ℕ)
    (hs : p * R ≤ ν s a - nuNext (ν s) a) (ht : R ≤ ν t b - nuNext (ν t) b) :
    ∃ e : ((Fin p × Fin R) ⊕ Fin R) ↪ (Σ i, FlagCopies (ν i)),
      (∀ m, (e (.inl m)).1 = s) ∧
      (∀ m, ((e (.inl m)).2).1 = a) ∧
      (∀ m, (e (.inr m)).1 = t) ∧
      (∀ m, ((e (.inr m)).2).1 = b) := by
  let f : Fin p × Fin R → Σ i, FlagCopies (ν i) :=
    fun m => ⟨s,⟨a,Fin.castLE hs (finProdFinEquiv m)⟩⟩
  let g : Fin R → Σ i, FlagCopies (ν i) :=
    fun m => ⟨t,⟨b,Fin.castLE ht m⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply finProdFinEquiv.injective
    apply (Fin.castLE_injective hs)
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hg : Function.Injective g := by
    intro x y h
    apply (Fin.castLE_injective ht)
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hd : ∀ x y, f x ≠ g y := fun x y h => hst (congrArg Sigma.fst h)
  exact ⟨⟨Sum.elim f g, hf.sumElim hg hd⟩,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

/-- The weight depends solely on the selected labels and their integer signs. -/
def labelWeight {β γ : Type*} [Fintype β] [Fintype γ] {I : β → Type*}
    (choose : γ → ∀ b, I b) (sgn : γ → β → ℤ) (a : ∀ b, I b) : ℤ :=
  ∑ c, if a = choose c then ∏ b, sgn c b else 0

/-- This identity remains valid even when two choices yield the same complete
labelling. It translates the rational coefficient row to the contraction sum. -/
theorem sum_integer_weight_on_labelled_products
    {β γ : Type*} [Fintype β] [Fintype γ] {I : β → Type*} [∀ b, Fintype (I b)]
    {K : Type*} [CommRing K] (choose : γ → ∀ b, I b) (sgn : γ → β → ℤ)
    (F : ∀ b, I b → K) :
    (∑ a : ∀ b, I b, (labelWeight choose sgn a : K) * ∏ b, F b (a b)) =
      ∑ c, ∏ b, (sgn c b : K) * F b (choose c b) := by
  classical
  unfold labelWeight
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_eq_single (choose c)]
  · simp only [ite_true, Finset.prod_mul_distrib]
  · intro a ha
    simp only [ha, ite_false, zero_mul]

/-- Reusing the same flag in each of the p marked copies makes every one of
the R groups one factor of the same contraction. -/
theorem marked_groups_product_eq_power {ι K : Type*} [Fintype ι] [CommSemiring K]
    (p R : ℕ) (x y : ι → K) :
    (∑ a : Fin R → ι, ∏ r, (∏ _ : Fin p, x (a r)) * y (a r)) =
      powerPair p x y ^ R := by
  simp only [powerPair, dotProduct, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.sum_pow]

/-- A disjoint allocation turns the complete labelled sum into the contraction
power times the untouched factors. The two input functions can be the two
parities of the native line and cofactor pair. -/
theorem allocated_label_sum_eq_contraction_pow
    {β ι K : Type*} [Fintype β] [Fintype ι] [CommRing K]
    {I : β → Type*} [∀ b, Fintype (I b)] (p R : ℕ)
    (e : ((Fin p × Fin R) ⊕ Fin R) ↪ β)
    (choose : (Fin R → ι) → ∀ b, I b) (sgn : (Fin R → ι) → β → ℤ)
    (F : ∀ b, I b → K) (x y : ι → K) (unused : β → K)
    (hleft : ∀ a q, (sgn a (e (.inl q)) : K) * F (e (.inl q)) (choose a (e (.inl q))) = x (a q.2))
    (hright : ∀ a q, (sgn a (e (.inr q)) : K) * F (e (.inr q)) (choose a (e (.inr q))) = y (a q))
    (hrest : ∀ a b, b ∉ Set.range e →
      (sgn a b : K) * F b (choose a b) = unused b) :
    (∑ a : ∀ b, I b, (labelWeight choose sgn a : K) * ∏ b, F b (a b)) =
      powerPair p x y ^ R * ∏ b ∈ (Finset.univ.map e)ᶜ, unused b := by
  classical
  rw [sum_integer_weight_on_labelled_products, ← marked_groups_product_eq_power, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  let H (b : β) := (sgn a b : K) * F b (choose a b)
  change (∏ b, H b) = _
  rw [← Finset.prod_mul_prod_compl (Finset.univ.map e) H, Finset.prod_map]
  congr 1
  · rw [Fintype.prod_sum_type]
    simp only [Function.comp_apply, H, hleft, hright]
    rw [← Finset.univ_product_univ, Finset.prod_product_right, ← Finset.prod_mul_distrib]
  · apply Finset.prod_congr rfl
    intro b hb
    apply hrest
    rintro ⟨a, rfl⟩
    exact (Finset.mem_compl.mp hb) (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩)

end

end Formalism.GradedWeylDivisibility.TypeI
