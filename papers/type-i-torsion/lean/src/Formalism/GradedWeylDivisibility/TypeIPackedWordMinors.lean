import Formalism.GradedWeylDivisibility.TypeIUnitLetter
import Mathlib.LinearAlgebra.Matrix.Transvection

open scoped BigOperators Matrix Classical
open Matrix MvPolynomial

namespace Formalism.GradedWeylDivisibility.TypeI

noncomputable section

/-- The independent slot embeddings commute with the complete minor product.
The copies inside a slot retain their common word variables. -/
theorem packFlagBlocks_sigma_prod {ι : Type*} [Fintype ι] {β σ : ι → Type*}
    [∀ i, Fintype (β i)] {K : Type*} [CommRing K]
    (P : ∀ i, β i → MvPolynomial (σ i) K) :
    packFlagBlocks (fun i => ∏ b, P i b) =
      ∏ b : Sigma β, MvPolynomial.rename (Sigma.mk b.1) (P b.1 b.2) := by
  classical
  rw [packFlagBlocks, Fintype.prod_sigma]
  simp only [map_prod]

/-- The same sum indexed by separate slot readings or by all labelled copies.
This identifies the weight used by the row with the weight in the packed
Frobenius contraction. -/
theorem sum_slot_weights_eq_sum_copy_weights {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] {I : (i : ι) → β i → Type*}
    [∀ i b, Fintype (I i b)] {K : Type*} [CommRing K]
    (l : ((b : Sigma β) → I b.1 b.2) → ℤ) (F : ∀ i b, I i b → K) :
    (∑ A : ∀ i b, I i b, (l (fun b => A b.1 b.2) : K) * ∏ i, ∏ b, F i b (A i b)) =
      ∑ A : (b : Sigma β) → I b.1 b.2, (l A : K) * ∏ b, F b.1 b.2 (A b) := by
  classical
  let e : (∀ i b, I i b) ≃ ((b : Sigma β) → I b.1 b.2) :=
    { toFun := fun A b => A b.1 b.2
      invFun := fun A i b => A ⟨i,b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ ?_
  intro A
  rw [Fintype.prod_sigma]
  rfl

/-- The full leading minor is a transvection determinant. The proper
leading minors use the excluded last row. -/
theorem unit_letter_leading_minor {m h : ℕ} (hm : 0 < m) (hh : h ≤ m+1)
    {K : Type*} [CommRing K] (X : K) :
    flagMinor hh (lineShear K X) (standardFlagRows hh) = 1 := by
  by_cases hs : h = m+1
  · subst h
    have hrows :
        ((standardFlagRows hh).1.orderEmbOfFin (standardFlagRows hh).2 :
          Fin (m+1) → Fin (m+1)) = id := by
      symm
      apply Finset.orderEmbOfFin_unique
      · intro i
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, Fin.ext rfl⟩
      · exact strictMono_id
    unfold flagMinor
    rw [hrows]
    have hs : (lineShear K X).submatrix id (Fin.castLE hh) = lineShear K X := by
      ext i j
      have hj : Fin.castLE hh j = j := Fin.ext rfl
      simp only [Matrix.submatrix_apply, id_eq, hj]
    rw [hs]
    have hne : Fin.last m ≠ (0 : Fin (m+1)) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at hv
      omega
    exact Matrix.det_transvection_of_ne _ _ hne X
  · exact proper_leading_unit_letter_minor (by omega) X

end

end Formalism.GradedWeylDivisibility.TypeI
