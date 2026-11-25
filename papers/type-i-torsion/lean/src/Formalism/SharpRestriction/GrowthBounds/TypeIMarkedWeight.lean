import Formalism.SharpRestriction.GrowthBounds.TypeINativeMarking

open scoped BigOperators Matrix Classical
open Matrix
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

private def markedRows {m h : ℕ} (b : Bool) (i : Fin (m+1))
    (hm : h = if b then 1 else m) : FlagRows (m+1) h :=
  Eq.mp (congrArg (FlagRows (m+1)) hm.symm)
    (match b with
    | true => lineRows i
    | false => hyperplaneRows i)

private def markedSign {m : ℕ} (b : Bool) (i : Fin (m+1)) : ℤ :=
  if b then 1 else (-1)^(i.val+m)

/-- At a marked position the integer sign and the chosen rows read a line
coordinate or a cofactor coordinate of the very same ordered flag. -/
theorem signed_marked_minor {m h : ℕ} (hh : h ≤ m+1) (b : Bool) (i : Fin (m+1))
    (hm : h = if b then 1 else m) {K : Type*} [CommRing K]
    (X : Matrix (Fin (m+1)) (Fin (m+1)) K) :
    (markedSign b i : K) * flagMinor hh X (markedRows b i hm) =
      if b then X i 0 else cofactorFlag X i := by
  cases b with
  | false =>
    change h = m at hm
    subst h
    simpa [markedSign,markedRows] using (cofactorFlag_eq_signed_minor X i).symm
  | true =>
    change h = 1 at hm
    subst h
    simpa [markedSign,markedRows] using lineRows_minor_eq X i

/-- Freeze one integer weight before either the unit flag or an incoming edge
is chosen. The same formula applies to integral lifts of the complete set of
minors, so the vectors used on the right may be integral normalized lifts. -/
theorem exists_fixed_marked_minor_weight {β ι : Type*} [Fintype β]
    {m : ℕ} (h : β → ℕ) (hh : ∀ b, h b ≤ m+1) (slot : β → ι) (s t : ι)
    (p R : ℕ) (leftLine : Bool) (e : ((Fin p × Fin R) ⊕ Fin R) ↪ β)
    (hs : ∀ a, slot (e (.inl a)) = s) (ht : ∀ a, slot (e (.inr a)) = t)
    (hleft : ∀ a, h (e (.inl a)) = if leftLine then 1 else m)
    (hright : ∀ a, h (e (.inr a)) = if !leftLine then 1 else m) :
    ∃ l : ((b : β) → FlagRows (m+1) (h b)) → ℤ,
      ∀ {K L : Type*} [CommRing K] [CommRing L] (q : K →+* L) (hq : Function.Injective q)
        (X : ι → Matrix (Fin (m+1)) (Fin (m+1)) L) (power : ι → L)
        (F : (b : β) → FlagRows (m+1) (h b) → K)
        (x y : Fin (m+1) → K),
        (∀ b I, q (F b I) = power (slot b) * flagMinor (hh b) (X (slot b)) I) →
        (∀ i, q (x i) = power s * (if leftLine then X s i 0 else cofactorFlag (X s) i)) →
        (∀ i, q (y i) = power t * (if !leftLine then X t i 0 else cofactorFlag (X t) i)) →
        (∑ I, (l I : K) * ∏ b, F b (I b)) =
          powerPair p x y ^ R * ∏ b ∈ (Finset.univ.map e)ᶜ, F b (standardFlagRows (hh b)) := by
  classical
  let mark (a : Fin R → Fin (m+1)) (i : (Fin p × Fin R) ⊕ Fin R) :
      FlagRows (m+1) (h (e i)) :=
    match i with
    | .inl j => markedRows leftLine (a j.2) (hleft j)
    | .inr j => markedRows (!leftLine) (a j) (hright j)
  let sign (a : Fin R → Fin (m+1)) (i : (Fin p × Fin R) ⊕ Fin R) : ℤ :=
    match i with
    | .inl j => markedSign leftLine (a j.2)
    | .inr j => markedSign (!leftLine) (a j)
  obtain ⟨choice,hchoose,hdefault⟩ := label_choices_at_marks e mark
    (fun b => standardFlagRows (hh b))
  let sgn (a : Fin R → Fin (m+1)) (b : β) : ℤ :=
    if hb : b ∈ Set.range e then sign a (Classical.choose hb) else 1
  have hsgn (a : Fin R → Fin (m+1)) (i : (Fin p × Fin R) ⊕ Fin R) :
      sgn a (e i) = sign a i := by
    let hb : e i ∈ Set.range e := ⟨i,rfl⟩
    unfold sgn
    rw [dite_eq_left hb]
    congr 1
    exact e.injective (Classical.choose_spec hb)
  refine ⟨labelWeight choice sgn,?_⟩
  intro K L _ _ q hq X power F x y hF hx hy
  refine allocated_label_sum_eq_contraction_pow p R e choice sgn F x y
    (fun b => F b (standardFlagRows (hh b))) ?_ ?_ ?_
  · intro a j
    rw [hsgn,hchoose]
    apply hq
    rw [map_mul,map_intCast,hF,hx,hs]
    change (markedSign leftLine (a j.2) : L) *
      (power s * _) = power s * _
    rw [mul_left_comm, signed_marked_minor]
  · intro a j
    rw [hsgn,hchoose]
    apply hq
    rw [map_mul,map_intCast,hF,hy,ht]
    change (markedSign (!leftLine) (a j) : L) *
      (power t * _) = power t * _
    rw [mul_left_comm, signed_marked_minor]
  · intro a b hb
    rw [hdefault a b hb]
    simp only [sgn, dite_eq_right hb, Int.cast_one, one_mul]

end

end GlobalTheory.EX.TypeIProduction
