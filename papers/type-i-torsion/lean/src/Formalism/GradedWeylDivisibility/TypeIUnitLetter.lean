import Formalism.GradedWeylDivisibility.TypeIMarkedFlagLabels
import Formalism.SharpRestriction.GrowthBounds.TypeINormalizedIncomingRow

open scoped BigOperators Matrix
open Matrix MvPolynomial
open GlobalTheory.EX.TypeIProduction

namespace Formalism.GradedWeylDivisibility.TypeI

noncomputable section

def standardFlagRows {n h : ℕ} (hh : h ≤ n) : FlagRows n h :=
  ⟨Finset.univ.map (Fin.castLEEmb hh), by simp⟩

private theorem standardFlagRows_order {n h : ℕ} (hh : h ≤ n) :
    ((standardFlagRows hh).1.orderEmbOfFin (standardFlagRows hh).2 : Fin h → Fin n) =
      Fin.castLE hh := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · intro i j hij
    exact hij

theorem standardFlagMinor_eq_one {n h : ℕ} (hh : h ≤ n) {K : Type*} [CommRing K] :
    flagMinor hh (1 : Matrix (Fin n) (Fin n) K) (standardFlagRows hh) = 1 := by
  unfold flagMinor
  rw [standardFlagRows_order]
  have h : (1 : Matrix (Fin n) (Fin n) K).submatrix (Fin.castLE hh) (Fin.castLE hh) = 1 := by
    apply Matrix.ext
    intro i j
    simp [Matrix.one_apply]
  rw [h, Matrix.det_one]

abbrev unitLetter (m k : ℕ) : List (Fin (m+1) × Fin (m+1) × ℕ) :=
  [(Fin.last m, 0, k)]

abbrev lineShear {m : ℕ} (K : Type*) [CommRing K] (X : K) : Matrix (Fin (m+1)) (Fin (m+1)) K :=
  letterMatrix (Fin.last m) 0 X

/-- The unaltered word coordinate, with the original order and transposition. -/
theorem wordFlag_unit_letter {m k : ℕ} (K : Type*) [CommRing K] :
    wordFlag (1 : Matrix (Fin (m+1)) (Fin (m+1)) K) (unitLetter m k) =
      lineShear (MvPolynomial (WordParameter 1) K) (X none) := by
  have hMap : (1 : Matrix (Fin (m+1)) (Fin (m+1)) K).map
      (MvPolynomial.C : K →+* MvPolynomial (WordParameter 1) K) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  change (1 : Matrix (Fin (m+1)) (Fin (m+1)) K).map MvPolynomial.C *
    orderedMatrix K [(Fin.last m,0,k)] = _
  rw [hMap, Matrix.one_mul]
  simp only [orderedMatrix, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

/-- A proper leading square omits the altered last row. -/
theorem proper_leading_unit_letter_minor {m h : ℕ} (hh : h ≤ m)
    {K : Type*} [CommRing K] (X : K) :
    flagMinor (Nat.le_succ_of_le hh) (lineShear K X) (standardFlagRows (Nat.le_succ_of_le hh)) = 1 := by
  unfold flagMinor
  rw [standardFlagRows_order]
  have he :
      (lineShear K X).submatrix (Fin.castLE (Nat.le_succ_of_le hh))
        (Fin.castLE (Nat.le_succ_of_le hh)) = 1 := by
    apply Matrix.ext
    intro i j
    have hrow : Fin.last m ≠ Fin.castLE (Nat.le_succ_of_le hh) i := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castLE] at hval
      omega
    simp [letterMatrix, Matrix.submatrix_apply, Matrix.one_apply, hrow]
  rw [he, Matrix.det_one]

/-- Pair the same line shear with the actual cofactor vector of the identity
flag. The sign disappears because the chosen coordinate is the last one. -/
theorem unit_letter_line_pairings {m : ℕ} (hm : 0 < m) (p : ℕ) (hp : p ≠ 0)
    {K : Type*} [CommRing K] (X : K) :
    powerPair p ((lineShear K X).col 0) (cofactorFlag (1 : Matrix (Fin (m+1)) (Fin (m+1)) K)) = X^p ∧
      powerPair p (cofactorFlag (1 : Matrix (Fin (m+1)) (Fin (m+1)) K)) ((lineShear K X).col 0) = X := by
  classical
  have hz : Fin.last m ≠ (0 : Fin (m+1)) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last,Fin.val_zero] at this
    omega
  have hA : (lineShear K X).col 0 (Fin.last m) = X := by
    simp [letterMatrix, Matrix.col, hz]
  have hc (i : Fin (m+1)) : cofactorFlag (1 : Matrix (Fin (m+1)) (Fin (m+1)) K) i =
      if i = Fin.last m then 1 else 0 := by
    simp [cofactorFlag, Matrix.one_apply, eq_comm]
  constructor
  · unfold powerPair dotProduct
    rw [Fintype.sum_eq_single (Fin.last m)]
    · simp only [hA, hc, ite_self, mul_one, ite_true]
    · intro i hi
      simp [hc,hi]
  · unfold powerPair dotProduct
    rw [Fintype.sum_eq_single (Fin.last m)]
    · simp only [hA, hc, ite_self, one_pow, one_mul, ite_true]
    · intro i hi
      simp [hc,hi,hp]

/-- With the appropriate choice of the single word degree, the selected
contraction has coefficient exactly one in both orientations. -/
theorem unit_letter_marked_coefficients {m : ℕ} (hm : 0 < m) (p R : ℕ) (hp : p ≠ 0)
    (K : Type*) [CommRing K] :
    let S := MvPolynomial (WordParameter 1) K
    let X : S := MvPolynomial.X none
    let C := cofactorFlag (1 : Matrix (Fin (m+1)) (Fin (m+1)) S)
    let L := (lineShear S X).col 0
    ((powerPair p L C)^R).coeff (wordExponent (unitLetter m (p*R))) = 1 ∧
      ((powerPair p C L)^R).coeff (wordExponent (unitLetter m R)) = 1 := by
  intro S Z C L
  obtain ⟨hl,hr⟩ := unit_letter_line_pairings hm p hp Z
  simp only [L,C,hl,hr,← pow_mul,Z]
  constructor
  · change (MvPolynomial.X (R := K) (none : WordParameter 1) ^ (p*R)).coeff
      (Finsupp.single none (p*R)) = 1
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, ite_eq_left rfl]
  · change (MvPolynomial.X (R := K) (none : WordParameter 1) ^ R).coeff
      (Finsupp.single none R) = 1
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, ite_eq_left rfl]

/-- The proposed unit word uses one letter in the selected line slot of the
actual standard tuple. All other words are literally empty. -/
def nativeUnitWords {p : ℕ} (G : Formalism.MainNotions.G.GAtP p)
    (slot : NativeFlagSlot G) (k : ℕ) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
      List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ) :=
  if (⟨v,s⟩ : NativeFlagSlot G) = slot then unitLetter G.P.m k else []

theorem native_unit_letter_generator_mem {p : ℕ} (G : Formalism.MainNotions.G.GAtP p)
    [IsFractionRing G.O G.Kf] (slot : NativeFlagSlot G) (k : ℕ) :
    framedTupleWord G (fun _ _ => 1) (nativeUnitWords G slot k) ∈
      G.P.HtupW (typeIStandardTuple G) := by
  have hs := HtupW_eq_span_framed_words G (typeIStandardTuple G) (fun _ _ => 1)
    (fun _ _ => by simp) (standard_slot_frame G)
  rw [hs]
  exact Submodule.subset_span ⟨nativeUnitWords G slot k,rfl⟩

end

end Formalism.GradedWeylDivisibility.TypeI
