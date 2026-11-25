import Formalism.SharpRestriction.ParConsts

open Formalism.BasicNotions

namespace Formalism.MainNotions

/-- The source lower bound for bTop follows from its equality and SizeLa.
The lower bound omits LaG, and SizeLa supplies its required factor x^eps. -/
theorem FamCore.bTop_lower_of_sizeLa {eps : ℝ} (F : FamCore eps)
    (x : ℝ) (hx : F.x1 < x) (i : F.Ix x) (hSize : SizeLa (F.L x i)) :
    (F.L x i).sc.b' + 2 * ((F.D x i).R.n : ℝ) * (F.L x i).sc.delta1 *
      x^(2*eps) * (F.L x i).sc.b' / ((F.D x i).R.k : ℝ) ≤ F.bTop x := by
  have hxpos : 0 < x := zero_lt_one.trans (F.one_lt_family_threshold.trans hx)
  have hLa := hSize.1
  rw [F.L_x x i hx, F.L_eps x i] at hLa
  have hPow : x^(2*eps) = x^eps * x^eps := by
    rw [two_mul, Real.rpow_add hxpos]
  have hScale : 0 < (F.L x i).sc.x := zero_lt_one.trans (F.L x i).sc.one_lt_alt
  have hDelta : 0 < (F.L x i).sc.delta1 := Real.rpow_pos_of_pos hScale _
  have hb : 0 < (F.L x i).sc.b' :=
    div_pos (mul_pos hScale (Real.exp_pos _)) (Real.exp_pos _)
  have hCoeff : 0 ≤ 2 * ((F.D x i).R.n : ℝ) * (F.L x i).sc.delta1 * x^eps :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hDelta.le)
      (Real.rpow_pos_of_pos hxpos _).le
  rw [F.bTop_eq x hx i, hPow,
    ← mul_assoc (2 * ((F.D x i).R.n : ℝ) * (F.L x i).sc.delta1) (x^eps) (x^eps)]
  exact add_le_add_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLa hCoeff) hb.le)
    (Nat.cast_nonneg _)) _

/-- Use the original proof field for the actual size of the same member. -/
theorem FamP.bTop_lower_from_eq_and_sizes {eps : ℝ} (F : FamP eps)
    (x : ℝ) (hx : F.x1 < x) (i : F.Ix x) :
    (F.L x i).sc.b' + 2 * ((F.D x i).R.n : ℝ) * (F.L x i).sc.delta1 *
      x^(2*eps) * (F.L x i).sc.b' / ((F.D x i).R.k : ℝ) ≤ F.bTop x :=
  F.toFamCore.bTop_lower_of_sizeLa x hx i (F.sizes x hx i).2.2.2.2.2.2.2.2.1

end Formalism.MainNotions
