import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SharpRestriction.GrowthBounds.TypeIAdjacentContractions
import Mathlib.Algebra.Ring.Aut

noncomputable section

namespace GlobalTheory.EX.TypeIProduction

open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility

/-- Identity frames at all coefficient places of the native model. -/
def typeIStandardTuple {p : ℕ} (G : GAtP p) : G.P.Tup :=
  fun v => colSpan (G.P.W v) (1 : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))

theorem typeIStandardTuple_isLatTup {p : ℕ} (G : GAtP p) :
    G.P.IsLatTup (typeIStandardTuple G) := by
  intro v
  exact ⟨1, by simp, rfl⟩

def rankOneDiagonal {A : Type*} [Zero A] [One A] {k : ℕ} (a : A) :
    Matrix (Fin k) (Fin k) A :=
  Matrix.diagonal fun i => if i.val < 1 then a else 1

/-- A source rank-one edge into the standard lattice has an integral frame
with unit determinant followed by the single rational-prime diagonal. -/
theorem exists_integral_rankOne_edge_frame
    {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (hr : G.P.r = 1)
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))
    (he : IsEdge p (G.P.n' v) G.P.r e) (hstd : e.tgt = typeIStandardTuple G v) :
    ∃ g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.W v), IsUnit g.det ∧
      e.src = colSpan (G.P.W v)
        (g.map (algebraMap (G.P.W v) (G.P.Qq v)) * rankOneDiagonal (p : G.P.Qq v)) := by
  letI := (G.P.setting v).frac_alt
  obtain ⟨B, _, hBsrc, hBtgt⟩ := (restEdgeBasis G v) e he
  let gQ := B * rankOneDiagonal ((p : G.P.Qq v)⁻¹)
  have hBtgt' : e.tgt = colSpan (G.P.W v) gQ := by
    change e.tgt = colSpan (G.P.W v)
      (B * Matrix.diagonal (fun c => if c.val < G.P.r then (p : G.P.Qq v)⁻¹ else 1)) at hBtgt
    rw [hr] at hBtgt
    exact hBtgt
  have hspan : colSpan (G.P.W v) (1 : Matrix _ _ (G.P.Qq v)) =
      colSpan (G.P.W v) gQ := hstd.symm.trans hBtgt'
  obtain ⟨g, hg⟩ := la_factor (O := G.P.W v) 1 gQ hspan.ge
  have hmap : gQ = g.map (algebraMap (G.P.W v) (G.P.Qq v)) := by
    simpa only [Matrix.one_mul] using hg
  obtain ⟨gInv, hInv⟩ := la_factor (O := G.P.W v) gQ 1 hspan.le
  have hprod : g * gInv = 1 := by
    apply Matrix.map_injective (IsFractionRing.injective (G.P.W v) (G.P.Qq v))
    change (g * gInv).map (algebraMap (G.P.W v) (G.P.Qq v)) =
      (1 : Matrix _ _ (G.P.W v)).map (algebraMap (G.P.W v) (G.P.Qq v))
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← hmap, ← hInv]
  have hdet : IsUnit (g.det * gInv.det) := by
    rw [← Matrix.det_mul, hprod, Matrix.det_one]
    exact isUnit_one
  have hp : (p : G.P.Qq v) ≠ 0 := by
    rw [← map_natCast (algebraMap (G.P.W v) (G.P.Qq v))]
    exact fun h => (G.P.setting v).p_unif.ne_zero
      ((IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (h.trans (map_zero _).symm))
  have hdiag : rankOneDiagonal (k := G.P.m + 1) ((p : G.P.Qq v)⁻¹) *
      rankOneDiagonal (p : G.P.Qq v) = 1 := by
    simp only [rankOneDiagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    by_cases hi : i.val < 1 <;> simp [hi, hp]
  have hB : B = g.map (algebraMap (G.P.W v) (G.P.Qq v)) * rankOneDiagonal (p : G.P.Qq v) := by
    calc
      B = B * (rankOneDiagonal ((p : G.P.Qq v)⁻¹) * rankOneDiagonal (p : G.P.Qq v)) := by
        rw [hdiag, Matrix.mul_one]
      _ = gQ * rankOneDiagonal (p : G.P.Qq v) := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [hmap]
  exact ⟨g, isUnit_of_mul_isUnit_left hdet, hBsrc.trans (congrArg (colSpan _) hB)⟩

/-- The period identity gives the next-slot Frobenius even at cyclic wrap. -/
theorem frobenius_pow_posAdd_one {Q : Type*} [CommRing Q] {n : ℕ}
    (σ : Q ≃+* Q) (hperiod : σ ^ n = 1) (s : Fin n) :
    σ ^ (posAdd s 1).val = σ ^ (s.val + 1) := by
  change σ ^ ((s.val + 1) % n) = _
  calc
    _ = σ ^ ((s.val + 1) % n) * (σ ^ n) ^ ((s.val + 1) / n) := by
      rw [hperiod, one_pow, mul_one]
    _ = σ ^ (((s.val + 1) % n) + n * ((s.val + 1) / n)) := by
      rw [pow_add, pow_mul]
    _ = _ := congrArg (fun t : ℕ => σ ^ t) (Nat.mod_add_div (s.val + 1) n)

/-- Compare any two integral lifts of the same source entry in adjacent slots. -/
theorem adjacent_integral_lifts_reduce
    {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (s : Fin (G.P.n' v))
    (x a b : G.P.W v)
    (ha : (G.P.σ v ^ s.val) (algebraMap (G.P.W v) (G.P.Qq v) x) =
      algebraMap (G.P.W v) (G.P.Qq v) a)
    (hb : (G.P.σ v ^ (posAdd s 1).val) (algebraMap (G.P.W v) (G.P.Qq v) x) =
      algebraMap (G.P.W v) (G.P.Qq v) b) :
    let q : G.P.W v →+* PrimeResidue (G.P.W v) p :=
      Ideal.Quotient.mk (Ideal.span {(p : G.P.W v)})
    q b = (q a) ^ p := by
  letI := (G.P.setting v).frac_alt
  intro q
  obtain ⟨c, hc⟩ := (G.P.setting v).frob a
  have hstep : (G.P.σ v ^ (posAdd s 1).val) (algebraMap (G.P.W v) (G.P.Qq v) x) =
      G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) a) := by
    rw [frobenius_pow_posAdd_one _ (G.P.setting v).period, pow_succ', RingAut.mul_apply, ha]
  have heq : b = a ^ p + (p : G.P.W v) * c :=
    (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (hb.symm.trans (hstep.trans hc))
  have hpq : q (p : G.P.W v) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [heq, map_add, map_mul, hpq, zero_mul, add_zero, map_pow]

/-- The actual signed rank-one normalizing exponent. -/
theorem arV_rankOne_eq_sum_first
    {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (hr : G.P.r = 1) :
    G.P.ArV v = ∑ t : Fin (G.P.n' v), lamAt (G.P.lam0 v) t 0 := by
  classical
  unfold Places.ArV Ar
  rw [hr]
  have hfirst : (Finset.univ.filter (fun i : Fin (G.P.m + 1) => i.val < 1)) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext (Nat.eq_zero_of_le_zero (Nat.lt_succ_iff.mp h)),
      fun h => by simp [h]⟩
  simp only [hfirst, Finset.sum_singleton]

/-- Number of marked height-one or height-`m` labels, computed by `hw`. -/
def typeIFirstMultiplicity {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) : ℕ :=
  let ν := nuOf (lamAt (G.P.lam0 v) s)
  ν 0 - nuNext ν 0

def typeILastProperMultiplicity {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) : ℕ :=
  let ν := nuOf (lamAt (G.P.lam0 v) s)
  let t : Fin (G.P.m + 1) := ⟨G.P.m - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  ν t - nuNext ν t

def TypeIAdjacentCapacity {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) (R : ℕ) : Prop := by
  classical
  exact if IsTypeV s then
    p * R ≤ typeIFirstMultiplicity G v s ∧ R ≤ typeILastProperMultiplicity G v (posAdd s 1)
  else
    p * R ≤ typeILastProperMultiplicity G v s ∧ R ≤ typeIFirstMultiplicity G v (posAdd s 1)

/-- The cyclic signed permutation sends the first `m` standard columns to
the complementary flag. The final sign gives determinant one. -/
def typeISignedShift {F : Type*} [Ring F] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  fun i j => if i = posAdd j 1 then if j = Fin.last m then (-1) ^ m else 1 else 0

def typeIStandardHighest {p : ℕ} (G : GAtP p) : G.P.Xsp :=
  ∏ u : Fin G.P.nV, G.P.vEmb u (∏ t : Fin (G.P.n' u),
    MvPolynomial.rename (fun ij : Fin (G.P.m + 1) × Fin (G.P.m + 1) => (t, ij))
      (hw G.Kf (r := G.P.m + 1) (n := G.P.m + 1) le_rfl (nuOf (lamAt (G.P.lam0 u) t))))

/-- Keep every standard flag except the odd member of the chosen adjacent pair. -/
def typeISignedPermutationOutput {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) : G.P.Xsp := by
  classical
  let odd := if IsTypeV s then posAdd s 1 else s
  exact G.P.subst (Function.update (fun _ _ => 1) v
    (fun t => if t = odd then (typeISignedShift (F := G.Kf) G.P.m)ᵀ else 1))
    (typeIStandardHighest G)

def TypeIAdjacentRowConclusion {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) (R : ℕ) : Prop :=
  let L := typeIStandardTuple G
  ∃ (Λ : G.P.Xsp →ₗ[G.Kf] G.Kf) (row : ↥(G.P.HtupW L) →ₗ[G.O] G.O)
    (ξ : ↥(G.P.HtupW L)),
    ξ.1 = typeISignedPermutationOutput G v s ∧ row ξ = 1 ∧
      (∀ F : ↥(G.P.HtupW L), algebraMap G.O G.Kf (row F) = Λ F.1) ∧
      ∀ L' (he : IsEdge p (G.P.n' v) G.P.r ⟨L', L v⟩),
        ∀ F ∈ G.P.HtupW (Function.update L v L'),
          Λ (((p : G.Kf) ^ G.P.ArV v) • F) ∈
            (algebraMap G.O G.Kf '' (Ideal.span {(p : G.O) ^ R} : Set G.O))

/-- Statement of the native single-pair row. The proof must construct the same
functional for the unit output and all native predecessors. -/
def TypeIAdjacentRowStatement : Prop :=
  ∀ {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (R : ℕ),
    G.P.r = 1 → 0 < G.P.m → TypeIAdjacentCapacity G v s R →
      TypeIAdjacentRowConclusion G v s R

end GlobalTheory.EX.TypeIProduction
