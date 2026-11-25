import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Adjugate

noncomputable section

namespace GlobalTheory.EX.TypeIProduction

open Matrix MvPolynomial

/-- The marked line and volume-dual hyperplane matrices share this identity.
Here `dInv` is the inverse of the unit factor in `det A = a * d`. -/
theorem normalized_pairing {ι W : Type*} [Fintype ι] [DecidableEq ι] [CommRing W]
    (A : Matrix ι ι W) (a d dInv : W) (hdet : A.det = a * d) (hd : dInv * d = 1) :
    (dInv • A)ᵀ * (dInv • A.adjugateᵀ) = (a * dInv) • (1 : Matrix ι ι W) := by
  have hcoeff : (dInv * dInv) * (a * d) = a * dInv := by
    calc
      _ = (a * dInv) * (dInv * d) := by ac_rfl
      _ = _ := by rw [hd, mul_one]
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.transpose_mul, Matrix.adjugate_mul, Matrix.transpose_smul,
    Matrix.transpose_one, smul_smul, hdet, hcoeff]

/-- All `p` marked factors on the outgoing slot are copies of this same generic flag. -/
def powerPair {ι W : Type*} [Fintype ι] [CommSemiring W]
    (p : ℕ) (x y : ι → W) : W :=
  (fun i => x i ^ p) ⬝ᵥ y

theorem map_powerPair {ι W B : Type*} [Fintype ι] [CommSemiring W] [CommSemiring B]
    (f : W →+* B) (p : ℕ) (x y : ι → W) :
    f (powerPair p x y) = powerPair p (f ∘ x) (f ∘ y) := by
  simp [powerPair, dotProduct]

private theorem powerPair_mulVec_eq_zero
    {ι B : Type*} [Fintype ι] [CommSemiring B] (p : ℕ) [ExpChar B p]
    (A D : Matrix ι ι B) (x y : ι → B)
    (h : Dᵀ * A.map (frobenius B p) = 0) :
    powerPair p (A *ᵥ x) (D *ᵥ y) = 0 := by
  have hPow : (fun i => ((A *ᵥ x) i) ^ p) =
      A.map (frobenius B p) *ᵥ (frobenius B p ∘ x) :=
    funext fun i => RingHom.map_mulVec (frobenius B p) A x i
  rw [powerPair, hPow, ← Matrix.dotProduct_transpose_mulVec D y,
    Matrix.mulVec_mulVec, h]
  simp

/-- The two cross-slot contractions after rational-prime reduction. -/
theorem adjacent_contractions_eq_zero
    {ι B : Type*} [Fintype ι] [CommSemiring B] (p : ℕ) [ExpChar B p]
    (U V U' V' : Matrix ι ι B) (x y x' y' : ι → B)
    (hUV : Vᵀ * U = 0) (hU : U' = U.map (frobenius B p))
    (hV : V' = V.map (frobenius B p)) :
    powerPair p (U *ᵥ x) (V' *ᵥ y') = 0 ∧
      powerPair p (V *ᵥ y) (U' *ᵥ x') = 0 := by
  let f : B →+* B := frobenius B p
  have htranspose : Vᵀ.map f = (V.map f)ᵀ := Matrix.ext fun _ _ => rfl
  have hcross : (V.map f)ᵀ * U.map f = 0 := by
    simpa only [Matrix.map_mul, htranspose, Matrix.map_zero f f.map_zero] using
      congrArg (fun M : Matrix ι ι B => M.map f) hUV
  have hcross' : (U.map f)ᵀ * V.map f = 0 := by
    have h := congrArg Matrix.transpose hcross
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  rw [hU, hV]
  exact ⟨powerPair_mulVec_eq_zero p U (V.map f) x y' hcross,
    powerPair_mulVec_eq_zero p V (U.map f) y x' hcross'⟩

abbrev PrimeResidue (W : Type*) [CommRing W] (p : ℕ) :=
  W ⧸ Ideal.span {((p : ℕ) : W)}

def reduceCoefficients {σ W : Type*} [CommRing W] (p : ℕ) :
    MvPolynomial σ W →+* MvPolynomial σ (PrimeResidue W p) :=
  MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(p : W)}))

/-- Reduce the polynomial contractions over `W/(p)` and recover divisibility by
the constant rational prime in the original polynomial ring. -/
theorem adjacent_polynomial_contractions_dvd
    {ι σ W : Type*} [Fintype ι] [CommRing W]
    (p : ℕ) (hp : p.Prime) (hpnu : ¬ IsUnit (p : W))
    (U V U' V' : Matrix ι ι (MvPolynomial σ W))
    (x y x' y' : ι → MvPolynomial σ W)
    (hUV : (Vᵀ * U).map (reduceCoefficients p) = 0)
    (hU : ∀ i j, reduceCoefficients p (U' i j) = reduceCoefficients p (U i j) ^ p)
    (hV : ∀ i j, reduceCoefficients p (V' i j) = reduceCoefficients p (V i j) ^ p) :
    C (p : W) ∣ powerPair p (U *ᵥ x) (V' *ᵥ y') ∧
      C (p : W) ∣ powerPair p (V *ᵥ y) (U' *ᵥ x') := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (PrimeResidue W p) p := CharP.quotient W p (mem_nonunits_iff.mpr hpnu)
  letI : CharP (MvPolynomial σ (PrimeResidue W p)) p :=
    charP_of_injective_ringHom (f := MvPolynomial.C) (MvPolynomial.C_injective σ (PrimeResidue W p)) p
  let ρ : MvPolynomial σ W →+* MvPolynomial σ (PrimeResidue W p) := reduceCoefficients p
  let φ := frobenius (MvPolynomial σ (PrimeResidue W p)) p
  have hU' : U'.map ρ = (U.map ρ).map φ := Matrix.ext fun i j => hU i j
  have hV' : V'.map ρ = (V.map ρ).map φ := Matrix.ext fun i j => hV i j
  have htranspose : Vᵀ.map (reduceCoefficients p) = (V.map ρ)ᵀ :=
    Matrix.ext fun _ _ => rfl
  have hUV' : (V.map ρ)ᵀ * U.map ρ = 0 := by
    simpa only [Matrix.map_mul, htranspose] using hUV
  have hmv (A : Matrix ι ι (MvPolynomial σ W)) (z : ι → MvPolynomial σ W) :
      ρ ∘ (A *ᵥ z) = A.map ρ *ᵥ (ρ ∘ z) :=
    funext fun i => RingHom.map_mulVec ρ A z i
  obtain ⟨hEven, hOdd⟩ := adjacent_contractions_eq_zero p
    (U.map ρ) (V.map ρ) (U'.map ρ) (V'.map ρ) (ρ ∘ x) (ρ ∘ y) (ρ ∘ x') (ρ ∘ y')
    hUV' hU' hV'
  have hdvd (f : MvPolynomial σ W) : C (p : W) ∣ f ↔ ρ f = 0 :=
    C_dvd_iff_map_hom_eq_zero (Ideal.Quotient.mk (Ideal.span {(p : W)})) (p : W)
      (fun z => Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton) f
  exact ⟨(hdvd _).2 (by simpa only [map_powerPair, hmv] using hEven),
    (hdvd _).2 (by simpa only [map_powerPair, hmv] using hOdd)⟩

/-- Taking the same contraction in `depth` disjoint groups before substitution
forces the rational prime power in every resulting coefficient. -/
theorem coeff_substitute_contraction_pow_mem
    {σ τ W : Type*} [CommRing W] (p depth : ℕ) (f unused : MvPolynomial σ W)
    (hf : C (p : W) ∣ f) (z : σ → MvPolynomial τ W) (m : τ →₀ ℕ) :
    (aeval z (f ^ depth * unused)).coeff m ∈ Ideal.span {((p : W) ^ depth)} := by
  obtain ⟨q, rfl⟩ := hf
  apply Ideal.mem_span_singleton.mpr
  refine ⟨(aeval z (q ^ depth * unused)).coeff m, ?_⟩
  rw [mul_pow, mul_assoc, ← map_pow C, map_mul, aeval_C, algebraMap_eq, coeff_C_mul]

end GlobalTheory.EX.TypeIProduction
