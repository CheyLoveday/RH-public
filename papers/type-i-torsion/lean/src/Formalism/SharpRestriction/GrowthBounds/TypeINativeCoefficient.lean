import Formalism.SharpRestriction.GrowthBounds.TypeINativeFrames
import Formalism.GradedWeylDivisibility.TypeIMarkedFlagLabels
import Mathlib.Data.Rat.Cast.CharZero

open scoped BigOperators Matrix Classical
open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

abbrev NativeFlagSlot {p : ℕ} (G : GAtP p) := Σ v : Fin G.P.nV, Fin (G.P.n' v)

abbrev NativeFlagWeight {p : ℕ} (G : GAtP p) (a : NativeFlagSlot G) :=
  nuOf (lamAt (G.P.lam0 a.1) a.2)

abbrev NativeFlagLabels {p : ℕ} (G : GAtP p) := ∀ a : NativeFlagSlot G, FlagLabels (NativeFlagWeight G a)

private def flattenFlags {p : ℕ} (G : GAtP p) :
    G.P.Xsp →ₐ[G.Kf] MvPolynomial (Σ _a : NativeFlagSlot G, Fin (G.P.m+1) × Fin (G.P.m+1)) G.Kf :=
  rename (fun x => ⟨⟨x.1,x.2.1⟩,x.2.2⟩)

private theorem flattenFlags_emb {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (s : Fin (G.P.n' v))
    (F : MvPolynomial (Fin (G.P.m+1) × Fin (G.P.m+1)) G.Kf) :
    flattenFlags G (G.P.vEmb v (blockEmb G.Kf s F)) = rename (Sigma.mk (⟨v,s⟩ : NativeFlagSlot G)) F := by
  unfold flattenFlags Places.vEmb blockEmb
  rw [rename_rename, rename_rename]
  rfl

private theorem flattenFlags_framedTupleWord {p : ℕ} (G : GAtP p)
    (g : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)
    (w : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ)) :
    flattenFlags G (framedTupleWord G g w) =
      (∏ a : NativeFlagSlot G, (g a.1 a.2).det ^ (-(lamAt (G.P.lam0 a.1) a.2 (Fin.last G.P.m)))) •
        packFlagBlocks (fun a : NativeFlagSlot G =>
          rowAct G.Kf (g a.1 a.2)⁻¹ (applyWord G.Kf (w a.1 a.2)
            (hw G.Kf le_rfl (NativeFlagWeight G a)))) := by
  unfold framedTupleWord packFlagBlocks
  simp only [map_prod, flattenFlags_emb]
  rw [Fintype.prod_sigma, Fintype.prod_sigma]
  simp only [framedWeylWord, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    map_mul, rename_C, Finset.prod_mul_distrib, map_prod]

/-- The integer-labelled row on the source HtupW is integral in the standard
tuple. Its ambient linear map has a single formula on every framed source word. -/
theorem exists_native_integral_label_row {p : ℕ} (G : GAtP p)
    [IsFractionRing G.O G.Kf] [CharZero G.Kf]
    (l : NativeFlagLabels G → ℤ) :
    ∃ (Λ : G.P.Xsp →ₗ[G.Kf] G.Kf)
      (row : ↥(G.P.HtupW (typeIStandardTuple G)) →ₗ[G.O] G.O),
      (∀ F : ↥(G.P.HtupW (typeIStandardTuple G)), algebraMap G.O G.Kf (row F) = Λ F.1) ∧
      ∀ (g : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)
        (w : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ)),
        Λ (framedTupleWord G g w) =
          (∏ a : NativeFlagSlot G, (g a.1 a.2).det ^ (-(lamAt (G.P.lam0 a.1) a.2 (Fin.last G.P.m)))) *
            ∑ I : NativeFlagLabels G, (l I : G.Kf) *
              ∏ a : NativeFlagSlot G,
                (flagProducts (NativeFlagWeight G a) (wordFlag (g a.1 a.2)⁻¹ᵀ (w a.1 a.2)) (I a)).coeff
                  (wordExponent (w a.1 a.2)) := by
  classical
  let f := algebraMap G.O G.Kf
  obtain ⟨read, hread⟩ := exists_polarized_row_on_flag_blocks (Rat.castHom G.Kf)
    (NativeFlagWeight G) (fun I : NativeFlagLabels G => ((l I : ℤ) : ℚ))
  let Λ := read.comp (flattenFlags G).toLinearMap
  have hword (g : ∀ v : Fin G.P.nV, Fin (G.P.n' v) →
      Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)
      (w : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ)) :
      Λ (framedTupleWord G g w) =
        (∏ a : NativeFlagSlot G, (g a.1 a.2).det ^ (-(lamAt (G.P.lam0 a.1) a.2 (Fin.last G.P.m)))) *
          ∑ I : NativeFlagLabels G, (l I : G.Kf) *
            ∏ a : NativeFlagSlot G,
              (flagProducts (NativeFlagWeight G a) (wordFlag (g a.1 a.2)⁻¹ᵀ (w a.1 a.2)) (I a)).coeff
                (wordExponent (w a.1 a.2)) := by
    change read (flattenFlags G (framedTupleWord G g w)) = _
    rw [flattenFlags_framedTupleWord, map_smul, smul_eq_mul]
    have h := congrArg (fun t => (∏ a : NativeFlagSlot G,
        (g a.1 a.2).det ^ (-(lamAt (G.P.lam0 a.1) a.2 (Fin.last G.P.m)))) * t)
        (hread (fun a => (g a.1 a.2)⁻¹ᵀ) (fun a => w a.1 a.2))
    simp only [Matrix.transpose_transpose, map_intCast] at h
    convert h using 2
    congr 1
    apply Finset.ext
    intro a
    simp only [Finset.mem_univ]
  let g₀ : ∀ v : Fin G.P.nV, Fin (G.P.n' v) →
      Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf := fun _ _ => 1
  have hSpan : G.P.HtupW (typeIStandardTuple G) =
      Submodule.span G.O (Set.range (framedTupleWord G g₀)) := by
    refine HtupW_eq_span_framed_words G _ g₀ (fun v s => by simp [g₀]) ?_
    intro v s
    rw [typeIStandardTuple, la_extO_G]
    have h : la_tw (G.P.ι v) (G.P.σ v) s.val
        (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.Qq v)) = 1 := by
      unfold la_tw
      exact map_one _
    rw [h]
  have hone : (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)⁻¹ = 1 :=
    Matrix.inv_eq_left_inv (by simp)
  have hIntWord (w : ∀ v : Fin G.P.nV, Fin (G.P.n' v) →
      List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ)) :
      Λ (framedTupleWord G g₀ w) ∈ LinearMap.range (Algebra.linearMap G.O G.Kf) := by
    let u (a : NativeFlagSlot G) (I : FlagLabels (NativeFlagWeight G a)) :=
      (flagProducts (NativeFlagWeight G a) (orderedMatrix G.O (w a.1 a.2)) I).coeff (wordExponent (w a.1 a.2))
    have hu (a : NativeFlagSlot G) (I : FlagLabels (NativeFlagWeight G a)) :
        f (u a I) = (flagProducts (NativeFlagWeight G a)
          (orderedMatrix G.Kf (w a.1 a.2)) I).coeff (wordExponent (w a.1 a.2)) := by
      dsimp only [u]
      rw [← MvPolynomial.coeff_map, map_flagProducts, map_orderedMatrix]
    refine ⟨∑ I : NativeFlagLabels G, (l I : G.O) * ∏ a : NativeFlagSlot G, u a (I a),?_⟩
    change f _ = _
    rw [hword]
    simp only [map_sum, map_prod, map_mul, map_intCast, hu, g₀, Matrix.det_one,
      _root_.one_zpow, Finset.prod_const_one, one_mul, hone, Matrix.transpose_one,
      wordFlag, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  have hInt (F : ↥(G.P.HtupW (typeIStandardTuple G))) :
      Λ F.1 ∈ LinearMap.range (Algebra.linearMap G.O G.Kf) := by
    have hle : Submodule.span G.O (Set.range (framedTupleWord G g₀)) ≤
        (LinearMap.range (Algebra.linearMap G.O G.Kf)).comap (Λ.restrictScalars G.O) := by
      rw [Submodule.span_le]
      rintro _ ⟨w,rfl⟩
      exact hIntWord w
    obtain ⟨x,hx⟩ := F
    change x ∈ G.P.HtupW (typeIStandardTuple G) at hx
    rw [hSpan] at hx
    exact hle hx
  let E := LinearEquiv.ofInjective (Algebra.linearMap G.O G.Kf)
    (IsFractionRing.injective G.O G.Kf)
  let restrict := ((Λ.restrictScalars G.O).comp (G.P.HtupW (typeIStandardTuple G)).subtype).codRestrict
    (LinearMap.range (Algebra.linearMap G.O G.Kf)) hInt
  let row := E.symm.toLinearMap.comp restrict
  refine ⟨Λ,row,?_,hword⟩
  intro F
  exact congrArg Subtype.val (E.apply_symm_apply (restrict F))

end

end GlobalTheory.EX.TypeIProduction
