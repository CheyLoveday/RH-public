import Formalism.GradedWeylDivisibility.TypeIFlagFrames
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
import Formalism.GradedWeylDivisibility.FinalD

open scoped BigOperators Matrix
open Matrix MvPolynomial
open Formalism.BasicNotions Formalism.MainNotions.G
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

private theorem map_letterMatrix {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : Fin n) (c : R) :
    (letterMatrix a b c).map f = letterMatrix a b (f c) := by
  unfold letterMatrix
  change f.mapMatrix (1 + Matrix.single a b c) = _
  rw [map_add, map_one]
  congr 1
  exact Matrix.map_single a b c f

theorem map_orderedMatrix {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : List (Fin n × Fin n × ℕ)) :
    (orderedMatrix R w).map (MvPolynomial.map f) = orderedMatrix S w := by
  induction w with
  | nil =>
      simp only [orderedMatrix, Matrix.map_one, map_zero, map_one]
  | cons a w ih =>
      simp only [orderedMatrix, Matrix.map_mul, map_letterMatrix, MvPolynomial.map_X]
      congr 1
      rw [← ih]
      apply Matrix.ext
      intro i j
      exact MvPolynomial.map_rename (f := f) _ _

/-- Change the coefficient ring on the literal generator using the same word. -/
theorem map_applyWord_hw {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ν : Fin n → ℕ) (w : List (Fin n × Fin n × ℕ)) :
    MvPolynomial.map f (applyWord R w (hw R le_rfl ν)) = applyWord S w (hw S le_rfl ν) := by
  rw [applyWord_hw_eq_labelled_coefficients, applyWord_hw_eq_labelled_coefficients, map_sum]
  apply Finset.sum_congr rfl
  intro I _
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.map_C]
  congr 1
  · rw [← MvPolynomial.coeff_map, map_flagProducts, map_orderedMatrix]
  · rw [map_flagProducts]
    congr 1
    apply Matrix.ext
    intro i j
    exact MvPolynomial.map_X f (i,j)

private theorem rowAct_one_eq {n : ℕ} {K : Type*} [Field K] :
    rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro x
  simp [rowAct, Matrix.one_apply, apply_ite, eq_comm]

/-- One literal source generator, including the determinant character. -/
def framedWeylWord {m : ℕ} {K : Type*} [Field K] (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (w : List (Fin (m + 1) × Fin (m + 1) × ℕ)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (g.det ^ (-(lam (Fin.last m)))) • rowAct K g⁻¹ (applyWord K w (hw K le_rfl (nuOf lam)))

/-- The twisted lattice uses the integral divided words in its frame. -/
theorem deltaLTw_eq_span_framed_words {O K : Type} [CommRing O] [Field K] [Algebra O K]
    {m : ℕ} (lam : Fin (m + 1) → ℤ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hg : IsUnit g.det) :
    deltaLTw O K m lam g = Submodule.span O (Set.range (framedWeylWord lam g)) := by
  let e : MvPolynomial (Fin (m+1) × Fin (m+1)) O →ₗ[O]
      MvPolynomial (Fin (m+1) × Fin (m+1)) K := (mapAlgHom (Algebra.ofId O K)).toLinearMap
  let act := (rowAct K (n := m+1) g).toLinearMap.restrictScalars O
  let inv := (rowAct K (n := m+1) g⁻¹).toLinearMap.restrictScalars O
  have hi (F) : inv (act F) = F := by
    change rowAct K g⁻¹ (rowAct K g F) = F
    have h := row_action_mul K (m+1) (m+1) g⁻¹ g
    rw [Matrix.mul_nonsing_inv g hg, rowAct_one_eq] at h
    exact congrArg (fun φ : MvPolynomial (Fin (m+1) × Fin (m+1)) K →ₐ[K]
      MvPolynomial (Fin (m+1) × Fin (m+1)) K => φ F) h
  have hj (F) : act (inv F) = F := by
    change rowAct K g (rowAct K g⁻¹ F) = F
    have h := row_action_mul K (m+1) (m+1) g g⁻¹
    rw [Matrix.nonsing_inv_mul g hg, rowAct_one_eq] at h
    exact congrArg (fun φ : MvPolynomial (Fin (m+1) × Fin (m+1)) K →ₐ[K]
      MvPolynomial (Fin (m+1) × Fin (m+1)) K => φ F) h
  have hδ : deltaL O K (m+1) (nuOf lam) g =
      (weyl O (m+1) (m+1) le_rfl (nuOf lam)).map (inv.comp e) := by
    apply Submodule.ext
    intro F
    change (act F ∈ (weyl O (m+1) (m+1) le_rfl (nuOf lam)).map e) ↔ _
    constructor
    · rintro ⟨f, hf, hF⟩
      exact ⟨f, hf, (congrArg inv hF).trans (hi F)⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, hf, (hj (e f)).symm⟩
  rw [deltaLTw, hδ, ← Submodule.map_comp, weyl, Submodule.map_span, ← Set.range_comp']
  apply congrArg (Submodule.span O)
  apply congrArg Set.range
  funext w
  change (g.det ^ (-(lam (Fin.last m)))) •
    rowAct K g⁻¹ (MvPolynomial.map (algebraMap O K) (applyWord O w (hw O le_rfl (nuOf lam)))) = _
  rw [map_applyWord_hw]
  rfl

private theorem product_mem_span_generators {ι A O : Type*} [Fintype ι] [CommRing O]
    [CommRing A] [Algebra O A] {α : ι → Type*}
    (g : ∀ i, α i → A) (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span O (Set.range (g i))) :
    (∏ i, x i) ∈ Submodule.span O (Set.range fun w : ∀ i, α i => ∏ i, g i (w i)) := by
  classical
  choose c hc using fun i => Finsupp.mem_span_range_iff_exists_finsupp.mp (hx i)
  let S (i : ι) := (c i).support
  have he (i : ι) : x i = ∑ a : (↑(S i) : Type _), c i a.1 • g i a.1 :=
    (hc i).symm.trans (Finset.sum_attach (S i) _).symm
  have hprod : (∏ i, x i) =
      ∑ w : ∀ i, (↑(S i) : Type _), ∏ i, c i (w i).1 • g i (w i).1 := by
    conv_lhs => enter [2, i]; rw [he i]
    exact Fintype.prod_sum _
  rw [hprod]
  apply Submodule.sum_mem
  intro w _
  have heq : (∏ i, c i (w i).1 • g i (w i).1) =
      (∏ i, c i (w i).1) • (∏ i, g i (w i).1) := by
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun i => (w i).1, rfl⟩)

private theorem map_span_range_algHom {O A B : Type*} [CommRing O] [CommRing A] [CommRing B]
    [Algebra O A] [Algebra O B] {α : Type*} (f : A →ₐ[O] B) (g : α → A)
    {x : A} (hx : x ∈ Submodule.span O (Set.range g)) :
    f x ∈ Submodule.span O (Set.range fun a => f (g a)) := by
  rw [Set.range_comp']
  change f x ∈ Submodule.span O (f.toLinearMap '' Set.range g)
  rw [← Submodule.map_span]
  exact ⟨x,hx,rfl⟩

def framedTupleWord {p : ℕ} (G : GAtP p)
    (g : ∀ v : Fin G.P.nV, Fin (G.P.n' v) →
      Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)
    (w : ∀ (v : Fin G.P.nV), Fin (G.P.n' v) →
      List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ)) : G.P.Xsp :=
  ∏ v, G.P.vEmb v (∏ s, blockEmb G.Kf s
    (framedWeylWord (lamAt (G.P.lam0 v) s) (g v s) (w v s)))

/-- Actual `HtupW` is generated by the framed divided words on the native
slot variables. The chosen frames are the columns supplied by `extO`. -/
theorem HtupW_eq_span_framed_words {p : ℕ} (G : GAtP p)
    [IsFractionRing G.O G.Kf] (l : G.P.Tup)
    (g : ∀ v : Fin G.P.nV, Fin (G.P.n' v) →
      Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)
    (hdet : ∀ v s, IsUnit (g v s).det)
    (hfrm : ∀ v s, extO G.O (G.P.ι v) (G.P.σ v) s.val (l v) = colSpan G.O (g v s)) :
    G.P.HtupW l = Submodule.span G.O (Set.range (framedTupleWord G g)) := by
  classical
  let f (v : Fin G.P.nV) (s : Fin (G.P.n' v)) := framedWeylWord (lamAt (G.P.lam0 v) s) (g v s)
  have hslot (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    Dl0 G.O G.P.m (lamAt (G.P.lam0 v) s)
      (extO G.O (G.P.ι v) (G.P.σ v) s.val (l v)) = Submodule.span G.O (Set.range (f v s)) := by
      rw [hfrm, Formalism.L2.G.Cmp.dw_eq (IsFractionRing.injective G.O G.Kf) G.P.m _
        (LatticeSystems.kp_lamAt_antitone (G.P.lam0 v) (G.P.dom v) s) _ (hdet v s),
        deltaLTw_eq_span_framed_words _ _ (hdet v s)]
  let fV (v : Fin G.P.nV) (w : Fin (G.P.n' v) →
      List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ)) := ∏ s, blockEmb G.Kf s (f v s (w s))
  have hV (v : Fin G.P.nV) :
      HtenW G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (l v)) =
        Submodule.span G.O (Set.range (fV v)) := by
    unfold HtenW tensorLat
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨F,hF,rfl⟩
      apply product_mem_span_generators (fun s a => blockEmb G.Kf s (f v s a))
      intro s
      have hs := hF s
      dsimp only at hs
      rw [hslot] at hs
      exact map_span_range_algHom ((blockEmb G.Kf s).restrictScalars G.O) _ hs
    · rw [Submodule.span_le]
      rintro _ ⟨w,rfl⟩
      apply Submodule.subset_span
      refine ⟨fun s => f v s (w s), ?_, rfl⟩
      intro s
      dsimp only
      rw [hslot]
      exact Submodule.subset_span ⟨w s,rfl⟩
  unfold Places.HtupW Places.tenV
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨F,hF,rfl⟩
    apply product_mem_span_generators (fun v a => G.P.vEmb v (fV v a))
    intro v
    have hv := hF v
    dsimp only at hv
    rw [hV] at hv
    exact map_span_range_algHom ((G.P.vEmb v).restrictScalars G.O) _ hv
  · rw [Submodule.span_le]
    rintro _ ⟨w,rfl⟩
    apply Submodule.subset_span
    refine ⟨fun v => fV v (w v), ?_, rfl⟩
    intro v
    dsimp only
    rw [hV]
    exact Submodule.subset_span ⟨w v,rfl⟩

end

end GlobalTheory.EX.TypeIProduction
