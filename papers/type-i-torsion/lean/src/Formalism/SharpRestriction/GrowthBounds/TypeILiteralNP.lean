import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices

open scoped BigOperators Matrix
open Formalism.BasicNotions Formalism.MainNotions.G
open Formalism.MainNotions.G.LatticeSystems

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

/-- The first of the three literal submodules in the original NP definition. -/
def literalFirstSpan {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn := by
  classical
  let p := D.what₂.places.resChar w
  let G := D.gat u w hg
  let V := VV X K (aL L) (bL L) p
  exact Submodule.span G.O {F' | ∃ V' ⊆ V, ∃ F ∈ G.M,
    F' = yProd Y u w hg V' (((p : G.O) ^ (∑ t ∈ V \ V',
      ⌈Sv X K (aL L) (bL L) p t⌉.toNat)) • F)}

theorem literalNP_le_firstSpan {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    NP X Y K u w hg ≤ literalFirstSpan X Y K u w hg := fun _ h => h.1.1

private def orbitListEnd {p : ℕ} (G : GAtP p) {α : Type*}
    (f : α → Fin G.P.nV) (m : ℕ) (l : List α) : Module.End G.O G.Fn :=
  (l.map fun t => yEnd G (f t) ^ m).prod

private theorem orbitListEnd_apply {p : ℕ} (G : GAtP p) {α : Type*}
    (f : α → Fin G.P.nV) (m : ℕ) (l : List α) (F : G.Fn) :
    orbitListEnd G f m l F =
      (l.map (fun t => (G.yv (f t))^[m])).foldr (fun q q' => q ∘ q') id F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      change (yEnd G (f a) ^ m) (orbitListEnd G f m l F) = _
      rw [yEnd_pow_apply, ih]
      rfl

private theorem yIterate_mem {D : D7} {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (m : ℕ) (F : G.Fn) (hF : F ∈ G.M) :
    (yEnd G v ^ m) F ∈ G.M := by
  have hp := (Formalism.L2.G.Model.operators_preserve_lattices D G).2 v
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hF
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hp _ ih

private theorem orbitListEnd_mem {D : D7} {p : ℕ} (G : GAtP p) {α : Type*}
    (f : α → Fin G.P.nV) (m : ℕ) (l : List α) (F : G.Fn) (hF : F ∈ G.M) :
    orbitListEnd G f m l F ∈ G.M := by
  induction l with
  | nil => exact hF
  | cons a l ih =>
      change (yEnd G (f a) ^ m) (orbitListEnd G f m l F) ∈ G.M
      exact yIterate_mem (D := D) G (f a) m _ ih

private theorem orbitListEnd_mem_selected {D : D7} {p : ℕ} (G : GAtP p) {α : Type*}
    (f : α → Fin G.P.nV) (m : ℕ) (hm : 0 < m) (t : α) (l : List α) (ht : t ∈ l)
    (F : G.Fn) (hF : F ∈ G.M) :
    orbitListEnd G f m l F ∈ G.M.map (yEnd G (f t)) := by
  induction l with
  | nil => cases ht
  | cons a l ih =>
    change (yEnd G (f a) ^ m) (orbitListEnd G f m l F) ∈ G.M.map (yEnd G (f t))
    rcases List.mem_cons.mp ht with rfl | ht'
    · cases m with
      | zero => omega
      | succ m =>
        rw [pow_succ', Module.End.mul_apply]
        exact ⟨_, yIterate_mem (D := D) G (f t) m _
          (orbitListEnd_mem (D := D) G f _ l F hF), rfl⟩
    · obtain ⟨Z, hZ, eZ⟩ := ih ht'
      refine ⟨(yEnd G (f a) ^ m) Z, yIterate_mem (D := D) G (f a) m Z hZ, ?_⟩
      rw [← eZ]
      have hc := (yEnd_commute G (f a) (f t)).pow_left m
      exact (congrArg (fun A : Module.End G.O G.Fn => A Z) hc.eq).symm

/-- A retained orbit gives one actual neighbour operator. An omitted orbit supplies
its original scalar power. The argument covers every literal subset. -/
theorem literalFirstSpan_le_neighbour_add_scalar {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hm : 0 < D.R.m) (t : HH D)
    (ht : t ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w)) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let S := ⌈Sv X K (aL L) (bL L) p t⌉.toNat
    literalFirstSpan X Y K u w hg ≤
      G.M.map (yEnd G (Y.vOf u w hg t)) ⊔
        G.M.map (((p : G.O) ^ S) • LinearMap.id) := by
  classical
  intro p G S
  let f := Y.vOf u w hg
  unfold literalFirstSpan
  rw [Submodule.span_le]
  rintro _ ⟨V',hV',F,hF,rfl⟩
  let n := ∑ z ∈ VV X K (aL L) (bL L) p \ V',
    ⌈Sv X K (aL L) (bL L) p z⌉.toNat
  change yProd Y u w hg V' (((p : G.O)^n) • F) ∈ _
  rw [show ∀ A, yProd Y u w hg V' A = orbitListEnd G f D.R.m V'.toList A from
    fun A => (orbitListEnd_apply G f D.R.m V'.toList A).symm]
  by_cases ht' : t ∈ V'
  · apply Submodule.mem_sup_left
    exact orbitListEnd_mem_selected (D := D) G f D.R.m hm t V'.toList
      (Finset.mem_toList.mpr ht') _ (G.M.smul_mem _ hF)
  · apply Submodule.mem_sup_right
    have hn : S ≤ n := by
      unfold S n
      exact Finset.single_le_sum
        (f := fun b => ⌈Sv X K (aL L) (bL L) p b⌉.toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_sdiff.mpr ⟨ht,ht'⟩)
    let Z := orbitListEnd G f D.R.m V'.toList F
    have hZ : Z ∈ G.M := orbitListEnd_mem (D := D) G f _ _ F hF
    refine ⟨(p : G.O)^(n-S) • Z, G.M.smul_mem _ hZ, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_smul,
      ← pow_add, Nat.add_sub_of_le hn]

private theorem neighbour_eval_mem_prime_power {p : ℕ} (G : GAtP p)
    (v : Fin G.P.nV) (i : G.comp) (l : G.P.Tup) (hl : G.P.IsLatTup l) (R : ℕ)
    (Λ : G.P.Xsp →ₗ[G.Kf] G.Kf)
    (hEdge : ∀ L' (_ : IsEdge p (G.P.n' v) G.P.r ⟨L',l v⟩),
      ∀ F ∈ G.P.HtupW (Function.update l v L'),
        Λ (((p : G.Kf)^G.P.ArV v) • F) ∈
          (algebraMap G.O G.Kf '' (Ideal.span {(p : G.O)^R} : Set G.O)))
    (F : G.Fn) (hF : F ∈ G.M) :
    Λ (G.yv v F i l) ∈ Submodule.map (Algebra.linearMap G.O G.Kf) (Ideal.span {(p : G.O)^R}) := by
  classical
  change Λ (Level.yv (P := G.P) v (F i) l) ∈ _
  rw [ef_yv_eq, Finset.smul_sum, map_sum]
  apply Submodule.sum_mem
  intro L' hmem
  have he : IsEdge p (G.P.n' v) G.P.r ⟨L',l v⟩ := by
    simpa [ef_E] using hmem
  have hL : G.P.IsLatTup (Function.update l v L') := by
    intro a
    by_cases ha : a = v
    · subst a
      simpa [Function.update] using he.1
    · simpa [Function.update,ha] using hl a
  exact hEdge L' he _ (((jd_fmem G G.P.HtupW F).mp hF i).1 _ hL)

/-- The row on the original first span, with the actual neighbour sum and the
actual omitted-orbit depth. The chart row premise is the native predecessor test. -/
theorem literalFirstSpan_eval_mem_prime_power {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hm : 0 < D.R.m) (t : HH D)
    (ht : t ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w)) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let v := Y.vOf u w hg t
    ∀ (i : G.comp) (l : G.P.Tup) (hl : G.P.IsLatTup l) (R : ℕ)
      (hR : R ≤ ⌈Sv X K (aL L) (bL L) p t⌉.toNat)
      (Λ : G.P.Xsp →ₗ[G.Kf] G.Kf)
      (hInt : ∀ F ∈ G.P.HtupW l, Λ F ∈ Set.range (algebraMap G.O G.Kf))
      (hEdge : ∀ L' (_ : IsEdge p (G.P.n' v) G.P.r ⟨L',l v⟩),
        ∀ F ∈ G.P.HtupW (Function.update l v L'),
          Λ (((p : G.Kf)^G.P.ArV v) • F) ∈
            (algebraMap G.O G.Kf '' (Ideal.span {(p : G.O)^R} : Set G.O))),
      ∀ F ∈ literalFirstSpan X Y K u w hg,
        Λ (F i l) ∈ (algebraMap G.O G.Kf '' (Ideal.span {(p : G.O)^R} : Set G.O)) := by
  intro p G v i l hl R hR Λ hInt hEdge F hF
  let J : Submodule G.O G.Kf :=
    Submodule.map (Algebra.linearMap G.O G.Kf) (Ideal.span {(p : G.O)^R})
  change Λ (F i l) ∈ J
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp
    (literalFirstSpan_le_neighbour_add_scalar X Y K u w hg hm t ht hF)
  have hx' : Λ (x i l) ∈ J := by
    obtain ⟨a,ha,rfl⟩ := Submodule.mem_map.mp hx
    exact neighbour_eval_mem_prime_power G v i l hl R Λ hEdge a ha
  have hy' : Λ (y i l) ∈ J := by
    obtain ⟨b,hb,rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨a,ha⟩ := hInt (b i l) (((jd_fmem G G.P.HtupW b).mp hb i).1 l hl)
    let S := ⌈Sv X K (aL L) (bL L) p t⌉.toNat
    change Λ ((((p : G.O)^S) • b) i l) ∈ J
    obtain ⟨c,hc⟩ := pow_dvd_pow (p : G.O) hR
    refine ⟨(p : G.O)^S * a, Ideal.mem_span_singleton.mpr ⟨c*a, by
      change (p : G.O)^S * a = _; rw [hc,mul_assoc]⟩, ?_⟩
    change algebraMap G.O G.Kf ((p : G.O)^S * a) = Λ (((p : G.O)^S) • b i l)
    rw [LinearMap.map_smul_of_tower Λ, Algebra.smul_def, map_mul, ha]
  change Λ (x i l + y i l) ∈ J
  rw [map_add]
  exact J.add_mem hx' hy'

/-- A uniform local killing power from the same empty subset that occurs in NP. -/
theorem literalNP_pow_mem_of_empty_word {D : D7} {L : SizeData₂ D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    let B := ∑ t ∈ VV X K (aL L) (bL L) p, ⌈Sv X K (aL L) (bL L) p t⌉.toNat
    ∀ F ∈ G.M ⊓ Y.Vram u w hg, ∀ n : ℕ, B ≤ n → T ≤ n →
      ((p : G.O)^n) • F ∈ NP X Y K u w hg := by
  classical
  intro p G T B F hF n hB hT
  have hpow (k : ℕ) (hk : k ≤ n) :
      ((p : G.O)^k) • (((p : G.O)^(n-k)) • F) = ((p : G.O)^n) • F := by
    rw [smul_smul, ← pow_add, Nat.add_sub_of_le hk]
  unfold NP
  refine ⟨⟨?_, ?_⟩, (Y.Vram u w hg).smul_mem _ hF.2⟩
  · apply Submodule.subset_span
    refine ⟨∅, Finset.empty_subset _, ((p : G.O)^(n-B)) • F, G.M.smul_mem _ hF.1, ?_⟩
    simpa [yProd, B, p] using (hpow B hB).symm
  · refine Submodule.mem_map.mpr ⟨((p : G.O)^(n-T)) • F, G.M.smul_mem _ hF.1, ?_⟩
    exact hpow T hT

end

end GlobalTheory.EX.TypeIProduction
