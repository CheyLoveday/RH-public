import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.GroupActionMulSingleEqDilation
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdmissibleStabilisersOfCompatibleForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms
open Classical

section Product

variable {ι H K V W : Type*} [DecidableEq ι] [CommGroup H] [Fintype H]
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  (ρ : (ι → H) →* Module.End K V) (sign : ι → H)

private def diff : List ι → V → V
  | [], b => b
  | j :: js, b =>
    let y := diff js b
    y - ρ (Pi.mulSingle j (sign j)) y

private def fullNorm (j : ι) (b : V) : V := ∑ a : H, ρ (Pi.mulSingle j a) b

private theorem fullNorm_mulSingle (j : ι) (h : H) (b : V) :
    fullNorm ρ j (ρ (Pi.mulSingle j h) b) = fullNorm ρ j b := by
  unfold fullNorm
  calc
    _ = ∑ a : H, ρ (Pi.mulSingle j (a * h)) b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Pi.mulSingle_mul, map_mul]
      rfl
    _ = _ := Equiv.sum_comp (Equiv.mulRight h) (fun a => ρ (Pi.mulSingle j a) b)

private theorem fullNorm_translate (j : ι) (g : ι → H) (b : V) :
    fullNorm ρ j (ρ g b) = ρ g (fullNorm ρ j b) := by
  unfold fullNorm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (ρ (Pi.mulSingle j a) * ρ g) b = (ρ g * ρ (Pi.mulSingle j a)) b
  rw [← map_mul, ← map_mul, mul_comm]

private theorem norm_diff (j : ι) (js : List ι) (hj : j ∈ js) (b : V) :
    fullNorm ρ j (diff ρ sign js b) = 0 := by
  induction js with
  | nil => simp at hj
  | cons k ks ih =>
    have sub (x y : V) : fullNorm ρ j (x - y) = fullNorm ρ j x - fullNorm ρ j y := by
      simp only [fullNorm, map_sub, Finset.sum_sub_distrib]
    rw [diff, sub]
    rcases List.mem_cons.mp hj with rfl | h
    · rw [fullNorm_mulSingle, sub_self]
    · rw [fullNorm_translate, ih h, map_zero, sub_self]

omit [Fintype H] in
/-- At each induction step, the unused coordinates of the translating group element are one. -/
private theorem eval_diff (ev : V →+ W) (b : V) (hsign : ∀ j, sign j ≠ 1)
    (hoff : ∀ g : ι → H, g ≠ 1 → ev (ρ g b) = 0) (js : List ι) (hd : js.Nodup)
    (g : ι → H) (hg : ∀ j ∈ js, g j = 1) :
    ev (ρ g (diff ρ sign js b)) = ev (ρ g b) := by
  induction js generalizing g with
  | nil => rfl
  | cons j js ih =>
    obtain ⟨hj, hjs⟩ := List.nodup_cons.mp hd
    let t : ι → H := Pi.mulSingle j (sign j)
    have hgj := hg j List.mem_cons_self
    have ht : g * t ≠ 1 := by
      intro eq
      have he := congrFun eq j
      exact hsign j (by simpa [t, hgj] using he)
    have htail : ∀ k ∈ js, (g * t) k = 1 := by
      intro k hk
      have hkj : k ≠ j := fun e => hj (e ▸ hk)
      simp [t, hg k (List.mem_cons_of_mem _ hk), Pi.mulSingle_eq_of_ne hkj]
    have comp (x : V) : ρ g (ρ t x) = ρ (g * t) x := by rw [map_mul]; rfl
    change ev (ρ g (diff ρ sign js b - ρ t (diff ρ sign js b))) = _
    rw [map_sub, map_sub, comp, ih hjs g (fun k hk => hg k (List.mem_cons_of_mem _ hk)),
      ih hjs (g * t) htail, hoff _ ht, sub_zero]

end Product

variable {D : D7} {u : D.what₂.Word}

private abbrev WordLat (D : D7) (u : D.what₂.Word) := ↥(((D.fm u).lat 0).L)

private def signLift (j : (D.mem u).A.vT) (b : WordLat D u) : WordLat D u :=
  let h := (D.fm u).rhoT_lat j (-1) b.1 b.2
  ⟨h.choose, h.choose_spec.1⟩

/-- Apply the integral factors (1 − Dⱼ) in the given order. -/
def integralSignDifferences (js : List (D.mem u).A.vT) (b : ↥(((D.fm u).lat 0).L)) :
    ↥(((D.fm u).lat 0).L) :=
  js.foldr (fun j y => y - signLift j y) b

private def embedded (Tf : Forms0 D u) (b : WordLat D u) : (D.mem u).A.Mu0 :=
  ⟨(D.fm u).emb 0 b.1, by
    rw [← (D.fm u).Fi_zero]
    exact ((Tf.val0.rat _).mp ⟨b.1, rfl⟩).1⟩

private theorem embedded_diff [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u)
    (hE : DiamondElementsExist Tf) (js : List (D.mem u).A.vT) (b : WordLat D u) :
    embedded Tf (integralSignDifferences js b) =
      diff (t2xRho Tf hE) (fun j => t2xU j (-1)) js (embedded Tf b) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    let y := integralSignDifferences js b
    rw [diff, ← ih]
    apply Subtype.ext
    change (D.fm u).emb 0 (y.1 - (signLift j y).1) =
      (D.fm u).emb 0 y.1 - ((t2xRho Tf hE (Pi.mulSingle j (t2xU j (-1))) (embedded Tf y)).1)
    rw [map_sub, group_rep_mulSingle_eq_rho, MulEquiv.symm_apply_apply]
    exact congrArg (fun z => (D.fm u).emb 0 y.1 - z) ((D.fm u).rhoT_lat j (-1) y.1 y.2).choose_spec.2

private theorem zero_on_translate [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u)
    (hE : DiamondElementsExist Tf) (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ)
    (c : (D.mem u).C.cls 0) (b : (D.mem u).A.Mu0)
    (hz : b.1 (t2xAc Tf hE g c) = 0) : (t2xRho Tf hE g b).1 c = 0 := by
  have hr : t2xRho Tf hE g⁻¹ (t2xRho Tf hE g b) = b := by
    change (t2xRho Tf hE g⁻¹ * t2xRho Tf hE g) b = b
    rw [← map_mul, inv_mul_cancel, map_one]; rfl
  have ha : t2xAc Tf hE g⁻¹ (t2xAc Tf hE g c) = c := by
    change (t2xAc Tf hE g⁻¹ * t2xAc Tf hE g) c = c
    rw [← map_mul, inv_mul_cancel, map_one]; rfl
  have h := zero_of_group_action_zero Tf hE g⁻¹ (t2xAc Tf hE g c) (t2xRho Tf hE g b)
    (by rw [hr]; exact hz)
  rwa [ha] at h

/-- Each tame coordinate occurs once. The integral sign differences preserve every frame at the
supported class and satisfy all full tame norm equations. -/
theorem integralSignDifferences_ramL_restrict (Tf : Forms0 D u) (c : (D.mem u).C.cls 0)
    (b : ↥(((D.fm u).lat 0).L)) (hsupp : ∀ c' ≠ c, (D.fm u).emb 0 b.1 c' = 0)
    (js : List (D.mem u).A.vT) (hd : js.Nodup) (hall : ∀ j, j ∈ js) :
    (integralSignDifferences js b).1 ∈ (D.fm u).ramL ∧
      (D.fm u).emb 0 (integralSignDifferences js b).1 c = (D.fm u).emb 0 b.1 c := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  let hE := diamond_elements_exist_all Tf
  let ρ := t2xRho Tf hE
  let sign := fun j : (D.mem u).A.vT => t2xU j (-1)
  let y := integralSignDifferences js b
  have he : embedded Tf y = diff ρ sign js (embedded Tf b) := embedded_diff Tf hE js b
  constructor
  · refine ⟨y.2, (embedded Tf y).2, (Submodule.mem_iInf _).mpr fun j => ?_⟩
    change (D.mem u).A.Nm j (embedded Tf y).1 = 0
    have hn : fullNorm ρ j (embedded Tf y) = 0 := he ▸ norm_diff ρ sign j js (hall j) _
    change (∑ a : ((D.mem u).A.Fv j)ˣ, (D.mem u).A.rhoT j a) (embedded Tf y).1 = 0
    rw [LinearMap.sum_apply]
    calc
      _ = ∑ a : ((D.mem u).A.Fv j)ˣ,
          (ρ (Pi.mulSingle j (t2xU j a)) (embedded Tf y)).1 := by
        apply Finset.sum_congr rfl
        intro a _
        simp [ρ, group_rep_mulSingle_eq_rho]
      _ = ∑ a : (ZMod (D.mem u).A.T)ˣ, (ρ (Pi.mulSingle j a) (embedded Tf y)).1 :=
        Equiv.sum_comp (t2xU j).toEquiv
          (fun a : (ZMod (D.mem u).A.T)ˣ => (ρ (Pi.mulSingle j a) (embedded Tf y)).1)
      _ = 0 := by
        simpa only [fullNorm, Submodule.coe_sum, ZeroMemClass.coe_zero] using congrArg Subtype.val hn
  · let ev : (D.mem u).A.Mu0 →+ ((D.mem u).C.Y 0 → ℂ) :=
      { toFun := fun f => f.1 c, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hsign (j : (D.mem u).A.vT) : sign j ≠ 1 := by
      intro h
      have hu : (-1 : ((D.mem u).A.Fv j)ˣ) = 1 := (t2xU j).injective (h.trans (map_one _).symm)
      have hf : (-1 : (D.mem u).A.Fv j) = 1 := congrArg Units.val hu
      have h2 := two_ne_zero_odd_prime_field (G := (D.mem u).A.Fv j) (D.mem u).A.T_prime
        ((Nat.card_eq_fintype_card).trans ((D.mem u).A.card_Fv j)) (D.T_ne_two u)
      exact h2 (by linear_combination -hf)
    have hOff (g) (hg : g ≠ 1) : ev (ρ g (embedded Tf b)) = 0 := by
      apply zero_on_translate Tf hE
      exact hsupp _ (fun h => hg (group_acts_freely_classes Tf
        (admissible_stabilisers_of_compatible_forms Tf) hE g c h))
    have hv := eval_diff ρ sign ev (embedded Tf b) hsign hOff js hd 1 (fun _ _ => rfl)
    change ev (embedded Tf y) = ev (embedded Tf b)
    simpa only [← he, map_one, one_apply_eq_self] using hv

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0
