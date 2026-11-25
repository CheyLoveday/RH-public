import Formalism.SharpRestriction.GrowthBounds.TypeINativeShearUnit

open scoped BigOperators Matrix Classical
open Matrix MvPolynomial
open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems
open Formalism.GradedWeylDivisibility Formalism.GradedWeylDivisibility.TypeI

namespace GlobalTheory.EX.TypeIProduction

noncomputable section

abbrev NativeWords {p : ℕ} (G : GAtP p) :=
  (v : Fin G.P.nV) → Fin (G.P.n' v) → List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ)

def nativeEdgeFrames {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (a : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.W v)) :
    (u : Fin G.P.nV) → Fin (G.P.n' u) → Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf :=
  Function.update (fun _ _ => 1) v (fun s =>
    (a.map (integralFrobeniusIter G v s.val)).map ((algebraMap G.O G.Kf).comp (G.P.j v)) *
      rankOnePole 0 (p : G.Kf))

/-- The common weight has its native unit output at the empty word in the
constant shear frame. On an incoming ordered word, its fully normalized
coefficient sum is a multiple of the rational prime power in the one W-ring. -/
theorem exists_common_word_readout {p : ℕ} (G : GAtP p) (v : Fin G.P.nV)
    (s : Fin (G.P.n' v)) (R : ℕ) (hm : 0 < G.P.m)
    (hc : TypeIAdjacentCapacity G v s R) :
    let line : NativeFlagSlot G := if IsTypeV s then ⟨v,s⟩ else ⟨v,posAdd s 1⟩
    ∃ l : NativeFlagLabels G → ℤ,
      (∑ I : NativeFlagLabels G, (l I : G.Kf) *
        ∏ b : NativeFlagSlot G,
          (flagProducts (NativeFlagWeight G b)
            (wordFlag (constantShearFrame G line b.1 b.2)⁻¹ᵀ []) (I b)).coeff
              (wordExponent ([] : List (Fin (G.P.m+1) × Fin (G.P.m+1) × ℕ)))) = 1 ∧
      ∀ (a : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) (G.P.W v)) (ha : IsUnit a.det)
        (w : NativeWords G),
        let f := (algebraMap G.O G.Kf).comp (G.P.j v)
        let g := nativeEdgeFrames G v a
        let scale (b : NativeFlagSlot G) : G.Kf := if b.1 = v then (p : G.Kf) else 1
        ∃ J : G.P.W v, (p : G.P.W v)^R ∣ J ∧
          f J = (∏ b : NativeFlagSlot G, (scale b)^(Fintype.card (FlagCopies (NativeFlagWeight G b)))) *
            ∑ I : NativeFlagLabels G, (l I : G.Kf) *
              ∏ b : NativeFlagSlot G,
                (flagProducts (NativeFlagWeight G b) (wordFlag (g b.1 b.2)⁻¹ᵀ (w b.1 b.2)) (I b)).coeff
                  (wordExponent (w b.1 b.2)) := by
  classical
  intro line
  obtain ⟨weight,hUnit,hDiv⟩ := exists_fixed_native_weight G v s R hm hc
  let e : NativeFlagLabels G ≃ NativeFlatRows G :=
    { toFun := fun A b => A b.1 b.2
      invFun := fun A i j => A ⟨i,j⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let l (I : NativeFlagLabels G) := weight (e I)
  refine ⟨l,?_,?_⟩
  · simp_rw [native_constant_shear_word_coefficient G line hm]
    unfold flagProducts
    refine Eq.trans ?_ hUnit
    refine Fintype.sum_equiv e _ _ ?_
    intro I
    refine congrArg (fun x : G.Kf => (weight (e I) : G.Kf) * x) ?_
    exact (Fintype.prod_sigma (fun b : NativeMinorLabel G =>
      flagMinor (Nat.succ_le_of_lt b.2.1.isLt)
        (if b.1 = line then lineShear G.Kf 1 else 1) (e I b))).symm
  · intro a ha w f g scale
    let W := G.P.W v
    let σ (b : NativeFlagSlot G) := WordParameter (w b.1 b.2).length
    let q (b : NativeFlagSlot G) := MvPolynomial.map (σ := σ b) f
    let flag (b : NativeFlagSlot G) := wordFlag (g b.1 b.2)⁻¹ᵀ (w b.1 b.2)
    have hpMap : f (p : W) = (p : G.Kf) := map_natCast f p
    have hpK : (p : G.Kf) ≠ 0 := by simpa only [map_natCast] using kp_p_ne_zero G v
    have hLift (b : NativeFlagSlot G) (j : FlagCopies (NativeFlagWeight G b))
        (I : FlagRows (G.P.m+1) (j.1.val+1)) :
        ∃ P : MvPolynomial (σ b) W,
          q b P = C (scale b) * flagMinor (Nat.succ_le_of_lt j.1.isLt) (flag b) I := by
      obtain ⟨u,t⟩ := b
      by_cases h : u = v
      · subst u
        let a' := a.map (integralFrobeniusIter G v t.val)
        have hdet : IsUnit a'.det :=
          ((integralFrobeniusIter G v t.val).map_det a) ▸ ha.map _
        obtain ⟨P,hP⟩ := scaled_word_minor_has_lift f (p : W) (hpMap.symm ▸ hpK) 0
          a' hdet (w v t) (Nat.succ_le_of_lt j.1.isLt) I
        refine ⟨P,?_⟩
        simpa only [q,scale,ite_true,flag,g,nativeEdgeFrames,Function.update_self,a',hpMap] using hP
      · let P := flagMinor (Nat.succ_le_of_lt j.1.isLt) (orderedMatrix W (w u t)) I
        refine ⟨P,?_⟩
        have hone : (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)⁻¹ = 1 :=
          Matrix.inv_eq_left_inv (by simp)
        simp only [q,P,map_flagMinor,scale,h,ite_false,map_one,one_mul,flag,g,
          nativeEdgeFrames,Function.update_of_ne h,hone,Matrix.transpose_one,wordFlag,
          Matrix.map_one _ (map_zero _) (map_one _)]
        exact congrArg (fun A => flagMinor (Nat.succ_le_of_lt j.1.isLt) A I)
          (map_orderedMatrix f (w u t))
    choose P hP using hLift
    let B (b : NativeFlagSlot G) (I : NativeFlagLabels G) := ∏ j, P b j (I b j)
    let renW (b : NativeFlagSlot G) := (rename (R := W) (Sigma.mk b : σ b → Sigma σ)).toRingHom
    let renK (b : NativeFlagSlot G) := (rename (R := G.Kf) (Sigma.mk b : σ b → Sigma σ)).toRingHom
    let X (b : NativeFlagSlot G) := (orderedMatrix W (w b.1 b.2)).map (renW b)
    let F (b : NativeMinorLabel G) (I : FlagRows (G.P.m+1) (b.2.1.val+1)) :=
      renW b.1 (P b.1 b.2 I)
    let qAll := MvPolynomial.map (σ := Sigma σ) f
    letI : IsFractionRing W (G.P.Qq v) := (G.P.setting v).frac_alt
    have hFi : Function.Injective f := by
      intro x y h
      apply IsFractionRing.injective W (G.P.Qq v)
      apply (G.P.ι v).injective
      exact (((G.P.setting v).ι_comp x).trans h).trans ((G.P.setting v).ι_comp y).symm
    have hNorm (b : NativeMinorLabel G) (I : FlagRows (G.P.m+1) (b.2.1.val+1)) :
        qAll (F b I) = C (scale b.1) *
          flagMinor (Nat.succ_le_of_lt b.2.1.isLt) ((flag b.1).map (renK b.1)) I := by
      change MvPolynomial.map f (rename (Sigma.mk b.1) (P b.1 b.2 I)) = _
      rw [MvPolynomial.map_rename]
      change renK b.1 (q b.1 (P b.1 b.2 I)) = _
      rw [hP,map_mul,map_flagMinor]
      rw [show renK b.1 (C (scale b.1)) = C (scale b.1) from rename_C _ _]
    have hMapFlag (b : NativeFlagSlot G) :
        (flag b).map (renK b) =
          if h : b.1 = v then
            (((a.map (integralFrobeniusIter G v b.2.val)).map f * rankOnePole 0 (p : G.Kf))⁻¹ᵀ).map
              (MvPolynomial.C : G.Kf →+* MvPolynomial (Sigma σ) G.Kf) * (X b).map qAll
          else (X b).map qAll := by
      obtain ⟨u,t⟩ := b
      have hX : (orderedMatrix G.Kf (w u t)).map (renK ⟨u,t⟩) = (X ⟨u,t⟩).map qAll := by
        apply Matrix.ext
        intro i j
        change renK ⟨u,t⟩ (orderedMatrix G.Kf (w u t) i j) =
          MvPolynomial.map f (rename (Sigma.mk ⟨u,t⟩) (orderedMatrix W (w u t) i j))
        rw [map_rename]
        exact congrArg (renK ⟨u,t⟩) (congrArg (fun M => M i j) (map_orderedMatrix f (w u t))).symm
      by_cases h : u = v
      · subst u
        simp only [flag,wordFlag,Matrix.map_mul,g,nativeEdgeFrames,Function.update_self,dite_true]
        rw [hX]
        congr 1
        apply Matrix.ext
        intro i j
        exact rename_C _ _
      · have hone : (1 : Matrix (Fin (G.P.m+1)) (Fin (G.P.m+1)) G.Kf)⁻¹ = 1 :=
          Matrix.inv_eq_left_inv (by simp)
        simpa only [flag,g,nativeEdgeFrames,Function.update_of_ne h,show (⟨u,t⟩ : NativeFlagSlot G).1 ≠ v from h,
          dite_false,hone,Matrix.transpose_one,wordFlag,Matrix.map_one _ (map_zero _) (map_one _),Matrix.one_mul]
          using hX
    have hScale (b : NativeFlagSlot G) :
        C (scale b) = if b.1 = v then C (p : G.Kf) else (1 : MvPolynomial (Sigma σ) G.Kf) := by
      by_cases h : b.1 = v <;> simp [scale,h]
    have hDivF := hDiv a ha X F (MvPolynomial.map_injective f hFi)
      (fun b I => (hNorm b I).trans
        (congrArg₂ (· * ·) (hScale b.1)
          (congrArg (fun A => flagMinor (Nat.succ_le_of_lt b.2.1.isLt) A I) (hMapFlag b.1))))
    have hPacked : (C (p : W))^R ∣
        ∑ I : NativeFlagLabels G, (l I : W) • packFlagBlocks (fun b => B b I) := by
      obtain ⟨Q,hQ⟩ := hDivF
      refine ⟨Q,?_⟩
      refine Eq.trans ?_ hQ
      simp only [Algebra.smul_def, map_intCast, packFlagBlocks, B, map_prod]
      refine Fintype.sum_equiv e _ _ ?_
      intro I
      refine congrArg (fun x : MvPolynomial (Sigma σ) W => (weight (e I) : MvPolynomial (Sigma σ) W) * x) ?_
      exact (Fintype.prod_sigma (fun b : NativeMinorLabel G => F b (e I b))).symm
    let exp (b : NativeFlagSlot G) := wordExponent (w b.1 b.2)
    have hDivRead := marked_normalized_word_coeff_dvd σ (p : W) R l B exp hPacked
    refine ⟨∑ I : NativeFlagLabels G, (l I : W) * ∏ b, (B b I).coeff (exp b),hDivRead,?_⟩
    have hCoeff (b : NativeFlagSlot G) (I : NativeFlagLabels G) :
        f ((B b I).coeff (exp b)) =
          (scale b)^(Fintype.card (FlagCopies (NativeFlagWeight G b))) *
            (flagProducts (NativeFlagWeight G b) (flag b) (I b)).coeff (exp b) := by
      have hProd : q b (B b I) =
          C ((scale b)^(Fintype.card (FlagCopies (NativeFlagWeight G b)))) *
            flagProducts (NativeFlagWeight G b) (flag b) (I b) := by
        unfold B flagProducts
        simp only [map_prod,hP,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,map_pow]
      change _ = _
      rw [← MvPolynomial.coeff_map, hProd, MvPolynomial.coeff_C_mul]
    change f _ = _
    simp only [map_sum,map_mul,map_intCast,map_prod,hCoeff,Finset.prod_mul_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    ring

end

end GlobalTheory.EX.TypeIProduction
