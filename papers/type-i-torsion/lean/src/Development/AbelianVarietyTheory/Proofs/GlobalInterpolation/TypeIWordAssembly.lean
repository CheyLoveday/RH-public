import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.F6SeedBridge
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FamilyServedOrder

noncomputable section

namespace GlobalTheory.EX.TypeIProduction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G
open Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Matrix

/-- Evaluate the actual integral model at a valid output tuple, with the target restricted
to its native integral coefficient lattice. -/
def integralCoefficientAt {p : ℕ} (G : GAtP p) (i : G.comp)
    (l : G.P.Tup) (hl : G.P.IsLatTup l) : ↥G.M →ₗ[G.O] ↥(G.P.HtupW l) where
  toFun F := ⟨F.1 i l, ((LatticeSystems.jd_fmem G G.P.HtupW F.1).mp F.2 i).1 l hl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A primitive coefficient row of the given depth on a fixed served word gives actual
torsion. The construction produces both the unit global seed and its finite order. -/
theorem servedWord_fromCoefficient {D : D7} {L : SizeData₂ D} {Gt : GatTies D}
    (X : Inst D L) (Y : LatInst D) (K : Consts) (cmp : LatCmp D)
    (served : cmp.NuServedDef X Y K) (H : GroupCompatibilityAll D Gt cmp)
    (u : D.what₂.Word) (hCom : Lnk.NuCommens D L) (hN : L.NuLat u ≤ DV.MramL D u)
    (w : {w : D.what₂.places.Pl // w ∈ L.supp ∧ D.what₂.places.resChar w ≠ (D.mem u).A.T})
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w.1))
    (orbit : {t₀ : HH D // t₀ ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w.1)}) :
    let p := D.what₂.places.resChar w.1
    let G := D.gat u w.1 hg
    let A := DV.MramL D u
    let U := (L.NuLat u).comap A.subtype
    let T := ⌈tauP X K (aL L) (bL L) p⌉.toNat
    ∀ (i : G.comp) (l : G.P.Tup) (hl : G.P.IsLatTup l)
      (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)),
    (∀ v, l v = colSpan (G.P.W v) (g v : Matrix _ _ (G.P.Qq v))) →
    ∀ (R : ℕ) (coeff : ↥(G.P.HtupW l) →ₗ[G.O] G.O) (ξ : ↥(G.P.HtupW l)), IsUnit (coeff ξ) →
    let row := coeff.comp (integralCoefficientAt G i l hl)
    let I : Ideal G.O := Ideal.span {((p : G.O) ^ R)}
    (∀ b : ↥G.M, b.1 ∈ NP X Y K u w.1 hg → row b ∈ I) →
    ∃ z : A,
      let q := U.mkQ z
      let m := addOrderOf q
      IsUnit (row (wordRamifiedImage cmp u w.1 hg z)) ∧ m ≠ 0 ∧
      p ^ R ∣ m ∧ addOrderOf ((m / p ^ R) • q) = p ^ R ∧
      (T + 1 ≤ R → addOrderOf ((m / p ^ (T + 1)) • q) = p ^ (T + 1)) := by
  intro p G A U T i l hl g hgl R coeff ξ hξ row I hRow
  obtain ⟨z, hz, hu⟩ := exists_word_numerator_unit H u w.1 hg i l hl g hgl coeff ξ hξ
  have hUnit : IsUnit (row (wordRamifiedImage cmp u w.1 hg z)) := hu
  have hFinite := wordOrder_ne_zero_of_nuCommens hCom u z
  obtain ⟨_, _, _, _, hdiv, hexact, hsmaller⟩ := servedData_primePowerOrders
    X Y K cmp served u w hg orbit R row z hN hRow hUnit hFinite
  exact ⟨z, hUnit, hFinite, hdiv, hexact, hsmaller⟩

end GlobalTheory.EX.TypeIProduction
