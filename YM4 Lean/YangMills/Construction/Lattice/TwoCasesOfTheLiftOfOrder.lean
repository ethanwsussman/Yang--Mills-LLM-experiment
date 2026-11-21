import YangMills.Construction.Lattice.CoarseBlockCentres
import YangMills.Construction.Lattice.LiftOfOrder
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def IsInsideSomeBlock (k : ℕ) {j : ℕ} (b : BondAtLevel L m K j) : Prop :=
  ∃ y : SiteAtLevel L m K k, IsInsideBlockAt j y b
def OrderLiftCases : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  (∀ j k : ℕ, j ≤ k → k ≤ K →
    (∀ (b : BondAtLevel L m K j) (c : BondAtLevel L m K k), CoversBond c b →
      c.source = coarseCentre j k b.source ∧ c.target = coarseCentre j k b.target) ∧
    (∀ (b : BondAtLevel L m K j) (c c' : BondAtLevel L m K k),
      CoversBond c b → CoversBond c' b → c = c') ∧
    (∀ b : BondAtLevel L m K j, IsInsideSomeBlock k b →
      ∀ c : BondAtLevel L m K k, ¬CoversBond c b) ∧
    ∀ (𝒞 : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2),
      IsReversalClosed 𝒞 → IsGaugeField complexGaugeGroup 𝒞 V →
      ∀ b ∈ bondsInsideOrOverCoarse j 𝒞,
        ¬(IsInsideSomeBlock k b ∧ ∃ c ∈ 𝒞, CoversBond c b) ∧
        (IsInsideSomeBlock k b ∨ ∃ c ∈ 𝒞, CoversBond c b) ∧
        ((∃ c ∈ 𝒞, CoversBond c b) → ∃! c, c ∈ 𝒞 ∧ CoversBond c b) ∧
        (IsInsideSomeBlock k b → orderLift j V b = 1) ∧
        (∀ c ∈ 𝒞, CoversBond c b → orderLift j V b = V c) ∧
        orderLift j V b ∈ complexGaugeGroup) ∧
  ∀ k : ℕ, k ≤ K →
    (∀ x : SiteAtLevel L m K k,
      coarseCentre k k x = x ∧ blockAtLevel k x = {(x : FourTorus L m)}) ∧
    (∀ b : BondAtLevel L m K k, ¬IsInsideSomeBlock k b) ∧
    (∀ b c : BondAtLevel L m K k, CoversBond c b ↔ c = b) ∧
    ∀ (𝒞 : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2),
      IsReversalClosed 𝒞 → IsGaugeField complexGaugeGroup 𝒞 V →
      bondsInsideOrOverCoarse k 𝒞 = 𝒞 ∧ ∀ b ∈ 𝒞, orderLift k V b = V b
end YangMills.Construction.PeriodicLattice
