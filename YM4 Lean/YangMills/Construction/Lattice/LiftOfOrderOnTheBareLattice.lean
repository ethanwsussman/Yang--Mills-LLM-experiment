import YangMills.Construction.Lattice.ConsistencyOfLiftsAndAveragesSetting
import YangMills.Construction.Lattice.LiftOfOrder
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def BareOrderLiftEqBareLift : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ k : ℕ, 1 ≤ k → k ≤ K →
  ∀ (𝒞 : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2),
    IsReversalClosed 𝒞 → IsComplexGaugeField 𝒞 V →
    (∀ b : BondAtLevel L m K 0,
      (∃ y : SiteAtLevel L m K k, IsInsideBlockAt 0 y b) ↔ EndsInOneBlock k b) ∧
    (∀ b : BondAtLevel L m K 0, EndsInOneBlock k b →
      orderLift 0 V b = 1 ∧ bareLift V b = 1) ∧
    (∀ b : BondAtLevel L m K 0, ∀ c ∈ 𝒞, CoversBond c b →
      orderLift 0 V b = V c ∧ bareLift V b = V c) ∧
    bondsInsideOrOverCoarse 0 𝒞 = liftSupport 0 𝒞 ∧
    liftSupport 0 𝒞 =
      {b : BondAtLevel L m K 0 | ∀ c : BondAtLevel L m K k, CoversBond c b → c ∈ 𝒞} ∧
    ∀ b ∈ bondsInsideOrOverCoarse 0 𝒞, orderLift 0 V b = bareLift V b
end YangMills.Construction.PeriodicLattice
