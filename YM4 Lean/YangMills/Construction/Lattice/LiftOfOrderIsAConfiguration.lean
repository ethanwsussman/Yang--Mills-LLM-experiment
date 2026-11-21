import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LiftOfOrder
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def OrderLiftIsGaugeField : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ j k : ℕ, j ≤ k → k ≤ K →
  ∀ 𝒞 : Set (BondAtLevel L m K k), IsReversalClosed 𝒞 →
  ∀ V : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsGaugeField complexGaugeGroup 𝒞 V →
    ((∀ (y : SiteAtLevel L m K k) (b : BondAtLevel L m K j),
        IsInsideBlockAt j y b → IsInsideBlockAt j y b.opposite) ∧
      ∀ (b : BondAtLevel L m K j) (c : BondAtLevel L m K k),
        CoversBond c b → CoversBond c.opposite b.opposite) ∧
    (IsReversalClosed (bondsInsideOrOverCoarse j 𝒞) ∧
      (∀ b ∈ bondsInsideOrOverCoarse j 𝒞, orderLift j V b.opposite = (orderLift j V b)⁻¹) ∧
      IsGaugeField complexGaugeGroup (bondsInsideOrOverCoarse j 𝒞) (orderLift j V) ∧
      (IsGaugeField compactGaugeGroup 𝒞 V →
        IsGaugeField compactGaugeGroup (bondsInsideOrOverCoarse j 𝒞) (orderLift j V))) ∧
    (𝒞 = univ →
      bondsInsideOrOverCoarse j 𝒞 = univ ∧
        (V ∈ gaugeFieldsAtLevel L m K k → orderLift j V ∈ gaugeFieldsAtLevel L m K j))
end YangMills.Construction.PeriodicLattice
end
