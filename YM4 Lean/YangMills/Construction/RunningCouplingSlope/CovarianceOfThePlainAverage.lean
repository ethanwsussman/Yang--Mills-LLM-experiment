import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open YangMills.Construction.Tower
def ContourMeanGaugeCovariant : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    ∀ v : Vertex L n k j → Matrices.ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.complexGaugeGroup) →
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      contourMean (PeriodicLattice.gaugeTransform v V) c =
          v (c.source.toSublattice (PeriodicLattice.levelDepth k j)) * contourMean V c *
            (v (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹ ∧
      meanRadius (PeriodicLattice.gaugeTransform v V) c = meanRadius V c ∧
      normalizedMean (PeriodicLattice.gaugeTransform v V) c =
        v (c.source.toSublattice (PeriodicLattice.levelDepth k j)) * normalizedMean V c *
          (v (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹
end RunningCouplingSlope
end YangMills.Construction
end
