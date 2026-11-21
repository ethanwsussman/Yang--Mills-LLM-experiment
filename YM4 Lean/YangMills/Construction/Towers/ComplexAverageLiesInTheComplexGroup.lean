import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def ComplexMeanLiesInComplexGaugeGroup : Prop :=
  (∀ X ∈ PeriodicLattice.complexGaugeGroup,
    Matrices.ComplexMatrix2.operatorNorm (X - 1) < 1 →
      Matrices.ComplexMatrix2.fullTrace (Matrices.ComplexMatrix2.logSeries X) = 0 ∧
        Matrices.ComplexMatrix2.logSeries X ∈ Matrices.ComplexMatrix2.traceless) ∧
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 1 ≤ j → j ≤ k →
    (∀ n : ℕ, 0 < n → ∀ (c : Edge L n k j) (V : Edge L n k (j - 1) → Matrices.ComplexMatrix2),
      c.IsPositivelyOriented →
      V ∈ PeriodicLattice.complexAveragingDomainNearOne c →
        (∀ y : Vertex L n k j, (y = c.source ∨ y = c.target) →
          ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k (j - 1)) y,
            PeriodicLattice.complexMeanContourHolonomy V y x ∈
              PeriodicLattice.complexGaugeGroup) ∧
        PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup) ∧
    ∀ (c : FullSpace.Edge L k j) (V : FullSpace.Edge L k (j - 1) → Matrices.ComplexMatrix2),
      c.IsPositivelyOriented →
      V ∈ FullSpace.complexDomainNearOne L c →
        (∀ y : FullSpace.Vertex L k j, (y = c.initial ∨ y = c.terminal) →
          ∀ x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) y,
            FullSpace.complexContourMean L V y x ∈ PeriodicLattice.complexGaugeGroup) ∧
        FullSpace.complexSmoothing L V c ∈ PeriodicLattice.complexGaugeGroup
end Tower
end YangMills.Construction
end
