import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
def PolydiscInComplexDomain : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
    ∀ n k j : ℕ, 0 < n → j < k → ∀ c : Edge L n k (j + 1), PeriodicLattice.Bond.IsPositivelyOriented c →
      nearIdentityPolydisc ρ c ⊆
          (PeriodicLattice.complexAveragingDomainNearOne c : Set (Edge L n k j → Matrices.ComplexMatrix2)) ∧
        (∀ V ∈ nearIdentityPolydisc ρ c,
          Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.complexBlockAverage V c - 1) < 1 / 2) ∧
        ∀ V ∈ nearIdentityPolydisc ρ c,
          ∀ y ∈ ({PeriodicLattice.Bond.source c, PeriodicLattice.Bond.target c} : Set (Vertex L n k (j + 1))),
          ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
            Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.complexMeanContourHolonomy V y x - 1) < 1 / 2
end YangMills.Construction.Tower
