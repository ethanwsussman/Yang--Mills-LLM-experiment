import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def TrivialFieldAtStep : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    (∀ y : Vertex L n k (i + 1),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        PeriodicLattice.meanContourHolonomy (trivialField L n k i) y x = 1) ∧
    smoothingStep L n k i (trivialField L n k i) = trivialField L n k (i + 1) ∧
    IsAxialGaugeAt L n k i (trivialField L n k i)
end Tower
end YangMills.Construction
end
