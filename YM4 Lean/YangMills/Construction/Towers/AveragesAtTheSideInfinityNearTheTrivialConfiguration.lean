import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open scoped ENNReal
namespace YangMills.Construction
namespace Tower.FullSpace
def SmoothingNearIdentity : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 1 ≤ k → 1 ≤ j → j ≤ k →
  ∀ U : Edge L k (j - 1) → Matrices.ComplexMatrix2, U ∈ fieldSpace L k (j - 1) →
    supDistOne U < ENNReal.ofReal (Averaging.smoothingRadius L / 4) →
  ∀ e : Edge L k j, e.IsPositivelyOriented →
    U ∈ complexDomainNearOne L e ∧
      complexSmoothing L U e ∈ PeriodicLattice.compactGaugeGroup ∧
      ∀ w : Vertex L k j, w = e.initial ∨ w = e.terminal →
        ∀ z ∈ cubeVertices L (meshAt L k (j - 1)) w,
          complexContourMean L U w z ∈ PeriodicLattice.compactGaugeGroup
end Tower.FullSpace
end YangMills.Construction
