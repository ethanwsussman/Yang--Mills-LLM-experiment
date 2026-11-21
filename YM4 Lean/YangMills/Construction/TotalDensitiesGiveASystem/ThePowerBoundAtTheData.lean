import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def PowerBoundAtData : Prop :=
  HoldsAtAdmissibleParameters fun T y => ForSmallCoupling fun g => ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℕ+) (β : ℝ),
    TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β → ∀ m : ℕ+, ∀ n : ℕ, 2 ≤ n →
      ∀ R d : ℝ, 0 < R → 0 < d →
      ∀ f : Fin n → PeriodicLattice.FourTorus (T.stepParameters y).side m → ℝ,
        (∀ i, TestFunctions.IsLipschitzFor (PeriodicLattice.torusEuclidDist (T.stepParameters y).side m) (f i)) →
        (∀ i, ∃ x, tsupport (f i) ⊆ TestFunctions.closedBallTorus x R) →
          TestFunctions.HasSeparatedSupportsTorus f d →
          ‖PeriodicLattice.torusUrsellFunction (T.stepParameters y).side m K β f‖ ≤
            (C * max 1 (d ^ (-((5 : ℕ) : ℤ))) * (1 + R) ^ 4) ^ n * (n.factorial : ℝ) ^ (6 : ℝ) *
              ∏ i, TestFunctions.sharpNormTorus 1 (f i)
end YangMills.Construction.TotalDensities
end
