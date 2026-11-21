import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourPointCondition
def connectedFunctionsHomogeneousStatement : Prop :=
  (∀ (s : Conventions.StandingParameters) (β : ℝ) (n : ℕ) (f : Fin n → s.Torus → ℝ) (c : Fin n → ℝ), 0 < β → 1 ≤ n →
    (∀ i, TestFunctions.IsLipschitzFor (PeriodicLattice.torusEuclidDist s.L s.m) (f i)) →
    (PeriodicLattice.torusUrsellFunction s.L s.m s.K β f).im = 0 ∧
    PeriodicLattice.torusUrsellFunction s.L s.m s.K β (fun i x => c i * f i x) =
      ((∏ i, c i : ℝ) : ℂ) * PeriodicLattice.torusUrsellFunction s.L s.m s.K β f) ∧
  ∀ (S : ℝ) (q : ℕ) (f : Fin (q + 1) → TorusMetric.Torus4 S → ℝ) (c : Fin (q + 1) → ℝ),
    ResponseInTheExpansion.gaussianCumulantLimit S (fun i x => c i * f i x) =
      (∏ i, c i) * ResponseInTheExpansion.gaussianCumulantLimit S f
end YangMills.Construction.FourPointCondition
end
