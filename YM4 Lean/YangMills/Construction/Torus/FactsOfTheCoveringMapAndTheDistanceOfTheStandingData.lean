import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Conventions.StandingParameters
open TorusMetric
def CoveringAndDistanceFacts : Prop :=
  ∀ P : StandingParameters,
    Function.Surjective (torusProj (PeriodicLattice.torusSide P.L P.m)) ∧
    (∀ y y' : Fin 4 → ℝ,
      torusProj (PeriodicLattice.torusSide P.L P.m) y =
          torusProj (PeriodicLattice.torusSide P.L P.m) y' ↔
        ∃ k : Fin 4 → ℤ, y - y' = fun μ => PeriodicLattice.torusSide P.L P.m * (k μ : ℝ)) ∧
    (∀ x x' : P.Torus, 0 ≤ torusEuclidNorm (x - x')) ∧
    (∀ x x' : P.Torus, torusEuclidNorm (x - x') = 0 ↔ x = x') ∧
    (∀ x x' : P.Torus, torusEuclidNorm (x - x') = torusEuclidNorm (x' - x)) ∧
    (∀ x x' x'' : P.Torus,
      torusEuclidNorm (x - x'') ≤ torusEuclidNorm (x - x') + torusEuclidNorm (x' - x'')) ∧
    (∀ y y' : Fin 4 → ℝ,
      torusEuclidNorm
          (torusProj (PeriodicLattice.torusSide P.L P.m) y -
            torusProj (PeriodicLattice.torusSide P.L P.m) y') ≤
        euclidNormVec (y - y')) ∧
    @Continuous _ _ _ (PeriodicLattice.metricTopology P.L P.m)
      (torusProj (PeriodicLattice.torusSide P.L P.m)) ∧
    @CompactSpace _ (PeriodicLattice.metricTopology P.L P.m)
end YangMills.Construction.Conventions.StandingParameters
end
