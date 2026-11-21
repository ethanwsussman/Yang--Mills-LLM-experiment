import YangMills.Construction.ParameterData.ShapesOfAPair
import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TrajectoryData
open PeriodicLattice TestFunctions
def bumpsFormSeparatedPairStatement : Prop :=
  ∀ (L m : ℕ) (n : ℝ) (v : Fin 4 → ℤ), 1 ≤ L → 0 < n → 40 * n ≤ torusSide L m →
    (firstBump L m n v, translatedBump L m n v) ∈ separatedPairsFourTorus L m n (1 / 4)
end TrajectoryData
end YangMills.Construction
end
