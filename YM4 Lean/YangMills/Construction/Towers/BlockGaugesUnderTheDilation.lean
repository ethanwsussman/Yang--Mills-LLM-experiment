import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.FamiliesOfCriticalBranches
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def BlockGaugeLiftCommutesWithScaling : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ j →
    ∀ i < j, ∀ v : Vertex L n k (i + 1) → Matrices.ComplexMatrix2,
      transportTotal (scaleVertex hL hj i).toEquiv (blockGaugeLift v) =
        blockGaugeLift (transportTotal (scaleVertex hL hj (i + 1)).toEquiv v)
end YangMills.Construction.Tower
end
