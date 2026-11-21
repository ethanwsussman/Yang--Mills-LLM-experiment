import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def RescaledTrivialSteps : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    Tower.trivialField L n k 0 ∈ Tower.smallIterateFields L n k ∧
      ∀ i < k, Tower.RescaledConditions.TrivialStep L n k i
end Tower
end YangMills.Construction
end
