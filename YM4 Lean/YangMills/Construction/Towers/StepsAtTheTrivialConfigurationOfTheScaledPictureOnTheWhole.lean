import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def RescaledTrivialSteps : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (fun _ => 1) ∈ Tower.FullSpace.smallIterateFields L k ∧
      ∀ i < k, Tower.FullSpace.RescaledConditions.TrivialStep L k i
end YangMills.Construction.Tower.FullSpace
end
