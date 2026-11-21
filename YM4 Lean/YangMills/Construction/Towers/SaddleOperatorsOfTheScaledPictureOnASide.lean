import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.RescaledSaddleOperators
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ U ∈ smallIterateFields L n k,
      RescaledConditions.SaddleScaling (rescaledOperators L n k U) (backgroundSaddle L n k U)
        (laplacianSaddle L n k U)
end YangMills.Construction.Tower.RescaledSaddleOperators
end
