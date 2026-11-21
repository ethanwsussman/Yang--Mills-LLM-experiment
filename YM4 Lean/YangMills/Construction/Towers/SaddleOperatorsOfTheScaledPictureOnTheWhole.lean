import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def RescaledSaddleScaling : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ Tower.FullSpace.smallIterateFields L k,
      Tower.RescaledConditions.SaddleScaling (Tower.FullSpace.rescaledOperators L k U)
        (Tower.FullSpace.backgroundSaddle L k U)
        (Tower.FullSpace.laplacianSaddle L k U)
end YangMills.Construction.Tower.FullSpace
end
