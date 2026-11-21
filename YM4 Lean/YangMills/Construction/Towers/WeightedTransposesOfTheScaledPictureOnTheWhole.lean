import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.MeshTransposes
def TransposeScalingHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ (i i' : Fin 3) (j j' : ℕ), j ≤ k → j' ≤ k →
      Tower.RescaledConditions.TransposeKernelScaling
        (Tower.FullSpace.RescaledConditions.levelRestriction L k j i)
        (Tower.FullSpace.RescaledConditions.levelRestriction L k j' i')
        (Tower.meshAt L k j) (Tower.meshAt L k j')
end YangMills.Construction.Tower.FullSpace.MeshTransposes
end
