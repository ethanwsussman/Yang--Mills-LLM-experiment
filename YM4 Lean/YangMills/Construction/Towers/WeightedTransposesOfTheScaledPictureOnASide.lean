import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open RescaledConditions
namespace WeightedTransposesOnTorus
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ (i i' : Fin 3) (j j' : ℕ), j ≤ k → j' ≤ k →
      TransposeKernelScaling (levelRestriction L n k j i) (levelRestriction L n k j' i')
        (meshAt L k j) (meshAt L k j')
end WeightedTransposesOnTorus
end YangMills.Construction.Tower
end
