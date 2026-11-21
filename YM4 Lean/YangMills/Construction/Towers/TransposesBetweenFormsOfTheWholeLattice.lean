import YangMills.Construction.Towers.TransposesOfRealLinearMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open LeftChartFields in
def EdgeFormTransposes : Prop :=
  ∀ L k i j : ℕ, Conventions.IsAdmissibleBlockingFactor L → i ≤ k → j ≤ k →
    HasUniqueTranspose (edgePairedSpace (meshAt L k i)) (edgePairedSpace (meshAt L k j)) ∧
      PairedFunctionSpace.AdmitsRealTransposes (edgePairedSpace (meshAt L k i))
        (edgePairedSpace (meshAt L k j))
end YangMills.Construction.Tower.FullSpace
end
