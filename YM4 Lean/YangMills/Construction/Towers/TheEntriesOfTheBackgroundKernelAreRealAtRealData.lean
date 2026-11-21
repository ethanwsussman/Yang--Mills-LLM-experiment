import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RealBackgroundKernel
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions (rawHessianKernel)
def RawHessianKernelReal : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ YangMills.Construction.Tower.FullSpace.smallIterateFields L k,
      U ∈ YangMills.Construction.Tower.FullSpace.fieldSpace L k 0 →
      ∀ J ∈ YangMills.Construction.Tower.FullSpace.edgeFormSpace (YangMills.Construction.Tower.meshAt L k 0),
        ∀ μ ∈ YangMills.Construction.Tower.FullSpace.edgeFormSpace (YangMills.Construction.Tower.meshAt L k k),
          ∀ ι' ι, (rawHessianKernel U J μ ι' ι).im = 0
end YangMills.Construction.Tower.FullSpace.RealBackgroundKernel
end
