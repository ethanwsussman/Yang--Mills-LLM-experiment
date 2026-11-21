import YangMills.Construction.Continuum.KernelsOfTheParametrix
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace Parametrix
open YangMills.Construction.TorusMetric
def UnitKernelRegularity : Prop :=
  ContDiff ℝ 1 (logKernel 0) ∧ ContDiff ℝ ∞ outerLogKernel ∧ ContDiff ℝ 1 innerKernelUnit ∧
    ContDiff ℝ ∞ outerKernelUnit ∧ HasCompactSupport innerKernelUnit ∧
      HasCompactSupport outerKernelUnit ∧
      ∀ x, 1 / 2 < euclidNormVec x ^ 2 → innerKernelUnit x = 0 ∧ outerKernelUnit x = 0
end Parametrix
end YangMills.Construction
end
