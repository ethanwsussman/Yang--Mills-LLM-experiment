import YangMills.Construction.Continuum.KernelsOfTheParametrix
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace Parametrix
open TorusMetric
def shellCutoff_properties : Prop :=
  ContDiff ℝ ∞ shellCutoff ∧ (∀ x, 0 ≤ shellCutoff x ∧ shellCutoff x ≤ 1) ∧
    (∀ x, euclidNormVec x ≤ 1 / 2 → shellCutoff x = 1) ∧
    ∀ x, 1 / 2 ≤ euclidNormVec x ^ 2 → shellCutoff x = 0
end Parametrix
end YangMills.Construction
