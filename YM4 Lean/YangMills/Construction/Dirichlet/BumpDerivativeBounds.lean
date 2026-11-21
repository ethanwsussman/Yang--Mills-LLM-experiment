import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open ContDiff
noncomputable section
namespace YangMills.Construction.Dirichlet
def bumpDerivSup : ℝ := ⨆ x, |deriv bumpProfile x|
def bumpSecondDerivSup : ℝ := ⨆ x, |deriv (deriv bumpProfile) x|
def expOne : ℝ := Real.exp 1
end YangMills.Construction.Dirichlet
