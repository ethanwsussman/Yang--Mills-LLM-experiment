import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusPowers
variable (D : Conventions.StandingParameters)
def IsPowerOfL (M : ℝ) : Prop := ∃ m' : ℕ, M = (D.L : ℝ) ^ m'
end YangMills.Construction.TorusPowers
