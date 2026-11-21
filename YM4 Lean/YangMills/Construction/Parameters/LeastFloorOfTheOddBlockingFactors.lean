import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
def IsOddBlockingFactorThreshold (N : ExternalConstants) (c : InitialChoice) (o : ℝ) (t : ℕ) :
    Prop :=
  13 ≤ t ∧ ∀ x : ℕ, Odd x → t ≤ x → BlockingFactorFloors N c o x
def leastOddBlockingFactorThreshold (N : ExternalConstants) (c : InitialChoice) (o : ℝ) : ℕ :=
  sInf {t | IsOddBlockingFactorThreshold N c o t}
end YangMills.Construction.ParameterChoice
end
