import YangMills.Construction.Continuum.FourierSeriesOfASystemDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def IntegerLatticeDecaySum : Prop :=
  ∀ n : ℕ, 1 ≤ n → IntegerLatticeSumBound n
end YangMills.Construction.ConfigSpace
