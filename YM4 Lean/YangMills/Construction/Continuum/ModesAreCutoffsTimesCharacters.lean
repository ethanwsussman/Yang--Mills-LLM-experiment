import YangMills.Construction.Continuum.FourierSeriesOfASystemDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def ModesAreLocalCharacters : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Q : PointSystem n), Q.ModesLocalCharacters
end YangMills.Construction.ConfigSpace
