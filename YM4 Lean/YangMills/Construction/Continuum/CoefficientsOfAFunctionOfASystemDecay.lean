import YangMills.Construction.Continuum.FourierSeriesOfASystemDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def SystemCoeffsDecay : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Q : PointSystem n), ∀ Φ ∈ Q.supportedClass, Q.CoeffDecay Φ
end YangMills.Construction.ConfigSpace
