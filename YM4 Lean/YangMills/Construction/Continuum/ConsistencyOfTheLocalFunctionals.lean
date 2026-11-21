import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import YangMills.Construction.Continuum.LocalFunctionalsOfAForm
import Mathlib
set_option autoImplicit false
open scoped ContDiff
namespace YangMills.Construction.ConfigSpace
def LocalPairingConsistent : Prop :=
  ∀ (n : ℕ) (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ),
    SeparatedBallBound c a G T →
    ∀ Q Q' : PointSystem n, Q.IsSeparated → Q'.IsSeparated →
    ∀ Φ : Config n → ℂ, ContDiff ℝ ∞ Φ →
      tsupport Φ ⊆ cylinderSet Q.box ∩ cylinderSet Q'.box →
      localPairing T Q Φ = localPairing T Q' Φ
end YangMills.Construction.ConfigSpace
