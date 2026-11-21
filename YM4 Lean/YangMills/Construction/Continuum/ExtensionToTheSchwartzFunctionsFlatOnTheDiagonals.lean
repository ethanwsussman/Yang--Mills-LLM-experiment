import YangMills.Construction.Continuum.ExtensionOfAFormToTheFlatFunctions
import YangMills.Construction.Continuum.GradientWeightRaisedToAtLeastOne
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.FlatSchwartzExtension
open ExtensionConstants FlatExtension ConfigSpace
def UniqueBoundedExtension : Prop :=
  ∀ (n : ℕ) (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ),
    2 ≤ n → 0 < c → 0 ≤ G → SeparatedBallBound c a G T →
      (∃! S : flatSchwartzSet n → ℂ, IsFlatExtension T S) ∧
      (∀ S : flatSchwartzSet n → ℂ, IsFlatExtension T S →
        ∀ ψ : flatSchwartzSet n,
          ENNReal.ofReal ‖S ψ‖ ≤
            ENNReal.ofReal (extConst n a * maxOneWeight c ^ n * G) *
              decaySeminorm (4 * n + 2) (10 * n + a - 2) ψ.1) ∧
      extConst n a ≤
        extFactor * extBase ^ (n + a) * (n.factorial : ℝ) ^ 19
end YangMills.Construction.FlatSchwartzExtension
