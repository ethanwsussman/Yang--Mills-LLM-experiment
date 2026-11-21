import YangMills.Construction.Continuum.ConstantOfTheExtension
import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.FlatExtension
open YangMills.Construction.ExtensionConstants YangMills.Construction.ConfigSpace
variable {n : ℕ}
def IsFlatExtension (T : smoothRealTupleSet n → ℝ) (S : flatSchwartzSet n → ℂ) : Prop :=
  S ∈ flatDualSet n ∧
    ∀ φ : smoothRealTupleSet n, ∃ χ : flatSchwartzSet n, χ.1 = tensorProd φ.1 ∧ S χ = (T φ : ℂ)
def ExtensionBound (c : ℝ) (a : ℕ) (G : ℝ) (S : flatSchwartzSet n → ℂ) : Prop :=
  ∀ ψ : flatSchwartzSet n,
    ENNReal.ofReal ‖S ψ‖ ≤
      ENNReal.ofReal (extConst n a * max 1 c ^ n * G) *
        decaySeminorm (4 * n + 2) (10 * n + a - 2) ψ.1
def FlatExtensionClaim : Prop :=
  ∀ (n : ℕ) (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ),
    2 ≤ n → 0 < c → 0 ≤ G → SeparatedBallBound c a G T →
      (∃! S : flatSchwartzSet n → ℂ, IsFlatExtension T S) ∧
      (∀ S : flatSchwartzSet n → ℂ, IsFlatExtension T S → ExtensionBound c a G S) ∧
      extConst n a ≤
        extFactor * extBase ^ (n + a) * (n.factorial : ℝ) ^ 19
end YangMills.Construction.FlatExtension
