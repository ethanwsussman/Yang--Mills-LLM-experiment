import YangMills.Construction.Continuum.ConstantOfTheExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExtensionConstants
def FactorialTypeBounds : Prop :=
  1 ≤ factorialConst ∧ 1 ≤ extFactor ∧ 2 ≤ extBase ∧
    (∀ n a : ℕ, 2 ≤ n →
      extConst n a ≤ extFactor * extBase ^ (n + a) * (n.factorial : ℝ) ^ 19) ∧
    ∀ n : ℕ, 2 ≤ n →
      PieceSystems.taylorConst n ≤ factorialConst ^ n * (n.factorial : ℝ) ^ 2 ∧
      ShellPieces.countConst n ≤ factorialConst ^ n * (n.factorial : ℝ) ^ 2 ∧
      PieceSystems.leibnizConst n ≤ factorialConst ^ n * (n.factorial : ℝ) ^ 15
end YangMills.Construction.ExtensionConstants
