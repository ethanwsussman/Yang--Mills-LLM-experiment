import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
def CopySizeSmallRadius.Statement : Prop :=
  ∀ A v : ℝ, 0 ≤ A → 0 ≤ v → ∃ A' : ℝ, 0 ≤ A' ∧ ∀ l r : ℝ, 0 < l → l ≤ 1 → 0 < r → r ≤ 1 →
    copySize A v l r ≤ A' / r
end YangMills.Construction.ReflectedCopies
end
