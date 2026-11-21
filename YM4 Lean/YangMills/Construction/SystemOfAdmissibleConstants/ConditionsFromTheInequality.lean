import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedMoments
open ChessboardTori ReflectedCopies
def CopyInequalityOnRelation (L : ℕ) (IsDatum : ℕ+ → ℝ → Prop) (A b : ℝ) : Prop :=
  ∀ D : ChessboardSetup, D.L = L → 2 ≤ (D.K : ℕ) → IsDatum D.K D.β → CopyInequality D A b
end YangMills.Construction.SeparatedMoments
end
