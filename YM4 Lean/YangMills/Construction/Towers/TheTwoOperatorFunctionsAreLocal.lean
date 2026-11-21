import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def OperatorFunctionsAreLocal : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    PeriodicOperators.IsLocalOpFun (Tower.FullSpace.fieldPeriodicData L k hL)
        (Tower.FullSpace.vectorIndices L k) (Tower.FullSpace.vectorIndices L k)
        (Tower.FullSpace.vectorOpFn L k hL) ∧
      PeriodicOperators.IsLocalOpFun (Tower.FullSpace.fieldPeriodicData L k hL)
        (Tower.FullSpace.ghostIndices L k) (Tower.FullSpace.ghostIndices L k)
        (Tower.FullSpace.ghostOpFn L k hL)
end YangMills.Construction.Tower.FullSpace
end
