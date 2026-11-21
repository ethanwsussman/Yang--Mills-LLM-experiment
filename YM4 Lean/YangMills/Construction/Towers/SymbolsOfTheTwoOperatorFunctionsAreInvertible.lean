import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def SymbolsInvertibleAtZero : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    PeriodicOperators.SymbolInvertibleOnReals (Tower.FullSpace.vectorIndices L k)
        (Tower.FullSpace.vectorOpFn L k hL 0) ∧
      PeriodicOperators.SymbolInvertibleOnReals (Tower.FullSpace.ghostIndices L k)
        (Tower.FullSpace.ghostOpFn L k hL 0)
end YangMills.Construction.Tower.FullSpace
end
