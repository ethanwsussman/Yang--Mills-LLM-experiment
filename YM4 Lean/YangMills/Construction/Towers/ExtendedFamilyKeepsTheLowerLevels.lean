import YangMills.Construction.Towers.OneStepOfACriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ExtendLevelPreservesLower : Prop :=
  ∀ L n k i : ℕ, ∀ (b : CriticalBranchData L n k)
    (p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2),
    b.IsCriticalUpTo i → (b.extendLevel i p).IsCriticalUpTo i
end YangMills.Construction.Tower
end
