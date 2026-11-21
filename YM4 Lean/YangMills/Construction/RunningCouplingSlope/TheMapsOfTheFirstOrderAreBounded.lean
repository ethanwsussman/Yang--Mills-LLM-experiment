import YangMills.Construction.RunningCouplingSlope.FirstOrderOfTheLeastPoint
import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def FirstVariationMapsBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
    IsLinearConstraintAdjoint (linearConstraintAdjoint L n k) ∧
    (∀ ξ : LevelForms L n k, ∃ G : Tower.edgeFormSpace L n k k,
      (G : Tower.Edge L n k k → Matrices.ComplexMatrix2) = linearChain ξ k ∧
        topFormNormSq G ≤ c * levelFormsNormSq ξ) ∧
    (∀ B G : Tower.edgeFormSpace L n k k,
      Tower.CriticalBranchResponse.periodicDefect L n k
          ((B : Tower.Edge L n k k → Matrices.ComplexMatrix2) - G) =
        Tower.CriticalBranchResponse.periodicDefect L n k B -
          Tower.CriticalBranchResponse.periodicDefect L n k G ∧
      Tower.CriticalBranchResponse.meshScaledResponse L n k
          ((B : Tower.Edge L n k k → Matrices.ComplexMatrix2) - G) =
        Tower.CriticalBranchResponse.meshScaledResponse L n k B -
          Tower.CriticalBranchResponse.meshScaledResponse L n k G) ∧
    ∀ B : Tower.edgeFormSpace L n k k,
      topFormNormSq (Tower.CriticalBranchResponse.periodicDefect L n k B) ≤ c * topFormNormSq B ∧
      levelFormsNormSq ((Tower.CriticalBranchResponse.meshScaledResponse L n k B, 0) : LevelForms L n k) ≤
        c * topFormNormSq B
end YangMills.Construction.RunningCouplingSlope
end
