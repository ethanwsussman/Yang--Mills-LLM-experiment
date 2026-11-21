import YangMills.Construction.RunningCouplingSlope.FirstOrderOfTheLeastPoint
import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Tower.CriticalBranchResponse
def FirstVariationNearResponse : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (B : edgeFormSpace L n k k) (t : LevelTriple L n k),
      IsFirstVariation a B t →
      ∃ (l : vertexFunctionSpace L n k 0) (A : edgeFormSpace L n k 0) (τ : LevelTriple L n k),
        (A : Edge L n k 0 → Matrices.ComplexMatrix2) =
          vertexCoboundary (l : Vertex L n k 0 → Matrices.ComplexMatrix2) ∧
        t = backgroundOnlyTriple (meshScaledResponse L n k B) + backgroundOnlyTriple A + τ ∧
        tripleNormSq τ ≤ C * topFormNormSq (periodicDefect L n k B)
end YangMills.Construction.RunningCouplingSlope
end
