import YangMills.Construction.RunningCouplingSlope.WaveSumsOfTheKernels
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower.CriticalBranchResponse
def DifferenceKernelTranslationInvariant : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ᶠ n in atTop,
    ∀ y x : TorusFields.TorusSite (2 * L ^ n),
      Tower.leftSecondDeriv (chainMinusBackground a) (Tower.trivialField L n k 0)
          (meshScaledResponse L n k (pauliUnitForm L n k (centredCoords y)) :
            Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
          (meshScaledResponse L n k (pauliUnitForm L n k (centredCoords x)) :
            Tower.Edge L n k 0 → Matrices.ComplexMatrix2) =
        differenceKernelFinite a L n k (centredCoords (x - y))
end YangMills.Construction.RunningCouplingSlope
end
