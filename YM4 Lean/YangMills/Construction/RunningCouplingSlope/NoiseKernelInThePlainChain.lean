import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import YangMills.Construction.RunningCouplingSlope.PlainChainOfATangent
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def NoiseCovarianceAsPlainChainSum : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      ∀ E : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → LevelForms L n k,
        (∀ κ, (E κ).1 = 0) → (∀ κ i, i ≠ κ.1 → (E κ).2 i = 0) →
        (∀ κ ι, toPauliCoeffs (restrictToPositiveEdges
          (((E κ).2 κ.1 : edgeFormSpace L n k (κ.1 + 1)) :
            Edge L n k (κ.1 + 1) → Matrices.ComplexMatrix2)) ι =
            open Classical in if ι = κ.2 then 1 else 0) →
        ∀ m ≤ k, ∀ t t', noiseCovariance a L n k U m t t' =
          ∑ᶠ κ : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)),
            toPauliCoeffs (restrictToPositiveEdges (tangentForms U (E κ) m)) t *
              toPauliCoeffs (restrictToPositiveEdges (tangentForms U (E κ) m)) t' *
                (((a * (meanRadius (meanIterate U κ.1) κ.2.2.1).re)⁻¹ : ℝ) : ℂ)
end YangMills.Construction.RunningCouplingSlope
end
