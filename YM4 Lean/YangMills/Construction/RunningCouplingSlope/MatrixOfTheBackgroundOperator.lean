import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def BackgroundHessianMatrix : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)],
      EventuallyNearIdentity (fieldSpace L n k 0) fun U => ∀ (B : edgeFormSpace L n k 0) ι,
        toPauliCoeffs (restrictToPositiveEdges
            ((backgroundHessian U 0 0 B : edgeFormSpace L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2)) ι =
          ∑ ι', ((finestMesh L k ^ 2 : ℝ) : ℂ) * (rescaledOperators L n k U).X ι ι' *
            toPauliCoeffs (restrictToPositiveEdges (B : Edge L n k 0 → Matrices.ComplexMatrix2)) ι'
end YangMills.Construction.RunningCouplingSlope
end
