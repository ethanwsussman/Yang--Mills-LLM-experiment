import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Matrices Conventions
def ChainActionHessianAtQuiet : Prop :=
  ∀ a : ℝ, ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    EventuallyNearIdentity (fieldSpace L n k 0) fun U => ∀ ξ : LevelForms L n k,
      RunningCouplingSlope.leftSecondDeriv (chainAction a) (quietPoint U) ξ ξ =
        Tower.leftSecondDeriv (plaquetteAction L n k) U (ξ.1 : Edge L n k 0 → ComplexMatrix2)
            (ξ.1 : Edge L n k 0 → ComplexMatrix2) +
          a * ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
            (meanRadius (meanIterate U i) c.1).re *
              (ComplexMatrix2.halfTrace
                (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1 *
                  ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1)).re
end YangMills.Construction.RunningCouplingSlope
end
