import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.IterDerivLocality
open Periodisation
def IterDerivIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n → 1 ≤ k →
    ∀ U ∈ Tower.smallIterateFields L n k, ∀ (j : ℕ) (h : j ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k 0 (Nat.zero_le k))
        (CellClass.edgeClass k j h) (3 * Tower.meshAt L k j)
        (Tower.FullSpace.complexIterDeriv L k j (liftGaugeField L n k 0 U))
        (Tower.complexIterDeriv L n k j U)
end YangMills.Construction.LocalKernels.IterDerivLocality
end
