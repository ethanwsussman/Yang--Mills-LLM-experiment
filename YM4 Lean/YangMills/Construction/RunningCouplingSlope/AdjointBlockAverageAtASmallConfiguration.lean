import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels
open Periodisation Tower
def AdjointCubeAverageIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ (j : ℕ) (h : j + 1 ≤ k), ∀ V ∈ smallComplexFields L n k j,
      IsLocalWithPeriodicCounterpart L n (CellClass.vertexClass k j (Nat.le_of_succ_le h))
        (CellClass.vertexClass k (j + 1) h) (meshAt L k (j + 1) / 2)
        (FullSpace.adjointCubeAverage (liftGaugeField L n k j V))
        (adjointCubeAverage V)
end YangMills.Construction.LocalKernels
end
