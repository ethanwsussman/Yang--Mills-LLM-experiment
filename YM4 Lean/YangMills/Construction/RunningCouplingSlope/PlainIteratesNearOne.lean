import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def MeanIteratesTendToOne : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n → ∀ j : ℕ, j ≤ k →
    Tendsto (fun U : Edge L n k 0 → Matrices.ComplexMatrix2 => meanIterate U j)
      (𝓝[fieldSpace L n k 0] fun _ => (1 : Matrices.ComplexMatrix2))
      (𝓝[fieldSpace L n k j] fun _ => (1 : Matrices.ComplexMatrix2))
end YangMills.Construction.RunningCouplingSlope
end
