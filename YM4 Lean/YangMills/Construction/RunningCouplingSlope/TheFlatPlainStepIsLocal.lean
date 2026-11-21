import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
def MeanStepAtTrivialFieldFiniteRange : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, m < k →
    FreeOperators.HasFiniteRangeEveryRate (colourEdges L k m) (colourEdges L k (m + 1))
      (FullLattice.meanStepKernel L k (fun _ => 1) m) ∧
    FreeOperators.HasFiniteRangeEveryRate (colourEdges L k (m + 1)) (colourEdges L k m)
      (kernelTranspose (colourEdges L k m) (colourEdges L k (m + 1))
        (FullLattice.meanStepKernel L k (fun _ => 1) m)) ∧
    ∀ (ι' : (colourEdges L k (m + 1)).Carrier) (ι : (colourEdges L k m).Carrier),
      (FullLattice.meanStepKernel L k (fun _ => 1) m ι' ι).im = 0
end YangMills.Construction.RunningCouplingSlope
end
