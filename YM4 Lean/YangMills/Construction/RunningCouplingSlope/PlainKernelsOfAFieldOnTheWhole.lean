import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
open YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace YangMills.Construction.PeriodicOperators
def MeanKernelsAreLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsLocalOpFun (colourEdges L k 0) (colourEdges L k 0) (colourEdges L k k)
      (fun f => meanKernelQ L k (BackgroundJets.gaugeFieldOfForm L k f)) ∧
    IsLocalOpFun (colourEdges L k 0) (colourVertices L k 0) (colourVertices L k k)
      (fun f => meanKernelR L k (BackgroundJets.gaugeFieldOfForm L k f)) ∧
    (∀ a : ℝ, IsLocalOpFun (colourEdges L k 0) (colourEdges L k k)
      (colourEdges L k k) (fun f => noiseCovariance a L k (BackgroundJets.gaugeFieldOfForm L k f) k)) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f : (colourEdges L k 0).Carrier → ℂ, (∀ κ, (f κ).im = 0) →
      IsSupBelow (colourEdges L k 0) f ρ →
        (∀ ι' ι, (meanKernelQ L k (BackgroundJets.gaugeFieldOfForm L k f) ι' ι).im = 0) ∧
        (∀ ι' ι, (meanKernelR L k (BackgroundJets.gaugeFieldOfForm L k f) ι' ι).im = 0) ∧
        ∀ (a : ℝ) ι' ι, (noiseCovariance a L k (BackgroundJets.gaugeFieldOfForm L k f) k ι' ι).im = 0
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
