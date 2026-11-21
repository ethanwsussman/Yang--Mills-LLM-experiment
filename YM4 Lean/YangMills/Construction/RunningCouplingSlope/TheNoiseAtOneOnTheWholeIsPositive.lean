import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
def NoiseCovarianceAtIdentityPositive : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, j ≤ k →
    IsPeriodicKernel (colourEdges L k j) (colourEdges L k j)
      (FullLattice.noiseCovariance a L k (fun _ => 1) j) ∧
    ∀ κ ∈ realDualPoints,
      SymbolSummableAt (colourEdges L k j) (colourEdges L k j)
        (FullLattice.noiseCovariance a L k (fun _ => 1) j) κ ∧
      ∀ v : (colourEdges L k j).UnitQuot → ℂ,
        0 ≤ (wInner ((colourEdges L k j).quotWeight 1) v
          (symbolHom (colourEdges L k j) (colourEdges L k j)
            (FullLattice.noiseCovariance a L k (fun _ => 1) j) κ v)).re ∧
        (1 ≤ j → a⁻¹ * (wInner ((colourEdges L k j).quotWeight 1) v v).re ≤
          (wInner ((colourEdges L k j).quotWeight 1) v
            (symbolHom (colourEdges L k j) (colourEdges L k j)
              (FullLattice.noiseCovariance a L k (fun _ => 1) j) κ v)).re)
end YangMills.Construction.RunningCouplingSlope
end
