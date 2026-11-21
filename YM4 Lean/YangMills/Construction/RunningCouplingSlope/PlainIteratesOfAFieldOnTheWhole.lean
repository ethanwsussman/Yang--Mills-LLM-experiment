import YangMills.Construction.RunningCouplingSlope.OnePlainStepOnTheWhole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
open YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
open scoped Topology Matrix.Norms.L2Operator
structure FieldIterateProperties (L k : ℕ) (δ ρ : ℝ) : Prop where
  mem_nearIdentity : ∀ m, m ≤ k → ∀ f : (colourEdges L k 0).Carrier → ℂ,
    IsSupBelow (colourEdges L k 0) f ρ →
      meanIterate (BackgroundJets.gaugeFieldOfForm L k f) m ∈ nearIdentityFields L k m δ
  analyticAt : ∀ (S : Set (colourEdges L k 0).Carrier) (l : ℕ) (e : Fin l ≃ S), ∀ m, m ≤ k →
    ∀ p ∈ openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ, ∀ b,
      AnalyticAt ℂ
        (fun w => meanIterate (BackgroundJets.gaugeFieldOfForm L k (fieldExtend e w)) m b) p
  local_dependence : ∀ m, m ≤ k → ∀ (b : FullSpace.Edge L k m) (f f' : (colourEdges L k 0).Carrier → ℂ),
    IsSupBelow (colourEdges L k 0) f ρ → IsSupBelow (colourEdges L k 0) f' ρ →
    (∀ κ : (colourEdges L k 0).Carrier,
      ‖((κ.2.1.initial : FullSpace.Vertex L k 0) : InfiniteLattice.AmbientSpace) -
        (b.initial : InfiniteLattice.AmbientSpace)‖ ≤ 3 * (m : ℝ) + 3 → f κ = f' κ) →
    meanIterate (BackgroundJets.gaugeFieldOfForm L k f) m b =
      meanIterate (BackgroundJets.gaugeFieldOfForm L k f') m b
  shift_eq : ∀ (v : Fin 4 → ℤ), ∀ m, m ≤ k → ∀ f : (colourEdges L k 0).Carrier → ℂ,
    IsSupBelow (colourEdges L k 0) f ρ →
      meanIterate (BackgroundJets.gaugeFieldOfForm L k
          (shiftField (colourEdges L k 0) v f)) m =
        FullSpace.pushField (intShift v)
          (meanIterate (BackgroundJets.gaugeFieldOfForm L k f) m)
  mem_compact : ∀ f : (colourEdges L k 0).Carrier → ℂ, IsSupBelow (colourEdges L k 0) f ρ →
    (∀ κ, (f κ).im = 0) → ∀ m, m ≤ k → ∀ b,
      meanIterate (BackgroundJets.gaugeFieldOfForm L k f) m b ∈ PeriodicLattice.compactGaugeGroup
def FieldIteratesNearIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ k : ℕ, 1 ≤ k → ∃ ρ : ℝ, 0 < ρ ∧ FieldIterateProperties L k δ ρ
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
