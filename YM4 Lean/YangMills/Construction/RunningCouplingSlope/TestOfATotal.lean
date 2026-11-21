import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.SlopeCoefficient
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def expAlong (n : ℕ) (B : TorusBond n → imaginaryQuaternions) (s : ℝ) : TorusField n :=
  fun x i => expUnit (s • B (x, i))
def secondDerivAlong (H : GaugeTotal) (n : ℕ) (B : TorusBond n → imaginaryQuaternions) : ℝ :=
  iteratedDeriv 2 (fun s : ℝ => H n (expAlong n B s)) 0
structure IsGaugeFunctionNear (H : GaugeTotal) (n : ℕ) : Prop where
  contDiffAt_perturb : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0
  gauge_invariant_near : ∀ᶠ p : (TorusSite n → UnitQuaternion) × TorusField n in 𝓝 (1, trivialField n),
    H n (gaugeTransform p.1 p.2) = H n p.2
def HessianBoundedBy (H : GaugeTotal) (n : ℕ) (M θ : ℝ) : Prop :=
  ∀ (c c' : TorusBond n) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
    |hessianAtTrivial H n c c' X X'| ≤ M * Real.exp (-(θ * supDist c.1 c'.1))
end YangMills.Construction.SlopeCoefficient
end
