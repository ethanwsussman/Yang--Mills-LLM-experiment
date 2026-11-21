import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
structure IsLocalGaugeDensity (h : TorusLumps.LocalDensity) : Prop where
  contDiffAt : ∀ᶠ n in Filter.atTop, ∀ (y : TorusFields.TorusSite n) (k : ℕ) (c : Fin k → TorusFields.TorusBond n)
      (X : Fin k → BlockAverages.imaginaryQuaternions),
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => h n y (TorusFields.perturb c X σ (TorusFields.trivialField n))) 0
  gauge_invariant : ∀ᶠ n in Filter.atTop, ∀ y : TorusFields.TorusSite n,
    ∀ᶠ p : (TorusFields.TorusSite n → BlockAverages.UnitQuaternion) × TorusFields.TorusField n
      in 𝓝 (1, TorusFields.trivialField n),
      h n y (TorusFields.gaugeTransform p.1 p.2) = h n y p.2
  translation_invariant : ∀ᶠ n in Filter.atTop, ∀ y u : TorusFields.TorusSite n,
    ∀ᶠ V in 𝓝 (TorusFields.trivialField n), h n y (TorusFields.translate u V) = h n (y + u) V
  kernel_decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ᶠ n in Filter.atTop, ∀ (c c' : TorusFields.TorusBond n)
      (X X' : BlockAverages.imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
    |TorusFields.mixedDeriv (h n 0) (TorusFields.trivialField n) ![c, c'] ![X, X']| ≤
      M * Real.exp (-(θ * TorusFields.supportDiam (0 : TorusFields.TorusSite n) ![c, c']))
  tendsto : TorusLumps.HasLimitSecondDeriv h
end YangMills.Construction.RunningCouplingSlope
end
