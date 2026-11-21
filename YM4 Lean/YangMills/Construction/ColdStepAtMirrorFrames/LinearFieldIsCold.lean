import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import YangMills.Construction.ColdStepAtMirrorFrames.CurvedChainIsAbelian
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def LinearFieldCurvatureBound : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (U : F.GaugeField j) (X : imaginaryQuaternions) (g : ℝ) (μ ν : Fin 4), ‖X‖ = 1 → μ < ν →
    IsAbelianLinearAlong X g μ ν U →
    (∀ (x : F.Site j) (α β : Fin 4), α < β →
      plaquetteHolonomy U (x, α, β) = expUnit ((if α = μ ∧ β = ν then g else 0) • X)) ∧
    ∀ p : F.Site j × Fin 4 × Fin 4, p.2.1 < p.2.2 → plaquetteDefect U p ≤ |g|
end YangMills.Construction.ColdStepAtMirrorFrames
end
