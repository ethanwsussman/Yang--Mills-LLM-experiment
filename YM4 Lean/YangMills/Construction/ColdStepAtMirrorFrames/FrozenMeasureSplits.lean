import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def FrozenPotentialExpectationFactorizes : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (S : Finset ι)
    (e : κ ≃ {b // b ∈ S}) (ρ μ : ℝ) (p : ℝ → ℝ) (Φ H : BondField ι → ℝ),
    0 < ρ → IsCutoff ρ p → Continuous Φ → 0 ≤ μ →
    ballExpectation (cutoffFactor ρ p) (frozenPotential S μ Φ) (fun η => H (restrictToBonds S η)) =
      ballExpectation (cutoffFactor ρ p) (fun ξ : BondField κ => Φ (pushforwardField (fun k => (e k).1) ξ))
        (fun ξ => H (pushforwardField (fun k => (e k).1) ξ))
end YangMills.Construction.ColdStepAtMirrorFrames
end
