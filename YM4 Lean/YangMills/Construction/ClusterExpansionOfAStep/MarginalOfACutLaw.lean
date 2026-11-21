import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames
def MarginalOfRestrictedLaw : Prop :=
  ∀ (ι ι₀ : Type) [Fintype ι] [DecidableEq ι] [Fintype ι₀] [DecidableEq ι₀] (ρ c : ℝ)
    (Ψ : BondField ι → ℝ) (p : ℝ → ℝ) (j : ι₀ → ι) (F : BondField ι₀ → ℝ),
    0 < ρ → IsCutoff ρ p → Function.Injective j →
    ballExpectation (cutoffFactor ρ p) (restrictedPotential c (Finset.univ.image j) Ψ)
        (fun η => F fun a => η (j a)) =
      ballExpectation (cutoffFactor ρ p) (fun ξ => Ψ (extendByZero j ξ)) F
end YangMills.Construction.ClusterExpansionOfAStep
end
