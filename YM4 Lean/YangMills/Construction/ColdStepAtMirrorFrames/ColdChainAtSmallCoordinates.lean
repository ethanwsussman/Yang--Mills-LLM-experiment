import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ColdChainAtSmallCoordinates : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∃ (lam ρ σA cg : ℝ) (N : ℕ → ℝ), YangMills.Construction.ColdChain.ColdChainConstants a δ L lam ρ σA cg N
end YangMills.Construction.ColdStepAtMirrorFrames
end
