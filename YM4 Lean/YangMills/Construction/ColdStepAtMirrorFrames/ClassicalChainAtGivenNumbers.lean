import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def AdmissibleParametersExist : Prop :=
  ∀ (a δ₁ : ℝ) (L : ℕ) (lam ρA σA cg : ℝ) (N : ℕ → ℝ), 1 ≤ a → Odd L →
    YangMills.Construction.ColdChain.ColdChainConstants a δ₁ L lam ρA σA cg N →
    ∃ c : ColdChainParameters, c.δ₁ = δ₁ ∧ c.δ' = δ₁ / 4 ∧ c.lam = lam ∧ c.ρA = ρA ∧ c.σA = σA ∧ c.cg = cg ∧
      c.N = N ∧ c.Admissible a L
end YangMills.Construction.ColdStepAtMirrorFrames
end
