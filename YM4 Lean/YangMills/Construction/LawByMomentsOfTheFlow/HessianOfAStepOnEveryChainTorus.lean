import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.TorusFields YangMills.Construction.WeightedResponses
def trivialHessianPosDefStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L → 0 < c.ρA →
    ∀ (u n : ℕ) [NeZero n], 64 ≤ n → (trivialHessian a L u n).PosDef ∧
      ∀ v : ↥(chordBonds (finiteCells (torusFrame L u n))) → ℝ,
        c.lam * ∑ b, v b ^ 2 ≤ v ⬝ᵥ (trivialHessian a L u n).mulVec v
end YangMills.Construction.MomentLaw
end
