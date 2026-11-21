import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStep
import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
def MaxwellKernelDecayAndLocality : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdStepAtMirrorFrames.ColdChainParameters), c.Admissible a L → ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧
    ∀ (u m m' : ℕ) [NeZero m] [NeZero m'], 64 ≤ m → 64 ≤ m' →
      (∀ b b' : TorusFields.TorusBond m, |maxwellKernel a L u b b'| ≤ C * Real.exp (-(μ * TorusFields.supDist b.1 b'.1))) ∧
      ∀ (y : TorusFields.TorusSite m) (y' : TorusFields.TorusSite m') (ρ r : ℕ) (e e' : TorusLumps.LatticeBond),
        2 * r + 16 ≤ m → 2 * r + 16 ≤ m' → ρ ≤ r →
        TorusFields.BondOffsetInBox ρ e → TorusFields.BondOffsetInBox r e' →
        |maxwellKernel a L u (TorusLumps.bondFrom y e) (TorusLumps.bondFrom y e') -
            maxwellKernel a L u (TorusLumps.bondFrom y' e) (TorusLumps.bondFrom y' e')| ≤
          C * Real.exp (-(μ * ((r : ℝ) - ρ)))
end YangMills.Construction.WeightedResponses
end
