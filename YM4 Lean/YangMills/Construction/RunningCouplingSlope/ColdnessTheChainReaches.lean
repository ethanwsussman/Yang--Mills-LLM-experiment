import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ColdChain
structure IsReachableColdness (c : ColdChainParameters) (L : ℕ) (s : ℝ) : Prop where
  pos : 0 < s
  le_bound : s ≤ c.σA
  small_vs_block : 2 ^ 10 * (L : ℝ) * (c.N 0 + 1) * s ≤ 9 / 8
end YangMills.Construction.ColdChain
end
