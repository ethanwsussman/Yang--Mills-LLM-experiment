import YangMills.Construction.LawInAState.HatsSumToTheFreeKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open InfiniteLattice (AmbientSpace)
def normalizedPairLocalizedStatement : Prop :=
  ∀ (d vt : ℝ) (f h : AmbientSpace → ℝ), 0 < d → 0 < vt → vt ≤ 1 → IsNormalizedTestPair d vt f h →
    ∃ c : AmbientSpace, IsLocalizedLipschitzPair c d (2 / (vt * d)) f h ∧
      10 ^ (-8 : ℤ) * vt ^ 2 ≤ TestFunctions.inverseEighthKernel f h
end YangMills.Construction.StateLaws
end
