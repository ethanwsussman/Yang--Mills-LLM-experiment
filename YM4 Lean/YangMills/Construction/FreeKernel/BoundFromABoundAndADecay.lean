import YangMills.Construction.FreeKernel.KernelsAndAbbreviationsInFourDimensions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open YangMills.Construction.FourDimKernel
def BoundFromBoundAndDecay : Prop :=
  ∀ (k : ℕ) (r x b₀ b : ℝ), 0 ≤ r → 0 ≤ x → 0 ≤ b₀ → 0 ≤ b → x ≤ b₀ →
    (0 < r → x ≤ b * r ^ (-(k : ℝ))) →
    x ≤ 2 ^ k * max b₀ b * bracketOnePlus r ^ (-(k : ℝ))
end YangMills.Construction.FreeKernel
end
