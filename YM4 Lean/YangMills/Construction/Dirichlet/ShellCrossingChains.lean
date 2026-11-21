import YangMills.Construction.Dirichlet.WeightedLengthEstimates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Dirichlet
open Torus
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
def scaledGap (k : ℕ) (p q : PeriodicTorus d S) : ℝ := (𝒮.scaleAt (k : ℤ))⁻¹ * lOneNorm (p - q)
end Dirichlet
end YangMills.Construction
