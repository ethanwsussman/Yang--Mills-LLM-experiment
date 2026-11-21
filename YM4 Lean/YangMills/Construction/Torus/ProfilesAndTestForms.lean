import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus
open Classical in
def parabolicProfile (N : ℕ) (s : ℤ) : ℝ :=
  if |(s : ℝ)| ≤ halfSpan N + 1 then
    6 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) * (((N : ℝ) + 1) ^ 2 / 4 - (s : ℝ) ^ 2)
  else 0
def tiltedParabolicProfile (β : ℝ) (N : ℕ) (s : ℤ) : ℝ := parabolicProfile N s * (1 + β * (s : ℝ))
namespace ScaleData
variable (D : ScaleData)
end ScaleData
namespace GaugeSetting
variable (W : GaugeSetting)
end GaugeSetting
end YangMills.Construction.GeneralTorus
end
