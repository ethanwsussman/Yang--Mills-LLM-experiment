import YangMills.Construction.ToriAtArbitraryCouplings.ClassesOfFunctionsSeparatedTuplesAndTheSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def gapAllLengths (E : Ambient) (X : s.FnTuple E) : ℝ≥0∞ :=
  if 2 ≤ X.length then s.supportGap E X else ∞
theorem gapAllLengths_of_two_le (E : Ambient) {X : s.FnTuple E} (h : 2 ≤ X.length) :
    s.gapAllLengths E X = s.supportGap E X :=
  if_pos h
theorem gapAllLengths_of_length_le_one (E : Ambient) {X : s.FnTuple E}
    (h : X.length ≤ 1) : s.gapAllLengths E X = ∞ :=
  if_neg (by omega)
theorem supportGap_of_length_le_one (E : Ambient) {X : s.FnTuple E} (h : X.length ≤ 1) :
    s.supportGap E X = ∞ :=
  iInf_eq_top.2 fun i => iInf_eq_top.2 fun k => iInf_eq_top.2 fun hik =>
    absurd (Fin.ext (by omega)) hik
theorem gapAllLengths_eq_supportGap (E : Ambient) (X : s.FnTuple E) :
    s.gapAllLengths E X = s.supportGap E X := by
  by_cases h : 2 ≤ X.length
  · exact s.gapAllLengths_of_two_le E h
  · rw [s.gapAllLengths_of_length_le_one E (by omega),
      s.supportGap_of_length_le_one E (by omega)]
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end
