import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible
def ConstantsAreAdmissible : Prop :=
  Tower.FreeStrip.admissibleRates.Nonempty ∧
    (∀ δ₀ ∈ Tower.FreeStrip.halfSupRate, (Tower.FreeStrip.admissibleConstants δ₀).Nonempty) ∧
    ∃ δ₀ ∈ Tower.FreeStrip.halfSupRate, ∃ C₀ ∈ Tower.FreeStrip.infConstantAtHalfRate,
      δ₀ ∈ Ioc (0 : ℝ) (1 / 64) ∧ 1 ≤ C₀ ∧ Tower.FreeStrip.IsAdmissiblePair δ₀ C₀
end YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible
end
