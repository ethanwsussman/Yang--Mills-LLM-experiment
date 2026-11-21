import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.Torus.SymmetricAndPositiveDefiniteOperatorsOnForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice.DirichletOperators
namespace SeparatedClasses.CoarseGreenLowerBound
open SingleSequence SingleSequence.SequenceData
theorem levelSpacing_eq_coarseMesh (s : OperatorSetting) {W : GeneralTorus.GaugeSetting}
    (hW : s.toSequenceData.IsGaugeSetting W) (n : ℕ) :
    W.data.levelSpacing n = s.data.toLeveledParameters.coarseMesh n := by
  rw [hW.data_eq]
  have hL : (s.data.L : ℝ) ≠ 0 := by
    have := s.data.isAdmissible.2
    exact_mod_cast (by omega : s.data.L ≠ 0)
  simp only [GeneralTorus.ScaleData.levelSpacing, GeneralTorus.physicalInLevelUnits]
  unfold Conventions.LeveledParameters.coarseMesh
  rw [sub_eq_add_neg, zpow_add₀ hL, zpow_natCast]
end SeparatedClasses.CoarseGreenLowerBound
end YangMills.Construction
end
