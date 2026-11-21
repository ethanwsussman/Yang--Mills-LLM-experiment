import YangMills.Construction.ClusterExpansionOfAStep.FieldsOfTwoSettings
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
theorem StepSettings.fieldsAgreeOfCoordsAgree_holds : StepSettings.FieldsAgreeOfCoordsAgree := by
  intro R n n' _ _ s s' Y Y' m k η η' o hadm hn hn' hf _ hag hk1 hk hnear ho
  exact BlockOffsets.fieldsAgreeNear_of_settings hadm.L_odd hn hn' hf hag hk1 hk hnear ho
end YangMills.Construction
