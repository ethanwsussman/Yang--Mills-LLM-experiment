import YangMills.Construction.EuclideanFunctionals.CorrespondenceOfSystemsAndReconstructions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.PositivityAndEnvelope
open DefinitionComparison
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily),
    (OSPositive S ↔ IsOSPositive S) ∧ LowerEnvelopeIsAdmissible m S
end YangMills.Construction.EuclideanFunctionals.PositivityAndEnvelope
