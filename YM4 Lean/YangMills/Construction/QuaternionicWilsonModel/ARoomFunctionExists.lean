import YangMills.Construction.RoomFunctions.WitnessDepth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace QuaternionicWilsonModel
namespace RoomFunctionExists
def SuccIsSubexpGrowth : Prop :=
  RoomFunctions.IsSubexpGrowth fun s : ℕ => (s : ℝ) + 1
end RoomFunctionExists
end QuaternionicWilsonModel
end YangMills.Construction
end
