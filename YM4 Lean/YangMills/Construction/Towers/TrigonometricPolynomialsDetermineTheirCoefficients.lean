import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def FourierCoeffsDetermined : Prop :=
  AbelianFieldFacts.FourierCoeffsUnique
end YangMills.Construction.Tower
end
