import YangMills.Construction.Torus.SettingOnThePhysicalTorusInLevelUnits
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.GeneralTorus
def GaugeSetting.IsExpansionSetting (W : GaugeSetting) (m K t : ℕ) : Prop :=
  W.IsLevelUnitSetting m K t
end YangMills.Construction.GeneralTorus
