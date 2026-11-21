import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.GeneralTorus
def ScaleData.IsLevelUnitTorus (D : ScaleData) (m K t : ℕ) : Prop :=
  0 < m ∧ 0 < K ∧ ∃ (h : t ≤ K) (m' r : ℕ), D = physicalInLevelUnits D.L D.blocking m K t h m' r
def GaugeSetting.IsLevelUnitSetting (W : GaugeSetting) (m K t : ℕ) : Prop :=
  W.data.IsLevelUnitTorus m K t ∧ W.mass = 1
end YangMills.Construction.GeneralTorus
