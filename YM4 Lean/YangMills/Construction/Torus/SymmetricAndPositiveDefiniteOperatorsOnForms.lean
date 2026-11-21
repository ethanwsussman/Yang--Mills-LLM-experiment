import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.GaugeSetting
variable (W : GaugeSetting)
def IsFormSymmetric (K : Module.End ℝ ↥W.formSubspace) : Prop :=
  ∀ A A' : ↥W.formSubspace, W.formInner A (K A') = W.formInner (K A) A'
def IsFormPosDef (K : Module.End ℝ ↥W.formSubspace) : Prop :=
  ∀ A : ↥W.formSubspace, A ≠ 0 → 0 < W.formInner A (K A)
end YangMills.Construction.GeneralTorus.GaugeSetting
end
