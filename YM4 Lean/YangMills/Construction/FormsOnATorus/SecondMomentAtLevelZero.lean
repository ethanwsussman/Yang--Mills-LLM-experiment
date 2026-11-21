import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
def wilsonLimitFormSecondMomentStatement : Prop :=
  ∀ (a cK c C : ℝ) (L : ℕ) (Q : IntBond → IntBond → ℝ), 0 < c → IsLimitForm a cK c C L 0 Q →
    ∀ i l : Fin 4, i ≠ l → HasSum (fun z : Fin 4 → ℤ => Q (0, i) (z, i) * (z l : ℝ) ^ 2) (-2)
end YangMills.Construction.LimitForms
end
