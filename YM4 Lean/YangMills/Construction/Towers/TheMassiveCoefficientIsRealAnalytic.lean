import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveStiffnessFunctions
open Set
def StiffnessAnalytic : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    AnalyticOnNhd ℝ (massiveStiffness hL) (Ioi 0)
end YangMills.Construction.Tower.MassiveStiffnessFunctions
end
