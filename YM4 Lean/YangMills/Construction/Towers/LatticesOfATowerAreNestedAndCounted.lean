import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SublatticesNestedAndCounted
def Statement : Prop :=
  ∀ L : ℕ, 0 < L → Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    Tower.FullSpace.SublatticesNested L k ∧ ∀ n : ℕ, 0 < n → Tower.SublatticeCounts L n k
end YangMills.Construction.Tower.SublatticesNestedAndCounted
end
