import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseRelationsAtAllHeights
open ResponseProperties (ResponseRelations)
def ResponseRelationsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ResponseRelations L k
end YangMills.Construction.Tower.ResponseRelationsAtAllHeights
end
