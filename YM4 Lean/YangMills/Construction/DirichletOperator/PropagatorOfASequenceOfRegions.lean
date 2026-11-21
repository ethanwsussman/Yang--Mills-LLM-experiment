import YangMills.Construction.DirichletOperator.ExpansionTerms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RegionSequence
namespace Propagator.PropagatorConstants
variable (c : PropagatorConstants)
structure ValidFor (L : ℕ) : Prop where
  delta_pos : 0 < c.δ
  delta_le_one : c.δ ≤ 1
  gamma_pos : 0 < c.γ
  one_le_B : 1 ≤ c.B
  conclusion : ∀ (K m M R₁ : ℕ) (N : NestedRegions), N.L = L → IsUnitSeparated N K m M R₁ →
    c.blockLower ≤ (M : ℝ) → c.gapLower ≤ (R₁ : ℝ) * (M : ℝ) → c.Conclusion N M
end Propagator.PropagatorConstants
namespace Propagator.SequenceOfRegions
def chosenConstants (L : ℕ) : PropagatorConstants :=
  Classical.epsilon fun c : PropagatorConstants => c.ValidFor L
end Propagator.SequenceOfRegions
end YangMills.Construction
