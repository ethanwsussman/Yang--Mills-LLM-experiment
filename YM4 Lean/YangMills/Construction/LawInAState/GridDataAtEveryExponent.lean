import YangMills.Construction.Lattice.GridDataOfEqualSides
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace EqualSideGrids
def AtEveryExponent : Prop :=
  ∀ (L m K : ℕ) (d : CellGrid L (K : ℤ)) (h : d.HasEqualSides m) (β : ℝ),
    SameGaugeFields h ∧ SameActionAndGibbsMeasure h β
end EqualSideGrids
end YangMills.Construction
end
