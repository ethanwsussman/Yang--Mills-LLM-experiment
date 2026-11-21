import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice.GaugeFieldSpace
def inverseOnOppositeFamilies (a : ℝ) : Set (Link a → Matrices.ComplexMatrix2.specialUnitary) :=
  {U | ∀ e : Link a, U e.opposite = (U e)⁻¹}
def linkFamily {a : ℝ} (U : GaugeField a) : Link a → Matrices.ComplexMatrix2.specialUnitary :=
  fun e => U e
def TopologyStatement : Prop :=
  ∀ a : ℝ, 0 < a →
    IsClosed (inverseOnOppositeFamilies a) ∧
    Set.range (linkFamily (a := a)) = inverseOnOppositeFamilies a ∧
    Topology.IsInducing (linkFamily (a := a)) ∧
    CompactSpace (GaugeField a) ∧
    TopologicalSpace.MetrizableSpace (GaugeField a) ∧
    borel (GaugeField a) =
      ⨆ e : Link a, MeasurableSpace.comap (fun U : GaugeField a => U e)
        (borel Matrices.ComplexMatrix2.specialUnitary)
end InfiniteLattice.GaugeFieldSpace
end YangMills.Construction
end
