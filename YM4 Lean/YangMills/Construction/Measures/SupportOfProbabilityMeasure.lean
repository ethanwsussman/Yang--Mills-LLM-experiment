import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Measures
def probabilitySupport {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] : Set Y :=
  {y | ∀ U : Set Y, IsOpen U → y ∈ U → 0 < μ U}
end YangMills.Construction.Measures
