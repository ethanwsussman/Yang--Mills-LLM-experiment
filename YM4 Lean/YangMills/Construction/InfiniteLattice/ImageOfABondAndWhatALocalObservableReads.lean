import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def SupportLiesIn (F : GaugeField 1 → ℂ) (O : Set AmbientSpace) : Prop :=
  LinksLieIn (observableSupport F) O
end YangMills.Construction.InfiniteLattice
