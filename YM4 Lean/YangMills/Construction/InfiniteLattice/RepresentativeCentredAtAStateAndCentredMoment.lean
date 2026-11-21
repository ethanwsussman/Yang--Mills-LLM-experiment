import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CentredRepresentative
open YangMills.Construction.InfiniteLattice YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {a : ℝ}
def centredProduct (ν : GaugeFieldProbability a) (X : FunctionTuple s .euclidean)
    (U : GaugeField a) : ℝ :=
  ∏ i, (smearedEnergy (X.2 i) U - ∫ V, smearedEnergy (X.2 i) V ∂ν.1)
def pairedCentredProduct (ρ ν : GaugeFieldProbability a)
    (X : FunctionTuple s .euclidean) : ℝ :=
  ∫ U, centredProduct ν X U ∂ρ.1
def centredMoment (ν : GaugeFieldProbability a) (X : FunctionTuple s .euclidean) : ℝ :=
  pairedCentredProduct ν ν X
end YangMills.Construction.CentredRepresentative
