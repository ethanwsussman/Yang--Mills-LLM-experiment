import YangMills.Construction.Continuum.SeparatedTuplesTheirConcatenationAndCombinationsOnFourSpace
import YangMills.Construction.FamiliesOfLimits.FamiliesOfLimitsAlongGrowingTori
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamiliesOfLimits.TupleHilbert
open Continuum.SeparatedFourTuples
variable {s : Conventions.StandingParameters}
def realPartMaps (S : SeparatedTupleFunctions s) : AmbientPoints.TupleMapFamily s .euclidean :=
  fun n hn X => (S n hn X).re
def centredMap (S : SeparatedTupleFunctions s) : SepTuple s → ℝ :=
  AmbientPoints.centredOfMaps (realPartMaps S)
end YangMills.Construction.FamiliesOfLimits.TupleHilbert
end
