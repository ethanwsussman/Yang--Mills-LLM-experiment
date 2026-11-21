import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.PotentialOfAPlaquetteByAGreenFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def curvatureProjectionGreenStatement : Prop :=
  ∀ P P' : IntPlaquette,
    intCurvatureProjection P P' = planePairEntry (secondDiffMatrix latticeGreen (P.1 - P'.1)) P.2 P'.2
end YangMills.Construction.MomentLaw
end
