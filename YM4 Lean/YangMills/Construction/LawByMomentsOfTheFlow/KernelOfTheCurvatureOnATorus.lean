import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.PotentialOfAPlaquetteByAGreenFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open PeriodicLattice.VectorClasses
def torusCurvatureProjectionGreenStatement : Prop :=
  ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ (p p' : WeightedResponses.OrientedPlaquette n) (P P' : IntPlaquette),
    IsLift P p → IsLift P' p' →
    torusCurvatureProjection p p' =
      planePairEntry (secondDiffMatrix (fun w => (greenOnVectors n w).re) (P.1 - P'.1)) P.2 P'.2
end YangMills.Construction.MomentLaw
end
