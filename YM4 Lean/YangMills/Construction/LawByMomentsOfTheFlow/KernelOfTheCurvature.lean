import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses CyclicFormula
def curvatureKernelBoundsStatement : Prop :=
  ∃ C : ℝ, ∀ (m : ℕ) [NeZero m],
    (∀ p p' : OrientedPlaquette m, |torusCurvatureProjection p p'| ≤ 1) ∧ (∀ P P' : IntPlaquette, |intCurvatureProjection P P'| ≤ 1) ∧
    (∀ (p p' : OrientedPlaquette m) (P P' : IntPlaquette), IsLift P p → IsLift P' p' →
      (∀ a, |intBarycenter P a - intBarycenter P' a| ≤ (m : ℝ) / 4) →
      |torusCurvatureProjection p p' - intCurvatureProjection P P'| ≤ C * ((m : ℝ) ^ 4)⁻¹ ∧
      (2 ≤ ‖intBarycenter P - intBarycenter P'‖ →
        |torusCurvatureProjection p p'| ≤ C * (‖intBarycenter P - intBarycenter P'‖ ^ 4)⁻¹)) ∧
    ∀ P P' : IntPlaquette, 2 ≤ ‖intBarycenter P - intBarycenter P'‖ →
      |intCurvatureProjection P P' - (Real.pi ^ 2 * ‖intBarycenter P - intBarycenter P'‖ ^ 4)⁻¹ *
          exteriorSquareMap (inversionMatrix (intBarycenter P - intBarycenter P')) P.2 P'.2| ≤
        C * (‖intBarycenter P - intBarycenter P'‖ ^ 5)⁻¹
end YangMills.Construction.MomentLaw
end
