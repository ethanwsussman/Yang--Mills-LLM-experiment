import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.WeightedResponses
open YangMills.Construction.FreeEnergies
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (Kr : ResponseParameters) (y : ℝ)
def tupleCumulantApproxAt : Prop :=
  ∀ vt : ℝ, 0 < vt → vt ≤ 1 → ∃ (Cq : ℕ → ℝ) (x₀ : ℝ),
    ∀ (q : ℕ) (β : ℝ) (k m : ℕ) (n : ℝ) (T : StageTower (ParameterAssignment.stepParameters Tb y)) (S : ScoredStageTower T),
      1 ≤ q → q ≤ 3 → InScaleWindow (ParameterAssignment.stepParameters Tb y) β k m n x₀ → S.params = Kr → S.FollowsFlow β k →
      ∀ f : Fin (q + 1) → PeriodicLattice.FourTorus (ParameterAssignment.stepParameters Tb y).side m → ℝ,
        IsSeparatedTestTuple (ParameterAssignment.stepParameters Tb y) m n vt f →
        ‖connectedCurvature β (fineSide (ParameterAssignment.stepParameters Tb y).side k (2 * (ParameterAssignment.stepParameters Tb y).side ^ m))
              (fun i => testWeight (ParameterAssignment.stepParameters Tb y).side k m (f i)) -
            Cumulants.mixedCumulant (markedSampleLaw T β k (2 * (ParameterAssignment.stepParameters Tb y).side ^ m))
              (fun i => response T β S.coeffs k (2 * (ParameterAssignment.stepParameters Tb y).side ^ m)
                (testWeight (ParameterAssignment.stepParameters Tb y).side k m (f i)))‖ ≤
          (couplingFlow (ParameterAssignment.stepParameters Tb y) β k).1 ^ (-(20 : ℝ)) ∧
        ∀ i, ∃ κ : ℝ, ∀ r : ℕ, 1 ≤ r →
          ∫ u, |response T β S.coeffs k (2 * (ParameterAssignment.stepParameters Tb y).side ^ m)
                (testWeight (ParameterAssignment.stepParameters Tb y).side k m (f i)) u - κ| ^ (2 * r)
              ∂(markedSampleLaw T β k (2 * (ParameterAssignment.stepParameters Tb y).side ^ m)) ≤
            (Cq r * n ^ 4 * (clusterRange (couplingFlow (ParameterAssignment.stepParameters Tb y) β k).1 : ℝ) ^ 4 *
              Real.log (couplingFlow (ParameterAssignment.stepParameters Tb y) β k).1) ^ (2 * r)
def tupleCumulantApproxStatement : Prop := AtResponseParameters tupleCumulantApproxAt
end YangMills.Construction.ResponseInTheExpansion
end
