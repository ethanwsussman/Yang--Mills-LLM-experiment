import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusLumps TorusFields FreeEnergies RenormalizationStepParameters
def chainResponseLocalityStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ Kr : ResponseParameters, Kr.Admissible (Tb.stepParameters y) → ∃ c x₀ : ℝ, 0 < c ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (β : ℝ) (k tp : ℕ), k ≤ tp → S.params = Kr →
      S.FollowsFlow β tp →
      (∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ flowCouplings (Tb.stepParameters y) β j) →
      x₀ ≤ flowCouplings (Tb.stepParameters y) β k →
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ w : PlaquetteWeight (fineSide (Tb.stepParameters y).side k n), ∀ᵐ u ∂(markedSampleLaw T β k n),
        ∃ F : TorusSite n → ℝ,
        response T β S.coeffs k n w u =
            ∑ z, F z + ∑ z, coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β)
              S.coeffs k n z (trivialField n) w ∧
        (∀ z, z ∉ weightSupportSites (Tb.stepParameters y).side k n w → F z = 0) ∧
        ∀ (z : TorusSite n) (n' : ℕ) [NeZero n'] (W' : TorusField n') (z' : TorusSite n') (m : ℕ)
          (ω' : (∅ : Finset (TorusSite n')) → (T.stage k).labels.Ω)
          (w' : PlaquetteWeight (fineSide (Tb.stepParameters y).side k n')),
          (Tb.stepParameters y).n₀ ≤ n' → TorusFields.IsCold (Tb.stepParameters y).threshold W' →
          (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) / 64 ≤ m →
          StatesAgreeNear (Tb.stepParameters y) (stageState T k n u).1 W' (stageState T k n u).2.1 ∅
            (stageState T k n u).2.2 ω' z z' m →
          WeightsAgreeAt (Tb.stepParameters y).side k z z' w w' →
          |F z - centeredResponse (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β)
              S.coeffs k) n' z' W' w'| ≤
            Real.exp (-(c * m)) * weightNorm (Tb.stepParameters y).side k w
end YangMills.Construction.ResponseInTheExpansion
end
