import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open WeightedResponses LevelTestFunctions CyclicFormula
def torusCycleSumNearLatticeStatement : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ R d : ℝ, 0 ≤ R → 0 < d → ∃ C : ℝ, ∀ (L : ℕ) [NeZero L] (P : LevelData k),
    P.SupAdmissible L R d →
    |3 * (if k = 2 then 1 / 2 else 1) * ∑ σ ∈ unorientedCyclicOrders k,
        ∑ p : Fin k → OrientedPlaquette (fineSide L P.windowLevel (P.period L)),
        (∏ i, P.testWeight L i _ (p i).1) * ∏ c : Fin k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) -
      latticeCycleSum L P.scaleLevel (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2) P.fn| ≤
      C * (L : ℝ) ^ (-(4 * ((P.windowLevel : ℝ) - (P.scaleLevel : ℝ))))
end YangMills.Construction.MomentLaw
end
