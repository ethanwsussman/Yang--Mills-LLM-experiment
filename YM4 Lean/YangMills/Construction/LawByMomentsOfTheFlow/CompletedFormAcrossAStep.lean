import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormsOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.CompletedForms
def completedFormAcrossStepStatement : Prop :=
  MomentLaw.ForAllPoints fun Λ _ _ _ S => ∀ l, l < S.lastSeparated → ∀ (m : ℕ) [NeZero m],
    m = S.levelSide (l + 1) → ∀ i : Fin Λ.k,
    ∃ (Sm : Matrix (Fin 3 × MomentLaw.ChartBondIndex Λ.stepParams.side l m)
        (Fin 3 × MomentLaw.ChartBondIndex Λ.stepParams.side l m) ℝ)
      (lin : MomentLaw.ColourForm m → Fin 3 × MomentLaw.ChartBondIndex Λ.stepParams.side l m → ℝ) (c₀ : ℝ),
      Sm.IsSymm ∧ (∀ b, Measurable fun Z => lin Z b) ∧
      ∀ (Z : MomentLaw.ColourForm m) (η : MomentLaw.StepFluctuation Λ.stepParams.side l m),
        S.levelStepValue l m i Z (descendForm Λ l m Z η) =
          (1 / 2) * MomentLaw.colourEval (S.supportForm (l + 1) m i) Z Z + c₀ + ∑ b, lin Z b * η b +
            (1 / 2) * ∑ b, ∑ b', Sm b b' * η b * η b' ∧
        ∀ b, lin Z b + ∑ b', Sm b b' * η b' = S.levelStepGradient l m i Z (descendForm Λ l m Z η) b
end YangMills.Construction.CompletedForms
end
