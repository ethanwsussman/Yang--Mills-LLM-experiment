import YangMills.Construction.ResponseInTheExpansion.IsometriesCarryTheScores
import YangMills.Construction.SixteenPointsOnASmallTorus.ScoresAreCarriedByAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields TorusLumps StepSettings StepCosts WeightedResponses
private def singletonLabels : LabelSpace where
  Ω := Unit
  μ := 0
  act := fun _ _ ω => ω
  act_borel := fun _ => measurable_snd
  act_one := fun _ _ => rfl
  act_mul := fun _ _ _ _ => rfl
  act_keeps := fun _ _ => MeasurePreserving.id _
  act_local := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  act_free := fun _ _ _ _ _ => rfl
private def bareStep (ℓ : StepParameters) (x : ℝ) : StepSetup where
  params := ℓ
  depth := 0
  coupling := x
  nextCoupling := x
  functional := fun _ _ => 0
  density := fun _ _ _ => 0
  labels := singletonLabels
  labelWeight := fun _ _ _ _ => 0
  clusterFactor := fun _ _ _ _ _ => 0
  siteDensity := fun _ _ _ _ _ => 0
  anchorRadius := 0
  barrierFn := fun _ => 0
private theorem stepTransitionDensity_eq (ℓ : StepParameters) (x : ℝ) {n : ℕ} [NeZero n] (U : TorusField (n * ℓ.side))
    (b : BaseChoice ℓ.side n) (V : TorusField n) :
    stepTransitionDensity ℓ x U b V = baseLaw (R := bareStep ℓ x) U b * ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 U) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c := by
  classical
  by_cases hb : b ∈ baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 U)
  · have h1 : stepTransitionDensity ℓ x U b V = (1 / ((baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 U)).card : ℝ)) *
        ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
          bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 U) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c := if_pos hb
    have h2 : baseLaw (R := bareStep ℓ x) U b = 1 / ((baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 U)).card : ℝ) := if_pos hb
    rw [h1, h2]
  · have h1 : stepTransitionDensity ℓ x U b V = 0 := if_neg hb
    have h2 : baseLaw (R := bareStep ℓ x) U b = 0 := if_neg hb
    rw [h1, h2, zero_mul]
private theorem baseLaw_ne_zero (ℓ : StepParameters) (x : ℝ) {n : ℕ} [NeZero n] {U : TorusField (n * ℓ.side)} {b : BaseChoice ℓ.side n}
    (hb : b ∈ baseChoices ℓ (fineLevelField ℓ n U)) : baseLaw (R := bareStep ℓ x) U b ≠ 0 := by
  classical
  have h2 : baseLaw (R := bareStep ℓ x) U b = 1 / ((baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 U)).card : ℝ) := if_pos hb
  rw [h2]
  have hc : 0 < (baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 U)).card := Finset.card_pos.mpr ⟨b, hb⟩
  positivity
theorem scoreIsometryInvariant (h : isometriesPreserveScoresStatement) : scoreIsometryInvariantStatement := by
  intro ℓ hadm x n _ hn g U U' V V' hU hV
  obtain ⟨-, e, he⟩ := h (bareStep ℓ x) hadm n hn g
  refine ⟨e, fun b => ?_⟩
  obtain ⟨h1, h2⟩ := he U U' V V' hU hV b
  refine ⟨?_, fun hb Y => h2 (baseLaw_ne_zero ℓ x hb) Y⟩
  rw [stepTransitionDensity_eq, stepTransitionDensity_eq]
  exact h1
end YangMills.Construction.SmallTorusCopies
end
