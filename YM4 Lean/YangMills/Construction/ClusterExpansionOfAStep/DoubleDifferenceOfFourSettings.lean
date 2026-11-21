import YangMills.Construction.ClusterExpansionOfAStep.DoubleRatiosOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings RenormalizationStepParameters
open Classical in
def StepSettings.ChartSetting.freeCoordinate {R : StepSetup} {n : ℕ} (s : ChartSetting R n)
    (η : FreeCoords s.free) (b : TorusBond (n * R.params.side)) : EuclideanSpace ℝ (Fin 3) :=
  if h : b ∈ s.free then η ⟨b, h⟩ else 0
namespace ClusterExpansionOfAStep
variable {R : StepSetup} {n : ℕ}
structure FourPointsAgree [NeZero n] (s : Fin 2 → Fin 2 → ChartSetting R n)
    (η : ∀ i j, FreeCoords (s i j).free) (P P' : Finset (TorusSite n)) : Prop where
  first_agree : ∀ i j j' b, BondJoinsBlocks R.params.side P b →
    (s i j).freeCoordinate (η i j) b = (s i j').freeCoordinate (η i j') b
  second_agree : ∀ i i' j b, BondJoinsBlocks R.params.side P' b →
    (s i j).freeCoordinate (η i j) b = (s i' j).freeCoordinate (η i' j) b
  rest_agree : ∀ i j i' j' b, ¬ BondJoinsBlocks R.params.side P b → ¬ BondJoinsBlocks R.params.side P' b →
    (s i j).freeCoordinate (η i j) b = (s i' j').freeCoordinate (η i' j') b
def MixedDifferenceDecay : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup,
    R.params = T.stepParameters y → R.anchorRadius = T.ρA →
    y ≤ R.coupling → R.HasExpansions → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ (s : Fin 2 → Fin 2 → ChartSetting R n) (η : ∀ i j, FreeCoords (s i j).free)
        (P P' : Finset (TorusSite n)) (g : ℕ),
        (∀ i j, (s i j).IsAdmissible) → (∀ i j, (s i j).InBalls (η i j)) → IsFourSettings s P P' →
        FourPointsAgree s η P P' → (∀ y ∈ P, ∀ y' ∈ P', g ≤ supDist y y') → 16 ≤ g →
        (R.range : ℝ) / 16 ≤ (R.params.side * (g - 5) : ℕ) →
        (∀ i j, ∀ X ∈ chainComponents R.range (s i j).support,
          ¬ ((X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P))).Nonempty ∧
            (X ∩ thickening R.range (sitesInBlocks R.params.side (thickening 2 P'))).Nonempty)) →
        |(s 1 1).potential (η 1 1) + (s 0 0).potential (η 0 0) - (s 1 0).potential (η 1 0) -
            (s 0 1).potential (η 0 1)| ≤
          C * R.coupling * min (P.card : ℝ) P'.card *
            Real.exp (-(R.params.decayRate * (R.params.side * (g - 5) : ℕ) / 3))
end ClusterExpansionOfAStep
end YangMills.Construction
end
