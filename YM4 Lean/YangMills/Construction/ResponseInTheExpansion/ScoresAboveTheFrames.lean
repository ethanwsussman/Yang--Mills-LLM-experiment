import YangMills.Construction.ResponseInTheExpansion.ColdImageAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheSmoothMoves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusFields TorusLumps StepCosts RenormalizationStepParameters WeightedResponses BlockAverages ColdStepAtMirrorFrames
variable {n : ℕ}
def torusBondInFrame (R : StepSetup) (c : TorusBond n) :
    (torusFrame R.params.side R.depth n).Site (torusFrame R.params.side R.depth n).top × Fin 4 :=
  (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top c.1, c.2)
def coldHalfDensity (R : StepSetup) [NeZero n] (V : TorusField n) :
    StepVariable (finiteCells (torusFrame R.params.side R.depth n)) → ℝ :=
  ballDensity (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
structure BondScoreAboveCold (R : StepSetup) [NeZero n] (V : TorusField n) (c : TorusBond n) : Prop where
  eq_at_point : ∀ k : StepVariable (finiteCells (torusFrame R.params.side R.depth n)), (∀ b, ‖k b‖ < R.ballRadius) →
    bondScore R.params R.coupling (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases c =
      bondFit R.params (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases c -
          3 / (2 * R.params.coupling * R.coupling) -
        (R.coupling ^ 2)⁻¹ * (coldHalfLawOf R).scoreRemainderAt (torusBondInFrame R c) k (coldTopField R V)
  score_integrable : MeasureTheory.Integrable fun k =>
    bondScore R.params R.coupling (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases c *
      coldHalfDensity R V k
  fit_integrable : MeasureTheory.Integrable fun k =>
    bondFit R.params (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases c * coldHalfDensity R V k
  remainder_integrable : MeasureTheory.Integrable fun k =>
    (coldHalfLawOf R).scoreRemainderAt (torusBondInFrame R c) k (coldTopField R V) * coldHalfDensity R V k
def scoresAboveFramesStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
      (∀ (k : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) (Y : TorusSite n),
        (∀ b, ‖k b‖ < R.ballRadius) →
        ∑ y ∈ sitesInBlocks R.params.side {Y},
            levelShare R.params.coupling R.params.side R.depth Finset.univ y (coldFieldAboveFrames R V k) +
            R.params.coupling / 2 * ∑ i : Fin 4,
              (bondFit R.params (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases (Y, i) +
                bondFit R.params (coldFieldAboveFrames R V k) V (coldChartSetting R V).bases (Y - TorusFields.unitStep n i, i)) =
          (coldHalfLawOf R).blockCost
            (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y) k
            (coldTopField R V)) ∧
      (∀ (h : LocalDensity) (k : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) (Y : TorusSite n),
        cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity h)
            (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y) k
            (coldTopField R V) =
          ∑ y ∈ sitesInBlocks R.params.side {Y}, centered h (n * R.params.side) y (coldFieldAboveFrames R V k)) ∧
      (∀ Y : TorusSite n, levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V =
        minimalCellShare R.params.coupling (finiteCells (torusFrame R.params.side R.depth n))
          (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y)
          (coldTopField R V)) ∧
      (∀ (Y : TorusSite n) (i : Fin 4) (back : Bool),
        cellBond (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y)
            i back =
          torusBondInFrame R (if back then Y - TorusFields.unitStep n i else Y, i)) ∧
      ∀ c : TorusBond n, BondScoreAboveCold R V c
end YangMills.Construction.ResponseInTheExpansion
end
