import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses
def supportFormCurvatureKernelStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ i : Fin Λ.k,
    ∃ κ : TorusPlaquette (S.levelSide S.lastSeparated) → TorusPlaquette (S.levelSide S.lastSeparated) → ℝ,
    (∀ X X' : ColourForm (S.levelSide S.lastSeparated),
      colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) X X' =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        κ p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p') ∧
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
      |κ p p'| * (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹ *
        (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p')⁻¹ ≤ C 0 * (S.range : ℝ) ^ 4 ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X X' : Ω → ColourForm (S.levelSide S.lastSeparated))
      (q : ℝ), 1 ≤ q → Measurable X → Measurable X' →
      eLpNorm (fun e => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) (X e) (X' e))
          (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (C 0 * (S.range : ℝ) ^ 4) *
          weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
            (ENNReal.ofReal (2 * q)) X *
          weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated))
            (ENNReal.ofReal (2 * q)) X'
end YangMills.Construction.MomentLaw
end
