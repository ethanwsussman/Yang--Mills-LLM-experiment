import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def formsReadCurvatureStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => ∀ u ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], n = S.levelSide u →
    ∀ (y : TorusFields.TorusSite n) (sz : ℝ) (q : BondBilinear n),
    0 < sz → IsDecayingAbout Λ.stepParams sz y q →
    (AnnihilatesClosedForms q → ∃ κ : TorusFields.TorusPlaquette n → TorusFields.TorusPlaquette n → ℝ,
      (∀ X X' : TorusFields.TorusBond n → ℝ, bilinearEval q X X' =
        ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)),
        ∑ p' ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)),
          κ p p' * WeightedResponses.curl X p * WeightedResponses.curl X' p') ∧
      ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)),
        ∑ p' ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)), |κ p p'| *
          Real.exp (Λ.stepParams.weightRate / 8 *
            ((TorusFields.supDist p.1 y : ℝ) + (TorusFields.supDist p'.1 y : ℝ))) ≤ C 0 * sz) ∧
    (X₀ ≤ S.scaleCoupling → S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 →
      AnnihilatesGradients q → TorusFields.supDist y (S.originSite u n) ≤ S.radius →
      ∀ (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)), S.IsGoodConfig u n W Y →
        |colourEval q (S.cutoffColourForm u n W) (S.cutoffColourForm u n W)| ≤
          C 1 * sz * S.localCurvature u n W ^ 2)
end YangMills.Construction.MomentLaw
end
