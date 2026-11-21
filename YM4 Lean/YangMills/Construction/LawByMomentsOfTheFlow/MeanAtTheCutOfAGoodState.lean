import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion BlockAverages
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
open Classical in
def cutoffMean (d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (W : TorusField n) (Y : Finset (TorusSite n)) : ℝ :=
  if S.IsGoodConfig (S.lastSeparated + d) n W Y then
    S.formProductMean d n B (S.cutoffColourForm (S.lastSeparated + d) n W) else 0
end MomentPoint
def cutoffMeanBoundsStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d ≤ S.logIndex →
    n = S.levelSide (S.lastSeparated + d) →
    Measurable (S.cutoffColourForm (S.lastSeparated + d) n) ∧
    Measurable (S.localCurvature (S.lastSeparated + d) n) ∧ ∀ B : Finset (Fin Λ.k),
    (∀ (X : ColourForm n) (K : ℝ), 0 ≤ K → (∀ p : OrientedPlaquette n, curlNorm X p.1 ≤ K) →
      |S.formProductMean d n B X| ≤
        C 0 * (S.range : ℝ) ^ (4 * B.card) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * K) ^ (2 * B.card)) ∧
    Continuous (S.formProductMean d n B) ∧
    (∀ W Y, |S.cutoffMean d n B W Y| ≤
      C 0 * (S.range : ℝ) ^ (4 * B.card) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ (2 * B.card)) ∧
    (∀ Y, Measurable fun W => S.cutoffMean d n B W Y) ∧
    (∀ (g : TorusSite n → UnitQuaternion) W Y,
      S.cutoffMean d n B (gaugeTransform g W) Y = S.cutoffMean d n B W Y) ∧
    ∀ W W' Y Y', (∀ c : TorusBond n,
        c.1 ∈ supBall (S.originSite (S.lastSeparated + d) n) (8 * S.rangeSq) →
        c.1 + TorusFields.unitStep n c.2 ∈ supBall (S.originSite (S.lastSeparated + d) n) (8 * S.rangeSq) →
        W c.1 c.2 = W' c.1 c.2) →
      Y ∩ supBall (S.originSite (S.lastSeparated + d) n) (8 * S.rangeSq) =
        Y' ∩ supBall (S.originSite (S.lastSeparated + d) n) (8 * S.rangeSq) →
      S.cutoffMean d n B W Y = S.cutoffMean d n B W' Y'
end YangMills.Construction.MomentLaw
end
