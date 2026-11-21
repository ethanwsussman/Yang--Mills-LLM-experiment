import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def formMeansAtWeightStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling →
    (∀ (d n : ℕ) [NeZero n], d ≤ S.logIndex + 1 → n = S.levelSide (S.lastSeparated + d) →
      ∀ (B : Finset (Fin Λ.k)) (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (A A' : Ω → ColourForm n), Measurable A → Measurable A' →
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w)| ∂μ ≤
        ENNReal.ofReal (C 0 * (S.range : ℝ) ^ (4 * B.card)) * (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^ (2 * B.card) ∧
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B 0| ∂μ ≤
        ENNReal.ofReal (C 0 * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(d : ℝ) / 4)) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^ (2 * B.card) ∧
      ∫⁻ w, ENNReal.ofReal |S.formProductMean d n B (A w) - S.formProductMean d n B (A' w)| ∂μ ≤
        ENNReal.ofReal (C 0 * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) (fun w => A w - A' w) *
          (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
            (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A +
              weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) n) (8 * (Λ.k : ENNReal)) A')) ^ (2 * B.card - 1)) ∧
    ∀ (N d n : ℕ) [NeZero n], S.lastSeparated + d = S.data.windowLevel → N ≤ d → n = S.levelSide (S.lastSeparated + N) →
      ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ →
      ∀ B : Finset (Fin Λ.k), |S.formProductMean N n B 0 - ∫ X, ∏ i ∈ B, S.halfForm d (S.data.period Λ.stepParams.side) i X ∂μ| ≤
        C 1 * (S.range : ℝ) ^ (4 * B.card) * (Λ.stepParams.side : ℝ) ^ (-(N : ℝ) / 4)
end YangMills.Construction.MomentLaw
end
