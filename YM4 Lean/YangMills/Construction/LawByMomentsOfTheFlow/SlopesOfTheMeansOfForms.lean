import YangMills.Construction.LawByMomentsOfTheFlow.GaussianAgainstACutLaw
import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps MomentMethod ColdStepAtMirrorFrames
def chartColourForm {L : ℕ} [NeZero L] {u n : ℕ} [NeZero n] (k : BondField (ChartBondIndex L u n)) : ColourForm (n * L) :=
  fun e => extendChart fun b => k b e
def formMeanDerivBoundStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex → n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ B : Finset (Fin Λ.k),
    ContDiff ℝ 2 (S.formProductMean d (n * Λ.stepParams.side) B) ∧
    (∃ (Cg : ℝ) (k : ℕ), ∀ (A : ColourForm (n * Λ.stepParams.side)) (l : ℕ), l ≤ 2 →
      ‖iteratedFDeriv ℝ l (S.formProductMean d (n * Λ.stepParams.side) B) A‖ ≤ Cg * (1 + ‖A‖) ^ k) ∧
    ∀ (w : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n → ℝ) (W : ℝ), (∀ b, 0 ≤ w b) → 0 ≤ W →
      (∀ (b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) (p : TorusPlaquette (n * Λ.stepParams.side)),
        TorusFields.supDist (toTorusSite (n * Λ.stepParams.side) b.1.1) p.1 ≤ 1 →
          w b * Real.sqrt (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p) ≤ W) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ColourForm (n * Λ.stepParams.side)),
        Measurable A →
        ∑ j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n, ENNReal.ofReal (w j.2) *
            eLpNorm (fun z => fderiv ℝ (S.formProductMean d (n * Λ.stepParams.side) B) (A z)
              (chartColourForm (unitVariation j))) 2 μ ≤
          ENNReal.ofReal (C 0 * W * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 2)) *
            (1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
              weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side))
                (8 * (Λ.k : ENNReal)) A) ^ (2 * B.card - 1)
end YangMills.Construction.MomentLaw
end
