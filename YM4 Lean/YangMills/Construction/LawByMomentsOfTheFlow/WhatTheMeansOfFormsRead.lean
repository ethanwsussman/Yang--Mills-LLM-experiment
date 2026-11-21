import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses TorusFields
def formMeansStatement : Prop :=
  ForAllPoints fun Λ C _ _ S =>
    (∀ (d n : ℕ) [NeZero n], S.lastSeparated + d ≤ S.data.windowLevel → n = S.levelSide (S.lastSeparated + d) → ∀ q : ℕ, 1 ≤ q →
      weightedCurvatureNorm (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d n) (fun _ => 1) (q : ENNReal)
        (descendWithNoise Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d n 0) ≤ ENNReal.ofReal (C q)) ∧
    (∀ (d n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (B : Finset (Fin Λ.k)) (A A' : ColourForm n),
      (∀ e p, curl (A e) p = curl (A' e) p) →
      S.formProductMean d n B A = S.formProductMean d n B A') ∧
    (∀ (d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (A : ColourForm n) (R : Matrix (Fin 3) (Fin 3) ℝ),
      R ∈ Matrix.orthogonalGroup (Fin 3) ℝ →
      S.formProductMean d n B (fun e b => ∑ e' : Fin 3, R e e' * A e' b) = S.formProductMean d n B A) ∧
    (∀ (n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (A : ColourForm n),
      S.formProductMean 0 n B A = S.formProduct S.lastSeparated n B A) ∧
    (∀ (d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) (A : ColourForm n),
      S.formProductMean (d + 1) n B A = ∫ η, S.formProductMean d (n * Λ.stepParams.side) B
        (fun e b => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d) A e b +
          S.scaleCoupling ^ (-(1 / 2) : ℝ) * extendFluctuation η e b)
        ∂(fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n)) ∧
    ∀ e d : ℕ, S.lastSeparated + e + d = S.data.windowLevel →
      ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + e + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + e + d) (S.data.period Λ.stepParams.side)) μ →
      ∀ B : Finset (Fin Λ.k),
      (fun X => S.formProductMean e (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) B
          (fun c b => S.scaleCoupling ^ (-(1 / 2) : ℝ) *
            chainTop (S.lastSeparated + e) _ (chainDescend (S.lastSeparated + e) d (S.data.period Λ.stepParams.side) X) c b)) =ᵐ[μ]
        μ[fun X => S.formProduct S.lastSeparated _ B (fun c b => S.scaleCoupling ^ (-(1 / 2) : ℝ) *
            chainTop S.lastSeparated _ (chainDescend S.lastSeparated e _
              (chainDescend (S.lastSeparated + e) d (S.data.period Λ.stepParams.side) X)) c b) |
          MeasurableSpace.comap (fun X (c : Fin 3) (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
            curl (chainTop (S.lastSeparated + e) _ (chainDescend (S.lastSeparated + e) d (S.data.period Λ.stepParams.side) X) c) p)
            inferInstance]
end YangMills.Construction.MomentLaw
end
