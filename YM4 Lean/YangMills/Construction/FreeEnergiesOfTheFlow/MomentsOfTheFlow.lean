import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open StepSettings RenormalizationStepParameters TorusLumps TorusFields StepGas WeightedResponses ColdStepAtMirrorFrames
def AtResponseParameters (P : ParameterAssignment → ResponseParameters → ℝ → Prop) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ T : ParameterAssignment, T.coupling = a → T.side = L → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom ColdRegimeEstimatesAt →
      T.rt ≤ rt₀ T.toChainParameters → C₀ ≤ T.derivBound → ∀ K : ResponseParameters,
      ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ExpansionHolds (T.stepParameters y) → P T K y
section Tower
variable {ℓ : TorusLumps.StepParameters}
structure ScoredStageTower (T : StageTower ℓ) where
  params : ResponseParameters
  setup : (u : ℕ) → ResponseSetup (T.stage u).toStepSetup
abbrev FinePlaquetteFunction : Type := (Fin 4 → ℝ) → ℝ
def fineWeight (f : FinePlaquetteFunction) (m : ℕ) : PlaquetteWeight m :=
  fun p => f (LevelTestFunctions.barycenterCoord p)
structure ScoredStageTower.FollowsFlow {Tb : ParameterAssignment} {y : ℝ} {T : StageTower (Tb.stepParameters y)}
    (S : ScoredStageTower T) (β : ℝ) (tp : ℕ) : Prop where
  isFlowStep : ∀ u ≤ tp, IsFlowStep Tb y β u (T.stage u).toStepSetup
  startsAtWilson : ResponseInTheExpansion.StageTower.StartsAtWilson T β
  bottom_coupling : T.base.coupling = β
  isCutoff_bottom : IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn
  marksMeasurable : T.MarksMeasurable
  params_eq : ∀ u, (S.setup u).responseParams = S.params
  N₀_eq : S.params.N₀ = Tb.N 0
  coeff_zero : (S.setup 0).coeff = 1
  score_zero : ∀ w, (S.setup 0).score w = 0
  cold_zero : ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (W : TorusField n) (f : FinePlaquetteFunction),
    (S.setup 0).cold n z W (fineWeight f _) = siteResponse z W (fineWeight f n)
  hull_zero : ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (W : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → (T.stage 0).labels.Ω) (f : FinePlaquetteFunction),
    (S.setup 0).hull n z W Y ω (fineWeight f _) = siteResponse z W (fineWeight f n)
  score_succ : ∀ u < tp, (S.setup (u + 1)).score = coarseLabelScore S.params.s₁ (S.setup u).score
  cold_succ : ∀ u < tp, (S.setup (u + 1)).cold = (S.setup u).coldStep
  hull_succ : ∀ u < tp, (S.setup (u + 1)).hull = (S.setup u).hullStep
  isAdmissible : ∀ u ≤ tp, (S.setup u).IsAdmissible
  coeff_near_one : ∀ u ≤ tp, |(S.setup u).coeff - 1| ≤ 1 / 4
def ScoredStageTower.coeffs {T : StageTower ℓ} (S : ScoredStageTower T) : ℕ → ℝ := fun u => (S.setup u).coeff
def ScoredStageTower.totalScore {T : StageTower ℓ} (S : ScoredStageTower T) (tp n : ℕ) [NeZero n]
    (u : MarkedSample ℓ tp n) : ℝ :=
  ∑ z : TorusSite n, siteScore (S.setup tp).score (stageState T tp n u).2.1 (stageState T tp n u).2.2 z
def ScoredStageTower.expScoreMean {T : StageTower ℓ} (S : ScoredStageTower T) (β : ℝ) (tp n : ℕ) [NeZero n] : ℝ :=
  ∫ u, Real.exp (S.totalScore tp n u) ∂(markedSampleLaw T β tp n)
def HasConditionalMean (T : StageTower ℓ) (β : ℝ) (w n : ℕ) [NeZero n] (F : MarkedSample ℓ w n → ℝ) : Prop :=
  Integrable F (markedSampleLaw T β w n) ∧ stageSigma T w n ≤ markedSampleMeasurableSpace ℓ w n
end Tower
namespace MomentSetup
def fineDist (m : ℕ) (x z : Fin 4 → ℝ) : ℝ :=
  TorusMetric.euclidNormVec fun a => LevelTestFunctions.circleRep m (x a - z a)
end MomentSetup
end YangMills.Construction.FreeEnergies
end
