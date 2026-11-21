import YangMills.Construction.ResponseInTheExpansion.LevelsOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open ClusterExpansionOfAStep BlockAverages TorusLumps TorusFields StepSettings StepGas WeightedResponses
section OneStep
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
def supportResponseTotal (f : PlaquetteWeight (fineSide R.params.side R.depth n)) (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω) : ℝ :=
  ∑ y ∈ weightSupportSites R.params.side R.depth n f, centeredHullResponse A.cold A.hull n y W Y ω f
def stepMeanShift (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : ℝ :=
  caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)
def centeredStepScore (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (W : TorusField (n * R.params.side)) (b : StepCosts.BaseChoice R.params.side n) : ℝ :=
  R.params.coupling / 2 * A.coeff * (∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
      blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y) - stepMeanShift A f
end OneStep
abbrev StateFunction (R : StepSetup) (n : ℕ) : Type :=
  (W : TorusField n) → (Y : Finset (TorusSite n)) → (Y → R.labels.Ω) → ℝ
def stateIntegral (R : StepSetup) (n : ℕ) [NeZero n] (H : StateFunction R n) : ℝ :=
  open Classical in
  ∫ W, ∑ Y ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
    ∫ ω, R.labelWeight n W Y ω * H W Y ω ∂(Measure.pi fun _ : Y => R.labels.μ) ∂(fieldHaar n)
def stateLIntegral (R : StepSetup) (n : ℕ) [NeZero n] (H : StateFunction R n) : ENNReal :=
  open Classical in
  ∫⁻ W, ∑ Y ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
    ∫⁻ ω, ENNReal.ofReal (R.labelWeight n W Y ω * H W Y ω) ∂(Measure.pi fun _ : Y => R.labels.μ)
      ∂(fieldHaar n)
section Stages
variable {P : StepParameters} (hL : ∀ c : ChainStage P, CoarseLabelFacts c.toStepSetup) (lam : ℝ)
  (x : ℕ → ℝ) (z₀ : StageWithResponse P)
abbrev stageStep (s : ℕ) : StepSetup := (stagesFrom hL lam x z₀ s).1.toStepSetup
abbrev stageResponse (s : ℕ) : ResponseSetup (stageStep hL lam x z₀ s) := (stagesFrom hL lam x z₀ s).2
abbrev StageWeight (s n : ℕ) : Type :=
  PlaquetteWeight (fineSide P.side (stageStep hL lam x z₀ s).depth n)
def accumulatedShift : (s n : ℕ) → [NeZero n] → StageWeight hL lam x z₀ s n → ℝ
  | 0, _, _, _ => 0
  | s + 1, n, _, f => accumulatedShift s (n * P.side) f +
      stepMeanShift (stageResponse hL lam x z₀ s) f
open Classical in
def jointMoment {ι : Type} : (s n : ℕ) → [NeZero n] → Finset ι → (ι → StageWeight hL lam x z₀ s n) →
    StateFunction (stageStep hL lam x z₀ s) n
  | 0, _, _, I, f, W, Y, ω => ∏ i ∈ I, supportResponseTotal (stageResponse hL lam x z₀ 0) (f i) W Y ω
  | s + 1, n, _, I, f, W, Y, ω => ∑ J ∈ I.powerset,
      caseMean (stageStep hL lam x z₀ s) (hotCoreSites (stageStep hL lam x z₀ s) W) W ⟨Y, ω⟩
        fun W' Yt ωt _ b => jointMoment s (n * P.side) J f W' Yt ωt *
          ∏ i ∈ I \ J, centeredStepScore (stageResponse hL lam x z₀ s) W (f i) W' b
def SeparatedAlong {ι : Type} (I : Finset ι) (D : ℕ → ℕ) :
    (s n : ℕ) → [NeZero n] → (ι → StageWeight hL lam x z₀ s n) → Prop
  | 0, _, _, _ => True
  | s + 1, n, _, f => SeparatedAlong I D s (n * P.side) f ∧
      2 ^ 10 * (stageStep hL lam x z₀ s).range ≤ D s ∧ 8 < D s ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ∀ Y ∈ thickening 2 (weightSupportSites P.side ((stageStep hL lam x z₀ s).depth + 1) n (f i)),
        ∀ Y' ∈ thickening 2 (weightSupportSites P.side ((stageStep hL lam x z₀ s).depth + 1) n (f j)),
          D s ≤ supDist Y Y'
open Classical in
def momentError {ι : Type} (ch : ℝ) (C : ℕ → ℝ) (D : ℕ → ℕ) : (s n : ℕ) → [NeZero n] → Finset ι →
    (ι → StageWeight hL lam x z₀ s n) → ℝ
  | 0, _, _, _, _ => 0
  | s + 1, n, _, I, f =>
    C I.card * (∑ i ∈ I, ((weightSupportSites P.side (stageStep hL lam x z₀ s).depth
        (n * P.side) (f i)).card : ℝ)) ^ 2 *
      Real.exp (-(P.rt * D s / 2 ^ 7)) *
      (∏ i ∈ I, (4 * ((stageResponse hL lam x z₀ s).responseParams.C₀ *
        ((weightSupportSites P.side (stageStep hL lam x z₀ s).depth
          (n * P.side) (f i)).card : ℝ)))) +
    Real.exp (2 ^ I.card * (I.card.factorial : ℝ) *
        Real.exp (-(7 * ch * (stageStep hL lam x z₀ s).coupling))) *
      ∑ J ∈ I.powerset, momentError ch C D s (n * P.side) J f *
        ∏ i ∈ I \ J, (2 * ((stageResponse hL lam x z₀ s).responseParams.C₀ *
          ((weightSupportSites P.side (stageStep hL lam x z₀ s).depth
            (n * P.side) (f i)).card : ℝ)))
end Stages
end ResponseInTheExpansion
end YangMills.Construction
end
