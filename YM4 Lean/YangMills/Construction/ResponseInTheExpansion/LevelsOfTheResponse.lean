import YangMills.Construction.ResponseInTheExpansion.ImageOfAResponse
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusLumps StepSettings WeightedResponses ClusterExpansionOfAStep
variable {ℓ : StepParameters}
def nextStepSetup (R : StepSetup) (h : CoarseLabelFacts R) (lam x'' : ℝ) : StepSetup where
  params := R.params
  depth := R.depth + 1
  coupling := R.nextCoupling
  nextCoupling := x''
  functional := kernelImage R.params R.coupling R.functional
  density := R.renormalizedDensity lam
  labels := coarseLabelSpace R h
  labelWeight := coarseWeightExpansion R
  clusterFactor := coarseFactorExpansion R
  siteDensity := R.stateDensity lam
  anchorRadius := R.anchorRadius
  barrierFn := R.barrierFn
def nextStage (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam x'' : ℝ) (c : ChainStage ℓ) :
    ChainStage ℓ :=
  c.next (hL c) x'' (c.toStepSetup.renormalizedDensity lam) (c.toStepSetup.stateDensity lam)
def nextResponseSetup (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam x'' : ℝ) {c : ChainStage ℓ}
    (A : ResponseSetup c.toStepSetup) (α : ℝ) (ρ₁ ρ₂ : LocalDensity) :
    ResponseSetup (nextStage hL lam x'' c).toStepSetup where
  responseParams := A.responseParams
  coeff := α
  score := coarseLabelScore A.responseParams.s₁ A.score
  cold := A.coldStep
  hull := A.hullStep
  siteRemainder := ρ₁
  totalRemainder := ρ₂
abbrev StageWithResponse (ℓ : StepParameters) : Type 1 := Σ c : ChainStage ℓ, ResponseSetup c.toStepSetup
open Classical in
def nextCoeff (R : StepSetup) (A : ResponseSetup R) (h : CoarseLabelFacts R) : ℝ :=
  if hn : ∃ α, StepHasResponseBounds R A h α then hn.choose else 0
open Classical in
def nextSiteRemainder (R : StepSetup) (A : ResponseSetup R) (h : CoarseLabelFacts R) : LocalDensity :=
  if hn : StepHasResponseBounds R A h (nextCoeff R A h) then hn.choose else fun _ _ _ => 0
open Classical in
def nextTotalRemainder (R : StepSetup) (A : ResponseSetup R) (h : CoarseLabelFacts R) : LocalDensity :=
  if hn : StepHasResponseBounds R A h (nextCoeff R A h) then hn.choose_spec.choose else fun _ _ _ => 0
def nextStageWithResponse (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam x'' : ℝ)
    (z : StageWithResponse ℓ) : StageWithResponse ℓ :=
  ⟨nextStage hL lam x'' z.1, nextResponseSetup hL lam x'' z.2 (nextCoeff z.1.toStepSetup z.2 (hL z.1))
    (nextSiteRemainder z.1.toStepSetup z.2 (hL z.1)) (nextTotalRemainder z.1.toStepSetup z.2 (hL z.1))⟩
def stagesFrom (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam : ℝ) (x : ℕ → ℝ)
    (z₀ : StageWithResponse ℓ) : ℕ → StageWithResponse ℓ
  | 0 => z₀
  | t + 1 => nextStageWithResponse hL lam (x (t + 2)) (stagesFrom hL lam x z₀ t)
end ResponseInTheExpansion
end YangMills.Construction
end
