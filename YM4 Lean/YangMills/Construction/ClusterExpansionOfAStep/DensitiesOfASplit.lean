import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open TorusFields StepSettings ColdStepAtMirrorFrames
variable {R : StepSetup} {n : ℕ}
structure BlockDensitySplit (R : StepSetup) (n : ℕ) (free : Finset (TorusBond (n * R.params.side))) where
  cost : TorusSite n → FreeCoords free → ℝ
  logJacobian : TorusSite n → FreeCoords free → ℝ
  density : TorusSite n → FreeCoords free → ℝ
def cutoffProd {free : Finset (TorusBond (n * R.params.side))} (η : FreeCoords free) : ℝ :=
  ∏ b : free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η b))
open Classical in
def freeBondsAt [NeZero n] (free : Finset (TorusBond (n * R.params.side))) (Y : TorusSite n) : Finset free :=
  Finset.univ.filter fun b => bondBlock (R := R) b.1 = Y
open Classical in
def singleBond {free : Finset (TorusBond (n * R.params.side))} (b : free) (η : FreeCoords free) : FreeCoords free :=
  fun b' => if b' = b then η b else 0
def gaussianPart [NeZero n] {free : Finset (TorusBond (n * R.params.side))} (lam : ℝ) (Y : TorusSite n)
    (η : FreeCoords free) : ℝ :=
  R.coupling * lam / 2 * ∑ b ∈ freeBondsAt free Y, ‖η b‖ ^ 2
namespace BlockDensitySplit
variable [NeZero n] {free : Finset (TorusBond (n * R.params.side))} (D : BlockDensitySplit R n free)
def totalCost (η : FreeCoords free) : ℝ := ∑ Y : TorusSite n, D.cost Y η
def potential (η : FreeCoords free) : ℝ :=
  ∑ Y : TorusSite n, (R.coupling * D.cost Y η - D.density Y η - D.logJacobian Y η)
def interaction (Y : TorusSite n) (η : FreeCoords free) : ℝ :=
  R.coupling * (∑ b ∈ freeBondsAt free Y, ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => D.totalCost (v • η + τ • singleBond b η)) 0) -
    D.logJacobian Y η + D.logJacobian Y 0
def totalInteraction (η : FreeCoords free) : ℝ := ∑ Y : TorusSite n, D.interaction Y η
def interpolatedDensity (lam τ : ℝ) (η : FreeCoords free) : ℝ :=
  cutoffProd η * Real.exp (-(τ * D.totalInteraction η) - (1 - τ) * ∑ Y : TorusSite n, gaussianPart lam Y η)
def perturbedDensity (ν : ℝ) (η : FreeCoords free) : ℝ :=
  cutoffProd η * Real.exp (-D.totalInteraction η + ν * ∑ Y : TorusSite n, D.density Y η)
def activity (lam : ℝ) (Y : TorusSite n) : ℝ :=
  -(R.coupling * D.cost Y 0) + D.logJacobian Y 0 + R.gaussianLogMass lam * (freeBondsAt free Y).card -
    (∫ τ in (0 : ℝ)..1, weightedMean (D.interpolatedDensity lam τ) fun η =>
      D.interaction Y η - gaussianPart lam Y η) +
    ∫ ν in (0 : ℝ)..1, weightedMean (D.perturbedDensity ν) (D.density Y)
end BlockDensitySplit
variable [NeZero n]
def _root_.YangMills.Construction.StepSettings.ChartSetting.densitySplit (s : ChartSetting R n) :
    BlockDensitySplit R n s.free :=
  ⟨s.blockCostAt, s.logJacobianAt, s.blockDensityAt⟩
def _root_.YangMills.Construction.StepSettings.ChartSetting.restrictedSplit (s : ChartSetting R n) (lam : ℝ)
    (X : Finset s.free) : BlockDensitySplit R n s.free where
  cost Y η := s.blockCostAt Y (s.restrictTo X η) + lam / 2 * ∑ b ∈ freeBondsAt s.free Y \ X, ‖η b‖ ^ 2
  logJacobian Y η := s.logJacobianAt Y (s.restrictTo X η)
  density Y η := s.blockDensityAt Y (s.restrictTo X η)
def openBallsIn (R : StepSetup) {n : ℕ} (free : Finset (TorusBond (n * R.params.side))) : Set (FreeCoords free) :=
  {η | ∀ b, coordNorm (η b) < R.ballRadius}
structure BlockDensitySplit.IsRegular {free : Finset (TorusBond (n * R.params.side))}
    (D : BlockDensitySplit R n free) : Prop where
  cost_smooth : ∃ U : Set (FreeCoords free), IsOpen U ∧ (∀ η, (∀ b, coordNorm (η b) ≤ R.ballRadius) → η ∈ U) ∧
    ContDiffOn ℝ 1 D.totalCost U
  measurable_logJacobian : ∀ Y, Measurable ((openBallsIn R free).indicator (D.logJacobian Y))
  measurable_density : ∀ Y, Measurable ((openBallsIn R free).indicator (D.density Y))
  bounded : ∃ M : ℝ, ∀ η ∈ openBallsIn R free, ∀ Y, |D.logJacobian Y η| ≤ M ∧ |D.density Y η| ≤ M
end ClusterExpansionOfAStep
end YangMills.Construction
end
