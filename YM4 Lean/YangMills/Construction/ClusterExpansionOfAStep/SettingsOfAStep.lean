import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames StepCosts TorusFields TorusLumps
structure StepSetup where
  params : StepParameters
  depth : ℕ
  coupling : ℝ
  nextCoupling : ℝ
  functional : TorusFunctional
  density : LocalDensity
  labels : LabelSpace
  labelWeight : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → labels.Ω) → ℝ
  clusterFactor : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → labels.Ω) → Finset (TorusSite n) → ℝ
  siteDensity : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → labels.Ω) → ℝ
  anchorRadius : ℝ
  barrierFn : ℝ → ℝ
variable (R : StepSetup)
def StepSetup.range : ℕ := clusterRange R.coupling
def StepSetup.frameReach : ℕ := R.range / 2 ^ 11
def StepSetup.ballRadius : ℝ := R.params.threshold / 64
variable {n : ℕ}
def StepSetup.nextRange (R : StepSetup) : ℕ := clusterRange R.nextCoupling
abbrev FreeCoords (free : Finset (TorusBond n)) : Type := free → EuclideanSpace ℝ (Fin 3)
structure ChartSetting (n : ℕ) where
  coarse : TorusField n
  region : Finset (TorusSite n)
  fine : TorusField (n * R.params.side)
  support : Finset (TorusSite (n * R.params.side))
  labelling : support → R.labels.Ω
  bases : BaseChoice R.params.side n
  free : Finset (TorusBond (n * R.params.side))
  bad : Finset (TorusBond (n * R.params.side))
variable {R}
def gaugeAt (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) : UnitQuaternion :=
  axialGauge 1 (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x)
open Classical in
def chartLink (s : ChartSetting R n) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (w : imaginaryQuaternions) : UnitQuaternion :=
  (gaugeAt s.fine x)⁻¹ *
    (if IsCrossingBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
      then expUnit w * s.coarse (parentBlock R.params.side x) i else expUnit w) *
    gaugeAt s.fine (x + TorusFields.unitStep (n * R.params.side) i)
def ChartSetting.frame (s : ChartSetting R n) (b : TorusBond (n * R.params.side)) : imaginaryQuaternions :=
  frameCoord R.params R.anchorRadius R.depth R.frameReach s.coarse b
open Classical in
def ChartSetting.field (s : ChartSetting R n) (η : FreeCoords s.free) : TorusField (n * R.params.side) :=
  fun x i =>
    if h : (x, i) ∈ s.free then chartLink s x i (s.frame (x, i) + toImaginary (η ⟨(x, i), h⟩))
    else s.fine x i
def coordNorm (v : EuclideanSpace ℝ (Fin 3)) : ℝ := ‖(toImaginary v : ℍ[ℝ])‖
def ChartSetting.InBalls (s : ChartSetting R n) (η : FreeCoords s.free) : Prop :=
  ∀ b, coordNorm (η b) ≤ R.ballRadius
def bondBlock (b : TorusBond (n * R.params.side)) : TorusSite n := parentBlock R.params.side b.1
def toCoords (w : imaginaryQuaternions) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK]
open Classical in
def ChartSetting.logJacobian [NeZero n] (s : ChartSetting R n) (W : TorusField (n * R.params.side))
    (η : FreeCoords s.free) (Y : TorusSite n) : ℝ :=
  ∑ i : Fin 4, logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params W s.bases (Y, i)) +
    ∑ b : s.free, if bondBlock (R := R) b.1 = Y then
      Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)) else 0
def ChartSetting.blockDensity [NeZero n] [NeZero (n * R.params.side)] (s : ChartSetting R n)
    (W : TorusField (n * R.params.side)) (Y : TorusSite n) : ℝ :=
  ∑ y ∈ sitesInBlocks R.params.side {Y}, R.siteDensity (n * R.params.side) y W s.support s.labelling
def ChartSetting.potential [NeZero n] (s : ChartSetting R n) (η : FreeCoords s.free) : ℝ :=
  ∑ Y : TorusSite n, (R.coupling * blockCost R.params R.depth (s.field η) s.coarse s.bases Y -
    s.blockDensity (s.field η) Y - s.logJacobian (s.field η) η Y)
structure ChartSetting.IsAdmissible [NeZero n] (s : ChartSetting R n) : Prop where
  subset_chart : s.free ⊆ chartBonds R.params.side n
  isHull : ∀ η, s.InBalls η → IsHullState R.params R.range (s.field η) s.support
  hotLumps_eq : ∀ η, s.InBalls η → torusHotLumps R.params (s.field η) = torusHotLumps R.params s.fine
  factor_ne_zero : ∀ η, s.InBalls η → ∀ X ∈ chainComponents R.range s.support,
    R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X ≠ 0
  far_from_support : ∀ b ∈ s.free, ∀ z ∈ s.support ∪ torusHotSites R.params s.fine,
    4 * R.range ≤ supDist b.1 z + R.params.side + 1
  curvature_lt : ∀ η, s.InBalls η → ∀ b ∈ s.free, ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν →
    supDist x b.1 ≤ 3 * R.range → curvature (s.field η) x μ ν < R.params.threshold / 4
  region_spec : (s.region = Finset.univ ∧ IsCold (9 / 8 * R.params.threshold) s.coarse) ∨
    (IsBlockTorusSide R.params n ∧
      s.region = Finset.univ \ thickening lumpRange (torusHotSites R.params s.coarse) ∧
      ∀ b ∈ s.free, ∀ z : TorusSite (n * R.params.side),
        parentBlock R.params.side z ∈ thickening (2 * R.nextRange) (torusHotSites R.params s.coarse) →
        4 * R.range ≤ supDist b.1 z + R.params.side + 1)
  near_frame : ∀ b ∈ s.free, ∀ b' ∈ chartBonds R.params.side n, b' ∉ s.free → supDist b.1 b'.1 ≤ 3 * R.range →
    ‖((chartCoord R.params s.coarse s.fine b' : imaginaryQuaternions) : ℍ[ℝ]) -
      ((s.frame b' : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius
  isBaseChoice : IsBaseChoice R.params.baseDepth (stepHotLumps R.params s.fine) s.bases
  cutoff_ne_zero : ∀ b ∈ chartBonds R.params.side n, b ∉ s.free → b ∉ s.bad →
    cutoffFactor R.ballRadius R.barrierFn
      ‖((chartCoord R.params s.coarse s.fine b : imaginaryQuaternions) : ℍ[ℝ]) -
        ((s.frame b : imaginaryQuaternions) : ℍ[ℝ])‖ ≠ 0
  half_le_meanNorm : ∀ η, s.InBalls η → ∀ b ∈ s.free, ∀ c : TorusBond n,
    supDist (parentBlock R.params.side b.1) c.1 ≤ 16 → 1 / 2 ≤ meanNorm R.params (s.field η) s.bases c
def bondBlockDist (b b' : TorusBond (n * R.params.side)) : ℕ :=
  supDist (bondBlock (R := R) b) (bondBlock (R := R) b')
def mixedSecondDeriv {free : Finset (TorusBond n)} (u : FreeCoords free → ℝ) (η : FreeCoords free)
    (b b' : free) (X X' : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  deriv (fun τ : ℝ => deriv (fun τ' : ℝ =>
    u (Function.update (Function.update η b (η b + τ • X)) b'
      ((Function.update η b (η b + τ • X)) b' + τ' • X'))) 0) 0
structure ChartSetting.HasDecay [NeZero n] (s : ChartSetting R n) (u : FreeCoords s.free → ℝ) (lam C : ℝ) :
    Prop where
  hessian_ge : ∀ η, s.InBalls η → ∀ v : FreeCoords s.free,
    R.coupling * lam / 4 * ∑ b, ‖v b‖ ^ 2 ≤
      deriv (deriv fun τ : ℝ => u (η + τ • v)) 0
  decay : ∃ M : s.free → s.free → ℝ, (∀ η, s.InBalls η → ∀ b b' X X', ‖X‖ = 1 → ‖X'‖ = 1 →
      |mixedSecondDeriv u η b b' X X'| ≤ M b b') ∧
    ∀ b, ∑ b', M b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) ≤
      R.coupling * lam / 8
  firstDeriv_le : ∀ η, s.InBalls η → ∀ b X, ‖X‖ = 1 →
    |deriv (fun τ : ℝ => u (Function.update η b (η b + τ • X))) 0| ≤ C * R.coupling
def StepSetup.HasExpansions (R : StepSetup) : Prop :=
  ColdExpansion R.params R.depth R.coupling R.functional R.density ∧
    HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity
def ChartSetting.partPotential [NeZero n] (s : ChartSetting R n) (ν : ℝ) (η : FreeCoords s.free) : ℝ :=
  ∑ Y : TorusSite n, (R.coupling * blockCost R.params R.depth (s.field η) s.coarse s.bases Y -
    ν * s.blockDensity (s.field η) Y - s.logJacobian (s.field η) η Y)
open Classical in
def ChartSetting.restrictTo (s : ChartSetting R n) (X : Finset s.free) (η : FreeCoords s.free) :
    FreeCoords s.free :=
  fun b => if b ∈ X then η b else 0
open Classical in
def ChartSetting.interpolatedPotential [NeZero n] (s : ChartSetting R n) (lam v : ℝ) (X : Finset s.free)
    (η : FreeCoords s.free) : ℝ :=
  v * s.potential η + (1 - v) * (s.potential (s.restrictTo X η) +
    R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2)
end StepSettings
end YangMills.Construction
end
