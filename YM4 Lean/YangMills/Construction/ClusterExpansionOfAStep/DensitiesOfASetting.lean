import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts
namespace StepSettings
variable {R : StepSetup} {n : ℕ}
def ChartSetting.cutoffProduct (s : ChartSetting R n) (η : FreeCoords s.free) : ℝ :=
  ∏ b : s.free, cutoffFactor R.ballRadius R.barrierFn (coordNorm (η b))
def ChartSetting.blockCostAt [NeZero n] (s : ChartSetting R n) (Y : TorusSite n) (η : FreeCoords s.free) : ℝ :=
  blockCost R.params R.depth (s.field η) s.coarse s.bases Y
def ChartSetting.totalCost [NeZero n] (s : ChartSetting R n) (η : FreeCoords s.free) : ℝ :=
  ∑ Y : TorusSite n, s.blockCostAt Y η
def ChartSetting.logJacobianAt [NeZero n] (s : ChartSetting R n) (Y : TorusSite n) (η : FreeCoords s.free) : ℝ :=
  s.logJacobian (s.field η) η Y
def ChartSetting.blockDensityAt [NeZero n] (s : ChartSetting R n) (Y : TorusSite n) (η : FreeCoords s.free) : ℝ :=
  s.blockDensity (s.field η) Y
open Classical in
def ChartSetting.freeBondsOf [NeZero n] (s : ChartSetting R n) (Y : TorusSite n) : Finset s.free :=
  Finset.univ.filter fun b => bondBlock (R := R) b.1 = Y
open Classical in
def ChartSetting.restrictToBond (s : ChartSetting R n) (b : s.free) (η : FreeCoords s.free) : FreeCoords s.free :=
  fun b' => if b' = b then η b else 0
def ChartSetting.blockInteraction [NeZero n] (s : ChartSetting R n) (Y : TorusSite n) (η : FreeCoords s.free) : ℝ :=
  R.coupling * (∑ b ∈ s.freeBondsOf Y, ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => s.totalCost (v • η + τ • s.restrictToBond b η)) 0) -
    s.logJacobianAt Y η + s.logJacobianAt Y 0
def ChartSetting.blockGaussian [NeZero n] (s : ChartSetting R n) (lam : ℝ) (Y : TorusSite n) (η : FreeCoords s.free) : ℝ :=
  R.coupling * lam / 2 * ∑ b ∈ s.freeBondsOf Y, ‖η b‖ ^ 2
def StepSetup.gaussianLogMass (R : StepSetup) (lam : ℝ) : ℝ :=
  Real.log (∫ z : EuclideanSpace ℝ (Fin 3),
    cutoffFactor R.ballRadius R.barrierFn (coordNorm z) * Real.exp (-(R.coupling * lam / 2 * ‖z‖ ^ 2)))
def ChartSetting.totalInteraction [NeZero n] (s : ChartSetting R n) (η : FreeCoords s.free) : ℝ :=
  ∑ Y : TorusSite n, s.blockInteraction Y η
def weightedMean {free : Finset (TorusBond n)} (d G : FreeCoords free → ℝ) : ℝ :=
  (∫ η, G η * d η) / ∫ η, d η
def ChartSetting.interpolatedDensity [NeZero n] (s : ChartSetting R n) (lam τ : ℝ) (η : FreeCoords s.free) : ℝ :=
  s.cutoffProduct η * Real.exp (-(τ * s.totalInteraction η) - (1 - τ) * ∑ Y : TorusSite n, s.blockGaussian lam Y η)
def ChartSetting.perturbedDensity [NeZero n] (s : ChartSetting R n) (ν : ℝ) (η : FreeCoords s.free) : ℝ :=
  s.cutoffProduct η * Real.exp (-s.totalInteraction η + ν * ∑ Y : TorusSite n, s.blockDensityAt Y η)
def ChartSetting.blockActivity [NeZero n] (s : ChartSetting R n) (lam : ℝ) (Y : TorusSite n) : ℝ :=
  -(R.coupling * s.blockCostAt Y 0) + s.logJacobianAt Y 0 + R.gaussianLogMass lam * (s.freeBondsOf Y).card -
    (∫ τ in (0 : ℝ)..1, weightedMean (s.interpolatedDensity lam τ) fun η => s.blockInteraction Y η - s.blockGaussian lam Y η) +
    ∫ ν in (0 : ℝ)..1, weightedMean (s.perturbedDensity ν) (s.blockDensityAt Y)
section TwoSettings
variable {n' : ℕ}
def fineSite (L : ℕ) (Y : TorusSite n) (h o : Fin 4 → ℤ) : TorusSite (n * L) :=
  siteOfInt fun i => (L : ℤ) * (((Y i).cast : ℤ) + h i) + o i
abbrev NearBondIndex : Type := (Fin 4 → ℤ) × (Fin 4 → ℤ) × Fin 4
def nearBond (L : ℕ) (Y : TorusSite n) (q : NearBondIndex) : TorusBond (n * L) := (fineSite L Y q.1 q.2.1, q.2.2)
def IsNearIndex (L m : ℕ) (q : NearBondIndex) : Prop :=
  OffsetInBox m q.1 ∧ q.2.1 ∈ centredCube L
open Classical in
def ChartSetting.coordsByIndex [NeZero n] (s : ChartSetting R n) (Y : TorusSite n) (η : FreeCoords s.free) (q : NearBondIndex) :
    EuclideanSpace ℝ (Fin 3) :=
  if h : nearBond R.params.side Y q ∈ s.free then η ⟨_, h⟩ else 0
structure SettingsAgreeNear [NeZero n] [NeZero n'] (s : ChartSetting R n) (s' : ChartSetting R n') (Y : TorusSite n)
    (Y' : TorusSite n') (m : ℕ) : Prop where
  lt_extent : 2 * m + 2 < n
  lt_extent' : 2 * m + 2 < n'
  coarse_agree : FieldsAgreeNear s.coarse s'.coarse Y Y' m
  free_iff : ∀ q, IsNearIndex R.params.side m q →
    (nearBond R.params.side Y q ∈ s.free ↔ nearBond R.params.side Y' q ∈ s'.free)
  fine_eq : ∀ q, IsNearIndex R.params.side m q → nearBond R.params.side Y q ∉ s.free →
    s.fine (nearBond R.params.side Y q).1 q.2.2 = s'.fine (nearBond R.params.side Y' q).1 q.2.2
  frame_eq : ∀ q, IsNearIndex R.params.side m q → nearBond R.params.side Y q ∈ s.free →
    s.frame (nearBond R.params.side Y q) = s'.frame (nearBond R.params.side Y' q)
  support_iff : ∀ h o, OffsetInBox m h → o ∈ centredCube R.params.side →
    (fineSite R.params.side Y h o ∈ s.support ↔ fineSite R.params.side Y' h o ∈ s'.support)
  labelling_eq : ∀ h o (hz : fineSite R.params.side Y h o ∈ s.support)
    (hz' : fineSite R.params.side Y' h o ∈ s'.support), OffsetInBox m h →
    o ∈ centredCube R.params.side → s.labelling ⟨_, hz⟩ = s'.labelling ⟨_, hz'⟩
  bases_match : ∀ h, OffsetInBox m h → ∃ o, o ∈ centredCube R.params.side ∧
    toTorusSite (n * R.params.side)
        (s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
      fineSite R.params.side Y h o ∧
    toTorusSite (n' * R.params.side)
        (s'.bases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h))) =
      fineSite R.params.side Y' h o
def DependsWithin (L m : ℕ) (F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ) : Prop :=
  ∀ z z', (∀ q, IsNearIndex L m q → z q = z' q) → F z = F z'
end TwoSettings
end StepSettings
end YangMills.Construction
end
