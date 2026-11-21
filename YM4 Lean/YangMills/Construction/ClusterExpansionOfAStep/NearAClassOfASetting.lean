import YangMills.Construction.ClusterExpansionOfAStep.ClusterDefs
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
variable {R : StepSetup} {n : ℕ}
structure SettingCore (R : StepSetup) (n : ℕ) where
  core : Finset (TorusSite n)
  badBonds : Finset (TorusBond (n * R.params.side))
section Core
variable [NeZero n] (s : ChartSetting R n) (c : SettingCore R n)
def ChartSetting.storedComponents : Finset (Finset (TorusSite (n * R.params.side))) :=
  clusterComponents R.params.side R.range c.badBonds s.support c.core
def ChartSetting.storedBlockSet : Finset (TorusSite n) :=
  c.core ∪ coreBlocks R.params.side R.range ((s.storedComponents c).biUnion id)
open Classical in
def ChartSetting.freeBondsLeft : Finset (TorusBond (n * R.params.side)) :=
  (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∉ c.core ∧
    ¬ (parentBlock R.params.side b.1 ∈ s.storedBlockSet c ∧
      parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2) ∈ s.storedBlockSet c)
structure ChartSetting.IsCoreOf : Prop where
  free_eq : s.free = s.freeBondsLeft c
  hot_or_cold : (IsBlockTorusSide R.params n ∧
      c.core = thickening (2 * clusterRange R.nextCoupling) (torusHotSites R.params s.coarse)) ∨
    (c.core = ∅ ∧ IsCold (9 / 8 * R.params.threshold) s.coarse)
end Core
section Local
variable [NeZero n]
open Classical in
def blocksNear (L : ℕ) [NeZero L] (r : ℕ) (K : Finset (TorusSite (n * L))) : Finset (TorusSite n) :=
  Finset.univ.filter fun Y => (sitesInBlocks L {Y} ∩ thickening (5 * r) K).Nonempty
variable (s : ChartSetting R n) (N : Finset (TorusSite n))
open Classical in
def ChartSetting.freeNear : Finset s.free :=
  Finset.univ.filter fun b => bondBlock (R := R) b.1 ∈ N
open Classical in
def ChartSetting.extendByZero (ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3)) : FreeCoords s.free :=
  fun b => if h : b ∈ s.freeNear N then ζ ⟨b, h⟩ else 0
def ChartSetting.farEnergy : ℝ :=
  ∑ Y ∈ Finset.univ \ N, (R.coupling * blockCost R.params R.depth (s.field 0) s.coarse s.bases Y -
    s.blockDensity (s.field 0) Y - s.logJacobian (s.field 0) 0 Y)
def ChartSetting.localPotential (ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  s.potential (s.extendByZero N ζ) - s.farEnergy N
def ChartSetting.localIntegral : ℝ :=
  ∫ ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3),
    (∏ b, cutoffFactor R.ballRadius R.barrierFn (coordNorm (ζ b))) * Real.exp (-s.localPotential N ζ)
end Local
end StepSettings
end YangMills.Construction
end
