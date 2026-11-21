import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts StepMarks
variable {n : ℕ}
open Classical in
def MarkedIntegrals.chartBondsInBlocks (L : ℕ) [NeZero L] [NeZero n] (A : Finset (TorusSite n)) :
    Finset (TorusBond (n * L)) :=
  (chartBonds L n).filter fun b => parentBlock L b.1 ∈ A
def StepSettings.StepSetup.bondMark (R : StepSetup) (V : TorusField n) (W : TorusField (n * R.params.side))
    (b : TorusBond (n * R.params.side)) : ℝ :=
  goodMark R.params R.anchorRadius R.barrierFn R.depth R.frameReach V W b
open Classical in
def StepSettings.StepSetup.avoidingPart (R : StepSetup) [NeZero n] (A : Finset (TorusSite n))
    (W : TorusField (n * R.params.side)) : ℝ :=
  (∑ Y ∈ Finset.univ.filter
      (fun Y : Finset (TorusSite (n * R.params.side)) =>
        IsHullState R.params R.range W Y ∧ Disjoint Y (sitesInBlocks R.params.side A)),
    ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω) ∂(Measure.pi fun _ : Y => R.labels.μ)).toReal
def StepSettings.StepSetup.markedIntegral (R : StepSetup) [NeZero n] (A : Finset (TorusSite n))
    (V : TorusField n) : ℝ :=
  ∫ W : TorusField (n * R.params.side), R.avoidingPart A W *
      averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) *
      ∏ b ∈ MarkedIntegrals.chartBondsInBlocks R.params.side A, R.bondMark V W b
    ∂(fieldHaar (n * R.params.side))
open Classical in
def MarkedIntegrals.precedingBlocks [NeZero n] (u : TorusSite n → ℝ) (Y : TorusSite n) :
    Finset (TorusSite n) :=
  Finset.univ.filter fun i => u i < u Y
def MarkedIntegrals.randomOrderLaw (n : ℕ) [NeZero n] : Measure (TorusSite n → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)
def StepSettings.StepSetup.blockDensityAt (R : StepSetup) [NeZero n] (Y : TorusSite n) (V : TorusField n) : ℝ :=
  ∫ u, (Real.log (R.markedIntegral (MarkedIntegrals.precedingBlocks u Y) V) -
      Real.log (R.markedIntegral (insert Y (MarkedIntegrals.precedingBlocks u Y)) V))
    ∂(MarkedIntegrals.randomOrderLaw n)
def StepSettings.StepSetup.blockDensity (R : StepSetup) : LocalDensity := fun n y V =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    R.blockDensityAt y V
def StepSettings.StepSetup.IsSymmetricWeight (R : StepSetup) : Prop :=
  ∀ n [NeZero n], R.params.n₀ ≤ n → Measurable (R.functional n) ∧ (∀ W, 0 ≤ R.functional n W) ∧
    (∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n),
      R.functional n (gaugeTransform g W) = R.functional n W) ∧
    ∀ (g : TorusIsometry) (W W' : TorusField n), g.Transports W W' → R.functional n W' = R.functional n W
end YangMills.Construction
end
