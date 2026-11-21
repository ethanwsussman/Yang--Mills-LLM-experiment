import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfAWeightWithCores
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.StepGas
open YangMills.Construction.Dobrushin YangMills.Construction.TorusFields
open YangMills.Construction.StepSettings YangMills.Construction.CoreColumns
variable {R : StepSetup} {n : ℕ} [NeZero n]
def GasGround.IsNear (G : GasGround R n) (i j : G.GasSpin) : Prop := ¬ i.1.FarApart j.1
def GasGround.influenceMatrix (G : GasGround R n) (c : ℝ) : G.GasSpin → G.GasSpin → ℝ :=
  spinInfluence G.IsNear R.params.rt (fun i => i.1.core) (G.spinActivity c)
def GasGround.coreWeightFrom (G : GasGround R n) (Y : TorusSite n) (i : G.GasSpin) : ℝ :=
  coreWeight (R.params.rt / 2 ^ 6) Y i.1.core
structure GasGround.HasSmallColumns (G : GasGround R n) (off : G.GasSpin → Prop) (c : ℝ)
    (h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity c)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure (G.gibbsLawOff off)
  isSpecification : G.pairConstraint.IsSpecification (G.gibbsLawOff off)
    (G.pairConstraint.singleSiteKernel (G.referenceMeasureOff off) h.measurable_weightDensity)
  occupied_le : ∀ i σ, G.pairConstraint.IsAdmissible σ →
    (G.pairConstraint.singleSiteKernel (G.referenceMeasureOff off) h.measurable_weightDensity i σ).real
      {G.pairConstraint.vacant i}ᶜ ≤ G.spinActivity c i
  abs_integral_le : ∀ (Y : TorusSite n) (F : G.Config → ℝ), Measurable F → (∀ σ, |F σ| ≤ 1) →
    (∀ σ ∈ G.NoSpinMeets Y, F σ = 0) →
    |∫ σ, F σ ∂G.gibbsLawOff off| ≤ Real.exp (-(7 * c * R.coupling))
  influenceMatrix_nonneg : ∀ i j, 0 ≤ G.influenceMatrix c i j
  kernel_le : ∀ i j, i ≠ j → ∀ σ σ', G.pairConstraint.IsAdmissible σ → G.pairConstraint.IsAdmissible σ' →
    (∀ k, k ≠ j → σ k = σ' k) → ∀ B, MeasurableSet B →
      (G.pairConstraint.singleSiteKernel (G.referenceMeasureOff off) h.measurable_weightDensity i σ).real B ≤
        (G.pairConstraint.singleSiteKernel (G.referenceMeasureOff off) h.measurable_weightDensity i σ').real B +
          G.influenceMatrix c i j / 2
  column_le : ∀ (Y : TorusSite n) j, ∑ i, G.coreWeightFrom Y i * G.influenceMatrix c i j ≤
    G.coreWeightFrom Y j * Real.exp (-(6 * c * R.coupling))
  exp_le_half : Real.exp (-(6 * c * R.coupling)) ≤ 1 / 2
end YangMills.Construction.StepGas
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.StepGas YangMills.Construction.StepSettings YangMills.Construction.RenormalizationStepParameters
def GasColumnsSmall : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
      ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → ∀ off : G.GasSpin → Prop,
        ∃ h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity T.gasRate),
          G.HasSmallColumns off T.gasRate h
end YangMills.Construction.ClusterExpansionOfAStep
end
