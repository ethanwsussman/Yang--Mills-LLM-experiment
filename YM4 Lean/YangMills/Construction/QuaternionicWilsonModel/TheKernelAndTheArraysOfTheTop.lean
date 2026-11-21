import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.TopAux
structure KernelAndFunctionalProperties (ℓ : TorusLumps.StepParameters) : Prop where
  baseChoices_nonempty : ∀ (n : ℕ) [NeZero n] (W : (TorusLumps.stepBlockFrame ℓ.side n).GaugeField 0),
    (TorusLumps.baseChoices ℓ W).Nonempty
  averagedKernel_pos : ∀ (x : ℝ) (n : ℕ) [NeZero n] (W : (TorusLumps.stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (TorusLumps.stepBlockFrame ℓ.side n).GaugeField 1),
    0 < TorusLumps.averagedKernel ℓ x W V
  averagedKernel_integral : ∀ (x : ℝ) (n : ℕ) [NeZero n] (W : (TorusLumps.stepBlockFrame ℓ.side n).GaugeField 0),
    ∫ V : TorusFields.TorusField n,
      TorusLumps.averagedKernel ℓ x W (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V)
        ∂(TorusFields.fieldHaar n) = 1
  averagedKernel_gauge : ∀ (x : ℝ) (n : ℕ) [NeZero n] (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField (n * ℓ.side)) (V : TorusFields.TorusField n),
    TorusLumps.averagedKernel ℓ x
        (TorusLumps.fineLevelField ℓ n (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge ℓ.side g) W))
        (TorusLumps.coarseLevelField ℓ n (TorusFields.gaugeTransform g V)) =
      TorusLumps.averagedKernel ℓ x (TorusLumps.fineLevelField ℓ n W) (TorusLumps.coarseLevelField ℓ n V)
  kernelImage_gauge : ∀ (x : ℝ) (D : TorusLumps.TorusFunctional) (n : ℕ) [NeZero n],
    (∀ (γ : TorusFields.TorusSite (n * ℓ.side) → BlockAverages.UnitQuaternion)
        (W : TorusFields.TorusField (n * ℓ.side)),
        D (n * ℓ.side) (TorusFields.gaugeTransform γ W) = D (n * ℓ.side) W) →
    ∀ (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n),
      TorusLumps.kernelImage ℓ x D n (TorusFields.gaugeTransform g V) = TorusLumps.kernelImage ℓ x D n V
  flowData_snd : ∀ (β : ℝ) (t : ℕ),
    (TotalDensityFlow.flowData ℓ β t).2 =
      WeightedResponses.chainFunctional ℓ β (TotalDensityFlow.coupling ℓ β) t
  chainFunctional_pos : ∀ (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n] (V : TorusFields.TorusField n),
    0 < WeightedResponses.chainFunctional ℓ β x t n V
  chainFunctional_gauge : ∀ (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n),
    WeightedResponses.chainFunctional ℓ β x t n (TorusFields.gaugeTransform g V) =
      WeightedResponses.chainFunctional ℓ β x t n V
  chainFunctional_integral : ∀ (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n],
    ∫ V, WeightedResponses.chainFunctional ℓ β x t n V ∂(TorusFields.fieldHaar n) =
      WeightedResponses.initialMass ℓ β t n
  initialMass_pos : ∀ (β : ℝ) (t n : ℕ) [NeZero n], 0 < WeightedResponses.initialMass ℓ β t n
def kernelAndFunctionalsStatement : Prop :=
  (∀ (L J : ℕ) (σ : ℝ), Odd L → 2 ^ 40 ≤ L → 1 ≤ J → 11 * 2 ^ 12 * J < L → σ ∈ Ioo (0 : ℝ) 1 →
    ∃ ℓ : TorusLumps.StepParameters, ℓ.side = L ∧ ℓ.baseDepth = J ∧ ℓ.threshold = σ ∧
      TotalDensitySystem.IsUnitMeshStepParameters ℓ) ∧
  ∀ ℓ : TorusLumps.StepParameters, TotalDensitySystem.IsUnitMeshStepParameters ℓ → KernelAndFunctionalProperties ℓ
end YangMills.Construction.TopAux
end
