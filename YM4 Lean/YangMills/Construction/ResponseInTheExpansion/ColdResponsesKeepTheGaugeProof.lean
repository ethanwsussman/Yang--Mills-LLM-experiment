import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsGaugeInvariant
import YangMills.Construction.ResponseInTheExpansion.ColdResponsesKeepTheGauge
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStepKeepsTheGaugeProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
namespace GaugeInvariance
private theorem integral_gaugeTransform {m : ℕ} [NeZero m] (hh : FieldHaar.HaarInvariantUnderSymmetries)
    (G : TorusFields.TorusSite m → BlockAverages.UnitQuaternion)
    (f' f : TorusFields.TorusField m → ℝ) (hf : ∀ W, f' (TorusFields.gaugeTransform G W) = f W) :
    ∫ W, f' W ∂(TorusFields.fieldHaar m) = ∫ W, f W ∂(TorusFields.fieldHaar m) := by apply _root_.YangMills.SharedProofs.p87219 <;> assumption
private theorem wilsonWeight_gaugeTransform (β : ℝ) (n : ℕ) [NeZero n]
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n) :
    TorusLumps.wilsonWeight β n (TorusFields.gaugeTransform g W) = TorusLumps.wilsonWeight β n W := by
  simp only [TorusLumps.wilsonWeight, dif_neg (NeZero.ne n), TorusFields.wilsonAction_gaugeTransform]
private theorem chainFunctional_gaugeTransform (hI : TorusLumps.KernelImageGaugeInvariant)
    {ℓ : TorusLumps.StepParameters} (hadm : ℓ.Admissible) (β : ℝ) (x : ℕ → ℝ) :
    ∀ (s n : ℕ) [NeZero n] (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n),
      WeightedResponses.chainFunctional ℓ β x s n (TorusFields.gaugeTransform g W) =
        WeightedResponses.chainFunctional ℓ β x s n W := by
  intro s
  induction s with
  | zero =>
    intro n _ g W
    exact wilsonWeight_gaugeTransform β n g W
  | succ s ih =>
    intro n _ g W
    haveI : NeZero (n * ℓ.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
    exact hI ℓ hadm (x s) (WeightedResponses.chainFunctional ℓ β x s) n (fun γ W' => ih (n * ℓ.side) γ W') g W
private theorem stepTransitionDensity_gaugeTransform (hk : TorusLumps.KernelGaugeInvariance)
    {ℓ : TorusLumps.StepParameters} (hadm : ℓ.Admissible) (y : ℝ) {n : ℕ} [NeZero n]
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField (n * ℓ.side))
    (V : TorusFields.TorusField n) (b : StepCosts.BaseChoice ℓ.side n) :
    WeightedResponses.stepTransitionDensity ℓ y
        (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge ℓ.side g) W) b (TorusFields.gaugeTransform g V) =
      WeightedResponses.stepTransitionDensity ℓ y W b V := by
  obtain ⟨-, hb, hker⟩ := hk ℓ hadm n g W V
  have hb' : TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0
        (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge ℓ.side g) W)) =
      TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W) := hb
  unfold WeightedResponses.stepTransitionDensity
  rw [hb']
  by_cases h : b ∈ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
  · simp only [h, if_true]
    have hc : ∀ c : (TorusLumps.stepBlockFrame ℓ.side n).Cell × Fin 4,
        TorusLumps.bondKernel ℓ y
            (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0
              (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge ℓ.side g) W))
            (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 (TorusFields.gaugeTransform g V)) b c =
          TorusLumps.bondKernel ℓ y (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
            (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V) b c := (hker y).1 b h
    rw [Finset.prod_congr rfl fun c _ => hc c]
  · simp only [h, if_false]
end GaugeInvariance
theorem coldResponseChain_gaugeTransform (hI : TorusLumps.KernelImageGaugeInvariant)
    (hk : TorusLumps.KernelGaugeInvariance) (hh : FieldHaar.HaarInvariantUnderSymmetries)
    (hs : ResponseInTheExpansion.BondScoreGaugeInvariantStatement) :
    ResponseInTheExpansion.coldResponseGaugeInvariantStatement := by
  intro ℓ hadm β x al t
  induction t with
  | zero =>
    intro n _ y g W h
    simp only [ResponseInTheExpansion.coldResponseChain, ResponseInTheExpansion.wilsonColdResponse,
      WeightedResponses.siteResponse, WeightedResponses.plaquetteEnergyOf,
      TorusFields.plaquetteEnergy_gaugeTransform]
  | succ t ih =>
    intro n _ Y g V h
    haveI : NeZero (n * ℓ.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
    have hD := GaugeInvariance.chainFunctional_gaugeTransform hI hadm β x t
    simp only [ResponseInTheExpansion.coldResponseChain, ResponseInTheExpansion.stepColdResponse,
      ResponseInTheExpansion.conditionalMean]
    rw [hI ℓ hadm (x t) (WeightedResponses.chainFunctional ℓ β x t) n (fun γ W' => hD (n * ℓ.side) γ W') g V]
    refine congrArg (· / TorusLumps.kernelImage ℓ (x t) (WeightedResponses.chainFunctional ℓ β x t) n V) ?_
    refine GaugeInvariance.integral_gaugeTransform hh (TorusLumps.blockConstantGauge ℓ.side g) _ _ fun W => ?_
    rw [hD (n * ℓ.side) _ W]
    refine congrArg₂ (· * ·) rfl ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GaugeInvariance.stepTransitionDensity_gaugeTransform hk hadm]
    by_cases hb : b ∈ TorusLumps.baseChoices ℓ (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
    · refine congrArg₂ (· * ·) rfl ?_
      have hsc : ResponseInTheExpansion.bondScoresAtSite ℓ (x t)
            (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge ℓ.side g) W)
            (TorusFields.gaugeTransform g V) b Y =
          ResponseInTheExpansion.bondScoresAtSite ℓ (x t) W V b Y := by
        unfold ResponseInTheExpansion.bondScoresAtSite
        refine Finset.sum_congr rfl fun i _ => ?_
        exact congrArg₂ (· + ·) (hs ℓ hadm (x t) n g W V b _ hb) (hs ℓ hadm (x t) n g W V b _ hb)
      rw [hsc, Finset.sum_congr rfl fun z _ => ih (n * ℓ.side) z (TorusLumps.blockConstantGauge ℓ.side g) W h]
    · have h0 : WeightedResponses.stepTransitionDensity ℓ (x t) W b V = 0 := by
        unfold WeightedResponses.stepTransitionDensity
        simp only [hb, if_false]
      rw [h0, zero_mul, zero_mul]
end YangMills.Construction.ResponseInTheExpansion
end
