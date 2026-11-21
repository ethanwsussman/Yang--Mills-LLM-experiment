import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusLumps TorusFields StepCosts BlockAverages LumpContours
instance : SecondCountableTopology UnitQuaternion := TopologicalSpace.Subtype.secondCountableTopology _
theorem eq_haarUnit_of_isMulLeftInvariant (μ : Measure UnitQuaternion) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] : μ = haarUnit := by
  have h := Measure.haarMeasure_unique μ (⊤ : TopologicalSpace.PositiveCompacts UnitQuaternion)
  have h1 : μ ((⊤ : TopologicalSpace.PositiveCompacts UnitQuaternion) : Set UnitQuaternion) = 1 := by simp
  rw [h1, one_smul] at h
  exact h
instance : haarUnit.IsMulRightInvariant := by
  constructor
  intro g
  have : (Measure.map (· * g) haarUnit).IsMulLeftInvariant := isMulLeftInvariant_map_mul_right g
  have : IsProbabilityMeasure (Measure.map (· * g) haarUnit) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_haarUnit_of_isMulLeftInvariant _
variable {n : ℕ}
theorem continuous_fieldAtBond (c : TorusBond n) :
    Continuous fun q : TorusField n × UnitQuaternion => fieldAtBond q.1 c q.2 := by
  refine continuous_pi fun z => continuous_pi fun i => ?_
  by_cases hz : z = c.1
  · subst hz
    by_cases hi : i = c.2
    · subst hi
      simpa [fieldAtBond] using continuous_snd
    · simpa [fieldAtBond, hi] using (by fun_prop : Continuous fun a : TorusField n × UnitQuaternion => a.1 c.1 i)
  · simpa [fieldAtBond, hz] using (by fun_prop : Continuous fun a : TorusField n × UnitQuaternion => a.1 z i)
def bondLeftMul (c : TorusBond n) (h : UnitQuaternion) (V : TorusField n) : TorusField n :=
  fieldAtBond V c (h * V c.1 c.2)
theorem bondLeftMul_eq_ite (c : TorusBond n) (h : UnitQuaternion) (V : TorusField n) :
    bondLeftMul c h V = fun z i => (if z = c.1 ∧ i = c.2 then (fun g : UnitQuaternion => h * g) else id) (V z i) := by
  funext z i
  by_cases hz : z = c.1
  · subst hz
    by_cases hi : i = c.2
    · subst hi
      simp [bondLeftMul, fieldAtBond]
    · simp [bondLeftMul, fieldAtBond, hi]
  · simp [bondLeftMul, fieldAtBond, hz]
theorem measurePreserving_bondLeftMul [NeZero n] (c : TorusBond n) (h : UnitQuaternion) :
    MeasurePreserving (bondLeftMul c h) (fieldHaar n) (fieldHaar n) := by
  have hone : ∀ (z : TorusSite n) (i : Fin 4), MeasurePreserving
      (if z = c.1 ∧ i = c.2 then (fun g : UnitQuaternion => h * g) else id) haarUnit haarUnit := by
    intro z i
    split_ifs
    · exact measurePreserving_mul_left haarUnit h
    · exact MeasurePreserving.id _
  have hrow : ∀ z : TorusSite n, MeasurePreserving
      (fun (r : Fin 4 → UnitQuaternion) i => (if z = c.1 ∧ i = c.2 then (fun g : UnitQuaternion => h * g) else id) (r i))
      (Measure.pi fun _ : Fin 4 => haarUnit) (Measure.pi fun _ : Fin 4 => haarUnit) := fun z =>
    measurePreserving_pi _ _ (hone z)
  have hall := measurePreserving_pi (fun _ : TorusSite n => Measure.pi fun _ : Fin 4 => haarUnit)
    (fun _ : TorusSite n => Measure.pi fun _ : Fin 4 => haarUnit) hrow
  have he : bondLeftMul c h = fun (V : TorusField n) z => (fun i =>
      (if z = c.1 ∧ i = c.2 then (fun g : UnitQuaternion => h * g) else id) (V z i)) := by
    funext V
    exact bondLeftMul_eq_ite c h V
  rw [he]
  exact hall
theorem integral_eq_integral_resampleBond [NeZero n] (c : TorusBond n) (F : TorusField n → ℝ) (hF : Continuous F) :
    ∫ V, F V ∂(fieldHaar n) = ∫ V, ∫ g, F (fieldAtBond V c g) ∂haarUnit ∂(fieldHaar n) := by
  have h1 : ∀ h : UnitQuaternion, ∫ V, F (bondLeftMul c h V) ∂(fieldHaar n) = ∫ V, F V ∂(fieldHaar n) := fun h => by
    have hp := measurePreserving_bondLeftMul c h
    calc ∫ V, F (bondLeftMul c h V) ∂(fieldHaar n)
        = ∫ y, F y ∂(Measure.map (bondLeftMul c h) (fieldHaar n)) :=
          (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm
      _ = ∫ V, F V ∂(fieldHaar n) := by rw [hp.map_eq]
  have h2 : ∫ V, F V ∂(fieldHaar n) = ∫ h : UnitQuaternion, ∫ V, F (bondLeftMul c h V) ∂(fieldHaar n) ∂haarUnit := by
    simp only [h1]
    simp
  have hc : Continuous fun q : UnitQuaternion × TorusField n => F (bondLeftMul c q.1 q.2) := by
    refine hF.comp ?_
    have hcomp : Continuous fun q : UnitQuaternion × TorusField n => (q.2, q.1 * q.2 c.1 c.2) :=
      continuous_snd.prodMk (continuous_fst.mul
        ((continuous_apply c.2).comp ((continuous_apply c.1).comp continuous_snd)))
    exact (continuous_fieldAtBond c).comp hcomp
  have hint : Integrable (Function.uncurry fun (h : UnitQuaternion) (V : TorusField n) => F (bondLeftMul c h V))
      (haarUnit.prod (fieldHaar n)) :=
    Continuous.integrable_of_hasCompactSupport hc (HasCompactSupport.of_compactSpace _)
  rw [h2, integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  exact integral_mul_right_eq_self (μ := haarUnit) (fun g => F (fieldAtBond V c g)) (V c.1 c.2)
theorem fieldAtBond_apply_self (V : TorusField n) (c : TorusBond n) (g : UnitQuaternion) :
    fieldAtBond V c g c.1 c.2 = g := by
  simp [fieldAtBond]
theorem fieldAtBond_apply_of_ne (V : TorusField n) (c c' : TorusBond n) (g : UnitQuaternion) (h : c' ≠ c) :
    fieldAtBond V c g c'.1 c'.2 = V c'.1 c'.2 := by
  by_cases hz : c'.1 = c.1
  · have hi : c'.2 ≠ c.2 := fun hi => h (Prod.ext hz hi)
    simp [fieldAtBond, hz, hi]
  · simp [fieldAtBond, hz]
section BondElements
variable [NeZero n]
theorem intCast_cast_intCast_of_eq {m n : ℕ} (hm : m = n) [NeZero m] (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod n) = (z : ZMod n) := by apply _root_.YangMills.Construction.TorusLumps.castInt_intCast <;> assumption
theorem intCast_cast_intCast_cast_of_eq {m n : ℕ} (hm : m = n) [NeZero m] (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod n).cast : ℤ) : ZMod m) = a := by
  subst hm
  simp
theorem stepBlockFrame_period_one {L : ℕ} (i : Fin 4) : (stepBlockFrame L n).period 1 i = n := by
  simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
theorem readAtLevel_torusSiteInFrame {L : ℕ} [NeZero L] (V : TorusField n) (z : TorusSite n) (i : Fin 4) :
    readAtLevel (stepBlockFrame L n) 1 V (torusSiteInFrame (stepBlockFrame L n) 1 z) i = V z i := by
  have : (fun k => ((siteCoords (torusSiteInFrame (stepBlockFrame L n) 1 z) k : ℤ) : ZMod n)) = z := by
    funext k
    have h := intCast_cast_intCast_of_eq (stepBlockFrame_period_one (L := L) (n := n) k) ((z k).cast : ℤ)
    exact h.trans (ZMod.intCast_zmod_cast (z k))
  simp only [readAtLevel]
  rw [this]
def torusSiteEquivCell {L : ℕ} [NeZero L] : TorusSite n ≃ (stepBlockFrame L n).Cell where
  toFun := torusSiteInFrame (stepBlockFrame L n) 1
  invFun := toTorusSite n
  left_inv := fun z => by
    funext k
    have h := intCast_cast_intCast_of_eq (stepBlockFrame_period_one (L := L) (n := n) k) ((z k).cast : ℤ)
    exact h.trans (ZMod.intCast_zmod_cast (z k))
  right_inv := fun x => by
    funext i
    exact intCast_cast_intCast_cast_of_eq (stepBlockFrame_period_one i) (x i)
def bondMean (p : StepParameters) (w : (stepBlockFrame p.side n).GaugeField 0) (b : BaseChoice p.side n)
    (c : TorusBond n) : ℍ[ℝ] :=
  contourMean p.baseDepth (hotLumps p.grid p.threshold (levelSites (stepBlockFrame p.side n) 0) w) b w
    (torusSiteInFrame (stepBlockFrame p.side n) 1 c.1, c.2)
def kernelOfElement (p : StepParameters) (x : ℝ) (w : (stepBlockFrame p.side n).GaugeField 0)
    (b : BaseChoice p.side n) (c : TorusBond n) (g : UnitQuaternion) : ℝ :=
  Real.exp (p.coupling * x * (bondMean p w b c * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) /
    partitionFn (p.coupling * x * ‖bondMean p w b c‖)
def fitOfElement (p : StepParameters) (w : (stepBlockFrame p.side n).GaugeField 0) (b : BaseChoice p.side n)
    (c : TorusBond n) (g : UnitQuaternion) : ℝ :=
  ‖bondMean p w b c‖ - (bondMean p w b c * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re
theorem continuous_re_mul_inv (q : ℍ[ℝ]) :
    Continuous fun g : UnitQuaternion => (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re :=
  Quaternion.continuous_re.comp (continuous_const.mul (continuous_subtype_val.comp continuous_inv))
theorem continuous_kernelOfElement (p : StepParameters) (x : ℝ) (w : (stepBlockFrame p.side n).GaugeField 0)
    (b : BaseChoice p.side n) (c : TorusBond n) : Continuous (kernelOfElement p x w b c) :=
  Continuous.div_const (Real.continuous_exp.comp (continuous_const.mul (continuous_re_mul_inv _))) _
theorem continuous_fitOfElement (p : StepParameters) (w : (stepBlockFrame p.side n).GaugeField 0)
    (b : BaseChoice p.side n) (c : TorusBond n) : Continuous (fitOfElement p w b c) :=
  continuous_const.sub (continuous_re_mul_inv _)
theorem bondKernelAt_eq_kernelOfElement (p : StepParameters) (x : ℝ) (W : TorusField (n * p.side))
    (V : TorusField n) (b : BaseChoice p.side n) (c : TorusBond n) :
    bondKernelAt p x W V b c = kernelOfElement p x (readAtLevel (stepBlockFrame p.side n) 0 W) b c (V c.1 c.2) := by
  simp only [bondKernelAt, bondKernel, kernelOfElement, bondMean, readAtLevel_torusSiteInFrame]
theorem bondFit_eq_fitOfElement (p : StepParameters) (W : TorusField (n * p.side)) (V : TorusField n)
    (b : BaseChoice p.side n) (c : TorusBond n) :
    bondFit p W V b c = fitOfElement p (readAtLevel (stepBlockFrame p.side n) 0 W) b c (V c.1 c.2) := by
  simp only [bondFit, stepHotLumps, contourFit, fitOfElement, bondMean, readAtLevel_torusSiteInFrame]
  rfl
end BondElements
end YangMills.Construction.WeightedResponses
end
