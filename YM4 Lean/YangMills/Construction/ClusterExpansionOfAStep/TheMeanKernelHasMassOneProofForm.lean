import YangMills.Construction.ClusterExpansionOfAStep.BasesExist
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanKernelHasMassOne
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusFields
theorem zmod_cast_intCast_cast_of_eq {m n : ℕ} (hm : m = n) [NeZero m] (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod n).cast : ℤ) : ZMod m) = a := by apply _root_.YangMills.Construction.WeightedResponses.intCast_cast_intCast_cast_of_eq <;> assumption
section Cells
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem stepBlockFrame_period_coarse (i : Fin 4) : (stepBlockFrame L n).period 1 i = n := by
  simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
def cellEquivTorusSite : (stepBlockFrame L n).Cell ≃ TorusSite n where
  toFun := toTorusSite n
  invFun := fun z => siteOfCoords 1 fun i => ((z i).cast : ℤ)
  left_inv := fun x => by
    funext i
    exact zmod_cast_intCast_cast_of_eq (stepBlockFrame_period_coarse i) (x i)
  right_inv := fun z => by
    funext i
    have h := castInt_intCast (stepBlockFrame_period_coarse (L := L) (n := n) i) ((z i).cast : ℤ)
    exact h.trans (ZMod.intCast_zmod_cast (z i))
end Cells
def bondWeight (ℓ : StepParameters) (x : ℝ) {n : ℕ} (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) (g : UnitQuaternion) :
    ℝ :=
  Real.exp (ℓ.coupling * x * (contourMean ℓ.baseDepth
      (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) b W c *
      ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) /
    partitionFn (ℓ.coupling * x * ‖contourMean ℓ.baseDepth
      (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) b W c‖)
theorem bondKernel_eq_bondWeight (ℓ : StepParameters) (x : ℝ) {n : ℕ}
    (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    bondKernel ℓ x W V b c = bondWeight ℓ x W b c (V c.1 c.2) := rfl
theorem continuous_bondWeight (ℓ : StepParameters) (x : ℝ) {n : ℕ}
    (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    Continuous (bondWeight ℓ x W b c) := by
  unfold bondWeight
  refine Continuous.div_const (Real.continuous_exp.comp (continuous_const.mul ?_)) _
  refine Quaternion.continuous_re.comp (continuous_const.mul ?_)
  exact continuous_subtype_val.comp continuous_inv
theorem integral_bondWeight (hK : BondKernelProperties) (ℓ : StepParameters) (x : ℝ) {n : ℕ}
    (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    ∫ g : UnitQuaternion, bondWeight ℓ x W b c g ∂haarUnit = 1 := by
  have h := (hK.2 ℓ x n W (fun _ _ => 1) b c).2.2
  have hw : ∀ g : UnitQuaternion,
      bondKernel ℓ x W (updateBond (fun _ _ => 1) c g) b c = bondWeight ℓ x W b c g := by
    intro g
    rw [bondKernel_eq_bondWeight]
    simp [updateBond]
  simpa only [hw] using h
theorem integral_prod_bondKernel (hK : BondKernelProperties) (ℓ : StepParameters) (x : ℝ) {n : ℕ}
    [NeZero n] (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) :
    ∫ V : TorusField n, ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ x W (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c ∂(fieldHaar n) = 1 := by
  let e : (stepBlockFrame ℓ.side n).Cell ≃ TorusSite n := cellEquivTorusSite
  have hprod : ∀ V : TorusField n, ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ x W (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c =
      ∏ z : TorusSite n, ∏ i : Fin 4, bondWeight ℓ x W b (e.symm z, i) (V z i) := by
    intro V
    rw [Fintype.prod_prod_type, ← e.symm.prod_comp (fun y => ∏ i : Fin 4,
      bondKernel ℓ x W (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b (y, i))]
    refine Finset.prod_congr rfl fun z _ => Finset.prod_congr rfl fun i _ => ?_
    rw [bondKernel_eq_bondWeight]
    have hz : toTorusSite n (e.symm z) = z := e.apply_symm_apply z
    have hread : readAtLevel (stepBlockFrame ℓ.side n) 1 V (e.symm z) i = V z i := by
      show V (toTorusSite n (e.symm z)) i = _
      rw [hz]
    exact congrArg _ hread
  simp only [hprod]
  unfold fieldHaar
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : TorusSite n => Measure.pi fun _ : Fin 4 => haarUnit)
    (f := fun z v => ∏ i : Fin 4, bondWeight ℓ x W b (e.symm z, i) (v i))]
  refine Finset.prod_eq_one fun z _ => ?_
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin 4 => haarUnit)
    (f := fun i g => bondWeight ℓ x W b (e.symm z, i) g)]
  exact Finset.prod_eq_one fun i _ => integral_bondWeight hK ℓ x W b _
theorem averagedKernelIntegralOne_holds (hK : BondKernelProperties) (hB : BaseChoicesNonempty) :
    AveragedKernelIntegralOne := by
  intro ℓ hfit hLam x n _ W
  have hne := hB ℓ hfit hLam n W
  have hint : ∀ b ∈ baseChoices ℓ W, Integrable (fun V : TorusField n =>
      ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ x W (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c) (fieldHaar n) := by
    intro b _
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    refine continuous_finset_prod _ fun c _ => ?_
    simp only [bondKernel_eq_bondWeight]
    refine (continuous_bondWeight ℓ x W b c).comp ?_
    simp only [readAtLevel]
    fun_prop
  unfold averagedKernel
  rw [integral_const_mul, integral_finset_sum _ hint]
  simp only [integral_prod_bondKernel hK]
  have hc : ((baseChoices ℓ W).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  simp [hc]
end YangMills.Construction.TorusLumps
end
