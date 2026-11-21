import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasProof
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsAnArray
import YangMills.Construction.ClusterExpansionOfAStep.WeightsOfAStepAddUp
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.StepSettings YangMills.Construction.StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem sum_markProduct_eq_one (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) :
    ∑ S ∈ (markedBonds R C).powerset, ENNReal.ofReal (markProduct R C V W S) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.sum_markProduct_eq_one <;> assumption
theorem baseLaw_nonneg (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
section KernelSums
variable (hker : BondKernelProperties)
include hker
theorem prod_bondKernel_nonneg (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n) :
    0 ≤ ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c :=
  Finset.prod_nonneg fun c _ => (hker.2 R.params R.coupling n _ _ b c).1.le
omit hker in
theorem averagedKernel_eq_sum (W : TorusField (n * R.params.side)) (V : TorusField n) :
    averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) =
      ∑ b : BaseChoice R.params.side n, baseLaw (R := R) W b *
        ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.averagedKernel_eq_sum <;> assumption
theorem lintegral_configurationWeight (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (S : Finset (TorusBond (n * R.params.side)))
    (Y : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    ∫⁻ ω : Y → R.labels.Ω, configurationWeight R C V S Y b W ω ∂(Measure.pi fun _ => R.labels.μ) =
      (open Classical in if IsHullState R.params R.range W Y then
          ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω)
            ∂(Measure.pi fun _ : Y => R.labels.μ) else 0) *
        ENNReal.ofReal (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
        ENNReal.ofReal (markProduct R C V W S) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.lintegral_configurationWeight <;> assumption
theorem sum_lintegral_configurationWeight (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n)
    (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hD : 0 ≤ R.functional (n * R.params.side) W) :
    ∑ S ∈ (markedBonds R C).powerset, ∑ Y : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n,
      ∫⁻ ω : Y → R.labels.Ω, configurationWeight R C V S Y b W ω ∂(Measure.pi fun _ => R.labels.μ) =
      ENNReal.ofReal (R.functional (n * R.params.side) W *
        averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V)) := by
  classical
  simp_rw [lintegral_configurationWeight hker hR C V W hside]
  have hsum := hR.hasExpansions.2.sum (n * R.params.side) hside W
  have hrow : ∑ Y : Finset (TorusSite (n * R.params.side)), (if IsHullState R.params R.range W Y then
      ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω)
        ∂(Measure.pi fun _ : Y => R.labels.μ) else 0) =
      ENNReal.ofReal (R.functional (n * R.params.side) W) := by
    rw [← hsum, Finset.sum_filter]
    rfl
  have hbase : ∑ b : BaseChoice R.params.side n, ENNReal.ofReal (baseLaw (R := R) W b *
      ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) =
      ENNReal.ofReal (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V)) := by
    rw [averagedKernel_eq_sum, ENNReal.ofReal_sum_of_nonneg]
    exact fun b _ => mul_nonneg (baseLaw_nonneg (R := R) W b) (prod_bondKernel_nonneg hker W V b)
  have hall : ∀ S, ∑ Y : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
      (if IsHullState R.params R.range W Y then
        ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω)
          ∂(Measure.pi fun _ : Y => R.labels.μ) else 0) *
      ENNReal.ofReal (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
      ENNReal.ofReal (markProduct R C V W S) =
      ENNReal.ofReal (R.functional (n * R.params.side) W) *
        ENNReal.ofReal (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V)) *
        ENNReal.ofReal (markProduct R C V W S) := by
    intro S
    rw [← hrow, ← hbase, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finset.sum_mul]
  simp_rw [hall]
  rw [← Finset.mul_sum, sum_markProduct_eq_one hR, mul_one, ← ENNReal.ofReal_mul hD]
end KernelSums
theorem configurationWeightsSum_holds (hker : BondKernelProperties) (himg : KernelImageIsDensity)
    (hmeas : ConfigurationWeightMeasurable) : ConfigurationWeightsSum := by
  classical
  intro R hR n _ hn C V
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm R.params.side R.params.n₀]; exact Nat.mul_le_mul_right _ hn⟩
  have hrow : HasExpansion R.params R.depth R.coupling R.functional :=
    ⟨hR.functional_spec, R.density, hR.hasExpansions.1, R.labels, R.labelWeight, R.clusterFactor,
      R.siteDensity, hR.hasExpansions.2⟩
  have harr := himg R.params hR.admissible R.depth R.coupling R.functional hR.coupling_pos
    hR.range_ge_base hrow n hn
  have hnn : R.params.n₀ ≤ n * R.params.side :=
    le_trans hn (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))
  have hD := (hR.functional_spec (n * R.params.side) hnn).2.1
  have hm : ∀ (S : Finset (TorusBond (n * R.params.side))) (Y : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun W : TorusField (n * R.params.side) =>
      ∫⁻ ω : Y → R.labels.Ω, configurationWeight R C V S Y b W ω ∂(Measure.pi fun _ => R.labels.μ) :=
    fun S Y b => (hmeas R hR n hn C V S Y b).lintegral_prod_right'
  have h3 : ∀ (S : Finset (TorusBond (n * R.params.side))) (Y : Finset (TorusSite (n * R.params.side))),
      ∑ b : BaseChoice R.params.side n, ∫⁻ W, ∫⁻ ω : Y → R.labels.Ω, configurationWeight R C V S Y b W ω
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ W, ∑ b : BaseChoice R.params.side n, ∫⁻ ω : Y → R.labels.Ω, configurationWeight R C V S Y b W ω
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) :=
    fun S Y => (lintegral_finset_sum _ fun b _ => hm S Y b).symm
  simp_rw [h3]
  have h2 : ∀ S : Finset (TorusBond (n * R.params.side)), ∑ Y : Finset (TorusSite (n * R.params.side)),
      ∫⁻ W, ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω : Y → R.labels.Ω, configurationWeight R C V S Y b W ω ∂(Measure.pi fun _ => R.labels.μ)
          ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ W, ∑ Y : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω : Y → R.labels.Ω, configurationWeight R C V S Y b W ω ∂(Measure.pi fun _ => R.labels.μ)
          ∂(fieldHaar (n * R.params.side)) :=
    fun S => (lintegral_finset_sum _ fun Y _ => Finset.measurable_sum _ fun b _ => hm S Y b).symm
  simp_rw [h2]
  rw [← lintegral_finset_sum _ fun S _ =>
    Finset.measurable_sum _ fun Y _ => Finset.measurable_sum _ fun b _ => hm S Y b]
  simp_rw [fun W => sum_lintegral_configurationWeight hker hR hn C V W hside (hD W)]
  have hI := harr.1 V
  have hval : kernelImage R.params R.coupling R.functional n V =
      ∫ W : TorusField (n * R.params.side), R.functional (n * R.params.side) W *
        averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) ∂(fieldHaar (n * R.params.side)) := by
    unfold kernelImage
    rw [dif_neg (NeZero.ne n)]
  have hnonneg : ∀ W : TorusField (n * R.params.side), 0 ≤ R.functional (n * R.params.side) W *
      averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) := by
    intro W
    refine mul_nonneg (hD W) ?_
    rw [averagedKernel_eq_sum (R := R)]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (baseLaw_nonneg (R := R) W b) (prod_bondKernel_nonneg hker W V b)
  rw [hval, ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hnonneg)]
end YangMills.Construction.ClusterExpansionOfAStep
end
