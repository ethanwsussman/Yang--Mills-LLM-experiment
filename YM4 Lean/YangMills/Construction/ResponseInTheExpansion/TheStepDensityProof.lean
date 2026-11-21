import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheMeanOfABond
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open TorusLumps TorusFields BlockAverages LumpContours StepCosts
namespace WeightedResponses
theorem measurable_comp_of_finite_range {α β γ : Type} [MeasurableSpace α] [MeasurableSpace γ]
    (f : α → β) (hfin : (Set.range f).Finite) (hlev : ∀ a, MeasurableSet {x | f x = a}) (g : β → γ) :
    Measurable fun x => g (f x) := by
  intro U _
  have hcov : (fun x => g (f x)) ⁻¹' U = ⋃ a ∈ Set.range f ∩ g ⁻¹' U, {x | f x = a} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro h
      exact ⟨f x, ⟨⟨x, rfl⟩, h⟩, rfl⟩
    · rintro ⟨a, ⟨_, h⟩, rfl⟩
      exact h
  rw [hcov]
  exact MeasurableSet.biUnion (hfin.subset Set.inter_subset_left).countable fun a _ => hlev a
theorem exp_neg_abs_le_partitionFn (s : ℝ) : Real.exp (-|s|) ≤ partitionFn s := by
  unfold partitionFn
  have hc : Continuous fun g : UnitQuaternion => Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re) :=
    Real.continuous_exp.comp (continuous_const.mul
      (Quaternion.continuous_re.comp continuous_subtype_val))
  have h := integral_mono (μ := haarUnit) (integrable_const (Real.exp (-|s|)))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun g => by
      have h1 : |((g : UnitQuaternion) : ℍ[ℝ]).re| ≤ 1 := (abs_re_le_norm _).trans (norm_unitQuaternion g).le
      have h2 : |s * ((g : UnitQuaternion) : ℍ[ℝ]).re| ≤ |s| := by
        rw [abs_mul]
        nlinarith [abs_nonneg s]
      exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (s * ((g : UnitQuaternion) : ℍ[ℝ]).re)])
  simpa using h
variable {n : ℕ} [NeZero n]
theorem bondKernel_le_exp (p : StepParameters) (x : ℝ) (w : (stepBlockFrame p.side n).GaugeField 0)
    (v : (stepBlockFrame p.side n).GaugeField 1)
    (b : BaseChoice p.side n) (c : (stepBlockFrame p.side n).Cell × Fin 4) :
    bondKernel p x w v b c ≤ Real.exp (2 * |p.coupling * x|) := by
  unfold bondKernel
  simp only
  set q := contourMean p.baseDepth (hotLumps p.grid p.threshold (levelSites (stepBlockFrame p.side n) 0) w) b w c with hq
  have hq1 : ‖q‖ ≤ 1 := norm_contourMean_le _ _ _ _ _
  set y := p.coupling * x with hy
  have hz : Real.exp (-|y|) ≤ partitionFn (y * ‖q‖) := by
    have h0 : |y * ‖q‖| ≤ |y| := by
      rw [abs_mul y ‖q‖, abs_of_nonneg (norm_nonneg q)]
      nlinarith [abs_nonneg y]
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) (exp_neg_abs_le_partitionFn _)
  have hzp : 0 < partitionFn (y * ‖q‖) := lt_of_lt_of_le (Real.exp_pos _) hz
  rw [div_le_iff₀ hzp]
  have hre := abs_re_mul_inv_le q (v c.1 c.2)
  have hnum : y * (q * (((v c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re ≤ |y| := by
    calc y * (q * (((v c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re
          ≤ |y * (q * (((v c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re| := le_abs_self _
      _ = |y| * |(q * (((v c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re| := abs_mul _ _
      _ ≤ |y| * 1 := mul_le_mul_of_nonneg_left (hre.trans hq1) (abs_nonneg y)
      _ = |y| := mul_one _
  calc Real.exp (y * (q * (((v c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) ≤ Real.exp |y| :=
        Real.exp_le_exp.mpr hnum
    _ = Real.exp (2 * |y|) * Real.exp (-|y|) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * |y|) * partitionFn (y * ‖q‖) := mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
theorem stepTransitionDensityBounds_of_bondKernel (hB : BondKernelBorel) (hK : BondKernelProperties) :
    StepTransitionDensityBounds := by
  intro p x n _
  obtain ⟨-, hR, -, hS, -, hker, -⟩ := hB p x n
  have hphi : ∀ b : BaseChoice p.side n, Measurable fun W : TorusField (n * p.side) =>
      (open Classical in if b ∈ baseChoices p (fineLevelField p n W) then
        (1 / ((baseChoices p (fineLevelField p n W)).card : ℝ)) else 0) := fun b =>
    measurable_comp_of_finite_range (fun W : TorusField (n * p.side) => baseChoices p (fineLevelField p n W)) hR hS
      (fun A => open Classical in if b ∈ A then (1 / (A.card : ℝ)) else 0)
  have hform : ∀ (W : TorusField (n * p.side)) (b : BaseChoice p.side n) (V : TorusField n),
      stepTransitionDensity p x W b V =
      (open Classical in if b ∈ baseChoices p (fineLevelField p n W) then
        (1 / ((baseChoices p (fineLevelField p n W)).card : ℝ)) else 0) *
      ∏ c : (stepBlockFrame p.side n).Cell × Fin 4,
        bondKernel p x (fineLevelField p n W) (coarseLevelField p n V) b c := by
    intro W b V
    unfold stepTransitionDensity
    split_ifs <;> simp
  refine ⟨fun b => ?_, ?_⟩
  · simp only [hform]
    exact ((hphi b).comp measurable_fst).mul (Finset.measurable_prod _ fun c _ => hker b c)
  · refine ⟨∏ _c : (stepBlockFrame p.side n).Cell × Fin 4, Real.exp (2 * |p.coupling * x|), fun W b V => ?_⟩
    have hk0 : ∀ c, 0 ≤ bondKernel p x (fineLevelField p n W) (coarseLevelField p n V) b c := fun c =>
      (hK.2 p x n _ _ b c).1.le
    have hP0 : 0 ≤ ∏ c : (stepBlockFrame p.side n).Cell × Fin 4,
        bondKernel p x (fineLevelField p n W) (coarseLevelField p n V) b c :=
      Finset.prod_nonneg fun c _ => hk0 c
    have hP1 : ∏ c : (stepBlockFrame p.side n).Cell × Fin 4,
        bondKernel p x (fineLevelField p n W) (coarseLevelField p n V) b c ≤
        ∏ _c : (stepBlockFrame p.side n).Cell × Fin 4, Real.exp (2 * |p.coupling * x|) :=
      Finset.prod_le_prod (fun c _ => hk0 c) fun c _ => bondKernel_le_exp p x _ _ b c
    rw [hform]
    by_cases hb : b ∈ baseChoices p (fineLevelField p n W)
    · rw [if_pos hb]
      have hc : (1 : ℝ) ≤ ((baseChoices p (fineLevelField p n W)).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨b, hb⟩
      have hphi0 : 0 ≤ 1 / ((baseChoices p (fineLevelField p n W)).card : ℝ) := by positivity
      have hphi1 : 1 / ((baseChoices p (fineLevelField p n W)).card : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hc
      refine ⟨mul_nonneg hphi0 hP0, ?_⟩
      calc _ ≤ 1 * ∏ c : (stepBlockFrame p.side n).Cell × Fin 4,
              bondKernel p x (fineLevelField p n W) (coarseLevelField p n V) b c :=
            mul_le_mul_of_nonneg_right hphi1 hP0
        _ ≤ _ := by rw [one_mul]; exact hP1
    · rw [if_neg hb, zero_mul]
      exact ⟨le_rfl, hP0.trans hP1⟩
end WeightedResponses
end YangMills.Construction
end
