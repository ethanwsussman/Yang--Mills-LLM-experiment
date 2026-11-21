import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStepProof
import YangMills.Construction.SummableBoundsOfTheFlow.SecondMomentsOfAGaussian
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAtTheScaleZero
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity MeasureTheory Set
namespace ScaledVariables
variable {F : BlockFrame}
private theorem coord_bondVariation (i : ChartCoord F) (b : ↥(chordBonds (finiteCells F))) (e : BondVector) :
    (bondVariation b e : StepVariable (finiteCells F)) i.1 i.2 = if i.1 = b then e i.2 else 0 := by apply _root_.YangMills.SharedProofs.p54563 <;> assumption
private theorem secondDerivAlong_eq_fderiv {X : Type} [Fintype X] [DecidableEq X] (E : BondField X → ℝ)
    (z u w : BondField X) (hz : DifferentiableAt ℝ (fderiv ℝ E) z) :
    secondDerivAlong E z u w = fderiv ℝ (fderiv ℝ E) z w u := by apply _root_.YangMills.SharedProofs.p7378 <;> assumption
private theorem secondDerivAlong_eq_hessian_sum (a ρ : ℝ) (V : F.GaugeField F.top)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0)
    (u v : StepVariable (finiteCells F)) :
    secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0 u v =
      ∑ i, ∑ j, chartedHessian a ρ V 0 i j * (u i.1 i.2 * v j.1 j.2) := by apply _root_.YangMills.SharedProofs.p21715 <;> assumption
private theorem norm_sq_eq_sum_coords (x : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) :
    ‖x b‖ ^ 2 = ∑ k, (x b k) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
private theorem sum_norm_sq_eq_sum_coords (x : StepVariable (finiteCells F)) :
    ∑ b, ‖x b‖ ^ 2 = ∑ i : ChartCoord F, (x i.1 i.2) ^ 2 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun b _ => norm_sq_eq_sum_coords x b
private theorem cell_sum_norm_sq_eq (x : StepVariable (finiteCells F)) (Y : F.Cell) :
    (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then ‖x b‖ ^ 2 else 0) =
      ∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then (x i.1 i.2) ^ 2 else 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact norm_sq_eq_sum_coords x b
  · simp
private theorem integral_one_sub_mul (c : ℝ) : ∫ v in (0 : ℝ)..1, (1 - v) * c = c / 2 := by
  have h : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => (v - v ^ 2 / 2) * c) ((1 - v) * c) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => v - v ^ 2 / 2) (1 - v) v :=
      ((hasDerivAt_id v).sub ((hasDerivAt_pow 2 v).div_const 2)).congr_deriv (by norm_num)
    exact h1.mul_const c
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun v : ℝ => (1 - v) * c).intervalIntegrable _ _)]
  ring
private theorem mem_finiteCells (hF : ∀ i, F.extent i ≠ 0) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p16107 <;> assumption
private theorem rescaledCellTerm_zero (a ρ : ℝ) (V : F.GaugeField F.top)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0) (Y : F.Cell)
    (x : StepVariable (finiteCells F)) :
    rescaledCellTerm a ρ 0 Y V x =
      (∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
        ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) / 2 else 0) -
      (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        3 / 2 * Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖) -
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) else 0 := by
  unfold rescaledCellTerm haarGapShift
  have h0 : ∀ v : ℝ, (v * 0) • x = 0 := fun v => by simp
  have h1 : (0 : ℝ) • x = 0 := zero_smul _ _
  simp only [h0, h1]
  have hq : ∀ b : ↥(chordBonds (finiteCells F)),
      (∫ v in (0 : ℝ)..1, (1 - v) * secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0 (bondVariation b (x b)) x) =
        ∑ i : ChartCoord F, if i.1 = b then
          ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) / 2 else 0 := by
    intro b
    rw [integral_one_sub_mul, secondDerivAlong_eq_hessian_sum a ρ V hd, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [coord_bondVariation]
    split_ifs with h
    · rw [Finset.sum_div]
      subst h
      rfl
    · simp
  simp only [hq]
  have hs : (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      (∑ i : ChartCoord F, if i.1 = b then
        ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) / 2 else 0) else 0) =
      ∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
        ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) / 2 else 0 := by
    have : ∀ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        (∑ i : ChartCoord F, if i.1 = b then
          ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) / 2 else 0) else 0) =
        ∑ i : ChartCoord F, if i.1 = b then (if enclosingCell b.1.1 = Y then
          ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) / 2 else 0) else 0 := by
      intro b
      split_ifs with h
      · simp [h]
      · simp [h]
    simp only [this]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
    simp
  rw [hs]
  have hg : ∀ c, 3 / 2 * Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖ +
      haarGapTail (0 ^ 2 / (a * ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖)) - haarGapTail (0 ^ 2 / a) =
      3 / 2 * Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖ := by
    intro c
    simp
  simp only [hg]
private theorem quadForm_chartedHessian (a ρ : ℝ) (V : F.GaugeField F.top) (x : StepVariable (finiteCells F)) :
    GaussianMoments.quadForm (chartedHessian a ρ V 0) x =
      ∑ i : ChartCoord F, ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) := rfl
private theorem quadForm_interp (M : Matrix (ChartCoord F) (ChartCoord F) ℝ) (τ c : ℝ)
    (x : StepVariable (finiteCells F)) :
    GaussianMoments.quadForm (τ • M + (1 - τ) • c • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)) x =
      τ * GaussianMoments.quadForm M x + (1 - τ) * (c * ∑ b, ‖x b‖ ^ 2) := by
  unfold GaussianMoments.quadForm
  rw [sum_norm_sq_eq_sum_coords, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring
private theorem rescaledExponent_sub_zero (a ρ ν : ℝ) (f : LocalFamily) (V : F.GaugeField F.top)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0) (hF : ∀ i, F.extent i ≠ 0)
    (x : StepVariable (finiteCells F)) :
    rescaledExponent a ρ f ν 0 V x - rescaledExponent a ρ f ν 0 V 0 =
      1 / 2 * GaussianMoments.quadForm (chartedHessian a ρ V 0) x := by
  unfold rescaledExponent
  have h1 : (0 : ℝ) • x = 0 := zero_smul _ _
  have h2 : (0 : ℝ) • (0 : StepVariable (finiteCells F)) = 0 := zero_smul _ _
  rw [h1, h2]
  have hs : ∀ y : StepVariable (finiteCells F), ∑ Y ∈ finiteCells F, rescaledCellTerm a ρ 0 Y V y =
      (∑ i : ChartCoord F, ∑ j, chartedHessian a ρ V 0 i j * (y i.1 i.2 * y j.1 j.2) / 2) -
      (∑ Y ∈ finiteCells F, ((∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        3 / 2 * Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖) +
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) else 0)) := by
    intro y
    have hq : ∑ Y ∈ finiteCells F, (∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
        ∑ j, chartedHessian a ρ V 0 i j * (y i.1 i.2 * y j.1 j.2) / 2 else 0) =
        ∑ i : ChartCoord F, ∑ j, chartedHessian a ρ V 0 i j * (y i.1 i.2 * y j.1 j.2) / 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_ite_eq, if_pos (mem_finiteCells hF _)]
    rw [← hq, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro Y _
    rw [rescaledCellTerm_zero a ρ V hd]
    ring
  rw [hs, hs]
  have hz : ∑ i : ChartCoord F, ∑ j, chartedHessian a ρ V 0 i j *
      ((0 : StepVariable (finiteCells F)) i.1 i.2 * (0 : StepVariable (finiteCells F)) j.1 j.2) / 2 = 0 := by
    simp
  rw [hz]
  unfold GaussianMoments.quadForm
  have hh : 1 / 2 * ∑ i : ChartCoord F, ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) =
      ∑ i : ChartCoord F, ∑ j, chartedHessian a ρ V 0 i j * (x i.1 i.2 * x j.1 j.2) / 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hh]
  ring
private theorem gaussianWeight_interpolated (a ρ lam τ : ℝ) (f : LocalFamily) (V : F.GaugeField F.top)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0) (hF : ∀ i, F.extent i ≠ 0)
    (x : StepVariable (finiteCells F)) :
    ScaledVariables.gaussianWeight a ρ lam f V (.interpolated τ) x = GaussianMoments.gaussianWeight
      (τ • chartedHessian a ρ V 0 + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)) x := by
  unfold ScaledVariables.gaussianWeight GaussianMoments.gaussianWeight
  rw [quadForm_interp]
  congr 1
  simp only [rescaledLawExponent]
  have h := rescaledExponent_sub_zero a ρ 0 f V hd hF x
  have h0 : ∑ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ ^ 2 = 0 := by simp
  rw [h0]
  have h3 : rescaledExponent a ρ f 0 0 V x = rescaledExponent a ρ f 0 0 V 0 +
      1 / 2 * GaussianMoments.quadForm (chartedHessian a ρ V 0) x := by linarith
  rw [h3]
  ring
private theorem gaussianWeight_tilted (a ρ lam ν : ℝ) (f : LocalFamily) (V : F.GaugeField F.top)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0) (hF : ∀ i, F.extent i ≠ 0)
    (x : StepVariable (finiteCells F)) :
    ScaledVariables.gaussianWeight a ρ lam f V (.tilted ν) x =
      GaussianMoments.gaussianWeight (chartedHessian a ρ V 0) x := by
  unfold ScaledVariables.gaussianWeight GaussianMoments.gaussianWeight
  simp only [rescaledLawExponent]
  rw [rescaledExponent_sub_zero a ρ ν f V hd hF x]
private theorem chartedHessian_isSymm (a ρ : ℝ) (V : F.GaugeField F.top)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0)
    (hc : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer a ρ V) 0) : (chartedHessian a ρ V 0).IsSymm := by
  have hs : IsSymmSndFDerivAt ℝ (chartedEnergyAtMinimizer a ρ V) 0 :=
    hc.isSymmSndFDerivAt (by simp)
  refine Matrix.IsSymm.ext fun i j => ?_
  show secondDerivAlong _ 0 _ _ = secondDerivAlong _ 0 _ _
  rw [secondDerivAlong_eq_fderiv _ _ _ _ hd, secondDerivAlong_eq_fderiv _ _ _ _ hd]
  exact hs _ _
private theorem interp_floor (M : Matrix (ChartCoord F) (ChartCoord F) ℝ) (lam τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hfl : ∀ x : StepVariable (finiteCells F), lam * ∑ b, ‖x b‖ ^ 2 ≤ GaussianMoments.quadForm M x)
    (x : StepVariable (finiteCells F)) :
    lam * ∑ b, ‖x b‖ ^ 2 ≤ GaussianMoments.quadForm
      (τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)) x := by
  rw [quadForm_interp]
  have := hfl x
  nlinarith [hτ.1, hτ.2]
private theorem interp_isSymm (M : Matrix (ChartCoord F) (ChartCoord F) ℝ) (hM : M.IsSymm) (lam τ : ℝ) :
    (τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hM.apply i j, eq_comm]
private theorem observableGaussianMean_interpolated (a ρ lam τ : ℝ) (f : LocalFamily) (V : F.GaugeField F.top)
    (Y : F.Cell) (hlam : 0 < lam) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer a ρ V)) 0) (hF : ∀ i, F.extent i ≠ 0)
    (hM : (chartedHessian a ρ V 0).IsSymm)
    (hfl : ∀ x : StepVariable (finiteCells F),
      lam * ∑ b, ‖x b‖ ^ 2 ≤ GaussianMoments.quadForm (chartedHessian a ρ V 0) x)
    (hG : GaussianMoments.CovarianceEqInverse) :
    observableGaussianMean a ρ lam f (.interpolated τ) (fun l x V' => rescaledCellRemainder a ρ lam l Y V' x) V =
      1 / 2 * hessianCellShare a ρ lam Y V τ -
      (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        3 / 2 * Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖) -
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) else 0 := by
  set M := chartedHessian a ρ V 0 with hMdef
  set A := τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ) with hA
  obtain ⟨-, hw, hZ, hm, hinv⟩ := hG ↥(chordBonds (finiteCells F)) A lam hlam (interp_isSymm M hM lam τ)
    (interp_floor M lam τ hτ hfl)
  set c₀ : ℝ := -(∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        3 / 2 * Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖) -
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) else 0 with hc₀
  set e : ChartCoord F → ChartCoord F → ℝ := fun i j =>
    if enclosingCell i.1.1.1 = Y then (M - lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)) i j / 2 else 0
    with he
  have hH : ∀ x : StepVariable (finiteCells F), rescaledCellRemainder a ρ lam 0 Y V x =
      c₀ + ∑ i, ∑ j, e i j * (x i.1 i.2 * x j.1 j.2) := by
    intro x
    unfold rescaledCellRemainder
    rw [rescaledCellTerm_zero a ρ V hd, cell_sum_norm_sq_eq]
    have h1 : (∑ i : ChartCoord F, ∑ j, e i j * (x i.1 i.2 * x j.1 j.2)) =
        (∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then
          ∑ j, M i j * (x i.1 i.2 * x j.1 j.2) / 2 else 0) -
        lam / 2 * ∑ i : ChartCoord F, if enclosingCell i.1.1.1 = Y then (x i.1 i.2) ^ 2 else 0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [he]
      by_cases h : enclosingCell i.1.1.1 = Y
      · simp only [if_pos h, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        have h2 : ∀ j : ChartCoord F, (M i j - lam * (if i = j then 1 else 0)) / 2 * (x i.1 i.2 * x j.1 j.2) =
            M i j * (x i.1 i.2 * x j.1 j.2) / 2 - (if i = j then lam / 2 * (x i.1 i.2 * x j.1 j.2) else 0) := by
          intro j
          split_ifs <;> ring
        simp only [h2, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring
      · simp [if_neg h]
    rw [h1, hc₀]
    ring
  have hint : ∀ i j : ChartCoord F, Integrable fun x : StepVariable (finiteCells F) =>
      e i j * (x i.1 i.2 * x j.1 j.2 * GaussianMoments.gaussianWeight A x) := fun i j => (hm i j).const_mul _
  have hmean : gaussianMean a ρ lam f V (.interpolated τ) (fun x => rescaledCellRemainder a ρ lam 0 Y V x) =
      c₀ + ∑ i, ∑ j, e i j * A⁻¹ i j := by
    unfold gaussianMean
    have hwt : (fun x => ScaledVariables.gaussianWeight a ρ lam f V (.interpolated τ) x) =
        GaussianMoments.gaussianWeight A := by
      funext x
      exact gaussianWeight_interpolated a ρ lam τ f V hd hF x
    simp only [hwt]
    have hnum : (fun x : StepVariable (finiteCells F) =>
        rescaledCellRemainder a ρ lam 0 Y V x * GaussianMoments.gaussianWeight A x) =
        fun x => c₀ * GaussianMoments.gaussianWeight A x +
          ∑ i, ∑ j, e i j * (x i.1 i.2 * x j.1 j.2 * GaussianMoments.gaussianWeight A x) := by
      funext x
      rw [hH, add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hnum, integral_add (hw.const_mul _)
      (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j),
      integral_const_mul, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
    simp only [integral_finset_sum _ fun j _ => hint _ j, integral_const_mul]
    rw [add_div, mul_div_assoc, div_self hZ.ne', mul_one, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_div_assoc, hinv]
  have hshare : ∑ i, ∑ j, e i j * A⁻¹ i j = 1 / 2 * hessianCellShare a ρ lam Y V τ := by
    unfold hessianCellShare
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he]
    by_cases h : enclosingCell i.1.1.1 = Y
    · simp only [if_pos h]
      rw [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hsym : A⁻¹ i j = A⁻¹ j i := by
        rw [← hinv i j, ← hinv j i]
        congr 1
        congr 1
        funext x
        ring
      rw [hsym]
      ring
    · simp [if_neg h]
  show gaussianMean a ρ lam f V (.interpolated τ) (fun x => rescaledCellRemainder a ρ lam 0 Y V x) = _
  rw [hmean, hshare, hc₀]
  ring
private theorem hessianCellShare_continuousOn (a ρ lam : ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (hlam : 0 < lam) (hM : (chartedHessian a ρ V 0).IsSymm)
    (hfl : ∀ x : StepVariable (finiteCells F),
      lam * ∑ b, ‖x b‖ ^ 2 ≤ GaussianMoments.quadForm (chartedHessian a ρ V 0) x)
    (hG : GaussianMoments.CovarianceEqInverse) :
    ContinuousOn (hessianCellShare a ρ lam Y V) (Icc 0 1) := by
  set M := chartedHessian a ρ V 0 with hMdef
  have hA : Continuous fun τ : ℝ =>
      τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ) := by
    fun_prop
  have hdet : ∀ τ ∈ Icc (0 : ℝ) 1,
      (τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).det ≠ 0 := by
    intro τ hτ
    exact (hG ↥(chordBonds (finiteCells F)) _ lam hlam (interp_isSymm M hM lam τ)
      (interp_floor M lam τ hτ hfl)).1.ne_zero
  have hinv : ContinuousOn (fun τ : ℝ =>
      (τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ))⁻¹) (Icc 0 1) := by
    have h1 : (fun τ : ℝ => (τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ))⁻¹) =
        fun τ => (τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).det⁻¹ •
          (τ • M + (1 - τ) • lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)).adjugate := by
      funext τ
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    exact (hA.matrix_det.continuousOn.inv₀ hdet).smul hA.matrix_adjugate.continuousOn
  unfold hessianCellShare
  refine continuousOn_finset_sum _ fun i _ => ?_
  by_cases h : enclosingCell i.1.1.1 = Y
  · simp only [if_pos h, Matrix.mul_apply]
    refine continuousOn_finset_sum _ fun j _ => continuousOn_const.mul ?_
    exact (continuous_apply_apply j i).comp_continuousOn hinv
  · simp only [if_neg h]
    exact continuousOn_const
theorem densitiesAtScaleZero_of_regular (h₁ : chartedEnergyAtMinimizerRegular)
    (h₂ : GaussianMoments.CovarianceEqInverse) : DensitiesAtScaleZero := by
  refine EventuallyOrdered.mono h₁ ?_
  intro T hT hn hE t f F V Y hF hV
  obtain ⟨hC, hcrit, -, hlam, hfloor⟩ := hE t F V hF hV
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold ColdStepAtMirrorFrames.StepParameters.ballRadius
    positivity
  have hside : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨_, _, n, hn', hn₀⟩ := hF
    intro i
    rw [hn' i]
    omega
  have hBo : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < T.ballRadius} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have h0B : (0 : StepVariable (finiteCells F)) ∈
      {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    intro b
    simpa using hρ
  have hc2 : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer T.a T.ρA V) 0 := hC.contDiffAt (hBo.mem_nhds h0B)
  have hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAtMinimizer T.a T.ρA V)) 0 :=
    (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hM := chartedHessian_isSymm T.a T.ρA V hd hc2
  have hfl : ∀ x : StepVariable (finiteCells F),
      T.lam * ∑ b, ‖x b‖ ^ 2 ≤ GaussianMoments.quadForm (chartedHessian T.a T.ρA V 0) x := by
    intro x
    rw [quadForm_chartedHessian, ← secondDerivAlong_eq_hessian_sum T.a T.ρA V hd]
    exact hfloor 0 x h0B
  constructor
  · have hcongr : ∫ τ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam f (.interpolated τ)
        (fun l x V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' x) V =
        ∫ τ in (0 : ℝ)..1, (1 / 2 * hessianCellShare T.a T.ρA T.lam Y V τ -
          (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
            3 / 2 * Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V 0) c‖) -
          ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
            haarLogRatio (coordsAboveFrame true T.a T.ρA 0 V 0 b.1.1 b.1.2) else 0) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      rw [uIcc_of_le zero_le_one] at hτ
      exact observableGaussianMean_interpolated T.a T.ρA T.lam τ f V Y hlam hτ hd hside hM hfl h₂
    have hint : IntervalIntegrable (hessianCellShare T.a T.ρA T.lam Y V) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le zero_le_one]
      exact hessianCellShare_continuousOn T.a T.ρA T.lam Y V hlam hM hfl h₂
    rw [hcongr, intervalIntegral.integral_sub ((hint.const_mul _).sub intervalIntegrable_const)
      intervalIntegrable_const, intervalIntegral.integral_sub (hint.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, intervalIntegral.integral_const]
    unfold stepDensity
    rw [Finset.mul_sum]
    simp only [sub_zero, one_smul]
    ring
  · have hZ := (h₂ ↥(chordBonds (finiteCells F)) (chartedHessian T.a T.ρA V 0) T.lam hlam hM hfl).2.2.1
    have hcongr : ∀ ν ∈ uIcc (0 : ℝ) 1, observableGaussianMean T.a T.ρA T.lam f (.tilted ν)
        (fun l x V' => rescaledCellExpansion T.a T.ρA f l Y V' x) V = cellCentredExpansion true T.a T.ρA 0 f Y 0 V := by
      intro ν _
      show gaussianMean T.a T.ρA T.lam f V (.tilted ν) (fun x => rescaledCellExpansion T.a T.ρA f 0 Y V x) = _
      unfold gaussianMean rescaledCellExpansion
      have hwt : (fun x => ScaledVariables.gaussianWeight T.a T.ρA T.lam f V (.tilted ν) x) =
          GaussianMoments.gaussianWeight (chartedHessian T.a T.ρA V 0) := by
        funext x
        exact gaussianWeight_tilted T.a T.ρA T.lam ν f V hd hside x
      simp only [hwt, zero_smul]
      rw [integral_const_mul, mul_div_assoc, div_self hZ.ne', mul_one]
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const]
    simp
end ScaledVariables
end YangMills.Construction
end
