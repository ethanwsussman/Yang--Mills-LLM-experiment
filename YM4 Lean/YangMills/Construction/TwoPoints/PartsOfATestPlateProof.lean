import YangMills.Construction.BaseFunctionals.PropertiesOfTheBumpFunctionsProof
import YangMills.Construction.Continuum.FlatFunctionsTensorsOfSubTuplesAndSmoothTuples
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Torus.OneBallIntegralsAndLiftOfATestPairProof
import YangMills.Construction.Splines.CubicSplineBasicFacts
import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import YangMills.Construction.TwoPoints.PartsOfATestPlate
import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.TestPlates.PlatePieces
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
open YangMills.Construction.TwoPoints.Shapes
open YangMills.Construction.Splines (cubicSpline cubicSplineIntegral)
theorem abs_apply_le_euclidNorm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : |x i| ≤ euclidNorm x := by
  unfold euclidNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun μ => x μ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
theorem euclidNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
theorem euclidNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    euclidNorm (c • x) = |c| * euclidNorm x := by apply _root_.YangMills.Construction.Mollifiers.BumpProperties.eucNorm_smul <;> assumption
theorem euclidNorm_transCoords_sub_le (x x' : AmbientSpace) :
    euclidNorm (transCoords x - transCoords x') ≤ euclidNorm (x - x') := by
  unfold euclidNorm
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_two, Fin.sum_univ_four, transCoords, Pi.sub_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [sq_nonneg (x 0 - x' 0), sq_nonneg (x 3 - x' 3)]
theorem abs_sub_le_derivUniformNorm_mul {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hb : BddDeriv f)
    (s s' : ℝ) :
    |f s - f s'| ≤ derivUniformNorm (Shapes.ofRealFun f) * |s - s'| := by
  have hc : ContDiff ℝ 1 (Shapes.ofRealFun f) := Complex.ofRealCLM.contDiff.comp hf
  have hd : ∀ x ∈ (univ : Set ℝ), DifferentiableAt ℝ (Shapes.ofRealFun f) x := fun x _ =>
    (hc.differentiable (by norm_num)) x
  have hC : ∀ x ∈ (univ : Set ℝ), ‖deriv (Shapes.ofRealFun f) x‖ ≤
      derivUniformNorm (Shapes.ofRealFun f) :=
    fun x _ => le_ciSup hb x
  have := convex_univ.norm_image_sub_le_of_norm_deriv_le hd hC (mem_univ s') (mem_univ s)
  simpa [Shapes.ofRealFun, ← Complex.ofReal_sub, Real.norm_eq_abs] using this
theorem norm_fderiv_apply_le_gradPlaneNorm (f : (Fin 2 → ℝ) → ℂ) (p v : Fin 2 → ℝ) :
    ‖fderiv ℝ f p v‖ ≤ gradPlaneNorm f p * euclidNorm v := by
  have hv : v = v 0 • Pi.single (0 : Fin 2) (1 : ℝ) + v 1 • Pi.single (1 : Fin 2) (1 : ℝ) := by
    funext i
    fin_cases i <;> simp
  have h1 : fderiv ℝ f p v = (v 0 : ℝ) • gradPlane f p 0 + (v 1 : ℝ) • gradPlane f p 1 := by
    conv_lhs => rw [hv]
    simp [gradPlane]
  rw [h1]
  set a := ‖gradPlane f p 0‖
  set b := ‖gradPlane f p 1‖
  have h2 : ‖(v 0 : ℝ) • gradPlane f p 0 + (v 1 : ℝ) • gradPlane f p 1‖ ≤
      |v 0| * a + |v 1| * b := by
    refine (norm_add_le _ _).trans ?_
    simp [a, b]
  refine h2.trans ?_
  have h3 : gradPlaneNorm f p = Real.sqrt (a ^ 2 + b ^ 2) := by
    simp [gradPlaneNorm, Fin.sum_univ_two, a, b]
  have h4 : euclidNorm v = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
    simp [euclidNorm, Fin.sum_univ_two]
  rw [h3, h4, ← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have e0 : |v 0| ^ 2 = v 0 ^ 2 := sq_abs _
  have e1 : |v 1| ^ 2 = v 1 ^ 2 := sq_abs _
  rw [← e0, ← e1]
  nlinarith [sq_nonneg (|v 0| * b - |v 1| * a)]
theorem norm_sub_le_gradPlaneSup_mul {f : (Fin 2 → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hG : gradPlaneEsup f ≠ ∞) (y y' : Fin 2 → ℝ) :
    ‖f y - f y'‖ ≤ gradPlaneSup f * euclidNorm (y - y') := by
  have hmod : ∀ p, gradPlaneNorm f p ≤ gradPlaneSup f := fun p =>
    (ENNReal.ofReal_le_iff_le_toReal hG).1
      (le_iSup (fun y => ENNReal.ofReal (gradPlaneNorm f y)) p)
  set v := y - y' with hv
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  let γ : ℝ → Fin 2 → ℝ := fun t => y' + t • v
  have hγ : ∀ t, HasDerivAt γ v t := fun t => by
    have := ((hasDerivAt_id t).smul_const v).const_add y'
    simpa [γ] using this
  have hg : ∀ t, HasDerivAt (fun t => f (γ t)) (fderiv ℝ f (γ t) v) t := fun t =>
    ((hdiff (γ t)).hasFDerivAt).comp_hasDerivAt t (hγ t)
  have hbound : ∀ t ∈ (univ : Set ℝ),
      ‖fderiv ℝ f (γ t) v‖ ≤ gradPlaneSup f * euclidNorm v := fun t _ =>
    (norm_fderiv_apply_le_gradPlaneNorm f _ v).trans
      (mul_le_mul_of_nonneg_right (hmod _) (euclidNorm_nonneg v))
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t).hasDerivWithinAt) hbound (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
  have e1 : γ 1 = y := by simp [γ, hv]
  have e0 : γ 0 = y' := by simp [γ]
  simpa [e1, e0] using this
theorem gradPlaneEsup_ne_top {f : (Fin 2 → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : IsCompact (tsupport f)) : gradPlaneEsup f ≠ ∞ := by
  have hcs : HasCompactSupport f := hc
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support (hcs.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hg : ∀ y i, ‖gradPlane f y i‖ ≤ C := fun y i => by
    have := (fderiv ℝ f y).le_opNorm (Pi.single i 1)
    have h1 : ‖(Pi.single i 1 : Fin 2 → ℝ)‖ = 1 := by rw [Pi.norm_single]; simp
    rw [h1, mul_one] at this
    exact this.trans (hC y)
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * C)) (iSup_le fun y => ?_)
  apply ENNReal.ofReal_le_ofReal
  unfold gradPlaneNorm
  apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_two]
  have h0 := hg y 0
  have h1 := hg y 1
  have n0 := norm_nonneg (gradPlane f y 0)
  have n1 := norm_nonneg (gradPlane f y 1)
  nlinarith
theorem mem_realCc1In_iff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {O : Set X}
    {f : X → ℂ} :
    f ∈ realCc1In O ↔
      (ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O) ∧ ∀ x, (f x).im = 0 :=
  Iff.rfl
theorem mem_transProfiles_iff {f : (Fin 2 → ℝ) → ℂ} :
    f ∈ transProfiles ↔
      (ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ univ) ∧ ∀ x, (f x).im = 0 :=
  Iff.rfl
theorem mem_compactC1Real_iff {f : AmbientSpace → ℂ} :
    f ∈ compactC1Real ↔
      (ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ univ) ∧ ∀ x, (f x).im = 0 :=
  Iff.rfl
theorem tsupport_shapesOfRealFun {X : Type*} [TopologicalSpace X] (f : X → ℝ) :
    tsupport (Shapes.ofRealFun f) = tsupport f := by apply _root_.YangMills.Construction.SingleBallPairs.tsupport_complexOfReal <;> assumption
structure ShapeFacts : Prop where
  time_diff : ContDiff ℝ 1 timeBump
  time_nonneg : ∀ s, 0 ≤ timeBump s
  time_le : ∀ s, timeBump s ≤ 1
  time_peak : ∃ s, timeBump s = 1
  time_supp : ∀ s, timeBump s ≠ 0 → s ∈ Icc (2 : ℝ) 3
  time_bdd : BddDeriv timeBump
  time_int : 1 / 2 ≤ ∫ s, timeBump s
  time_pos : 0 < derivUniformNorm (Shapes.ofRealFun timeBump)
  spline_diff : ContDiff ℝ 1 cubicSpline
  spline_nonneg : ∀ s, 0 ≤ cubicSpline s
  spline_le : ∀ s, cubicSpline s ≤ 1
  spline_zero : cubicSpline 0 = 1
  spline_supp : ∀ s, cubicSpline s ≠ 0 → s ∈ Icc (-1 : ℝ) 1
  spline_bdd : BddDeriv cubicSpline
  spline_int : 0 < ∫ s, cubicSpline s
  part_diff : ContDiff ℝ 1 (Shapes.ofRealFun planePartitionOfUnity)
  part_range : ∀ ζ, planePartitionOfUnity ζ ∈ Icc (0 : ℝ) 1
  part_supp : ∀ ζ, planePartitionOfUnity ζ ≠ 0 → ζ ∈ openSquare 1
  part_sum : ∀ ζ, HasSum (fun ι : Fin 2 → ℤ => planePartitionOfUnity (ζ - fun i => (ι i : ℝ))) 1
  part_grad : gradPlaneEsup (Shapes.ofRealFun planePartitionOfUnity) ≠ ∞
  plat_diff : ContDiff ℝ 1 (Shapes.ofRealFun planePlateau)
  plat_range : ∀ ζ, planePlateau ζ ∈ Icc (0 : ℝ) 1
  plat_supp : ∀ ζ, planePlateau ζ ≠ 0 → ζ ∈ openSquare (3 / 2)
  plat_one : ∀ ζ ∈ closedSquare 1, planePlateau ζ = 1
  plat_grad : gradPlaneEsup (Shapes.ofRealFun planePlateau) ≠ ∞
  plat_int : 0 < ∫ ζ, planePlateau ζ
theorem shapeFacts_of (hE : Shapes.ShapesExist.Statement)
    (hB : Splines.CubicSplineBasicFacts) : ShapeFacts := by
  obtain ⟨hInd, hA, hP, hT, hbA, hbB, hGP, hGT, hpos, -, h4⟩ := hE
  obtain ⟨-, hS, hTr, -⟩ := hB
  obtain ⟨hb0, -, hbs, hbd, hble, hb1⟩ := hS
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hA
  obtain ⟨hP1, hP2, hP3⟩ := hP
  obtain ⟨hT1, hT2, hT3⟩ := hT
  have hA1' := mem_realCc1In_iff.1 hA1
  have hP1' := mem_realCc1In_iff.1 hP1
  have hT1' := mem_realCc1In_iff.1 hT1
  refine
    { time_diff := (hInd (9 / 4) (11 / 4) (by norm_num)).2.1
      time_nonneg := hA2
      time_le := fun s => hA3.2 ⟨s, rfl⟩
      time_peak := hA3.1
      time_supp := fun s hs => ?_
      time_bdd := hbA
      time_int := hA4
      time_pos := hpos
      spline_diff := hbd
      spline_nonneg := hb0
      spline_le := fun s => (hble s).trans_eq hb1
      spline_zero := hb1
      spline_supp := fun s hs => hbs (subset_tsupport _ hs)
      spline_bdd := hbB
      spline_int := ?_
      part_diff := hP1'.1.1
      part_range := hP2
      part_supp := fun ζ hζ => ?_
      part_sum := hP3
      part_grad := hGP
      plat_diff := hT1'.1.1
      plat_range := hT2
      plat_supp := fun ζ hζ => ?_
      plat_one := hT3
      plat_grad := hGT
      plat_int := by linarith }
  · have h1 : s ∈ tsupport (Shapes.ofRealFun timeBump) := by
      rw [tsupport_shapesOfRealFun]
      exact subset_tsupport _ hs
    have h2 := hA1'.1.2.2 h1
    exact ⟨h2.1.le, h2.2.le⟩
  · have := hTr.2.2
    have e : cubicSplineIntegral = ∫ s, cubicSpline s := rfl
    rwa [e] at this
  · have h1 : ζ ∈ tsupport (Shapes.ofRealFun planePartitionOfUnity) := by
      rw [tsupport_shapesOfRealFun]
      exact subset_tsupport _ hζ
    exact hP1'.1.2.2 h1
  · have h1 : ζ ∈ tsupport (Shapes.ofRealFun planePlateau) := by
      rw [tsupport_shapesOfRealFun]
      exact subset_tsupport _ hζ
    exact hT1'.1.2.2 h1
theorem derivUniformNorm_nonneg (f : ℝ → ℂ) : 0 ≤ derivUniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem gradPlaneSup_nonneg (f : (Fin 2 → ℝ) → ℂ) : 0 ≤ gradPlaneSup f :=
  ENNReal.toReal_nonneg
theorem lowerShapeBound_pos (h : ShapeFacts) : 0 < lowerShapeBound := by
  have h1 := h.time_pos
  have h2 := derivUniformNorm_nonneg (Shapes.ofRealFun cubicSpline)
  have h3 := gradPlaneSup_nonneg (Shapes.ofRealFun planePlateau)
  unfold lowerShapeBound
  linarith
theorem upperShapeBound_pos (h : ShapeFacts) : 0 < upperShapeBound := by
  have h1 := h.time_pos
  have h2 := derivUniformNorm_nonneg (Shapes.ofRealFun cubicSpline)
  have h3 := gradPlaneSup_nonneg (Shapes.ofRealFun planePlateau)
  have h4 := gradPlaneSup_nonneg (Shapes.ofRealFun planePartitionOfUnity)
  unfold upperShapeBound
  linarith
theorem shapeConst_pos (h : ShapeFacts) : 0 < shapeConst := by
  have h1 : 0 < shapeCoeffOne * (∫ s, cubicSpline s) * ∫ ζ, planePlateau ζ := by
    have := h.spline_int
    have := h.plat_int
    unfold shapeCoeffOne
    positivity
  have h2 : 0 < shapeCoeffTwo / lowerShapeBound :=
    div_pos (by norm_num [shapeCoeffTwo]) (lowerShapeBound_pos h)
  have h3 : 0 < shapeCoeffThree / upperShapeBound :=
    div_pos (by norm_num [shapeCoeffThree]) (upperShapeBound_pos h)
  unfold shapeConst
  exact lt_min one_pos (lt_min h1 (lt_min h2 h3))
theorem shapeConst_le_integral_prod :
    shapeConst ≤ 2 / 1875 * (∫ s, cubicSpline s) * ∫ ζ, planePlateau ζ := by
  unfold shapeConst
  exact (min_le_right _ _).trans (min_le_left _ _)
theorem shapeConst_mul_lowerShapeBound_le (h : ShapeFacts) :
    shapeConst * lowerShapeBound ≤ 2 / 5 := by
  have h1 : shapeConst ≤ shapeCoeffTwo / lowerShapeBound := by
    unfold shapeConst
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have := (le_div_iff₀ (lowerShapeBound_pos h)).1 h1
  simpa [shapeCoeffTwo] using this
theorem shapeConst_mul_upperShapeBound_le (h : ShapeFacts) :
    shapeConst * upperShapeBound ≤ 2 / 5 := by
  have h1 : shapeConst ≤ shapeCoeffThree / upperShapeBound := by
    unfold shapeConst
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have := (le_div_iff₀ (upperShapeBound_pos h)).1 h1
  simpa [shapeCoeffThree] using this
def cellCoord (ϖ : ℝ) (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => ζ i / ϖ - (ι i : ℝ)
theorem contDiff_cellCoord (ϖ : ℝ) (ι : Fin 2 → ℤ) : ContDiff ℝ 1 (cellCoord ϖ ι) := by
  unfold cellCoord
  refine contDiff_pi.2 fun i => ?_
  exact ((contDiff_apply ℝ ℝ i).div_const ϖ).sub contDiff_const
theorem cellCoord_sub {ϖ : ℝ} (ι : Fin 2 → ℤ) (ζ ζ' : Fin 2 → ℝ) :
    cellCoord ϖ ι ζ - cellCoord ϖ ι ζ' = ϖ⁻¹ • (ζ - ζ') := by
  funext i
  simp [cellCoord, div_eq_inv_mul]
  ring
def cellSquare (ϖ : ℝ) (ι : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  Set.pi univ fun i => Icc (ϖ * ι i - 3 / 2 * ϖ) (ϖ * ι i + 3 / 2 * ϖ)
theorem isCompact_cellSquare (ϖ : ℝ) (ι : Fin 2 → ℤ) : IsCompact (cellSquare ϖ ι) :=
  isCompact_univ_pi fun _ => isCompact_Icc
theorem mem_cellSquare_of {ϖ : ℝ} (hϖ : 0 < ϖ) {ι : Fin 2 → ℤ} {ζ : Fin 2 → ℝ}
    (h : cellCoord ϖ ι ζ ∈ openSquare (3 / 2)) : ζ ∈ cellSquare ϖ ι := by
  intro i _
  have hi := h i (mem_univ i)
  simp only [cellCoord, mem_Ioo] at hi
  obtain ⟨h1, h2⟩ := hi
  have e : ζ i = (ζ i / ϖ) * ϖ := by field_simp
  constructor <;> nlinarith
theorem cellPlateauAt_mem_cellSquare (h : ShapeFacts) {ϖ : ℝ} (hϖ : 0 < ϖ) {ι : Fin 2 → ℤ}
    {ζ : Fin 2 → ℝ} (hz : cellPlateauAt ϖ ι ζ ≠ 0) : ζ ∈ cellSquare ϖ ι :=
  mem_cellSquare_of hϖ (h.plat_supp _ hz)
theorem cellBump_le_cellPlateauAt (h : ShapeFacts) (ϖ : ℝ) (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) :
    cellBump ϖ ι ζ ≤ cellPlateauAt ϖ ι ζ := by
  by_cases h0 : cellBump ϖ ι ζ = 0
  · rw [h0]
    exact (h.plat_range _).1
  · have h1 := h.part_supp _ h0
    have h2 : cellPlateauAt ϖ ι ζ = 1 := by
      refine h.plat_one _ fun i _ => ?_
      have := h1 i (mem_univ i)
      exact ⟨this.1.le, this.2.le⟩
    rw [h2]
    exact (h.part_range _).2
theorem cellBump_nonneg (h : ShapeFacts) (ϖ : ℝ) (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) :
    0 ≤ cellBump ϖ ι ζ := (h.part_range _).1
theorem cellBump_le_one (h : ShapeFacts) (ϖ : ℝ) (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) :
    cellBump ϖ ι ζ ≤ 1 := (h.part_range _).2
theorem cellPlateauAt_nonneg (h : ShapeFacts) (ϖ : ℝ) (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) :
    0 ≤ cellPlateauAt ϖ ι ζ := (h.plat_range _).1
theorem cellPlateauAt_le_one (h : ShapeFacts) (ϖ : ℝ) (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) :
    cellPlateauAt ϖ ι ζ ≤ 1 := (h.plat_range _).2
theorem cellPlateauAt_center (h : ShapeFacts) {ϖ : ℝ} (hϖ : 0 < ϖ) (ι : Fin 2 → ℤ) :
    cellPlateauAt ϖ ι (fun i => ϖ * ι i) = 1 := by
  refine h.plat_one _ fun i _ => ?_
  have : (ϖ * (ι i : ℝ)) / ϖ - (ι i : ℝ) = 0 := by
    field_simp
    ring
  simp only [this]
  norm_num
theorem cellPlateauAt_lipschitz (h : ShapeFacts) {ϖ : ℝ} (hϖ : 0 < ϖ) (ι : Fin 2 → ℤ)
    (ζ ζ' : Fin 2 → ℝ) :
    |cellPlateauAt ϖ ι ζ - cellPlateauAt ϖ ι ζ'| ≤
      gradPlaneSup (Shapes.ofRealFun planePlateau) / ϖ * euclidNorm (ζ - ζ') := by
  have h1 := norm_sub_le_gradPlaneSup_mul h.plat_diff h.plat_grad (cellCoord ϖ ι ζ)
    (cellCoord ϖ ι ζ')
  rw [cellCoord_sub, euclidNorm_smul, abs_inv, abs_of_pos hϖ] at h1
  have e : ‖Shapes.ofRealFun planePlateau (cellCoord ϖ ι ζ) -
      Shapes.ofRealFun planePlateau (cellCoord ϖ ι ζ')‖ =
      |cellPlateauAt ϖ ι ζ - cellPlateauAt ϖ ι ζ'| := by
    simp only [Shapes.ofRealFun, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rfl
  rw [e] at h1
  refine h1.trans_eq ?_
  rw [div_eq_mul_inv]
  ring
theorem cellBump_lipschitz (h : ShapeFacts) {ϖ : ℝ} (hϖ : 0 < ϖ) (ι : Fin 2 → ℤ)
    (ζ ζ' : Fin 2 → ℝ) :
    |cellBump ϖ ι ζ - cellBump ϖ ι ζ'| ≤
      gradPlaneSup (Shapes.ofRealFun planePartitionOfUnity) / ϖ * euclidNorm (ζ - ζ') := by
  have h1 := norm_sub_le_gradPlaneSup_mul h.part_diff h.part_grad (cellCoord ϖ ι ζ)
    (cellCoord ϖ ι ζ')
  rw [cellCoord_sub, euclidNorm_smul, abs_inv, abs_of_pos hϖ] at h1
  have e : ‖Shapes.ofRealFun planePartitionOfUnity (cellCoord ϖ ι ζ) -
      Shapes.ofRealFun planePartitionOfUnity (cellCoord ϖ ι ζ')‖ =
      |cellBump ϖ ι ζ - cellBump ϖ ι ζ'| := by
    simp only [Shapes.ofRealFun, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rfl
  rw [e] at h1
  refine h1.trans_eq ?_
  rw [div_eq_mul_inv]
  ring
theorem contDiff_cellPlateauAt (h : ShapeFacts) (ϖ : ℝ) (ι : Fin 2 → ℤ) :
    ContDiff ℝ 1 (Shapes.ofRealFun (cellPlateauAt ϖ ι)) :=
  h.plat_diff.comp (contDiff_cellCoord ϖ ι)
theorem contDiff_cellBump (h : ShapeFacts) (ϖ : ℝ) (ι : Fin 2 → ℤ) :
    ContDiff ℝ 1 (Shapes.ofRealFun (cellBump ϖ ι)) :=
  h.part_diff.comp (contDiff_cellCoord ϖ ι)
section Setting
variable {φ : (Fin 2 → ℝ) → ℂ} {r₁ ϖ κ : ℝ}
theorem plateHyp_contDiff (hs : PlateHypotheses φ r₁ ϖ κ) : ContDiff ℝ 1 φ :=
  (mem_transProfiles_iff.1 hs.profile_mem).1.1
theorem plateHyp_isCompact (hs : PlateHypotheses φ r₁ ϖ κ) : IsCompact (tsupport φ) :=
  (mem_transProfiles_iff.1 hs.profile_mem).1.2.1
theorem plateHyp_eq_re (hs : PlateHypotheses φ r₁ ϖ κ) (ζ : Fin 2 → ℝ) :
    φ ζ = (((φ ζ).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using (mem_transProfiles_iff.1 hs.profile_mem).2 ζ
theorem plateHyp_bddAbove (hs : PlateHypotheses φ r₁ ϖ κ) :
    BddAbove (range fun ζ => ‖φ ζ‖) := by
  obtain ⟨C, hC⟩ := (plateHyp_contDiff hs).continuous.bounded_above_of_compact_support
    (plateHyp_isCompact hs)
  exact ⟨C, by rintro _ ⟨ζ, rfl⟩; exact hC ζ⟩
theorem norm_le_uniformNorm (hs : PlateHypotheses φ r₁ ϖ κ) (ζ : Fin 2 → ℝ) :
    ‖φ ζ‖ ≤ TestFunctions.uniformNorm φ :=
  le_ciSup (plateHyp_bddAbove hs) ζ
theorem uniformNorm_pos (hs : PlateHypotheses φ r₁ ϖ κ) : 0 < TestFunctions.uniformNorm φ := by
  obtain ⟨ζ, hζ⟩ := hs.exists_ne_zero
  exact (norm_pos_iff.2 hζ).trans_le (norm_le_uniformNorm hs ζ)
theorem plateWidthNorm_pos (hs : PlateHypotheses φ r₁ ϖ κ) : 0 < plateWidthNorm ϖ φ := by
  have h1 := uniformNorm_pos hs
  have h2 := mul_nonneg hs.width_pos.le (gradPlaneSup_nonneg φ)
  unfold plateWidthNorm
  linarith
theorem uniformNorm_le_plateWidthNorm (hs : PlateHypotheses φ r₁ ϖ κ) :
    TestFunctions.uniformNorm φ ≤ plateWidthNorm ϖ φ := by
  have h2 := mul_nonneg hs.width_pos.le (gradPlaneSup_nonneg φ)
  unfold plateWidthNorm
  linarith
theorem gradPlaneSup_le_plateWidthNorm_div (hs : PlateHypotheses φ r₁ ϖ κ) :
    gradPlaneSup φ ≤ plateWidthNorm ϖ φ / ϖ := by
  have h1 := uniformNorm_pos hs
  rw [le_div_iff₀ hs.width_pos]
  unfold plateWidthNorm
  nlinarith
theorem re_lipschitz (hs : PlateHypotheses φ r₁ ϖ κ) (ζ ζ' : Fin 2 → ℝ) :
    |(φ ζ).re - (φ ζ').re| ≤ gradPlaneSup φ * euclidNorm (ζ - ζ') := by
  have h1 := norm_sub_le_gradPlaneSup_mul (plateHyp_contDiff hs)
    (gradPlaneEsup_ne_top (plateHyp_contDiff hs) (plateHyp_isCompact hs)) ζ ζ'
  refine le_trans ?_ h1
  have := Complex.abs_re_le_norm (φ ζ - φ ζ')
  simpa using this
theorem abs_supportCells_lt (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) {ι : Fin 2 → ℤ}
    (hι : ι ∈ supportCells ϖ φ) (i : Fin 2) : |(ι i : ℝ)| < r₁ / ϖ + 1 := by
  obtain ⟨ζ, hζ⟩ := hι
  have hϖ := hs.width_pos
  have h1 : cellBump ϖ ι ζ ≠ 0 := fun e => hζ (by simp [localizedProfile, e])
  have h2 : φ ζ ≠ 0 := fun e => hζ (by simp [localizedProfile, e])
  have h3 := (h.part_supp _ h1) i (mem_univ i)
  simp only [mem_Ioo] at h3
  have h4 : euclidNorm ζ ≤ r₁ := hs.tsupport_subset (subset_tsupport _ h2)
  have h5 := (abs_apply_le_euclidNorm ζ i).trans h4
  have h6 : |ζ i / ϖ| ≤ r₁ / ϖ := by
    rw [abs_div, abs_of_pos hϖ]
    exact div_le_div_of_nonneg_right h5 hϖ.le
  rw [abs_le] at h6
  rw [abs_lt]
  constructor <;> linarith [h3.1, h3.2, h6.1, h6.2]
theorem supportCells_finite_ncard_le (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) :
    (supportCells ϖ φ).Finite ∧ ((supportCells ϖ φ).ncard : ℝ) ≤ cellCountBound ϖ r₁ := by
  have hϖ := hs.width_pos
  have hR0 : 0 < r₁ / ϖ := div_pos hs.radius_pos hϖ
  set R := r₁ / ϖ with hR
  set m : ℤ := ⌈R + 1⌉ - 1 with hm
  have hceil : (0 : ℤ) < ⌈R + 1⌉ := Int.ceil_pos.2 (by linarith)
  have hm0 : 0 ≤ m := by omega
  have hmR : (m : ℝ) < R + 1 := by
    have := Int.ceil_lt_add_one (R + 1)
    rw [hm]
    push_cast
    linarith
  let S : Finset (Fin 2 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-m) m
  have hsub : supportCells ϖ φ ⊆ (S : Set (Fin 2 → ℤ)) := by
    intro ι hι
    simp only [S, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hb := abs_lt.1 (abs_supportCells_lt h hs hι i)
    have hle := Int.le_ceil (R + 1)
    have h1 : (ι i : ℝ) < (⌈R + 1⌉ : ℝ) := lt_of_lt_of_le hb.2 hle
    have h2 : ((-ι i : ℤ) : ℝ) < (⌈R + 1⌉ : ℝ) := by
      push_cast
      linarith [hb.1]
    have h1' : ι i < ⌈R + 1⌉ := by exact_mod_cast h1
    have h2' : -ι i < ⌈R + 1⌉ := by exact_mod_cast h2
    constructor <;> omega
  have hfin : (supportCells ϖ φ).Finite := S.finite_toSet.subset hsub
  refine ⟨hfin, ?_⟩
  have h1 : (supportCells ϖ φ).ncard ≤ S.card := by
    have := Set.ncard_le_ncard hsub S.finite_toSet
    rwa [Set.ncard_coe_finset] at this
  have h2 : (S.card : ℝ) = (2 * (m : ℝ) + 1) ^ 2 := by
    have hc : ((Finset.Icc (-m) m).card : ℤ) = 2 * m + 1 := by
      rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
      ring
    have hc' : ((Finset.Icc (-m) m).card : ℝ) = 2 * (m : ℝ) + 1 := by
      exact_mod_cast hc
    simp only [S, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [hc']
  have h3 : (2 * (m : ℝ) + 1) ^ 2 ≤ cellCountBound ϖ r₁ := by
    have hm0' : (0 : ℝ) ≤ m := by exact_mod_cast hm0
    unfold cellCountBound
    have e : 2 * r₁ / ϖ = 2 * R := by rw [hR]; ring
    rw [e]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc ((supportCells ϖ φ).ncard : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h1
    _ = (2 * (m : ℝ) + 1) ^ 2 := h2
    _ ≤ _ := h3
theorem cellsCoverProfile (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) :
    CellsCoverProfile φ r₁ ϖ := by
  obtain ⟨hfin, hcard⟩ := supportCells_finite_ncard_le h hs
  refine ⟨fun ζ => h.part_sum (fun i => ζ i / ϖ), fun ι ζ =>
    ⟨cellBump_nonneg h ϖ ι ζ, cellBump_le_cellPlateauAt h ϖ ι ζ⟩, hfin, hcard, ?_⟩
  have hϖ := hs.width_pos
  have hR : 1 ≤ r₁ / ϖ := (one_le_div hϖ).2 hs.width_le_radius
  have e1 : 2 * r₁ / ϖ = 2 * (r₁ / ϖ) := by ring
  have e2 : 25 * r₁ ^ 2 / ϖ ^ 2 = (5 * (r₁ / ϖ)) ^ 2 := by
    rw [mul_pow, div_pow]
    ring
  unfold cellCountBound
  rw [e1, e2]
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2
def lowerCellReal (ϖ : ℝ) (φ : (Fin 2 → ℝ) → ℂ) (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) : ℝ :=
  2 * plateWidthNorm ϖ φ * cellPlateauAt ϖ ι ζ
def upperCellReal (ϖ : ℝ) (φ : (Fin 2 → ℝ) → ℂ) (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) : ℝ :=
  2 * plateWidthNorm ϖ φ * cellPlateauAt ϖ ι ζ + cellBump ϖ ι ζ * (φ ζ).re
theorem upperCellProfile_eq (hs : PlateHypotheses φ r₁ ϖ κ) (ι : Fin 2 → ℤ) :
    upperCellProfile ϖ φ ι = Shapes.ofRealFun (upperCellReal ϖ φ ι) := by
  funext ζ
  simp only [upperCellProfile, basePedestal, localizedProfile, Shapes.ofRealFun, upperCellReal]
  push_cast
  rw [← plateHyp_eq_re hs ζ]
theorem abs_cellBump_mul_re_le (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ)
    (ι : Fin 2 → ℤ) (ζ : Fin 2 → ℝ) :
    |cellBump ϖ ι ζ * (φ ζ).re| ≤ plateWidthNorm ϖ φ * cellPlateauAt ϖ ι ζ := by
  have h1 := cellBump_nonneg h ϖ ι ζ
  have h2 := cellBump_le_cellPlateauAt h ϖ ι ζ
  have h3 : |(φ ζ).re| ≤ plateWidthNorm ϖ φ :=
    ((Complex.abs_re_le_norm _).trans (norm_le_uniformNorm hs ζ)).trans
      (uniformNorm_le_plateWidthNorm hs)
  rw [abs_mul, abs_of_nonneg h1]
  calc cellBump ϖ ι ζ * |(φ ζ).re| ≤ cellBump ϖ ι ζ * plateWidthNorm ϖ φ :=
        mul_le_mul_of_nonneg_left h3 h1
    _ ≤ cellPlateauAt ϖ ι ζ * plateWidthNorm ϖ φ :=
        mul_le_mul_of_nonneg_right h2 (plateWidthNorm_pos hs).le
    _ = _ := mul_comm _ _
theorem le_upperCellReal (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) (ι : Fin 2 → ℤ)
    (ζ : Fin 2 → ℝ) :
    plateWidthNorm ϖ φ * cellPlateauAt ϖ ι ζ ≤ upperCellReal ϖ φ ι ζ := by
  have := abs_le.1 (abs_cellBump_mul_re_le h hs ι ζ)
  unfold upperCellReal
  linarith [this.1]
theorem upperCellReal_le (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) (ι : Fin 2 → ℤ)
    (ζ : Fin 2 → ℝ) :
    upperCellReal ϖ φ ι ζ ≤ 3 * plateWidthNorm ϖ φ * cellPlateauAt ϖ ι ζ := by
  have := abs_le.1 (abs_cellBump_mul_re_le h hs ι ζ)
  unfold upperCellReal
  linarith [this.2]
theorem pedestalEstimate (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) :
    PedestalEstimate φ ϖ := by
  refine ⟨plateWidthNorm_pos hs, fun ι _ ζ => ?_⟩
  rw [upperCellProfile_eq hs]
  exact ⟨Complex.ofReal_im _, le_upperCellReal h hs ι ζ, upperCellReal_le h hs ι ζ⟩
end Setting
section Shape
variable {ϖ κ : ℝ}
theorem planeBumpAt_nonneg (h : ShapeFacts) (y : Fin 2 → ℝ) : 0 ≤ planeBumpAt ϖ κ y :=
  mul_nonneg (h.time_nonneg _) (h.spline_nonneg _)
theorem planeBumpAt_le_one (h : ShapeFacts) (y : Fin 2 → ℝ) : planeBumpAt ϖ κ y ≤ 1 := by
  unfold planeBumpAt
  exact mul_le_one₀ (h.time_le _) (h.spline_nonneg _) (h.spline_le _)
theorem contDiff_planeBumpAt (h : ShapeFacts) :
    ContDiff ℝ 1 (Shapes.ofRealFun (planeBumpAt ϖ κ)) := by
  have h1 : ContDiff ℝ 1 (planeBumpAt ϖ κ) := by
    unfold planeBumpAt
    exact (h.time_diff.comp ((contDiff_apply ℝ ℝ (0 : Fin 2)).div_const ϖ)).mul
      (h.spline_diff.comp ((contDiff_const.mul (contDiff_apply ℝ ℝ (1 : Fin 2))).div_const _))
  exact Complex.ofRealCLM.contDiff.comp h1
theorem isCompact_stripRect (ϖ r : ℝ) : IsCompact (stripRect ϖ r) := by
  have e : stripRect ϖ r = Set.pi univ fun i : Fin 2 =>
      Icc (![2 * ϖ, -r] i) (![3 * ϖ, r] i) := by
    ext y
    constructor
    · rintro ⟨h0, h1⟩ i _
      fin_cases i
      exacts [h0, h1]
    · intro hy
      exact ⟨hy 0 (mem_univ _), hy 1 (mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_Icc
theorem mem_stripRect_of_planeBumpAt_ne_zero (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : 0 < κ)
    {y : Fin 2 → ℝ} (hy : planeBumpAt ϖ κ y ≠ 0) : y ∈ stripRect ϖ (1 / 4 * κ * ϖ) := by
  have h1 : timeBump (y 0 / ϖ) ≠ 0 := fun e => hy (by simp [planeBumpAt, e])
  have h2 : cubicSpline (4 * y 1 / (κ * ϖ)) ≠ 0 := fun e => hy (by simp [planeBumpAt, e])
  have h3 := h.time_supp _ h1
  have h4 := h.spline_supp _ h2
  have hκϖ : 0 < κ * ϖ := mul_pos hκ hϖ
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_div_iff₀ hϖ).1 h3.1
  · exact (div_le_iff₀ hϖ).1 h3.2
  · have := (le_div_iff₀ hκϖ).1 h4.1
    linarith
  · have := (div_le_iff₀ hκϖ).1 h4.2
    linarith
theorem tsupport_planeBumpAt_subset (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : 0 < κ) :
    tsupport (Shapes.ofRealFun (planeBumpAt ϖ κ)) ⊆ stripRect ϖ (1 / 4 * κ * ϖ) := by
  rw [tsupport_shapesOfRealFun]
  refine closure_minimal (fun y hy => mem_stripRect_of_planeBumpAt_ne_zero h hϖ hκ hy)
    (isCompact_stripRect _ _).isClosed
theorem exists_planeBumpAt_eq_one (h : ShapeFacts) (hϖ : 0 < ϖ) :
    ∃ y, planeBumpAt ϖ κ y = 1 := by
  obtain ⟨s, hs⟩ := h.time_peak
  refine ⟨![ϖ * s, 0], ?_⟩
  have e : ϖ * s / ϖ = s := by field_simp
  simp [planeBumpAt, e, hs, h.spline_zero]
theorem planeBumpAt_mem_cc1Plane (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : 0 < κ) :
    Shapes.ofRealFun (planeBumpAt ϖ κ) ∈ cc1Plane :=
  ⟨contDiff_planeBumpAt h, (isCompact_stripRect ϖ (1 / 4 * κ * ϖ)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_planeBumpAt_subset h hϖ hκ), subset_univ _⟩
theorem planeBumpProperties (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : κ ∈ Icc (1 : ℝ) 2) :
    PlaneBumpProperties ϖ κ := by
  have hκ0 : 0 < κ := by linarith [hκ.1]
  refine ⟨planeBumpAt_nonneg h, ⟨planeBumpAt_mem_cc1Plane h hϖ hκ0, fun y => Complex.ofReal_im _⟩,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := exists_planeBumpAt_eq_one (κ := κ) h hϖ
    exact ⟨y, hy⟩
  · rintro _ ⟨y, rfl⟩
    exact planeBumpAt_le_one h y
  · rw [← tsupport_shapesOfRealFun]
    exact tsupport_planeBumpAt_subset h hϖ hκ0
  · rintro y ⟨h1, h2⟩
    refine ⟨h1, ⟨?_, ?_⟩⟩
    · have := h2.1
      nlinarith [hκ.2]
    · have := h2.2
      nlinarith [hκ.2]
end Shape
theorem reflectAcross_last_apply (x : AmbientSpace) :
    reflectAcross (coordVec 3) x = ![x 0, x 1, x 2, -x 3] := by
  funext i
  fin_cases i <;>
    simp [reflectAcross, euclidDot, PeriodicLattice.coordVec, Pi.single_apply]
  ring
theorem reflectAcross_last_twice (x : AmbientSpace) :
    reflectAcross (coordVec 3) (reflectAcross (coordVec 3) x) = x := by
  rw [reflectAcross_last_apply, reflectAcross_last_apply]
  funext i
  fin_cases i <;> simp
theorem reflectAcross_last_apply_last (x : AmbientSpace) :
    reflectAcross (coordVec 3) x 3 = -x 3 := by
  rw [reflectAcross_last_apply]
  simp
theorem euclidNormVec_reflectAcross_last_sub (x y : AmbientSpace) :
    TorusMetric.euclidNormVec
      (reflectAcross (coordVec 3) x - reflectAcross (coordVec 3) y) =
      TorusMetric.euclidNormVec (x - y) := by
  rw [reflectAcross_last_apply, reflectAcross_last_apply]
  unfold TorusMetric.euclidNormVec
  congr 1
  simp only [Fin.sum_univ_four, Pi.sub_apply]
  simp
  ring
theorem contDiff_reflectAcross_last : ContDiff ℝ 1 (reflectAcross (coordVec 3)) := by
  have e : reflectAcross (coordVec 3) = fun x : AmbientSpace => ![x 0, x 1, x 2, -x 3] :=
    funext reflectAcross_last_apply
  rw [e]
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_apply ℝ ℝ (0 : Fin 4)
  · exact contDiff_apply ℝ ℝ (1 : Fin 4)
  · exact contDiff_apply ℝ ℝ (2 : Fin 4)
  · exact (contDiff_apply ℝ ℝ (3 : Fin 4)).neg
theorem reflectAcross_last_injective : Function.Injective (reflectAcross (coordVec 3)) :=
  Function.LeftInverse.injective reflectAcross_last_twice
theorem reflectAcross_last_surjective : Function.Surjective (reflectAcross (coordVec 3)) :=
  Function.RightInverse.surjective reflectAcross_last_twice
theorem measurePreserving_reflectAcross_last :
    MeasurePreserving (reflectAcross (coordVec 3)) volume volume := by
  have hf : ∀ i : Fin 4, MeasurePreserving (if i = 3 then (Neg.neg : ℝ → ℝ) else id)
      (volume : Measure ℝ) volume := by
    intro i
    by_cases hi : i = 3
    · simp only [hi, if_true]
      exact Measure.measurePreserving_neg volume
    · simp only [hi, if_false]
      exact MeasurePreserving.id _
  have h1 := measurePreserving_pi (fun _ : Fin 4 => (volume : Measure ℝ))
    (fun _ : Fin 4 => (volume : Measure ℝ)) hf
  have e : reflectAcross (coordVec 3) =
      fun (a : AmbientSpace) (i : Fin 4) => (if i = 3 then (Neg.neg : ℝ → ℝ) else id) (a i) := by
    funext x i
    rw [reflectAcross_last_apply]
    fin_cases i <;> simp
  rw [e]
  exact h1
theorem integral_comp_reflectAcross_last (g : AmbientSpace → ℝ) :
    ∫ x, g (reflectAcross (coordVec 3) x) = ∫ x, g x :=
  measurePreserving_reflectAcross_last.integral_comp
    (contDiff_reflectAcross_last.continuous.measurable.measurableEmbedding
      reflectAcross_last_injective) g
theorem uniformNorm_comp_reflectAcross_last {E : Type*} [Norm E] (g : AmbientSpace → E) :
    TestFunctions.uniformNorm (g ∘ reflectAcross (coordVec 3)) = TestFunctions.uniformNorm g :=
  reflectAcross_last_surjective.iSup_comp fun x => ‖g x‖
theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (i : Fin 4) :
    |v i| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem tsupport_ofRealFun (g : AmbientSpace → ℝ) :
    tsupport (TwoPoints.ofRealFun g) = tsupport g := by apply _root_.YangMills.Construction.FlatTensors.tsupport_ofReal_comp <;> assumption
theorem continuous_hasCompactSupport_of_mem {g : AmbientSpace → ℝ}
    (hm : TwoPoints.ofRealFun g ∈ compactC1Real) :
    Continuous g ∧ HasCompactSupport g := by
  obtain ⟨⟨h1, h2, -⟩, -⟩ := mem_compactC1Real_iff.1 hm
  constructor
  · have := Complex.continuous_re.comp h1.continuous
    simpa [Function.comp_def, TwoPoints.ofRealFun] using this
  · have : IsCompact (tsupport g) := by rwa [← tsupport_ofRealFun]
    exact this
theorem isShapedBump_of {f : AmbientSpace → ℝ} {ϑ d : ℝ} {c : AmbientSpace} (hϑd : 0 < ϑ * d)
    (hnn : ∀ x, 0 ≤ f x) (hne : ∃ x, f x ≠ 0)
    (hball : tsupport f ⊆ TestFunctions.closedBallR4 c d)
    (hint : ϑ * TestFunctions.uniformNorm f * d ^ 4 ≤ ∫ x, f x)
    (hlip : ∀ x y, |f x - f y| ≤
      TestFunctions.uniformNorm f / (ϑ * d) * TorusMetric.euclidNormVec (x - y)) :
    TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4
      (fun f => ∫ x, f x) d ϑ c f := by
  have hC : 0 ≤ TestFunctions.uniformNorm f / (ϑ * d) :=
    div_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) hϑd.le
  refine ⟨⟨_, hC, fun x y => hlip x y⟩, hnn, hne, hball, hint, ?_⟩
  exact csInf_le ⟨0, fun C hC => hC.1⟩ ⟨hC, fun x y => hlip x y⟩
theorem reflectedPairAdmissible_of {g : AmbientSpace → ℝ} {ϖ : ℝ} {c : AmbientSpace}
    (hϖ : 0 < ϖ) (hϑ : 0 < shapeConst)
    (hnn : ∀ x, 0 ≤ g x) (hmem : TwoPoints.ofRealFun g ∈ compactC1Real) (hne : ∃ x, g x ≠ 0)
    (hslab : tsupport g ⊆ {x | 2 * ϖ ≤ x 3 ∧ x 3 ≤ 3 * ϖ})
    (hball : tsupport g ⊆ TestFunctions.closedBallR4 c (5 / 2 * ϖ))
    (hint : shapeConst * TestFunctions.uniformNorm g * (5 / 2 * ϖ) ^ 4 ≤ ∫ x, g x)
    (hlip : ∀ x y, |g x - g y| ≤
      TestFunctions.uniformNorm g / (shapeConst * (5 / 2 * ϖ)) *
        TorusMetric.euclidNormVec (x - y)) :
    ReflectedPairAdmissible ϖ (TwoPoints.ofRealFun g) := by
  have hθc : Continuous (reflectAcross (coordVec 3)) := contDiff_reflectAcross_last.continuous
  have hd : 0 < 5 / 2 * ϖ := by positivity
  have hϑd : 0 < shapeConst * (5 / 2 * ϖ) := mul_pos hϑ hd
  have hsup : TestFunctions.uniformNorm (g ∘ (reflectAcross (coordVec 3))) =
      TestFunctions.uniformNorm g := uniformNorm_comp_reflectAcross_last g
  have hts : ∀ x ∈ tsupport (g ∘ (reflectAcross (coordVec 3))),
      (reflectAcross (coordVec 3)) x ∈ tsupport g := by
    have : tsupport (g ∘ (reflectAcross (coordVec 3))) ⊆
        (reflectAcross (coordVec 3)) ⁻¹' tsupport g :=
      closure_minimal (fun x hx => subset_tsupport g hx) ((isClosed_tsupport g).preimage hθc)
    exact this
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀' : (g ∘ (reflectAcross (coordVec 3))) ((reflectAcross (coordVec 3)) x₀) ≠ 0 := by
    simp only [Function.comp_apply]
    rw [reflectAcross_last_twice]
    exact hx₀
  have hbump := isShapedBump_of hϑd hnn ⟨x₀, hx₀⟩ hball hint hlip
  have hbump' : TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4
      (fun f => ∫ x, f x) (5 / 2 * ϖ) shapeConst ((reflectAcross (coordVec 3)) c)
      (g ∘ (reflectAcross (coordVec 3))) := by
    refine isShapedBump_of hϑd (fun x => hnn _) ⟨(reflectAcross (coordVec 3)) x₀, hx₀'⟩ ?_ ?_ ?_
    · intro x hx
      have h1 := hball (hts x hx)
      have h2 := euclidNormVec_reflectAcross_last_sub ((reflectAcross (coordVec 3)) x) c
      rw [reflectAcross_last_twice] at h2
      change TorusMetric.euclidNormVec (x - (reflectAcross (coordVec 3)) c) ≤ 5 / 2 * ϖ
      rw [h2]
      exact h1
    · rw [hsup]
      simp only [Function.comp_apply]
      rw [integral_comp_reflectAcross_last]
      exact hint
    · intro x y
      rw [hsup]
      have h1 := hlip ((reflectAcross (coordVec 3)) x) ((reflectAcross (coordVec 3)) y)
      rw [euclidNormVec_reflectAcross_last_sub] at h1
      exact h1
  have hlo : ENNReal.ofReal (5 / 2 * ϖ) ≤
      TestFunctions.setDistR4 (tsupport (g ∘ (reflectAcross (coordVec 3)))) (tsupport g) := by
    unfold TestFunctions.setDistR4
    refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
    have h1 := hslab (hts a ha)
    have h2 := hslab hb
    simp only [mem_ofPred_eq, reflectAcross_last_apply_last] at h1 h2
    have h3 := abs_apply_le_euclidNormVec (a - b) 3
    simp only [Pi.sub_apply] at h3
    linarith [neg_abs_le (a 3 - b 3), h1.1, h2.1]
  have hhi : TestFunctions.setDistR4 (tsupport (g ∘ (reflectAcross (coordVec 3)))) (tsupport g) ≤
      ENNReal.ofReal (6 * (5 / 2 * ϖ)) := by
    unfold TestFunctions.setDistR4
    have ha : (reflectAcross (coordVec 3)) x₀ ∈ tsupport (g ∘ (reflectAcross (coordVec 3))) :=
      subset_tsupport _ hx₀'
    have hb : x₀ ∈ tsupport g := subset_tsupport _ hx₀
    refine (iInf₂_le ((reflectAcross (coordVec 3)) x₀) ha).trans
      ((iInf₂_le x₀ hb).trans (ENNReal.ofReal_le_ofReal ?_))
    have h2 := hslab hb
    simp only [mem_ofPred_eq] at h2
    have h3 : (2 * x₀ 3) ^ 2 ≤ (6 * ϖ) ^ 2 :=
      pow_le_pow_left₀ (by linarith [h2.1]) (by linarith [h2.2]) 2
    rw [reflectAcross_last_apply]
    unfold TorusMetric.euclidNormVec
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    simp only [Fin.sum_univ_four, Pi.sub_apply]
    simp
    nlinarith
  have hmem' : reflectFun (coordVec 3) (TwoPoints.ofRealFun g) ∈ compactC1Real := by
    obtain ⟨⟨h1, h2, -⟩, -⟩ := mem_compactC1Real_iff.1 hmem
    refine mem_compactC1Real_iff.2 ⟨⟨h1.comp contDiff_reflectAcross_last, ?_, subset_univ _⟩,
      fun x => Complex.ofReal_im _⟩
    refine (h2.image hθc).of_isClosed_subset (isClosed_tsupport _) ?_
    exact closure_minimal (fun x hx => ⟨(reflectAcross (coordVec 3)) x, subset_tsupport _ hx,
      reflectAcross_last_twice x⟩) (h2.image hθc).isClosed
  refine ⟨⟨(g ∘ (reflectAcross (coordVec 3)), g), ?_, rfl, rfl⟩, hmem', hmem,
    uniformNorm_comp_reflectAcross_last _⟩
  unfold TestFunctions.separatedPairsR4 TestFunctions.separatedPairs
  simp only [mem_ofPred_eq]
  exact ⟨(reflectAcross (coordVec 3)) c, c, hbump', hbump, hlo, hhi⟩
def realPlate (ϖ κ : ℝ) (F : (Fin 2 → ℝ) → ℝ) (x : AmbientSpace) : ℝ :=
  planeBumpAt ϖ κ (planeCoords x) * F (transCoords x)
theorem tensorPlate_eq_realPlate (ϖ κ : ℝ) (F : (Fin 2 → ℝ) → ℝ) :
    tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) (Shapes.ofRealFun F) =
      TwoPoints.ofRealFun (realPlate ϖ κ F) := by
  funext x
  simp [tensorPlate, Shapes.ofRealFun, TwoPoints.ofRealFun, realPlate]
structure CellProfileData (ϖ W : ℝ) (ι : Fin 2 → ℤ) (F : (Fin 2 → ℝ) → ℝ) (M m L : ℝ) :
    Prop where
  mem_trans : Shapes.ofRealFun F ∈ transProfiles
  ne_zero_mem : ∀ z, F z ≠ 0 → z ∈ cellSquare ϖ ι
  nonneg : ∀ z, 0 ≤ F z
  le_bound : ∀ z, F z ≤ M
  center_ge : m ≤ F fun i => ϖ * ι i
  plateau_le : ∀ z, W * cellPlateauAt ϖ ι z ≤ F z
  lipschitz : ∀ z z', |F z - F z'| ≤ L * euclidNorm (z - z')
section Plate
variable {ϖ κ W M m L : ℝ} {ι : Fin 2 → ℤ} {F : (Fin 2 → ℝ) → ℝ}
theorem realPlate_nonneg (h : ShapeFacts) (P : CellProfileData ϖ W ι F M m L) (x : AmbientSpace) :
    0 ≤ realPlate ϖ κ F x :=
  mul_nonneg (planeBumpAt_nonneg h _) (P.nonneg _)
theorem realPlate_mem (hEl : TensorPlateSupport) (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : 0 < κ)
    (P : CellProfileData ϖ W ι F M m L) :
    TwoPoints.ofRealFun (realPlate ϖ κ F) ∈ compactC1Real ∧
      ∀ x ∈ tsupport (realPlate ϖ κ F),
        planeCoords x ∈ stripRect ϖ (1 / 4 * κ * ϖ) ∧ transCoords x ∈ cellSquare ϖ ι := by
  obtain ⟨h1, h2⟩ := hEl.1 _ (planeBumpAt_mem_cc1Plane h hϖ hκ) _ P.mem_trans
  rw [tensorPlate_eq_realPlate] at h1 h2
  refine ⟨mem_compactC1Real_iff.2 ⟨h1, fun x => Complex.ofReal_im _⟩, fun x hx => ?_⟩
  rw [← tsupport_ofRealFun, h2] at hx
  refine ⟨tsupport_planeBumpAt_subset h hϖ hκ hx.1, ?_⟩
  have hb : tsupport (Shapes.ofRealFun F) ⊆ cellSquare ϖ ι := by
    rw [tsupport_shapesOfRealFun]
    exact closure_minimal (fun z hz => P.ne_zero_mem z hz) (isCompact_cellSquare ϖ ι).isClosed
  exact hb hx.2
theorem realPlate_uniformNorm_bounds (h : ShapeFacts) (hϖ : 0 < ϖ)
    (P : CellProfileData ϖ W ι F M m L) :
    m ≤ TestFunctions.uniformNorm (realPlate ϖ κ F) ∧
      TestFunctions.uniformNorm (realPlate ϖ κ F) ≤ M := by
  have hb : ∀ x, ‖realPlate ϖ κ F x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (realPlate_nonneg h P x)]
    exact (mul_le_of_le_one_left (P.nonneg _) (planeBumpAt_le_one h _)).trans (P.le_bound _)
  refine ⟨?_, ciSup_le hb⟩
  obtain ⟨y, hy⟩ := exists_planeBumpAt_eq_one (κ := κ) h hϖ
  have hbdd : BddAbove (range fun x => ‖realPlate ϖ κ F x‖) :=
    ⟨M, by rintro _ ⟨x, rfl⟩; exact hb x⟩
  have h1 := le_ciSup hbdd (assemble y fun i => ϖ * ι i)
  have e1 : planeCoords (assemble y fun i => ϖ * ι i) = y := by
    funext i
    fin_cases i <;> simp [planeCoords, assemble]
  have e2 : transCoords (assemble y fun i => ϖ * ι i) = fun i => ϖ * ι i := by
    funext i
    fin_cases i <;> simp [transCoords, assemble]
  have h2 : realPlate ϖ κ F (assemble y fun i => ϖ * ι i) = F fun i => ϖ * ι i := by
    simp only [realPlate]
    rw [e1, e2, hy, one_mul]
  simp only [h2] at h1
  exact P.center_ge.trans ((le_abs_self _).trans h1)
theorem planeBump_factor_lipschitz (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : 1 ≤ κ)
    (x x' : AmbientSpace) (p q p' q' : ℝ)
    (hp : p = timeBump (x 3 / ϖ)) (hq : q = cubicSpline (4 * x 0 / (κ * ϖ)))
    (hp' : p' = timeBump (x' 3 / ϖ)) (hq' : q' = cubicSpline (4 * x' 0 / (κ * ϖ))) :
    |p - p'| ≤ derivUniformNorm (Shapes.ofRealFun timeBump) / ϖ *
      TorusMetric.euclidNormVec (x - x') ∧
    |q - q'| ≤ 4 * derivUniformNorm (Shapes.ofRealFun cubicSpline) / ϖ *
      TorusMetric.euclidNormVec (x - x') := by
  have hκϖ : 0 < κ * ϖ := by positivity
  have hD3 := abs_apply_le_euclidNormVec (x - x') 3
  have hD0 := abs_apply_le_euclidNormVec (x - x') 0
  simp only [Pi.sub_apply] at hD3 hD0
  have hCa := derivUniformNorm_nonneg (Shapes.ofRealFun timeBump)
  have hCb := derivUniformNorm_nonneg (Shapes.ofRealFun cubicSpline)
  constructor
  · rw [hp, hp']
    refine (abs_sub_le_derivUniformNorm_mul h.time_diff h.time_bdd _ _).trans ?_
    have e : x 3 / ϖ - x' 3 / ϖ = (x 3 - x' 3) / ϖ := by ring
    rw [e, abs_div, abs_of_pos hϖ, div_mul_eq_mul_div, mul_div_assoc',
      div_le_div_iff_of_pos_right hϖ]
    exact mul_le_mul_of_nonneg_left hD3 hCa
  · rw [hq, hq']
    refine (abs_sub_le_derivUniformNorm_mul h.spline_diff h.spline_bdd _ _).trans ?_
    have e : 4 * x 0 / (κ * ϖ) - 4 * x' 0 / (κ * ϖ) = 4 * (x 0 - x' 0) / (κ * ϖ) := by ring
    have h1 : |4 * (x 0 - x' 0) / (κ * ϖ)| ≤ 4 * |x 0 - x' 0| / ϖ := by
      rw [abs_div, abs_mul, abs_of_pos hκϖ, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      apply div_le_div_of_nonneg_left (by positivity) hϖ
      nlinarith
    rw [e]
    calc derivUniformNorm (Shapes.ofRealFun cubicSpline) * |4 * (x 0 - x' 0) / (κ * ϖ)|
        ≤ derivUniformNorm (Shapes.ofRealFun cubicSpline) * (4 * |x 0 - x' 0| / ϖ) :=
          mul_le_mul_of_nonneg_left h1 hCb
      _ = 4 * derivUniformNorm (Shapes.ofRealFun cubicSpline) / ϖ * |x 0 - x' 0| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD0 (by positivity)
theorem realPlate_lipschitz (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : 1 ≤ κ)
    (P : CellProfileData ϖ W ι F M m L) (hL : 0 ≤ L) (x x' : AmbientSpace) :
    |realPlate ϖ κ F x - realPlate ϖ κ F x'| ≤
      (derivUniformNorm (Shapes.ofRealFun timeBump) / ϖ * M +
        4 * derivUniformNorm (Shapes.ofRealFun cubicSpline) / ϖ * M + L) *
        TorusMetric.euclidNormVec (x - x') := by
  obtain ⟨hp, hq⟩ := planeBump_factor_lipschitz h hϖ hκ x x' _ _ _ _ rfl rfl rfl rfl
  have hF := P.lipschitz (transCoords x) (transCoords x')
  have hF' := mul_le_mul_of_nonneg_left (euclidNorm_transCoords_sub_le x x') hL
  set D := TorusMetric.euclidNormVec (x - x') with hD
  have hDe : euclidNorm (x - x') = D := rfl
  rw [hDe] at hF'
  set p := timeBump (x 3 / ϖ)
  set q := cubicSpline (4 * x 0 / (κ * ϖ))
  set p' := timeBump (x' 3 / ϖ)
  set q' := cubicSpline (4 * x' 0 / (κ * ϖ))
  set r := F (transCoords x)
  set r' := F (transCoords x')
  have e : realPlate ϖ κ F x - realPlate ϖ κ F x' =
      (p - p') * q * r + p' * (q - q') * r + p' * q' * (r - r') := by
    simp only [realPlate, planeBumpAt, planeCoords]
    simp
    ring
  have hp0 : 0 ≤ p' := h.time_nonneg _
  have hp1 : p' ≤ 1 := h.time_le _
  have hq0 : 0 ≤ q := h.spline_nonneg _
  have hq1 : q ≤ 1 := h.spline_le _
  have hq0' : 0 ≤ q' := h.spline_nonneg _
  have hq1' : q' ≤ 1 := h.spline_le _
  have hr0 : 0 ≤ r := P.nonneg _
  have hr1 : r ≤ M := P.le_bound _
  have hM : 0 ≤ M := hr0.trans hr1
  have t1 : |(p - p') * q * r| ≤ |p - p'| * M := by
    rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hr0, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_left hr0 hq1).trans hr1) (abs_nonneg _)
  have t2 : |p' * (q - q') * r| ≤ |q - q'| * M := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hr0]
    calc p' * |q - q'| * r ≤ 1 * |q - q'| * M := by gcongr
      _ = _ := by ring
  have t3 : |p' * q' * (r - r')| ≤ |r - r'| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hq0']
    exact mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀ hp1 hq0' hq1')
  rw [e]
  have hsum := abs_add_three ((p - p') * q * r) (p' * (q - q') * r) (p' * q' * (r - r'))
  have u1 := mul_le_mul_of_nonneg_right hp hM
  have u2 := mul_le_mul_of_nonneg_right hq hM
  nlinarith
end Plate
section Mass
variable {ϖ κ W M m L : ℝ} {ι : Fin 2 → ℤ} {F : (Fin 2 → ℝ) → ℝ}
theorem integral_comp_div_sub {ϖ : ℝ} (hϖ : 0 < ϖ) (n : ℝ) (f : ℝ → ℝ) :
    ∫ u, f (u / ϖ - n) = ϖ * ∫ s, f s := by
  have h1 := Measure.integral_comp_div (fun v => f (v - n)) ϖ
  rw [h1, abs_of_pos hϖ, integral_sub_right_eq_self f n, smul_eq_mul]
theorem integral_planePlateau :
    ∫ ζ, planePlateau ζ = (∫ s, smoothedIcc (-(5 / 4)) (5 / 4) s) ^ 2 := by
  have h1 := integral_fintype_prod_volume_eq_prod (𝕜 := ℝ)
    (fun _ : Fin 2 => smoothedIcc (-(5 / 4)) (5 / 4))
  have e : (∫ ζ, planePlateau ζ) =
      ∫ x : Fin 2 → ℝ, ∏ i, smoothedIcc (-(5 / 4)) (5 / 4) (x i) := rfl
  rw [e, h1]
  simp [sq]
theorem realPlate_integral_ge (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : 1 ≤ κ) (hW : 0 ≤ W)
    (P : CellProfileData ϖ W ι F M m L) (hi : Integrable (realPlate ϖ κ F)) :
    W * ϖ ^ 4 * (∫ s, cubicSpline s) * (∫ ζ, planePlateau ζ) / 8 ≤ ∫ x, realPlate ϖ κ F x := by
  let si := smoothedIcc (-(5 / 4)) (5 / 4)
  let Fm : Fin 4 → ℝ → ℝ := ![fun u => cubicSpline (4 * u / (κ * ϖ)), fun u => si (u / ϖ - ι 0),
    fun u => si (u / ϖ - ι 1), fun u => timeBump (u / ϖ)]
  have hprod : ∀ x : AmbientSpace, ∏ μ, Fm μ (x μ) =
      planeBumpAt ϖ κ (planeCoords x) * cellPlateauAt ϖ ι (transCoords x) := by
    intro x
    simp only [Fin.prod_univ_four, planeBumpAt, planeCoords, cellPlateauAt, planePlateau,
      transCoords, Fin.prod_univ_two]
    simp [Fm, si]
    ring
  have hnn : ∀ x : AmbientSpace, 0 ≤ W * ∏ μ, Fm μ (x μ) := fun x => by
    rw [hprod]
    exact mul_nonneg hW (mul_nonneg (planeBumpAt_nonneg h _) (cellPlateauAt_nonneg h _ _ _))
  have hlow : ∀ x : AmbientSpace, W * ∏ μ, Fm μ (x μ) ≤ realPlate ϖ κ F x := fun x => by
    rw [hprod]
    have := mul_le_mul_of_nonneg_left (P.plateau_le (transCoords x))
      (planeBumpAt_nonneg (ϖ := ϖ) (κ := κ) h (planeCoords x))
    simp only [realPlate]
    linarith
  have hI := integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hi
    (Filter.Eventually.of_forall hlow)
  have e1 : ∫ x : AmbientSpace, W * ∏ μ, Fm μ (x μ) = W * ∏ μ, ∫ u, Fm μ u := by
    rw [integral_const_mul]
    congr 1
    exact integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) Fm
  have i0 : ∫ u, Fm 0 u = κ * ϖ / 4 * ∫ s, cubicSpline s := by
    have e : Fm 0 = fun u => cubicSpline (u / (κ * ϖ / 4)) := by
      funext u
      simp only [Fm, Matrix.cons_val_zero]
      congr 1
      field_simp
    rw [e, Measure.integral_comp_div, abs_of_pos (by positivity), smul_eq_mul]
  have i1 : ∫ u, Fm 1 u = ϖ * ∫ s, si s := integral_comp_div_sub hϖ _ si
  have i2 : ∫ u, Fm 2 u = ϖ * ∫ s, si s := integral_comp_div_sub hϖ _ si
  have i3 : ∫ u, Fm 3 u = ϖ * ∫ s, timeBump s := by
    have e : Fm 3 = fun u => timeBump (u / ϖ) := rfl
    rw [e, Measure.integral_comp_div, abs_of_pos hϖ, smul_eq_mul]
  rw [e1, Fin.prod_univ_four, i0, i1, i2, i3] at hI
  refine le_trans ?_ hI
  rw [integral_planePlateau]
  set B := ∫ s, cubicSpline s
  set S := ∫ s, si s
  set A := ∫ s, timeBump s
  have hB : 0 < B := h.spline_int
  have hA : 1 / 2 ≤ A := h.time_int
  have hκA : 1 / 2 ≤ κ * A := by nlinarith
  calc W * ϖ ^ 4 * B * S ^ 2 / 8 = W * ϖ ^ 4 * B * S ^ 2 * (1 / 2) / 4 := by ring
    _ ≤ W * ϖ ^ 4 * B * S ^ 2 * (κ * A) / 4 := by gcongr
    _ = _ := by ring
end Mass
theorem cellPlate_facts {ϖ κ W M m L : ℝ} {ι : Fin 2 → ℤ} {F : (Fin 2 → ℝ) → ℝ}
    (hEl : TensorPlateSupport) (h : ShapeFacts) (hϖ : 0 < ϖ) (hκ : κ ∈ Icc (1 : ℝ) 2)
    (hW : 0 < W) (P : CellProfileData ϖ W ι F M m L) (hL : 0 ≤ L) (hM : M ≤ 3 * W) (hm : 0 < m)
    (hLm : derivUniformNorm (Shapes.ofRealFun timeBump) / ϖ * M +
        4 * derivUniformNorm (Shapes.ofRealFun cubicSpline) / ϖ * M + L ≤
      m / (shapeConst * (5 / 2 * ϖ))) :
    IsPlatePiece ϖ (tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) (Shapes.ofRealFun F)) ∧
    m ≤ TestFunctions.uniformNorm
      (tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) (Shapes.ofRealFun F)) ∧
    TestFunctions.uniformNorm
      (tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) (Shapes.ofRealFun F)) ≤ M ∧
    ReflectedPairAdmissible ϖ
      (tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) (Shapes.ofRealFun F)) := by
  have hκ0 : 0 < κ := by linarith [hκ.1]
  have hϑ := shapeConst_pos h
  rw [tensorPlate_eq_realPlate]
  obtain ⟨hmem, hsupp⟩ := realPlate_mem (κ := κ) hEl h hϖ hκ0 P
  obtain ⟨s1, s2⟩ := realPlate_uniformNorm_bounds (κ := κ) h hϖ P
  have hsn : TestFunctions.uniformNorm (TwoPoints.ofRealFun (realPlate ϖ κ F)) =
      TestFunctions.uniformNorm (realPlate ϖ κ F) := by
    simp [TestFunctions.uniformNorm, TwoPoints.ofRealFun]
  have hslab : tsupport (realPlate ϖ κ F) ⊆ {x | 2 * ϖ ≤ x 3 ∧ x 3 ≤ 3 * ϖ} := fun x hx =>
    (hsupp x hx).1.1
  have hne : ∃ x, realPlate ϖ κ F x ≠ 0 := by
    by_contra hc
    push Not at hc
    have : TestFunctions.uniformNorm (realPlate ϖ κ F) = 0 := by
      simp [TestFunctions.uniformNorm, hc]
    linarith
  let c : AmbientSpace := ![0, ϖ * ι 0, ϖ * ι 1, 5 / 2 * ϖ]
  have hball : tsupport (realPlate ϖ κ F) ⊆ TestFunctions.closedBallR4 c (5 / 2 * ϖ) := by
    intro x hx
    obtain ⟨⟨ha, hb⟩, hz⟩ := hsupp x hx
    have z0 := hz 0 (mem_univ _)
    have z1 := hz 1 (mem_univ _)
    have ha1 : 2 * ϖ ≤ x 3 := ha.1
    have ha2 : x 3 ≤ 3 * ϖ := ha.2
    have hb1 : -(1 / 4 * κ * ϖ) ≤ x 0 := hb.1
    have hb2 : x 0 ≤ 1 / 4 * κ * ϖ := hb.2
    have z01 : ϖ * ι 0 - 3 / 2 * ϖ ≤ x 1 := z0.1
    have z02 : x 1 ≤ ϖ * ι 0 + 3 / 2 * ϖ := z0.2
    have z11 : ϖ * ι 1 - 3 / 2 * ϖ ≤ x 2 := z1.1
    have z12 : x 2 ≤ ϖ * ι 1 + 3 / 2 * ϖ := z1.2
    have hκϖ : 1 / 4 * κ * ϖ ≤ 1 / 2 * ϖ := by nlinarith [hκ.2]
    change TorusMetric.euclidNormVec (x - c) ≤ 5 / 2 * ϖ
    unfold TorusMetric.euclidNormVec
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    simp only [Fin.sum_univ_four, Pi.sub_apply]
    have c0 : c 0 = 0 := rfl
    have c1 : c 1 = ϖ * ι 0 := rfl
    have c2 : c 2 = ϖ * ι 1 := rfl
    have c3 : c 3 = 5 / 2 * ϖ := rfl
    rw [c0, c1, c2, c3]
    have q0 : (x 0 - 0) ^ 2 ≤ (1 / 2 * ϖ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have q1 : (x 1 - ϖ * ι 0) ^ 2 ≤ (3 / 2 * ϖ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have q2 : (x 2 - ϖ * ι 1) ^ 2 ≤ (3 / 2 * ϖ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have q3 : (x 3 - 5 / 2 * ϖ) ^ 2 ≤ (1 / 2 * ϖ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith [sq_nonneg ϖ]
  obtain ⟨hcont, hcs⟩ := continuous_hasCompactSupport_of_mem hmem
  have hmass := realPlate_integral_ge (κ := κ) h hϖ hκ.1 hW.le P
    (hcont.integrable_of_hasCompactSupport hcs)
  have hint : shapeConst * TestFunctions.uniformNorm (realPlate ϖ κ F) * (5 / 2 * ϖ) ^ 4 ≤
      ∫ x, realPlate ϖ κ F x := by
    refine le_trans ?_ hmass
    have hB := h.spline_int
    have hI := h.plat_int
    have hT : shapeConst ≤ 2 / 1875 * (∫ s, cubicSpline s) * ∫ ζ, planePlateau ζ :=
      shapeConst_le_integral_prod
    have hS : TestFunctions.uniformNorm (realPlate ϖ κ F) ≤ 3 * W := s2.trans hM
    have hS0 : 0 ≤ TestFunctions.uniformNorm (realPlate ϖ κ F) :=
      Real.iSup_nonneg fun _ => norm_nonneg _
    calc shapeConst * TestFunctions.uniformNorm (realPlate ϖ κ F) * (5 / 2 * ϖ) ^ 4
        ≤ (2 / 1875 * (∫ s, cubicSpline s) * ∫ ζ, planePlateau ζ) * (3 * W) *
            (5 / 2 * ϖ) ^ 4 := by
          gcongr
      _ = _ := by ring
  have hlip : ∀ x y, |realPlate ϖ κ F x - realPlate ϖ κ F y| ≤
      TestFunctions.uniformNorm (realPlate ϖ κ F) / (shapeConst * (5 / 2 * ϖ)) *
        TorusMetric.euclidNormVec (x - y) := by
    intro x y
    refine (realPlate_lipschitz h hϖ hκ.1 P hL x y).trans ?_
    refine mul_le_mul_of_nonneg_right (hLm.trans ?_) (Real.sqrt_nonneg _)
    gcongr
  refine ⟨⟨fun x => ⟨Complex.ofReal_im _, ?_⟩, hmem, ?_⟩, ?_, ?_,
    reflectedPairAdmissible_of hϖ hϑ (realPlate_nonneg h P) hmem hne hslab hball hint hlip⟩
  · simpa [TwoPoints.ofRealFun] using realPlate_nonneg (κ := κ) h P x
  · rw [tsupport_ofRealFun]
    exact hslab
  · rw [hsn]
    exact s1
  · rw [hsn]
    exact s2
theorem mem_transProfiles_of {F : (Fin 2 → ℝ) → ℝ} {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hc : ContDiff ℝ 1 (Shapes.ofRealFun F)) (hs : ∀ z, F z ≠ 0 → z ∈ K) :
    Shapes.ofRealFun F ∈ transProfiles := by
  refine mem_transProfiles_iff.2
    ⟨⟨hc, hK.of_isClosed_subset (isClosed_tsupport _) ?_, subset_univ _⟩,
      fun _ => Complex.ofReal_im _⟩
  rw [tsupport_shapesOfRealFun]
  exact closure_minimal (fun z hz => hs z hz) hK.isClosed
section Cell
variable {φ : (Fin 2 → ℝ) → ℂ} {r₁ ϖ κ : ℝ}
theorem lowerCellReal_data (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) (ι : Fin 2 → ℤ) :
    CellProfileData ϖ (plateWidthNorm ϖ φ) ι (lowerCellReal ϖ φ ι) (2 * plateWidthNorm ϖ φ)
      (2 * plateWidthNorm ϖ φ)
      (2 * plateWidthNorm ϖ φ * gradPlaneSup (Shapes.ofRealFun planePlateau) / ϖ) := by
  have hϖ := hs.width_pos
  have hW := plateWidthNorm_pos hs
  have hbox : ∀ z, lowerCellReal ϖ φ ι z ≠ 0 → z ∈ cellSquare ϖ ι := fun z hz =>
    cellPlateauAt_mem_cellSquare h hϖ fun e => hz (by simp [lowerCellReal, e])
  have hdiff : ContDiff ℝ 1 (Shapes.ofRealFun (lowerCellReal ϖ φ ι)) := by
    have e : Shapes.ofRealFun (lowerCellReal ϖ φ ι) = fun z =>
        ((2 * plateWidthNorm ϖ φ : ℝ) : ℂ) * Shapes.ofRealFun (cellPlateauAt ϖ ι) z := by
      funext z
      simp [Shapes.ofRealFun, lowerCellReal]
    rw [e]
    exact contDiff_const.mul (contDiff_cellPlateauAt h ϖ ι)
  refine ⟨mem_transProfiles_of (isCompact_cellSquare ϖ ι) hdiff hbox, hbox, fun z => ?_,
    fun z => ?_, ?_, fun z => ?_, fun z z' => ?_⟩
  · exact mul_nonneg (by positivity) (cellPlateauAt_nonneg h _ _ _)
  · exact mul_le_of_le_one_right (by positivity) (cellPlateauAt_le_one h _ _ _)
  · simp only [lowerCellReal]
    rw [cellPlateauAt_center h hϖ, mul_one]
  · have := cellPlateauAt_nonneg h ϖ ι z
    simp only [lowerCellReal]
    nlinarith
  · have h1 := cellPlateauAt_lipschitz h hϖ ι z z'
    have e : lowerCellReal ϖ φ ι z - lowerCellReal ϖ φ ι z' =
        2 * plateWidthNorm ϖ φ * (cellPlateauAt ϖ ι z - cellPlateauAt ϖ ι z') := by
      simp only [lowerCellReal]
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * plateWidthNorm ϖ φ)]
    calc 2 * plateWidthNorm ϖ φ * |cellPlateauAt ϖ ι z - cellPlateauAt ϖ ι z'|
        ≤ 2 * plateWidthNorm ϖ φ *
            (gradPlaneSup (Shapes.ofRealFun planePlateau) / ϖ * euclidNorm (z - z')) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
theorem upperCellReal_data (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) (ι : Fin 2 → ℤ) :
    CellProfileData ϖ (plateWidthNorm ϖ φ) ι (upperCellReal ϖ φ ι) (3 * plateWidthNorm ϖ φ)
      (plateWidthNorm ϖ φ)
      ((2 * gradPlaneSup (Shapes.ofRealFun planePlateau) +
        gradPlaneSup (Shapes.ofRealFun planePartitionOfUnity) + 1) * plateWidthNorm ϖ φ / ϖ) := by
  have hϖ := hs.width_pos
  have hW := plateWidthNorm_pos hs
  have hbox : ∀ z, upperCellReal ϖ φ ι z ≠ 0 → z ∈ cellSquare ϖ ι := fun z hz => by
    refine cellPlateauAt_mem_cellSquare h hϖ fun e => hz ?_
    have h0 : cellBump ϖ ι z = 0 :=
      le_antisymm ((cellBump_le_cellPlateauAt h ϖ ι z).trans_eq e) (cellBump_nonneg h ϖ ι z)
    simp [upperCellReal, e, h0]
  have hdiff : ContDiff ℝ 1 (Shapes.ofRealFun (upperCellReal ϖ φ ι)) := by
    have e : Shapes.ofRealFun (upperCellReal ϖ φ ι) = fun z =>
        Shapes.ofRealFun (lowerCellReal ϖ φ ι) z + Shapes.ofRealFun (cellBump ϖ ι) z * φ z := by
      rw [← upperCellProfile_eq hs ι]
      rfl
    rw [e]
    exact (lowerCellReal_data h hs ι |>.mem_trans |> mem_transProfiles_iff.1).1.1.add
      ((contDiff_cellBump h ϖ ι).mul (plateHyp_contDiff hs))
  refine ⟨mem_transProfiles_of (isCompact_cellSquare ϖ ι) hdiff hbox, hbox, fun z => ?_,
    fun z => ?_, ?_, fun z => le_upperCellReal h hs ι z, fun z z' => ?_⟩
  · exact (mul_nonneg hW.le (cellPlateauAt_nonneg h _ _ _)).trans (le_upperCellReal h hs ι z)
  · exact (upperCellReal_le h hs ι z).trans
      (mul_le_of_le_one_right (by positivity) (cellPlateauAt_le_one h _ _ _))
  · have := le_upperCellReal h hs ι fun i => ϖ * ι i
    rwa [cellPlateauAt_center h hϖ, mul_one] at this
  · set D := euclidNorm (z - z') with hD
    have hD0 : 0 ≤ D := euclidNorm_nonneg _
    set Gt := gradPlaneSup (Shapes.ofRealFun planePlateau)
    set Gp := gradPlaneSup (Shapes.ofRealFun planePartitionOfUnity)
    set W := plateWidthNorm ϖ φ
    have h1 := cellPlateauAt_lipschitz h hϖ ι z z'
    have h2 := cellBump_lipschitz h hϖ ι z z'
    have h3 := re_lipschitz hs z z'
    have h4 : gradPlaneSup φ * D ≤ W / ϖ * D :=
      mul_le_mul_of_nonneg_right (gradPlaneSup_le_plateWidthNorm_div hs) hD0
    have h5 : |(φ z).re| ≤ W :=
      ((Complex.abs_re_le_norm _).trans (norm_le_uniformNorm hs z)).trans
        (uniformNorm_le_plateWidthNorm hs)
    have e : upperCellReal ϖ φ ι z - upperCellReal ϖ φ ι z' =
        2 * W * (cellPlateauAt ϖ ι z - cellPlateauAt ϖ ι z') +
        (cellBump ϖ ι z - cellBump ϖ ι z') * (φ z).re +
        cellBump ϖ ι z' * ((φ z).re - (φ z').re) := by
      simp only [upperCellReal]
      ring
    have t1 : |2 * W * (cellPlateauAt ϖ ι z - cellPlateauAt ϖ ι z')| ≤ 2 * W * (Gt / ϖ * D) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * W)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have t2 : |(cellBump ϖ ι z - cellBump ϖ ι z') * (φ z).re| ≤ Gp / ϖ * D * W := by
      rw [abs_mul]
      exact mul_le_mul h2 h5 (abs_nonneg _) (h2.trans' (abs_nonneg _))
    have t3 : |cellBump ϖ ι z' * ((φ z).re - (φ z').re)| ≤ W / ϖ * D := by
      rw [abs_mul, abs_of_nonneg (cellBump_nonneg h _ _ _)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (cellBump_le_one h _ _ _)).trans
        (h3.trans h4)
    rw [e]
    refine (abs_add_three _ _ _).trans ((add_le_add (add_le_add t1 t2) t3).trans_eq ?_)
    ring
end Cell
section Decomposition
variable {φ : (Fin 2 → ℝ) → ℂ} {r₁ ϖ κ : ℝ}
theorem sum_localizedProfile (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ)
    (S : Finset (Fin 2 → ℤ)) (hS : ∀ ι, ι ∈ S ↔ ι ∈ supportCells ϖ φ) (z : Fin 2 → ℝ) :
    ∑ ι ∈ S, localizedProfile ϖ φ ι z = φ z := by
  by_cases hz : φ z = 0
  · simp [localizedProfile, hz]
  · have h1 : HasSum (fun ι => cellBump ϖ ι z) 1 := (cellsCoverProfile h hs).1 z
    have h2 : HasSum (fun ι => cellBump ϖ ι z) (∑ ι ∈ S, cellBump ϖ ι z) :=
      hasSum_sum_of_ne_finset_zero fun ι hι => by
        by_contra hc
        exact hι ((hS ι).2 ⟨z, mul_ne_zero (by exact_mod_cast hc) hz⟩)
    have h3 := h1.unique h2
    simp only [localizedProfile]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← h3]
    simp
theorem widthPlate_eq_finsum (h : ShapeFacts) (hs : PlateHypotheses φ r₁ ϖ κ) :
    widthPlate ϖ κ φ =
      ∑ᶠ ι ∈ supportCells ϖ φ, (upperCellPlate ϖ κ φ ι - lowerCellPlate ϖ κ φ ι) := by
  have hfin : (supportCells ϖ φ).Finite := (supportCells_finite_ncard_le h hs).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  funext x
  rw [Finset.sum_apply]
  have e : ∀ ι, (upperCellPlate ϖ κ φ ι - lowerCellPlate ϖ κ φ ι) x =
      Shapes.ofRealFun (planeBumpAt ϖ κ) (planeCoords x) *
        localizedProfile ϖ φ ι (transCoords x) := by
    intro ι
    simp only [upperCellPlate, lowerCellPlate, tensorPlate, upperCellProfile, lowerCellProfile,
      Pi.sub_apply]
    ring
  simp only [e]
  rw [← Finset.mul_sum, sum_localizedProfile h hs hfin.toFinset (fun ι => hfin.mem_toFinset)]
  rfl
theorem widthPlate_mem (hEl : TensorPlateSupport) (h : ShapeFacts)
    (hs : PlateHypotheses φ r₁ ϖ κ) :
    widthPlate ϖ κ φ ∈ realCc1In {x : AmbientSpace | 0 < x 3} := by
  have hϖ := hs.width_pos
  have hκ0 : 0 < κ := by linarith [hs.dilation_mem.1]
  obtain ⟨h1, h2⟩ := hEl.1 _ (planeBumpAt_mem_cc1Plane h hϖ hκ0) _ hs.profile_mem
  have h1' : ContDiff ℝ 1 (tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) φ) ∧
      IsCompact (tsupport (tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) φ)) ∧
      tsupport (tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) φ) ⊆ univ := h1
  refine mem_realCc1In_iff.2 ⟨⟨h1'.1, h1'.2.1, fun x hx => ?_⟩, fun x => ?_⟩
  · have hx' : x ∈ tsupport (tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) φ) := hx
    rw [h2] at hx'
    have h3 := tsupport_planeBumpAt_subset h hϖ hκ0 hx'.1
    have h4 : 2 * ϖ ≤ x 3 := h3.1.1
    change 0 < x 3
    linarith
  · have := (mem_transProfiles_iff.1 hs.profile_mem).2 (transCoords x)
    simp [widthPlate, tensorPlate, Shapes.ofRealFun, this]
end Decomposition
theorem lower_lipschitz_condition (h : ShapeFacts) {ϖ W : ℝ} (hϖ : 0 < ϖ) (hW : 0 < W) :
    derivUniformNorm (Shapes.ofRealFun timeBump) / ϖ * (2 * W) +
        4 * derivUniformNorm (Shapes.ofRealFun cubicSpline) / ϖ * (2 * W) +
        2 * W * gradPlaneSup (Shapes.ofRealFun planePlateau) / ϖ ≤
      2 * W / (shapeConst * (5 / 2 * ϖ)) := by
  have hϑ := shapeConst_pos h
  have key := shapeConst_mul_lowerShapeBound_le h
  rw [le_div_iff₀ (by positivity)]
  have e : (derivUniformNorm (Shapes.ofRealFun timeBump) / ϖ * (2 * W) +
        4 * derivUniformNorm (Shapes.ofRealFun cubicSpline) / ϖ * (2 * W) +
        2 * W * gradPlaneSup (Shapes.ofRealFun planePlateau) / ϖ) *
        (shapeConst * (5 / 2 * ϖ)) =
      5 * W * (shapeConst * lowerShapeBound) := by
    unfold lowerShapeBound
    field_simp
  rw [e]
  nlinarith
theorem upper_lipschitz_condition (h : ShapeFacts) {ϖ W : ℝ} (hϖ : 0 < ϖ) (hW : 0 < W) :
    derivUniformNorm (Shapes.ofRealFun timeBump) / ϖ * (3 * W) +
        4 * derivUniformNorm (Shapes.ofRealFun cubicSpline) / ϖ * (3 * W) +
        (2 * gradPlaneSup (Shapes.ofRealFun planePlateau) +
          gradPlaneSup (Shapes.ofRealFun planePartitionOfUnity) + 1) * W / ϖ ≤
      W / (shapeConst * (5 / 2 * ϖ)) := by
  have hϑ := shapeConst_pos h
  have key := shapeConst_mul_upperShapeBound_le h
  rw [le_div_iff₀ (by positivity)]
  have e : (derivUniformNorm (Shapes.ofRealFun timeBump) / ϖ * (3 * W) +
        4 * derivUniformNorm (Shapes.ofRealFun cubicSpline) / ϖ * (3 * W) +
        (2 * gradPlaneSup (Shapes.ofRealFun planePlateau) +
          gradPlaneSup (Shapes.ofRealFun planePartitionOfUnity) + 1) * W / ϖ) *
        (shapeConst * (5 / 2 * ϖ)) =
      5 / 2 * W * (shapeConst * upperShapeBound) := by
    unfold upperShapeBound
    field_simp
    ring
  rw [e]
  nlinarith
theorem testPlatePieces (hE : Shapes.ShapesExist.Statement)
    (hB : Splines.CubicSplineBasicFacts)
    (hM : ReflectionsPlaneFacts.Statement) : TestPlatePieces.Statement := by
  have h := shapeFacts_of hE hB
  have hEl : TensorPlateSupport := hM.2.2.2.2.2.2.1
  intro φ r₁ ϖ κ hs
  have hϖ := hs.width_pos
  have hκ := hs.dilation_mem
  have hW := plateWidthNorm_pos hs
  have hLow : ∀ ι, lowerCellPlate ϖ κ φ ι =
      tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ))
        (Shapes.ofRealFun (lowerCellReal ϖ φ ι)) := fun ι => rfl
  have hUp : ∀ ι, upperCellPlate ϖ κ φ ι =
      tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ))
        (Shapes.ofRealFun (upperCellReal ϖ φ ι)) := fun ι => by
    unfold upperCellPlate
    rw [upperCellProfile_eq hs]
  have hL0 : 0 ≤ 2 * plateWidthNorm ϖ φ * gradPlaneSup (Shapes.ofRealFun planePlateau) / ϖ :=
    div_nonneg (mul_nonneg (by positivity) (gradPlaneSup_nonneg _)) hϖ.le
  have hU0 : 0 ≤ (2 * gradPlaneSup (Shapes.ofRealFun planePlateau) +
      gradPlaneSup (Shapes.ofRealFun planePartitionOfUnity) + 1) * plateWidthNorm ϖ φ / ϖ := by
    have h1 := gradPlaneSup_nonneg (Shapes.ofRealFun planePlateau)
    have h2 := gradPlaneSup_nonneg (Shapes.ofRealFun planePartitionOfUnity)
    positivity
  have hlow : ∀ ι, _ := fun ι => cellPlate_facts (κ := κ) hEl h hϖ hκ hW
    (lowerCellReal_data h hs ι) hL0 (by linarith) (by positivity) (lower_lipschitz_condition h hϖ hW)
  have hup : ∀ ι, _ := fun ι => cellPlate_facts (κ := κ) hEl h hϖ hκ hW
    (upperCellReal_data h hs ι) hU0 le_rfl hW (upper_lipschitz_condition h hϖ hW)
  refine ⟨cellsCoverProfile h hs, pedestalEstimate h hs, planeBumpProperties h hϖ hκ,
    ⟨widthPlate_mem hEl h hs, widthPlate_eq_finsum h hs, fun ι _ => ?_⟩, fun ι _ => ?_⟩
  · rw [hLow, hUp]
    obtain ⟨l1, l2, l3, -⟩ := hlow ι
    obtain ⟨u1, u2, u3, -⟩ := hup ι
    exact ⟨u1, l1, le_antisymm l3 l2, u2, u3⟩
  · rw [hLow, hUp]
    exact ⟨(hup ι).2.2.2, (hlow ι).2.2.2⟩
end YangMills.Construction.TwoPoints.TestPlates.PlatePieces
