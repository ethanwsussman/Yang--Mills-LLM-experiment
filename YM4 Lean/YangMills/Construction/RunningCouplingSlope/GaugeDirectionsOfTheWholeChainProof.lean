import YangMills.Construction.Towers.FirstDifferentialInTheExponentialChartVanishesProof
import YangMills.Construction.Lattice.ReversalOfTheAveragingAtABondProof
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.FunctionOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.GaugeDirectionsOfTheWholeChain
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalOnGaugeDirectionsProof
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.GaugeInvariance
open Matrices Tower
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem secondOrder_isLittleO {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (h0 : fderiv ℝ f 0 = 0) :
    (fun w => f w - f 0 - (1 / 2) * fderiv ℝ (fderiv ℝ f) 0 w w) =o[𝓝 0] fun w => ‖w‖ ^ 2 := by
  set A := fderiv ℝ (fderiv ℝ f) 0 with hA
  have hD : HasFDerivAt (fderiv ℝ f) A 0 :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have hsym : ∀ x y, A x y = A y x := (hf.isSymmSndFDerivAt (by simp)).eq
  have hdiff : ∀ᶠ w in 𝓝 (0 : E), DifferentiableAt ℝ f w :=
    (hf.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have h1 := hD.isLittleO
  rw [Asymptotics.isLittleO_iff] at h1
  have h2 : ∀ᶠ w in 𝓝 (0 : E), ‖fderiv ℝ f w - A w‖ ≤ ε * ‖w‖ := by
    filter_upwards [h1 hε] with w hw
    simpa [h0] using hw
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h2.and hdiff)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with w hw
  have hwδ : ‖w‖ < δ := by simpa using hw
  let g : E → ℝ := fun y => f y - (1 / 2) * A y y
  have hq : ∀ y, HasFDerivAt (fun y => A y y) (2 • A y) y := by
    intro y
    have h := (A.hasFDerivAt (x := y)).clm_apply (hasFDerivAt_id y)
    refine h.congr_fderiv ?_
    ext z
    simp [two_smul, hsym z y]
  have hg : ∀ y ∈ Metric.closedBall (0 : E) ‖w‖,
      HasFDerivWithinAt g (fderiv ℝ f y - A y) (Metric.closedBall (0 : E) ‖w‖) y := by
    intro y hy
    have hyδ : dist y 0 < δ := lt_of_le_of_lt (by simpa using hy) hwδ
    have h3 := (hball hyδ).2.hasFDerivAt
    have h4 := h3.sub ((hq y).const_mul (1 / 2 : ℝ))
    refine (h4.congr_fderiv ?_).hasFDerivWithinAt
    ext z
    simp [two_smul]
    ring
  have hb : ∀ y ∈ Metric.closedBall (0 : E) ‖w‖, ‖fderiv ℝ f y - A y‖ ≤ ε * ‖w‖ := by
    intro y hy
    have hyn : ‖y‖ ≤ ‖w‖ := by simpa using hy
    have hyδ : dist y 0 < δ := lt_of_le_of_lt (by simpa using hy) hwδ
    exact (hball hyδ).1.trans (mul_le_mul_of_nonneg_left hyn hε.le)
  have hw0 : w ∈ Metric.closedBall (0 : E) ‖w‖ := by simp
  have h5 := (convex_closedBall (0 : E) ‖w‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hb
    (Metric.mem_closedBall_self (norm_nonneg w)) hw0
  have e : f w - f 0 - (1 / 2) * A w w = g w - g 0 := by
    simp only [g, map_zero, mul_zero, sub_zero]
    ring
  rw [e, norm_pow, norm_norm]
  calc ‖g w - g 0‖ ≤ ε * ‖w‖ * ‖w - 0‖ := h5
    _ = ε * ‖w‖ ^ 2 := by rw [sub_zero]; ring
abbrev _root_.YangMills.SharedProofs.p5928 := @secondOrder_isLittleO
private theorem secondOrder_along_curve {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (h0 : fderiv ℝ f 0 = 0)
    {c : ℝ → E} {v : E} (hc0 : c 0 = 0) (hc : HasDerivAt c v 0) :
    (fun r => f (c r) - f 0 - r ^ 2 / 2 * fderiv ℝ (fderiv ℝ f) 0 v v) =o[𝓝 0]
      fun r : ℝ => r ^ 2 := by
  set A := fderiv ℝ (fderiv ℝ f) 0 with hA
  have ht : Tendsto c (𝓝 0) (𝓝 0) := by
    have := hc.continuousAt.tendsto
    rwa [hc0] at this
  have h1 := (secondOrder_isLittleO hf h0).comp_tendsto ht
  have hO : (fun r => c r) =O[𝓝 0] fun r : ℝ => r := by
    have := hc.isBigO_sub
    simpa [hc0] using this
  have hO2 : (fun r => ‖c r‖ ^ 2) =O[𝓝 0] fun r : ℝ => r ^ 2 := by
    have := (hO.norm_left.pow 2)
    exact this
  have h2 := h1.trans_isBigO hO2
  have hs : Tendsto (fun r : ℝ => r⁻¹ • c r) (𝓝[≠] 0) (𝓝 v) := by
    have := hasDerivAt_iff_tendsto_slope_zero.1 hc
    simpa [hc0] using this
  have hq : Tendsto (fun r : ℝ => A (r⁻¹ • c r) (r⁻¹ • c r)) (𝓝[≠] 0) (𝓝 (A v v)) := by
    have hcont : Continuous fun p : E × E => A p.1 p.2 := by fun_prop
    exact (hcont.tendsto (v, v)).comp (hs.prodMk_nhds hs)
  have h3 : (fun r => (1 / 2) * A (c r) (c r) - r ^ 2 / 2 * A v v) =o[𝓝 0]
      fun r : ℝ => r ^ 2 := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have h4 := Metric.tendsto_nhds.1 hq ε hε
    have h5 := eventually_nhdsWithin_iff.1 h4
    filter_upwards [h5] with r hr
    by_cases h : r = 0
    · subst h
      simp [hc0]
    · have hr' := hr h
      rw [Real.dist_eq] at hr'
      have e : A (c r) (c r) = r ^ 2 * A (r⁻¹ • c r) (r⁻¹ • c r) := by
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        field_simp
      have e2 : (1 / 2) * A (c r) (c r) - r ^ 2 / 2 * A v v =
          r ^ 2 / 2 * (A (r⁻¹ • c r) (r⁻¹ • c r) - A v v) := by
        rw [e]
        ring
      rw [e2, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ 2 / 2),
        abs_of_nonneg (by positivity : 0 ≤ r ^ 2)]
      nlinarith [sq_nonneg r, abs_nonneg (A (r⁻¹ • c r) (r⁻¹ • c r) - A v v)]
  refine (h2.add h3).congr_left fun r => ?_
  simp only [Function.comp]
  ring
abbrev _root_.YangMills.SharedProofs.p98659 := @secondOrder_along_curve
private theorem eq_zero_of_half_sq_mul_isLittleO {c : ℝ}
    (h : (fun t : ℝ => t ^ 2 / 2 * c) =o[𝓝 0] fun t : ℝ => t ^ 2) : c = 0 := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.eq_zero_of_sq_mul_isLittleO <;> assumption
private theorem hessian_diag_eq_of_curves {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (h0 : fderiv ℝ f 0 = 0)
    {c c' : ℝ → E} {v v' : E} (hc0 : c 0 = 0) (hc0' : c' 0 = 0) (hc : HasDerivAt c v 0)
    (hc' : HasDerivAt c' v' 0) (he : ∀ᶠ r in 𝓝 (0 : ℝ), f (c r) = f (c' r)) :
    fderiv ℝ (fderiv ℝ f) 0 v v = fderiv ℝ (fderiv ℝ f) 0 v' v' := by
  have d := (secondOrder_along_curve hf h0 hc0 hc).sub (secondOrder_along_curve hf h0 hc0' hc')
  have d' : (fun t : ℝ => t ^ 2 / 2 * (fderiv ℝ (fderiv ℝ f) 0 v' v' -
      fderiv ℝ (fderiv ℝ f) 0 v v)) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine d.congr' ?_ EventuallyEq.rfl
    filter_upwards [he] with r hr
    simp only [hr]
    ring
  have := eq_zero_of_half_sq_mul_isLittleO d'
  linarith
private theorem mixedDeriv_eq_hessian (g : E → ℝ) (hg : ContDiffAt ℝ 2 g 0) (x y : E) :
    deriv (fun s : ℝ => deriv (fun u : ℝ => g (s • x + u • y)) 0) 0 =
      fderiv ℝ (fderiv ℝ g) 0 x y := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
private theorem hasDerivAt_comp_smul_line {g : E → ℝ} (hg : DifferentiableAt ℝ g 0) (x : E) :
    HasDerivAt (fun u : ℝ => g (u • x)) (fderiv ℝ g 0 x) 0 := by
  have h1 : HasDerivAt (fun u : ℝ => u • x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
  have h2 : HasFDerivAt g (fderiv ℝ g 0) ((0 : ℝ) • x) := by
    simpa using hg.hasFDerivAt
  exact h2.comp_hasDerivAt (0 : ℝ) h1
end Calculus
private def expPath (X : ComplexMatrix2) (r : ℝ) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (((r : ℂ) * Complex.I) • X)
private theorem expPath_zero (X : ComplexMatrix2) : expPath X 0 = 1 := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.expRay_zero <;> assumption
private theorem hasDerivAt_expPath (X : ComplexMatrix2) : HasDerivAt (expPath X) (Complex.I • X) 0 := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.hasDerivAt_expRay <;> assumption
private theorem real_smul_eq_complex_smul (r : ℝ) (X : ComplexMatrix2) : r • X = (r : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
private theorem expPath_mem_specialUnitary (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (r : ℝ) : expPath X r ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.expRay_mem_specialUnitary <;> assumption
private theorem isUnit_of_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : IsUnit g := by apply _root_.YangMills.Construction.PeriodicLattice.OppositeBond.su_isUnit <;> assumption
private theorem conjugateBy_mem {g X : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.conjugateBy_mem_hermitianTraceless <;> assumption
private theorem conj_matExp_eq {g : ComplexMatrix2} (hg : IsUnit g) (X : ComplexMatrix2) :
    g * ComplexMatrix2.matExp (Complex.I • X) * g⁻¹ =
      ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy g X) := by
  rw [ComplexMatrix2.matExp, ComplexMatrix2.matExp, ← Matrix.exp_conj _ _ hg]
  simp [ComplexMatrix2.conjugateBy, mul_assoc]
private def quaternionUnit : Fin 3 → ComplexMatrix2 :=
  ![!![0, Complex.I; Complex.I, 0], !![0, 1; -1, 0], !![Complex.I, 0; 0, -Complex.I]]
private theorem quaternionUnit_mul_self (a : Fin 3) : quaternionUnit a * quaternionUnit a = -1 := by apply _root_.YangMills.Construction.Tower.FirstDerivVanishing.pauliQuaternion_mul_self <;> assumption
private theorem quaternionUnit_conjTranspose (a : Fin 3) :
    (quaternionUnit a).conjTranspose = -quaternionUnit a := by apply _root_.YangMills.Construction.Tower.FirstDerivVanishing.pauliQuaternion_conjTranspose <;> assumption
private theorem quaternionUnit_det (a : Fin 3) : (quaternionUnit a).det = 1 := by apply _root_.YangMills.Construction.Tower.FirstDerivVanishing.pauliQuaternion_det <;> assumption
private theorem quaternionUnit_mem (a : Fin 3) : quaternionUnit a ∈ ComplexMatrix2.specialUnitary := by
  refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨?_, quaternionUnit_det a⟩
  refine Matrix.mem_unitaryGroup_iff.2 ?_
  rw [Matrix.star_eq_conjTranspose, quaternionUnit_conjTranspose, mul_neg, quaternionUnit_mul_self,
    neg_neg]
private theorem sum_conjugateBy_quaternionUnits {X : ComplexMatrix2} (hX : Matrix.trace X = 0) :
    X + ComplexMatrix2.conjugateBy (quaternionUnit 0) X + ComplexMatrix2.conjugateBy (quaternionUnit 1) X +
      ComplexMatrix2.conjugateBy (quaternionUnit 2) X = 0 := by apply _root_.YangMills.Construction.Tower.FirstDerivVanishing.add_conjugateBy_pauliRotations_eq_zero <;> assumption
private def tracelessProjection : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2.traceless :=
  (LinearMap.id - (LinearMap.toSpanSingleton ℂ ComplexMatrix2 (1 : ComplexMatrix2)) ∘ₗ
      ((1 / 2 : ℂ) • Matrix.traceLinearMap (Fin 2) ℂ ℂ)).codRestrict ComplexMatrix2.traceless (by
    intro X
    show Matrix.trace _ = 0
    simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    ring)
private def pauliFunctional (c : Fin 3) : ComplexMatrix2 →L[ℝ] ℝ :=
  Complex.reCLM ∘L
    (LinearMap.toContinuousLinearMap
      ((LinearMap.proj c : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        (OneLoop.pauliCoordinateEquiv.toLinearMap ∘ₗ tracelessProjection))).restrictScalars ℝ
private theorem re_pauliCoeff_eq (c : Fin 3) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    (pauliCoeff c X).re = pauliFunctional c X := by
  have h : X ∈ ComplexMatrix2.traceless := hX.2
  have e : tracelessProjection X = ⟨X, h⟩ := by
    apply Subtype.ext
    have t : Matrix.trace X = 0 := h
    simp [tracelessProjection, t]
  simp [pauliFunctional, pauliCoeff, h, e]
private theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
private theorem hasDerivAt_logSeries_comp (hE : ComplexMatrix2.ExpLogEstimates)
    {f : ℝ → ComplexMatrix2} {v : ComplexMatrix2}
    (hf : HasDerivAt f v 0) (h0 : f 0 = 1) :
    HasDerivAt (fun r => ComplexMatrix2.logSeries (f r)) v 0 := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.hasDerivAt_logSeries_comp <;> assumption
private theorem logSeries_of_specialUnitary (hE : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.specialUnitary) (h1 : ‖A - 1‖ < 1) :
    ∃ Y ∈ ComplexMatrix2.hermitianTraceless, ComplexMatrix2.logSeries A = Complex.I • Y ∧
      ComplexMatrix2.matExp (Complex.I • Y) = A := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.logSeries_of_specialUnitary <;> assumption
private theorem logSeries_inv (hE : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (h1 : ‖A - 1‖ < 1 / 2) :
    ComplexMatrix2.logSeries A⁻¹ = -ComplexMatrix2.logSeries A := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.logSeries_inv <;> assumption
private theorem hasDerivAt_conjugateBy_expPath (X Y : ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => ComplexMatrix2.conjugateBy (expPath (-X) r) (r • Y)) Y 0 := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.hasDerivAt_conjugateBy_expRay <;> assumption
section Lattice
variable {L n k j : ℕ}
private def toEdgeForm (B : Edge L n k j → ComplexMatrix2) : edgeFormSpace L n k j :=
  open Classical in if h : B ∈ edgeFormSpace L n k j then ⟨B, h⟩ else 0
private theorem toEdgeForm_of_mem {B : Edge L n k j → ComplexMatrix2} (h : B ∈ edgeFormSpace L n k j) :
    (toEdgeForm B : Edge L n k j → ComplexMatrix2) = B := by
  simp [toEdgeForm, h]
private theorem toEdgeForm_zero : toEdgeForm (0 : Edge L n k j → ComplexMatrix2) = 0 := by
  apply Subtype.ext
  rw [toEdgeForm_of_mem (zero_mem _)]
  rfl
private theorem edgeForm_apply_mem (B : edgeFormSpace L n k j) (b : Edge L n k j) :
    (B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.edgeForm_apply_mem <;> assumption
private theorem adjointForm_of_pos (u : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    adjointForm u B b = ComplexMatrix2.conjugateBy (u b.source) (B b) := by
  simp only [adjointForm, extendOddly, if_pos h]
private theorem adjointForm_of_not_pos (u : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2) {b : Edge L n k j} (h : ¬b.IsPositivelyOriented) :
    adjointForm u B b = -ComplexMatrix2.conjugateBy (u b.opposite.source) (B b.opposite) := by
  simp only [adjointForm, extendOddly, if_neg h]
private theorem opposite_opposite_edge (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem adjointForm_mem
    (hO : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {u : Vertex L n k j → ComplexMatrix2} (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    (B : edgeFormSpace L n k j) :
    adjointForm u (B : Edge L n k j → ComplexMatrix2) ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [adjointForm_of_pos _ _ hb]
    exact conjugateBy_mem (hu _) (edgeForm_apply_mem B b)
  · rcases hO b with ⟨hp, hr⟩ | ⟨hp, hr⟩
    · rw [adjointForm_of_not_pos _ _ hr, opposite_opposite_edge, adjointForm_of_pos _ _ hp]
    · rw [adjointForm_of_pos _ _ hp, adjointForm_of_not_pos _ _ hr, neg_neg]
private theorem adjointForm_smul (u : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)
    (t : ℝ) : adjointForm u (t • B) = t • adjointForm u B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [adjointForm_of_pos _ _ hb, ComplexMatrix2.conjugateBy]
  · simp [adjointForm_of_not_pos _ _ hb, ComplexMatrix2.conjugateBy]
private theorem adjointForm_const (g : ComplexMatrix2) (B : edgeFormSpace L n k j) (b : Edge L n k j) :
    adjointForm (fun _ => g) (B : Edge L n k j → ComplexMatrix2) b =
      ComplexMatrix2.conjugateBy g ((B : Edge L n k j → ComplexMatrix2) b) := by
  by_cases hb : b.IsPositivelyOriented
  · rw [adjointForm_of_pos _ _ hb]
  · have h2 : (B : Edge L n k j → ComplexMatrix2) b.opposite = -(B : Edge L n k j → ComplexMatrix2) b :=
      B.2.2 b
    rw [adjointForm_of_not_pos _ _ hb, h2]
    simp [ComplexMatrix2.conjugateBy]
private def conjForm (u : Vertex L n k j → ComplexMatrix2) (B : edgeFormSpace L n k j) :
    edgeFormSpace L n k j :=
  toEdgeForm (adjointForm u (B : Edge L n k j → ComplexMatrix2))
private theorem conjForm_coe
    (hO : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {u : Vertex L n k j → ComplexMatrix2} (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    (B : edgeFormSpace L n k j) :
    (conjForm u B : Edge L n k j → ComplexMatrix2) = adjointForm u (B : Edge L n k j → ComplexMatrix2) :=
  toEdgeForm_of_mem (adjointForm_mem hO hu B)
private theorem conjForm_smul
    (hO : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {u : Vertex L n k j → ComplexMatrix2} (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary) (t : ℝ)
    (B : edgeFormSpace L n k j) :
    conjForm u (t • B) = t • conjForm u B := by
  apply Subtype.ext
  show (conjForm u (t • B) : Edge L n k j → ComplexMatrix2) = t • (conjForm u B : Edge L n k j → ComplexMatrix2)
  rw [conjForm_coe hO hu, conjForm_coe hO hu]
  exact adjointForm_smul u _ t
private def gaugePath (l : Vertex L n k j → ComplexMatrix2) (r : ℝ) : Vertex L n k j → ComplexMatrix2 :=
  fun x => expPath (-(l x)) r
private def fieldPath (B : Edge L n k j → ComplexMatrix2) (r : ℝ) : Edge L n k j → ComplexMatrix2 :=
  fun b => expPath (B b) r
private def transformedPath (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)
    (r : ℝ) : Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.gaugeTransform (gaugePath l r) (fieldPath B r)
private def logPath (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2) (r : ℝ) :
    Edge L n k j → ComplexMatrix2 :=
  fun b => Complex.I⁻¹ • ComplexMatrix2.logSeries (transformedPath l B r b)
private theorem expGaugeField_smul_eq_fieldPath (B : Edge L n k j → ComplexMatrix2) (r : ℝ) :
    PeriodicLattice.expGaugeField (r • B) = fieldPath B r := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.expGaugeField_smul <;> assumption
private theorem gaugePath_mem (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (r : ℝ) (x : Vertex L n k j) :
    gaugePath l r x ∈ ComplexMatrix2.specialUnitary :=
  expPath_mem_specialUnitary hI (ComplexMatrix2.hermitianTraceless.neg_mem (hl x)) r
private theorem transformedPath_apply (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2) (r : ℝ) (b : Edge L n k j) :
    transformedPath l B r b = expPath (-(l b.source)) r * expPath (B b) r * expPath (l b.target) r := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.transformedRay_apply <;> assumption
private theorem transformedPath_zero (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    transformedPath l B 0 b = 1 := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.transformedRay_zero <;> assumption
private theorem hasDerivAt_logPath (hE : ComplexMatrix2.ExpLogEstimates)
    (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    HasDerivAt (fun r => logPath l B r b) (B b + vertexCoboundary l b) 0 := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.hasDerivAt_transformedRayLog <;> assumption
private theorem eventually_transformedPath_near_one [Finite (Edge L n k j)]
    (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ∀ b, ‖transformedPath l B r b - 1‖ < 1 / 2 := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.eventually_transformedRay_near_one <;> assumption
private theorem eventually_gaugePath_near_one [Finite (Vertex L n k j)]
    (l : Vertex L n k j → ComplexMatrix2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ∀ x, ComplexMatrix2.operatorNorm (gaugePath l r x - 1) < δ := by
  refine Filter.eventually_all.2 fun x => ?_
  have h := (hasDerivAt_expPath (-(l x))).continuousAt.tendsto
  rw [expPath_zero] at h
  filter_upwards [Metric.tendsto_nhds.1 h δ hδ] with r hr
  rwa [dist_eq_norm] at hr
private theorem transformedPath_mem (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (B : edgeFormSpace L n k j) (r : ℝ)
    (b : Edge L n k j) :
    transformedPath l (B : Edge L n k j → ComplexMatrix2) r b ∈ ComplexMatrix2.specialUnitary := by
  rw [transformedPath_apply]
  exact mul_mem (mul_mem (expPath_mem_specialUnitary hI (ComplexMatrix2.hermitianTraceless.neg_mem (hl _)) r)
    (expPath_mem_specialUnitary hI (edgeForm_apply_mem B b) r)) (expPath_mem_specialUnitary hI (hl _) r)
private theorem transformedPath_opposite (l : Vertex L n k j → ComplexMatrix2) (B : edgeFormSpace L n k j)
    (r : ℝ) (b : Edge L n k j) :
    transformedPath l (B : Edge L n k j → ComplexMatrix2) r b.opposite =
      (transformedPath l (B : Edge L n k j → ComplexMatrix2) r b)⁻¹ := by apply _root_.YangMills.Construction.Tower.HessianOnGaugeDirections.transformedRay_opposite <;> assumption
private theorem logPath_mem (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (B : edgeFormSpace L n k j) {r : ℝ}
    (hs : ∀ b, ‖transformedPath l (B : Edge L n k j → ComplexMatrix2) r b - 1‖ < 1 / 2) :
    logPath l (B : Edge L n k j → ComplexMatrix2) r ∈ edgeFormSpace L n k j := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · obtain ⟨Y, hY, h1, -⟩ := logSeries_of_specialUnitary hE (transformedPath_mem hI hl B r b)
      ((hs b).trans (by norm_num))
    show Complex.I⁻¹ • ComplexMatrix2.logSeries _ ∈ ComplexMatrix2.hermitianTraceless
    rw [h1, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    exact hY
  · show Complex.I⁻¹ • ComplexMatrix2.logSeries _ = -(Complex.I⁻¹ • ComplexMatrix2.logSeries _)
    rw [transformedPath_opposite, logSeries_inv hE (hs b), smul_neg]
private theorem expGaugeField_logPath (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (B : edgeFormSpace L n k j) {r : ℝ}
    (hs : ∀ b, ‖transformedPath l (B : Edge L n k j → ComplexMatrix2) r b - 1‖ < 1 / 2) :
    PeriodicLattice.expGaugeField (logPath l (B : Edge L n k j → ComplexMatrix2) r) =
      transformedPath l (B : Edge L n k j → ComplexMatrix2) r := by
  funext b
  obtain ⟨Y, -, h1, h2⟩ := logSeries_of_specialUnitary hE (transformedPath_mem hI hl B r b)
    ((hs b).trans (by norm_num))
  show ComplexMatrix2.matExp (Complex.I • Complex.I⁻¹ • ComplexMatrix2.logSeries _) = _
  rw [h1, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, h2]
private theorem expTwist_unit (B : edgeFormSpace L n k j) :
    PeriodicLattice.expTwist (B : Edge L n k j → ComplexMatrix2) (fun _ => (1 : ComplexMatrix2)) =
      PeriodicLattice.expGaugeField (B : Edge L n k j → ComplexMatrix2) := by
  funext b
  have h2 : (B : Edge L n k j → ComplexMatrix2) b.opposite = -(B : Edge L n k j → ComplexMatrix2) b :=
    B.2.2 b
  unfold PeriodicLattice.expTwist PeriodicLattice.expGaugeField
  by_cases hb : b.IsPositivelyOriented
  · simp [hb]
  · simp only [hb, if_false, mul_one, h2, smul_neg, ComplexMatrix2.matExp]
    rw [Matrix.exp_neg]
    exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
end Lattice
section Triples
variable {L n k : ℕ}
private def OrientationDichotomy (L n k : ℕ) : Prop :=
  ∀ j, j ≤ k → ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
private def conjLevelForms (u : Vertex L n k 0 → ComplexMatrix2) (ξ : LevelForms L n k) :
    LevelForms L n k :=
  (conjForm u ξ.1, fun i => conjForm (restrictVertexFunction ((i : ℕ) + 1) u) (ξ.2 i))
private def conjTriple (u : Vertex L n k 0 → ComplexMatrix2) (τ : LevelTriple L n k) : LevelTriple L n k :=
  (conjLevelForms u τ.1, conjLevelForms u τ.2.1, conjForm (restrictVertexFunction k u) τ.2.2)
private theorem isConjugatedCurrent_conjLevelForms (hO : OrientationDichotomy L n k)
    {u : Vertex L n k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary) (J : LevelForms L n k) :
    IsConjugatedCurrent u J (conjLevelForms u J) := by
  unfold IsConjugatedCurrent
  exact Prod.ext (conjForm_coe (hO 0 (Nat.zero_le _)) hu J.1)
    (funext fun i => conjForm_coe (hO _ i.2) (fun y => hu _) (J.2 i))
private theorem conjLevelForms_smul (hO : OrientationDichotomy L n k)
    {u : Vertex L n k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary) (t : ℝ) (ξ : LevelForms L n k) :
    conjLevelForms u (t • ξ) = t • conjLevelForms u ξ :=
  Prod.ext (conjForm_smul (hO 0 (Nat.zero_le _)) hu t ξ.1)
    (funext fun i => conjForm_smul (hO _ i.2) (fun _ => hu _) t (ξ.2 i))
private theorem conjTriple_smul (hO : OrientationDichotomy L n k) {u : Vertex L n k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary) (t : ℝ) (τ : LevelTriple L n k) :
    conjTriple u (t • τ) = t • conjTriple u τ :=
  Prod.ext (conjLevelForms_smul hO hu t τ.1) (Prod.ext (conjLevelForms_smul hO hu t τ.2.1)
    (conjForm_smul (hO k le_rfl) (fun _ => hu _) t τ.2.2))
private theorem chainPoint_ext {X Y : ChainPoint L n k} (h1 : X.fine = Y.fine)
    (h2 : ∀ i c, X.noise i c = Y.noise i c) : X = Y := by
  cases X
  cases Y
  simp only [ChainPoint.mk.injEq]
  exact ⟨h1, funext fun i => funext fun c => h2 i c⟩
private theorem noise_expMove_conjLevelForms (hO : OrientationDichotomy L n k)
    {u : Vertex L n k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary) (ξ : LevelForms L n k) (i : Fin k)
    (c : PositiveEdge L n k ((i : ℕ) + 1)) :
    (expMove (conjLevelForms u ξ) (unitPoint L n k)).noise i c =
      (gaugeTransformPoint u (expMove ξ (unitPoint L n k))).noise i c := by
  show ComplexMatrix2.matExp (Complex.I • (conjForm (restrictVertexFunction ((i : ℕ) + 1) u) (ξ.2 i) :
      Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) c.1) * 1 =
    restrictVertexFunction ((i : ℕ) + 1) u c.1.source *
      (ComplexMatrix2.matExp (Complex.I • (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) c.1) * 1) *
      (restrictVertexFunction ((i : ℕ) + 1) u c.1.source)⁻¹
  have hr : ∀ y, restrictVertexFunction ((i : ℕ) + 1) u y ∈ ComplexMatrix2.specialUnitary := fun y => hu _
  rw [conjForm_coe (hO _ i.2) hr, adjointForm_of_pos _ _ c.2, mul_one, mul_one,
    conj_matExp_eq (isUnit_of_mem_specialUnitary (hr _))]
private theorem expMove_conjLevelForms_const (hO : OrientationDichotomy L n k) {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) (ξ : LevelForms L n k) :
    expMove (conjLevelForms (fun _ => g) ξ) (unitPoint L n k) =
      gaugeTransformPoint (fun _ => g) (expMove ξ (unitPoint L n k)) := by
  refine chainPoint_ext ?_ (noise_expMove_conjLevelForms hO (fun _ => hg) ξ)
  show PeriodicLattice.expTwist (conjForm (fun _ => g) ξ.1 : Edge L n k 0 → ComplexMatrix2) (fun _ => 1) =
    fun b => g * PeriodicLattice.expTwist (ξ.1 : Edge L n k 0 → ComplexMatrix2) (fun _ => 1) b * g⁻¹
  rw [expTwist_unit, expTwist_unit]
  funext b
  show ComplexMatrix2.matExp (Complex.I • (conjForm (fun _ => g) ξ.1 : Edge L n k 0 → ComplexMatrix2) b) =
    g * ComplexMatrix2.matExp (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b) * g⁻¹
  rw [conjForm_coe (hO 0 (Nat.zero_le _)) (fun _ => hg), adjointForm_const,
    conj_matExp_eq (isUnit_of_mem_specialUnitary hg)]
private theorem sum_conjForm_quaternionUnits {j : ℕ}
    (hO : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k j) :
    B + conjForm (fun _ => quaternionUnit 0) B + conjForm (fun _ => quaternionUnit 1) B +
      conjForm (fun _ => quaternionUnit 2) B = 0 := by
  apply Subtype.ext
  funext b
  show (B : Edge L n k j → ComplexMatrix2) b +
    (conjForm (fun _ => quaternionUnit 0) B : Edge L n k j → ComplexMatrix2) b +
    (conjForm (fun _ => quaternionUnit 1) B : Edge L n k j → ComplexMatrix2) b +
    (conjForm (fun _ => quaternionUnit 2) B : Edge L n k j → ComplexMatrix2) b = 0
  rw [conjForm_coe hO (fun _ => quaternionUnit_mem 0), conjForm_coe hO (fun _ => quaternionUnit_mem 1),
    conjForm_coe hO (fun _ => quaternionUnit_mem 2), adjointForm_const, adjointForm_const,
    adjointForm_const]
  exact sum_conjugateBy_quaternionUnits (edgeForm_apply_mem B b).2
private theorem sum_conjLevelForms_quaternionUnits (hO : OrientationDichotomy L n k)
    (ξ : LevelForms L n k) :
    ξ + conjLevelForms (fun _ => quaternionUnit 0) ξ + conjLevelForms (fun _ => quaternionUnit 1) ξ +
      conjLevelForms (fun _ => quaternionUnit 2) ξ = 0 :=
  Prod.ext (sum_conjForm_quaternionUnits (hO 0 (Nat.zero_le _)) ξ.1)
    (funext fun i => sum_conjForm_quaternionUnits (hO _ i.2) (ξ.2 i))
private theorem sum_conjTriple_quaternionUnits (hO : OrientationDichotomy L n k) (τ : LevelTriple L n k) :
    τ + conjTriple (fun _ => quaternionUnit 0) τ + conjTriple (fun _ => quaternionUnit 1) τ +
      conjTriple (fun _ => quaternionUnit 2) τ = 0 :=
  Prod.ext (sum_conjLevelForms_quaternionUnits hO τ.1)
    (Prod.ext (sum_conjLevelForms_quaternionUnits hO τ.2.1)
    (sum_conjForm_quaternionUnits (hO k le_rfl) τ.2.2))
private def FormCurveAt {j : ℕ} (γ : ℝ → edgeFormSpace L n k j) (v : edgeFormSpace L n k j) : Prop :=
  ∀ b, HasDerivAt (fun r => (γ r : Edge L n k j → ComplexMatrix2) b)
    ((v : Edge L n k j → ComplexMatrix2) b) 0
private def LevelFormsCurveAt (γ : ℝ → LevelForms L n k) (v : LevelForms L n k) : Prop :=
  FormCurveAt (fun r => (γ r).1) v.1 ∧ ∀ i, FormCurveAt (fun r => (γ r).2 i) (v.2 i)
private def TripleCurveAt (γ : ℝ → LevelTriple L n k) (v : LevelTriple L n k) : Prop :=
  LevelFormsCurveAt (fun r => (γ r).1) v.1 ∧ LevelFormsCurveAt (fun r => (γ r).2.1) v.2.1 ∧
    FormCurveAt (fun r => (γ r).2.2) v.2.2
private theorem exists_edgeForm_coordinates (hc : PauliCoordsOrthonormal)
    (hf : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) :
    ∃ (ι : Type) (_ : Fintype ι) (Ψ : edgeFormSpace L n k j ≃ₗ[ℝ] (ι → ℝ))
      (c : ι → ComplexMatrix2 →L[ℝ] ℝ) (β : ι → Edge L n k j),
      ∀ (f : edgeFormSpace L n k j) (i : ι), Ψ f i = c i ((f : Edge L n k j → ComplexMatrix2) (β i)) := by
  have hb : Finite (Edge L n k j) := Set.finite_univ_iff.1 ((hf L hL k j hj).1 n hn).2.1
  haveI : Finite (PositiveEdge L n k j) := Subtype.finite
  letI : Fintype (Fin 3 × PositiveEdge L n k j) := Fintype.ofFinite _
  obtain ⟨Ψ, hΨ, -⟩ := (hc L n k j hL hn hj).1
  refine ⟨_, inferInstance, Ψ, fun ι => pauliFunctional ι.1, fun ι => ι.2.1, fun f ι => ?_⟩
  have h := congrArg Complex.re (hΨ f ι)
  rw [Complex.ofReal_re] at h
  rw [← h]
  exact re_pauliCoeff_eq ι.1 (edgeForm_apply_mem f ι.2.1)
private theorem hasDerivAt_edgeForm_coordinates {j : ℕ} {ι : Type} [Fintype ι]
    {Ψ : edgeFormSpace L n k j ≃ₗ[ℝ] (ι → ℝ)} {c : ι → ComplexMatrix2 →L[ℝ] ℝ} {β : ι → Edge L n k j}
    (h : ∀ (f : edgeFormSpace L n k j) (i : ι), Ψ f i = c i ((f : Edge L n k j → ComplexMatrix2) (β i)))
    {γ : ℝ → edgeFormSpace L n k j} {v : edgeFormSpace L n k j} (hγ : FormCurveAt γ v) :
    HasDerivAt (fun r => Ψ (γ r)) (Ψ v) 0 := by
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [h]
  exact (c i).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hγ (β i))
private theorem exists_triple_coordinates (hc : PauliCoordsOrthonormal)
    (hf : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) :
    ∃ (N : ℕ) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k),
      ∀ (γ : ℝ → LevelTriple L n k) (v : LevelTriple L n k), TripleCurveAt γ v →
        HasDerivAt (fun r => e.symm (γ r)) (e.symm v) 0 := by
  obtain ⟨ι₀, f₀, Ψ₀, c₀, β₀, h₀⟩ :=
    exists_edgeForm_coordinates (k := k) (j := 0) hc hf hL hn (Nat.zero_le _)
  obtain ⟨ιk, fk, Ψk, ck, βk, hk⟩ := exists_edgeForm_coordinates (k := k) (j := k) hc hf hL hn le_rfl
  choose ιs fs Ψs cs βs hs using fun i : Fin k =>
    exists_edgeForm_coordinates (k := k) (j := (i : ℕ) + 1) hc hf hL hn i.2
  let T : LevelForms L n k ≃ₗ[ℝ] (ι₀ → ℝ) × ((i : Fin k) → ιs i → ℝ) :=
    Ψ₀.prodCongr (LinearEquiv.piCongrRight Ψs)
  let E : LevelTriple L n k ≃ₗ[ℝ]
      ((ι₀ → ℝ) × ((i : Fin k) → ιs i → ℝ)) × ((ι₀ → ℝ) × ((i : Fin k) → ιs i → ℝ)) × (ιk → ℝ) :=
    T.prodCongr (T.prodCongr Ψk)
  have hT : ∀ {γ : ℝ → LevelForms L n k} {v : LevelForms L n k}, LevelFormsCurveAt γ v →
      HasDerivAt (fun r => T (γ r)) (T v) 0 := by
    intro γ v hγ
    exact (hasDerivAt_edgeForm_coordinates h₀ hγ.1).prodMk
      (hasDerivAt_pi.2 fun i => hasDerivAt_edgeForm_coordinates (hs i) (hγ.2 i))
  let b := Module.finBasis ℝ
    (((ι₀ → ℝ) × ((i : Fin k) → ιs i → ℝ)) × ((ι₀ → ℝ) × ((i : Fin k) → ιs i → ℝ)) × (ιk → ℝ))
  refine ⟨_, (E.trans b.equivFun).symm, fun γ v hγ => ?_⟩
  have hE : HasDerivAt (fun r => E (γ r)) (E v) 0 :=
    (hT hγ.1).prodMk ((hT hγ.2.1).prodMk (hasDerivAt_edgeForm_coordinates hk hγ.2.2))
  have hC := (LinearMap.toContinuousLinearMap b.equivFun.toLinearMap).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hE
  exact hC
private theorem conjForm_zero_smul {j : ℕ} (u : Vertex L n k j → ComplexMatrix2)
    (B : edgeFormSpace L n k j) :
    conjForm u ((0 : ℝ) • B) = 0 := by
  have e : (((0 : ℝ) • B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) =
      (0 : ℝ) • (B : Edge L n k j → ComplexMatrix2) := rfl
  have h : adjointForm u (((0 : ℝ) • B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) = 0 := by
    rw [e, adjointForm_smul, zero_smul]
  simp only [conjForm, h, toEdgeForm_zero]
private def gaugeOrbitCurve (l : Vertex L n k 0 → ComplexMatrix2) (τ : LevelTriple L n k) (r : ℝ) :
    LevelTriple L n k :=
  ((toEdgeForm (logPath l (τ.1.1 : Edge L n k 0 → ComplexMatrix2) r),
      (conjLevelForms (gaugePath l r) (r • τ.1)).2),
    conjLevelForms (gaugePath l r) (r • τ.2.1),
    conjForm (restrictVertexFunction k (gaugePath l r)) (r • τ.2.2))
private theorem gaugeOrbitCurve_zero (l : Vertex L n k 0 → ComplexMatrix2) (τ : LevelTriple L n k) :
    gaugeOrbitCurve l τ 0 = 0 := by
  have h1 : logPath l (τ.1.1 : Edge L n k 0 → ComplexMatrix2) 0 = 0 := by
    funext b
    simp [logPath, transformedPath_zero, logSeries_one]
  refine Prod.ext (Prod.ext ?_ (funext fun i => ?_)) (Prod.ext (Prod.ext ?_ (funext fun i => ?_)) ?_)
  · show toEdgeForm (logPath l (τ.1.1 : Edge L n k 0 → ComplexMatrix2) 0) = 0
    rw [h1]
    exact toEdgeForm_zero
  · exact conjForm_zero_smul _ _
  · exact conjForm_zero_smul _ _
  · exact conjForm_zero_smul _ _
  · exact conjForm_zero_smul _ _
private theorem formCurveAt_conjForm {j : ℕ}
    (hO : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) {m : Vertex L n k j → ComplexMatrix2}
    (hm : ∀ x, m x ∈ ComplexMatrix2.hermitianTraceless)
    (B : edgeFormSpace L n k j) : FormCurveAt (fun r => conjForm (gaugePath m r) (r • B)) B := by
  intro b
  by_cases hb : b.IsPositivelyOriented
  · have e : (fun r : ℝ => (conjForm (gaugePath m r) (r • B) : Edge L n k j → ComplexMatrix2) b) =
        fun r : ℝ => ComplexMatrix2.conjugateBy (expPath (-(m b.source)) r)
          (r • (B : Edge L n k j → ComplexMatrix2) b) := by
      funext r
      rw [conjForm_coe hO (gaugePath_mem hI hm r), adjointForm_of_pos _ _ hb]
      rfl
    rw [e]
    exact hasDerivAt_conjugateBy_expPath _ _
  · have e : (fun r : ℝ => (conjForm (gaugePath m r) (r • B) : Edge L n k j → ComplexMatrix2) b) =
        fun r : ℝ => -ComplexMatrix2.conjugateBy (expPath (-(m b.opposite.source)) r)
          (r • (B : Edge L n k j → ComplexMatrix2) b.opposite) := by
      funext r
      rw [conjForm_coe hO (gaugePath_mem hI hm r), adjointForm_of_not_pos _ _ hb]
      rfl
    rw [e]
    have h2 : (B : Edge L n k j → ComplexMatrix2) b.opposite = -(B : Edge L n k j → ComplexMatrix2) b :=
      B.2.2 b
    have h3 := (hasDerivAt_conjugateBy_expPath (m b.opposite.source)
      ((B : Edge L n k j → ComplexMatrix2) b.opposite)).neg
    exact h3.congr_deriv (by rw [h2, neg_neg])
private theorem formCurveAt_logPath [Finite (Edge L n k 0)] (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (B A : edgeFormSpace L n k 0) (hA : (A : Edge L n k 0 → ComplexMatrix2) = vertexCoboundary l) :
    FormCurveAt (fun r => toEdgeForm (logPath l (B : Edge L n k 0 → ComplexMatrix2) r)) (B + A) := by
  intro b
  have h := hasDerivAt_logPath hE l (B : Edge L n k 0 → ComplexMatrix2) b
  have e : (((B + A : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) b) =
      (B : Edge L n k 0 → ComplexMatrix2) b + vertexCoboundary l b := by
    rw [← hA]
    rfl
  rw [e]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_transformedPath_near_one l (B : Edge L n k 0 → ComplexMatrix2)] with r hr
  rw [toEdgeForm_of_mem (logPath_mem hE hI hl B hr)]
private theorem tripleCurveAt_gaugeOrbitCurve [Finite (Edge L n k 0)] (hO : OrientationDichotomy L n k)
    (hE : ComplexMatrix2.ExpLogEstimates) (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {l : Vertex L n k 0 → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (A : edgeFormSpace L n k 0)
    (hA : (A : Edge L n k 0 → ComplexMatrix2) = vertexCoboundary l) (τ : LevelTriple L n k) :
    TripleCurveAt (gaugeOrbitCurve l τ) (τ + backgroundOnlyTriple A) := by
  have hr : ∀ {j : ℕ} (hj : j ≤ k) (B : edgeFormSpace L n k j),
      FormCurveAt (fun r => conjForm (restrictVertexFunction j (gaugePath l r)) (r • B)) B :=
    fun hj B => formCurveAt_conjForm (m := restrictVertexFunction _ l) (hO _ hj) hI (fun y => hl _) B
  have h0 : ∀ B : edgeFormSpace L n k 0, FormCurveAt (fun r => conjForm (gaugePath l r) (r • B)) B :=
    fun B => formCurveAt_conjForm (hO 0 (Nat.zero_le _)) hI hl B
  have hz : ∀ {j : ℕ} (B : edgeFormSpace L n k j), B + 0 = B := fun B => add_zero B
  refine ⟨⟨?_, fun i => ?_⟩, ⟨?_, fun i => ?_⟩, ?_⟩
  · exact formCurveAt_logPath hE hI hl τ.1.1 A hA
  · have h := hr i.2 (τ.1.2 i)
    have e : (τ + backgroundOnlyTriple A).1.2 i = τ.1.2 i := hz _
    rw [e]
    exact h
  · have e : (τ + backgroundOnlyTriple A).2.1.1 = τ.2.1.1 := hz _
    rw [e]
    exact h0 _
  · have h := hr i.2 (τ.2.1.2 i)
    have e : (τ + backgroundOnlyTriple A).2.1.2 i = τ.2.1.2 i := hz _
    rw [e]
    exact h
  · have h := hr le_rfl τ.2.2
    have e : (τ + backgroundOnlyTriple A).2.2 = τ.2.2 := hz _
    rw [e]
    exact h
private theorem eventually_expMove_gaugeOrbitCurve [Finite (Edge L n k 0)] (hO : OrientationDichotomy L n k)
    (hE : ComplexMatrix2.ExpLogEstimates) (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {l : Vertex L n k 0 → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (τ : LevelTriple L n k) :
    ∀ᶠ r in 𝓝 (0 : ℝ), expMove (gaugeOrbitCurve l τ r).1 (unitPoint L n k) =
      gaugeTransformPoint (gaugePath l r) (expMove (r • τ).1 (unitPoint L n k)) := by
  filter_upwards [eventually_transformedPath_near_one l (τ.1.1 : Edge L n k 0 → ComplexMatrix2)] with r hs
  have hm := logPath_mem hE hI hl τ.1.1 hs
  refine chainPoint_ext ?_ fun i c => ?_
  · show PeriodicLattice.expTwist (toEdgeForm (logPath l (τ.1.1 : Edge L n k 0 → ComplexMatrix2) r) :
        Edge L n k 0 → ComplexMatrix2) (fun _ => 1) =
      fun b => gaugePath l r b.source * PeriodicLattice.expTwist ((r • τ.1.1 : edgeFormSpace L n k 0) :
        Edge L n k 0 → ComplexMatrix2) (fun _ => 1) b * (gaugePath l r b.target)⁻¹
    rw [expTwist_unit, expTwist_unit, toEdgeForm_of_mem hm, expGaugeField_logPath hE hI hl τ.1.1 hs]
    have e : ((r • τ.1.1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
        r • (τ.1.1 : Edge L n k 0 → ComplexMatrix2) := rfl
    rw [e, expGaugeField_smul_eq_fieldPath]
    rfl
  · exact noise_expMove_conjLevelForms hO (gaugePath_mem hI hl r) (r • τ.1) i c
private def GaugeInvariantNear (a : ℝ) {N : ℕ} (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) (δ : ℝ) :
    Prop :=
  ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
    ∀ v : Vertex L n k 0 → ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) →
      ((∀ x, ComplexMatrix2.operatorNorm (v x - 1) < δ) ∨ ∀ x y, v x = v y) →
      ∀ (J' : LevelForms L n k) (μ' : edgeFormSpace L n k k),
        IsConjugatedCurrent v (e w).2.1 J' →
        (μ' : Edge L n k k → ComplexMatrix2) =
          adjointForm (restrictVertexFunction k v) ((e w).2.2 : Edge L n k k → ComplexMatrix2) →
        chainFreeEnergy a (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))) J' μ' =
          tripleFreeEnergy a (e w)
private theorem eventually_tripleFreeEnergy_eq {a : ℝ} {N : ℕ}
    {e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k} {δ : ℝ}
    (hev : GaugeInvariantNear a e δ)
    (τ : LevelTriple L n k) {γ : ℝ → LevelTriple L n k} {u : ℝ → Vertex L n k 0 → ComplexMatrix2}
    (hu : ∀ r x, u r x ∈ PeriodicLattice.compactGaugeGroup)
    (hn : ∀ᶠ r in 𝓝 (0 : ℝ), (∀ x, ComplexMatrix2.operatorNorm (u r x - 1) < δ) ∨ ∀ x y, u r x = u r y)
    (hγ : ∀ᶠ r in 𝓝 (0 : ℝ), expMove (γ r).1 (unitPoint L n k) =
      gaugeTransformPoint (u r) (expMove (r • τ).1 (unitPoint L n k)))
    (hJ : ∀ r, IsConjugatedCurrent (u r) (r • τ).2.1 (γ r).2.1)
    (hμ : ∀ r, ((γ r).2.2 : Edge L n k k → ComplexMatrix2) =
      adjointForm (restrictVertexFunction k (u r)) ((r • τ).2.2 : Edge L n k k → ComplexMatrix2)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), tripleFreeEnergy a (γ r) = tripleFreeEnergy a (r • τ) := by
  have ht : Tendsto (fun r : ℝ => r • e.symm τ) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => r • e.symm τ := by fun_prop
    simpa using hc.tendsto 0
  filter_upwards [ht.eventually hev, hn, hγ] with r h1 h2 h3
  have ew : e (r • e.symm τ) = r • τ := by simp
  rw [ew] at h1
  have h4 := h1 (u r) (hu r) h2 _ _ (hJ r) (hμ r)
  rw [tripleFreeEnergy, h3]
  exact h4
private theorem hasDerivAt_tripleFreeEnergy_line {a : ℝ} {N : ℕ}
    {e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k}
    {f : (Fin N → ℝ) → ℝ} (hfe : f = fun w => tripleFreeEnergy a (e w)) (hd : DifferentiableAt ℝ f 0)
    (τ : LevelTriple L n k) :
    HasDerivAt (fun r : ℝ => tripleFreeEnergy a (r • τ)) (fderiv ℝ f 0 (e.symm τ)) 0 := by
  have h := hasDerivAt_comp_smul_line hd (e.symm τ)
  have e1 : (fun u : ℝ => f (u • e.symm τ)) = fun r : ℝ => tripleFreeEnergy a (r • τ) := by
    funext u
    simp [hfe]
  rwa [e1] at h
private theorem fderiv_conjTriple_quaternionUnit {a : ℝ} {N : ℕ}
    {e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k}
    {δ : ℝ} (hev : GaugeInvariantNear a e δ) (hOr : OrientationDichotomy L n k) {f : (Fin N → ℝ) → ℝ}
    (hfe : f = fun w => tripleFreeEnergy a (e w)) (hd : DifferentiableAt ℝ f 0) (c : Fin 3)
    (τ : LevelTriple L n k) :
    fderiv ℝ f 0 (e.symm (conjTriple (fun _ => quaternionUnit c) τ)) = fderiv ℝ f 0 (e.symm τ) := by
  have hu : ∀ _ : Vertex L n k 0, quaternionUnit c ∈ ComplexMatrix2.specialUnitary :=
    fun _ => quaternionUnit_mem c
  have hs := eventually_tripleFreeEnergy_eq hev τ
    (γ := fun r => conjTriple (fun _ => quaternionUnit c) (r • τ))
    (u := fun _ _ => quaternionUnit c) (fun _ _ => quaternionUnit_mem c)
    (Eventually.of_forall fun r => Or.inr fun _ _ => rfl)
    (Eventually.of_forall fun r => expMove_conjLevelForms_const hOr (quaternionUnit_mem c) _)
    (fun r => isConjugatedCurrent_conjLevelForms hOr hu _)
    (fun r => conjForm_coe (hOr k le_rfl) (fun _ => quaternionUnit_mem c) _)
  simp only [conjTriple_smul hOr hu] at hs
  exact (hasDerivAt_tripleFreeEnergy_line hfe hd _).unique
    ((hasDerivAt_tripleFreeEnergy_line hfe hd τ).congr_of_eventuallyEq hs)
private theorem fderiv_eq_zero_of_gaugeInvariant {a : ℝ} {N : ℕ}
    {e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k}
    {δ : ℝ} (hev : GaugeInvariantNear a e δ) (hOr : OrientationDichotomy L n k) {f : (Fin N → ℝ) → ℝ}
    (hfe : f = fun w => tripleFreeEnergy a (e w)) (hd : DifferentiableAt ℝ f 0) :
    fderiv ℝ f 0 = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hs := congrArg (fun y => fderiv ℝ f 0 (e.symm y)) (sum_conjTriple_quaternionUnits hOr (e x))
  simp only [map_add, map_zero, fderiv_conjTriple_quaternionUnit hev hOr hfe hd,
    LinearEquiv.symm_apply_apply] at hs
  simp only [ContinuousLinearMap.zero_apply]
  linarith
private theorem hessian_diag_add_vertexCoboundary [Finite (Edge L n k 0)] [Finite (Vertex L n k 0)]
    {a : ℝ} {N : ℕ}
    {e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k} {δ : ℝ} (hδ : 0 < δ) (hev : GaugeInvariantNear a e δ)
    (hOr : OrientationDichotomy L n k)
    (hcur : ∀ (γ : ℝ → LevelTriple L n k) (v : LevelTriple L n k), TripleCurveAt γ v →
      HasDerivAt (fun r => e.symm (γ r)) (e.symm v) 0)
    (hE : ComplexMatrix2.ExpLogEstimates) (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {f : (Fin N → ℝ) → ℝ} (hfe : f = fun w => tripleFreeEnergy a (e w)) (hC : ContDiffAt ℝ 2 f 0)
    (hD0 : fderiv ℝ f 0 = 0) {l : Vertex L n k 0 → ComplexMatrix2}
    (hlm : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (A : edgeFormSpace L n k 0) (hA : (A : Edge L n k 0 → ComplexMatrix2) = vertexCoboundary l)
    (τ : LevelTriple L n k) :
    fderiv ℝ (fderiv ℝ f) 0 (e.symm (τ + backgroundOnlyTriple A)) (e.symm (τ + backgroundOnlyTriple A)) =
      fderiv ℝ (fderiv ℝ f) 0 (e.symm τ) (e.symm τ) := by
  have hc1 := hcur _ _ (tripleCurveAt_gaugeOrbitCurve hOr hE hI hlm A hA τ)
  have hc2 : HasDerivAt (fun r : ℝ => r • e.symm τ) (e.symm τ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (e.symm τ)
  refine hessian_diag_eq_of_curves hC hD0 (by simp [gaugeOrbitCurve_zero]) (by simp) hc1 hc2 ?_
  have hs := eventually_tripleFreeEnergy_eq hev τ (γ := gaugeOrbitCurve l τ)
    (u := gaugePath l) (fun r x => gaugePath_mem hI hlm r x)
    ((eventually_gaugePath_near_one l hδ).mono fun r h => Or.inl h)
    (eventually_expMove_gaugeOrbitCurve hOr hE hI hlm τ)
    (fun r => isConjugatedCurrent_conjLevelForms hOr (gaugePath_mem hI hlm r) _)
    (fun r => conjForm_coe (hOr k le_rfl) (fun _ => gaugePath_mem hI hlm r _) _)
  filter_upwards [hs] with r hr
  simp only [hfe, LinearEquiv.apply_symm_apply, map_smul]
  exact hr
private theorem hessianOfFreeEnergy_eq_coordinates {a : ℝ} {N : ℕ}
    {e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k}
    {f : (Fin N → ℝ) → ℝ} (hfe : f = fun w => tripleFreeEnergy a (e w)) (hC : ContDiffAt ℝ 2 f 0)
    (τ τ' : LevelTriple L n k) :
    hessianOfFreeEnergy a τ τ' = fderiv ℝ (fderiv ℝ f) 0 (e.symm τ) (e.symm τ') := by
  rw [← mixedDeriv_eq_hessian f hC]
  unfold hessianOfFreeEnergy
  simp only [hfe, map_add, map_smul, LinearEquiv.apply_symm_apply]
private theorem hessian_mixed_eq_zero_of_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ}
    (hC : ContDiffAt ℝ 2 f 0) {g x : E}
    (k1 : fderiv ℝ (fderiv ℝ f) 0 (x + g) (x + g) = fderiv ℝ (fderiv ℝ f) 0 x x)
    (k2 : fderiv ℝ (fderiv ℝ f) 0 g g = 0) : fderiv ℝ (fderiv ℝ f) 0 g x = 0 := by
  have hsym : ∀ x y, fderiv ℝ (fderiv ℝ f) 0 x y = fderiv ℝ (fderiv ℝ f) 0 y x :=
    (hC.isSymmSndFDerivAt (by simp)).eq
  simp only [map_add, ContinuousLinearMap.add_apply] at k1
  have := hsym x g
  linarith
end Triples
theorem gaugeDirectionsAreFlat_holds (hF : ChainFreeEnergyAnalytic.Claim) (hc : PauliCoordsOrthonormal)
    (hf : BondSetFields.ProductStructureHolds)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy)
    (hE : ComplexMatrix2.ExpLogEstimates) (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    GaugeDirectionsAreFlat := by
  intro a ha L hLs k n hk hn
  have hOr : OrientationDichotomy L n k := fun j hj b => hO L n k hLs hn (by omega) j hj b
  have hb0 : Finite (Edge L n k 0) :=
    Set.finite_univ_iff.1 ((hf L hLs k 0 (Nat.zero_le _)).1 n hn).2.1
  have hs0 : Finite (Vertex L n k 0) :=
    Finite.of_injective (fun x => PeriodicLattice.Bond.forwardFrom x (0 : Fin 4))
      fun x y h => congrArg PeriodicLattice.Bond.source h
  obtain ⟨N, e, hcur⟩ := exists_triple_coordinates (k := k) hc hf hLs hn
  obtain ⟨hA, δ, hδ, hev⟩ := (hF a ha L hLs k n hk hn).1 N e
  obtain ⟨f, hfe⟩ : ∃ f : (Fin N → ℝ) → ℝ, f = fun w => tripleFreeEnergy a (e w) := ⟨_, rfl⟩
  have hC : ContDiffAt ℝ 2 f 0 := hfe ▸ hA.contDiffAt
  have hd : DifferentiableAt ℝ f 0 := hC.differentiableAt (by simp)
  have hD0 := fderiv_eq_zero_of_gaugeInvariant hev hOr hfe hd
  refine ⟨fun τ => ?_, fun l A hA' τ => ?_⟩
  · rw [(hasDerivAt_tripleFreeEnergy_line hfe hd τ).deriv, hD0]
    rfl
  · have hlm : ∀ x, (l : Vertex L n k 0 → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
      fun x => (Submodule.mem_pi.1 l.2) x (Set.mem_univ x)
    have k2 := hessian_diag_add_vertexCoboundary hδ hev hOr hcur hE hI hfe hC hD0 hlm A hA' 0
    rw [zero_add] at k2
    simp only [map_zero] at k2
    rw [hessianOfFreeEnergy_eq_coordinates hfe hC]
    exact hessian_mixed_eq_zero_of_diag hC
      (by simpa only [map_add] using
        hessian_diag_add_vertexCoboundary hδ hev hOr hcur hE hI hfe hC hD0 hlm A hA' τ) k2
end YangMills.Construction.RunningCouplingSlope.GaugeInvariance
end
