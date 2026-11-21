import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurationsProof
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscsProof
import YangMills.Construction.Towers.FirstDifferentialInTheExponentialChartVanishes
import YangMills.Construction.Towers.RepresentationOfTheLogarithmOfTheTotalNormaliser
import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalAndItsComplexExtension
import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalOnGaugeDirections
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.HessianOnGaugeDirections
open Matrices Tower
def expRay (X : ComplexMatrix2) (r : ℝ) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (((r : ℂ) * Complex.I) • X)
theorem expRay_zero (X : ComplexMatrix2) : expRay X 0 = 1 := by
  simp [expRay, ComplexMatrix2.matExp]
theorem expRay_inv (X : ComplexMatrix2) (r : ℝ) : (expRay X r)⁻¹ = expRay (-X) r := by
  simp only [expRay, ComplexMatrix2.matExp, smul_neg]
  exact (Matrix.exp_neg _).symm
theorem hasDerivAt_expRay (X : ComplexMatrix2) : HasDerivAt (expRay X) (Complex.I • X) 0 := by
  have h : HasDerivAt (fun z : ℂ => NormedSpace.exp (z • (Complex.I • X)))
      (NormedSpace.exp ((0 : ℂ) • (Complex.I • X)) * (Complex.I • X)) ((0 : ℝ) : ℂ) := by
    simpa using hasDerivAt_exp_smul_const (Complex.I • X) (0 : ℂ)
  have h2 := h.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
  have e : (fun z : ℂ => NormedSpace.exp (z • (Complex.I • X))) ∘ Complex.ofReal = expRay X := by
    funext r
    simp [expRay, ComplexMatrix2.matExp, smul_smul]
  rw [e] at h2
  have e2 : Complex.ofRealCLM 1 • (NormedSpace.exp ((0 : ℂ) • (Complex.I • X)) * (Complex.I • X)) =
      Complex.I • X := by
    simp
  exact h2.congr_deriv e2
theorem real_smul_eq_ofReal_smul (r : ℝ) (X : ComplexMatrix2) : r • X = (r : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem expRay_mem_specialUnitary (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) (r : ℝ) :
    expRay X r ∈ ComplexMatrix2.specialUnitary := by
  have h := (hI.1 (r • X) (ComplexMatrix2.hermitianTraceless.smul_mem r hX)).2.2.2
  have e : Complex.I • (r • X) = ((r : ℂ) * Complex.I) • X := by
    rw [real_smul_eq_ofReal_smul, smul_smul, mul_comm]
  rwa [e] at h
def tracelessProjection : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2.traceless :=
  (LinearMap.id - (LinearMap.toSpanSingleton ℂ ComplexMatrix2 (1 : ComplexMatrix2)) ∘ₗ
      ((1 / 2 : ℂ) • Matrix.traceLinearMap (Fin 2) ℂ ℂ)).codRestrict ComplexMatrix2.traceless (by
    intro X
    show Matrix.trace _ = 0
    simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    ring)
def pauliReCLM (c : Fin 3) : ComplexMatrix2 →L[ℝ] ℝ :=
  Complex.reCLM ∘L
    (LinearMap.toContinuousLinearMap
      ((LinearMap.proj c : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        (OneLoop.pauliCoordinateEquiv.toLinearMap ∘ₗ tracelessProjection))).restrictScalars ℝ
theorem re_pauliCoeff_eq (c : Fin 3) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    (pauliCoeff c X).re = pauliReCLM c X := by
  have h : X ∈ ComplexMatrix2.traceless := hX.2
  have e : tracelessProjection X = ⟨X, h⟩ := by
    apply Subtype.ext
    have t : Matrix.trace X = 0 := h
    simp [tracelessProjection, t]
  simp [pauliReCLM, pauliCoeff, h, e]
theorem hasDerivAt_re_pauliCoeff (c : Fin 3) {X Y : ℝ → ComplexMatrix2} {v : ComplexMatrix2}
    (hY : HasDerivAt Y v 0)
    (hXY : ∀ᶠ r in 𝓝 (0 : ℝ), X r = Y r ∧ Y r ∈ ComplexMatrix2.hermitianTraceless)
    (hv : v ∈ ComplexMatrix2.hermitianTraceless) :
    HasDerivAt (fun r => (pauliCoeff c (X r)).re) (pauliCoeff c v).re 0 := by
  rw [re_pauliCoeff_eq c hv]
  refine ((pauliReCLM c).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hY).congr_of_eventuallyEq ?_
  filter_upwards [hXY] with r hr
  simp only [Function.comp, hr.1, re_pauliCoeff_eq c hr.2]
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
theorem hasFDerivAt_logSeries_one (hE : ComplexMatrix2.ExpLogEstimates) :
    HasFDerivAt ComplexMatrix2.logSeries (ContinuousLinearMap.id ℝ ComplexMatrix2) 1 := by
  refine HasFDerivAt.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := min (1 / 2) (c / 2) with hε
  have ε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have ε1 : ε ≤ 1 / 2 := min_le_left _ _
  have ε2 : ε ≤ c / 2 := min_le_right _ _
  have hb : ∀ᶠ A : ComplexMatrix2 in 𝓝 1, ‖A - 1‖ < ε := by
    have := Metric.ball_mem_nhds (1 : ComplexMatrix2) ε0
    filter_upwards [this] with A hA
    rwa [Metric.mem_ball, dist_eq_norm] at hA
  filter_upwards [hb] with A hA
  have h := (hE.2.2.2.2.2.2.2.2.1 ε A 1 ε0.le (by linarith) hA.le (by simp [ε0.le])).2.2.1
  rw [logSeries_one] at h
  simp only [logSeries_one, ContinuousLinearMap.id_apply]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [div_le_iff₀ (by linarith)]
  nlinarith
theorem hasDerivAt_logSeries_comp (hE : ComplexMatrix2.ExpLogEstimates) {f : ℝ → ComplexMatrix2}
    {v : ComplexMatrix2} (hf : HasDerivAt f v 0) (h0 : f 0 = 1) :
    HasDerivAt (fun r => ComplexMatrix2.logSeries (f r)) v 0 := by
  have h : HasFDerivAt ComplexMatrix2.logSeries (ContinuousLinearMap.id ℝ ComplexMatrix2) (f 0) := by
    rw [h0]
    exact hasFDerivAt_logSeries_one hE
  exact h.comp_hasDerivAt (0 : ℝ) hf
theorem logSeries_of_specialUnitary (hE : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.specialUnitary) (h1 : ‖A - 1‖ < 1) :
    ∃ Y ∈ ComplexMatrix2.hermitianTraceless, ComplexMatrix2.logSeries A = Complex.I • Y ∧
      ComplexMatrix2.matExp (Complex.I • Y) = A := by
  have hA' := Matrix.mem_specialUnitaryGroup_iff.1 hA
  obtain ⟨H, -, hlog, -, hexp, -, hdet⟩ := hE.2.2.2.2.2.2.2.1 A hA'.1 h1
  exact ⟨H, (hdet hA'.2).2.1, hlog, hexp⟩
theorem logSeries_inv (hE : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (h1 : ‖A - 1‖ < 1 / 2) :
    ComplexMatrix2.logSeries A⁻¹ = -ComplexMatrix2.logSeries A := by
  have hE4 := hE.2.2.2.1 (A - 1) (by linarith)
  have e : 1 + (A - 1) = A := by abel
  rw [e] at hE4
  have hs : ‖ComplexMatrix2.logSeries A‖ < Real.log 2 := by
    have h2 : -Real.log (1 - ‖A - 1‖) < Real.log 2 := by
      have : Real.log (1 / 2) < Real.log (1 - ‖A - 1‖) :=
        Real.log_lt_log (by norm_num) (by linarith)
      rw [one_div, Real.log_inv] at this
      linarith
    exact lt_of_le_of_lt hE4.1 h2
  have h3 := (hE.2.2.2.2.1 (-ComplexMatrix2.logSeries A) (by simpa using hs)).2
  have h4 : ComplexMatrix2.matExp (-ComplexMatrix2.logSeries A) = A⁻¹ := by
    have := Matrix.exp_neg (ComplexMatrix2.logSeries A)
    rw [show NormedSpace.exp (ComplexMatrix2.logSeries A) = A from hE4.2.2.2.2] at this
    exact this
  rwa [h4] at h3
section Lattice
variable {L n k j : ℕ}
def toEdgeForm (B : Edge L n k j → ComplexMatrix2) : edgeFormSpace L n k j :=
  open Classical in if h : B ∈ edgeFormSpace L n k j then ⟨B, h⟩ else 0
theorem coe_toEdgeForm_of_mem {B : Edge L n k j → ComplexMatrix2} (h : B ∈ edgeFormSpace L n k j) :
    (toEdgeForm B : Edge L n k j → ComplexMatrix2) = B := by
  simp [toEdgeForm, h]
theorem toEdgeForm_zero : toEdgeForm (0 : Edge L n k j → ComplexMatrix2) = 0 := by
  apply Subtype.ext
  rw [coe_toEdgeForm_of_mem (zero_mem _)]
  rfl
theorem opposite_isPositivelyOriented_of_not (b : Edge L n k j) (h : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem edgeForm_apply_mem (B : edgeFormSpace L n k j) (b : Edge L n k j) :
    (B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := by
  have hB : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
      (B : Edge L n k j → ComplexMatrix2) := B.2
  by_cases h : b.IsPositivelyOriented
  · exact hB.1 b h
  · have h1 := hB.1 _ (opposite_isPositivelyOriented_of_not b h)
    have h2 := hB.2 b
    have h3 : -(B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := by
      rw [← h2]
      exact h1
    simpa using ComplexMatrix2.hermitianTraceless.neg_mem h3
theorem finite_edge [Finite (PositiveEdge L n k j)] : Finite (Edge L n k j) := by apply _root_.YangMills.Construction.Tower.IdentityChart.finite_edge <;> assumption
def gaugeRay (l : Vertex L n k j → ComplexMatrix2) (r : ℝ) : Vertex L n k j → ComplexMatrix2 :=
  fun x => expRay (-(l x)) r
def fieldRay (B : Edge L n k j → ComplexMatrix2) (r : ℝ) : Edge L n k j → ComplexMatrix2 :=
  fun b => expRay (B b) r
def transformedRay (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)
    (r : ℝ) : Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.gaugeTransform (gaugeRay l r) (fieldRay B r)
def transformedRayLog (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)
    (r : ℝ) : Edge L n k j → ComplexMatrix2 :=
  fun b => Complex.I⁻¹ • ComplexMatrix2.logSeries (transformedRay l B r b)
theorem expGaugeField_smul (B : Edge L n k j → ComplexMatrix2) (r : ℝ) :
    PeriodicLattice.expGaugeField (r • B) = fieldRay B r := by
  funext b
  simp only [PeriodicLattice.expGaugeField, fieldRay, expRay, Pi.smul_apply]
  rw [real_smul_eq_ofReal_smul, smul_smul, mul_comm]
theorem gaugeRay_mem (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {l : Vertex L n k j → ComplexMatrix2} (hl : l ∈ vertexFunctionSpace L n k j) (r : ℝ) :
    gaugeRay l r ∈ gaugeGroupAt L n k j := by
  intro x
  exact expRay_mem_specialUnitary hI
    (ComplexMatrix2.hermitianTraceless.neg_mem ((Submodule.mem_pi.1 hl) x (Set.mem_univ x))) r
theorem fieldRay_mem (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    (B : edgeFormSpace L n k j) (r : ℝ) :
    fieldRay (B : Edge L n k j → ComplexMatrix2) r ∈ fieldSpace L n k j := by
  have hB : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
      (B : Edge L n k j → ComplexMatrix2) := B.2
  refine ⟨fun b _ => expRay_mem_specialUnitary hI (edgeForm_apply_mem B b) r, fun b _ => ?_⟩
  show expRay (_) r = (expRay (_) r)⁻¹
  rw [expRay_inv, hB.2 b]
theorem tendsto_gaugeRay (l : Vertex L n k j → ComplexMatrix2) :
    Tendsto (gaugeRay l) (𝓝 0) (𝓝 fun _ => (1 : ComplexMatrix2)) := by
  refine tendsto_pi_nhds.2 fun x => ?_
  have h := (hasDerivAt_expRay (-(l x))).continuousAt.tendsto
  rwa [expRay_zero] at h
theorem tendsto_fieldRay (B : Edge L n k j → ComplexMatrix2) :
    Tendsto (fieldRay B) (𝓝 0) (𝓝 fun _ => (1 : ComplexMatrix2)) := by
  refine tendsto_pi_nhds.2 fun b => ?_
  have h := (hasDerivAt_expRay (B b)).continuousAt.tendsto
  rwa [expRay_zero] at h
theorem transformedRay_apply (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)
    (r : ℝ) (b : Edge L n k j) :
    transformedRay l B r b = expRay (-(l b.source)) r * expRay (B b) r * expRay (l b.target) r := by
  simp [transformedRay, PeriodicLattice.gaugeTransform, gaugeRay, fieldRay, expRay_inv]
theorem transformedRay_zero (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)
    (b : Edge L n k j) : transformedRay l B 0 b = 1 := by
  simp [transformedRay_apply, expRay_zero]
theorem hasDerivAt_transformedRay (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    HasDerivAt (fun r => transformedRay l B r b) (Complex.I • (B b + vertexCoboundary l b)) 0 := by
  have h := ((hasDerivAt_expRay (-(l b.source))).mul (hasDerivAt_expRay (B b))).mul
    (hasDerivAt_expRay (l b.target))
  have e : (fun r => transformedRay l B r b) =
      (expRay (-(l b.source)) * expRay (B b)) * expRay (l b.target) := by
    funext r
    simp [transformedRay_apply]
  rw [e]
  have e2 : (Complex.I • -(l b.source) * expRay (B b) 0 +
        expRay (-(l b.source)) 0 * (Complex.I • B b)) * expRay (l b.target) 0 +
      (expRay (-(l b.source)) * expRay (B b)) 0 * (Complex.I • l b.target) =
      Complex.I • (B b + vertexCoboundary l b) := by
    simp only [expRay_zero, Pi.mul_apply, vertexCoboundary, mul_one, one_mul, smul_add, smul_sub,
      smul_neg]
    abel
  exact h.congr_deriv e2
theorem hasDerivAt_transformedRayLog (hE : ComplexMatrix2.ExpLogEstimates)
    (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    HasDerivAt (fun r => transformedRayLog l B r b) (B b + vertexCoboundary l b) 0 := by
  have h := (hasDerivAt_logSeries_comp hE (hasDerivAt_transformedRay l B b)
    (transformedRay_zero l B b)).const_smul (Complex.I⁻¹)
  have e : Complex.I⁻¹ • Complex.I • (B b + vertexCoboundary l b) = B b + vertexCoboundary l b := by
    rw [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  exact h.congr_deriv e
theorem eventually_transformedRay_near_one [Finite (Edge L n k j)]
    (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ∀ b, ‖transformedRay l B r b - 1‖ < 1 / 2 := by
  refine Filter.eventually_all.2 fun b => ?_
  have h := (hasDerivAt_transformedRay l B b).continuousAt.tendsto
  rw [transformedRay_zero] at h
  filter_upwards [Metric.tendsto_nhds.1 h (1 / 2) (by norm_num)] with r hr
  rwa [dist_eq_norm] at hr
theorem transformedRay_mem (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    {l : Vertex L n k j → ComplexMatrix2} (hl : l ∈ vertexFunctionSpace L n k j)
    (B : edgeFormSpace L n k j) (r : ℝ) (b : Edge L n k j) :
    transformedRay l (B : Edge L n k j → ComplexMatrix2) r b ∈ ComplexMatrix2.specialUnitary := by
  have h : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless :=
    fun x => (Submodule.mem_pi.1 hl) x (Set.mem_univ x)
  rw [transformedRay_apply]
  exact mul_mem (mul_mem (expRay_mem_specialUnitary hI (ComplexMatrix2.hermitianTraceless.neg_mem (h _)) r)
    (expRay_mem_specialUnitary hI (edgeForm_apply_mem B b) r)) (expRay_mem_specialUnitary hI (h _) r)
theorem transformedRay_opposite (l : Vertex L n k j → ComplexMatrix2) (B : edgeFormSpace L n k j)
    (r : ℝ) (b : Edge L n k j) :
    transformedRay l (B : Edge L n k j → ComplexMatrix2) r b.opposite =
      (transformedRay l (B : Edge L n k j → ComplexMatrix2) r b)⁻¹ := by
  have hB : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
      (B : Edge L n k j → ComplexMatrix2) := B.2
  have t : b.opposite.source = b.target := rfl
  have u : b.opposite.target = b.source := rfl
  rw [transformedRay_apply, transformedRay_apply, t, u, hB.2 b]
  simp only [Matrix.mul_inv_rev, expRay_inv, neg_neg, mul_assoc]
theorem transformedRayLog_mem (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) {l : Vertex L n k j → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n k j) (B : edgeFormSpace L n k j) {r : ℝ}
    (hs : ∀ b, ‖transformedRay l (B : Edge L n k j → ComplexMatrix2) r b - 1‖ < 1 / 2) :
    transformedRayLog l (B : Edge L n k j → ComplexMatrix2) r ∈ edgeFormSpace L n k j := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · obtain ⟨Y, hY, h1, -⟩ := logSeries_of_specialUnitary hE (transformedRay_mem hI hl B r b)
      ((hs b).trans (by norm_num))
    show Complex.I⁻¹ • ComplexMatrix2.logSeries _ ∈ ComplexMatrix2.hermitianTraceless
    rw [h1, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    exact hY
  · show Complex.I⁻¹ • ComplexMatrix2.logSeries _ = -(Complex.I⁻¹ • ComplexMatrix2.logSeries _)
    rw [transformedRay_opposite, logSeries_inv hE (hs b), smul_neg]
theorem expGaugeField_transformedRayLog (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) {l : Vertex L n k j → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n k j) (B : edgeFormSpace L n k j) {r : ℝ}
    (hs : ∀ b, ‖transformedRay l (B : Edge L n k j → ComplexMatrix2) r b - 1‖ < 1 / 2) :
    PeriodicLattice.expGaugeField (transformedRayLog l (B : Edge L n k j → ComplexMatrix2) r) =
      transformedRay l (B : Edge L n k j → ComplexMatrix2) r := by
  funext b
  obtain ⟨Y, -, h1, h2⟩ := logSeries_of_specialUnitary hE (transformedRay_mem hI hl B r b)
    ((hs b).trans (by norm_num))
  show ComplexMatrix2.matExp (Complex.I • Complex.I⁻¹ • ComplexMatrix2.logSeries _) = _
  rw [h1, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, h2]
theorem hasDerivAt_conjugateBy_expRay (X Y : ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => ComplexMatrix2.conjugateBy (expRay (-X) r) (r • Y)) Y 0 := by
  have hs : HasDerivAt (fun r : ℝ => (r : ℂ) • Y) Y 0 := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).smul_const Y
    have e : Complex.ofRealCLM 1 • Y = Y := by simp
    exact h.congr_deriv e
  have h := ((hasDerivAt_expRay (-X)).mul hs).mul (hasDerivAt_expRay X)
  have e : (fun r : ℝ => ComplexMatrix2.conjugateBy (expRay (-X) r) (r • Y)) =
      (expRay (-X) * fun r : ℝ => (r : ℂ) • Y) * expRay X := by
    funext r
    simp only [ComplexMatrix2.conjugateBy, expRay_inv, neg_neg, Pi.mul_apply, real_smul_eq_ofReal_smul]
  rw [e]
  have e2 : (Complex.I • -X * (((0 : ℝ) : ℂ) • Y) + expRay (-X) 0 * Y) * expRay X 0 +
      (expRay (-X) * fun r : ℝ => (r : ℂ) • Y) 0 * (Complex.I • X) = Y := by
    simp [expRay_zero]
  exact h.congr_deriv e2
theorem adjointForm_zero (u : Vertex L n k j → ComplexMatrix2) :
    adjointForm u (0 : Edge L n k j → ComplexMatrix2) = 0 := by
  funext b
  simp [adjointForm, extendOddly, ComplexMatrix2.conjugateBy]
end Lattice
section Curve
variable {L n k : ℕ}
theorem exists_curve_gaugeShift (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
    (hinv : ∀ᶠ q in 𝓝[gaugeGroupAt L n k 0] (fun _ => (1 : ComplexMatrix2)) ×ˢ
      𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)),
        BackgroundFunctionalGaugeInvariant q.1 q.2)
    (hW : ∃ 𝒲 : Set (FieldTriple L n k), IsExpChartNhd 𝒲)
    {l : Vertex L n k 0 → ComplexMatrix2} (hl : l ∈ vertexFunctionSpace L n k 0)
    (g : edgeFormSpace L n k 0)
    (hg : (g : Edge L n k 0 → ComplexMatrix2) = vertexCoboundary l) (a : FieldTriple L n k) :
    ∃ γ : ℝ → FieldTriple L n k, IsCurveFromZero γ (a + (g, 0, 0)) ∧
      ∀ᶠ r in 𝓝 (0 : ℝ), expChartFunctional (γ r) = expChartFunctional (r • a) := by
  obtain ⟨𝒲, ho, h0, hform, -, -⟩ := hW
  have : Finite (Edge L n k 0) := finite_edge
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), BackgroundFunctionalGaugeInvariant (gaugeRay l r)
      (fieldRay (a.1 : Edge L n k 0 → ComplexMatrix2) r) := by
    have ht : Tendsto (fun r => (gaugeRay l r, fieldRay (a.1 : Edge L n k 0 → ComplexMatrix2) r))
        (𝓝 (0 : ℝ)) (𝓝[gaugeGroupAt L n k 0] (fun _ => (1 : ComplexMatrix2)) ×ˢ
          𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2))) :=
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_gaugeRay l, Eventually.of_forall (gaugeRay_mem hI hl)⟩).prodMk
        (tendsto_nhdsWithin_iff.2 ⟨tendsto_fieldRay _,
          Eventually.of_forall (fieldRay_mem hI a.1)⟩)
    exact ht.eventually hinv
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), r • a ∈ 𝒲 := by
    have ht : Tendsto (fun r : ℝ => r • a) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun r : ℝ => r • a := continuous_id.smul continuous_const
      simpa using hc.tendsto 0
    exact ht.eventually (ho.mem_nhds h0)
  have hsmall := eventually_transformedRay_near_one l (a.1 : Edge L n k 0 → ComplexMatrix2)
  have hall : ∀ᶠ r in 𝓝 (0 : ℝ), ∃ (J' : edgeFormSpace L n k 0) (μ' : edgeFormSpace L n k k),
      (J' : Edge L n k 0 → ComplexMatrix2) =
        adjointForm (gaugeRay l r) ((r • a).2.1 : edgeFormSpace L n k 0) ∧
      (μ' : Edge L n k k → ComplexMatrix2) =
        adjointForm (restrictVertexFunction k (gaugeRay l r)) ((r • a).2.2 : edgeFormSpace L n k k) ∧
      BackgroundFunctionalWellDefined
        (PeriodicLattice.gaugeTransform (gaugeRay l r)
          (fieldRay (a.1 : Edge L n k 0 → ComplexMatrix2) r))
        J' μ' ∧
      backgroundFunctional
        (PeriodicLattice.gaugeTransform (gaugeRay l r)
          (fieldRay (a.1 : Edge L n k 0 → ComplexMatrix2) r))
        J' μ' = expChartFunctional (r • a) := by
    filter_upwards [hev, hnear] with r h1 h2
    have hf : BackgroundFunctionalWellDefined (fieldRay (a.1 : Edge L n k 0 → ComplexMatrix2) r)
        (r • a).2.1 (r • a).2.2 := by
      have := hform _ h2
      rw [ExpChartFunctionalDefined] at this
      rwa [show (((r • a).1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
        r • (a.1 : Edge L n k 0 → ComplexMatrix2) from rfl, expGaugeField_smul] at this
    obtain ⟨J', μ', e1, e2, e3, e4⟩ := h1 _ _ hf
    refine ⟨J', μ', e1, e2, e3, ?_⟩
    rw [e4, expChartFunctional,
      show (((r • a).1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
        r • (a.1 : Edge L n k 0 → ComplexMatrix2) from rfl, expGaugeField_smul]
  refine ⟨fun r => (toEdgeForm (transformedRayLog l (a.1 : Edge L n k 0 → ComplexMatrix2) r),
    toEdgeForm (adjointForm (gaugeRay l r) ((r • a).2.1 : edgeFormSpace L n k 0)),
    toEdgeForm (adjointForm (restrictVertexFunction k (gaugeRay l r))
      ((r • a).2.2 : edgeFormSpace L n k k))),
    ⟨?_, ?_⟩, ?_⟩
  · have e1 : transformedRayLog l (a.1 : Edge L n k 0 → ComplexMatrix2) 0 = 0 := by
      funext b
      simp [transformedRayLog, transformedRay_zero, logSeries_one]
    have e2 : (((0 : ℝ) • a).2.1 : edgeFormSpace L n k 0) = 0 := by simp
    have e3 : (((0 : ℝ) • a).2.2 : edgeFormSpace L n k k) = 0 := by simp
    simp only [e1, e2, e3, ZeroMemClass.coe_zero, adjointForm_zero, toEdgeForm_zero]
    rfl
  · refine hasDerivAt_pi.2 fun i => ?_
    rcases i with ι | ι | ι
    · have hY : HasDerivAt (fun r => transformedRayLog l (a.1 : Edge L n k 0 → ComplexMatrix2) r ι.2.1)
          ((a.1 : Edge L n k 0 → ComplexMatrix2) ι.2.1 + (g : Edge L n k 0 → ComplexMatrix2) ι.2.1) 0 := by
        rw [hg]
        exact hasDerivAt_transformedRayLog hE l (a.1 : Edge L n k 0 → ComplexMatrix2) ι.2.1
      have hd := hasDerivAt_re_pauliCoeff ι.1 (X := fun r =>
        (toEdgeForm (transformedRayLog l (a.1 : Edge L n k 0 → ComplexMatrix2) r) :
          Edge L n k 0 → ComplexMatrix2) ι.2.1) hY ?_
        (ComplexMatrix2.hermitianTraceless.add_mem (edgeForm_apply_mem a.1 _) (edgeForm_apply_mem g _))
      · exact hd
      · filter_upwards [hsmall] with r hr
        have hm := transformedRayLog_mem hE hI hl a.1 hr
        exact ⟨by rw [coe_toEdgeForm_of_mem hm], edgeForm_apply_mem ⟨_, hm⟩ ι.2.1⟩
    · have hY := hasDerivAt_conjugateBy_expRay (l ι.2.1.source)
        ((a.2.1 : Edge L n k 0 → ComplexMatrix2) ι.2.1)
      have hd := hasDerivAt_re_pauliCoeff ι.1 (X := fun r =>
        (toEdgeForm (adjointForm (gaugeRay l r) ((r • a).2.1 : edgeFormSpace L n k 0)) :
          Edge L n k 0 → ComplexMatrix2) ι.2.1) hY ?_ (edgeForm_apply_mem a.2.1 _)
      · exact hd.congr_deriv (by simp [fieldTripleCoords, toPauliCoeffs, restrictToPositiveEdges])
      · filter_upwards [hall] with r hr
        obtain ⟨J', μ', e1, -, -, -⟩ := hr
        have hv : adjointForm (gaugeRay l r) ((r • a).2.1 : edgeFormSpace L n k 0) ι.2.1 =
            ComplexMatrix2.conjugateBy (expRay (-(l ι.2.1.source)) r)
              (r • (a.2.1 : Edge L n k 0 → ComplexMatrix2) ι.2.1) := by
          simp only [adjointForm, extendOddly, if_pos ι.2.2]
          rfl
        have hm : adjointForm (gaugeRay l r) ((r • a).2.1 : edgeFormSpace L n k 0) ∈
            edgeFormSpace L n k 0 :=
          e1 ▸ J'.2
        refine ⟨by rw [coe_toEdgeForm_of_mem hm, hv], ?_⟩
        rw [← hv, ← e1]
        exact edgeForm_apply_mem J' _
    · have hY := hasDerivAt_conjugateBy_expRay
        (l (PeriodicLattice.Site.toSublattice ι.2.1.source (PeriodicLattice.levelDepth k 0)))
        ((a.2.2 : Edge L n k k → ComplexMatrix2) ι.2.1)
      have hd := hasDerivAt_re_pauliCoeff ι.1 (X := fun r =>
        (toEdgeForm (adjointForm (restrictVertexFunction k (gaugeRay l r))
          ((r • a).2.2 : edgeFormSpace L n k k)) :
          Edge L n k k → ComplexMatrix2) ι.2.1) hY ?_ (edgeForm_apply_mem a.2.2 _)
      · exact hd.congr_deriv (by simp [fieldTripleCoords, toPauliCoeffs, restrictToPositiveEdges])
      · filter_upwards [hall] with r hr
        obtain ⟨J', μ', -, e1, -, -⟩ := hr
        have hv : adjointForm (restrictVertexFunction k (gaugeRay l r))
              ((r • a).2.2 : edgeFormSpace L n k k) ι.2.1 =
            ComplexMatrix2.conjugateBy (expRay (-(l (PeriodicLattice.Site.toSublattice ι.2.1.source
              (PeriodicLattice.levelDepth k 0)))) r)
              (r • (a.2.2 : Edge L n k k → ComplexMatrix2) ι.2.1) := by
          simp only [adjointForm, extendOddly, if_pos ι.2.2]
          rfl
        have hm : adjointForm (restrictVertexFunction k (gaugeRay l r))
            ((r • a).2.2 : edgeFormSpace L n k k) ∈ edgeFormSpace L n k k := e1 ▸ μ'.2
        refine ⟨by rw [coe_toEdgeForm_of_mem hm, hv], ?_⟩
        rw [← hv, ← e1]
        exact edgeForm_apply_mem μ' _
  · filter_upwards [hall, hsmall] with r hr hs
    obtain ⟨J', μ', e1, e2, -, e4⟩ := hr
    have hm := transformedRayLog_mem hE hI hl a.1 hs
    have c1 : toEdgeForm (adjointForm (gaugeRay l r) ((r • a).2.1 : edgeFormSpace L n k 0)) = J' := by
      apply Subtype.ext
      rw [coe_toEdgeForm_of_mem (e1 ▸ J'.2), e1]
    have c2 : toEdgeForm (adjointForm (restrictVertexFunction k (gaugeRay l r))
        ((r • a).2.2 : edgeFormSpace L n k k)) = μ' := by
      apply Subtype.ext
      rw [coe_toEdgeForm_of_mem (e2 ▸ μ'.2), e2]
    rw [← e4, expChartFunctional]
    simp only [c1, c2, coe_toEdgeForm_of_mem hm, expGaugeField_transformedRayLog hE hI hl a.1 hs]
    rfl
theorem eq_zero_of_sq_mul_isLittleO {c : ℝ}
    (h : (fun t : ℝ => t ^ 2 / 2 * c) =o[𝓝 0] fun t : ℝ => t ^ 2) : c = 0 := by
  have h1 := h.tendsto_div_nhds_zero.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have h2 : Tendsto (fun t : ℝ => t ^ 2 / 2 * c / t ^ 2) (𝓝[≠] 0) (𝓝 (c / 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have : t ≠ 0 := ht
    field_simp
  have := tendsto_nhds_unique h1 h2
  linarith
theorem expChartSecondDeriv_diag_eq_of_curves [Fintype (PositiveEdge L n k 0)]
    [Fintype (PositiveEdge L n k k)]
    (P : ExpChartFunctionalExpansion L n k)
    (hφ : ∀ x : FieldTriple L n k, expChartFirstDeriv x = 0)
    {γ γ' : ℝ → FieldTriple L n k} {v v' : FieldTriple L n k}
    (hc : IsCurveFromZero γ v) (hc' : IsCurveFromZero γ' v')
    (he : ∀ᶠ r in 𝓝 (0 : ℝ), expChartFunctional (γ r) = expChartFunctional (γ' r)) :
    expChartSecondDeriv v v = expChartSecondDeriv v' v' := by
  have d := (P.isLittleO γ v hc).sub (P.isLittleO γ' v' hc')
  have d' : (fun t : ℝ => t ^ 2 / 2 * (expChartSecondDeriv v' v' -
      expChartSecondDeriv v v)) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine d.congr' ?_ EventuallyEq.rfl
    filter_upwards [he] with r hr
    simp only [hφ, hr]
    ring
  have := eq_zero_of_sq_mul_isLittleO d'
  linarith
end Curve
theorem hessianVanishesOnGaugeDirections_holds (h₁ : ExpChartFirstDerivVanishes)
    (h₂ : HessianAndComplexExtensionHolds)
    (h₃ : LogNormaliserRepresentationHolds)
    (h₄ : ExpChartFunctionalClaim)
    (h₅ : ComplexMatrix2.ExpLogEstimates)
    (h₆ : ComplexMatrix2.UnitaryLogarithmProperties) :
    HessianVanishesOnGaugeDirections := by
  intro L n k hL hn hk l hl g hg ζ
  have R := h₃ L n k hL hn hk
  obtain ⟨f0, fk, -⟩ := R.analytic_near_identity
  have P : ExpChartFunctionalExpansion L n k := (h₄ L n k hL hn hk).2
  have hφ : ∀ x : FieldTriple L n k, expChartFirstDeriv x = 0 :=
    fun x => h₁ L n k hL hn hk x
  have S : HessianAndComplexExtension L n k := h₂ L n k hL hn hk
  rw [S.eq_expChartSecondDeriv]
  obtain ⟨β, hβ, hsym⟩ := P.symmetric
  have hg0 : ((0 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) = vertexCoboundary 0 := by
    funext b
    simp [vertexCoboundary]
  have key : ∀ a : FieldTriple L n k, β (a + (g, 0, 0)) (a + (g, 0, 0)) = β a a := by
    intro a
    obtain ⟨γ, hc, he⟩ := exists_curve_gaugeShift h₅ h₆ R.gauge_invariant.1 P.exists_nhd hl g hg a
    obtain ⟨γ', hc', he'⟩ :=
      exists_curve_gaugeShift h₅ h₆ R.gauge_invariant.1 P.exists_nhd (zero_mem _) 0 hg0 a
    have e : a + ((0 : edgeFormSpace L n k 0), (0 : edgeFormSpace L n k 0),
        (0 : edgeFormSpace L n k k)) = a := add_zero a
    rw [e] at hc'
    have := expChartSecondDeriv_diag_eq_of_curves P hφ hc hc' (by
      filter_upwards [he, he'] with r h1 h2
      rw [h1, h2])
    rwa [← hβ, ← hβ] at this
  have k1 := key ζ
  have k2 := key 0
  have e0 : (0 : FieldTriple L n k) + (g, 0, 0) = (g, 0, 0) := zero_add _
  rw [e0] at k2
  simp only [map_zero] at k2
  simp only [map_add, LinearMap.add_apply] at k1
  rw [← hβ]
  have := hsym ζ (g, 0, 0)
  linarith
end YangMills.Construction.Tower.HessianOnGaugeDirections
end
