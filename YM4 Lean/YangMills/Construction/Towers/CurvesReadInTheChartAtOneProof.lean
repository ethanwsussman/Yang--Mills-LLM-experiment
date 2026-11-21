import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfGProof
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurationsProof
import YangMills.Construction.Towers.CurvesReadInTheChartAtOne
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.PowerExpCharts YangMills.Construction.IdentityExpChart
open scoped Matrix.Norms.L2Operator Topology ContDiff
noncomputable section
namespace YangMills.Construction.Tower.IdentityChartCurves
def toMatrixCLM : ComplexMatrix2.LieElement →L[ℝ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := ComplexMatrix2.LieElement.toMatrix, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
theorem toMatrix_injective : Function.Injective ComplexMatrix2.LieElement.toMatrix :=
  fun _ _ h => Subtype.ext h
theorem toMatrix_mem (Y : ComplexMatrix2.LieElement) :
    Y.toMatrix ∈ ComplexMatrix2.hermitianTraceless := Y.2
def pauliCoeffs : ComplexMatrix2 →ₗ[ℝ] Fin 3 → ℝ where
  toFun A := ![(A 0 1).re, -(A 0 1).im, (A 0 0).re]
  map_add' A B := by
    ext a
    fin_cases a <;> simp [add_comm]
  map_smul' c A := by
    ext a
    fin_cases a <;> simp
def projLie : ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ∑ a, pauliCoeffs A a • pauliLie a
      map_add' := fun A B => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c A => by simp [mul_smul, Finset.smul_sum] }
theorem sum_pauliCoeffs_smul (Y : ComplexMatrix2.LieElement) :
    ∑ a, pauliCoeffs Y.toMatrix a • pauliLie a = Y := by
  obtain ⟨hH, hT⟩ := toMatrix_mem Y
  apply toMatrix_injective
  have h10 : Y.toMatrix 1 0 = (starRingEnd ℂ) (Y.toMatrix 0 1) := by
    have := congrFun (congrFun hH 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have h00 : (Y.toMatrix 0 0).im = 0 := by
    have := congrArg Complex.im (congrFun (congrFun hH 0) 0)
    simp [Matrix.conjTranspose_apply] at this
    linarith
  have h11 : Y.toMatrix 1 1 = -Y.toMatrix 0 0 := by
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] at hT
    linear_combination hT
  have e : (∑ a, pauliCoeffs Y.toMatrix a • pauliLie a).toMatrix =
      ∑ a, pauliCoeffs Y.toMatrix a • pauliFamily a := by
    simp only [Fin.sum_univ_three]
    rfl
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, pauliCoeffs, pauliFamily, OneLoop.pauliX,
      OneLoop.pauliY, OneLoop.pauliZ, h10, h11] <;>
    apply Complex.ext <;> simp [h00]
@[simp] theorem projLie_toMatrix (Y : ComplexMatrix2.LieElement) : projLie Y.toMatrix = Y :=
  sum_pauliCoeffs_smul Y
section Families
variable {σ : Type} [Fintype σ]
theorem oneFamily_mem : oneFamily σ ∈ specialUnitaryPower σ := fun _ => by
  simp [ComplexMatrix2.FactorKind.compactReal, oneFamily]
theorem exp_half_le_nineteen_tenths : Real.exp (1 / 2) ≤ 19 / 10 := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exp_half_le_nineteen_tenths <;> assumption
def toMatricesCLM : (σ → ComplexMatrix2.LieElement) →L[ℝ] σ → ComplexMatrix2 :=
  ContinuousLinearMap.pi fun s => toMatrixCLM.comp (ContinuousLinearMap.proj s)
@[simp] theorem toMatricesCLM_apply (y : σ → ComplexMatrix2.LieElement) :
    toMatricesCLM y = toMatrices y := rfl
theorem toMatrices_injective : Function.Injective (toMatrices (σ := σ)) := fun _ _ h =>
  funext fun s => toMatrix_injective (congrFun h s)
def projLieFamily : (σ → ComplexMatrix2) →L[ℝ] σ → ComplexMatrix2.LieElement :=
  ContinuousLinearMap.pi fun s => projLie.comp (ContinuousLinearMap.proj s)
@[simp] theorem projLieFamily_toMatrices (y : σ → ComplexMatrix2.LieElement) :
    projLieFamily (toMatrices y) = y := funext fun s => projLie_toMatrix (y s)
theorem contDiff_matExp : ContDiff ℝ ∞ (ComplexMatrix2.matExp) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
theorem contDiff_expFamily : ContDiff ℝ ∞ (expFamily (σ := σ)) := by
  refine contDiff_pi.2 fun s => ?_
  have h : ContDiff ℝ ∞ fun y : σ → ComplexMatrix2.LieElement => Complex.I • toMatrixCLM (y s) :=
    (toMatrixCLM.comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : σ => ComplexMatrix2.LieElement) s)).contDiff.const_smul Complex.I
  exact contDiff_matExp.comp h
theorem differentiable_expFamily : Differentiable ℝ (expFamily (σ := σ)) :=
  contDiff_expFamily.differentiable (by simp)
theorem mem_smallBall_of_mem_lieBall {y : σ → ComplexMatrix2.LieElement} {ε : ℝ}
    (h : y ∈ lieBall σ ε) : y ∈ smallBall σ ε := fun s =>
  lt_of_le_of_lt (le_ciSup (f := fun s => ComplexMatrix2.operatorNorm (toMatrices y s))
    (Set.finite_range _).bddAbove s) h
theorem isOpen_smallBall (ε : ℝ) : IsOpen (smallBall σ ε) := by apply _root_.YangMills.SharedProofs.p16540 <;> assumption
structure LogAtOne (σ : Type) [Fintype σ] : Prop where
  mem : ∀ y : σ → ComplexMatrix2.LieElement, expFamily y ∈ specialUnitaryPower σ
  mem_domain : ∀ y ∈ smallBall σ (1 / 2), expFamily y ∈ logDomain (oneFamily σ)
  log_exp : ∀ y ∈ smallBall σ (1 / 2), logChart (oneFamily σ) (expFamily y) = toMatrices y
  isOpen_domain : IsOpen (logDomain (oneFamily σ))
  contDiffOn_log : ContDiffOn ℝ ∞ (PowerExpCharts.logChart (oneFamily σ)) (logDomain (oneFamily σ))
theorem logAtOne (h : PowerCharts σ) : LogAtOne σ := by
  obtain ⟨-, h2, h3⟩ := h (oneFamily σ) oneFamily_mem
  have e : ∀ y : σ → ComplexMatrix2.LieElement, expChartI (oneFamily σ) y = expFamily y :=
    fun y => by
      rw [(h2 y).2.1]
      funext s
      simp [oneFamily, expFamily]
  obtain ⟨-, -, -, -, h5, h6, h7, h8, -⟩ := h3 (1 / 2) (by norm_num) exp_half_le_nineteen_tenths
  refine ⟨fun y => e y ▸ (h2 y).2.2, fun y hy => ?_, fun y hy => ?_, h5, h6⟩
  · exact h7 ⟨y, hy, e y⟩
  · rw [← e y, h8 y hy]
    rfl
def lieLog (X : σ → ComplexMatrix2) : σ → ComplexMatrix2.LieElement :=
  projLieFamily (logChart (oneFamily σ) X)
theorem lieLog_expFamily (hc : LogAtOne σ) {y : σ → ComplexMatrix2.LieElement}
    (hy : y ∈ smallBall σ (1 / 2)) : lieLog (expFamily y) = y := by
  rw [lieLog, hc.log_exp y hy, projLieFamily_toMatrices]
theorem contDiffOn_lieLog (hc : LogAtOne σ) :
    ContDiffOn ℝ ∞ (lieLog (σ := σ)) (logDomain (oneFamily σ)) := by
  exact show ContDiffOn ℝ ∞ (⇑(projLieFamily (σ := σ)) ∘ PowerExpCharts.logChart (oneFamily σ))
      (logDomain (oneFamily σ)) from
    (projLieFamily (σ := σ)).contDiff.comp_contDiffOn hc.contDiffOn_log
theorem differentiableAt_lieLog (hc : LogAtOne σ) {X : σ → ComplexMatrix2}
    (hX : X ∈ logDomain (oneFamily σ)) : DifferentiableAt ℝ (lieLog (σ := σ)) X :=
  ((contDiffOn_lieLog hc).contDiffAt (hc.isOpen_domain.mem_nhds hX)).differentiableAt (by simp)
theorem fderiv_expFamily_injective (hc : LogAtOne σ) {z : σ → ComplexMatrix2.LieElement}
    (hz : z ∈ smallBall σ (1 / 2)) : Function.Injective (fderiv ℝ (expFamily (σ := σ)) z) := by
  have hlog : HasFDerivAt (PowerExpCharts.logChart (oneFamily σ))
      (fderiv ℝ (PowerExpCharts.logChart (oneFamily σ)) (expFamily z)) (expFamily z) :=
    ((hc.contDiffOn_log.contDiffAt (hc.isOpen_domain.mem_nhds (hc.mem_domain z hz))).differentiableAt
      (by simp)).hasFDerivAt
  have hcomp := hlog.comp z (differentiable_expFamily z).hasFDerivAt
  have he : (PowerExpCharts.logChart (oneFamily σ) ∘ expFamily) =ᶠ[𝓝 z] toMatricesCLM := by
    filter_upwards [(isOpen_smallBall (1 / 2)).mem_nhds hz] with y hy
    exact hc.log_exp y hy
  have hm : HasFDerivAt (PowerExpCharts.logChart (oneFamily σ) ∘ expFamily) toMatricesCLM z :=
    (toMatricesCLM.hasFDerivAt).congr_of_eventuallyEq he
  have hu := hcomp.unique hm
  intro v w hvw
  apply toMatrices_injective
  have := congrArg (fun T => T v) hu
  have h2 := congrArg (fun T => T w) hu
  simp only [ContinuousLinearMap.comp_apply, toMatricesCLM_apply] at this h2
  rw [← this, ← h2, hvw]
end Families
section Tower
variable {L n k j : ℕ}
abbrev UniqueOrientation (L n k j : ℕ) : Prop :=
  ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem uniqueOrientation (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    UniqueOrientation L n k j := fun b =>
  PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by have := hL.2; omega)
    (by show -(n : ℤ) < (k : ℤ) - (j : ℤ); omega) b
instance instNonemptyPositiveEdge : Nonempty (PositiveEdge L n k j) :=
  ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos h
theorem extendOddly_of_not_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := if_neg h
theorem extendOddly_congr (hx : UniqueOrientation L n k j) {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b = g b) :
    extendOddly f = extendOddly g := by
  funext b
  rcases hx b with ⟨hb, -⟩ | ⟨hr, hb⟩
  · rw [extendOddly_of_pos f hb, extendOddly_of_pos g hb, h b hb]
  · rw [extendOddly_of_not_pos f hb, extendOddly_of_not_pos g hb, h _ hr]
theorem identityChartPoint_of_pos (y : PositiveEdge L n k j → ComplexMatrix2.LieElement)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    identityChartPoint y b = expFamily y ⟨b, h⟩ := by apply _root_.YangMills.Construction.Tower.IdentityChart.identityChartPoint_of_positive <;> assumption
theorem restrict_identityChartPoint (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    restrictToPositiveEdges (identityChartPoint y) = expFamily y := by apply _root_.YangMills.Construction.Tower.IdentityChart.restrictToPositiveEdges_identityChartPoint <;> assumption
def extendByZero : (PositiveEdge L n k j → ComplexMatrix2) →ₗ[ℝ] Edge L n k j → ComplexMatrix2 where
  toFun w := extendOddly fun c => open Classical in
    if h : c.IsPositivelyOriented then w ⟨c, h⟩ else 0
  map_add' w w' := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · simp [extendOddly_of_pos _ hb, hb]
    · by_cases hr : b.opposite.IsPositivelyOriented
      · simp [extendOddly_of_not_pos _ hb, hr, add_comm]
      · simp [extendOddly_of_not_pos _ hb, hr]
  map_smul' c w := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · simp [extendOddly_of_pos _ hb, hb]
    · by_cases hr : b.opposite.IsPositivelyOriented
      · simp [extendOddly_of_not_pos _ hb, hr]
      · simp [extendOddly_of_not_pos _ hb, hr]
theorem extendByZero_apply (w : PositiveEdge L n k j → ComplexMatrix2) :
    extendByZero w = extendOddly fun c => open Classical in
      if h : c.IsPositivelyOriented then w ⟨c, h⟩ else 0 := rfl
theorem extendByZero_of_pos (w : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : extendByZero w b = w ⟨b, h⟩ := by
  rw [extendByZero_apply, extendOddly_of_pos _ h, dif_pos h]
def leftTangent [Fintype (PositiveEdge L n k j)]
    (y₀ : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    (PositiveEdge L n k j → ComplexMatrix2.LieElement) →ₗ[ℝ] PositiveEdge L n k j → ComplexMatrix2 where
  toFun h := fun b => Complex.I⁻¹ • (fderiv ℝ expFamily y₀ h b * (expFamily y₀ b)⁻¹)
  map_add' h h' := by
    funext b
    simp [map_add, add_mul, smul_add]
  map_smul' c h := by
    funext b
    simp only [map_smul, Pi.smul_apply, smul_mul_assoc, RingHom.id_apply]
    exact smul_comm _ _ _
theorem mul_inv_mul_of_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (X : ComplexMatrix2) : X * g⁻¹ * g = X := by
  have h : g.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
  rw [mul_assoc, Matrix.nonsing_inv_mul g (by rw [h]; exact isUnit_one), mul_one]
theorem leftTangent_injective [Fintype (PositiveEdge L n k j)]
    (hc : LogAtOne (PositiveEdge L n k j)) {y₀ : PositiveEdge L n k j → ComplexMatrix2.LieElement}
    (hz : y₀ ∈ smallBall (PositiveEdge L n k j) (1 / 2)) :
    Function.Injective (extendByZero ∘ₗ leftTangent y₀) := by
  intro h h' e
  apply fderiv_expFamily_injective hc hz
  funext b
  have e1 := congrFun e b.1
  simp only [LinearMap.comp_apply, extendByZero_of_pos _ b.2] at e1
  have e2 : fderiv ℝ expFamily y₀ h b * (expFamily y₀ b)⁻¹ =
      fderiv ℝ expFamily y₀ h' b * (expFamily y₀ b)⁻¹ :=
    smul_right_injective ComplexMatrix2 (inv_ne_zero Complex.I_ne_zero) e1
  have hg : expFamily y₀ b ∈ PeriodicLattice.compactGaugeGroup := hc.mem y₀ b
  rw [← mul_inv_mul_of_mem hg (fderiv ℝ expFamily y₀ h b), e2, mul_inv_mul_of_mem hg]
theorem log_of_mem_image [Fintype (PositiveEdge L n k j)]
    (hc : LogAtOne (PositiveEdge L n k j))
    (hpt : ∀ y ∈ lieBall (PositiveEdge L n k j) (1 / 2),
      identityChartLog (identityChartPoint y) = y)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ identityChartPoint '' lieBall (PositiveEdge L n k j) (1 / 2)) :
    restrictToPositiveEdges V ∈ logDomain (oneFamily (PositiveEdge L n k j)) ∧
      identityChartLog V = lieLog (restrictToPositiveEdges V) ∧
      expFamily (identityChartLog V) = restrictToPositiveEdges V := by
  obtain ⟨y, hy, rfl⟩ := hV
  rw [restrict_identityChartPoint, hpt y hy]
  exact ⟨hc.mem_domain y (mem_smallBall_of_mem_lieBall hy),
    (lieLog_expFamily hc (mem_smallBall_of_mem_lieBall hy)).symm, rfl⟩
theorem differentiable_log_curve [Fintype (PositiveEdge L n k j)]
    (hc : LogAtOne (PositiveEdge L n k j))
    (hpt : ∀ y ∈ lieBall (PositiveEdge L n k j) (1 / 2),
      identityChartLog (identityChartPoint y) = y)
    {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ)
    (hm : MapsTo γ I (identityChartPoint '' lieBall (PositiveEdge L n k j) (1 / 2))) :
    DifferentiableOn ℝ (fun t => identityChartLog (γ t)) I ∧
      ((∀ b : Edge L n k j, b.IsPositivelyOriented → DifferentiableOn ℝ (deriv fun t => γ t b) I) →
        DifferentiableOn ℝ (deriv fun t => identityChartLog (γ t)) I) := by
  obtain ⟨⟨hIo, -, -⟩, -, hd⟩ := hγ
  have hw : DifferentiableOn ℝ (fun t => restrictToPositiveEdges (γ t)) I :=
    differentiableOn_pi.2 fun b => hd b.1 b.2
  have hlog : ∀ t ∈ I, identityChartLog (γ t) = lieLog (restrictToPositiveEdges (γ t)) :=
    fun t ht => (log_of_mem_image hc hpt (hm ht)).2.1
  have hdom : ∀ t ∈ I, restrictToPositiveEdges (γ t) ∈
      logDomain (oneFamily (PositiveEdge L n k j)) :=
    fun t ht => (log_of_mem_image hc hpt (hm ht)).1
  refine ⟨fun t ht => ?_, fun hdd => ?_⟩
  · have h1 : DifferentiableWithinAt ℝ (lieLog ∘ fun s => restrictToPositiveEdges (γ s)) I t :=
      DifferentiableAt.comp_differentiableWithinAt (g := lieLog) t
        (differentiableAt_lieLog hc (hdom t ht)) (hw t ht)
    exact h1.congr hlog (hlog t ht)
  · have hw' : ∀ t ∈ I, HasDerivAt (fun s => restrictToPositiveEdges (γ s))
        (fun b => deriv (fun s => γ s b.1) t) t := fun t ht =>
      hasDerivAt_pi.2 fun b => ((hd b.1 b.2 t ht).differentiableAt
        (hIo.mem_nhds ht)).hasDerivAt
    have hder : ∀ t ∈ I, deriv (fun s => identityChartLog (γ s)) t =
        fderiv ℝ lieLog (restrictToPositiveEdges (γ t)) fun b => deriv (fun s => γ s b.1) t := by
      intro t ht
      have h1 := (differentiableAt_lieLog hc (hdom t ht)).hasFDerivAt.comp_hasDerivAt t (hw' t ht)
      refine (h1.congr_of_eventuallyEq ?_).deriv
      filter_upwards [hIo.mem_nhds ht] with s hs
      exact hlog s hs
    have hfd : DifferentiableOn ℝ (fderiv ℝ (lieLog (σ := PositiveEdge L n k j)))
        (logDomain (oneFamily (PositiveEdge L n k j))) :=
      ((contDiffOn_lieLog hc).fderiv_of_isOpen hc.isOpen_domain
        (m := 1) (by norm_cast)).differentiableOn (by simp)
    have hv : DifferentiableOn ℝ
        (fun t => (fun b : PositiveEdge L n k j => deriv (fun s => γ s b.1) t)) I :=
      differentiableOn_pi.2 fun b => hdd b.1 b.2
    have hf1 : DifferentiableOn ℝ
        (fderiv ℝ (lieLog (σ := PositiveEdge L n k j)) ∘ fun t => restrictToPositiveEdges (γ t)) I :=
      DifferentiableOn.comp (g := fderiv ℝ (lieLog (σ := PositiveEdge L n k j))) hfd hw hdom
    have hg := DifferentiableOn.clm_apply hf1 hv
    exact hg.congr hder
theorem differentiable_point_curve [Fintype (PositiveEdge L n k j)]
    (hmem : ∀ y ∈ lieBall (PositiveEdge L n k j) (1 / 2),
      identityChartPoint y ∈ fieldSpace L n k j)
    {I : Set ℝ} {y : ℝ → PositiveEdge L n k j → ComplexMatrix2.LieElement}
    (hI : IsOpenIntervalAroundZero I) (hy : DifferentiableOn ℝ y I)
    (hm : MapsTo y I (lieBall (PositiveEdge L n k j) (1 / 2))) :
    IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I
        (fun t => identityChartPoint (y t)) ∧
      (DifferentiableOn ℝ (deriv y) I → ∀ b : Edge L n k j, b.IsPositivelyOriented →
        DifferentiableOn ℝ (deriv fun t => identityChartPoint (y t) b) I) := by
  have e : ∀ (b : Edge L n k j) (h : b.IsPositivelyOriented),
      (fun t => identityChartPoint (y t) b) = fun t => expFamily (y t) ⟨b, h⟩ :=
    fun b h => funext fun t => identityChartPoint_of_pos (y t) h
  have hc : DifferentiableOn ℝ (fun t => expFamily (y t)) I := fun t ht =>
    (differentiable_expFamily (y t)).comp_differentiableWithinAt t (hy t ht)
  refine ⟨⟨hI, fun t ht => hmem _ (hm ht), fun b h => ?_⟩, fun hdy b h => ?_⟩
  · rw [e b h]
    exact differentiableOn_pi.1 hc ⟨b, h⟩
  · rw [e b h]
    have hder : ∀ t ∈ I, deriv (fun s => expFamily (y s) ⟨b, h⟩) t =
        fderiv ℝ expFamily (y t) (deriv y t) ⟨b, h⟩ := by
      intro t ht
      have h1 := ((hy t ht).differentiableAt (hI.1.mem_nhds ht)).hasDerivAt
      have h2 := (differentiable_expFamily (y t)).hasFDerivAt.comp_hasDerivAt t h1
      exact ((hasDerivAt_pi.1 h2) ⟨b, h⟩).deriv
    have hfd : Differentiable ℝ (fderiv ℝ (expFamily (σ := PositiveEdge L n k j))) :=
      (contDiff_expFamily.fderiv_right (m := 1) (by norm_cast)).differentiable (by simp)
    have hf1 : DifferentiableOn ℝ
        (fderiv ℝ (expFamily (σ := PositiveEdge L n k j)) ∘ y) I :=
      Differentiable.comp_differentiableOn
        (g := fderiv ℝ (expFamily (σ := PositiveEdge L n k j))) hfd hy
    have hg := DifferentiableOn.clm_apply hf1 hdy
    exact (differentiableOn_pi.1 hg ⟨b, h⟩).congr hder
theorem curveTangent_eq [Fintype (PositiveEdge L n k j)]
    (hx : UniqueOrientation L n k j) (hc : LogAtOne (PositiveEdge L n k j))
    (hpt : ∀ y ∈ lieBall (PositiveEdge L n k j) (1 / 2),
      identityChartLog (identityChartPoint y) = y)
    {y₀ : PositiveEdge L n k j → ComplexMatrix2.LieElement}
    {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ)
    (hm : MapsTo γ I (identityChartPoint '' lieBall (PositiveEdge L n k j) (1 / 2)))
    (h0 : identityChartLog (γ 0) = y₀) :
    curveTangent γ =
      (extendByZero ∘ₗ leftTangent y₀) (deriv (fun t => identityChartLog (γ t)) 0) := by
  have hI := hγ.1
  have hd0 : HasDerivAt (fun t => identityChartLog (γ t))
      (deriv (fun t => identityChartLog (γ t)) 0) 0 :=
    (((differentiable_log_curve hc hpt hγ hm).1 0 hI.2.2).differentiableAt
      (hI.1.mem_nhds hI.2.2)).hasDerivAt
  have hmap : HasDerivAt (fun t => expFamily (identityChartLog (γ t)))
      (fderiv ℝ expFamily y₀ (deriv (fun t => identityChartLog (γ t)) 0)) 0 := by
    have h2 := (differentiable_expFamily (identityChartLog (γ 0))).hasFDerivAt.comp_hasDerivAt 0 hd0
    rw [h0] at h2
    exact h2
  have hpos : expFamily y₀ = restrictToPositiveEdges (γ 0) := by
    rw [← h0]
    exact (log_of_mem_image hc hpt (hm hI.2.2)).2.2
  rw [LinearMap.comp_apply, extendByZero_apply, curveTangent]
  refine extendOddly_congr hx fun b hb => ?_
  have hb1 : HasDerivAt (fun t => γ t b)
      (fderiv ℝ expFamily y₀ (deriv (fun t => identityChartLog (γ t)) 0) ⟨b, hb⟩) 0 := by
    refine ((hasDerivAt_pi.1 hmap) ⟨b, hb⟩).congr_of_eventuallyEq ?_
    filter_upwards [hI.1.mem_nhds hI.2.2] with t ht
    exact (congrFun (log_of_mem_image hc hpt (hm ht)).2.2 ⟨b, hb⟩).symm
  have hval : γ 0 b = expFamily y₀ ⟨b, hb⟩ := (congrFun hpos ⟨b, hb⟩).symm
  rw [dif_pos hb, hb1.deriv, hval]
  rfl
end Tower
theorem identityChartCurves (hC : IdentityChartOnFields)
    (hE : ExpChartsStatement) : IdentityChartCurvesStatement := by
  intro L n k j hL hn hj _
  have hx : UniqueOrientation L n k j := uniqueOrientation hL hn hj
  have hc : LogAtOne (PositiveEdge L n k j) :=
    logAtOne (hE (PositiveEdge L n k j) (PositiveEdge L n k j)).1
  obtain ⟨-, -, -, hpt, -⟩ := hC L n k j hL hn hj
  have hlog := fun y hy => (hpt y hy).2
  have hmem := fun y hy => (hpt y hy).1
  refine ⟨fun I γ hγ hm => differentiable_log_curve hc hlog hγ hm,
    fun I y hI hy hm => differentiable_point_curve hmem hI hy hm, fun y₀ hy₀ => ?_⟩
  exact ⟨extendByZero ∘ₗ leftTangent y₀, leftTangent_injective hc (mem_smallBall_of_mem_lieBall hy₀),
    fun I γ hγ hm h0 => curveTangent_eq hx hc hlog hγ hm h0⟩
end YangMills.Construction.Tower.IdentityChartCurves
end
