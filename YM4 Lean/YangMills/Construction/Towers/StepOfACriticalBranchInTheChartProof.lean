import YangMills.Construction.Towers.ChartAtOneOnTheConfigurationsProof
import YangMills.Construction.Towers.CurvesReadInTheChartAtOneProof
import YangMills.Construction.Towers.MapsReadBackFromTheChartAtOneProof
import YangMills.Construction.Towers.DifferentialOfTheAveragingOnTheSides
import YangMills.Construction.Towers.QuadraticFormOfAStepOfTheBranchProof
import YangMills.Construction.Towers.SecondDerivativeAtOneIsBilinearProof
import YangMills.Construction.Towers.StepOfACriticalBranchInTheChart
import YangMills.Construction.Towers.TrivialConfigurationAtAStep
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology NNReal ENNReal
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces Matrices.PowerExpCharts
  IdentityExpChart
namespace Tower.CriticalStepProof
section Series
variable {N : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
private def multiDegree (a : Fin N → ℕ) : ℕ := ∑ j, a j
private theorem exists_word_prod_eq (k : ℕ) (a : Fin N → ℕ) (ha : ∑ j, a j = k) :
    ∃ σ : Fin k → Fin N, ∀ g : Fin N → ℝ, ∏ i, g (σ i) = ∏ j, g j ^ a j := by
  subst ha
  refine ⟨fun i => (finSigmaFinEquiv.symm i).1, fun g => ?_⟩
  refine (Fintype.prod_equiv finSigmaFinEquiv.symm (fun i => g (finSigmaFinEquiv.symm i).1)
    (fun x : (j : Fin N) × Fin (a j) => g x.1) (fun _ => rfl)).trans ?_
  rw [Fintype.prod_sigma]
  simp
private theorem exists_monomial_multilinear (k : ℕ) (a : Fin N → ℕ) (ha : multiDegree a = k)
    (v : V) :
    ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin N → ℝ) V,
      (∀ y : Fin N → ℝ, T (fun _ => y) = (∏ j, y j ^ a j) • v) ∧ ‖T‖ ≤ ‖v‖ := by
  obtain ⟨σ, hσ⟩ := exists_word_prod_eq k a ha
  let M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin N → ℝ) ℝ :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
      fun i => ContinuousLinearMap.proj (σ i)
  have hM : ∀ w : Fin k → Fin N → ℝ, M w = ∏ i, w i (σ i) := fun w => by simp [M]
  refine ⟨M.smulRight v, fun y => ?_, ?_⟩
  · rw [ContinuousMultilinearMap.smulRight_apply, hM, hσ fun j => y j]
  · refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg v) fun w => ?_
    rw [ContinuousMultilinearMap.smulRight_apply, hM, norm_smul, norm_prod, mul_comm]
    gcongr with i
    exact norm_le_pi_norm (w i) (σ i)
private theorem analyticAt_zero_of_summable_series [CompleteSpace V] (c : (Fin N → ℕ) → V)
    (f : (Fin N → ℝ) → V) (r : ℝ≥0) (hr : 0 < r)
    (hsum : ∀ y : Fin N → ℝ, ‖y‖ < r → HasSum (fun a => (∏ j, y j ^ a j) • c a) (f y))
    (hbound : Summable fun a : Fin N → ℕ => (r : ℝ) ^ multiDegree a * ‖c a‖) :
    AnalyticAt ℝ f 0 := by
  classical
  let S : ℕ → Finset (Fin N → ℕ) := fun k => Finset.piAntidiag Finset.univ k
  have hS : ∀ k a, a ∈ S k ↔ multiDegree a = k := by
    intro k a
    simp [S, multiDegree, Finset.mem_piAntidiag]
  have hT : ∀ k (a : S k), ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin N → ℝ) V,
      (∀ y : Fin N → ℝ, T (fun _ => y) = (∏ j, y j ^ a.1 j) • c a.1) ∧ ‖T‖ ≤ ‖c a.1‖ :=
    fun k a => exists_monomial_multilinear k a.1 ((hS k a.1).1 a.2) (c a.1)
  choose T hTv hTn using hT
  let p : FormalMultilinearSeries ℝ (Fin N → ℝ) V := fun k => ∑ a : S k, T k a
  have hp : ∀ k (y : Fin N → ℝ),
      p k (fun _ => y) = ∑ a ∈ S k, (∏ j, y j ^ a j) • c a := by
    intro k y
    simp only [p, _root_.sum_apply, hTv]
    exact Finset.sum_coe_sort (S k) fun a => (∏ j, y j ^ a j) • c a
  have hnorm : ∀ k, ‖p k‖ * (r : ℝ) ^ k ≤ ∑' a, (r : ℝ) ^ multiDegree a * ‖c a‖ := by
    intro k
    calc ‖p k‖ * (r : ℝ) ^ k ≤ (∑ a : S k, ‖c a.1‖) * (r : ℝ) ^ k := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hTn k a)
      _ = ∑ a ∈ S k, (r : ℝ) ^ multiDegree a * ‖c a‖ := by
          rw [Finset.sum_mul,
            ← Finset.sum_coe_sort (S k) fun a => (r : ℝ) ^ multiDegree a * ‖c a‖]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [(hS k a.1).1 a.2, mul_comm]
      _ ≤ _ := hbound.sum_le_tsum _ fun _ _ => by positivity
  refine ⟨p, (r : ℝ≥0∞), p.le_radius_of_bound _ hnorm, ENNReal.coe_pos.2 hr, ?_⟩
  intro y hy
  have hy₀ : ‖y‖₊ < r := by
    simpa [Metric.eball, edist_zero_right, enorm_eq_nnnorm] using hy
  have hy' : ‖y‖ < r := NNReal.coe_lt_coe.2 hy₀
  have hfib := (hsum y hy').tsum_fiberwise multiDegree
  rw [zero_add]
  convert hfib using 2 with k
  rw [hp]
  have hset : multiDegree ⁻¹' {k} = (↑(S k) : Set (Fin N → ℕ)) := by
    ext a
    simp [hS]
  rw [hset]
  exact (Finset.tsum_subtype' (S k) fun a => (∏ j, y j ^ a j) • c a).symm
theorem analyticAt_zero_of_hasSum_monomials [FiniteDimensional ℝ V] (c : (Fin N → ℕ) → V)
    (f : (Fin N → ℝ) → V)
    (h : ∀ᶠ x in 𝓝 (0 : Fin N → ℝ), HasSum (fun a => (∏ j, x j ^ a j) • c a) (f x)) :
    AnalyticAt ℝ f 0 := by
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h
  let r : ℝ≥0 := ⟨ε / 2, by positivity⟩
  have hr : 0 < r := by
    show (0 : ℝ) < ε / 2
    positivity
  have hre : (r : ℝ) = ε / 2 := rfl
  have hsmall : ∀ y : Fin N → ℝ, ‖y‖ ≤ r → dist y 0 < ε := fun y hy => by
    rw [dist_zero_right]
    linarith
  refine analyticAt_zero_of_summable_series c f r hr (fun y hy => hball (hsmall y hy.le)) ?_
  have hpt := hball (hsmall (fun _ => (r : ℝ))
    ((pi_norm_le_iff_of_nonneg r.2).2 fun _ => by simp))
  have hs := (summable_norm_iff.2 hpt.summable)
  refine hs.congr fun a => ?_
  have hn : ‖(r : ℝ)‖ = r := Real.norm_of_nonneg r.2
  rw [norm_smul, Finset.prod_pow_eq_pow_sum, norm_pow, hn]
  rfl
theorem analyticAt_zero_of_isRealAnalyticToRealSpace {E W : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {D : Set E} {g : E → W} (h : IsRealAnalyticToRealSpace D g)
    (h0 : (0 : E) ∈ D) : AnalyticAt ℝ g 0 := by
  let x : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
  let y : W ≃ₗ[ℝ] (Fin (Module.finrank ℝ W) → ℝ) := (Module.finBasis ℝ W).equivFun
  obtain ⟨-, hra⟩ := h _ y
  obtain ⟨-, hpt⟩ := hra _ x
  have hmem : PowerSeries.RealSeries.realEmbed (0 : Fin (Module.finrank ℝ E) → ℝ) ∈
      PowerSeries.RealSeries.realEmbed '' (x '' D) := ⟨0, ⟨0, h0, map_zero x⟩, rfl⟩
  obtain ⟨c, hc⟩ := hpt _ hmem
  have hzero : PowerSeries.RealSeries.realEmbed (0 : Fin (Module.finrank ℝ E) → ℝ) = 0 := by
    funext i
    simp [PowerSeries.RealSeries.realEmbed]
  have hcont : Continuous (PowerSeries.RealSeries.realEmbed (n := Module.finrank ℝ E)) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have htend : Tendsto (PowerSeries.RealSeries.realEmbed (n := Module.finrank ℝ E)) (𝓝 0)
      (𝓝[Coordinates.ComplexCoordinates.realLocus _] (PowerSeries.RealSeries.realEmbed 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto 0, Eventually.of_forall fun u j => by
      simp [PowerSeries.RealSeries.realEmbed]⟩
  let G : (Fin (Module.finrank ℝ E) → ℝ) → Coordinates.ComplexCoordinates (Module.finrank ℝ W) :=
    fun u => PowerSeries.RealSeries.realEmbed (y (g (x.symm u)))
  have hG : AnalyticAt ℝ G 0 := by
    refine analyticAt_zero_of_hasSum_monomials c G ((htend.eventually hc).mono fun u hu => ?_)
    have e₁ : (fun i => (PowerSeries.RealSeries.realEmbed u i).re) = u := by
      funext i
      simp [PowerSeries.RealSeries.realEmbed]
    have e₃ : (fun a : Fin (Module.finrank ℝ E) → ℕ => (∏ j, u j ^ a j) • c a) = fun a =>
        (∏ j, (PowerSeries.RealSeries.realEmbed u j -
          PowerSeries.RealSeries.realEmbed 0 j) ^ a j) • c a := by
      funext a
      have e₂ : (∏ j, (PowerSeries.RealSeries.realEmbed u j -
          PowerSeries.RealSeries.realEmbed 0 j) ^ a j) = (((∏ j, u j ^ a j : ℝ)) : ℂ) := by
        simp [PowerSeries.RealSeries.realEmbed]
      rw [e₂]
      funext i
      simp [Complex.real_smul]
    have e₄ : G u = PowerSeries.RealSeries.realEmbed
        (y (g (x.symm fun i => (PowerSeries.RealSeries.realEmbed u i).re))) := by
      rw [e₁]
    rw [e₃, e₄]
    exact hu
  let xL : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := x.toContinuousLinearEquiv
  let yL : W ≃L[ℝ] (Fin (Module.finrank ℝ W) → ℝ) := y.toContinuousLinearEquiv
  let re : Coordinates.ComplexCoordinates (Module.finrank ℝ W) →L[ℝ]
      (Fin (Module.finrank ℝ W) → ℝ) :=
    ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i)
  let A : W →L[ℝ] W := ContinuousLinearMap.id ℝ W
  let B : Coordinates.ComplexCoordinates (Module.finrank ℝ W) →L[ℝ] W :=
    (yL.symm : (Fin (Module.finrank ℝ W) → ℝ) →L[ℝ] W).comp re
  have e : g = B ∘ G ∘ (xL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)) := by
    funext v
    have e₁ : (fun i => (PowerSeries.RealSeries.realEmbed (y (g v)) i).re) = y (g v) := by
      funext i
      simp [PowerSeries.RealSeries.realEmbed]
    have e₂ : x.symm (xL v) = v := x.symm_apply_apply v
    show g v = yL.symm (re (PowerSeries.RealSeries.realEmbed (y (g (x.symm (xL v))))))
    rw [e₂]
    show g v = y.symm (fun i => (PowerSeries.RealSeries.realEmbed (y (g v)) i).re)
    rw [e₁, y.symm_apply_apply]
  have hG' : AnalyticAt ℝ G ((xL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)) 0) := by
    simpa using hG
  rw [e]
  exact AnalyticAt.comp (B.analyticAt _)
    (AnalyticAt.comp hG' ((xL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).analyticAt 0))
end Series
section Calculus
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
theorem hasDerivAt_comp_smul_zero {ψ : E → W} (h : DifferentiableAt ℝ ψ 0) (u : E) :
    HasDerivAt (fun t : ℝ => ψ (t • u)) (fderiv ℝ ψ 0 u) 0 := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.hasDerivAt_comp_smul_line <;> assumption
theorem deriv_deriv_plane_eq_fderiv_fderiv {ψ : E → ℝ} (h : ContDiffAt ℝ 2 ψ 0) (u v : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => ψ (s • u + t • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ ψ) 0 u v := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
end Calculus
section Forms
def toMatrixCLM : ComplexMatrix2.LieElement →L[ℝ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := ComplexMatrix2.LieElement.toMatrix, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
theorem toMatrix_injective : Function.Injective ComplexMatrix2.LieElement.toMatrix :=
  fun _ _ h => Subtype.ext h
variable {L n k j : ℕ}
abbrev UniqueOrientation (L n k j : ℕ) : Prop :=
  ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem uniqueOrientation (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) : UniqueOrientation L n k j := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.uniqueOrientation <;> assumption
theorem nonempty_positiveEdge : Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.Construction.Tower.IdentityChart.nonempty_positiveEdge <;> assumption
theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos h
theorem extendOddly_of_not_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := if_neg h
theorem extendOddly_of_mem {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    extendOddly B = B := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.extendOddly_of_mem <;> assumption
theorem extendOddly_congr (hx : UniqueOrientation L n k j) {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b = g b) :
    extendOddly f = extendOddly g := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_congr <;> assumption
theorem extendOddly_mem (hx : UniqueOrientation L n k j) {f : Edge L n k j → ComplexMatrix2}
    (hf : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [extendOddly_of_pos f hb]
    exact hf b hb
  · rcases hx b with ⟨hb, hr⟩ | ⟨hr, hb⟩
    · rw [extendOddly_of_not_pos f hr, extendOddly_of_pos f hb]
      rfl
    · rw [extendOddly_of_pos f hr, extendOddly_of_not_pos f hb, neg_neg]
theorem edgeForm_ext (hx : UniqueOrientation L n k j) {A B : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hB : B ∈ edgeFormSpace L n k j)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → A b = B b) : A = B := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.edgeForm_ext <;> assumption
theorem formValues_toMatrix {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (b : PositiveEdge L n k j) : (formValues B b).toMatrix = B b.1 := by apply _root_.YangMills.SharedProofs.p338 <;> assumption
theorem ofValues_of_pos (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : ofValues y b = (y ⟨b, h⟩).toMatrix := by apply _root_.YangMills.Construction.Tower.IdentityChart.ofValues_of_positive <;> assumption
theorem ofValues_mem (hx : UniqueOrientation L n k j)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) : ofValues y ∈ edgeFormSpace L n k j :=
  extendOddly_mem hx fun b hb => by
    simp only [dif_pos hb]
    exact (y ⟨b, hb⟩).2
theorem formValues_ofValues (hx : UniqueOrientation L n k j)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) : formValues (ofValues y) = y := by
  funext b
  apply toMatrix_injective
  rw [formValues_toMatrix (ofValues_mem hx y), ofValues_of_pos y b.2]
theorem ofValues_formValues (hx : UniqueOrientation L n k j) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : ofValues (formValues B) = B :=
  edgeForm_ext hx (ofValues_mem hx _) hB fun b hb => by
    rw [ofValues_of_pos _ hb, formValues_toMatrix hB]
theorem ofValues_zero (hx : UniqueOrientation L n k j) :
    ofValues (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) = 0 :=
  edgeForm_ext hx (ofValues_mem hx _) (edgeFormSpace L n k j).zero_mem fun b hb => by
    rw [ofValues_of_pos _ hb]
    rfl
theorem ofValues_plane (hx : UniqueOrientation L n k j)
    (y y' : PositiveEdge L n k j → ComplexMatrix2.LieElement) (s t : ℝ) :
    ofValues (s • y + t • y') =
      algebraMap ℝ ℂ s • ofValues y + algebraMap ℝ ℂ t • ofValues y' := by
  rw [algebraMap_smul, algebraMap_smul]
  refine edgeForm_ext hx (ofValues_mem hx _) ((edgeFormSpace L n k j).add_mem
    ((edgeFormSpace L n k j).smul_mem s (ofValues_mem hx y))
    ((edgeFormSpace L n k j).smul_mem t (ofValues_mem hx y'))) fun b hb => ?_
  simp only [Pi.add_apply, Pi.smul_apply, ofValues_of_pos _ hb]
  rfl
theorem ofValues_line (hx : UniqueOrientation L n k j)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) (t : ℝ) :
    ofValues (t • y) = algebraMap ℝ ℂ t • ofValues y := by
  rw [algebraMap_smul]
  refine edgeForm_ext hx (ofValues_mem hx _) ((edgeFormSpace L n k j).smul_mem t
    (ofValues_mem hx y)) fun b hb => ?_
  simp only [Pi.smul_apply, ofValues_of_pos _ hb]
  rfl
def formValuesLinear : edgeFormSpace L n k j →ₗ[ℝ] PositiveEdge L n k j → ComplexMatrix2.LieElement where
  toFun B := formValues B
  map_add' A B := by
    funext b
    apply toMatrix_injective
    rw [formValues_toMatrix (A + B).2]
    show _ = (formValues (A : Edge L n k j → ComplexMatrix2) b).toMatrix +
      (formValues (B : Edge L n k j → ComplexMatrix2) b).toMatrix
    rw [formValues_toMatrix A.2, formValues_toMatrix B.2]
    rfl
  map_smul' c B := by
    funext b
    apply toMatrix_injective
    rw [formValues_toMatrix (c • B).2]
    show _ = c • (formValues (B : Edge L n k j → ComplexMatrix2) b).toMatrix
    rw [formValues_toMatrix B.2]
    rfl
theorem expTwist_of_not_pos (A U : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := if_neg h
theorem fieldOfPositiveValues_expFamily (hx : UniqueOrientation L n k j)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    fieldOfPositiveValues (expFamily y) = expForm (ofValues y) := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.fieldOfPositiveValues_expFamily <;> assumption
theorem fieldOfPositiveValues_restrict (hx : UniqueOrientation L n k j)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) :
    fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.fieldOfPositiveValues_restrict <;> assumption
theorem isRelativelyOpen_inter {E : Type} [TopologicalSpace E] {P D D' : Set E}
    (h : ComplexMatrix2.IsRelativelyOpen P D) (h' : ComplexMatrix2.IsRelativelyOpen P D') :
    ComplexMatrix2.IsRelativelyOpen P (D ∩ D') := by apply _root_.YangMills.SharedProofs.p7081 <;> assumption
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
def tracelessBasis : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
  Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
end Forms
section Zero
variable {σ : Type} [Fintype σ]
theorem expFamily_zero : expFamily (0 : σ → ComplexMatrix2.LieElement) = oneFamily σ := by
  funext s
  show ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1
  rw [smul_zero]
  exact NormedSpace.exp_zero
theorem zero_mem_lieBall [Nonempty σ] :
    (0 : σ → ComplexMatrix2.LieElement) ∈ lieBall σ (1 / 2) := by
  show supNorm (toMatrices (0 : σ → ComplexMatrix2.LieElement)) < 1 / 2
  have e : ∀ s, ComplexMatrix2.operatorNorm
      (toMatrices (0 : σ → ComplexMatrix2.LieElement) s) = 0 := fun s => by
    show ComplexMatrix2.operatorNorm (0 : ComplexMatrix2) = 0
    simp
  simp only [supNorm, e, ciSup_const]
  norm_num
theorem oneFamily_mem_expImage [Nonempty σ] : oneFamily σ ∈ expImage σ :=
  ⟨0, zero_mem_lieBall, expFamily_zero⟩
end Zero
section EvaluationMaps
variable {L n k j j' : ℕ}
theorem analyticAt_fnOnValues [inst : Fintype (PositiveEdge L n k j)]
    [Fintype (PositiveEdge L n k j')] [Nonempty (PositiveEdge L n k j)]
    (hx : UniqueOrientation L n k j) (hC : ExpChartAtOne (PositiveEdge L n k j))
    (hR : RealAnalyticIffInExpChart (PositiveEdge L n k j) (PositiveEdge L n k j') tracelessBasis)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h1 : trivialField L n k j ∈ 𝒰) (hF : IsAnalyticFieldFunction 𝒰 F) :
    AnalyticAt ℝ (fnOnValues (funPullback F)) 0 := by
  obtain ⟨hopen, f₁, hra⟩ := hF
  obtain rfl : f₁ = inst := Subsingleton.elim _ _
  have hE : specialUnitaryPower.IsOpenSubset (expImage (PositiveEdge L n k j)) := hC.2.1
  have hconf : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict hx (hopen.1 hU)
  let f : (PositiveEdge L n k j → ComplexMatrix2) → ℝ := fun w => F (fieldOfPositiveValues w)
  let O : Set (PositiveEdge L n k j → ComplexMatrix2) :=
    restrictToPositiveEdges '' 𝒰 ∩ expImage (PositiveEdge L n k j)
  have hO : specialUnitaryPower.IsOpenSubset O := isRelativelyOpen_inter hopen.2 hE
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar tracelessBasis)
      Complex.ofReal O f := by
    rintro _ ⟨⟨U, hU, rfl⟩, -⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ _), ?_⟩
    rintro _ ⟨⟨U', hU', rfl⟩, -⟩ hx'
    have hval := heq ⟨hx', (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  have hreal := ((hR O hO inter_subset_right).1 f).1 hrest
  have h0 : (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) ∈ pullbackDomain O := by
    refine ⟨zero_mem_lieBall, ?_, ?_⟩
    · rw [expFamily_zero]
      exact ⟨_, h1, rfl⟩
    · rw [expFamily_zero]
      exact oneFamily_mem_expImage
  have e : fnOnValues (funPullback F) = f ∘ expFamily := funext fun y => by
    show F (expForm (ofValues y)) = F (fieldOfPositiveValues (expFamily y))
    rw [fieldOfPositiveValues_expFamily hx]
  rw [e]
  exact analyticAt_zero_of_isRealAnalyticToRealSpace hreal h0
theorem mapOnValues_logPullback (hx : UniqueOrientation L n k j)
    (M : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2) :
    mapOnValues (logPullback M) =
      IdentityExpChart.logChart ∘ (fun w => restrictToPositiveEdges (M (fieldOfPositiveValues w))) ∘ expFamily := by
  funext y
  show toLieFamily (restrictToPositiveEdges (logPullback M (ofValues y))) =
    toLieFamily (logFamily (restrictToPositiveEdges (M (fieldOfPositiveValues (expFamily y)))))
  rw [fieldOfPositiveValues_expFamily hx]
  congr 1
  funext c
  exact extendOddly_of_pos
    (fun c => (1 / Complex.I) • ComplexMatrix2.logSeries (M (expForm (ofValues y)) c)) c.2
theorem mapOnValues_analytic_and_log [inst : Fintype (PositiveEdge L n k j)]
    [inst' : Fintype (PositiveEdge L n k j')]
    [Nonempty (PositiveEdge L n k j)] [Nonempty (PositiveEdge L n k j')]
    (hx : UniqueOrientation L n k j)
    (hC : ExpChartAtOne (PositiveEdge L n k j)) (hC' : ExpChartAtOne (PositiveEdge L n k j'))
    (hR : RealAnalyticIffInExpChart (PositiveEdge L n k j) (PositiveEdge L n k j') tracelessBasis)
    (hComp : specialUnitaryPower.Composition.CompDifferentiable
      (PositiveEdge L n k j) (PositiveEdge L n k j') ℂ)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    {M : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (h1 : trivialField L n k j ∈ 𝒰) (hM : IsAnalyticFieldMap 𝒰 M)
    (hD : IsDifferentiableFieldMap 𝒰 M)
    (hone : M (trivialField L n k j) = trivialField L n k j') :
    AnalyticAt ℝ (mapOnValues (logPullback M)) 0 ∧
      ∃ D : Set (PositiveEdge L n k j → ComplexMatrix2.LieElement), IsOpen D ∧ 0 ∈ D ∧
        ∀ y ∈ D, ∀ c : PositiveEdge L n k j', (mapOnValues (logPullback M) y c).toMatrix =
          (1 / Complex.I) • ComplexMatrix2.logSeries (M (expForm (ofValues y)) c.1) := by
  obtain ⟨hopen, hmaps, f₁, f₂, hra⟩ := hM
  obtain rfl : f₁ = inst := Subsingleton.elim _ _
  obtain rfl : f₂ = inst' := Subsingleton.elim _ _
  obtain ⟨-, -, g₁, g₂, hdiff⟩ := hD
  obtain rfl : g₁ = f₁ := Subsingleton.elim _ _
  obtain rfl : g₂ = f₂ := Subsingleton.elim _ _
  have hE : specialUnitaryPower.IsOpenSubset (expImage (PositiveEdge L n k j)) := hC.2.1
  have hE' : specialUnitaryPower.IsOpenSubset (expImage (PositiveEdge L n k j')) := hC'.2.1
  have hconf : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict hx (hopen.1 hU)
  let f : (PositiveEdge L n k j → ComplexMatrix2) → PositiveEdge L n k j' → ComplexMatrix2 :=
    fun w => restrictToPositiveEdges (M (fieldOfPositiveValues w))
  have hpre := (hComp (restrictToPositiveEdges '' 𝒰) f (expImage (PositiveEdge L n k j'))
    (fun _ => (0 : ℂ)) hdiff ⟨hE', fun c => differentiableOn_const _⟩).2.1
  let O : Set (PositiveEdge L n k j → ComplexMatrix2) :=
    (restrictToPositiveEdges '' 𝒰 ∩ f ⁻¹' expImage (PositiveEdge L n k j')) ∩
      expImage (PositiveEdge L n k j)
  have hO : specialUnitaryPower.IsOpenSubset O := isRelativelyOpen_inter hpre hE
  have hinto : MapsTo f O (specialUnitaryPower (PositiveEdge L n k j')) := fun w hw =>
    hdiff.2 hw.1.1
  have hinto' : MapsTo f O (expImage (PositiveEdge L n k j')) := fun w hw => hw.1.2
  have hrest : IsLocallyHolomorphicRestriction (IsHolomorphicToProduct tracelessBasis)
      asGroupFactors O f := by
    rintro _ ⟨⟨⟨U, hU, rfl⟩, -⟩, -⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, heq⟩ := hra.2.2.2 _ hq
    refine ⟨𝒳, Ψ, hp𝒳, hΨ _, ?_⟩
    rintro _ ⟨⟨⟨V, hV, rfl⟩, -⟩, -⟩ hxV
    refine heq ⟨hxV, ?_, ?_⟩
    · exact (Submodule.mem_bot ℝ).2 (funext fun e => e.elim)
    · exact fun c => (hopen.1 hV).1 c (mem_univ _)
  have hreal := (((hR O hO inter_subset_right).2.2 f hinto).2 hinto').1 hrest
  have hf0 : f (expFamily 0) = oneFamily (PositiveEdge L n k j') := by
    show restrictToPositiveEdges (M (fieldOfPositiveValues (expFamily 0))) = _
    rw [expFamily_zero]
    have e : oneFamily (PositiveEdge L n k j) =
        restrictToPositiveEdges (trivialField L n k j) := rfl
    rw [e, hconf h1, hone]
    rfl
  have h0 : (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) ∈ pullbackDomain O := by
    refine ⟨zero_mem_lieBall, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [expFamily_zero]
      exact ⟨_, h1, rfl⟩
    · show f (expFamily 0) ∈ expImage (PositiveEdge L n k j')
      rw [hf0]
      exact oneFamily_mem_expImage
    · rw [expFamily_zero]
      exact oneFamily_mem_expImage
  refine ⟨?_, pullbackDomain O, ?_, h0, fun y hy c => ?_⟩
  · rw [mapOnValues_logPullback hx]
    exact analyticAt_zero_of_isRealAnalyticToRealSpace hreal h0
  · exact (hreal _
      (Module.finBasis ℝ (PositiveEdge L n k j' → ComplexMatrix2.LieElement)).equivFun).1
  · have hin : f (expFamily y) ∈ expImage (PositiveEdge L n k j') := hy.2.1.2
    have e := congrFun (hC'.2.2.2.1 _ hin) c
    rw [mapOnValues_logPullback hx]
    show (toMatrices (IdentityExpChart.logChart (f (expFamily y))) c) = _
    rw [e]
    show (1 / Complex.I) • ComplexMatrix2.logSeries (M (fieldOfPositiveValues (expFamily y)) c.1) = _
    rw [fieldOfPositiveValues_expFamily hx]
theorem leftDifferential_eq_fderiv [Fintype (PositiveEdge L n k j)]
    [Fintype (PositiveEdge L n k j')] (hx : UniqueOrientation L n k j)
    {M : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hA : AnalyticAt ℝ (mapOnValues (logPullback M)) 0)
    {D : Set (PositiveEdge L n k j → ComplexMatrix2.LieElement)} (hD : IsOpen D) (h0 : 0 ∈ D)
    (hval : ∀ y ∈ D, ∀ c : PositiveEdge L n k j', (mapOnValues (logPullback M) y c).toMatrix =
      (1 / Complex.I) • ComplexMatrix2.logSeries (M (expForm (ofValues y)) c.1))
    (hone : M (trivialField L n k j) = trivialField L n k j')
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) (c : PositiveEdge L n k j') :
    leftDifferential M (trivialField L n k j) (ofValues y) c.1 =
      (fderiv ℝ (mapOnValues (logPullback M)) 0 y c).toMatrix := by
  let m := mapOnValues (logPullback M)
  have hd : DifferentiableAt ℝ m 0 := hA.differentiableAt
  have hl : HasDerivAt (fun t : ℝ => m (t • y)) (fderiv ℝ m 0 y) 0 :=
    hasDerivAt_comp_smul_zero hd y
  let P : (PositiveEdge L n k j' → ComplexMatrix2.LieElement) →L[ℝ] ComplexMatrix2 :=
    toMatrixCLM.comp (ContinuousLinearMap.proj c)
  have hp : HasDerivAt (fun t : ℝ => (m (t • y) c).toMatrix) ((fderiv ℝ m 0 y c).toMatrix) 0 :=
    P.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  let φ : ℝ → ComplexMatrix2 := fun t => ComplexMatrix2.logSeries (M (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ t • ofValues y) (trivialField L n k j)) c.1)
  have hline : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => t • y := by fun_prop
    simpa using this.tendsto 0
  have hev : (fun t : ℝ => (m (t • y) c).toMatrix) =ᶠ[𝓝 0] fun t => (1 / Complex.I) • φ t := by
    filter_upwards [hline.eventually (hD.mem_nhds h0)] with t ht
    show (mapOnValues (logPullback M) (t • y) c).toMatrix = _
    rw [hval _ ht c, ofValues_line hx]
    rfl
  have hφ : HasDerivAt φ (Complex.I • (fderiv ℝ m 0 y c).toMatrix) 0 := by
    have h₁ := (hp.congr_of_eventuallyEq hev.symm).const_smul Complex.I
    have e : (Complex.I • fun t => (1 / Complex.I) • φ t) = φ := by
      funext t
      rw [Pi.smul_apply, smul_smul, mul_one_div_cancel Complex.I_ne_zero, one_smul]
    rw [e] at h₁
    exact h₁
  rw [leftDifferential, extendOddly_of_pos _ c.2]
  have hW : M (trivialField L n k j) c.1 = 1 := by rw [hone]
  show Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (M (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ t • ofValues y) (trivialField L n k j)) c.1 *
      (M (trivialField L n k j) c.1)⁻¹)) 0 = _
  have hi : (1 : ComplexMatrix2)⁻¹ = 1 := by simp
  simp only [hW, hi, mul_one]
  show Complex.I⁻¹ • deriv φ 0 = _
  rw [hφ.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem fderiv_mapOnValues_eq [Fintype (PositiveEdge L n k j)] [Fintype (PositiveEdge L n k j')]
    (hx : UniqueOrientation L n k j) (hx' : UniqueOrientation L n k j')
    {M : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hA : AnalyticAt ℝ (mapOnValues (logPullback M)) 0)
    {D : Set (PositiveEdge L n k j → ComplexMatrix2.LieElement)} (hD : IsOpen D) (h0 : 0 ∈ D)
    (hval : ∀ y ∈ D, ∀ c : PositiveEdge L n k j', (mapOnValues (logPullback M) y c).toMatrix =
      (1 / Complex.I) • ComplexMatrix2.logSeries (M (expForm (ofValues y)) c.1))
    (hone : M (trivialField L n k j) = trivialField L n k j')
    {Q : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hQ : ∀ B ∈ edgeFormSpace L n k j, leftDifferential M (trivialField L n k j) B = Q B) :
    (∀ y : PositiveEdge L n k j → ComplexMatrix2.LieElement,
        Q (ofValues y) ∈ edgeFormSpace L n k j') ∧
      ∀ y, fderiv ℝ (mapOnValues (logPullback M)) 0 y = formValues (Q (ofValues y)) := by
  have hval' : ∀ (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) (b : Edge L n k j')
      (hb : b.IsPositivelyOriented), Q (ofValues y) b =
        (fderiv ℝ (mapOnValues (logPullback M)) 0 y ⟨b, hb⟩).toMatrix := by
    intro y b hb
    rw [← hQ _ (ofValues_mem hx y)]
    exact leftDifferential_eq_fderiv hx hA hD h0 hval hone y ⟨b, hb⟩
  have hmem : ∀ y : PositiveEdge L n k j → ComplexMatrix2.LieElement,
      Q (ofValues y) ∈ edgeFormSpace L n k j' := by
    intro y
    rw [← hQ _ (ofValues_mem hx y)]
    refine extendOddly_mem hx' fun b hb => ?_
    have e := leftDifferential_eq_fderiv hx hA hD h0 hval hone y ⟨b, hb⟩
    rw [leftDifferential, extendOddly_of_pos _ hb] at e
    rw [e]
    exact (fderiv ℝ (mapOnValues (logPullback M)) 0 y ⟨b, hb⟩).2
  refine ⟨hmem, fun y => ?_⟩
  funext b
  apply toMatrix_injective
  rw [formValues_toMatrix (hmem y) b, hval' y b.1 b.2]
theorem expForm_zero : expForm (0 : Edge L n k j → ComplexMatrix2) = trivialField L n k j := by
  have hexp : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
  funext b
  by_cases h : b.IsPositivelyOriented
  · have e : expForm (0 : Edge L n k j → ComplexMatrix2) b =
        ComplexMatrix2.matExp (Complex.I • (0 : Edge L n k j → ComplexMatrix2) b) *
          (1 : Edge L n k j → ComplexMatrix2) b := if_pos h
    rw [e, Pi.zero_apply, smul_zero, hexp]
    simp
  · have e : expForm (0 : Edge L n k j → ComplexMatrix2) b =
        (ComplexMatrix2.matExp (Complex.I • (0 : Edge L n k j → ComplexMatrix2) b.opposite) *
          (1 : Edge L n k j → ComplexMatrix2) b.opposite)⁻¹ := if_neg h
    rw [e, Pi.zero_apply, smul_zero, hexp]
    simp
theorem mapOnValues_zero (hx : UniqueOrientation L n k j)
    {M : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    {D : Set (PositiveEdge L n k j → ComplexMatrix2.LieElement)} (h0 : 0 ∈ D)
    (hval : ∀ y ∈ D, ∀ c : PositiveEdge L n k j', (mapOnValues (logPullback M) y c).toMatrix =
      (1 / Complex.I) • ComplexMatrix2.logSeries (M (expForm (ofValues y)) c.1))
    (hone : M (trivialField L n k j) = trivialField L n k j') :
    mapOnValues (logPullback M) 0 = 0 := by
  funext c
  apply toMatrix_injective
  have e := hval 0 h0 c
  rw [ofValues_zero hx, expForm_zero, hone] at e
  have e₂ : ComplexMatrix2.logSeries (1 : ComplexMatrix2) = 0 := by simp [ComplexMatrix2.logSeries]
  refine e.trans ?_
  show (1 / Complex.I) • ComplexMatrix2.logSeries (1 : ComplexMatrix2) = 0
  rw [e₂, smul_zero]
end EvaluationMaps
section Gradient
variable {L n k j : ℕ}
theorem exists_inner_eq {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    [FiniteDimensional ℝ (edgeFormSpace L n k j)] (ℓ : edgeFormSpace L n k j →ₗ[ℝ] ℝ) :
    ∃ X : edgeFormSpace L n k j, ∀ B, c.inner X B = ℓ B := by apply _root_.YangMills.Construction.Tower.StepQuadraticFormProof.exists_inner_eq <;> assumption
theorem leftDeriv_eq_fderiv [Fintype (PositiveEdge L n k j)] (hx : UniqueOrientation L n k j)
    {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hd : DifferentiableAt ℝ (fnOnValues (funPullback F)) 0)
    (y : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    leftDeriv (fun V => (F V : ℂ)) (trivialField L n k j) (ofValues y) =
      ((fderiv ℝ (fnOnValues (funPullback F)) 0 y : ℝ) : ℂ) := by
  have h2 := (hasDerivAt_comp_smul_zero hd y).ofReal_comp
  have e : (fun t : ℝ => ((F (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • ofValues y)
      (trivialField L n k j)) : ℝ) : ℂ)) =
      fun t => ((fnOnValues (funPullback F) (t • y) : ℝ) : ℂ) := by
    funext t
    rw [← ofValues_line hx]
    rfl
  show deriv (fun t : ℝ => ((F (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • ofValues y)
    (trivialField L n k j)) : ℝ) : ℂ)) 0 = _
  rw [e]
  exact h2.deriv
theorem fderiv_fnOnValues_eq_zero [Fintype (PositiveEdge L n k j)] (hx : UniqueOrientation L n k j)
    {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B' : Edge L n k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    [FiniteDimensional ℝ (edgeFormSpace L n k j)] {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hd : DifferentiableAt ℝ (fnOnValues (funPullback F)) 0)
    (h0 : leftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) (trivialField L n k j) = 0) :
    fderiv ℝ (fnOnValues (funPullback F)) 0 = 0 := by
  let ψ := fnOnValues (funPullback F)
  obtain ⟨X, hX⟩ := exists_inner_eq (c := c) ((fderiv ℝ ψ 0 : _ →ₗ[ℝ] ℝ) ∘ₗ formValuesLinear)
  have hg : IsLeftGradient (fieldSpace L n k j) (fun V => (F V : ℂ))
      (trivialField L n k j)
      (leftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) (trivialField L n k j)) := by
    refine Classical.epsilon_spec (p := IsLeftGradient (fieldSpace L n k j) _ _)
      ⟨(X : Edge L n k j → ComplexMatrix2), ⟨fun b hb => (X.2.1 b hb).2, X.2.2⟩, fun _ => X.2,
        fun B hB _ => ?_⟩
    have e := leftDeriv_eq_fderiv hx hd (formValues B)
    rw [ofValues_formValues hx hB] at e
    rw [e, hc X ⟨B, hB⟩, hX]
    rfl
  ext y
  have h₁ := hg.2.2 (ofValues y) (ofValues_mem hx y) (Set.toFinite _)
  rw [h0, leftDeriv_eq_fderiv hx hd y] at h₁
  have h₂ : edgeFormPairing (0 : Edge L n k j → ComplexMatrix2) (ofValues y) = 0 := by
    have e₁ := c.add_left 0 0 ⟨ofValues y, ofValues_mem hx y⟩
    rw [add_zero] at e₁
    have e₂ : c.inner 0 ⟨ofValues y, ofValues_mem hx y⟩ = 0 := by linarith
    have e := hc 0 ⟨ofValues y, ofValues_mem hx y⟩
    rw [e₂] at e
    simpa using e
  rw [h₂] at h₁
  exact_mod_cast h₁.symm
theorem fderiv_fderiv_eq_leftSecondDeriv [Fintype (PositiveEdge L n k j)]
    (hx : UniqueOrientation L n k j) {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hA : AnalyticAt ℝ (fnOnValues (funPullback F)) 0)
    (y y' : PositiveEdge L n k j → ComplexMatrix2.LieElement) :
    fderiv ℝ (fderiv ℝ (fnOnValues (funPullback F))) 0 y y' =
      leftSecondDeriv F (trivialField L n k j) (ofValues y) (ofValues y') := by
  rw [← deriv_deriv_plane_eq_fderiv_fderiv hA.contDiffAt y y']
  show _ = deriv (fun s : ℝ => deriv (fun t : ℝ => F (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ s • ofValues y + algebraMap ℝ ℂ t • ofValues y')
    (trivialField L n k j))) 0) 0
  simp only [← ofValues_plane hx]
  rfl
end Gradient
theorem criticalStepInExpChart_holds
    (hAn : SmoothingAnalyticCovariantOnSides)
    (hDf : SmoothingDerivAtOneOnAllSides)
    (hTriv : TrivialFieldAtStep)
    (hRel : TrivialLinearization.AllRelationsStatement)
    (hCh : IdentityExpChart.ChartAndBallImages.Statement)
    (hRead : IdentityExpChart.AnalyticReadInExpChartStatement)
    (hDiff : AnalyticMapDifferentiableStatement)
    (hComp : specialUnitaryPower.Composition.CompositionProperties)
    (hSp : FiniteSideFormSpaces) : CriticalStepInExpChart := by
  intro L n k i hL hn hi _ _ F hF hgrad hpos
  have hx : UniqueOrientation L n k i := uniqueOrientation hL hn hi.le
  have hx' : UniqueOrientation L n k (i + 1) := uniqueOrientation hL hn hi
  have : Nonempty (PositiveEdge L n k i) := nonempty_positiveEdge
  have : Nonempty (PositiveEdge L n k (i + 1)) := nonempty_positiveEdge
  obtain ⟨𝒰, h𝒰, hFa⟩ := hF
  have hC := (hCh (PositiveEdge L n k i)).1
  have hC' := (hCh (PositiveEdge L n k (i + 1))).1
  have hR := hRead (PositiveEdge L n k i) (PositiveEdge L n k (i + 1)) tracelessBasis
  have hCo := (hComp (PositiveEdge L n k i) (PositiveEdge L n k (i + 1))).2.2.2.1
  obtain ⟨𝒰₁, h𝒰₁, hM, -⟩ := (hAn L hL n k i hn hi).analytic
  have hone := (hTriv L n k i hL hn hi).2.1
  have hDM := hDiff L n k i (i + 1) hL hn hi.le hi _ _ hM
  obtain ⟨hmA, D, hDo, hD0, hval⟩ :=
    mapOnValues_analytic_and_log hx hC hC' hR hCo h𝒰₁.2 hM hDM hone
  have hfA := analyticAt_fnOnValues hx hC hR h𝒰.2 hFa
  obtain ⟨-, hfd, -, c, hc⟩ := hSp L n k i hL hn hi.le
  obtain ⟨𝒰₂, -, -, hQ⟩ := (hDf L hL n k i hn hi).deriv_eq_linear
  obtain ⟨hQmem, hT⟩ := fderiv_mapOnValues_eq hx hx' hmA hDo hD0 hval hone hQ
  have hzero : smoothingInExpChart L n k i 0 = 0 := mapOnValues_zero hx hD0 hval hone
  refine ⟨⟨hmA, hfA, hzero, fun Z => ?_, ?_, fun ξ hξ hne => ?_⟩, hT, ?_⟩
  · obtain ⟨B, hB, hBZ⟩ := ((hRel L hL).1 n k i 0 hn hi (Nat.zero_le _)).2.2.2.1.1
      (ofValues Z) (ofValues_mem hx' Z)
    refine ⟨formValues B, ?_⟩
    rw [hT, ofValues_formValues hx hB, hBZ, formValues_ofValues hx']
  · exact fderiv_fnOnValues_eq_zero hx hc hfA.differentiableAt hgrad
  · rw [fderiv_fderiv_eq_leftSecondDeriv hx hfA]
    refine hpos _ (ofValues_mem hx ξ) ?_ ?_
    · have e := hT ξ
      rw [hξ] at e
      rw [← ofValues_formValues hx' (hQmem ξ), ← e, ofValues_zero hx']
    · intro h0
      apply hne
      rw [← formValues_ofValues hx ξ, h0]
      funext b
      apply toMatrix_injective
      rw [formValues_toMatrix (edgeFormSpace L n k i).zero_mem]
      rfl
  · exact fun y y' => fderiv_fderiv_eq_leftSecondDeriv hx hfA y y'
end Tower.CriticalStepProof
end YangMills.Construction
end
