import YangMills.Construction.Towers.MapsReadBackFromTheChartAtOneProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChartProof
import YangMills.Construction.Towers.ExpansionOfTheIterateInTheLeftChartProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace Tower
namespace LeftChartStep
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
def hessianAtZero (g : E → F) : E →L[ℝ] E →L[ℝ] F := fderiv ℝ (fderiv ℝ g) 0
theorem hessianAtZero_symm {g : E → F} (hg : ContDiffAt ℝ 3 g 0) (u v : E) :
    hessianAtZero g u v = hessianAtZero g v u :=
  (hg.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq u v
theorem differentiableAt_fderiv_of_contDiffAt_three {g : E → F} {z : E}
    (hg : ContDiffAt ℝ 3 g z) : DifferentiableAt ℝ (fderiv ℝ g) z :=
  (hg.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
theorem hasDerivAt_comp_smul_line {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} (y : E) {t : ℝ} (hf : DifferentiableAt ℝ f (t • y)) :
    HasDerivAt (fun s : ℝ => f (s • y)) (fderiv ℝ f (t • y) y) t := by apply _root_.YangMills.Construction.Tower.IterLeftChart.hasDerivAt_comp_smul <;> assumption
theorem hasDerivAt_line_at_zero {g : E → F} (hg : ContDiffAt ℝ 3 g 0) (y : E) :
    HasDerivAt (fun s : ℝ => g (s • y)) (fderiv ℝ g 0 y) 0 := by apply _root_.YangMills.Construction.Tower.IterLeftChart.hasDerivAt_comp_smul_zero <;> assumption
theorem hasDerivAt_fderiv_along_line {g : E → F} (hg : ContDiffAt ℝ 3 g 0) (y y' : E) :
    HasDerivAt (fun s : ℝ => fderiv ℝ g (s • y) y') (hessianAtZero g y y') 0 := by
  have h := hasDerivAt_comp_smul_line (f := fderiv ℝ g) y (t := 0) (by
    simpa using differentiableAt_fderiv_of_contDiffAt_three hg)
  have h' := h.clm_apply (hasDerivAt_const (0 : ℝ) y')
  simpa [hessianAtZero] using h'
theorem iteratedDeriv_two_along_line {g : E → F} (hg : ContDiffAt ℝ 3 g 0) (y : E) :
    iteratedDeriv 2 (fun s : ℝ => g (s • y)) 0 = hessianAtZero g y y := by
  have hev : ∀ᶠ z in 𝓝 (0 : E), ContDiffAt ℝ 3 g z := hg.eventually (by simp)
  have hc : Tendsto (fun s : ℝ => s • y) (𝓝 0) (𝓝 (0 : E)) := by
    have : Continuous fun s : ℝ => s • y := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have heq : deriv (fun s : ℝ => g (s • y)) =ᶠ[𝓝 0] fun s => fderiv ℝ g (s • y) y := by
    filter_upwards [hc.eventually hev] with s hs
    exact (hasDerivAt_comp_smul_line y (hs.differentiableAt (by norm_num))).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  exact (hasDerivAt_fderiv_along_line hg y y).deriv
theorem taylor_two_remainder {g : E → F} (hg : ContDiffAt ℝ 3 g 0) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ y : E, ‖y‖ < r →
      ‖g y - g 0 - fderiv ℝ g 0 y - (1 / 2 : ℝ) • hessianAtZero g y y‖ ≤ C * ‖y‖ ^ 3 := by
  set D₁ := fderiv ℝ g with hD₁
  set D₂ := fderiv ℝ D₁ with hD₂
  set Q := hessianAtZero g with hQ
  have hQ0 : Q = D₂ 0 := rfl
  have h₁ : ContDiffAt ℝ 2 D₁ 0 := hg.fderiv_right (m := 2) (by norm_num)
  have h₂ : ContDiffAt ℝ 1 D₂ 0 := h₁.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h₂.exists_lipschitzOnWith
  have hev₁ : ∀ᶠ z in 𝓝 (0 : E), ContDiffAt ℝ 3 g z := hg.eventually (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem ht hev₁)
  have hin : ∀ z : E, ‖z‖ < r → z ∈ t ∧ ContDiffAt ℝ 3 g z := fun z hz =>
    hball (by simpa using hz)
  have hgd : ∀ z : E, ‖z‖ < r → HasFDerivAt g (D₁ z) z := fun z hz =>
    ((hin z hz).2.differentiableAt (by norm_num)).hasFDerivAt
  have hDd : ∀ z : E, ‖z‖ < r → HasFDerivAt D₁ (D₂ z) z := fun z hz =>
    (differentiableAt_fderiv_of_contDiffAt_three (hin z hz).2).hasFDerivAt
  have h0t : (0 : E) ∈ t := (hin 0 (by simpa using hr)).1
  have hlip : ∀ z : E, ‖z‖ < r → ‖D₂ z - Q‖ ≤ K * ‖z‖ := by
    intro z hz
    have := hK.dist_le_mul z (hin z hz).1 0 h0t
    simpa [dist_eq_norm, hQ0] using this
  let S : E → E →L[ℝ] F := fun z => D₁ z - D₁ 0 - Q z
  have hSd : ∀ z : E, ‖z‖ < r → HasFDerivAt S (D₂ z - Q) z := fun z hz =>
    ((hDd z hz).sub_const _).sub Q.hasFDerivAt
  have hS0 : S 0 = 0 := by simp [S]
  have hSb : ∀ y : E, ‖y‖ < r → ‖S y‖ ≤ K * ‖y‖ ^ 2 := by
    intro y hy
    have hs : Convex ℝ (Metric.closedBall (0 : E) ‖y‖) := convex_closedBall _ _
    have hzr : ∀ z ∈ Metric.closedBall (0 : E) ‖y‖, ‖z‖ < r := fun z hz =>
      lt_of_le_of_lt (by simpa using hz) hy
    have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := S) (C := K * ‖y‖)
      (fun z hz => (hSd z (hzr z hz)).hasFDerivWithinAt)
      (fun z hz => (hlip z (hzr z hz)).trans
        (mul_le_mul_of_nonneg_left (by simpa using hz) K.2))
      (x := 0) (y := y) (by simp) (by simp)
    simpa [hS0, pow_two, mul_assoc] using this
  let R : E → F := fun y => g y - g 0 - D₁ 0 y - (1 / 2 : ℝ) • Q y y
  have hflip : ∀ z : E, Q.flip z = Q z := by
    intro z
    ext w
    exact hessianAtZero_symm hg w z
  have hRd : ∀ z : E, ‖z‖ < r → HasFDerivAt R (S z) z := by
    intro z hz
    have hq : HasFDerivAt (fun y => Q y y) (Q z + Q z) z := by
      have := Q.hasFDerivAt (x := z) |>.clm_apply (hasFDerivAt_id z)
      simpa [hflip] using this
    have h := (((hgd z hz).sub_const (g 0)).sub (D₁ 0).hasFDerivAt).sub
      (hq.const_smul (1 / 2 : ℝ))
    have hval : D₁ z - D₁ 0 - (1 / 2 : ℝ) • (Q z + Q z) = S z := by
      ext w
      simp only [S, sub_apply, smul_apply, add_apply]
      rw [← two_smul ℝ (Q z w), smul_smul]
      norm_num
    rw [hval] at h
    exact h
  have hR0 : R 0 = 0 := by simp [R]
  refine ⟨K, r, K.2, hr, fun y hy => ?_⟩
  have hs : Convex ℝ (Metric.closedBall (0 : E) ‖y‖) := convex_closedBall _ _
  have hzr : ∀ z ∈ Metric.closedBall (0 : E) ‖y‖, ‖z‖ < r := fun z hz =>
    lt_of_le_of_lt (by simpa using hz) hy
  have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := R) (C := K * ‖y‖ ^ 2)
    (fun z hz => (hRd z (hzr z hz)).hasFDerivWithinAt)
    (fun z hz => (hSb z (hzr z hz)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg z) (by simpa using hz) 2) K.2))
    (x := 0) (y := y) (by simp) (by simp)
  have h2 : ‖R y‖ ≤ K * ‖y‖ ^ 2 * ‖y‖ := by simpa [hR0] using this
  calc ‖R y‖ ≤ K * ‖y‖ ^ 2 * ‖y‖ := h2
    _ = K * ‖y‖ ^ 3 := by ring
theorem hasDerivAt_mem_of_eventually_mem (H : Submodule ℝ F) (hH : IsClosed (H : Set F))
    {φ : ℝ → F} {v : F} (hd : HasDerivAt φ v 0) (h : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ H) : v ∈ H := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  have h0 : φ 0 ∈ H := h.self_of_nhds
  refine hH.mem_of_tendsto hs ?_
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with t ht
  simp only [slope, vsub_eq_sub]
  exact H.smul_mem _ (H.sub_mem ht h0)
theorem eventually_fderiv_apply_mem (H : Submodule ℝ F) (hH : IsClosed (H : Set F)) {g : E → F}
    (hg : ContDiffAt ℝ 3 g 0) (hv : ∀ᶠ z in 𝓝 (0 : E), g z ∈ H) :
    ∀ᶠ z in 𝓝 (0 : E), ∀ w, fderiv ℝ g z w ∈ H := by
  have hev : ∀ᶠ z in 𝓝 (0 : E), ContDiffAt ℝ 3 g z := hg.eventually (by simp)
  filter_upwards [hev, hv.eventually_nhds] with z hz hzv w
  have hc : Tendsto (fun s : ℝ => z + s • w) (𝓝 0) (𝓝 z) := by
    have : Continuous fun s : ℝ => z + s • w :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using this.tendsto 0
  have hl : HasDerivAt (fun s : ℝ => z + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
  have hd : HasDerivAt (fun s : ℝ => g (z + s • w)) (fderiv ℝ g z w) 0 := by
    have hf : HasFDerivAt g (fderiv ℝ g z) ((fun s : ℝ => z + s • w) 0) := by
      simpa using (hz.differentiableAt (by norm_num)).hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hl
  exact hasDerivAt_mem_of_eventually_mem H hH hd (hc.eventually hzv)
theorem fderiv_zero_apply_mem (H : Submodule ℝ F) (hH : IsClosed (H : Set F)) {g : E → F}
    (hg : ContDiffAt ℝ 3 g 0) (hv : ∀ᶠ z in 𝓝 (0 : E), g z ∈ H) (w : E) :
    fderiv ℝ g 0 w ∈ H :=
  (eventually_fderiv_apply_mem H hH hg hv).self_of_nhds w
theorem hessianAtZero_mem (H : Submodule ℝ F) (hH : IsClosed (H : Set F)) {g : E → F}
    (hg : ContDiffAt ℝ 3 g 0) (hv : ∀ᶠ z in 𝓝 (0 : E), g z ∈ H) (y y' : E) :
    hessianAtZero g y y' ∈ H := by
  have hc : Tendsto (fun s : ℝ => s • y) (𝓝 0) (𝓝 (0 : E)) := by
    have : Continuous fun s : ℝ => s • y := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  refine hasDerivAt_mem_of_eventually_mem H hH (hasDerivAt_fderiv_along_line hg y y') ?_
  filter_upwards [hc.eventually (eventually_fderiv_apply_mem H hH hg hv)] with s hs
  exact hs y'
end Calculus
section Edges
variable {L n k i : ℕ}
def OrientationDichotomy (L n k i : ℕ) : Prop :=
  ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem opposite_positive_of_not (hp : OrientationDichotomy L n k i) {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IterLeftChart.opposite_pos_of_not_pos <;> assumption
theorem not_opposite_positive (hp : OrientationDichotomy L n k i) {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IterLeftChart.not_opposite_pos_of_pos <;> assumption
theorem opposite_opposite (b : Edge L n k i) : b.opposite.opposite = b := rfl
theorem fieldOfPositiveValues_restrict (hp : OrientationDichotomy L n k i)
    {U : Edge L n k i → ComplexMatrix2} (hU : U ∈ fieldSpace L n k i) :
    fieldOfPositiveValues (restrictToPositiveEdges U) = U := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.fieldOfPositiveValues_restrict <;> assumption
theorem fieldOfPositiveValues_expTwist (hp : OrientationDichotomy L n k i)
    (A V : Edge L n k i → ComplexMatrix2) :
    fieldOfPositiveValues (fun b : PositiveEdge L n k i =>
        ComplexMatrix2.matExp (Complex.I • A b.1) * V b.1) =
      PeriodicLattice.expTwist A V := by apply _root_.YangMills.Construction.Tower.IterLeftChart.fieldOfPositiveValues_expMul <;> assumption
theorem edgeFormOfPositiveValues_add (w w' : PositiveEdge L n k i → ComplexMatrix2) :
    edgeFormOfPositiveValues (w + w') =
      edgeFormOfPositiveValues w + edgeFormOfPositiveValues w' := by apply _root_.YangMills.Construction.Tower.IterLeftChart.edgeFormOfPositiveValues_add <;> assumption
theorem edgeFormOfPositiveValues_smul (t : ℝ) (w : PositiveEdge L n k i → ComplexMatrix2) :
    edgeFormOfPositiveValues (t • w) = t • edgeFormOfPositiveValues w := by apply _root_.YangMills.Construction.Tower.IterLeftChart.edgeFormOfPositiveValues_smul <;> assumption
theorem edgeFormOfPositiveValues_mem (hp : OrientationDichotomy L n k i)
    {w : PositiveEdge L n k i → ComplexMatrix2}
    (hw : ∀ b, w b ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k i := by apply _root_.YangMills.Construction.Tower.IterLeftChart.edgeFormOfPositiveValues_mem <;> assumption
def positiveValues (L n k i : ℕ) :
    edgeFormSpace L n k i →ₗ[ℝ] PositiveEdge L n k i → ComplexMatrix2.LieElement where
  toFun B b := (⟨B.1 b.1, B.2.1 b.1 b.2⟩ : ComplexMatrix2.hermitianTraceless)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem continuous_positiveValues [FiniteDimensional ℝ (edgeFormSpace L n k i)] :
    Continuous (positiveValues L n k i) :=
  LinearMap.continuous_of_finiteDimensional _
theorem tendsto_positiveValues [FiniteDimensional ℝ (edgeFormSpace L n k i)] :
    Tendsto (positiveValues L n k i) (𝓝 0) (𝓝 0) := by
  simpa using (continuous_positiveValues (L := L) (n := n) (k := k) (i := i)).tendsto 0
theorem edgeFormNorm_eq_sqrt [Fintype (PositiveEdge L n k i)] (B : edgeFormSpace L n k i) :
    edgeFormNorm (B : Edge L n k i → ComplexMatrix2) =
      Real.sqrt (∑ b, ‖positiveValues L n k i B b‖ ^ 2) := by
  have h : ∀ Y : ComplexMatrix2.LieElement,
      (ComplexMatrix2.halfTrace (Y.toMatrix * Y.toMatrix)).re = ‖Y‖ ^ 2 := fun Y => by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  unfold edgeFormNorm traceFinsumNorm traceFinsumPairing
  rw [finsum_eq_sum_of_fintype, Complex.re_sum]
  congr 1
  exact Finset.sum_congr rfl fun b _ => h (positiveValues L n k i B b)
theorem norm_positiveValues_le [Fintype (PositiveEdge L n k i)] (B : edgeFormSpace L n k i) :
    ‖positiveValues L n k i B‖ ≤ edgeFormNorm (B : Edge L n k i → ComplexMatrix2) := by
  rw [edgeFormNorm_eq_sqrt]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun b => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun b => ‖positiveValues L n k i B b‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ b)
theorem edgeFormNorm_smul [Fintype (PositiveEdge L n k i)] (t : ℝ) (B : edgeFormSpace L n k i) :
    edgeFormNorm ((t • B : edgeFormSpace L n k i) : Edge L n k i → ComplexMatrix2) =
      |t| * edgeFormNorm (B : Edge L n k i → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.IterLeftChart.edgeFormNorm_smul <;> assumption
end Edges
section Step
open YangMills.Construction.Matrices.PowerExpCharts
variable {L n k i : ℕ}
def stepOnPositive (L n k i : ℕ) (w : PositiveEdge L n k i → ComplexMatrix2) :
    PositiveEdge L n k (i + 1) → ComplexMatrix2 :=
  restrictToPositiveEdges (smoothingStep L n k i (fieldOfPositiveValues w))
def chartedStepLog (L n k i : ℕ) (V : Edge L n k i → ComplexMatrix2)
    (Y : PositiveEdge L n k i → ComplexMatrix2.LieElement)
    (c : PositiveEdge L n k (i + 1)) : ComplexMatrix2 :=
  logChart (stepOnPositive L n k i (restrictToPositiveEdges V))
    (stepOnPositive L n k i (expChartI (restrictToPositiveEdges V) Y)) c
theorem expChartI_positiveValues (V : Edge L n k i → ComplexMatrix2) (B : edgeFormSpace L n k i) :
    expChartI (restrictToPositiveEdges V) (positiveValues L n k i B) =
      fun b : PositiveEdge L n k i => ComplexMatrix2.matExp (Complex.I • B.1 b.1) * V b.1 := rfl
theorem stepOnPositive_expChartI (hp : OrientationDichotomy L n k i)
    (V : Edge L n k i → ComplexMatrix2) (B : edgeFormSpace L n k i)
    (c : PositiveEdge L n k (i + 1)) :
    stepOnPositive L n k i (expChartI (restrictToPositiveEdges V) (positiveValues L n k i B)) c =
      smoothingStep L n k i
        (PeriodicLattice.expTwist (B : Edge L n k i → ComplexMatrix2) V) c := by
  rw [expChartI_positiveValues, stepOnPositive, fieldOfPositiveValues_expTwist hp]
  rfl
theorem stepOnPositive_restrict (hp : OrientationDichotomy L n k i)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ fieldSpace L n k i)
    (c : PositiveEdge L n k (i + 1)) :
    stepOnPositive L n k i (restrictToPositiveEdges V) c = smoothingStep L n k i V c := by
  rw [stepOnPositive, fieldOfPositiveValues_restrict hp hV]
  rfl
theorem stepLog_eq_chartedStepLog (hp : OrientationDichotomy L n k i)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ fieldSpace L n k i)
    (B : edgeFormSpace L n k i) (c : PositiveEdge L n k (i + 1)) :
    stepLog V c (B : Edge L n k i → ComplexMatrix2) =
      chartedStepLog L n k i V (positiveValues L n k i B) c := by
  simp only [stepLog, chartedStepLog, logChart]
  rw [stepOnPositive_expChartI hp, stepOnPositive_restrict hp hV, one_div]
end Step
section ChartData
open YangMills.Construction.Matrices.PowerExpCharts YangMills.Construction.Matrices.GroupLieProduct
variable {L n k i : ℕ}
theorem mul_inv_mem_specialUnitary {A B : ComplexMatrix2}
    (hA : A ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (hB : B ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    A * B⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
  have hB' := Matrix.mem_specialUnitaryGroup_iff.mp hB
  have hinv : B⁻¹ = star B := Matrix.inv_eq_right_inv (Unitary.mul_star_self_of_mem hB'.1)
  have hstar : star B ∈ ComplexMatrix2.specialUnitary := by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Unitary.star_mem hB'.1, ?_⟩
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hB'.2]
    simp
  rw [hinv]
  exact ComplexMatrix2.specialUnitary.mul_mem hA hstar
theorem logSeries_div_I_mem (hexp : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (h : ComplexMatrix2.operatorNorm (A - 1) < 1) :
    (1 / Complex.I) • ComplexMatrix2.logSeries A ∈ ComplexMatrix2.hermitianTraceless := by
  have hA' := Matrix.mem_specialUnitaryGroup_iff.mp hA
  obtain ⟨H, -, hlog, -, -, -, hdet⟩ := hexp.2.2.2.2.2.2.2.1 A hA'.1 h
  have hH := (hdet hA'.2).2.1
  rw [hlog, smul_smul, one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  exact hH
structure ChartedStepData (V : Edge L n k i → ComplexMatrix2)
    [Fintype (PositiveEdge L n k (i + 1))] [Fintype (PositiveEdge L n k i)] : Prop where
  contDiff : ∀ c, ContDiffAt ℝ ∞ (fun Y => chartedStepLog L n k i V Y c) 0
  vanishes : ∀ c, chartedStepLog L n k i V 0 c = 0
  eventually : ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement), ∀ c,
    stepOnPositive L n k i (expChartI (restrictToPositiveEdges V) Y) c ∈
        (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) ∧
      stepOnPositive L n k i (expChartI (restrictToPositiveEdges V) Y) c *
        (stepOnPositive L n k i (restrictToPositiveEdges V) c)⁻¹ ∈ ComplexMatrix2.logBall ∧
      chartedStepLog L n k i V Y c ∈ ComplexMatrix2.hermitianTraceless
  base_mem : ∀ c, stepOnPositive L n k i (restrictToPositiveEdges V) c ∈
    (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)
theorem expChartI_zero {σ : Type} (p : σ → ComplexMatrix2) : expChartI p 0 = p := by apply _root_.YangMills.SharedProofs.p27659 <;> assumption
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by simp [ComplexMatrix2.logSeries]
theorem chartedStepData_of [Fintype (PositiveEdge L n k (i + 1))]
    [Fintype (PositiveEdge L n k i)] (hexp : ComplexMatrix2.ExpLogEstimates)
    (hcharts : PowerCharts (PositiveEdge L n k (i + 1)))
    {V : Edge L n k i → ComplexMatrix2} {O : Set (PositiveEdge L n k i → ComplexMatrix2)}
    (hmaps : MapsTo (stepOnPositive L n k i) O
      (specialUnitaryPower (PositiveEdge L n k (i + 1))))
    (hser : HasChartPowerSeries O (stepOnPositive L n k i))
    (hV : restrictToPositiveEdges V ∈ O) : ChartedStepData V := by
  set p₀ := restrictToPositiveEdges V with hp₀
  set F := stepOnPositive L n k i with hF
  set p₁ := F p₀ with hp₁
  obtain ⟨N, hN, hform, hsm, -⟩ := hser.1 p₀ hV
  have hbase : p₁ ∈ specialUnitaryPower (PositiveEdge L n k (i + 1)) := hmaps hV
  have hbase' : ∀ c, p₁ c ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := hbase
  have hε : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, -, hlog⟩ := hcharts p₁ hbase
  obtain ⟨-, -, -, -, hopen, hlogsm, -⟩ := hlog (Real.log (19 / 10)) hε
    (by rw [Real.exp_log (by norm_num)])
  have hΦ : ContDiffAt ℝ ∞ (F ∘ expChartI p₀) 0 := hsm.contDiffAt hN
  have hΦ0 : (F ∘ expChartI p₀) 0 = p₁ := by simp [expChartI_zero, hp₁]
  have hunit : ∀ c, p₁ c * (p₁ c)⁻¹ = 1 := fun c =>
    Matrix.mul_nonsing_inv _ (by
      rw [(Matrix.mem_specialUnitaryGroup_iff.mp (hbase' c)).2]
      exact isUnit_one)
  have hmem : (F ∘ expChartI p₀) 0 ∈ logDomain p₁ := by
    rw [hΦ0]
    intro c
    simp [hunit c]
  have hG : ContDiffAt ℝ ∞ (logChart p₁ ∘ (F ∘ expChartI p₀)) 0 :=
    (hlogsm.contDiffAt (hopen.mem_nhds hmem)).comp 0 hΦ
  have hnear : ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement),
      (F ∘ expChartI p₀) Y ∈ logDomain p₁ :=
    hΦ.continuousAt.eventually (hopen.mem_nhds hmem)
  refine ⟨fun c => contDiffAt_pi.mp hG c, fun c => ?_, ?_, hbase'⟩
  · have : chartedStepLog L n k i V 0 c = logChart p₁ ((F ∘ expChartI p₀) 0) c := rfl
    rw [this, hΦ0]
    simp [logChart, hunit c, logSeries_one]
  · filter_upwards [hnear, hN] with Y hY hYN c
    have hin : F (expChartI p₀ Y) c ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
      hmaps (hform hYN) c
    refine ⟨hin, hY c, ?_⟩
    exact logSeries_div_I_mem hexp (mul_inv_mem_specialUnitary hin (hbase' c)) (hY c)
end ChartData
section Consequences
open YangMills.Construction.Matrices.PowerExpCharts
variable {L n k i : ℕ} [Fintype (PositiveEdge L n k (i + 1))] [Fintype (PositiveEdge L n k i)]
  [FiniteDimensional ℝ (edgeFormSpace L n k i)] {V : Edge L n k i → ComplexMatrix2}
theorem isClosed_hermitianTraceless :
    IsClosed (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.LeftChartFields.isClosed_hermitianTraceless <;> assumption
theorem contDiffAt_three (h : ChartedStepData V) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 3 (fun Y => chartedStepLog L n k i V Y c) 0 :=
  by exact_mod_cast contDiffAt_infty.mp (h.contDiff c) 3
theorem eventually_mem_hermitianTraceless (h : ChartedStepData V)
    (c : PositiveEdge L n k (i + 1)) :
    ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement),
      chartedStepLog L n k i V Y c ∈ ComplexMatrix2.hermitianTraceless :=
  h.eventually.mono fun _ hY => (hY c).2.2
theorem ofReal_smul_edgeForm (t : ℝ) (B : edgeFormSpace L n k i) :
    (t : ℂ) • (B : Edge L n k i → ComplexMatrix2) =
      ((t • B : edgeFormSpace L n k i) : Edge L n k i → ComplexMatrix2) := by
  funext b
  ext r s
  simp
theorem stepLog_ofReal_smul (hp : OrientationDichotomy L n k i) (hV : V ∈ fieldSpace L n k i)
    (c : PositiveEdge L n k (i + 1)) (t : ℝ) (B : edgeFormSpace L n k i) :
    stepLog V c ((t : ℂ) • (B : Edge L n k i → ComplexMatrix2)) =
      chartedStepLog L n k i V (t • positiveValues L n k i B) c := by
  rw [ofReal_smul_edgeForm, stepLog_eq_chartedStepLog hp hV, map_smul]
theorem logDirectionalDeriv_eq_fderiv (hp : OrientationDichotomy L n k i)
    (hV : V ∈ fieldSpace L n k i) (h : ChartedStepData V) (B : edgeFormSpace L n k i)
    (c : PositiveEdge L n k (i + 1)) :
    logDirectionalDeriv ℝ (fun X => smoothingStep L n k i (PeriodicLattice.expTwist X V) c.1)
        (smoothingStep L n k i V c.1) (B : Edge L n k i → ComplexMatrix2) =
      fderiv ℝ (fun Y => chartedStepLog L n k i V Y c) 0 (positiveValues L n k i B) := by
  unfold logDirectionalDeriv
  have hfun : (fun t : ℝ => ComplexMatrix2.logSeries (smoothingStep L n k i
      (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • (B : Edge L n k i → ComplexMatrix2)) V) c.1 *
        (smoothingStep L n k i V c.1)⁻¹)) =
      fun t => Complex.I • chartedStepLog L n k i V (t • positiveValues L n k i B) c := by
    funext t
    rw [← stepLog_ofReal_smul hp hV c t B]
    simp only [stepLog, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
    rfl
  have hd : HasDerivAt
      (fun t : ℝ => Complex.I • chartedStepLog L n k i V (t • positiveValues L n k i B) c)
      (Complex.I • fderiv ℝ (fun Y => chartedStepLog L n k i V Y c) 0
        (positiveValues L n k i B)) 0 :=
    (hasDerivAt_line_at_zero (contDiffAt_three h c) (positiveValues L n k i B)).const_smul
      Complex.I
  rw [hfun, hd.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem leftDifferential_eq (hp : OrientationDichotomy L n k i)
    (hp' : OrientationDichotomy L n k (i + 1)) (hV : V ∈ fieldSpace L n k i)
    (h : ChartedStepData V) (B : edgeFormSpace L n k i) :
    leftDifferential (smoothingStep L n k i) V (B : Edge L n k i → ComplexMatrix2) =
      edgeFormOfPositiveValues fun c =>
        fderiv ℝ (fun Y => chartedStepLog L n k i V Y c) 0 (positiveValues L n k i B) := by
  funext b
  unfold leftDifferential extendOddly edgeFormOfPositiveValues
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb, dif_pos hb]
    exact logDirectionalDeriv_eq_fderiv hp hV h B ⟨b, hb⟩
  · have h' := opposite_positive_of_not hp' hb
    rw [if_neg hb, dif_neg hb, dif_pos h']
    exact congrArg Neg.neg (logDirectionalDeriv_eq_fderiv hp hV h B ⟨b.opposite, h'⟩)
theorem leftDifferential_apply (hp : OrientationDichotomy L n k i)
    (hp' : OrientationDichotomy L n k (i + 1)) (hV : V ∈ fieldSpace L n k i)
    (h : ChartedStepData V) (B : edgeFormSpace L n k i) (c : PositiveEdge L n k (i + 1)) :
    leftDifferential (smoothingStep L n k i) V (B : Edge L n k i → ComplexMatrix2) c =
      fderiv ℝ (fun Y => chartedStepLog L n k i V Y c) 0 (positiveValues L n k i B) := by
  rw [leftDifferential_eq hp hp' hV h]
  simp only [edgeFormOfPositiveValues, dif_pos c.2]
theorem exists_linearMap_leftDifferential (hp : OrientationDichotomy L n k i)
    (hp' : OrientationDichotomy L n k (i + 1)) (hV : V ∈ fieldSpace L n k i)
    (h : ChartedStepData V) :
    ∃ T : edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k (i + 1), ∀ B : edgeFormSpace L n k i,
      (T B : Edge L n k (i + 1) → ComplexMatrix2) =
        leftDifferential (smoothingStep L n k i) V (B : Edge L n k i → ComplexMatrix2) := by
  let D : edgeFormSpace L n k i → PositiveEdge L n k (i + 1) → ComplexMatrix2 := fun B c =>
    fderiv ℝ (fun Y => chartedStepLog L n k i V Y c) 0 (positiveValues L n k i B)
  have hD : ∀ B, edgeFormOfPositiveValues (D B) ∈ edgeFormSpace L n k (i + 1) := fun B =>
    edgeFormOfPositiveValues_mem hp' fun c =>
      fderiv_zero_apply_mem ComplexMatrix2.hermitianTraceless isClosed_hermitianTraceless
        (contDiffAt_three h c) (eventually_mem_hermitianTraceless h c) _
  refine ⟨{ toFun := fun B => ⟨edgeFormOfPositiveValues (D B), hD B⟩
            map_add' := fun B B' => ?_
            map_smul' := fun t B => ?_ }, fun B => (leftDifferential_eq hp hp' hV h B).symm⟩
  · apply Subtype.ext
    have : D (B + B') = D B + D B' := by
      funext c
      simp [D]
    simp only [this, edgeFormOfPositiveValues_add]
    rfl
  · apply Subtype.ext
    have : D (t • B) = t • D B := by
      funext c
      simp [D]
    simp only [this, edgeFormOfPositiveValues_smul]
    rfl
theorem taylorCoeff_one (hp : OrientationDichotomy L n k i)
    (hp' : OrientationDichotomy L n k (i + 1)) (hV : V ∈ fieldSpace L n k i)
    (h : ChartedStepData V) (B : edgeFormSpace L n k i) (c : PositiveEdge L n k (i + 1)) :
    taylorCoeffAtZero 1 (stepLog V c) (B : Edge L n k i → ComplexMatrix2) =
        deriv (fun t : ℝ => stepLog V c ((t : ℂ) • (B : Edge L n k i → ComplexMatrix2))) 0 ∧
      deriv (fun t : ℝ => stepLog V c ((t : ℂ) • (B : Edge L n k i → ComplexMatrix2))) 0 =
        leftDifferential (smoothingStep L n k i) V (B : Edge L n k i → ComplexMatrix2) c := by
  refine ⟨by simp [taylorCoeffAtZero, iteratedDeriv_one], ?_⟩
  simp only [stepLog_ofReal_smul hp hV c _ B]
  rw [leftDifferential_apply hp hp' hV h]
  exact (hasDerivAt_line_at_zero (contDiffAt_three h c) (positiveValues L n k i B)).deriv
def hessianForm (V : Edge L n k i → ComplexMatrix2) : EdgeFormBilinear L n k i :=
  LinearMap.mk₂ ℝ
    (fun B B' c => hessianAtZero (fun Y => chartedStepLog L n k i V Y c)
      (positiveValues L n k i B) (positiveValues L n k i B'))
    (fun B₁ B₂ B' => by funext c; simp)
    (fun t B B' => by funext c; simp)
    (fun B B₁ B₂ => by funext c; simp)
    (fun t B B' => by funext c; simp)
theorem hessianForm_apply (B B' : edgeFormSpace L n k i) (c : PositiveEdge L n k (i + 1)) :
    hessianForm V B B' c = hessianAtZero (fun Y => chartedStepLog L n k i V Y c)
      (positiveValues L n k i B) (positiveValues L n k i B') := rfl
theorem isQuadraticExpansion_hessianForm (hp : OrientationDichotomy L n k i)
    (hp' : OrientationDichotomy L n k (i + 1)) (hV : V ∈ fieldSpace L n k i)
    (h : ChartedStepData V) : IsQuadraticExpansion V (hessianForm V) := by
  refine ⟨fun B B' => ?_, fun c => ?_⟩
  · funext c
    exact hessianAtZero_symm (contDiffAt_three h c) _ _
  · obtain ⟨C, r, hC, hr, hb⟩ := taylor_two_remainder (contDiffAt_three h c)
    refine ⟨C, ?_⟩
    have hball : ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement), ‖Y‖ < r := by
      filter_upwards
        [Metric.ball_mem_nhds (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement) hr]
        with Y hY
      simpa using hY
    have hev : ∀ᶠ B : edgeFormSpace L n k i in 𝓝 0, ‖positiveValues L n k i B‖ < r :=
      tendsto_positiveValues.eventually hball
    filter_upwards [hev] with B hB
    have hbound := hb _ hB
    simp only [h.vanishes c, sub_zero] at hbound
    rw [stepLog_eq_chartedStepLog hp hV, leftDifferential_apply hp hp' hV h, hessianForm_apply]
    refine hbound.trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_positiveValues_le B) 3) hC
theorem quadraticExpansion_unique {q q' : EdgeFormBilinear L n k i}
    (hq : IsQuadraticExpansion V q) (hq' : IsQuadraticExpansion V q') : q = q' := by
  have hdiag : ∀ (B : edgeFormSpace L n k i) (c : PositiveEdge L n k (i + 1)),
      q B B c = q' B B c := by
    intro B c
    obtain ⟨C₁, h₁⟩ := hq.2 c
    obtain ⟨C₂, h₂⟩ := hq'.2 c
    set x := q B B c - q' B B c with hx
    set β := edgeFormNorm (B : Edge L n k i → ComplexMatrix2) with hβ
    have hc : Tendsto (fun t : ℝ => t • B) (𝓝 0) (𝓝 (0 : edgeFormSpace L n k i)) := by
      have : Continuous fun t : ℝ => t • B := continuous_id.smul continuous_const
      simpa using this.tendsto 0
    have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) * ‖x‖ ≤ (C₁ + C₂) * β ^ 3 * t := by
      filter_upwards [((hc.eventually h₁).and (hc.eventually h₂)).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ⟨a₁, a₂⟩ ht
      have ht' : (0 : ℝ) < t := ht
      have hn : edgeFormNorm ((t • B : edgeFormSpace L n k i) : Edge L n k i → ComplexMatrix2) =
          t * β := by
        rw [edgeFormNorm_smul, abs_of_pos ht']
      rw [hn] at a₁ a₂
      have hqt : ∀ r : EdgeFormBilinear L n k i, r (t • B) (t • B) c = (t ^ 2) • r B B c := by
        intro r
        simp [smul_smul, pow_two]
      rw [hqt] at a₁
      rw [hqt] at a₂
      set w := stepLog V c ((t • B : edgeFormSpace L n k i) : Edge L n k i → ComplexMatrix2) -
        leftDifferential (smoothingStep L n k i) V
          ((t • B : edgeFormSpace L n k i) : Edge L n k i → ComplexMatrix2) c
        with hw
      have hdiff : ((1 / 2 : ℝ) * t ^ 2) • x =
          (w - (1 / 2 : ℝ) • (t ^ 2) • q' B B c) - (w - (1 / 2 : ℝ) • (t ^ 2) • q B B c) := by
        simp only [hx, smul_sub, smul_smul]
        abel
      have hnorm : (1 / 2 : ℝ) * t ^ 2 * ‖x‖ ≤ (C₁ + C₂) * (t * β) ^ 3 := by
        have h3 := norm_sub_le (w - (1 / 2 : ℝ) • (t ^ 2) • q' B B c)
          (w - (1 / 2 : ℝ) • (t ^ 2) • q B B c)
        rw [← hdiff, norm_smul, Real.norm_of_nonneg (by positivity)] at h3
        have a₁' : ‖w - (1 / 2 : ℝ) • (t ^ 2) • q B B c‖ ≤ C₁ * (t * β) ^ 3 := a₁
        have a₂' : ‖w - (1 / 2 : ℝ) • (t ^ 2) • q' B B c‖ ≤ C₂ * (t * β) ^ 3 := a₂
        linarith
      have ht2 : (0 : ℝ) < t ^ 2 := by positivity
      have hfin : t ^ 2 * ((1 / 2 : ℝ) * ‖x‖) ≤ t ^ 2 * ((C₁ + C₂) * β ^ 3 * t) := by
        calc t ^ 2 * ((1 / 2 : ℝ) * ‖x‖) = (1 / 2 : ℝ) * t ^ 2 * ‖x‖ := by ring
          _ ≤ (C₁ + C₂) * (t * β) ^ 3 := hnorm
          _ = t ^ 2 * ((C₁ + C₂) * β ^ 3 * t) := by ring
      exact le_of_mul_le_mul_left hfin ht2
    have hlim : Tendsto (fun t : ℝ => (C₁ + C₂) * β ^ 3 * t) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous fun t : ℝ => (C₁ + C₂) * β ^ 3 * t := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hle : (1 / 2 : ℝ) * ‖x‖ ≤ 0 := ge_of_tendsto hlim key
    have hx0 : ‖x‖ = 0 := le_antisymm (by linarith) (norm_nonneg x)
    exact sub_eq_zero.mp (norm_eq_zero.mp hx0)
  refine LinearMap.ext₂ fun B B' => ?_
  funext c
  have h₁ := hdiag (B + B') c
  simp only [map_add, LinearMap.add_apply, Pi.add_apply, hdiag B c, hdiag B' c] at h₁
  have hs : q B' B c = q B B' c := by rw [hq.1 B' B]
  have hs' : q' B' B c = q' B B' c := by rw [hq'.1 B' B]
  rw [hs, hs'] at h₁
  have h₂ : (2 : ℝ) • q B B' c = (2 : ℝ) • q' B B' c := by
    rw [two_smul, two_smul]
    have : q' B B c + q B B' c + (q B B' c + q' B' B' c) =
        q' B B c + q' B B' c + (q' B B' c + q' B' B' c) := h₁
    exact show q B B' c + q B B' c = q' B B' c + q' B B' c from by
      have := congrArg (fun X => X - q' B B c - q' B' B' c) this
      calc q B B' c + q B B' c
          = q' B B c + q B B' c + (q B B' c + q' B' B' c) - q' B B c - q' B' B' c := by abel
        _ = q' B B c + q' B B' c + (q' B B' c + q' B' B' c) - q' B B c - q' B' B' c := this
        _ = q' B B' c + q' B B' c := by abel
  exact smul_right_injective _ (two_ne_zero) h₂
theorem stepHasQuadraticExpansion (hp : OrientationDichotomy L n k i)
    (hp' : OrientationDichotomy L n k (i + 1)) (hV : V ∈ fieldSpace L n k i)
    (h : ChartedStepData V) : StepHasQuadraticExpansion V := by
  have hq₀ := isQuadraticExpansion_hessianForm hp hp' hV h
  refine ⟨⟨hessianForm V, hq₀, fun q hq => quadraticExpansion_unique hq hq₀⟩, fun q hq => ?_⟩
  obtain rfl := quadraticExpansion_unique hq hq₀
  refine ⟨fun B c => ?_, fun B B' c => ?_,
    fun B B' => edgeFormOfPositiveValues_mem hp' fun c => ?_⟩
  · simp only [taylorCoeffAtZero, stepLog_ofReal_smul hp hV c _ B]
    rw [iteratedDeriv_two_along_line (contDiffAt_three h c), hessianForm_apply]
    norm_num [Nat.factorial]
  · exact hessianAtZero_mem ComplexMatrix2.hermitianTraceless isClosed_hermitianTraceless
      (contDiffAt_three h c) (eventually_mem_hermitianTraceless h c) _ _
  · exact hessianAtZero_mem ComplexMatrix2.hermitianTraceless isClosed_hermitianTraceless
      (contDiffAt_three h c) (eventually_mem_hermitianTraceless h c) _ _
theorem eventually_stepLog_mem (hp : OrientationDichotomy L n k i)
    (hV : V ∈ fieldSpace L n k i) (h : ChartedStepData V) :
    ∀ᶠ B : edgeFormSpace L n k i in 𝓝 0, ∀ c : PositiveEdge L n k (i + 1),
      smoothingStep L n k i (PeriodicLattice.expTwist (B : Edge L n k i → ComplexMatrix2) V) c ∈
          PeriodicLattice.compactGaugeGroup ∧
        smoothingStep L n k i V c ∈ PeriodicLattice.compactGaugeGroup ∧
        smoothingStep L n k i (PeriodicLattice.expTwist (B : Edge L n k i → ComplexMatrix2) V) c *
          (smoothingStep L n k i V c)⁻¹ ∈ ComplexMatrix2.logBall ∧
        stepLog V c (B : Edge L n k i → ComplexMatrix2) ∈ ComplexMatrix2.hermitianTraceless := by
  filter_upwards [tendsto_positiveValues.eventually h.eventually] with B hB c
  obtain ⟨h₁, h₂, h₃⟩ := hB c
  rw [stepOnPositive_expChartI hp] at h₁ h₂
  rw [stepOnPositive_restrict hp hV] at h₂
  have hb := h.base_mem c
  rw [stepOnPositive_restrict hp hV] at hb
  exact ⟨h₁, hb, h₂, by rw [stepLog_eq_chartedStepLog hp hV]; exact h₃⟩
theorem stepLog_zero (hp : OrientationDichotomy L n k i) (hV : V ∈ fieldSpace L n k i)
    (h : ChartedStepData V) (c : PositiveEdge L n k (i + 1)) : stepLog V c 0 = 0 := by
  have := stepLog_eq_chartedStepLog hp hV (0 : edgeFormSpace L n k i) c
  rw [map_zero, h.vanishes c] at this
  simpa using this
end Consequences
section Continuation
open YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
variable {σ τ : Type}
def scalarMulMap (z : ℂ) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun X := z • X
  map_add' := smul_add z
  map_smul' w X := smul_comm z w X
def expChartOfAlgebra (V₀ : σ → ComplexMatrix2) (q : Empty ⊕ σ → ComplexMatrix2) :
    σ ⊕ Empty → ComplexMatrix2 :=
  Sum.elim (fun s => ComplexMatrix2.matExp (Complex.I • q (.inr s)) * V₀ s) Empty.elim
def continuedRatio (V₀ : σ → ComplexMatrix2)
    (Ψ : (σ ⊕ Empty → ComplexMatrix2) → τ ⊕ Empty → ComplexMatrix2) (c : τ)
    (M : ComplexMatrix2) (q : Empty ⊕ σ → ComplexMatrix2) : ComplexMatrix2 :=
  Ψ (expChartOfAlgebra V₀ q) (.inl c) * M
def continuedRatioDomain (V₀ : σ → ComplexMatrix2) (𝒳 : Set (σ ⊕ Empty → ComplexMatrix2))
    (Ψ : (σ ⊕ Empty → ComplexMatrix2) → τ ⊕ Empty → ComplexMatrix2) (c : τ)
    (M : ComplexMatrix2) : Set (Empty ⊕ σ → ComplexMatrix2) :=
  (GroupLieProduct Empty σ ∩ expChartOfAlgebra V₀ ⁻¹' 𝒳) ∩
    continuedRatio V₀ Ψ c M ⁻¹' ComplexMatrix2.logBall
theorem isOpen_logBall : IsOpen ComplexMatrix2.logBall :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
theorem continuedLog_holomorphic [Fintype σ] [Fintype τ]
    (hexp : ComplexMatrix2.ExpLogEstimates)
    (hops : GroupLieProduct.HolomorphyClosureStatement)
    (hH2 : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {V₀ : σ → ComplexMatrix2}
    (hV₀ : ∀ s, V₀ s ∈ ComplexMatrix2.unitDeterminant)
    {𝒳 : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Ψ : (σ ⊕ Empty → ComplexMatrix2) → τ ⊕ Empty → ComplexMatrix2}
    (hΨ : IsHolomorphicToProduct b 𝒳 Ψ) (c : τ) (M : ComplexMatrix2) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty σ)
        (continuedRatioDomain V₀ 𝒳 Ψ c M) ∧
      IsHolomorphicToMatrixEntries b (continuedRatioDomain V₀ 𝒳 Ψ c M)
        fun q => Complex.I⁻¹ • ComplexMatrix2.logSeries (continuedRatio V₀ Ψ c M q) := by
  have hprod := hH2.2.2.2.1
  have hcomp := hH2.2.2.2.2.1
  have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty σ)
      (GroupLieProduct Empty σ) :=
    ⟨univ, isOpen_univ, by simp⟩
  have hO₀ := hops Empty σ b _ hopen
  have hi : ∀ s, IsHolomorphicToMatrixEntries b (GroupLieProduct Empty σ)
      fun q => ComplexMatrix2.matExp (Complex.I • q (.inr s)) * V₀ s := fun s => by
    have h₁ : IsHolomorphicToMatrixEntries b (GroupLieProduct Empty σ)
        fun q => q (.inr s) := hO₀.2.1 (.inr s)
    have h₂ : IsHolomorphicToMatrixEntries b (GroupLieProduct Empty σ)
        fun q => Complex.I • q (.inr s) := hO₀.2.2.2.2.1 (scalarMulMap Complex.I) _ h₁
    have h₃ : IsHolomorphicToMatrixEntries b (GroupLieProduct Empty σ)
        fun q => ComplexMatrix2.matExp (Complex.I • q (.inr s)) := hO₀.2.2.2.2.2.2.1 _ h₂
    exact hO₀.2.2.2.1 _ _ h₃ (hO₀.1 (V₀ s))
  have hgroup : ∀ s, MapsTo
      (fun q : Empty ⊕ σ → ComplexMatrix2 => ComplexMatrix2.matExp (Complex.I • q (.inr s)) * V₀ s)
      (GroupLieProduct Empty σ) ComplexMatrix2.unitDeterminant := by
    intro s q hq
    have hq' : ComplexMatrix2.fullTrace (q (.inr s)) = 0 := hq (.inr s)
    have hV' : (V₀ s).det = 1 := hV₀ s
    change (ComplexMatrix2.matExp (Complex.I • q (.inr s)) * V₀ s).det = 1
    rw [Matrix.det_mul, hexp.2.2.2.2.2.1, hV']
    simp [ComplexMatrix2.fullTrace, Matrix.trace_smul] at hq' ⊢
    simp [hq']
  have hΞ : IsHolomorphicToProduct b (GroupLieProduct Empty σ) (expChartOfAlgebra V₀) :=
    ⟨hopen, fun s => ((hprod Empty σ).2.1 b _ _ hopen (hgroup s)).mpr (hi s),
      fun e => e.elim⟩
  have hΦ : IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv 𝒳
      fun p => Ψ p (.inl c) :=
    ((hprod σ Empty).2.1 b 𝒳 _ hΨ.1 (hΨ.2.1 c).2.1).mp (hΨ.2.1 c)
  have hC := hcomp Empty σ σ Empty b _ _ hopen hΞ ComplexMatrix2 4
    Coordinates.ComplexCoordinates.matrixEquiv 𝒳 (fun p => Ψ p (.inl c)) hΦ
  have hW₁ := hC.2.1
  have hO₁ := hops Empty σ b _ hW₁
  have h₂ : IsHolomorphicToMatrixEntries b
      (GroupLieProduct Empty σ ∩ expChartOfAlgebra V₀ ⁻¹' 𝒳)
      (continuedRatio V₀ Ψ c M) := hO₁.2.2.2.1 _ _ hC.2.2 (hO₁.1 M)
  have hW₂ : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty σ)
      (continuedRatioDomain V₀ 𝒳 Ψ c M) :=
    hO₁.2.2.2.2.2.2.2.2.1 _ h₂ ComplexMatrix2.logBall isOpen_logBall
  refine ⟨hW₂, ?_⟩
  have hO₂ := hops Empty σ b _ hW₂
  have h₃ : IsHolomorphicToMatrixEntries b (continuedRatioDomain V₀ 𝒳 Ψ c M)
      (continuedRatio V₀ Ψ c M) :=
    hO₁.2.2.2.2.2.2.2.2.2.1 _ inter_subset_left hW₂ _ h₂
  have h₄ : IsHolomorphicToMatrixEntries b (continuedRatioDomain V₀ 𝒳 Ψ c M)
      fun q => ComplexMatrix2.logSeries (continuedRatio V₀ Ψ c M q) :=
    hO₂.2.2.2.2.2.2.2.1 _ h₃ fun q hq => hq.2
  exact hO₂.2.2.2.2.1 (scalarMulMap Complex.I⁻¹) _ h₄
end Continuation
section RealAnalytic
open YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
variable {L n k i : ℕ} [Fintype (PositiveEdge L n k i)]
theorem stepLog_isAnalyticNearZero (hexp : ComplexMatrix2.ExpLogEstimates)
    (hops : GroupLieProduct.HolomorphyClosureStatement)
    (hH2 : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hconf : ∀ B ∈ edgeFormSpace L n k i, ∀ V ∈ fieldSpace L n k i,
      PeriodicLattice.expTwist B V ∈ fieldSpace L n k i)
    (hp : OrientationDichotomy L n k i) {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) (b₀ : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    [Fintype (PositiveEdge L n k (i + 1))]
    {𝒳 : Set (PositiveEdge L n k i ⊕ Empty → ComplexMatrix2)}
    {Ψ : (PositiveEdge L n k i ⊕ Empty → ComplexMatrix2) →
      PositiveEdge L n k (i + 1) ⊕ Empty → ComplexMatrix2}
    (hpt : asGroupFactors (restrictToPositiveEdges V) ∈ 𝒳)
    (hΨ : ∀ b, IsHolomorphicToProduct b 𝒳 Ψ)
    (heq : EqOn Ψ (fun q => ofParts (restrictToPositiveEdges (smoothingStep L n k i
      (fieldOfPositiveValues (groupComponent q)))) Empty.elim)
      (𝒳 ∩ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) (PositiveEdge L n k i)))
    (c : PositiveEdge L n k (i + 1))
    (hc : smoothingStep L n k i V c ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    IsAnalyticNearZero (stepLog V c) := by
  have hVG : ∀ b : Edge L n k i, V b ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
    fun b => (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ V
      from hV).1 b (mem_univ _)
  obtain ⟨V₀, hV₀d⟩ : ∃ V₀, V₀ = restrictToPositiveEdges V := ⟨_, rfl⟩
  rw [← hV₀d] at hpt
  obtain ⟨M, hM⟩ : ∃ M, M = (smoothingStep L n k i V c)⁻¹ := ⟨_, rfl⟩
  have hV₀ : ∀ s, V₀ s ∈ ComplexMatrix2.unitDeterminant := fun s => by
    rw [hV₀d]
    exact (Matrix.mem_specialUnitaryGroup_iff.mp (hVG s.1)).2
  have hhol := fun b => continuedLog_holomorphic hexp hops hH2 b hV₀ (hΨ b) c M
  have key : ∀ q ∈ subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k i)) Empty,
      expChartOfAlgebra V₀ q ∈ 𝒳 → continuedRatio V₀ Ψ c M q =
        smoothingStep L n k i
          (PeriodicLattice.expTwist (edgeFormOfPositiveValues (algebraComponent q)) V) c * M := by
    intro q hq hx
    set A := edgeFormOfPositiveValues (algebraComponent q) with hAd
    have hA : A ∈ edgeFormSpace L n k i :=
      edgeFormOfPositiveValues_mem hp fun b => hq.1 b (mem_univ b)
    have hAval : ∀ s : PositiveEdge L n k i, A s.1 = q (.inr s) := fun s => by
      simp only [hAd, edgeFormOfPositiveValues, dif_pos s.2]
      rfl
    have hgp : groupComponent (expChartOfAlgebra V₀ q) =
        fun s : PositiveEdge L n k i => ComplexMatrix2.matExp (Complex.I • A s.1) * V s.1 := by
      funext s
      simp only [groupComponent, expChartOfAlgebra, Sum.elim_inl, hAval, hV₀d]
      rfl
    have hcfg : fieldOfPositiveValues (groupComponent (expChartOfAlgebra V₀ q)) =
        PeriodicLattice.expTwist A V := by
      rw [hgp, fieldOfPositiveValues_expTwist hp]
    have hreal : expChartOfAlgebra V₀ q ∈
        subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) (PositiveEdge L n k i) := by
      refine ⟨(Submodule.mem_bot ℝ).mpr (funext fun e => e.elim), fun s => ?_⟩
      have hmem := (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ
        (PeriodicLattice.expTwist A V) from hconf A hA V hV).1 s.1 (mem_univ _)
      have hval : PeriodicLattice.expTwist A V s.1 =
          ComplexMatrix2.matExp (Complex.I • A s.1) * V s.1 := by
        simp [PeriodicLattice.expTwist, s.2]
      rw [hval] at hmem
      rw [hgp]
      exact hmem
    have h₁ : Ψ (expChartOfAlgebra V₀ q) = ofParts (restrictToPositiveEdges (smoothingStep L n k i
        (fieldOfPositiveValues (groupComponent (expChartOfAlgebra V₀ q))))) Empty.elim :=
      heq ⟨hx, hreal⟩
    rw [hcfg] at h₁
    rw [continuedRatio, h₁]
    rfl
  have hchart0 : expChartOfAlgebra V₀ (ofParts Empty.elim 0) = asGroupFactors V₀ := by
    funext x
    cases x with
    | inl s => simp [expChartOfAlgebra, ofParts, asGroupFactors]
    | inr e => exact e.elim
  have hreal₀ : asGroupFactors V₀ ∈
      subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) (PositiveEdge L n k i) :=
    ⟨(Submodule.mem_bot ℝ).mpr (funext fun e => e.elim), fun s => by
      rw [hV₀d]
      exact hVG s.1⟩
  have hΨ₀ : Ψ (asGroupFactors V₀) (.inl c) = smoothingStep L n k i V c := by
    have h₁ : Ψ (asGroupFactors V₀) = ofParts (restrictToPositiveEdges (smoothingStep L n k i
        (fieldOfPositiveValues (groupComponent (asGroupFactors V₀))))) Empty.elim :=
      heq ⟨hpt, hreal₀⟩
    have hg : fieldOfPositiveValues (groupComponent (asGroupFactors V₀)) = V := by
      rw [hV₀d]
      exact fieldOfPositiveValues_restrict hp hV
    rw [h₁, hg]
    rfl
  have hunit : smoothingStep L n k i V c * M = 1 := by
    rw [hM]
    exact Matrix.mul_nonsing_inv _ (by
      rw [(Matrix.mem_specialUnitaryGroup_iff.mp hc).2]
      exact isUnit_one)
  have hq₀W : ofParts Empty.elim 0 ∈ continuedRatioDomain V₀ 𝒳 Ψ c M := by
    refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
    · cases x with
      | inl e => exact e.elim
      | inr s => exact ComplexMatrix2.traceless.zero_mem
    · change expChartOfAlgebra V₀ _ ∈ 𝒳
      rw [hchart0]
      exact hpt
    · change continuedRatio V₀ Ψ c M _ ∈ ComplexMatrix2.logBall
      rw [continuedRatio, hchart0, hΨ₀, hunit]
      simp [ComplexMatrix2.logBall]
  have hq₀R : ofParts Empty.elim 0 ∈
      subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k i)) Empty :=
    ⟨Submodule.zero_mem _, fun e => e.elim⟩
  have hsub : ∀ q ∈ subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k i)) Empty,
      q ∈ GroupLieProduct Empty (PositiveEdge L n k i) := by
    intro q hq x
    cases x with
    | inl e => exact e.elim
    | inr s => exact (hq.1 s (mem_univ s)).2
  obtain ⟨O, hO, hWO⟩ := (hhol b₀).1
  refine ⟨inferInstance, continuedRatioDomain V₀ 𝒳 Ψ c M ∩
      subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k i)) Empty, ⟨hq₀W, hq₀R⟩,
    ⟨le_rfl, O, hO, ?_⟩, fun p hpW => ⟨continuedRatioDomain V₀ 𝒳 Ψ c M, hpW.1, (hhol b₀).1,
      subset_rfl, fun q => Coordinates.ComplexCoordinates.matrixEquiv
        (Complex.I⁻¹ • ComplexMatrix2.logSeries (continuedRatio V₀ Ψ c M q)), fun b => (hhol b).2,
      fun q hq => ?_⟩⟩
  · rw [hWO]
    ext q
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hsub q h.2⟩, h.2⟩⟩
  · change Coordinates.ComplexCoordinates.matrixEquiv _ =
      Coordinates.ComplexCoordinates.matrixEquiv _
    rw [key q hq.2 hq.1.1.2, hM]
    rfl
end RealAnalytic
section NearIdentity
variable {L n k i : ℕ}
theorem eventually_mem_of_isOpenNhdOfOne (hp : OrientationDichotomy L n k i)
    {𝒰 : Set (Edge L n k i → ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2)), V ∈ 𝒰 := by apply _root_.YangMills.Construction.Tower.IterLeftChart.eventually_mem_of_isOpenNhdOfOne <;> assumption
end NearIdentity
end LeftChartStep
open LeftChartStep YangMills.Construction.Matrices.GroupLieProduct
  YangMills.Construction.Matrices.GroupLieProduct.Subspaces
  YangMills.Construction.Matrices.PowerExpCharts in
theorem leftChartStepExpansion_holds
    (hAvg : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hVal : SmoothingNearTrivialField)
    (hChart : PowerExpCharts.ExpChartsStatement)
    (hCfg : BondSetFields.ProductStructureHolds)
    (hForms : FiniteSideFormSpaces)
    (hExp : ComplexMatrix2.ExpLogEstimates)
    (hPauli : OneLoop.PauliMatrixRelations)
    (hOps : GroupLieProduct.HolomorphyClosureStatement)
    (hH2 : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hPos : PeriodicLattice.LevelBondOrientationDichotomy) :
    LeftChartStepExpansion := by
  intro L n k i hL hn hik
  have hk : 0 < k := by omega
  have hp : OrientationDichotomy L n k i := hPos L n k hL hn hk i (by omega)
  have hp' : OrientationDichotomy L n k (i + 1) := hPos L n k hL hn hk (i + 1) hik
  have := (hForms L n k i hL hn (by omega)).2.1
  have hconf : ∀ B ∈ edgeFormSpace L n k i, ∀ V ∈ fieldSpace L n k i,
      PeriodicLattice.expTwist B V ∈ fieldSpace L n k i :=
    (hVal L n k hL hn hk).2 i (by omega)
  obtain ⟨𝒰, h𝒰, hAn, -⟩ := ((hAvg.1 L hL).1 n k i hn hik).1.analytic
  obtain ⟨-, hMaps, fP, fQ, -, -, -, hRA⟩ := hAn
  have hne : ∀ j, j ≤ k → OrientationDichotomy L n k j → Nonempty (PositiveEdge L n k j) := by
    intro j hj hpj
    obtain ⟨b, -⟩ := ((hCfg L hL k j hj).1 n hn).2.2.1
    by_cases hb : b.IsPositivelyOriented
    · exact ⟨⟨b, hb⟩⟩
    · exact ⟨⟨b.opposite, opposite_positive_of_not hpj hb⟩⟩
  have := hne i (by omega) hp
  have := hne (i + 1) hik hp'
  obtain ⟨-, -, -, ⟨b₀, -⟩, -⟩ := hPauli
  have hCh := hChart (PositiveEdge L n k i) (PositiveEdge L n k (i + 1))
  have hCh' := (hChart (PositiveEdge L n k (i + 1)) (PositiveEdge L n k i)).1
  have hOopen : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := h𝒰.1.2
  have hcv : ∀ U ∈ 𝒰, fieldOfPositiveValues (restrictToPositiveEdges U) = U := fun U hU =>
    fieldOfPositiveValues_restrict hp (h𝒰.1.1 hU)
  have hmapsO : MapsTo (stepOnPositive L n k i) (restrictToPositiveEdges '' 𝒰)
      (specialUnitaryPower (PositiveEdge L n k (i + 1))) := by
    rintro _ ⟨U, hU, rfl⟩ c
    have hm := hMaps hU
    change smoothingStep L n k i (fieldOfPositiveValues (restrictToPositiveEdges U)) c.1 ∈
      ComplexMatrix2.specialUnitary
    rw [hcv U hU]
    exact (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ _ from hm).1
      c.1 (mem_univ _)
  have hgp : ∀ U ∈ 𝒰, asGroupFactors (restrictToPositiveEdges U) ∈
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := fun U hU => by
    change fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
    rw [hcv U hU]
    exact hU
  have hR : IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b₀) asGroupFactors
      (restrictToPositiveEdges '' 𝒰) (stepOnPositive L n k i) := by
    rintro _ ⟨U, hU, rfl⟩
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, hEq⟩ := hRA _ (hgp U hU)
    refine ⟨𝒳, Ψ, hp𝒳, hΨ b₀, fun x hx hxX => ?_⟩
    have hxG : x ∈ specialUnitaryPower (PositiveEdge L n k i) := by
      obtain ⟨U', hU', rfl⟩ := hx
      exact fun b => (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U'
        from h𝒰.1.1 hU').1 b.1 (mem_univ _)
    exact hEq ⟨hxX, (Submodule.mem_bot ℝ).mpr (funext fun e => e.elim), hxG⟩
  have h4 := ((hCh.2.2.2.2.2.2.2 b₀).1 _ hOopen).2.2.2 _ hmapsO hR
  change ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2)), _
  filter_upwards [eventually_mem_of_isOpenNhdOfOne hp h𝒰, self_mem_nhdsWithin] with V hV hVc
  have hcf : ChartedStepData V := chartedStepData_of hExp hCh' hmapsO h4.1 ⟨V, hV, rfl⟩
  obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, hEq⟩ := hRA _ (hgp V hV)
  have hval : ∀ c : PositiveEdge L n k (i + 1),
      smoothingStep L n k i V c ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := fun c =>
    (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ _ from hMaps hV).1
      c.1 (mem_univ _)
  exact ⟨⟨eventually_stepLog_mem hp hVc hcf, fun c =>
      ⟨stepLog_isAnalyticNearZero hExp hOps hH2 hconf hp hVc b₀ hp𝒳 hΨ hEq c (hval c),
        stepLog_zero hp hVc hcf c⟩⟩,
    ⟨⟨𝒰, hV, h𝒰.1, hMaps, fP, fQ, h4.2⟩, exists_linearMap_leftDifferential hp hp' hVc hcf,
      fun B c => taylorCoeff_one hp hp' hVc hcf B c⟩,
    stepHasQuadraticExpansion hp hp' hVc hcf⟩
end Tower
end YangMills.Construction
end
