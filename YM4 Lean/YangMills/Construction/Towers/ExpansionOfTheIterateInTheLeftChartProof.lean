import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfGProof
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscs
import YangMills.Construction.Towers.FibresOfTheAveragingMaps
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
open Matrices
namespace IterLeftChart
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
def secondFDerivAtZero (g : E → F) : E →L[ℝ] E →L[ℝ] F := fderiv ℝ (fderiv ℝ g) 0
theorem secondFDerivAtZero_symm {g : E → F} (hg : ContDiffAt ℝ 3 g 0) (a b : E) :
    secondFDerivAtZero g a b = secondFDerivAtZero g b a :=
  (hg.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq a b
theorem differentiableAt_fderiv_of_contDiffAt_three {g : E → F} {z : E}
    (hg : ContDiffAt ℝ 3 g z) : DifferentiableAt ℝ (fderiv ℝ g) z :=
  (hg.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
theorem hasDerivAt_comp_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G}
    (y : E) {t : ℝ} (hf : DifferentiableAt ℝ f (t • y)) :
    HasDerivAt (fun s : ℝ => f (s • y)) (fderiv ℝ f (t • y) y) t := by
  have h₁ : HasDerivAt (fun s : ℝ => s • y) y t := by
    simpa using (hasDerivAt_id t).smul_const y
  exact hf.hasFDerivAt.comp_hasDerivAt t h₁
theorem hasDerivAt_comp_smul_zero {g : E → F} (hg : ContDiffAt ℝ 3 g 0) (y : E) :
    HasDerivAt (fun s : ℝ => g (s • y)) (fderiv ℝ g 0 y) 0 := by
  have h := hasDerivAt_comp_smul (f := g) y (t := 0) (by
    simpa using hg.differentiableAt (by norm_num))
  simpa using h
theorem hasDerivAt_fderiv_comp_smul {g : E → F} (hg : ContDiffAt ℝ 3 g 0) (y y' : E) :
    HasDerivAt (fun s : ℝ => fderiv ℝ g (s • y) y') (secondFDerivAtZero g y y') 0 := by
  have h := hasDerivAt_comp_smul (f := fderiv ℝ g) y (t := 0) (by
    simpa using differentiableAt_fderiv_of_contDiffAt_three hg)
  have h' := h.clm_apply (hasDerivAt_const (0 : ℝ) y')
  simpa [secondFDerivAtZero] using h'
theorem iteratedDeriv_two_comp_smul {g : E → F} (hg : ContDiffAt ℝ 3 g 0) (y : E) :
    iteratedDeriv 2 (fun s : ℝ => g (s • y)) 0 = secondFDerivAtZero g y y := by
  have hev : ∀ᶠ z in 𝓝 (0 : E), ContDiffAt ℝ 3 g z := hg.eventually (by simp)
  have hc : Tendsto (fun s : ℝ => s • y) (𝓝 0) (𝓝 (0 : E)) := by
    have : Continuous fun s : ℝ => s • y := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have heq : deriv (fun s : ℝ => g (s • y)) =ᶠ[𝓝 0] fun s => fderiv ℝ g (s • y) y := by
    filter_upwards [hc.eventually hev] with s hs
    exact (hasDerivAt_comp_smul y (hs.differentiableAt (by norm_num))).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  exact (hasDerivAt_fderiv_comp_smul hg y y).deriv
theorem taylor_two_remainder {g : E → F} (hg : ContDiffAt ℝ 3 g 0) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ y : E, ‖y‖ < r →
      ‖g y - g 0 - fderiv ℝ g 0 y - (1 / 2 : ℝ) • secondFDerivAtZero g y y‖ ≤ C * ‖y‖ ^ 3 := by
  set D₁ := fderiv ℝ g with hD₁
  set D₂ := fderiv ℝ D₁ with hD₂
  set Q := secondFDerivAtZero g with hQ
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
    exact secondFDerivAtZero_symm hg w z
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
end Calculus
section Edges
variable {L n k i : ℕ}
def EdgeOrientationDichotomy (L n k i : ℕ) : Prop :=
  ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem opposite_pos_of_not_pos (hp : EdgeOrientationDichotomy L n k i) {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases hp b with ⟨h, _⟩ | ⟨h, _⟩
  · exact absurd h hb
  · exact h
theorem not_opposite_pos_of_pos (hp : EdgeOrientationDichotomy L n k i) {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases hp b with ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · exact absurd hb h
theorem edge_opposite_opposite (b : Edge L n k i) : b.opposite.opposite = b := rfl
theorem fieldOfPositiveValues_restrict (hp : EdgeOrientationDichotomy L n k i)
    {𝒢 : Set ComplexMatrix2} {U : Edge L n k i → ComplexMatrix2} (hU : U ∈ fieldsIn L n k i 𝒢) :
    fieldOfPositiveValues (restrictToPositiveEdges U) = U := by
  funext b
  unfold fieldOfPositiveValues
  by_cases h : b.IsPositivelyOriented
  · simp [h, restrictToPositiveEdges]
  · have h' := opposite_pos_of_not_pos hp h
    rw [dif_neg h, dif_pos h']
    have hrev : U b.opposite.opposite = (U b.opposite)⁻¹ :=
      (show PeriodicLattice.IsGaugeField 𝒢 univ U from hU).2 b.opposite (mem_univ _)
    rw [edge_opposite_opposite] at hrev
    exact hrev.symm
theorem fieldOfPositiveValues_expMul (hp : EdgeOrientationDichotomy L n k i)
    (A V : Edge L n k i → ComplexMatrix2) :
    fieldOfPositiveValues (fun b : PositiveEdge L n k i =>
        ComplexMatrix2.matExp (Complex.I • A b.1) * V b.1) =
      PeriodicLattice.expTwist A V := by
  funext b
  unfold fieldOfPositiveValues PeriodicLattice.expTwist
  by_cases h : b.IsPositivelyOriented
  · simp [h]
  · have h' := opposite_pos_of_not_pos hp h
    simp [h, h']
theorem edgeFormOfPositiveValues_add (w w' : PositiveEdge L n k i → ComplexMatrix2) :
    edgeFormOfPositiveValues (w + w') =
      edgeFormOfPositiveValues w + edgeFormOfPositiveValues w' := by
  funext b
  simp only [edgeFormOfPositiveValues, Pi.add_apply]
  split_ifs <;> simp [add_comm]
theorem edgeFormOfPositiveValues_smul (t : ℝ) (w : PositiveEdge L n k i → ComplexMatrix2) :
    edgeFormOfPositiveValues (t • w) = t • edgeFormOfPositiveValues w := by
  funext b
  simp only [edgeFormOfPositiveValues, Pi.smul_apply]
  split_ifs <;> simp
theorem edgeFormOfPositiveValues_mem (hp : EdgeOrientationDichotomy L n k i)
    {w : PositiveEdge L n k i → ComplexMatrix2} (hw : ∀ b, w b ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k i := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [edgeFormOfPositiveValues, dif_pos hb]
    exact hw _
  · by_cases h : b.IsPositivelyOriented
    · have h' := not_opposite_pos_of_pos hp h
      have h'' : b.opposite.opposite.IsPositivelyOriented := by
        rwa [edge_opposite_opposite]
      simp only [edgeFormOfPositiveValues, dif_pos h, dif_neg h', dif_pos h'']
      rfl
    · have h' := opposite_pos_of_not_pos hp h
      simp only [edgeFormOfPositiveValues, dif_neg h, dif_pos h', neg_neg]
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
      |t| * edgeFormNorm (B : Edge L n k i → ComplexMatrix2) := by
  rw [edgeFormNorm_eq_sqrt, edgeFormNorm_eq_sqrt]
  have : ∀ b, ‖positiveValues L n k i (t • B) b‖ ^ 2 =
      t ^ 2 * ‖positiveValues L n k i B b‖ ^ 2 := fun b => by
    rw [map_smul, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [this, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
end Edges
section Iterate
open PowerExpCharts
variable {L n k : ℕ}
def complexIterOnValues (L n k : ℕ) (w : PositiveEdge L n k 0 → ComplexMatrix2) :
    PositiveEdge L n k k → ComplexMatrix2 :=
  restrictToPositiveEdges (PeriodicLattice.complexBlockFieldAtLevel k (fieldOfPositiveValues w))
def realIterOnValues (L n k : ℕ) (w : PositiveEdge L n k 0 → ComplexMatrix2) :
    PositiveEdge L n k k → ComplexMatrix2 :=
  restrictToPositiveEdges (smoothingIter L n k k (fieldOfPositiveValues w))
def iterLogInChart (L n k : ℕ) (V : Edge L n k 0 → ComplexMatrix2)
    (Y : PositiveEdge L n k 0 → ComplexMatrix2.LieElement) (c : PositiveEdge L n k k) :
    ComplexMatrix2 :=
  logChart (complexIterOnValues L n k (restrictToPositiveEdges V))
    (complexIterOnValues L n k (expChartI (restrictToPositiveEdges V) Y)) c
theorem expChartI_positiveValues {i : ℕ} (V : Edge L n k i → ComplexMatrix2)
    (B : edgeFormSpace L n k i) :
    expChartI (restrictToPositiveEdges V) (positiveValues L n k i B) =
      fun b : PositiveEdge L n k i => ComplexMatrix2.matExp (Complex.I • B.1 b.1) * V b.1 := rfl
theorem complexIterOnValues_expChartI (hp : EdgeOrientationDichotomy L n k 0)
    (V : Edge L n k 0 → ComplexMatrix2) (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) :
    complexIterOnValues L n k (expChartI (restrictToPositiveEdges V) (positiveValues L n k 0 B)) c =
      PeriodicLattice.complexBlockFieldAtLevel k
        (PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) V) c := by
  rw [expChartI_positiveValues, complexIterOnValues, fieldOfPositiveValues_expMul hp]
  rfl
theorem complexIterOnValues_restrict (hp : EdgeOrientationDichotomy L n k 0)
    {V : Edge L n k 0 → ComplexMatrix2} (hV : V ∈ fieldSpace L n k 0) (c : PositiveEdge L n k k) :
    complexIterOnValues L n k (restrictToPositiveEdges V) c =
      PeriodicLattice.complexBlockFieldAtLevel k V c := by
  rw [complexIterOnValues,
    fieldOfPositiveValues_restrict hp (𝒢 := PeriodicLattice.compactGaugeGroup) hV]
  rfl
theorem iterLogRatio_eq (hp : EdgeOrientationDichotomy L n k 0) {V : Edge L n k 0 → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k 0) (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) :
    iterLogRatio V c (B : Edge L n k 0 → ComplexMatrix2) =
      iterLogInChart L n k V (positiveValues L n k 0 B) c := by
  simp only [iterLogRatio, iterLogInChart, logChart]
  rw [complexIterOnValues_expChartI hp, complexIterOnValues_restrict hp hV, one_div]
end Iterate
section Defined
open LevelwiseMeans MeanStableFields
variable {L n k : ℕ}
def IteratesDefined (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) : Prop :=
  ∀ i ≤ k, smoothingIter L n k i U ∈ fieldSpace L n k i ∧
    (∀ b, ComplexMatrix2.operatorNorm (smoothingIter L n k i U b - 1) < polydiscRadius L) ∧
    ∀ c, levelwiseMean U i c = some (smoothingIter L n k i U c)
theorem fieldsIn_complex_of_mem {i : ℕ} {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) :
    V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
theorem isMeanSequence {U : Edge L n k 0 → ComplexMatrix2} (hF : IteratesDefined L n k U) :
    IsMeanSequence k fun i => smoothingIter L n k i U where
  mem_fields i hi := fieldsIn_complex_of_mem (hF i hi).1
  norm_sub_one_lt i hi := (hF i hi.le).2.1
  eq_mean i hi c hc := by
    have h₁ := (hF (i + 1) hi).2.2 c
    have h₂ := (hF i hi.le).2.2
    have hfv : valuesOrOne (levelwiseMean U i) = smoothingIter L n k i U := by
      funext b
      simp [valuesOrOne, h₂ b]
    have h₃ : meanOfDefined (levelwiseMean U i) c =
        some (smoothingIter L n k (i + 1) U c) := by
      rw [← h₁]
      simp only [levelwiseMean, if_pos hc]
    simp only [meanOfDefined] at h₃
    split_ifs at h₃ with h
    rw [hfv] at h₃
    exact (Option.some.inj h₃).symm
theorem meanSequence_eq (hO : IteratedMeans.TorusConditions L n k)
    {W : Edge L n k 0 → ComplexMatrix2} {V : ∀ i : ℕ, Edge L n k i → ComplexMatrix2}
    (hb : IsMeanSequenceFrom k W V) :
    ∀ i ≤ k, V i = PeriodicLattice.complexBlockFieldAtLevel i W := by
  intro i
  induction i with
  | zero => exact fun _ => hb.2
  | succ i ih =>
    intro hi
    have hi' : i < k := hi
    have hw : V i ∈ fieldsNearOne L n k i :=
      ⟨hb.1.mem_fields i hi'.le, hb.1.norm_sub_one_lt i hi'⟩
    have h := (hO.meanStep_unique i hi' (V i) hw (V (i + 1))
      (hb.1.mem_fields (i + 1) hi)).mp (hb.1.eq_mean i hi')
    rw [h, ih hi'.le]
    rfl
theorem meanStable_props (hO : IteratedMeans.TorusConditions L n k)
    (hP : MeanStableFields.MeanStableConditions L n k)
    {W : Edge L n k 0 → ComplexMatrix2} (hW : W ∈ meanStableFields L n k k) :
    W ∈ smallIterateFields L n k ∧
      ∀ c, levelwiseMeanAt k c W = PeriodicLattice.complexBlockFieldAtLevel k W c := by
  obtain ⟨V, hb⟩ := hW
  have heq := meanSequence_eq hO hb
  refine ⟨⟨?_, fun j hj => ?_⟩, fun c => ?_⟩
  · have h := hb.1.mem_fields 0 (Nat.zero_le _)
    rwa [hb.2] at h
  · rw [← heq j hj.le]
    exact ⟨hb.1.mem_fields j hj.le, hb.1.norm_sub_one_lt j hj⟩
  · have h := hP.eq_levelwiseMean k le_rfl W V hb k le_rfl c
    simp [levelwiseMeanAt, valuesOrOne, h, heq k le_rfl]
theorem iteratesDefined_props (hO : IteratedMeans.TorusConditions L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hF : IteratesDefined L n k U) :
    U ∈ meanStableFields L n k k ∧
      ∀ c, PeriodicLattice.complexBlockFieldAtLevel k U c = smoothingIter L n k k U c := by
  have h₀ : smoothingIter L n k 0 U = U := by
    funext c
    have h := (hF 0 (Nat.zero_le _)).2.2 c
    simp only [levelwiseMean] at h
    exact (Option.some.inj h).symm
  have hb : IsMeanSequenceFrom k U fun i => smoothingIter L n k i U := ⟨isMeanSequence hF, h₀⟩
  exact ⟨⟨_, hb⟩, fun c => by rw [← meanSequence_eq hO hb k le_rfl]⟩
end Defined
section Curves
open MeanStableFields
variable {L n k i : ℕ}
theorem continuousAt_matrix_inv {A : ComplexMatrix2} (hA : IsUnit A.det) :
    ContinuousAt (fun X : ComplexMatrix2 => X⁻¹) A := by
  have h₁ : ContinuousAt (fun X : ComplexMatrix2 => Ring.inverse X.det) A := by
    simp only [Ring.inverse_eq_inv']
    exact (Continuous.matrix_det continuous_id).continuousAt.inv₀ hA.ne_zero
  simp only [Matrix.inv_def]
  exact h₁.smul (Continuous.matrix_adjugate continuous_id).continuousAt
theorem continuous_matExp : Continuous ComplexMatrix2.matExp := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.continuous_matExp <;> assumption
theorem continuous_expMul (b : Edge L n k i) (M : ComplexMatrix2) :
    Continuous fun B : edgeFormSpace L n k i =>
      ComplexMatrix2.matExp (Complex.I • (B : Edge L n k i → ComplexMatrix2) b) * M := by
  have h₁ : Continuous fun B : edgeFormSpace L n k i => (B : Edge L n k i → ComplexMatrix2) b :=
    (continuous_apply b).comp continuous_subtype_val
  have h₂ : Continuous fun B : edgeFormSpace L n k i =>
      ComplexMatrix2.matExp (Complex.I • (B : Edge L n k i → ComplexMatrix2) b) :=
    continuous_matExp.comp (h₁.const_smul Complex.I)
  exact h₂.mul continuous_const
theorem tendsto_expMul (b : Edge L n k i) (M : ComplexMatrix2) :
    Tendsto (fun B : edgeFormSpace L n k i =>
        ComplexMatrix2.matExp (Complex.I • (B : Edge L n k i → ComplexMatrix2) b) * M)
      (𝓝 0) (𝓝 M) := by
  simpa using (continuous_expMul (L := L) (n := n) (k := k) (i := i) b M).tendsto 0
theorem tendsto_expTwist
    (hconf : ∀ B ∈ edgeFormSpace L n k i, ∀ V ∈ fieldSpace L n k i,
      PeriodicLattice.expTwist B V ∈ fieldSpace L n k i)
    {U : Edge L n k i → ComplexMatrix2} (hU : U ∈ fieldSpace L n k i) :
    Tendsto (fun B : edgeFormSpace L n k i =>
        PeriodicLattice.expTwist (B : Edge L n k i → ComplexMatrix2) U) (𝓝 0)
      (𝓝[fieldSpace L n k i] U) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_pi_nhds.mpr fun b => ?_,
    Eventually.of_forall fun B => hconf B B.2 U hU⟩
  have hU' := fieldsIn_complex_of_mem hU
  by_cases h : b.IsPositivelyOriented
  · have he : (fun B : edgeFormSpace L n k i =>
        PeriodicLattice.expTwist (B : Edge L n k i → ComplexMatrix2) U b) =
        fun B : edgeFormSpace L n k i =>
          ComplexMatrix2.matExp (Complex.I • (B : Edge L n k i → ComplexMatrix2) b) * U b := by
      funext B
      simp [PeriodicLattice.expTwist, h]
    rw [he]
    exact tendsto_expMul b (U b)
  · have he : (fun B : edgeFormSpace L n k i =>
        PeriodicLattice.expTwist (B : Edge L n k i → ComplexMatrix2) U b) =
        fun B : edgeFormSpace L n k i =>
          (ComplexMatrix2.matExp (Complex.I • (B : Edge L n k i → ComplexMatrix2) b.opposite) *
            U b.opposite)⁻¹ := by
      funext B
      simp [PeriodicLattice.expTwist, h]
    have hdet : IsUnit (U b.opposite).det := by
      have h₁ : (U b.opposite).det = 1 := hU'.1 b.opposite (mem_univ _)
      rw [h₁]
      exact isUnit_one
    have hval : U b = (U b.opposite)⁻¹ := hU'.2 b.opposite (mem_univ _)
    rw [he, hval]
    exact (continuousAt_matrix_inv hdet).tendsto.comp (tendsto_expMul b.opposite (U b.opposite))
theorem expTwist_mem_fieldsIn (hp : EdgeOrientationDichotomy L n k i)
    (hexp : ComplexMatrix2.ExpLogEstimates) {A V : Edge L n k i → ComplexMatrix2}
    (hA : ∀ b : Edge L n k i, b.IsPositivelyOriented → ComplexMatrix2.fullTrace (A b) = 0)
    (hV : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist A V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup := by
  have hdet : ∀ b : Edge L n k i, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • A b) * V b).det = 1 := by
    intro b hb
    have hV' : (V b).det = 1 := hV.1 b (mem_univ _)
    have hq := hA b hb
    rw [Matrix.det_mul, hexp.2.2.2.2.2.1, hV']
    simp [ComplexMatrix2.fullTrace, Matrix.trace_smul] at hq ⊢
    simp [hq]
  have hpos : ∀ b : Edge L n k i, b.IsPositivelyOriented →
      PeriodicLattice.expTwist A V b = ComplexMatrix2.matExp (Complex.I • A b) * V b :=
    fun b hb => by
      simp [PeriodicLattice.expTwist, hb]
  have hneg : ∀ b : Edge L n k i, ¬b.IsPositivelyOriented →
      PeriodicLattice.expTwist A V b =
        (ComplexMatrix2.matExp (Complex.I • A b.opposite) * V b.opposite)⁻¹ := fun b hb => by
    simp [PeriodicLattice.expTwist, hb]
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [hpos b hb]
      exact hdet b hb
    · have hr := opposite_pos_of_not_pos hp hb
      rw [hneg b hb]
      change (ComplexMatrix2.matExp (Complex.I • A b.opposite) * V b.opposite)⁻¹.det = 1
      rw [Matrix.det_nonsing_inv, hdet _ hr]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · have hr := not_opposite_pos_of_pos hp hb
      rw [hneg _ hr, edge_opposite_opposite, hpos b hb]
    · have hr := opposite_pos_of_not_pos hp hb
      rw [hpos _ hr, hneg b hb, Matrix.nonsing_inv_nonsing_inv _ (by
        rw [hdet _ hr]
        exact isUnit_one)]
theorem eventually_expTwist_mem_meanStable [Fintype (PositiveEdge L n k 0)]
    (hp : EdgeOrientationDichotomy L n k 0)
    (hexp : ComplexMatrix2.ExpLogEstimates)
    (hP : MeanStableFields.MeanStableConditions L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ meanStableFields L n k k)
    (hUc : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup) (B : edgeFormSpace L n k 0) :
    ∀ᶠ t : ℂ in 𝓝 0, PeriodicLattice.expTwist (t • (B : Edge L n k 0 → ComplexMatrix2)) U ∈
      meanStableFields L n k k := by
  let F : Finset (Edge L n k 0) :=
    (Finset.univ : Finset (PositiveEdge L n k 0)).map ⟨Subtype.val, Subtype.val_injective⟩
  have hF : ∀ b ∈ F, b.IsPositivelyOriented := by
    intro b hb
    obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hb
    exact s.2
  have hFm : ∀ b : Edge L n k 0, b.IsPositivelyOriented → b ∈ F := fun b hb =>
    Finset.mem_map.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩
  obtain ⟨ε, hε, h⟩ := hP.small_perturbation U hU F hF
  have hev : ∀ s : PositiveEdge L n k 0, ∀ᶠ t : ℂ in 𝓝 0,
      ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp
        (Complex.I • (t • (B : Edge L n k 0 → ComplexMatrix2) s.1)) * U s.1 - U s.1) <
        ε := fun s => by
    have hc : Continuous fun t : ℂ =>
        ComplexMatrix2.matExp (Complex.I • (t • (B : Edge L n k 0 → ComplexMatrix2) s.1)) *
          U s.1 - U s.1 :=
      by
        have h₂ : Continuous fun t : ℂ =>
            ComplexMatrix2.matExp (Complex.I • (t • (B : Edge L n k 0 → ComplexMatrix2) s.1)) :=
          continuous_matExp.comp
            ((continuous_id.smul continuous_const).const_smul Complex.I)
        exact (h₂.mul continuous_const).sub continuous_const
    have ht := hc.tendsto 0
    simp only [zero_smul, smul_zero, NormedSpace.exp_zero, one_mul, sub_self] at ht
    have := ht.eventually (Metric.ball_mem_nhds (0 : ComplexMatrix2) hε)
    filter_upwards [this] with t ht'
    simpa using ht'
  filter_upwards [Filter.eventually_all.mpr hev] with t ht
  refine h _ (expTwist_mem_fieldsIn hp hexp (fun b hb => ?_) hUc) (fun b hb hbF => ?_)
    (fun b hb => ?_)
  · have h₁ : ComplexMatrix2.fullTrace ((B : Edge L n k 0 → ComplexMatrix2) b) = 0 :=
      (B.2.1 b hb).2
    simp only [Pi.smul_apply, ComplexMatrix2.fullTrace, Matrix.trace_smul] at h₁ ⊢
    rw [h₁, smul_zero]
  · exact absurd (hFm b hb) hbF
  · have hbp := hF b hb
    have he : PeriodicLattice.expTwist (t • (B : Edge L n k 0 → ComplexMatrix2)) U b =
        ComplexMatrix2.matExp (Complex.I • (t • (B : Edge L n k 0 → ComplexMatrix2) b)) * U b := by
      simp [PeriodicLattice.expTwist, hbp]
    rw [he]
    exact ht ⟨b, hbp⟩
def formOfPositiveValues (hp : EdgeOrientationDichotomy L n k i) :
    (PositiveEdge L n k i → ComplexMatrix2.LieElement) →ₗ[ℝ] edgeFormSpace L n k i where
  toFun Y := ⟨edgeFormOfPositiveValues fun b => (Y b).toMatrix,
    edgeFormOfPositiveValues_mem hp fun b => (Y b).2⟩
  map_add' Y Y' := Subtype.ext (by
    exact edgeFormOfPositiveValues_add (fun b => (Y b).toMatrix) fun b => (Y' b).toMatrix)
  map_smul' t Y := Subtype.ext (by
    exact edgeFormOfPositiveValues_smul t fun b => (Y b).toMatrix)
theorem positiveValues_formOfPositiveValues (hp : EdgeOrientationDichotomy L n k i)
    (Y : PositiveEdge L n k i → ComplexMatrix2.LieElement) :
    positiveValues L n k i (formOfPositiveValues hp Y) = Y := by
  funext b
  apply Subtype.ext
  change edgeFormOfPositiveValues (fun b => (Y b).toMatrix) b.1 = (Y b).toMatrix
  simp only [edgeFormOfPositiveValues, dif_pos b.2]
end Curves
section Charts
open PowerExpCharts GroupLieProduct
variable {L n k : ℕ}
structure ChartProperties (V : Edge L n k 0 → ComplexMatrix2) [Fintype (PositiveEdge L n k k)]
    [Fintype (PositiveEdge L n k 0)] : Prop where
  contDiffAt : ∀ c, ContDiffAt ℝ ∞ (fun Y => iterLogInChart L n k V Y c) 0
  eq_zero : ∀ c, iterLogInChart L n k V 0 c = 0
  eventually_mem : ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k 0 → ComplexMatrix2.LieElement), ∀ c,
    complexIterOnValues L n k (expChartI (restrictToPositiveEdges V) Y) c *
      (complexIterOnValues L n k (restrictToPositiveEdges V) c)⁻¹ ∈ ComplexMatrix2.logBall
theorem expChartI_zero {σ : Type} (p : σ → ComplexMatrix2) : expChartI p 0 = p := by apply _root_.YangMills.SharedProofs.p27659 <;> assumption
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by simp [ComplexMatrix2.logSeries]
theorem chartProperties [Fintype (PositiveEdge L n k k)] [Fintype (PositiveEdge L n k 0)]
    (hcharts : PowerCharts (PositiveEdge L n k k))
    {V : Edge L n k 0 → ComplexMatrix2} {O : Set (PositiveEdge L n k 0 → ComplexMatrix2)}
    (hmaps : MapsTo (realIterOnValues L n k) O (specialUnitaryPower (PositiveEdge L n k k)))
    (hser : HasChartPowerSeries O (realIterOnValues L n k))
    (hV : restrictToPositiveEdges V ∈ O)
    (hbase : complexIterOnValues L n k (restrictToPositiveEdges V) =
      realIterOnValues L n k (restrictToPositiveEdges V))
    (hnear : ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k 0 → ComplexMatrix2.LieElement),
      complexIterOnValues L n k (expChartI (restrictToPositiveEdges V) Y) =
        realIterOnValues L n k (expChartI (restrictToPositiveEdges V) Y)) :
    ChartProperties V := by
  set p₀ := restrictToPositiveEdges V with hp₀
  set F := realIterOnValues L n k with hF
  set p₁ := F p₀ with hp₁
  obtain ⟨N, hN, hform, hsm, -⟩ := hser.1 p₀ hV
  have hb : p₁ ∈ specialUnitaryPower (PositiveEdge L n k k) := hmaps hV
  have hb' : ∀ c, p₁ c ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := hb
  have hε : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, -, hlog⟩ := hcharts p₁ hb
  obtain ⟨-, -, -, -, hopen, hlogsm, -⟩ := hlog (Real.log (19 / 10)) hε
    (by rw [Real.exp_log (by norm_num)])
  have hΦ : ContDiffAt ℝ ∞ (F ∘ expChartI p₀) 0 := hsm.contDiffAt hN
  have hΦ0 : (F ∘ expChartI p₀) 0 = p₁ := by simp [expChartI_zero, hp₁]
  have hunit : ∀ c, p₁ c * (p₁ c)⁻¹ = 1 := fun c =>
    Matrix.mul_nonsing_inv _ (by
      rw [(Matrix.mem_specialUnitaryGroup_iff.mp (hb' c)).2]
      exact isUnit_one)
  have hmem : (F ∘ expChartI p₀) 0 ∈ logDomain p₁ := by
    rw [hΦ0]
    intro c
    simp [hunit c]
  have hG : ContDiffAt ℝ ∞ (logChart p₁ ∘ (F ∘ expChartI p₀)) 0 :=
    (hlogsm.contDiffAt (hopen.mem_nhds hmem)).comp 0 hΦ
  have hin : ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k 0 → ComplexMatrix2.LieElement),
      (F ∘ expChartI p₀) Y ∈ logDomain p₁ :=
    hΦ.continuousAt.eventually (hopen.mem_nhds hmem)
  refine ⟨fun c => ?_, fun c => ?_, ?_⟩
  · refine (contDiffAt_pi.mp hG c).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with Y hY
    simp only [iterLogInChart, Function.comp_apply]
    rw [hY, hbase]
  · simp only [iterLogInChart]
    rw [expChartI_zero, hbase]
    simp [logChart, hunit c, logSeries_one]
  · filter_upwards [hin, hnear] with Y hY hYe c
    rw [hYe, hbase]
    exact hY c
end Charts
section Consequences
open PowerExpCharts
variable {L n k : ℕ} [Fintype (PositiveEdge L n k k)] [Fintype (PositiveEdge L n k 0)]
  [FiniteDimensional ℝ (edgeFormSpace L n k 0)] {V : Edge L n k 0 → ComplexMatrix2}
theorem contDiffAt_three (h : ChartProperties V) (c : PositiveEdge L n k k) :
    ContDiffAt ℝ 3 (fun Y => iterLogInChart L n k V Y c) 0 :=
  by exact_mod_cast contDiffAt_infty.mp (h.contDiffAt c) 3
omit [Fintype (PositiveEdge L n k k)] [Fintype (PositiveEdge L n k 0)]
  [FiniteDimensional ℝ (edgeFormSpace L n k 0)] in
theorem ofReal_smul_form {i : ℕ} (t : ℝ) (B : edgeFormSpace L n k i) :
    (t : ℂ) • (B : Edge L n k i → ComplexMatrix2) =
      ((t • B : edgeFormSpace L n k i) : Edge L n k i → ComplexMatrix2) := by
  funext b
  ext r s
  simp
omit [Fintype (PositiveEdge L n k k)] [Fintype (PositiveEdge L n k 0)]
  [FiniteDimensional ℝ (edgeFormSpace L n k 0)] in
theorem iterLogRatio_ofReal_smul (hp : EdgeOrientationDichotomy L n k 0)
    (hV : V ∈ fieldSpace L n k 0) (c : PositiveEdge L n k k) (t : ℝ) (B : edgeFormSpace L n k 0) :
    iterLogRatio V c ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)) =
      iterLogInChart L n k V (t • positiveValues L n k 0 B) c := by
  rw [ofReal_smul_form, iterLogRatio_eq hp hV, map_smul]
def HasRayDerivs (V : Edge L n k 0 → ComplexMatrix2) : Prop :=
  ∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k),
    HasDerivAt (fun t : ℝ => iterLogRatio V c ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)))
      (complexIterDeriv L n k k V B c) 0
omit [Fintype (PositiveEdge L n k k)] [Fintype (PositiveEdge L n k 0)]
  [FiniteDimensional ℝ (edgeFormSpace L n k 0)] in
theorem iterDerivIsLinearTaylorTerm (hD : HasRayDerivs V) : IterDerivIsLinearTaylorTerm V :=
  fun B c => ⟨by simp [taylorCoeffAtZero, iteratedDeriv_one], (hD B c).deriv⟩
theorem complexIterDeriv_eq_fderiv (hp : EdgeOrientationDichotomy L n k 0)
    (hV : V ∈ fieldSpace L n k 0) (h : ChartProperties V) (hD : HasRayDerivs V)
    (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) :
    complexIterDeriv L n k k V B c =
      fderiv ℝ (fun Y => iterLogInChart L n k V Y c) 0 (positiveValues L n k 0 B) := by
  have h₁ := hD B c
  simp only [iterLogRatio_ofReal_smul hp hV c _ B] at h₁
  exact h₁.unique (hasDerivAt_comp_smul_zero (contDiffAt_three h c) (positiveValues L n k 0 B))
def quadraticPart (V : Edge L n k 0 → ComplexMatrix2) : IterBilinearForm L n k :=
  LinearMap.mk₂ ℝ
    (fun B B' c => secondFDerivAtZero (fun Y => iterLogInChart L n k V Y c)
      (positiveValues L n k 0 B) (positiveValues L n k 0 B'))
    (fun B₁ B₂ B' => by funext c; simp)
    (fun t B B' => by funext c; simp)
    (fun B B₁ B₂ => by funext c; simp)
    (fun t B B' => by funext c; simp)
theorem quadraticPart_apply (B B' : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) :
    quadraticPart V B B' c = secondFDerivAtZero (fun Y => iterLogInChart L n k V Y c)
      (positiveValues L n k 0 B) (positiveValues L n k 0 B') := rfl
theorem isIterQuadraticExpansion (hp : EdgeOrientationDichotomy L n k 0)
    (hV : V ∈ fieldSpace L n k 0) (h : ChartProperties V) (hD : HasRayDerivs V) :
    IsIterQuadraticExpansion V (quadraticPart V) := by
  refine ⟨fun B B' => ?_, fun c => ?_⟩
  · funext c
    exact secondFDerivAtZero_symm (contDiffAt_three h c) _ _
  · obtain ⟨C, r, hC, hr, hb⟩ := taylor_two_remainder (contDiffAt_three h c)
    refine ⟨C, ?_⟩
    have hball : ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k 0 → ComplexMatrix2.LieElement), ‖Y‖ < r := by
      filter_upwards [Metric.ball_mem_nhds (0 : PositiveEdge L n k 0 → ComplexMatrix2.LieElement) hr]
        with Y hY
      simpa using hY
    have hev : ∀ᶠ B : edgeFormSpace L n k 0 in 𝓝 0, ‖positiveValues L n k 0 B‖ < r :=
      tendsto_positiveValues.eventually hball
    filter_upwards [hev] with B hB
    have hbound := hb _ hB
    simp only [h.eq_zero c, sub_zero] at hbound
    rw [iterLogRatio_eq hp hV, complexIterDeriv_eq_fderiv hp hV h hD, quadraticPart_apply]
    refine hbound.trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_positiveValues_le B) 3) hC
theorem quadraticExpansion_unique {q q' : IterBilinearForm L n k}
    (hq : IsIterQuadraticExpansion V q)
    (hq' : IsIterQuadraticExpansion V q') : q = q' := by
  have hdiag : ∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k),
      q B B c = q' B B c := by
    intro B c
    obtain ⟨C₁, h₁⟩ := hq.2 c
    obtain ⟨C₂, h₂⟩ := hq'.2 c
    set x := q B B c - q' B B c with hx
    set β := edgeFormNorm (B : Edge L n k 0 → ComplexMatrix2) with hβ
    have hc : Tendsto (fun t : ℝ => t • B) (𝓝 0) (𝓝 (0 : edgeFormSpace L n k 0)) := by
      have : Continuous fun t : ℝ => t • B := continuous_id.smul continuous_const
      simpa using this.tendsto 0
    have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) * ‖x‖ ≤ (C₁ + C₂) * β ^ 3 * t := by
      filter_upwards [((hc.eventually h₁).and (hc.eventually h₂)).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ⟨a₁, a₂⟩ ht
      have ht' : (0 : ℝ) < t := ht
      have hn : edgeFormNorm ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
          t * β := by
        rw [edgeFormNorm_smul, abs_of_pos ht']
      rw [hn] at a₁ a₂
      have hqt : ∀ r : IterBilinearForm L n k,
          r (t • B) (t • B) c = (t ^ 2) • r B B c := by
        intro r
        simp [smul_smul, pow_two]
      rw [hqt] at a₁
      rw [hqt] at a₂
      set w := iterLogRatio V c ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) -
        complexIterDeriv L n k k V
          ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) c
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
theorem iterHasUniqueQuadraticExpansion (hp : EdgeOrientationDichotomy L n k 0)
    (hV : V ∈ fieldSpace L n k 0) (h : ChartProperties V) (hD : HasRayDerivs V) :
    IterHasUniqueQuadraticExpansion V := by
  have hq₀ := isIterQuadraticExpansion hp hV h hD
  refine ⟨⟨quadraticPart V, hq₀, fun q hq => quadraticExpansion_unique hq hq₀⟩,
    Classical.epsilon_spec (p := IsIterQuadraticExpansion V) ⟨_, hq₀⟩,
    fun q hq B c => ?_⟩
  obtain rfl := quadraticExpansion_unique hq hq₀
  simp only [taylorCoeffAtZero, iterLogRatio_ofReal_smul hp hV c _ B]
  rw [iteratedDeriv_two_comp_smul (contDiffAt_three h c), quadraticPart_apply]
  norm_num [Nat.factorial]
theorem iterLogRatio_zero (hp : EdgeOrientationDichotomy L n k 0) (hV : V ∈ fieldSpace L n k 0)
    (h : ChartProperties V) (c : PositiveEdge L n k k) : iterLogRatio V c 0 = 0 := by
  have := iterLogRatio_eq hp hV (0 : edgeFormSpace L n k 0) c
  rw [map_zero, h.eq_zero c] at this
  simpa using this
end Consequences
section Continuation
open GroupLieProduct GroupLieProduct.Subspaces
variable {σ : Type}
def smulLinear (z : ℂ) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun X := z • X
  map_add' := smul_add z
  map_smul' w X := smul_comm z w X
def algebraChart (V₀ : σ → ComplexMatrix2) (q : Empty ⊕ σ → ComplexMatrix2) :
    σ ⊕ Empty → ComplexMatrix2 :=
  Sum.elim (fun s => ComplexMatrix2.matExp (Complex.I • q (.inr s)) * V₀ s) Empty.elim
def continuedRatio (V₀ : σ → ComplexMatrix2) (Φ : (σ ⊕ Empty → ComplexMatrix2) → ComplexMatrix2)
    (M : ComplexMatrix2) (q : Empty ⊕ σ → ComplexMatrix2) : ComplexMatrix2 :=
  Φ (algebraChart V₀ q) * M
def continuedDomain (V₀ : σ → ComplexMatrix2) (𝒳 : Set (σ ⊕ Empty → ComplexMatrix2))
    (Φ : (σ ⊕ Empty → ComplexMatrix2) → ComplexMatrix2) (M : ComplexMatrix2) :
    Set (Empty ⊕ σ → ComplexMatrix2) :=
  (GroupLieProduct Empty σ ∩ algebraChart V₀ ⁻¹' 𝒳) ∩
    continuedRatio V₀ Φ M ⁻¹' ComplexMatrix2.logBall
theorem isOpen_logBall : IsOpen ComplexMatrix2.logBall :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
theorem continuedLog_holomorphic [Fintype σ]
    (hexp : ComplexMatrix2.ExpLogEstimates)
    (hops : GroupLieProduct.HolomorphyClosureStatement)
    (hH2 : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {V₀ : σ → ComplexMatrix2}
    (hV₀ : ∀ s, V₀ s ∈ ComplexMatrix2.unitDeterminant)
    {𝒳 : Set (σ ⊕ Empty → ComplexMatrix2)} {Φ : (σ ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular b 𝒳 Φ) (M : ComplexMatrix2) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty σ) (continuedDomain V₀ 𝒳 Φ M) ∧
      IsHolomorphicToMatrixEntries b (continuedDomain V₀ 𝒳 Φ M)
        fun q => Complex.I⁻¹ • ComplexMatrix2.logSeries (continuedRatio V₀ Φ M q) := by
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
        fun q => Complex.I • q (.inr s) := hO₀.2.2.2.2.1 (smulLinear Complex.I) _ h₁
    have h₃ : IsHolomorphicToMatrixEntries b (GroupLieProduct Empty σ)
        fun q => ComplexMatrix2.matExp (Complex.I • q (.inr s)) := hO₀.2.2.2.2.2.2.1 _ h₂
    exact hO₀.2.2.2.1 _ _ h₃ (hO₀.1 (V₀ s))
  have hgroup : ∀ s, MapsTo (fun q : Empty ⊕ σ → ComplexMatrix2 =>
      ComplexMatrix2.matExp (Complex.I • q (.inr s)) * V₀ s)
      (GroupLieProduct Empty σ) ComplexMatrix2.unitDeterminant := by
    intro s q hq
    have hq' : ComplexMatrix2.fullTrace (q (.inr s)) = 0 := hq (.inr s)
    have hV' : (V₀ s).det = 1 := hV₀ s
    change (ComplexMatrix2.matExp (Complex.I • q (.inr s)) * V₀ s).det = 1
    rw [Matrix.det_mul, hexp.2.2.2.2.2.1, hV']
    simp [ComplexMatrix2.fullTrace, Matrix.trace_smul] at hq' ⊢
    simp [hq']
  have hΞ : IsHolomorphicToProduct b (GroupLieProduct Empty σ) (algebraChart V₀) :=
    ⟨hopen, fun s => ((hprod Empty σ).2.1 b _ _ hopen (hgroup s)).mpr (hi s),
      fun e => e.elim⟩
  have hΦc : IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv 𝒳 Φ :=
    ((hprod σ Empty).2.1 b 𝒳 _ hΦ.1 hΦ.2.1).mp hΦ
  have hC := hcomp Empty σ σ Empty b _ _ hopen hΞ ComplexMatrix2 4
    Coordinates.ComplexCoordinates.matrixEquiv 𝒳 Φ hΦc
  have hW₁ := hC.2.1
  have hO₁ := hops Empty σ b _ hW₁
  have h₂ : IsHolomorphicToMatrixEntries b
      (GroupLieProduct Empty σ ∩ algebraChart V₀ ⁻¹' 𝒳)
      (continuedRatio V₀ Φ M) := hO₁.2.2.2.1 _ _ hC.2.2 (hO₁.1 M)
  have hW₂ : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Empty σ)
      (continuedDomain V₀ 𝒳 Φ M) :=
    hO₁.2.2.2.2.2.2.2.2.1 _ h₂ ComplexMatrix2.logBall isOpen_logBall
  refine ⟨hW₂, ?_⟩
  have hO₂ := hops Empty σ b _ hW₂
  have h₃ : IsHolomorphicToMatrixEntries b (continuedDomain V₀ 𝒳 Φ M)
      (continuedRatio V₀ Φ M) :=
    hO₁.2.2.2.2.2.2.2.2.2.1 _ inter_subset_left hW₂ _ h₂
  have h₄ : IsHolomorphicToMatrixEntries b (continuedDomain V₀ 𝒳 Φ M)
      fun q => ComplexMatrix2.logSeries (continuedRatio V₀ Φ M q) :=
    hO₂.2.2.2.2.2.2.2.1 _ h₃ fun q hq => hq.2
  exact hO₂.2.2.2.2.1 (smulLinear Complex.I⁻¹) _ h₄
end Continuation
section Analytic
open GroupLieProduct GroupLieProduct.Subspaces
open MeanStableFields
variable {L n k : ℕ} [Fintype (PositiveEdge L n k 0)]
def meanStablePoints (L n k : ℕ) : Set (PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2) :=
  asGroupFactors '' (restrictToPositiveEdges '' meanStableFields L n k k)
def levelwiseMeanOnPoints (L n k : ℕ) (c : PositiveEdge L n k k)
    (p : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2) : ComplexMatrix2 :=
  levelwiseMeanAt k c.1 (fieldOfPositiveValues fun b => p (.inl b))
theorem iterLogRatio_isAnalyticNearZero (hexp : ComplexMatrix2.ExpLogEstimates)
    (hops : GroupLieProduct.HolomorphyClosureStatement)
    (hH2 : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hO : IteratedMeans.TorusConditions L n k)
    (hP : MeanStableFields.MeanStableConditions L n k)
    (hp : EdgeOrientationDichotomy L n k 0) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) (hst : U ∈ meanStableFields L n k k)
    (b₀ : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (c : PositiveEdge L n k k)
    (hΦ : ∀ β, IsHolomorphicToUnimodular β (meanStablePoints L n k) (levelwiseMeanOnPoints L n k c))
    (hc : IsUnit (PeriodicLattice.complexBlockFieldAtLevel k U c).det) :
    IsAnalyticNearZero (iterLogRatio U c) := by
  have hVG : ∀ b : Edge L n k 0, U b ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
    fun b => (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U from
      hU).1 b (mem_univ _)
  obtain ⟨V₀, hV₀d⟩ : ∃ V₀, V₀ = restrictToPositiveEdges U := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (PeriodicLattice.complexBlockFieldAtLevel k U c)⁻¹ := ⟨_, rfl⟩
  have hV₀ : ∀ s, V₀ s ∈ ComplexMatrix2.unitDeterminant := fun s => by
    rw [hV₀d]
    exact (Matrix.mem_specialUnitaryGroup_iff.mp (hVG s.1)).2
  have hhol := fun b => continuedLog_holomorphic hexp hops hH2 b hV₀ (hΦ b) M
  have key : ∀ q, algebraChart V₀ q ∈ meanStablePoints L n k →
      continuedRatio V₀ (levelwiseMeanOnPoints L n k c) M q =
        PeriodicLattice.complexBlockFieldAtLevel k
          (PeriodicLattice.expTwist (edgeFormOfPositiveValues (algebraComponent q)) U) c * M := by
    rintro q ⟨_, ⟨W, hW, rfl⟩, hx⟩
    set A := edgeFormOfPositiveValues (algebraComponent q) with hAd
    have hAval : ∀ s : PositiveEdge L n k 0, A s.1 = q (.inr s) := fun s => by
      simp only [hAd, edgeFormOfPositiveValues, dif_pos s.2]
      rfl
    have hgp : (fun b => algebraChart V₀ q (.inl b)) =
        fun s : PositiveEdge L n k 0 => ComplexMatrix2.matExp (Complex.I • A s.1) * U s.1 := by
      funext s
      simp only [algebraChart, Sum.elim_inl, hAval, hV₀d]
      rfl
    have hcfg : fieldOfPositiveValues (fun b => algebraChart V₀ q (.inl b)) =
        PeriodicLattice.expTwist A U := by
      rw [hgp, fieldOfPositiveValues_expMul hp]
    have hWv : (fun b => algebraChart V₀ q (.inl b)) = restrictToPositiveEdges W := by
      rw [← hx]
      rfl
    have hWeq : PeriodicLattice.expTwist A U = W := by
      rw [← hcfg, hWv]
      exact fieldOfPositiveValues_restrict hp (meanStable_props hO hP hW).1.1
    rw [continuedRatio, levelwiseMeanOnPoints, hcfg, hWeq, (meanStable_props hO hP hW).2 c.1]
  have hchart0 : algebraChart V₀ (ofParts Empty.elim 0) = asGroupFactors V₀ := by
    funext x
    cases x with
    | inl s => simp [algebraChart, ofParts, asGroupFactors]
    | inr e => exact e.elim
  have hpt : asGroupFactors V₀ ∈ meanStablePoints L n k := ⟨V₀, ⟨U, hst, hV₀d.symm⟩, rfl⟩
  have hΦ₀ : levelwiseMeanOnPoints L n k c (asGroupFactors V₀) =
      PeriodicLattice.complexBlockFieldAtLevel k U c := by
    have hg : fieldOfPositiveValues (fun b => asGroupFactors V₀ (.inl b)) = U := by
      change fieldOfPositiveValues V₀ = U
      rw [hV₀d]
      exact fieldOfPositiveValues_restrict hp (𝒢 := PeriodicLattice.compactGaugeGroup) hU
    rw [levelwiseMeanOnPoints, hg]
    exact (meanStable_props hO hP hst).2 c.1
  have hunit : PeriodicLattice.complexBlockFieldAtLevel k U c * M = 1 := by
    rw [hM]
    exact Matrix.mul_nonsing_inv _ hc
  have hq₀W : ofParts Empty.elim 0 ∈ continuedDomain V₀ (meanStablePoints L n k)
      (levelwiseMeanOnPoints L n k c) M := by
    refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
    · cases x with
      | inl e => exact e.elim
      | inr s => exact ComplexMatrix2.traceless.zero_mem
    · change algebraChart V₀ _ ∈ meanStablePoints L n k
      rw [hchart0]
      exact hpt
    · change continuedRatio V₀ (levelwiseMeanOnPoints L n k c) M _ ∈ ComplexMatrix2.logBall
      rw [continuedRatio, hchart0, hΦ₀, hunit]
      simp [ComplexMatrix2.logBall]
  have hq₀R : ofParts Empty.elim 0 ∈
      subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k 0)) Empty :=
    ⟨Submodule.zero_mem _, fun e => e.elim⟩
  have hsub : ∀ q ∈ subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k 0)) Empty,
      q ∈ GroupLieProduct Empty (PositiveEdge L n k 0) := by
    intro q hq x
    cases x with
    | inl e => exact e.elim
    | inr s => exact (hq.1 s (mem_univ s)).2
  obtain ⟨O, hO', hWO⟩ := (hhol b₀).1
  refine ⟨inferInstance, continuedDomain V₀ (meanStablePoints L n k)
      (levelwiseMeanOnPoints L n k c) M ∩
      subspaceTimesGroup (hermitianTracelessFunctions (PositiveEdge L n k 0)) Empty, ⟨hq₀W, hq₀R⟩,
    ⟨le_rfl, O, hO', ?_⟩, fun p hpW => ⟨continuedDomain V₀ (meanStablePoints L n k)
      (levelwiseMeanOnPoints L n k c) M, hpW.1, (hhol b₀).1,
      subset_rfl, fun q => Coordinates.ComplexCoordinates.matrixEquiv
        (Complex.I⁻¹ • ComplexMatrix2.logSeries
          (continuedRatio V₀ (levelwiseMeanOnPoints L n k c) M q)),
      fun b => (hhol b).2, fun q hq => ?_⟩⟩
  · rw [hWO]
    ext q
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hsub q h.2⟩, h.2⟩⟩
  · change Coordinates.ComplexCoordinates.matrixEquiv _ =
      Coordinates.ComplexCoordinates.matrixEquiv _
    rw [key q hq.1.1.2, hM]
    rfl
end Analytic
section Rays
open PowerExpCharts
open LevelwiseMeans MeanStableFields
variable {L n k : ℕ}
theorem complexIterDeriv_eq [Fintype (PositiveEdge L n k 0)]
    (hH : LevelwiseMeans.PeriodicConditions L n k)
    (hO : IteratedMeans.TorusConditions L n k)
    (hP : MeanStableFields.MeanStableConditions L n k)
    (hp : EdgeOrientationDichotomy L n k 0) (hexp : ComplexMatrix2.ExpLogEstimates)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) (hF : IteratesDefined L n k U)
    (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) {D : ComplexMatrix2}
    (hW : ∀ (F : Finset (Edge L n k 0)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → ComplexMatrix2),
      IsHolomorphicRepresentation k c.1 U F O f →
      HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries
        (f (expChartPoint F (t • (B : Edge L n k 0 → ComplexMatrix2)) U) *
          (f (edgeEntries F U))⁻¹)) (Complex.I • D) 0) :
    complexIterDeriv L n k k U B c = D := by
  have hUc := fieldsIn_complex_of_mem hU
  obtain ⟨hst, hval⟩ := iteratesDefined_props hO hF
  have hform := (hF k le_rfl).2.2 c.1
  have hsome : IsDefinedAt U k c.1 := by simp [IsDefinedAt, hform]
  obtain ⟨F, O, f, hw⟩ := hH.exists_representation k le_rfl c.1 U hUc hsome
  have hcur := hH.represents_along_curves k le_rfl c.1 U hUc F O f hw
    (B : Edge L n k 0 → ComplexMatrix2) fun b hb => (B.2.1 b hb).2
  have hbase : f (edgeEntries F U) = PeriodicLattice.complexBlockFieldAtLevel k U c.1 := by
    have h₁ := hw.eq_some U hUc hw.mem
    rw [hform] at h₁
    exact (Option.some.inj h₁).symm.trans (hval c.1).symm
  have hev : (fun t : ℂ => ComplexMatrix2.logSeries (PeriodicLattice.complexBlockFieldAtLevel k
        (PeriodicLattice.expTwist (t • (B : Edge L n k 0 → ComplexMatrix2)) U) c.1 *
        (PeriodicLattice.complexBlockFieldAtLevel k U c.1)⁻¹)) =ᶠ[𝓝 0]
      fun t => ComplexMatrix2.logSeries
        (f (expChartPoint F (t • (B : Edge L n k 0 → ComplexMatrix2)) U) *
          (f (edgeEntries F U))⁻¹) := by
    filter_upwards [hcur, eventually_expTwist_mem_meanStable hp hexp hP hst hUc B] with t ht hs
    have h₃ := (meanStable_props hO hP hs).2 c.1
    have h₄ : PeriodicLattice.complexBlockFieldAtLevel k
        (PeriodicLattice.expTwist (t • (B : Edge L n k 0 → ComplexMatrix2)) U) c.1 =
        f (expChartPoint F (t • (B : Edge L n k 0 → ComplexMatrix2)) U) := by
      rw [← h₃, levelwiseMeanAt, valuesOrOne, ht.2]
      rfl
    rw [h₄, hbase]
  have hd := (hW F O f hw).congr_of_eventuallyEq hev
  have he : complexIterDeriv L n k k U (B : Edge L n k 0 → ComplexMatrix2) c.1 =
      Complex.I⁻¹ • deriv (fun t : ℂ => ComplexMatrix2.logSeries
        (PeriodicLattice.complexBlockFieldAtLevel k
          (PeriodicLattice.expTwist (t • (B : Edge L n k 0 → ComplexMatrix2)) U) c.1 *
        (PeriodicLattice.complexBlockFieldAtLevel k U c.1)⁻¹)) 0 := by
    simp only [complexIterDeriv, holLeftDifferential, extendOddly, if_pos c.2,
      logDirectionalDeriv]
    rfl
  rw [he, hd.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem hasDerivAt_iterLogRatio_ofReal
    (hconf : ∀ B ∈ edgeFormSpace L n k 0, ∀ V ∈ fieldSpace L n k 0,
      PeriodicLattice.expTwist B V ∈ fieldSpace L n k 0)
    (hO : IteratedMeans.TorusConditions L n k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) (hF : IteratesDefined L n k U)
    (hnb : ∀ᶠ V in 𝓝[fieldSpace L n k 0] U, IteratesDefined L n k V)
    (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) {D : ComplexMatrix2}
    (hR : HasDerivAt (fun t : ℝ => ComplexMatrix2.logSeries (smoothingIter L n k k
        (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)) U) c *
        (smoothingIter L n k k U c)⁻¹)) (Complex.I • D) 0) :
    HasDerivAt (fun t : ℝ => iterLogRatio U c ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)))
      D 0 := by
  have h₁ : Tendsto (fun t : ℝ => t • B) (𝓝 0) (𝓝 (0 : edgeFormSpace L n k 0)) := by
    have : Continuous fun t : ℝ => t • B := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hev := h₁.eventually ((tendsto_expTwist hconf hU).eventually hnb)
  have hUeq := (iteratesDefined_props hO hF).2 c.1
  have hcongr : (fun t : ℝ =>
      iterLogRatio U c ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2))) =ᶠ[𝓝 0]
      fun t => Complex.I⁻¹ • ComplexMatrix2.logSeries (smoothingIter L n k k
        (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)) U) c *
        (smoothingIter L n k k U c)⁻¹) := by
    filter_upwards [hev] with t ht
    rw [← ofReal_smul_form] at ht
    simp only [iterLogRatio]
    rw [(iteratesDefined_props hO ht).2 c.1, hUeq]
  have h₂ := (hR.const_smul Complex.I⁻¹).congr_of_eventuallyEq hcongr
  rwa [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul] at h₂
theorem eventually_iteratesDefined_expChartI [FiniteDimensional ℝ (edgeFormSpace L n k 0)]
    [Fintype (PositiveEdge L n k 0)]
    (hp : EdgeOrientationDichotomy L n k 0)
    (hconf : ∀ B ∈ edgeFormSpace L n k 0, ∀ V ∈ fieldSpace L n k 0,
      PeriodicLattice.expTwist B V ∈ fieldSpace L n k 0)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (hnb : ∀ᶠ V in 𝓝[fieldSpace L n k 0] U, IteratesDefined L n k V) :
    ∀ᶠ Y in 𝓝 (0 : PositiveEdge L n k 0 → ComplexMatrix2.LieElement),
      IteratesDefined L n k (fieldOfPositiveValues (expChartI (restrictToPositiveEdges U) Y)) := by
  have hc : Tendsto (formOfPositiveValues hp) (𝓝 0) (𝓝 0) := by
    have : Continuous (formOfPositiveValues hp) := LinearMap.continuous_of_finiteDimensional _
    simpa using this.tendsto 0
  filter_upwards [hc.eventually ((tendsto_expTwist hconf hU).eventually hnb)] with Y hY
  have he : fieldOfPositiveValues (expChartI (restrictToPositiveEdges U) Y) =
      PeriodicLattice.expTwist (formOfPositiveValues hp Y : Edge L n k 0 → ComplexMatrix2) U := by
    conv_lhs =>
      rw [← positiveValues_formOfPositiveValues hp Y, expChartI_positiveValues,
        fieldOfPositiveValues_expMul hp]
  rw [he]
  exact hY
end Rays
section NearOne
variable {L n k i : ℕ}
theorem eventually_mem_of_isOpenNhdOfOne (hp : EdgeOrientationDichotomy L n k i)
    {𝒰 : Set (Edge L n k i → ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2)), V ∈ 𝒰 := by
  obtain ⟨⟨hsub, O, hO, himg⟩, h1⟩ := h
  have hcont : Continuous (restrictToPositiveEdges : (Edge L n k i → ComplexMatrix2) → _) :=
    continuous_pi fun b => continuous_apply _
  have h1' : restrictToPositiveEdges (trivialField L n k i) ∈ O := by
    have : restrictToPositiveEdges (trivialField L n k i) ∈ restrictToPositiveEdges '' 𝒰 :=
      ⟨_, h1, rfl⟩
    rw [himg] at this
    exact this.1
  have hnh : {V : Edge L n k i → ComplexMatrix2 | restrictToPositiveEdges V ∈ O} ∈
      𝓝 (fun _ => (1 : ComplexMatrix2)) := (hO.preimage hcont).mem_nhds h1'
  filter_upwards [mem_nhdsWithin_of_mem_nhds hnh, self_mem_nhdsWithin] with V hVO hVc
  have hV : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := by
    rw [himg]
    exact ⟨hVO, fun b =>
      (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ V from hVc).1 b.1
        (mem_univ _)⟩
  obtain ⟨U, hU, hUV⟩ := hV
  have hUc : U ∈ fieldSpace L n k i := hsub hU
  rw [← fieldOfPositiveValues_restrict hp (𝒢 := PeriodicLattice.compactGaugeGroup) hVc, ← hUV,
    fieldOfPositiveValues_restrict hp (𝒢 := PeriodicLattice.compactGaugeGroup) hUc]
  exact hU
end NearOne
end IterLeftChart
open IterLeftChart Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
  Matrices.PowerExpCharts in
theorem iterLeftChartExpansion_holds
    (hFib : SmoothingFibres)
    (hVal : SmoothingNearTrivialField)
    (hH1 : LevelwiseMeans.LevelwiseMeansHold)
    (hO1 : IteratedMeans.IteratedMeansHold)
    (hP1 : MeanStableFields.MeanStableFieldsHold)
    (hChart : ExpChartsStatement)
    (hCfg : BondSetFields.ProductStructureHolds)
    (hForms : FiniteSideFormSpaces)
    (hExp : ComplexMatrix2.ExpLogEstimates)
    (hPauli : OneLoop.PauliMatrixRelations)
    (hOps : HolomorphyClosureStatement)
    (hH2 : ExpChartHolomorphy.ExpChartTheory)
    (hPos : PeriodicLattice.LevelBondOrientationDichotomy) :
    IterLeftChartExpansion := by
  intro L n k hL hn hk₁
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hk : 0 < i + 1 := by omega
  have hp : EdgeOrientationDichotomy L n (i + 1) 0 := hPos L n (i + 1) hL hn hk 0 (by omega)
  have hp' : EdgeOrientationDichotomy L n (i + 1) (i + 1) :=
    hPos L n (i + 1) hL hn hk (i + 1) le_rfl
  have := (hForms L n (i + 1) 0 hL hn (by omega)).2.1
  have hconf : ∀ B ∈ edgeFormSpace L n (i + 1) 0, ∀ V ∈ fieldSpace L n (i + 1) 0,
      PeriodicLattice.expTwist B V ∈ fieldSpace L n (i + 1) 0 :=
    (hVal L n (i + 1) hL hn hk).2 0 (by omega)
  obtain ⟨𝒰, h𝒰, -, hAn, -⟩ := (hFib L n (i + 1) i hL hn (by omega)).2.2.2.2.1
  obtain ⟨-, hMaps, fP, fQ, -, -, -, hRA⟩ := hAn
  have hne : ∀ j, j ≤ i + 1 → EdgeOrientationDichotomy L n (i + 1) j →
      Nonempty (PositiveEdge L n (i + 1) j) := by
    intro j hj hpj
    obtain ⟨b, -⟩ := ((hCfg L hL (i + 1) j hj).1 n hn).2.2.1
    by_cases hb : b.IsPositivelyOriented
    · exact ⟨⟨b, hb⟩⟩
    · exact ⟨⟨b.opposite, opposite_pos_of_not_pos hpj hb⟩⟩
  have := hne 0 (by omega) hp
  have := hne (i + 1) le_rfl hp'
  obtain ⟨-, -, -, ⟨b₀, -⟩, -⟩ := hPauli
  have hCh := hChart (PositiveEdge L n (i + 1) 0) (PositiveEdge L n (i + 1) (i + 1))
  have hCh' := (hChart (PositiveEdge L n (i + 1) (i + 1)) (PositiveEdge L n (i + 1) 0)).1
  have hOopen : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := h𝒰.1.2
  have hcv : ∀ U ∈ 𝒰, fieldOfPositiveValues (restrictToPositiveEdges U) = U := fun U hU =>
    fieldOfPositiveValues_restrict hp (𝒢 := PeriodicLattice.compactGaugeGroup) (h𝒰.1.1 hU)
  have hmapsO : MapsTo (realIterOnValues L n (i + 1)) (restrictToPositiveEdges '' 𝒰)
      (specialUnitaryPower (PositiveEdge L n (i + 1) (i + 1))) := by
    rintro _ ⟨U, hU, rfl⟩ c
    have hm := hMaps hU
    change smoothingIter L n (i + 1) (i + 1)
      (fieldOfPositiveValues (restrictToPositiveEdges U)) c.1 ∈ ComplexMatrix2.specialUnitary
    rw [hcv U hU]
    exact (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ _ from hm).1
      c.1 (mem_univ _)
  have hgp : ∀ U ∈ 𝒰, asGroupFactors (restrictToPositiveEdges U) ∈
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := fun U hU => by
    change fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
    rw [hcv U hU]
    exact hU
  have hR : IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b₀) asGroupFactors
      (restrictToPositiveEdges '' 𝒰) (realIterOnValues L n (i + 1)) := by
    rintro _ ⟨U, hU, rfl⟩
    obtain ⟨𝒳, hp𝒳, -, -, Ψ, hΨ, hEq⟩ := hRA _ (hgp U hU)
    refine ⟨𝒳, Ψ, hp𝒳, hΨ b₀, fun x hx hxX => ?_⟩
    have hxG : x ∈ specialUnitaryPower (PositiveEdge L n (i + 1) 0) := by
      obtain ⟨U', hU', rfl⟩ := hx
      exact fun b => (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U'
        from h𝒰.1.1 hU').1 b.1 (mem_univ _)
    exact hEq ⟨hxX, (Submodule.mem_bot ℝ).mpr (funext fun e => e.elim), hxG⟩
  have h4 := ((hCh.2.2.2.2.2.2.2 b₀).1 _ hOopen).2.2.2 _ hmapsO hR
  have hH := (hH1 L hL (i + 1) hk₁).1 n hn
  have hO := (hO1 L hL (i + 1) hk₁).1 n hn
  have hP := (hP1 L hL (i + 1) hk₁).1 n hn
  have hΦ : ∀ (c : PositiveEdge L n (i + 1) (i + 1))
      (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
      IsHolomorphicToUnimodular β (meanStablePoints L n (i + 1))
        (levelwiseMeanOnPoints L n (i + 1) c) := by
    intro c β
    obtain ⟨-, f', h⟩ := hP.holomorphic_mean (i + 1) le_rfl c.1 c.2 β
    have hf : f' = fP := Subsingleton.elim _ _
    subst hf
    exact h
  have hnear : ∀ᶠ V in 𝓝[fieldSpace L n (i + 1) 0] (fun _ => (1 : ComplexMatrix2)),
      IteratesDefined L n (i + 1) V :=
    Eventually.mono hH.iterates_defined fun V hV j hj =>
      ⟨(hV j hj).1, (hV j hj).2.1, (hV j hj).2.2.1⟩
  change ∀ᶠ V in 𝓝[fieldSpace L n (i + 1) 0] (fun _ => (1 : ComplexMatrix2)), _
  filter_upwards [eventually_mem_of_isOpenNhdOfOne hp h𝒰, self_mem_nhdsWithin,
    hH.iterates_defined, eventually_eventually_nhdsWithin.mpr hnear, hnear]
    with V hV hVc hfull hnb hF
  obtain ⟨hst, hval⟩ := iteratesDefined_props hO hF
  have hsm := (meanStable_props hO hP hst).1
  have hbase : complexIterOnValues L n (i + 1) (restrictToPositiveEdges V) =
      realIterOnValues L n (i + 1) (restrictToPositiveEdges V) := by
    funext c
    simp only [complexIterOnValues, realIterOnValues, restrictToPositiveEdges]
    rw [hcv V hV]
    exact hval c.1
  have hch := eventually_iteratesDefined_expChartI hp hconf hVc hnb
  have hcf : ChartProperties V := chartProperties hCh' hmapsO h4.1 ⟨V, hV, rfl⟩ hbase (by
    filter_upwards [hch] with Y hY
    funext c
    exact (iteratesDefined_props hO hY).2 c.1)
  have hD : HasRayDerivs V := fun B c => by
    obtain ⟨-, -, -, hder⟩ := hfull (i + 1) le_rfl
    obtain ⟨hRe, hWr⟩ := hder B B.2 c.1 c.2
    rw [complexIterDeriv_eq hH hO hP hp hExp hVc hF B c hWr]
    exact hasDerivAt_iterLogRatio_ofReal hconf hO hVc hF hnb B c hRe
  have hdet : ∀ c : PositiveEdge L n (i + 1) (i + 1),
      IsUnit (PeriodicLattice.complexBlockFieldAtLevel (i + 1) V c.1).det := fun c => by
    have h₁ := (hF (i + 1) le_rfl).1
    have h₂ := (fieldsIn_complex_of_mem h₁).1 c.1 (mem_univ _)
    have h₃ : (smoothingIter L n (i + 1) (i + 1) V c.1).det = 1 := h₂
    rw [hval c.1, h₃]
    exact isUnit_one
  refine ⟨⟨hsm, fun c => hval c.1, ?_, fun c =>
      ⟨iterLogRatio_isAnalyticNearZero hExp hOps hH2 hO hP hp hVc
        hst b₀ c (hΦ c) (hdet c), iterLogRatio_zero hp hVc hcf c⟩⟩,
    iterDerivIsLinearTaylorTerm hD, iterHasUniqueQuadraticExpansion hp hVc hcf hD⟩
  filter_upwards [(tendsto_expTwist hconf hVc).eventually hnb,
    tendsto_positiveValues.eventually hcf.eventually_mem]
    with B hB hB'
  obtain ⟨hs', hv'⟩ := iteratesDefined_props hO hB
  refine ⟨(meanStable_props hO hP hs').1, fun c => hv' c.1, fun c => ?_⟩
  have h₁ := hB' c
  rwa [complexIterOnValues_expChartI hp, complexIterOnValues_restrict hp hVc] at h₁
end YangMills.Construction.Tower
end
