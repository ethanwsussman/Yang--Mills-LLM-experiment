import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.GrowingTori.SubFamiliesNeighbourhoodsAndTheSeparation
import YangMills.Construction.GrowingTori.TransportThroughABallToTheTorusOfAnExponent
import YangMills.Construction.Torus.CoveringMapOnSmallBallsProof
import YangMills.Construction.Towers.ObjectsOfATowerPickedByTheirPropertiesHaveThosePropertiesProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.TorusMetric (torusProj euclidNormVec torusEuclidNorm Torus4 setEuclidDist)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriLimits.ExponentTorusPeriodization
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_sub_comm (v w : Fin 4 → ℝ) :
    euclidNormVec (v - w) = euclidNormVec (w - v) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_smul (t : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (t • v) = |t| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
theorem side_le_euclidNormVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (TestFunctions.latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
theorem latticeTranslate_zero (ℓ : ℝ) : TestFunctions.latticeTranslate ℓ 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
theorem latticeTranslate_neg (ℓ : ℝ) (k : Fin 4 → ℤ) :
    TestFunctions.latticeTranslate ℓ (-k) = -TestFunctions.latticeTranslate ℓ k := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace.latticeTranslate_neg <;> assumption
section Torus
variable {ℓ : ℝ}
theorem torusProj_sub (x y : Fin 4 → ℝ) : torusProj ℓ (x - y) = torusProj ℓ x - torusProj ℓ y := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem continuous_torusProj : Continuous (torusProj ℓ) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
theorem isLeast_torusEuclidNorm (y : Torus4 ℓ) :
    IsLeast (euclidNormVec '' (torusProj ℓ ⁻¹' {y})) (torusEuclidNorm y) := by apply _root_.YangMills.Construction.TestFunctions.SmallBalls.isLeast_torusEuclidNorm <;> assumption
theorem torusEuclidNorm_nonneg (y : Torus4 ℓ) : 0 ≤ torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
theorem torusEuclidNorm_neg (y : Torus4 ℓ) : torusEuclidNorm (-y) = torusEuclidNorm y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.torusEuclidNorm_neg <;> assumption
theorem torusEuclidNorm_zero : torusEuclidNorm (0 : Torus4 ℓ) = 0 := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_zero <;> assumption
theorem eq_zero_of_torusEuclidNorm_eq_zero {y : Torus4 ℓ} (h : torusEuclidNorm y = 0) :
    y = 0 := by apply _root_.YangMills.Construction.Tower.SelectedObjects.eq_zero_of_torusEuclidNorm_eq_zero <;> assumption
theorem continuous_torusEuclidNorm : Continuous (torusEuclidNorm : Torus4 ℓ → ℝ) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusEuclidNorm <;> assumption
theorem torusEuclidNorm_proj_sub_le (x y : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) ≤
      euclidNormVec (x - y - TestFunctions.latticeTranslate ℓ k) := by
  refine (isLeast_torusEuclidNorm _).2 ⟨_, ?_, rfl⟩
  have h : x - y - TestFunctions.latticeTranslate ℓ k =
      (x - y) + TestFunctions.latticeTranslate ℓ (-k) := by
    rw [latticeTranslate_neg, sub_eq_add_neg]
  change torusProj ℓ (x - y - TestFunctions.latticeTranslate ℓ k) = _
  rw [h, TestFunctions.torusProj_add_latticeTranslate, torusProj_sub]
theorem exists_torusEuclidNorm_proj_sub_eq (x y : Fin 4 → ℝ) :
    ∃ k, torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) =
      euclidNormVec (x - y - TestFunctions.latticeTranslate ℓ k) := by
  obtain ⟨b, hb, hbv⟩ := (isLeast_torusEuclidNorm (torusProj ℓ x - torusProj ℓ y)).1
  have hb' : torusProj ℓ b = torusProj ℓ (x - y) := by
    rw [torusProj_sub]
    exact hb
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hb'
  refine ⟨-k, ?_⟩
  rw [← hbv, hk, latticeTranslate_neg, sub_neg_eq_add]
variable (hℓ : 0 < ℓ) {B : Set (Fin 4 → ℝ)}
  (hB : ∀ x ∈ B, ∀ y ∈ B, euclidNormVec (x - y) < ℓ / 2)
include hℓ hB
theorem euclidNormVec_sub_lt_sub_translate {x y : Fin 4 → ℝ} (hx : x ∈ B) (hy : y ∈ B)
    {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    euclidNormVec (x - y) < euclidNormVec (x - y - TestFunctions.latticeTranslate ℓ k) := by
  have h₁ := side_le_euclidNormVec_latticeTranslate hℓ hk
  have h₂ : euclidNormVec (TestFunctions.latticeTranslate ℓ k) ≤
      euclidNormVec (x - y) + euclidNormVec (x - y - TestFunctions.latticeTranslate ℓ k) := by
    have h := euclidNormVec_add_le (x - y) (-(x - y - TestFunctions.latticeTranslate ℓ k))
    rwa [euclidNormVec_neg, add_neg_eq_iff_eq_add.2 (by abel :
      x - y = TestFunctions.latticeTranslate ℓ k + (x - y - TestFunctions.latticeTranslate ℓ k))] at h
  have h₃ := hB x hx y hy
  linarith
theorem torusEuclidNorm_proj_sub_eq {x y : Fin 4 → ℝ} (hx : x ∈ B) (hy : y ∈ B) :
    torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) = euclidNormVec (x - y) := by
  obtain ⟨k, hk⟩ := exists_torusEuclidNorm_proj_sub_eq (ℓ := ℓ) x y
  have hle := torusEuclidNorm_proj_sub_le (ℓ := ℓ) x y 0
  rw [latticeTranslate_zero, sub_zero] at hle
  by_cases hk0 : k = 0
  · rw [hk, hk0, latticeTranslate_zero, sub_zero]
  · have := euclidNormVec_sub_lt_sub_translate hℓ hB hx hy hk0
    linarith
theorem add_latticeTranslate_notMem {x : Fin 4 → ℝ} (hx : x ∈ B) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    x + TestFunctions.latticeTranslate ℓ k ∉ B := by
  intro hy
  have h := euclidNormVec_sub_lt_sub_translate hℓ hB hx hy (neg_ne_zero.2 hk)
  have h₀ : x - (x + TestFunctions.latticeTranslate ℓ k) - TestFunctions.latticeTranslate ℓ (-k) = 0 := by
    rw [latticeTranslate_neg]
    abel
  rw [h₀, euclidNormVec_zero] at h
  exact absurd h (not_lt.2 (euclidNormVec_nonneg _))
theorem torusProj_injOn : InjOn (torusProj ℓ) B := by
  intro x hx y hy h
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h
  by_cases hk0 : k = 0
  · rw [hk, hk0, latticeTranslate_zero, add_zero]
  · exact absurd (hk ▸ hx) (add_latticeTranslate_notMem hℓ hB hy hk0)
section Functions
variable {E : Type*} [NormedAddCommGroup E] {f : (Fin 4 → ℝ) → E}
omit hℓ hB in
theorem eq_zero_of_notMem_of_supp_subset {Z : Type*} [Zero Z] {g : (Fin 4 → ℝ) → Z}
    {A : Set (Fin 4 → ℝ)} (h : fnSupport g ⊆ A) : ∀ x, x ∉ A → g x = 0 := by
  intro x hx
  by_contra h₀
  exact hx (h (subset_closure h₀))
theorem periodize_torusProj_of_mem (hf : ∀ x, x ∉ B → f x = 0) {x : Fin 4 → ℝ} (hx : x ∈ B) :
    TestFunctions.periodize ℓ f (torusProj ℓ x) = f x := by
  rw [TestFunctions.periodize_torusProj, TestFunctions.periodicSum,
    tsum_eq_single (0 : Fin 4 → ℤ) fun k hk => hf _ (add_latticeTranslate_notMem hℓ hB hx hk),
    latticeTranslate_zero, add_zero]
omit hℓ hB in
theorem periodize_eq_zero_off_image (hf : ∀ x, x ∉ B → f x = 0) {u : Torus4 ℓ}
    (hu : u ∉ torusProj ℓ '' B) : TestFunctions.periodize ℓ f u = 0 := by
  have h : ∀ k, f (TestFunctions.liftPoint u + TestFunctions.latticeTranslate ℓ k) = 0 := fun k =>
    hf _ fun hmem => hu ⟨_, hmem, by
      rw [TestFunctions.torusProj_add_latticeTranslate, TestFunctions.torusProj_liftPoint]⟩
  simp [TestFunctions.periodize, TestFunctions.periodicSum, h]
theorem mem_image_fnSupport_of_periodize_ne (hs : fnSupport f ⊆ B) {u : Torus4 ℓ}
    (hu : TestFunctions.periodize ℓ f u ≠ 0) : u ∈ torusProj ℓ '' fnSupport f := by
  have hz := eq_zero_of_notMem_of_supp_subset hs
  by_contra hn
  by_cases hb : u ∈ torusProj ℓ '' B
  · obtain ⟨x, hx, rfl⟩ := hb
    rw [periodize_torusProj_of_mem hℓ hB hz hx] at hu
    exact hn ⟨x, subset_closure hu, rfl⟩
  · exact hu (periodize_eq_zero_off_image hz hb)
theorem closureWrt_periodize (hc : IsCompact (fnSupport f)) (hs : fnSupport f ⊆ B) :
    MetricNotions.closureWrt (fun u v : Torus4 ℓ => torusEuclidNorm (u - v))
      {u | TestFunctions.periodize ℓ f u ≠ 0} = torusProj ℓ '' fnSupport f := by
  have hz := eq_zero_of_notMem_of_supp_subset hs
  have hP : IsCompact (torusProj ℓ '' fnSupport f) := hc.image continuous_torusProj
  ext u
  constructor
  · intro hu
    obtain ⟨y₀, hy₀, -⟩ := hu 1 one_pos
    have hne : (torusProj ℓ '' fnSupport f).Nonempty :=
      ⟨y₀, mem_image_fnSupport_of_periodize_ne hℓ hB hs hy₀⟩
    have hφ : ContinuousOn (fun w : Torus4 ℓ => torusEuclidNorm (u - w))
        (torusProj ℓ '' fnSupport f) :=
      (continuous_torusEuclidNorm.comp (continuous_const.sub continuous_id)).continuousOn
    obtain ⟨w, hw, hmin⟩ := hP.exists_isMinOn hne hφ
    have h₀ : torusEuclidNorm (u - w) ≤ 0 := by
      refine le_of_forall_pos_le_add fun r hr => ?_
      obtain ⟨y, hy, hyr⟩ := hu r hr
      have h₁ : torusEuclidNorm (u - w) ≤ torusEuclidNorm (u - y) :=
        hmin (mem_image_fnSupport_of_periodize_ne hℓ hB hs hy)
      have h₂ : torusEuclidNorm (u - y) < r := hyr
      linarith
    have h₁ : u - w = 0 :=
      eq_zero_of_torusEuclidNorm_eq_zero (le_antisymm h₀ (torusEuclidNorm_nonneg _))
    rwa [sub_eq_zero.1 h₁]
  · rintro ⟨x, hx, rfl⟩ r hr
    have hU : IsOpen {y : Fin 4 → ℝ | euclidNormVec (x - y) < r} :=
      isOpen_lt (continuous_euclidNormVec.comp (continuous_const.sub continuous_id))
        continuous_const
    have hxU : x ∈ {y : Fin 4 → ℝ | euclidNormVec (x - y) < r} := by
      simpa [euclidNormVec_zero] using hr
    obtain ⟨y, hyU, hy⟩ := mem_closure_iff.1 hx _ hU hxU
    have hyB : y ∈ B := hs (subset_closure hy)
    refine ⟨torusProj ℓ y, ?_, ?_⟩
    · change TestFunctions.periodize ℓ f (torusProj ℓ y) ≠ 0
      rw [periodize_torusProj_of_mem hℓ hB hz hyB]
      exact hy
    · have h := torusEuclidNorm_proj_sub_le (ℓ := ℓ) x y 0
      rw [latticeTranslate_zero, sub_zero] at h
      exact lt_of_le_of_lt h hyU
theorem tsupport_periodize (hc : IsCompact (fnSupport f)) (hs : fnSupport f ⊆ B) :
    tsupport (TestFunctions.periodize ℓ f) = torusProj ℓ '' fnSupport f := by
  have hz := eq_zero_of_notMem_of_supp_subset hs
  have hP : IsCompact (torusProj ℓ '' fnSupport f) := hc.image continuous_torusProj
  apply Subset.antisymm
  · exact closure_minimal (fun u hu => mem_image_fnSupport_of_periodize_ne hℓ hB hs hu) hP.isClosed
  · refine (image_closure_subset_closure_image continuous_torusProj).trans (closure_mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    change TestFunctions.periodize ℓ f (torusProj ℓ x) ≠ 0
    rw [periodize_torusProj_of_mem hℓ hB hz (hs (subset_closure hx))]
    exact hx
omit hℓ hB in
theorem setEuclidDist_image_of_isometric
    (hB' : ∀ x ∈ B, ∀ y ∈ B,
      torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) = euclidNormVec (x - y))
    {S S' : Set (Fin 4 → ℝ)} (hS : S ⊆ B) (hS' : S' ⊆ B) :
    setEuclidDist (torusProj ℓ '' S) (torusProj ℓ '' S') = infDist S S' := by
  unfold setEuclidDist infDist TestFunctions.setDistR4
  rw [iInf_image]
  refine iInf_congr fun a => iInf_congr fun ha => ?_
  rw [iInf_image]
  refine iInf_congr fun b => iInf_congr fun hb => ?_
  rw [hB' a (hS ha) b (hS' hb)]
theorem periodize_lipschitz_of_lipschitz {C : ℝ} (hC₀ : 0 ≤ C) (hf : ∀ x, x ∉ B → f x = 0)
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidNormVec (x - y)) (u v : Torus4 ℓ) :
    ‖TestFunctions.periodize ℓ f u - TestFunctions.periodize ℓ f v‖ ≤
      C * torusEuclidNorm (u - v) := by
  have hside : ∀ x ∈ B, ∀ w : Torus4 ℓ, w ∉ torusProj ℓ '' B →
      ‖f x‖ ≤ C * torusEuclidNorm (torusProj ℓ x - w) := by
    intro x hx w hw
    obtain ⟨k, hk⟩ := exists_torusEuclidNorm_proj_sub_eq (ℓ := ℓ) x (TestFunctions.liftPoint w)
    rw [TestFunctions.torusProj_liftPoint] at hk
    have hy : TestFunctions.liftPoint w + TestFunctions.latticeTranslate ℓ k ∉ B := fun hmem =>
      hw ⟨_, hmem, by
        rw [TestFunctions.torusProj_add_latticeTranslate, TestFunctions.torusProj_liftPoint]⟩
    have h := hC x (TestFunctions.liftPoint w + TestFunctions.latticeTranslate ℓ k)
    rw [hf _ hy, sub_zero, ← sub_sub] at h
    rwa [hk]
  by_cases hu : u ∈ torusProj ℓ '' B
  · obtain ⟨x, hx, rfl⟩ := hu
    by_cases hv : v ∈ torusProj ℓ '' B
    · obtain ⟨y, hy, rfl⟩ := hv
      rw [periodize_torusProj_of_mem hℓ hB hf hx, periodize_torusProj_of_mem hℓ hB hf hy,
        torusEuclidNorm_proj_sub_eq hℓ hB hx hy]
      exact hC x y
    · rw [periodize_torusProj_of_mem hℓ hB hf hx, periodize_eq_zero_off_image hf hv, sub_zero]
      exact hside x hx v hv
  · rw [periodize_eq_zero_off_image hf hu]
    by_cases hv : v ∈ torusProj ℓ '' B
    · obtain ⟨y, hy, rfl⟩ := hv
      rw [periodize_torusProj_of_mem hℓ hB hf hy, zero_sub, norm_neg, ← neg_sub,
        torusEuclidNorm_neg]
      exact hside y hy u hu
    · rw [periodize_eq_zero_off_image hf hv, sub_zero, norm_zero]
      exact mul_nonneg hC₀ (torusEuclidNorm_nonneg _)
theorem uniformNorm_periodize (hf : ∀ x, x ∉ B → f x = 0) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    TestFunctions.uniformNorm (TestFunctions.periodize ℓ f) = TestFunctions.uniformNorm f := by
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hbound : ∀ u, ‖TestFunctions.periodize ℓ f u‖ ≤ C := by
    intro u
    by_cases hu : u ∈ torusProj ℓ '' B
    · obtain ⟨x, hx, rfl⟩ := hu
      rw [periodize_torusProj_of_mem hℓ hB hf hx]
      exact hC x
    · rw [periodize_eq_zero_off_image hf hu, norm_zero]
      exact hC₀
  have hbf : BddAbove (range fun x => ‖f x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hbg : BddAbove (range fun u => ‖TestFunctions.periodize ℓ f u‖) :=
    ⟨C, by rintro _ ⟨u, rfl⟩; exact hbound u⟩
  have h₀f : 0 ≤ TestFunctions.uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
  have h₀g : 0 ≤ TestFunctions.uniformNorm (TestFunctions.periodize ℓ f) :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  apply le_antisymm
  · refine ciSup_le fun u => ?_
    by_cases hu : u ∈ torusProj ℓ '' B
    · obtain ⟨x, hx, rfl⟩ := hu
      rw [periodize_torusProj_of_mem hℓ hB hf hx]
      exact le_ciSup hbf x
    · rw [periodize_eq_zero_off_image hf hu, norm_zero]
      exact h₀f
  · refine ciSup_le fun x => ?_
    by_cases hx : x ∈ B
    · rw [← periodize_torusProj_of_mem hℓ hB hf hx]
      exact le_ciSup hbg (torusProj ℓ x)
    · rw [hf x hx, norm_zero]
      exact h₀g
end Functions
omit hℓ hB in
theorem continuous_of_isLipschitzFor {E : Type*} [NormedAddCommGroup E] {f : (Fin 4 → ℝ) → E}
    (h : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f) : Continuous f := by
  obtain ⟨C, hC₀, hC⟩ := h
  have hl : LipschitzWith (Real.toNNReal (C * 2)) f := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    calc ‖f x - f y‖ ≤ C * euclidNormVec (x - y) := hC x y
      _ ≤ C * (2 * ‖x - y‖) := mul_le_mul_of_nonneg_left (euclidNormVec_le_two_mul_norm _) hC₀
      _ = C * 2 * ‖x - y‖ := by ring
  exact hl.continuous
omit hℓ hB in
theorem continuous_of_lipschitz_torus {E : Type*} [NormedAddCommGroup E]
    {g : Torus4 ℓ → E} {C : ℝ} (hC : ∀ u v, ‖g u - g v‖ ≤ C * torusEuclidNorm (u - v)) :
    Continuous g := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun v => hC v u) ?_
  have h : Continuous fun v : Torus4 ℓ => C * torusEuclidNorm (v - u) :=
    continuous_const.mul (continuous_torusEuclidNorm.comp (continuous_id.sub continuous_const))
  simpa [torusEuclidNorm_zero] using h.tendsto u
end Torus
section Ball
variable {ℓ ρ : ℝ} {E : Type*} [NormedAddCommGroup E] {f : (Fin 4 → ℝ) → E}
theorem mem_ballOrigin_iff {x : Fin 4 → ℝ} : x ∈ ballOrigin ρ ↔ euclidNormVec x < ρ := Iff.rfl
theorem lipschitz_of_periodize_lipschitz (hℓ : 0 < ℓ)
    (hB : ∀ x ∈ ballOrigin ρ, ∀ y ∈ ballOrigin ρ, euclidNormVec (x - y) < ℓ / 2)
    (hc : IsCompact (fnSupport f)) (hs : fnSupport f ⊆ ballOrigin ρ) {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ u v : Torus4 ℓ,
      ‖TestFunctions.periodize ℓ f u - TestFunctions.periodize ℓ f v‖ ≤
        C * torusEuclidNorm (u - v)) (x y : Fin 4 → ℝ) :
    ‖f x - f y‖ ≤ C * euclidNormVec (x - y) := by
  have hz := eq_zero_of_notMem_of_supp_subset hs
  have hin : ∀ x ∈ ballOrigin ρ, ∀ y ∈ ballOrigin ρ,
      ‖f x - f y‖ ≤ C * euclidNormVec (x - y) := by
    intro x hx y hy
    have h := hC (torusProj ℓ x) (torusProj ℓ y)
    rwa [periodize_torusProj_of_mem hℓ hB hz hx, periodize_torusProj_of_mem hℓ hB hz hy,
      torusEuclidNorm_proj_sub_eq hℓ hB hx hy] at h
  have hcross : ∀ x ∈ fnSupport f, ∀ y, y ∉ ballOrigin ρ →
      ‖f x - f y‖ ≤ C * euclidNormVec (x - y) := by
    intro x hx y hy
    obtain ⟨z₀, hz₀, hmax⟩ := hc.exists_isMaxOn ⟨x, hx⟩ continuous_euclidNormVec.continuousOn
    have hz₀ρ : euclidNormVec z₀ < ρ := hs hz₀
    have hxz : euclidNormVec x ≤ euclidNormVec z₀ := hmax hx
    have hyρ : ρ ≤ euclidNormVec y := not_lt.1 hy
    set c := (euclidNormVec z₀ + ρ) / 2 with hcdef
    have hg : Continuous fun τ : ℝ => euclidNormVec (x + τ • (y - x)) :=
      continuous_euclidNormVec.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hmem : c ∈ Icc ((fun τ : ℝ => euclidNormVec (x + τ • (y - x))) 0)
        ((fun τ : ℝ => euclidNormVec (x + τ • (y - x))) 1) := by
      simp only [zero_smul, add_zero, one_smul, add_sub_cancel]
      constructor <;> linarith
    obtain ⟨τ, hτ, hτc⟩ := intermediate_value_Icc zero_le_one hg.continuousOn hmem
    have hτc' : euclidNormVec (x + τ • (y - x)) = c := hτc
    have hzK : x + τ • (y - x) ∉ fnSupport f := fun hmem' => by
      have : euclidNormVec (x + τ • (y - x)) ≤ euclidNormVec z₀ := hmax hmem'
      linarith
    have hzB : x + τ • (y - x) ∈ ballOrigin ρ := by
      rw [mem_ballOrigin_iff, hτc']
      linarith
    have hfz : f (x + τ • (y - x)) = 0 := by
      by_contra h₀
      exact hzK (subset_closure h₀)
    rw [hz y hy]
    have h₁ := hin x (hs hx) _ hzB
    rw [hfz] at h₁
    refine h₁.trans (mul_le_mul_of_nonneg_left ?_ hC₀)
    have h₂ : x - (x + τ • (y - x)) = τ • (x - y) := by
      rw [sub_add_cancel_left, ← smul_neg, neg_sub]
    rw [h₂, euclidNormVec_smul, abs_of_nonneg hτ.1]
    exact mul_le_of_le_one_left (euclidNormVec_nonneg _) hτ.2
  have hoff : ∀ x, x ∉ fnSupport f → f x = 0 := fun x hx => by
    by_contra h₀
    exact hx (subset_closure h₀)
  by_cases hx : x ∈ ballOrigin ρ
  · by_cases hy : y ∈ ballOrigin ρ
    · exact hin x hx y hy
    · by_cases hxs : x ∈ fnSupport f
      · exact hcross x hxs y hy
      · rw [hoff x hxs, hz y hy, sub_zero, norm_zero]
        exact mul_nonneg hC₀ (euclidNormVec_nonneg _)
  · by_cases hys : y ∈ fnSupport f
    · have h := hcross y hys x hx
      rwa [norm_sub_rev, euclidNormVec_sub_comm] at h
    · rw [hz x hx, hoff y hys, sub_zero, norm_zero]
      exact mul_nonneg hC₀ (euclidNormVec_nonneg _)
theorem lipConstTorus_periodize (hℓ : 0 < ℓ)
    (hB : ∀ x ∈ ballOrigin ρ, ∀ y ∈ ballOrigin ρ, euclidNormVec (x - y) < ℓ / 2)
    (hc : IsCompact (fnSupport f)) (hs : fnSupport f ⊆ ballOrigin ρ) :
    TestFunctions.lipConstTorus (TestFunctions.periodize ℓ f) = TestFunctions.lipConstR4 f := by
  unfold TestFunctions.lipConstTorus TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
  congr 1
  ext C
  constructor
  · rintro ⟨hC₀, hC⟩
    exact ⟨hC₀, lipschitz_of_periodize_lipschitz hℓ hB hc hs hC₀ hC⟩
  · rintro ⟨hC₀, hC⟩
    exact ⟨hC₀, periodize_lipschitz_of_lipschitz hℓ hB hC₀ (eq_zero_of_notMem_of_supp_subset hs) hC⟩
end Ball
section Exponent
variable (D : Setup) (m : ℕ+)
theorem exponentSide_pos : 0 < exponentSide D m := by
  have hL : (0 : ℝ) < D.L := by exact_mod_cast D.one_lt_L.trans' Nat.zero_lt_one
  unfold exponentSide PeriodicLattice.torusSide
  positivity
variable {D m}
theorem euclidNormVec_sub_lt_half_of_mem_ballOrigin {ρ : ℝ} (hρ : ρ ≤ maxBallRadius D m) :
    ∀ x ∈ ballOrigin ρ, ∀ y ∈ ballOrigin ρ, euclidNormVec (x - y) < exponentSide D m / 2 := by
  intro x hx y hy
  have h₁ : euclidNormVec x < ρ := hx
  have h₂ : euclidNormVec y < ρ := hy
  have h₃ := euclidNormVec_add_le x (-y)
  rw [euclidNormVec_neg, ← sub_eq_add_neg] at h₃
  have h₄ : exponentSide D m / 2 = (D.L : ℝ) ^ (m : ℕ) := by
    unfold exponentSide PeriodicLattice.torusSide
    ring
  have h₅ : ρ ≤ ((D.L : ℝ) ^ (m : ℕ) - 2) / 2 := hρ
  rw [h₄]
  linarith
theorem torusDistIsLeastOverLifts_holds : TorusDistIsLeastOverLifts D m := by
  intro x y
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨k, hk⟩ := exists_torusEuclidNorm_proj_sub_eq (ℓ := exponentSide D m) x y
    exact ⟨k, hk.symm⟩
  · rintro _ ⟨k, rfl⟩
    exact torusEuclidNorm_proj_sub_le x y k
  · have h := torusEuclidNorm_proj_sub_le (ℓ := exponentSide D m) x y 0
    rwa [latticeTranslate_zero, sub_zero] at h
theorem projOnBall_holds {ρ : ℝ} (hρ : ρ ≤ maxBallRadius D m) : ProjOnBall D m ρ := by
  have hB := euclidNormVec_sub_lt_half_of_mem_ballOrigin hρ
  have hℓ := exponentSide_pos D m
  exact ⟨fun x hx y hy k hk => euclidNormVec_sub_lt_sub_translate hℓ hB hx hy hk,
    fun x hx y hy => torusEuclidNorm_proj_sub_eq hℓ hB hx hy, torusProj_injOn hℓ hB,
    fun x hx k hk => add_latticeTranslate_notMem hℓ hB hx hk⟩
theorem torusSupp_periodize {ρ : ℝ} (hρ : ρ ≤ maxBallRadius D m) {E : Type*}
    [NormedAddCommGroup E] {f : (Fin 4 → ℝ) → E} (hf : SupportedIn f (ballOrigin ρ)) :
    torusSupp D m (TestFunctions.periodize (exponentSide D m) f) = proj D m '' fnSupport f :=
  closureWrt_periodize (exponentSide_pos D m) (euclidNormVec_sub_lt_half_of_mem_ballOrigin hρ)
    hf.1 hf.2
section Functions
variable {ρ : ℝ} (hρ : ρ ≤ maxBallRadius D m) (𝕜 : Type) [RCLike 𝕜]
include hρ
omit hρ in
theorem supportedIn_linearCombination {f h : (Fin 4 → ℝ) → 𝕜} {c c' : 𝕜}
    (hf : SupportedIn f (ballOrigin ρ)) (hh : SupportedIn h (ballOrigin ρ)) :
    SupportedIn (c • f + c' • h) (ballOrigin ρ) := by
  have hsub : fnSupport (c • f + c' • h) ⊆ fnSupport f ∪ fnSupport h := by
    refine closure_minimal ?_ (isClosed_closure.union isClosed_closure)
    intro x hx
    by_contra hn
    have h₁ : f x = 0 := by
      by_contra h₀
      exact hn (Or.inl (subset_closure h₀))
    have h₂ : h x = 0 := by
      by_contra h₀
      exact hn (Or.inr (subset_closure h₀))
    exact hx (by simp [h₁, h₂])
  exact ⟨(hf.1.union hh.1).of_isClosed_subset isClosed_closure hsub,
    hsub.trans (union_subset hf.2 hh.2)⟩
theorem periodizeValues_holds : PeriodizeValues D m ρ 𝕜 := by
  have hB := euclidNormVec_sub_lt_half_of_mem_ballOrigin hρ
  have hℓ := exponentSide_pos D m
  refine ⟨fun f hf => ?_, fun f h c c' hf hh => ?_⟩
  · have hz := eq_zero_of_notMem_of_supp_subset hf.2
    refine ⟨fun x hx => periodize_torusProj_of_mem hℓ hB hz hx,
      fun u hu => periodize_eq_zero_off_image hz hu, ?_, torusSupp_periodize hρ hf⟩
    have hz' : ∀ x, x ∉ ballOrigin ρ → starRingEnd 𝕜 (f x) = 0 := fun x hx => by
      rw [hz x hx, map_zero]
    funext u
    by_cases hu : u ∈ proj D m '' ballOrigin ρ
    · obtain ⟨x, hx, rfl⟩ := hu
      rw [periodize_torusProj_of_mem hℓ hB hz' hx, periodize_torusProj_of_mem hℓ hB hz hx]
    · rw [periodize_eq_zero_off_image hz' hu, periodize_eq_zero_off_image hz hu, map_zero]
  · have hcomb := supportedIn_linearCombination 𝕜 (c := c) (c' := c') hf hh
    refine ⟨hcomb, ?_⟩
    have hzf := eq_zero_of_notMem_of_supp_subset hf.2
    have hzh := eq_zero_of_notMem_of_supp_subset hh.2
    have hzc := eq_zero_of_notMem_of_supp_subset hcomb.2
    funext u
    by_cases hu : u ∈ proj D m '' ballOrigin ρ
    · obtain ⟨x, hx, rfl⟩ := hu
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [periodize_torusProj_of_mem hℓ hB hzc hx, periodize_torusProj_of_mem hℓ hB hzf hx,
        periodize_torusProj_of_mem hℓ hB hzh hx]
      simp
    · simp only [Pi.add_apply, Pi.smul_apply]
      rw [periodize_eq_zero_off_image hzc hu, periodize_eq_zero_off_image hzf hu,
        periodize_eq_zero_off_image hzh hu]
      simp
theorem periodizeNorms_holds : PeriodizeNorms D m ρ 𝕜 := by
  have hB := euclidNormVec_sub_lt_half_of_mem_ballOrigin hρ
  have hℓ := exponentSide_pos D m
  intro f hf him hlip
  have hz := eq_zero_of_notMem_of_supp_subset hf.2
  have hcont := continuous_of_isLipschitzFor hlip
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hf.1
  have hsup := uniformNorm_periodize hℓ hB hz hC
  have hLip := lipConstTorus_periodize hℓ hB hf.1 hf.2
  refine ⟨fun u => ?_, ?_, hsup, hLip, ?_⟩
  · by_cases hu : u ∈ proj D m '' ballOrigin ρ
    · obtain ⟨x, hx, rfl⟩ := hu
      rw [periodize_torusProj_of_mem hℓ hB hz hx]
      exact him x
    · rw [periodize_eq_zero_off_image hz hu, map_zero]
  · obtain ⟨K, hK₀, hK⟩ := hlip
    exact ⟨K, hK₀, periodize_lipschitz_of_lipschitz hℓ hB hK₀ hz hK⟩
  · unfold TestFunctions.sharpNormTorus TestFunctions.sharpNormR4
    rw [hsup, hLip]
theorem periodizeSupports_holds : PeriodizeSupports D m ρ 𝕜 := by
  have hB := euclidNormVec_sub_lt_half_of_mem_ballOrigin hρ
  have hℓ := exponentSide_pos D m
  refine ⟨fun f h hf hh => ?_, fun f x R hf _ _ hR => ?_⟩
  · rw [torusSupp_periodize hρ hf, torusSupp_periodize hρ hh]
    exact setEuclidDist_image_of_isometric
      (fun x hx y hy => torusEuclidNorm_proj_sub_eq hℓ hB hx hy) hf.2 hh.2
  · rw [torusSupp_periodize hρ hf]
    rintro _ ⟨y, hy, rfl⟩
    have h := torusEuclidNorm_proj_sub_le (ℓ := exponentSide D m) y x 0
    rw [latticeTranslate_zero, sub_zero] at h
    exact h.trans (hR hy)
end Functions
theorem periodizeTuples_holds (hsep : SubfamiliesAndGaps.Statement) {ρ : ℝ}
    (hρ : ρ ≤ maxBallRadius D m) : PeriodizeTuples D m ρ := by
  have hB := euclidNormVec_sub_lt_half_of_mem_ballOrigin hρ
  have hℓ := exponentSide_pos D m
  intro n hn f hf hs
  have hz := fun i => eq_zero_of_notMem_of_supp_subset (hs i)
  have hentry : ∀ i, SchwingerFunctions.periodizeAll D.L m f i =
      TestFunctions.periodize (exponentSide D m) (f i) := fun _ => rfl
  have hlipT : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : ExponentTorus D m,
      ‖SchwingerFunctions.periodizeAll D.L m f i u - SchwingerFunctions.periodizeAll D.L m f i v‖ ≤
        K * torusEuclidNorm (u - v) := fun i => by
    obtain ⟨K, hK₀, hK⟩ := hf.1 i
    exact ⟨K, hK₀, periodize_lipschitz_of_lipschitz hℓ hB hK₀ (hz i) hK⟩
  have hbdd : ∀ i, TestFunctions.IsBoundedFun (SchwingerFunctions.periodizeAll D.L m f i) :=
    fun i => by
    obtain ⟨C, hC⟩ := (continuous_of_isLipschitzFor (hf.1 i)).bounded_above_of_compact_support
      (hf.2.1 i)
    refine ⟨C, fun u => ?_⟩
    by_cases hu : u ∈ proj D m '' ballOrigin ρ
    · obtain ⟨x, hx, rfl⟩ := hu
      rw [hentry, periodize_torusProj_of_mem hℓ hB (hz i) hx]
      exact hC x
    · rw [hentry, periodize_eq_zero_off_image (hz i) hu, norm_zero]
      exact (norm_nonneg _).trans (hC 0)
  have hmeas : ∀ i, Measurable (SchwingerFunctions.periodizeAll D.L m f i) := fun i => by
    obtain ⟨K, -, hK⟩ := hlipT i
    exact (continuous_of_lipschitz_torus hK).measurable
  have hts : ∀ i, tsupport (SchwingerFunctions.periodizeAll D.L m f i) =
      proj D m '' fnSupport (f i) :=
    fun i => tsupport_periodize hℓ hB (hf.2.1 i) (hs i)
  have hiso : ∀ x ∈ ballOrigin ρ, ∀ y ∈ ballOrigin ρ,
      torusEuclidNorm (torusProj (exponentSide D m) x - torusProj (exponentSide D m) y) =
        euclidNormVec (x - y) :=
    fun x hx y hy => torusEuclidNorm_proj_sub_eq hℓ hB hx hy
  have hdist : ∀ i k, setEuclidDist (proj D m '' fnSupport (f i)) (proj D m '' fnSupport (f k)) =
      infDist (fnSupport (f i)) (fnSupport (f k)) := fun i k =>
    setEuclidDist_image_of_isometric hiso (hs i) (hs k)
  have hsepT : ∀ d : ℝ, 0 < d → ENNReal.ofReal d ≤ minSuppGap hn f hf →
      TestFunctions.HasSeparatedSupportsTorus (SchwingerFunctions.periodizeAll D.L m f) d := by
    intro d hd hle
    refine ⟨hd, fun i k hik => ?_⟩
    rw [hts i, hts k, hdist i k]
    exact hle.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le _ hik)))
  refine ⟨hbdd, hmeas, fun d hd hle => hsepT d hd hle, ⟨hbdd, hmeas, ?_⟩, ?_, ?_⟩
  · obtain ⟨r, hr₀, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hsep.2.2.2.1 n hn f hf).1
    have hr₀' : (0 : ℝ) < r := by exact_mod_cast hr₀
    refine ⟨r, hsepT r hr₀' ?_⟩
    rw [ENNReal.ofReal_coe_nnreal]
    exact hr.le
  · intro ρ' hρ'₀ hρ' hs' g hg
    have hB' := euclidNormVec_sub_lt_half_of_mem_ballOrigin hρ'
    have hgeq : g = SchwingerFunctions.periodizeAll D.L m f := by
      funext i u
      have hz' := eq_zero_of_notMem_of_supp_subset (hs' i)
      by_cases hu : u ∈ proj D m '' ballOrigin ρ'
      · obtain ⟨x, hx, rfl⟩ := hu
        rw [hentry, periodize_torusProj_of_mem hℓ hB' hz' hx]
        exact (hg i).1 x hx
      · rw [hentry, periodize_eq_zero_off_image hz' hu]
        exact (hg i).2 u hu
    refine ⟨hgeq, fun K β => ⟨?_, ?_⟩⟩
    · rw [hgeq]
      rfl
    · rw [hgeq]
      obtain ⟨q, rfl⟩ : ∃ q, n = q + 2 := ⟨n - 2, by omega⟩
      rfl
  · rintro d R hd hR hRm ⟨hf', hrad, hle⟩
    have hsupT : ∀ i, (SourcesAndGluing.Ambient.torus m).supp (gluingSetup D m)
        (SchwingerFunctions.periodizeAll D.L m f i) = proj D m '' fnSupport (f i) := fun i =>
      closureWrt_periodize hℓ hB (hf.2.1 i) (hs i)
    refine And.intro (fun i => ?_) (And.intro (fun i => ?_) (fun i k hik => ?_))
    · exact hlipT i
    · obtain ⟨x, hx⟩ := hrad i
      refine ⟨proj D m x, ?_⟩
      rw [hsupT i]
      rintro _ ⟨y, hy, rfl⟩
      have h := torusEuclidNorm_proj_sub_le (ℓ := exponentSide D m) y x 0
      rw [latticeTranslate_zero, sub_zero] at h
      exact h.trans (hx hy)
    · rw [hsupT i, hsupT k]
      exact (hle.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le _ hik)))).trans_eq
        (hdist i k).symm
end Exponent
theorem statement_holds (hsep : SubfamiliesAndGaps.Statement) : Statement := by
  intro D m
  refine ⟨torusDistIsLeastOverLifts_holds, fun ρ _ hρ => ⟨projOnBall_holds hρ, fun 𝕜 _ =>
    ⟨periodizeValues_holds hρ 𝕜, periodizeNorms_holds hρ 𝕜, periodizeSupports_holds hρ 𝕜⟩,
    periodizeTuples_holds hsep hρ⟩⟩
end YangMills.Construction.ToriLimits.ExponentTorusPeriodization
end
