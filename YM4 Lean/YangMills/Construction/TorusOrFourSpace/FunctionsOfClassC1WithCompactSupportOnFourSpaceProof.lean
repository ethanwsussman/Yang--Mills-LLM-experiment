import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1WithCompactSupportOnFourSpace
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.GrowingDomains.CompactSupportC1
open YangMills.Construction.PeriodicSpace.Kind YangMills.Construction.TorusMetric
theorem abs_coord_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem quotDist_euclidean (P : Params) (x y : Fin 4 → ℝ) :
    quotDist P euclidean x y = euclidNormVec (x - y) := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_euclidean <;> assumption
theorem isOpenWrt_of_isOpen (P : Params) {U : Set (Fin 4 → ℝ)} (hU : IsOpen U) :
    MetricNotions.IsOpenWrt (quotDist P euclidean) U := by
  intro (x : Fin 4 → ℝ) hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨r, hr, fun (y : Fin 4 → ℝ) hy => hball ?_⟩
  have hy' : euclidNormVec (x - y) < r := lt_of_eq_of_lt (quotDist_euclidean P x y).symm hy
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro i
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (abs_coord_le_euclidNormVec (x - y) i) hy'
theorem bddAbove_of_isCompactWrt (P : Params) {K : Set (Fin 4 → ℝ)}
    (hK : MetricNotions.IsCompactWrt (quotDist P euclidean) K) {φ : (Fin 4 → ℝ) → ℝ}
    (hφ : Continuous φ) : ∃ C : ℝ, ∀ x ∈ K, φ x ≤ C := by
  obtain ⟨W, hW, hfin, hcov⟩ := hK (Set.range fun n : ℕ => {x | φ x < n})
    (by
      rintro _ ⟨n, rfl⟩
      exact isOpenWrt_of_isOpen P (isOpen_lt hφ continuous_const))
    (by
      intro x _
      obtain ⟨n, hn⟩ := exists_nat_gt (φ x)
      exact ⟨_, ⟨n, rfl⟩, hn⟩)
  have hex : ∀ U ∈ W, ∃ n : ℕ, {x | φ x < n} = U := fun U hU => hW hU
  choose! f hf using hex
  refine ⟨((hfin.toFinset.sup f : ℕ) : ℝ), fun x hx => ?_⟩
  obtain ⟨U, hU, hxU⟩ := hcov hx
  rw [← hf U hU] at hxU
  have hle : f U ≤ hfin.toFinset.sup f := Finset.le_sup (hfin.mem_toFinset.2 hU)
  exact (le_of_lt hxU).trans (by exact_mod_cast hle)
def axisGradient (F : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => fderiv ℝ F x (Pi.single i 1)
theorem partialDerivR4_eq_axisGradient {F : (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) (i : Fin 4)
    (x : Fin 4 → ℝ) : TestFunctions.partialDerivR4 i F x = axisGradient F x i := by
  have hd : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)) := by
    simpa using ((hF.differentiable (by simp)) x).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single i (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single i (1 : ℝ) : Fin 4 → ℝ)).const_add x
  exact (hd.comp_hasDerivAt 0 hl).deriv
theorem continuous_euclidNormVec_axisGradient {F : (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous fun x => euclidNormVec (axisGradient F x) :=
  continuous_euclidNormVec.comp
    (continuous_pi fun i => (hF.continuous_fderiv (by simp)).clm_apply continuous_const)
theorem abs_fderiv_apply_le (F : (Fin 4 → ℝ) → ℝ) (z v : Fin 4 → ℝ) :
    |fderiv ℝ F z v| ≤ euclidNormVec (axisGradient F z) * euclidNormVec v := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : fderiv ℝ F z v = ∑ i, axisGradient F z i * v i := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  rw [hsum]
  unfold euclidNormVec
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
theorem abs_sub_le_of_gradient_bound {F : (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ}
    (hC : ∀ z, euclidNormVec (axisGradient F z) ≤ C) (x y : Fin 4 → ℝ) :
    |F x - F y| ≤ C * euclidNormVec (x - y) := by
  have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => F (y + s • (x - y)))
      (fderiv ℝ F (y + t • (x - y)) (x - y)) t := by
    intro t
    have hd : HasFDerivAt F (fderiv ℝ F (y + t • (x - y))) (y + t • (x - y)) :=
      ((hF.differentiable (by simp)) _).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
    exact hd.comp_hasDerivAt t hl
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => F (y + s • (x - y)))
    (f' := fun t => fderiv ℝ F (y + t • (x - y)) (x - y))
    (C := C * euclidNormVec (x - y))
    (fun t _ => (hder t).hasDerivWithinAt)
    (fun t _ => by
      rw [Real.norm_eq_abs]
      exact (abs_fderiv_apply_le F _ _).trans
        (mul_le_mul_of_nonneg_right (hC _) (Real.sqrt_nonneg _)))
  simpa [Real.norm_eq_abs] using hmv
theorem gradVec_euclidean_eq (P : Params) {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (y : Fin 4 → ℝ) : gradVec P euclidean f y = axisGradient f y := by
  funext i
  have hspec := Classical.epsilon_spec
    (p := fun v : euclidean.Pt P → ℝ =>
      v ∘ quotMap P euclidean = TestFunctions.partialDerivR4 i (f ∘ quotMap P euclidean))
    ⟨TestFunctions.partialDerivR4 i (f ∘ quotMap P euclidean), rfl⟩
  have hy := congrFun hspec y
  exact hy.trans (partialDerivR4_eq_axisGradient hf i y)
theorem exists_axisGradient_bound (P : Params) {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hK : IsCompactQ P euclidean (supportQ P euclidean f)) :
    ∃ C : ℝ, ∀ z, euclidNormVec (axisGradient f z) ≤ C := by
  obtain ⟨C, hC⟩ := bddAbove_of_isCompactWrt P hK (continuous_euclidNormVec_axisGradient hf)
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hz : z ∈ supportQ P euclidean f
  · exact (hC z hz).trans (le_max_left _ _)
  · have hzero : axisGradient f z = 0 := by
      have hnot : ¬ ∀ r : ℝ, 0 < r → ∃ y ∈ {y | f y ≠ 0}, quotDist P euclidean z y < r := hz
      push Not at hnot
      obtain ⟨r, hr, hoff⟩ := hnot
      have hcont : Continuous fun y : Fin 4 → ℝ => euclidNormVec (z - y) :=
        continuous_euclidNormVec.comp (continuous_const.sub continuous_id)
      have hz0 : euclidNormVec (z - z) < r := by simpa [euclidNormVec] using hr
      have hev : f =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const hz0] with y hy
        by_contra hne
        exact absurd (lt_of_eq_of_lt (quotDist_euclidean P z y) hy) (not_lt.2 (hoff y hne))
      funext i
      simp [axisGradient, hev.fderiv_eq]
    rw [hzero]
    simp [euclidNormVec]
theorem main_bounds (P : Params) (f : (Fin 4 → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hK : IsCompactQ P euclidean (supportQ P euclidean f)) :
    vecSupNormQ P euclidean (gradVec P euclidean f) < ∞ ∧
      (∀ x y : euclidean.Pt P,
        ENNReal.ofReal |f x - f y| ≤
          vecSupNormQ P euclidean (gradVec P euclidean f) *
            ENNReal.ofReal (quotDist P euclidean x y)) ∧
      IsLipschitzQ P euclidean f ∧
      ENNReal.ofReal (lipConstQ P euclidean f) ≤
        vecSupNormQ P euclidean (gradVec P euclidean f) ∧
      sharpNormQ P euclidean f ≤
        ENNReal.ofReal (40 * P.M) * GrowingDomains.cOneNorm P euclidean f := by
  have hM : (1 : ℝ) ≤ 40 * P.M := by linarith [P.one_le_M]
  obtain ⟨C, hC⟩ := exists_axisGradient_bound P hf hK
  have hlen : ∀ y : Fin 4 → ℝ,
      euclidNormVec (gradVec P euclidean f y) = euclidNormVec (axisGradient f y) :=
    fun y => by rw [gradVec_euclidean_eq P hf y]
  have hfin : vecSupNormQ P euclidean (gradVec P euclidean f) < ∞ := by
    refine lt_of_le_of_lt (iSup_le fun y => ?_) (ENNReal.ofReal_lt_top (r := C))
    rw [hlen y]
    exact ENNReal.ofReal_le_ofReal (hC y)
  set N := vecSupNormQ P euclidean (gradVec P euclidean f) with hN
  have hNtop : N ≠ ∞ := hfin.ne
  have hbound : ∀ z, euclidNormVec (axisGradient f z) ≤ N.toReal := by
    intro z
    rw [← ENNReal.ofReal_le_iff_le_toReal hNtop, ← hlen z]
    exact le_iSup (fun y => ENNReal.ofReal (euclidNormVec (gradVec P euclidean f y))) z
  have hpt : ∀ x y : Fin 4 → ℝ, |f x - f y| ≤ N.toReal * quotDist P euclidean x y := by
    intro x y
    exact (abs_sub_le_of_gradient_bound hf hbound x y).trans_eq
      (congrArg (N.toReal * ·) (quotDist_euclidean P x y).symm)
  have hlip : lipConstQ P euclidean f ≤ N.toReal :=
    csInf_le ⟨0, fun _ hL => hL.1⟩ ⟨ENNReal.toReal_nonneg, hpt⟩
  have hlipN : ENNReal.ofReal (lipConstQ P euclidean f) ≤ N := by
    rw [ENNReal.ofReal_le_iff_le_toReal hNtop]
    exact hlip
  refine ⟨hfin, fun x y => ?_, ⟨N.toReal, ENNReal.toReal_nonneg, hpt⟩, hlipN, ?_⟩
  · calc ENNReal.ofReal |f x - f y|
        ≤ ENNReal.ofReal (N.toReal * quotDist P euclidean x y) :=
          ENNReal.ofReal_le_ofReal (hpt x y)
      _ = N * ENNReal.ofReal (quotDist P euclidean x y) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hNtop]
  · have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (40 * P.M) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hM
    have hc1 : GrowingDomains.cOneNorm P euclidean f =
        max (supNormQ P euclidean f) N := rfl
    rw [hc1]
    refine max_le ?_ ?_
    · calc supNormQ P euclidean f
          = 1 * supNormQ P euclidean f := (one_mul _).symm
        _ ≤ ENNReal.ofReal (40 * P.M) * supNormQ P euclidean f := by gcongr
        _ ≤ ENNReal.ofReal (40 * P.M) * max (supNormQ P euclidean f) N := by
            gcongr
            exact le_max_left _ _
    · rw [ENNReal.ofReal_mul (by linarith)]
      gcongr
      exact hlipN.trans (le_max_right _ _)
theorem compactlySupportedC1Bounds_holds : GrowingDomains.CompactlySupportedC1Bounds :=
  fun P _ f hf hK => main_bounds P f hf hK
end YangMills.Construction.PeriodicSpace.GrowingDomains.CompactSupportC1
