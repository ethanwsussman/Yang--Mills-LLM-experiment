import YangMills.Construction.InfiniteLattice.TransportToATorusProof
import YangMills.Construction.ReflectionPositivity.GradientOfAFunctionOfClassC1AtALift
import YangMills.Construction.ReflectionPositivity.ModulusOfAFunctionOfClassC1TendsToZero
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal
open YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
namespace SmoothModulusVanishes
variable {𝕜 : Type} [RCLike 𝕜]
theorem vecLength_nonneg (v : Fin 4 → 𝕜) : 0 ≤ vecLength v := Real.sqrt_nonneg _
theorem vecLength_sub_le (v w : Fin 4 → 𝕜) :
    vecLength (v - w) ≤ vecLength v + vecLength w := by
  have key : ∀ u : Fin 4 → 𝕜,
      vecLength u = ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (Fin 4))‖ := by
    intro u
    simp [vecLength, EuclideanSpace.norm_eq]
  rw [key, key, key, WithLp.toLp_sub]
  exact norm_sub_le _ _
theorem vecLength_le_two_mul_norm (v : Fin 4 → 𝕜) : vecLength v ≤ 2 * ‖v‖ := by
  have h : ∑ μ, ‖v μ‖ ^ 2 ≤ (2 * ‖v‖) ^ 2 := by
    calc ∑ μ, ‖v μ‖ ^ 2 ≤ ∑ _μ : Fin 4, ‖v‖ ^ 2 :=
          Finset.sum_le_sum fun μ _ => by
            gcongr
            exact norm_le_pi_norm v μ
      _ = (2 * ‖v‖) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  exact Real.sqrt_le_iff.2 ⟨by positivity, h⟩
theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
theorem dist_le_euclidNormVec (y y' : Fin 4 → ℝ) : dist y y' ≤ euclidNormVec (y - y') := by apply _root_.YangMills.Construction.PeriodicTransport.dist_le_euclidNormVec <;> assumption
theorem partialDerivR4_eq_fderiv {F : (Fin 4 → ℝ) → 𝕜} (hF : TestFunctions.IsC1R4 F) (μ : Fin 4)
    (y : Fin 4 → ℝ) : TestFunctions.partialDerivR4 μ F y = fderiv ℝ F y (Pi.single μ 1) := by
  have hd : HasFDerivAt F (fderiv ℝ F y) y :=
    ((ContDiff.differentiable hF (by norm_num)) y).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => y + t • Pi.single μ (1 : ℝ)) (Pi.single μ (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ))).const_add y
  exact (HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd hline (by simp)).deriv
theorem gradR4_eq_fderiv {F : (Fin 4 → ℝ) → 𝕜} (hF : TestFunctions.IsC1R4 F) :
    gradR4 F = fun y μ => fderiv ℝ F y (Pi.single μ 1) := by
  funext y μ
  exact partialDerivR4_eq_fderiv hF μ y
theorem continuous_gradR4 {F : (Fin 4 → ℝ) → 𝕜} (hF : TestFunctions.IsC1R4 F) :
    Continuous (gradR4 F) := by
  rw [gradR4_eq_fderiv hF]
  exact continuous_pi fun μ =>
    (ContDiff.continuous_fderiv hF (by norm_num)).clm_apply continuous_const
theorem isCompact_of_isCompactWrt {Z : Set (Fin 4 → ℝ)}
    (h : MetricNotions.IsCompactWrt InfiniteLattice.euclidDist Z) : IsCompact Z := by
  rw [isCompact_iff_finite_subcover]
  intro ι U hU hcov
  have hopen : ∀ V ∈ Set.range U, MetricNotions.IsOpenWrt InfiniteLattice.euclidDist V := by
    rintro _ ⟨i, rfl⟩ x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hU i) x hx
    refine ⟨r, hr, fun y hy => hball ?_⟩
    rw [Metric.mem_ball, dist_comm]
    exact (dist_le_euclidNormVec x y).trans_lt hy
  obtain ⟨𝒰, h𝒰, hfin, hsub⟩ := h (Set.range U) hopen (by rwa [Set.sUnion_range])
  obtain ⟨t, -, htf, hcov'⟩ := (Set.exists_subset_image_finite_and (f := U) (s := Set.univ)
    (p := fun 𝒱 => Z ⊆ ⋃₀ 𝒱)).1 ⟨𝒰, by simpa using h𝒰, hfin, hsub⟩
  refine ⟨htf.toFinset, fun x hx => ?_⟩
  obtain ⟨_, ⟨i, hi, rfl⟩, hxi⟩ := hcov' hx
  exact Set.mem_biUnion (by simpa using hi) hxi
theorem hasCompactSupport_of_isCompactWrt {F : (Fin 4 → ℝ) → 𝕜}
    (hK : MetricNotions.IsCompactWrt InfiniteLattice.euclidDist
      (MetricNotions.closureWrt InfiniteLattice.euclidDist {x | F x ≠ 0})) :
    HasCompactSupport F := by
  refine (isCompact_of_isCompactWrt hK).of_isClosed_subset (isClosed_tsupport F) ?_
  intro x hx r hr
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (r / 2) (by positivity)
  refine ⟨y, hy, ?_⟩
  have h1 := euclidNormVec_le_two_mul_norm (x - y)
  rw [← dist_eq_norm] at h1
  have : InfiniteLattice.euclidDist x y = euclidNormVec (x - y) := rfl
  rw [this]
  linarith
theorem gradR4_bounded_and_uniformly_continuous {F : (Fin 4 → ℝ) → 𝕜}
    (hF : TestFunctions.IsC1R4 F)
    (hK : MetricNotions.IsCompactWrt InfiniteLattice.euclidDist
      (MetricNotions.closureWrt InfiniteLattice.euclidDist {x | F x ≠ 0})) :
    (∃ C : ℝ, ∀ x, ‖gradR4 F x‖ ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x', InfiniteLattice.euclidDist x x' ≤ δ →
        ‖gradR4 F x - gradR4 F x'‖ ≤ ε := by
  have hcont := continuous_gradR4 hF
  have hsupp : HasCompactSupport (gradR4 F) := by
    have h := ((hasCompactSupport_of_isCompactWrt hK).fderiv (𝕜 := ℝ)).comp_left
      (g := fun (A : (Fin 4 → ℝ) →L[ℝ] 𝕜) (μ : Fin 4) => A (Pi.single μ 1)) (by
        funext μ
        simp)
    rw [gradR4_eq_fderiv hF]
    exact h
  refine ⟨hcont.bounded_above_of_compact_support hsupp, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hu⟩ :=
    Metric.uniformContinuous_iff.1 (hsupp.uniformContinuous_of_continuous hcont) ε hε
  refine ⟨δ / 4, by positivity, fun x x' h => ?_⟩
  have hd : dist x x' < δ := by
    have h1 : dist x x' ≤ euclidNormVec (x - x') := dist_le_euclidNormVec x x'
    have h2 : InfiniteLattice.euclidDist x x' = euclidNormVec (x - x') := rfl
    rw [h2] at h
    linarith
  have := hu hd
  rw [dist_eq_norm] at this
  exact this.le
theorem grad_torus_bounded_and_uniformly_continuous (hProj : ProjectionFacts)
    (hLift : gradAtAnyLift) (D : MirrorData) {f : D.Torus → 𝕜} (hf : IsC1 D torus f) :
    (∃ C : ℝ, ∀ x, ‖grad D torus f x‖ ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x', metric D torus x x' ≤ δ →
        ‖grad D torus f x - grad D torus f x'‖ ≤ ε := by
  have hF : TestFunctions.IsC1R4 (f ∘ D.projection) := hf
  have hcont := continuous_gradR4 hF
  have hat : ∀ y, grad D torus f (D.projection y) =
      gradR4 (f ∘ D.projection) y := hLift D 𝕜 f hf
  obtain ⟨-, hlift, -⟩ := (hProj D).1
  obtain ⟨-, -, hnear, -⟩ := (hProj D).2.1
  have hQ : IsCompact (Set.Icc (fun _ : Fin 4 => (-1 : ℝ)) fun _ => D.side + 1) := isCompact_Icc
  have hmem : ∀ y : Fin 4 → ℝ, (∀ μ, y μ ∈ Set.Ico 0 D.side) →
      y ∈ Set.Icc (fun _ : Fin 4 => (-1 : ℝ)) fun _ => D.side + 1 := by
    intro y hy
    exact ⟨fun μ => by linarith [(hy μ).1], fun μ => by linarith [(hy μ).2]⟩
  constructor
  · obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨C, fun x => ?_⟩
    obtain ⟨y, rfl, hy⟩ := hlift x
    rw [hat]
    exact hC y (hmem y hy)
  · intro ε hε
    obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.1
      (hQ.uniformContinuousOn_of_continuous hcont.continuousOn) ε hε
    refine ⟨min (δ / 2) 1, by positivity, fun x x' h => ?_⟩
    obtain ⟨y, rfl, hy⟩ := hlift x
    obtain ⟨y', rfl, hy'⟩ := hnear y x'
    have hdist : dist y y' ≤ min (δ / 2) 1 :=
      (dist_le_euclidNormVec y y').trans (hy'.trans_le h)
    have hone : dist y y' ≤ 1 := hdist.trans (min_le_right _ _)
    have hlt : dist y y' < δ := by linarith [hdist.trans (min_le_left _ _)]
    have hcoord : ∀ μ, |y μ - y' μ| ≤ 1 := fun μ => by
      have := (dist_le_pi_dist y y' μ).trans hone
      rwa [Real.dist_eq] at this
    have hQ' : y' ∈ Set.Icc (fun _ : Fin 4 => (-1 : ℝ)) fun _ => D.side + 1 := by
      refine ⟨fun μ => ?_, fun μ => ?_⟩
      · linarith [(abs_le.1 (hcoord μ)).2, (hy μ).1]
      · linarith [(abs_le.1 (hcoord μ)).1, (hy μ).2]
    have := hu y (hmem y hy) y' hQ' hlt
    rw [dist_eq_norm] at this
    rw [hat, hat]
    exact this.le
theorem of_bounded_and_uniformly_continuous {D : MirrorData} {E : Ambient} (M : ScaleParam)
    (f : compactC1 D 𝕜 E)
    (hbound : ∃ C : ℝ, ∀ x, ‖grad D E f.1 x‖ ≤ C)
    (huniform : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x', metric D E x x' ≤ δ →
      ‖grad D E f.1 x - grad D E f.1 x'‖ ≤ ε) :
    gradSup f < ∞ ∧
    (∀ δ : ℝ≥0, gradOsc f δ ≤ 2 * gradSup f ∧ 2 * gradSup f < ∞) ∧
    Filter.Tendsto (gradOsc f) (nhds 0) (nhds 0) ∧
    Filter.Tendsto (smoothModulus M f) (nhds 0) (nhds 0) := by
  obtain ⟨C, hC⟩ := hbound
  have hsup : gradSup f ≤ ENNReal.ofReal (2 * C) :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal
      ((vecLength_le_two_mul_norm _).trans (by linarith [hC x]))
  have hfin : gradSup f < ∞ := hsup.trans_lt ENNReal.ofReal_lt_top
  have hat : ∀ x, ENNReal.ofReal (vecLength (grad D E f.1 x)) ≤ gradSup f :=
    fun x => le_iSup (fun x => ENNReal.ofReal (vecLength (grad D E f.1 x))) x
  have hosc : ∀ δ : ℝ≥0, gradOsc f δ ≤ 2 * gradSup f := by
    intro δ
    refine iSup_le fun x => iSup_le fun y => iSup_le fun _ => ?_
    calc ENNReal.ofReal (vecLength (grad D E f.1 x - grad D E f.1 y))
        ≤ ENNReal.ofReal (vecLength (grad D E f.1 x) + vecLength (grad D E f.1 y)) :=
          ENNReal.ofReal_le_ofReal (vecLength_sub_le _ _)
      _ = ENNReal.ofReal (vecLength (grad D E f.1 x)) +
            ENNReal.ofReal (vecLength (grad D E f.1 y)) :=
          ENNReal.ofReal_add (vecLength_nonneg _) (vecLength_nonneg _)
      _ ≤ gradSup f + gradSup f := add_le_add (hat x) (hat y)
      _ = 2 * gradSup f := (two_mul _).symm
  have htwo : 2 * gradSup f < ∞ := ENNReal.mul_lt_top (by simp) hfin
  have htend : Filter.Tendsto (gradOsc f) (nhds 0) (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ∞
    · subst htop
      exact Filter.Eventually.of_forall fun _ => le_top
    have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    obtain ⟨δ, hδ, hnear⟩ := huniform (ε.toReal / 2) (by positivity)
    have hnhds : Set.Iio (⟨δ, hδ.le⟩ : ℝ≥0) ∈ nhds (0 : ℝ≥0) := Iio_mem_nhds hδ
    filter_upwards [hnhds] with δ' hδ'
    refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
    have hle : (δ' : ℝ) ≤ δ := le_of_lt hδ'
    have := hnear x y (hxy.trans hle)
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal ((vecLength_le_two_mul_norm _).trans (by linarith))
  refine ⟨hfin, fun δ => ⟨hosc δ, htwo⟩, htend, ?_⟩
  have hfirst : Filter.Tendsto (fun δ : ℝ≥0 => (gradSup f).toReal * (δ : ℝ))
      (nhds 0) (nhds 0) := by
    have hc : Continuous fun δ : ℝ≥0 => (gradSup f).toReal * (δ : ℝ) :=
      continuous_const.mul NNReal.continuous_coe
    simpa using hc.tendsto 0
  have hsecond : Filter.Tendsto
      (fun δ : ℝ≥0 => 40 * (M : ℝ) * (gradOsc f δ).toReal) (nhds 0) (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
    simpa using h.const_mul (40 * (M : ℝ))
  have h := hfirst.max hsecond
  rw [max_self] at h
  exact h
end SmoothModulusVanishes
theorem SmoothModulusVanishes.holds (hProj : ProjectionFacts)
    (hLift : gradAtAnyLift) : SmoothModulusVanishes.Claim := by
  intro D 𝕜 _ E M f
  cases E with
  | torus =>
    obtain ⟨h1, h2⟩ :=
      SmoothModulusVanishes.grad_torus_bounded_and_uniformly_continuous hProj hLift D f.2.1
    exact SmoothModulusVanishes.of_bounded_and_uniformly_continuous M f h1 h2
  | euclidean =>
    obtain ⟨h1, h2⟩ := SmoothModulusVanishes.gradR4_bounded_and_uniformly_continuous f.2.1 f.2.2
    exact SmoothModulusVanishes.of_bounded_and_uniformly_continuous M f h1 h2
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
