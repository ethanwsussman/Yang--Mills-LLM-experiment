import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsFromSlopesProof
import YangMills.Construction.ColdStepAtMirrorFrames.RayOfSlopesIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
private theorem raySmooth_isOpen_openPolyball (r : ℝ) : IsOpen (openPolyball ι r) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.isOpen_openPolyball <;> assumption
omit [Fintype ι] [DecidableEq ι] in
private theorem raySmooth_smul_mem_openPolyball {r t : ℝ} {x : BondField ι} (hx : x ∈ openPolyball ι r)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • x ∈ openPolyball ι r := fun b => by
  have h1 : ‖(t • x) b‖ = |t| * ‖x b‖ := by simp [norm_smul]
  have h2 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have h3 := hx b
  rw [h1]
  nlinarith [norm_nonneg (x b), abs_nonneg t]
private def bondProjection (k : ι) : BondField ι →L[ℝ] BondField ι :=
  (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) k)
private def radialIntegrandDeriv (f : BondField ι → ℝ) (k : ι) (z : BondField ι) (t : ℝ) :
    BondField ι →L[ℝ] ℝ :=
  (fderiv ℝ f (t • z)).comp (bondProjection k) + t • (fderiv ℝ (fderiv ℝ f) (t • z)).flip (bondProjection k z)
variable {r : ℝ} {f : BondField ι → ℝ}
omit [DecidableEq ι] in
private theorem continuousOn_fderiv_and_fderiv_fderiv (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) :
    ContinuousOn (fderiv ℝ f) (openPolyball ι r) ∧ ContinuousOn (fderiv ℝ (fderiv ℝ f)) (openPolyball ι r) := by
  have ho := raySmooth_isOpen_openPolyball (ι := ι) r
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) (openPolyball ι r) :=
    hf.fderiv_of_isOpen ho (by norm_num)
  have h2 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ f)) (openPolyball ι r) :=
    h1.fderiv_of_isOpen ho (by norm_num)
  exact ⟨h1.continuousOn, h2.continuousOn⟩
omit [DecidableEq ι] in
private theorem hasFDerivAt_fderiv (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) {η : BondField ι}
    (hη : η ∈ openPolyball ι r) : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) η) η := by
  have ho := raySmooth_isOpen_openPolyball (ι := ι) r
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) (openPolyball ι r) :=
    hf.fderiv_of_isOpen ho (by norm_num)
  exact ((h1.contDiffAt (ho.mem_nhds hη)).differentiableAt (by norm_num)).hasFDerivAt
private theorem hasFDerivAt_radialIntegrand (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) {z : BondField ι} {t : ℝ}
    (hz : t • z ∈ openPolyball ι r) (k : ι) :
    HasFDerivAt (fun y => bondPartialDeriv f k (t • y) (y k)) (radialIntegrandDeriv f k z t) z := by
  have h1 : HasFDerivAt (fun y : BondField ι => t • y) (t • ContinuousLinearMap.id ℝ _) z :=
    (ContinuousLinearMap.id ℝ (BondField ι)).hasFDerivAt.const_smul t
  have h2 := (hasFDerivAt_fderiv hf hz).comp z h1
  have h3 : HasFDerivAt (fun y : BondField ι => bondProjection k y) (bondProjection k) z := (bondProjection k).hasFDerivAt
  have h4 := h2.clm_apply h3
  refine h4.congr_fderiv ?_
  ext y
  simp [radialIntegrandDeriv, ContinuousLinearMap.flip_apply]
private theorem continuousOn_radialIntegrandDeriv (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) {x : BondField ι}
    (hx : x ∈ openPolyball ι r) (k : ι) : ContinuousOn (radialIntegrandDeriv f k x) (Set.Icc 0 1) := by
  obtain ⟨c1, c2⟩ := continuousOn_fderiv_and_fderiv_fderiv hf
  have hm : Set.MapsTo (fun t : ℝ => t • x) (Set.Icc 0 1) (openPolyball ι r) := fun t ht => raySmooth_smul_mem_openPolyball hx ht
  have hc : ContinuousOn (fun t : ℝ => t • x) (Set.Icc 0 1) :=
    (continuous_id.smul continuous_const).continuousOn
  have a1 := c1.comp hc hm
  have a2 := c2.comp hc hm
  unfold radialIntegrandDeriv
  refine ContinuousOn.add ?_ ?_
  · exact a1.clm_comp continuousOn_const
  · refine continuousOn_id.smul ?_
    have : ContinuousOn (fun t : ℝ => (ContinuousLinearMap.flipₗᵢ ℝ (BondField ι) (BondField ι) ℝ)
        (fderiv ℝ (fderiv ℝ f) (t • x))) (Set.Icc 0 1) :=
      (ContinuousLinearMap.flipₗᵢ ℝ (BondField ι) (BondField ι) ℝ).continuous.comp_continuousOn a2
    exact this.clm_apply continuousOn_const
private theorem continuousOn_radialIntegrand (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) {x : BondField ι}
    (hx : x ∈ openPolyball ι r) (k : ι) :
    ContinuousOn (fun t : ℝ => bondPartialDeriv f k (t • x) (x k)) (Set.Icc 0 1) := by
  obtain ⟨c1, _⟩ := continuousOn_fderiv_and_fderiv_fderiv hf
  have hm : Set.MapsTo (fun t : ℝ => t • x) (Set.Icc 0 1) (openPolyball ι r) := fun t ht => raySmooth_smul_mem_openPolyball hx ht
  have hc : ContinuousOn (fun t : ℝ => t • x) (Set.Icc 0 1) :=
    (continuous_id.smul continuous_const).continuousOn
  exact (c1.comp hc hm).clm_apply continuousOn_const
abbrev _root_.YangMills.SharedProofs.p41991 := @continuousOn_radialIntegrand
private theorem uIoc_zero_one_subset_Icc : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
  rw [Set.uIoc_of_le zero_le_one]
  exact Set.Ioc_subset_Icc_self
private theorem norm_radialIntegrandDeriv_le (z : BondField ι) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ι) :
    ‖radialIntegrandDeriv f k z t‖ ≤ ‖fderiv ℝ f (t • z)‖ * ‖bondProjection k‖ +
      ‖fderiv ℝ (fderiv ℝ f) (t • z)‖ * (‖bondProjection k‖ * ‖z‖) := by
  unfold radialIntegrandDeriv
  refine (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) ?_)
  have ht1 : ‖t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  rw [norm_smul]
  have e1 : ‖(fderiv ℝ (fderiv ℝ f) (t • z)).flip (bondProjection k z)‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (t • z)‖ * (‖bondProjection k‖ * ‖z‖) := by
    refine ((fderiv ℝ (fderiv ℝ f) (t • z)).flip.le_opNorm _).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_mul_of_nonneg_left ((bondProjection k).le_opNorm z) (ContinuousLinearMap.opNorm_nonneg _)
  calc ‖t‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact e1
omit [DecidableEq ι] in
private theorem exists_bound_along_segments {G : Type} [NormedAddCommGroup G] {g : BondField ι → G} {s : Set (BondField ι)}
    (hg : ContinuousOn g (openPolyball ι r)) (hs : IsCompact s) (hsub : s ⊆ openPolyball ι r) :
    ∃ M, ∀ z ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g (t • z)‖ ≤ M := by
  have hK : IsCompact (s ×ˢ Set.Icc (0 : ℝ) 1) := hs.prod isCompact_Icc
  have hmaps : Set.MapsTo (fun p : BondField ι × ℝ => p.2 • p.1) (s ×ˢ Set.Icc (0 : ℝ) 1)
      (openPolyball ι r) := fun p hp => raySmooth_smul_mem_openPolyball (hsub hp.1) hp.2
  have hcs : ContinuousOn (fun p : BondField ι × ℝ => p.2 • p.1) (s ×ˢ Set.Icc (0 : ℝ) 1) :=
    (continuous_snd.smul continuous_fst).continuousOn
  have q : ContinuousOn (fun p : BondField ι × ℝ => g (p.2 • p.1)) (s ×ˢ Set.Icc (0 : ℝ) 1) :=
    hg.comp hcs hmaps
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn q
  exact ⟨M, fun z hz t ht => hM (z, t) ⟨hz, ht⟩⟩
private theorem exists_bound_radialIntegrandDeriv (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) {x : BondField ι} {ε : ℝ}
    (hsub : Metric.closedBall x ε ⊆ openPolyball ι r) (k : ι) :
    ∃ M, ∀ z ∈ Metric.closedBall x ε, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖radialIntegrandDeriv f k z t‖ ≤ M := by
  obtain ⟨c1, c2⟩ := continuousOn_fderiv_and_fderiv_fderiv hf
  have hcomp : IsCompact (Metric.closedBall x ε) := isCompact_closedBall x ε
  obtain ⟨M₁, h₁⟩ := exists_bound_along_segments c1 hcomp hsub
  obtain ⟨M₂, h₂⟩ := exists_bound_along_segments (G := BondField ι →L[ℝ] BondField ι →L[ℝ] ℝ) c2 hcomp hsub
  obtain ⟨M₃, h₃⟩ := hcomp.exists_bound_of_continuousOn (f := fun z : BondField ι => z)
    continuousOn_id
  refine ⟨M₁ * ‖bondProjection k‖ + M₂ * (‖bondProjection k‖ * M₃), fun z hz t ht => ?_⟩
  refine (norm_radialIntegrandDeriv_le z ht k).trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right (h₁ z hz t ht) (norm_nonneg _)
  · have a := h₂ z hz t ht
    have b : ‖bondProjection k‖ * ‖z‖ ≤ ‖bondProjection k‖ * M₃ := mul_le_mul_of_nonneg_left (h₃ z hz) (norm_nonneg _)
    exact mul_le_mul a b (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))
      ((ContinuousLinearMap.opNorm_nonneg _).trans a)
private theorem hasFDerivAt_radialTerm (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) {x : BondField ι}
    (hx : x ∈ openPolyball ι r) (k : ι) :
    HasFDerivAt (fun z => ∫ t in (0 : ℝ)..1, bondPartialDeriv f k (t • z) (z k))
      (∫ t in (0 : ℝ)..1, radialIntegrandDeriv f k x t) x := by
  have ho := raySmooth_isOpen_openPolyball (ι := ι) r
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (ho.mem_nhds hx)
  obtain ⟨M, hbound⟩ := exists_bound_radialIntegrandDeriv hf hsub k
  have hmeas : ∀ z ∈ openPolyball ι r, AEStronglyMeasurable
      (fun t : ℝ => bondPartialDeriv f k (t • z) (z k)) (volume.restrict (Set.uIoc 0 1)) := fun z hz =>
    ((continuousOn_radialIntegrand hf hz k).mono uIoc_zero_one_subset_Icc).aestronglyMeasurable measurableSet_uIoc
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z t => bondPartialDeriv f k (t • z) (z k)) (F' := fun z t => radialIntegrandDeriv f k z t)
    (bound := fun _ => M) (Metric.closedBall_mem_nhds x hε) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [ho.mem_nhds hx] with z hz using hmeas z hz
  · have := (continuousOn_radialIntegrand hf hx k)
    rw [← Set.uIcc_of_le zero_le_one] at this
    exact this.intervalIntegrable
  · exact ((continuousOn_radialIntegrandDeriv hf hx k).mono uIoc_zero_one_subset_Icc).aestronglyMeasurable measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun t ht z hz => hbound z hz t (uIoc_zero_one_subset_Icc ht)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht z hz =>
      hasFDerivAt_radialIntegrand hf (raySmooth_smul_mem_openPolyball (hsub hz) (uIoc_zero_one_subset_Icc ht)) k
private theorem continuousAt_radialIntegrandDeriv (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) {x : BondField ι}
    (hx : x ∈ openPolyball ι r) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ι) :
    ContinuousAt (fun z => radialIntegrandDeriv f k z t) x := by
  obtain ⟨c1, c2⟩ := continuousOn_fderiv_and_fderiv_fderiv hf
  have ho := raySmooth_isOpen_openPolyball (ι := ι) r
  have hm := raySmooth_smul_mem_openPolyball hx ht
  have hsc : ContinuousAt (fun z : BondField ι => t • z) x :=
    (continuous_const_smul t).continuousAt
  have a1 : ContinuousAt (fun z : BondField ι => fderiv ℝ f (t • z)) x :=
    ContinuousAt.comp (f := fun z : BondField ι => t • z)
      (c1.continuousAt (ho.mem_nhds hm)) hsc
  have a2 : ContinuousAt (fun z : BondField ι => fderiv ℝ (fderiv ℝ f) (t • z)) x :=
    ContinuousAt.comp (f := fun z : BondField ι => t • z)
      (c2.continuousAt (ho.mem_nhds hm)) hsc
  unfold radialIntegrandDeriv
  refine ContinuousAt.add (a1.clm_comp continuousAt_const) (ContinuousAt.const_smul ?_ t)
  have a3 : ContinuousAt (fun z : BondField ι =>
      (ContinuousLinearMap.flipₗᵢ ℝ (BondField ι) (BondField ι) ℝ)
        (fderiv ℝ (fderiv ℝ f) (t • z))) x :=
    (ContinuousLinearMap.flipₗᵢ ℝ (BondField ι) (BondField ι) ℝ).continuous.continuousAt.comp a2
  exact a3.clm_apply (bondProjection k).continuous.continuousAt
private theorem continuousAt_integral_radialIntegrandDeriv (hf : ContDiffOn ℝ 2 f (openPolyball ι r)) {x : BondField ι}
    (hx : x ∈ openPolyball ι r) (k : ι) :
    ContinuousAt (fun z => ∫ t in (0 : ℝ)..1, radialIntegrandDeriv f k z t) x := by
  have ho := raySmooth_isOpen_openPolyball (ι := ι) r
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (ho.mem_nhds hx)
  obtain ⟨M, hbound⟩ := exists_bound_radialIntegrandDeriv hf hsub k
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [ho.mem_nhds hx] with z hz
    exact ((continuousOn_radialIntegrandDeriv hf hz k).mono uIoc_zero_one_subset_Icc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [Metric.closedBall_mem_nhds x hε] with z hz
    exact Filter.Eventually.of_forall fun t ht => hbound z hz t (uIoc_zero_one_subset_Icc ht)
  · exact Filter.Eventually.of_forall fun t ht => continuousAt_radialIntegrandDeriv hf hx (uIoc_zero_one_subset_Icc ht) k
theorem radialSlopeIntegral_contDiffOn : RadialSlopeIntegralContDiffOn := by
  intro ι _ _ B r f hf
  have ho := raySmooth_isOpen_openPolyball (ι := ι) r
  have hsum : ∀ x ∈ openPolyball ι r, HasFDerivAt (radialSlopeIntegral B f)
      (∑ k ∈ B, ∫ t in (0 : ℝ)..1, radialIntegrandDeriv f k x t) x := fun x hx => by
    unfold radialSlopeIntegral
    exact HasFDerivAt.fun_sum fun k _ => hasFDerivAt_radialTerm hf hx k
  have hcont : ContinuousOn (fderiv ℝ (radialSlopeIntegral B f)) (openPolyball ι r) := fun x hx => by
    have hev : fderiv ℝ (radialSlopeIntegral B f) =ᶠ[nhds x]
        fun z => ∑ k ∈ B, ∫ t in (0 : ℝ)..1, radialIntegrandDeriv f k z t := by
      filter_upwards [ho.mem_nhds hx] with z hz using (hsum z hz).fderiv
    have hc : ContinuousAt (fun z => ∑ k ∈ B, ∫ t in (0 : ℝ)..1, radialIntegrandDeriv f k z t) x :=
      tendsto_finsetSum _ fun k _ => continuousAt_integral_radialIntegrandDeriv hf hx k
    exact (hc.congr hev.symm).continuousWithinAt
  have h01 : ContDiffOn ℝ (0 + 1) (radialSlopeIntegral B f) (openPolyball ι r) :=
    (contDiffOn_succ_iff_fderiv_of_isOpen ho).2
      ⟨fun x hx => (hsum x hx).differentiableAt.differentiableWithinAt, fun h => absurd h (by simp),
        contDiffOn_zero.2 hcont⟩
  simpa using h01
end YangMills.Construction.ColdStepAtMirrorFrames
end
