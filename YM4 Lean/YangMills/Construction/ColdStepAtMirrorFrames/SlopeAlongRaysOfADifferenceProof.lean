import YangMills.Construction.ColdStepAtMirrorFrames.EnergiesCompareOnPairedVariablesProof
import YangMills.Construction.ColdStepAtMirrorFrames.RayOfSlopesIsSmoothProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames.RadialSlope
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem isOpen_openPolyball (ρ : ℝ) : IsOpen (openPolyball ι ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.PairedEnergies.isOpen_openPolyball <;> assumption
theorem smul_mem_openPolyball {ρ t : ℝ} {x : BondField ι} (hx : x ∈ openPolyball ι ρ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • x ∈ openPolyball ι ρ := fun b => by
  have h1 : ‖(t • x) b‖ = |t| * ‖x b‖ := by simp [norm_smul]
  have h2 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have h3 := hx b
  rw [h1]
  nlinarith [norm_nonneg (x b), abs_nonneg t]
theorem secondDerivAlong_eq_sum (D : BondField ι → ℝ) (η u z : BondField ι)
    (hd : DifferentiableAt ℝ (fun ζ => fderiv ℝ D ζ u) η) :
    secondDerivAlong D η u z = ∑ l, secondDerivAlong D η u (bondVariation l (z l)) := by
  unfold secondDerivAlong bondVariation
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
variable {B : Finset ι} {ρ B₀ A : ℝ} {D : BondField ι → ℝ}
theorem differentiableAt_fderiv_apply (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) {η : BondField ι}
    (hη : η ∈ openPolyball ι ρ) (u : BondField ι) :
    DifferentiableAt ℝ (fun ζ => fderiv ℝ D ζ u) η := by
  have ho := isOpen_openPolyball (ι := ι) ρ
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ D) (openPolyball ι ρ) :=
    hD.fderiv_of_isOpen ho (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ D) η :=
    (h1.contDiffAt (ho.mem_nhds hη)).differentiableAt (by norm_num)
  exact h2.clm_apply (differentiableAt_const u)
theorem abs_bondPartialDeriv_smul_le (hρ : 0 < ρ) (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ))
    (h0 : ∀ k ∈ B, ∀ e, |bondPartialDeriv D k 0 e| ≤ B₀ * ‖e‖)
    (h2 : ∀ x ∈ openPolyball ι ρ, ∀ k ∈ B, ∀ l e e',
      |secondDerivAlong D x (bondVariation k e) (bondVariation l e')| ≤ A * ‖e‖ * ‖e'‖)
    {x : BondField ι} (hx : x ∈ openPolyball ι ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {k : ι}
    (hk : k ∈ B) (e : BondVector) :
    |bondPartialDeriv D k (t • x) e| ≤ (B₀ + A * ∑ l, ‖x l‖) * ‖e‖ := by
  have hA : 0 ≤ A := by
    by_contra hA
    rw [not_le] at hA
    have h := h2 0 (fun b => by simpa using hρ) k hk k
      (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
    have := abs_nonneg (secondDerivAlong D 0 (bondVariation k (EuclideanSpace.single 0 (1 : ℝ)))
      (bondVariation k (EuclideanSpace.single 0 1)))
    simp at h
    linarith
  set z : BondField ι := t • x with hz
  have hzU := smul_mem_openPolyball hx ht
  set φ : ℝ → ℝ := fun s => fderiv ℝ D (s • z) (bondVariation k e) with hφ
  have hφd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt φ (secondDerivAlong D (s • z) (bondVariation k e) z) (Set.Icc 0 1) s :=
    fun s hs => by
    have hm := smul_mem_openPolyball hzU hs
    have h1 := (differentiableAt_fderiv_apply hD hm (bondVariation k e)).hasFDerivAt
    have h3 : HasDerivAt (fun s : ℝ => s • z) z s := by
      simpa using (hasDerivAt_id s).smul_const z
    exact (h1.comp_hasDerivAt s h3).hasDerivWithinAt
  have hb : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖secondDerivAlong D (s • z) (bondVariation k e) z‖ ≤ A * ‖e‖ * ∑ l, ‖x l‖ :=
    fun s hs => by
    have hm := smul_mem_openPolyball hzU hs
    rw [secondDerivAlong_eq_sum D _ _ _ (differentiableAt_fderiv_apply hD hm _), Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => (h2 _ hm k hk l e (z l)).trans ?_
    have : ‖z l‖ ≤ ‖x l‖ := by
      have h1 : ‖z l‖ = |t| * ‖x l‖ := by simp [hz, norm_smul]
      have h2 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
      rw [h1]
      nlinarith [norm_nonneg (x l), abs_nonneg t]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hA (norm_nonneg _))
  have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hφd hb
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simp only [hφ, sub_zero, one_smul, zero_smul, norm_one, mul_one, Real.norm_eq_abs] at hmv
  have h00 := h0 k hk e
  unfold bondPartialDeriv at h00 ⊢
  have := abs_sub_abs_le_abs_sub (fderiv ℝ D z (bondVariation k e)) (fderiv ℝ D 0 (bondVariation k e))
  nlinarith
def bondProjection (k : ι) : BondField ι →L[ℝ] BondField ι :=
  (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) k)
theorem bondProjection_apply (k : ι) (z : BondField ι) :
    bondProjection k z = bondVariation k (z k) := rfl
theorem bondProjection_bondVariation (k l : ι) (e : BondVector) :
    bondProjection k (bondVariation l e) = if l = k then bondVariation k e else 0 := by
  rw [bondProjection_apply]
  by_cases h : l = k
  · subst h
    simp [bondVariation]
  · simp [bondVariation, h, Pi.single_eq_of_ne (Ne.symm h)]
def radialIntegrandDeriv (D : BondField ι → ℝ) (k : ι) (z : BondField ι) (t : ℝ) :
    BondField ι →L[ℝ] ℝ :=
  (fderiv ℝ D (t • z)).comp (bondProjection k) +
    t • (fderiv ℝ (fderiv ℝ D) (t • z)).flip (bondProjection k z)
theorem hasFDerivAt_fderiv (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) {η : BondField ι}
    (hη : η ∈ openPolyball ι ρ) : HasFDerivAt (fderiv ℝ D) (fderiv ℝ (fderiv ℝ D) η) η := by
  have ho := isOpen_openPolyball (ι := ι) ρ
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ D) (openPolyball ι ρ) :=
    hD.fderiv_of_isOpen ho (by norm_num)
  exact ((h1.contDiffAt (ho.mem_nhds hη)).differentiableAt (by norm_num)).hasFDerivAt
theorem fderiv_fderiv_apply_eq (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) {η : BondField ι}
    (hη : η ∈ openPolyball ι ρ) (u y : BondField ι) :
    fderiv ℝ (fderiv ℝ D) η y u = secondDerivAlong D η u y := by
  have h := ((hasFDerivAt_fderiv hD hη).clm_apply (hasFDerivAt_const u η)).fderiv
  unfold secondDerivAlong
  rw [h]
  simp
theorem hasFDerivAt_radialIntegrand (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) {z : BondField ι}
    {t : ℝ} (hz : t • z ∈ openPolyball ι ρ) (k : ι) :
    HasFDerivAt (fun y => bondPartialDeriv D k (t • y) (y k)) (radialIntegrandDeriv D k z t) z := by
  have h1 : HasFDerivAt (fun y : BondField ι => t • y) (t • ContinuousLinearMap.id ℝ _) z :=
    (ContinuousLinearMap.id ℝ (BondField ι)).hasFDerivAt.const_smul t
  have h2 := (hasFDerivAt_fderiv hD hz).comp z h1
  have h3 : HasFDerivAt (fun y : BondField ι => bondProjection k y) (bondProjection k) z :=
    (bondProjection k).hasFDerivAt
  have h4 := h2.clm_apply h3
  refine h4.congr_fderiv ?_
  ext y
  simp [radialIntegrandDeriv, ContinuousLinearMap.flip_apply]
theorem continuousOn_fderiv_and_fderiv_fderiv (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) :
    ContinuousOn (fderiv ℝ D) (openPolyball ι ρ) ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ D)) (openPolyball ι ρ) := by
  have ho := isOpen_openPolyball (ι := ι) ρ
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ D) (openPolyball ι ρ) :=
    hD.fderiv_of_isOpen ho (by norm_num)
  have h2 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ D)) (openPolyball ι ρ) :=
    h1.fderiv_of_isOpen ho (by norm_num)
  exact ⟨h1.continuousOn, h2.continuousOn⟩
theorem continuousOn_radialIntegrandDeriv (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) {x : BondField ι}
    (hx : x ∈ openPolyball ι ρ) (k : ι) :
    ContinuousOn (radialIntegrandDeriv D k x) (Set.Icc 0 1) := by
  obtain ⟨c1, c2⟩ := continuousOn_fderiv_and_fderiv_fderiv hD
  have hm : Set.MapsTo (fun t : ℝ => t • x) (Set.Icc 0 1) (openPolyball ι ρ) :=
    fun t ht => smul_mem_openPolyball hx ht
  have hc : ContinuousOn (fun t : ℝ => t • x) (Set.Icc 0 1) :=
    (continuous_id.smul continuous_const).continuousOn
  have a1 := c1.comp hc hm
  have a2 := c2.comp hc hm
  unfold radialIntegrandDeriv
  refine ContinuousOn.add ?_ ?_
  · exact a1.clm_comp continuousOn_const
  · refine continuousOn_id.smul ?_
    have : ContinuousOn (fun t : ℝ => (ContinuousLinearMap.flipₗᵢ ℝ (BondField ι) (BondField ι) ℝ)
        (fderiv ℝ (fderiv ℝ D) (t • x))) (Set.Icc 0 1) :=
      (ContinuousLinearMap.flipₗᵢ ℝ (BondField ι) (BondField ι) ℝ).continuous.comp_continuousOn a2
    exact this.clm_apply continuousOn_const
theorem continuousOn_radialIntegrand (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) {x : BondField ι}
    (hx : x ∈ openPolyball ι ρ) (k : ι) :
    ContinuousOn (fun t : ℝ => bondPartialDeriv D k (t • x) (x k)) (Set.Icc 0 1) := by apply _root_.YangMills.SharedProofs.p41991 <;> assumption
theorem uIoc_zero_one_subset_Icc : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
  rw [Set.uIoc_of_le zero_le_one]
  exact Set.Ioc_subset_Icc_self
theorem norm_radialIntegrandDeriv_le (z : BondField ι) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ι) :
    ‖radialIntegrandDeriv D k z t‖ ≤ ‖fderiv ℝ D (t • z)‖ * ‖bondProjection k‖ +
      ‖fderiv ℝ (fderiv ℝ D) (t • z)‖ * (‖bondProjection k‖ * ‖z‖) := by
  unfold radialIntegrandDeriv
  refine (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) ?_)
  have ht1 : ‖t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  rw [norm_smul]
  have e1 : ‖(fderiv ℝ (fderiv ℝ D) (t • z)).flip (bondProjection k z)‖ ≤
      ‖fderiv ℝ (fderiv ℝ D) (t • z)‖ * (‖bondProjection k‖ * ‖z‖) := by
    refine ((fderiv ℝ (fderiv ℝ D) (t • z)).flip.le_opNorm _).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_mul_of_nonneg_left ((bondProjection k).le_opNorm z)
      (ContinuousLinearMap.opNorm_nonneg _)
  calc ‖t‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact e1
theorem exists_bound_smul_of_continuousOn {G : Type} [NormedAddCommGroup G] {g : BondField ι → G}
    {s : Set (BondField ι)} (hg : ContinuousOn g (openPolyball ι ρ)) (hs : IsCompact s)
    (hsub : s ⊆ openPolyball ι ρ) :
    ∃ M, ∀ z ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g (t • z)‖ ≤ M := by
  have hK : IsCompact (s ×ˢ Set.Icc (0 : ℝ) 1) := hs.prod isCompact_Icc
  have hmaps : Set.MapsTo (fun p : BondField ι × ℝ => p.2 • p.1) (s ×ˢ Set.Icc (0 : ℝ) 1)
      (openPolyball ι ρ) := fun p hp => smul_mem_openPolyball (hsub hp.1) hp.2
  have hcs : ContinuousOn (fun p : BondField ι × ℝ => p.2 • p.1) (s ×ˢ Set.Icc (0 : ℝ) 1) :=
    (continuous_snd.smul continuous_fst).continuousOn
  have q : ContinuousOn (fun p : BondField ι × ℝ => g (p.2 • p.1)) (s ×ˢ Set.Icc (0 : ℝ) 1) :=
    hg.comp hcs hmaps
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn q
  exact ⟨M, fun z hz t ht => hM (z, t) ⟨hz, ht⟩⟩
theorem exists_bound_radialIntegrandDeriv (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) {x : BondField ι}
    {ε : ℝ} (hsub : Metric.closedBall x ε ⊆ openPolyball ι ρ) (k : ι) :
    ∃ M, ∀ z ∈ Metric.closedBall x ε, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖radialIntegrandDeriv D k z t‖ ≤ M := by
  obtain ⟨c1, c2⟩ := continuousOn_fderiv_and_fderiv_fderiv hD
  have hcomp : IsCompact (Metric.closedBall x ε) := isCompact_closedBall x ε
  obtain ⟨M₁, h₁⟩ := exists_bound_smul_of_continuousOn c1 hcomp hsub
  obtain ⟨M₂, h₂⟩ := exists_bound_smul_of_continuousOn
    (G := BondField ι →L[ℝ] BondField ι →L[ℝ] ℝ) c2 hcomp hsub
  obtain ⟨M₃, h₃⟩ := hcomp.exists_bound_of_continuousOn (f := fun z : BondField ι => z)
    continuousOn_id
  refine ⟨M₁ * ‖bondProjection k‖ + M₂ * (‖bondProjection k‖ * M₃), fun z hz t ht => ?_⟩
  refine (norm_radialIntegrandDeriv_le z ht k).trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right (h₁ z hz t ht) (norm_nonneg _)
  · have a := h₂ z hz t ht
    have b : ‖bondProjection k‖ * ‖z‖ ≤ ‖bondProjection k‖ * M₃ :=
      mul_le_mul_of_nonneg_left (h₃ z hz) (norm_nonneg _)
    exact mul_le_mul a b (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))
      ((ContinuousLinearMap.opNorm_nonneg _).trans a)
theorem hasFDerivAt_radialIntegral (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ)) {x : BondField ι}
    (hx : x ∈ openPolyball ι ρ) (k : ι) :
    HasFDerivAt (fun z => ∫ t in (0 : ℝ)..1, bondPartialDeriv D k (t • z) (z k))
      (∫ t in (0 : ℝ)..1, radialIntegrandDeriv D k x t) x := by
  have ho := isOpen_openPolyball (ι := ι) ρ
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (ho.mem_nhds hx)
  obtain ⟨M, hbound⟩ := exists_bound_radialIntegrandDeriv hD hsub k
  have hmeas : ∀ z ∈ openPolyball ι ρ, AEStronglyMeasurable
      (fun t : ℝ => bondPartialDeriv D k (t • z) (z k)) (volume.restrict (Set.uIoc 0 1)) :=
    fun z hz =>
    ((continuousOn_radialIntegrand hD hz k).mono uIoc_zero_one_subset_Icc).aestronglyMeasurable
      measurableSet_uIoc
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z t => bondPartialDeriv D k (t • z) (z k)) (F' := fun z t => radialIntegrandDeriv D k z t)
    (bound := fun _ => M) (Metric.closedBall_mem_nhds x hε) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [ho.mem_nhds hx] with z hz using hmeas z hz
  · have := (continuousOn_radialIntegrand hD hx k)
    rw [← Set.uIcc_of_le zero_le_one] at this
    exact this.intervalIntegrable
  · exact ((continuousOn_radialIntegrandDeriv hD hx k).mono uIoc_zero_one_subset_Icc).aestronglyMeasurable
      measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun t ht z hz => hbound z hz t (uIoc_zero_one_subset_Icc ht)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht z hz =>
      hasFDerivAt_radialIntegrand hD (smul_mem_openPolyball (hsub hz) (uIoc_zero_one_subset_Icc ht)) k
theorem abs_radialIntegrandDeriv_bondVariation_le (hρ : 0 < ρ) (hD : ContDiffOn ℝ 2 D (openPolyball ι ρ))
    (h0 : ∀ k ∈ B, ∀ e, |bondPartialDeriv D k 0 e| ≤ B₀ * ‖e‖)
    (h2 : ∀ x ∈ openPolyball ι ρ, ∀ k ∈ B, ∀ l e e',
      |secondDerivAlong D x (bondVariation k e) (bondVariation l e')| ≤ A * ‖e‖ * ‖e'‖)
    {x : BondField ι} (hx : x ∈ openPolyball ι ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {k : ι}
    (hk : k ∈ B) (l : ι) (e : BondVector) :
    |radialIntegrandDeriv D k x t (bondVariation l e)| ≤
      (if l = k then (B₀ + A * ∑ l', ‖x l'‖) * ‖e‖ else 0) + A * ‖x k‖ * ‖e‖ := by
  have hm := smul_mem_openPolyball hx ht
  have e1 : radialIntegrandDeriv D k x t (bondVariation l e) =
      fderiv ℝ D (t • x) (bondProjection k (bondVariation l e)) +
        t * secondDerivAlong D (t • x) (bondVariation k (x k)) (bondVariation l e) := by
    unfold radialIntegrandDeriv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [fderiv_fderiv_apply_eq hD hm]
    simp only [bondProjection_apply]
  rw [e1]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [bondProjection_bondVariation]
    by_cases hl : l = k
    · subst hl
      have := abs_bondPartialDeriv_smul_le hρ hD h0 h2 hx ht hk e
      simpa [bondPartialDeriv] using this
    · simp [hl]
  · rw [abs_mul]
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have := h2 _ hm k hk l (x k) e
    calc |t| * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact this
theorem radialSlopeIntegralBound_holds : RadialSlopeIntegralBound := by
  intro ι _ _ B ρ B₀ A D hρ hD h0 h2 x hx
  have hnorm : ∀ (f : ℝ → ℝ) (C : ℝ), (∀ t ∈ Set.Icc (0 : ℝ) 1, |f t| ≤ C) →
      |∫ t in (0 : ℝ)..1, f t| ≤ C := fun f C hf => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (f := f)
      (C := C) fun s hs => by
        rw [Real.norm_eq_abs]
        exact hf s (uIoc_zero_one_subset_Icc hs)
    simpa using this
  have hd : ∀ k, HasFDerivAt (fun z => ∫ t in (0 : ℝ)..1, bondPartialDeriv D k (t • z) (z k))
      (∫ t in (0 : ℝ)..1, radialIntegrandDeriv D k x t) x := fun k => hasFDerivAt_radialIntegral hD hx k
  have hsum : HasFDerivAt (radialSlopeIntegral B D)
      (∑ k ∈ B, ∫ t in (0 : ℝ)..1, radialIntegrandDeriv D k x t) x := by
    unfold radialSlopeIntegral
    exact HasFDerivAt.fun_sum fun k _ => hd k
  refine ⟨hsum.differentiableAt, ?_, fun l => ?_⟩
  · unfold radialSlopeIntegral
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    refine hnorm _ _ fun t ht => ?_
    have := abs_bondPartialDeriv_smul_le hρ hD h0 h2 hx ht hk (x k)
    rw [mul_comm]
    exact this
  · rcases B.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
    · have : radialSlopeIntegral (∅ : Finset ι) D = fun _ => 0 := by
        funext z
        simp [radialSlopeIntegral]
      rw [this]
      simp [bondGradNorm]
    have hA : 0 ≤ A := by
      by_contra hA
      rw [not_le] at hA
      have h := h2 0 (fun b => by simpa using hρ) k₀ hk₀ k₀
        (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
      have := abs_nonneg (secondDerivAlong D 0 (bondVariation k₀ (EuclideanSpace.single 0 (1 : ℝ)))
        (bondVariation k₀ (EuclideanSpace.single 0 1)))
      simp at h
      linarith
    have hB : 0 ≤ B₀ := by
      have h := h0 k₀ hk₀ (EuclideanSpace.single 0 1)
      have := abs_nonneg (bondPartialDeriv D k₀ 0 (EuclideanSpace.single 0 (1 : ℝ)))
      simp at h
      linarith
    have hS : 0 ≤ ∑ l', ‖x l'‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hT : 0 ≤ ∑ k ∈ B, ‖x k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    unfold bondGradNorm
    rw [hsum.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ ?_ fun e => ?_
    · split_ifs <;> positivity
    have hv : ∀ k ∈ B, |(∫ t in (0 : ℝ)..1, radialIntegrandDeriv D k x t) (bondVariation l e)| ≤
        (if l = k then (B₀ + A * ∑ l', ‖x l'‖) * ‖e‖ else 0) + A * ‖x k‖ * ‖e‖ := fun k hk => by
      have hint : IntervalIntegrable (radialIntegrandDeriv D k x) volume 0 1 := by
        have := continuousOn_radialIntegrandDeriv hD hx k
        rw [← Set.uIcc_of_le zero_le_one] at this
        exact this.intervalIntegrable
      rw [ContinuousLinearMap.intervalIntegral_apply hint]
      exact hnorm _ _ fun t ht => abs_radialIntegrandDeriv_bondVariation_le hρ hD h0 h2 hx ht hk l e
    show ‖(∑ k ∈ B, ∫ t in (0 : ℝ)..1, radialIntegrandDeriv D k x t) (bondVariation l e)‖ ≤ _
    rw [ContinuousLinearMap.sum_apply, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hv).trans ?_)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    have : ∑ k ∈ B, A * ‖x k‖ * ‖e‖ = A * (∑ k ∈ B, ‖x k‖) * ‖e‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [this]
    by_cases hl : l ∈ B
    · simp [hl]
      nlinarith
    · simp [hl]
end YangMills.Construction.ColdStepAtMirrorFrames.RadialSlope
end
