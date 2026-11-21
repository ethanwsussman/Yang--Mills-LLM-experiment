import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
namespace HomNorm
section Weighted
variable {J J' : Type} [Fintype J]
theorem normSummable_of_fintype (w : J → ℝ) (f : J → ℂ) : NormSummable w f :=
  (hasSum_fintype _).summable
theorem wNorm_eq_sqrt_sum (w : J → ℝ) (f : J → ℂ) :
    wNorm w f = Real.sqrt (∑ i, w i * ‖f i‖ ^ 2) := by
  simp [wNorm, tsum_fintype]
def sqrtWeighted (w : J → ℝ) (f : J → ℂ) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 fun i => ((Real.sqrt (w i) : ℝ) : ℂ) * f i
theorem wNorm_eq_norm_sqrtWeighted {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) (f : J → ℂ) :
    wNorm w f = ‖sqrtWeighted w f‖ := by
  rw [wNorm_eq_sqrt_sum, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [sqrtWeighted, mul_pow, Real.sq_sqrt (hw i)]
theorem wNorm_add_le {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) (f g : J → ℂ) :
    wNorm w (f + g) ≤ wNorm w f + wNorm w g := by
  have e : sqrtWeighted w (f + g) = sqrtWeighted w f + sqrtWeighted w g := by
    ext i
    simp [sqrtWeighted, mul_add]
  rw [wNorm_eq_norm_sqrtWeighted hw, wNorm_eq_norm_sqrtWeighted hw,
    wNorm_eq_norm_sqrtWeighted hw, e]
  exact norm_add_le _ _
theorem wNorm_smul {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℂ) (f : J → ℂ) :
    wNorm w (a • f) = ‖a‖ * wNorm w f := by
  have e : sqrtWeighted w (a • f) = a • sqrtWeighted w f := by
    ext i
    simp [sqrtWeighted, mul_left_comm]
  rw [wNorm_eq_norm_sqrtWeighted hw, wNorm_eq_norm_sqrtWeighted hw, e, norm_smul]
theorem sqrt_weight_mul_norm_le_wNorm {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) (f : J → ℂ) (i : J) :
    Real.sqrt (w i) * ‖f i‖ ≤ wNorm w f := by
  rw [wNorm_eq_sqrt_sum]
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, Real.sq_sqrt (hw i)]
  exact Finset.single_le_sum (f := fun i => w i * ‖f i‖ ^ 2)
    (fun i _ => mul_nonneg (hw i) (sq_nonneg _)) (Finset.mem_univ i)
theorem wNorm_le_sum_sqrt_mul {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) (f : J → ℂ) :
    wNorm w f ≤ ∑ i, Real.sqrt (w i) * ‖f i‖ := by
  have hx : ∀ i, 0 ≤ Real.sqrt (w i) * ‖f i‖ :=
    fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hT : 0 ≤ ∑ i, Real.sqrt (w i) * ‖f i‖ := Finset.sum_nonneg fun i _ => hx i
  rw [wNorm_eq_sqrt_sum]
  refine Real.sqrt_le_iff.2 ⟨hT, ?_⟩
  calc ∑ i, w i * ‖f i‖ ^ 2
      = ∑ i, (Real.sqrt (w i) * ‖f i‖) * (Real.sqrt (w i) * ‖f i‖) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_mul_mul_comm, Real.mul_self_sqrt (hw i), sq]
    _ ≤ ∑ i, (Real.sqrt (w i) * ‖f i‖) * ∑ j, Real.sqrt (w j) * ‖f j‖ := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hx i)
        exact Finset.single_le_sum (f := fun i => Real.sqrt (w i) * ‖f i‖)
          (fun i _ => hx i) (Finset.mem_univ i)
    _ = (∑ i, Real.sqrt (w i) * ‖f i‖) ^ 2 := by
        rw [← Finset.sum_mul, sq]
theorem eq_zero_of_wNorm_eq_zero {w : J → ℝ} (hw : ∀ i, 0 < w i) {f : J → ℂ}
    (h : wNorm w f = 0) : f = 0 := by
  funext i
  have h1 := sqrt_weight_mul_norm_le_wNorm (fun i => (hw i).le) f i
  rw [h] at h1
  have hs : 0 < Real.sqrt (w i) := Real.sqrt_pos.2 (hw i)
  have h2 : ‖f i‖ ≤ 0 := by
    by_contra hc
    exact absurd (mul_pos hs (not_le.1 hc)) (not_lt.2 h1)
  simpa using h2
theorem wNorm_single_one [DecidableEq J] {w : J → ℝ} (i : J) :
    wNorm w (Pi.single i 1 : J → ℂ) = Real.sqrt (w i) := by
  rw [wNorm_eq_sqrt_sum]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp
theorem apply_eq_sum_linearMapEntry (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ) (c' : J') :
    M f c' = ∑ c, linearMapEntry M c' c * f c := by
  classical
  have hf : f = ∑ c, f c • (Pi.single c 1 : J → ℂ) := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, linearMapEntry]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
theorem linearMapOfEntries_linearMapEntry (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) :
    linearMapOfEntries (linearMapEntry M) = M := by
  refine LinearMap.ext fun f => ?_
  funext c'
  rw [linearMapOfEntries_eq_applyKernel, apply_eq_sum_linearMapEntry]
  simp [applyKernel, tsum_fintype]
theorem linearMapEntry_linearMapOfEntries (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by
  classical
  funext c' c
  simp only [linearMapEntry]
  rw [linearMapOfEntries_eq_applyKernel]
  simp [applyKernel, tsum_fintype, Pi.single_apply]
theorem wNorm_apply_le_wOpNorm_mul [Fintype J'] {w : J → ℝ} {w' : J' → ℝ} (hw : ∀ i, 0 < w i)
    (hw' : ∀ i, 0 ≤ w' i) (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ) :
    ENNReal.ofReal (wNorm w' (M f)) ≤
      wOpNorm w w' univ (fun f => M f) * ENNReal.ofReal (wNorm w f) := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  by_cases h0 : wNorm w f = 0
  · have hf := eq_zero_of_wNorm_eq_zero hw h0
    subst hf
    simp [wNorm]
  · have hpos : 0 < wNorm w f := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    set r : ℝ := wNorm w f with hr
    have hg : (((r⁻¹ : ℝ) : ℂ) • f) ∈ wUnitBall w univ := by
      refine ⟨mem_univ _, normSummable_of_fintype _ _, ?_⟩
      rw [wNorm_smul hw0, ← hr, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne']
    have hle : ENNReal.ofReal (wNorm w' (M (((r⁻¹ : ℝ) : ℂ) • f))) ≤
        wOpNorm w w' univ (fun f => M f) :=
      le_iSup₂ (f := fun (g : J → ℂ) (_ : g ∈ wUnitBall w univ) =>
        ENNReal.ofReal (wNorm w' (M g))) _ hg
    have e : wNorm w' (M f) = r * wNorm w' (M (((r⁻¹ : ℝ) : ℂ) • f)) := by
      rw [map_smul, wNorm_smul hw', Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hpos), mul_inv_cancel_left₀ hpos.ne']
    rw [e, ENNReal.ofReal_mul hpos.le, mul_comm]
    gcongr
end Weighted
theorem sqrtOf_eq_sqrt {x : ℝ} (hx : 0 < x) :
    RealPower.sqrtOf x = Real.sqrt x := by
  rw [RealPower.sqrtOf, if_neg hx.ne', RealPower.rpowPos, if_pos hx,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, mul_comm]
section Quotients
variable {I I' I'' : PeriodicData}
theorem ofReal_wNorm_apply_le_of_mem (M : QuotHom I I') {f : I.UnitQuot → ℂ}
    (hf : f ∈ wUnitBall (I.quotWeight 1) univ) :
    ENNReal.ofReal (wNorm (I'.quotWeight 1) (M f)) ≤ quotHomNorm M :=
  le_iSup₂ (f := fun (g : I.UnitQuot → ℂ) (_ : g ∈ wUnitBall (I.quotWeight 1) univ) =>
    ENNReal.ofReal (wNorm (I'.quotWeight 1) (M g))) f hf
theorem quotHomNorm_add_le [Fintype I'.UnitQuot] (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (M N : QuotHom I I') : quotHomNorm (M + N) ≤ quotHomNorm M + quotHomNorm N := by
  refine iSup₂_le fun f hf => ?_
  calc ENNReal.ofReal (wNorm (I'.quotWeight 1) (M f + N f))
      ≤ ENNReal.ofReal (wNorm (I'.quotWeight 1) (M f) +
          wNorm (I'.quotWeight 1) (N f)) :=
        ENNReal.ofReal_le_ofReal (wNorm_add_le (fun c => (hw' c).le) _ _)
    _ ≤ ENNReal.ofReal (wNorm (I'.quotWeight 1) (M f)) +
          ENNReal.ofReal (wNorm (I'.quotWeight 1) (N f)) := ENNReal.ofReal_add_le
    _ ≤ quotHomNorm M + quotHomNorm N :=
        add_le_add (ofReal_wNorm_apply_le_of_mem M hf) (ofReal_wNorm_apply_le_of_mem N hf)
theorem quotHomNorm_smul [Fintype I'.UnitQuot] (hw' : ∀ c, 0 < I'.quotWeight 1 c) (z : ℂ)
    (M : QuotHom I I') : quotHomNorm (z • M) = quotHomNorm M * ENNReal.ofReal ‖z‖ := by
  simp only [quotHomNorm, wOpNorm, ENNReal.iSup_mul]
  refine iSup_congr fun f => iSup_congr fun _ => ?_
  rw [LinearMap.smul_apply, wNorm_smul (fun c => (hw' c).le),
    ENNReal.ofReal_mul (norm_nonneg z), mul_comm]
theorem quotHomNorm_comp_le [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (M : QuotHom I I') (N : QuotHom I'' I) :
    quotHomNorm (M.comp N) ≤ quotHomNorm M * quotHomNorm N := by
  refine iSup₂_le fun f hf => ?_
  show ENNReal.ofReal (wNorm (I'.quotWeight 1) (M (N f))) ≤ _
  refine (wNorm_apply_le_wOpNorm_mul hw (fun c => (hw' c).le) M (N f)).trans ?_
  have := ofReal_wNorm_apply_le_of_mem N hf
  show quotHomNorm M * _ ≤ _
  gcongr
theorem quotHomNorm_id_le : quotHomNorm (LinearMap.id : QuotHom I I) ≤ 1 := by
  refine iSup₂_le fun f hf => ?_
  exact ENNReal.ofReal_le_one.2 hf.2.2
theorem wNorm_apply_le_toReal_mul [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (M : QuotHom I I') (hM : quotHomNorm M < ∞) (f : I.UnitQuot → ℂ) :
    wNorm (I'.quotWeight 1) (M f) ≤
      (quotHomNorm M).toReal * wNorm (I.quotWeight 1) f := by
  have h := wNorm_apply_le_wOpNorm_mul hw (fun c => (hw' c).le) M f
  have hne : quotHomNorm M * ENNReal.ofReal (wNorm (I.quotWeight 1) f) ≠ ∞ :=
    ENNReal.mul_ne_top hM.ne ENNReal.ofReal_ne_top
  have h' := ENNReal.toReal_mono hne h
  have hn : ∀ {J : Type} (w : J → ℝ) (g : J → ℂ), 0 ≤ wNorm w g :=
    fun _ _ => Real.sqrt_nonneg _
  rwa [ENNReal.toReal_ofReal (hn _ _), ENNReal.toReal_mul, ENNReal.toReal_ofReal (hn _ _)] at h'
theorem norm_linearMapEntry_le [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (M : QuotHom I I') (hM : quotHomNorm M < ∞) (c' : I'.UnitQuot) (c : I.UnitQuot) :
    ‖linearMapEntry M c' c‖ ≤ (quotHomNorm M).toReal *
      RealPower.sqrtOf (I.quotWeight 1 c / I'.quotWeight 1 c') := by
  classical
  have hs' : 0 < Real.sqrt (I'.quotWeight 1 c') := Real.sqrt_pos.2 (hw' c')
  have he : linearMapEntry M c' c = M (Pi.single c 1) c' := by
    simp only [linearMapEntry]
  have h1 := sqrt_weight_mul_norm_le_wNorm (fun c => (hw' c).le) (M (Pi.single c 1)) c'
  have h2 := wNorm_apply_le_toReal_mul hw hw' M hM (Pi.single c 1)
  rw [wNorm_single_one] at h2
  rw [sqrtOf_eq_sqrt (div_pos (hw c) (hw' c')), Real.sqrt_div (hw c).le, he, ← mul_div_assoc,
    le_div_iff₀ hs', mul_comm]
  exact h1.trans h2
def weightedEntrySum (I I' : PeriodicData) [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (K : I'.UnitQuot → I.UnitQuot → ℂ) : ℝ :=
  ∑ c', ∑ c, Real.sqrt (I'.quotWeight 1 c') / Real.sqrt (I.quotWeight 1 c) * ‖K c' c‖
theorem weightedEntrySum_nonneg [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (K : I'.UnitQuot → I.UnitQuot → ℂ) : 0 ≤ weightedEntrySum I I' K :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (norm_nonneg _)
theorem quotHomNorm_le_weightedEntrySum [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c) (M : QuotHom I I') :
    quotHomNorm M ≤ ENNReal.ofReal (weightedEntrySum I I' (linearMapEntry M)) := by
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  have hfc : ∀ c, ‖f c‖ ≤ (Real.sqrt (I.quotWeight 1 c))⁻¹ := by
    intro c
    have h1 := sqrt_weight_mul_norm_le_wNorm (fun c => (hw c).le) f c
    have hs : 0 < Real.sqrt (I.quotWeight 1 c) := Real.sqrt_pos.2 (hw c)
    rw [← one_div, le_div_iff₀ hs, mul_comm]
    exact h1.trans hf.2.2
  refine (wNorm_le_sum_sqrt_mul (fun c => (hw' c).le) (M f)).trans ?_
  refine Finset.sum_le_sum fun c' _ => ?_
  calc Real.sqrt (I'.quotWeight 1 c') * ‖M f c'‖
      ≤ Real.sqrt (I'.quotWeight 1 c') *
          ∑ c, ‖linearMapEntry M c' c‖ * (Real.sqrt (I.quotWeight 1 c))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [apply_eq_sum_linearMapEntry]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hfc c) (norm_nonneg _)
    _ = ∑ c, Real.sqrt (I'.quotWeight 1 c') / Real.sqrt (I.quotWeight 1 c) *
          ‖linearMapEntry M c' c‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [div_eq_mul_inv]
        ring
theorem toReal_quotHomNorm_le_add [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (hN : ∀ M : QuotHom I I', quotHomNorm M < ∞) (M M' : QuotHom I I') :
    (quotHomNorm M).toReal ≤ (quotHomNorm M').toReal +
      weightedEntrySum I I' fun c' c => linearMapEntry M c' c - linearMapEntry M' c' c := by
  have e : linearMapEntry (M - M') =
      fun c' c => linearMapEntry M c' c - linearMapEntry M' c' c := rfl
  have h : quotHomNorm M ≤
      ENNReal.ofReal (weightedEntrySum I I' fun c' c =>
        linearMapEntry M c' c - linearMapEntry M' c' c) + quotHomNorm M' := by
    calc quotHomNorm M = quotHomNorm ((M - M') + M') := by rw [sub_add_cancel]
      _ ≤ quotHomNorm (M - M') + quotHomNorm M' := quotHomNorm_add_le hw' _ _
      _ ≤ _ := by
        rw [← e]
        gcongr
        exact quotHomNorm_le_weightedEntrySum hw hw' _
  have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, (hN M').ne⟩) h
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (hN M').ne,
    ENNReal.toReal_ofReal (weightedEntrySum_nonneg _)] at h'
  linarith
theorem abs_sub_toReal_quotHomNorm_le [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (hN : ∀ M : QuotHom I I', quotHomNorm M < ∞) (M M' : QuotHom I I') :
    |(quotHomNorm M).toReal - (quotHomNorm M').toReal| ≤
      weightedEntrySum I I' fun c' c => linearMapEntry M c' c - linearMapEntry M' c' c := by
  have e : (weightedEntrySum I I' fun c' c => linearMapEntry M' c' c - linearMapEntry M c' c) =
      weightedEntrySum I I' fun c' c => linearMapEntry M c' c - linearMapEntry M' c' c := by
    simp only [weightedEntrySum, norm_sub_rev]
  have h1 := toReal_quotHomNorm_le_add hw hw' hN M M'
  have h2 := toReal_quotHomNorm_le_add hw hw' hN M' M
  rw [e] at h2
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
theorem continuous_toReal_quotHomNorm_linearMapOfEntries [Fintype I.UnitQuot]
    [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (hN : ∀ M : QuotHom I I', quotHomNorm M < ∞) :
    Continuous fun K : I'.UnitQuot → I.UnitQuot → ℂ =>
      (quotHomNorm (linearMapOfEntries K : QuotHom I I')).toReal := by
  rw [continuous_iff_continuousAt]
  intro K₀
  have hS : Continuous fun K : I'.UnitQuot → I.UnitQuot → ℂ =>
      weightedEntrySum I I' fun c' c => K c' c - K₀ c' c := by
    unfold weightedEntrySum
    fun_prop
  have h0 : Filter.Tendsto (fun K : I'.UnitQuot → I.UnitQuot → ℂ =>
      weightedEntrySum I I' fun c' c => K c' c - K₀ c' c) (nhds K₀) (nhds 0) := by
    have h := hS.tendsto K₀
    simpa [weightedEntrySum] using h
  show Filter.Tendsto _ _ _
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) (fun K => ?_) h0)
  rw [Real.norm_eq_abs]
  have h := abs_sub_toReal_quotHomNorm_le hw hw' hN (linearMapOfEntries K)
    (linearMapOfEntries K₀)
  simpa only [linearMapEntry_linearMapOfEntries] using h
theorem normContinuousInEntries_of_pos [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (hN : ∀ M : QuotHom I I', quotHomNorm M < ∞) :
    NormContinuousInEntries I I' :=
  ⟨fun K => (quotHomNorm (linearMapOfEntries K : QuotHom I I')).toReal,
    continuous_toReal_quotHomNorm_linearMapOfEntries hw hw' hN,
    fun M => by simp only [linearMapOfEntries_linearMapEntry]⟩
theorem normContinuousAlong_of_continuousInEntries
    (h : NormContinuousInEntries I I') : NormContinuousAlong I I' := by
  intro S M hM
  obtain ⟨φ, hφ, he⟩ := h
  have hc : ContinuousOn (fun κ => φ (linearMapEntry (M κ))) S :=
    hφ.comp_continuousOn
      (continuousOn_pi.2 fun c' => continuousOn_pi.2 fun c => hM.2 (c', c))
  simpa only [he] using hc
theorem normBoundedIffEntriesBounded_of_pos [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
    (hw : ∀ c, 0 < I.quotWeight 1 c) (hw' : ∀ c, 0 < I'.quotWeight 1 c)
    (hN : ∀ M : QuotHom I I', quotHomNorm M < ∞) :
    NormBoundedIffEntriesBounded I I' := by
  intro X S M
  constructor
  · rintro ⟨C, hC⟩ e
    have hr : 0 ≤ RealPower.sqrtOf (I.quotWeight 1 e.2 / I'.quotWeight 1 e.1) := by
      rw [sqrtOf_eq_sqrt (div_pos (hw _) (hw' _))]
      exact Real.sqrt_nonneg _
    refine ⟨C * RealPower.sqrtOf (I.quotWeight 1 e.2 / I'.quotWeight 1 e.1),
      fun x hx => ?_⟩
    show ‖linearMapEntry (M x) e.1 e.2‖ ≤ _
    refine (norm_linearMapEntry_le hw hw' (M x) (hN _) e.1 e.2).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hC x hx)) hr
  · intro hB
    have hB' : ∀ e : I'.UnitQuot × I.UnitQuot, ∃ C : ℝ, ∀ x ∈ S,
        ‖linearMapEntry (M x) e.1 e.2‖ ≤ C := hB
    choose C hC using hB'
    refine ⟨∑ c', ∑ c, Real.sqrt (I'.quotWeight 1 c') / Real.sqrt (I.quotWeight 1 c) * C (c', c),
      fun x hx => ?_⟩
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (quotHomNorm_le_weightedEntrySum hw hw' (M x))
    rw [ENNReal.toReal_ofReal (weightedEntrySum_nonneg _)] at h
    refine h.trans (Finset.sum_le_sum fun c' _ => Finset.sum_le_sum fun c _ => ?_)
    exact mul_le_mul_of_nonneg_left (hC (c', c) x hx)
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
theorem complexModuleStructure_holds : ComplexModuleStructure I I' :=
  ⟨LinearMap.addCommGroup, LinearMap.module, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
theorem quotOneIsIdNormLeOne_holds [Fintype I.UnitQuot] :
    QuotOneIsIdNormLeOne I := by
  classical
  refine ⟨LinearMap.ext fun f => ?_, quotHomNorm_id_le⟩
  funext c'
  rw [linearMapOfEntries_eq_applyKernel]
  simp [applyKernel, tsum_fintype, quotOne]
theorem subAndEntriesOfLinComb_holds [Fintype I.UnitQuot] :
    SubAndEntriesOfLinComb I I' := by
  intro M M' z
  have e₁ : ∀ c' c, linearMapEntry (M + M') c' c = linearMapEntry M c' c + linearMapEntry M' c' c :=
    fun _ _ => rfl
  have e₂ : ∀ c' c, linearMapEntry (z • M) c' c = z * linearMapEntry M c' c := fun _ _ => rfl
  have e₃ : ∀ c' c, linearMapEntry (M - M') c' c = linearMapEntry M c' c - linearMapEntry M' c' c :=
    fun _ _ => rfl
  refine ⟨by rw [neg_one_smul ℂ M', sub_eq_add_neg], fun c' c => ⟨e₁ c' c, e₂ c' c, e₃ c' c⟩,
    ?_, ?_, ?_⟩
  · refine (linearMapOfEntries_linearMapEntry _).symm.trans (congrArg linearMapOfEntries ?_)
    funext c' c
    simp [kernelLinComb, e₁]
  · refine (linearMapOfEntries_linearMapEntry _).symm.trans (congrArg linearMapOfEntries ?_)
    funext c' c
    exact e₂ c' c
  · refine (linearMapOfEntries_linearMapEntry _).symm.trans (congrArg linearMapOfEntries ?_)
    funext c' c
    rw [e₃]
    simp [kernelLinComb, sub_eq_add_neg]
theorem quotWeight_pos (hQ : Quotients.QuotientTransposeNorm) (hI : IsPeriodic I)
    (c : I.UnitQuot) : 0 < I.quotWeight 1 c := by
  obtain ⟨ι, rfl⟩ : ∃ ι, I.mkQuot 1 ι = c := Quot.exists_rep c
  rw [((hQ I I hI hI 1 one_pos).2.1 1 (Or.inl rfl)).1.2 ι]
  exact hI.weight_pos _
end Quotients
theorem claim_of_quotientTransposeNorm (hQ : Quotients.QuotientTransposeNorm) : Claim := by
  intro I I' hI hI'
  have hfin : Quotients.LinearMapNormFinite I I' 1 1 :=
    ((hQ I I' hI hI' 1 one_pos).2.2.1 1 1 (Or.inl rfl) (Or.inl rfl)).1
  have hN : ∀ M : QuotHom I I', quotHomNorm M < ∞ := fun M => (hfin M).2
  have hf₁ : Finite I.UnitQuot := hI.finite_quot
  have hf₂ : Finite I'.UnitQuot := hI'.finite_quot
  let _ : Fintype I.UnitQuot := Fintype.ofFinite _
  let _ : Fintype I'.UnitQuot := Fintype.ofFinite _
  have hw : ∀ c, 0 < I.quotWeight 1 c := quotWeight_pos hQ hI
  have hw' : ∀ c, 0 < I'.quotWeight 1 c := quotWeight_pos hQ hI'
  have hc := normContinuousInEntries_of_pos hw hw' hN
  refine ⟨hfin, hc, normContinuousAlong_of_continuousInEntries hc,
    fun M c' c => norm_linearMapEntry_le hw hw' M (hN M) c' c,
    normBoundedIffEntriesBounded_of_pos hw hw' hN,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, complexModuleStructure_holds, quotHomNorm_add_le hw',
      quotHomNorm_smul hw'⟩,
    fun I'' _ => ⟨fun M f => wNorm_apply_le_toReal_mul hw hw' M (hN M) f,
      fun M M'' => quotHomNorm_comp_le hw hw' M M''⟩,
    quotOneIsIdNormLeOne_holds,
    subAndEntriesOfLinComb_holds⟩
end HomNorm
end PeriodicOperators
end YangMills.Construction
end
