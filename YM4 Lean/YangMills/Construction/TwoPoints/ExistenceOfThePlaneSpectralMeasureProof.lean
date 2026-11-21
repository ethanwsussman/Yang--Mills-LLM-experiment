import YangMills.Construction.SpectralCalculus.PositiveMeasureOfLimits
import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import YangMills.Construction.TwoPoints.ExistenceOfThePlaneSpectralMeasure
import YangMills.Construction.TwoPoints.OneFieldSpaceAndSlidesAlongTheNormal
import YangMills.Construction.TwoPoints.PropertiesOfThePlaneKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace YangMills.Construction
open SpectralCalculus
namespace TwoPoints
open InfiniteLattice (AmbientSpace)
namespace AveragedKernelSpectralMeasure
structure IsProbWeight (w : ℝ → ℝ) (C : Set ℝ) : Prop where
  smooth : ContDiff ℝ 1 w
  nonneg : ∀ x, 0 ≤ w x
  integral_eq_one : ∫ x, w x = 1
  isCompact_set : IsCompact C
  eq_zero_off : ∀ x, x ∉ C → w x = 0
theorem exists_probWeight (c r : ℝ) (hr : 0 < r) :
    ∃ w : ℝ → ℝ, IsProbWeight w (Metric.closedBall c r) := by
  let f : ContDiffBump c := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨f.normed volume, f.contDiff_normed, fun x => f.nonneg_normed x, f.integral_normed,
    isCompact_closedBall c r, fun x hx => ?_⟩
  have hs : x ∉ Function.support (f.normed volume) := by
    rw [f.support_normed_eq]
    exact fun h => hx (Metric.ball_subset_closedBall h)
  simpa using hs
section Iterated
variable {F : Type*} [TopologicalSpace F] [SecondCountableTopology F] [MeasureSpace F]
  [BorelSpace F] [SFinite (volume : Measure F)] [IsFiniteMeasureOnCompacts (volume : Measure F)]
theorem integral_prod_eq_iterated (H : ℝ × F → ℂ) (hc : Continuous H) (hs : HasCompactSupport H) :
    ∫ z, H z = ∫ x, ∫ y, H (x, y) := by
  have hi : Integrable H (volume : Measure (ℝ × F)) := hc.integrable_of_hasCompactSupport hs
  rw [Measure.volume_eq_prod] at hi ⊢
  exact integral_prod H hi
omit [SecondCountableTopology F] [MeasureSpace F] [BorelSpace F] in
theorem continuous_slice {H : ℝ × F → ℂ} (hc : Continuous H) (x : ℝ) :
    Continuous fun y => H (x, y) :=
  hc.comp (continuous_const.prodMk continuous_id)
omit [SecondCountableTopology F] [MeasureSpace F] [BorelSpace F] in
theorem hasCompactSupport_slice [T2Space F] {H : ℝ × F → ℂ} (hs : HasCompactSupport H) (x : ℝ) :
    HasCompactSupport fun y => H (x, y) := by
  refine HasCompactSupport.intro (hs.isCompact.image continuous_snd) fun y hy => ?_
  by_contra h
  exact hy ⟨(x, y), subset_tsupport _ h, rfl⟩
omit [TopologicalSpace F] [SecondCountableTopology F] [BorelSpace F]
  [IsFiniteMeasureOnCompacts (volume : Measure F)] in
theorem integral_mul_prod_eq (f : ℝ → ℝ) (g : F → ℝ) :
    ∫ z : ℝ × F, f z.1 * g z.2 = (∫ x, f x) * ∫ y, g y := by
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul f g
end Iterated
theorem norm_iterated4_sub_le {w₁ w₂ w₃ w₄ : ℝ → ℝ} {C₁ C₂ C₃ C₄ : Set ℝ}
    (h₁ : IsProbWeight w₁ C₁) (h₂ : IsProbWeight w₂ C₂) (h₃ : IsProbWeight w₃ C₃)
    (h₄ : IsProbWeight w₄ C₄)
    (K : ℝ × ℝ × ℝ × ℝ → ℂ) (c : ℂ) (ε : ℝ)
    (hK : ∀ x ∈ C₄ ×ˢ C₃ ×ˢ C₂ ×ˢ C₁, ContinuousAt K x)
    (hc : ∀ x ∈ C₄ ×ˢ C₃ ×ˢ C₂ ×ˢ C₁, ‖K x - c‖ ≤ ε) :
    ‖(∫ x₄, ∫ x₃, ∫ x₂, ∫ x₁,
        ((w₄ x₄ * (w₃ x₃ * (w₂ x₂ * w₁ x₁)) : ℝ) : ℂ) * K (x₄, x₃, x₂, x₁)) - c‖ ≤ ε := by
  have hbox : IsCompact (C₄ ×ˢ C₃ ×ˢ C₂ ×ˢ C₁) :=
    h₄.isCompact_set.prod (h₃.isCompact_set.prod (h₂.isCompact_set.prod h₁.isCompact_set))
  let W : ℝ × ℝ × ℝ × ℝ → ℝ := fun x => w₄ x.1 * (w₃ x.2.1 * (w₂ x.2.2.1 * w₁ x.2.2.2))
  have c₁ := h₁.smooth.continuous
  have c₂ := h₂.smooth.continuous
  have c₃ := h₃.smooth.continuous
  have c₄ := h₄.smooth.continuous
  have hWc : Continuous W := by
    simp only [W]
    fun_prop
  have hW0 : ∀ x, x ∉ C₄ ×ˢ C₃ ×ˢ C₂ ×ˢ C₁ → W x = 0 := by
    rintro ⟨x₄, x₃, x₂, x₁⟩ hx
    simp only [mem_prod, not_and_or] at hx
    rcases hx with h | h | h | h
    · simp [W, h₄.eq_zero_off _ h]
    · simp [W, h₃.eq_zero_off _ h]
    · simp [W, h₂.eq_zero_off _ h]
    · simp [W, h₁.eq_zero_off _ h]
  have hWn : ∀ x, 0 ≤ W x := fun x =>
    mul_nonneg (h₄.nonneg _) (mul_nonneg (h₃.nonneg _) (mul_nonneg (h₂.nonneg _) (h₁.nonneg _)))
  have hWi : ∫ x, W x = 1 := by
    have e₁ : ∫ z : ℝ × ℝ, w₂ z.1 * w₁ z.2 = 1 := by
      rw [integral_mul_prod_eq, h₂.integral_eq_one, h₁.integral_eq_one, one_mul]
    have e₂ : ∫ z : ℝ × ℝ × ℝ, w₃ z.1 * (w₂ z.2.1 * w₁ z.2.2) = 1 := by
      rw [integral_mul_prod_eq w₃ (fun z : ℝ × ℝ => w₂ z.1 * w₁ z.2), h₃.integral_eq_one, e₁,
        one_mul]
    simp only [W]
    rw [integral_mul_prod_eq w₄ (fun z : ℝ × ℝ × ℝ => w₃ z.1 * (w₂ z.2.1 * w₁ z.2.2)),
      h₄.integral_eq_one, e₂, one_mul]
  have hWs : HasCompactSupport W := HasCompactSupport.intro hbox hW0
  have hWint : Integrable W := hWc.integrable_of_hasCompactSupport hWs
  let H : ℝ × ℝ × ℝ × ℝ → ℂ := fun x => (W x : ℂ) * K x
  have hH0 : ∀ x, x ∉ C₄ ×ˢ C₃ ×ˢ C₂ ×ˢ C₁ → H x = 0 := fun x hx => by simp [H, hW0 x hx]
  have hHs : HasCompactSupport H := HasCompactSupport.intro hbox hH0
  have hsub : tsupport H ⊆ C₄ ×ˢ C₃ ×ˢ C₂ ×ˢ C₁ := by
    refine closure_minimal (fun x hx => ?_) hbox.isClosed
    by_contra h
    exact hx (hH0 x h)
  have hHc : Continuous H := by
    refine continuous_of_tsupport fun x hx => ?_
    exact (Complex.continuous_ofReal.comp hWc).continuousAt.mul (hK x (hsub hx))
  have hHint : Integrable H := hHc.integrable_of_hasCompactSupport hHs
  have hit : (∫ x₄, ∫ x₃, ∫ x₂, ∫ x₁,
      ((w₄ x₄ * (w₃ x₃ * (w₂ x₂ * w₁ x₁)) : ℝ) : ℂ) * K (x₄, x₃, x₂, x₁)) = ∫ x, H x := by
    have e₁ := integral_prod_eq_iterated H hHc hHs
    have e₂ : ∀ x₄, ∫ q, H (x₄, q) = ∫ x₃, ∫ q, H (x₄, x₃, q) := fun x₄ =>
      integral_prod_eq_iterated _ (continuous_slice hHc x₄) (hasCompactSupport_slice hHs x₄)
    have e₃ : ∀ x₄ x₃, ∫ q, H (x₄, x₃, q) = ∫ x₂, ∫ x₁, H (x₄, x₃, x₂, x₁) := fun x₄ x₃ =>
      integral_prod_eq_iterated _ (continuous_slice (continuous_slice hHc x₄) x₃)
        (hasCompactSupport_slice (hasCompactSupport_slice hHs x₄) x₃)
    rw [e₁]
    simp only [e₂, e₃]
    rfl
  have hcW : ∫ x, (W x : ℂ) * c = c := by
    rw [integral_mul_const, integral_complex_ofReal, hWi]
    simp
  have hWcI : Integrable fun x => (W x : ℂ) * c := hWint.ofReal.mul_const c
  rw [hit]
  calc ‖(∫ x, H x) - c‖ = ‖∫ x, (H x - (W x : ℂ) * c)‖ := by
        rw [integral_sub hHint hWcI, hcW]
    _ ≤ ∫ x, W x * ε := by
        refine norm_integral_le_of_norm_le (hWint.mul_const ε) (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ C₄ ×ˢ C₃ ×ˢ C₂ ×ˢ C₁
        · have : H x - (W x : ℂ) * c = (W x : ℂ) * (K x - c) := by
            simp only [H]
            ring
          rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hWn x)]
          exact mul_le_mul_of_nonneg_left (hc x hx) (hWn x)
        · simp [H, hW0 x hx]
    _ = ε := by rw [integral_mul_const, hWi, one_mul]
def rotatedBump (a b : ℝ) (A B : ℝ → ℝ) (y : Fin 2 → ℝ) : ℂ :=
  ((A (a * y 0 + b * y 1) * B (-b * y 0 + a * y 1) : ℝ) : ℂ)
theorem rotatedBump_mem_cc1In {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {A B : ℝ → ℝ} {CA CB : Set ℝ}
    (hA : IsProbWeight A CA) (hB : IsProbWeight B CB) (hpos : CA ⊆ Ioi 0) :
    rotatedBump a b A B ∈ cc1In {y : Fin 2 → ℝ | 0 < euclidDot ![a, b] y} := by
  let inv : ℝ × ℝ → Fin 2 → ℝ := fun u => ![a * u.1 - b * u.2, b * u.1 + a * u.2]
  have hinv : Continuous inv := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [inv] <;> fun_prop
  have hL : IsCompact (inv '' (CA ×ˢ CB)) :=
    (hA.isCompact_set.prod hB.isCompact_set).image hinv
  have hsub : tsupport (rotatedBump a b A B) ⊆ inv '' (CA ×ˢ CB) := by
    refine closure_minimal (fun y hy => ?_) hL.isClosed
    have hy' : A (a * y 0 + b * y 1) * B (-b * y 0 + a * y 1) ≠ 0 := fun h =>
      hy (by simp only [rotatedBump]; rw [h]; simp)
    have hu : a * y 0 + b * y 1 ∈ CA := by
      by_contra h
      exact hy' (by rw [hA.eq_zero_off _ h, zero_mul])
    have hv : -b * y 0 + a * y 1 ∈ CB := by
      by_contra h
      exact hy' (by rw [hB.eq_zero_off _ h, mul_zero])
    refine ⟨(a * y 0 + b * y 1, -b * y 0 + a * y 1), ⟨hu, hv⟩, ?_⟩
    funext i
    fin_cases i
    · simp only [inv]
      simp
      linear_combination (y 0) * hab
    · simp only [inv]
      simp
      linear_combination (y 1) * hab
  show ContDiff ℝ 1 (rotatedBump a b A B) ∧ IsCompact (tsupport (rotatedBump a b A B)) ∧
    tsupport (rotatedBump a b A B) ⊆ {y : Fin 2 → ℝ | 0 < euclidDot ![a, b] y}
  refine ⟨?_, hL.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans ?_⟩
  · have l₁ : ContDiff ℝ 1 fun y : Fin 2 → ℝ => a * y 0 + b * y 1 :=
      (contDiff_const.mul (contDiff_apply ℝ ℝ 0)).add (contDiff_const.mul (contDiff_apply ℝ ℝ 1))
    have l₂ : ContDiff ℝ 1 fun y : Fin 2 → ℝ => -b * y 0 + a * y 1 :=
      (contDiff_const.mul (contDiff_apply ℝ ℝ 0)).add (contDiff_const.mul (contDiff_apply ℝ ℝ 1))
    exact Complex.ofRealCLM.contDiff.comp ((hA.smooth.comp l₁).mul (hB.smooth.comp l₂))
  · rintro _ ⟨⟨u, v⟩, ⟨hu, -⟩, rfl⟩
    have hu' : 0 < u := hpos hu
    have : euclidDot ![a, b] (inv (u, v)) = u := by
      simp only [euclidDot, Fin.sum_univ_two, inv]
      simp
      linear_combination u * hab
    simpa [this] using hu'
theorem planeCoords_frame (m : AmbientSpace) (t s : ℝ) :
    planeCoords (t • m + s • planePerp m) = ![m 3 * t - m 0 * s, m 0 * t + m 3 * s] := by
  funext i
  fin_cases i <;> simp [planeCoords, planePerp, PeriodicLattice.coordVec] <;> ring
theorem rotatedBump_planeCoords {m : AmbientSpace} (hab : m 3 ^ 2 + m 0 ^ 2 = 1) (A B : ℝ → ℝ)
    (t s : ℝ) :
    rotatedBump (m 3) (m 0) A B (planeCoords (t • m + s • planePerp m)) = ((A t * B s : ℝ) : ℂ) := by
  rw [planeCoords_frame]
  have e₁ : m 3 * (m 3 * t - m 0 * s) + m 0 * (m 0 * t + m 3 * s) = t := by
    linear_combination t * hab
  have e₂ : -m 0 * (m 3 * t - m 0 * s) + m 3 * (m 0 * t + m 3 * s) = s := by
    linear_combination s * hab
  simp only [rotatedBump, Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂]
theorem planeCoords_frame_ne_zero {m : AmbientSpace} (hab : m 3 ^ 2 + m 0 ^ 2 = 1) {t : ℝ}
    (ht : t ≠ 0) (s : ℝ) : planeCoords (t • m + s • planePerp m) ≠ 0 := by
  intro h
  rw [planeCoords_frame] at h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp at h₀ h₁
  exact ht (by linear_combination m 3 * h₀ + m 0 * h₁ - t * hab)
def bumpWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
theorem bumpWidth_pos (n : ℕ) : 0 < bumpWidth n := by
  unfold bumpWidth
  positivity
theorem abs_le_of_mem_closedBall_half {σ x : ℝ} (hσ : 0 < σ)
    (h : x ∈ Metric.closedBall (σ / 2) (σ / 4)) : |x| ≤ σ := by
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at h
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]
theorem tendsto_normalFrameIntegral {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    {φ : (Fin 2 → ℝ) → ℂ} {m : AmbientSpace} (hab : m 3 ^ 2 + m 0 ^ 2 = 1)
    (hcont : ContinuousOn (transverseAveragedKernel S φ) {y | y ≠ 0}) {A B : ℕ → ℝ → ℝ}
    (hA : ∀ n, IsProbWeight (A n) (Metric.closedBall (bumpWidth n / 2) (bumpWidth n / 4)))
    (hB : ∀ n, IsProbWeight (B n) (Metric.closedBall 0 (bumpWidth n)))
    {T : ℝ} (hT : 0 < T) (s : ℝ) :
    Tendsto (fun p : ℕ × ℕ => normalFrameIntegral S φ m (rotatedBump (m 3) (m 0) (A p.1) (B p.1))
        (rotatedBump (m 3) (m 0) (A p.2) (B p.2)) T s) atTop
      (𝓝 (transverseAveragedKernel S φ (planeCoords (T • m + s • planePerp m)))) := by
  let Y : ℝ × ℝ × ℝ × ℝ → Fin 2 → ℝ := fun x =>
    planeCoords ((T + x.2.2.2 + x.2.1) • m + (s + x.1 - x.2.2.1) • planePerp m)
  have hY : Continuous Y := by
    have hYe : Y = fun x => ![m 3 * (T + x.2.2.2 + x.2.1) - m 0 * (s + x.1 - x.2.2.1),
        m 0 * (T + x.2.2.2 + x.2.1) + m 3 * (s + x.1 - x.2.2.1)] := by
      funext x
      exact planeCoords_frame m _ _
    rw [hYe]
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have hY0 : Y 0 = planeCoords (T • m + s • planePerp m) := by
    simp [Y]
  have h0 : Y 0 ≠ 0 := by
    rw [hY0]
    exact planeCoords_frame_ne_zero hab hT.ne' s
  have hGc : ContinuousAt (transverseAveragedKernel S φ) (Y 0) :=
    hcont.continuousAt (isOpen_ne.mem_nhds h0)
  have hK0 : ContinuousAt (fun x => transverseAveragedKernel S φ (Y x)) 0 :=
    ContinuousAt.comp (f := Y) (g := transverseAveragedKernel S φ) hGc hY.continuousAt
  rw [← hY0, Metric.tendsto_nhds]
  intro ε hε
  have ev : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ × ℝ × ℝ),
      dist (transverseAveragedKernel S φ (Y x)) (transverseAveragedKernel S φ (Y 0)) < ε / 2 ∧
        Y x ≠ 0 :=
    (Metric.tendsto_nhds.mp hK0 (ε / 2) (by positivity)).and
      (hY.continuousAt.eventually_ne h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ev
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  have hsm : ∀ n, N ≤ n → bumpWidth n < δ := fun n hn => by
    refine lt_of_le_of_lt ?_ hN
    unfold bumpWidth
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
  filter_upwards [eventually_ge_atTop (N, N)] with p hp
  have hp₁ : bumpWidth p.1 < δ := hsm _ hp.1
  have hp₂ : bumpWidth p.2 < δ := hsm _ hp.2
  have hbox : ∀ x ∈ Metric.closedBall 0 (bumpWidth p.2) ×ˢ
      Metric.closedBall (bumpWidth p.2 / 2) (bumpWidth p.2 / 4) ×ˢ
      Metric.closedBall 0 (bumpWidth p.1) ×ˢ
      Metric.closedBall (bumpWidth p.1 / 2) (bumpWidth p.1 / 4),
      dist x (0 : ℝ × ℝ × ℝ × ℝ) < δ := by
    rintro ⟨x₄, x₃, x₂, x₁⟩ ⟨m₄, m₃, m₂, m₁⟩
    have a₄ : |x₄| ≤ bumpWidth p.2 := by simpa using m₄
    have a₃ : |x₃| ≤ bumpWidth p.2 := abs_le_of_mem_closedBall_half (bumpWidth_pos _) m₃
    have a₂ : |x₂| ≤ bumpWidth p.1 := by simpa using m₂
    have a₁ : |x₁| ≤ bumpWidth p.1 := abs_le_of_mem_closedBall_half (bumpWidth_pos _) m₁
    rw [dist_zero_right]
    simp only [Prod.norm_def, Real.norm_eq_abs]
    exact max_lt (by linarith) (max_lt (by linarith) (max_lt (by linarith) (by linarith)))
  have hform : normalFrameIntegral S φ m (rotatedBump (m 3) (m 0) (A p.1) (B p.1))
      (rotatedBump (m 3) (m 0) (A p.2) (B p.2)) T s =
      ∫ x₄, ∫ x₃, ∫ x₂, ∫ x₁,
        ((B p.2 x₄ * (A p.2 x₃ * (B p.1 x₂ * A p.1 x₁)) : ℝ) : ℂ) *
          transverseAveragedKernel S φ (Y (x₄, x₃, x₂, x₁)) := by
    have hpt : ∀ x₄ x₃ x₂ x₁ : ℝ,
        conjFun (rotatedBump (m 3) (m 0) (A p.1) (B p.1)) (planeCoords (x₁ • m + x₂ • planePerp m)) *
          rotatedBump (m 3) (m 0) (A p.2) (B p.2) (planeCoords (x₃ • m + x₄ • planePerp m)) *
          transverseAveragedKernel S φ
            (planeCoords ((T + x₁ + x₃) • m + (s + x₄ - x₂) • planePerp m)) =
        ((B p.2 x₄ * (A p.2 x₃ * (B p.1 x₂ * A p.1 x₁)) : ℝ) : ℂ) *
          transverseAveragedKernel S φ (Y (x₄, x₃, x₂, x₁)) := by
      intro x₄ x₃ x₂ x₁
      simp only [conjFun]
      rw [rotatedBump_planeCoords hab, rotatedBump_planeCoords hab, Complex.conj_ofReal]
      simp only [Y]
      push_cast
      ring
    simp only [normalFrameIntegral, lebesgueIntegral, integralWrt, hpt]
  rw [hform, dist_eq_norm]
  refine lt_of_le_of_lt (norm_iterated4_sub_le (hA p.1) (hB p.1) (hA p.2) (hB p.2)
    (fun x => transverseAveragedKernel S φ (Y x)) (transverseAveragedKernel S φ (Y 0)) (ε / 2)
    ?_ ?_) (by linarith)
  · intro x hx
    have hne : Y x ≠ 0 := (hball (hbox x hx)).2
    exact ContinuousAt.comp (f := Y) (g := transverseAveragedKernel S φ)
      (hcont.continuousAt (isOpen_ne.mem_nhds hne)) hY.continuousAt
  · intro x hx
    have := (hball (hbox x hx)).1
    rw [dist_eq_norm] at this
    exact this.le
theorem inner_reflectedClass {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {n : AmbientSpace}
    (hform : IsPosHermitianForm (reflectedForm S n)) (f g : halfSpaceDomain n) :
    inner ℂ (reflectedClass S n f) (reflectedClass S n g) = reflectedForm S n f g := by
  have h := tendsto_inner_seqClass (reflectedForm S n)
    (isFormCauchy_const (reflectedForm S n) f) (isFormCauchy_const (reflectedForm S n) g)
  have h' := tendsto_nhds_unique h tendsto_const_nhds
  rw [posHermitianPart_of_isPosHermitianForm hform] at h'
  exact h'
theorem inner_transfer_lateral {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    {m m' : AmbientSpace}
    (hform : IsPosHermitianForm (reflectedForm S m))
    (hpair : IsCommutingSemigroupGroup (transferSemigroup S m) (lateralGroup S m m'))
    (hT : ∀ t : ℝ≥0, ActsByTranslation S m ((t : ℝ) • m) (transferSemigroup S m t))
    (hU : ∀ s : ℝ, ActsByTranslation S m (s • m') (lateralGroup S m m' s))
    (f g : halfSpaceDomain m) (t₀ t : ℝ≥0) (s : ℝ)
    (h' : translateFun (((2 * t₀ + t : ℝ≥0) : ℝ) • m + s • m') (g : AmbientSpace → ℂ) ∈
      halfSpaceDomain m) :
    inner ℂ (transferSemigroup S m t₀ (reflectedClass S m f))
      (transferSemigroup S m t (lateralGroup S m m' s
        (transferSemigroup S m t₀ (reflectedClass S m g)))) =
      reflectedForm S m f ⟨_, h'⟩ := by
  have hs := hpair.semigroup
  have e₁ : lateralGroup S m m' s (transferSemigroup S m t₀ (reflectedClass S m g)) =
      transferSemigroup S m t₀ (lateralGroup S m m' s (reflectedClass S m g)) :=
    (congrArg (fun B => B (reflectedClass S m g)) (hpair.commute t₀ s).eq).symm
  have e₂ : ∀ w, transferSemigroup S m t₀ (transferSemigroup S m t (transferSemigroup S m t₀ w)) =
      transferSemigroup S m (2 * t₀ + t) w := by
    intro w
    have hτ : t₀ + t + t₀ = 2 * t₀ + t := by ring
    have h₁ := hs.map_add t₀ t
    have h₂ := hs.map_add (t₀ + t) t₀
    rw [← hτ, ← h₂, ← h₁]
    rfl
  obtain ⟨hU', eU⟩ := hU s g
  obtain ⟨hT', eT⟩ := hT (2 * t₀ + t) ⟨_, hU'⟩
  have e₃ : (⟨translateFun (((2 * t₀ + t : ℝ≥0) : ℝ) • m)
      (translateFun (s • m') (g : AmbientSpace → ℂ)), hT'⟩ : halfSpaceDomain m) = ⟨_, h'⟩ := by
    refine Subtype.ext ?_
    funext x
    simp only [translateFun, sub_sub]
  calc _ = inner ℂ (reflectedClass S m f) (transferSemigroup S m t₀ (transferSemigroup S m t
        (lateralGroup S m m' s (transferSemigroup S m t₀ (reflectedClass S m g))))) :=
        hs.isSymmetricBounded t₀ _ _
    _ = inner ℂ (reflectedClass S m f) (reflectedClass S m ⟨_, h'⟩) := by
        rw [e₁, e₂, eU, eT, e₃]
    _ = _ := inner_reflectedClass hform f _
theorem exists_spectralMeasure (h₁ : PositiveSpectralMeasureOfLimits)
    (h₂ : ReflectedSpaceAndSlides.Statement) (h₃ : AveragedKernelProperties.Statement)
    (h₄ : ReflectionsPlaneFacts.Statement) :
    AveragedKernelSpectralMeasureExists.Statement := by
  intro St S φ hS hP hφ m hm
  obtain ⟨C₂, hC₂⟩ := hP.ballDecay
  have hone : IsReflectedFormData St S m := ⟨hS, hm.1, hP⟩
  obtain ⟨⟨hsemi, hgroup, -⟩, -⟩ := h₂ St S C₂ m hone hC₂
  obtain ⟨hker, -, hframes⟩ := h₃ St S hS hP φ hφ
  have hframe := hframes m hm
  obtain ⟨-, -, -, h8, hdir, -⟩ := h₄
  have hm' := hm
  rw [h8.1] at hm'
  obtain ⟨j, hj⟩ := hm'
  obtain ⟨-, ⟨b₁, b₂, b₃, -⟩, -, -⟩ := hdir.1 _ 0 m hj
  have hperp : transCoords m = 0 := hm.2
  have m₁ : m 1 = 0 := congrFun hperp 0
  have m₂ : m 2 = 0 := congrFun hperp 1
  have hab : m 3 ^ 2 + m 0 ^ 2 = 1 := by
    simp only [planeOrthoFrame, euclidDot, Fin.sum_univ_four, m₁, m₂] at b₁
    linarith
  have hunit : IsUnitNormalTo m (planePerp m) := by
    refine ⟨?_, ?_⟩
    · have hsum : ∑ μ, planePerp m μ ^ 2 = 1 := by
        simp only [planeOrthoFrame, euclidDot] at b₂
        rw [← b₂]
        exact Finset.sum_congr rfl fun μ _ => pow_two _
      rw [euclidNorm, hsum, Real.sqrt_one]
    · simp only [planeOrthoFrame, euclidDot] at b₃
      rw [euclidDot, ← b₃]
      exact Finset.sum_congr rfl fun μ _ => mul_comm _ _
  have hpair := (hgroup _ hunit).commuting
  have hT : ∀ t : ℝ≥0, ActsByTranslation S m ((t : ℝ) • m) (transferSemigroup S m t) :=
    fun t => Classical.epsilon_spec (hsemi.translation_extends t).2.exists
  have hU : ∀ s : ℝ, ActsByTranslation S m (s • planePerp m)
      (lateralGroup S m (planePerp m) s) :=
    fun s => Classical.epsilon_spec ((hgroup _ hunit).translation_extends s).2.exists
  choose A hA using fun n => exists_probWeight (bumpWidth n / 2) (bumpWidth n / 4)
    (by have := bumpWidth_pos n; positivity)
  choose B hB using fun n => exists_probWeight 0 (bumpWidth n) (bumpWidth_pos n)
  have hpos : ∀ n, Metric.closedBall (bumpWidth n / 2) (bumpWidth n / 4) ⊆ Ioi 0 := by
    intro n x hx
    have hσ := bumpWidth_pos n
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    simp only [mem_Ioi]
    linarith [hx.1]
  have hα : ∀ n, rotatedBump (m 3) (m 0) (A n) (B n) ∈
      cc1In {y : Fin 2 → ℝ | 0 < euclidDot (planeCoords m) y} :=
    fun n => rotatedBump_mem_cc1In hab (hA n) (hB n) (hpos n)
  have hdom : ∀ n, tensorPlate (rotatedBump (m 3) (m 0) (A n) (B n)) φ ∈ halfSpaceDomain m :=
    fun n => by
      obtain ⟨h, -⟩ := hframe _ (hα n) _ (hα n) 0 le_rfl 0
      exact h
  have hreal : ∀ t : ℝ≥0, 0 < t →
      (transverseAveragedKernel S φ (planeCoords (((t : ℝ)) • m + (0 : ℝ) • planePerp m))).im = 0 :=
    fun t ht => hker.im_eq_zero _ (planeCoords_frame_ne_zero hab (by exact_mod_cast ht.ne') 0)
  obtain ⟨ρ, hρ⟩ := h₁ (ReflectedSpace S m) (transferSemigroup S m)
    (lateralGroup S m (planePerp m))
    (fun n => reflectedClass S m ⟨_, hdom n⟩)
    (fun t s => transverseAveragedKernel S φ (planeCoords ((t : ℝ) • m + s • planePerp m)))
    hpair hreal (by
      intro t₀ ht₀ t s
      have hτ : (0 : ℝ) < ((2 * t₀ + t : ℝ≥0) : ℝ) := by
        have : 0 < 2 * t₀ + t := by positivity
        exact_mod_cast this
      refine (tendsto_normalFrameIntegral hab hker.continuousOn hA hB hτ s).congr fun p => ?_
      obtain ⟨h, h', ef⟩ :=
        hframe _ (hα p.1) _ (hα p.2) ((2 * t₀ + t : ℝ≥0) : ℝ) (NNReal.coe_nonneg _) s
      exact ef.symm.trans
        (inner_transfer_lateral hsemi.posHermitian hpair hT hU ⟨_, hdom p.1⟩ ⟨_, hdom p.2⟩
          t₀ t s h').symm)
  exact ⟨ρ, fun t ht => (hρ t ht).1, fun t ht s => (hρ t ht).2 s⟩
end AveragedKernelSpectralMeasure
end TwoPoints
end YangMills.Construction
end
