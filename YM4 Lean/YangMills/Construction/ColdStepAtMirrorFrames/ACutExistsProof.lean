import YangMills.Construction.ColdStepAtMirrorFrames.ACutExists
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace CutoffConstruction
variable (ρ : ℝ)
def transition (u : ℝ) : ℝ := Real.smoothTransition ((u - 5 * ρ / 8) / (ρ / 8))
def cutoffSecondDeriv (u : ℝ) : ℝ := transition ρ u * ((ρ - u) ^ 4)⁻¹
def cutoffDeriv (u : ℝ) : ℝ := ∫ s in (0 : ℝ)..u, cutoffSecondDeriv ρ s
def cutoff (u : ℝ) : ℝ := ∫ s in (0 : ℝ)..u, cutoffDeriv ρ s
variable {ρ}
theorem transition_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (transition ρ) := by
  unfold transition
  exact Real.smoothTransition.contDiff.comp (by fun_prop)
theorem cutoffSecondDeriv_contDiffOn :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoffSecondDeriv ρ) (Iio ρ) := by
  unfold cutoffSecondDeriv
  apply transition_contDiff.contDiffOn.mul
  apply ContDiffOn.inv (by fun_prop)
  intro u hu
  have : 0 < ρ - u := by
    have : u < ρ := hu
    linarith
  positivity
theorem cutoffSecondDeriv_nonneg {u : ℝ} (hu : u < ρ) : 0 ≤ cutoffSecondDeriv ρ u := by
  unfold cutoffSecondDeriv transition
  have h1 := Real.smoothTransition.nonneg ((u - 5 * ρ / 8) / (ρ / 8))
  have : 0 < ρ - u := by linarith
  positivity
theorem cutoffSecondDeriv_eq_zero (hρ : 0 < ρ) {u : ℝ} (hu : u ≤ 5 * ρ / 8) :
    cutoffSecondDeriv ρ u = 0 := by
  unfold cutoffSecondDeriv transition
  rw [Real.smoothTransition.zero_of_nonpos]
  · simp
  · apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
theorem cutoffSecondDeriv_eq_of_le (hρ : 0 < ρ) {u : ℝ} (hu : 3 * ρ / 4 ≤ u) :
    cutoffSecondDeriv ρ u = ((ρ - u) ^ 4)⁻¹ := by
  unfold cutoffSecondDeriv transition
  rw [Real.smoothTransition.one_of_one_le, one_mul]
  rw [le_div_iff₀ (by positivity)]
  linarith
theorem cutoffSecondDeriv_continuousOn : ContinuousOn (cutoffSecondDeriv ρ) (Iio ρ) :=
  cutoffSecondDeriv_contDiffOn.continuousOn
theorem cutoffSecondDeriv_intervalIntegrable {a b : ℝ} (ha : a < ρ) (hb : b < ρ) :
    IntervalIntegrable (cutoffSecondDeriv ρ) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply cutoffSecondDeriv_continuousOn.mono
  intro u hu
  rcases Set.mem_uIcc.mp hu with h | h <;> exact lt_of_le_of_lt h.2 (by assumption)
theorem hasDerivAt_cutoffDeriv (hρ : 0 < ρ) {u : ℝ} (hu : u < ρ) :
    HasDerivAt (cutoffDeriv ρ) (cutoffSecondDeriv ρ u) u := by
  apply intervalIntegral.integral_hasDerivAt_right (cutoffSecondDeriv_intervalIntegrable hρ hu)
  · exact cutoffSecondDeriv_continuousOn.stronglyMeasurableAtFilter isOpen_Iio u hu
  · exact cutoffSecondDeriv_continuousOn.continuousAt (Iio_mem_nhds hu)
theorem cutoffDeriv_continuousOn (hρ : 0 < ρ) : ContinuousOn (cutoffDeriv ρ) (Iio ρ) :=
  fun u hu => (hasDerivAt_cutoffDeriv hρ hu).continuousAt.continuousWithinAt
theorem cutoffDeriv_intervalIntegrable (hρ : 0 < ρ) {b : ℝ} (hb : b < ρ) :
    IntervalIntegrable (cutoffDeriv ρ) volume 0 b := by
  apply ContinuousOn.intervalIntegrable
  apply (cutoffDeriv_continuousOn hρ).mono
  intro u hu
  rcases Set.mem_uIcc.mp hu with h | h
  · exact lt_of_le_of_lt h.2 hb
  · exact lt_of_le_of_lt h.2 hρ
theorem hasDerivAt_cutoff (hρ : 0 < ρ) {u : ℝ} (hu : u < ρ) :
    HasDerivAt (cutoff ρ) (cutoffDeriv ρ u) u := by
  apply intervalIntegral.integral_hasDerivAt_right (cutoffDeriv_intervalIntegrable hρ hu)
  · exact (cutoffDeriv_continuousOn hρ).stronglyMeasurableAtFilter isOpen_Iio u hu
  · exact (cutoffDeriv_continuousOn hρ).continuousAt (Iio_mem_nhds hu)
theorem deriv_cutoff (hρ : 0 < ρ) {u : ℝ} (hu : u < ρ) : deriv (cutoff ρ) u = cutoffDeriv ρ u :=
  (hasDerivAt_cutoff hρ hu).deriv
theorem deriv_cutoffDeriv (hρ : 0 < ρ) {u : ℝ} (hu : u < ρ) :
    deriv (cutoffDeriv ρ) u = cutoffSecondDeriv ρ u :=
  (hasDerivAt_cutoffDeriv hρ hu).deriv
theorem cutoffDeriv_contDiffOn (hρ : 0 < ρ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoffDeriv ρ) (Iio ρ) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨fun u hu => (hasDerivAt_cutoffDeriv hρ hu).differentiableAt.differentiableWithinAt, ?_⟩
  exact cutoffSecondDeriv_contDiffOn.congr fun u hu => deriv_cutoffDeriv hρ hu
theorem cutoff_contDiffOn (hρ : 0 < ρ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoff ρ) (Iio ρ) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨fun u hu => (hasDerivAt_cutoff hρ hu).differentiableAt.differentiableWithinAt, ?_⟩
  exact (cutoffDeriv_contDiffOn hρ).congr fun u hu => deriv_cutoff hρ hu
theorem cutoffDeriv_eq_zero (hρ : 0 < ρ) {u : ℝ} (h0 : 0 ≤ u) (hu : u ≤ 5 * ρ / 8) :
    cutoffDeriv ρ u = 0 := by
  unfold cutoffDeriv
  apply intervalIntegral.integral_zero_ae
  refine Filter.Eventually.of_forall fun s hs => ?_
  rw [Set.uIoc_of_le h0] at hs
  exact cutoffSecondDeriv_eq_zero hρ (hs.2.trans hu)
theorem cutoff_eq_zero (hρ : 0 < ρ) {u : ℝ} (h0 : 0 ≤ u) (hu : u ≤ 5 * ρ / 8) :
    cutoff ρ u = 0 := by
  unfold cutoff
  apply intervalIntegral.integral_zero_ae
  refine Filter.Eventually.of_forall fun s hs => ?_
  rw [Set.uIoc_of_le h0] at hs
  exact cutoffDeriv_eq_zero hρ hs.1.le (hs.2.trans hu)
theorem cutoffDeriv_monotoneOn (hρ : 0 < ρ) : MonotoneOn (cutoffDeriv ρ) (Iio ρ) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iio ρ) (cutoffDeriv_continuousOn hρ)
  · intro u hu
    rw [interior_Iio] at hu
    exact (hasDerivAt_cutoffDeriv hρ hu).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Iio] at hu
    rw [deriv_cutoffDeriv hρ hu]
    exact cutoffSecondDeriv_nonneg hu
end CutoffConstruction
open CutoffConstruction in
theorem existsCutoff_holds : ExistsCutoff := by
  intro ρ hρ
  refine ⟨cutoff ρ, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro u h0 hu
    exact cutoff_eq_zero hρ h0 hu
  · exact (cutoff_contDiffOn hρ).mono fun u hu => hu.2
  · apply MonotoneOn.convexOn_of_deriv (convex_Ico 0 ρ)
    · exact (cutoff_contDiffOn hρ).continuousOn.mono fun u hu => hu.2
    · intro u hu
      rw [interior_Ico] at hu
      exact (hasDerivAt_cutoff hρ hu.2).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro u hu v hv huv
      rw [deriv_cutoff hρ hu.2, deriv_cutoff hρ hv.2]
      exact cutoffDeriv_monotoneOn hρ hu.2 hv.2 huv
  · refine ⟨3 * ρ / 4, by linarith, fun u h1 h2 => ?_⟩
    have e : deriv (cutoff ρ) =ᶠ[nhds u] cutoffDeriv ρ := by
      filter_upwards [Iio_mem_nhds h2] with v hv
      exact deriv_cutoff hρ hv
    rw [e.deriv_eq, deriv_cutoffDeriv hρ h2, cutoffSecondDeriv_eq_of_le hρ h1.le]
end YangMills.Construction.ColdStepAtMirrorFrames
end
