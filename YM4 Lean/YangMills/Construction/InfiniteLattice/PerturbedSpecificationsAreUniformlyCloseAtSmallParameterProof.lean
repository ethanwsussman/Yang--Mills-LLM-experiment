import YangMills.Construction.InfiniteLattice.PerturbedSpecificationOfAnArrayIsDefined
import YangMills.Construction.InfiniteLattice.PerturbedSpecificationsAreUniformlyCloseAtSmallParameter
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace TiltedKernelCloseness
theorem abs_sub_le_of_le_mul_of_le_mul {a b K : ℝ} (hb : 0 < b) (hK : 1 ≤ K)
    (hab : a ≤ K * b) (hba : b ≤ K * a) : |a - b| ≤ (K - 1) * b := by
  rw [abs_le]
  constructor
  · have hK0 : 0 < K := by linarith
    have h : 0 ≤ K * (a - (2 - K) * b) := by nlinarith [mul_nonneg (sq_nonneg (K - 1)) hb.le]
    have h2 : 0 ≤ a - (2 - K) * b := nonneg_of_mul_nonneg_right h hK0
    nlinarith
  · linarith
theorem norm_normalized_integral_sub_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℂ) (w v : α → ℝ) (k B : ℝ) (hk : 1 ≤ k) (hw : ∀ x, 0 < w x) (hv : ∀ x, 0 < v x)
    (hvw : ∀ x, v x ≤ k * w x) (hwv : ∀ x, w x ≤ k * v x) (hf : ∀ x, ‖f x‖ ≤ B)
    (hZw : 0 < ∫ x, w x ∂μ) (hZv : 0 < ∫ x, v x ∂μ)
    (hnw : Integrable (fun x => f x * (w x : ℂ)) μ)
    (hnv : Integrable (fun x => f x * (v x : ℂ)) μ) :
    ‖(∫ x, f x * (v x : ℂ) ∂μ) / ((∫ x, v x ∂μ : ℝ) : ℂ) -
        (∫ x, f x * (w x : ℂ) ∂μ) / ((∫ x, w x ∂μ : ℝ) : ℂ)‖ ≤ B * (k ^ 2 - 1) := by
  have hiw : Integrable w μ := by
    by_contra h
    rw [integral_undef h] at hZw
    exact lt_irrefl _ hZw
  have hiv : Integrable v μ := by
    by_contra h
    rw [integral_undef h] at hZv
    exact lt_irrefl _ hZv
  set Zw : ℝ := ∫ x, w x ∂μ with hZwd
  set Zv : ℝ := ∫ x, v x ∂μ with hZvd
  have hk0 : 0 < k := by linarith
  have hZ1 : Zv ≤ k * Zw := by
    have h := integral_mono hiv (hiw.const_mul k) hvw
    rwa [integral_const_mul] at h
  have hZ2 : Zw ≤ k * Zv := by
    have h := integral_mono hiw (hiv.const_mul k) hwv
    rwa [integral_const_mul] at h
  have key : (∫ x, f x * (v x : ℂ) ∂μ) / (Zv : ℂ) - (∫ x, f x * (w x : ℂ) ∂μ) / (Zw : ℂ) =
      ∫ x, (f x * (v x : ℂ) / (Zv : ℂ) - f x * (w x : ℂ) / (Zw : ℂ)) ∂μ := by
    rw [integral_sub (hnv.div_const _) (hnw.div_const _), integral_div, integral_div]
  have hpoint : ∀ x, ‖f x * (v x : ℂ) / (Zv : ℂ) - f x * (w x : ℂ) / (Zw : ℂ)‖ ≤
      B * ((k ^ 2 - 1) * (w x / Zw)) := by
    intro x
    have hsplit : f x * (v x : ℂ) / (Zv : ℂ) - f x * (w x : ℂ) / (Zw : ℂ) =
        f x * ((v x / Zv - w x / Zw : ℝ) : ℂ) := by
      push_cast
      ring
    have hb : 0 < w x / Zw := div_pos (hw x) hZw
    have hab : v x / Zv ≤ k ^ 2 * (w x / Zw) := by
      rw [div_le_iff₀ hZv, mul_assoc, mul_comm (w x / Zw), ← mul_assoc, ← mul_div_assoc,
        le_div_iff₀' hZw]
      nlinarith [mul_le_mul (hvw x) hZ2 hZw.le (mul_nonneg hk0.le (hw x).le)]
    have hba : w x / Zw ≤ k ^ 2 * (v x / Zv) := by
      rw [div_le_iff₀ hZw, mul_assoc, mul_comm (v x / Zv), ← mul_assoc, ← mul_div_assoc,
        le_div_iff₀' hZv]
      nlinarith [mul_le_mul (hwv x) hZ1 hZv.le (mul_nonneg hk0.le (hv x).le)]
    have hK : 1 ≤ k ^ 2 := one_le_pow₀ hk
    have habs := abs_sub_le_of_le_mul_of_le_mul hb hK hab hba
    rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hf x) habs (abs_nonneg _) ((norm_nonneg _).trans (hf x))
  have hg : Integrable (fun x => B * ((k ^ 2 - 1) * (w x / Zw))) μ :=
    ((hiw.div_const Zw).const_mul _).const_mul _
  have hbound := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpoint)
  have hint : ∫ x, B * ((k ^ 2 - 1) * (w x / Zw)) ∂μ = B * (k ^ 2 - 1) := by
    rw [integral_const_mul, integral_const_mul, integral_div, ← hZwd, div_self hZw.ne', mul_one]
  rw [key]
  rwa [hint] at hbound
end TiltedKernelCloseness
open TiltedKernelCloseness in
theorem tiltedKernelsUniformlyCloseNearZero_of_wellDefined
    (hWell : TiltedKernelOfArrayIsWellDefined) :
    TiltedKernelsUniformlyCloseNearZero := by
  intro β hβ 𝔸 W F hF
  have hobs : IsBoundedObservable F := hF.1
  obtain ⟨D₀, hD₀⟩ := ((hWell β hβ 𝔸 0).windowEnergy_mem W).1.2
  obtain ⟨D₁, hD₁⟩ := ((hWell β hβ 𝔸 1).windowEnergy_mem W).1.2
  have hb₀ : ∀ U, |𝔸.windowEnergy β 0 W U| ≤ D₀ := fun U => by
    simpa [Complex.norm_real] using hD₀ U
  have hb₁ : ∀ U, |𝔸.windowEnergy β 1 W U| ≤ D₁ := fun U => by
    simpa [Complex.norm_real] using hD₁ U
  let S : GaugeField 1 → ℝ := fun U => 𝔸.windowEnergy β 0 W U - 𝔸.windowEnergy β 1 W U
  have hE : ∀ (s : ℝ) (U : GaugeField 1),
      𝔸.windowEnergy β s W U = 𝔸.windowEnergy β 0 W U - s * S U := by
    intro s U
    simp only [S, LocalObservableArray.windowEnergy]
    ring
  let M : ℝ := D₀ + D₁
  have hS : ∀ U, |S U| ≤ M := fun U =>
    (abs_sub _ _).trans (add_le_add (hb₀ U) (hb₁ U))
  have hM : 0 ≤ M := (abs_nonneg _).trans (hS ⟨fun _ => 1, fun _ => by simp⟩)
  refine ⟨2 * M, by positivity, fun s U => ?_⟩
  have hfb : ∀ U', ‖F U'‖ ≤ observableSupNorm F := by
    obtain ⟨-, D, hD⟩ := hobs
    exact fun U' => le_ciSup (f := fun U => ‖F U‖) ⟨D, by rintro _ ⟨U, rfl⟩; exact hD U⟩ U'
  have hsS : ∀ U', |s * S U'| ≤ M * |s| := fun U' => by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hS U') (abs_nonneg _)
  have hexp : Real.exp (2 * M * |s|) = Real.exp (M * |s|) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hk : 1 ≤ Real.exp (M * |s|) := Real.one_le_exp (by positivity)
  have h := norm_normalized_integral_sub_le W.haarProd (fun V => F (W.glue one_pos V U))
    (fun V => Real.exp (-𝔸.windowEnergy β 0 W (W.glue one_pos V U)))
    (fun V => Real.exp (-𝔸.windowEnergy β s W (W.glue one_pos V U)))
    (Real.exp (M * |s|)) (observableSupNorm F) hk
    (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _)
    (fun V => by
      rw [← Real.exp_add, Real.exp_le_exp, hE s]
      linarith [(abs_le.mp (hsS (W.glue one_pos V U))).2])
    (fun V => by
      rw [← Real.exp_add, Real.exp_le_exp, hE s]
      linarith [(abs_le.mp (hsS (W.glue one_pos V U))).1])
    (fun V => hfb _)
    ((hWell β hβ 𝔸 0).windowPartition_pos W U)
    ((hWell β hβ 𝔸 s).windowPartition_pos W U)
    ((hWell β hβ 𝔸 0).integrable_weighted W F hobs U)
    ((hWell β hβ 𝔸 s).integrable_weighted W F hobs U)
  rw [hexp]
  exact h
end YangMills.Construction.InfiniteLattice
