import YangMills.Construction.SummableBoundsOfTheFlow.MeanNearANumber
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Estimates
open ColdStepAtMirrorFrames
theorem expectationNearConstant_holds : ExpectationNearConstant := by
  intro ι _ ρ p Φ f D f₀ t m₂ hρ ht Fm hf hD hclose hm
  have hconst : ∀ c : ℝ, ballExpectation (cutoffFactor ρ p) Φ (fun _ => c) = c := fun c => by
    have := Fm.map_smul c (fun _ => 1)
    rw [Fm.map_one] at this
    simpa using this
  set gb : ι → BondField ι → ℝ := fun b η => D b * (t / 2) + D b / (2 * t) * ‖η b‖ ^ 2 with hgb
  have hgbN : ∀ b, IsBoundedContinuousOn ι ρ (gb b) := fun b =>
    (IsBoundedContinuousOn.const _).add ((IsBoundedContinuousOn.const _).mul (IsBoundedContinuousOn.norm_sq_apply hρ b))
  have hgN : IsBoundedContinuousOn ι ρ (fun η => ∑ b, gb b η) :=
    IsBoundedContinuousOn.sum _ gb fun b _ => hgbN b
  have hv : IsBoundedContinuousOn ι ρ (fun η => f η - f₀) := hf.sub (IsBoundedContinuousOn.const f₀)
  have hmajor : ∀ η ∈ openPolyball ι ρ, |f η - f₀| ≤ ∑ b, gb b η := fun η hη => by
    refine (hclose η hη).trans (Finset.sum_le_sum fun b _ => ?_)
    have h1 : ‖η b‖ ≤ t / 2 + ‖η b‖ ^ 2 / (2 * t) := by
      have h2 : 0 ≤ (‖η b‖ - t) ^ 2 := sq_nonneg _
      have h3 : t / 2 + ‖η b‖ ^ 2 / (2 * t) - ‖η b‖ = (‖η b‖ - t) ^ 2 / (2 * t) := by
        field_simp
        ring
      have h4 : 0 ≤ (‖η b‖ - t) ^ 2 / (2 * t) := by positivity
      linarith
    calc ‖η b‖ * D b ≤ (t / 2 + ‖η b‖ ^ 2 / (2 * t)) * D b := mul_le_mul_of_nonneg_right h1 (hD b)
      _ = gb b η := by
        simp only [hgb]
        ring
  have hmeanV : ballExpectation (cutoffFactor ρ p) Φ (fun η => f η - f₀) =
      ballExpectation (cutoffFactor ρ p) Φ f - f₀ := by
    rw [Fm.map_sub hf (IsBoundedContinuousOn.const f₀), hconst]
  have hmeanG : ballExpectation (cutoffFactor ρ p) Φ (fun η => ∑ b, gb b η) ≤ (∑ b, D b) * (t / 2 + m₂ / (2 * t)) := by
    rw [Fm.map_sum Finset.univ gb fun b _ => hgbN b, Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    have e : ballExpectation (cutoffFactor ρ p) Φ (gb b) =
        D b * (t / 2) + D b / (2 * t) * ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ 2) := by
      simp only [hgb]
      rw [Fm.map_add _ _ (IsBoundedContinuousOn.const _)
        ((IsBoundedContinuousOn.const _).mul (IsBoundedContinuousOn.norm_sq_apply hρ b)), hconst, Fm.map_smul]
    rw [e]
    have h5 : D b / (2 * t) * ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ 2) ≤ D b / (2 * t) * m₂ :=
      mul_le_mul_of_nonneg_left (hm b) (div_nonneg (hD b) (by positivity))
    have h6 : D b * (t / 2 + m₂ / (2 * t)) = D b * (t / 2) + D b / (2 * t) * m₂ := by
      field_simp
    linarith
  have hup := Fm.mono _ _ hv hgN fun η hη => (le_abs_self _).trans (hmajor η hη)
  have hlo := Fm.mono _ _ hgN.neg hv fun η hη => by
    have := neg_abs_le (f η - f₀)
    linarith [hmajor η hη]
  have hneg : ballExpectation (cutoffFactor ρ p) Φ (fun η => -∑ b, gb b η) =
      - ballExpectation (cutoffFactor ρ p) Φ (fun η => ∑ b, gb b η) := by
    have := Fm.map_smul (-1) (fun η => ∑ b, gb b η)
    simpa using this
  rw [hmeanV] at hup hlo
  rw [hneg] at hlo
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end YangMills.Construction.Estimates
end
