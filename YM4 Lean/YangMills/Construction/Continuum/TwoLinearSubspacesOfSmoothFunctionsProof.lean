import YangMills.Construction.Continuum.SupremaOfASmoothFunctionAndTheVectorSpaceOfSchwartzFunctions
import YangMills.Construction.Continuum.TwoLinearSubspacesOfSmoothFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
open SmoothMaps
namespace SmoothSubspaces
variable {n : ℕ}
theorem isFunctionSubspace_of_lincomb_mem {S : Set (Config n → ℂ)}
    (h0 : (0 : Config n → ℂ) ∈ S)
    (hc : ∀ φ ∈ S, ∀ φ' ∈ S, ∀ c c' : ℂ, c • φ + c' • φ' ∈ S) :
    IsFunctionSubspace S := by
  refine ⟨{ carrier := S, add_mem' := ?_, zero_mem' := h0, smul_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    simpa using hc a ha b hb 1 1
  · intro c x hx
    simpa using hc x hx x hx c 0
theorem weightedSup_lincomb_lt_top (k : ℕ) {a b : Config n → ℂ} (c c' : ℂ)
    (ha : (⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖a x‖)) < ⊤)
    (hb : (⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖b x‖)) < ⊤) :
    (⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖(c • a + c' • b) x‖)) < ⊤ := by
  set A := ⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖a x‖)
  set B := ⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖b x‖)
  have bound : (⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖(c • a + c' • b) x‖)) ≤
      ENNReal.ofReal ‖c‖ * A + ENNReal.ofReal ‖c'‖ * B := by
    refine iSup_le fun x => ?_
    have hw : 0 ≤ (1 + euclidNorm x) ^ k :=
      pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) k
    have hle : (1 + euclidNorm x) ^ k * ‖(c • a + c' • b) x‖ ≤
        ‖c‖ * ((1 + euclidNorm x) ^ k * ‖a x‖) +
          ‖c'‖ * ((1 + euclidNorm x) ^ k * ‖b x‖) := by
      have ht : ‖(c • a + c' • b) x‖ ≤ ‖c‖ * ‖a x‖ + ‖c'‖ * ‖b x‖ := by
        simpa [norm_smul] using norm_add_le (c • a x) (c' • b x)
      calc (1 + euclidNorm x) ^ k * ‖(c • a + c' • b) x‖
          ≤ (1 + euclidNorm x) ^ k * (‖c‖ * ‖a x‖ + ‖c'‖ * ‖b x‖) :=
            mul_le_mul_of_nonneg_left ht hw
        _ = _ := by ring
    calc ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖(c • a + c' • b) x‖)
        ≤ ENNReal.ofReal (‖c‖ * ((1 + euclidNorm x) ^ k * ‖a x‖) +
            ‖c'‖ * ((1 + euclidNorm x) ^ k * ‖b x‖)) := ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal ‖c‖ * ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖a x‖) +
            ENNReal.ofReal ‖c'‖ * ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖b x‖) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (norm_nonneg c), ENNReal.ofReal_mul (norm_nonneg c')]
      _ ≤ ENNReal.ofReal ‖c‖ * A + ENNReal.ofReal ‖c'‖ * B := by
          gcongr
          · exact le_iSup (fun x => ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖a x‖)) x
          · exact le_iSup (fun x => ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖b x‖)) x
  refine lt_of_le_of_lt bound (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb
end SmoothSubspaces
open SmoothSubspaces in
theorem smoothSubspacesStatement_of_schwartzSuprema (suprema : SchwartzSupremaStatement) :
    SmoothSubspacesStatement := by
  intro n hn
  obtain ⟨-, hlin, -⟩ := suprema n hn
  have smooth_comb : ∀ φ φ' : Config n → ℂ, ContDiff ℝ ∞ φ → ContDiff ℝ ∞ φ' → ∀ c c' : ℂ,
      ContDiff ℝ ∞ (c • φ + c' • φ') :=
    fun φ φ' h h' c c' => (hlin φ φ' h h' c c' 0 0 le_rfl).2.1
  have deriv_comb : ∀ φ φ' : Config n → ℂ, ContDiff ℝ ∞ φ → ContDiff ℝ ∞ φ' → ∀ (c c' : ℂ)
      (α : MultiIndex n), iteratedPartial α (c • φ + c' • φ') =
        c • iteratedPartial α φ + c' • iteratedPartial α φ' :=
    fun φ φ' h h' c c' => (hlin φ φ' h h' c c' 0 0 le_rfl).2.2
  have zero_smooth : ContDiff ℝ ∞ (0 : Config n → ℂ) := contDiff_const
  have deriv_zero : ∀ α : MultiIndex n, iteratedPartial α (0 : Config n → ℂ) = 0 := by
    intro α
    simpa using deriv_comb 0 0 zero_smooth zero_smooth 0 0 α
  refine ⟨?_, ⟨fun φ h => h.1, ?_⟩, ⟨fun φ h => h.1, ?_⟩⟩
  · exact isFunctionSubspace_of_lincomb_mem zero_smooth
      fun φ h φ' h' c c' => smooth_comb φ φ' h h' c c'
  · refine isFunctionSubspace_of_lincomb_mem ⟨zero_smooth, fun k α => ?_⟩
      fun φ h φ' h' c c' => ⟨smooth_comb φ φ' h.1 h'.1 c c', fun k α => ?_⟩
    · simp [deriv_zero]
    · rw [deriv_comb φ φ' h.1 h'.1 c c' α]
      exact weightedSup_lincomb_lt_top k c c' (h.2 k α) (h'.2 k α)
  · refine isFunctionSubspace_of_lincomb_mem ⟨zero_smooth, fun x _ α => ?_⟩
      fun φ h φ' h' c c' => ⟨smooth_comb φ φ' h.1 h'.1 c c', fun x hx α => ?_⟩
    · simp [deriv_zero]
    · rw [deriv_comb φ φ' h.1 h'.1 c c' α]
      simp [h.2 x hx α, h'.2 x hx α]
end YangMills.Construction.ConfigSpace
end
