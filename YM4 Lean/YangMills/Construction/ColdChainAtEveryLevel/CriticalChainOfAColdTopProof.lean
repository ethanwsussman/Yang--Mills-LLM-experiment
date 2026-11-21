import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPoint
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainOfAColdTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
theorem coldTopCriticalChain (hSlice : sliceCriticalPointStatement)
    (hBounds : splitCriticalPointBoundsStatement) : coldTopCriticalChainStatement := by
  intro a ha
  obtain ⟨θ, δ, Ca, hθ, hθ8, hδ, hδ8, hCa, L₁, hSlice'⟩ := hSlice a ha
  obtain ⟨L₂, hBounds'⟩ := hBounds a θ δ Ca ha hθ hθ8 hδ hδ8 hCa
  refine ⟨θ, δ, Ca, hθ, hθ8, hδ, hδ8, hCa, max L₁ L₂, fun L hL hge => ?_⟩
  obtain ⟨r, σ₁, C₁, hr, hσ₁, hC₁, hcrit⟩ := hSlice' L hL (le_of_max_le_left hge)
  obtain ⟨σ₂, C₂, hσ₂, hC₂, hloc⟩ := hBounds' L hL (le_of_max_le_right hge) r C₁ hr hC₁
  refine ⟨r, min σ₁ σ₂, max C₁ C₂, hr, lt_min hσ₁ hσ₂, lt_max_of_lt_left hC₁, ?_⟩
  intro F m S hside hamb hm hreg s V hs0 hsle hcold
  obtain ⟨U, hU⟩ := hcrit F m S hside hamb hm hreg s V hs0 (hsle.trans (min_le_left _ _)) hcold
  have hl := hloc F m S hside hamb hm hreg s V hs0 (hsle.trans (min_le_right _ _)) hcold U hU
  have hCs : C₂ * s ≤ max C₁ C₂ * s := mul_le_mul_of_nonneg_right (le_max_right _ _) hs0.le
  have hCs0 : 0 ≤ C₂ * s := by positivity
  have hpow4 : (C₂ * s) ^ 4 ≤ (max C₁ C₂ * s) ^ 4 := pow_le_pow_left₀ hCs0 hCs 4
  have hpow2 : (C₂ * s) ^ 2 ≤ (max C₁ C₂ * s) ^ 2 := pow_le_pow_left₀ hCs0 hCs 2
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL.pos
  refine ⟨U, hU.mem_slice, hU.small, hU.critical, hU.unique, ?_, hU.floor, hl.colder, ?_, ?_, ?_⟩
  · obtain ⟨Ul, Ur, hsame, hbd⟩ := hU.split
    refine ⟨Ul, Ur, hsame, fun p y₀ θ' h' => ⟨(hbd p y₀ θ' h').1, (hbd p y₀ θ' h').2.trans ?_⟩⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg s)
  · intro j p ρ hj h₁ h₂
    refine (hl.quartic j p ρ hj h₁ h₂).trans (mul_le_mul_of_nonneg_right hpow4 ?_)
    have : (0 : ℝ) < (F.blockSide : ℝ) := by rw [hside]; exact hLpos
    exact Real.rpow_nonneg (by positivity) _
  · intro p ρ h₁ h₂
    have : (0 : ℝ) < (F.blockSide : ℝ) := by rw [hside]; exact hLpos
    have hx : 0 ≤ (ρ / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) := Real.rpow_nonneg (by positivity) _
    obtain ⟨q₁, q₂⟩ := hl.curvature_and_misfits p ρ h₁ h₂
    exact ⟨q₁.trans (mul_le_mul_of_nonneg_right hpow2 hx), q₂.trans (mul_le_mul_of_nonneg_right hpow2 hx)⟩
  · intro j z hj
    obtain ⟨q₁, q₂⟩ := hl.misfits_on_cells j z hj
    rw [hside] at q₁ q₂
    have hf₁ : 0 ≤ (4 / (L : ℝ) ^ 2) ^ (F.top - 1 - j) := by positivity
    have hf₂ : 0 ≤ (4 / (L : ℝ)) ^ (F.top - 1 - j) := by positivity
    refine ⟨q₁.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCs hf₁) 4),
      q₂.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCs hf₂) 2)⟩
end YangMills.Construction.BlockAverages
end
