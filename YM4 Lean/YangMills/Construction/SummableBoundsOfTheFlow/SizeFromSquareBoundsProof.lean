import YangMills.Construction.ColdStepAtMirrorFrames.SizeFromSquareBounds
import YangMills.Construction.SummableBoundsOfTheFlow.SizeFromSquareBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem ballDensity_eq_zero_of_not_mem {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {η : BondField ι}
    (h : ¬ ∀ b, ‖η b‖ < ρ) : ballDensity (cutoffFactor ρ p) Φ η = 0 := by
  push_neg at h
  obtain ⟨b, hb⟩ := h
  unfold ballDensity radialWeightProd
  rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb]), zero_mul]
abbrev _root_.YangMills.SharedProofs.p11780 := @ballDensity_eq_zero_of_not_mem
private theorem ballDensity_congr_on_balls {ρ : ℝ} {p : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Ψ η = Φ η) :
    ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ := by
  funext η
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · unfold ballDensity
    rw [h η hη]
  · rw [ballDensity_eq_zero_of_not_mem hη, ballDensity_eq_zero_of_not_mem hη]
private theorem momentBound_of_ballDensity_eq {r : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ} {G G' : BondField ι → ℝ}
    {q : ℕ} {B : ℝ}
    (hd : ballDensity r Φ = ballDensity r Ψ) (hG : G = G') (h : MomentBound r Ψ G' q B) :
    MomentBound r Φ G q B := by
  subst hG
  refine ⟨by rw [hd]; exact h.1, ?_⟩
  have : ballExpectation r Φ (fun η => |G η| ^ q) = ballExpectation r Ψ (fun η => |G η| ^ q) := by
    simp only [ballExpectation, hd]
  rw [this]
  exact h.2
theorem localSizeOfQuadraticBounds (hS : ColdStepAtMirrorFrames.LocalSizeOfQuadraticBounds) :
    localSizeOfQuadraticBoundsStatement := by
  intro ι _ _ ρ x lam κ W W₀ C h H₀ d Φ p dZ w H hρ hx hlam hκ hW hW₀ h0 hp hd hL hd₂ hw hsum hC hval hgrad
  obtain ⟨Ψ, K, hag, hcv, hsl, -⟩ := hL
  have hx0 : 0 < x := by linarith
  have hdens := ballDensity_congr_on_balls (p := p) hag
  have hfd : ∀ η, fderiv ℝ (fun ζ => H ζ - H₀) η = fderiv ℝ H η := fun η => fderiv_sub_const H₀
  have hpn : ∀ b, bondGradNorm (fun ζ => H ζ - H₀) b = bondGradNorm H b := fun b => by
    funext η
    unfold bondGradNorm
    rw [hfd]
  have hCon : ContDiffOn ℝ 1 (fun ζ => H ζ - H₀) {η : BondField ι | ∀ b, ‖η b‖ < ρ} := fun η hη =>
    (ContDiffAt.sub (by exact_mod_cast hC η hη) contDiffAt_const).contDiffWithinAt
  have hb1 : IsQuadraticallyBoundedOnBalls ρ x W₀ 1 h (fun ζ => H ζ - H₀) := by
    refine ⟨fun b => h * w b, h, h0, le_rfl, fun b => mul_nonneg h0 (hw b), ?_, fun η hη => ?_⟩
    · rw [← Finset.mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left hsum h0]
    · refine (hval η hη).trans (le_of_eq ?_)
      have : ∑ b, h * w b * ‖η b‖ ^ 2 = h * ∑ b, w b * ‖η b‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [this]
      ring
  have hb2 : ∀ b, IsQuadraticallyBoundedOnBalls ρ x W₀ (Real.sqrt x * 1) (h * Real.exp (-(2 * κ * dZ b)))
      (bondGradNorm (fun ζ => H ζ - H₀) b) := by
    intro b
    rw [hpn]
    have he := (Real.exp_pos (-(2 * κ * dZ b))).le
    have he0 : 0 ≤ h * Real.exp (-(2 * κ * dZ b)) := mul_nonneg h0 he
    refine ⟨fun b' => h * Real.exp (-(2 * κ * dZ b)) * w b', h * Real.exp (-(2 * κ * dZ b)), he0, le_rfl,
      fun b' => mul_nonneg he0 (hw b'), ?_, fun η hη => ?_⟩
    · rw [← Finset.mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left hsum he0]
    · have h1 := hgrad η b hη
      have h2 : |bondGradNorm H b η| = bondGradNorm H b η := abs_of_nonneg (norm_nonneg _)
      rw [h2]
      refine h1.trans (le_of_eq ?_)
      have : ∑ b', h * Real.exp (-(2 * κ * dZ b)) * w b' * ‖η b'‖ ^ 2 =
          h * Real.exp (-(2 * κ * dZ b)) * ∑ b', w b' * ‖η b'‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b' _ => by ring
      rw [this]
      ring
  obtain ⟨-, N₀, hm⟩ := hS ι ρ x lam κ W W₀ d Ψ K p hρ hx0 hlam hκ hW hW₀ hp hd hcv hd₂ hsl
    (fun ζ => H ζ - H₀) 1 h dZ zero_le_one h0 hCon hb1 hb2
  refine ⟨fun η hη => (hC η hη).differentiableAt (by simp), H₀ + N₀, fun q hq => ?_⟩
  obtain ⟨m1, m2⟩ := hm q hq
  refine ⟨momentBound_of_ballDensity_eq hdens ?_ (by simpa using m1),
    fun b => momentBound_of_ballDensity_eq hdens rfl ?_⟩
  · funext η
    ring
  · have := m2 b
    rw [hpn] at this
    simpa using this
end Interpolation
end YangMills.Construction
end
