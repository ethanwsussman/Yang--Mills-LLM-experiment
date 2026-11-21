import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter
open scoped NNReal ENNReal Topology
noncomputable section
namespace YangMills.Construction.TwoPoints.LineTransforms
open YangMills.Construction.SpectralCalculus (SpectralPlane)
abbrev c1Functions : Submodule ℂ (ℝ → ℂ) := cc1In (Set.univ : Set ℝ)
def lineTransform (g : ℝ → ℂ) (q : ℝ) : ℂ :=
  lebesgueIntegral fun x : ℝ => g x * Complex.exp (Complex.I * (x : ℂ) * (q : ℂ))
def reflectConj (g : ℝ → ℂ) (x : ℝ) : ℂ := (starRingEnd ℂ) (g (-x))
def convPow (h : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => 0
  | 1 => h
  | n + 2 => convolve (convPow h (n + 1)) h
theorem convPow_one (h : ℝ → ℂ) : convPow h 1 = h := rfl
theorem convPow_succ (h : ℝ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    convPow h (n + 1) = convolve (convPow h n) h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rfl
def bumpFn (x : ℝ) : ℂ := if |x| ≤ 1 then (((15 / 16) * (1 - x ^ 2) ^ 2 : ℝ) : ℂ) else 0
def scaledBump (n : ℕ) (x₀ x : ℝ) : ℂ := (n : ℂ) * bumpFn ((n : ℝ) * (x - x₀))
abbrev UnitStrip : Type := unitInterval × ℝ
def stripSup (F : UnitStrip → ℂ) (q : ℝ) : ℝ≥0∞ := ⨆ a : unitInterval, ‖F (a, q)‖ₑ
def stripC0 : Submodule ℂ (UnitStrip → ℂ) where
  carrier := {F | Continuous F ∧
    Tendsto (stripSup F) (comap (fun q : ℝ => |q|) atTop) (𝓝 0)}
  zero_mem' := by
    refine ⟨continuous_const, ?_⟩
    have hz : stripSup (0 : UnitStrip → ℂ) = fun _ => 0 := by
      funext q
      simp [stripSup]
    rw [hz]
    exact tendsto_const_nhds
  add_mem' := by
    rintro F G ⟨hFc, hFt⟩ ⟨hGc, hGt⟩
    refine ⟨hFc.add hGc, ?_⟩
    have hs := hFt.add hGt
    rw [add_zero] at hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
      (fun _ => zero_le) fun q => ?_
    refine iSup_le fun a => (enorm_add_le _ _).trans ?_
    exact add_le_add (le_iSup (fun a : unitInterval => ‖F (a, q)‖ₑ) a)
      (le_iSup (fun a : unitInterval => ‖G (a, q)‖ₑ) a)
  smul_mem' := by
    rintro c F ⟨hFc, hFt⟩
    refine ⟨hFc.const_smul c, ?_⟩
    have hm := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) hFt (Or.inr enorm_ne_top)
    rw [mul_zero] at hm
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun _ => zero_le) fun q => ?_
    refine iSup_le fun a => ?_
    have he : ‖(c • F) (a, q)‖ₑ = ‖c‖ₑ * ‖F (a, q)‖ₑ := by
      simp [enorm_mul]
    rw [he]
    exact mul_le_mul_right (le_iSup (fun a : unitInterval => ‖F (a, q)‖ₑ) a) _
def dyadics : Set ℝ≥0 := {t | ∃ i j : ℕ, (t : ℝ) = (j : ℝ) * 2 ^ (-(i : ℤ))}
def intervalRpow (t : ℝ≥0) (a : unitInterval) : ℝ := (a : ℝ) ^ (t : ℝ)
def stripAlgebra : Submodule ℂ (UnitStrip → ℂ) :=
  Submodule.span ℂ {F | ∃ t ∈ dyadics, ∃ g ∈ c1Functions,
    F = fun p : UnitStrip => (intervalRpow t p.1 : ℂ) * lineTransform g p.2}
def spectralToStrip (p : SpectralPlane) : UnitStrip :=
  (⟨Real.exp (-(p.1 : ℝ)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr p.1.coe_nonneg)⟩, p.2)
end YangMills.Construction.TwoPoints.LineTransforms
