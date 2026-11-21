import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.DecayOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.FloorsOfTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation
namespace YangMills.Construction.SummableBounds
variable {F : BlockFrame}
theorem interpolatedFrame_analytic {s a ρA : ℝ} {m : ℕ} {d : F.Site F.depth × Fin 4} {V : F.GaugeField F.top}
    (h₁ : IsBondAnalyticAt (stepFrame true a ρA m d) V) (h₂ : IsBondAnalyticAt (stepFrame false a ρA m d) V) :
    IsBondAnalyticAt (interpolatedFrame s a ρA m d) V := by
  intro k e X
  have e₁ : AnalyticAt ℝ (fun τ : Fin k → ℝ =>
      (1 - s) • stepFrame true a ρA m d (rotatedField (BlockAverages.bondSpread e X τ) V)) 0 :=
    (((1 - s) • ContinuousLinearMap.id ℝ imaginaryQuaternions).analyticAt _).comp (h₁ k e X)
  have e₂ : AnalyticAt ℝ (fun τ : Fin k → ℝ =>
      s • stepFrame false a ρA m d (rotatedField (BlockAverages.bondSpread e X τ) V)) 0 :=
    ((s • ContinuousLinearMap.id ℝ imaginaryQuaternions).analyticAt _).comp (h₂ k e X)
  exact e₁.add e₂
theorem norm_bondDeriv_interpolatedFrame_le {s a ρA B : ℝ} {m k : ℕ} {d : F.Site F.depth × Fin 4}
    {V : F.GaugeField F.top} {e : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h₁ : IsBondAnalyticAt (stepFrame true a ρA m d) V) (h₂ : IsBondAnalyticAt (stepFrame false a ρA m d) V)
    (b₁ : ‖bondDeriv (stepFrame true a ρA m d) V e X‖ ≤ B)
    (b₂ : ‖bondDeriv (stepFrame false a ρA m d) V e X‖ ≤ B) :
    ‖bondDeriv (interpolatedFrame s a ρA m d) V e X‖ ≤ B := by
  have c₁ : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      stepFrame true a ρA m d (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) 0 :=
    (h₁ k e X).contDiffAt
  have c₂ : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      stepFrame false a ρA m d (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) 0 :=
    (h₂ k e X).contDiffAt
  have hfun : (fun τ : Fin k → ℝ =>
      interpolatedFrame s a ρA m d (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) =
      (fun τ => (1 - s) • stepFrame true a ρA m d (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) +
        fun τ => s • stepFrame false a ρA m d (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V) := rfl
  have hE : bondDeriv (interpolatedFrame s a ρA m d) V e X =
      (1 - s) • bondDeriv (stepFrame true a ρA m d) V e X +
        s • bondDeriv (stepFrame false a ρA m d) V e X := by
    simp only [bondDeriv]
    have c₁' : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
        (1 - s) • stepFrame true a ρA m d (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) 0 :=
      c₁.const_smul (1 - s)
    have c₂' : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
        s • stepFrame false a ρA m d (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) 0 :=
      c₂.const_smul s
    rw [hfun, iteratedFDeriv_add_apply c₁' c₂']
    have e₁ := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := 1 - s) c₁
    have e₂ := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := s) c₂
    rw [e₁, e₂]
    rfl
  rw [hE]
  calc _ ≤ ‖(1 - s) • bondDeriv (stepFrame true a ρA m d) V e X‖ +
        ‖s • bondDeriv (stepFrame false a ρA m d) V e X‖ := norm_add_le _ _
    _ ≤ (1 - s) * B + s * B := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0]
        exact add_le_add (mul_le_mul_of_nonneg_left b₁ (by linarith))
          (mul_le_mul_of_nonneg_left b₂ hs0)
    _ = B := by ring
theorem interpolatedFrameDecay (hW : frameBoundsStatement)
    (hfl : Estimates.frameRadiusGrowthStatement) : interpolatedFrameDecayStatement := by
  choose! Cf₀ C₀ σ₀₀ hW' using hW
  refine ⟨fun a L c => |C₀ a L c| + 1, fun a L c => by positivity, ?_⟩
  intro a ha
  refine ⟨2 ^ 40, fun L hodd hL c hc => ?_⟩
  obtain ⟨hCf, hC, hσ₀, hold⟩ := hW' a L c ha hodd hL hc
  set Cf := Cf₀ a L c with hCfd
  set C := C₀ a L c with hCd
  set σ₀ := σ₀₀ a L c with hσ₀d
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨0, fun Ct _ => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ₀ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨σ₀, hσ₀, fun σ hσ hσ₀' p _ => ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn₀ =>
    ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  obtain ⟨y₁, hy₁, h₁⟩ := hfl (max 16 (Cf * 2 ^ 10 / σ + 1)) (c.δ₂ / 4) (by positivity) (by positivity)
  obtain ⟨y₂, hy₂, h₂⟩ := hfl (C * Cf) (3 * c.δ₂ / 16) (by positivity) (by positivity)
  obtain ⟨y₃, hy₃, h₃⟩ := hfl C (2 * c.δ₂) (by positivity) (by positivity)
  refine ⟨max y₁ (max y₂ y₃), fun y hy x t F V s hxy htor hcold hs0 hs1 d hd => ?_⟩
  have hx₁ : y₁ ≤ x := (le_max_left _ _).trans (hy.trans hxy)
  have hx₂ : y₂ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans (hy.trans hxy)
  have hx₃ : y₃ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans (hy.trans hxy)
  have hx1 : 1 ≤ x := hy₁.trans hx₁
  set m := frameRadius x with hm
  have hm16 : (16 : ℝ) ≤ m := (le_max_left _ _).trans (h₁ x hx₁).2
  have hm16' : 16 ≤ m := by exact_mod_cast hm16
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx1
  have hgap : frameDecayBound Cf c.δ₂ m ≤ 2⁻¹ ^ 10 * σ := by
    have h := (h₁ x hx₁).1
    have hA : Cf * 2 ^ 10 / σ ≤ max 16 (Cf * 2 ^ 10 / σ + 1) := by
      refine le_trans ?_ (le_max_right _ _)
      linarith
    have hE := Real.exp_pos (-(c.δ₂ / 4 * m))
    have h' : Cf * 2 ^ 10 / σ * Real.exp (-(c.δ₂ / 4 * m)) ≤ 1 := by
      refine le_trans ?_ h
      have : 0 ≤ Cf * 2 ^ 10 / σ := by positivity
      calc Cf * 2 ^ 10 / σ * Real.exp (-(c.δ₂ / 4 * m)) ≤
            max 16 (Cf * 2 ^ 10 / σ + 1) * Real.exp (-(c.δ₂ / 4 * m)) :=
            mul_le_mul_of_nonneg_right hA hE.le
        _ ≤ max 16 (Cf * 2 ^ 10 / σ + 1) * x ^ 2 * Real.exp (-(c.δ₂ / 4 * m)) := by
            refine mul_le_mul_of_nonneg_right ?_ hE.le
            exact le_mul_of_one_le_right (by positivity) hx2
    rw [frameDecayBound]
    rw [div_mul_eq_mul_div, div_le_one hσ] at h'
    nlinarith
  have hfx : C * x ^ 2 * frameDecayBound Cf c.δ₂ m ≤ Real.exp (-(2 ^ 10 * κ * m)) := by
    have h := (h₂ x hx₂).1
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hk : 2 ^ 10 * κ ≤ c.δ₂ / 16 := by
      have : κ ≤ c.δ₂ / 2 ^ 14 := hκ₀
      nlinarith
    have hsplit : Real.exp (-(c.δ₂ / 4 * m)) ≤
        Real.exp (-(3 * c.δ₂ / 16 * m)) * Real.exp (-(2 ^ 10 * κ * m)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_right hk hm0]
    rw [frameDecayBound]
    calc C * x ^ 2 * (Cf * Real.exp (-(c.δ₂ / 4 * m))) ≤
          C * x ^ 2 * (Cf * (Real.exp (-(3 * c.δ₂ / 16 * m)) * Real.exp (-(2 ^ 10 * κ * m)))) := by
          gcongr
      _ = (C * Cf * x ^ 2 * Real.exp (-(3 * c.δ₂ / 16 * m))) * Real.exp (-(2 ^ 10 * κ * m)) := by ring
      _ ≤ 1 * Real.exp (-(2 ^ 10 * κ * m)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := one_mul _
  have hex : C * x ^ 2 * Real.exp (-(2 * c.δ₂ * m)) ≤ 1 := (h₃ x hx₃).1
  have hAt := hold κ σ x m t n₀ hκ hκ₀ hσ hσ₀' hx1 hm16' (by omega) hgap hfx hex F V htor hcold
  obtain ⟨-, hsmall, -⟩ := hAt
  have h₁' := hsmall true
  have h₂' := hsmall false
  refine ⟨?_, interpolatedFrame_analytic (h₁'.analytic d hd) (h₂'.analytic d hd), fun k e X hk hX => ?_⟩
  · have hz₁ := h₁'.norm_le d hd
    have hz₂ := h₂'.norm_le d hd
    have hB : C * σ ≤ (|C| + 1) * σ := mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self C]) hσ.le
    show ‖(1 - s) • stepFrame true a c.ρA m d V + s • stepFrame false a c.ρA m d V‖ ≤ (|C| + 1) * σ
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0]
    calc _ ≤ (1 - s) * ((|C| + 1) * σ) + s * ((|C| + 1) * σ) :=
          add_le_add (mul_le_mul_of_nonneg_left (hz₁.trans hB) (by linarith))
            (mul_le_mul_of_nonneg_left (hz₂.trans hB) hs0)
      _ = _ := by ring
  exact norm_bondDeriv_interpolatedFrame_le hs0 hs1 (h₁'.analytic d hd) (h₂'.analytic d hd)
    (h₁'.deriv_bound d hd k e X hk hX) (h₂'.deriv_bound d hd k e X hk hX)
end YangMills.Construction.SummableBounds
end
