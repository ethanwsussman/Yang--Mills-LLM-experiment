import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
section
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
private theorem abs_gibbsMean_le {A f : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ᵐ ω ∂μ, |f ω| ≤ c) :
    |gibbsMean μ A f| ≤ c := by
  unfold gibbsMean
  by_cases hi : Integrable (fun ω => Real.exp (- A ω)) μ
  · set Z := ∫ ω, Real.exp (- A ω) ∂μ with hZ
    have hZ0 : 0 ≤ Z := integral_nonneg fun ω => (Real.exp_pos _).le
    rcases hZ0.eq_or_lt with h0 | hpos
    · rw [← h0, div_zero, abs_zero]
      exact hc
    · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      calc |∫ ω, f ω * Real.exp (- A ω) ∂μ|
          ≤ ∫ ω, |f ω * Real.exp (- A ω)| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ ω, c * Real.exp (- A ω) ∂μ := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
              (hi.const_mul c)
            filter_upwards [hf] with ω hω
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_right hω (Real.exp_pos _).le
        _ = c * Z := integral_const_mul _ _
  · rw [integral_undef hi, div_zero, abs_zero]
    exact hc
private theorem ae_abs_mul_le {f g : Ω → ℝ} {c d : ℝ} (hc : 0 ≤ c) (hf : ∀ᵐ ω ∂μ, |f ω| ≤ c)
    (hg : ∀ᵐ ω ∂μ, |g ω| ≤ d) : ∀ᵐ ω ∂μ, |f ω * g ω| ≤ c * d := by
  filter_upwards [hf, hg] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) hc
end
theorem gibbsMeanBounds_holds : GibbsMeanBounds := by
  intro Ω _ μ A f g h l c d e r hc hd he hr hf hg hh hl
  have m1 := abs_gibbsMean_le (A := A) hc hf
  have m2 := abs_gibbsMean_le (A := A) hd hg
  have m3 := abs_gibbsMean_le (A := A) he hh
  have m4 := abs_gibbsMean_le (A := A) hr hl
  have fg := ae_abs_mul_le hc hf hg
  have fh := ae_abs_mul_le hc hf hh
  have fl := ae_abs_mul_le hc hf hl
  have gh := ae_abs_mul_le hd hg hh
  have gl := ae_abs_mul_le hd hg hl
  have hl' := ae_abs_mul_le he hh hl
  have fgh := ae_abs_mul_le (by positivity) fg hh
  have fgl := ae_abs_mul_le (by positivity) fg hl
  have fhl := ae_abs_mul_le (by positivity) fh hl
  have ghl := ae_abs_mul_le (by positivity) gh hl
  have fghl := ae_abs_mul_le (by positivity) fgh hl
  have Mfg := abs_gibbsMean_le (A := A) (by positivity) fg
  have Mfh := abs_gibbsMean_le (A := A) (by positivity) fh
  have Mfl := abs_gibbsMean_le (A := A) (by positivity) fl
  have Mgh := abs_gibbsMean_le (A := A) (by positivity) gh
  have Mgl := abs_gibbsMean_le (A := A) (by positivity) gl
  have Mhl := abs_gibbsMean_le (A := A) (by positivity) hl'
  have Mfgh := abs_gibbsMean_le (A := A) (by positivity) fgh
  have Mfgl := abs_gibbsMean_le (A := A) (by positivity) fgl
  have Mfhl := abs_gibbsMean_le (A := A) (by positivity) fhl
  have Mghl := abs_gibbsMean_le (A := A) (by positivity) ghl
  have Mfghl := abs_gibbsMean_le (A := A) (by positivity) fghl
  have pr : ∀ {p q P Q : ℝ}, |p| ≤ P → |q| ≤ Q → |p * q| ≤ P * Q := fun h1 h2 => by
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  refine ⟨m1, ?_, ?_, ?_⟩
  · unfold gibbsCovariance
    obtain ⟨a1, a2⟩ := abs_le.mp Mfg
    obtain ⟨b1, b2⟩ := abs_le.mp (pr m1 m2)
    rw [abs_le]
    constructor <;> linarith
  · unfold gibbsCumulantThree
    obtain ⟨p1, p2⟩ := abs_le.mp Mfgh
    obtain ⟨a1, a2⟩ := abs_le.mp (pr Mfg m3)
    obtain ⟨b1, b2⟩ := abs_le.mp (pr Mfh m2)
    obtain ⟨c1, c2⟩ := abs_le.mp (pr Mgh m1)
    obtain ⟨d1, d2⟩ := abs_le.mp (pr (pr m1 m2) m3)
    rw [abs_le]
    constructor <;> linarith
  · unfold gibbsCumulantFour
    obtain ⟨p1, p2⟩ := abs_le.mp Mfghl
    obtain ⟨a1, a2⟩ := abs_le.mp (pr Mfgh m4)
    obtain ⟨a3, a4⟩ := abs_le.mp (pr Mfgl m3)
    obtain ⟨a5, a6⟩ := abs_le.mp (pr Mfhl m2)
    obtain ⟨a7, a8⟩ := abs_le.mp (pr Mghl m1)
    obtain ⟨b1, b2⟩ := abs_le.mp (pr Mfg Mhl)
    obtain ⟨b3, b4⟩ := abs_le.mp (pr Mfh Mgl)
    obtain ⟨b5, b6⟩ := abs_le.mp (pr Mfl Mgh)
    obtain ⟨c1, c2⟩ := abs_le.mp (pr (pr Mfg m3) m4)
    obtain ⟨c3, c4⟩ := abs_le.mp (pr (pr Mfh m2) m4)
    obtain ⟨c5, c6⟩ := abs_le.mp (pr (pr Mfl m2) m3)
    obtain ⟨c7, c8⟩ := abs_le.mp (pr (pr Mgh m1) m4)
    obtain ⟨c9, c10⟩ := abs_le.mp (pr (pr Mgl m1) m3)
    obtain ⟨c11, c12⟩ := abs_le.mp (pr (pr Mhl m1) m2)
    obtain ⟨e1, e2⟩ := abs_le.mp (pr (pr (pr m1 m2) m3) m4)
    rw [abs_le]
    constructor <;> linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
