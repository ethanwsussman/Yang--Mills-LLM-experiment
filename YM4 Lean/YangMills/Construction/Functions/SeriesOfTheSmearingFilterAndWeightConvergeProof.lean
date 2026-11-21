import YangMills.Construction.FreeKernel.IntegerHeatKernelSolvesHeatEquation
import YangMills.Construction.Functions.PropertiesOfTheSmearingSequenceAndTheTriangleFunction
import YangMills.Construction.Functions.SmearingSeriesConvergence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmearingFilter.SeriesConvergence
open TriangleKernel
theorem norm_smearingSeq_mul_tentFourierCoeff {n : ℤ} (hIm : (tentFourierCoeff n).im = 0)
    (hRe : 0 ≤ (tentFourierCoeff n).re) :
    ‖(smearingSeq n : ℂ) * tentFourierCoeff n‖ =
      |(smearingSeq n : ℝ)| * (tentFourierCoeff n).re := by
  have hReal : tentFourierCoeff n = ((tentFourierCoeff n).re : ℂ) :=
    Complex.ext (by simp) (by simp [hIm])
  have hNorm : ‖tentFourierCoeff n‖ = (tentFourierCoeff n).re := by
    conv_lhs => rw [hReal]
    rw [Complex.norm_real, Real.norm_of_nonneg hRe]
  rw [norm_mul, Complex.norm_intCast, hNorm]
theorem norm_exp_I_mul_intCast_mul (n : ℤ) (x : ℝ) : ‖Complex.exp (Complex.I * n * x)‖ = 1 := by apply _root_.YangMills.Construction.FreeKernel.IntegerHeat.norm_exp_I_mul_int_mul <;> assumption
theorem seriesConverge_of_seqAndTentProperties (hProp : SeqAndTentProperties) : SeriesConverge := by
  obtain ⟨-, -, ⟨-, -, -, hCoeff, -, -⟩, -, ⟨hSum, -, -, -⟩⟩ := hProp
  have hNormEq : ∀ n : ℤ, ‖(smearingSeq n : ℂ) * tentFourierCoeff n‖ =
      |(smearingSeq n : ℝ)| * (tentFourierCoeff n).re :=
    fun n => norm_smearingSeq_mul_tentFourierCoeff (hCoeff n).1 (hCoeff n).2
  have hNonneg : ∀ n : ℤ, 0 ≤ |(smearingSeq n : ℝ)| * (tentFourierCoeff n).re :=
    fun n => mul_nonneg (abs_nonneg _) (hCoeff n).2
  have hFilterBound : ∀ (n : ℤ) (x : ℝ),
      ‖(smearingSeq n : ℂ) * tentFourierCoeff n * Complex.exp (Complex.I * n * x)‖ ≤
        |(smearingSeq n : ℝ)| * (tentFourierCoeff n).re := by
    intro n x
    rw [norm_mul, norm_exp_I_mul_intCast_mul, mul_one, hNormEq]
  have hShifted : Summable fun n : ℕ =>
      |(smearingSeq ((n : ℤ) + 1) : ℝ)| * (tentFourierCoeff ((n : ℤ) + 1)).re :=
    hSum.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (fun a b hab => by simpa using hab)
  have hWeightBound : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(smearingSeq ((n : ℤ) + 1) : ℂ) * tentFourierCoeff ((n : ℤ) + 1) * (s : ℂ) ^ n‖ ≤
        |(smearingSeq ((n : ℤ) + 1) : ℝ)| * (tentFourierCoeff ((n : ℤ) + 1)).re := by
    intro n s hs
    have hPow : ‖(s : ℂ) ^ n‖ ≤ 1 := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.1]
      exact pow_le_one₀ hs.1 hs.2
    rw [norm_mul, hNormEq]
    exact mul_le_of_le_one_right (hNonneg _) hPow
  have hWeightSummable : ∀ s ∈ Set.Icc (0 : ℝ) 1, Summable fun n : ℕ =>
      ‖(smearingSeq ((n : ℤ) + 1) : ℂ) * tentFourierCoeff ((n : ℤ) + 1) * (s : ℂ) ^ n‖ :=
    fun s hs => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hWeightBound n s hs) hShifted
  have hFilterSummable : ∀ x : ℝ, Summable fun n : ℤ =>
      ‖(smearingSeq n : ℂ) * tentFourierCoeff n * Complex.exp (Complex.I * n * x)‖ :=
    fun x => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hFilterBound n x) hSum
  refine ⟨⟨?_, ?_⟩, ⟨hFilterBound, hFilterSummable, ?_, ?_⟩, ⟨hWeightBound, hWeightSummable, ?_, ?_⟩⟩
  · simpa only [Real.norm_of_nonneg (hNonneg _)] using hSum
  · have hHas := Complex.ofRealCLM.hasSum hSum.hasSum
    have hTerms : (fun n : ℤ => Complex.ofRealCLM
          (|(smearingSeq n : ℝ)| * (tentFourierCoeff n).re)) =
        fun n : ℤ => ((|(smearingSeq n : ℝ)| : ℝ) : ℂ) * tentFourierCoeff n := by
      funext n
      have hReal : tentFourierCoeff n = ((tentFourierCoeff n).re : ℂ) :=
        Complex.ext (by simp) (by simp [(hCoeff n).1])
      conv_rhs => rw [hReal]
      simp
    rw [hTerms] at hHas
    exact hHas
  · intro x
    exact (hFilterSummable x).of_norm.hasSum
  · exact tendstoUniformly_tsum hSum hFilterBound
  · intro s hs
    exact (hWeightSummable s hs).of_norm.hasSum.mul_left 2
  · have hUnif := tendstoUniformlyOn_tsum (s := Set.Icc (0 : ℝ) 1)
      (f := fun (n : ℕ) (s : ℝ) => 2 *
        ((smearingSeq ((n : ℤ) + 1) : ℂ) * tentFourierCoeff ((n : ℤ) + 1) * (s : ℂ) ^ n))
      (hShifted.mul_left 2)
      (fun n s hs => by
        rw [norm_mul, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left (hWeightBound n s hs) (by norm_num))
    have hPartial : (fun (F : Finset ℕ) (s : ℝ) => ∑ n ∈ F, 2 *
          ((smearingSeq ((n : ℤ) + 1) : ℂ) * tentFourierCoeff ((n : ℤ) + 1) * (s : ℂ) ^ n)) =
        fun (F : Finset ℕ) (s : ℝ) => 2 * ∑ n ∈ F,
          (smearingSeq ((n : ℤ) + 1) : ℂ) * tentFourierCoeff ((n : ℤ) + 1) * (s : ℂ) ^ n := by
      funext F s
      rw [Finset.mul_sum]
    have hLimit : (fun s : ℝ => ∑' n : ℕ, 2 *
          ((smearingSeq ((n : ℤ) + 1) : ℂ) * tentFourierCoeff ((n : ℤ) + 1) * (s : ℂ) ^ n)) =
        weightSeries := by
      funext s
      rw [tsum_mul_left, weightSeries]
    rw [hPartial, hLimit] at hUnif
    exact hUnif
end YangMills.Construction.SmearingFilter.SeriesConvergence
