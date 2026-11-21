import YangMills.Construction.Cumulants.ExponentialMomentsOfBoundedRandomVariables
import YangMills.Construction.Cumulants.JointCumulantsAreRealSymmetricAndMultilinear
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.RealSymmetricMultilinear
open YangMills.Construction.Probability (IsBoundedRealRV)
open YangMills.Construction.Cumulants.RealVariables
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
theorem finsetCumulant_univ (μ : Measure Ω) (f : Fin n → Ω → ℝ) :
    finsetCumulant μ f Finset.univ = mixedCumulant μ f := by
  have key : ∀ (k : ℕ) (hk : k = n) (g : Fin k → Ω → ℝ), (∀ j, g j = f (Fin.cast hk j)) →
      mixedCumulant μ g = mixedCumulant μ f := by
    intro k hk g hg
    subst hk
    have hgf : g = f := funext fun j => by simpa using hg j
    rw [hgf]
  have hcard : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  refine key _ hcard _ fun j => ?_
  have hemb : (Fin.cast hcard : Fin _ → Fin n) = Finset.univ.orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl (fun _ => Finset.mem_univ _) (fun _ _ h => h)
  simp only [restrictTuple]
  rw [← hemb]
theorem momentGeneratingFunction_ofReal (μ : Measure Ω) (f : Fin n → Ω → ℝ) (s : Fin n → ℝ) :
    momentGeneratingFunction μ f (fun i => (s i : ℂ)) =
      ((realMomentGeneratingFunction μ f s : ℝ) : ℂ) := by
  unfold momentGeneratingFunction realMomentGeneratingFunction expLinearCombinationAt
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp [Complex.ofReal_exp]
theorem logMgfReal_eq_realLogMgf (μ : Measure Ω) (f : Fin n → Ω → ℝ) :
    logMgfReal μ f = realLogMomentGeneratingFunction μ f := by
  funext s
  simp only [logMgfReal, realLogMomentGeneratingFunction, momentGeneratingFunction_ofReal,
    Complex.ofReal_re]
theorem integrable_cexp_linear (μ : Measure Ω) [IsFiniteMeasure μ] (f : Fin n → Ω → ℝ)
    (hf : ∀ i, IsBoundedRealRV (f i)) (z : Coordinates.ComplexCoordinates n) :
    Integrable (fun ω => Complex.exp (∑ i, z i * (f i ω : ℂ))) μ := by
  have hmeas : Measurable fun ω => Complex.exp (∑ i, z i * (f i ω : ℂ)) := by
    refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
    exact (Complex.measurable_ofReal.comp (hf i).measurable).const_mul _
  choose B hB using fun i => (hf i).bounded
  refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp (∑ i, ‖z i‖ * B i))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)))
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (hB i ω) (norm_nonneg _)
variable (Ω) in
def boundedRVSubmodule : Submodule ℝ (Ω → ℝ) where
  carrier := {f | IsBoundedRealRV f}
  add_mem' := by
    rintro f g ⟨hf, B, hB⟩ ⟨hg, D, hD⟩
    exact ⟨hf.add hg, B + D, fun ω => (abs_add_le _ _).trans (add_le_add (hB ω) (hD ω))⟩
  zero_mem' := ⟨measurable_const, 0, fun _ => by simp⟩
  smul_mem' := by
    rintro r f ⟨hf, B, hB⟩
    refine ⟨hf.const_smul r, |r| * B, fun ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB ω) (abs_nonneg _)
theorem mixedCumulant_update_linearCombination (hReal : BoundedRealCumulantTheorem)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    [DecidableEq (Fin n)] (g : Fin n → boundedRVSubmodule Ω) (i : Fin n) (a b : ℝ)
    (u v : boundedRVSubmodule Ω) :
    mixedCumulant μ (fun j => ((Function.update g i (a • u + b • v) j : boundedRVSubmodule Ω) : Ω → ℝ)) =
      (a : ℂ) * mixedCumulant μ (fun j => ((Function.update g i u j : boundedRVSubmodule Ω) : Ω → ℝ)) +
        (b : ℂ) * mixedCumulant μ (fun j => ((Function.update g i v j : boundedRVSubmodule Ω) : Ω → ℝ)) := by
  obtain ⟨-, -, hlin, -⟩ := hReal Ω μ n
    (fun j => ((Function.update g i (a • u + b • v) j : boundedRVSubmodule Ω) : Ω → ℝ)) hn
    (fun j => (Function.update g i (a • u + b • v) j).2)
  have hupd : ∀ w : boundedRVSubmodule Ω,
      @Function.update _ _ (instDecidableEqFin n)
          (fun j => ((Function.update g i (a • u + b • v) j : boundedRVSubmodule Ω) : Ω → ℝ))
          i (w : Ω → ℝ) = fun j => ((Function.update g i w j : boundedRVSubmodule Ω) : Ω → ℝ) := by
    intro w
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  have := hlin i (u : Ω → ℝ) (v : Ω → ℝ) a b u.2 v.2 (fun ω => by simp)
  rw [hupd, hupd] at this
  exact this
theorem cumulantIsRealSymmetricMultilinear_holds (hExp : ExpMoments.HolomorphicAndNormalized)
    (hReal : BoundedRealCumulantTheorem) : CumulantIsRealSymmetricMultilinear := by
  intro Ω _ μ _ n hn
  refine ⟨fun f hf => ?_, ?_⟩
  · obtain ⟨hs, -, -, -⟩ := hReal Ω μ n f hn hf
    obtain ⟨hhol, hnorm⟩ := hExp Ω μ n hn f hf
    refine ⟨integrable_cexp_linear μ f hf, hhol, hnorm, fun z hz => ?_, ?_, ?_⟩
    · have hzre : z = fun i => (((z i).re : ℝ) : ℂ) :=
        funext fun j => Complex.ext (by simp) (by simpa using hz j)
      rw [hzre, momentGeneratingFunction_ofReal]
      exact ⟨Complex.ofReal_im _, by simpa using hs.positive _⟩
    · rw [logMgfReal_eq_realLogMgf]
      exact hs.contDiff_log
    · rw [logMgfReal_eq_realLogMgf, ← finsetCumulant_univ]
      exact hs.cumulant_eq Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  · let Φ : MultilinearMap ℝ (fun _ : Fin n => boundedRVSubmodule Ω) ℝ :=
      { toFun := fun g => (mixedCumulant μ fun i => (g i : Ω → ℝ)).re
        map_update_add' := by
          intro _ g i u v
          have := mixedCumulant_update_linearCombination hReal μ hn g i 1 1 u v
          simp only [one_smul, Complex.ofReal_one, one_mul] at this
          rw [this, Complex.add_re]
        map_update_smul' := by
          intro _ g i r u
          have := mixedCumulant_update_linearCombination hReal μ hn g i r 0 u u
          simp only [zero_smul, add_zero, Complex.ofReal_zero, zero_mul] at this
          rw [this, Complex.re_ofReal_mul, smul_eq_mul] }
    refine ⟨boundedRVSubmodule Ω, rfl, Φ, fun σ g => ?_, fun g => ?_⟩
    · obtain ⟨-, hsymm, -, -⟩ := hReal Ω μ n (fun i => (g i : Ω → ℝ)) hn (fun i => (g i).2)
      exact congrArg Complex.re (hsymm σ)
    · obtain ⟨hs, -, -, -⟩ := hReal Ω μ n (fun i => (g i : Ω → ℝ)) hn (fun i => (g i).2)
      exact Complex.ext (by simp [Φ]) (by simpa using hs.cumulant_real)
end YangMills.Construction.Cumulants.RealSymmetricMultilinear
end
