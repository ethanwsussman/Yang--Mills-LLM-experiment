import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStepProof
import YangMills.Construction.ColdStepAtMirrorFrames.RimMeanIsAWeightedMean
import YangMills.Construction.DirichletOperator.BoundsAtOneCubeProof
import YangMills.Construction.SummableBoundsOfTheFlow.BoundedDerivativesOnASetProof
import YangMills.Construction.SummableBoundsOfTheFlow.FloorOfTheScaledExponents
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesAreTameNearATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsEven
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfTheScaledMeans
import Mathlib
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheExponentOfALawIsASumOfItsParts
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledLawsTendToTheirGaussians
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreSmoothInTheScale
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansHaveTheirBounds
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.ScaledVariables
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open scoped Topology
def ScaledMeanCurvatureLimit : Prop :=
  ForallSmoothObservables fun T _ _ _ f law _ _ V Ob _ _ _ =>
    Filter.Tendsto (iteratedDeriv 2 fun l => observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l V)
      (𝓝[>] 0) (𝓝 (2 * observableSecondOrderCoeff T.a T.ρA T.lam f law Ob V))
end YangMills.Construction.ScaledVariables
end

noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames StepDensities MeasureTheory Filter Set
open scoped Topology
namespace ScaledVariables
namespace CurvatureLimit
private def bumpFn (ρ u : ℝ) : ℝ := Real.smoothTransition ((ρ ^ 2 / 4 - u) / (3 * ρ ^ 2 / 16))
private theorem bumpFn_contDiff (ρ : ℝ) : ContDiff ℝ 4 (bumpFn ρ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
private theorem bumpFn_eq_one {ρ u : ℝ} (hρ : 0 < ρ) (h : u ≤ ρ ^ 2 / 16) : bumpFn ρ u = 1 := by
  unfold bumpFn
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]
  linarith
private theorem bumpFn_eq_zero {ρ u : ℝ} (hρ : 0 < ρ) (h : ρ ^ 2 / 4 ≤ u) : bumpFn ρ u = 0 := by
  unfold bumpFn
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · positivity
private theorem bumpFn_nonneg (ρ u : ℝ) : 0 ≤ bumpFn ρ u := Real.smoothTransition.nonneg _
private theorem bumpFn_le_one (ρ u : ℝ) : bumpFn ρ u ≤ 1 := Real.smoothTransition.le_one _
private def bumpD1 (ρ u : ℝ) : ℝ := deriv (bumpFn ρ) u
private def bumpD2 (ρ u : ℝ) : ℝ := deriv (bumpD1 ρ) u
private theorem bumpD1_contDiff (ρ : ℝ) : ContDiff ℝ 3 (bumpD1 ρ) :=
  ContDiff.deriv' (n := 3) (by rw [show ((3 : WithTop ℕ∞) + 1) = 4 by norm_num]; exact bumpFn_contDiff ρ)
private theorem bumpD2_contDiff (ρ : ℝ) : ContDiff ℝ 2 (bumpD2 ρ) :=
  ContDiff.deriv' (n := 2) (by rw [show ((2 : WithTop ℕ∞) + 1) = 3 by norm_num]; exact bumpD1_contDiff ρ)
private theorem bumpFn_hasDerivAt (ρ u : ℝ) : HasDerivAt (bumpFn ρ) (bumpD1 ρ u) u :=
  ((bumpFn_contDiff ρ).differentiable (by norm_num) u).hasDerivAt
private theorem bumpD1_hasDerivAt (ρ u : ℝ) : HasDerivAt (bumpD1 ρ) (bumpD2 ρ u) u :=
  ((bumpD1_contDiff ρ).differentiable (by norm_num) u).hasDerivAt
private theorem bumpDerivs_eq_zero_of_lt {ρ u : ℝ} (hρ : 0 < ρ) (h : u < ρ ^ 2 / 16) :
    bumpD1 ρ u = 0 ∧ bumpD2 ρ u = 0 := by
  have e₁ : bumpD1 ρ =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds h] with v hv
    have e' : bumpFn ρ =ᶠ[𝓝 v] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds hv] with w hw using bumpFn_eq_one hρ (le_of_lt hw)
    unfold bumpD1
    rw [e'.deriv_eq]
    simp
  refine ⟨e₁.eq_of_nhds, ?_⟩
  unfold bumpD2
  rw [e₁.deriv_eq]
  simp
private theorem bumpDerivs_eq_zero_of_gt {ρ u : ℝ} (hρ : 0 < ρ) (h : ρ ^ 2 / 4 < u) :
    bumpD1 ρ u = 0 ∧ bumpD2 ρ u = 0 := by
  have e₁ : bumpD1 ρ =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds h] with v hv
    have e' : bumpFn ρ =ᶠ[𝓝 v] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hv] with w hw using bumpFn_eq_zero hρ (le_of_lt hw)
    unfold bumpD1
    rw [e'.deriv_eq]
    simp
  refine ⟨e₁.eq_of_nhds, ?_⟩
  unfold bumpD2
  rw [e₁.deriv_eq]
  simp
private theorem bumpDerivs_bounded {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |bumpD1 ρ u| ≤ C ∧ |bumpD2 ρ u| ≤ C := by
  obtain ⟨C₁, h₁⟩ := (isCompact_Icc (a := ρ ^ 2 / 16) (b := ρ ^ 2 / 4)).exists_bound_of_continuousOn
    (bumpD1_contDiff ρ).continuous.continuousOn
  obtain ⟨C₂, h₂⟩ := (isCompact_Icc (a := ρ ^ 2 / 16) (b := ρ ^ 2 / 4)).exists_bound_of_continuousOn
    (bumpD2_contDiff ρ).continuous.continuousOn
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun u => ?_⟩
  have hb : 0 ≤ max (max C₁ C₂) 0 := le_max_right _ _
  by_cases hu : u ∈ Icc (ρ ^ 2 / 16) (ρ ^ 2 / 4)
  · exact ⟨(h₁ u hu).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (h₂ u hu).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · obtain ⟨a, b⟩ := bumpDerivs_eq_zero_of_lt hρ hu
      simp [a, b, hb]
    · obtain ⟨a, b⟩ := bumpDerivs_eq_zero_of_gt hρ hu
      simp [a, b, hb]
private def scaleBump (ρ Q s : ℝ) : ℝ := bumpFn ρ (s ^ 2 * Q)
private def scaleBumpD1 (ρ Q s : ℝ) : ℝ := bumpD1 ρ (s ^ 2 * Q) * (2 * s * Q)
private def scaleBumpD2 (ρ Q s : ℝ) : ℝ :=
  bumpD2 ρ (s ^ 2 * Q) * (2 * s * Q) ^ 2 + bumpD1 ρ (s ^ 2 * Q) * (2 * Q)
private theorem scaleBump_hasDerivAt (ρ Q s : ℝ) : HasDerivAt (scaleBump ρ Q) (scaleBumpD1 ρ Q s) s := by
  have h := (bumpFn_hasDerivAt ρ (s ^ 2 * Q)).comp s ((hasDerivAt_pow 2 s).mul_const Q)
  refine h.congr_deriv ?_
  simp [scaleBumpD1]
private theorem scaleBumpD1_hasDerivAt (ρ Q s : ℝ) : HasDerivAt (scaleBumpD1 ρ Q) (scaleBumpD2 ρ Q s) s := by
  have hu : HasDerivAt (fun s : ℝ => s ^ 2 * Q) (2 * s * Q) s := by
    have := (hasDerivAt_pow 2 s).mul_const Q
    simpa using this
  have h₁ : HasDerivAt (fun s : ℝ => bumpD1 ρ (s ^ 2 * Q)) (bumpD2 ρ (s ^ 2 * Q) * (2 * s * Q)) s :=
    (bumpD1_hasDerivAt ρ (s ^ 2 * Q)).comp s hu
  have h₂ : HasDerivAt (fun s : ℝ => 2 * s * Q) (2 * Q) s := by
    have := ((hasDerivAt_id s).const_mul (2 : ℝ)).mul_const Q
    simpa using this
  refine (h₁.mul h₂).congr_deriv ?_
  simp [scaleBumpD2]
  ring
private theorem scaleBump_eq_zero_of_large {ρ Q s : ℝ} (hρ : 0 < ρ) (h : ρ ^ 2 / 4 < s ^ 2 * Q) :
    scaleBump ρ Q s = 0 ∧ scaleBumpD1 ρ Q s = 0 ∧ scaleBumpD2 ρ Q s = 0 := by
  obtain ⟨a, b⟩ := bumpDerivs_eq_zero_of_gt hρ h
  refine ⟨bumpFn_eq_zero hρ h.le, ?_, ?_⟩
  · simp [scaleBumpD1, a]
  · simp [scaleBumpD2, a, b]
private theorem scaleBump_eq_one_of_small {ρ Q s : ℝ} (hρ : 0 < ρ) (h : s ^ 2 * Q < ρ ^ 2 / 16) :
    scaleBump ρ Q s = 1 ∧ scaleBumpD1 ρ Q s = 0 ∧ scaleBumpD2 ρ Q s = 0 := by
  obtain ⟨a, b⟩ := bumpDerivs_eq_zero_of_lt hρ h
  refine ⟨bumpFn_eq_one hρ h.le, ?_, ?_⟩
  · simp [scaleBumpD1, a]
  · simp [scaleBumpD2, a, b]
private def firstTerm (t t₁ g g₁ e₁ : ℝ) : ℝ := t₁ * g + t * g₁ - t * g * e₁
private def secondTerm (t t₁ t₂ g g₁ g₂ e₁ e₂ : ℝ) : ℝ :=
  t₂ * g + 2 * t₁ * g₁ + t * g₂ - 2 * (t₁ * g + t * g₁) * e₁ - t * g * e₂ + t * g * e₁ ^ 2
private theorem hasDerivAt_firstTerm {t t₁ g g₁ e e₁ : ℝ → ℝ} {s : ℝ} (ht : HasDerivAt t (t₁ s) s)
    (hg : HasDerivAt g (g₁ s) s) (he : HasDerivAt e (e₁ s) s) :
    HasDerivAt (fun u => t u * g u * Real.exp (-e u))
      (firstTerm (t s) (t₁ s) (g s) (g₁ s) (e₁ s) * Real.exp (-e s)) s := by
  refine ((ht.mul hg).mul he.neg.exp).congr_deriv ?_
  simp only [firstTerm, Pi.mul_apply, Pi.neg_apply]
  ring
private theorem hasDerivAt_secondTerm {t t₁ t₂ g g₁ g₂ e e₁ e₂ : ℝ → ℝ} {s : ℝ} (ht : HasDerivAt t (t₁ s) s)
    (ht₁ : HasDerivAt t₁ (t₂ s) s) (hg : HasDerivAt g (g₁ s) s) (hg₁ : HasDerivAt g₁ (g₂ s) s)
    (he : HasDerivAt e (e₁ s) s) (he₁ : HasDerivAt e₁ (e₂ s) s) :
    HasDerivAt (fun u => firstTerm (t u) (t₁ u) (g u) (g₁ u) (e₁ u) * Real.exp (-e u))
      (secondTerm (t s) (t₁ s) (t₂ s) (g s) (g₁ s) (g₂ s) (e₁ s) (e₂ s) * Real.exp (-e s)) s := by
  have h := ((((ht₁.mul hg).add (ht.mul hg₁)).sub ((ht.mul hg).mul he₁))).mul he.neg.exp
  refine h.congr_deriv ?_
  simp only [secondTerm, Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
  ring
private theorem abs_mul_le_mul {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.abs_mul_le_mul_of_abs_le <;> assumption
private theorem abs_firstTerm_le {t t₁ g g₁ e₁ T P R : ℝ} (h₀ : |t| ≤ T) (h₁ : |t₁| ≤ T) (h₂ : |g| ≤ P)
    (h₃ : |g₁| ≤ P) (h₄ : |e₁| ≤ R) : |firstTerm t t₁ g g₁ e₁| ≤ 3 * T * P * (1 + R) ^ 2 := by
  have hT : 0 ≤ T := (abs_nonneg _).trans h₀
  have hP : 0 ≤ P := (abs_nonneg _).trans h₂
  have hR : 0 ≤ R := (abs_nonneg _).trans h₄
  have a := abs_mul_le_mul h₁ h₂
  have b := abs_mul_le_mul h₀ h₃
  have c := abs_mul_le_mul (abs_mul_le_mul h₀ h₂) h₄
  have hTP : 0 ≤ T * P := mul_nonneg hT hP
  unfold firstTerm
  calc |t₁ * g + t * g₁ - t * g * e₁| ≤ |t₁ * g| + |t * g₁| + |t * g * e₁| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ T * P + T * P + T * P * R := by linarith
    _ ≤ 3 * T * P * (1 + R) ^ 2 := by nlinarith [mul_nonneg hTP hR, mul_nonneg hTP (mul_nonneg hR hR)]
private theorem abs_secondTerm_le {t t₁ t₂ g g₁ g₂ e₁ e₂ T P R : ℝ} (h₀ : |t| ≤ T) (h₁ : |t₁| ≤ T)
    (h₂ : |t₂| ≤ T) (h₃ : |g| ≤ P) (h₄ : |g₁| ≤ P) (h₅ : |g₂| ≤ P) (h₆ : |e₁| ≤ R) (h₇ : |e₂| ≤ R) :
    |secondTerm t t₁ t₂ g g₁ g₂ e₁ e₂| ≤ 8 * T * P * (1 + R) ^ 2 := by
  have hT : 0 ≤ T := (abs_nonneg _).trans h₀
  have hP : 0 ≤ P := (abs_nonneg _).trans h₃
  have hR : 0 ≤ R := (abs_nonneg _).trans h₆
  have hTP : 0 ≤ T * P := mul_nonneg hT hP
  have a := abs_mul_le_mul h₂ h₃
  have b := abs_mul_le_mul h₁ h₄
  have c := abs_mul_le_mul h₀ h₅
  have d := abs_mul_le_mul (abs_mul_le_mul h₁ h₃) h₆
  have e := abs_mul_le_mul (abs_mul_le_mul h₀ h₄) h₆
  have f := abs_mul_le_mul (abs_mul_le_mul h₀ h₃) h₇
  have g' := abs_mul_le_mul (abs_mul_le_mul (abs_mul_le_mul h₀ h₃) h₆) h₆
  have key : secondTerm t t₁ t₂ g g₁ g₂ e₁ e₂ = t₂ * g + 2 * (t₁ * g₁) + t * g₂ - 2 * (t₁ * g * e₁) -
      2 * (t * g₁ * e₁) - t * g * e₂ + t * g * e₁ * e₁ := by
    unfold secondTerm
    ring
  rw [key]
  have tri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => abs_sub _ _
  have tr2 : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := fun x y => abs_add_le _ _
  have two : ∀ x : ℝ, |2 * x| = 2 * |x| := fun x => by rw [abs_mul, abs_two]
  have t₁' := tr2 (t₂ * g + 2 * (t₁ * g₁) + t * g₂ - 2 * (t₁ * g * e₁) - 2 * (t * g₁ * e₁) - t * g * e₂)
    (t * g * e₁ * e₁)
  have t₂' := tri (t₂ * g + 2 * (t₁ * g₁) + t * g₂ - 2 * (t₁ * g * e₁) - 2 * (t * g₁ * e₁)) (t * g * e₂)
  have t₃ := tri (t₂ * g + 2 * (t₁ * g₁) + t * g₂ - 2 * (t₁ * g * e₁)) (2 * (t * g₁ * e₁))
  have t₄ := tri (t₂ * g + 2 * (t₁ * g₁) + t * g₂) (2 * (t₁ * g * e₁))
  have t₅ := tr2 (t₂ * g + 2 * (t₁ * g₁)) (t * g₂)
  have t₆ := tr2 (t₂ * g) (2 * (t₁ * g₁))
  rw [two] at t₃ t₄ t₆
  nlinarith [mul_nonneg hTP hR, mul_nonneg hTP (mul_nonneg hR hR)]
variable {F : BlockFrame}
private def sumSq (ζ : StepVariable (finiteCells F)) : ℝ := ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2
private theorem sumSq_nonneg (ζ : StepVariable (finiteCells F)) : 0 ≤ sumSq ζ :=
  Finset.sum_nonneg fun _ _ => by positivity
private theorem continuous_sumSq : Continuous (sumSq (F := F)) :=
  continuous_finsetSum _ fun b _ => (continuous_apply b).norm.pow 2
private theorem sq_norm_le_sumSq (ζ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) :
    ‖ζ b‖ ^ 2 ≤ sumSq ζ :=
  Finset.single_le_sum (f := fun b => ‖ζ b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
private theorem sumSq_le (ζ : StepVariable (finiteCells F)) :
    sumSq ζ ≤ (Fintype.card ↥(chordBonds (finiteCells F))) * ‖ζ‖ ^ 2 := by
  unfold sumSq
  calc _ ≤ ∑ _b : ↥(chordBonds (finiteCells F)), ‖ζ‖ ^ 2 := Finset.sum_le_sum fun b _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm ζ b) 2
    _ = _ := by simp
private theorem norm_le_of_sumSq_le {ζ : StepVariable (finiteCells F)} {R : ℝ} (hR : 0 ≤ R)
    (h : sumSq ζ ≤ R ^ 2) : ‖ζ‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).2 fun b => ?_
  exact le_of_sq_le_sq ((sq_norm_le_sumSq ζ b).trans h) hR
private theorem mul_norm_le_of_sumSq {ρ s : ℝ} {ζ : StepVariable (finiteCells F)} (hρ : 0 < ρ) (_hs : 0 ≤ s)
    (h : s ^ 2 * sumSq ζ ≤ ρ ^ 2 / 4) (b : ↥(chordBonds (finiteCells F))) : s * ‖ζ b‖ ≤ ρ / 2 := by
  have h1 : (s * ‖ζ b‖) ^ 2 ≤ (ρ / 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left (sq_norm_le_sumSq ζ b) (sq_nonneg s)
    nlinarith
  exact le_of_sq_le_sq h1 (by positivity)
private theorem hasDerivAt_iteratedDeriv {g : ℝ → ℝ} {n : ℕ} {l : ℝ} (h : ContDiffAt ℝ (n + 1 : ℕ) g l) :
    HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g l) l := by apply _root_.YangMills.Construction.UniformDerivativeBounds.hasDerivAt_iteratedDeriv_of_contDiffAt <;> assumption
private def scaleD1 (g : ℝ → StepVariable (finiteCells F) → ℝ) (s : ℝ) (ζ : StepVariable (finiteCells F)) : ℝ :=
  deriv (fun u => g u ζ) s
private def scaleD2 (g : ℝ → StepVariable (finiteCells F) → ℝ) (s : ℝ) (ζ : StepVariable (finiteCells F)) : ℝ :=
  deriv (fun u => scaleD1 g u ζ) s
private structure IsTameInScale (ρ l₀ K : ℝ) (m : ℕ) (g : ℝ → StepVariable (finiteCells F) → ℝ) : Prop where
  nonneg : 0 ≤ K
  contDiffAt : ∀ s ζ, MemScaledBalls ρ |s| ζ → ContDiffAt ℝ 3 (fun u => g u ζ) s
  bound0 : ∀ s ζ, 0 < s → s ≤ l₀ → MemScaledBalls ρ s ζ → |g s ζ| ≤ K * (1 + ‖ζ‖) ^ m
  bound1 : ∀ s ζ, 0 < s → s ≤ l₀ → MemScaledBalls ρ s ζ → |scaleD1 g s ζ| ≤ K * (1 + ‖ζ‖) ^ m
  bound2 : ∀ s ζ, 0 < s → s ≤ l₀ → MemScaledBalls ρ s ζ → |scaleD2 g s ζ| ≤ K * (1 + ‖ζ‖) ^ m
  cont0 : ∀ s, 0 < s → s ≤ l₀ → ContinuousOn (g s) {ζ | MemScaledBalls ρ s ζ}
  cont1 : ∀ s, 0 < s → s ≤ l₀ → ContinuousOn (scaleD1 g s) {ζ | MemScaledBalls ρ s ζ}
  cont2 : ∀ s, 0 < s → s ≤ l₀ → ContinuousOn (scaleD2 g s) {ζ | MemScaledBalls ρ s ζ}
private theorem IsTameInScale.hasDerivAt_d1 {ρ l₀ K : ℝ} {m : ℕ} {g : ℝ → StepVariable (finiteCells F) → ℝ}
    (h : IsTameInScale ρ l₀ K m g) {s : ℝ} {ζ : StepVariable (finiteCells F)} (hs : MemScaledBalls ρ |s| ζ) :
    HasDerivAt (fun u => g u ζ) (scaleD1 g s ζ) s :=
  ((h.contDiffAt s ζ hs).differentiableAt (by norm_num)).hasDerivAt
private theorem IsTameInScale.hasDerivAt_d2 {ρ l₀ K : ℝ} {m : ℕ} {g : ℝ → StepVariable (finiteCells F) → ℝ}
    (h : IsTameInScale ρ l₀ K m g) {s : ℝ} {ζ : StepVariable (finiteCells F)} (hs : MemScaledBalls ρ |s| ζ) :
    HasDerivAt (fun u => scaleD1 g u ζ) (scaleD2 g s ζ) s := by
  have h1 := hasDerivAt_iteratedDeriv (n := 1)
    ((h.contDiffAt s ζ hs).of_le (by norm_num) : ContDiffAt ℝ ((1 + 1 : ℕ)) _ s)
  have e : iteratedDeriv (1 + 1) (fun u => g u ζ) s = scaleD2 g s ζ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rfl
  rw [e, iteratedDeriv_one] at h1
  exact h1
private def bumped0 (ρ : ℝ) (g : ℝ → StepVariable (finiteCells F) → ℝ) (s : ℝ) (ζ : StepVariable (finiteCells F)) :
    ℝ :=
  scaleBump ρ (sumSq ζ) s * g s ζ
private def bumped1 (ρ : ℝ) (E g : ℝ → StepVariable (finiteCells F) → ℝ) (s : ℝ)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  firstTerm (scaleBump ρ (sumSq ζ) s) (scaleBumpD1 ρ (sumSq ζ) s) (g s ζ) (scaleD1 g s ζ) (scaleD1 E s ζ)
private def bumped2 (ρ : ℝ) (E g : ℝ → StepVariable (finiteCells F) → ℝ) (s : ℝ)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  secondTerm (scaleBump ρ (sumSq ζ) s) (scaleBumpD1 ρ (sumSq ζ) s) (scaleBumpD2 ρ (sumSq ζ) s) (g s ζ)
    (scaleD1 g s ζ) (scaleD2 g s ζ) (scaleD1 E s ζ) (scaleD2 E s ζ)
private theorem bumped_eq_zero {ρ s : ℝ} {E g : ℝ → StepVariable (finiteCells F) → ℝ}
    {ζ : StepVariable (finiteCells F)} (hρ : 0 < ρ) (h : ρ ^ 2 / 4 < s ^ 2 * sumSq ζ) :
    bumped0 ρ g s ζ = 0 ∧ bumped1 ρ E g s ζ = 0 ∧ bumped2 ρ E g s ζ = 0 := by
  obtain ⟨x, y, z⟩ := scaleBump_eq_zero_of_large hρ h
  simp [bumped0, bumped1, bumped2, firstTerm, secondTerm, x, y, z]
private theorem eventually_large {ρ s Q : ℝ} (h : ρ ^ 2 / 4 < s ^ 2 * Q) : ∀ᶠ u in 𝓝 s, ρ ^ 2 / 4 < u ^ 2 * Q :=
  ((continuous_pow 2).mul continuous_const).continuousAt.eventually (lt_mem_nhds h) |>.mono fun _ h => h
private theorem memScaledBalls_of_sumSq {ρ s : ℝ} {ζ : StepVariable (finiteCells F)} (hρ : 0 < ρ)
    (h : s ^ 2 * sumSq ζ ≤ ρ ^ 2 / 4) : MemScaledBalls ρ |s| ζ := fun b =>
  lt_of_le_of_lt (mul_norm_le_of_sumSq hρ (abs_nonneg s) (by rwa [sq_abs]) b) (by linarith)
private theorem hasDerivAt_bumped0 {ρ l₀ KE Kg : ℝ} {mE mg : ℕ} {E g : ℝ → StepVariable (finiteCells F) → ℝ}
    (hρ : 0 < ρ) (hE : IsTameInScale ρ l₀ KE mE E) (hg : IsTameInScale ρ l₀ Kg mg g) (s : ℝ)
    (ζ : StepVariable (finiteCells F)) :
    HasDerivAt (fun u => bumped0 ρ g u ζ * Real.exp (-E u ζ)) (bumped1 ρ E g s ζ * Real.exp (-E s ζ)) s := by
  by_cases h : s ^ 2 * sumSq ζ ≤ ρ ^ 2 / 4
  · have hb := memScaledBalls_of_sumSq hρ h
    exact hasDerivAt_firstTerm (t := scaleBump ρ (sumSq ζ)) (t₁ := scaleBumpD1 ρ (sumSq ζ))
      (g := fun u => g u ζ) (g₁ := fun u => scaleD1 g u ζ) (e := fun u => E u ζ) (e₁ := fun u => scaleD1 E u ζ)
      (scaleBump_hasDerivAt _ _ s) (hg.hasDerivAt_d1 hb) (hE.hasDerivAt_d1 hb)
  · have hlt := not_le.1 h
    rw [(bumped_eq_zero (E := E) (g := g) hρ hlt).2.1, zero_mul]
    refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_large hlt] with u hu
    rw [(bumped_eq_zero (E := E) (g := g) hρ hu).1, zero_mul]
private theorem hasDerivAt_bumped1 {ρ l₀ KE Kg : ℝ} {mE mg : ℕ} {E g : ℝ → StepVariable (finiteCells F) → ℝ}
    (hρ : 0 < ρ) (hE : IsTameInScale ρ l₀ KE mE E) (hg : IsTameInScale ρ l₀ Kg mg g) (s : ℝ)
    (ζ : StepVariable (finiteCells F)) :
    HasDerivAt (fun u => bumped1 ρ E g u ζ * Real.exp (-E u ζ)) (bumped2 ρ E g s ζ * Real.exp (-E s ζ)) s := by
  by_cases h : s ^ 2 * sumSq ζ ≤ ρ ^ 2 / 4
  · have hb := memScaledBalls_of_sumSq hρ h
    exact hasDerivAt_secondTerm (t := scaleBump ρ (sumSq ζ)) (t₁ := scaleBumpD1 ρ (sumSq ζ))
      (t₂ := scaleBumpD2 ρ (sumSq ζ)) (g := fun u => g u ζ) (g₁ := fun u => scaleD1 g u ζ)
      (g₂ := fun u => scaleD2 g u ζ) (e := fun u => E u ζ) (e₁ := fun u => scaleD1 E u ζ)
      (e₂ := fun u => scaleD2 E u ζ) (scaleBump_hasDerivAt _ _ s) (scaleBumpD1_hasDerivAt _ _ s)
      (hg.hasDerivAt_d1 hb) (hg.hasDerivAt_d2 hb) (hE.hasDerivAt_d1 hb) (hE.hasDerivAt_d2 hb)
  · have hlt := not_le.1 h
    rw [(bumped_eq_zero (E := E) (g := g) hρ hlt).2.2, zero_mul]
    refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_large hlt] with u hu
    rw [(bumped_eq_zero (E := E) (g := g) hρ hu).2.1, zero_mul]
private theorem measurable_of_continuousOn_open {f : StepVariable (finiteCells F) → ℝ}
    {U : Set (StepVariable (finiteCells F))} (hU : IsOpen U) (hf : ContinuousOn f U) (h0 : ∀ ζ, ζ ∉ U → f ζ = 0) :
    Measurable f := by
  classical
  have e : f = U.piecewise f 0 := by
    funext ζ
    by_cases h : ζ ∈ U
    · simp [h]
    · simp [h, h0 ζ h]
  rw [e]
  exact hf.measurable_piecewise continuousOn_const hU.measurableSet
private theorem isOpen_memScaledBalls (ρ s : ℝ) : IsOpen {ζ : StepVariable (finiteCells F) | MemScaledBalls ρ s ζ} := by apply _root_.YangMills.SharedProofs.p7210 <;> assumption
private theorem continuous_scaleBump (ρ s : ℝ) :
    Continuous fun ζ : StepVariable (finiteCells F) => scaleBump ρ (sumSq ζ) s :=
  (bumpFn_contDiff ρ).continuous.comp (continuous_const.mul continuous_sumSq)
private theorem continuous_scaleBumpD1 (ρ s : ℝ) :
    Continuous fun ζ : StepVariable (finiteCells F) => scaleBumpD1 ρ (sumSq ζ) s :=
  ((bumpD1_contDiff ρ).continuous.comp (continuous_const.mul continuous_sumSq)).mul
    (continuous_const.mul continuous_sumSq)
private theorem continuous_scaleBumpD2 (ρ s : ℝ) :
    Continuous fun ζ : StepVariable (finiteCells F) => scaleBumpD2 ρ (sumSq ζ) s :=
  (((bumpD2_contDiff ρ).continuous.comp (continuous_const.mul continuous_sumSq)).mul
    ((continuous_const.mul continuous_sumSq).pow 2)).add
    (((bumpD1_contDiff ρ).continuous.comp (continuous_const.mul continuous_sumSq)).mul
      (continuous_const.mul continuous_sumSq))
private theorem large_of_not_mem {ρ s : ℝ} {ζ : StepVariable (finiteCells F)} (hρ : 0 < ρ) (hs : 0 < s)
    (h : ζ ∉ {ζ : StepVariable (finiteCells F) | MemScaledBalls ρ s ζ}) : ρ ^ 2 / 4 < s ^ 2 * sumSq ζ := by
  by_contra hc
  apply h
  have := memScaledBalls_of_sumSq hρ (not_lt.1 hc)
  rwa [abs_of_pos hs] at this
private theorem measurable_bumped0 {ρ l₀ KE Kg s : ℝ} {mE mg : ℕ} {E g : ℝ → StepVariable (finiteCells F) → ℝ}
    (hρ : 0 < ρ) (hE : IsTameInScale ρ l₀ KE mE E) (hg : IsTameInScale ρ l₀ Kg mg g) (hs : 0 < s) (hs' : s ≤ l₀) :
    Measurable fun ζ => bumped0 ρ g s ζ * Real.exp (-E s ζ) := by
  refine measurable_of_continuousOn_open (isOpen_memScaledBalls ρ s) ?_ fun ζ h => ?_
  · exact ((continuous_scaleBump ρ s).continuousOn.mul (hg.cont0 s hs hs')).mul ((hE.cont0 s hs hs').neg.rexp)
  · rw [(bumped_eq_zero (E := E) (g := g) hρ (large_of_not_mem hρ hs h)).1, zero_mul]
private theorem measurable_bumped1 {ρ l₀ KE Kg s : ℝ} {mE mg : ℕ} {E g : ℝ → StepVariable (finiteCells F) → ℝ}
    (hρ : 0 < ρ) (hE : IsTameInScale ρ l₀ KE mE E) (hg : IsTameInScale ρ l₀ Kg mg g) (hs : 0 < s) (hs' : s ≤ l₀) :
    Measurable fun ζ => bumped1 ρ E g s ζ * Real.exp (-E s ζ) := by
  refine measurable_of_continuousOn_open (isOpen_memScaledBalls ρ s) ?_ fun ζ h => ?_
  · have c₀ := (continuous_scaleBump (F := F) ρ s).continuousOn (s := {ζ | MemScaledBalls ρ s ζ})
    have c₁ := (continuous_scaleBumpD1 (F := F) ρ s).continuousOn (s := {ζ | MemScaledBalls ρ s ζ})
    have g₀ := hg.cont0 s hs hs'
    have g₁ := hg.cont1 s hs hs'
    have e₁ := hE.cont1 s hs hs'
    refine ContinuousOn.mul ?_ ((hE.cont0 s hs hs').neg.rexp)
    exact ((c₁.mul g₀).add (c₀.mul g₁)).sub ((c₀.mul g₀).mul e₁)
  · rw [(bumped_eq_zero (E := E) (g := g) hρ (large_of_not_mem hρ hs h)).2.1, zero_mul]
private theorem measurable_bumped2 {ρ l₀ KE Kg s : ℝ} {mE mg : ℕ} {E g : ℝ → StepVariable (finiteCells F) → ℝ}
    (hρ : 0 < ρ) (hE : IsTameInScale ρ l₀ KE mE E) (hg : IsTameInScale ρ l₀ Kg mg g) (hs : 0 < s) (hs' : s ≤ l₀) :
    Measurable fun ζ => bumped2 ρ E g s ζ * Real.exp (-E s ζ) := by
  refine measurable_of_continuousOn_open (isOpen_memScaledBalls ρ s) ?_ fun ζ h => ?_
  · have c₀ := (continuous_scaleBump (F := F) ρ s).continuousOn (s := {ζ | MemScaledBalls ρ s ζ})
    have c₁ := (continuous_scaleBumpD1 (F := F) ρ s).continuousOn (s := {ζ | MemScaledBalls ρ s ζ})
    have c₂ := (continuous_scaleBumpD2 (F := F) ρ s).continuousOn (s := {ζ | MemScaledBalls ρ s ζ})
    have g₀ := hg.cont0 s hs hs'
    have g₁ := hg.cont1 s hs hs'
    have g₂ := hg.cont2 s hs hs'
    have e₁ := hE.cont1 s hs hs'
    have e₂ := hE.cont2 s hs hs'
    refine ContinuousOn.mul ?_ ((hE.cont0 s hs hs').neg.rexp)
    exact ((((c₂.mul g₀).add ((continuousOn_const.mul c₁).mul g₁)).add (c₀.mul g₂)).sub
      ((continuousOn_const.mul ((c₁.mul g₀).add (c₀.mul g₁))).mul e₁)).sub ((c₀.mul g₀).mul e₂) |>.add
      ((c₀.mul g₀).mul (e₁.pow 2))
  · rw [(bumped_eq_zero (E := E) (g := g) hρ (large_of_not_mem hρ hs h)).2.2, zero_mul]
private theorem abs_bumped_le {t t₁ t₂ gg g₁ g₂ e₁ e₂ ex T P PE : ℝ} (h₀ : |t| ≤ T) (h₁ : |t₁| ≤ T)
    (h₂ : |t₂| ≤ T) (h₃ : |gg| ≤ P) (h₄ : |g₁| ≤ P) (h₅ : |g₂| ≤ P) (h₆ : |e₁| ≤ PE) (h₇ : |e₂| ≤ PE)
    (hex : |ex| ≤ Real.exp PE) :
    |t * gg * ex| ≤ 8 * T * P * (1 + PE) ^ 2 * Real.exp PE ∧
      |firstTerm t t₁ gg g₁ e₁ * ex| ≤ 8 * T * P * (1 + PE) ^ 2 * Real.exp PE ∧
      |secondTerm t t₁ t₂ gg g₁ g₂ e₁ e₂ * ex| ≤ 8 * T * P * (1 + PE) ^ 2 * Real.exp PE := by
  have hT : 0 ≤ T := (abs_nonneg _).trans h₀
  have hP : 0 ≤ P := (abs_nonneg _).trans h₃
  have hR : 0 ≤ PE := (abs_nonneg _).trans h₆
  have hTP : 0 ≤ T * P := mul_nonneg hT hP
  have hE := (Real.exp_pos PE).le
  have big : 1 ≤ 8 * (1 + PE) ^ 2 := by nlinarith [sq_nonneg PE]
  refine ⟨?_, ?_, ?_⟩
  · refine (abs_mul_le_mul (abs_mul_le_mul h₀ h₃) hex).trans (mul_le_mul_of_nonneg_right ?_ hE)
    nlinarith
  · refine (abs_mul_le_mul (abs_firstTerm_le h₀ h₁ h₃ h₄ h₆) hex).trans (mul_le_mul_of_nonneg_right ?_ hE)
    have : 0 ≤ T * P * (1 + PE) ^ 2 := by positivity
    nlinarith
  · exact abs_mul_le_mul (abs_secondTerm_le h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇) hex
private def sumSqBall (ρ l : ℝ) : Set (StepVariable (finiteCells F)) := {ζ | sumSq ζ ≤ (ρ / l) ^ 2}
private theorem integrable_indicator_sumSqBall (ρ l C : ℝ) (hρ : 0 < ρ) (hl : 0 < l) :
    Integrable fun ζ : StepVariable (finiteCells F) => C * (sumSqBall ρ l).indicator (fun _ => (1 : ℝ)) ζ := by
  have hcl : IsClosed (sumSqBall (F := F) ρ l) := isClosed_le continuous_sumSq continuous_const
  have hsub : sumSqBall (F := F) ρ l ⊆ Metric.closedBall 0 (ρ / l) := fun ζ hζ => by
    rw [mem_closedBall_zero_iff]
    exact norm_le_of_sumSq_le (by positivity) hζ
  have hc : IsCompact (sumSqBall (F := F) ρ l) := (isCompact_closedBall 0 (ρ / l)).of_isClosed_subset hcl hsub
  refine Integrable.const_mul ?_ C
  exact (integrable_indicator_iff hcl.measurableSet).2 (integrableOn_const hc.measure_lt_top.ne)
private theorem bumped_dominated {ρ l₀ KE Kg C l : ℝ} {mE mg : ℕ} {E g : ℝ → StepVariable (finiteCells F) → ℝ}
    (hρ : 0 < ρ) (hE : IsTameInScale ρ l₀ KE mE E) (hg : IsTameInScale ρ l₀ Kg mg g) (hC : 0 ≤ C)
    (hb : ∀ u, |bumpD1 ρ u| ≤ C ∧ |bumpD2 ρ u| ≤ C) (hl : 0 < l) (hl₀ : 3 * l / 2 ≤ l₀) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ x ∈ Ioo (l / 2) (3 * l / 2), ∀ ζ : StepVariable (finiteCells F),
      |bumped0 ρ g x ζ * Real.exp (-E x ζ)| ≤ Cb * (sumSqBall ρ l).indicator (fun _ => (1 : ℝ)) ζ ∧
      |bumped1 ρ E g x ζ * Real.exp (-E x ζ)| ≤ Cb * (sumSqBall ρ l).indicator (fun _ => (1 : ℝ)) ζ ∧
      |bumped2 ρ E g x ζ * Real.exp (-E x ζ)| ≤ Cb * (sumSqBall ρ l).indicator (fun _ => (1 : ℝ)) ζ := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ρ / l := ⟨_, rfl⟩
  have hRp : 0 < R := by rw [hR]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = Kg * (1 + R) ^ mg := ⟨_, rfl⟩
  have hPp : 0 ≤ P := by rw [hP]; exact mul_nonneg hg.nonneg (by positivity)
  obtain ⟨PE, hPE⟩ : ∃ PE : ℝ, PE = KE * (1 + R) ^ mE := ⟨_, rfl⟩
  have hPEp : 0 ≤ PE := by rw [hPE]; exact mul_nonneg hE.nonneg (by positivity)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 + C * (3 * l * R ^ 2) + C * (3 * l * R ^ 2) ^ 2 + C * (2 * R ^ 2) := ⟨_, rfl⟩
  have hTp : 0 ≤ T := by rw [hT]; positivity
  have hT1 : 1 ≤ T := by
    have : 0 ≤ C * (3 * l * R ^ 2) + C * (3 * l * R ^ 2) ^ 2 + C * (2 * R ^ 2) := by positivity
    rw [hT]
    linarith
  refine ⟨8 * T * P * (1 + PE) ^ 2 * Real.exp PE, by positivity, fun x hx ζ => ?_⟩
  have hx0 : 0 < x := by linarith [hx.1]
  have hxl : x ≤ l₀ := by linarith [hx.2]
  by_cases h : x ^ 2 * sumSq ζ ≤ ρ ^ 2 / 4
  · have hQ₀ := sumSq_nonneg ζ
    have hQ : sumSq ζ ≤ R ^ 2 := by
      have h1 : (l / 2) ^ 2 * sumSq ζ ≤ x ^ 2 * sumSq ζ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hx.1.le 2) hQ₀
      rw [hR, div_pow, le_div_iff₀ (by positivity)]
      nlinarith
    have hz : ‖ζ‖ ≤ R := norm_le_of_sumSq_le hRp.le hQ
    have hball : MemScaledBalls ρ x ζ := by
      have := memScaledBalls_of_sumSq hρ h
      rwa [abs_of_pos hx0] at this
    have mono : ∀ m : ℕ, (1 + ‖ζ‖) ^ m ≤ (1 + R) ^ m := fun m =>
      pow_le_pow_left₀ (by positivity) (by linarith) m
    have g₀ : |g x ζ| ≤ P :=
      hP ▸ (hg.bound0 x ζ hx0 hxl hball).trans (mul_le_mul_of_nonneg_left (mono _) hg.nonneg)
    have g₁ : |scaleD1 g x ζ| ≤ P :=
      hP ▸ (hg.bound1 x ζ hx0 hxl hball).trans (mul_le_mul_of_nonneg_left (mono _) hg.nonneg)
    have g₂ : |scaleD2 g x ζ| ≤ P :=
      hP ▸ (hg.bound2 x ζ hx0 hxl hball).trans (mul_le_mul_of_nonneg_left (mono _) hg.nonneg)
    have e₀ : |E x ζ| ≤ PE :=
      hPE ▸ (hE.bound0 x ζ hx0 hxl hball).trans (mul_le_mul_of_nonneg_left (mono _) hE.nonneg)
    have e₁ : |scaleD1 E x ζ| ≤ PE :=
      hPE ▸ (hE.bound1 x ζ hx0 hxl hball).trans (mul_le_mul_of_nonneg_left (mono _) hE.nonneg)
    have e₂ : |scaleD2 E x ζ| ≤ PE :=
      hPE ▸ (hE.bound2 x ζ hx0 hxl hball).trans (mul_le_mul_of_nonneg_left (mono _) hE.nonneg)
    have hs₁ : 2 * x * sumSq ζ ≤ 3 * l * R ^ 2 := by
      have h1 : 2 * x ≤ 3 * l := by linarith [hx.2]
      exact mul_le_mul h1 hQ hQ₀ (by positivity)
    have hs₀ : 0 ≤ 2 * x * sumSq ζ := by positivity
    have t₀ : |scaleBump ρ (sumSq ζ) x| ≤ T := by
      have e : scaleBump ρ (sumSq ζ) x = bumpFn ρ (x ^ 2 * sumSq ζ) := rfl
      rw [e, abs_of_nonneg (bumpFn_nonneg _ _)]
      exact (bumpFn_le_one _ _).trans hT1
    have p₁ : |scaleBumpD1 ρ (sumSq ζ) x| ≤ C * (3 * l * R ^ 2) := by
      unfold scaleBumpD1
      rw [abs_mul, abs_of_nonneg hs₀]
      exact mul_le_mul (hb _).1 hs₁ hs₀ hC
    have p₂ : |scaleBumpD2 ρ (sumSq ζ) x| ≤ C * (3 * l * R ^ 2) ^ 2 + C * (2 * R ^ 2) := by
      unfold scaleBumpD2
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 * x * sumSq ζ) ^ 2)]
        exact mul_le_mul (hb _).2 (pow_le_pow_left₀ hs₀ hs₁ 2) (by positivity) hC
      · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * sumSq ζ)]
        exact mul_le_mul (hb _).1 (by linarith) (by positivity) hC
    have t₁ : |scaleBumpD1 ρ (sumSq ζ) x| ≤ T := by
      have : 0 ≤ C * (3 * l * R ^ 2) ^ 2 + C * (2 * R ^ 2) := by positivity
      rw [hT]
      linarith
    have t₂ : |scaleBumpD2 ρ (sumSq ζ) x| ≤ T := by
      have : 0 ≤ C * (3 * l * R ^ 2) := by positivity
      rw [hT]
      linarith
    have hexp : |Real.exp (-E x ζ)| ≤ Real.exp PE := by
      rw [Real.abs_exp]
      exact Real.exp_le_exp.2 ((neg_le_abs _).trans e₀)
    have hin : (sumSqBall ρ l).indicator (fun _ => (1 : ℝ)) ζ = 1 :=
      Set.indicator_of_mem (show ζ ∈ sumSqBall ρ l from by
        show sumSq ζ ≤ (ρ / l) ^ 2
        rw [← hR]
        exact hQ) _
    rw [hin, mul_one]
    exact abs_bumped_le t₀ t₁ t₂ g₀ g₁ g₂ e₁ e₂ hexp
  · have hlt := not_le.1 h
    obtain ⟨v₀, v₁, v₂⟩ := bumped_eq_zero (E := E) (g := g) hρ hlt
    rw [v₀, v₁, v₂]
    have hn : 0 ≤ 8 * T * P * (1 + PE) ^ 2 * Real.exp PE * (sumSqBall ρ l).indicator (fun _ => (1 : ℝ)) ζ := by
      refine mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    simpa using hn
private def bumpedIntegral0 (ρ : ℝ) (E g : ℝ → StepVariable (finiteCells F) → ℝ) (s : ℝ) : ℝ :=
  ∫ ζ, bumped0 ρ g s ζ * Real.exp (-E s ζ)
private def bumpedIntegral1 (ρ : ℝ) (E g : ℝ → StepVariable (finiteCells F) → ℝ) (s : ℝ) : ℝ :=
  ∫ ζ, bumped1 ρ E g s ζ * Real.exp (-E s ζ)
private def bumpedIntegral2 (ρ : ℝ) (E g : ℝ → StepVariable (finiteCells F) → ℝ) (s : ℝ) : ℝ :=
  ∫ ζ, bumped2 ρ E g s ζ * Real.exp (-E s ζ)
private theorem hasDerivAt_bumpedIntegral {ρ l₀ KE Kg C l : ℝ} {mE mg : ℕ}
    {E g : ℝ → StepVariable (finiteCells F) → ℝ} (hρ : 0 < ρ) (hE : IsTameInScale ρ l₀ KE mE E)
    (hg : IsTameInScale ρ l₀ Kg mg g) (hC : 0 ≤ C) (hb : ∀ u, |bumpD1 ρ u| ≤ C ∧ |bumpD2 ρ u| ≤ C) (hl : 0 < l)
    (hl₀ : 3 * l / 2 ≤ l₀) :
    HasDerivAt (bumpedIntegral0 ρ E g) (bumpedIntegral1 ρ E g l) l ∧
      HasDerivAt (bumpedIntegral1 ρ E g) (bumpedIntegral2 ρ E g l) l := by
  obtain ⟨Cb, hCb, hbd⟩ := bumped_dominated hρ hE hg hC hb hl hl₀
  have hs : Ioo (l / 2) (3 * l / 2) ∈ 𝓝 l := Ioo_mem_nhds (by linarith) (by linarith)
  have pos : ∀ x ∈ Ioo (l / 2) (3 * l / 2), 0 < x ∧ x ≤ l₀ := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hl' : l ∈ Ioo (l / 2) (3 * l / 2) := ⟨by linarith, by linarith⟩
  have bi := integrable_indicator_sumSqBall (F := F) ρ l Cb hρ hl
  constructor
  · refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun s ζ => bumped0 ρ g s ζ * Real.exp (-E s ζ))
      (F' := fun s ζ => bumped1 ρ E g s ζ * Real.exp (-E s ζ)) hs ?_ ?_ ?_ ?_ bi ?_).2
    · filter_upwards [hs] with x hx using (measurable_bumped0 hρ hE hg (pos x hx).1 (pos x hx).2).aestronglyMeasurable
    · exact bi.mono' (measurable_bumped0 hρ hE hg (pos l hl').1 (pos l hl').2).aestronglyMeasurable
        (Eventually.of_forall fun ζ => (hbd l hl' ζ).1)
    · exact (measurable_bumped1 hρ hE hg (pos l hl').1 (pos l hl').2).aestronglyMeasurable
    · exact Eventually.of_forall fun ζ x hx => (hbd x hx ζ).2.1
    · exact Eventually.of_forall fun ζ x _ => hasDerivAt_bumped0 hρ hE hg x ζ
  · refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun s ζ => bumped1 ρ E g s ζ * Real.exp (-E s ζ))
      (F' := fun s ζ => bumped2 ρ E g s ζ * Real.exp (-E s ζ)) hs ?_ ?_ ?_ ?_ bi ?_).2
    · filter_upwards [hs] with x hx using (measurable_bumped1 hρ hE hg (pos x hx).1 (pos x hx).2).aestronglyMeasurable
    · exact bi.mono' (measurable_bumped1 hρ hE hg (pos l hl').1 (pos l hl').2).aestronglyMeasurable
        (Eventually.of_forall fun ζ => (hbd l hl' ζ).2.1)
    · exact (measurable_bumped2 hρ hE hg (pos l hl').1 (pos l hl').2).aestronglyMeasurable
    · exact Eventually.of_forall fun ζ x hx => (hbd x hx ζ).2.2
    · exact Eventually.of_forall fun ζ x _ => hasDerivAt_bumped1 hρ hE hg x ζ
private def ratioMean (w H : StepVariable (finiteCells F) → ℝ) : ℝ := (∫ ζ, H ζ * w ζ) / ∫ ζ, w ζ
private structure IsConvergentPiece (ρ l₀ : ℝ) (p : ℝ → StepVariable (finiteCells F) → ℝ)
    (p₀ : StepVariable (finiteCells F) → ℝ) : Prop where
  continuousOn : ∀ l, 0 < l → l ≤ l₀ → ContinuousOn (p l) {ζ | MemScaledBalls ρ l ζ}
  bounded : ∃ (K : ℝ) (m : ℕ), 0 ≤ K ∧
    ∀ l ζ, 0 < l → l ≤ l₀ → MemScaledBalls ρ l ζ → |p l ζ| ≤ K * (1 + ‖ζ‖) ^ m
  tendsto : ∀ ζ, Tendsto (fun l => p l ζ) (𝓝[>] 0) (𝓝 (p₀ ζ))
private theorem IsConvergentPiece.mul {ρ l₀ : ℝ} {p q : ℝ → StepVariable (finiteCells F) → ℝ}
    {p₀ q₀ : StepVariable (finiteCells F) → ℝ} (hp : IsConvergentPiece ρ l₀ p p₀) (hq : IsConvergentPiece ρ l₀ q q₀) :
    IsConvergentPiece ρ l₀ (fun l ζ => p l ζ * q l ζ) fun ζ => p₀ ζ * q₀ ζ := by
  obtain ⟨K, m, hK, hb⟩ := hp.bounded
  obtain ⟨K', m', hK', hb'⟩ := hq.bounded
  refine ⟨fun l h0 h1 => (hp.continuousOn l h0 h1).mul (hq.continuousOn l h0 h1),
    ⟨K * K', m + m', by positivity, fun l ζ h0 h1 h2 => ?_⟩, fun ζ => (hp.tendsto ζ).mul (hq.tendsto ζ)⟩
  refine (abs_mul_le_mul (hb l ζ h0 h1 h2) (hb' l ζ h0 h1 h2)).trans (le_of_eq ?_)
  rw [pow_add]
  ring
private theorem IsConvergentPiece.add {ρ l₀ : ℝ} {p q : ℝ → StepVariable (finiteCells F) → ℝ}
    {p₀ q₀ : StepVariable (finiteCells F) → ℝ} (hp : IsConvergentPiece ρ l₀ p p₀) (hq : IsConvergentPiece ρ l₀ q q₀) :
    IsConvergentPiece ρ l₀ (fun l ζ => p l ζ + q l ζ) fun ζ => p₀ ζ + q₀ ζ := by
  obtain ⟨K, m, hK, hb⟩ := hp.bounded
  obtain ⟨K', m', hK', hb'⟩ := hq.bounded
  refine ⟨fun l h0 h1 => (hp.continuousOn l h0 h1).add (hq.continuousOn l h0 h1),
    ⟨K + K', m + m', by positivity, fun l ζ h0 h1 h2 => ?_⟩, fun ζ => (hp.tendsto ζ).add (hq.tendsto ζ)⟩
  have h₁ : (1 + ‖ζ‖) ^ m ≤ (1 + ‖ζ‖) ^ (m + m') :=
    pow_le_pow_right₀ (by linarith [norm_nonneg ζ]) (by omega)
  have h₂ : (1 + ‖ζ‖) ^ m' ≤ (1 + ‖ζ‖) ^ (m + m') :=
    pow_le_pow_right₀ (by linarith [norm_nonneg ζ]) (by omega)
  calc |p l ζ + q l ζ| ≤ |p l ζ| + |q l ζ| := abs_add_le _ _
    _ ≤ K * (1 + ‖ζ‖) ^ m + K' * (1 + ‖ζ‖) ^ m' := add_le_add (hb l ζ h0 h1 h2) (hb' l ζ h0 h1 h2)
    _ ≤ K * (1 + ‖ζ‖) ^ (m + m') + K' * (1 + ‖ζ‖) ^ (m + m') :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ hK) (mul_le_mul_of_nonneg_left h₂ hK')
    _ = _ := by ring
private theorem IsConvergentPiece.const_mul {ρ l₀ : ℝ} {p : ℝ → StepVariable (finiteCells F) → ℝ}
    {p₀ : StepVariable (finiteCells F) → ℝ} (c : ℝ) (hp : IsConvergentPiece ρ l₀ p p₀) :
    IsConvergentPiece ρ l₀ (fun l ζ => c * p l ζ) fun ζ => c * p₀ ζ := by
  obtain ⟨K, m, hK, hb⟩ := hp.bounded
  refine ⟨fun l h0 h1 => continuousOn_const.mul (hp.continuousOn l h0 h1),
    ⟨|c| * K, m, by positivity, fun l ζ h0 h1 h2 => ?_⟩, fun ζ => (hp.tendsto ζ).const_mul c⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb l ζ h0 h1 h2) (abs_nonneg _)
private theorem IsConvergentPiece.congr_limit {ρ l₀ : ℝ} {p : ℝ → StepVariable (finiteCells F) → ℝ}
    {p₀ q₀ : StepVariable (finiteCells F) → ℝ} (hp : IsConvergentPiece ρ l₀ p p₀) (h : ∀ ζ, p₀ ζ = q₀ ζ) :
    IsConvergentPiece ρ l₀ p q₀ := by
  have e : p₀ = q₀ := funext h
  rwa [e] at hp
private theorem piece_of_tame0 {ρ l₀ K : ℝ} {m : ℕ} {g : ℝ → StepVariable (finiteCells F) → ℝ} (hρ : 0 < ρ)
    (hg : IsTameInScale ρ l₀ K m g) : IsConvergentPiece ρ l₀ g fun ζ => g 0 ζ := by
  refine ⟨hg.cont0, ⟨K, m, hg.nonneg, hg.bound0⟩, fun ζ => ?_⟩
  have h0 : MemScaledBalls ρ |(0 : ℝ)| ζ := fun b => by simpa using hρ
  exact ((hg.contDiffAt 0 ζ h0).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
private theorem piece_of_tame1 {ρ l₀ K : ℝ} {m : ℕ} {g : ℝ → StepVariable (finiteCells F) → ℝ} (hρ : 0 < ρ)
    (hg : IsTameInScale ρ l₀ K m g) : IsConvergentPiece ρ l₀ (scaleD1 g) fun ζ => scaleD1 g 0 ζ := by
  refine ⟨hg.cont1, ⟨K, m, hg.nonneg, hg.bound1⟩, fun ζ => ?_⟩
  have h0 : MemScaledBalls ρ |(0 : ℝ)| ζ := fun b => by simpa using hρ
  have h1 := hasDerivAt_iteratedDeriv (n := 1)
    ((hg.contDiffAt 0 ζ h0).of_le (by norm_num) : ContDiffAt ℝ ((1 + 1 : ℕ)) (fun u => g u ζ) (0 : ℝ))
  rw [iteratedDeriv_one] at h1
  exact (h1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
private theorem piece_of_tame2 {ρ l₀ K : ℝ} {m : ℕ} {g : ℝ → StepVariable (finiteCells F) → ℝ} (hρ : 0 < ρ)
    (hg : IsTameInScale ρ l₀ K m g) : IsConvergentPiece ρ l₀ (scaleD2 g) fun ζ => scaleD2 g 0 ζ := by
  refine ⟨hg.cont2, ⟨K, m, hg.nonneg, hg.bound2⟩, fun ζ => ?_⟩
  have h0 : MemScaledBalls ρ |(0 : ℝ)| ζ := fun b => by simpa using hρ
  have h1 := hasDerivAt_iteratedDeriv (n := 2)
    ((hg.contDiffAt 0 ζ h0) : ContDiffAt ℝ ((2 + 1 : ℕ)) (fun u => g u ζ) (0 : ℝ))
  have e : iteratedDeriv 2 (fun u => g u ζ) = fun s => scaleD2 g s ζ := by
    funext s
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    rfl
  rw [e] at h1
  exact (h1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
private theorem eventually_small {ρ Q : ℝ} (hρ : 0 < ρ) : ∀ᶠ l : ℝ in 𝓝[>] 0, l ^ 2 * Q < ρ ^ 2 / 16 := by
  have h1 : Tendsto (fun l : ℝ => l ^ 2 * Q) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2 * Q)) :=
    (((continuous_pow 2).mul continuous_const).tendsto 0)
  have h2 : (0 : ℝ) ^ 2 * Q < ρ ^ 2 / 16 := by
    have : 0 < ρ ^ 2 / 16 := by positivity
    simpa using this
  exact (h1.eventually (gt_mem_nhds h2)).filter_mono nhdsWithin_le_nhds
private theorem piece_scaleBump0 {ρ l₀ : ℝ} (hρ : 0 < ρ) :
    IsConvergentPiece (F := F) ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l) fun _ => 1 := by
  refine ⟨fun l _ _ => (continuous_scaleBump ρ l).continuousOn, ⟨1, 0, zero_le_one, fun l ζ _ _ _ => ?_⟩,
    fun ζ => ?_⟩
  · have e : scaleBump ρ (sumSq ζ) l = bumpFn ρ (l ^ 2 * sumSq ζ) := rfl
    rw [e, abs_of_nonneg (bumpFn_nonneg _ _)]
    simpa using bumpFn_le_one _ _
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_small (Q := sumSq ζ) hρ] with l hl
    exact (scaleBump_eq_one_of_small hρ hl).1.symm
private theorem sumSq_le_pow (ζ : StepVariable (finiteCells F)) :
    sumSq ζ ≤ (Fintype.card ↥(chordBonds (finiteCells F))) * (1 + ‖ζ‖) ^ 2 := by
  refine (sumSq_le ζ).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
private theorem piece_scaleBump1 {ρ l₀ C : ℝ} (hρ : 0 < ρ) (hl₀ : l₀ ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ u, |bumpD1 ρ u| ≤ C ∧ |bumpD2 ρ u| ≤ C) :
    IsConvergentPiece (F := F) ρ l₀ (fun l ζ => scaleBumpD1 ρ (sumSq ζ) l) fun _ => 0 := by
  set n : ℝ := ((Fintype.card ↥(chordBonds (finiteCells F)) : ℕ) : ℝ) with hn
  refine ⟨fun l _ _ => (continuous_scaleBumpD1 ρ l).continuousOn,
    ⟨C * (2 * n), 2, by positivity, fun l ζ h0 h1 _ => ?_⟩, fun ζ => ?_⟩
  · unfold scaleBumpD1
    have hQ := sumSq_nonneg ζ
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * l * sumSq ζ)]
    have h3 := sumSq_le_pow ζ
    have h4 : 2 * l * sumSq ζ ≤ 2 * 1 * sumSq ζ :=
      mul_le_mul_of_nonneg_right (by linarith) hQ
    calc _ ≤ C * (2 * (n * (1 + ‖ζ‖) ^ 2)) :=
          mul_le_mul (hb _).1 (by linarith) (by positivity) hC
      _ = _ := by ring
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_small (Q := sumSq ζ) hρ] with l hl
    exact (scaleBump_eq_one_of_small hρ hl).2.1.symm
private theorem piece_scaleBump2 {ρ l₀ C : ℝ} (hρ : 0 < ρ) (hl₀ : l₀ ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ u, |bumpD1 ρ u| ≤ C ∧ |bumpD2 ρ u| ≤ C) :
    IsConvergentPiece (F := F) ρ l₀ (fun l ζ => scaleBumpD2 ρ (sumSq ζ) l) fun _ => 0 := by
  set n : ℝ := ((Fintype.card ↥(chordBonds (finiteCells F)) : ℕ) : ℝ) with hn
  have hn₀ : 0 ≤ n := by positivity
  refine ⟨fun l _ _ => (continuous_scaleBumpD2 ρ l).continuousOn,
    ⟨C * (2 * n) ^ 2 + C * (2 * n), 4, by positivity, fun l ζ h0 h1 _ => ?_⟩, fun ζ => ?_⟩
  · unfold scaleBumpD2
    have hQ := sumSq_nonneg ζ
    have h3 := sumSq_le_pow ζ
    set q : ℝ := (1 + ‖ζ‖) with hq
    have hq1 : 1 ≤ q := by rw [hq]; linarith [norm_nonneg ζ]
    have h4 : 2 * l * sumSq ζ ≤ 2 * n * q ^ 2 := by
      have : 2 * l * sumSq ζ ≤ 2 * 1 * sumSq ζ := mul_le_mul_of_nonneg_right (by linarith) hQ
      linarith
    have h5 : 0 ≤ 2 * l * sumSq ζ := by positivity
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 * l * sumSq ζ) ^ 2),
      abs_of_nonneg (by positivity : 0 ≤ 2 * sumSq ζ)]
    have h6 : (2 * l * sumSq ζ) ^ 2 ≤ (2 * n) ^ 2 * q ^ 4 := by
      calc _ ≤ (2 * n * q ^ 2) ^ 2 := pow_le_pow_left₀ h5 h4 2
        _ = _ := by ring
    have h7 : 2 * sumSq ζ ≤ 2 * n * q ^ 4 := by
      have : q ^ 2 ≤ q ^ 4 := pow_le_pow_right₀ hq1 (by norm_num)
      have h8 : n * q ^ 2 ≤ n * q ^ 4 := mul_le_mul_of_nonneg_left this hn₀
      linarith
    calc _ ≤ C * ((2 * n) ^ 2 * q ^ 4) + C * (2 * n * q ^ 4) :=
          add_le_add (mul_le_mul (hb _).2 h6 (by positivity) hC) (mul_le_mul (hb _).1 h7 (by positivity) hC)
      _ = _ := by ring
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_small (Q := sumSq ζ) hρ] with l hl
    exact (scaleBump_eq_one_of_small hρ hl).2.2.symm
private structure ScaleWeights (ρ l₀ : ℝ) (E W : ℝ → StepVariable (finiteCells F) → ℝ)
    (G : (StepVariable (finiteCells F) → ℝ) → ℝ) : Prop where
  mass_ne_zero : ∀ l, 0 < l → l ≤ l₀ → (∫ ζ, W l ζ) ≠ 0
  eq_exp : ∀ l ζ, 0 < l → l ≤ l₀ → l ^ 2 * sumSq ζ ≤ ρ ^ 2 / 4 → W l ζ = Real.exp (-E l ζ)
  eq_zero : ∀ l ζ, 0 < l → l ≤ l₀ → ¬ MemScaledBalls ρ l ζ → W l ζ = 0
  tendsto_mean : ∀ (H : ℝ → StepVariable (finiteCells F) → ℝ) (H₀ : StepVariable (finiteCells F) → ℝ) (K : ℝ)
    (m : ℕ), (∀ l, 0 < l → l ≤ l₀ → Measurable (H l)) →
    (∀ l ζ, 0 < l → l ≤ l₀ → MemScaledBalls ρ l ζ → |H l ζ| ≤ K * (1 + ‖ζ‖) ^ m) →
    (∀ ζ, Tendsto (fun l => H l ζ) (𝓝[>] 0) (𝓝 (H₀ ζ))) →
    Tendsto (fun l => ratioMean (W l) (H l)) (𝓝[>] 0) (𝓝 (G H₀))
open Classical in
private def restrictToBalls (ρ : ℝ) (p : ℝ → StepVariable (finiteCells F) → ℝ) (l : ℝ)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  if MemScaledBalls ρ l ζ then p l ζ else 0
private theorem measurable_restrictToBalls {ρ l₀ l : ℝ} {p : ℝ → StepVariable (finiteCells F) → ℝ}
    {p₀ : StepVariable (finiteCells F) → ℝ} (hp : IsConvergentPiece ρ l₀ p p₀) (h0 : 0 < l) (h1 : l ≤ l₀) :
    Measurable (restrictToBalls ρ p l) := by
  classical
  refine measurable_of_continuousOn_open (isOpen_memScaledBalls ρ l)
    ((hp.continuousOn l h0 h1).congr fun ζ hζ => if_pos hζ) fun ζ h => if_neg h
private theorem eventually_memScaledBalls {ρ : ℝ} (hρ : 0 < ρ) (ζ : StepVariable (finiteCells F)) :
    ∀ᶠ l : ℝ in 𝓝[>] 0, MemScaledBalls ρ l ζ := by
  refine (eventually_all.2 fun b => ?_)
  have h1 : Tendsto (fun l : ℝ => l * ‖ζ b‖) (𝓝 0) (𝓝 (0 * ‖ζ b‖)) :=
    (continuous_id.mul continuous_const).tendsto 0
  rw [zero_mul] at h1
  exact (h1.eventually (gt_mem_nhds hρ)).filter_mono nhdsWithin_le_nhds
private theorem tendsto_ratioMean_piece {ρ l₀ : ℝ} {E W : ℝ → StepVariable (finiteCells F) → ℝ}
    {G : (StepVariable (finiteCells F) → ℝ) → ℝ} {p : ℝ → StepVariable (finiteCells F) → ℝ}
    {p₀ : StepVariable (finiteCells F) → ℝ} (hρ : 0 < ρ) (hl₀ : 0 < l₀) (hw : ScaleWeights ρ l₀ E W G)
    (hp : IsConvergentPiece ρ l₀ p p₀) : Tendsto (fun l => ratioMean (W l) (p l)) (𝓝[>] 0) (𝓝 (G p₀)) := by
  classical
  obtain ⟨K, m, hK, hb⟩ := hp.bounded
  have h := hw.tendsto_mean (restrictToBalls ρ p) p₀ K m (fun l h0 h1 => measurable_restrictToBalls hp h0 h1)
    (fun l ζ h0 h1 h2 => by
      unfold restrictToBalls
      rw [if_pos h2]
      exact hb l ζ h0 h1 h2)
    (fun ζ => by
      refine (hp.tendsto ζ).congr' ?_
      filter_upwards [eventually_memScaledBalls hρ ζ] with l hl
      unfold restrictToBalls
      rw [if_pos hl])
  refine h.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hl₀] with l hl
  unfold ratioMean
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  by_cases hz : MemScaledBalls ρ l ζ
  · simp only [restrictToBalls, if_pos hz]
  · simp only [hw.eq_zero l ζ hl.1 hl.2 hz, mul_zero]
private theorem integrable_piece {ρ l₀ l : ℝ} {E W : ℝ → StepVariable (finiteCells F) → ℝ}
    {G : (StepVariable (finiteCells F) → ℝ) → ℝ} {p : ℝ → StepVariable (finiteCells F) → ℝ}
    {p₀ : StepVariable (finiteCells F) → ℝ} (hρ : 0 < ρ) (hw : ScaleWeights ρ l₀ E W G)
    (hp : IsConvergentPiece ρ l₀ p p₀) (h0 : 0 < l) (h1 : l ≤ l₀) : Integrable fun ζ => p l ζ * W l ζ := by
  classical
  obtain ⟨K, m, hK, hb⟩ := hp.bounded
  have hWi : Integrable (W l) := by
    by_contra hn
    exact hw.mass_ne_zero l h0 h1 (integral_undef hn)
  have hbd : ∀ ζ, ‖restrictToBalls ρ p l ζ‖ ≤ K * (1 + ρ / l) ^ m := by
    intro ζ
    unfold restrictToBalls
    by_cases hz : MemScaledBalls ρ l ζ
    · rw [if_pos hz, Real.norm_eq_abs]
      refine (hb l ζ h0 h1 hz).trans (mul_le_mul_of_nonneg_left ?_ hK)
      have hn : ‖ζ‖ ≤ ρ / l := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
        rw [le_div_iff₀ h0, mul_comm]
        exact (hz b).le
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    · rw [if_neg hz, norm_zero]
      positivity
  have h := hWi.bdd_mul (measurable_restrictToBalls hp h0 h1).aestronglyMeasurable (Eventually.of_forall hbd)
  refine h.congr (Eventually.of_forall fun ζ => ?_)
  by_cases hz : MemScaledBalls ρ l ζ
  · simp only [restrictToBalls, if_pos hz]
  · simp only [hw.eq_zero l ζ h0 h1 hz, mul_zero]
private theorem integrable_add_mul {w H H' : StepVariable (finiteCells F) → ℝ} (h : Integrable fun ζ => H ζ * w ζ)
    (h' : Integrable fun ζ => H' ζ * w ζ) : Integrable fun ζ => (H ζ + H' ζ) * w ζ :=
  (h.add h').congr (Eventually.of_forall fun ζ => by
    simp only [Pi.add_apply]
    ring)
private theorem integrable_const_mul_mul {w H : StepVariable (finiteCells F) → ℝ} (c : ℝ)
    (h : Integrable fun ζ => H ζ * w ζ) : Integrable fun ζ => (c * H ζ) * w ζ :=
  (h.const_mul c).congr (Eventually.of_forall fun ζ => by
    simp only
    ring)
private theorem ratioMean_add {w H H' : StepVariable (finiteCells F) → ℝ} (h : Integrable fun ζ => H ζ * w ζ)
    (h' : Integrable fun ζ => H' ζ * w ζ) : ratioMean w (fun ζ => H ζ + H' ζ) = ratioMean w H + ratioMean w H' := by
  unfold ratioMean
  rw [← add_div, ← integral_add h h']
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [add_mul]
private theorem ratioMean_const_mul (w H : StepVariable (finiteCells F) → ℝ) (c : ℝ) :
    ratioMean w (fun ζ => c * H ζ) = c * ratioMean w H := by
  unfold ratioMean
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [mul_assoc]
private theorem ratioMean_one {w : StepVariable (finiteCells F) → ℝ} (h : (∫ ζ, w ζ) ≠ 0) :
    ratioMean w (fun _ => 1) = 1 := by
  unfold ratioMean
  simp only [one_mul]
  exact div_self h
private theorem integral_eq_mass_mul_ratioMean {ρ l₀ l : ℝ} {E W : ℝ → StepVariable (finiteCells F) → ℝ}
    {G : (StepVariable (finiteCells F) → ℝ) → ℝ} {A : StepVariable (finiteCells F) → ℝ}
    (hw : ScaleWeights ρ l₀ E W G) (h0 : 0 < l) (h1 : l ≤ l₀)
    (hA : ∀ ζ, ρ ^ 2 / 4 < l ^ 2 * sumSq ζ → A ζ = 0) :
    (∫ ζ, A ζ * Real.exp (-E l ζ)) = (∫ ζ, W l ζ) * ratioMean (W l) A := by
  unfold ratioMean
  rw [mul_div_cancel₀ _ (hw.mass_ne_zero l h0 h1)]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  by_cases hz : l ^ 2 * sumSq ζ ≤ ρ ^ 2 / 4
  · simp only [hw.eq_exp l ζ h0 h1 hz]
  · simp only [hA ζ (not_le.1 hz), zero_mul]
private theorem tendsto_bumped_means {ρ l₀ KE Kg C : ℝ} {mE mg : ℕ} {E g W : ℝ → StepVariable (finiteCells F) → ℝ}
    {G : (StepVariable (finiteCells F) → ℝ) → ℝ} (hρ : 0 < ρ) (hl₀ : 0 < l₀) (hl₁ : l₀ ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ u, |bumpD1 ρ u| ≤ C ∧ |bumpD2 ρ u| ≤ C) (hE : IsTameInScale ρ l₀ KE mE E)
    (hg : IsTameInScale ρ l₀ Kg mg g) (hw : ScaleWeights ρ l₀ E W G) (hG₀ : G (fun _ => 0) = 0) :
    Tendsto (fun l => ratioMean (W l) (bumped0 ρ g l)) (𝓝[>] 0) (𝓝 (G fun ζ => g 0 ζ)) ∧
    Tendsto (fun l => ratioMean (W l) (bumped1 ρ E g l)) (𝓝[>] 0)
      (𝓝 (G (fun ζ => scaleD1 g 0 ζ) - G fun ζ => g 0 ζ * scaleD1 E 0 ζ)) ∧
    Tendsto (fun l => ratioMean (W l) (bumped2 ρ E g l)) (𝓝[>] 0)
      (𝓝 (2 * G (fun ζ => scaleD2 g 0 ζ / 2) - 2 * G (fun ζ => scaleD1 g 0 ζ * scaleD1 E 0 ζ) -
        2 * G (fun ζ => g 0 ζ * (scaleD2 E 0 ζ / 2)) + G fun ζ => g 0 ζ * scaleD1 E 0 ζ ^ 2)) := by
  have t₀ := piece_scaleBump0 (F := F) (l₀ := l₀) hρ
  have t₁ := piece_scaleBump1 (F := F) hρ hl₁ hC hb
  have t₂ := piece_scaleBump2 (F := F) hρ hl₁ hC hb
  have g₀ := piece_of_tame0 hρ hg
  have g₁ := piece_of_tame1 hρ hg
  have g₂ := piece_of_tame2 hρ hg
  have e₁ := piece_of_tame1 hρ hE
  have e₂ := piece_of_tame2 hρ hE
  have P₀ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * g l ζ) fun ζ => g 0 ζ :=
    (t₀.mul g₀).congr_limit fun ζ => one_mul _
  have Q₀ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBumpD1 ρ (sumSq ζ) l * g l ζ) fun _ => 0 :=
    (t₁.mul g₀).congr_limit fun ζ => zero_mul _
  have Q₁ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * scaleD1 g l ζ) fun ζ => scaleD1 g 0 ζ :=
    (t₀.mul g₁).congr_limit fun ζ => one_mul _
  have Q₂ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * g l ζ * scaleD1 E l ζ)
      fun ζ => g 0 ζ * scaleD1 E 0 ζ :=
    P₀.mul e₁
  have R₀ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBumpD2 ρ (sumSq ζ) l * g l ζ +
      2 * (scaleBumpD1 ρ (sumSq ζ) l * scaleD1 g l ζ) +
      -2 * (scaleBumpD1 ρ (sumSq ζ) l * g l ζ * scaleD1 E l ζ)) fun _ => 0 :=
    (((t₂.mul g₀).add ((t₁.mul g₁).const_mul 2)).add ((Q₀.mul e₁).const_mul (-2))).congr_limit fun ζ => by simp
  have R₁ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * ((1 / 2) * scaleD2 g l ζ))
      fun ζ => scaleD2 g 0 ζ / 2 :=
    (t₀.mul (g₂.const_mul (1 / 2))).congr_limit fun ζ => by ring
  have R₂ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * scaleD1 g l ζ * scaleD1 E l ζ)
      fun ζ => scaleD1 g 0 ζ * scaleD1 E 0 ζ :=
    Q₁.mul e₁
  have R₃ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * g l ζ * ((1 / 2) * scaleD2 E l ζ))
      fun ζ => g 0 ζ * (scaleD2 E 0 ζ / 2) := (P₀.mul (e₂.const_mul (1 / 2))).congr_limit fun ζ => by ring
  have R₄ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * g l ζ * (scaleD1 E l ζ * scaleD1 E l ζ))
      fun ζ => g 0 ζ * scaleD1 E 0 ζ ^ 2 := (P₀.mul (e₁.mul e₁)).congr_limit fun ζ => by ring
  have ev := Ioc_mem_nhdsGT hl₀
  refine ⟨tendsto_ratioMean_piece hρ hl₀ hw P₀, ?_, ?_⟩
  · have T := ((tendsto_ratioMean_piece hρ hl₀ hw Q₀).add (tendsto_ratioMean_piece hρ hl₀ hw Q₁)).sub
      (tendsto_ratioMean_piece hρ hl₀ hw Q₂)
    rw [hG₀, zero_add] at T
    refine T.congr' ?_
    filter_upwards [ev] with l hl
    have i₀ := integrable_piece hρ hw Q₀ hl.1 hl.2
    have i₁ := integrable_piece hρ hw Q₁ hl.1 hl.2
    have i₂ := integrable_piece hρ hw Q₂ hl.1 hl.2
    have e : bumped1 ρ E g l = fun ζ => (scaleBumpD1 ρ (sumSq ζ) l * g l ζ + scaleBump ρ (sumSq ζ) l * scaleD1 g l ζ) +
        (-1) * (scaleBump ρ (sumSq ζ) l * g l ζ * scaleD1 E l ζ) := by
      funext ζ
      simp only [bumped1, firstTerm]
      ring
    have i₃ := integrable_add_mul i₀ i₁
    have i₄ := integrable_const_mul_mul (-1) i₂
    rw [e, ratioMean_add i₃ i₄, ratioMean_add i₀ i₁, ratioMean_const_mul]
    ring
  · have T := (((((tendsto_ratioMean_piece hρ hl₀ hw R₀).add
      ((tendsto_ratioMean_piece hρ hl₀ hw R₁).const_mul 2))).sub
      ((tendsto_ratioMean_piece hρ hl₀ hw R₂).const_mul 2)).sub
      ((tendsto_ratioMean_piece hρ hl₀ hw R₃).const_mul 2)).add (tendsto_ratioMean_piece hρ hl₀ hw R₄)
    rw [hG₀, zero_add] at T
    refine T.congr' ?_
    filter_upwards [ev] with l hl
    have i₀ := integrable_piece hρ hw R₀ hl.1 hl.2
    have i₁ := integrable_piece hρ hw R₁ hl.1 hl.2
    have i₂ := integrable_piece hρ hw R₂ hl.1 hl.2
    have i₃ := integrable_piece hρ hw R₃ hl.1 hl.2
    have i₄ := integrable_piece hρ hw R₄ hl.1 hl.2
    set p₀ : StepVariable (finiteCells F) → ℝ := fun ζ => scaleBumpD2 ρ (sumSq ζ) l * g l ζ +
      2 * (scaleBumpD1 ρ (sumSq ζ) l * scaleD1 g l ζ) +
      -2 * (scaleBumpD1 ρ (sumSq ζ) l * g l ζ * scaleD1 E l ζ) with hp₀
    set p₁ : StepVariable (finiteCells F) → ℝ := fun ζ => scaleBump ρ (sumSq ζ) l * ((1 / 2) * scaleD2 g l ζ)
      with hp₁
    set p₂ : StepVariable (finiteCells F) → ℝ := fun ζ => scaleBump ρ (sumSq ζ) l * scaleD1 g l ζ * scaleD1 E l ζ
      with hp₂
    set p₃ : StepVariable (finiteCells F) → ℝ := fun ζ =>
      scaleBump ρ (sumSq ζ) l * g l ζ * ((1 / 2) * scaleD2 E l ζ) with hp₃
    set p₄ : StepVariable (finiteCells F) → ℝ := fun ζ =>
      scaleBump ρ (sumSq ζ) l * g l ζ * (scaleD1 E l ζ * scaleD1 E l ζ) with hp₄
    have e : bumped2 ρ E g l = fun ζ => (((p₀ ζ + 2 * p₁ ζ) + (-2) * p₂ ζ) + (-2) * p₃ ζ) + p₄ ζ := by
      funext ζ
      simp only [bumped2, secondTerm, hp₀, hp₁, hp₂, hp₃, hp₄]
      ring
    have s₁ := integrable_const_mul_mul 2 i₁
    have s₂ := integrable_const_mul_mul (-2) i₂
    have s₃ := integrable_const_mul_mul (-2) i₃
    have u₁ := integrable_add_mul i₀ s₁
    have u₂ := integrable_add_mul u₁ s₂
    have u₃ := integrable_add_mul u₂ s₃
    rw [e, ratioMean_add u₃ i₄, ratioMean_add u₂ s₃, ratioMean_add u₁ s₂, ratioMean_add i₀ s₁,
      ratioMean_const_mul, ratioMean_const_mul, ratioMean_const_mul]
    ring
private theorem abs_secondDifference_le {g g' g'' : ℝ → ℝ} {l s L ε : ℝ} (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (h1 : ∀ u ∈ Icc (l - s) (l + s), HasDerivAt g (g' u) u)
    (h2 : ∀ u ∈ Icc (l - s) (l + s), HasDerivAt g' (g'' u) u)
    (hb : ∀ u ∈ Icc (l - s) (l + s), |g'' u - L| ≤ ε) :
    |g (l + s) + g (l - s) - 2 * g l - L * s ^ 2| ≤ 2 * ε * s ^ 2 := by
  have mem₁ : ∀ u ∈ Icc (0 : ℝ) s, l + u ∈ Icc (l - s) (l + s) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have mem₂ : ∀ u ∈ Icc (0 : ℝ) s, l - u ∈ Icc (l - s) (l + s) := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  set ψ : ℝ → ℝ := fun u => g' (l + u) - g' (l - u) - 2 * L * u with hψ
  set φ : ℝ → ℝ := fun u => g (l + u) + g (l - u) - 2 * g l - L * u ^ 2 with hφ
  have dψ : ∀ u ∈ Icc (0 : ℝ) s, HasDerivAt ψ (g'' (l + u) + g'' (l - u) - 2 * L) u := by
    intro u hu
    have a := (h2 _ (mem₁ u hu)).comp_const_add l u
    have b := (h2 _ (mem₂ u hu)).comp_const_sub l u
    have c := (hasDerivAt_id u).const_mul (2 * L)
    exact ((a.sub b).sub c).congr_deriv (by simp)
  have dφ : ∀ u ∈ Icc (0 : ℝ) s, HasDerivAt φ (ψ u) u := by
    intro u hu
    have a := (h1 _ (mem₁ u hu)).comp_const_add l u
    have b := (h1 _ (mem₂ u hu)).comp_const_sub l u
    have c := (hasDerivAt_pow 2 u).const_mul L
    refine (((a.add b).sub_const (2 * g l)).sub c).congr_deriv ?_
    simp only [hψ]
    simp
    ring
  have bψ : ∀ u ∈ Icc (0 : ℝ) s, |ψ u| ≤ 2 * ε * s := by
    intro u hu
    have hsub := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := ψ)
      (f' := fun u => g'' (l + u) + g'' (l - u) - 2 * L) (C := 2 * ε) (s := Icc 0 s) (x := 0) (y := u)
      (fun x hx => (dψ x hx).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        have a := hb _ (mem₁ x hx)
        have b := hb _ (mem₂ x hx)
        rw [abs_le] at a b ⊢
        constructor <;> linarith [a.1, a.2, b.1, b.2])
      (convex_Icc 0 s) (left_mem_Icc.2 hs) hu
    have h0 : ψ 0 = 0 := by simp [hψ]
    rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu.1] at hsub
    exact hsub.trans (mul_le_mul_of_nonneg_left hu.2 (by positivity))
  have hsub := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ) (f' := ψ) (C := 2 * ε * s)
    (s := Icc 0 s) (x := 0) (y := s) (fun x hx => (dφ x hx).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact bψ x hx) (convex_Icc 0 s) (left_mem_Icc.2 hs)
    (right_mem_Icc.2 hs)
  have h0 : φ 0 = 0 := by simp [hφ]; ring
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs] at hsub
  calc _ ≤ 2 * ε * s * s := hsub
    _ = _ := by ring
abbrev _root_.YangMills.SharedProofs.p15625 := @abs_secondDifference_le
private theorem abs_bumpTail_le {ρ Q l : ℝ} (hρ : 0 < ρ) (_hQ : 0 ≤ Q) (h0 : 0 < l) (h1 : l ≤ 1) :
    |(1 - scaleBump ρ Q l) / l ^ 3| ≤ (16 / ρ ^ 2) ^ 2 * Q ^ 2 := by
  have hp : 0 < l ^ 3 := by positivity
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  by_cases h : l ^ 2 * Q ≤ ρ ^ 2 / 16
  · have e : scaleBump ρ Q l = 1 := bumpFn_eq_one hρ h
    rw [e, sub_self, abs_zero]
    positivity
  · have h2 : ρ ^ 2 / 16 < l ^ 2 * Q := not_le.1 h
    have e₀ : scaleBump ρ Q l = bumpFn ρ (l ^ 2 * Q) := rfl
    have ha : |1 - scaleBump ρ Q l| ≤ 1 := by
      rw [e₀, abs_le]
      constructor <;> linarith [bumpFn_nonneg ρ (l ^ 2 * Q), bumpFn_le_one ρ (l ^ 2 * Q)]
    have h3 : 1 ≤ 16 / ρ ^ 2 * (l ^ 2 * Q) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have h4 : 1 ≤ (16 / ρ ^ 2 * (l ^ 2 * Q)) ^ 2 := by nlinarith
    have h5 : (16 / ρ ^ 2 * (l ^ 2 * Q)) ^ 2 ≤ (16 / ρ ^ 2) ^ 2 * Q ^ 2 * l ^ 3 := by
      have e : (16 / ρ ^ 2 * (l ^ 2 * Q)) ^ 2 = (16 / ρ ^ 2) ^ 2 * Q ^ 2 * l ^ 3 * l := by ring
      rw [e]
      have : 0 ≤ (16 / ρ ^ 2) ^ 2 * Q ^ 2 * l ^ 3 := by positivity
      nlinarith
    linarith
private theorem piece_bumpTail {ρ l₀ : ℝ} (hρ : 0 < ρ) (hl₁ : l₀ ≤ 1) :
    IsConvergentPiece (F := F) ρ l₀ (fun l ζ => (1 - scaleBump ρ (sumSq ζ) l) / l ^ 3) fun _ => 0 := by
  set n : ℝ := ((Fintype.card ↥(chordBonds (finiteCells F)) : ℕ) : ℝ) with hn
  refine ⟨fun l _ _ => ((continuous_const.sub (continuous_scaleBump ρ l)).div_const _).continuousOn,
    ⟨(16 / ρ ^ 2) ^ 2 * n ^ 2, 4, by positivity, fun l ζ h0 h1 _ => ?_⟩, fun ζ => ?_⟩
  · refine (abs_bumpTail_le hρ (sumSq_nonneg ζ) h0 (h1.trans hl₁)).trans ?_
    have h3 := sumSq_le_pow ζ
    have h4 : sumSq ζ ^ 2 ≤ (n * (1 + ‖ζ‖) ^ 2) ^ 2 := pow_le_pow_left₀ (sumSq_nonneg ζ) h3 2
    calc _ ≤ (16 / ρ ^ 2) ^ 2 * (n * (1 + ‖ζ‖) ^ 2) ^ 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_small (Q := sumSq ζ) hρ] with l hl
    rw [(scaleBump_eq_one_of_small hρ hl).1]
    simp
private theorem ratio_deriv_eq {u u₁ v v₁ : ℝ} (hv : v ≠ 0) :
    (u₁ * v - u * v₁) / v ^ 2 = u₁ / v - u * v₁ / v ^ 2 := by
  field_simp
private theorem ratio_secondDeriv_eq {Z n₀ n₁ n₂ e₀ e₁ e₂ : ℝ} (hZ : Z ≠ 0) (he : e₀ ≠ 0) :
    (Z * n₂) / (Z * e₀) - 2 * (Z * n₁) * (Z * e₁) / (Z * e₀) ^ 2 - (Z * n₀) * (Z * e₂) / (Z * e₀) ^ 2 +
      2 * (Z * n₀) * (Z * e₁) ^ 2 / (Z * e₀) ^ 3 =
      n₂ / e₀ - 2 * n₁ * e₁ / e₀ ^ 2 - n₀ * e₂ / e₀ ^ 2 + 2 * n₀ * e₁ ^ 2 / e₀ ^ 3 := by
  field_simp
private theorem tendsto_secondDifference_ratio {u u₁ u₂ v v₁ v₂ Z n₀ n₁ n₂ e₀ e₁ e₂ M ε₁ ε₂ : ℝ → ℝ}
    {a₀ a₁ a₂ b₂ δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ l ∈ Ioo 0 δ, HasDerivAt u (u₁ l) l) (hu₁ : ∀ l ∈ Ioo 0 δ, HasDerivAt u₁ (u₂ l) l)
    (hv : ∀ l ∈ Ioo 0 δ, HasDerivAt v (v₁ l) l) (hv₁ : ∀ l ∈ Ioo 0 δ, HasDerivAt v₁ (v₂ l) l)
    (hZ : ∀ l ∈ Ioo 0 δ, Z l ≠ 0) (eu : ∀ l ∈ Ioo 0 δ, u l = Z l * n₀ l) (eu₁ : ∀ l ∈ Ioo 0 δ, u₁ l = Z l * n₁ l)
    (eu₂ : ∀ l ∈ Ioo 0 δ, u₂ l = Z l * n₂ l) (ev : ∀ l ∈ Ioo 0 δ, v l = Z l * e₀ l)
    (ev₁ : ∀ l ∈ Ioo 0 δ, v₁ l = Z l * e₁ l) (ev₂ : ∀ l ∈ Ioo 0 δ, v₂ l = Z l * e₂ l)
    (tn₀ : Tendsto n₀ (𝓝[>] 0) (𝓝 a₀)) (tn₁ : Tendsto n₁ (𝓝[>] 0) (𝓝 a₁)) (tn₂ : Tendsto n₂ (𝓝[>] 0) (𝓝 a₂))
    (te₀ : Tendsto e₀ (𝓝[>] 0) (𝓝 1)) (te₁ : Tendsto e₁ (𝓝[>] 0) (𝓝 0)) (te₂ : Tendsto e₂ (𝓝[>] 0) (𝓝 b₂))
    (tε₁ : Tendsto ε₁ (𝓝[>] 0) (𝓝 0)) (tε₂ : Tendsto ε₂ (𝓝[>] 0) (𝓝 0))
    (eM : ∀ l ∈ Ioo 0 δ, M l = n₀ l + l ^ 3 * ε₁ l) (e1 : ∀ l ∈ Ioo 0 δ, 1 = e₀ l + l ^ 3 * ε₂ l) :
    Tendsto (fun l => (M (3 * l / 2) + M (l / 2) - 2 * M l) / (l / 2) ^ 2) (𝓝[>] 0) (𝓝 (a₂ - a₀ * b₂)) := by
  have hhalf : ∀ᶠ l in 𝓝[>] (0 : ℝ), 1 / 2 < e₀ l := te₀.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hhalf
  have hδ₁' : (0 : ℝ) < δ₁ := hδ₁
  set δ₂ : ℝ := min δ δ₁ with hδ₂
  have δ₂pos : 0 < δ₂ := lt_min hδ hδ₁'
  have inδ : ∀ l ∈ Ioo 0 δ₂, l ∈ Ioo 0 δ := fun l hl => ⟨hl.1, lt_of_lt_of_le hl.2 (min_le_left _ _)⟩
  have ne₀ : ∀ l ∈ Ioo 0 δ₂, e₀ l ≠ 0 := fun l hl => by
    have h : (1 / 2 : ℝ) < e₀ l := hsub ⟨hl.1, lt_of_lt_of_le hl.2 (min_le_right _ _)⟩
    linarith
  have nv : ∀ l ∈ Ioo 0 δ₂, v l ≠ 0 := fun l hl => by
    rw [ev l (inδ l hl)]
    exact mul_ne_zero (hZ l (inδ l hl)) (ne₀ l hl)
  set g₁ : ℝ → ℝ := fun l => u₁ l / v l - u l * v₁ l / v l ^ 2 with hg₁
  set g₂ : ℝ → ℝ := fun l => u₂ l / v l - 2 * u₁ l * v₁ l / v l ^ 2 - u l * v₂ l / v l ^ 2 +
    2 * u l * v₁ l ^ 2 / v l ^ 3 with hg₂
  have dR : ∀ l ∈ Ioo 0 δ₂, HasDerivAt (fun l => u l / v l) (g₁ l) l := by
    intro l hl
    refine ((hu l (inδ l hl)).div (hv l (inδ l hl)) (nv l hl)).congr_deriv ?_
    simp only [hg₁]
    exact ratio_deriv_eq (nv l hl)
  have dg : ∀ l ∈ Ioo 0 δ₂, HasDerivAt g₁ (g₂ l) l := by
    intro l hl
    have hn := nv l hl
    have a := (hu₁ l (inδ l hl)).div (hv l (inδ l hl)) hn
    have b := ((hu l (inδ l hl)).mul (hv₁ l (inδ l hl))).div ((hv l (inδ l hl)).pow 2) (pow_ne_zero 2 hn)
    refine (a.sub b).congr_deriv ?_
    simp only [hg₂, Pi.mul_apply, Pi.pow_apply]
    field_simp
    ring
  have T : Tendsto g₂ (𝓝[>] 0) (𝓝 (a₂ - a₀ * b₂)) := by
    have h₀ : Tendsto (fun l => n₂ l / e₀ l - 2 * n₁ l * e₁ l / e₀ l ^ 2 - n₀ l * e₂ l / e₀ l ^ 2 +
        2 * n₀ l * e₁ l ^ 2 / e₀ l ^ 3) (𝓝[>] 0)
        (𝓝 (a₂ / 1 - 2 * a₁ * 0 / 1 ^ 2 - a₀ * b₂ / 1 ^ 2 + 2 * a₀ * 0 ^ 2 / 1 ^ 3)) :=
      (((tn₂.div te₀ one_ne_zero).sub (((tn₁.const_mul 2).mul te₁).div (te₀.pow 2) (by norm_num))).sub
        ((tn₀.mul te₂).div (te₀.pow 2) (by norm_num))).add
        (((tn₀.const_mul 2).mul (te₁.pow 2)).div (te₀.pow 3) (by norm_num))
    have e : a₂ / 1 - 2 * a₁ * 0 / 1 ^ 2 - a₀ * b₂ / 1 ^ 2 + 2 * a₀ * 0 ^ 2 / 1 ^ 3 = a₂ - a₀ * b₂ := by ring
    rw [e] at h₀
    refine h₀.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT δ₂pos] with l hl
    have hl' := inδ l hl
    simp only [hg₂]
    rw [eu l hl', eu₁ l hl', eu₂ l hl', ev l hl', ev₁ l hl', ev₂ l hl']
    exact (ratio_secondDeriv_eq (hZ l hl') (ne₀ l hl)).symm
  have T₁ : Tendsto (fun l => (u (3 * l / 2) / v (3 * l / 2) + u (l / 2) / v (l / 2) - 2 * (u l / v l)) /
      (l / 2) ^ 2) (𝓝[>] 0) (𝓝 (a₂ - a₀ * b₂)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h1 := (Metric.tendsto_nhds.1 T) (ε / 4) (by positivity)
    obtain ⟨δ₃, hδ₃, hsub₃⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    have hδ₃' : (0 : ℝ) < δ₃ := hδ₃
    set δ₄ : ℝ := min δ₂ δ₃ with hδ₄
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * δ₄ / 3 by positivity)] with l hl
    have hl0 : 0 < l := hl.1
    have rng : ∀ w ∈ Icc (l - l / 2) (l + l / 2), w ∈ Ioo 0 δ₂ ∧ w ∈ Ioo 0 δ₃ := by
      intro w hw
      have h2 : w < δ₄ := by linarith [hw.2, hl.2]
      have h3 : 0 < w := by linarith [hw.1]
      exact ⟨⟨h3, lt_of_lt_of_le h2 (min_le_left _ _)⟩, ⟨h3, lt_of_lt_of_le h2 (min_le_right _ _)⟩⟩
    have h2 := abs_secondDifference_le (g := fun l => u l / v l) (g' := g₁) (g'' := g₂) (l := l) (s := l / 2)
      (L := a₂ - a₀ * b₂) (ε := ε / 4) (by positivity) (by positivity)
      (fun w hw => dR w (rng w hw).1) (fun w hw => dg w (rng w hw).1)
      (fun w hw => by
        have h3 := hsub₃ (rng w hw).2
        have h4 : dist (g₂ w) (a₂ - a₀ * b₂) < ε / 4 := h3
        rw [Real.dist_eq] at h4
        exact h4.le)
    have f₁ : l + l / 2 = 3 * l / 2 := by ring
    have f₂ : l - l / 2 = l / 2 := by ring
    simp only [f₁, f₂] at h2
    rw [Real.dist_eq]
    have hs : 0 < (l / 2) ^ 2 := by positivity
    set X : ℝ := u (3 * l / 2) / v (3 * l / 2) + u (l / 2) / v (l / 2) - 2 * (u l / v l) with hX
    have e : X / (l / 2) ^ 2 - (a₂ - a₀ * b₂) = (X - (a₂ - a₀ * b₂) * (l / 2) ^ 2) / (l / 2) ^ 2 := by
      field_simp
    rw [e, abs_div, abs_of_pos hs, div_lt_iff₀ hs]
    have : 2 * (ε / 4) * (l / 2) ^ 2 < ε * (l / 2) ^ 2 := by nlinarith
    exact lt_of_le_of_lt h2 this
  set q : ℝ → ℝ := fun l => (u l / v l - M l) / l ^ 2 with hq
  have tq : Tendsto q (𝓝[>] 0) (𝓝 0) := by
    have h₀ : Tendsto (fun l : ℝ => l * (n₀ l * ε₂ l / e₀ l - ε₁ l)) (𝓝[>] 0) (𝓝 (0 * (a₀ * 0 / 1 - 0))) := by
      have hid : Tendsto (fun l : ℝ => l) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      exact hid.mul (((tn₀.mul tε₂).div te₀ one_ne_zero).sub tε₁)
    rw [zero_mul] at h₀
    refine h₀.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT δ₂pos] with l hl
    have hl' := inδ l hl
    have hl0 : l ≠ 0 := hl.1.ne'
    have hz := hZ l hl'
    have he := ne₀ l hl
    simp only [hq]
    rw [eu l hl', ev l hl', eM l hl', mul_div_mul_left _ _ hz]
    have h3 := e1 l hl'
    have h4 : e₀ l = 1 - l ^ 3 * ε₂ l := by linarith
    field_simp
    rw [h4]
    ring
  have up : ∀ c : ℝ, 0 < c → Tendsto (fun l : ℝ => c * l) (𝓝[>] 0) (𝓝[>] 0) := by
    intro c hc
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto (fun l : ℝ => c * l) (𝓝 0) (𝓝 (c * 0)) := (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with l hl
      exact mul_pos hc hl
  have D₃ : Tendsto (fun l => q (3 / 2 * l)) (𝓝[>] 0) (𝓝 0) := tq.comp (up _ (by norm_num))
  have D₁ : Tendsto (fun l => q (1 / 2 * l)) (𝓝[>] 0) (𝓝 0) := tq.comp (up _ (by norm_num))
  have D := ((D₃.const_mul 9).add D₁).sub (tq.const_mul 8)
  have S := T₁.sub D
  have e0 : a₂ - a₀ * b₂ - (9 * 0 + 0 - 8 * 0) = a₂ - a₀ * b₂ := by ring
  rw [e0] at S
  refine S.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT δ₂pos] with l hl
  have hl0 : l ≠ 0 := hl.1.ne'
  simp only [hq]
  have f₁ : 3 / 2 * l = 3 * l / 2 := by ring
  have f₂ : 1 / 2 * l = l / 2 := by ring
  rw [f₁, f₂]
  field_simp
  ring
private def constOne : ℝ → StepVariable (finiteCells F) → ℝ := fun _ _ => 1
private theorem scaleD1_constOne (s : ℝ) (ζ : StepVariable (finiteCells F)) : scaleD1 constOne s ζ = 0 := by
  simp [scaleD1, constOne]
private theorem scaleD2_constOne (s : ℝ) (ζ : StepVariable (finiteCells F)) : scaleD2 constOne s ζ = 0 := by
  have e : (fun u => scaleD1 (constOne (F := F)) u ζ) = fun _ => 0 := funext fun u => scaleD1_constOne u ζ
  simp [scaleD2, e]
private theorem tame_constOne (ρ l₀ : ℝ) : IsTameInScale (F := F) ρ l₀ 1 0 constOne := by
  refine ⟨zero_le_one, fun _ _ _ => contDiffAt_const, fun _ _ _ _ _ => by simp [constOne], fun s ζ _ _ _ => ?_,
    fun s ζ _ _ _ => ?_, fun _ _ _ => continuousOn_const, fun s _ _ => ?_, fun s _ _ => ?_⟩
  · rw [scaleD1_constOne]
    simp
  · rw [scaleD2_constOne]
    simp
  · have e : scaleD1 (constOne (F := F)) s = fun _ => 0 := funext fun ζ => scaleD1_constOne s ζ
    rw [e]
    exact continuousOn_const
  · have e : scaleD2 (constOne (F := F)) s = fun _ => 0 := funext fun ζ => scaleD2_constOne s ζ
    rw [e]
    exact continuousOn_const
private theorem tendsto_secondDifference_mean {ρ l₀ KE KO C : ℝ} {mE mO : ℕ}
    {E O W : ℝ → StepVariable (finiteCells F) → ℝ} {G : (StepVariable (finiteCells F) → ℝ) → ℝ} (hρ : 0 < ρ)
    (hl₀ : 0 < l₀) (hl₁ : l₀ ≤ 1) (hC : 0 ≤ C) (hb : ∀ u, |bumpD1 ρ u| ≤ C ∧ |bumpD2 ρ u| ≤ C)
    (hE : IsTameInScale ρ l₀ KE mE E) (hO : IsTameInScale ρ l₀ KO mO O) (hw : ScaleWeights ρ l₀ E W G)
    (hU : G (fun ζ => scaleD1 E 0 ζ) = 0) :
    Tendsto (fun l => (ratioMean (W (3 * l / 2)) (O (3 * l / 2)) + ratioMean (W (l / 2)) (O (l / 2)) -
      2 * ratioMean (W l) (O l)) / (l / 2) ^ 2) (𝓝[>] 0)
      (𝓝 (2 * G (fun ζ => scaleD2 O 0 ζ / 2) - 2 * G (fun ζ => scaleD1 O 0 ζ * scaleD1 E 0 ζ) -
        2 * G (fun ζ => O 0 ζ * (scaleD2 E 0 ζ / 2)) + G (fun ζ => O 0 ζ * scaleD1 E 0 ζ ^ 2) -
        G (fun ζ => O 0 ζ) * (G (fun ζ => scaleD1 E 0 ζ ^ 2) - 2 * G fun ζ => scaleD2 E 0 ζ / 2))) := by
  have hone := tame_constOne (F := F) ρ l₀
  have ev := Ioc_mem_nhdsGT hl₀
  have hG₀ : G (fun _ => 0) = 0 := by
    have hp := ((piece_of_tame0 hρ hone).const_mul 0).congr_limit (q₀ := fun _ => 0) fun ζ => zero_mul _
    have h := tendsto_ratioMean_piece hρ hl₀ hw hp
    have h' : Tendsto (fun l => ratioMean (W l) (fun ζ => 0 * constOne l ζ)) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr fun l => ?_
      simp [ratioMean]
    exact tendsto_nhds_unique h h'
  have hG₁ : G (fun _ => 1) = 1 := by
    have h := tendsto_ratioMean_piece hρ hl₀ hw (piece_of_tame0 hρ hone)
    have h' : Tendsto (fun l => ratioMean (W l) (constOne l)) (𝓝[>] 0) (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ev] with l hl
      exact (ratioMean_one (hw.mass_ne_zero l hl.1 hl.2)).symm
    exact tendsto_nhds_unique h h'
  obtain ⟨A₀, A₁, A₂⟩ := tendsto_bumped_means hρ hl₀ hl₁ hC hb hE hO hw hG₀
  obtain ⟨B₀, B₁, B₂⟩ := tendsto_bumped_means hρ hl₀ hl₁ hC hb hE hone hw hG₀
  have eB₀ : G (fun ζ => constOne (F := F) 0 ζ) = 1 := hG₁
  have eB₁ : G (fun ζ => scaleD1 constOne 0 ζ) - G (fun ζ => constOne 0 ζ * scaleD1 E 0 ζ) = 0 := by
    have e₁ : (fun ζ => scaleD1 (constOne (F := F)) 0 ζ) = fun _ => 0 := funext fun ζ => scaleD1_constOne 0 ζ
    have e₂ : (fun ζ => constOne 0 ζ * scaleD1 E 0 ζ) = fun ζ => scaleD1 E 0 ζ := funext fun ζ => one_mul _
    rw [e₁, e₂, hG₀, hU, sub_zero]
  have eB₂ : 2 * G (fun ζ => scaleD2 constOne 0 ζ / 2) - 2 * G (fun ζ => scaleD1 constOne 0 ζ * scaleD1 E 0 ζ) -
      2 * G (fun ζ => constOne 0 ζ * (scaleD2 E 0 ζ / 2)) + G (fun ζ => constOne 0 ζ * scaleD1 E 0 ζ ^ 2) =
      G (fun ζ => scaleD1 E 0 ζ ^ 2) - 2 * G fun ζ => scaleD2 E 0 ζ / 2 := by
    have e₁ : (fun ζ => scaleD2 (constOne (F := F)) 0 ζ / 2) = fun _ => 0 :=
      funext fun ζ => by rw [scaleD2_constOne]; simp
    have e₂ : (fun ζ => scaleD1 constOne 0 ζ * scaleD1 E 0 ζ) = fun _ => 0 :=
      funext fun ζ => by rw [scaleD1_constOne]; simp
    have e₃ : (fun ζ => constOne 0 ζ * (scaleD2 E 0 ζ / 2)) = fun ζ => scaleD2 E 0 ζ / 2 := funext fun ζ => one_mul _
    have e₄ : (fun ζ => constOne 0 ζ * scaleD1 E 0 ζ ^ 2) = fun ζ => scaleD1 E 0 ζ ^ 2 := funext fun ζ => one_mul _
    rw [e₁, e₂, e₃, e₄, hG₀]
    ring
  rw [eB₀] at B₀
  rw [eB₁] at B₁
  rw [eB₂] at B₂
  have g₀ := piece_of_tame0 hρ hO
  have t₀ := piece_scaleBump0 (F := F) (l₀ := l₀) hρ
  have tp := piece_bumpTail (F := F) (l₀ := l₀) hρ hl₁
  have P₀ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * O l ζ) fun ζ => O 0 ζ :=
    (t₀.mul g₀).congr_limit fun ζ => one_mul _
  have P₁ : IsConvergentPiece ρ l₀ (fun l ζ => (1 - scaleBump ρ (sumSq ζ) l) / l ^ 3 * O l ζ) fun _ => 0 :=
    (tp.mul g₀).congr_limit fun ζ => zero_mul _
  have P₂ : IsConvergentPiece ρ l₀ (fun l ζ => scaleBump ρ (sumSq ζ) l * constOne l ζ) fun ζ => 1 :=
    (t₀.mul (piece_of_tame0 hρ hone)).congr_limit fun ζ => one_mul _
  have tε₁ := tendsto_ratioMean_piece hρ hl₀ hw P₁
  have tε₂ := tendsto_ratioMean_piece hρ hl₀ hw tp
  rw [hG₀] at tε₁ tε₂
  have rng : ∀ l ∈ Ioo 0 (2 * l₀ / 3), 0 < l ∧ l ≤ l₀ ∧ 3 * l / 2 ≤ l₀ := fun l hl =>
    ⟨hl.1, by linarith [hl.1, hl.2], by linarith [hl.2]⟩
  have sum_eq : ∀ {g : ℝ → StepVariable (finiteCells F) → ℝ} {l : ℝ}, l ≠ 0 → g l = fun ζ =>
      scaleBump ρ (sumSq ζ) l * g l ζ + l ^ 3 * ((1 - scaleBump ρ (sumSq ζ) l) / l ^ 3 * g l ζ) := by
    intro g l hl
    funext ζ
    field_simp
    ring
  refine tendsto_secondDifference_ratio (u := bumpedIntegral0 ρ E O) (u₁ := bumpedIntegral1 ρ E O)
    (u₂ := bumpedIntegral2 ρ E O) (v := bumpedIntegral0 ρ E constOne) (v₁ := bumpedIntegral1 ρ E constOne)
    (v₂ := bumpedIntegral2 ρ E constOne) (Z := fun l => ∫ ζ, W l ζ) (n₀ := fun l => ratioMean (W l) (bumped0 ρ O l))
    (n₁ := fun l => ratioMean (W l) (bumped1 ρ E O l)) (n₂ := fun l => ratioMean (W l) (bumped2 ρ E O l))
    (e₀ := fun l => ratioMean (W l) (bumped0 ρ constOne l)) (e₁ := fun l => ratioMean (W l) (bumped1 ρ E constOne l))
    (e₂ := fun l => ratioMean (W l) (bumped2 ρ E constOne l)) (M := fun l => ratioMean (W l) (O l))
    (ε₁ := fun l => ratioMean (W l) fun ζ => (1 - scaleBump ρ (sumSq ζ) l) / l ^ 3 * O l ζ)
    (ε₂ := fun l => ratioMean (W l) fun ζ => (1 - scaleBump ρ (sumSq ζ) l) / l ^ 3) (δ := 2 * l₀ / 3) (by positivity)
    (fun l hl => (hasDerivAt_bumpedIntegral hρ hE hO hC hb (rng l hl).1 (rng l hl).2.2).1)
    (fun l hl => (hasDerivAt_bumpedIntegral hρ hE hO hC hb (rng l hl).1 (rng l hl).2.2).2)
    (fun l hl => (hasDerivAt_bumpedIntegral hρ hE hone hC hb (rng l hl).1 (rng l hl).2.2).1)
    (fun l hl => (hasDerivAt_bumpedIntegral hρ hE hone hC hb (rng l hl).1 (rng l hl).2.2).2)
    (fun l hl => hw.mass_ne_zero l (rng l hl).1 (rng l hl).2.1)
    (fun l hl => integral_eq_mass_mul_ratioMean hw (rng l hl).1 (rng l hl).2.1 fun ζ h =>
      (bumped_eq_zero (E := E) hρ h).1)
    (fun l hl => integral_eq_mass_mul_ratioMean hw (rng l hl).1 (rng l hl).2.1 fun ζ h => (bumped_eq_zero hρ h).2.1)
    (fun l hl => integral_eq_mass_mul_ratioMean hw (rng l hl).1 (rng l hl).2.1 fun ζ h => (bumped_eq_zero hρ h).2.2)
    (fun l hl => integral_eq_mass_mul_ratioMean hw (rng l hl).1 (rng l hl).2.1 fun ζ h =>
      (bumped_eq_zero (E := E) hρ h).1)
    (fun l hl => integral_eq_mass_mul_ratioMean hw (rng l hl).1 (rng l hl).2.1 fun ζ h => (bumped_eq_zero hρ h).2.1)
    (fun l hl => integral_eq_mass_mul_ratioMean hw (rng l hl).1 (rng l hl).2.1 fun ζ h => (bumped_eq_zero hρ h).2.2)
    A₀ A₁ A₂ B₀ B₁ B₂ tε₁ tε₂ ?_ ?_
  · intro l hl
    obtain ⟨h0, h1, -⟩ := rng l hl
    have i₀ := integrable_piece hρ hw P₀ h0 h1
    have i₁ := integrable_const_mul_mul (l ^ 3) (integrable_piece hρ hw P₁ h0 h1)
    show ratioMean (W l) (O l) = ratioMean (W l) (bumped0 ρ O l) +
      l ^ 3 * ratioMean (W l) fun ζ => (1 - scaleBump ρ (sumSq ζ) l) / l ^ 3 * O l ζ
    conv_lhs => rw [sum_eq (g := O) h0.ne']
    rw [ratioMean_add i₀ i₁, ratioMean_const_mul]
    rfl
  · intro l hl
    obtain ⟨h0, h1, -⟩ := rng l hl
    have i₀ := integrable_piece hρ hw P₂ h0 h1
    have i₁ := integrable_const_mul_mul (l ^ 3) (integrable_piece hρ hw tp h0 h1)
    have e₁ := ratioMean_one (hw.mass_ne_zero l h0 h1)
    have e₂ : (fun _ : StepVariable (finiteCells F) => (1 : ℝ)) = fun ζ =>
        scaleBump ρ (sumSq ζ) l * constOne l ζ + l ^ 3 * ((1 - scaleBump ρ (sumSq ζ) l) / l ^ 3) := by
      funext ζ
      have := h0.ne'
      simp only [constOne]
      field_simp
      ring
    rw [e₂, ratioMean_add i₀ i₁, ratioMean_const_mul] at e₁
    exact e₁.symm
private theorem IsTameInScale.mono {ρ l₀ l₁ K : ℝ} {m : ℕ} {g : ℝ → StepVariable (finiteCells F) → ℝ}
    (h : IsTameInScale ρ l₀ K m g) (hl : l₁ ≤ l₀) : IsTameInScale ρ l₁ K m g :=
  ⟨h.nonneg, h.contDiffAt, fun s ζ a b => h.bound0 s ζ a (b.trans hl), fun s ζ a b => h.bound1 s ζ a (b.trans hl),
    fun s ζ a b => h.bound2 s ζ a (b.trans hl), fun s a b => h.cont0 s a (b.trans hl),
    fun s a b => h.cont1 s a (b.trans hl), fun s a b => h.cont2 s a (b.trans hl)⟩
private theorem eventually_memScaledBalls_abs {ρ s : ℝ} {ζ : StepVariable (finiteCells F)}
    (h : MemScaledBalls ρ |s| ζ) : ∀ᶠ u in 𝓝 s, MemScaledBalls ρ |u| ζ := by
  refine eventually_all.2 fun b => ?_
  have hc : Continuous fun u : ℝ => |u| * ‖ζ b‖ := continuous_abs.mul continuous_const
  exact hc.continuousAt.eventually (gt_mem_nhds (h b))
private theorem memScaledBalls_abs_of_pos {ρ s : ℝ} {ζ : StepVariable (finiteCells F)} (hs : 0 < s)
    (h : MemScaledBalls ρ s ζ) : MemScaledBalls ρ |s| ζ := by
  rwa [abs_of_pos hs]
private theorem IsTameInScale.add {ρ l₀ K K' : ℝ} {m m' : ℕ} {g h : ℝ → StepVariable (finiteCells F) → ℝ}
    (hg : IsTameInScale ρ l₀ K m g) (hh : IsTameInScale ρ l₀ K' m' h) :
    IsTameInScale ρ l₀ (K + K') (m + m') fun s ζ => g s ζ + h s ζ := by
  have e₁ : ∀ {s : ℝ} {ζ : StepVariable (finiteCells F)}, MemScaledBalls ρ |s| ζ →
      scaleD1 (fun s ζ => g s ζ + h s ζ) s ζ = scaleD1 g s ζ + scaleD1 h s ζ := fun hs =>
    ((hg.hasDerivAt_d1 hs).add (hh.hasDerivAt_d1 hs)).deriv
  have e₂ : ∀ {s : ℝ} {ζ : StepVariable (finiteCells F)}, MemScaledBalls ρ |s| ζ →
      scaleD2 (fun s ζ => g s ζ + h s ζ) s ζ = scaleD2 g s ζ + scaleD2 h s ζ := fun {s ζ} hs => by
    have h1 : HasDerivAt (fun u => scaleD1 g u ζ + scaleD1 h u ζ) (scaleD2 g s ζ + scaleD2 h s ζ) s :=
      (hg.hasDerivAt_d2 hs).add (hh.hasDerivAt_d2 hs)
    refine (h1.congr_of_eventuallyEq ?_).deriv
    filter_upwards [eventually_memScaledBalls_abs hs] with u hu using e₁ hu
  have pw : ∀ (ζ : StepVariable (finiteCells F)) {x y : ℝ}, |x| ≤ K * (1 + ‖ζ‖) ^ m → |y| ≤ K' * (1 + ‖ζ‖) ^ m' →
      |x + y| ≤ (K + K') * (1 + ‖ζ‖) ^ (m + m') := fun ζ {x y} hx hy => by
    have h₁ : (1 + ‖ζ‖) ^ m ≤ (1 + ‖ζ‖) ^ (m + m') :=
      pow_le_pow_right₀ (by linarith [norm_nonneg ζ]) (by omega)
    have h₂ : (1 + ‖ζ‖) ^ m' ≤ (1 + ‖ζ‖) ^ (m + m') :=
      pow_le_pow_right₀ (by linarith [norm_nonneg ζ]) (by omega)
    calc |x + y| ≤ |x| + |y| := abs_add_le _ _
      _ ≤ K * (1 + ‖ζ‖) ^ (m + m') + K' * (1 + ‖ζ‖) ^ (m + m') :=
          add_le_add (hx.trans (mul_le_mul_of_nonneg_left h₁ hg.nonneg))
            (hy.trans (mul_le_mul_of_nonneg_left h₂ hh.nonneg))
      _ = _ := by ring
  refine ⟨add_nonneg hg.nonneg hh.nonneg, fun s ζ hs => (hg.contDiffAt s ζ hs).add (hh.contDiffAt s ζ hs),
    fun s ζ a b c => pw ζ (hg.bound0 s ζ a b c) (hh.bound0 s ζ a b c), fun s ζ a b c => ?_, fun s ζ a b c => ?_,
    fun s a b => (hg.cont0 s a b).add (hh.cont0 s a b), fun s a b => ?_, fun s a b => ?_⟩
  · rw [e₁ (memScaledBalls_abs_of_pos a c)]
    exact pw ζ (hg.bound1 s ζ a b c) (hh.bound1 s ζ a b c)
  · rw [e₂ (memScaledBalls_abs_of_pos a c)]
    exact pw ζ (hg.bound2 s ζ a b c) (hh.bound2 s ζ a b c)
  · exact ((hg.cont1 s a b).add (hh.cont1 s a b)).congr fun ζ hζ => e₁ (memScaledBalls_abs_of_pos a hζ)
  · exact ((hg.cont2 s a b).add (hh.cont2 s a b)).congr fun ζ hζ => e₂ (memScaledBalls_abs_of_pos a hζ)
private theorem IsTameInScale.const_mul {ρ l₀ K : ℝ} {m : ℕ} {g : ℝ → StepVariable (finiteCells F) → ℝ} (c : ℝ)
    (hg : IsTameInScale ρ l₀ K m g) : IsTameInScale ρ l₀ (|c| * K) m fun s ζ => c * g s ζ := by
  have e₁ : ∀ {s : ℝ} {ζ : StepVariable (finiteCells F)}, MemScaledBalls ρ |s| ζ →
      scaleD1 (fun s ζ => c * g s ζ) s ζ = c * scaleD1 g s ζ := fun hs => ((hg.hasDerivAt_d1 hs).const_mul c).deriv
  have e₂ : ∀ {s : ℝ} {ζ : StepVariable (finiteCells F)}, MemScaledBalls ρ |s| ζ →
      scaleD2 (fun s ζ => c * g s ζ) s ζ = c * scaleD2 g s ζ := fun {s ζ} hs => by
    have h1 : HasDerivAt (fun u => c * scaleD1 g u ζ) (c * scaleD2 g s ζ) s := (hg.hasDerivAt_d2 hs).const_mul c
    refine (h1.congr_of_eventuallyEq ?_).deriv
    filter_upwards [eventually_memScaledBalls_abs hs] with u hu using e₁ hu
  have pw : ∀ (ζ : StepVariable (finiteCells F)) {x : ℝ}, |x| ≤ K * (1 + ‖ζ‖) ^ m →
      |c * x| ≤ |c| * K * (1 + ‖ζ‖) ^ m := fun ζ {x} hx => by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  refine ⟨mul_nonneg (abs_nonneg _) hg.nonneg, fun s ζ hs => contDiffAt_const.mul (hg.contDiffAt s ζ hs),
    fun s ζ a b c' => pw ζ (hg.bound0 s ζ a b c'), fun s ζ a b c' => ?_, fun s ζ a b c' => ?_,
    fun s a b => continuousOn_const.mul (hg.cont0 s a b), fun s a b => ?_, fun s a b => ?_⟩
  · rw [e₁ (memScaledBalls_abs_of_pos a c')]
    exact pw ζ (hg.bound1 s ζ a b c')
  · rw [e₂ (memScaledBalls_abs_of_pos a c')]
    exact pw ζ (hg.bound2 s ζ a b c')
  · exact (continuousOn_const.mul (hg.cont1 s a b)).congr fun ζ hζ => e₁ (memScaledBalls_abs_of_pos a hζ)
  · exact (continuousOn_const.mul (hg.cont2 s a b)).congr fun ζ hζ => e₂ (memScaledBalls_abs_of_pos a hζ)
private theorem tame_finsetSum {ι : Type} {ρ l₀ : ℝ} (S : Finset ι) {G : ι → ℝ → StepVariable (finiteCells F) → ℝ}
    (h : ∀ i ∈ S, ∃ (K : ℝ) (m : ℕ), IsTameInScale ρ l₀ K m (G i)) :
    ∃ (K : ℝ) (m : ℕ), IsTameInScale ρ l₀ K m fun s ζ => ∑ i ∈ S, G i s ζ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 := (tame_constOne (F := F) ρ l₀).const_mul 0
    refine ⟨|0| * 1, 0, ?_⟩
    have e : (fun (s : ℝ) (ζ : StepVariable (finiteCells F)) => ∑ i ∈ (∅ : Finset ι), G i s ζ) =
        fun s ζ => 0 * constOne s ζ := by
      funext s ζ
      simp
    rw [e]
    exact h0
  | insert a S ha ih =>
    obtain ⟨K, m, hK⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨K', m', hK'⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨K + K', m + m', ?_⟩
    have e : (fun (s : ℝ) (ζ : StepVariable (finiteCells F)) => ∑ i ∈ insert a S, G i s ζ) =
        fun s ζ => G a s ζ + ∑ i ∈ S, G i s ζ := by
      funext s ζ
      rw [Finset.sum_insert ha]
    rw [e]
    exact hK.add hK'
private theorem tame_const_mul_sumSq (ρ l₀ c : ℝ) :
    IsTameInScale (F := F) ρ l₀ (|c| * ((Fintype.card ↥(chordBonds (finiteCells F)) : ℕ) : ℝ)) 2
      fun _ ζ => c * sumSq ζ := by
  have z₁ : ∀ s (ζ : StepVariable (finiteCells F)), scaleD1 (fun _ ζ => c * sumSq ζ) s ζ = 0 := fun s ζ => by
    simp [scaleD1]
  have z₂ : ∀ s (ζ : StepVariable (finiteCells F)), scaleD2 (fun _ ζ => c * sumSq ζ) s ζ = 0 := fun s ζ => by
    have e : (fun u => scaleD1 (fun _ ζ => c * sumSq ζ) u ζ) = fun _ => 0 := funext fun u => z₁ u ζ
    simp [scaleD2, e]
  have hn : 0 ≤ |c| * ((Fintype.card ↥(chordBonds (finiteCells F)) : ℕ) : ℝ) := by positivity
  have hp : ∀ ζ : StepVariable (finiteCells F),
      0 ≤ |c| * ((Fintype.card ↥(chordBonds (finiteCells F)) : ℕ) : ℝ) * (1 + ‖ζ‖) ^ 2 := fun ζ => by positivity
  refine ⟨hn, fun _ _ _ => contDiffAt_const, fun s ζ _ _ _ => ?_, fun s ζ _ _ _ => ?_, fun s ζ _ _ _ => ?_,
    fun _ _ _ => (continuous_const.mul continuous_sumSq).continuousOn, fun s _ _ => ?_, fun s _ _ => ?_⟩
  · rw [abs_mul, abs_of_nonneg (sumSq_nonneg ζ), mul_assoc]
    exact mul_le_mul_of_nonneg_left (sumSq_le_pow ζ) (abs_nonneg _)
  · rw [z₁]
    simpa using hp ζ
  · rw [z₂]
    simpa using hp ζ
  · have e : scaleD1 (fun _ ζ => c * sumSq (F := F) ζ) s = fun _ => 0 := funext fun ζ => z₁ s ζ
    rw [e]
    exact continuousOn_const
  · have e : scaleD2 (fun _ ζ => c * sumSq (F := F) ζ) s = fun _ => 0 := funext fun ζ => z₂ s ζ
    rw [e]
    exact continuousOn_const
private theorem bondDeriv_zero_order (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem leftTranslate_bondSpread_zero (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions)
    (τ : Fin 0 → ℝ) (V : F.GaugeField F.top) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V = V := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExponentBoundsAux.leftTranslate_bondSpread_empty <;> assumption
private theorem iteratedDeriv_two_eq (g : ℝ → ℝ) (s : ℝ) : iteratedDeriv 2 g s = deriv (deriv g) s := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
private theorem tame_of_isSmoothObservable {κ ρ l₀ K : ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
    {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hκ : 0 < κ) (hK : 0 ≤ K)
    (h : IsSmoothObservable κ ρ l₀ K Y V Ob) :
    IsTameInScale ρ l₀ (K * (1 + ((Fintype.card ↥(chordBonds (finiteCells F)) : ℕ) : ℝ)) ^ 7) 7
      fun l ζ => Ob l ζ V := by
  set n : ℝ := ((Fintype.card ↥(chordBonds (finiteCells F)) : ℕ) : ℝ) with hn
  have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  have sd : ∀ (i : ℕ) (ζ : StepVariable (finiteCells F)) (s : ℝ),
      scaleDeriv Ob V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) Fin.elim0 i ζ s =
        iteratedDeriv i (fun u => Ob u ζ V) s := by
    intro i ζ s
    unfold scaleDeriv
    congr 1
    funext u
    exact bondDeriv_zero_order _ _ _ _
  have near : ∀ ζ : StepVariable (finiteCells F), localWeight κ Y ζ ≤ n * ‖ζ‖ := by
    intro ζ
    unfold localWeight
    calc _ ≤ ∑ _b : ↥(chordBonds (finiteCells F)), ‖ζ‖ := Finset.sum_le_sum fun b _ => by
          have h1 : Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ 1 := by
            apply Real.exp_le_one_iff.mpr
            have : 0 ≤ 2 ^ 4 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ) := by positivity
            linarith
          calc _ ≤ 1 * ‖ζ b‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ ≤ ‖ζ‖ := by simpa using norm_le_pi_norm ζ b
      _ = n * ‖ζ‖ := by simp [hn]
  have nn : ∀ ζ : StepVariable (finiteCells F), 0 ≤ localWeight κ Y ζ := fun ζ =>
    Finset.sum_nonneg fun b _ => by positivity
  have bound : ∀ (i : ℕ) (s : ℝ) (ζ : StepVariable (finiteCells F)), i ≤ 2 → 0 < s → s ≤ l₀ →
      MemScaledBalls ρ s ζ → |iteratedDeriv i (fun u => Ob u ζ V) s| ≤ K * (1 + n) ^ 7 * (1 + ‖ζ‖) ^ 7 := by
    intro i s ζ hi h0 h1 hz
    have h2 := h.deriv_le 0 i Fin.elim0 Fin.elim0 s ζ (Or.inl ⟨by norm_num, hi⟩) hX₀ h0 h1 hz
    rw [sd] at h2
    refine h2.trans ?_
    have h3 : Real.exp (-(2 ^ 4 * κ * bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ 2 ^ 4 * κ * (bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ) := by positivity
      linarith
    have h4 : (1 + localWeight κ Y ζ) ^ 7 ≤ ((1 + n) * (1 + ‖ζ‖)) ^ 7 := by
      refine pow_le_pow_left₀ (by linarith [nn ζ]) ?_ 7
      have := near ζ
      nlinarith [norm_nonneg ζ]
    calc _ ≤ K * (1 + localWeight κ Y ζ) ^ 7 * 1 :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hK (pow_nonneg (by linarith [nn ζ]) 7))
      _ ≤ K * ((1 + n) * (1 + ‖ζ‖)) ^ 7 := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left h4 hK
      _ = _ := by ring
  have cont : ∀ (i : ℕ) (s : ℝ), i ≤ 2 → 0 < s → s ≤ l₀ →
      ContinuousOn (fun ζ => iteratedDeriv i (fun u => Ob u ζ V) s) {ζ | MemScaledBalls ρ s ζ} := by
    intro i s hi h0 h1
    have hc := h.continuousOn 0 i Fin.elim0 Fin.elim0 (ρ / s + 1) (Or.inl ⟨by norm_num, hi⟩)
    have hcomp : ContinuousOn (fun ζ : StepVariable (finiteCells F) => ((s, ζ) : ℝ × StepVariable (finiteCells F)))
        {ζ | MemScaledBalls ρ s ζ} := (continuous_const.prodMk continuous_id).continuousOn
    refine (hc.comp hcomp ?_).congr fun ζ _ => ?_
    · intro ζ hz
      refine ⟨h0.le, h1, hz, fun b => ?_⟩
      have h2 : s * ‖ζ b‖ < ρ := hz b
      have h3 : ‖ζ b‖ < ρ / s := by
        rw [lt_div_iff₀ h0, mul_comm]
        exact h2
      linarith
    · simp only [Function.comp]
      rw [sd]
  refine ⟨by positivity, fun s ζ hs => ?_, fun s ζ a b c => ?_, fun s ζ a b c => ?_, fun s ζ a b c => ?_,
    fun s a b => ?_, fun s a b => ?_, fun s a b => ?_⟩
  · have h1 := h.contDiffAt s ζ 0 Fin.elim0 Fin.elim0 hs
    have h2 : ContDiffAt ℝ 6 (fun u : ℝ => (((u, ζ), (0 : Fin 0 → ℝ)) :
        (ℝ × StepVariable (finiteCells F)) × (Fin 0 → ℝ))) s :=
      (contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const
    have h3 := ContDiffAt.comp s h1 h2
    have e : (fun u => Ob u ζ V) = (fun q : (ℝ × StepVariable (finiteCells F)) × (Fin 0 → ℝ) =>
        Ob q.1.1 q.1.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread
          (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) Fin.elim0 q.2) V)) ∘
        fun u : ℝ => (((u, ζ), (0 : Fin 0 → ℝ)) : (ℝ × StepVariable (finiteCells F)) × (Fin 0 → ℝ)) := by
      funext u
      simp only [Function.comp]
      rw [leftTranslate_bondSpread_zero]
    rw [e]
    exact h3.of_le (by norm_num)
  · simpa using bound 0 s ζ (by norm_num) a b c
  · have := bound 1 s ζ (by norm_num) a b c
    rwa [iteratedDeriv_one] at this
  · have := bound 2 s ζ le_rfl a b c
    rwa [iteratedDeriv_two_eq] at this
  · simpa using cont 0 s (by norm_num) a b
  · have := cont 1 s (by norm_num) a b
    simp only [iteratedDeriv_one] at this
    exact this
  · have := cont 2 s le_rfl a b
    simp only [iteratedDeriv_two_eq] at this
    exact this
private def lawExponentAt (a ρ lam : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw) :
    ℝ → StepVariable (finiteCells F) → ℝ := fun l ζ => rescaledLawExponent a ρ lam f l V law ζ
private theorem tame_lawExponentAt {a ρA lam ρ l₀ κ K : ℝ} {f : LocalFamily} {V : F.GaugeField F.top}
    {law : StepLaw} (hSum : lawExponentDecompositionStatement) (hfin : Finite F.Cell) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hP : ∀ Y : F.Cell, IsSmoothObservable κ ρ l₀ K Y V (fun l ζ V' => rescaledCellRemainder a ρA lam l Y V' ζ) ∧
      IsSmoothObservable κ ρ l₀ K Y V (fun l ζ V' => rescaledCellExpansion a ρA f l Y V' ζ)) :
    ∃ (K' : ℝ) (m : ℕ), IsTameInScale ρ l₀ K' m (lawExponentAt a ρA lam f V law) := by
  obtain ⟨K₁, m₁, h₁⟩ := tame_finsetSum (ρ := ρ) (l₀ := l₀) (finiteCells F)
    (G := fun Y l ζ => rescaledCellRemainder a ρA lam l Y V ζ)
    fun Y _ => ⟨_, _, tame_of_isSmoothObservable hκ hK (hP Y).1⟩
  obtain ⟨K₂, m₂, h₂⟩ := tame_finsetSum (ρ := ρ) (l₀ := l₀) (finiteCells F)
    (G := fun Y l ζ => rescaledCellExpansion a ρA f l Y V ζ) fun Y _ => ⟨_, _, tame_of_isSmoothObservable hκ hK (hP Y).2⟩
  have h := ((h₁.const_mul (remainderCoefficient law)).add (tame_const_mul_sumSq (F := F) ρ l₀ (lam / 2))).add
    (h₂.const_mul (-expansionCoefficient law))
  have e : lawExponentAt a ρA lam f V law = fun l ζ =>
      remainderCoefficient law * (∑ Y ∈ finiteCells F, rescaledCellRemainder a ρA lam l Y V ζ) +
      lam / 2 * sumSq ζ + -expansionCoefficient law * ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρA f l Y V ζ := by
    funext l ζ
    unfold lawExponentAt
    rw [hSum F a ρA lam l f law V ζ hfin]
    simp only [sumSq]
    ring
  rw [e]
  exact ⟨_, _, h⟩
private theorem lawExponentAt_neg (hEv : RescaledTermsEven) (Y : F.Cell) (a ρA lam : ℝ) (f : LocalFamily)
    (V : F.GaugeField F.top) (law : StepLaw) (l : ℝ) (ζ : StepVariable (finiteCells F)) :
    lawExponentAt a ρA lam f V law (-l) (-ζ) = lawExponentAt a ρA lam f V law l ζ := by
  unfold lawExponentAt
  cases law with
  | tilted ν => exact (hEv F a ρA lam f (fun _ => 0) ν l Y V ζ).2.1
  | interpolated τ =>
    simp only [rescaledLawExponent]
    rw [(hEv F a ρA lam f (fun _ => 0) 0 l Y V ζ).2.1]
    simp
private theorem gaussianMean_scaleD1_eq_zero (hEv : RescaledTermsEven) (Y : F.Cell) (a ρA lam : ℝ)
    (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw) :
    gaussianMean a ρA lam f V law (fun ζ => scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ) = 0 := by
  set E := lawExponentAt a ρA lam f V law with hE
  have ev := lawExponentAt_neg hEv Y a ρA lam f V law
  have odd : ∀ ζ, scaleD1 E 0 (-ζ) = -scaleD1 E 0 ζ := by
    intro ζ
    have e : (fun u => E u (-ζ)) = fun u => E (-u) ζ := by
      funext u
      have := ev (-u) ζ
      rwa [neg_neg] at this
    unfold scaleD1
    rw [e, deriv_comp_neg (fun u => E u ζ) 0, neg_zero]
  have wev : ∀ ζ, gaussianWeight a ρA lam f V law (-ζ) = gaussianWeight a ρA lam f V law ζ := by
    intro ζ
    have h0 := ev 0 ζ
    rw [neg_zero] at h0
    have h1 : rescaledLawExponent a ρA lam f 0 V law (-ζ) = rescaledLawExponent a ρA lam f 0 V law ζ := h0
    unfold gaussianWeight
    rw [h1]
  have key : (∫ ζ, scaleD1 E 0 ζ * gaussianWeight a ρA lam f V law ζ) = 0 := by
    have h1 := Measure.integral_comp_smul (volume : Measure (StepVariable (finiteCells F)))
      (fun ζ => scaleD1 E 0 ζ * gaussianWeight a ρA lam f V law ζ) (-1)
    have h2 : (fun ζ : StepVariable (finiteCells F) =>
        scaleD1 E 0 ((-1 : ℝ) • ζ) * gaussianWeight a ρA lam f V law ((-1 : ℝ) • ζ)) =
        fun ζ => -(scaleD1 E 0 ζ * gaussianWeight a ρA lam f V law ζ) := by
      funext ζ
      rw [neg_one_smul, odd, wev]
      ring
    have h3 : |((-1 : ℝ) ^ Module.finrank ℝ (StepVariable (finiteCells F)))⁻¹| = 1 := by
      rw [abs_inv, abs_pow, abs_neg, abs_one, one_pow, inv_one]
    rw [h2, integral_neg, h3, one_smul] at h1
    linarith
  unfold gaussianMean
  rw [key, zero_div]
private theorem cutoffWeight_smul_eq_one {ρ l : ℝ} {p : ℝ → ℝ} {ζ : StepVariable (finiteCells F)} (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (h0 : 0 < l) (h : l ^ 2 * sumSq ζ ≤ ρ ^ 2 / 4) :
    ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) = 1 := by
  unfold ColdStepAtMirrorFrames.cutoffWeight
  refine Finset.prod_eq_one fun b _ => ?_
  have e : ‖(l • ζ) b‖ = l * ‖ζ b‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos h0]
  have hb := mul_norm_le_of_sumSq hρ h0.le h b
  unfold cutoffFactor
  rw [e, if_pos (by linarith), hp.vanish_small _ (by positivity) (by linarith)]
  simp
private theorem cutoffWeight_smul_eq_zero {ρ l : ℝ} {p : ℝ → ℝ} {ζ : StepVariable (finiteCells F)} (h0 : 0 < l)
    (h : ¬ MemScaledBalls ρ l ζ) : ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) = 0 := by
  unfold MemScaledBalls at h
  simp only [not_forall, not_lt] at h
  obtain ⟨b, hb⟩ := h
  unfold ColdStepAtMirrorFrames.cutoffWeight
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  have e : ‖(l • ζ) b‖ = l * ‖ζ b‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos h0]
  unfold cutoffFactor
  rw [e, if_neg (not_lt.2 hb)]
private theorem integral_rescale {ρ l : ℝ} {p : ℝ → ℝ} {Ψ E₀ : StepVariable (finiteCells F) → ℝ} (h0 : 0 < l)
    (hE : ∀ ζ, MemScaledBalls ρ l ζ → Ψ (l • ζ) = E₀ ζ) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ H : StepVariable (finiteCells F) → ℝ,
      (∫ η, H (l⁻¹ • η) * (ColdStepAtMirrorFrames.cutoffWeight ρ p η * Real.exp (-Ψ η))) =
        c * ∫ ζ, H ζ * (ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) * Real.exp (-E₀ ζ)) := by
  have hne : |(l ^ Module.finrank ℝ (StepVariable (finiteCells F)))⁻¹| ≠ 0 :=
    abs_ne_zero.2 (inv_ne_zero (pow_ne_zero _ h0.ne'))
  refine ⟨|(l ^ Module.finrank ℝ (StepVariable (finiteCells F)))⁻¹|⁻¹, inv_ne_zero hne, fun H' => ?_⟩
  have h := Measure.integral_comp_smul (volume : Measure (StepVariable (finiteCells F)))
    (fun η => H' (l⁻¹ • η) * (ColdStepAtMirrorFrames.cutoffWeight ρ p η * Real.exp (-Ψ η))) l
  have e : (fun ζ : StepVariable (finiteCells F) =>
      H' (l⁻¹ • l • ζ) * (ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) * Real.exp (-Ψ (l • ζ)))) =
      fun ζ => H' ζ * (ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) * Real.exp (-E₀ ζ)) := by
    funext ζ
    rw [smul_smul, inv_mul_cancel₀ h0.ne', one_smul]
    by_cases hz : MemScaledBalls ρ l ζ
    · rw [hE ζ hz]
    · rw [cutoffWeight_smul_eq_zero h0 hz]
      simp
  rw [e, smul_eq_mul] at h
  rw [h, inv_mul_cancel_left₀ hne]
private theorem cutoff_mass_ne_zero {ρ : ℝ} {p : ℝ → ℝ} {Ψ : StepVariable (finiteCells F) → ℝ}
    (hRim : CutoffMeanIsGibbsMean) (hρ : 0 < ρ) (hcut : IsCutoff ρ p) {P : ℝ}
    (hb : ∀ᵐ η ∂cutoffLaw F ρ p, |Ψ η| ≤ P) (hm : AEStronglyMeasurable Ψ (cutoffLaw F ρ p)) :
    (∫ η, ColdStepAtMirrorFrames.cutoffWeight ρ p η * Real.exp (-Ψ η)) ≠ 0 := by
  obtain ⟨hfin, hne, -, hmean⟩ := hRim F ρ p hρ hcut
  have hi : Integrable (fun η => Real.exp (-Ψ η)) (cutoffLaw F ρ p) := by
    refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable hm.neg) (Real.exp P) ?_
    filter_upwards [hb] with η hη
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_exp.2 ((neg_le_abs _).trans hη)
  have := NeZero.mk hne
  have hpos := integral_exp_pos (μ := cutoffLaw F ρ p) (f := fun η => -Ψ η) hi
  have h1 := hmean Ψ fun _ => 1
  unfold cutoffMean gibbsMean at h1
  simp only [one_mul] at h1
  rw [div_self hpos.ne'] at h1
  intro h0
  rw [h0, div_zero] at h1
  exact zero_ne_one h1
private theorem limit_eq_two_mul_coeff (a ρA lam : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw)
    (O : ℝ → StepVariable (finiteCells F) → ℝ) (hU : gaussianMean a ρA lam f V law
      (fun ζ => scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ) = 0) :
    2 * gaussianMean a ρA lam f V law (fun ζ => scaleD2 O 0 ζ / 2) -
        2 * gaussianMean a ρA lam f V law (fun ζ => scaleD1 O 0 ζ * scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ) -
        2 * gaussianMean a ρA lam f V law (fun ζ => O 0 ζ * (scaleD2 (lawExponentAt a ρA lam f V law) 0 ζ / 2)) +
        gaussianMean a ρA lam f V law (fun ζ => O 0 ζ * scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ ^ 2) -
        gaussianMean a ρA lam f V law (fun ζ => O 0 ζ) *
          (gaussianMean a ρA lam f V law (fun ζ => scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ ^ 2) -
            2 * gaussianMean a ρA lam f V law fun ζ => scaleD2 (lawExponentAt a ρA lam f V law) 0 ζ / 2) =
      2 * secondOrderCoeff a ρA lam f V law O := by
  have t₀ : ∀ g : ℝ → ℝ, taylorCoeffAtZero 0 g = g 0 := fun g => by simp [taylorCoeffAtZero]
  have t₁ : ∀ g : ℝ → ℝ, taylorCoeffAtZero 1 g = deriv g 0 := fun g => by simp [taylorCoeffAtZero]
  have t₂ : ∀ g : ℝ → ℝ, taylorCoeffAtZero 2 g = deriv (deriv g) 0 / 2 := fun g => by
    simp [taylorCoeffAtZero, iteratedDeriv_two_eq]
  simp only [secondOrderCoeff, gaussianCovariance, t₀, t₁, t₂]
  have e₁ : (fun ζ => deriv (fun l => rescaledLawExponent a ρA lam f l V law ζ) 0) =
      fun ζ => scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ := rfl
  have e₂ : (fun ζ => deriv (deriv fun l => rescaledLawExponent a ρA lam f l V law ζ) 0 / 2) =
      fun ζ => scaleD2 (lawExponentAt a ρA lam f V law) 0 ζ / 2 := rfl
  have e₃ : (fun ζ => deriv (deriv fun l => O l ζ) 0 / 2) = fun ζ => scaleD2 O 0 ζ / 2 := rfl
  have e₄ : (fun ζ => deriv (fun l => O l ζ) 0) = fun ζ => scaleD1 O 0 ζ := rfl
  have e₅ : (fun ζ => deriv (fun l => rescaledLawExponent a ρA lam f l V law ζ) 0 ^ 2) =
      fun ζ => scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ ^ 2 := rfl
  rw [e₁, e₂, e₃, e₄, e₅, hU]
  show _ = 2 * (_ - (gaussianMean a ρA lam f V law
      (fun ζ => scaleD1 O 0 ζ * scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ) - _) -
    (gaussianMean a ρA lam f V law (fun ζ => O 0 ζ * (scaleD2 (lawExponentAt a ρA lam f V law) 0 ζ / 2)) - _) +
    1 / 2 * (gaussianMean a ρA lam f V law (fun ζ => O 0 ζ * scaleD1 (lawExponentAt a ρA lam f V law) 0 ζ ^ 2) - _))
  ring
private theorem memScaledBalls_inv_smul {ρ s : ℝ} (hs : 0 < s) {η : StepVariable (finiteCells F)}
    (hη : ∀ b, ‖η b‖ < ρ) : MemScaledBalls ρ s (s⁻¹ • η) := by
  intro b
  have e : ‖(s⁻¹ • η) b‖ = s⁻¹ * ‖η b‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
  rw [e, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  exact hη b
abbrev _root_.YangMills.SharedProofs.p27453 := @memScaledBalls_inv_smul
private theorem isOpen_norm_lt (ρ : ℝ) : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.isOpen_bondBall <;> assumption
private theorem norm_le_of_memScaledBalls {ρ s : ℝ} {ζ : StepVariable (finiteCells F)} (hρ : 0 < ρ) (hs : 0 < s)
    (h : MemScaledBalls ρ s ζ) : ‖ζ‖ ≤ ρ / s := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  rw [le_div_iff₀ hs, mul_comm]
  exact (h b).le
private theorem cutoffMean_eq_ratioMean {ρ l K : ℝ} {m : ℕ} {p : ℝ → ℝ} {Ψ E₀ : StepVariable (finiteCells F) → ℝ}
    (hRim : CutoffMeanIsGibbsMean) (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (h0 : 0 < l) (hK : 0 ≤ K)
    (hE : ∀ ζ, MemScaledBalls ρ l ζ → Ψ (l • ζ) = E₀ ζ)
    (hb : ∀ ζ, MemScaledBalls ρ l ζ → |E₀ ζ| ≤ K * (1 + ‖ζ‖) ^ m)
    (hc : ContinuousOn E₀ {ζ | MemScaledBalls ρ l ζ}) :
    (∫ ζ, ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) * Real.exp (-E₀ ζ)) ≠ 0 ∧ ∀ H : StepVariable (finiteCells F) → ℝ,
      cutoffMean ρ p Ψ (fun η => H (l⁻¹ • η)) =
        ratioMean (fun ζ => ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) * Real.exp (-E₀ ζ)) H := by
  obtain ⟨c, hc₀, hI⟩ := integral_rescale (ρ := ρ) (p := p) (Ψ := Ψ) (E₀ := E₀) h0 hE
  obtain ⟨-, -, hball, -⟩ := hRim F ρ p hρ hcut
  have back : ∀ η : StepVariable (finiteCells F), l • l⁻¹ • η = η := fun η => by
    rw [smul_smul, mul_inv_cancel₀ h0.ne', one_smul]
  have den : (∫ η, ColdStepAtMirrorFrames.cutoffWeight ρ p η * Real.exp (-Ψ η)) =
      c * ∫ ζ, ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) * Real.exp (-E₀ ζ) := by
    have := hI fun _ => 1
    simpa only [one_mul] using this
  have mass : (∫ η, ColdStepAtMirrorFrames.cutoffWeight ρ p η * Real.exp (-Ψ η)) ≠ 0 := by
    refine cutoff_mass_ne_zero hRim hρ hcut (Ψ := Ψ) (P := K * (1 + ρ / l) ^ m) ?_ ?_
    · filter_upwards [hball] with η hη
      have hz := memScaledBalls_inv_smul h0 hη
      have h1 := hE _ hz
      rw [back] at h1
      rw [h1]
      refine (hb _ hz).trans (mul_le_mul_of_nonneg_left ?_ hK)
      exact pow_le_pow_left₀ (by positivity) (by linarith [norm_le_of_memScaledBalls hρ h0 hz]) m
    · have hmeq : (cutoffLaw F ρ p).restrict {η | ∀ b, ‖η b‖ < ρ} = cutoffLaw F ρ p :=
        Measure.restrict_eq_self_of_ae_mem hball
      have hcc : ContinuousOn (fun η : StepVariable (finiteCells F) => E₀ (l⁻¹ • η)) {η | ∀ b, ‖η b‖ < ρ} :=
        hc.comp (continuous_const_smul _).continuousOn fun η hη => memScaledBalls_inv_smul h0 hη
      have hm := hcc.aestronglyMeasurable (μ := cutoffLaw F ρ p) (isOpen_norm_lt ρ).measurableSet
      rw [hmeq] at hm
      refine hm.congr ?_
      filter_upwards [hball] with η hη
      have h1 := hE _ (memScaledBalls_inv_smul h0 hη)
      rw [back] at h1
      exact h1.symm
  refine ⟨fun h => mass (by rw [den, h, mul_zero]), fun H => ?_⟩
  unfold cutoffMean ratioMean
  rw [hI H, den, mul_div_mul_left _ _ hc₀]
end CurvatureLimit
open CurvatureLimit in
theorem scaledMeanCurvatureLimit_holds (hR : scaledMeansSmoothInScale) (hB : scaledMeansBounded)
    (hL : scaledLawsTendToGaussian) (hS : rescaledPartsSmoothStatement) (hFl : rescaledExponentFloorStatement)
    (hSum : lawExponentDecompositionStatement) (hEv : RescaledTermsEven) (hRim : CutoffMeanIsGibbsMean) :
    ScaledMeanCurvatureLimit := by
  unfold scaledMeansSmoothInScale ForallSmoothObservables at hR
  unfold scaledMeansBounded ForallSmoothObservables at hB
  unfold ScaledMeanCurvatureLimit ForallSmoothObservables
  refine EventuallyOrdered.mono (EventuallyOrdered.and hR (EventuallyOrdered.and hB (EventuallyOrdered.and hL
    (EventuallyOrdered.and hS hFl)))) ?_
  rintro T hT hn₁ ⟨g₁, g₂, gL, gS, gF⟩ e
  obtain ⟨a₁, c₁, p₁, q₁, k₁⟩ := g₁ e
  obtain ⟨a₂, C₂, p₂, pC, k₂⟩ := g₂ e
  obtain ⟨aL, hLp, gL⟩ := gL e
  obtain ⟨aS, K₂, hSp, hK₂, gS⟩ := gS e
  obtain ⟨aF, hFp, gF⟩ := gF e
  refine ⟨min a₁ (min a₂ (min aL (min aS aF))), 1, by positivity, one_pos,
    fun l₁ hl hle t f F V Y law K Ob _ _ _ hf hF hV hLw hK hO _ => ?_⟩
  have e₁ : l₁ ≤ a₁ := hle.trans (min_le_left _ _)
  have e₂ : l₁ ≤ a₂ := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have eL : l₁ ≤ aL := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have eS : l₁ ≤ aS := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have eF : l₁ ≤ aF := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ := hT.κ_pos
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hside, hn⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = min l₁ 1 := ⟨_, rfl⟩
  have hL₀ : 0 < L := by rw [hLdef]; exact lt_min hl one_pos
  have hL₁ : L ≤ 1 := by rw [hLdef]; exact min_le_right _ _
  have hLl : L ≤ l₁ := by rw [hLdef]; exact min_le_left _ _
  have hOt := (tame_of_isSmoothObservable hκ hK (hO V hV)).mono (show L ≤ 2 * l₁ by linarith)
  obtain ⟨KE, mE, hEt⟩ := tame_lawExponentAt (a := T.a) (ρA := T.ρA) (lam := T.lam) (f := f) (V := V) (law := law)
    hSum hfin hκ hK₂ fun Y' => gS l₁ hl eS t f F V Y' hf hF hV
  have hEt' := hEt.mono hLl
  obtain ⟨C, hC, hb⟩ := bumpDerivs_bounded hρ
  obtain ⟨-, hlaw, -, -⟩ := gF t f F V law hf hF hV hLw
  have ms := fun (l : ℝ) (h0 : 0 < l) (h1 : l ≤ L) => cutoffMean_eq_ratioMean (K := KE) (m := mE) (p := T.p)
    (Ψ := stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f V law) (E₀ := lawExponentAt T.a T.ρA T.lam f V law l) hRim hρ
    hT.cutoff h0 hEt'.nonneg (fun ζ hz => hlaw l ζ h0 (h1.trans (hLl.trans eF)) hz)
    (fun ζ hz => hEt'.bound0 l ζ h0 h1 hz) (hEt'.cont0 l h0 h1)
  have hw : ScaleWeights T.ballRadius L (lawExponentAt T.a T.ρA T.lam f V law)
      (fun l ζ => ColdStepAtMirrorFrames.cutoffWeight T.ballRadius T.p (l • ζ) *
        Real.exp (-lawExponentAt T.a T.ρA T.lam f V law l ζ))
      (gaussianMean T.a T.ρA T.lam f V law) := by
    refine ⟨fun l h0 h1 => (ms l h0 h1).1, fun l ζ h0 _ h2 => ?_, fun l ζ h0 _ h2 => ?_, ?_⟩
    · simp only [cutoffWeight_smul_eq_one hρ hT.cutoff h0 h2, one_mul]
    · simp only [cutoffWeight_smul_eq_zero h0 h2, zero_mul]
    · intro H H₀ K' m hm hbd hlim
      classical
      have h := gL t f F V law (fun l => if l ≤ L then H l else fun _ => 0) H₀ (max K' 0) m hf hF hV hLw
        (fun l h0 _ => by
          by_cases hlL : l ≤ L
          · simp only [if_pos hlL]
            exact hm l h0 hlL
          · simp only [if_neg hlL]
            exact measurable_const)
        (fun l ζ h0 _ hz => by
          have hq : 0 ≤ (1 + ‖ζ‖) ^ m := by positivity
          by_cases hlL : l ≤ L
          · simp only [if_pos hlL]
            exact (hbd l ζ h0 hlL hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
          · simp only [if_neg hlL, abs_zero]
            exact mul_nonneg (le_max_right _ _) hq)
        (fun ζ => by
          refine (hlim ζ).congr' ?_
          filter_upwards [Ioc_mem_nhdsGT hL₀] with l hl'
          simp only [if_pos hl'.2])
      refine h.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hL₀] with l hl'
      simp only [if_pos hl'.2]
      exact (ms l hl'.1 hl'.2).2 (H l)
  have hU := gaussianMean_scaleD1_eq_zero hEv Y T.a T.ρA T.lam f V law
  have diff := tendsto_secondDifference_mean hρ hL₀ hL₁ hC hb hEt' hOt hw hU
  rw [limit_eq_two_mul_coeff _ _ _ _ _ _ _ hU] at diff
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ → ℝ, M = fun l => observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l V :=
    ⟨_, rfl⟩
  have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  have hm : (fun l' => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) = M := by
    rw [hMdef]
    exact funext fun l' => bondDeriv_zero_order _ _ _ _
  have rg := k₁ l₁ hl e₁ t f F V Y law K Ob 0 Fin.elim0 Fin.elim0 hf hF hV hLw hK hO hX₀ (by norm_num)
  have bd := k₂ l₁ hl e₂ t f F V Y law K Ob 0 Fin.elim0 Fin.elim0 hf hF hV hLw hK hO hX₀
  rw [hm] at rg bd
  have rg₃ : ∀ l, 0 < l → l ≤ l₁ → ContDiffAt ℝ (3 : ℕ) M l := fun l a b => by simpa using rg l a b
  have B₀ : 0 ≤ C₂ * K := by positivity
  have b₃ : ∀ u, 0 < u → u ≤ l₁ → |iteratedDeriv 3 M u| ≤ C₂ * K := by
    intro u a b
    refine (bd 3 u (Or.inr ⟨by norm_num, le_rfl⟩) a b).trans ?_
    have h3 : Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ) := by positivity
      linarith
    calc _ ≤ C₂ * K * 1 := mul_le_mul_of_nonneg_left h3 B₀
      _ = _ := mul_one _
  have H₁ : ∀ u, 0 < u → u ≤ l₁ → HasDerivAt M (deriv M u) u := fun u a b =>
    ((rg₃ u a b).differentiableAt (by norm_num)).hasDerivAt
  have H₂ : ∀ u, 0 < u → u ≤ l₁ → HasDerivAt (deriv M) (iteratedDeriv 2 M u) u := fun u a b => by
    have h3 := hasDerivAt_iteratedDeriv (n := 1) ((rg₃ u a b).of_le (by norm_num) : ContDiffAt ℝ ((1 + 1 : ℕ)) M u)
    rwa [iteratedDeriv_one] at h3
  have H₃ : ∀ u, 0 < u → u ≤ l₁ → HasDerivAt (iteratedDeriv 2 M) (iteratedDeriv 3 M u) u := fun u a b =>
    hasDerivAt_iteratedDeriv (n := 2) (rg₃ u a b)
  have diff₂ : Tendsto (fun l => (M (3 * l / 2) + M (l / 2) - 2 * M l) / (l / 2) ^ 2) (𝓝[>] 0)
      (𝓝 (2 * observableSecondOrderCoeff T.a T.ρA T.lam f law Ob V)) := by
    refine diff.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * L / 3 by positivity)] with l hl'
    have hp : 0 < l := hl'.1
    have hq : l < 2 * L / 3 := hl'.2
    have m₁ := (ms (3 * l / 2) (by positivity) (by linarith)).2 fun ζ => Ob (3 * l / 2) ζ V
    have m₂ := (ms (l / 2) (by positivity) (by linarith)).2 fun ζ => Ob (l / 2) ζ V
    have m₃ := (ms l hp (by linarith)).2 fun ζ => Ob l ζ V
    rw [hMdef]
    simp only [observableMean, rescaledMean]
    rw [m₁, m₂, m₃]
  have close : ∀ l : ℝ, 0 < l → l ≤ 2 * l₁ / 3 →
      |iteratedDeriv 2 M l - (M (3 * l / 2) + M (l / 2) - 2 * M l) / (l / 2) ^ 2| ≤ C₂ * K * l := by
    intro l h0 h1
    have rng : ∀ u ∈ Icc (l - l / 2) (l + l / 2), 0 < u ∧ u ≤ l₁ := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have vary : ∀ u ∈ Icc (l - l / 2) (l + l / 2),
        |iteratedDeriv 2 M u - iteratedDeriv 2 M l| ≤ C₂ * K * (l / 2) := by
      intro u hu
      have hsub := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := iteratedDeriv 2 M)
        (f' := iteratedDeriv 3 M) (C := C₂ * K) (s := Icc (l - l / 2) (l + l / 2)) (x := l) (y := u)
        (fun x hx => (H₃ x (rng x hx).1 (rng x hx).2).hasDerivWithinAt)
        (fun x hx => by
          rw [Real.norm_eq_abs]
          exact b₃ x (rng x hx).1 (rng x hx).2)
        (convex_Icc _ _) ⟨by linarith, by linarith⟩ hu
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hsub
      refine hsub.trans (mul_le_mul_of_nonneg_left ?_ B₀)
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
    have h2 := abs_secondDifference_le (g := M) (g' := deriv M) (g'' := iteratedDeriv 2 M) (l := l) (s := l / 2)
      (L := iteratedDeriv 2 M l) (ε := C₂ * K * (l / 2)) (by positivity) (by positivity)
      (fun u hu => H₁ u (rng u hu).1 (rng u hu).2) (fun u hu => H₂ u (rng u hu).1 (rng u hu).2) vary
    have f₁ : l + l / 2 = 3 * l / 2 := by ring
    have f₂ : l - l / 2 = l / 2 := by ring
    simp only [f₁, f₂] at h2
    have hs : 0 < (l / 2) ^ 2 := by positivity
    have e : iteratedDeriv 2 M l - (M (3 * l / 2) + M (l / 2) - 2 * M l) / (l / 2) ^ 2 =
        -((M (3 * l / 2) + M (l / 2) - 2 * M l - iteratedDeriv 2 M l * (l / 2) ^ 2) / (l / 2) ^ 2) := by
      field_simp
      ring
    rw [e, abs_neg, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    refine h2.trans (le_of_eq ?_)
    ring
  have to₀ : Tendsto (fun l => iteratedDeriv 2 M l - (M (3 * l / 2) + M (l / 2) - 2 * M l) / (l / 2) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    have hu : Tendsto (fun l : ℝ => C₂ * K * l) (𝓝[>] 0) (𝓝 0) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have h2 : Tendsto (fun l : ℝ => C₂ * K * l) (𝓝 0) (𝓝 (C₂ * K * 0)) :=
        (continuous_const.mul continuous_id : Continuous fun l : ℝ => C₂ * K * l).tendsto 0
      rwa [mul_zero] at h2
    refine squeeze_zero_norm' ?_ hu
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 2 * l₁ / 3 by positivity)] with l hl'
    rw [Real.norm_eq_abs]
    exact close l hl'.1 hl'.2
  have res := to₀.add diff₂
  simp only [sub_add_cancel, zero_add] at res
  rw [hMdef] at res
  exact res
end ScaledVariables
end YangMills.Construction
end
