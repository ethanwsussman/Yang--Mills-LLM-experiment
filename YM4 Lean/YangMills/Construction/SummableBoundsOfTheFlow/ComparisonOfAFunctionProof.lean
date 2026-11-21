import YangMills.Construction.ColdStepAtMirrorFrames.ComparisonOnABlockProof
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonOfAFunction
import YangMills.Construction.SummableBoundsOfTheFlow.CovarianceOnTheOpenBalls
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongASegmentOfLaws
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open MeasureTheory ColdStepAtMirrorFrames ColdStepAtMirrorFrames.LocalCalculus ConvexObservables DensityMeans
namespace Freezing
namespace ExpectationComparison
variable {ι κ P : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype P]
  {ρ r c x : ℝ} {pos : ι → P} {D : P → P → ℝ} {z : P} {θ : BondField ι → ℝ}
theorem weightedSqNormNear_pushforwardField (j : κ → ι) (hj : Function.Injective j) (ξ : BondField κ) :
    weightedSqNormNear r pos D z (pushforwardField j ξ) =
      weightedSqNormNear r (fun k => pos (j k)) D z ξ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockComparison.weightedSqNormNear_pushforwardField <;> assumption
theorem sum_comp_injective_le (j : κ → ι) (hj : Function.Injective j) (w : ι → ℝ)
    (hw : ∀ b, 0 ≤ w b) : ∑ k, w (j k) ≤ ∑ b, w b := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockComparison.sum_comp_le_sum_of_injective <;> assumption
def restrictToBlock (j : κ → ι) (θ : BondField ι → ℝ) (ξ : BondField κ) : ℝ :=
  θ (pushforwardField j ξ)
theorem contDiffOn_restrictToBlock (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j)
    {n : WithTop ℕ∞} (hθ : ContDiffOn ℝ n θ (openPolyball ι ρ)) :
    ContDiffOn ℝ n (restrictToBlock j θ) (openPolyball κ ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockComparison.contDiffOn_restrictToBlock <;> assumption
theorem bondGradNorm_restrictToBlock_le (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j)
    (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ)) {ξ : BondField κ} (hξ : ξ ∈ openPolyball κ ρ) (k : κ) :
    bondGradNorm (restrictToBlock j θ) k ξ ≤ bondGradNorm θ (j k) (pushforwardField j ξ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockComparison.bondGradNorm_restrictToBlock_le <;> assumption
theorem bondGradNorm_restrictToBlock_le_decay (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j)
    (hT : IsLocalTermAt ρ r c x pos D z θ) {ξ : BondField κ} (hξ : ξ ∈ openPolyball κ ρ) (k : κ) :
    bondGradNorm (restrictToBlock j θ) k ξ ≤
      c * (x * Real.sqrt (weightedSqNormNear r (fun k => pos (j k)) D z ξ) + 1) *
        Real.exp (-(2 ^ 5 * r * D (pos (j k)) z)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockComparison.bondGradNorm_restrictToBlock_le_decay <;> assumption
theorem exists_bondGradNorm_restrictToBlock_bound (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hD : IsPseudoMetricOnBonds D) (j : κ → ι) (hj : Function.Injective j)
    (hT : IsLocalTermAt ρ r c x pos D z θ) :
    ∃ M, 0 ≤ M ∧ ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm (restrictToBlock j θ) k ξ ≤ M := by
  exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockComparison.exists_bondGradNorm_restrictToBlock_bound
    (P := P) hρ hr hc hx hD j hj hT
section CutoffLaw
variable {m S : ℝ} {p : ℝ → ℝ} {T : BondField ι → ℝ}
structure CutoffLawFacts (ρ : ℝ) (p : ℝ → ℝ) (T : BondField ι → ℝ) : Prop where
  isProbability : IsProbabilityMeasure (normalizedBallLaw (cutoffFactor ρ p) T)
  integral_eq : ∀ f : BondField ι → ℝ,
    ∫ η, f η ∂normalizedBallLaw (cutoffFactor ρ p) T = ballExpectation (cutoffFactor ρ p) T f
  ae_mem : ∀ᵐ η ∂normalizedBallLaw (cutoffFactor ρ p) T, η ∈ openPolyball ι ρ
theorem aestronglyMeasurable_of_continuousOn (hρ : 0 < ρ) (hl : CutoffLawFacts ρ p T)
    {f : BondField ι → ℝ} (hf : ContinuousOn f (openPolyball ι ρ)) :
    AEStronglyMeasurable f (normalizedBallLaw (cutoffFactor ρ p) T) := by
  have h := Measure.restrict_eq_self_of_ae_mem hl.ae_mem
  rw [← h]
  exact hf.aestronglyMeasurable (isOpen_openPolyball hρ).measurableSet
theorem integrable_of_isBoundedContinuousOn (hρ : 0 < ρ) (hl : CutoffLawFacts ρ p T)
    {f : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f) :
    Integrable f (normalizedBallLaw (cutoffFactor ρ p) T) := by
  haveI := hl.isProbability
  obtain ⟨c₀, M, hM⟩ := hf
  refine Integrable.of_bound (aestronglyMeasurable_of_continuousOn hρ hl c₀) M ?_
  filter_upwards [hl.ae_mem] with η hη
  simpa [Real.norm_eq_abs] using hM η hη
theorem integrable_sq_of_isBoundedContinuousOn (hρ : 0 < ρ) (hl : CutoffLawFacts ρ p T)
    {f : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f) :
    Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) := by
  have : IsBoundedContinuousOn ι ρ (fun η => f η * f η) := hf.mul hf
  refine (integrable_of_isBoundedContinuousOn hρ hl this).congr
    (Filter.Eventually.of_forall fun η => ?_)
  simp only
  ring
theorem integrable_bondGradNorm_sq (hρ : 0 < ρ) (hl : CutoffLawFacts ρ p T) {g : BondField ι → ℝ}
    (hg : ContDiffOn ℝ 1 g (openPolyball ι ρ)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm g b η ≤ M) (b : ι) :
    Integrable (fun η => bondGradNorm g b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
  integrable_sq_of_isBoundedContinuousOn hρ hl (isBoundedContinuousOn_bondGradNorm hρ hg hM b)
theorem integrable_of_integrable_sq (hρ : 0 < ρ) (hl : CutoffLawFacts ρ p T) {f : BondField ι → ℝ}
    (hf : ContinuousOn f (openPolyball ι ρ))
    (h2 : Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T)) :
    Integrable f (normalizedBallLaw (cutoffFactor ρ p) T) := by
  haveI := hl.isProbability
  have hm := aestronglyMeasurable_of_continuousOn hρ hl hf
  exact ((memLp_two_iff_integrable_sq hm).2 h2).integrable (by norm_num)
theorem integrable_mul_of_isBoundedContinuousOn (hρ : 0 < ρ) (hl : CutoffLawFacts ρ p T)
    {f g : BondField ι → ℝ} (hf : Integrable f (normalizedBallLaw (cutoffFactor ρ p) T))
    (hg : IsBoundedContinuousOn ι ρ g) :
    Integrable (fun η => f η * g η) (normalizedBallLaw (cutoffFactor ρ p) T) := by
  obtain ⟨c₀, M, hM⟩ := hg
  refine hf.mul_bdd (c := M) (aestronglyMeasurable_of_continuousOn hρ hl c₀) ?_
  filter_upwards [hl.ae_mem] with η hη
  simpa [Real.norm_eq_abs] using hM η hη
theorem ballCovariance_sum_right {α : Type} (hρ : 0 < ρ) (F : IsPositiveUnitalForm ρ p T)
    (hl : CutoffLawFacts ρ p T) {f : BondField ι → ℝ} (hc : ContinuousOn f (openPolyball ι ρ))
    (h2 : Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (s : Finset α) (g : α → BondField ι → ℝ) (hg : ∀ a ∈ s, IsBoundedContinuousOn ι ρ (g a)) :
    ballCovariance (cutoffFactor ρ p) T f (fun η => ∑ a ∈ s, g a η) =
      ∑ a ∈ s, ballCovariance (cutoffFactor ρ p) T f (g a) := by
  have hf := integrable_of_integrable_sq hρ hl hc h2
  unfold ballCovariance
  have e1 : ballExpectation (cutoffFactor ρ p) T (fun η => f η * ∑ a ∈ s, g a η) =
      ∑ a ∈ s, ballExpectation (cutoffFactor ρ p) T (fun η => f η * g a η) := by
    simp only [← hl.integral_eq, Finset.mul_sum]
    exact integral_finset_sum _ fun a ha => integrable_mul_of_isBoundedContinuousOn hρ hl hf (hg a ha)
  have e2 : ballExpectation (cutoffFactor ρ p) T (fun η => ∑ a ∈ s, g a η) =
      ∑ a ∈ s, ballExpectation (cutoffFactor ρ p) T (g a) := by
    simp only [← hl.integral_eq]
    exact integral_finset_sum _ fun a ha => integrable_of_isBoundedContinuousOn hρ hl (hg a ha)
  rw [e1, e2, Finset.mul_sum, Finset.sum_sub_distrib]
theorem ballCovariance_sub_right (hρ : 0 < ρ) (F : IsPositiveUnitalForm ρ p T) (hl : CutoffLawFacts ρ p T)
    {f g h : BondField ι → ℝ} (hc : ContinuousOn f (openPolyball ι ρ))
    (h2 : Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hg : IsBoundedContinuousOn ι ρ g) (hh : IsBoundedContinuousOn ι ρ h) :
    ballCovariance (cutoffFactor ρ p) T f (fun η => g η - h η) =
      ballCovariance (cutoffFactor ρ p) T f g - ballCovariance (cutoffFactor ρ p) T f h := by
  have hf := integrable_of_integrable_sq hρ hl hc h2
  unfold ballCovariance
  have e1 : ballExpectation (cutoffFactor ρ p) T (fun η => f η * (g η - h η)) =
      ballExpectation (cutoffFactor ρ p) T (fun η => f η * g η) -
        ballExpectation (cutoffFactor ρ p) T (fun η => f η * h η) := by
    simp only [← hl.integral_eq, mul_sub]
    exact integral_sub (integrable_mul_of_isBoundedContinuousOn hρ hl hf hg)
      (integrable_mul_of_isBoundedContinuousOn hρ hl hf hh)
  have e2 : ballExpectation (cutoffFactor ρ p) T (fun η => g η - h η) =
      ballExpectation (cutoffFactor ρ p) T g - ballExpectation (cutoffFactor ρ p) T h := by
    simp only [← hl.integral_eq]
    exact integral_sub (integrable_of_isBoundedContinuousOn hρ hl hg)
      (integrable_of_isBoundedContinuousOn hρ hl hh)
  rw [e1, e2]
  ring
theorem abs_ballCovariance_le_of_weights (hρ : 0 < ρ) (hr : 0 < r) (hD : IsPseudoMetricOnBonds D)
    (hm : 0 < m) (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
    (hcov : covarianceOpenBallsStatement)
    (hK : ∃ K, IsUniformlyConvexDecaying ρ m r (fun b b' => D (pos b) (pos b')) T K) (hp : IsCutoff ρ p)
    {f g : BondField ι → ℝ} {A : ℝ} {G : ι → ℝ}
    (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ)) (hg : ContDiffOn ℝ 1 g (openPolyball ι ρ))
    (hf2 : Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hg2 : Integrable (fun η => g η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hpf : ∀ b, Integrable (fun η => bondGradNorm f b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hpg : ∀ b, Integrable (fun η => bondGradNorm g b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hA : 0 ≤ A) (hG : ∀ b, 0 ≤ G b)
    (hfn : ∀ b, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm f b) ≤
      A * Real.exp (-(2 * r * D (pos b) z)))
    (hgn : ∀ b, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm g b) ≤ G b) :
    |ballCovariance (cutoffFactor ρ p) T f g| ≤
      m⁻¹ * A * S * ∑ b, G b * Real.exp (-(r / 2 * D (pos b) z)) := by
  obtain ⟨K, hKc⟩ := hK
  have hd : IsPseudoMetricOnBonds (fun b b' => D (pos b) (pos b')) :=
    ⟨fun b => hD.self _, fun b b' => hD.symm _ _, fun b b' b'' => hD.triangle _ _ _⟩
  have h := hcov ι ρ m r (fun b b' => D (pos b) (pos b')) T K p hρ hm hr.le hp hd hKc f g hf hg hf2 hg2
    hpf hpg
  refine h.trans ?_
  have hcn : ∀ (h : BondField ι → ℝ), 0 ≤ ballL2Norm (cutoffFactor ρ p) T h := fun h =>
    Real.sqrt_nonneg _
  have hin : ∀ b', ∑ b, Real.exp (-(2 * r * D (pos b) z)) * Real.exp (-(r * D (pos b) (pos b'))) ≤
      S * Real.exp (-(r / 2 * D (pos b') z)) := by
    intro b'
    have : ∀ b, Real.exp (-(2 * r * D (pos b) z)) * Real.exp (-(r * D (pos b) (pos b'))) ≤
        Real.exp (-(r / 4 * D (pos b) z)) * Real.exp (-(r / 2 * D (pos b') z)) := by
      intro b
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have t1 := hD.triangle (pos b') (pos b) z
      have t2 := pseudoMetric_nonneg hD (pos b) z
      have t3 := pseudoMetric_nonneg hD (pos b) (pos b')
      rw [hD.symm (pos b') (pos b)] at t1
      nlinarith
    refine (Finset.sum_le_sum fun b _ => this b).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hS z) (Real.exp_pos _).le
  have hmi : 0 ≤ m⁻¹ := by positivity
  rw [mul_assoc m⁻¹ A S, mul_assoc m⁻¹ (A * S)]
  apply mul_le_mul_of_nonneg_left _ hmi
  calc ∑ b, ∑ b', ballL2Norm (cutoffFactor ρ p) T (bondGradNorm f b) *
          Real.exp (-(r * D (pos b) (pos b'))) * ballL2Norm (cutoffFactor ρ p) T (bondGradNorm g b')
      ≤ ∑ b, ∑ b', (A * Real.exp (-(2 * r * D (pos b) z))) *
          Real.exp (-(r * D (pos b) (pos b'))) * G b' := by
        refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hfn b) (Real.exp_pos _).le) (hgn b')
          (hcn _) (by positivity)
    _ = ∑ b', G b' * (A * ∑ b, Real.exp (-(2 * r * D (pos b) z)) *
          Real.exp (-(r * D (pos b) (pos b')))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ ∑ b', G b' * (A * (S * Real.exp (-(r / 2 * D (pos b') z)))) := by
        refine Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left ?_ (hG b')
        exact mul_le_mul_of_nonneg_left (hin b') hA
    _ = A * S * ∑ b, G b * Real.exp (-(r / 2 * D (pos b) z)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
theorem abs_ballCovariance_le_of_centers (hρ : 0 < ρ) (hr : 0 < r) (hD : IsPseudoMetricOnBonds D)
    (hm : 0 < m) (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
    (hcov : covarianceOpenBallsStatement)
    (hK : ∃ K, IsUniformlyConvexDecaying ρ m r (fun b b' => D (pos b) (pos b')) T K) (hp : IsCutoff ρ p)
    {f g : BondField ι → ℝ} {A B : ℝ} {z z' : P}
    (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ)) (hg : ContDiffOn ℝ 1 g (openPolyball ι ρ))
    (hf2 : Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hg2 : Integrable (fun η => g η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hpf : ∀ b, Integrable (fun η => bondGradNorm f b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hpg : ∀ b, Integrable (fun η => bondGradNorm g b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfn : ∀ b, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm f b) ≤
      A * Real.exp (-(2 * r * D (pos b) z)))
    (hgn : ∀ b, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm g b) ≤
      B * Real.exp (-(2 * r * D (pos b) z'))) :
    |ballCovariance (cutoffFactor ρ p) T f g| ≤ m⁻¹ * A * S * (B * S * Real.exp (-(r / 2 * D z' z))) := by
  have h := abs_ballCovariance_le_of_weights (z := z) (G := fun b => B * Real.exp (-(2 * r * D (pos b) z')))
    hρ hr hD hm hS hcov hK hp hf hg hf2 hg2 hpf hpg hA (fun b => by positivity) hfn hgn
  refine h.trans ?_
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS z)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hnn : ∀ y w, 0 ≤ D y w := fun y w => pseudoMetric_nonneg hD y w
  calc ∑ b, B * Real.exp (-(2 * r * D (pos b) z')) * Real.exp (-(r / 2 * D (pos b) z))
      ≤ ∑ b, B * (Real.exp (-(r / 4 * D (pos b) z')) * Real.exp (-(r / 2 * D z' z))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hB
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have t1 := hD.triangle z' (pos b) z
        rw [hD.symm z' (pos b)] at t1
        have t2 := hnn (pos b) z'
        nlinarith
    _ = B * (∑ b, Real.exp (-(r / 4 * D (pos b) z'))) * Real.exp (-(r / 2 * D z' z)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ B * S * Real.exp (-(r / 2 * D z' z)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (hS z') hB
theorem ballCovariance_add_right (hρ : 0 < ρ) (hl : CutoffLawFacts ρ p T)
    {f g h : BondField ι → ℝ} (hc : ContinuousOn f (openPolyball ι ρ))
    (h2 : Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hg : IsBoundedContinuousOn ι ρ g) (hh : IsBoundedContinuousOn ι ρ h) :
    ballCovariance (cutoffFactor ρ p) T f (fun η => g η + h η) =
      ballCovariance (cutoffFactor ρ p) T f g + ballCovariance (cutoffFactor ρ p) T f h := by
  have hf := integrable_of_integrable_sq hρ hl hc h2
  unfold ballCovariance
  have e1 : ballExpectation (cutoffFactor ρ p) T (fun η => f η * (g η + h η)) =
      ballExpectation (cutoffFactor ρ p) T (fun η => f η * g η) +
        ballExpectation (cutoffFactor ρ p) T (fun η => f η * h η) := by
    simp only [← hl.integral_eq, mul_add]
    exact integral_add (integrable_mul_of_isBoundedContinuousOn hρ hl hf hg)
      (integrable_mul_of_isBoundedContinuousOn hρ hl hf hh)
  have e2 : ballExpectation (cutoffFactor ρ p) T (fun η => g η + h η) =
      ballExpectation (cutoffFactor ρ p) T g + ballExpectation (cutoffFactor ρ p) T h := by
    simp only [← hl.integral_eq]
    exact integral_add (integrable_of_isBoundedContinuousOn hρ hl hg)
      (integrable_of_isBoundedContinuousOn hρ hl hh)
  rw [e1, e2]
  ring
end CutoffLaw
section BlockLaw
variable {m S : ℝ} {p : ℝ → ℝ} {T : BondField κ → ℝ}
theorem ballL2Norm_bondGradNorm_le_of_majorant (hρ : 0 < ρ) {posκ : κ → P} (hx : 0 ≤ x)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p posκ D T)
    {G : BondField κ → ℝ} (hG : ContDiffOn ℝ 1 G (openPolyball κ ρ)) {M a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm G k ξ ≤ M) (z : P) {k : κ} {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ ξ ∈ openPolyball κ ρ, bondGradNorm G k ξ ≤
      a * (x * Real.sqrt (weightedSqNormNear r posκ D z ξ) + 1) * w) :
    ballL2Norm (cutoffFactor ρ p) T (bondGradNorm G k) ≤
      a * w * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) := by
  exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockComparison.ballL2Norm_bondGradNorm_le
    (P := P) hρ hx F Sz hG ha hM z hw h
end BlockLaw
theorem comparison_terms_le {lam S x c A ε e : ℝ} (hlam : 0 < lam) (hS : 0 ≤ S) (hx : 1 ≤ x)
    (hc : 1 ≤ c) (hA : 0 ≤ A) (hε : 0 ≤ ε) (he : 0 < e) :
    (x * lam / 4)⁻¹ * A * S * (c * ε * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) * S * S) +
        (x * lam / 4)⁻¹ * A * S *
          (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) * S * (S * e)) +
        (x * lam / 4)⁻¹ * A * S *
          (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) * S * (S * e)) ≤
      A * (Real.sqrt x)⁻¹ * c * comparisonConstant lam S * (ε + e) := by
  have hx0 : 0 < x := by linarith
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have hss : s ^ 2 = x := Real.sq_sqrt hx0.le
  set g := Real.sqrt (64 * S ^ 2 / lam + 2) with hg
  have hG : Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) ≤ s * g := by
    have h1 : 2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2 ≤ x * (64 * S ^ 2 / lam + 2) := by
      have : 2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) = x * (64 * S ^ 2 / lam) := by
        field_simp
        ring
      rw [this]
      nlinarith
    calc Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2)
        ≤ Real.sqrt (x * (64 * S ^ 2 / lam + 2)) := Real.sqrt_le_sqrt h1
      _ = s * g := by rw [Real.sqrt_mul hx0.le]
  set G := Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) with hGd
  have a1 : (x * lam / 4)⁻¹ * A * S * (c * ε * G * S * S) ≤
      (x * lam / 4)⁻¹ * A * S * (c * ε * (s * g) * S * S) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hS
    apply mul_le_mul_of_nonneg_right _ hS
    exact mul_le_mul_of_nonneg_left hG (by positivity)
  have a2 : (x * lam / 4)⁻¹ * A * S * (c * G * S * (S * e)) ≤
      (x * lam / 4)⁻¹ * A * S * (c * (s * g) * S * (S * e)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hS
    exact mul_le_mul_of_nonneg_left hG (by positivity)
  unfold comparisonConstant
  rw [← hg]
  have e1 : (x * lam / 4)⁻¹ * A * S * (c * ε * (s * g) * S * S) =
      A * s⁻¹ * c * (4 * S ^ 3 / lam * g) * ε := by
    rw [← hss]
    field_simp
  have e2 : (x * lam / 4)⁻¹ * A * S * (c * (s * g) * S * (S * e)) =
      A * s⁻¹ * c * (4 * S ^ 3 / lam * g) * e := by
    rw [← hss]
    field_simp
  have hq : 0 ≤ A * s⁻¹ * c * (4 * S ^ 3 / lam * g) * ε := by positivity
  have : A * s⁻¹ * c * (8 * S ^ 3 / lam * g) * (ε + e) =
      2 * (A * s⁻¹ * c * (4 * S ^ 3 / lam * g) * ε) +
        2 * (A * s⁻¹ * c * (4 * S ^ 3 / lam * g) * e) := by
    ring
  rw [this]
  linarith
end ExpectationComparison
set_option maxHeartbeats 1000000 in
open ExpectationComparison in
theorem expectationComparisonBound_holds (hseg : WeightedMeanDiffLeOfDerivBound)
    (hgood : AdmissiblePotentialStability) (hsz : AdmissibleMomentBoundsHold)
    (hmc : CutoffExpectationIsPositiveForm) (hcov : covarianceOpenBallsStatement)
    (hlaw : normalizedBallLawIsProbabilityStatement) : expectationComparisonBound := by
  intro ι ι' κ P P' _ _ _ _ _ _ _ _ _ _ ρ r S lam x c ε R Aₐ B p pos D Ψ θ Y pos' D' Ψ' θ' Y' j j' M M' φ
    Hb Hb' hρ hr hlam hx hc hε hR hA0 hp hD hD' hΨ hΨ' hS hSp hS2 hSp2 hθ hsum hθ' hsum' hj hj' hdist hY
    hfar hfar' hcomp hHi hHi' hstep
  have hx0 : 0 < x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hm0 : 0 < x * lam / 4 := by positivity
  have h2m : 2 * (x * lam / 4) ≤ x * lam := by nlinarith [mul_pos hx0 hlam]
  have hd : IsPseudoMetricOnBonds (fun b b' => D (pos b) (pos b')) :=
    ⟨fun b => hD.self _, fun b b' => hD.symm _ _, fun b b' b'' => hD.triangle _ _ _⟩
  have hd' : IsPseudoMetricOnBonds (fun b b' => D' (pos' b) (pos' b')) :=
    ⟨fun b => hD'.self _, fun b b' => hD'.symm _ _, fun b b' b'' => hD'.triangle _ _ _⟩
  have hdk : IsPseudoMetricOnBonds (fun k k' => D (pos (j k)) (pos (j k'))) :=
    ⟨fun b => hD.self _, fun b b' => hD.symm _ _, fun b b' b'' => hD.triangle _ _ _⟩
  have hSn : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS Y)
  have gA := (hgood ι ρ (x * lam / 4) r (x * lam) _ hρ hm0 hr.le hd h2m).2.2.2 κ j Ψ hj hΨ
  have gB := (hgood ι' ρ (x * lam / 4) r (x * lam) _ hρ hm0 hr.le hd' h2m).2.2.2 κ j' Ψ' hj' hΨ'
  have ed : (fun k k' => D' (pos' (j' k)) (pos' (j' k'))) = fun k k' => D (pos (j k)) (pos (j k')) := by
    funext k k'
    exact (hdist k k').symm
  simp only [ed] at gB
  have hsg := (hgood κ ρ (x * lam / 4) r (x * lam) _ hρ hm0 hr.le hdk h2m).1
  have cA : Continuous (fun ξ => Ψ (pushforwardField j ξ)) := by
    obtain ⟨K, hK, _⟩ := gA
    exact hK.smooth.continuous
  have cB : Continuous (fun ξ => Ψ' (pushforwardField j' ξ)) := by
    obtain ⟨K, hK, _⟩ := gB
    exact hK.smooth.continuous
  set A := fun ξ => Ψ (pushforwardField j ξ) with hA
  set Bf := fun ξ => Ψ' (pushforwardField j' ξ) with hB
  have hSk : ∀ z, ∑ k, Real.exp (-(r / 4 * D (pos (j k)) z)) ≤ S := fun z =>
    (sum_comp_injective_le j hj (fun b => Real.exp (-(r / 4 * D (pos b) z)))
      fun b => (Real.exp_pos _).le).trans (hS z)
  have hSk' : ∀ z, ∑ k, Real.exp (-(r / 4 * D' (pos' (j' k)) z)) ≤ S := fun z =>
    (sum_comp_injective_le j' hj' (fun b => Real.exp (-(r / 4 * D' (pos' b) z)))
      fun b => (Real.exp_pos _).le).trans (hS2 z)
  have hbdd : ∀ f : BondField κ → ℝ, Continuous f → ∃ M, ∀ η ∈ openPolyball κ ρ, |f η| ≤ M := by
    intro f hf
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : BondField κ) ρ).exists_bound_of_continuousOn
      hf.continuousOn
    refine ⟨M, fun η hη => ?_⟩
    have : η ∈ Metric.closedBall (0 : BondField κ) ρ := by
      rw [openPolyball_eq_ball hρ] at hη
      exact Metric.ball_subset_closedBall hη
    simpa using hM η this
  obtain ⟨N₂, hN₂⟩ := hbdd A cA
  obtain ⟨N₃, hN₃⟩ := hbdd Bf cB
  obtain ⟨-, -, -, -, -, hw0, hwi, hwp, -, hwne, -⟩ :=
    hlaw κ ρ p (fun _ => 0) hρ hp continuous_const
  set w : BondField κ → ℝ := radialWeightProd (cutoffFactor ρ p) with hw
  have hdw : ∀ η, ballDensity (cutoffFactor ρ p) (fun _ => (0 : ℝ)) η = w η := by
    intro η
    simp [ballDensity, hw]
  have hmeas : MeasurableSet (openPolyball κ ρ) := (isOpen_openPolyball hρ).measurableSet
  have hconv : ∀ Φ f : BondField κ → ℝ,
      weightedMean volume w Φ f = ballExpectation (cutoffFactor ρ p) Φ f := fun _ _ => rfl
  have key := hseg (BondField κ) volume (openPolyball κ ρ) w A Bf Hb Hb' (max N₂ N₃)
    (B + Aₐ * (Real.sqrt x)⁻¹ * c * comparisonConstant lam S * (ε + Real.exp (-(r * R / 32)))) hmeas
    (fun η => by simpa [hdw] using hw0 η)
    (fun η hη => by
      by_contra hne
      have : ballDensity (cutoffFactor ρ p) (fun _ => (0 : ℝ)) η ≠ 0 := by
        rw [hdw]; exact hne
      exact hη ((hwne η).1 this))
    (by rw [← funext hdw]; exact hwi) (by
      have e : ∫ η, w η = ∫ η, ballDensity (cutoffFactor ρ p) (fun _ => (0 : ℝ)) η :=
        integral_congr_ae (Filter.Eventually.of_forall fun η => (hdw η).symm)
      rw [e]
      exact hwp)
    (cA.continuousOn.aestronglyMeasurable hmeas) (cB.continuousOn.aestronglyMeasurable hmeas)
    (fun η hη => (hN₂ η hη).trans (le_max_left _ _)) (fun η hη => (hN₃ η hη).trans (le_max_right _ _))
    hHi hHi' ?_
  · simpa only [hconv] using key
  intro v hv0 hv1
  have hv1' : 0 ≤ 1 - v := by linarith
  set T := segmentInterpolant A Bf v with hT
  have gT := hsg A Bf v gA gB hv0 hv1
  have cT : Continuous T := by
    obtain ⟨K, hK, _⟩ := gT
    exact hK.smooth.continuous
  have hKT : ∃ K, IsUniformlyConvexDecaying ρ (x * lam / 4) r
      (fun k k' => D (pos (j k)) (pos (j k'))) T K := by
    obtain ⟨K, hK, _⟩ := gT
    exact ⟨K, hK⟩
  have F := hmc κ ρ p T hρ hp cT
  have Sz := hsz κ P ρ (x * lam / 4) r S p (fun k => pos (j k)) D T hρ hm0 hr hp hD gT hSk
  have gT' : IsAdmissiblePotential ρ (x * lam / 4) r
      (fun k k' => D' (pos' (j' k)) (pos' (j' k'))) T := by
    rw [ed]
    exact gT
  have hKT' : ∃ K, IsUniformlyConvexDecaying ρ (x * lam / 4) r
      (fun k k' => D' (pos' (j' k)) (pos' (j' k'))) T K := by
    obtain ⟨K, hK, _⟩ := gT'
    exact ⟨K, hK⟩
  have Sz' := hsz κ P' ρ (x * lam / 4) r S p (fun k => pos' (j' k)) D' T hρ hm0 hr hp hD' gT' hSk'
  obtain ⟨l1, l2, l3, l4, -⟩ := hlaw κ ρ p T hρ hp cT
  have hl : CutoffLawFacts ρ p T := ⟨l1, l2, l4⟩
  obtain ⟨gH, gH', hBv⟩ := hstep v hv0 hv1
  set G := Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) with hGd
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  set e := Real.exp (-(r * R / 32)) with hed
  have he : 0 < e := Real.exp_pos _
  have hnn := fun y w => pseudoMetric_nonneg hD y w
  have hnn' := fun y w => pseudoMetric_nonneg hD' y w
  set Δ : {z // z ∈ M} → BondField κ → ℝ := fun z ζ =>
    θ' (φ z).1 (pushforwardField j' ζ) - θ z.1 (pushforwardField j ζ) with hΔ
  have hΔs : ∀ z, ContDiffOn ℝ 1 (Δ z) (openPolyball κ ρ) := fun z =>
    (contDiffOn_restrictToBlock hρ j' hj' (contDiffOn_one_of_two (hθ' (φ z).1).smooth)).sub
      (contDiffOn_restrictToBlock hρ j hj (contDiffOn_one_of_two (hθ z.1).smooth))
  have hΔb : ∀ z, ∃ Mz, 0 ≤ Mz ∧ ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm (Δ z) k ξ ≤ Mz := by
    intro z
    obtain ⟨A₁, hA₁0, hA₁⟩ :=
      exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD' j' hj' (hθ' (φ z).1)
    obtain ⟨A₂, hA₂0, hA₂⟩ :=
      exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD j hj (hθ z.1)
    refine ⟨A₁ + A₂, by positivity, fun ξ hξ k => ?_⟩
    have e1 : Δ z = fun ζ => 1 * restrictToBlock j' (θ' (φ z).1) ζ + (-1) * restrictToBlock j (θ z.1) ζ := by
      funext ζ
      simp only [hΔ, restrictToBlock]
      ring
    rw [e1]
    have := bondGradNorm_linear_combination_le hρ
      (contDiffOn_restrictToBlock hρ j' hj' (contDiffOn_one_of_two (hθ' (φ z).1).smooth))
      (contDiffOn_restrictToBlock hρ j hj (contDiffOn_one_of_two (hθ z.1).smooth)) 1 (-1) hξ k
    have h1 := hA₁ ξ hξ k
    have h2 := hA₂ ξ hξ k
    simp only [abs_one, abs_neg, one_mul] at this
    simp only [one_mul]
    linarith
  have hΔn : ∀ z, IsBoundedContinuousOn κ ρ (Δ z) := fun z => by
    obtain ⟨Mz, h0, hMz⟩ := hΔb z
    exact isBoundedContinuousOn_of_bondGradNorm_le hρ (hΔs z) h0 hMz
  have hgs : ∀ z, ContDiffOn ℝ 1 (restrictToBlock j (θ z)) (openPolyball κ ρ) := fun z =>
    contDiffOn_restrictToBlock hρ j hj (contDiffOn_one_of_two (hθ z).smooth)
  have hgs' : ∀ z, ContDiffOn ℝ 1 (restrictToBlock j' (θ' z)) (openPolyball κ ρ) := fun z =>
    contDiffOn_restrictToBlock hρ j' hj' (contDiffOn_one_of_two (hθ' z).smooth)
  have hgb := fun z => exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD j hj (hθ z)
  have hgb' := fun z => exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD' j' hj' (hθ' z)
  have hgn : ∀ z, IsBoundedContinuousOn κ ρ (restrictToBlock j (θ z)) := fun z => by
    obtain ⟨Mz, h0, hMz⟩ := hgb z
    exact isBoundedContinuousOn_of_bondGradNorm_le hρ (hgs z) h0 hMz
  have hgn' : ∀ z, IsBoundedContinuousOn κ ρ (restrictToBlock j' (θ' z)) := fun z => by
    obtain ⟨Mz, h0, hMz⟩ := hgb' z
    exact isBoundedContinuousOn_of_bondGradNorm_le hρ (hgs' z) h0 hMz
  have hsplit : ∀ ξ ∈ openPolyball κ ρ, Bf ξ - A ξ =
      ((∑ z, Δ z ξ) + ∑ z ∈ M'ᶜ, restrictToBlock j' (θ' z) ξ) - ∑ z ∈ Mᶜ, restrictToBlock j (θ z) ξ := by
    intro ξ hξ
    have h1 := hsum _ (pushforwardField_mem_openPolyball hρ j hj hξ)
    have h2 := hsum' _ (pushforwardField_mem_openPolyball hρ j' hj' hξ)
    simp only [hA, hB, h1, h2, hΔ, restrictToBlock, Finset.sum_sub_distrib]
    have s1 := Finset.sum_add_sum_compl M (fun z => θ z (pushforwardField j ξ))
    have s2 := Finset.sum_add_sum_compl M' (fun z => θ' z (pushforwardField j' ξ))
    have s3 : ∑ z : {z // z ∈ M}, θ z.1 (pushforwardField j ξ) = ∑ z ∈ M, θ z (pushforwardField j ξ) :=
      Finset.sum_coe_sort M (fun z => θ z (pushforwardField j ξ))
    have s4 : ∑ z : {z // z ∈ M}, θ' (φ z).1 (pushforwardField j' ξ) =
        ∑ z ∈ M', θ' z (pushforwardField j' ξ) := by
      rw [Equiv.sum_comp φ (fun z : {z // z ∈ M'} => θ' z.1 (pushforwardField j' ξ))]
      exact Finset.sum_coe_sort M' (fun z => θ' z (pushforwardField j' ξ))
    rw [s3, s4, ← s1, ← s2]
    ring
  have far : ∀ {d : ℝ}, R / 8 ≤ d → Real.exp (-(r / 2 * d)) ≤ Real.exp (-(r / 4 * d)) * e := by
    intro d hd
    rw [hed, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h3 : (R / 8) * r ≤ d * r := mul_le_mul_of_nonneg_right hd hr.le
    nlinarith
  have covb : ∀ f : BondField κ → ℝ, HasFrozenGradientBound ρ r Aₐ p (fun k => pos (j k)) D Y T f →
      |ballCovariance (cutoffFactor ρ p) T f (fun ξ => Bf ξ - A ξ)| ≤
        (x * lam / 4)⁻¹ * Aₐ * S * (c * ε * G * S * S) +
          (x * lam / 4)⁻¹ * Aₐ * S * (c * G * S * (S * e)) +
          (x * lam / 4)⁻¹ * Aₐ * S * (c * G * S * (S * e)) := by
    intro f gf
    have sqf : Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
      (l3 _).2 gf.sq_integrable
    have pqf : ∀ k, Integrable (fun η => bondGradNorm f k η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
      fun k => (l3 _).2 (gf.grad_sq_integrable k)
    have hcf := gf.smooth.continuousOn
    have hHn := gf.grad_norm_le
    have hHn' : ∀ k, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm f k) ≤
        Aₐ * Real.exp (-(2 * r * D' (pos' (j' k)) Y')) := by
      intro k
      rw [← hY k]
      exact hHn k
    have e1 : ballCovariance (cutoffFactor ρ p) T f (fun ξ => Bf ξ - A ξ) =
        ((∑ z, ballCovariance (cutoffFactor ρ p) T f (Δ z)) +
          ∑ z ∈ M'ᶜ, ballCovariance (cutoffFactor ρ p) T f (restrictToBlock j' (θ' z))) -
          ∑ z ∈ Mᶜ, ballCovariance (cutoffFactor ρ p) T f (restrictToBlock j (θ z)) := by
      have n1 : IsBoundedContinuousOn κ ρ (fun ξ => ∑ z, Δ z ξ) :=
        IsBoundedContinuousOn.sum _ _ fun z _ => hΔn z
      have n2 : IsBoundedContinuousOn κ ρ (fun ξ => ∑ z ∈ M'ᶜ, restrictToBlock j' (θ' z) ξ) :=
        IsBoundedContinuousOn.sum _ _ fun z _ => hgn' z
      have n3 : IsBoundedContinuousOn κ ρ (fun ξ => ∑ z ∈ Mᶜ, restrictToBlock j (θ z) ξ) :=
        IsBoundedContinuousOn.sum _ _ fun z _ => hgn z
      rw [ballCovariance_congr F (fun _ _ => rfl) hsplit,
        ballCovariance_sub_right hρ F hl hcf sqf (n1.add n2) n3,
        ballCovariance_add_right hρ hl hcf sqf n1 n2,
        ballCovariance_sum_right hρ F hl hcf sqf _ _ fun z _ => hΔn z,
        ballCovariance_sum_right hρ F hl hcf sqf _ _ fun z _ => hgn' z,
        ballCovariance_sum_right hρ F hl hcf sqf _ _ fun z _ => hgn z]
    have c1 : ∀ z : {z // z ∈ M}, |ballCovariance (cutoffFactor ρ p) T f (Δ z)| ≤
        (x * lam / 4)⁻¹ * Aₐ * S * (c * ε * G * S * Real.exp (-(r / 4 * D z.1 Y))) := by
      intro z
      obtain ⟨Mz, h0, hMz⟩ := hΔb z
      have h1 := abs_ballCovariance_le_of_centers (B := c * ε * G) (z := Y) (z' := z.1) hρ hr hD hm0 hSk
        hcov hKT hp gf.smooth (hΔs z) sqf (integrable_sq_of_isBoundedContinuousOn hρ hl (hΔn z)) pqf
        (integrable_bondGradNorm_sq hρ hl (hΔs z) h0 hMz) hA0 (by positivity) hHn (fun k => by
          have := ballL2Norm_le_of_near_majorant (a := c * ε * Real.exp (-(2 * r * D (pos (j k)) z.1)))
            hρ F Sz (isBoundedContinuousOn_bondGradNorm hρ (hΔs z) hMz k) (by positivity) hx0.le z.1
            (fun ξ hξ => by
              rw [abs_of_nonneg (bondGradNorm_nonneg _ k ξ)]
              refine (hcomp z ξ hξ k).trans (le_of_eq ?_)
              ring)
          refine this.trans (le_of_eq ?_)
          ring)
      refine h1.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have := hnn z.1 Y
      nlinarith
    have c2 : ∀ z ∈ Mᶜ, |ballCovariance (cutoffFactor ρ p) T f (restrictToBlock j (θ z))| ≤
        (x * lam / 4)⁻¹ * Aₐ * S * (c * G * S * (Real.exp (-(r / 4 * D z Y)) * e)) := by
      intro z hz
      obtain ⟨Mz, h0, hMz⟩ := hgb z
      have h1 := abs_ballCovariance_le_of_centers (B := c * G) (z := Y) (z' := z) hρ hr hD hm0 hSk hcov
        hKT hp gf.smooth (hgs z) sqf (integrable_sq_of_isBoundedContinuousOn hρ hl (hgn z)) pqf
        (integrable_bondGradNorm_sq hρ hl (hgs z) h0 hMz) hA0 (by positivity) hHn (fun k => by
          have key := ballL2Norm_bondGradNorm_le_of_majorant (a := c)
            (w := Real.exp (-(2 ^ 5 * r * D (pos (j k)) z))) hρ hx0.le F Sz (hgs z) hc0 hMz z
            (Real.exp_pos _).le (fun ξ hξ => bondGradNorm_restrictToBlock_le_decay hρ j hj (hθ z) hξ k)
          refine key.trans ?_
          have hw : Real.exp (-(2 ^ 5 * r * D (pos (j k)) z)) ≤ Real.exp (-(2 * r * D (pos (j k)) z)) := by
            apply Real.exp_le_exp.mpr
            have := hnn (pos (j k)) z
            nlinarith
          calc c * Real.exp (-(2 ^ 5 * r * D (pos (j k)) z)) * G
              = c * G * Real.exp (-(2 ^ 5 * r * D (pos (j k)) z)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity))
      refine h1.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact far (hfar z (by simpa using hz))
    have c3 : ∀ z ∈ M'ᶜ, |ballCovariance (cutoffFactor ρ p) T f (restrictToBlock j' (θ' z))| ≤
        (x * lam / 4)⁻¹ * Aₐ * S * (c * G * S * (Real.exp (-(r / 4 * D' z Y')) * e)) := by
      intro z hz
      obtain ⟨Mz, h0, hMz⟩ := hgb' z
      have h1 := abs_ballCovariance_le_of_centers (B := c * G) (z := Y') (z' := z) hρ hr hD' hm0 hSk' hcov
        hKT' hp gf.smooth (hgs' z) sqf (integrable_sq_of_isBoundedContinuousOn hρ hl (hgn' z)) pqf
        (integrable_bondGradNorm_sq hρ hl (hgs' z) h0 hMz) hA0 (by positivity) hHn' (fun k => by
          have key := ballL2Norm_bondGradNorm_le_of_majorant (a := c)
            (w := Real.exp (-(2 ^ 5 * r * D' (pos' (j' k)) z))) hρ hx0.le F Sz' (hgs' z) hc0 hMz z
            (Real.exp_pos _).le
            (fun ξ hξ => bondGradNorm_restrictToBlock_le_decay hρ j' hj' (hθ' z) hξ k)
          refine key.trans ?_
          have hw : Real.exp (-(2 ^ 5 * r * D' (pos' (j' k)) z)) ≤
              Real.exp (-(2 * r * D' (pos' (j' k)) z)) := by
            apply Real.exp_le_exp.mpr
            have := hnn' (pos' (j' k)) z
            nlinarith
          calc c * Real.exp (-(2 ^ 5 * r * D' (pos' (j' k)) z)) * G
              = c * G * Real.exp (-(2 ^ 5 * r * D' (pos' (j' k)) z)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity))
      refine h1.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact far (hfar' z (by simpa using hz))
    have s1 : ∑ z : {z // z ∈ M}, |ballCovariance (cutoffFactor ρ p) T f (Δ z)| ≤
        (x * lam / 4)⁻¹ * Aₐ * S * (c * ε * G * S * S) := by
      refine (Finset.sum_le_sum fun z _ => c1 z).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : ∑ z : {z // z ∈ M}, Real.exp (-(r / 4 * D z.1 Y)) =
          ∑ z ∈ M, Real.exp (-(r / 4 * D z Y)) :=
        Finset.sum_coe_sort M (fun z => Real.exp (-(r / 4 * D z Y)))
      rw [h1]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
        fun z _ _ => (Real.exp_pos _).le).trans (hSp Y)
    have s2 : ∑ z ∈ Mᶜ, |ballCovariance (cutoffFactor ρ p) T f (restrictToBlock j (θ z))| ≤
        (x * lam / 4)⁻¹ * Aₐ * S * (c * G * S * (S * e)) := by
      refine (Finset.sum_le_sum c2).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ he.le
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Mᶜ)
        fun z _ _ => (Real.exp_pos _).le).trans (hSp Y)
    have s3 : ∑ z ∈ M'ᶜ, |ballCovariance (cutoffFactor ρ p) T f (restrictToBlock j' (θ' z))| ≤
        (x * lam / 4)⁻¹ * Aₐ * S * (c * G * S * (S * e)) := by
      refine (Finset.sum_le_sum c3).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ he.le
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M'ᶜ)
        fun z _ _ => (Real.exp_pos _).le).trans (hSp2 Y')
    rw [e1]
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · exact (Finset.abs_sum_le_sum_abs _ _).trans s1
    · exact (Finset.abs_sum_le_sum_abs _ _).trans s3
    · exact (Finset.abs_sum_le_sum_abs _ _).trans s2
  have hnum := comparison_terms_le (e := e) (A := Aₐ) (ε := ε) hlam hSn hx hc hA0 hε he
  set K' := Aₐ * (Real.sqrt x)⁻¹ * c * comparisonConstant lam S * (ε + e) with hK'
  have b1 : |ballCovariance (cutoffFactor ρ p) T Hb (fun ξ => Bf ξ - A ξ)| ≤ K' := (covb Hb gH).trans hnum
  have b2 : |ballCovariance (cutoffFactor ρ p) T Hb' (fun ξ => Bf ξ - A ξ)| ≤ K' :=
    (covb Hb' gH').trans hnum
  have nice_g : IsBoundedContinuousOn κ ρ (fun ξ => Bf ξ - A ξ) :=
    ⟨(cB.sub cA).continuousOn, |N₃| + |N₂|, fun η hη => by
      have a1 := hN₃ η hη
      have a2 := hN₂ η hη
      have a3 := abs_sub (Bf η) (A η)
      have a4 := le_abs_self N₂
      have a5 := le_abs_self N₃
      linarith⟩
  have sq1 : Integrable (fun η => Hb η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
    (l3 _).2 gH.sq_integrable
  have sq2 : Integrable (fun η => Hb' η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
    (l3 _).2 gH'.sq_integrable
  have iH := integrable_of_integrable_sq hρ hl gH.smooth.continuousOn sq1
  have iC := integrable_of_integrable_sq hρ hl gH'.smooth.continuousOn sq2
  have iHg := integrable_mul_of_isBoundedContinuousOn hρ hl iH nice_g
  have iCg := integrable_mul_of_isBoundedContinuousOn hρ hl iC nice_g
  have eMean : ballExpectation (cutoffFactor ρ p) T (segmentPoint Hb Hb' v) =
      v * ballExpectation (cutoffFactor ρ p) T Hb' + (1 - v) * ballExpectation (cutoffFactor ρ p) T Hb := by
    simp only [← l2]
    unfold segmentPoint
    rw [integral_add (iC.const_mul v) (iH.const_mul (1 - v)), integral_const_mul, integral_const_mul]
  have eProd : ballExpectation (cutoffFactor ρ p) T
      (fun η => segmentPoint Hb Hb' v η * (Bf η - A η)) =
      v * ballExpectation (cutoffFactor ρ p) T (fun η => Hb' η * (Bf η - A η)) +
        (1 - v) * ballExpectation (cutoffFactor ρ p) T (fun η => Hb η * (Bf η - A η)) := by
    simp only [← l2]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iCg.const_mul v) (iHg.const_mul (1 - v))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [segmentPoint]
    ring
  have eSlope : meanDerivAlongSegment volume w A Bf Hb Hb' v =
      ballExpectation (cutoffFactor ρ p) T (fun η => Hb' η - Hb η) -
        (v * ballCovariance (cutoffFactor ρ p) T Hb' (fun η => Bf η - A η) +
          (1 - v) * ballCovariance (cutoffFactor ρ p) T Hb (fun η => Bf η - A η)) := by
    have hTs : segmentPoint A Bf v = T := rfl
    unfold meanDerivAlongSegment
    rw [hTs]
    simp only [hconv]
    rw [eProd, eMean]
    unfold ballCovariance
    ring
  rw [eSlope]
  have hcv : |v * ballCovariance (cutoffFactor ρ p) T Hb' (fun η => Bf η - A η) +
      (1 - v) * ballCovariance (cutoffFactor ρ p) T Hb (fun η => Bf η - A η)| ≤ K' := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_nonneg hv1']
    nlinarith
  exact (abs_sub _ _).trans (add_le_add hBv hcv)
end Freezing
end YangMills.Construction
end
