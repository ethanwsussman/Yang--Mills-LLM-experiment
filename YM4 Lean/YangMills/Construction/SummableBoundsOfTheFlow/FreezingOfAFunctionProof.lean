import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOnOneTorusProof
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonOfAFunctionProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open ColdStepAtMirrorFrames ColdStepAtMirrorFrames.LocalCalculus ConvexObservables DensityMeans
namespace Freezing
section LocalGradients
variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P] {ρ r c x : ℝ} {pos : ι → P}
  {D : P → P → ℝ} {z : P} {θ : BondField ι → ℝ}
def restrictedObservable (Λ : Finset ι) (θ : BondField ι → ℝ) (η : BondField ι) : ℝ :=
  θ (restrictToBonds Λ η)
theorem norm_restrictToBonds_le (Λ : Finset ι) (η : BondField ι) (b : ι) :
    ‖restrictToBonds Λ η b‖ ≤ ‖η b‖ := by
  by_cases h : b ∈ Λ <;> simp [restrictToBonds, h]
theorem majorant_mono {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) {w : ℝ} (hw : 0 ≤ w) (z : P)
    {ζ η : BondField ι} (h : ∀ b, ‖ζ b‖ ≤ ‖η b‖) :
    c * (x * Real.sqrt (weightedSqNormNear r pos D z ζ) + 1) * w ≤
      c * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) * w := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.majorant_mono <;> assumption
def restrictionDefect (Λ : Finset ι) (θ : BondField ι → ℝ) (η : BondField ι) : ℝ :=
  θ η - restrictedObservable Λ θ η
theorem contDiffOn_restrictionDefect (hρ : 0 < ρ) (Λ : Finset ι) {n : WithTop ℕ∞}
    (hθ : ContDiffOn ℝ n θ (openPolyball ι ρ)) :
    ContDiffOn ℝ n (restrictionDefect Λ θ) (openPolyball ι ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.contDiffOn_restrictionDefect <;> assumption
theorem bondGradNorm_restrictionDefect_le (hρ : 0 < ρ) (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ))
    (Λ : Finset ι) {η : BondField ι} (hη : η ∈ openPolyball ι ρ) (b : ι) :
    bondGradNorm (restrictionDefect Λ θ) b η ≤
      bondGradNorm θ b η + bondGradNorm (restrictedObservable Λ θ) b η := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.bondGradNorm_restrictionDefect_le <;> assumption
theorem bondGradNorm_restrictionDefect_le_of_not_mem (hρ : 0 < ρ)
    (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ)) (Λ : Finset ι)
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) {b : ι} (hb : b ∉ Λ) :
    bondGradNorm (restrictionDefect Λ θ) b η ≤ bondGradNorm θ b η := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.bondGradNorm_restrictionDefect_le_of_not_mem <;> assumption
theorem bondGradNorm_restrictionDefect_le_of_mem (hρ : 0 < ρ) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hT : IsLocalTermAt ρ r c x pos D z θ)
    (Λ : Finset ι) {η : BondField ι} (hη : η ∈ openPolyball ι ρ) {b : ι} (hb : b ∈ Λ) :
    bondGradNorm (restrictionDefect Λ θ) b η ≤ ∑ b', (if b' ∈ Λ then 0 else
      c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z)))) * ‖η b'‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.bondGradNorm_restrictionDefect_le_of_mem <;> assumption
theorem exp_neg_le_mul_exp_neg {r R s d : ℝ} (h : r * R / 16 ≤ (s - r / 4) * d) :
    Real.exp (-(s * d)) ≤ Real.exp (-(r / 4 * d)) * Real.exp (-(r * R / 16)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.exp_neg_le_mul_exp_neg <;> assumption
section Measure
variable {m S lam R : ℝ} {p : ℝ → ℝ} {T : BondField ι → ℝ} {H : BondField ι → ℝ} {Y : P}
  {Λ : Finset ι}
theorem ballL2Norm_bondGradNorm_le_of_majorant (hρ : 0 < ρ) (hr : 0 < r) (hx : 0 ≤ x)
    (hD : IsPseudoMetricOnBonds D)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    {G : BondField ι → ℝ} (hG : ContDiffOn ℝ 1 G (openPolyball ι ρ)) {M a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm G b η ≤ M) (z : P) {b : ι} {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ η ∈ openPolyball ι ρ, bondGradNorm G b η ≤
      a * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) * w) :
    ballL2Norm (cutoffFactor ρ p) T (bondGradNorm G b) ≤
      a * w * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) := by exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.ballL2Norm_bondGradNorm_le_of_majorant (P := P) (pos := pos) (D := D) hρ hr hx hD F Sz hG ha hM z hw h
theorem exists_bondGradNorm_restrictionDefect_bound (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hD : IsPseudoMetricOnBonds D)
    (hT : IsLocalTermAt ρ r c x pos D z θ) (Λ : Finset ι) :
    ∃ M, 0 ≤ M ∧ ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm (restrictionDefect Λ θ) b η ≤ M := by exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.exists_bondGradNorm_restrictionDefect_bound (P := P) (pos := pos) (D := D) hρ hr hc hx hD hT Λ
theorem ballL2Norm_restrictionDefect_le_far (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hD : IsPseudoMetricOnBonds D)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    (hT : IsLocalTermAt ρ r c x pos D z θ) (Λ : Finset ι) (b : ι) :
    ballL2Norm (cutoffFactor ρ p) T (bondGradNorm (restrictionDefect Λ θ) b) ≤
      2 * c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) * Real.exp (-(2 * r * D (pos b) z)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.ballL2Norm_restrictionDefect_le <;> assumption
theorem ballL2Norm_restrictionDefect_le_near (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hm : 0 < m) (hR : 0 ≤ R)
    (hSn : 0 ≤ S) (hD : IsPseudoMetricOnBonds D) (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    (hT : IsLocalTermAt ρ r c x pos D z θ) (Λ : Finset ι) (hoff : ∀ b, b ∉ Λ → R / 4 ≤ D (pos b) z)
    (b : ι) :
    ballL2Norm (cutoffFactor ρ p) T (bondGradNorm (restrictionDefect Λ θ) b) ≤
      c * (Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) + S * (x * Real.sqrt (8 * S / m))) *
        Real.exp (-(r * R / 16)) * Real.exp (-(2 * r * D (pos b) z)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FreezingBound.ballL2Norm_restrictionDefect_le_of_far <;> assumption
structure BallLawProperties (ρ : ℝ) (p : ℝ → ℝ) (T : BondField ι → ℝ) : Prop where
  isProbability : IsProbabilityMeasure (normalizedBallLaw (cutoffFactor ρ p) T)
  integral_eq : ∀ f : BondField ι → ℝ,
    ∫ η, f η ∂normalizedBallLaw (cutoffFactor ρ p) T = ballExpectation (cutoffFactor ρ p) T f
  ae_mem : ∀ᵐ η ∂normalizedBallLaw (cutoffFactor ρ p) T, η ∈ openPolyball ι ρ
theorem aestronglyMeasurable_of_continuousOn (hρ : 0 < ρ) (hl : BallLawProperties ρ p T)
    {f : BondField ι → ℝ} (hf : ContinuousOn f (openPolyball ι ρ)) :
    AEStronglyMeasurable f (normalizedBallLaw (cutoffFactor ρ p) T) := by
  have h := Measure.restrict_eq_self_of_ae_mem hl.ae_mem
  rw [← h]
  exact hf.aestronglyMeasurable (isOpen_openPolyball hρ).measurableSet
theorem integrable_of_isBoundedContinuousOn (hρ : 0 < ρ) (hl : BallLawProperties ρ p T)
    {f : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f) :
    Integrable f (normalizedBallLaw (cutoffFactor ρ p) T) := by
  haveI := hl.isProbability
  obtain ⟨c₀, M, hM⟩ := hf
  refine Integrable.of_bound (aestronglyMeasurable_of_continuousOn hρ hl c₀) M ?_
  filter_upwards [hl.ae_mem] with η hη
  simpa [Real.norm_eq_abs] using hM η hη
theorem integrable_sq_of_isBoundedContinuousOn (hρ : 0 < ρ) (hl : BallLawProperties ρ p T)
    {f : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f) :
    Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) := by
  have : IsBoundedContinuousOn ι ρ (fun η => f η * f η) := hf.mul hf
  refine (integrable_of_isBoundedContinuousOn hρ hl this).congr
    (Filter.Eventually.of_forall fun η => ?_)
  simp only
  ring
theorem integrable_bondGradNorm_sq (hρ : 0 < ρ) (hl : BallLawProperties ρ p T)
    {g : BondField ι → ℝ}
    (hg : ContDiffOn ℝ 1 g (openPolyball ι ρ)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm g b η ≤ M) (b : ι) :
    Integrable (fun η => bondGradNorm g b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
  integrable_sq_of_isBoundedContinuousOn hρ hl (isBoundedContinuousOn_bondGradNorm hρ hg hM b)
theorem integrable_of_integrable_sq (hρ : 0 < ρ) (hl : BallLawProperties ρ p T)
    {f : BondField ι → ℝ} (hf : ContinuousOn f (openPolyball ι ρ))
    (h2 : Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T)) :
    Integrable f (normalizedBallLaw (cutoffFactor ρ p) T) := by
  haveI := hl.isProbability
  have hm := aestronglyMeasurable_of_continuousOn hρ hl hf
  exact ((memLp_two_iff_integrable_sq hm).2 h2).integrable (by norm_num)
theorem integrable_mul_of_isBoundedContinuousOn (hρ : 0 < ρ) (hl : BallLawProperties ρ p T)
    {f g : BondField ι → ℝ}
    (hf : Integrable f (normalizedBallLaw (cutoffFactor ρ p) T)) (hg : IsBoundedContinuousOn ι ρ g) :
    Integrable (fun η => f η * g η) (normalizedBallLaw (cutoffFactor ρ p) T) := by
  obtain ⟨c₀, M, hM⟩ := hg
  refine hf.mul_bdd (c := M) (aestronglyMeasurable_of_continuousOn hρ hl c₀) ?_
  filter_upwards [hl.ae_mem] with η hη
  simpa [Real.norm_eq_abs] using hM η hη
theorem ballCovariance_finset_sum {α : Type} (hρ : 0 < ρ) (F : IsPositiveUnitalForm ρ p T)
    (hl : BallLawProperties ρ p T)
    {f : BondField ι → ℝ} (hc : ContinuousOn f (openPolyball ι ρ))
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
theorem ballCovariance_sub (hρ : 0 < ρ) (F : IsPositiveUnitalForm ρ p T) (hl : BallLawProperties ρ p T)
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
theorem abs_ballCovariance_le_of_gradient_bounds (hρ : 0 < ρ) (hr : 0 < r)
    (hD : IsPseudoMetricOnBonds D) (hm : 0 < m)
    (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
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
      m⁻¹ * A * S * ∑ b, G b * Real.exp (-(r / 2 * D (pos b) z)) := by apply _root_.YangMills.Construction.Freezing.ExpectationComparison.abs_ballCovariance_le_of_weights <;> assumption
theorem abs_ballCovariance_le_of_localized (hρ : 0 < ρ) (hr : 0 < r) (hD : IsPseudoMetricOnBonds D)
    (hm : 0 < m)
    (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
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
    |ballCovariance (cutoffFactor ρ p) T f g| ≤ m⁻¹ * A * S * (B * S * Real.exp (-(r / 2 * D z' z))) := by apply _root_.YangMills.Construction.Freezing.ExpectationComparison.abs_ballCovariance_le_of_centers <;> assumption
theorem abs_ballCovariance_frozen_difference_le {Q : P → BondField ι → ℝ}
    {Ψ Af Hv : BondField ι → ℝ} {μ A : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x) (hm : 0 < m) (hR : 0 ≤ R) (hμ : 0 ≤ μ)
    (hSn : 0 ≤ S) (hD : IsPseudoMetricOnBonds D)
    (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
    (hSp : ∀ z, ∑ z', Real.exp (-(r / 4 * D z' z)) ≤ S)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p pos D T)
    (hQ : ∀ z, IsLocalTermAt ρ r c x pos D z (Q z))
    (hsplit : ∀ η ∈ openPolyball ι ρ,
      Ψ η - Af η = (∑ z, restrictionDefect Λ (Q z) η) - halfSqNormOn μ Λᶜ η)
    (hoff : ∀ b, b ∉ Λ → R / 2 ≤ D (pos b) Y)
    (hcov : covarianceOpenBallsStatement) (hlaw : BallLawProperties ρ p T)
    (hK : ∃ K, IsUniformlyConvexDecaying ρ m r (fun b b' => D (pos b) (pos b')) T K)
    (hp : IsCutoff ρ p)
    (hHv : ContDiffOn ℝ 1 Hv (openPolyball ι ρ)) (hA0 : 0 ≤ A)
    (hf2 : Integrable (fun η => Hv η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hpf : ∀ b, Integrable (fun η => bondGradNorm Hv b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T))
    (hHn : ∀ b, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm Hv b) ≤
      A * Real.exp (-(2 * r * D (pos b) Y))) :
    |ballCovariance (cutoffFactor ρ p) T Hv (fun η => Ψ η - Af η)| ≤
      m⁻¹ * A * S *
          (2 * c * (Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) + S * (x * Real.sqrt (8 * S / m))) * S *
            (S * Real.exp (-(r * R / 16)))) +
        m⁻¹ * A * S *
          (μ * Real.sqrt (8 * S / m) * (S * Real.exp (-(r * R / 16)))) := by
  set G := Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) with hGd
  set q := Real.sqrt (8 * S / m) with hqd
  set e := Real.exp (-(r * R / 16)) with hed
  have he : 0 < e := Real.exp_pos _
  have hnn := fun y w => pseudoMetric_nonneg hD y w
  have hgs : ∀ z, ContDiffOn ℝ 1 (restrictionDefect Λ (Q z)) (openPolyball ι ρ) := fun z =>
    contDiffOn_restrictionDefect hρ Λ (contDiffOn_one_of_two (hQ z).smooth)
  have hgb := fun z => exists_bondGradNorm_restrictionDefect_bound hρ hr hc hx hD (hQ z) Λ
  have hgn : ∀ z, IsBoundedContinuousOn ι ρ (restrictionDefect Λ (Q z)) := fun z => by
    obtain ⟨M, hM0, hM⟩ := hgb z
    exact isBoundedContinuousOn_of_bondGradNorm_le hρ (hgs z) hM0 hM
  have hqs : ContDiffOn ℝ 1 (halfSqNormOn μ Λᶜ) (openPolyball ι ρ) :=
    ((contDiff_halfSqNormOn μ Λᶜ).of_le (by norm_num)).contDiffOn
  have hqb : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm (halfSqNormOn μ Λᶜ) b η ≤ μ * ρ := by
    intro η hη b
    refine (bondGradNorm_halfSqNormOn_le hμ Λᶜ η b).trans ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_left (hη b).le hμ
    · positivity
  have hqn : IsBoundedContinuousOn ι ρ (halfSqNormOn μ Λᶜ) :=
    isBoundedContinuousOn_of_bondGradNorm_le hρ hqs (by positivity) hqb
  have e1 : ballCovariance (cutoffFactor ρ p) T Hv (fun η => Ψ η - Af η) =
      (∑ z, ballCovariance (cutoffFactor ρ p) T Hv (restrictionDefect Λ (Q z))) -
        ballCovariance (cutoffFactor ρ p) T Hv (halfSqNormOn μ Λᶜ) := by
    rw [ballCovariance_congr F (fun _ _ => rfl) hsplit,
      ballCovariance_sub hρ F hlaw hHv.continuousOn hf2
        (IsBoundedContinuousOn.sum _ _ fun z _ => hgn z) hqn,
      ballCovariance_finset_sum hρ F hlaw hHv.continuousOn hf2 _ _ fun z _ => hgn z]
  rw [e1]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    set Bx := 2 * c * (G + S * (x * q)) with hBx
    have hBx0 : 0 ≤ Bx := by positivity
    have hz : ∀ z, |ballCovariance (cutoffFactor ρ p) T Hv (restrictionDefect Λ (Q z))| ≤
        m⁻¹ * A * S * (Bx * S * (e * Real.exp (-(r / 4 * D z Y)))) := by
      intro z
      obtain ⟨M, hM0, hM⟩ := hgb z
      have g2 := integrable_sq_of_isBoundedContinuousOn hρ hlaw (hgn z)
      have pg2 := integrable_bondGradNorm_sq hρ hlaw (hgs z) hM0 hM
      by_cases hnear : D z Y < R / 4
      · have h1 := abs_ballCovariance_le_of_localized (B := Bx * e) (z := Y) (z' := z) hρ hr hD hm hS
          hcov hK hp hHv (hgs z) hf2 g2 hpf pg2
          hA0 (by positivity) hHn (fun b => by
            have hoffz : ∀ b', b' ∉ Λ → R / 4 ≤ D (pos b') z := fun b' hb' => by
              have t := hD.triangle (pos b') z Y
              have := hoff b' hb'
              linarith
            refine (ballL2Norm_restrictionDefect_le_near hρ hr hc hx hm hR hSn hD hS F Sz (hQ z) Λ
              hoffz b).trans ?_
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_right _ he.le
            simp only [hBx]
            have : 0 ≤ c * (G + S * (x * q)) := by positivity
            linarith)
        refine h1.trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h2 : Real.exp (-(r / 2 * D z Y)) ≤ Real.exp (-(r / 4 * D z Y)) := by
          apply Real.exp_le_exp.mpr
          have := hnn z Y
          nlinarith
        calc Bx * e * S * Real.exp (-(r / 2 * D z Y))
            ≤ Bx * e * S * Real.exp (-(r / 4 * D z Y)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := by ring
      · push Not at hnear
        have h1 := abs_ballCovariance_le_of_localized (B := Bx) (z := Y) (z' := z) hρ hr hD hm hS
          hcov hK hp hHv (hgs z) hf2 g2 hpf pg2
          hA0 hBx0 hHn (fun b => by
            refine (ballL2Norm_restrictionDefect_le_far hρ hr hc hx hD F Sz (hQ z) Λ b).trans ?_
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            simp only [hBx]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have : 0 ≤ S * (x * q) := by positivity
            linarith)
        refine h1.trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h2 := exp_neg_le_mul_exp_neg (r := r) (R := R) (s := r / 2) (d := D z Y) (by
          have h3 : (R / 4) * r ≤ D z Y * r := mul_le_mul_of_nonneg_right hnear hr.le
          nlinarith)
        calc Bx * S * Real.exp (-(r / 2 * D z Y))
            ≤ Bx * S * (Real.exp (-(r / 4 * D z Y)) * e) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := by ring
    refine (Finset.sum_le_sum fun z _ => hz z).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_comm S e]
    exact mul_le_mul_of_nonneg_left (hSp Y) he.le
  · have g2 := integrable_sq_of_isBoundedContinuousOn hρ hlaw hqn
    have pg2 := integrable_bondGradNorm_sq hρ hlaw hqs (by positivity) hqb
    set Gq : ι → ℝ := fun b => if b ∈ Λ then 0 else μ * q with hGq
    have hGq0 : ∀ b, 0 ≤ Gq b := fun b => by
      simp only [hGq]
      split_ifs
      · exact le_rfl
      · positivity
    have h1 := abs_ballCovariance_le_of_gradient_bounds (z := Y) (G := Gq) hρ hr hD hm hS hcov hK hp
      hHv hqs hf2 g2 hpf pg2 hA0 hGq0 hHn
      (fun b => by
        set a' : ι → ℝ := fun b' => if b' = b ∧ b ∉ Λ then μ else 0 with ha'
        have ha0 : ∀ b', 0 ≤ a' b' := fun b' => by
          simp only [ha']
          split_ifs
          · exact hμ
          · exact le_rfl
        have key := ballL2Norm_le_of_linear_majorant hρ F Sz hSn hm
          (isBoundedContinuousOn_bondGradNorm hρ hqs hqb b) a' ha0
          (fun η hη => by
            rw [abs_of_nonneg (bondGradNorm_nonneg _ b η)]
            refine (bondGradNorm_halfSqNormOn_le hμ Λᶜ η b).trans ?_
            by_cases hb : b ∈ Λ
            · simp only [Finset.mem_compl, hb, not_true_eq_false, if_false]
              exact Finset.sum_nonneg fun b' _ => mul_nonneg (ha0 b') (norm_nonneg _)
            · simp only [Finset.mem_compl, hb, not_false_eq_true, if_true]
              rw [Finset.sum_eq_single b]
              · simp [ha', hb]
              · intro b' _ hne
                simp [ha', hne]
              · simp)
        refine key.trans (le_of_eq ?_)
        by_cases hb : b ∈ Λ
        · simp [ha', hGq, hb]
        · simp only [ha', hGq, hb, not_false_eq_true, and_true, if_false]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rfl)
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h2 : ∀ b, Gq b * Real.exp (-(r / 2 * D (pos b) Y)) ≤
        μ * q * (Real.exp (-(r / 4 * D (pos b) Y)) * e) := by
      intro b
      by_cases hb : b ∈ Λ
      · simp only [hGq, hb, if_true, zero_mul]
        positivity
      · simp only [hGq, hb, if_false]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply exp_neg_le_mul_exp_neg
        have h3 : (R / 2) * r ≤ D (pos b) Y * r := mul_le_mul_of_nonneg_right (hoff b hb) hr.le
        have h4 : 0 ≤ r * R := by positivity
        nlinarith
    refine (Finset.sum_le_sum fun b _ => h2 b).trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (hS Y) he.le
theorem constants_le_freezeGradientConstant {lam S x c A e : ℝ} (hlam : 0 < lam) (hS : 0 ≤ S)
    (hx : 1 ≤ x) (hc : 1 ≤ c) (hA : 0 ≤ A) (he : 0 < e) :
    (x * lam / 4)⁻¹ * A * S *
        (2 * c * (Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) +
          S * (x * Real.sqrt (8 * S / (x * lam / 4)))) * S * (S * e)) +
      (x * lam / 4)⁻¹ * A * S *
        (x * lam * Real.sqrt (8 * S / (x * lam / 4)) * (S * e)) ≤
      A * (Real.sqrt x)⁻¹ * c * freezeGradientConstant lam S * e := by
  have hx0 : 0 < x := by linarith
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have hss : s ^ 2 = x := Real.sq_sqrt hx0.le
  set g := Real.sqrt (64 * S ^ 2 / lam + 2) with hg
  set q₀ := Real.sqrt (32 * S / lam) with hq₀
  have hq : Real.sqrt (8 * S / (x * lam / 4)) = q₀ / s := by
    have : 8 * S / (x * lam / 4) = (32 * S / lam) / x := by
      field_simp
      ring
    rw [this, Real.sqrt_div (by positivity)]
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
  rw [hq]
  have hxq : x * (q₀ / s) = s * q₀ := by
    rw [← hss]
    field_simp
  have hsum : Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) + S * (x * (q₀ / s)) ≤
      s * (g + S * q₀) := by
    rw [hxq]
    nlinarith
  have step : (x * lam / 4)⁻¹ * A * S *
        (2 * c * (Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) + S * (x * (q₀ / s))) * S *
          (S * e)) ≤ (x * lam / 4)⁻¹ * A * S * (2 * c * (s * (g + S * q₀)) * S * (S * e)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hS
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  refine (add_le_add_left step _).trans ?_
  unfold freezeGradientConstant
  rw [← hg, ← hq₀]
  have e1 : (x * lam / 4)⁻¹ * A * S * (2 * c * (s * (g + S * q₀)) * S * (S * e)) =
      A * s⁻¹ * c * (8 * S ^ 3 / lam * (g + S * q₀)) * e := by
    rw [← hss]
    field_simp
    ring
  have e2 : (x * lam / 4)⁻¹ * A * S * (x * lam * (q₀ / s) * (S * e)) =
      A * s⁻¹ * (4 * S ^ 2 * q₀) * e := by
    field_simp
  rw [e1, e2]
  have hk : 0 ≤ A * s⁻¹ * (4 * S ^ 2 * q₀) * e := by positivity
  have : A * s⁻¹ * c * (8 * S ^ 3 / lam * (g + S * q₀) + 4 * S ^ 2 * q₀) * e -
      (A * s⁻¹ * c * (8 * S ^ 3 / lam * (g + S * q₀)) * e + A * s⁻¹ * (4 * S ^ 2 * q₀) * e) =
      (c - 1) * (A * s⁻¹ * (4 * S ^ 2 * q₀) * e) := by ring
  have h2 : 0 ≤ (c - 1) * (A * s⁻¹ * (4 * S ^ 2 * q₀) * e) :=
    mul_nonneg (by linarith) hk
  linarith
end Measure
end LocalGradients
theorem frozenExpectationDifferenceBound_holds (hseg : WeightedMeanDiffLeOfDerivBound)
    (hgood : AdmissiblePotentialStability) (hsz : AdmissibleMomentBoundsHold)
    (hmc : CutoffExpectationIsPositiveForm) (hcov : covarianceOpenBallsStatement)
    (hlaw : normalizedBallLawIsProbabilityStatement) : frozenExpectationDifferenceBound := by
  intro ι P _ _ _ ρ r S lam x c R A B p pos D Ψ H θ Y Λ hρ hr hlam hx hc hR hA hp hD hΨ hS hSp hθ hsum hΛ
    hHi hHci hstep
  have hx0 : 0 < x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hm0 : 0 < x * lam / 4 := by positivity
  have h2m : 2 * (x * lam / 4) ≤ x * lam := by nlinarith [mul_pos hx0 hlam]
  have hd : IsPseudoMetricOnBonds (fun b b' => D (pos b) (pos b')) :=
    ⟨fun b => hD.self _, fun b b' => hD.symm _ _, fun b b' b'' => hD.triangle _ _ _⟩
  have hSn : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS Y)
  obtain ⟨hsg, -, hfrz, -⟩ := hgood ι ρ (x * lam / 4) r (x * lam) _ hρ hm0 hr.le hd h2m
  have gA := hfrz Ψ Λ hΨ
  have cΨ : Continuous Ψ := by
    obtain ⟨K, hK, _⟩ := hΨ
    exact hK.smooth.continuous
  have cA : Continuous (frozenPotential Λ (x * lam) Ψ) := by
    obtain ⟨K, hK, _⟩ := gA
    exact hK.smooth.continuous
  set Af := frozenPotential Λ (x * lam) Ψ with hAf
  set Hc : BondField ι → ℝ := fun η => H (restrictToBonds Λ η) with hHc
  have hbdd : ∀ f : BondField ι → ℝ, Continuous f → ∃ M, ∀ η ∈ openPolyball ι ρ, |f η| ≤ M := by
    intro f hf
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
      hf.continuousOn
    refine ⟨M, fun η hη => ?_⟩
    have : η ∈ Metric.closedBall (0 : BondField ι) ρ := by
      rw [openPolyball_eq_ball hρ] at hη
      exact Metric.ball_subset_closedBall hη
    simpa using hM η this
  obtain ⟨M₃, hM₃⟩ := hbdd Af cA
  obtain ⟨M₄, hM₄⟩ := hbdd Ψ cΨ
  obtain ⟨-, -, -, -, -, hw0, hwi, hwp, -, hwne, -⟩ :=
    hlaw ι ρ p (fun _ => 0) hρ hp continuous_const
  set w : BondField ι → ℝ := radialWeightProd (cutoffFactor ρ p) with hw
  have hdw : ∀ η, ballDensity (cutoffFactor ρ p) (fun _ => (0 : ℝ)) η = w η := by
    intro η
    simp [ballDensity, hw]
  have hmeas : MeasurableSet (openPolyball ι ρ) := (isOpen_openPolyball hρ).measurableSet
  have hconv : ∀ Φ f : BondField ι → ℝ,
      weightedMean volume w Φ f = ballExpectation (cutoffFactor ρ p) Φ f := fun _ _ => rfl
  have key := hseg (BondField ι) volume (openPolyball ι ρ) w Af Ψ Hc H (max M₃ M₄)
    (B + A * (Real.sqrt x)⁻¹ * c * freezeGradientConstant lam S * Real.exp (-(r * R / 16))) hmeas
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
    (cA.continuousOn.aestronglyMeasurable hmeas) (cΨ.continuousOn.aestronglyMeasurable hmeas)
    (fun η hη => (hM₃ η hη).trans (le_max_left _ _)) (fun η hη => (hM₄ η hη).trans (le_max_right _ _))
    hHci hHi ?_
  · simpa only [hconv] using key
  intro v hv0 hv1
  have hv1' : 0 ≤ 1 - v := by linarith
  set T := segmentInterpolant Af Ψ v with hT
  have gT := hsg Af Ψ v gA hΨ hv0 hv1
  have cT : Continuous T := by
    obtain ⟨K, hK, _⟩ := gT
    exact hK.smooth.continuous
  have hKT : ∃ K, IsUniformlyConvexDecaying ρ (x * lam / 4) r (fun b b' => D (pos b) (pos b')) T K := by
    obtain ⟨K, hK, _⟩ := gT
    exact ⟨K, hK⟩
  have F := hmc ι ρ p T hρ hp cT
  have Sz := hsz ι P ρ (x * lam / 4) r S p pos D T hρ hm0 hr hp hD gT hS
  obtain ⟨l1, l2, l3, l4, -⟩ := hlaw ι ρ p T hρ hp cT
  have hl : BallLawProperties ρ p T := ⟨l1, l2, l4⟩
  obtain ⟨gH, gC, hB⟩ := hstep v hv0 hv1
  have hoff : ∀ b, b ∉ Λ → R / 2 ≤ D (pos b) Y := fun b hb => by
    have : ¬ D (pos b) Y ≤ R / 2 := fun h => hb ((hΛ b).mpr h)
    linarith
  have hsplit : ∀ η ∈ openPolyball ι ρ,
      Ψ η - Af η = (∑ z, restrictionDefect Λ (θ z) η) - halfSqNormOn (x * lam) Λᶜ η := by
    intro η hη
    have h1 := hsum η hη
    have h2 := hsum _ (restrictToBonds_mem_openPolyball hρ Λ hη)
    simp only [hAf, frozenPotential, restrictionDefect, restrictedObservable, Finset.sum_sub_distrib]
    rw [h1, h2]
    ring
  have sq1 : Integrable (fun η => H η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
    (l3 _).2 gH.sq_integrable
  have sq2 : Integrable (fun η => Hc η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
    (l3 _).2 gC.sq_integrable
  have pq1 : ∀ b, Integrable (fun η => bondGradNorm H b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
    fun b => (l3 _).2 (gH.grad_sq_integrable b)
  have pq2 : ∀ b, Integrable (fun η => bondGradNorm Hc b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) T) :=
    fun b => (l3 _).2 (gC.grad_sq_integrable b)
  have t1 := abs_ballCovariance_frozen_difference_le (T := T) (Ψ := Ψ) (Af := Af) (Hv := H) (Q := θ)
    (μ := x * lam) (A := A)
    hρ hr hc0 hx0.le hm0 hR (by positivity) hSn hD hS hSp F Sz hθ hsplit hoff hcov hl hKT hp gH.smooth hA
    sq1 pq1 gH.grad_norm_le
  have t2 := abs_ballCovariance_frozen_difference_le (T := T) (Ψ := Ψ) (Af := Af) (Hv := Hc) (Q := θ)
    (μ := x * lam) (A := A)
    hρ hr hc0 hx0.le hm0 hR (by positivity) hSn hD hS hSp F Sz hθ hsplit hoff hcov hl hKT hp gC.smooth hA
    sq2 pq2 gC.grad_norm_le
  have hnum := constants_le_freezeGradientConstant (e := Real.exp (-(r * R / 16))) (A := A) hlam hSn hx hc
    hA (Real.exp_pos _)
  set K' := A * (Real.sqrt x)⁻¹ * c * freezeGradientConstant lam S * Real.exp (-(r * R / 16)) with hK'
  have b1 : |ballCovariance (cutoffFactor ρ p) T H (fun η => Ψ η - Af η)| ≤ K' := t1.trans hnum
  have b2 : |ballCovariance (cutoffFactor ρ p) T Hc (fun η => Ψ η - Af η)| ≤ K' := t2.trans hnum
  have nice_g : IsBoundedContinuousOn ι ρ (fun η => Ψ η - Af η) :=
    ⟨(cΨ.sub cA).continuousOn, |M₄| + |M₃|, fun η hη => by
      have a1 := hM₄ η hη
      have a2 := hM₃ η hη
      have a3 := abs_sub (Ψ η) (Af η)
      have a4 := le_abs_self M₃
      have a5 := le_abs_self M₄
      linarith⟩
  have iH := integrable_of_integrable_sq hρ hl gH.smooth.continuousOn sq1
  have iC := integrable_of_integrable_sq hρ hl gC.smooth.continuousOn sq2
  have iHg := integrable_mul_of_isBoundedContinuousOn hρ hl iH nice_g
  have iCg := integrable_mul_of_isBoundedContinuousOn hρ hl iC nice_g
  have eMean : ballExpectation (cutoffFactor ρ p) T (segmentPoint Hc H v) =
      v * ballExpectation (cutoffFactor ρ p) T H + (1 - v) * ballExpectation (cutoffFactor ρ p) T Hc := by
    simp only [← l2]
    unfold segmentPoint
    rw [integral_add (iH.const_mul v) (iC.const_mul (1 - v)), integral_const_mul, integral_const_mul]
  have eProd : ballExpectation (cutoffFactor ρ p) T
      (fun η => segmentPoint Hc H v η * (Ψ η - Af η)) =
      v * ballExpectation (cutoffFactor ρ p) T (fun η => H η * (Ψ η - Af η)) +
        (1 - v) * ballExpectation (cutoffFactor ρ p) T (fun η => Hc η * (Ψ η - Af η)) := by
    simp only [← l2]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iHg.const_mul v) (iCg.const_mul (1 - v))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [segmentPoint]
    ring
  have eSlope : meanDerivAlongSegment volume w Af Ψ Hc H v =
      ballExpectation (cutoffFactor ρ p) T (fun η => H η - Hc η) -
        (v * ballCovariance (cutoffFactor ρ p) T H (fun η => Ψ η - Af η) +
          (1 - v) * ballCovariance (cutoffFactor ρ p) T Hc (fun η => Ψ η - Af η)) := by
    have hTs : segmentPoint Af Ψ v = T := rfl
    unfold meanDerivAlongSegment
    rw [hTs]
    simp only [hconv]
    rw [eProd, eMean]
    unfold ballCovariance
    ring
  rw [eSlope]
  have hcv : |v * ballCovariance (cutoffFactor ρ p) T H (fun η => Ψ η - Af η) +
      (1 - v) * ballCovariance (cutoffFactor ρ p) T Hc (fun η => Ψ η - Af η)| ≤ K' := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_nonneg hv1']
    nlinarith
  exact (abs_sub _ _).trans (add_le_add hB hcv)
end Freezing
end YangMills.Construction
end
