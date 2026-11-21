import YangMills.Construction.ColdStepAtMirrorFrames.TransportParameters
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersHaveACouplingAboveOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison ConvexObservables FamilyNorms
namespace WeightedResponses
namespace GradientMoves
section BallLaws
variable {ι : Type} [Fintype ι] [DecidableEq ι]
structure AdmissibleBallLaw (ρ : ℝ) (p : ℝ → ℝ) (x c : ℝ) (Φ : BondField ι → ℝ) (μ : Measure (BondField ι)) : Prop where
  isProbability : IsProbabilityMeasure μ
  expectation_eq : ∀ f : BondField ι → ℝ, ballExpectation (cutoffFactor ρ p) Φ f = ∫ η, f η ∂μ
  integrable_iff : ∀ f : BondField ι → ℝ,
    Integrable f μ ↔ Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Φ η
  ae_mem_ball : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ < ρ
  moment_le : ∀ b, ∫ η, ‖η b‖ ^ 2 ∂μ ≤ c / x
theorem isOpen_ball_set (ρ : ℝ) : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
theorem exists_admissibleBallLaw (hLaw : normalizedBallLawIsProbabilityStatement) {ρ x lam κ C C' : ℝ} {p : ℝ → ℝ}
    {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {d : ι → ι → ℝ} {Φ : BondField ι → ℝ} (hρ : 0 < ρ) (hcut : IsCutoff ρ p)
    (hconv : HasUniformlyConvexLaw ρ lam x κ C d Φ) (hm : LawMomentBounds ρ x κ C' p Cq Cr d Φ) :
    ∃ μ, AdmissibleBallLaw ρ p x (Cq 1) Φ μ := by
  obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
  obtain ⟨h1, h2, h3, h4, -, -, -, -, -, hnz, -⟩ := hLaw ι ρ p Ψ' hρ hcut hconvex.smooth.continuous
  have hdens : ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < ρ
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 : ballDensity (cutoffFactor ρ p) Ψ' η = 0 := by
        by_contra hne
        exact hη' ((hnz η).1 hne)
      have h1 : radialWeightProd (cutoffFactor ρ p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  have hmean : ∀ f : BondField ι → ℝ,
      ballExpectation (cutoffFactor ρ p) Φ f = ballExpectation (cutoffFactor ρ p) Ψ' f := by
    intro f
    unfold ballExpectation
    rw [hdens]
  refine ⟨normalizedBallLaw (cutoffFactor ρ p) Ψ', h1, fun f => by rw [hmean, h2],
    fun f => by rw [hdens]; exact h3 f, h4, fun b => ?_⟩
  have := hm.moments 1 b
  rw [hmean, ← h2] at this
  simpa [div_eq_mul_inv] using this
variable {ρ x c : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {μ : Measure (BondField ι)}
theorem AdmissibleBallLaw.aestronglyMeasurable (h : AdmissibleBallLaw ρ p x c Φ μ) {H : BondField ι → ℝ}
    (hH : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ}) : AEStronglyMeasurable H μ := by
  have hμ : μ.restrict {η | ∀ b, ‖η b‖ < ρ} = μ := Measure.restrict_eq_self_of_ae_mem h.ae_mem_ball
  rw [← hμ]
  exact hH.aestronglyMeasurable (isOpen_ball_set ρ).measurableSet
theorem AdmissibleBallLaw.integrable_of_bound (h : AdmissibleBallLaw ρ p x c Φ μ) {H : BondField ι → ℝ}
    (hH : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ}) {M : ℝ} (hM : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ≤ M) :
    Integrable H μ := by
  have := h.isProbability
  exact Integrable.of_bound (h.aestronglyMeasurable hH) M (h.ae_mem_ball.mono fun η hη => by simpa using hM η hη)
theorem AdmissibleBallLaw.momentBound_two (h : AdmissibleBallLaw ρ p x c Φ μ) {H G : BondField ι → ℝ} {B : ℝ}
    (hH : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ}) {M : ℝ} (hM : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ≤ M)
    (hG : Integrable G μ) (hHG : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ^ 2 ≤ G η) (hB : ∫ η, G η ∂μ ≤ B ^ 2) :
    MomentBound (cutoffFactor ρ p) Φ H 2 B := by
  have hc2 : ContinuousOn (fun η => |H η| ^ 2) {η | ∀ b, ‖η b‖ < ρ} := (continuous_abs.comp_continuousOn hH).pow 2
  have hb2 : ∀ η, (∀ b, ‖η b‖ < ρ) → |(fun η => |H η| ^ 2) η| ≤ M ^ 2 := fun η hη => by
    have := hM η hη
    have h0 := abs_nonneg (H η)
    simp only [abs_pow, abs_abs]
    exact pow_le_pow_left₀ h0 this 2
  have hi := h.integrable_of_bound hc2 hb2
  refine ⟨(h.integrable_iff _).1 hi, ?_⟩
  rw [h.expectation_eq]
  exact (integral_mono_ae hi hG (h.ae_mem_ball.mono fun η hη => hHG η hη)).trans hB
end BallLaws
section ExtensionByZero
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
theorem extendByZero_apply_mem {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) {Λ : Finset ι}
    {i : ι} (hi : i ∈ Λ) (ζ : BondField ι) : _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ (j i) = ζ i := by apply _root_.YangMills.SharedProofs.p25945 <;> assumption
theorem extendByZero_apply_of_not {j : ι → ↥(chordBonds (finiteCells F))} {Λ : Finset ι} (ζ : BondField ι)
    {b : ↥(chordBonds (finiteCells F))} (hb : ∀ i ∈ Λ, j i ≠ b) : _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b = 0 :=
  Finset.sum_eq_zero fun i hi => if_neg (hb i hi)
theorem norm_extendByZero_lt {ρ : ℝ} (hρ : 0 < ρ) {j : ι → ↥(chordBonds (finiteCells F))}
    (hj : Function.Injective j) (Λ : Finset ι) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < ρ)
    (b : ↥(chordBonds (finiteCells F))) : ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ < ρ := by apply _root_.YangMills.SharedProofs.p22320 <;> assumption
theorem extendByZero_id_univ (η : StepVariable (finiteCells F)) : _root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ η = η := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
def extendByZeroCLM (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) :
    BondField ι →L[ℝ] StepVariable (finiteCells F) :=
  ContinuousLinearMap.pi fun b => ∑ i ∈ Λ, if j i = b then
    (ContinuousLinearMap.proj i : BondField ι →L[ℝ] BondVector) else 0
theorem extendByZeroCLM_apply (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) (ζ : BondField ι) :
    extendByZeroCLM j Λ ζ = _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ := by
  funext b
  simp only [extendByZeroCLM, ContinuousLinearMap.coe_pi', sum_apply, _root_.YangMills.Construction.Interpolation.extendByZero]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp
theorem abs_fderiv_single_le {κ' : Type} [Fintype κ'] [DecidableEq κ'] (A : BondField κ' → ℝ) (η : BondField κ')
    (b : κ') (e : BondVector) : |fderiv ℝ A η (Pi.single b e)| ≤ bondGradNorm A b η * ‖e‖ :=
  ((fderiv ℝ A η).comp (ContinuousLinearMap.single ℝ (fun _ : κ' => BondVector) b)).le_opNorm e
theorem bondGradNorm_comp_extendByZero_le {A : StepVariable (finiteCells F) → ℝ}
    {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (Λ : Finset ι) {ζ : BondField ι}
    (hd : DifferentiableAt ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) (i : ι) :
    bondGradNorm (fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) i ζ ≤
      if i ∈ Λ then bondGradNorm A (j i) (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) else 0 := by apply _root_.YangMills.SharedProofs.p25557 <;> assumption
end ExtensionByZero
section Moves
variable {F : BlockFrame}
theorem localSqNorm_mono (κ : ℝ) (Y : F.Cell) {η η' : StepVariable (finiteCells F)} (h : ∀ b, ‖η' b‖ ≤ ‖η b‖) :
    localSqNorm κ Y η' ≤ localSqNorm κ Y η :=
  Finset.sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h b) 2) (Real.exp_pos _).le
theorem localSqNorm_nonneg (κ : ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) : 0 ≤ localSqNorm κ Y η :=
  Finset.sum_nonneg fun b _ => by positivity
theorem differentiableAt_of_mem_ball {ρ x κ g₀ g₁ : ℝ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    (hA : IsVanishingMoveWithGradient ρ x κ g₀ g₁ Y A) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) :
    DifferentiableAt ℝ A η :=
  (hA.smooth.contDiffAt ((isOpen_ball_set ρ).mem_nhds hη)).differentiableAt one_ne_zero
theorem abs_sub_extendByZero_le {ρ x κ g₀ g₁ : ℝ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    (hA : IsVanishingMoveWithGradient ρ x κ g₀ g₁ Y A) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁) (hx : 0 ≤ x)
    (Λ : Finset ↥(chordBonds (finiteCells F))) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ < ρ) :
    |A η - A (_root_.YangMills.Construction.Interpolation.extendByZero id Λ η)| ≤ ∑ b, if b ∈ Λ then 0 else
      (g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y η))) * Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b)) * ‖η b‖ := by
  classical
  set P := _root_.YangMills.Construction.Interpolation.extendByZero id Λ η with hP
  set u := η - P with hu
  have hPin : ∀ b ∈ Λ, P b = η b := fun b hb => extendByZero_apply_mem Function.injective_id hb η
  have hPout : ∀ b, b ∉ Λ → P b = 0 := fun b hb => extendByZero_apply_of_not η fun i hi h => hb (h ▸ hi)
  have hcomp : ∀ v : ℝ, v ∈ Set.Icc (0 : ℝ) 1 → ∀ b, ‖(P + v • u) b‖ ≤ ‖η b‖ := by
    intro v hv b
    by_cases hb : b ∈ Λ
    · simp [hu, hPin b hb]
    · simp only [hu, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hPout b hb, sub_zero, zero_add, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hv.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hv.2
  have hball : ∀ v : ℝ, v ∈ Set.Icc (0 : ℝ) 1 → ∀ b, ‖(P + v • u) b‖ < ρ := fun v hv b =>
    (hcomp v hv b).trans_lt (hη b)
  have hder : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => A (P + v • u)) (fderiv ℝ A (P + v • u) ((1 : ℝ) • u)) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => P + v • u) ((1 : ℝ) • u) v := ((hasDerivAt_id v).smul_const u).const_add P
    exact (differentiableAt_of_mem_ball hA (hball v hv)).hasFDerivAt.comp_hasDerivAt v h1
  have hbound : ∀ v ∈ Set.Ico (0 : ℝ) 1, ‖fderiv ℝ A (P + v • u) ((1 : ℝ) • u)‖ ≤ ∑ b, if b ∈ Λ then 0 else
      (g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y η))) * Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b)) * ‖η b‖ := by
    intro v hv
    have hv' : v ∈ Set.Icc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
    rw [one_smul, Real.norm_eq_abs]
    have esum : fderiv ℝ A (P + v • u) u = ∑ b, fderiv ℝ A (P + v • u) (Pi.single b (u b)) := by
      rw [← map_sum, Finset.univ_sum_single]
    rw [esum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (abs_fderiv_single_le A _ b (u b)).trans ?_
    have hs := hA.gradient_le (P + v • u) (hball v hv') b
    have hsq : Real.sqrt (localSqNorm κ Y (P + v • u)) ≤ Real.sqrt (localSqNorm κ Y η) :=
      Real.sqrt_le_sqrt (localSqNorm_mono κ Y (hcomp v hv'))
    have hs2 : bondGradNorm A b (P + v • u) ≤ (g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y η))) *
        Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b)) := by
      refine hs.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      have := mul_le_mul_of_nonneg_left hsq hx
      have := mul_le_mul_of_nonneg_left this hg₁
      linarith
    by_cases hb : b ∈ Λ
    · have : u b = 0 := by simp [hu, hPin b hb]
      simp [this, hb]
    · have : u b = η b := by simp [hu, hPout b hb]
      rw [if_neg hb, this]
      exact mul_le_mul_of_nonneg_right hs2 (norm_nonneg _)
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (fun v hv => (hder v hv).hasDerivWithinAt) hbound
  simp only [one_smul, zero_smul, add_zero, hu, add_sub_cancel, Real.norm_eq_abs] at this
  exact this
end Moves
section Expectations
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x c : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ}
  {μ : Measure (BondField ι)}
theorem AdmissibleBallLaw.integrable_norm_sq (h : AdmissibleBallLaw ρ p x c Φ μ) (i : ι) :
    Integrable (fun η : BondField ι => ‖η i‖ ^ 2) μ := by
  refine h.integrable_of_bound (M := ρ ^ 2) ((continuous_norm.comp (continuous_apply i)).pow 2).continuousOn
    fun η hη => ?_
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hη i).le 2
theorem rpow_neg_half_sq {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2) : ℝ)) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num [Real.rpow_neg_one]
theorem AdmissibleBallLaw.exists_majorant (h : AdmissibleBallLaw ρ p x c Φ μ) {S : BondField ι → ℝ} {s g₀ g₁ : ℝ}
    (hx : 0 < x) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁) (hS : Integrable S μ) (hS0 : ∀ η, 0 ≤ S η)
    (hSi : ∫ η, S η ∂μ ≤ s / x) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ R : BondField ι → ℝ, Integrable R μ ∧
      (∀ η, ∑ i, a i * ((g₀ + g₁ * (x * Real.sqrt (S η))) * ‖η i‖) ≤ R η) ∧
      ∫ η, R η ∂μ ≤ (∑ i, a i) * (g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + c) / 2) + g₁ * ((s + c) / 2)) := by
  have hprob := h.isProbability
  set t : ℝ := x ^ (-(1 / 2) : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx _
  have ht2 : t ^ 2 = x⁻¹ := rpow_neg_half_sq hx
  let r : ι → BondField ι → ℝ := fun i η =>
    g₀ * t / 2 + (g₀ / (2 * t) + g₁ * x / 2) * ‖η i‖ ^ 2 + g₁ * x / 2 * S η
  have hr : ∀ i, Integrable (r i) μ := fun i =>
    ((integrable_const _).add ((h.integrable_norm_sq i).const_mul _)).add (hS.const_mul _)
  have hri : ∀ i, ∫ η, r i η ∂μ ≤ g₀ * t * ((1 + c) / 2) + g₁ * ((s + c) / 2) := by
    intro i
    have e : ∫ η, r i η ∂μ = g₀ * t / 2 + (g₀ / (2 * t) + g₁ * x / 2) * ∫ η, ‖η i‖ ^ 2 ∂μ +
        g₁ * x / 2 * ∫ η, S η ∂μ := by
      have i1 : Integrable (fun η : BondField ι => (g₀ / (2 * t) + g₁ * x / 2) * ‖η i‖ ^ 2) μ :=
        (h.integrable_norm_sq i).const_mul _
      have i2 : Integrable (fun η : BondField ι => g₀ * t / 2 + (g₀ / (2 * t) + g₁ * x / 2) * ‖η i‖ ^ 2) μ :=
        (integrable_const _).add i1
      have i3 : Integrable (fun η : BondField ι => g₁ * x / 2 * S η) μ := hS.const_mul _
      simp only [r]
      rw [integral_add i2 i3, integral_add (integrable_const _) i1, integral_const, integral_const_mul,
        integral_const_mul]
      simp
    rw [e]
    have h1 := h.moment_le i
    have c1 : 0 ≤ g₀ / (2 * t) + g₁ * x / 2 := by positivity
    have c2 : 0 ≤ g₁ * x / 2 := by positivity
    have e1 := mul_le_mul_of_nonneg_left h1 c1
    have e2 := mul_le_mul_of_nonneg_left hSi c2
    have e3 : (g₀ / (2 * t) + g₁ * x / 2) * (c / x) = g₀ * t * c / 2 + g₁ * c / 2 := by
      have hxt : x⁻¹ = t ^ 2 := ht2.symm
      have A1 : g₀ / (2 * t) * (c / x) = g₀ * t * c / 2 := by
        rw [div_eq_mul_inv c, hxt]
        field_simp
      have A2 : g₁ * x / 2 * (c / x) = g₁ * c / 2 := by
        field_simp
      rw [add_mul, A1, A2]
    have e4 : g₁ * x / 2 * (s / x) = g₁ * s / 2 := by
      field_simp
    nlinarith
  refine ⟨fun η => ∑ i, a i * r i η, integrable_finsetSum _ fun i _ => (hr i).const_mul _, fun η => ?_, ?_⟩
  · refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ha i)
    have hq2 : Real.sqrt (S η) ^ 2 = S η := Real.sq_sqrt (hS0 η)
    have p1 : ‖η i‖ ≤ t / 2 + ‖η i‖ ^ 2 / (2 * t) := by
      have : 0 ≤ (‖η i‖ - t) ^ 2 / (2 * t) := by positivity
      have e : (‖η i‖ - t) ^ 2 / (2 * t) = t / 2 + ‖η i‖ ^ 2 / (2 * t) - ‖η i‖ := by
        field_simp
        ring
      linarith
    have p2 : Real.sqrt (S η) * ‖η i‖ ≤ (S η + ‖η i‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt (S η) - ‖η i‖)]
    simp only [r]
    have q1 := mul_le_mul_of_nonneg_left p1 hg₀
    have q2 := mul_le_mul_of_nonneg_left p2 (mul_nonneg hg₁ hx.le)
    have e : g₀ / (2 * t) * ‖η i‖ ^ 2 = g₀ * (‖η i‖ ^ 2 / (2 * t)) := by ring
    nlinarith
  · rw [integral_finsetSum _ fun i _ => (hr i).const_mul _, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hri i) (ha i)
end Expectations
section Gradient
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x c : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ}
  {μ : Measure (BondField ι)}
theorem AdmissibleBallLaw.mono_moment (h : AdmissibleBallLaw ρ p x c Φ μ) {c' : ℝ} (hc : c ≤ c') (hx : 0 < x) :
    AdmissibleBallLaw ρ p x c' Φ μ :=
  ⟨h.isProbability, h.expectation_eq, h.integrable_iff, h.ae_mem_ball,
    fun b => (h.moment_le b).trans (div_le_div_of_nonneg_right hc hx.le)⟩
theorem extendByZero_coord_cases {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    (Λ : Finset ι) (b : ↥(chordBonds (finiteCells F))) :
    (∀ ζ : BondField ι, _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b = 0) ∨ ∃ i, ∀ ζ : BondField ι, _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b = ζ i := by
  by_cases h : ∃ i ∈ Λ, j i = b
  · obtain ⟨i, hi, rfl⟩ := h
    exact Or.inr ⟨i, fun ζ => extendByZero_apply_mem hj hi ζ⟩
  · push Not at h
    exact Or.inl fun ζ => extendByZero_apply_of_not ζ h
theorem localSqNorm_extendByZero_integral_le (h : AdmissibleBallLaw ρ p x c Φ μ) (hc : 0 ≤ c) (hx : 0 < x)
    {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (Λ : Finset ι) (κ : ℝ) (Y : F.Cell)
    {W : ℝ} (hW : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * κ * bondDistToCell Y b)) ≤ W) :
    Integrable (fun ζ => localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) μ ∧
      ∫ ζ, localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ∂μ ≤ W * c / x := by
  have hb : ∀ b : ↥(chordBonds (finiteCells F)), Integrable (fun ζ => ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ ^ 2) μ ∧
      ∫ ζ, ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ ^ 2 ∂μ ≤ c / x := by
    intro b
    rcases extendByZero_coord_cases hj Λ b with h0 | ⟨i, hi⟩
    · simp only [h0]
      have := div_nonneg hc hx.le
      simpa using this
    · simp only [hi]
      exact ⟨h.integrable_norm_sq i, h.moment_le i⟩
  unfold localSqNorm
  have hi : ∀ b ∈ (Finset.univ : Finset ↥(chordBonds (finiteCells F))),
      Integrable (fun ζ => Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) *
        ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ ^ 2) μ :=
    fun b _ => (hb b).1.const_mul _
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  calc ∑ b, ∫ ζ, Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ ^ 2 ∂μ
      ≤ ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * κ * bondDistToCell Y b)) * (c / x) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hb b).2 (Real.exp_pos _).le
    _ = (∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * κ * bondDistToCell Y b))) * (c / x) := by
        rw [Finset.sum_mul]
    _ ≤ W * (c / x) := mul_le_mul_of_nonneg_right hW (div_nonneg hc hx.le)
    _ = W * c / x := by ring
theorem continuousOn_bondGradNorm {κ' : Type} [Fintype κ'] [DecidableEq κ'] {H : BondField κ' → ℝ} {ρ : ℝ}
    (hH : ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ}) (b : κ') :
    ContinuousOn (bondGradNorm H b) {η | ∀ b, ‖η b‖ < ρ} := by
  have h1 := hH.continuousOn_fderiv_of_isOpen (isOpen_ball_set ρ) le_rfl
  exact (h1.clm_comp continuousOn_const).norm
theorem hasGradientBound_comp (h : AdmissibleBallLaw ρ p x c Φ μ) (hρ : 0 < ρ) (hc : 0 ≤ c) (hx : 0 < x)
    {κ g₀ g₁ : ℝ} (hκ : 0 ≤ κ) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁) {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ}
    (hA : IsVanishingMoveWithGradient ρ x κ g₀ g₁ Y A) {j : ι → ↥(chordBonds (finiteCells F))}
    (hj : Function.Injective j) (Λ : Finset ι) {W : ℝ}
    (hW : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * κ * bondDistToCell Y b)) ≤ W)
    {dZ : ι → ℝ} (hd : ∀ i, dZ i = bondDistToCell Y (j i)) {hh : ℝ} (h0 : 0 ≤ hh)
    (hbig : 2 * (g₀ ^ 2 + g₁ ^ 2 * x * (W * c)) ≤ x * hh ^ 2) :
    HasGradientBound ρ (cutoffFactor ρ p) Φ x κ hh dZ (fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) := by
  set H : BondField ι → ℝ := fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) with hHdef
  have hball : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ b, ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ < ρ :=
    fun ζ hζ => norm_extendByZero_lt hρ hj Λ hζ
  have hHc : ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ} := by
    have e : H = A ∘ extendByZeroCLM j Λ := by
      funext ζ
      simp [hHdef, extendByZeroCLM_apply]
    rw [e]
    refine hA.smooth.comp (extendByZeroCLM j Λ).contDiff.contDiffOn fun ζ hζ => ?_
    show ∀ b, ‖extendByZeroCLM j Λ ζ b‖ < ρ
    rw [extendByZeroCLM_apply]
    exact hball ζ hζ
  obtain ⟨M, hM⟩ := hA.bounded
  have hHb : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → |H ζ| ≤ M := fun ζ hζ => hM _ (hball ζ hζ)
  have hsq : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ≤ W * ρ ^ 2 := by
    intro ζ hζ
    calc localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)
        ≤ ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * κ * bondDistToCell Y b)) * ρ ^ 2 :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hball ζ hζ b).le 2) (Real.exp_pos _).le
      _ = (∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * κ * bondDistToCell Y b))) * ρ ^ 2 := by
          rw [Finset.sum_mul]
      _ ≤ W * ρ ^ 2 := mul_le_mul_of_nonneg_right hW (by positivity)
  have hdist : ∀ i, 0 ≤ dZ i := fun i => by
    rw [hd]
    exact Nat.cast_nonneg _
  have hpn : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ i, bondGradNorm H i ζ ≤
      (g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)))) * Real.exp (-(2 * κ * dZ i)) := by
    intro ζ hζ i
    have hdiff := differentiableAt_of_mem_ball hA (hball ζ hζ)
    refine (bondGradNorm_comp_extendByZero_le hj Λ hdiff i).trans ?_
    have hnn : 0 ≤ g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y (extendByZero j Λ ζ))) := by positivity
    split_ifs with hi
    · refine (hA.gradient_le _ (hball ζ hζ) (j i)).trans (mul_le_mul_of_nonneg_left ?_ hnn)
      rw [Real.exp_le_exp, hd i]
      have h1 : 0 ≤ κ * bondDistToCell Y (j i) := mul_nonneg hκ (Nat.cast_nonneg _)
      nlinarith
    · positivity
  have hpn0 : ∀ ζ i, 0 ≤ bondGradNorm H i ζ := fun ζ i => norm_nonneg _
  have hbig' : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ i, |bondGradNorm H i ζ| ≤
      g₀ + g₁ * (x * Real.sqrt (W * ρ ^ 2)) := by
    intro ζ hζ i
    rw [abs_of_nonneg (hpn0 ζ i)]
    refine (hpn ζ hζ i).trans ?_
    have e1 : Real.exp (-(2 * κ * dZ i)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg hκ (hdist i)
      linarith
    have e2 : Real.sqrt (localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) ≤ Real.sqrt (W * ρ ^ 2) :=
      Real.sqrt_le_sqrt (hsq ζ hζ)
    have e3 : g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ))) ≤
        g₀ + g₁ * (x * Real.sqrt (W * ρ ^ 2)) := by
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 hx.le) hg₁
      linarith
    have hnn : 0 ≤ g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y (extendByZero j Λ ζ))) := by positivity
    calc _ ≤ (g₀ + g₁ * (x * Real.sqrt (localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)))) * 1 :=
          mul_le_mul_of_nonneg_left e1 hnn
      _ ≤ _ := by rw [mul_one]; exact e3
  refine ⟨fun ζ hζ => ?_, fun k hk => ⟨?_, fun i => ?_⟩, fun i => ?_⟩
  · exact (hHc.contDiffAt ((isOpen_ball_set ρ).mem_nhds hζ)).differentiableAt one_ne_zero
  · refine (h.integrable_iff _).1 (h.integrable_of_bound (M := M ^ k) ?_ ?_)
    · exact (continuous_abs.comp_continuousOn hHc.continuousOn).pow k
    · intro ζ hζ
      simp only [abs_pow, abs_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hHb ζ hζ) k
  · refine (h.integrable_iff _).1
      (h.integrable_of_bound (M := (g₀ + g₁ * (x * Real.sqrt (W * ρ ^ 2))) ^ k) ?_ ?_)
    · exact (continuous_abs.comp_continuousOn (continuousOn_bondGradNorm hHc i)).pow k
    · intro ζ hζ
      simp only [abs_pow, abs_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbig' ζ hζ i) k
  · obtain ⟨hS1, hS2⟩ := localSqNorm_extendByZero_integral_le h hc hx hj Λ κ Y hW
    set E : ℝ := Real.exp (-(2 * κ * dZ i)) with hE
    refine h.momentBound_two
      (G := fun ζ => E ^ 2 * (2 * (g₀ ^ 2 + g₁ ^ 2 * x ^ 2 * localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ))))
      (continuousOn_bondGradNorm hHc i) (hbig' · · i) ?_ ?_ ?_
    · have i1 : Integrable (fun ζ => g₀ ^ 2 + g₁ ^ 2 * x ^ 2 * localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) μ := by
        have := h.isProbability
        exact (integrable_const _).add (hS1.const_mul _)
      exact (i1.const_mul _).const_mul _
    · intro ζ hζ
      have h1 := hpn ζ hζ i
      have h2 := hpn0 ζ i
      rw [sq_abs]
      set S := localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) with hS
      have hS0 : 0 ≤ S := localSqNorm_nonneg κ Y _
      have hr := Real.sq_sqrt hS0
      have h3 : bondGradNorm H i ζ ^ 2 ≤ ((g₀ + g₁ * (x * Real.sqrt S)) * E) ^ 2 := pow_le_pow_left₀ h2 h1 2
      have h4 : (g₀ + g₁ * (x * Real.sqrt S)) ^ 2 ≤ 2 * (g₀ ^ 2 + g₁ ^ 2 * x ^ 2 * S) := by
        have e5 : (g₁ * (x * Real.sqrt S)) ^ 2 = g₁ ^ 2 * x ^ 2 * S := by
          rw [mul_pow, mul_pow, hr]
          ring
        nlinarith [sq_nonneg (g₀ - g₁ * (x * Real.sqrt S))]
      calc _ ≤ _ := h3
        _ = E ^ 2 * (g₀ + g₁ * (x * Real.sqrt S)) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
    · have hprob := h.isProbability
      have i0 : Integrable (fun ζ => g₁ ^ 2 * x ^ 2 * localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) μ :=
        hS1.const_mul _
      have e : ∫ ζ, E ^ 2 * (2 * (g₀ ^ 2 + g₁ ^ 2 * x ^ 2 * localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ))) ∂μ =
          E ^ 2 * (2 * (g₀ ^ 2 + g₁ ^ 2 * x ^ 2 * ∫ ζ, localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ∂μ)) := by
        rw [integral_const_mul, integral_const_mul, integral_add (integrable_const _) i0, integral_const,
          integral_const_mul]
        simp
      rw [e]
      have e1 : g₁ ^ 2 * x ^ 2 * ∫ ζ, localSqNorm κ Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ∂μ ≤ g₁ ^ 2 * x * (W * c) := by
        have := mul_le_mul_of_nonneg_left hS2 (by positivity : 0 ≤ g₁ ^ 2 * x ^ 2)
        refine this.trans (le_of_eq ?_)
        field_simp
      have e2 : (Real.sqrt x * hh * E) ^ 2 = E ^ 2 * (x * hh ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hx.le]
        ring
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
end Gradient
section Laws
variable {F F' : BlockFrame} {T : StepParameters} {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ} {x : ℝ}
  {f : LocalFamily}
theorem integrable_mul_radialWeightProd (hLaw : normalizedBallLawIsProbabilityStatement) {ι : Type} [Fintype ι]
    [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hcut : IsCutoff ρ p) {H : BondField ι → ℝ}
    (hH : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ}) {M : ℝ} (hM : ∀ η, (∀ b, ‖η b‖ < ρ) → |H η| ≤ M) :
    Integrable fun η => H η * radialWeightProd (cutoffFactor ρ p) η := by apply _root_.YangMills.SharedProofs.p23182 <;> assumption
theorem exists_law_freezingHomotopy (hLaw : normalizedBallLawIsProbabilityStatement) (hdr : T.IsOrdered)
    (FB : InterpolatedFrameBoundsAt T Cq Cz Cr t x) {V : F.GaugeField F.top} (hst : IsAdmissibleAt T t x f F V)
    (Λ : Finset ↥(chordBonds (finiteCells F))) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    ∃ μ, AdmissibleBallLaw T.ballRadius T.p x (Cq 1)
      (freezingHomotopy T.chainParams.lam x Λ ((coldHalfLawAt T x f).exponent V) v) μ := by
  have hρ : 0 < T.ballRadius := by
    have := hdr.σ_pos
    unfold StepParameters.ballRadius
    positivity
  set Ψ := (coldHalfLawAt T x f).exponent V with hΨ
  let d : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ :=
    fun i i' => cellSupDist (enclosingCell i.1.1) (enclosingCell i'.1.1)
  let M : Fin 2 → LawOnBondVariables ↥(chordBonds (finiteCells F)) :=
    ![⟨F, V, id, Finset.univ, Ψ⟩, ⟨F, V, id, Λ, Ψ⟩]
  have hw : IsConvexWeights ![v, 1 - v] := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using h0
      · simpa using h1
    · simp
  have hlaw : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ :=
    IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded
  have hM : ∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
      T.L t T.n₀ (frameRadius x) d := by
    intro l
    fin_cases l
    · exact ⟨hst.torus, hst.small_curvature, hlaw, Function.injective_id, fun _ _ => rfl⟩
    · exact ⟨hst.torus, hst.small_curvature, hlaw, Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hc, hm, -⟩ := FB.laws _ d 2 ![v, 1 - v] M hw hM
  have e : convexCombinationExponent T.chainParams.lam x ![v, 1 - v] M =
      freezingHomotopy T.chainParams.lam x Λ Ψ v := by
    funext η
    have h1 : frozenExponent T.chainParams.lam x id Finset.univ Ψ η = Ψ η := by
      unfold frozenExponent
      rw [extendByZero_id_univ]
      simp
    show ∑ l, ![v, 1 - v] l * (M l).exponent T.chainParams.lam x η =
      v * Ψ η + (1 - v) * frozenExponent T.chainParams.lam x id Λ Ψ η
    rw [Fin.sum_univ_two]
    show v * frozenExponent T.chainParams.lam x id Finset.univ Ψ η +
      (1 - v) * frozenExponent T.chainParams.lam x id Λ Ψ η = _
    rw [h1]
  rw [e] at hc hm
  exact exists_admissibleBallLaw hLaw hρ hdr.cutoff hc hm
theorem exists_law_pairingHomotopy (hLaw : normalizedBallLawIsProbabilityStatement) (hdr : T.IsOrdered)
    (FB : InterpolatedFrameBoundsAt T Cq Cz Cr t x) {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    (hst : IsAdmissibleAt T t x f F V) (hst' : IsAdmissibleAt T t x f F' V') {ι : Type} [Fintype ι]
    [DecidableEq ι] {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hj : Function.Injective j) (hj' : Function.Injective j')
    (hdist : ∀ i i', cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1) =
      cellSupDist (enclosingCell (j' i).1.1) (enclosingCell (j' i').1.1))
    {th : ℝ} (h0 : 0 ≤ th) (h1 : th ≤ 1) :
    ∃ μ, AdmissibleBallLaw T.ballRadius T.p x (Cq 1)
      (pairingHomotopy j j' ((coldHalfLawAt T x f).exponent V) ((coldHalfLawAt T x f).exponent V') th) μ := by
  have hρ : 0 < T.ballRadius := by
    have := hdr.σ_pos
    unfold StepParameters.ballRadius
    positivity
  set Ψ := (coldHalfLawAt T x f).exponent V with hΨ
  set Ψ' := (coldHalfLawAt T x f).exponent V' with hΨ'
  let d : ι → ι → ℝ := fun i i' => cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1)
  let M : Fin 2 → LawOnBondVariables ι := ![⟨F, V, j, Finset.univ, Ψ⟩, ⟨F', V', j', Finset.univ, Ψ'⟩]
  have hw : IsConvexWeights ![th, 1 - th] := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using h0
      · simpa using h1
    · simp
  have hlaw : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ :=
    IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded
  have hlaw' : IsIntermediateLaw T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x)
      (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V' Ψ' :=
    IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst'.family_bounded
  have hM : ∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
      T.L t T.n₀ (frameRadius x) d := by
    intro l
    fin_cases l
    · exact ⟨hst.torus, hst.small_curvature, hlaw, hj, fun _ _ => rfl⟩
    · exact ⟨hst'.torus, hst'.small_curvature, hlaw', hj', fun i i' => by
        show (cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1) : ℝ) = _
        rw [hdist i i']
        rfl⟩
  obtain ⟨hc, hm, -⟩ := FB.laws _ d 2 ![th, 1 - th] M hw hM
  have e : convexCombinationExponent T.chainParams.lam x ![th, 1 - th] M = pairingHomotopy j j' Ψ Ψ' th := by
    funext η
    simp [convexCombinationExponent, Fin.sum_univ_two, M, LawOnBondVariables.exponent, pairingHomotopy,
      frozenExponent, toTorus]
  rw [e] at hc hm
  exact exists_admissibleBallLaw hLaw hρ hdr.cutoff hc hm
theorem shortPairing_distances (hOff : Estimates.cellOffsetStatement) {q : ℕ} {Y : F.Cell} {Y' : F'.Cell}
    {ι : Type} {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hL : Odd F.blockSide) (hL' : F'.blockSide = F.blockSide)
    (hs : ∀ i, 2 * q + 2 < F.extent i) (hs' : ∀ i, 2 * q + 2 < F'.extent i) (hp : IsShortPairing Y Y' q j j') :
    (∀ i i', cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1) =
      cellSupDist (enclosingCell (j' i).1.1) (enclosingCell (j' i').1.1)) ∧
    ∀ i, bondDistToCell Y (j i) = bondDistToCell Y' (j' i) := by apply _root_.YangMills.SharedProofs.p91775 <;> assumption
end Laws
section Amplitude
variable {F F' : BlockFrame} {T : StepParameters}
def amplitudeConstant (W c : ℝ) : ℝ := 8 * (1 + W) ^ 2 * (1 + c) ^ 2
theorem sum_exp_comp_injective_le {κ : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι] {Y : F.Cell}
    {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) :
    ∑ i, Real.exp (-(κ * bondDistToCell Y (j i))) ≤
      ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(κ * bondDistToCell Y b)) := by apply _root_.YangMills.SharedProofs.p95346 <;> assumption
theorem exp_neg_mul_le {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 1 ≤ r) (Y : F.Cell) (b : ↥(chordBonds (finiteCells F))) :
    Real.exp (-(r * κ * bondDistToCell Y b)) ≤ Real.exp (-(κ * bondDistToCell Y b)) := by
  rw [Real.exp_le_exp]
  have h1 : 0 ≤ κ * bondDistToCell Y b := mul_nonneg hκ (Nat.cast_nonneg _)
  nlinarith
theorem abs_integral_sub_extendByZero_le {ρ x c κ g₀ g₁ W : ℝ} {p : ℝ → ℝ}
    {Φ : BondField ↥(chordBonds (finiteCells F)) → ℝ} {μ : Measure (BondField ↥(chordBonds (finiteCells F)))}
    (h : AdmissibleBallLaw ρ p x c Φ μ) (hc : 0 ≤ c) (hx : 0 < x) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁) {Y : F.Cell}
    {A : StepVariable (finiteCells F) → ℝ} (hA : IsVanishingMoveWithGradient ρ x κ g₀ g₁ Y A)
    (hW : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * κ * bondDistToCell Y b)) ≤ W)
    (Λ : Finset ↥(chordBonds (finiteCells F))) (a : ↥(chordBonds (finiteCells F)) → ℝ)
    (ha : ∀ b, a b = if b ∈ Λ then 0 else Real.exp (-(2 ^ 5 * κ * bondDistToCell Y b))) :
    |∫ η, (A η - A (_root_.YangMills.Construction.Interpolation.extendByZero id Λ η)) ∂μ| ≤ (∑ b, a b) *
      (g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + c) / 2) + g₁ * ((W * c + c) / 2)) := by
  obtain ⟨hS1, hS2⟩ :=
    localSqNorm_extendByZero_integral_le h hc hx (j := id) Function.injective_id Finset.univ κ Y hW
  simp only [extendByZero_id_univ] at hS1 hS2
  have ha0 : ∀ b, 0 ≤ a b := fun b => by
    rw [ha]
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  obtain ⟨R, hR1, hR2, hR3⟩ := h.exists_majorant hx hg₀ hg₁ hS1 (localSqNorm_nonneg κ Y) hS2 a ha0
  refine le_trans ?_ hR3
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hR1 (h.ae_mem_ball.mono fun η hη => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_sub_extendByZero_le hA hg₀ hg₁ hx.le Λ hη).trans (le_trans (le_of_eq ?_) (hR2 η))
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ha]
  split_ifs
  · simp
  · ring
theorem comparisonBoundsOnTorus (hLaw : normalizedBallLawIsProbabilityStatement) (hdr : T.IsOrdered)
    {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ} {x : ℝ} {f : LocalFamily}
    (FB : InterpolatedFrameBoundsAt T Cq Cz Cr t x) (hx : 1 ≤ x) {V : F.GaugeField F.top}
    (hst : IsAdmissibleAt T t x f F V) {g₀ g₁ W α : ℝ} (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁) {Y : F.Cell}
    {A : StepVariable (finiteCells F) → ℝ} (hA : IsVanishingMoveWithGradient T.ballRadius x T.κ g₀ g₁ Y A)
    (hW : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ * bondDistToCell Y b)) ≤ W) (hα : 0 ≤ α)
    (hgr : 2 * (g₀ ^ 2 + g₁ ^ 2 * x * (W * |Cq 1|)) ≤ x * α ^ 2)
    (hme : W * (g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + |Cq 1|) / 2) + g₁ * ((W * |Cq 1| + |Cq 1|) / 2)) ≤ α) (q : ℕ) :
    ComparisonHypothesesOnTorus T.ballRadius T.chainParams.lam x T.κ α T.p q Y ((coldHalfLawAt T x f).exponent V) A := by
  have hρ : 0 < T.ballRadius := by
    have := hdr.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hκ := hdr.κ_pos
  have hx0 : 0 < x := by linarith
  have hc : 0 ≤ |Cq 1| := abs_nonneg _
  have hW6 : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * T.κ * bondDistToCell Y b)) ≤ W :=
    (Finset.sum_le_sum fun b _ => exp_neg_mul_le hκ.le (by norm_num) Y b).trans hW
  obtain ⟨M, hM⟩ := hA.bounded
  have hfc : ∀ Λ : Finset ↥(chordBonds (finiteCells F)),
      ContinuousOn (fun η => A (freezeOutside Λ η)) {η | ∀ b, ‖η b‖ < T.ballRadius} := by
    intro Λ
    have e : (fun η => A (freezeOutside Λ η)) = A ∘ extendByZeroCLM id Λ := by
      funext η
      simp [extendByZeroCLM_apply, freezeOutside]
    rw [e]
    refine hA.smooth.continuousOn.comp (extendByZeroCLM id Λ).continuous.continuousOn fun η hη => ?_
    show ∀ b, ‖extendByZeroCLM id Λ η b‖ < T.ballRadius
    rw [extendByZeroCLM_apply]
    exact norm_extendByZero_lt hρ Function.injective_id Λ hη
  have law : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∃ μ, AdmissibleBallLaw T.ballRadius T.p x |Cq 1|
      (freezingHomotopy T.chainParams.lam x (bondsNearCell Y q) ((coldHalfLawAt T x f).exponent V) v) μ := by
    intro v h0 h1
    obtain ⟨μ, hμ⟩ := exists_law_freezingHomotopy hLaw hdr FB hst (bondsNearCell Y q) h0 h1
    exact ⟨μ, hμ.mono_moment (le_abs_self _) hx0⟩
  refine ⟨integrable_mul_radialWeightProd hLaw hρ hdr.cutoff hA.smooth.continuousOn hM,
    integrable_mul_radialWeightProd hLaw hρ hdr.cutoff (hfc _)
      (fun η hη => hM _ (norm_extendByZero_lt hρ Function.injective_id _ hη)),
    fun v h0 h1 => ?_, fun v h0 h1 => ?_, fun v h0 h1 => ?_⟩
  · obtain ⟨μ, hμ⟩ := law v h0 h1
    have := hasGradientBound_comp hμ hρ hc hx0 hκ.le hg₀ hg₁ hA (j := id) Function.injective_id Finset.univ hW6
      (dZ := bondDistToCell Y) (fun _ => rfl) hα hgr
    simpa only [extendByZero_id_univ] using this
  · obtain ⟨μ, hμ⟩ := law v h0 h1
    exact hasGradientBound_comp hμ hρ hc hx0 hκ.le hg₀ hg₁ hA (j := id) Function.injective_id (bondsNearCell Y q)
      hW6 (dZ := bondDistToCell Y) (fun _ => rfl) hα hgr
  · obtain ⟨μ, hμ⟩ := law v h0 h1
    rw [hμ.expectation_eq]
    have h1' := abs_integral_sub_extendByZero_le hμ hc hx0 hg₀ hg₁ hA hW6 (bondsNearCell Y q) _ fun _ => rfl
    refine h1'.trans ?_
    have hm0 : 0 ≤ g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + |Cq 1|) / 2) + g₁ * ((W * |Cq 1| + |Cq 1|) / 2) := by
      have hW0 : 0 ≤ W := le_trans (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le) hW
      have := Real.rpow_pos_of_pos hx0 (-(1 / 2) : ℝ)
      positivity
    have hsum : (∑ b : ↥(chordBonds (finiteCells F)), if b ∈ bondsNearCell Y q then (0 : ℝ) else
        Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y b))) ≤ Real.exp (-(4 * T.κ * q)) * W := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      split_ifs with hb
      · positivity
      · rw [← Real.exp_add, Real.exp_le_exp]
        have hb' : (q : ℝ) < 2 * bondDistToCell Y b := by
          have : ¬ 2 * cellSupDist (enclosingCell b.1.1) Y ≤ q := fun h => hb (by simp [bondsNearCell, h])
          have h2 : q < 2 * cellSupDist (enclosingCell b.1.1) Y := not_le.1 this
          unfold bondDistToCell
          exact_mod_cast h2
        nlinarith [mul_pos hκ (by linarith [Nat.cast_nonneg (α := ℝ) q] : (0 : ℝ) < 2 * bondDistToCell Y b + 1),
          mul_nonneg hκ.le (Nat.cast_nonneg (α := ℝ) q), mul_le_mul_of_nonneg_left hb'.le hκ.le,
          mul_nonneg hκ.le (Nat.cast_nonneg (α := ℝ) (cellSupDist (enclosingCell b.1.1) Y))]
    calc _ ≤ (Real.exp (-(4 * T.κ * q)) * W) * _ := mul_le_mul_of_nonneg_right hsum hm0
      _ = Real.exp (-(4 * T.κ * q)) * (W * (g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + |Cq 1|) / 2) +
          g₁ * ((W * |Cq 1| + |Cq 1|) / 2))) := by ring
      _ ≤ Real.exp (-(4 * T.κ * q)) * α := mul_le_mul_of_nonneg_left hme (Real.exp_pos _).le
      _ = α * Real.exp (-(4 * T.κ * q)) := by ring
end Amplitude
section Assembly
variable {T : StepParameters}
theorem amplitude_bounds {W c g₀ g₁ x : ℝ} (hW : 0 ≤ W) (hc : 0 ≤ c) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁) (hx : 0 < x) :
    2 * (g₀ ^ 2 + g₁ ^ 2 * x * (W * c)) ≤ x * (amplitudeConstant W c * (g₀ * x ^ (-(1 / 2) : ℝ) + g₁)) ^ 2 ∧
    2 * (W * (g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + c) / 2) + g₁ * ((W * c + c) / 2))) ≤
      amplitudeConstant W c * (g₀ * x ^ (-(1 / 2) : ℝ) + g₁) ∧
    W * (g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + c) / 2)) + g₁ * (W * c + 1) ≤
      amplitudeConstant W c * (g₀ * x ^ (-(1 / 2) : ℝ) + g₁) := by
  set t : ℝ := x ^ (-(1 / 2) : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx _
  have ht2 : t ^ 2 = x⁻¹ := rpow_neg_half_sq hx
  have hxt : x * t ^ 2 = 1 := by rw [ht2]; exact mul_inv_cancel₀ hx.ne'
  set B := amplitudeConstant W c with hB
  have hWc : 0 ≤ W * c := mul_nonneg hW hc
  have hB1 : 8 * (1 + W) ^ 2 * (1 + c) ^ 2 = B := rfl
  have hB8 : 8 * ((1 + W) * (1 + c)) ≤ B := by
    have : ((1 + W) * (1 + c)) ≤ ((1 + W) * (1 + c)) ^ 2 := by nlinarith
    nlinarith
  have hBbig : 2 * (W * c) ≤ B ^ 2 ∧ 2 ≤ B ^ 2 := by
    constructor <;> nlinarith
  have hB3 : W * (1 + c) ≤ B / 2 := by nlinarith
  have hB4 : 2 * (W * ((W * c + c) / 2)) ≤ B := by
    have : W * (W * c + c) ≤ 8 * (1 + W) ^ 2 * (1 + c) ^ 2 := by
      have e2 : (1 + W) ^ 2 * (1 + c) ≤ (1 + W) ^ 2 * (1 + c) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith
      nlinarith [mul_nonneg (sq_nonneg (1 + W)) (sq_nonneg (1 + c))]
    nlinarith
  have hgt : 0 ≤ g₀ * t := mul_nonneg hg₀ ht0.le
  refine ⟨?_, ?_, ?_⟩
  · have e : x * (B * (g₀ * t + g₁)) ^ 2 =
        B ^ 2 * (g₀ ^ 2 * (x * t ^ 2) + 2 * g₀ * g₁ * t * x + g₁ ^ 2 * x) := by ring
    rw [e, hxt]
    have h1 : 0 ≤ 2 * g₀ * g₁ * t * x := by positivity
    have h2 : g₀ ^ 2 * 2 ≤ B ^ 2 * g₀ ^ 2 := by nlinarith [sq_nonneg g₀, hBbig.2]
    have h3 : g₁ ^ 2 * x * (2 * (W * c)) ≤ B ^ 2 * (g₁ ^ 2 * x) := by
      have : 0 ≤ g₁ ^ 2 * x := by positivity
      nlinarith [hBbig.1]
    have h4 : 0 ≤ B ^ 2 * (2 * g₀ * g₁ * t * x) := by positivity
    nlinarith
  · have h1 : g₀ * t * (W * (1 + c)) ≤ g₀ * t * (B / 2) := mul_le_mul_of_nonneg_left hB3 hgt
    have h2 : g₁ * (2 * (W * ((W * c + c) / 2))) ≤ g₁ * B := mul_le_mul_of_nonneg_left hB4 hg₁
    nlinarith
  · have h1 : g₀ * t * (W * (1 + c)) ≤ g₀ * t * (B / 2) := mul_le_mul_of_nonneg_left hB3 hgt
    have h2 : g₁ * (W * c + 1) ≤ g₁ * (B / 2) := mul_le_mul_of_nonneg_left (by linarith) hg₁
    have hB0 : 0 ≤ B := by linarith [mul_nonneg hW hc]
    nlinarith [mul_nonneg hgt hB0, mul_nonneg hg₁ hB0]
theorem comparisonFromGradientBoundsAt_of (hLaw : normalizedBallLawIsProbabilityStatement)
    (hOff : Estimates.cellOffsetStatement) (hdr : T.IsOrdered) (hy : 1 ≤ T.coupling) (hn : 2 ≤ T.n₀)
    {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hFB : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x) {W : ℝ} (hW0 : 0 ≤ W)
    (hWs : ∀ F : BlockFrame, F.blockSide = T.L → (∀ i, 2 ≤ F.extent i) → ∀ Y : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ * bondDistToCell Y b)) ≤ W) :
    ComparisonFromGradientBoundsAt T (amplitudeConstant W |Cq 1|) := by
  intro t x f F F' V V' Y Y' q ι _ _ j j' g₀ g₁ α A A' hst hst' hag hnp hg₀ hg₁ hαge hA hA' hsh
  have hx1 : 1 ≤ x := hy.trans hst.coupling_le
  have hx : 0 < x := by linarith
  have hκ := hdr.κ_pos
  have hc : 0 ≤ |Cq 1| := abs_nonneg _
  have hFL : F.blockSide = T.L := hst.torus.1
  have hFL' : F'.blockSide = T.L := hst'.torus.1
  obtain ⟨-, -, n, hside, hnn⟩ := hst.torus
  obtain ⟨-, -, n', hside', hnn'⟩ := hst'.torus
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hside']; omega
  have sd : ∀ i, 2 * q + 2 < F.extent i := fun i => by
    rcases hag.1 i with h0 | h0
    · have := hs2 i
      omega
    · exact h0
  have sd' : ∀ i, 2 * q + 2 < F'.extent i := fun i => by
    rcases hag.2.1 i with h0 | h0
    · have := hs2' i
      omega
    · exact h0
  have hLo : Odd F.blockSide := by rw [hFL]; exact hdr.odd_L
  obtain ⟨hd1, hd2⟩ := shortPairing_distances hOff hLo (hFL'.trans hFL.symm) sd sd' hnp
  have hj := hnp.isBoxPairing.injective_left
  have hj' := hnp.isBoxPairing.injective_right
  have FB := hFB t x hst.coupling_le
  have hW1 := hWs F hFL hs2 Y
  have hW2 := hWs F' hFL' hs2' Y'
  obtain ⟨a1, a2, a3⟩ := amplitude_bounds (x := x) hW0 hc hg₀ hg₁ hx
  have ht0 : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
  have hB0 : 0 ≤ amplitudeConstant W |Cq 1| := by unfold amplitudeConstant; positivity
  have hα₀ : 0 ≤ amplitudeConstant W |Cq 1| * (g₀ * x ^ (-(1 / 2) : ℝ) + g₁) := mul_nonneg hB0 (by positivity)
  have hα : 0 ≤ α := hα₀.trans hαge
  replace a1 : 2 * (g₀ ^ 2 + g₁ ^ 2 * x * (W * |Cq 1|)) ≤ x * α ^ 2 :=
    a1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hα₀ hαge 2) hx.le)
  replace a2 := a2.trans hαge
  replace a3 := a3.trans hαge
  set m := g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + |Cq 1|) / 2) + g₁ * ((W * |Cq 1| + |Cq 1|) / 2) with hm
  have hm0 : 0 ≤ m := by positivity
  have hme : W * m ≤ α := by
    have : 0 ≤ W * m := by positivity
    linarith
  have hρ : 0 < T.ballRadius := by
    have := hdr.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have mean1 : ∀ {G : BlockFrame} {U : G.GaugeField G.top} {Z : G.Cell} {B : StepVariable (finiteCells G) → ℝ},
      IsAdmissibleAt T t x f G U → IsVanishingMoveWithGradient T.ballRadius x T.κ g₀ g₁ Z B →
      (∑ b : ↥(chordBonds (finiteCells G)), Real.exp (-(T.κ * bondDistToCell Z b)) ≤ W) →
      |ballExpectation (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent U) B| ≤ W * m := by
    intro G U Z B hs hB hWZ
    obtain ⟨μ, hμ⟩ := exists_law_freezingHomotopy hLaw hdr FB hs ∅ zero_le_one le_rfl
    have hμ' := hμ.mono_moment (le_abs_self _) hx
    have e : freezingHomotopy T.chainParams.lam x ∅ ((coldHalfLawAt T x f).exponent U) 1 =
        (coldHalfLawAt T x f).exponent U := by
      funext η
      simp [freezingHomotopy]
    rw [e] at hμ'
    have hW6 : ∑ b : ↥(chordBonds (finiteCells G)), Real.exp (-(2 ^ 6 * T.κ * bondDistToCell Z b)) ≤ W :=
      (Finset.sum_le_sum fun b _ => exp_neg_mul_le hκ.le (by norm_num) Z b).trans hWZ
    have h1 := abs_integral_sub_extendByZero_le hμ' hc hx hg₀ hg₁ hB hW6 ∅ _ fun _ => rfl
    have ez : ∀ η : StepVariable (finiteCells G), _root_.YangMills.Construction.Interpolation.extendByZero id ∅ η = 0 := fun η => by
      funext b
      simp [_root_.YangMills.Construction.Interpolation.extendByZero]
    simp only [ez, hB.map_zero, sub_zero] at h1
    rw [hμ'.expectation_eq]
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hm0)
    simp only [Finset.notMem_empty, if_false]
    exact (Finset.sum_le_sum fun b _ => exp_neg_mul_le hκ.le (by norm_num) Z b).trans hWZ
  have hW6 : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * T.κ * bondDistToCell Y b)) ≤ W :=
    (Finset.sum_le_sum fun b _ => exp_neg_mul_le hκ.le (by norm_num) Y b).trans hW1
  have hW6' : ∑ b : ↥(chordBonds (finiteCells F')), Real.exp (-(2 ^ 6 * T.κ * bondDistToCell Y' b)) ≤ W :=
    (Finset.sum_le_sum fun b _ => exp_neg_mul_le hκ.le (by norm_num) Y' b).trans hW2
  have law : ∀ th : ℝ, 0 ≤ th → th ≤ 1 → ∃ μ, AdmissibleBallLaw T.ballRadius T.p x |Cq 1|
      (pairingHomotopy j j' ((coldHalfLawAt T x f).exponent V) ((coldHalfLawAt T x f).exponent V') th) μ := by
    intro th h0 h1
    obtain ⟨μ, hμ⟩ := exists_law_pairingHomotopy hLaw hdr FB hst hst' hj hj' hd1 h0 h1
    exact ⟨μ, hμ.mono_moment (le_abs_self _) hx⟩
  refine ⟨comparisonBoundsOnTorus hLaw hdr FB hx1 hst hg₀ hg₁ hA hW1 hα a1 hme q,
    comparisonBoundsOnTorus hLaw hdr FB hx1 hst' hg₀ hg₁ hA' hW2 hα a1 hme q, ?_,
    fun th h0 h1 => ?_, fun hq th h0 h1 => ?_⟩
  · have b1 := mean1 hst hA hW1
    have b2 := mean1 hst' hA' hW2
    refine (abs_sub _ _).trans ?_
    linarith
  · obtain ⟨μ, hμ⟩ := law th h0 h1
    exact ⟨hasGradientBound_comp hμ hρ hc hx hκ.le hg₀ hg₁ hA hj Finset.univ hW6 (fun _ => rfl) hα a1,
      hasGradientBound_comp hμ hρ hc hx hκ.le hg₀ hg₁ hA' hj' Finset.univ hW6' (fun i => hd2 i) hα a1⟩
  · obtain ⟨μ, hμ⟩ := law th h0 h1
    have hprob := hμ.isProbability
    obtain ⟨hS1, hS2⟩ := localSqNorm_extendByZero_integral_le hμ hc hx hj Finset.univ T.κ Y hW6
    have ha0 : ∀ i, 0 ≤ Real.exp (-(T.κ * bondDistToCell Y (j i))) := fun i => (Real.exp_pos _).le
    obtain ⟨R, hR1, hR2, hR3⟩ :=
      hμ.exists_majorant hx hg₀ le_rfl hS1 (fun ζ => localSqNorm_nonneg T.κ Y _) hS2 _ ha0
    have hsumW : ∑ i, Real.exp (-(T.κ * bondDistToCell Y (j i))) ≤ W :=
      (sum_exp_comp_injective_le hj).trans hW1
    set e₄ : ℝ := Real.exp (-(4 * T.κ * q)) with he₄
    have he₄0 : 0 < e₄ := Real.exp_pos _
    let S₂ : BondField ι → ℝ := fun ζ => ∑ i, Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2
    have hS₂i : ∀ i ∈ (Finset.univ : Finset ι), Integrable
        (fun ζ : BondField ι => Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2) μ :=
      fun i _ => (hμ.integrable_norm_sq i).const_mul _
    have hS₂1 : Integrable S₂ μ := integrable_finsetSum _ hS₂i
    have hS₂2 : ∫ ζ, S₂ ζ ∂μ ≤ W * |Cq 1| / x := by
      simp only [S₂]
      rw [integral_finsetSum _ hS₂i]
      have hsum5 : ∑ i, Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i))) ≤ W :=
        (sum_exp_comp_injective_le hj).trans
          ((Finset.sum_le_sum fun b _ => exp_neg_mul_le hκ.le (by norm_num) Y b).trans hW1)
      calc ∑ i, ∫ ζ, Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2 ∂μ
          ≤ ∑ i, Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i))) * (|Cq 1| / x) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [integral_const_mul]
            exact mul_le_mul_of_nonneg_left (hμ.moment_le i) (Real.exp_pos _).le
        _ = (∑ i, Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i)))) * (|Cq 1| / x) := by rw [Finset.sum_mul]
        _ ≤ W * (|Cq 1| / x) := mul_le_mul_of_nonneg_right hsum5 (div_nonneg hc hx.le)
        _ = W * |Cq 1| / x := by ring
    let G : BondField ι → ℝ := fun ζ => e₄ * (R ζ + g₁ * (x * S₂ ζ + 1))
    have hi0 : Integrable (fun ζ => g₁ * (x * S₂ ζ + 1)) μ :=
      ((hS₂1.const_mul x).add (integrable_const _)).const_mul _
    have hG : Integrable G μ := (hR1.add hi0).const_mul _
    rw [hμ.expectation_eq]
    have hle : ∫ ζ, G ζ ∂μ ≤ α * e₄ := by
      have e : ∫ ζ, G ζ ∂μ = e₄ * (∫ ζ, R ζ ∂μ + g₁ * (x * ∫ ζ, S₂ ζ ∂μ + 1)) := by
        simp only [G]
        rw [integral_const_mul, integral_add hR1 hi0, integral_const_mul,
          integral_add (hS₂1.const_mul x) (integrable_const _), integral_const_mul]
        simp
      rw [e, mul_comm α]
      refine mul_le_mul_of_nonneg_left ?_ he₄0.le
      have c1 : x * ∫ ζ, S₂ ζ ∂μ ≤ W * |Cq 1| := by
        have := mul_le_mul_of_nonneg_left hS₂2 hx.le
        refine this.trans (le_of_eq ?_)
        field_simp
      have c2 := mul_le_mul_of_nonneg_left (add_le_add_left c1 1) hg₁
      have c3 : ∫ ζ, R ζ ∂μ ≤ W * (g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + |Cq 1|) / 2)) := by
        refine hR3.trans ?_
        have : (0 : ℝ) ≤ g₀ * x ^ (-(1 / 2) : ℝ) * ((1 + |Cq 1|) / 2) := by positivity
        simpa using mul_le_mul_of_nonneg_right hsumW (by simpa using this)
      nlinarith
    refine le_trans ?_ hle
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hG (hμ.ae_mem_ball.mono fun ζ hζ => ?_)
    rw [Real.norm_eq_abs]
    refine (hsh hq ζ hζ).trans (mul_le_mul_of_nonneg_left ?_ he₄0.le)
    have e2 := hR2 ζ
    simp only [zero_mul, add_zero, mul_zero] at e2
    have e3 : g₀ * ∑ i, Real.exp (-(T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ≤ R ζ := by
      refine le_trans (le_of_eq ?_) e2
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    linarith
end Assembly
end GradientMoves
open GradientMoves in
theorem comparisonFromGradientBounds_holds (hFr : interpolatedFramesStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement) (hOff : Estimates.cellOffsetStatement)
    (hSum : CellCounting.ExpDecaySumBounded) (hFew : Estimates.cellBondsCardStatement)
    (hJ : EventuallyInParametersCombines) (hOne : SummableBounds.couplingAtLeastOneStatement)
    (hLet : transportConditionsEventually) : comparisonFromGradientBoundsStatement := by
  classical
  obtain ⟨Cq, Cz, Cr, hF⟩ := hFr
  let Wf : StepParameters → ℝ := fun T =>
    if h : 0 < T.κ then Classical.choose (hSum (4 * T.L ^ 4) T.κ h) else 0
  refine ⟨fun T => amplitudeConstant (|Wf T|) |Cq (momentParameters T) 1|, fun T => ?_, ?_⟩
  · unfold amplitudeConstant
    positivity
  refine hJ.2 _ _ (fun T hdr h => ?_) (hJ.1 _ _ (hOne _ hF) (hLet fun _ => 0))
  obtain ⟨⟨hFB, hy⟩, hl⟩ := h
  have hn : 2 ≤ T.n₀ := by
    have := hl.2.2.2.1
    omega
  have hκ := hdr.κ_pos
  have hW : Wf T = Classical.choose (hSum (4 * T.L ^ 4) T.κ hκ) := dif_pos hκ
  have hspec := Classical.choose_spec (hSum (4 * T.L ^ 4) T.κ hκ)
  rw [← hW] at hspec
  refine comparisonFromGradientBoundsAt_of hLaw hOff hdr hy hn (fun t x h => hFB t x h) (abs_nonneg _)
    fun F hFL hs Y => ?_
  show ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ |Wf T|
  refine le_trans (hspec.2 F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) (fun z => ?_) Y)
    (le_abs_self _)
  have := hFew F (by rw [hFL]; exact hdr.odd_L) hs z
  rwa [hFL] at this
end WeightedResponses
end YangMills.Construction
end
