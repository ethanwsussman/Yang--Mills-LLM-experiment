import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ResponseInTheExpansion.SizeOfASumOfObservables
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithTheirConstantsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.ConvexObservables
namespace YangMills.Construction.WeightedResponses
namespace SumBounds
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem abs_sum_pow_le_weighted {J : Type} (S : Finset J) (f : J → ℝ) (w : J → ℝ) (hw : ∀ j, 0 < w j) (q : ℕ)
    (hq : 1 ≤ q) (hS : S.Nonempty) :
    |∑ j ∈ S, f j| ^ q ≤ (∑ j ∈ S, w j) ^ (q - 1) * ∑ j ∈ S, (w j)⁻¹ ^ (q - 1) * |f j| ^ q := by
  have hT : 0 < ∑ j ∈ S, w j := Finset.sum_pos (fun j _ => hw j) hS
  set T := ∑ j ∈ S, w j with hTdef
  have hone : ∑ j ∈ S, w j / T = 1 := by rw [← Finset.sum_div, div_self hT.ne']
  have h1 := Real.pow_arith_mean_le_arith_mean_pow S (fun j => w j / T) (fun j => |f j| * (T / w j))
    (fun j _ => (div_pos (hw j) hT).le) hone (fun j _ => mul_nonneg (abs_nonneg _) (div_pos hT (hw j)).le) q
  have e1 : ∑ j ∈ S, w j / T * (|f j| * (T / w j)) = ∑ j ∈ S, |f j| := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (hw j).ne'
    field_simp
  rw [e1] at h1
  have h2 : |∑ j ∈ S, f j| ^ q ≤ (∑ j ∈ S, |f j|) ^ q :=
    pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) _
  refine h2.trans (h1.trans (le_of_eq ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have := (hw j).ne'
  have hT' := hT.ne'
  simp only [Nat.add_sub_cancel, mul_pow, div_pow, pow_succ, inv_pow]
  field_simp
def openBondBall (ι : Type) (ρ : ℝ) : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ}
theorem isOpen_openBondBall (ρ : ℝ) : IsOpen (openBondBall ι ρ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.isOpen_ballProduct <;> assumption
theorem continuousOn_bondGradNorm {O : Set (BondField ι)} (hO : IsOpen O)
    {f : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f O) (b : ι) : ContinuousOn (bondGradNorm f b) O := by apply _root_.YangMills.Construction.Cumulants.continuousOn_bondGradNorm <;> assumption
variable {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
structure BallLawFacts (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) : Prop where
  isProbability : IsProbabilityMeasure (normalizedBallLaw (cutoffFactor ρ p) Ψ)
  integral_eq : ∀ f : BondField ι → ℝ,
    ∫ η, f η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ = ballExpectation (cutoffFactor ρ p) Ψ f
  integrable_iff : ∀ f : BondField ι → ℝ, Integrable f (normalizedBallLaw (cutoffFactor ρ p) Ψ) ↔
    Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η
  ae_mem_ball : ∀ᵐ η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ, ∀ b, ‖η b‖ < ρ
theorem aestronglyMeasurable_of_continuousOn (hL : BallLawFacts ρ p Ψ) {g : BondField ι → ℝ}
    (hg : ContinuousOn g (openBondBall ι ρ)) :
    AEStronglyMeasurable g (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
  have hm : MeasurableSet (openBondBall ι ρ) := (isOpen_openBondBall ρ).measurableSet
  have h1 := hg.aestronglyMeasurable (μ := normalizedBallLaw (cutoffFactor ρ p) Ψ) hm
  rwa [Measure.restrict_eq_self_of_ae_mem (by exact hL.ae_mem_ball)] at h1
theorem momentBound_mono (hL : BallLawFacts ρ p Ψ) {f g : BondField ι → ℝ} {q : ℕ} {C C' : ℝ}
    (hf : ContinuousOn f (openBondBall ι ρ)) (hle : ∀ η ∈ openBondBall ι ρ, |f η| ≤ |g η|)
    (hC : 0 ≤ C) (hCC : C ≤ C') (hg : MomentBound (cutoffFactor ρ p) Ψ g q C) :
    MomentBound (cutoffFactor ρ p) Ψ f q C' := by
  have := hL.isProbability
  obtain ⟨h1, h2⟩ := hg
  have hi : Integrable (fun η => |g η| ^ q) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
    (hL.integrable_iff _).2 h1
  have hae : AEStronglyMeasurable (fun η => |f η| ^ q) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
    aestronglyMeasurable_of_continuousOn hL ((hf.abs).pow q)
  have hle' : ∀ᵐ η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ, |f η| ^ q ≤ |g η| ^ q := by
    filter_upwards [hL.ae_mem_ball] with η hη
    exact pow_le_pow_left₀ (abs_nonneg _) (hle η hη) _
  have hfi : Integrable (fun η => |f η| ^ q) (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    refine Integrable.mono' hi hae ?_
    filter_upwards [hle'] with η hη
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hη
  refine ⟨(hL.integrable_iff _).1 hfi, ?_⟩
  have h3 : ∫ η, |f η| ^ q ∂normalizedBallLaw (cutoffFactor ρ p) Ψ ≤
      ∫ η, |g η| ^ q ∂normalizedBallLaw (cutoffFactor ρ p) Ψ :=
    integral_mono_ae hfi hi hle'
  rw [hL.integral_eq, hL.integral_eq] at h3
  exact h3.trans (h2.trans (pow_le_pow_left₀ hC hCC _))
theorem momentBound_finset_sum (hL : BallLawFacts ρ p Ψ) {J : Type} (S : Finset J) (f : J → BondField ι → ℝ)
    (C : J → ℝ) (hC : ∀ j, 0 < C j) (q : ℕ) (hq : 1 ≤ q) (hc : ∀ j, ContinuousOn (f j) (openBondBall ι ρ))
    (hm : ∀ j ∈ S, MomentBound (cutoffFactor ρ p) Ψ (f j) q (C j)) :
    MomentBound (cutoffFactor ρ p) Ψ (fun η => ∑ j ∈ S, f j η) q (∑ j ∈ S, C j) := by
  classical
  have := hL.isProbability
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have e : (fun η : BondField ι => |∑ j ∈ (∅ : Finset J), f j η| ^ q) = fun _ => 0 := by
      funext η
      simp [show q ≠ 0 by omega]
    constructor
    · have e' : (fun η : BondField ι => |∑ j ∈ (∅ : Finset J), f j η| ^ q *
          ballDensity (cutoffFactor ρ p) Ψ η) = (0 : BondField ι → ℝ) := by
        funext η
        simp [show q ≠ 0 by omega]
      rw [e']
      exact integrable_zero _ ℝ _
    · simp only [e]
      rw [← hL.integral_eq]
      simp [show q ≠ 0 by omega]
  have hT : 0 < ∑ j ∈ S, C j := Finset.sum_pos (fun j _ => hC j) hS
  set T := ∑ j ∈ S, C j with hTdef
  have hi : ∀ j ∈ S, Integrable (fun η => |f j η| ^ q) (normalizedBallLaw (cutoffFactor ρ p) Ψ) := fun j hj =>
    (hL.integrable_iff _).2 (hm j hj).1
  have hG : Integrable (fun η => T ^ (q - 1) * ∑ j ∈ S, (C j)⁻¹ ^ (q - 1) * |f j η| ^ q)
      (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
    (integrable_finset_sum _ fun j hj => (hi j hj).const_mul _).const_mul _
  have hcs : ContinuousOn (fun η => ∑ j ∈ S, f j η) (openBondBall ι ρ) :=
    continuousOn_finset_sum _ fun j _ => hc j
  have hae : AEStronglyMeasurable (fun η => |∑ j ∈ S, f j η| ^ q) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
    aestronglyMeasurable_of_continuousOn hL (hcs.abs.pow q)
  have hpt : ∀ η, |∑ j ∈ S, f j η| ^ q ≤ T ^ (q - 1) * ∑ j ∈ S, (C j)⁻¹ ^ (q - 1) * |f j η| ^ q :=
    fun η => abs_sum_pow_le_weighted S (fun j => f j η) C hC q hq hS
  have hfi : Integrable (fun η => |∑ j ∈ S, f j η| ^ q) (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    refine Integrable.mono' hG hae (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt η
  refine ⟨(hL.integrable_iff _).1 hfi, ?_⟩
  rw [← hL.integral_eq]
  have h1 : ∫ η, |∑ j ∈ S, f j η| ^ q ∂normalizedBallLaw (cutoffFactor ρ p) Ψ ≤
      ∫ η, T ^ (q - 1) * ∑ j ∈ S, (C j)⁻¹ ^ (q - 1) * |f j η| ^ q ∂normalizedBallLaw (cutoffFactor ρ p) Ψ :=
    integral_mono hfi hG hpt
  refine h1.trans ?_
  rw [integral_const_mul, integral_finset_sum _ fun j hj => (hi j hj).const_mul _]
  have h2 : ∀ j ∈ S, ∫ η, (C j)⁻¹ ^ (q - 1) * |f j η| ^ q ∂normalizedBallLaw (cutoffFactor ρ p) Ψ ≤ C j := by
    intro j hj
    rw [integral_const_mul, hL.integral_eq]
    have h3 := (hm j hj).2
    have hb := hC j
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    calc (C j)⁻¹ ^ n * ballExpectation (cutoffFactor ρ p) Ψ (fun η => |f j η| ^ (n + 1))
        ≤ (C j)⁻¹ ^ n * C j ^ (n + 1) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = C j := by
        rw [inv_pow, pow_succ]
        field_simp
  have h3 : ∑ j ∈ S, ∫ η, (C j)⁻¹ ^ (q - 1) * |f j η| ^ q ∂normalizedBallLaw (cutoffFactor ρ p) Ψ ≤ T :=
    Finset.sum_le_sum h2
  calc T ^ (q - 1) * ∑ j ∈ S, ∫ η, (C j)⁻¹ ^ (q - 1) * |f j η| ^ q ∂normalizedBallLaw (cutoffFactor ρ p) Ψ
      ≤ T ^ (q - 1) * T := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = T ^ q := by
      obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
      simp [pow_succ]
theorem bondGradNorm_sum_le {J : Type} (S : Finset J) (H : J → BondField ι → ℝ) (b : ι) (η : BondField ι)
    (hd : ∀ j, DifferentiableAt ℝ (H j) η) :
    bondGradNorm (fun ζ => ∑ j ∈ S, H j ζ) b η ≤ ∑ j ∈ S, bondGradNorm (H j) b η := by
  classical
  unfold bondGradNorm
  rw [fderiv_fun_sum fun j _ => hd j]
  have e : (∑ j ∈ S, fderiv ℝ (H j) η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) =
      ∑ j ∈ S, (fderiv ℝ (H j) η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) :=
    ContinuousLinearMap.ext fun v => by simp [ContinuousLinearMap.sum_apply]
  rw [e]
  exact norm_sum_le _ _
end SumBounds
open SumBounds in
theorem finiteSumSizeBound_holds (h₁ : normalizedBallLawIsProbabilityStatement) :
    FiniteSumSizeBound := by
  intro ι _ _ J S ρ x κ B p Ψ Cq H h dZ dZ₀ hρ hcut hΨ hx hCq hh hc hs hsum hdecay
  classical
  obtain ⟨hprob, hmean, hint, hball, -⟩ := h₁ ι ρ p Ψ hρ hcut hΨ
  have hL : BallLawFacts ρ p Ψ := ⟨hprob, hmean, hint, hball⟩
  have hO := isOpen_openBondBall (ι := ι) ρ
  have hdiff : ∀ j, ∀ η ∈ openBondBall ι ρ, DifferentiableAt ℝ (H j) η := fun j η hη =>
    ((hc j).contDiffAt (hO.mem_nhds hη)).differentiableAt (by norm_num)
  have hex : ∀ j ∈ S, ∃ H₀ : ℝ, ∀ q : ℕ, 1 ≤ q →
      MomentBound (cutoffFactor ρ p) Ψ (fun η => H j η - H₀) q (Cq q * h j) ∧
      ∀ b : ι, MomentBound (cutoffFactor ρ p) Ψ (bondGradNorm (H j) b) q
        (Cq q * Real.sqrt x * h j * Real.exp (-(2 * κ * dZ j b))) := fun j hj => (hs j hj).2
  choose! H₀ hH₀ using hex
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg fun j _ => (hh j).le) hsum
  refine ⟨fun η hη => ?_, ∑ j ∈ S, H₀ j, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · exact DifferentiableAt.fun_sum fun j _ => hdiff j η hη
  · have e : (fun η => ∑ j ∈ S, H j η - ∑ j ∈ S, H₀ j) = fun η => ∑ j ∈ S, (H j η - H₀ j) := by
      funext η
      rw [Finset.sum_sub_distrib]
    rw [e]
    have hm := momentBound_finset_sum hL S (fun j η => H j η - H₀ j) (fun j => Cq q * h j)
      (fun j => mul_pos (hCq q) (hh j)) q hq
      (fun j => ((hc j).continuousOn).sub continuousOn_const) (fun j hj => (hH₀ j hj q hq).1)
    rw [← Finset.mul_sum] at hm
    exact momentBound_mono hL
      ((continuousOn_finset_sum _ fun j _ => ((hc j).continuousOn).sub continuousOn_const))
      (fun _ _ => le_rfl) (mul_nonneg (hCq q).le (Finset.sum_nonneg fun j _ => (hh j).le))
      (mul_le_mul_of_nonneg_left hsum (hCq q).le) hm
  · have hx' : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have hm := momentBound_finset_sum hL S (fun j => bondGradNorm (H j) b)
      (fun j => Cq q * Real.sqrt x * h j * Real.exp (-(2 * κ * dZ j b)))
      (fun j => mul_pos (mul_pos (mul_pos (hCq q) hx') (hh j)) (Real.exp_pos _)) q hq
      (fun j => continuousOn_bondGradNorm hO (hc j) b) (fun j hj => (hH₀ j hj q hq).2 b)
    have hc' : ContDiffOn ℝ 1 (fun η => ∑ j ∈ S, H j η) (openBondBall ι ρ) :=
      ContDiffOn.sum fun j _ => hc j
    have hsumB : ∑ j ∈ S, Cq q * Real.sqrt x * h j * Real.exp (-(2 * κ * dZ j b)) ≤
        Cq q * Real.sqrt x * B * Real.exp (-(2 * κ * dZ₀ b)) := by
      have : ∑ j ∈ S, Cq q * Real.sqrt x * h j * Real.exp (-(2 * κ * dZ j b)) =
          Cq q * Real.sqrt x * ∑ j ∈ S, h j * Real.exp (-(2 * κ * dZ j b)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, mul_assoc (Cq q * Real.sqrt x) B]
      exact mul_le_mul_of_nonneg_left (hdecay b) (mul_pos (hCq q) hx').le
    exact momentBound_mono hL (continuousOn_bondGradNorm hO hc' b)
      (fun η hη => by
        have h1 := bondGradNorm_sum_le S H b η fun j => by
          by_cases hj : True
          · exact hdiff j η hη
          · exact absurd trivial hj
        have h2 : 0 ≤ bondGradNorm (fun ζ => ∑ j ∈ S, H j ζ) b η := norm_nonneg _
        rw [abs_of_nonneg h2, abs_of_nonneg (h2.trans h1)]
        exact h1)
      (Finset.sum_nonneg fun j _ =>
        (mul_pos (mul_pos (mul_pos (hCq q) hx') (hh j)) (Real.exp_pos _)).le) hsumB hm
end YangMills.Construction.WeightedResponses
end
