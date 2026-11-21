import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongTheScaleAndATopProof
import YangMills.Construction.ClusterExpansionOfAStep.CovarianceOfAFunctionOfSomeBondsProof
import YangMills.Construction.SummableBoundsOfTheFlow.SizesOfObservablesOfTheWeightForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Interpolation.WeightMoments
open Set Filter Topology MeasureTheory BlockAverages ColdStepAtMirrorFrames
section BallLaw
variable {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
def openPolyBall (ι : Type) (ρ : ℝ) : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ}
theorem isOpen_openPolyBall [Finite ι] (ρ : ℝ) : IsOpen (openPolyBall ι ρ) := by
  have : openPolyBall ι ρ = ⋂ b, {η | ‖η b‖ < ρ} := by
    ext η
    simp [openPolyBall]
  rw [this]
  exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
theorem ballDensity_nonneg (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) :
    0 ≤ ballDensity (cutoffFactor ρ p) Ψ η := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.ballDensity_nonneg <;> assumption
theorem ballDensity_eq_zero_of_not_mem {η : BondField ι} (h : η ∉ openPolyBall ι ρ) :
    ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
  simp only [openPolyBall, mem_ofPred_eq, not_forall, not_lt] at h
  obtain ⟨b, hb⟩ := h
  have : radialWeightProd (cutoffFactor ρ p) η = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb])
  simp [ballDensity, this]
theorem continuous_ballDensity (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : Continuous Ψ) : Continuous (ballDensity (cutoffFactor ρ p) Ψ) := by
  have h1 : Continuous fun u : ℝ => cutoffFactor ρ p (max u 0) := (hR ρ p hρ hp).smooth.continuous
  have h2 : ∀ b : ι, Continuous fun η : BondField ι => cutoffFactor ρ p ‖η b‖ := fun b => by
    have := h1.comp (continuous_norm.comp (continuous_apply (A := fun _ : ι => BondVector) b))
    refine this.congr fun η => ?_
    simp [norm_nonneg]
  unfold ballDensity radialWeightProd
  exact (continuous_finsetProd _ fun b _ => h2 b).mul (Real.continuous_exp.comp hΨ.neg)
theorem isCompact_closedPolyBall (ρ : ℝ) : IsCompact {η : BondField ι | ∀ b, ‖η b‖ ≤ ρ} := by apply _root_.YangMills.Construction.ScaleDerivatives.isCompact_polyBall <;> assumption
theorem hasCompactSupport_ballDensity : HasCompactSupport (ballDensity (cutoffFactor ρ p) Ψ) := by
  refine HasCompactSupport.intro (isCompact_closedPolyBall ρ) fun η hη => ?_
  refine ballDensity_eq_zero_of_not_mem fun h => hη fun b => (h b).le
theorem integrable_ballDensity (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : Continuous Ψ) : Integrable (ballDensity (cutoffFactor ρ p) Ψ) :=
  (continuous_ballDensity hR hρ hp hΨ).integrable_of_hasCompactSupport hasCompactSupport_ballDensity
theorem integral_ballDensity_pos (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : Continuous Ψ) : 0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := by
  refine (continuous_ballDensity hR hρ hp hΨ).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_ballDensity (fun η => ballDensity_nonneg _ _ _ η) (x := 0) ?_
  have : 0 < radialWeightProd (cutoffFactor ρ p) (0 : BondField ι) :=
    Finset.prod_pos fun b _ => by simp [cutoffFactor, hρ, Real.exp_pos]
  exact (mul_pos this (Real.exp_pos _)).ne'
theorem integrable_mul_ballDensity_of_bounded (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (hΨ : Continuous Ψ)
    {f : BondField ι → ℝ} (hf : ContinuousOn f (openPolyBall ι ρ)) {B : ℝ}
    (hB : ∀ η ∈ openPolyBall ι ρ, |f η| ≤ B) :
    Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η := by
  have hU := (isOpen_openPolyBall (ι := ι) ρ).measurableSet
  have hc := continuous_ballDensity hR hρ hp hΨ
  have hm : AEStronglyMeasurable (fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η) volume := by
    have h1 : AEStronglyMeasurable (fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η)
        (volume.restrict (openPolyBall ι ρ)) :=
      (hf.mul hc.continuousOn).aestronglyMeasurable hU
    have h2 : (openPolyBall ι ρ).indicator (fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η) =
        fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η := by
      funext η
      by_cases h : η ∈ openPolyBall ι ρ
      · simp [h]
      · simp [h, ballDensity_eq_zero_of_not_mem h]
    rw [← h2]
    exact (aestronglyMeasurable_indicator_iff hU).mpr h1
  refine ((integrable_ballDensity hR hρ hp hΨ).const_mul B).mono' hm (Eventually.of_forall fun η => ?_)
  by_cases h : η ∈ openPolyBall ι ρ
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ballDensity_nonneg _ _ _ η)]
    exact mul_le_mul_of_nonneg_right (hB η h) (ballDensity_nonneg _ _ _ η)
  · simp [ballDensity_eq_zero_of_not_mem h]
theorem ballExpectation_mono {f g : BondField ι → ℝ} (hm : 0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η)
    (hf : Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η)
    (hg : Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η)
    (h : ∀ η ∈ openPolyBall ι ρ, f η ≤ g η) :
    ballExpectation (cutoffFactor ρ p) Ψ f ≤ ballExpectation (cutoffFactor ρ p) Ψ g := by
  unfold ballExpectation
  refine div_le_div_of_nonneg_right ?_ hm.le
  refine integral_mono hf hg fun η => ?_
  by_cases hη : η ∈ openPolyBall ι ρ
  · exact mul_le_mul_of_nonneg_right (h η hη) (ballDensity_nonneg _ _ _ η)
  · simp [ballDensity_eq_zero_of_not_mem hη]
theorem ballExpectation_const (hm : 0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η) (c : ℝ) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun _ => c) = c := by
  unfold ballExpectation
  rw [integral_const_mul]
  field_simp
theorem ballExpectation_add {f g : BondField ι → ℝ}
    (hf : Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η)
    (hg : Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => f η + g η) =
      ballExpectation (cutoffFactor ρ p) Ψ f + ballExpectation (cutoffFactor ρ p) Ψ g := by
  unfold ballExpectation
  rw [← add_div, ← integral_add hf hg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [add_mul]
theorem ballExpectation_const_mul (c : ℝ) (f : BondField ι → ℝ) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => c * f η) = c * ballExpectation (cutoffFactor ρ p) Ψ f := by
  unfold ballExpectation
  rw [mul_div_assoc', ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [mul_assoc]
theorem ballExpectation_sum {α : Type} (s : Finset α) {f : α → BondField ι → ℝ}
    (hf : ∀ a ∈ s, Integrable fun η => f a η * ballDensity (cutoffFactor ρ p) Ψ η) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => ∑ a ∈ s, f a η) =
      ∑ a ∈ s, ballExpectation (cutoffFactor ρ p) Ψ (f a) := by
  unfold ballExpectation
  rw [← Finset.sum_div, ← integral_finsetSum _ hf]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [Finset.sum_mul]
end BallLaw
variable {F : BlockFrame}
theorem pow_le_one_add_pow_two_mul (t : ℝ) (ht : 0 ≤ t) (m : ℕ) : t ^ m ≤ 1 + t ^ (2 * m) := by
  rcases le_total t 1 with h | h
  · have h1 : t ^ m ≤ 1 := pow_le_one₀ ht h
    have h2 : 0 ≤ t ^ (2 * m) := by positivity
    linarith
  · have h1 : t ^ m ≤ t ^ (2 * m) := pow_le_pow_right₀ h (by omega)
    linarith
theorem one_add_weighted_sum_pow_le {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ b, 0 ≤ w b) (z : ι → ℝ)
    (hz : ∀ b, 0 ≤ z b) (m : ℕ) :
    (1 + ∑ b, w b * z b) ^ m ≤ (1 + ∑ b, w b) ^ m * (1 + ∑ b, w b * z b ^ m) := by
  set Wt : ℝ := 1 + ∑ b, w b with hWt
  have hW0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw b
  have hWp : 0 < Wt := by positivity
  have hW1 : 1 ≤ Wt := by linarith
  set wh : Option ι → ℝ := fun o => match o with
    | none => 1 / Wt
    | some b => w b / Wt with hwh
  set zh : Option ι → ℝ := fun o => match o with
    | none => 1
    | some b => z b with hzh
  have h1 : ∑ o, wh o = 1 := by
    rw [Fintype.sum_option]
    simp only [hwh]
    rw [← Finset.sum_div, ← add_div]
    exact div_self hWp.ne'
  have h2 := Real.pow_arith_mean_le_arith_mean_pow Finset.univ wh zh
    (fun o _ => by cases o <;> simp only [hwh] <;> first | positivity | exact div_nonneg (hw _) hWp.le) h1
    (fun o _ => by
      cases o with
      | none => simp [hzh]
      | some b => exact hz b) m
  rw [Fintype.sum_option, Fintype.sum_option] at h2
  simp only [hwh, hzh, one_pow, mul_one] at h2
  have e1 : 1 / Wt + ∑ b, w b / Wt * z b = (1 + ∑ b, w b * z b) / Wt := by
    rw [add_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e2 : 1 / Wt + ∑ b, w b / Wt * z b ^ m = (1 + ∑ b, w b * z b ^ m) / Wt := by
    rw [add_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e1, e2, div_pow] at h2
  have hX : 0 ≤ 1 + ∑ b, w b * z b ^ m :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (pow_nonneg (hz b) m))
  have h3 : (1 + ∑ b, w b * z b) ^ m ≤ (1 + ∑ b, w b * z b ^ m) / Wt * Wt ^ m := by
    rwa [div_le_iff₀ (by positivity)] at h2
  refine h3.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact div_le_self hX hW1
def weightMomentConst (W : ℝ) (Cq : ℕ → ℝ) (m : ℕ) : ℝ := (1 + W) ^ m * (1 + W * (1 + Cq m))
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem weightedL1Norm_moment (hR : CutoffFactorIsRadialCutoff) {κ W : ℝ} {Cq : ℕ → ℝ} (hW0 : 0 ≤ W)
    (hCq : ∀ q, 0 ≤ Cq q)
    {y : ι → F.Cell} {ρ l : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {Y : F.Cell}
    (hρ : 0 < ρ) (hl : 0 < l) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ)
    (hW : ∑ b, Real.exp (-(2 ^ 4 * κ * cellSupDist (y b) Y)) ≤ W)
    (hm : ∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤
      Cq q * ((l⁻¹ ^ 2) ^ q)⁻¹) (m : ℕ) :
    (Integrable fun η => (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ m * ballDensity (cutoffFactor ρ p) Ψ η) ∧
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ m) ≤
      weightMomentConst W Cq m := by
  set w : ι → ℝ := fun b => Real.exp (-(2 ^ 4 * κ * cellSupDist (y b) Y)) with hw
  have hwn : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
  set x : ℝ := l⁻¹ ^ 2 with hx
  have hxp : 0 < x := by positivity
  have hmass := integral_ballDensity_pos (Ψ := Ψ) hR hρ hp hΨ
  have hnorm : ∀ (η : BondField ι) b, ‖(l⁻¹ • η) b‖ = l⁻¹ * ‖η b‖ := fun η b => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hcw : Continuous fun η : BondField ι => weightedL1Norm κ y Y (l⁻¹ • η) := by
    unfold weightedL1Norm
    refine continuous_finsetSum _ fun b _ => continuous_const.mul ?_
    exact continuous_norm.comp ((continuous_apply b).comp (continuous_const_smul l⁻¹))
  have hwb : ∀ η ∈ openPolyBall ι ρ, |(1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ m| ≤ (1 + W * (l⁻¹ * ρ)) ^ m := by
    intro η hη
    have h0 : 0 ≤ weightedL1Norm κ y Y (l⁻¹ • η) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (hwn b) (norm_nonneg _)
    rw [abs_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have h1 : weightedL1Norm κ y Y (l⁻¹ • η) ≤ ∑ b, w b * (l⁻¹ * ρ) := by
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hwn b)
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left (hη b).le (by positivity)
    have h2 : ∑ b, w b * (l⁻¹ * ρ) ≤ W * (l⁻¹ * ρ) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hW (by positivity)
    linarith
  have hint : Integrable fun η => (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ m * ballDensity (cutoffFactor ρ p) Ψ η :=
    integrable_mul_ballDensity_of_bounded hR hρ hp hΨ ((continuous_const.add hcw).pow m).continuousOn hwb
  refine ⟨hint, ?_⟩
  have hib : ∀ (b : ι), Integrable fun η => ‖η b‖ ^ (2 * m) * ballDensity (cutoffFactor ρ p) Ψ η := by
    intro b
    refine integrable_mul_ballDensity_of_bounded (B := ρ ^ (2 * m)) hR hρ hp hΨ ?_ fun η hη => ?_
    · exact ((continuous_norm.comp (continuous_apply b)).pow _).continuousOn
    · rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hη b).le _
  have hid : Integrable (ballDensity (cutoffFactor ρ p) Ψ) := integrable_ballDensity hR hρ hp hΨ
  set c : ℝ := (1 + W) ^ m with hc
  have hc0 : 0 ≤ c := by positivity
  set g : BondField ι → ℝ := fun η => c * (1 + ∑ b, w b * (1 + x ^ m * ‖η b‖ ^ (2 * m))) with hg
  have hone : Integrable fun η : BondField ι => (1 : ℝ) * ballDensity (cutoffFactor ρ p) Ψ η := by
    simpa using hid
  have hterm : ∀ b, Integrable fun η =>
      (w b * (1 + x ^ m * ‖η b‖ ^ (2 * m))) * ballDensity (cutoffFactor ρ p) Ψ η := by
    intro b
    have e : (fun η => (w b * (1 + x ^ m * ‖η b‖ ^ (2 * m))) * ballDensity (cutoffFactor ρ p) Ψ η) =
        fun η => w b * (1 * ballDensity (cutoffFactor ρ p) Ψ η +
          x ^ m * (‖η b‖ ^ (2 * m) * ballDensity (cutoffFactor ρ p) Ψ η)) := by
      funext η
      ring
    rw [e]
    exact (hone.add ((hib b).const_mul _)).const_mul _
  have hsum : Integrable fun η =>
      (∑ b, w b * (1 + x ^ m * ‖η b‖ ^ (2 * m))) * ballDensity (cutoffFactor ρ p) Ψ η := by
    have e : (fun η => (∑ b, w b * (1 + x ^ m * ‖η b‖ ^ (2 * m))) * ballDensity (cutoffFactor ρ p) Ψ η) =
        fun η => ∑ b, (w b * (1 + x ^ m * ‖η b‖ ^ (2 * m))) * ballDensity (cutoffFactor ρ p) Ψ η := by
      funext η
      rw [Finset.sum_mul]
    rw [e]
    exact integrable_finsetSum _ fun b _ => hterm b
  have hgi : Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η := by
    have e : (fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η) = fun η =>
        c * (1 * ballDensity (cutoffFactor ρ p) Ψ η +
          (∑ b, w b * (1 + x ^ m * ‖η b‖ ^ (2 * m))) * ballDensity (cutoffFactor ρ p) Ψ η) := by
      funext η
      simp only [hg]
      ring
    rw [e]
    exact (hone.add hsum).const_mul _
  have hle : ballExpectation (cutoffFactor ρ p) Ψ (fun η => (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ m) ≤
      ballExpectation (cutoffFactor ρ p) Ψ g := by
    refine ballExpectation_mono hmass hint hgi fun η _ => ?_
    have h1 := one_add_weighted_sum_pow_le w hwn (fun b => ‖(l⁻¹ • η) b‖) (fun b => norm_nonneg _) m
    have h2 : (1 + ∑ b, w b) ^ m ≤ c := pow_le_pow_left₀ (by
      have := Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) => hwn b; linarith) (by linarith) m
    have h3 : ∀ b, ‖(l⁻¹ • η) b‖ ^ m ≤ 1 + x ^ m * ‖η b‖ ^ (2 * m) := by
      intro b
      have h4 := pow_le_one_add_pow_two_mul ‖(l⁻¹ • η) b‖ (norm_nonneg _) m
      refine h4.trans (le_of_eq ?_)
      rw [hnorm, mul_pow, hx, pow_mul]
    have h5 : 1 + ∑ b, w b * ‖(l⁻¹ • η) b‖ ^ m ≤ 1 + ∑ b, w b * (1 + x ^ m * ‖η b‖ ^ (2 * m)) := by
      gcongr with b
      exact h3 b
    have h6 : 0 ≤ 1 + ∑ b, w b * ‖(l⁻¹ • η) b‖ ^ m :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun b _ => mul_nonneg (hwn b) (by positivity))
    calc _ ≤ (1 + ∑ b, w b) ^ m * (1 + ∑ b, w b * ‖(l⁻¹ • η) b‖ ^ m) := h1
      _ ≤ c * (1 + ∑ b, w b * (1 + x ^ m * ‖η b‖ ^ (2 * m))) := mul_le_mul h2 h5 h6 hc0
  refine hle.trans ?_
  have hmean : ballExpectation (cutoffFactor ρ p) Ψ g =
      c * (1 + ∑ b, w b * (1 + x ^ m * ballExpectation (cutoffFactor ρ p) Ψ fun η => ‖η b‖ ^ (2 * m))) := by
    simp only [hg]
    rw [ballExpectation_const_mul, ballExpectation_add (f := fun _ => (1 : ℝ)) hone hsum,
      ballExpectation_const hmass, ballExpectation_sum _ fun b _ => hterm b]
    congr 2
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ballExpectation_const_mul, ballExpectation_add (f := fun _ => (1 : ℝ)) hone
      (by simpa [mul_assoc] using (hib b).const_mul (x ^ m)), ballExpectation_const hmass,
      ballExpectation_const_mul]
  rw [hmean]
  have hb : ∀ b, x ^ m * ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * m)) ≤ Cq m := by
    intro b
    have h1 := hm m b
    have h2 : 0 < x ^ m := by positivity
    calc _ ≤ x ^ m * (Cq m * (x ^ m)⁻¹) := mul_le_mul_of_nonneg_left h1 h2.le
      _ = Cq m := by field_simp
  have h7 : ∑ b, w b * (1 + x ^ m * ballExpectation (cutoffFactor ρ p) Ψ fun η => ‖η b‖ ^ (2 * m)) ≤
      W * (1 + Cq m) := by
    calc _ ≤ ∑ b, w b * (1 + Cq m) := Finset.sum_le_sum fun b _ => by
          refine mul_le_mul_of_nonneg_left ?_ (hwn b)
          linarith [hb b]
      _ = (∑ b, w b) * (1 + Cq m) := by rw [Finset.sum_mul]
      _ ≤ W * (1 + Cq m) := mul_le_mul_of_nonneg_right hW (by linarith [hCq m])
  unfold weightMomentConst
  exact mul_le_mul_of_nonneg_left (by linarith) hc0
variable {F : BlockFrame}
theorem weightMomentConst_nonneg {W : ℝ} {Cq : ℕ → ℝ} (hW : 0 ≤ W) (hCq : ∀ q, 0 ≤ Cq q) (m : ℕ) :
    0 ≤ weightMomentConst W Cq m := by
  have := hCq m
  unfold weightMomentConst
  positivity
theorem momentBound_of_le_weight_pow (hR : CutoffFactorIsRadialCutoff) {ι : Type} [Fintype ι] [DecidableEq ι]
    {κ W : ℝ} {Cq : ℕ → ℝ} (hW0 : 0 ≤ W)
    (hCq : ∀ q, 0 ≤ Cq q)
    {y : ι → F.Cell} {ρ l : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {Y : F.Cell}
    (hρ : 0 < ρ) (hl : 0 < l) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ)
    (hW : ∑ b, Real.exp (-(2 ^ 4 * κ * cellSupDist (y b) Y)) ≤ W)
    (hm : ∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤
      Cq q * ((l⁻¹ ^ 2) ^ q)⁻¹)
    {f : BondField ι → ℝ} (hf : ContinuousOn f (openPolyBall ι ρ)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ η ∈ openPolyBall ι ρ, |f η| ≤ B * (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ 7) {q : ℕ} (hq : 1 ≤ q) :
    MomentBound (cutoffFactor ρ p) Ψ f q ((1 + weightMomentConst W Cq (7 * q)) * B) := by
  have hmass := integral_ballDensity_pos (Ψ := Ψ) hR hρ hp hΨ
  obtain ⟨hi, hmean⟩ := weightedL1Norm_moment hR (κ := κ) (y := y) (Y := Y) hW0 hCq hρ hl hp hΨ hW hm (7 * q)
  have hwn : ∀ η : BondField ι, 0 ≤ weightedL1Norm κ y Y (l⁻¹ • η) := fun η =>
    Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hpt : ∀ η ∈ openPolyBall ι ρ, |f η| ^ q ≤ B ^ q * (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ (7 * q) := by
    intro η hη
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hb η hη) q
    refine h1.trans (le_of_eq ?_)
    rw [mul_pow, ← pow_mul]
  have hbd : ∀ η ∈ openPolyBall ι ρ, |f η| ≤ B * (1 + (W * (l⁻¹ * ρ))) ^ 7 := by
    intro η hη
    refine (hb η hη).trans (mul_le_mul_of_nonneg_left ?_ hB)
    refine pow_le_pow_left₀ (by have := hwn η; linarith) ?_ 7
    have h1 : weightedL1Norm κ y Y (l⁻¹ • η) ≤
        ∑ b, Real.exp (-(2 ^ 4 * κ * cellSupDist (y b) Y)) * (l⁻¹ * ρ) := by
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hη b).le (by positivity)
    have h2 : ∑ b, Real.exp (-(2 ^ 4 * κ * cellSupDist (y b) Y)) * (l⁻¹ * ρ) ≤ W * (l⁻¹ * ρ) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hW (by positivity)
    linarith
  have hint : Integrable fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η := by
    refine integrable_mul_ballDensity_of_bounded (B := (B * (1 + (W * (l⁻¹ * ρ))) ^ 7) ^ q) hR hρ hp hΨ
      (hf.abs.pow q) fun η hη => ?_
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbd η hη) q
  refine ⟨hint, ?_⟩
  have h3 : ballExpectation (cutoffFactor ρ p) Ψ (fun η => |f η| ^ q) ≤
      ballExpectation (cutoffFactor ρ p) Ψ fun η => B ^ q * (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ (7 * q) := by
    refine ballExpectation_mono hmass hint ?_ hpt
    have := hi.const_mul (B ^ q)
    simpa [mul_assoc] using this
  refine h3.trans ?_
  rw [ballExpectation_const_mul]
  set D := weightMomentConst W Cq (7 * q) with hD
  have hD0 : 0 ≤ D := weightMomentConst_nonneg hW0 hCq _
  have h4 : D ≤ (1 + D) ^ q := by
    have : 1 + D ≤ (1 + D) ^ q := le_self_pow₀ (by linarith) (by omega)
    linarith
  rw [mul_pow, mul_comm]
  have hBq : 0 ≤ B ^ q := by positivity
  exact mul_le_mul_of_nonneg_right (hmean.trans h4) hBq
end Interpolation.WeightMoments
theorem Interpolation.observableSizeOfWeightedBound_holds
    (hR : ColdStepAtMirrorFrames.CutoffFactorIsRadialCutoff) :
    Interpolation.ObservableSizeOfWeightedBound := by
  open Set Filter Topology MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation
    Interpolation.WeightMoments in
  intro κ W Cq hW0 hCq
  refine ⟨fun q => 1 + weightMomentConst W Cq (7 * q), fun q => by
    have := weightMomentConst_nonneg hW0 hCq (7 * q)
    linarith, ?_⟩
  intro F ι _ _ y ρ l A p Ψ Y H hρ hl hA hp hΨ hW hm hH hb hs
  have hlinv : 0 < l⁻¹ := by positivity
  set x : ℝ := l⁻¹ ^ 2 with hx
  have hsq : Real.sqrt x = l⁻¹ := by
    rw [hx]
    exact Real.sqrt_sq hlinv.le
  have hmaps : ∀ η ∈ openPolyBall ι ρ, ∀ b, l * ‖(l⁻¹ • η) b‖ < ρ := fun η hη b => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hlinv.le, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul]
    exact hη b
  set U : Set (BondField ι) := {ζ | ∀ b, l * ‖ζ b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {ζ | l * ‖ζ b‖ < ρ} := by
      ext ζ
      simp [hU]
    rw [this]
    refine isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    exact continuous_const.mul (continuous_norm.comp (continuous_apply b))
  set h : BondField ι → ℝ := fun η => H (l⁻¹ • η) with hh
  have hsc : ContDiff ℝ 1 (fun η : BondField ι => l⁻¹ • η) := contDiff_id.const_smul l⁻¹
  have hhC : ContDiffOn ℝ 1 h (openPolyBall ι ρ) :=
    hH.comp hsc.contDiffOn fun η hη => hmaps η hη
  have hBo := isOpen_openPolyBall (ι := ι) ρ
  have hdiff : ∀ η ∈ openPolyBall ι ρ, DifferentiableAt ℝ H (l⁻¹ • η) := fun η hη =>
    (hH.contDiffAt (hUo.mem_nhds (hmaps η hη))).differentiableAt (by norm_num)
  have hfd : ∀ η ∈ openPolyBall ι ρ, fderiv ℝ h η = l⁻¹ • fderiv ℝ H (l⁻¹ • η) := by
    intro η hη
    have h1 : HasFDerivAt (fun η : BondField ι => l⁻¹ • η) (l⁻¹ • ContinuousLinearMap.id ℝ (BondField ι)) η :=
      (ContinuousLinearMap.id ℝ (BondField ι)).hasFDerivAt.const_smul l⁻¹
    have h2 := (hdiff η hη).hasFDerivAt.comp η h1
    rw [show h = H ∘ fun η : BondField ι => l⁻¹ • η from rfl, h2.fderiv]
    ext v
    simp
  have hbound : ∀ (η) (_ : η ∈ openPolyBall ι ρ) (b : ι), |bondGradNorm h b η| ≤
      (l⁻¹ * A * Real.exp (-(2 * κ * cellSupDist (y b) Y))) * (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ 7 := by
    intro η hη b
    have hwn : 0 ≤ weightedL1Norm κ y Y (l⁻¹ • η) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    unfold bondGradNorm
    rw [abs_of_nonneg (norm_nonneg _)]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
    rw [hfd η hη]
    by_cases hv : v = 0
    · simp [hv]
    have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hnv : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv']
    have h1 := hs (l⁻¹ • η) b (‖v‖⁻¹ • v) (hmaps η hη) hnv
    have e : (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) v =
        ‖v‖ • bondVariation b (‖v‖⁻¹ • v) := by
      ext1 b'
      by_cases hb' : b' = b
      · subst hb'
        simp [bondVariation, smul_smul, mul_inv_cancel₀ hv']
      · simp [bondVariation, hb']
    have e2 : (l⁻¹ • fderiv ℝ H (l⁻¹ • η)) ((ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) v) =
        l⁻¹ * ‖v‖ * bondPartialDeriv H b (l⁻¹ • η) (‖v‖⁻¹ • v) := by
      rw [e]
      simp [bondPartialDeriv, mul_assoc]
      ring
    rw [e2, abs_mul, abs_mul, abs_of_pos hlinv, abs_of_nonneg (norm_nonneg _)]
    calc l⁻¹ * ‖v‖ * |bondPartialDeriv H b (l⁻¹ • η) (‖v‖⁻¹ • v)| ≤
          l⁻¹ * ‖v‖ * (A * Real.exp (-(2 * κ * cellSupDist (y b) Y)) *
          (1 + weightedL1Norm κ y Y (l⁻¹ • η)) ^ 7) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  refine ⟨fun q hq => momentBound_of_le_weight_pow hR hW0 hCq (y := y) (κ := κ) (Y := Y) (f := h) hρ hl hp hΨ hW hm
    hhC.continuousOn hA (fun η hη => hb (l⁻¹ • η) (hmaps η hη)) hq, fun η hη => ?_, 0,
    fun q hq => ⟨?_, fun b => ?_⟩⟩
  · exact (hhC.contDiffAt (hBo.mem_nhds hη)).differentiableAt (by norm_num)
  · have h1 := momentBound_of_le_weight_pow hR hW0 hCq (y := y) (κ := κ) (Y := Y) (f := fun η => h η - 0)
      hρ hl hp hΨ hW hm (hhC.continuousOn.sub continuousOn_const) hA (fun η hη => by
        simpa using hb (l⁻¹ • η) (hmaps η hη)) hq
    exact h1
  · have hcont : ContinuousOn (bondGradNorm h b) (openPolyBall ι ρ) := by
      have h1 : ContinuousOn (fderiv ℝ h) (openPolyBall ι ρ) := hhC.continuousOn_fderiv_of_isOpen hBo le_rfl
      unfold bondGradNorm
      have h2 : ContinuousOn (fun η => (fderiv ℝ h η).comp
          (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)) (openPolyBall ι ρ) :=
        h1.clm_comp continuousOn_const
      exact h2.norm
    have h1 := momentBound_of_le_weight_pow hR hW0 hCq (y := y) (κ := κ) (Y := Y) (f := bondGradNorm h b)
      (B := l⁻¹ * A * Real.exp (-(2 * κ * cellSupDist (y b) Y))) hρ hl hp hΨ hW hm hcont (by positivity)
      (fun η hη => hbound η hη b) hq
    rw [hsq]
    have e : (1 + weightMomentConst W Cq (7 * q)) * l⁻¹ * A * Real.exp (-(2 * κ * (cellSupDist (y b) Y : ℝ))) =
        (1 + weightMomentConst W Cq (7 * q)) * (l⁻¹ * A * Real.exp (-(2 * κ * cellSupDist (y b) Y))) := by ring
    rw [e]
    exact h1
end YangMills.Construction
end
