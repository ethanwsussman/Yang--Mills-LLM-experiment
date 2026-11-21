import YangMills.Construction.SummableBoundsOfTheFlow.ByPartsAtABondProof
import YangMills.Construction.SummableBoundsOfTheFlow.SecondMomentsOfAGaussianProof
import YangMills.Construction.RunningCouplingSlope.CutLogarithmIsTwiceDifferentiable
import YangMills.Construction.RunningCouplingSlope.LaplaceOfAFamilyOfExponents
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfALogDeterminant
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheCutLogarithm
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbabilityProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open ColdStepAtMirrorFrames GaussianMeans
namespace LaplaceAsymptotics
namespace LaplaceMethod
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private structure IsMomentLaw (f S : BondField ι → ℝ) (m : ℕ → ℝ) : Prop where
  nonneg : ∀ η, 0 ≤ f η
  S_nonneg : ∀ η, 0 ≤ S η
  integrable : ∀ k : ℕ, Integrable (fun η => (1 + S η) ^ k * f η)
  mass : 0 < ∫ η, f η
  moment : ∀ k : ℕ, ∫ η, (1 + S η) ^ k * f η ≤ m k * ∫ η, f η
private structure IsPolyBounded (f S g : BondField ι → ℝ) (k : ℕ) (M : ℝ) : Prop where
  meas : AEStronglyMeasurable g volume
  bound : ∀ η, f η ≠ 0 → |g η| ≤ M * (1 + S η) ^ k
private theorem IsMomentLaw.integrable_density {f S : BondField ι → ℝ} {m : ℕ → ℝ}
    (L : IsMomentLaw f S m) : Integrable f := by
  simpa using L.integrable 0
private theorem IsPolyBounded.integrable_mul {f S g : BondField ι → ℝ} {m : ℕ → ℝ} {k : ℕ} {M : ℝ}
    (L : IsMomentLaw f S m) (h : IsPolyBounded f S g k M) : Integrable (fun η => g η * f η) := by
  refine ((L.integrable k).const_mul M).mono' (h.meas.mul L.integrable_density.aestronglyMeasurable)
    (ae_of_all _ fun η => ?_)
  by_cases h0 : f η = 0
  · have : 0 ≤ M * ((1 + S η) ^ k * f η) ∨ True := Or.inr trivial
    simp [h0]
  · have hb := h.bound η h0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (L.nonneg η)]
    calc |g η| * f η ≤ M * (1 + S η) ^ k * f η :=
          mul_le_mul_of_nonneg_right hb (L.nonneg η)
      _ = M * ((1 + S η) ^ k * f η) := by ring
private theorem IsPolyBounded.abs_integral_mul_le {f S g : BondField ι → ℝ} {m : ℕ → ℝ} {k : ℕ}
    {M : ℝ} (L : IsMomentLaw f S m) (h : IsPolyBounded f S g k M) (hM : 0 ≤ M) :
    |∫ η, g η * f η| ≤ M * m k * ∫ η, f η := by
  have h1 : |∫ η, g η * f η| ≤ ∫ η, M * ((1 + S η) ^ k * f η) := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
      ((L.integrable k).const_mul M) (ae_of_all _ fun η => ?_))
    by_cases h0 : f η = 0
    · simp [h0]
    · have hb := h.bound η h0
      show |g η * f η| ≤ M * ((1 + S η) ^ k * f η)
      rw [abs_mul, abs_of_nonneg (L.nonneg η)]
      calc |g η| * f η ≤ M * (1 + S η) ^ k * f η :=
            mul_le_mul_of_nonneg_right hb (L.nonneg η)
        _ = M * ((1 + S η) ^ k * f η) := by ring
  rw [integral_const_mul] at h1
  calc _ ≤ _ := h1
    _ ≤ M * (m k * ∫ η, f η) := mul_le_mul_of_nonneg_left (L.moment k) hM
    _ = _ := by ring
private theorem IsPolyBounded.abs_densityMean_le {f S g : BondField ι → ℝ} {m : ℕ → ℝ} {k : ℕ}
    {M : ℝ} (L : IsMomentLaw f S m) (h : IsPolyBounded f S g k M) (hM : 0 ≤ M) :
    |densityMean f g| ≤ M * m k := by
  unfold densityMean
  rw [abs_div, abs_of_pos L.mass, div_le_iff₀ L.mass]
  exact h.abs_integral_mul_le L hM
private theorem abs_ratio_sub_ratio_le {Z₀ Z₁ G₀ G₁ a₁ a₂ b : ℝ} (h0 : 0 < Z₀) (h1 : 0 < Z₁)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb : 0 ≤ b) (hs : a₁ ≤ 1 / 4) (hZ : |Z₁ - Z₀| ≤ a₁ * (Z₀ + Z₁))
    (hG : |G₁ - G₀| ≤ a₂ * (Z₀ + Z₁)) (hG₀ : |G₀| ≤ b * Z₀) :
    |G₁ / Z₁ - G₀ / Z₀| ≤ 3 * a₂ + 3 * b * a₁ := by
  have hZZ : Z₀ ≤ 2 * Z₁ := by
    have := (abs_le.1 hZ).1
    nlinarith
  have e : G₁ / Z₁ - G₀ / Z₀ = (G₁ - G₀) / Z₁ + (G₀ / Z₀) * ((Z₀ - Z₁) / Z₁) := by
    field_simp
    ring
  have hsum : (Z₀ + Z₁) / Z₁ ≤ 3 := by
    rw [div_le_iff₀ h1]
    linarith
  have t1 : |(G₁ - G₀) / Z₁| ≤ a₂ * 3 := by
    rw [abs_div, abs_of_pos h1]
    calc |G₁ - G₀| / Z₁ ≤ a₂ * (Z₀ + Z₁) / Z₁ := by gcongr
      _ = a₂ * ((Z₀ + Z₁) / Z₁) := by ring
      _ ≤ _ := by gcongr
  have t2 : |G₀ / Z₀| ≤ b := by
    rw [abs_div, abs_of_pos h0, div_le_iff₀ h0]
    exact hG₀
  have t3 : |(Z₀ - Z₁) / Z₁| ≤ a₁ * 3 := by
    rw [abs_div, abs_of_pos h1, abs_sub_comm]
    calc |Z₁ - Z₀| / Z₁ ≤ a₁ * (Z₀ + Z₁) / Z₁ := by gcongr
      _ = a₁ * ((Z₀ + Z₁) / Z₁) := by ring
      _ ≤ _ := by gcongr
  rw [e]
  calc _ ≤ |(G₁ - G₀) / Z₁| + |(G₀ / Z₀) * ((Z₀ - Z₁) / Z₁)| := abs_add_le _ _
    _ ≤ a₂ * 3 + b * (a₁ * 3) := by
        rw [abs_mul]
        gcongr
    _ = _ := by ring
private theorem abs_exp_neg_sub_one_bound (r : ℝ) :
    |Real.exp (-r) - 1| ≤ |r| * (1 + Real.exp (-r)) := by
  rcases le_total 0 r with h | h
  · have h1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : 1 - r ≤ Real.exp (-r) := by
      have := Real.add_one_le_exp (-r)
      linarith
    rw [abs_of_nonpos (by linarith), abs_of_nonneg h]
    have : 0 < Real.exp (-r) := Real.exp_pos _
    nlinarith
  · have h1 : 1 ≤ Real.exp (-r) := Real.one_le_exp (by linarith)
    have h2 : 1 + r * Real.exp (-r) ≥ 0 ∨ True := Or.inr trivial
    have h3 : Real.exp (-r) * Real.exp r = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : r + 1 ≤ Real.exp r := Real.add_one_le_exp r
    rw [abs_of_nonneg (by linarith), abs_of_nonpos h]
    have : 0 < Real.exp (-r) := Real.exp_pos _
    nlinarith
private theorem polyBounded_one {f S : BondField ι → ℝ} : IsPolyBounded f S (fun _ => (1 : ℝ)) 0 1 :=
  ⟨aestronglyMeasurable_const, fun η _ => by simp⟩
private theorem abs_integral_sub_of_exp_tilt {f₀ f₁ S R u : BondField ι → ℝ} {m : ℕ → ℝ} {j : ℕ}
    {Mu ε : ℝ} (L₀ : IsMomentLaw f₀ S m) (L₁ : IsMomentLaw f₁ S m)
    (hf : ∀ η, f₁ η = f₀ η * Real.exp (-R η))
    (hR₀ : IsPolyBounded f₀ S R 2 ε) (hu₀ : IsPolyBounded f₀ S u j Mu)
    (hu₁ : IsPolyBounded f₁ S u j Mu) (hε : 0 ≤ ε) (hMu : 0 ≤ Mu) :
    |(∫ η, u η * f₁ η) - ∫ η, u η * f₀ η| ≤
      Mu * ε * m (j + 2) * ((∫ η, f₀ η) + ∫ η, f₁ η) := by
  have i₀ := hu₀.integrable_mul L₀
  have i₁ := hu₁.integrable_mul L₁
  rw [← integral_sub i₁ i₀]
  have hb := ((L₀.integrable (j + 2)).add (L₁.integrable (j + 2))).const_mul (Mu * ε)
  have h1 : |∫ η, (u η * f₁ η - u η * f₀ η)| ≤
      ∫ η, Mu * ε * ((1 + S η) ^ (j + 2) * f₀ η + (1 + S η) ^ (j + 2) * f₁ η) := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ => abs_nonneg _) hb (ae_of_all _ fun η => ?_))
    show |u η * f₁ η - u η * f₀ η| ≤ _
    by_cases h0 : f₀ η = 0
    · have h1 : f₁ η = 0 := by rw [hf, h0, zero_mul]
      simp [h0, h1]
    · have a1 := hu₀.bound η h0
      have a2 := hR₀.bound η h0
      have a3 := abs_exp_neg_sub_one_bound (R η)
      have hS : 0 ≤ (1 + S η) ^ j := pow_nonneg (by linarith [L₀.S_nonneg η]) _
      have e : u η * f₁ η - u η * f₀ η = u η * (f₀ η * (Real.exp (-R η) - 1)) := by
        rw [hf]
        ring
      have p0 := L₀.nonneg η
      have hfe : f₀ η * (1 + Real.exp (-R η)) = f₀ η + f₁ η := by
        rw [hf]
        ring
      rw [e, abs_mul, abs_mul, abs_of_nonneg p0]
      calc |u η| * (f₀ η * |Real.exp (-R η) - 1|)
          ≤ (Mu * (1 + S η) ^ j) * (f₀ η * (|R η| * (1 + Real.exp (-R η)))) := by gcongr
        _ = (Mu * (1 + S η) ^ j) * |R η| * (f₀ η * (1 + Real.exp (-R η))) := by ring
        _ ≤ (Mu * (1 + S η) ^ j) * (ε * (1 + S η) ^ 2) * (f₀ η * (1 + Real.exp (-R η))) := by
            have : 0 ≤ f₀ η * (1 + Real.exp (-R η)) := by positivity
            gcongr
        _ = _ := by
            rw [hfe]
            ring
  rw [integral_const_mul, integral_add (L₀.integrable _) (L₁.integrable _)] at h1
  have m0 := L₀.moment (j + 2)
  have m1 := L₁.moment (j + 2)
  calc _ ≤ _ := h1
    _ ≤ Mu * ε * (m (j + 2) * (∫ η, f₀ η) + m (j + 2) * ∫ η, f₁ η) := by gcongr
    _ = _ := by ring
private theorem abs_densityMean_sub_of_exp_tilt {f₀ f₁ S R g : BondField ι → ℝ} {m : ℕ → ℝ} {k : ℕ}
    {M ε : ℝ} (L₀ : IsMomentLaw f₀ S m) (L₁ : IsMomentLaw f₁ S m)
    (hf : ∀ η, f₁ η = f₀ η * Real.exp (-R η))
    (hR₀ : IsPolyBounded f₀ S R 2 ε) (hg₀ : IsPolyBounded f₀ S g k M) (hg₁ : IsPolyBounded f₁ S g k M)
    (hε : 0 ≤ ε) (hM : 0 ≤ M) (hm2 : 0 ≤ m 2) (hmk : 0 ≤ m k) (hmk2 : 0 ≤ m (k + 2))
    (hs : ε * m 2 ≤ 1 / 4) :
    |densityMean f₁ g - densityMean f₀ g| ≤ 3 * (M * ε * m (k + 2)) + 3 * (M * m k) * (ε * m 2) := by
  have dZ := abs_integral_sub_of_exp_tilt L₀ L₁ hf hR₀ polyBounded_one polyBounded_one hε zero_le_one
  have dG := abs_integral_sub_of_exp_tilt L₀ L₁ hf hR₀ hg₀ hg₁ hε hM
  simp only [one_mul, zero_add] at dZ
  unfold densityMean
  exact abs_ratio_sub_ratio_le L₀.mass L₁.mass (by positivity) (by positivity) (by positivity) hs dZ dG
    (hg₀.abs_integral_mul_le L₀ hM)
private theorem abs_integral_sub_of_cutoff {fg f₀ S W u : BondField ι → ℝ} {m : ℕ → ℝ} {j : ℕ}
    {Mu δ : ℝ} (Lg : IsMomentLaw fg S m) (h₀ : AEStronglyMeasurable f₀ volume)
    (hf : ∀ η, f₀ η = W η * fg η)
    (hW₀ : ∀ η, 0 ≤ W η) (hW₁ : ∀ η, W η ≤ 1) (hWδ : ∀ η, W η ≠ 1 → 1 ≤ δ * (1 + S η))
    (hu : IsPolyBounded fg S u j Mu) (hδ : 0 ≤ δ) (hMu : 0 ≤ Mu) :
    Integrable (fun η => u η * f₀ η) ∧
      |(∫ η, u η * f₀ η) - ∫ η, u η * fg η| ≤ Mu * δ * m (j + 1) * ∫ η, fg η := by
  have ig := hu.integrable_mul Lg
  have i₀ : Integrable (fun η => u η * f₀ η) := by
    refine ig.mono (hu.meas.mul h₀) (ae_of_all _ fun η => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hf, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hW₀ η),
      abs_of_nonneg (Lg.nonneg η)]
    have : |u η| * fg η * W η ≤ |u η| * fg η * 1 :=
      mul_le_mul_of_nonneg_left (hW₁ η) (mul_nonneg (abs_nonneg _) (Lg.nonneg η))
    nlinarith
  refine ⟨i₀, ?_⟩
  rw [← integral_sub i₀ ig]
  have hb := (Lg.integrable (j + 1)).const_mul (Mu * δ)
  have h1 : |∫ η, (u η * f₀ η - u η * fg η)| ≤ ∫ η, Mu * δ * ((1 + S η) ^ (j + 1) * fg η) := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ => abs_nonneg _) hb (ae_of_all _ fun η => ?_))
    show |u η * f₀ η - u η * fg η| ≤ _
    have p0 := Lg.nonneg η
    have hS : 0 ≤ 1 + S η := by linarith [Lg.S_nonneg η]
    by_cases h0 : fg η = 0
    · simp [hf, h0]
    by_cases h1 : W η = 1
    · simp only [hf, h1, one_mul, sub_self, abs_zero]
      positivity
    · have a1 := hu.bound η h0
      have a2 := hWδ η h1
      have e : u η * f₀ η - u η * fg η = -(u η * ((1 - W η) * fg η)) := by
        rw [hf]
        ring
      have hw : 0 ≤ 1 - W η := by linarith [hW₁ η]
      have hw1 : 1 - W η ≤ δ * (1 + S η) := by linarith [hW₀ η]
      rw [e, abs_neg, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg p0]
      calc |u η| * ((1 - W η) * fg η) ≤ (Mu * (1 + S η) ^ j) * ((δ * (1 + S η)) * fg η) := by gcongr
        _ = _ := by ring
  rw [integral_const_mul] at h1
  calc _ ≤ _ := h1
    _ ≤ Mu * δ * (m (j + 1) * ∫ η, fg η) := by
        gcongr
        exact Lg.moment _
    _ = _ := by ring
private theorem abs_densityMean_sub_of_cutoff {fg f₀ S W g : BondField ι → ℝ} {m : ℕ → ℝ} {k : ℕ}
    {M δ : ℝ} (Lg : IsMomentLaw fg S m) (h₀ : AEStronglyMeasurable f₀ volume) (hm₀ : 0 < ∫ η, f₀ η)
    (hf : ∀ η, f₀ η = W η * fg η)
    (hW₀ : ∀ η, 0 ≤ W η) (hW₁ : ∀ η, W η ≤ 1) (hWδ : ∀ η, W η ≠ 1 → 1 ≤ δ * (1 + S η))
    (hg : IsPolyBounded fg S g k M) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hm1 : 0 ≤ m 1) (hmk : 0 ≤ m k)
    (hmk1 : 0 ≤ m (k + 1)) (hs : δ * m 1 ≤ 1 / 4) :
    |densityMean f₀ g - densityMean fg g| ≤ 3 * (M * δ * m (k + 1)) + 3 * (M * m k) * (δ * m 1) := by
  have dZ := (abs_integral_sub_of_cutoff Lg h₀ hf hW₀ hW₁ hWδ polyBounded_one hδ zero_le_one).2
  have dG := (abs_integral_sub_of_cutoff Lg h₀ hf hW₀ hW₁ hWδ hg hδ hM).2
  simp only [one_mul, zero_add] at dZ
  have hZ := Lg.mass
  unfold densityMean
  refine abs_ratio_sub_ratio_le hZ hm₀ (by positivity) (by positivity) (by positivity) hs ?_ ?_
    (hg.abs_integral_mul_le Lg hM)
  · refine dZ.trans ?_
    have : 0 ≤ δ * m 1 := by positivity
    nlinarith
  · refine dG.trans ?_
    have : 0 ≤ M * δ * m (k + 1) := by positivity
    nlinarith
private theorem momentLaw_of_radial_growth {f S : BondField ι → ℝ} {a b s : ℝ} (hf : ∀ η, 0 ≤ f η)
    (hi : Integrable f) (hm : 0 < ∫ η, f η) (hS : ∀ η, 0 ≤ S η) (hSc : Continuous S) (ha : 0 < a)
    (hs : 0 < s) (hsN : (s ^ Module.finrank ℝ (BondField ι))⁻¹ ≤ Real.exp 1)
    (hray : ∀ η, f η * Real.exp (a * S η - b) ≤ f (s • η)) :
    IsMomentLaw f S (fun k => (k.factorial : ℝ) * (a⁻¹) ^ k * Real.exp (a + b + 1)) := by
  have hi2 : Integrable (fun η => f (s • η)) := hi.comp_smul hs.ne'
  have hE : ∫ η, f (s • η) = (s ^ Module.finrank ℝ (BondField ι))⁻¹ • ∫ η, f η :=
    Measure.integral_comp_smul_of_nonneg volume f s (hR := hs.le)
  have hum : AEStronglyMeasurable (fun η => f η * Real.exp (a * S η - b)) volume :=
    hi.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  have hu : Integrable (fun η => f η * Real.exp (a * S η - b)) := by
    refine hi2.mono' hum (ae_of_all _ fun η => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hf η) (Real.exp_pos _).le)]
    exact hray η
  have hint : ∫ η, f η * Real.exp (a * S η - b) ≤ Real.exp 1 * ∫ η, f η := by
    calc _ ≤ ∫ η, f (s • η) := integral_mono hu hi2 hray
      _ = _ := hE
      _ ≤ _ := by
        rw [smul_eq_mul]
        gcongr
  have hpt : ∀ (k : ℕ) η, (1 + S η) ^ k * f η ≤ ((k.factorial : ℝ) * (a⁻¹) ^ k * Real.exp (a + b)) *
      (f η * Real.exp (a * S η - b)) := by
    intro k η
    have hu0 : 0 ≤ a * (1 + S η) := mul_nonneg ha.le (by linarith [hS η])
    have h1 := Real.pow_div_factorial_le_exp (a * (1 + S η)) hu0 k
    have hfac : (0 : ℝ) < k.factorial := by positivity
    rw [div_le_iff₀ hfac] at h1
    have h2 : (1 + S η) ^ k = (a⁻¹) ^ k * (a * (1 + S η)) ^ k := by
      rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    have h3 : Real.exp (a * (1 + S η)) = Real.exp (a + b) * Real.exp (a * S η - b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h3] at h1
    rw [h2]
    have hfk : 0 ≤ (a⁻¹) ^ k * f η := by
      have := hf η
      positivity
    calc (a⁻¹) ^ k * (a * (1 + S η)) ^ k * f η = (a * (1 + S η)) ^ k * ((a⁻¹) ^ k * f η) := by ring
      _ ≤ (Real.exp (a + b) * Real.exp (a * S η - b) * (k.factorial : ℝ)) * ((a⁻¹) ^ k * f η) :=
          mul_le_mul_of_nonneg_right h1 hfk
      _ = _ := by ring
  have hik : ∀ k : ℕ, Integrable (fun η => (1 + S η) ^ k * f η) := by
    intro k
    refine (hu.const_mul ((k.factorial : ℝ) * (a⁻¹) ^ k * Real.exp (a + b))).mono'
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul hi.aestronglyMeasurable)
      (ae_of_all _ fun η => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by linarith [hS η]) _) (hf η))]
    exact hpt k η
  refine ⟨hf, hS, hik, hm, fun k => ?_⟩
  calc _ ≤ ∫ η, ((k.factorial : ℝ) * (a⁻¹) ^ k * Real.exp (a + b)) *
        (f η * Real.exp (a * S η - b)) := integral_mono (hik k) (hu.const_mul _) (hpt k)
    _ = ((k.factorial : ℝ) * (a⁻¹) ^ k * Real.exp (a + b)) *
        ∫ η, f η * Real.exp (a * S η - b) := integral_const_mul _ _
    _ ≤ ((k.factorial : ℝ) * (a⁻¹) ^ k * Real.exp (a + b)) * (Real.exp 1 * ∫ η, f η) := by gcongr
    _ = _ := by
        rw [Real.exp_add (a + b) 1]
        ring
section Calculus
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
private theorem hasFDerivAt_iteratedFDeriv_apply {f : P → ℝ} {n : ℕ} {p : P}
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f p) (w : Fin n → P) :
    HasFDerivAt (fun z => iteratedFDeriv ℝ n f z w)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => P) ℝ w).comp
        (fderiv ℝ (iteratedFDeriv ℝ n f) p)) p := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) p :=
    h.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => P) ℝ w).hasFDerivAt.comp p hd.hasFDerivAt
private theorem fderiv_iteratedFDeriv_apply {f : P → ℝ} {n : ℕ} {p : P}
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f p) (w : Fin n → P) (a : P) :
    fderiv ℝ (fun z => iteratedFDeriv ℝ n f z w) p a =
      iteratedFDeriv ℝ (n + 1) f p (Fin.cons a w) := by
  rw [(hasFDerivAt_iteratedFDeriv_apply h w).fderiv, iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_cons]
private theorem contDiffAt_iteratedFDeriv_apply {f : P → ℝ} {n k : ℕ} {p : P}
    (h : ContDiffAt ℝ ((n + k : ℕ) : WithTop ℕ∞) f p) (w : Fin n → P) :
    ContDiffAt ℝ (k : WithTop ℕ∞) (fun z => iteratedFDeriv ℝ n f z w) p := by
  have h1 : ContDiffAt ℝ (k : WithTop ℕ∞) (iteratedFDeriv ℝ n f) p :=
    h.iteratedFDeriv_right (by push_cast; rw [add_comm])
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => P) ℝ w).contDiff.contDiffAt.comp p h1
private theorem contDiffAt_eventually {f : P → ℝ} {n : ℕ} {p : P}
    (h : ContDiffAt ℝ (n : WithTop ℕ∞) f p) :
    ∀ᶠ z in 𝓝 p, ContDiffAt ℝ (n : WithTop ℕ∞) f z :=
  h.eventually (by simp)
private theorem iteratedFDeriv_swap_first {f : P → ℝ} {n : ℕ} {p : P}
    (h : ContDiffAt ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f p) (a b : P) (w : Fin n → P) :
    iteratedFDeriv ℝ (n + 2) f p (Fin.cons a (Fin.cons b w)) =
      iteratedFDeriv ℝ (n + 2) f p (Fin.cons b (Fin.cons a w)) := by
  have h1 : ContDiffAt ℝ ((n + 1 + 1 : ℕ) : WithTop ℕ∞) f p := h
  have hc : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f p := h1.of_le (by norm_cast; omega)
  have h0 : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun z => iteratedFDeriv ℝ n f z w) p :=
    contDiffAt_iteratedFDeriv_apply (k := 2) h w
  have hev : ∀ c : P, (fun z => iteratedFDeriv ℝ (n + 1) f z (Fin.cons c w)) =ᶠ[𝓝 p]
      fun z => fderiv ℝ (fun z => iteratedFDeriv ℝ n f z w) z c := by
    intro c
    filter_upwards [contDiffAt_eventually hc] with z hz
    exact (fderiv_iteratedFDeriv_apply hz w c).symm
  have key : ∀ c d : P, iteratedFDeriv ℝ (n + 2) f p (Fin.cons c (Fin.cons d w)) =
      fderiv ℝ (fderiv ℝ (fun z => iteratedFDeriv ℝ n f z w)) p c d := by
    intro c d
    have e1 := fderiv_iteratedFDeriv_apply h1 (Fin.cons d w) c
    rw [← e1, (hev d).fderiv_eq]
    have hd : DifferentiableAt ℝ (fderiv ℝ (fun z => iteratedFDeriv ℝ n f z w)) p :=
      (h0.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have e2 := ((ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp p hd.hasFDerivAt).fderiv
    have e3 : (fun z => fderiv ℝ (fun z => iteratedFDeriv ℝ n f z w) z d) =
        (ContinuousLinearMap.apply ℝ ℝ d) ∘ fderiv ℝ (fun z => iteratedFDeriv ℝ n f z w) := rfl
    rw [e3, e2]
    simp
  rw [key, key]
  exact (h0.isSymmSndFDerivAt (by simp)) a b
private theorem iteratedFDeriv_cons_congr {f : P → ℝ} {n : ℕ} {p : P}
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f p) (a : P) {w w' : Fin n → P}
    (hw : ∀ᶠ z in 𝓝 p, iteratedFDeriv ℝ n f z w = iteratedFDeriv ℝ n f z w') :
    iteratedFDeriv ℝ (n + 1) f p (Fin.cons a w) = iteratedFDeriv ℝ (n + 1) f p (Fin.cons a w') := by
  rw [← fderiv_iteratedFDeriv_apply h w a, ← fderiv_iteratedFDeriv_apply h w' a]
  have : (fun z => iteratedFDeriv ℝ n f z w) =ᶠ[𝓝 p] fun z => iteratedFDeriv ℝ n f z w' := hw
  rw [this.fderiv_eq]
private theorem iteratedFDeriv_swap_second {f : P → ℝ} {n : ℕ} {p : P}
    (h : ContDiffAt ℝ ((n + 3 : ℕ) : WithTop ℕ∞) f p) (a b c : P) (w : Fin n → P) :
    iteratedFDeriv ℝ (n + 3) f p (Fin.cons a (Fin.cons b (Fin.cons c w))) =
      iteratedFDeriv ℝ (n + 3) f p (Fin.cons a (Fin.cons c (Fin.cons b w))) := by
  have h1 : ContDiffAt ℝ ((n + 2 + 1 : ℕ) : WithTop ℕ∞) f p := h
  have hc : ContDiffAt ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f p := h1.of_le (by norm_cast; omega)
  refine iteratedFDeriv_cons_congr h1 a ?_
  filter_upwards [contDiffAt_eventually hc] with z hz
  exact iteratedFDeriv_swap_first hz b c w
private theorem hasDerivAt_iteratedFDeriv_line {f : P → ℝ} {n : ℕ} {p v : P} {t : ℝ}
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (p + t • v)) (w : Fin n → P) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n f (p + s • v) w)
      (iteratedFDeriv ℝ (n + 1) f (p + t • v) (Fin.cons v w)) t := by
  have hl : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have := (hasFDerivAt_iteratedFDeriv_apply h w).comp_hasDerivAt t hl
  have e := fderiv_iteratedFDeriv_apply h w v
  rw [(hasFDerivAt_iteratedFDeriv_apply h w).fderiv] at e
  rw [← e]
  exact this
end Calculus
section OneVariable
private theorem hasDerivAt_square_poly (s : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
  simpa using hasDerivAt_pow 2 s
private theorem hasDerivAt_cube_poly (s : ℝ) : HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := by
  simpa using hasDerivAt_pow 3 s
private theorem monotoneOn_unitInterval_of_deriv {u u' : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' t) t)
    (hn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ u' t) :
    MonotoneOn u (Set.Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht
    exact (hd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc] at ht
    rw [(hd t (Set.Ioo_subset_Icc_self ht)).deriv]
    exact hn t (Set.Ioo_subset_Icc_self ht)
private theorem taylor_second_order_le {g g₁ g₂ g₃ : ℝ → ℝ} {L : ℝ}
    (h₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g₁ t) t)
    (h₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g₁ (g₂ t) t)
    (h₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g₂ (g₃ t) t)
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, g₃ t ≤ L) :
    g 1 - g 0 - g₁ 0 - g₂ 0 / 2 ≤ L / 6 := by
  have z : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have o : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have a₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g₂ 0 + L * t - g₂ t := by
    intro t ht
    have hm := monotoneOn_unitInterval_of_deriv (u := fun s => L * s - g₂ s) (u' := fun s => L - g₃ s)
      (fun s hs => by
        simpa using ((hasDerivAt_id' s).const_mul L).fun_sub (h₂ s hs))
      (fun s hs => by linarith [hL s hs])
    have := hm z ht ht.1
    simp only [mul_zero, zero_sub] at this
    linarith
  have a₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g₁ 0 + g₂ 0 * t + L * t ^ 2 / 2 - g₁ t := by
    intro t ht
    have hm := monotoneOn_unitInterval_of_deriv (u := fun s => g₂ 0 * s + L * s ^ 2 / 2 - g₁ s)
      (u' := fun s => g₂ 0 + L * s - g₂ s)
      (fun s hs => by
        have e1 := (hasDerivAt_id' s).const_mul (g₂ 0)
        have e2 := ((hasDerivAt_square_poly s).const_mul L).div_const 2
        exact ((e1.fun_add e2).fun_sub (h₁ s hs)).congr_deriv (by ring))
      (fun s hs => a₂ s hs)
    have := hm z ht ht.1
    simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, zero_sub] at this
    linarith
  have hm := monotoneOn_unitInterval_of_deriv
    (u := fun s => g₁ 0 * s + g₂ 0 * s ^ 2 / 2 + L * s ^ 3 / 6 - g s)
    (u' := fun s => g₁ 0 + g₂ 0 * s + L * s ^ 2 / 2 - g₁ s)
    (fun s hs => by
      have e1 := (hasDerivAt_id' s).const_mul (g₁ 0)
      have e2 := ((hasDerivAt_square_poly s).const_mul (g₂ 0)).div_const 2
      have e3 := ((hasDerivAt_cube_poly s).const_mul L).div_const 6
      exact (((e1.fun_add e2).fun_add e3).fun_sub (h₀ s hs)).congr_deriv (by ring))
    (fun s hs => a₁ s hs)
  have := hm z o (by norm_num)
  norm_num at this
  linarith
private theorem gain_of_second_deriv_lower {g g₁ g₂ : ℝ → ℝ} {M s : ℝ}
    (h₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g₁ t) t)
    (h₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g₁ (g₂ t) t)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, M ≤ g₂ t) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 - s) * g₁ 0 + M * (1 - s ^ 2) / 2 ≤ g 1 - g s := by
  have z : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have o : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have a₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g₁ t - g₁ 0 - M * t := by
    intro t ht
    have hm := monotoneOn_unitInterval_of_deriv (u := fun s => g₁ s - M * s) (u' := fun s => g₂ s - M)
      (fun s hs => by simpa using (h₁ s hs).fun_sub ((hasDerivAt_id' s).const_mul M))
      (fun s hs => by linarith [hM s hs])
    have := hm z ht ht.1
    norm_num at this
    linarith
  have hm := monotoneOn_unitInterval_of_deriv (u := fun s => g s - g₁ 0 * s - M * s ^ 2 / 2)
    (u' := fun s => g₁ s - g₁ 0 - M * s)
    (fun s hs => by
      have e1 := (hasDerivAt_id' s).const_mul (g₁ 0)
      have e2 := ((hasDerivAt_square_poly s).const_mul M).div_const 2
      exact (((h₀ s hs).fun_sub e1).fun_sub e2).congr_deriv (by ring))
    (fun s hs => a₁ s hs)
  have := hm hs o hs.2
  norm_num at this
  nlinarith
end OneVariable
section Line
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
private theorem iteratedFDeriv_swap_third {f : P → ℝ} {n : ℕ} {p : P}
    (h : ContDiffAt ℝ ((n + 4 : ℕ) : WithTop ℕ∞) f p) (a b c d : P) (w : Fin n → P) :
    iteratedFDeriv ℝ (n + 4) f p (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d w)))) =
      iteratedFDeriv ℝ (n + 4) f p (Fin.cons a (Fin.cons b (Fin.cons d (Fin.cons c w)))) := by
  have h1 : ContDiffAt ℝ ((n + 3 + 1 : ℕ) : WithTop ℕ∞) f p := h
  have hc : ContDiffAt ℝ ((n + 3 : ℕ) : WithTop ℕ∞) f p := h1.of_le (by norm_cast; omega)
  refine iteratedFDeriv_cons_congr h1 a ?_
  filter_upwards [contDiffAt_eventually hc] with z hz
  exact iteratedFDeriv_swap_second hz b c d w
private theorem hasDerivAt_iteratedFDeriv_ray {f : P → ℝ} {n : ℕ} {v : P} {t : ℝ}
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (t • v)) (w : Fin n → P) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n f (s • v) w)
      (iteratedFDeriv ℝ (n + 1) f (t • v) (Fin.cons v w)) t := by
  have := hasDerivAt_iteratedFDeriv_line (p := (0 : P)) (v := v) (t := t) (by simpa using h) w
  simpa using this
private theorem iteratedFDeriv_cons_eq_zero_of_line {f : P → ℝ} {n : ℕ} {p v : P}
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f p)
    (w : Fin n → P) (hz : ∀ᶠ t : ℝ in 𝓝 0, iteratedFDeriv ℝ n f (p + t • v) w = 0) :
    iteratedFDeriv ℝ (n + 1) f p (Fin.cons v w) = 0 := by
  have d := hasDerivAt_iteratedFDeriv_line (p := p) (v := v) (t := 0) (by simpa using h) w
  have c : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n f (p + s • v) w) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hz
  simpa using d.unique c
private theorem abs_iteratedFDeriv_apply_le {f : P → ℝ} {n : ℕ} {z : P} {L : ℝ}
    (hb : ‖iteratedFDeriv ℝ n f z‖ ≤ L)
    (u : Fin n → P) : |iteratedFDeriv ℝ n f z u| ≤ L * ∏ i, ‖u i‖ := by
  have h := (iteratedFDeriv ℝ n f z).le_opNorm u
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun _ _ => norm_nonneg _))
private theorem abs_iteratedFDeriv_taylor_le {f : P → ℝ} {l : ℕ} (w : Fin l → P) (v : P) {L : ℝ}
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((l + 3 : ℕ) : WithTop ℕ∞) f (t • v))
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (l + 3) f (t • v)‖ ≤ L) :
    |iteratedFDeriv ℝ l f v w - iteratedFDeriv ℝ l f 0 w -
        iteratedFDeriv ℝ (l + 1) f 0 (Fin.cons v w) -
        iteratedFDeriv ℝ (l + 2) f 0 (Fin.cons v (Fin.cons v w)) / 2| ≤
      L * ‖v‖ ^ 3 * (∏ i, ‖w i‖) / 6 := by
  have c2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((l + 2 + 1 : ℕ) : WithTop ℕ∞) f (t • v) := hC
  have c1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((l + 1 + 1 : ℕ) : WithTop ℕ∞) f (t • v) :=
    fun t ht => (hC t ht).of_le (by norm_cast; omega)
  have c0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((l + 1 : ℕ) : WithTop ℕ∞) f (t • v) :=
    fun t ht => (hC t ht).of_le (by norm_cast; omega)
  set g : ℝ → ℝ := fun s => iteratedFDeriv ℝ l f (s • v) w with hg
  set g₁ : ℝ → ℝ := fun s => iteratedFDeriv ℝ (l + 1) f (s • v) (Fin.cons v w) with hg₁
  set g₂ : ℝ → ℝ := fun s => iteratedFDeriv ℝ (l + 2) f (s • v) (Fin.cons v (Fin.cons v w)) with hg₂
  set g₃ : ℝ → ℝ := fun s =>
    iteratedFDeriv ℝ (l + 3) f (s • v) (Fin.cons v (Fin.cons v (Fin.cons v w))) with hg₃
  have d₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g₁ t) t :=
    fun t ht => hasDerivAt_iteratedFDeriv_ray (c0 t ht) w
  have d₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g₁ (g₂ t) t :=
    fun t ht => hasDerivAt_iteratedFDeriv_ray (c1 t ht) (Fin.cons v w)
  have d₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g₂ (g₃ t) t :=
    fun t ht => hasDerivAt_iteratedFDeriv_ray (c2 t ht) (Fin.cons v (Fin.cons v w))
  have hprod : (∏ i, ‖(Fin.cons v (Fin.cons v (Fin.cons v w)) : Fin (l + 3) → P) i‖) =
      ‖v‖ ^ 3 * ∏ i, ‖w i‖ := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  have b₃ : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g₃ t| ≤ L * (‖v‖ ^ 3 * ∏ i, ‖w i‖) := by
    intro t ht
    have := abs_iteratedFDeriv_apply_le (hb t ht) (Fin.cons v (Fin.cons v (Fin.cons v w)))
    rwa [hprod] at this
  have up := taylor_second_order_le d₀ d₁ d₂ (fun t ht => (abs_le.1 (b₃ t ht)).2)
  have dn := taylor_second_order_le (L := L * (‖v‖ ^ 3 * ∏ i, ‖w i‖)) (g := fun s => -g s)
    (g₁ := fun s => -g₁ s) (g₂ := fun s => -g₂ s)
    (g₃ := fun s => -g₃ s) (fun t ht => (d₀ t ht).fun_neg) (fun t ht => (d₁ t ht).fun_neg)
    (fun t ht => (d₂ t ht).fun_neg) (fun t ht => by
      have := (abs_le.1 (b₃ t ht)).1
      show -g₃ t ≤ L * (‖v‖ ^ 3 * ∏ i, ‖w i‖)
      linarith)
  simp only [hg, hg₁, hg₂, one_smul, zero_smul] at up dn
  rw [abs_le]
  constructor
  · have e : L * ‖v‖ ^ 3 * (∏ i, ‖w i‖) / 6 = L * (‖v‖ ^ 3 * ∏ i, ‖w i‖) / 6 := by ring
    rw [e]
    linarith
  · have e : L * ‖v‖ ^ 3 * (∏ i, ‖w i‖) / 6 = L * (‖v‖ ^ 3 * ∏ i, ‖w i‖) / 6 := by ring
    rw [e]
    linarith
private theorem abs_iteratedFDeriv_sub_le {f : P → ℝ} {l : ℕ} (w : Fin l → P) (v : P) {L : ℝ}
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((l + 1 : ℕ) : WithTop ℕ∞) f (t • v))
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (l + 1) f (t • v)‖ ≤ L) :
    |iteratedFDeriv ℝ l f v w - iteratedFDeriv ℝ l f 0 w| ≤ L * ‖v‖ * ∏ i, ‖w i‖ := by
  set c : ℝ := L * ‖v‖ * ∏ i, ‖w i‖ with hc
  set g : ℝ → ℝ := fun s => iteratedFDeriv ℝ l f (s • v) w with hg
  set g₁ : ℝ → ℝ := fun s => iteratedFDeriv ℝ (l + 1) f (s • v) (Fin.cons v w) with hg₁
  have d₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g₁ t) t :=
    fun t ht => hasDerivAt_iteratedFDeriv_ray (hC t ht) w
  have hprod : (∏ i, ‖(Fin.cons v w : Fin (l + 1) → P) i‖) = ‖v‖ * ∏ i, ‖w i‖ := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have b₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g₁ t| ≤ c := by
    intro t ht
    have := abs_iteratedFDeriv_apply_le (hb t ht) (Fin.cons v w)
    rw [hprod] at this
    rw [hc, mul_assoc]
    exact this
  have z : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have o : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have up := monotoneOn_unitInterval_of_deriv (u := fun s => c * s - g s) (u' := fun s => c - g₁ s)
    (fun s hs => by simpa using ((hasDerivAt_id' s).const_mul c).fun_sub (d₀ s hs))
    (fun s hs => by linarith [(abs_le.1 (b₁ s hs)).2]) z o (by norm_num)
  have dn := monotoneOn_unitInterval_of_deriv (u := fun s => c * s + g s) (u' := fun s => c + g₁ s)
    (fun s hs => by simpa using ((hasDerivAt_id' s).const_mul c).fun_add (d₀ s hs))
    (fun s hs => by linarith [(abs_le.1 (b₁ s hs)).1]) z o (by norm_num)
  simp only [hg, one_smul, zero_smul, mul_one, mul_zero, zero_sub, zero_add] at up dn
  rw [abs_le]
  constructor <;> linarith
end Line
section Family
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private abbrev ParamBondField (ι : Type) : Type := (Fin 2 → ℝ) × BondField ι
private def noVec : Fin 0 → ParamBondField ι := Fin.elim0
private def liftField (η : BondField ι) : ParamBondField ι := (0, η)
private def paramUnit (l : Fin 2) : ParamBondField ι := (Pi.single l 1, 0)
private theorem smul_liftField (t : ℝ) (η : BondField ι) : t • liftField η = liftField (t • η) := by
  simp [liftField]
private theorem norm_liftField (η : BondField ι) : ‖liftField η‖ = ‖η‖ := by
  simp [liftField, Prod.norm_def]
private theorem norm_paramUnit (l : Fin 2) : ‖(paramUnit l : ParamBondField ι)‖ = 1 := by
  simp [paramUnit, Prod.norm_def, Pi.norm_single]
private theorem mem_ball_smul {ρ t : ℝ} {η : BondField ι} (hη : ∀ b, ‖η b‖ ≤ ρ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ∀ b, ‖(t • η) b‖ ≤ ρ := by
  intro b
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg ht.1]
  calc t * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ ≤ ρ := by simpa using hη b
private theorem mem_ball_zero {ρ : ℝ} (hρ : 0 < ρ) : ∀ b, ‖(0 : BondField ι) b‖ ≤ ρ := by
  intro b
  simpa using hρ.le
private theorem fderiv_fieldSlice {g : ParamBondField ι → ℝ} {τ : Fin 2 → ℝ} {ζ : BondField ι}
    (hd : DifferentiableAt ℝ g (τ, ζ)) (u : BondField ι) :
    fderiv ℝ (fun η => g (τ, η)) ζ u = fderiv ℝ g (τ, ζ) (0, u) := by
  have h := hd.hasFDerivAt.comp ζ (hasFDerivAt_prodMk_right τ ζ)
  have e : (fun η => g (τ, η)) = g ∘ fun f => (τ, f) := rfl
  rw [e, h.fderiv]
  simp
private theorem fderiv_paramSlice {g : ParamBondField ι → ℝ} {τ : Fin 2 → ℝ} {ζ : BondField ι}
    (hd : DifferentiableAt ℝ g (τ, ζ)) (e : Fin 2 → ℝ) :
    fderiv ℝ (fun σ => g (σ, ζ)) τ e = fderiv ℝ g (τ, ζ) (e, 0) := by
  have h := hd.hasFDerivAt.comp τ (hasFDerivAt_prodMk_left (𝕜 := ℝ) τ ζ)
  have e' : (fun σ => g (σ, ζ)) = g ∘ fun f => (f, ζ) := rfl
  rw [e', h.fderiv]
  simp
variable {ρ lam K : ℝ} {Q B : ParamBondField ι → ℝ}
private theorem contDiffAt_Q (LF : IsAdmissibleExponentFamily ρ lam K Q B) {η : BondField ι}
    (hη : ∀ b, ‖η b‖ ≤ ρ) {n : ℕ} (hn : n ≤ 5) : ContDiffAt ℝ (n : WithTop ℕ∞) Q (liftField η) :=
  (LF.contDiff_Q η hη).of_le (by exact_mod_cast hn)
private theorem contDiffAt_B (LF : IsAdmissibleExponentFamily ρ lam K Q B) {η : BondField ι}
    (hη : ∀ b, ‖η b‖ ≤ ρ) {n : ℕ} (hn : n ≤ 3) : ContDiffAt ℝ (n : WithTop ℕ∞) B (liftField η) :=
  (LF.contDiff_B η hη).of_le (by exact_mod_cast hn)
private theorem contDiffAt_eventually_param {n : ℕ} {f : ParamBondField ι → ℝ}
    (h : ContDiffAt ℝ (n : WithTop ℕ∞) f (liftField 0)) :
    ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), ContDiffAt ℝ (n : WithTop ℕ∞) f (τ, 0) := by
  have ht : Filter.Tendsto (fun τ : Fin 2 → ℝ => ((τ, 0) : ParamBondField ι)) (𝓝 0)
      (𝓝 (liftField 0)) :=
    (by fun_prop : Continuous fun τ : Fin 2 → ℝ => ((τ, 0) : ParamBondField ι)).tendsto' 0 _ rfl
  exact ht.eventually (contDiffAt_eventually h)
private theorem first_deriv_param_eq_zero (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B) :
    ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), ∀ e : Fin 2 → ℝ,
      iteratedFDeriv ℝ 1 Q (τ, 0) (Fin.cons (e, 0) noVec) = 0 := by
  filter_upwards [contDiffAt_eventually_param (n := 0 + 1)
    (contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num))] with τ hτ e
  refine iteratedFDeriv_cons_eq_zero_of_line hτ noVec (Filter.Eventually.of_forall fun t => ?_)
  have : ((τ, 0) : ParamBondField ι) + t • ((e, 0) : ParamBondField ι) = (τ + t • e, 0) := by simp
  rw [this, iteratedFDeriv_zero_apply]
  exact LF.value_zero _
private theorem second_deriv_param_eq_zero (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (e e' : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 Q (liftField 0) (Fin.cons (e, 0) (Fin.cons (e', 0) noVec)) = 0 := by
  refine iteratedFDeriv_cons_eq_zero_of_line (n := 1) (contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num))
    (Fin.cons (e', 0) noVec) ?_
  have ht : Filter.Tendsto (fun t : ℝ => t • e) (𝓝 0) (𝓝 0) :=
    (by fun_prop : Continuous fun t : ℝ => t • e).tendsto' 0 _ (by simp)
  filter_upwards [ht.eventually (first_deriv_param_eq_zero hρ LF)] with t h
  have : liftField (0 : BondField ι) + t • ((e, 0) : ParamBondField ι) = (t • e, 0) := by
    simp [liftField]
  rw [this]
  exact h e'
private theorem first_deriv_field_eq_zero (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B) :
    ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), ∀ u : BondField ι,
      iteratedFDeriv ℝ 1 Q (τ, 0) (Fin.cons (0, u) noVec) = 0 := by
  filter_upwards [LF.critical_zero, contDiffAt_eventually_param (n := 1)
    (contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num))] with τ hc hτ u
  rw [iteratedFDeriv_one_apply]
  have := fderiv_fieldSlice (hτ.differentiableAt one_ne_zero) u
  simp only [Fin.cons_zero]
  rw [← this, hc]
  rfl
private theorem second_deriv_param_field_eq_zero (hρ : 0 < ρ)
    (LF : IsAdmissibleExponentFamily ρ lam K Q B) :
    ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), ∀ (e : Fin 2 → ℝ) (u : BondField ι),
      iteratedFDeriv ℝ 2 Q (τ, 0) (Fin.cons (e, 0) (Fin.cons (0, u) noVec)) = 0 := by
  filter_upwards [(first_deriv_field_eq_zero hρ LF).eventually_nhds,
    contDiffAt_eventually_param (n := 1 + 1) (contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num))]
    with τ hτ hc e u
  refine iteratedFDeriv_cons_eq_zero_of_line (n := 1) hc (Fin.cons (0, u) noVec) ?_
  have ht : Filter.Tendsto (fun t : ℝ => τ + t • e) (𝓝 0) (𝓝 τ) :=
    (by fun_prop : Continuous fun t : ℝ => τ + t • e).tendsto' 0 _ (by simp)
  filter_upwards [ht.eventually hτ] with t h
  have : ((τ, 0) : ParamBondField ι) + t • ((e, 0) : ParamBondField ι) = (τ + t • e, 0) := by simp
  rw [this]
  exact h u
private theorem third_deriv_param_param_field_eq_zero (hρ : 0 < ρ)
    (LF : IsAdmissibleExponentFamily ρ lam K Q B) (e e' : Fin 2 → ℝ) (u : BondField ι) :
    iteratedFDeriv ℝ 3 Q (liftField 0)
      (Fin.cons (e, 0) (Fin.cons (e', 0) (Fin.cons (0, u) noVec))) = 0 := by
  refine iteratedFDeriv_cons_eq_zero_of_line (n := 2) (contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num))
    (Fin.cons (e', 0) (Fin.cons (0, u) noVec)) ?_
  have ht : Filter.Tendsto (fun t : ℝ => t • e) (𝓝 0) (𝓝 0) :=
    (by fun_prop : Continuous fun t : ℝ => t • e).tendsto' 0 _ (by simp)
  filter_upwards [ht.eventually (second_deriv_param_field_eq_zero hρ LF)] with t h
  have : liftField (0 : BondField ι) + t • ((e, 0) : ParamBondField ι) = (t • e, 0) := by
    simp [liftField]
  rw [this]
  exact h e' u
private theorem liftField_zero : liftField (0 : BondField ι) = 0 := rfl
private theorem prod_norm_one_paramUnit (l : Fin 2) :
    (∏ i, ‖(Fin.cons (paramUnit l) noVec : Fin 1 → ParamBondField ι) i‖) = 1 := by
  simp [Fin.prod_univ_succ, norm_paramUnit]
private theorem prod_norm_two_paramUnit :
    (∏ i, ‖(Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec) : Fin 2 → ParamBondField ι) i‖) =
      1 := by
  simp [Fin.prod_univ_succ, norm_paramUnit]
private theorem taylor_Q_value (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    |Q (liftField η) - iteratedFDeriv ℝ 2 Q 0 (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) / 2| ≤
      K * ‖η‖ ^ 3 / 6 := by
  have h := abs_iteratedFDeriv_taylor_le (f := Q) (l := 0) (L := K) noVec (liftField η)
    (fun t ht => by
      rw [smul_liftField]
      exact contDiffAt_Q LF (mem_ball_smul hη ht) (by norm_num))
    (fun t ht => by
      rw [smul_liftField]
      exact LF.deriv_bound_Q _ (mem_ball_smul hη ht) _ (by norm_num) (by norm_num))
  have v0 : Q 0 = 0 := LF.value_zero 0
  have v1 : iteratedFDeriv ℝ 1 Q 0 (Fin.cons (liftField η) noVec) = 0 :=
    (first_deriv_field_eq_zero hρ LF).self_of_nhds η
  simp only [iteratedFDeriv_zero_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
    norm_liftField] at h
  rw [v0] at h
  have v1' : iteratedFDeriv ℝ (0 + 1) Q 0 (Fin.cons (liftField η) noVec) = 0 := v1
  rw [v1'] at h
  simpa using h
private theorem taylor_Q_slope (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ ≤ ρ) (l : Fin 2) :
    |iteratedFDeriv ℝ 1 Q (liftField η) (Fin.cons (paramUnit l) noVec) -
        iteratedFDeriv ℝ 3 Q 0 (Fin.cons (paramUnit l)
          (Fin.cons (liftField η) (Fin.cons (liftField η) noVec))) / 2| ≤
      K * ‖η‖ ^ 3 / 6 := by
  have h := abs_iteratedFDeriv_taylor_le (f := Q) (l := 1) (L := K) (Fin.cons (paramUnit l) noVec)
    (liftField η)
    (fun t ht => by
      rw [smul_liftField]
      exact contDiffAt_Q LF (mem_ball_smul hη ht) (by norm_num))
    (fun t ht => by
      rw [smul_liftField]
      exact LF.deriv_bound_Q _ (mem_ball_smul hη ht) _ (by norm_num) (by norm_num))
  have c3 : ContDiffAt ℝ ((0 + 3 : ℕ) : WithTop ℕ∞) Q 0 := contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have c3' : ContDiffAt ℝ ((1 + 2 : ℕ) : WithTop ℕ∞) Q 0 :=
    contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have c2 : ContDiffAt ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) Q 0 := contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have v0 : iteratedFDeriv ℝ 1 Q 0 (Fin.cons (paramUnit l) noVec) = 0 :=
    (first_deriv_param_eq_zero hρ LF).self_of_nhds (Pi.single l 1)
  have v1 : iteratedFDeriv ℝ (1 + 1) Q 0 (Fin.cons (liftField η) (Fin.cons (paramUnit l) noVec)) = 0 := by
    have := iteratedFDeriv_swap_first c2 (liftField η) (paramUnit l) noVec
    exact this.trans ((second_deriv_param_field_eq_zero hρ LF).self_of_nhds (Pi.single l 1) η)
  have v2 : iteratedFDeriv ℝ (1 + 2) Q 0 (Fin.cons (liftField η) (Fin.cons (liftField η)
        (Fin.cons (paramUnit l) noVec))) =
      iteratedFDeriv ℝ 3 Q 0 (Fin.cons (paramUnit l) (Fin.cons (liftField η)
        (Fin.cons (liftField η) noVec))) :=
    (iteratedFDeriv_swap_second c3 (liftField η) (liftField η) (paramUnit l) noVec).trans
      (iteratedFDeriv_swap_first c3' (liftField η) (paramUnit l) (Fin.cons (liftField η) noVec))
  rw [v0, v1, v2, prod_norm_one_paramUnit, norm_liftField] at h
  simpa using h
private theorem taylor_Q_mixed (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    |iteratedFDeriv ℝ 2 Q (liftField η) (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) -
        iteratedFDeriv ℝ 4 Q 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1)
          (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)))) / 2| ≤
      K * ‖η‖ ^ 3 / 6 := by
  have h := abs_iteratedFDeriv_taylor_le (f := Q) (l := 2) (L := K)
    (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) (liftField η)
    (fun t ht => by
      rw [smul_liftField]
      exact contDiffAt_Q LF (mem_ball_smul hη ht) (by norm_num))
    (fun t ht => by
      rw [smul_liftField]
      exact LF.deriv_bound_Q _ (mem_ball_smul hη ht) _ (by norm_num) (by norm_num))
  have c03 : ContDiffAt ℝ ((0 + 3 : ℕ) : WithTop ℕ∞) Q 0 :=
    contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have c12 : ContDiffAt ℝ ((1 + 2 : ℕ) : WithTop ℕ∞) Q 0 :=
    contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have c13 : ContDiffAt ℝ ((1 + 3 : ℕ) : WithTop ℕ∞) Q 0 :=
    contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have c22 : ContDiffAt ℝ ((2 + 2 : ℕ) : WithTop ℕ∞) Q 0 :=
    contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have c04 : ContDiffAt ℝ ((0 + 4 : ℕ) : WithTop ℕ∞) Q 0 :=
    contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have v0 : iteratedFDeriv ℝ 2 Q 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) = 0 :=
    second_deriv_param_eq_zero hρ LF _ _
  have v1 : iteratedFDeriv ℝ (2 + 1) Q 0 (Fin.cons (liftField η) (Fin.cons (paramUnit 0)
      (Fin.cons (paramUnit 1) noVec))) = 0 :=
    (iteratedFDeriv_swap_first c12 (liftField η) (paramUnit 0) (Fin.cons (paramUnit 1) noVec)).trans
      ((iteratedFDeriv_swap_second c03 (paramUnit 0) (liftField η) (paramUnit 1) noVec).trans
        (third_deriv_param_param_field_eq_zero hρ LF _ _ η))
  have v2 : iteratedFDeriv ℝ (2 + 2) Q 0 (Fin.cons (liftField η) (Fin.cons (liftField η)
        (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)))) =
      iteratedFDeriv ℝ 4 Q 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1)
        (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)))) :=
    (iteratedFDeriv_swap_second c13 (liftField η) (liftField η) (paramUnit 0)
      (Fin.cons (paramUnit 1) noVec)).trans
      ((iteratedFDeriv_swap_first c22 (liftField η) (paramUnit 0)
        (Fin.cons (liftField η) (Fin.cons (paramUnit 1) noVec))).trans
        ((iteratedFDeriv_swap_third c04 (paramUnit 0) (liftField η) (liftField η) (paramUnit 1)
          noVec).trans
          (iteratedFDeriv_swap_second c13 (paramUnit 0) (liftField η) (paramUnit 1)
            (Fin.cons (liftField η) noVec))))
  rw [v0, v1, v2, prod_norm_two_paramUnit, norm_liftField] at h
  simpa using h
private theorem lipschitz_B_value (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ ≤ ρ) : |B (liftField η) - B 0| ≤ K * ‖η‖ := by
  have h := abs_iteratedFDeriv_sub_le (f := B) (l := 0) (L := K) noVec (liftField η)
    (fun t ht => by
      rw [smul_liftField]
      exact contDiffAt_B LF (mem_ball_smul hη ht) (by norm_num))
    (fun t ht => by
      rw [smul_liftField]
      exact LF.deriv_bound_B _ (mem_ball_smul hη ht) _ (by norm_num) (by norm_num))
  simpa [iteratedFDeriv_zero_apply, norm_liftField] using h
private theorem lipschitz_B_slope (LF : IsAdmissibleExponentFamily ρ lam K Q B) {η : BondField ι}
    (hη : ∀ b, ‖η b‖ ≤ ρ) (l : Fin 2) :
    |iteratedFDeriv ℝ 1 B (liftField η) (Fin.cons (paramUnit l) noVec) -
        iteratedFDeriv ℝ 1 B 0 (Fin.cons (paramUnit l) noVec)| ≤ K * ‖η‖ := by
  have h := abs_iteratedFDeriv_sub_le (f := B) (l := 1) (L := K) (Fin.cons (paramUnit l) noVec)
    (liftField η)
    (fun t ht => by
      rw [smul_liftField]
      exact contDiffAt_B LF (mem_ball_smul hη ht) (by norm_num))
    (fun t ht => by
      rw [smul_liftField]
      exact LF.deriv_bound_B _ (mem_ball_smul hη ht) _ (by norm_num) (by norm_num))
  rw [prod_norm_one_paramUnit, norm_liftField, mul_one] at h
  exact h
private theorem lipschitz_B_mixed (LF : IsAdmissibleExponentFamily ρ lam K Q B) {η : BondField ι}
    (hη : ∀ b, ‖η b‖ ≤ ρ) :
    |iteratedFDeriv ℝ 2 B (liftField η) (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) -
        iteratedFDeriv ℝ 2 B 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec))| ≤
      K * ‖η‖ := by
  have h := abs_iteratedFDeriv_sub_le (f := B) (l := 2) (L := K)
    (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) (liftField η)
    (fun t ht => by
      rw [smul_liftField]
      exact contDiffAt_B LF (mem_ball_smul hη ht) (by norm_num))
    (fun t ht => by
      rw [smul_liftField]
      exact LF.deriv_bound_B _ (mem_ball_smul hη ht) _ (by norm_num) (by norm_num))
  rw [prod_norm_two_paramUnit, norm_liftField, mul_one] at h
  exact h
private theorem secondDerivAlong_eq_iteratedFDeriv {f : ParamBondField ι → ℝ} {τ : Fin 2 → ℝ}
    {ζ : BondField ι} (h : ContDiffAt ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) f (τ, ζ)) (u v : BondField ι) :
    secondDerivAlong (fun ζ' => f (τ, ζ')) ζ u v =
      iteratedFDeriv ℝ 2 f (τ, ζ) (Fin.cons (0, v) (Fin.cons (0, u) noVec)) := by
  have h1 : ContDiffAt ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) f (τ, ζ) := h.of_le (by norm_cast)
  have ht : Filter.Tendsto (fun ζ' : BondField ι => ((τ, ζ') : ParamBondField ι)) (𝓝 ζ) (𝓝 (τ, ζ)) :=
    (by fun_prop : Continuous fun ζ' : BondField ι => ((τ, ζ') : ParamBondField ι)).tendsto' _ _ rfl
  have hev : (fun ζ' => fderiv ℝ (fun ζ'' => f (τ, ζ'')) ζ' u) =ᶠ[𝓝 ζ]
      fun ζ' => iteratedFDeriv ℝ 1 f (τ, ζ') (Fin.cons (0, u) noVec) := by
    filter_upwards [ht.eventually (contDiffAt_eventually h1)] with ζ' hz
    rw [fderiv_fieldSlice (hz.differentiableAt (by simp)), iteratedFDeriv_one_apply]
    simp
  unfold secondDerivAlong
  rw [hev.fderiv_eq]
  have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ 1 f z (Fin.cons (0, u) noVec)) (τ, ζ) :=
    (hasFDerivAt_iteratedFDeriv_apply h _).differentiableAt
  rw [fderiv_fieldSlice (g := fun z => iteratedFDeriv ℝ 1 f z (Fin.cons (0, u) noVec)) hd]
  exact fderiv_iteratedFDeriv_apply h _ _
private theorem iteratedFDeriv_linearExponent {n : ℕ} {x : ℝ} {z : ParamBondField ι}
    (hQ : ContDiffAt ℝ (n : WithTop ℕ∞) Q z)
    (hB : ContDiffAt ℝ (n : WithTop ℕ∞) B z) (w : Fin n → ParamBondField ι) :
    iteratedFDeriv ℝ n (linearExponent x Q B) z w =
      x * iteratedFDeriv ℝ n Q z w + iteratedFDeriv ℝ n B z w := by
  have e : linearExponent x Q B = x • Q + B := by
    funext y
    simp [linearExponent]
  have hq : ContDiffAt ℝ (n : WithTop ℕ∞) (x • Q) z := contDiffAt_const.smul hQ |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)
  rw [e, iteratedFDeriv_add_apply hq hB, iteratedFDeriv_const_smul_apply hQ]
  simp
end Family
section Cut
variable {ρ : ℝ} {p : ℝ → ℝ}
private theorem cutoffFactor_nonneg (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
private theorem cutoffFactor_le_one (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u) :
    cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
private theorem cutoffFactor_antitone (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u v : ℝ} (h0 : 0 ≤ u)
    (huv : u ≤ v) : cutoffFactor ρ p v ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.ConvexObservables.cutoffFactor_antitone <;> assumption
private theorem cutoffFactor_eq_one (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u)
    (h1 : u ≤ 5 * ρ / 8) : cutoffFactor ρ p u = 1 := by
  unfold cutoffFactor
  rw [if_pos (by linarith), hp.vanish_small u h0 h1]
  simp
private theorem cutoffFactor_piecewise_measurable (hp : IsCutoff ρ p) :
    Measurable fun u : ℝ => (Set.Ico 0 ρ).piecewise (fun v => Real.exp (-p v)) (fun _ => 0) u := by
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ico
  exact Real.continuous_exp.comp_continuousOn hp.smooth.continuousOn.neg
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem weight_nonneg (η : BondField ι) : 0 ≤ radialWeightProd (cutoffFactor ρ p) η :=
  Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _
private theorem weight_le_one (hρ : 0 < ρ) (hp : IsCutoff ρ p) (η : BondField ι) :
    radialWeightProd (cutoffFactor ρ p) η ≤ 1 :=
  Finset.prod_le_one (fun _ _ => cutoffFactor_nonneg _) fun _ _ =>
    cutoffFactor_le_one hρ hp (norm_nonneg _)
private theorem weight_le_weight_smul (hρ : 0 < ρ) (hp : IsCutoff ρ p) (η : BondField ι) {s : ℝ}
    (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    radialWeightProd (cutoffFactor ρ p) η ≤ radialWeightProd (cutoffFactor ρ p) (s • η) := by
  refine Finset.prod_le_prod (fun _ _ => cutoffFactor_nonneg _) fun b _ =>
    cutoffFactor_antitone hρ hp (norm_nonneg _) ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h0]
  calc s * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _
private theorem norm_lt_of_weight_ne_zero {η : BondField ι}
    (h : radialWeightProd (cutoffFactor ρ p) η ≠ 0) (b : ι) : ‖η b‖ < ρ := by
  by_contra hb
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  unfold cutoffFactor
  rw [if_neg hb]
private theorem weight_eq_one (hρ : 0 < ρ) (hp : IsCutoff ρ p) {η : BondField ι}
    (h : ∀ b, ‖η b‖ ≤ 5 * ρ / 8) : radialWeightProd (cutoffFactor ρ p) η = 1 :=
  Finset.prod_eq_one fun b _ => cutoffFactor_eq_one hρ hp (norm_nonneg _) (h b)
private theorem weight_measurable (hp : IsCutoff ρ p) :
    Measurable (radialWeightProd (cutoffFactor ρ p) : BondField ι → ℝ) := by
  have e : (radialWeightProd (cutoffFactor ρ p) : BondField ι → ℝ) = fun η => ∏ b, (Set.Ico 0 ρ).piecewise
      (fun v => Real.exp (-p v)) (fun _ => 0) ‖η b‖ := by
    funext η
    refine Finset.prod_congr rfl fun b _ => ?_
    unfold cutoffFactor
    by_cases h : ‖η b‖ < ρ
    · have hm : ‖η b‖ ∈ Set.Ico 0 ρ := ⟨norm_nonneg _, h⟩
      rw [if_pos h, Set.piecewise_eq_of_mem _ _ _ hm]
    · have hm : ‖η b‖ ∉ Set.Ico 0 ρ := fun hm => h hm.2
      rw [if_neg h, Set.piecewise_eq_of_notMem _ _ _ hm]
  rw [e]
  exact Finset.measurable_fun_prod _ fun b _ => (cutoffFactor_piecewise_measurable hp).comp
    (by fun_prop : Measurable fun η : BondField ι => ‖η b‖)
private def closedBalls (ρ : ℝ) : Set (BondField ι) := {η | ∀ b, ‖η b‖ ≤ ρ}
private theorem closedBalls_eq_pi (ρ : ℝ) :
    (closedBalls ρ : Set (BondField ι)) = Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
  ext η
  simp [closedBalls, Set.mem_pi]
private theorem isCompact_closedBalls (ρ : ℝ) : IsCompact (closedBalls ρ : Set (BondField ι)) := by
  rw [closedBalls_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
private theorem measurableSet_closedBalls (ρ : ℝ) : MeasurableSet (closedBalls ρ : Set (BondField ι)) :=
  (isCompact_closedBalls ρ).isClosed.measurableSet
private theorem aestronglyMeasurable_indicator_closedBalls {h : BondField ι → ℝ}
    (hc : ContinuousOn h (closedBalls ρ)) :
    AEStronglyMeasurable ((closedBalls ρ).indicator h) volume :=
  (aestronglyMeasurable_indicator_iff (measurableSet_closedBalls ρ)).2
    (hc.aestronglyMeasurable (measurableSet_closedBalls ρ))
private theorem weighted_exp_eq_indicator (Φ : BondField ι → ℝ) :
    (fun η => radialWeightProd (cutoffFactor ρ p) η * Real.exp (-Φ η)) =
      fun η => radialWeightProd (cutoffFactor ρ p) η *
        (closedBalls ρ).indicator (fun η => Real.exp (-Φ η)) η := by
  funext η
  by_cases h : radialWeightProd (cutoffFactor ρ p) η = 0
  · simp [h]
  · rw [Set.indicator_of_mem]
    exact fun b => (norm_lt_of_weight_ne_zero h b).le
private theorem integrable_weighted_exp (hρ : 0 < ρ) (hp : IsCutoff ρ p) {Φ : BondField ι → ℝ}
    (hΦ : ContinuousOn Φ (closedBalls ρ)) :
    Integrable fun η => radialWeightProd (cutoffFactor ρ p) η * Real.exp (-Φ η) := by
  rw [weighted_exp_eq_indicator]
  have hc : ContinuousOn (fun η => Real.exp (-Φ η)) (closedBalls ρ) :=
    Real.continuous_exp.comp_continuousOn hΦ.neg
  have hi : Integrable ((closedBalls ρ).indicator fun η => Real.exp (-Φ η)) :=
    (integrable_indicator_iff (measurableSet_closedBalls ρ)).2
      (hc.integrableOn_compact (isCompact_closedBalls ρ))
  refine hi.mono ((weight_measurable hp).aestronglyMeasurable.mul
    (aestronglyMeasurable_indicator_closedBalls hc)) (ae_of_all _ fun η => ?_)
  rw [norm_mul, Real.norm_of_nonneg (weight_nonneg η)]
  calc _ ≤ 1 * ‖(closedBalls ρ).indicator (fun η => Real.exp (-Φ η)) η‖ :=
        mul_le_mul_of_nonneg_right (weight_le_one hρ hp η) (norm_nonneg _)
    _ = _ := one_mul _
private theorem integral_weighted_exp_pos (hρ : 0 < ρ) (hp : IsCutoff ρ p) {Φ : BondField ι → ℝ}
    (hΦ : ContinuousOn Φ (closedBalls ρ)) :
    0 < ∫ η, radialWeightProd (cutoffFactor ρ p) η * Real.exp (-Φ η) := by
  have hnn : 0 ≤ fun η : BondField ι => radialWeightProd (cutoffFactor ρ p) η * Real.exp (-Φ η) :=
    fun η => mul_nonneg (weight_nonneg η) (Real.exp_pos _).le
  rw [integral_pos_iff_support_of_nonneg hnn (integrable_weighted_exp hρ hp hΦ)]
  set U : Set (BondField ι) := Set.pi Set.univ fun _ => Metric.ball 0 (5 * ρ / 8) with hU
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  have hUn : U.Nonempty := ⟨0, fun b _ => by simp; positivity⟩
  refine (hUo.measure_pos volume hUn).trans_le (measure_mono fun η hη => ?_)
  have h1 : radialWeightProd (cutoffFactor ρ p) η = 1 := weight_eq_one hρ hp fun b => by
    have := hη b (Set.mem_univ b)
    simp only [Metric.mem_ball, dist_zero_right] at this
    exact this.le
  simp only [Function.mem_support, h1, one_mul]
  exact (Real.exp_pos _).ne'
private theorem momentLaw_weighted_exp (hρ : 0 < ρ) (hp : IsCutoff ρ p) {Φ S : BondField ι → ℝ}
    {a b s : ℝ} (hΦ : ContinuousOn Φ (closedBalls ρ)) (hS : ∀ η, 0 ≤ S η) (hSc : Continuous S)
    (ha : 0 < a) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hsN : (s ^ Module.finrank ℝ (BondField ι))⁻¹ ≤ Real.exp 1)
    (hgain : ∀ η ∈ closedBalls ρ, a * S η - b ≤ Φ η - Φ (s • η)) :
    IsMomentLaw (fun η => radialWeightProd (cutoffFactor ρ p) η * Real.exp (-Φ η)) S
      (fun k => (k.factorial : ℝ) * (a⁻¹) ^ k * Real.exp (a + b + 1)) := by
  refine momentLaw_of_radial_growth (fun η => mul_nonneg (weight_nonneg η) (Real.exp_pos _).le)
    (integrable_weighted_exp hρ hp hΦ) (integral_weighted_exp_pos hρ hp hΦ) hS hSc ha hs0 hsN
    fun η => ?_
  by_cases h : radialWeightProd (cutoffFactor ρ p) η = 0
  · simp only [h, zero_mul]
    exact mul_nonneg (weight_nonneg _) (Real.exp_pos _).le
  · have hb : η ∈ closedBalls ρ := fun b => (norm_lt_of_weight_ne_zero h b).le
    have h1 := weight_le_weight_smul hρ hp η hs0.le hs1
    have h2 := hgain η hb
    rw [mul_assoc, ← Real.exp_add]
    have h3 : Real.exp (-Φ η + (a * S η - b)) ≤ Real.exp (-Φ (s • η)) :=
      Real.exp_le_exp.2 (by linarith)
    exact mul_le_mul h1 h3 (Real.exp_pos _).le (weight_nonneg _)
end Cut
section Bridge
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private def coordUnit (i : ι × Fin 3) : BondField ι := bondVariation i.1 (EuclideanSpace.single i.2 1)
private theorem sum_single_bondVector (v : BondVector) :
    ∑ c, (v c) • EuclideanSpace.single c (1 : ℝ) = v := by apply _root_.YangMills.Construction.BondIntegration.sum_smul_bondBasis <;> assumption
private theorem sum_coordUnit (η : BondField ι) : ∑ i, (η i.1 i.2) • coordUnit i = η := by
  rw [Fintype.sum_prod_type]
  have h : ∀ b, ∑ c, (η b c) • coordUnit (b, c) = Pi.single b (η b) := by
    intro b
    have e : ∀ c, (η b c) • coordUnit (b, c) =
        Pi.single b ((η b c) • EuclideanSpace.single c (1 : ℝ)) := by
      intro c
      simp [coordUnit, bondVariation, Pi.single_smul]
    simp_rw [e]
    have m : Pi.single b (∑ c, (η b c) • EuclideanSpace.single c (1 : ℝ)) =
        ∑ c, (Pi.single b ((η b c) • EuclideanSpace.single c (1 : ℝ)) : BondField ι) :=
      map_sum (AddMonoidHom.single (fun _ : ι => BondVector) b) _ _
    rw [← m, sum_single_bondVector]
  simp_rw [h]
  exact Finset.univ_sum_single η
private theorem sum_liftField (c : ι × Fin 3 → ℝ) :
    ∑ i, c i • liftField (coordUnit i) = liftField (∑ i, c i • coordUnit i) := by
  have : ∀ η : BondField ι, liftField η =
      ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (BondField ι) η := by
    intro η
    simp [liftField]
  simp_rw [this, map_sum, map_smul]
private def toBilin (Ψ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ParamBondField ι) ℝ) :
    ParamBondField ι →ₗ[ℝ] ParamBondField ι →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => Ψ (Fin.cons u (Fin.cons v noVec)))
    (fun u u' v => Ψ.cons_add _ u u')
    (fun c u v => Ψ.cons_smul _ c u)
    (fun u v v' => by
      have := (Ψ.curryLeft u).cons_add noVec v v'
      simpa only [ContinuousMultilinearMap.curryLeft_apply] using this)
    (fun c u v => by
      have := (Ψ.curryLeft u).cons_smul noVec c v
      simpa only [ContinuousMultilinearMap.curryLeft_apply] using this)
private theorem bilin_expand (Ψ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ParamBondField ι) ℝ)
    (η : BondField ι) :
    Ψ (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) =
      ∑ i, ∑ j, Ψ (Fin.cons (liftField (coordUnit j)) (Fin.cons (liftField (coordUnit i)) noVec)) *
        (η i.1 i.2 * η j.1 j.2) := by
  have key : ∀ c : ι × Fin 3 → ℝ, toBilin Ψ (∑ i, c i • liftField (coordUnit i))
      (∑ i, c i • liftField (coordUnit i)) =
      ∑ i, ∑ j, toBilin Ψ (liftField (coordUnit j)) (liftField (coordUnit i)) * (c i * c j) := by
    intro c
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h := key fun i => η i.1 i.2
  rw [sum_liftField, sum_coordUnit] at h
  exact h
private theorem quadraticForm_eq_bilin
    (Ψ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ParamBondField ι) ℝ)
    (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    (hM : ∀ i j, M i j = Ψ (Fin.cons (liftField (coordUnit j)) (Fin.cons (liftField (coordUnit i)) noVec)))
    (η : BondField ι) : quadraticForm M η = Ψ (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) := by
  rw [bilin_expand]
  unfold quadraticForm
  simp_rw [hM]
private theorem continuous_quadraticForm (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    Continuous (quadraticForm M : BondField ι → ℝ) := by
  unfold quadraticForm
  fun_prop
private def coordPair (i j : ι × Fin 3) : Fin 2 → ParamBondField ι :=
  Fin.cons (liftField (coordUnit j)) (Fin.cons (liftField (coordUnit i)) noVec)
variable {ρ lam K : ℝ} {Q B : ParamBondField ι → ℝ}
private theorem familyHessian_apply {τ : Fin 2 → ℝ}
    (h : ContDiffAt ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) Q (τ, 0)) (i j : ι × Fin 3) :
    familyHessian Q τ i j = iteratedFDeriv ℝ 2 Q (τ, 0) (coordPair i j) :=
  secondDerivAlong_eq_iteratedFDeriv h _ _
private theorem fderiv_param_at_zero {G : ParamBondField ι → ℝ} (h : DifferentiableAt ℝ G (liftField 0))
    (e : Fin 2 → ℝ) :
    fderiv ℝ (fun τ => G (τ, 0)) 0 e = fderiv ℝ G (liftField 0) (e, 0) :=
  fderiv_paramSlice h e
private theorem second_deriv_param_at_zero {G : ParamBondField ι → ℝ}
    (h : ContDiffAt ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) G (liftField 0)) :
    iteratedFDeriv ℝ 2 (fun τ => G (τ, 0)) 0 (fun l => Pi.single l 1) =
      iteratedFDeriv ℝ 2 G (liftField 0) (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) := by
  have h0 : ContDiffAt ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) G (liftField 0) := h.of_le (by norm_cast)
  have hc : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun τ : Fin 2 → ℝ => G (τ, 0)) 0 := by
    have h2 : ContDiffAt ℝ (2 : WithTop ℕ∞) G
        ((fun τ : Fin 2 → ℝ => ((τ, 0) : ParamBondField ι)) 0) := by
      exact_mod_cast h
    exact h2.comp (0 : Fin 2 → ℝ) (by fun_prop)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun τ : Fin 2 → ℝ => G (τ, 0))) 0 :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [iteratedFDeriv_two_apply]
  have e2 := ((ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : Fin 2 → ℝ)).hasFDerivAt.comp
    (0 : Fin 2 → ℝ) hd.hasFDerivAt).fderiv
  have e3 : (fun τ => fderiv ℝ (fun τ : Fin 2 → ℝ => G (τ, 0)) τ (Pi.single 1 1)) =
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : Fin 2 → ℝ)) ∘
        fderiv ℝ (fun τ : Fin 2 → ℝ => G (τ, 0)) := rfl
  have e4 : fderiv ℝ (fderiv ℝ (fun τ : Fin 2 → ℝ => G (τ, 0))) 0 (Pi.single 0 1) (Pi.single 1 1) =
      fderiv ℝ (fun τ => fderiv ℝ (fun τ : Fin 2 → ℝ => G (τ, 0)) τ (Pi.single 1 1)) 0
        (Pi.single 0 1) := by
    rw [e3, e2]
    simp
  have hev : (fun τ => fderiv ℝ (fun τ : Fin 2 → ℝ => G (τ, 0)) τ (Pi.single 1 1)) =ᶠ[𝓝 0]
      fun τ => iteratedFDeriv ℝ 1 G (τ, 0) (Fin.cons (paramUnit 1) noVec) := by
    filter_upwards [contDiffAt_eventually_param h0] with τ hτ
    rw [fderiv_paramSlice (hτ.differentiableAt (by simp)), iteratedFDeriv_one_apply]
    simp [paramUnit]
  show fderiv ℝ (fderiv ℝ (fun τ : Fin 2 → ℝ => G (τ, 0))) 0 (Pi.single 0 1) (Pi.single 1 1) = _
  rw [e4, hev.fderiv_eq]
  have hd2 : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ 1 G z (Fin.cons (paramUnit 1) noVec))
      (liftField 0) :=
    (hasFDerivAt_iteratedFDeriv_apply h _).differentiableAt
  have := fderiv_paramSlice (g := fun z => iteratedFDeriv ℝ 1 G z (Fin.cons (paramUnit 1) noVec)) hd2
    (Pi.single 0 1)
  refine this.trans ?_
  exact fderiv_iteratedFDeriv_apply h _ _
private theorem iteratedFDeriv_two_iteratedFDeriv {f : ParamBondField ι → ℝ} {n : ℕ}
    {z : ParamBondField ι} (h : ContDiffAt ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f z)
    (w : Fin n → ParamBondField ι) (a b : ParamBondField ι) :
    iteratedFDeriv ℝ 2 (fun y => iteratedFDeriv ℝ n f y w) z (Fin.cons a (Fin.cons b noVec)) =
      iteratedFDeriv ℝ (n + 2) f z (Fin.cons a (Fin.cons b w)) := by
  have h1 : ContDiffAt ℝ ((n + 1 + 1 : ℕ) : WithTop ℕ∞) f z := h
  have hc : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f z := h1.of_le (by norm_cast; omega)
  have hG : ContDiffAt ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (fun y => iteratedFDeriv ℝ n f y w) z :=
    contDiffAt_iteratedFDeriv_apply (k := 1 + 1) h w
  have hev : (fun y => iteratedFDeriv ℝ 1 (fun y => iteratedFDeriv ℝ n f y w) y
      (Fin.cons b noVec)) =ᶠ[𝓝 z] fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.cons b w) := by
    filter_upwards [contDiffAt_eventually hc] with y hy
    rw [iteratedFDeriv_one_apply]
    simp only [Fin.cons_zero]
    exact fderiv_iteratedFDeriv_apply hy w b
  rw [← fderiv_iteratedFDeriv_apply hG (Fin.cons b noVec) a, hev.fderiv_eq]
  exact fderiv_iteratedFDeriv_apply h1 _ _
end Bridge
section Matrices
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ρ lam K x : ℝ} {Q B : ParamBondField ι → ℝ}
private def scaledHessian (x : ℝ) (Q : ParamBondField ι → ℝ) (τ : Fin 2 → ℝ) :
    Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  x • familyHessian Q τ
private theorem scaledHessian_eventually_eq (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B) :
    ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), ∀ i j,
      scaledHessian x Q τ i j = x * iteratedFDeriv ℝ 2 Q (τ, 0) (coordPair i j) := by
  filter_upwards [contDiffAt_eventually_param (n := 1 + 1)
    (contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num))] with τ hτ i j
  simp [scaledHessian, familyHessian_apply hτ]
private theorem scaledHessian_zero (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (i j : ι × Fin 3) :
    scaledHessian x Q 0 i j = x * iteratedFDeriv ℝ 2 Q 0 (coordPair i j) :=
  (scaledHessian_eventually_eq hρ LF).self_of_nhds i j
private theorem contDiffAt_scaledHessian (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (i j : ι × Fin 3) :
    ContDiffAt ℝ 3 (fun τ => scaledHessian x Q τ i j) 0 := by
  have hG : ContDiffAt ℝ (3 : WithTop ℕ∞) (fun z => iteratedFDeriv ℝ 2 Q z (coordPair i j))
      ((fun τ : Fin 2 → ℝ => ((τ, 0) : ParamBondField ι)) 0) := by
    have := contDiffAt_iteratedFDeriv_apply (n := 2) (k := 3)
      (contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)) (coordPair i j)
    exact_mod_cast this
  have h0 : ContDiffAt ℝ (3 : WithTop ℕ∞)
      (fun τ : Fin 2 → ℝ => iteratedFDeriv ℝ 2 Q (τ, 0) (coordPair i j)) 0 :=
    ContDiffAt.comp (g := fun z => iteratedFDeriv ℝ 2 Q z (coordPair i j))
      (f := fun τ : Fin 2 → ℝ => ((τ, 0) : ParamBondField ι)) 0 hG (by fun_prop)
  have h1 : ContDiffAt ℝ (3 : WithTop ℕ∞)
      (fun τ : Fin 2 → ℝ => x * iteratedFDeriv ℝ 2 Q (τ, 0) (coordPair i j)) 0 :=
    contDiffAt_const.mul h0
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [scaledHessian_eventually_eq (x := x) hρ LF] with τ h
  exact h i j
private theorem scaledHessian_isSymm (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B) :
    ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), (scaledHessian x Q τ).IsSymm := by
  filter_upwards [scaledHessian_eventually_eq (x := x) hρ LF,
    contDiffAt_eventually_param (n := 0 + 2) (contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num))]
    with τ h hτ
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [h, h]
  congr 1
  exact iteratedFDeriv_swap_first hτ _ _ _
private theorem familyPartialDeriv_scaledHessian (hρ : 0 < ρ)
    (LF : IsAdmissibleExponentFamily ρ lam K Q B) (l : Fin 2) (i j : ι × Fin 3) :
    familyPartialDeriv (scaledHessian x Q) l i j =
      x * iteratedFDeriv ℝ 3 Q 0 (Fin.cons (paramUnit l) (coordPair i j)) := by
  have hev : (fun τ => scaledHessian x Q τ i j) =ᶠ[𝓝 0]
      fun τ => (fun z => x * iteratedFDeriv ℝ 2 Q z (coordPair i j)) (τ, 0) := by
    filter_upwards [scaledHessian_eventually_eq (x := x) hρ LF] with τ h
    exact h i j
  have c3 : ContDiffAt ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) Q (liftField 0) :=
    contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ 2 Q z (coordPair i j)) (liftField 0) :=
    (hasFDerivAt_iteratedFDeriv_apply c3 _).differentiableAt
  unfold familyPartialDeriv
  rw [hev.fderiv_eq, fderiv_param_at_zero (hd.const_mul x), fderiv_const_mul hd]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  congr 1
  exact fderiv_iteratedFDeriv_apply c3 _ _
private theorem familyMixedDeriv_scaledHessian (hρ : 0 < ρ)
    (LF : IsAdmissibleExponentFamily ρ lam K Q B) (i j : ι × Fin 3) :
    familyMixedDeriv (scaledHessian x Q) i j =
      x * iteratedFDeriv ℝ 4 Q 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) (coordPair i j))) := by
  have hev : (fun τ => scaledHessian x Q τ i j) =ᶠ[𝓝 0]
      fun τ => (fun z => x * iteratedFDeriv ℝ 2 Q z (coordPair i j)) (τ, 0) := by
    filter_upwards [scaledHessian_eventually_eq (x := x) hρ LF] with τ h
    exact h i j
  have c4 : ContDiffAt ℝ ((2 + 2 : ℕ) : WithTop ℕ∞) Q (liftField 0) :=
    contDiffAt_Q LF (mem_ball_zero hρ) (by norm_num)
  have hG : ContDiffAt ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (fun z => iteratedFDeriv ℝ 2 Q z (coordPair i j))
      (liftField 0) := contDiffAt_iteratedFDeriv_apply (k := 1 + 1) c4 _
  have hGx : ContDiffAt ℝ ((1 + 1 : ℕ) : WithTop ℕ∞)
      (fun z => x * iteratedFDeriv ℝ 2 Q z (coordPair i j)) (liftField 0) := contDiffAt_const.mul hG
  unfold familyMixedDeriv
  have e1 := (hev.iteratedFDeriv ℝ 2).eq_of_nhds
  rw [e1, second_deriv_param_at_zero hGx]
  have e2 : (fun z => x * iteratedFDeriv ℝ 2 Q z (coordPair i j)) =
      x • fun z => iteratedFDeriv ℝ 2 Q z (coordPair i j) := by
    funext z
    simp
  rw [e2, iteratedFDeriv_const_smul_apply (by exact_mod_cast hG)]
  simp only [Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  exact iteratedFDeriv_two_iteratedFDeriv c4 _ _ _
private theorem quadraticForm_scaledHessian_zero (hρ : 0 < ρ)
    (LF : IsAdmissibleExponentFamily ρ lam K Q B) (η : BondField ι) :
    quadraticForm (scaledHessian x Q 0) η =
      x * iteratedFDeriv ℝ 2 Q 0 (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) :=
  quadraticForm_eq_bilin (x • iteratedFDeriv ℝ 2 Q 0) _ (fun i j => scaledHessian_zero hρ LF i j) η
private theorem quadraticForm_partial (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (l : Fin 2) (η : BondField ι) :
    quadraticForm (familyPartialDeriv (scaledHessian x Q) l) η =
      x * iteratedFDeriv ℝ 3 Q 0 (Fin.cons (paramUnit l)
        (Fin.cons (liftField η) (Fin.cons (liftField η) noVec))) :=
  quadraticForm_eq_bilin (x • (iteratedFDeriv ℝ 3 Q 0).curryLeft (paramUnit l)) _
    (fun i j => familyPartialDeriv_scaledHessian hρ LF l i j) η
private theorem quadraticForm_mixed (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (η : BondField ι) :
    quadraticForm (familyMixedDeriv (scaledHessian x Q)) η =
      x * iteratedFDeriv ℝ 4 Q 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1)
        (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)))) :=
  quadraticForm_eq_bilin
    (x • ((iteratedFDeriv ℝ 4 Q 0).curryLeft (paramUnit 0)).curryLeft (paramUnit 1)) _
    (fun i j => familyMixedDeriv_scaledHessian hρ LF i j) η
private theorem quadraticForm_smul (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (s : ℝ) (η : BondField ι) :
    quadraticForm M (s • η) = s ^ 2 * quadraticForm M η := by
  unfold quadraticForm
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring
private def sqNorm (η : BondField ι) : ℝ := ∑ b, ‖η b‖ ^ 2
private theorem sqNorm_nonneg (η : BondField ι) : 0 ≤ sqNorm η :=
  Finset.sum_nonneg fun _ _ => by positivity
private theorem continuous_sqNorm : Continuous (sqNorm : BondField ι → ℝ) := by
  unfold sqNorm
  fun_prop
private theorem norm_sq_le_sqNorm (η : BondField ι) : ‖η‖ ^ 2 ≤ sqNorm η := by
  have h : ‖η‖ ≤ Real.sqrt (sqNorm η) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun b => ‖η b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
  calc ‖η‖ ^ 2 ≤ Real.sqrt (sqNorm η) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt (sqNorm_nonneg η)
abbrev _root_.YangMills.DeltaSharedProofs.p501099 := @norm_sq_le_sqNorm
private theorem hessian_lower_bound (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    {ζ : BondField ι} (hζ : ∀ b, ‖ζ b‖ ≤ ρ) (η : BondField ι) :
    lam * sqNorm η ≤
      iteratedFDeriv ℝ 2 Q (liftField ζ) (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) := by
  have h := LF.hessian_lower ζ hζ η
  rw [secondDerivAlong_eq_iteratedFDeriv (contDiffAt_Q LF hζ (by norm_num))] at h
  exact h
private theorem abs_second_iteratedFDeriv_le {f : ParamBondField ι → ℝ} {z : ParamBondField ι} {L : ℝ}
    (hb : ‖iteratedFDeriv ℝ 2 f z‖ ≤ L) (hL : 0 ≤ L) (η : BondField ι) :
    |iteratedFDeriv ℝ 2 f z (Fin.cons (liftField η) (Fin.cons (liftField η) noVec))| ≤
      L * sqNorm η := by
  have h := abs_iteratedFDeriv_apply_le hb (Fin.cons (liftField η) (Fin.cons (liftField η) noVec))
  have e : (∏ i, ‖(Fin.cons (liftField η) (Fin.cons (liftField η) noVec) :
      Fin 2 → ParamBondField ι) i‖) = ‖η‖ ^ 2 := by
    simp [Fin.prod_univ_succ, norm_liftField, sq]
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_sq_le_sqNorm η) hL)
private theorem quadraticForm_lower (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hx : 0 ≤ x) (η : BondField ι) :
    x * lam * sqNorm η ≤ quadraticForm (scaledHessian x Q 0) η := by
  rw [quadraticForm_scaledHessian_zero hρ LF, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hessian_lower_bound hρ LF (mem_ball_zero hρ) η) hx
private theorem linear_le_quadratic_add {lam K e x : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hKx : K ^ 2 ≤ x) : K * e ≤ lam * x * e ^ 2 / 8 + 2 / lam := by
  have h1 : lam * K ^ 2 * e ^ 2 / 8 - K * e + 2 / lam = 2 / lam * (lam * K * e / 4 - 1) ^ 2 := by
    field_simp
    ring
  have h2 : 0 ≤ 2 / lam * (lam * K * e / 4 - 1) ^ 2 := by positivity
  have h3 : lam * K ^ 2 * e ^ 2 / 8 ≤ lam * x * e ^ 2 / 8 := by gcongr
  linarith
private theorem linearExponent_radial_gain (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hlam : 0 < lam) (hK : 0 ≤ K) (hKx : K ^ 2 ≤ x) (hKl : K ≤ x * lam / 2) (hx : 0 ≤ x)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ ≤ ρ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 - s) * (lam * (x * sqNorm η) / 8 - 2 / lam) ≤
      linearExponent x Q B (liftField η) - linearExponent x Q B (liftField (s • η)) := by
  set A := linearExponent x Q B with hA
  have cA : ∀ (n : ℕ), n ≤ 3 → ∀ ζ : BondField ι, (∀ b, ‖ζ b‖ ≤ ρ) →
      ContDiffAt ℝ (n : WithTop ℕ∞) A (liftField ζ) := fun n hn ζ hζ =>
    (contDiffAt_const.mul (contDiffAt_Q LF hζ (by omega))).add (contDiffAt_B LF hζ hn)
  set M : ℝ := x * lam / 2 * sqNorm η with hM
  have hsq := sqNorm_nonneg η
  have d₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s => iteratedFDeriv ℝ 0 A (s • liftField η) noVec)
      (iteratedFDeriv ℝ 1 A (t • liftField η) (Fin.cons (liftField η) noVec)) t := fun t ht =>
    hasDerivAt_iteratedFDeriv_ray (by
      rw [smul_liftField]
      exact cA _ (by norm_num) _ (mem_ball_smul hη ht)) noVec
  have d₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt
      (fun s => iteratedFDeriv ℝ 1 A (s • liftField η) (Fin.cons (liftField η) noVec))
      (iteratedFDeriv ℝ 2 A (t • liftField η)
        (Fin.cons (liftField η) (Fin.cons (liftField η) noVec))) t := fun t ht =>
    hasDerivAt_iteratedFDeriv_ray (by
      rw [smul_liftField]
      exact cA _ (by norm_num) _ (mem_ball_smul hη ht)) _
  have hM2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, M ≤
      iteratedFDeriv ℝ 2 A (t • liftField η) (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) := by
    intro t ht
    rw [smul_liftField]
    have hb := mem_ball_smul hη ht
    rw [hA, iteratedFDeriv_linearExponent (contDiffAt_Q LF hb (by norm_num))
      (contDiffAt_B LF hb (by norm_num))]
    have h1 := hessian_lower_bound hρ LF hb η
    have h2 := abs_second_iteratedFDeriv_le (LF.deriv_bound_B _ hb 2 (by norm_num) (by norm_num)) hK η
    have h3 := (abs_le.1 h2).1
    have h4 : x * (lam * sqNorm η) ≤
        x * iteratedFDeriv ℝ 2 Q (liftField (t • η))
          (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) :=
      mul_le_mul_of_nonneg_left h1 hx
    have h5 : K * sqNorm η ≤ x * lam / 2 * sqNorm η := mul_le_mul_of_nonneg_right hKl hsq
    rw [hM]
    have h6 : iteratedFDeriv ℝ 2 B (liftField (t • η))
        (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) ≥ -(K * sqNorm η) := h3
    nlinarith
  have hg := gain_of_second_deriv_lower d₀ d₁ hM2 hs
  simp only [iteratedFDeriv_zero_apply, one_smul, zero_smul] at hg
  have h0 : iteratedFDeriv ℝ 1 A 0 (Fin.cons (liftField η) noVec) ≥ -(K * ‖η‖) := by
    have c1q := contDiffAt_Q (n := 1) LF (mem_ball_zero hρ) (by norm_num)
    have c1b := contDiffAt_B (n := 1) LF (mem_ball_zero hρ) (by norm_num)
    have e1 := iteratedFDeriv_linearExponent (x := x) c1q c1b (Fin.cons (liftField η) noVec)
    rw [liftField_zero] at e1
    have e2 : iteratedFDeriv ℝ 1 Q 0 (Fin.cons (liftField η) noVec) = 0 :=
      (first_deriv_field_eq_zero hρ LF).self_of_nhds η
    have e3 := abs_iteratedFDeriv_apply_le
      (LF.deriv_bound_B 0 (mem_ball_zero hρ) 1 (by norm_num) (by norm_num))
      (Fin.cons (liftField η) noVec)
    have e4 : (∏ i, ‖(Fin.cons (liftField η) noVec : Fin 1 → ParamBondField ι) i‖) = ‖η‖ := by
      simp [norm_liftField]
    rw [e4] at e3
    have e5 := (abs_le.1 e3).1
    rw [hA, e1, e2]
    have e6 : iteratedFDeriv ℝ 1 B 0 (Fin.cons (liftField η) noVec) ≥ -(K * ‖η‖) := e5
    linarith
  have hsd := linear_le_quadratic_add hlam hK (norm_nonneg η) hKx
  have hnn := norm_sq_le_sqNorm η
  have h1s : 0 ≤ 1 - s := by linarith [hs.2]
  have hs0 := hs.1
  have key : lam * (x * sqNorm η) / 8 - 2 / lam ≤ -(K * ‖η‖) + M / 2 := by
    have h7 : lam * x * ‖η‖ ^ 2 / 8 ≤ lam * (x * sqNorm η) / 8 := by
      have : lam * x * ‖η‖ ^ 2 ≤ lam * x * sqNorm η := by gcongr
      linarith
    rw [hM]
    nlinarith
  have hfin : (1 - s) * (-(K * ‖η‖) + M / 2) ≤
      (1 - s) * iteratedFDeriv ℝ 1 A 0 (Fin.cons (liftField η) noVec) + M * (1 - s ^ 2) / 2 := by
    have : (1 - s) * (M / 2) ≤ M * (1 - s ^ 2) / 2 := by
      have : M * (1 - s ^ 2) / 2 - (1 - s) * (M / 2) = M * (1 - s) * s / 2 := by ring
      have h9 : 0 ≤ M * (1 - s) * s / 2 := by positivity
      linarith
    have h8 := mul_le_mul_of_nonneg_left h0 h1s
    nlinarith
  have e7 : s • liftField η = liftField (s • η) := smul_liftField s η
  rw [e7] at hg
  calc _ ≤ (1 - s) * (-(K * ‖η‖) + M / 2) := mul_le_mul_of_nonneg_left key h1s
    _ ≤ _ := hfin
    _ ≤ _ := hg
end Matrices
section Means
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {f S g h : BondField ι → ℝ} {m : ℕ → ℝ}
private theorem IsPolyBounded.mono {k k' : ℕ} {M M' : ℝ} (t : IsPolyBounded f S g k M)
    (hS : ∀ η, 0 ≤ S η) (hk : k ≤ k') (hM : M ≤ M') (hM' : 0 ≤ M') : IsPolyBounded f S g k' M' := by
  refine ⟨t.meas, fun η h0 => (t.bound η h0).trans ?_⟩
  have h1 : 1 ≤ 1 + S η := by linarith [hS η]
  have h2 : (1 + S η) ^ k ≤ (1 + S η) ^ k' := pow_le_pow_right₀ h1 hk
  have h3 : 0 ≤ (1 + S η) ^ k := by positivity
  calc M * (1 + S η) ^ k ≤ M' * (1 + S η) ^ k := mul_le_mul_of_nonneg_right hM h3
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hM'
private theorem IsPolyBounded.mul {k₁ k₂ : ℕ} {M₁ M₂ : ℝ} (t₁ : IsPolyBounded f S g k₁ M₁)
    (t₂ : IsPolyBounded f S h k₂ M₂) (hS : ∀ η, 0 ≤ S η) (h₁ : 0 ≤ M₁) :
    IsPolyBounded f S (fun η => g η * h η) (k₁ + k₂) (M₁ * M₂) := by
  refine ⟨t₁.meas.mul t₂.meas, fun η h0 => ?_⟩
  rw [abs_mul, pow_add]
  have h3 : 0 ≤ (1 + S η) ^ k₁ := pow_nonneg (by linarith [hS η]) _
  calc |g η| * |h η| ≤ (M₁ * (1 + S η) ^ k₁) * (M₂ * (1 + S η) ^ k₂) :=
        mul_le_mul (t₁.bound η h0) (t₂.bound η h0) (abs_nonneg _) (by positivity)
    _ = _ := by ring
private theorem densityMean_const_mul (c : ℝ) (g : BondField ι → ℝ) :
    densityMean f (fun η => c * g η) = c * densityMean f g := by
  unfold densityMean
  simp only [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]
private theorem densityMean_const (L : IsMomentLaw f S m) (c : ℝ) : densityMean f (fun _ => c) = c := by
  unfold densityMean
  rw [integral_const_mul, mul_div_assoc, div_self L.mass.ne', mul_one]
private theorem densityMean_congr (hg : ∀ η, f η ≠ 0 → g η = h η) : densityMean f g = densityMean f h := by
  unfold densityMean
  congr 1
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  by_cases h0 : f η = 0
  · simp [h0]
  · simp only
    rw [hg η h0]
private theorem densityMean_const_mul_density {c : ℝ} (hc : c ≠ 0) (f g : BondField ι → ℝ) :
    densityMean (fun η => c * f η) g = densityMean f g := by
  unfold densityMean
  have e : ∀ η, g η * (c * f η) = c * (g η * f η) := fun η => by ring
  simp_rw [e]
  rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ hc]
private theorem densityMean_add_of_integrable (hg : Integrable fun η => g η * f η)
    (hh : Integrable fun η => h η * f η) :
    densityMean f (fun η => g η + h η) = densityMean f g + densityMean f h := by
  unfold densityMean
  simp only [add_mul]
  rw [integral_add hg hh, add_div]
private theorem integrable_add_mul (hg : Integrable fun η => g η * f η)
    (hh : Integrable fun η => h η * f η) :
    Integrable fun η => (g η + h η) * f η := by
  refine (hg.add hh).congr (ae_of_all _ fun η => ?_)
  simp [add_mul]
private theorem integrable_const_mul_mul (c : ℝ) (hg : Integrable fun η => g η * f η) :
    Integrable fun η => (c * g η) * f η := by
  simpa only [mul_assoc] using hg.const_mul c
private theorem integrable_const_mul_density (L : IsMomentLaw f S m) (c : ℝ) :
    Integrable fun η => (fun _ => c) η * f η :=
  L.integrable_density.const_mul c
private theorem covariance_shift {u₀ u₁ : BondField ι → ℝ} {c₀ c₁ : ℝ} (L : IsMomentLaw f S m)
    (h₀ : Integrable fun η => u₀ η * f η) (h₁ : Integrable fun η => u₁ η * f η)
    (h₂ : Integrable fun η => (u₀ η * u₁ η) * f η) :
    densityMean f (fun η => (u₀ η + c₀) * (u₁ η + c₁)) -
        densityMean f (fun η => u₀ η + c₀) * densityMean f (fun η => u₁ η + c₁) =
      densityMean f (fun η => u₀ η * u₁ η) - densityMean f u₀ * densityMean f u₁ := by
  have e : (fun η => (u₀ η + c₀) * (u₁ η + c₁)) =
      fun η => ((u₀ η * u₁ η + c₁ * u₀ η) + c₀ * u₁ η) + (fun _ => c₀ * c₁) η := by
    funext η
    ring
  rw [e, densityMean_add_of_integrable (integrable_add_mul (integrable_add_mul h₂
      (integrable_const_mul_mul _ h₀)) (integrable_const_mul_mul _ h₁))
      (integrable_const_mul_density L _),
    densityMean_add_of_integrable (integrable_add_mul h₂ (integrable_const_mul_mul _ h₀))
      (integrable_const_mul_mul _ h₁),
    densityMean_add_of_integrable h₂ (integrable_const_mul_mul _ h₀),
    densityMean_add_of_integrable h₀ (integrable_const_mul_density L _),
    densityMean_add_of_integrable h₁ (integrable_const_mul_density L _),
    densityMean_const_mul, densityMean_const_mul,
    densityMean_const L, densityMean_const L, densityMean_const L]
  ring
private theorem covariance_expand {a₀ a₁ a₂ r₀ r₁ r₂ : BondField ι → ℝ} {c₀ c₁ c₂ : ℝ}
    (L₁ : IsMomentLaw f S m)
    (I₀ : Integrable fun η => a₀ η * f η) (I₁ : Integrable fun η => a₁ η * f η)
    (I₂ : Integrable fun η => a₂ η * f η) (Ir₀ : Integrable fun η => r₀ η * f η)
    (Ir₁ : Integrable fun η => r₁ η * f η) (Ir₂ : Integrable fun η => r₂ η * f η)
    (Ip : Integrable fun η => (a₀ η * a₁ η) * f η) (Iz₁ : Integrable fun η => (a₀ η * r₁ η) * f η)
    (Iz₂ : Integrable fun η => (r₀ η * a₁ η) * f η) (Iz₃ : Integrable fun η => (r₀ η * r₁ η) * f η) :
    densityMean f (fun η => -(a₂ η + c₂ + r₂ η) + (a₀ η + c₀ + r₀ η) * (a₁ η + c₁ + r₁ η)) -
        densityMean f (fun η => a₀ η + c₀ + r₀ η) * densityMean f (fun η => a₁ η + c₁ + r₁ η) =
      -densityMean f a₂ - densityMean f r₂ - c₂ +
        (densityMean f (fun η => a₀ η * a₁ η) + densityMean f (fun η => a₀ η * r₁ η) +
          densityMean f (fun η => r₀ η * a₁ η) + densityMean f (fun η => r₀ η * r₁ η)) -
        (densityMean f a₀ + densityMean f r₀) * (densityMean f a₁ + densityMean f r₁) := by
  have Iu₀ : Integrable fun η => (a₀ η + r₀ η) * f η := integrable_add_mul I₀ Ir₀
  have Iu₁ : Integrable fun η => (a₁ η + r₁ η) * f η := integrable_add_mul I₁ Ir₁
  have eU : (fun η => (a₀ η + r₀ η) * (a₁ η + r₁ η)) =
      fun η => ((a₀ η * a₁ η + a₀ η * r₁ η) + r₀ η * a₁ η) + r₀ η * r₁ η := by
    funext η
    ring
  have Iuu : Integrable fun η => ((a₀ η + r₀ η) * (a₁ η + r₁ η)) * f η := by
    have := integrable_add_mul (integrable_add_mul (integrable_add_mul Ip Iz₁) Iz₂) Iz₃
    refine this.congr (ae_of_all _ fun η => ?_)
    simp only
    ring
  have mUU : densityMean f (fun η => (a₀ η + r₀ η) * (a₁ η + r₁ η)) =
      densityMean f (fun η => a₀ η * a₁ η) + densityMean f (fun η => a₀ η * r₁ η) +
        densityMean f (fun η => r₀ η * a₁ η) + densityMean f (fun η => r₀ η * r₁ η) := by
    rw [eU, densityMean_add_of_integrable (integrable_add_mul (integrable_add_mul Ip Iz₁) Iz₂) Iz₃,
      densityMean_add_of_integrable (integrable_add_mul Ip Iz₁) Iz₂,
      densityMean_add_of_integrable Ip Iz₁]
  have cov := covariance_shift (c₀ := c₀) (c₁ := c₁) L₁ Iu₀ Iu₁ Iuu
  have mA₀ : densityMean f (fun η => a₀ η + r₀ η) = densityMean f a₀ + densityMean f r₀ :=
    densityMean_add_of_integrable I₀ Ir₀
  have mA₁ : densityMean f (fun η => a₁ η + r₁ η) = densityMean f a₁ + densityMean f r₁ :=
    densityMean_add_of_integrable I₁ Ir₁
  have e₀ : (fun η => a₀ η + c₀ + r₀ η) = fun η => a₀ η + r₀ η + c₀ := by
    funext η
    ring
  have e₁ : (fun η => a₁ η + c₁ + r₁ η) = fun η => a₁ η + r₁ η + c₁ := by
    funext η
    ring
  have Iprod : Integrable fun η => ((a₀ η + r₀ η + c₀) * (a₁ η + r₁ η + c₁)) * f η := by
    have := integrable_add_mul (integrable_add_mul (integrable_add_mul Iuu
      (integrable_const_mul_mul c₁ Iu₀)) (integrable_const_mul_mul c₀ Iu₁))
      (integrable_const_mul_density L₁ (c₀ * c₁))
    refine this.congr (ae_of_all _ fun η => ?_)
    simp only
    ring
  have eB : (fun η => -(a₂ η + c₂ + r₂ η) + (a₀ η + c₀ + r₀ η) * (a₁ η + c₁ + r₁ η)) =
      fun η => (((-1) * a₂ η + (-1) * r₂ η) + (fun _ => -c₂) η) +
        (a₀ η + r₀ η + c₀) * (a₁ η + r₁ η + c₁) := by
    funext η
    ring
  have mB : densityMean f (fun η => -(a₂ η + c₂ + r₂ η) + (a₀ η + c₀ + r₀ η) * (a₁ η + c₁ + r₁ η)) =
      -densityMean f a₂ - densityMean f r₂ - c₂ +
        densityMean f (fun η => (a₀ η + r₀ η + c₀) * (a₁ η + r₁ η + c₁)) := by
    rw [eB, densityMean_add_of_integrable (integrable_add_mul (integrable_add_mul
        (integrable_const_mul_mul _ I₂) (integrable_const_mul_mul _ Ir₂))
        (integrable_const_mul_density L₁ _)) Iprod,
      densityMean_add_of_integrable (integrable_add_mul (integrable_const_mul_mul _ I₂)
        (integrable_const_mul_mul _ Ir₂)) (integrable_const_mul_density L₁ _),
      densityMean_add_of_integrable (integrable_const_mul_mul _ I₂) (integrable_const_mul_mul _ Ir₂),
      densityMean_const_mul, densityMean_const_mul, densityMean_const L₁]
    ring
  rw [mUU, mA₀, mA₁] at cov
  rw [e₀, e₁, mB]
  linarith
private theorem error_arithmetic {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Z₁ Z₂ Z₃ G₀ G₁ G₂ G₃ M₂ Mm ε δ : ℝ}
    (hM₂1 : 1 ≤ M₂) (hMm : 1 ≤ Mm) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hsm : 7 * M₂ * (ε + δ) * Mm ^ 2 ≤ 1)
    (d₂ : |X₂ - G₂| ≤ 6 * M₂ * (ε + δ) * Mm ^ 2) (d₀ : |X₀ - G₀| ≤ 6 * M₂ * (ε + δ) * Mm ^ 2)
    (d₁ : |X₁ - G₁| ≤ 6 * M₂ * (ε + δ) * Mm ^ 2) (d₃ : |X₃ - G₃| ≤ 6 * M₂ * (ε + δ) * Mm ^ 2)
    (y₀ : |Y₀| ≤ ε * Mm) (y₁ : |Y₁| ≤ ε * Mm) (y₂ : |Y₂| ≤ ε * Mm)
    (z₁ : |Z₁| ≤ M₂ * ε * Mm) (z₂ : |Z₂| ≤ M₂ * ε * Mm) (z₃ : |Z₃| ≤ M₂ * ε * Mm)
    (g₀ : |G₀| ≤ M₂ * Mm) (g₁ : |G₁| ≤ M₂ * Mm) :
    |-(X₂ - G₂) - Y₂ + (X₃ - G₃) + (Z₁ + Z₂ + Z₃) - ((X₀ + Y₀) * (X₁ + Y₁) - G₀ * G₁)| ≤
      37 * M₂ ^ 2 * Mm ^ 3 * (ε + δ) := by
  have ht : 0 ≤ ε + δ := by positivity
  have hM0 : 0 ≤ M₂ := by linarith
  have hMm0 : 0 ≤ Mm := by linarith
  set Q0 : ℝ := M₂ * Mm ^ 2 * (ε + δ) with hQ0
  have hQ0n : 0 ≤ Q0 := by positivity
  have hEc : 6 * M₂ * (ε + δ) * Mm ^ 2 = 6 * Q0 := by
    rw [hQ0]
    ring
  rw [hEc] at d₀ d₁ d₂ d₃
  have hMm2 : Mm ≤ Mm ^ 2 := le_self_pow₀ hMm (by norm_num)
  have hM2Mm : 1 ≤ M₂ * Mm := one_le_mul_of_one_le_of_one_le hM₂1 hMm
  have hεt : ε ≤ ε + δ := by linarith
  have hεM1 : ε * Mm ≤ Q0 := by
    calc ε * Mm ≤ (ε + δ) * Mm ^ 2 := mul_le_mul hεt hMm2 hMm0 ht
      _ = 1 * Mm ^ 2 * (ε + δ) := by ring
      _ ≤ Q0 := by
          rw [hQ0]
          gcongr
  have hεM2 : M₂ * ε * Mm ≤ Q0 := by
    calc M₂ * ε * Mm = M₂ * (ε * Mm) := by ring
      _ ≤ M₂ * ((ε + δ) * Mm ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hεt hMm2 hMm0 ht) hM0
      _ = Q0 := by
          rw [hQ0]
          ring
  have u₀ : |X₀ + Y₀ - G₀| ≤ 7 * Q0 := by
    have e : X₀ + Y₀ - G₀ = (X₀ - G₀) + Y₀ := by ring
    rw [e]
    have := abs_add_le (X₀ - G₀) Y₀
    linarith
  have u₁ : |X₁ + Y₁ - G₁| ≤ 7 * Q0 := by
    have e : X₁ + Y₁ - G₁ = (X₁ - G₁) + Y₁ := by ring
    rw [e]
    have := abs_add_le (X₁ - G₁) Y₁
    linarith
  have hU1 : |X₁ + Y₁| ≤ M₂ * Mm + 1 := by
    have e : X₁ + Y₁ = (X₁ + Y₁ - G₁) + G₁ := by ring
    rw [e]
    have := abs_add_le (X₁ + Y₁ - G₁) G₁
    linarith
  have hUU : |(X₀ + Y₀) * (X₁ + Y₁) - G₀ * G₁| ≤
      7 * Q0 * (M₂ * Mm + 1) + (M₂ * Mm) * (7 * Q0) := by
    have e : (X₀ + Y₀) * (X₁ + Y₁) - G₀ * G₁ =
        (X₀ + Y₀ - G₀) * (X₁ + Y₁) + G₀ * (X₁ + Y₁ - G₁) := by ring
    rw [e]
    have h1 : |(X₀ + Y₀ - G₀) * (X₁ + Y₁)| ≤ 7 * Q0 * (M₂ * Mm + 1) := by
      rw [abs_mul]
      exact mul_le_mul u₀ hU1 (abs_nonneg _) (by positivity)
    have h2 : |G₀ * (X₁ + Y₁ - G₁)| ≤ (M₂ * Mm) * (7 * Q0) := by
      rw [abs_mul]
      exact mul_le_mul g₀ u₁ (abs_nonneg _) (by positivity)
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have t₃ : |Z₁ + Z₂ + Z₃| ≤ 3 * Q0 := by
    have h1 := abs_add_three Z₁ Z₂ Z₃
    linarith
  have total : |-(X₂ - G₂) - Y₂ + (X₃ - G₃) + (Z₁ + Z₂ + Z₃) -
      ((X₀ + Y₀) * (X₁ + Y₁) - G₀ * G₁)| ≤
      |X₂ - G₂| + |Y₂| + |X₃ - G₃| + |Z₁ + Z₂ + Z₃| +
        |(X₀ + Y₀) * (X₁ + Y₁) - G₀ * G₁| := by
    have a1 := abs_sub (-(X₂ - G₂) - Y₂ + (X₃ - G₃) + (Z₁ + Z₂ + Z₃))
      ((X₀ + Y₀) * (X₁ + Y₁) - G₀ * G₁)
    have a2 := abs_add_le (-(X₂ - G₂) - Y₂ + (X₃ - G₃)) (Z₁ + Z₂ + Z₃)
    have a3 := abs_add_le (-(X₂ - G₂) - Y₂) (X₃ - G₃)
    have a4 := abs_sub (-(X₂ - G₂)) Y₂
    rw [abs_neg] at a4
    linarith
  have h1 : Q0 ≤ M₂ * Mm * Q0 := le_mul_of_one_le_left hQ0n hM2Mm
  have e : 37 * M₂ ^ 2 * Mm ^ 3 * (ε + δ) = 37 * (M₂ * Mm * Q0) := by
    rw [hQ0]
    ring
  have e2 : 7 * Q0 * (M₂ * Mm + 1) + (M₂ * Mm) * (7 * Q0) = 14 * (M₂ * Mm * Q0) + 7 * Q0 := by ring
  rw [e]
  rw [e2] at hUU
  linarith
variable {f₁ f₀ fg R W a₀ a₁ a₂ r₀ r₁ r₂ : BondField ι → ℝ}
variable {K ε δ Mm c₀ c₁ c₂ : ℝ}
private theorem abs_densityMean_sub_gaussian {M : ℝ} (L₁ : IsMomentLaw f₁ S m) (L₀ : IsMomentLaw f₀ S m)
    (Lg : IsMomentLaw fg S m)
    (hf : ∀ η, f₁ η = f₀ η * Real.exp (-R η)) (hf₀ : ∀ η, f₀ η = W η * fg η)
    (hW₀ : ∀ η, 0 ≤ W η) (hW₁ : ∀ η, W η ≤ 1) (hWδ : ∀ η, W η ≠ 1 → 1 ≤ δ * (1 + S η))
    (hR : IsPolyBounded f₀ S R 2 ε) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hMm : 1 ≤ Mm)
    (hm : ∀ j, 0 ≤ m j) (hmM : ∀ j ≤ 4, m j ≤ Mm) (hεs : ε * Mm ≤ 1 / 4) (hδs : δ * Mm ≤ 1 / 4)
    (t₁ : IsPolyBounded f₁ S g 2 M) (t₀ : IsPolyBounded f₀ S g 2 M) (tg : IsPolyBounded fg S g 2 M)
    (hM : 0 ≤ M) :
    |densityMean f₁ g - densityMean fg g| ≤ 6 * M * (ε + δ) * Mm ^ 2 := by
  have hm2 := hmM 2 (by norm_num)
  have hm1 := hmM 1 (by norm_num)
  have hm3 := hmM 3 (by norm_num)
  have hm4 := hmM 4 (by norm_num)
  have s1 : ε * m 2 ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hm2 hε).trans hεs
  have s2 : δ * m 1 ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hm1 hδ).trans hδs
  have e1 := abs_densityMean_sub_of_exp_tilt L₀ L₁ hf hR t₀ t₁ hε hM (hm 2) (hm 2) (hm 4) s1
  have e2 := abs_densityMean_sub_of_cutoff Lg L₀.integrable_density.aestronglyMeasurable L₀.mass hf₀
    hW₀ hW₁ hWδ tg hδ hM (hm 1) (hm 2) (hm 3) s2
  have hMM : Mm ≤ Mm ^ 2 := by nlinarith
  have b1 : M * ε * m (2 + 2) ≤ M * ε * Mm ^ 2 :=
    mul_le_mul_of_nonneg_left (hm4.trans hMM) (by positivity)
  have b2 : (M * m 2) * (ε * m 2) ≤ M * ε * Mm ^ 2 := by
    calc (M * m 2) * (ε * m 2) = M * ε * (m 2 * m 2) := by ring
      _ ≤ M * ε * (Mm * Mm) := by
          have := hm 2
          gcongr
      _ = _ := by ring
  have b3 : M * δ * m (2 + 1) ≤ M * δ * Mm ^ 2 :=
    mul_le_mul_of_nonneg_left (hm3.trans hMM) (by positivity)
  have b4 : (M * m 2) * (δ * m 1) ≤ M * δ * Mm ^ 2 := by
    calc (M * m 2) * (δ * m 1) = M * δ * (m 2 * m 1) := by ring
      _ ≤ M * δ * (Mm * Mm) := by
          have := hm 2
          have := hm 1
          gcongr
      _ = _ := by ring
  calc _ ≤ |densityMean f₁ g - densityMean f₀ g| + |densityMean f₀ g - densityMean fg g| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add e1 e2
    _ ≤ 6 * M * (ε + δ) * Mm ^ 2 := by nlinarith
private theorem covariance_comparison (L₁ : IsMomentLaw f₁ S m) (L₀ : IsMomentLaw f₀ S m)
    (Lg : IsMomentLaw fg S m)
    (hf : ∀ η, f₁ η = f₀ η * Real.exp (-R η)) (hf₀ : ∀ η, f₀ η = W η * fg η)
    (hW₀ : ∀ η, 0 ≤ W η) (hW₁ : ∀ η, W η ≤ 1) (hWδ : ∀ η, W η ≠ 1 → 1 ≤ δ * (1 + S η))
    (hR : IsPolyBounded f₀ S R 2 ε)
    (ta₀ : ∀ f : BondField ι → ℝ, IsPolyBounded f S a₀ 1 K)
    (ta₁ : ∀ f : BondField ι → ℝ, IsPolyBounded f S a₁ 1 K)
    (ta₂ : ∀ f : BondField ι → ℝ, IsPolyBounded f S a₂ 1 K)
    (tr₀ : IsPolyBounded f₁ S r₀ 2 ε) (tr₁ : IsPolyBounded f₁ S r₁ 2 ε)
    (tr₂ : IsPolyBounded f₁ S r₂ 2 ε)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hMm : 1 ≤ Mm)
    (hm : ∀ j, 0 ≤ m j) (hmM : ∀ j ≤ 4, m j ≤ Mm) (hεs : ε * Mm ≤ 1 / 4) (hδs : δ * Mm ≤ 1 / 4)
    (hsm : 7 * (1 + K) ^ 2 * (ε + δ) * Mm ^ 2 ≤ 1) :
    |(densityMean f₁ (fun η => -(a₂ η + c₂ + r₂ η) + (a₀ η + c₀ + r₀ η) * (a₁ η + c₁ + r₁ η)) -
        densityMean f₁ (fun η => a₀ η + c₀ + r₀ η) * densityMean f₁ (fun η => a₁ η + c₁ + r₁ η)) -
      (-c₂ + (densityMean fg (fun η => -a₂ η + a₀ η * a₁ η) -
        densityMean fg a₀ * densityMean fg a₁))| ≤ 37 * (1 + K) ^ 4 * Mm ^ 3 * (ε + δ) := by
  have hS := L₁.S_nonneg
  set M₂ : ℝ := (1 + K) ^ 2 with hM₂
  have hM₂1 : 1 ≤ M₂ := by
    rw [hM₂]
    nlinarith
  have hKM : K ≤ M₂ := by
    rw [hM₂]
    nlinarith
  have hKK : K * K ≤ M₂ := by
    rw [hM₂]
    nlinarith
  have hM0 : 0 ≤ M₂ := by linarith
  have T₂ : ∀ (f a : BondField ι → ℝ), (∀ f, IsPolyBounded f S a 1 K) → IsPolyBounded f S a 2 M₂ :=
    fun f a t => (t f).mono hS (by norm_num) hKM hM0
  have Tp : ∀ f : BondField ι → ℝ, IsPolyBounded f S (fun η => a₀ η * a₁ η) 2 M₂ := fun f =>
    ((ta₀ f).mul (ta₁ f) hS hK).mono hS (by norm_num) hKK hM0
  have C : ∀ {g : BondField ι → ℝ}, (∀ f : BondField ι → ℝ, IsPolyBounded f S g 2 M₂) →
      |densityMean f₁ g - densityMean fg g| ≤ 6 * M₂ * (ε + δ) * Mm ^ 2 := fun t =>
    abs_densityMean_sub_gaussian L₁ L₀ Lg hf hf₀ hW₀ hW₁ hWδ hR hε hδ hMm hm hmM hεs hδs
      (t _) (t _) (t _) hM0
  set Ec : ℝ := 6 * M₂ * (ε + δ) * Mm ^ 2 with hEc
  have d₂ := C (fun f => T₂ f a₂ ta₂)
  have d₀ := C (fun f => T₂ f a₀ ta₀)
  have d₁ := C (fun f => T₂ f a₁ ta₁)
  have d₀₁ := C Tp
  have hm2 := hmM 2 (by norm_num)
  have hm4 := hmM 4 (by norm_num)
  have y₀ := (tr₀.abs_densityMean_le L₁ hε).trans (mul_le_mul_of_nonneg_left hm2 hε)
  have y₁ := (tr₁.abs_densityMean_le L₁ hε).trans (mul_le_mul_of_nonneg_left hm2 hε)
  have y₂ := (tr₂.abs_densityMean_le L₁ hε).trans (mul_le_mul_of_nonneg_left hm2 hε)
  have hεM : ε ≤ M₂ * ε := by nlinarith
  have tz₁ : IsPolyBounded f₁ S (fun η => a₀ η * r₁ η) 4 (M₂ * ε) :=
    ((T₂ f₁ a₀ ta₀).mul tr₁ hS hM0)
  have tz₂ : IsPolyBounded f₁ S (fun η => r₀ η * a₁ η) 4 (M₂ * ε) := by
    have := tr₀.mul (T₂ f₁ a₁ ta₁) hS hε
    exact this.mono hS (by norm_num) (by nlinarith) (by positivity)
  have tz₃ : IsPolyBounded f₁ S (fun η => r₀ η * r₁ η) 4 (M₂ * ε) := by
    have := tr₀.mul tr₁ hS hε
    exact this.mono hS (by norm_num) (by nlinarith) (by positivity)
  have hMe : 0 ≤ M₂ * ε := by positivity
  have z₁ := (tz₁.abs_densityMean_le L₁ hMe).trans (mul_le_mul_of_nonneg_left hm4 hMe)
  have z₂ := (tz₂.abs_densityMean_le L₁ hMe).trans (mul_le_mul_of_nonneg_left hm4 hMe)
  have z₃ := (tz₃.abs_densityMean_le L₁ hMe).trans (mul_le_mul_of_nonneg_left hm4 hMe)
  have g₀ : |densityMean fg a₀| ≤ M₂ * Mm :=
    ((T₂ fg a₀ ta₀).abs_densityMean_le Lg hM0).trans (mul_le_mul_of_nonneg_left hm2 hM0)
  have g₁ : |densityMean fg a₁| ≤ M₂ * Mm :=
    ((T₂ fg a₁ ta₁).abs_densityMean_le Lg hM0).trans (mul_le_mul_of_nonneg_left hm2 hM0)
  have hex := covariance_expand (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) L₁ ((ta₀ f₁).integrable_mul L₁)
    ((ta₁ f₁).integrable_mul L₁) ((ta₂ f₁).integrable_mul L₁) (tr₀.integrable_mul L₁)
    (tr₁.integrable_mul L₁) (tr₂.integrable_mul L₁) ((Tp f₁).integrable_mul L₁)
    (tz₁.integrable_mul L₁) (tz₂.integrable_mul L₁) (tz₃.integrable_mul L₁)
  have mG : densityMean fg (fun η => -a₂ η + a₀ η * a₁ η) =
      -densityMean fg a₂ + densityMean fg (fun η => a₀ η * a₁ η) := by
    have e : (fun η => -a₂ η + a₀ η * a₁ η) = fun η => (-1) * a₂ η + a₀ η * a₁ η := by
      funext η
      ring
    rw [e, densityMean_add_of_integrable (integrable_const_mul_mul _ ((ta₂ fg).integrable_mul Lg))
      ((Tp fg).integrable_mul Lg), densityMean_const_mul]
    ring
  have hP : 37 * (1 + K) ^ 4 * Mm ^ 3 * (ε + δ) = 37 * M₂ ^ 2 * Mm ^ 3 * (ε + δ) := by
    rw [hM₂]
    ring
  rw [hex, mG, hP]
  have hnum := error_arithmetic hM₂1 hMm hε hδ hsm d₂ d₀ d₁ d₀₁ y₀ y₁ y₂ z₁ z₂ z₃ g₀ g₁
  have e : ∀ X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Z₁ Z₂ Z₃ G₀ G₁ G₂ G₃ : ℝ,
      -X₂ - Y₂ - c₂ + (X₃ + Z₁ + Z₂ + Z₃) - (X₀ + Y₀) * (X₁ + Y₁) -
        (-c₂ + (-G₂ + G₃ - G₀ * G₁)) =
      -(X₂ - G₂) - Y₂ + (X₃ - G₃) + (Z₁ + Z₂ + Z₃) - ((X₀ + Y₀) * (X₁ + Y₁) - G₀ * G₁) := by
    intros
    ring
  rw [e]
  exact hnum
end Means
section Laws
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem integrable_gaussian_sqNorm {c : ℝ} (hc : 0 < c) :
    Integrable fun η : BondField ι => Real.exp (-(c * sqNorm η)) := by apply _root_.YangMills.DeltaSharedProofs.p502286 <;> assumption
private def contractionRatio (N : ℕ) : ℝ := (N : ℝ) / (N + 1)
private theorem contractionRatio_pos {N : ℕ} (hN : 1 ≤ N) : 0 < contractionRatio N := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  unfold contractionRatio
  positivity
private theorem contractionRatio_le_one (N : ℕ) : contractionRatio N ≤ 1 := by
  unfold contractionRatio
  rw [div_le_one (by positivity)]
  linarith
private theorem inv_contractionRatio_pow_le {N : ℕ} (hN : 1 ≤ N) :
    (contractionRatio N ^ N)⁻¹ ≤ Real.exp 1 := by
  have e : (contractionRatio N ^ N)⁻¹ = (1 + 1 / (N : ℝ)) ^ N := by
    unfold contractionRatio
    rw [← inv_pow]
    congr 1
    field_simp
  rw [e]
  have h1 : 1 + 1 / (N : ℝ) ≤ Real.exp (1 / (N : ℝ)) := by
    have := Real.add_one_le_exp (1 / (N : ℝ))
    linarith
  calc (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp (1 / (N : ℝ)) ^ N := pow_le_pow_left₀ (by positivity) h1 N
    _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
private def gainRate (lam : ℝ) (N : ℕ) : ℝ := (1 - contractionRatio N) * (lam / 8)
private def gainLoss (lam : ℝ) (N : ℕ) : ℝ := (1 - contractionRatio N) * (2 / lam)
private def momentBound (lam : ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * ((gainRate lam N)⁻¹) ^ k * Real.exp (gainRate lam N + gainLoss lam N + 1)
private theorem one_sub_contractionRatio {N : ℕ} : 1 - contractionRatio N = 1 / ((N : ℝ) + 1) := by
  unfold contractionRatio
  field_simp
  ring
private theorem gainRate_pos {lam : ℝ} (hlam : 0 < lam) (N : ℕ) : 0 < gainRate lam N := by
  unfold gainRate
  rw [one_sub_contractionRatio]
  positivity
variable {ρ lam K x : ℝ} {Q B : ParamBondField ι → ℝ} {p : ℝ → ℝ}
private def gaussianExponent (x : ℝ) (Q : ParamBondField ι → ℝ) (η : BondField ι) : ℝ :=
  1 / 2 * quadraticForm (scaledHessian x Q 0) η
private def shiftedExponent (x : ℝ) (Q B : ParamBondField ι → ℝ) (η : BondField ι) : ℝ :=
  linearExponent x Q B (liftField η) - B 0
private theorem continuous_gaussianExponent :
    Continuous (gaussianExponent x Q : BondField ι → ℝ) :=
  (continuous_quadraticForm _).const_mul _ |>.congr fun _ => rfl
private theorem gaussianExponent_smul (s : ℝ) (η : BondField ι) :
    gaussianExponent x Q (s • η) = s ^ 2 * gaussianExponent x Q η := by
  unfold gaussianExponent
  rw [quadraticForm_smul]
  ring
private theorem gaussianExponent_lower (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hx : 0 ≤ x) (η : BondField ι) : x * lam * sqNorm η / 2 ≤ gaussianExponent x Q η := by
  have := quadraticForm_lower (x := x) hρ LF hx η
  unfold gaussianExponent
  linarith
private theorem gaussianExponent_radial_gain (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hlam : 0 < lam) (hx : 0 ≤ x) (η : BondField ι) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 - s) * (lam * (x * sqNorm η) / 8 - 2 / lam) ≤
      gaussianExponent x Q η - gaussianExponent x Q (s • η) := by
  rw [gaussianExponent_smul]
  have h1 := gaussianExponent_lower hρ LF hx η
  have hq := sqNorm_nonneg η
  have hA : 0 ≤ x * lam * sqNorm η := by positivity
  have h1s : 0 ≤ 1 - s := by linarith [hs.2]
  have h2 : (0 : ℝ) ≤ 2 / lam := by positivity
  have h3 : lam * (x * sqNorm η) / 8 - 2 / lam ≤ gaussianExponent x Q η := by
    have e : lam * (x * sqNorm η) = x * lam * sqNorm η := by ring
    rw [e]
    linarith
  have hg0 : 0 ≤ gaussianExponent x Q η := by linarith
  calc _ ≤ (1 - s) * gaussianExponent x Q η := mul_le_mul_of_nonneg_left h3 h1s
    _ ≤ (1 - s) * gaussianExponent x Q η + s * (1 - s) * gaussianExponent x Q η := by
        have : 0 ≤ s * (1 - s) * gaussianExponent x Q η := mul_nonneg (mul_nonneg hs.1 h1s) hg0
        linarith
    _ = _ := by ring
private theorem continuousOn_shiftedExponent (LF : IsAdmissibleExponentFamily ρ lam K Q B) :
    ContinuousOn (shiftedExponent x Q B) (closedBalls ρ : Set (BondField ι)) := by
  intro η hη
  have hc : ContinuousAt (linearExponent x Q B) (liftField η) :=
    ((contDiffAt_const.mul (contDiffAt_Q (n := 1) LF hη (by norm_num))).add
      (contDiffAt_B (n := 1) LF hη (by norm_num))).continuousAt
  have hz : ContinuousAt (liftField : BondField ι → ParamBondField ι) η := by
    unfold liftField
    fun_prop
  have := ContinuousAt.comp (g := linearExponent x Q B) (f := liftField) hc hz
  exact (this.sub continuousAt_const).continuousWithinAt
private def exponentDensity (ρ x : ℝ) (p : ℝ → ℝ) (Q B : ParamBondField ι → ℝ) (η : BondField ι) : ℝ :=
  radialWeightProd (cutoffFactor ρ p) η * Real.exp (-shiftedExponent x Q B η)
private def cutoffGaussianDensity (ρ x : ℝ) (p : ℝ → ℝ) (Q : ParamBondField ι → ℝ)
    (η : BondField ι) : ℝ :=
  radialWeightProd (cutoffFactor ρ p) η * Real.exp (-gaussianExponent x Q η)
private def gaussianDensity (x : ℝ) (Q : ParamBondField ι → ℝ) (η : BondField ι) : ℝ :=
  Real.exp (-gaussianExponent x Q η)
private theorem momentLaw_exponentDensity (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (LF : IsAdmissibleExponentFamily ρ lam K Q B) (hlam : 0 < lam)
    (hK : 0 ≤ K) (hKx : K ^ 2 ≤ x) (hKl : K ≤ x * lam / 2) (hx : 0 < x)
    {N : ℕ} (hN : 1 ≤ N) (hNf : N = Module.finrank ℝ (BondField ι)) :
    IsMomentLaw (exponentDensity ρ x p Q B) (fun η => x * sqNorm η) (momentBound lam N) := by
  subst hNf
  refine momentLaw_weighted_exp hρ hp (continuousOn_shiftedExponent LF)
    (fun η => mul_nonneg hx.le (sqNorm_nonneg η))
    (continuous_const.mul continuous_sqNorm) (gainRate_pos hlam _) (contractionRatio_pos hN)
    (contractionRatio_le_one _) (inv_contractionRatio_pow_le hN) fun η hη => ?_
  have h := linearExponent_radial_gain (x := x) hρ LF hlam hK hKx hKl hx.le hη
    (s := contractionRatio (Module.finrank ℝ (BondField ι)))
    ⟨(contractionRatio_pos hN).le, contractionRatio_le_one _⟩
  unfold shiftedExponent
  unfold gainRate gainLoss
  linarith
private theorem momentLaw_cutoffGaussianDensity (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (LF : IsAdmissibleExponentFamily ρ lam K Q B) (hlam : 0 < lam)
    (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) (hNf : N = Module.finrank ℝ (BondField ι)) :
    IsMomentLaw (cutoffGaussianDensity ρ x p Q) (fun η => x * sqNorm η) (momentBound lam N) := by
  subst hNf
  refine momentLaw_weighted_exp hρ hp continuous_gaussianExponent.continuousOn
    (fun η => mul_nonneg hx.le (sqNorm_nonneg η))
    (continuous_const.mul continuous_sqNorm) (gainRate_pos hlam _) (contractionRatio_pos hN)
    (contractionRatio_le_one _) (inv_contractionRatio_pow_le hN) fun η _ => ?_
  have h := gaussianExponent_radial_gain (x := x) hρ LF hlam hx.le η
    (s := contractionRatio (Module.finrank ℝ (BondField ι)))
    ⟨(contractionRatio_pos hN).le, contractionRatio_le_one _⟩
  unfold gainRate gainLoss
  linarith
private theorem momentLaw_gaussianDensity (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hlam : 0 < lam) (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) (hNf : N = Module.finrank ℝ (BondField ι)) :
    IsMomentLaw (gaussianDensity x Q) (fun η => x * sqNorm η) (momentBound lam N) := by
  subst hNf
  have hc : 0 < x * lam / 2 := by positivity
  have hi : Integrable (gaussianDensity x Q : BondField ι → ℝ) := by
    refine (integrable_gaussian_sqNorm hc).mono' ?_ (ae_of_all _ fun η => ?_)
    · exact (Real.continuous_exp.comp continuous_gaussianExponent.neg).aestronglyMeasurable
    · show ‖Real.exp (-gaussianExponent x Q η)‖ ≤ _
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_exp.2 ?_
      have := gaussianExponent_lower hρ LF hx.le η
      have e : x * lam / 2 * sqNorm η = x * lam * sqNorm η / 2 := by ring
      rw [e]
      linarith
  have hm : 0 < ∫ η, gaussianDensity x Q η := by
    have hnn : 0 ≤ (gaussianDensity x Q : BondField ι → ℝ) := fun η => (Real.exp_pos _).le
    rw [integral_pos_iff_support_of_nonneg hnn hi]
    have : Function.support (gaussianDensity x Q : BondField ι → ℝ) = Set.univ :=
      Set.eq_univ_of_forall fun η => (Real.exp_pos _).ne'
    rw [this]
    exact isOpen_univ.measure_pos volume Set.univ_nonempty
  refine momentLaw_of_radial_growth (fun η => (Real.exp_pos _).le) hi hm
    (fun η => mul_nonneg hx.le (sqNorm_nonneg η))
    (continuous_const.mul continuous_sqNorm) (gainRate_pos hlam _) (contractionRatio_pos hN)
    (inv_contractionRatio_pow_le hN) fun η => ?_
  have h := gaussianExponent_radial_gain (x := x) hρ LF hlam hx.le η
    (s := contractionRatio (Module.finrank ℝ (BondField ι)))
    ⟨(contractionRatio_pos hN).le, contractionRatio_le_one _⟩
  unfold gaussianDensity
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  unfold gainRate gainLoss
  linarith
private theorem cubic_remainder_bound {y x e sq K : ℝ} (hy : 0 < y) (hyx : y ^ 2 * x = 1) (hx : 0 < x)
    (he : 0 ≤ e) (hes : e ^ 2 ≤ sq) (hK : 0 ≤ K) :
    x * (K * e ^ 3 / 6) + K * e ≤ 2 * K * y * (1 + x * sq) ^ 2 ∧ x * e ^ 2 ≤ 1 + x * sq := by
  have hsq : 0 ≤ sq := (by positivity : 0 ≤ e ^ 2).trans hes
  set S : ℝ := x * sq with hS
  have hS0 : 0 ≤ S := by positivity
  have h1 : x * e ^ 2 ≤ S := mul_le_mul_of_nonneg_left hes hx.le
  have h1' : x * e ^ 2 ≤ 1 + S := by linarith
  have hSS : S ≤ (1 + S) ^ 2 := by nlinarith
  have h2 : e ^ 2 ≤ (y * (1 + S)) ^ 2 := by
    calc e ^ 2 = y ^ 2 * (x * e ^ 2) := by
          have : y ^ 2 * (x * e ^ 2) = (y ^ 2 * x) * e ^ 2 := by ring
          rw [this, hyx, one_mul]
      _ ≤ y ^ 2 * (1 + S) ^ 2 := by
          have : x * e ^ 2 ≤ (1 + S) ^ 2 := h1.trans hSS
          gcongr
      _ = _ := by ring
  have h3 : e ≤ y * (1 + S) :=
    (pow_le_pow_iff_left₀ he (by positivity) two_ne_zero).1 h2
  have h4 : x * e ^ 3 ≤ y * (1 + S) ^ 2 := by
    calc x * e ^ 3 = (x * e ^ 2) * e := by ring
      _ ≤ (1 + S) * (y * (1 + S)) := mul_le_mul h1' h3 he (by positivity)
      _ = _ := by ring
  refine ⟨?_, h1'⟩
  have h5 : 1 + S ≤ (1 + S) ^ 2 := by nlinarith
  have h6 : K * e ≤ K * y * (1 + S) ^ 2 := by
    calc K * e ≤ K * (y * (1 + S)) := mul_le_mul_of_nonneg_left h3 hK
      _ = K * y * (1 + S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)
  have h7 : x * (K * e ^ 3 / 6) ≤ K * y * (1 + S) ^ 2 / 6 := by
    have := mul_le_mul_of_nonneg_left h4 hK
    nlinarith
  have h8 : 0 ≤ K * y * (1 + S) ^ 2 := by positivity
  linarith
private theorem polyBounded_partial_form (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hK : 0 ≤ K) (hx : 0 < x) (l : Fin 2) (f : BondField ι → ℝ) :
    IsPolyBounded f (fun η => x * sqNorm η)
      (fun η => 1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) l) η) 1 K := by
  refine ⟨((continuous_quadraticForm _).const_mul _ |>.congr fun _ => rfl).aestronglyMeasurable,
    fun η _ => ?_⟩
  rw [quadraticForm_partial hρ LF]
  have h := abs_iteratedFDeriv_apply_le
    (LF.deriv_bound_Q 0 (mem_ball_zero hρ) 3 (by norm_num) (by norm_num))
    (Fin.cons (paramUnit l) (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)))
  have e : (∏ i, ‖(Fin.cons (paramUnit l) (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) :
      Fin 3 → ParamBondField ι) i‖) = ‖η‖ ^ 2 := by
    simp [Fin.prod_univ_succ, norm_liftField, norm_paramUnit, sq]
  rw [e] at h
  have h' : |iteratedFDeriv ℝ 3 Q 0 (Fin.cons (paramUnit l)
      (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)))| ≤ K * ‖η‖ ^ 2 := h
  have hq := norm_sq_le_sqNorm η
  have hs := sqNorm_nonneg η
  rw [abs_mul, abs_mul, abs_of_pos hx, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), pow_one]
  have hxq : x * ‖η‖ ^ 2 ≤ x * sqNorm η := mul_le_mul_of_nonneg_left hq hx.le
  have h2 : 0 ≤ x * sqNorm η := by positivity
  calc 1 / 2 * (x * |iteratedFDeriv ℝ 3 Q 0 _|) ≤ 1 / 2 * (x * (K * ‖η‖ ^ 2)) := by gcongr
    _ = 1 / 2 * K * (x * ‖η‖ ^ 2) := by ring
    _ ≤ 1 / 2 * K * (x * sqNorm η) := by gcongr
    _ ≤ _ := by nlinarith
private theorem polyBounded_mixed_form (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hK : 0 ≤ K) (hx : 0 < x) (f : BondField ι → ℝ) :
    IsPolyBounded f (fun η => x * sqNorm η)
      (fun η => 1 / 2 * quadraticForm (familyMixedDeriv (scaledHessian x Q)) η) 1 K := by
  refine ⟨((continuous_quadraticForm _).const_mul _ |>.congr fun _ => rfl).aestronglyMeasurable,
    fun η _ => ?_⟩
  rw [quadraticForm_mixed hρ LF]
  have h := abs_iteratedFDeriv_apply_le
    (LF.deriv_bound_Q 0 (mem_ball_zero hρ) 4 (by norm_num) (by norm_num))
    (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) (Fin.cons (liftField η)
      (Fin.cons (liftField η) noVec))))
  have e : (∏ i, ‖(Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) (Fin.cons (liftField η)
      (Fin.cons (liftField η) noVec))) : Fin 4 → ParamBondField ι) i‖) = ‖η‖ ^ 2 := by
    simp [Fin.prod_univ_succ, norm_liftField, norm_paramUnit, sq]
  rw [e] at h
  have h' : |iteratedFDeriv ℝ 4 Q 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1)
      (Fin.cons (liftField η) (Fin.cons (liftField η) noVec))))| ≤ K * ‖η‖ ^ 2 := h
  have hq := norm_sq_le_sqNorm η
  have hs := sqNorm_nonneg η
  rw [abs_mul, abs_mul, abs_of_pos hx, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), pow_one]
  have hxq : x * ‖η‖ ^ 2 ≤ x * sqNorm η := mul_le_mul_of_nonneg_left hq hx.le
  have h2 : 0 ≤ x * sqNorm η := by positivity
  calc 1 / 2 * (x * |iteratedFDeriv ℝ 4 Q 0 _|) ≤ 1 / 2 * (x * (K * ‖η‖ ^ 2)) := by gcongr
    _ = 1 / 2 * K * (x * ‖η‖ ^ 2) := by ring
    _ ≤ 1 / 2 * K * (x * sqNorm η) := by gcongr
    _ ≤ _ := by nlinarith
private theorem continuousOn_iteratedFDeriv_lift {A : ParamBondField ι → ℝ} {n : ℕ}
    (hA : ∀ η ∈ (closedBalls ρ : Set (BondField ι)),
      ContDiffAt ℝ ((n + 0 : ℕ) : WithTop ℕ∞) A (liftField η))
    (w : Fin n → ParamBondField ι) :
    ContinuousOn (fun η => iteratedFDeriv ℝ n A (liftField η) w) (closedBalls ρ : Set (BondField ι)) := by
  intro η hη
  have hc : ContinuousAt (fun z => iteratedFDeriv ℝ n A z w) (liftField η) :=
    (contDiffAt_iteratedFDeriv_apply (k := 0) (hA η hη) w).continuousAt
  have hz : ContinuousAt (liftField : BondField ι → ParamBondField ι) η := by
    unfold liftField
    fun_prop
  exact (ContinuousAt.comp (g := fun z => iteratedFDeriv ℝ n A z w) (f := liftField) hc hz).continuousWithinAt
private theorem parameterSlope_eq (l : Fin 2) (A : ParamBondField ι → ℝ) (η : BondField ι) :
    parameterSlope A l η = iteratedFDeriv ℝ 1 A (liftField η) (Fin.cons (paramUnit l) noVec) := by
  rw [iteratedFDeriv_one_apply]
  rfl
private theorem parameterMixedDeriv_eq (A : ParamBondField ι → ℝ) (η : BondField ι) :
    parameterMixedDeriv A η =
      iteratedFDeriv ℝ 2 A (liftField η) (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) := by
  unfold parameterMixedDeriv
  congr 1
  funext i
  fin_cases i <;> rfl
private def exponentRemainder (ρ x : ℝ) (Q B : ParamBondField ι → ℝ) : BondField ι → ℝ :=
  (closedBalls ρ).indicator fun η => shiftedExponent x Q B η - gaussianExponent x Q η
private def slopeRemainder (ρ x : ℝ) (Q B : ParamBondField ι → ℝ) (l : Fin 2) : BondField ι → ℝ :=
  (closedBalls ρ).indicator fun η => parameterSlope (linearExponent x Q B) l η -
    1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) l) η -
    iteratedFDeriv ℝ 1 B 0 (Fin.cons (paramUnit l) noVec)
private def mixedRemainder (ρ x : ℝ) (Q B : ParamBondField ι → ℝ) : BondField ι → ℝ :=
  (closedBalls ρ).indicator fun η => parameterMixedDeriv (linearExponent x Q B) η -
    1 / 2 * quadraticForm (familyMixedDeriv (scaledHessian x Q)) η -
    iteratedFDeriv ℝ 2 B 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec))
private theorem polyBounded_indicator {g h : BondField ι → ℝ} {S : BondField ι → ℝ} {ε : ℝ}
    (f : BondField ι → ℝ) (hε : 0 ≤ ε) (hS : ∀ η, 0 ≤ S η)
    (hg : g = (closedBalls ρ).indicator h) (hc : ContinuousOn h (closedBalls ρ))
    (hb : ∀ η ∈ (closedBalls ρ : Set (BondField ι)), |h η| ≤ ε * (1 + S η) ^ 2) :
    IsPolyBounded f S g 2 ε := by
  subst hg
  refine ⟨aestronglyMeasurable_indicator_closedBalls hc, fun η _ => ?_⟩
  by_cases hη : η ∈ (closedBalls ρ : Set (BondField ι))
  · rw [Set.indicator_of_mem hη]
    exact hb η hη
  · rw [Set.indicator_of_notMem hη, abs_zero]
    have := hS η
    positivity
private theorem polyBounded_exponentRemainder (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hK : 0 ≤ K) (hx : 0 < x) {y : ℝ} (hy : 0 < y) (hyx : y ^ 2 * x = 1) (f : BondField ι → ℝ) :
    IsPolyBounded f (fun η => x * sqNorm η) (exponentRemainder ρ x Q B) 2 (2 * K * y) := by
  refine polyBounded_indicator f (by positivity) (fun η => mul_nonneg hx.le (sqNorm_nonneg η)) rfl
    ((continuousOn_shiftedExponent LF).sub continuous_gaussianExponent.continuousOn) fun η hη => ?_
  have h1 := taylor_Q_value hρ LF hη
  have h2 := lipschitz_B_value hρ LF hη
  have hs := (cubic_remainder_bound hy hyx hx (norm_nonneg η) (norm_sq_le_sqNorm η) hK).1
  refine le_trans ?_ hs
  have e : shiftedExponent x Q B η - gaussianExponent x Q η =
      x * (Q (liftField η) -
        iteratedFDeriv ℝ 2 Q 0 (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) / 2) +
        (B (liftField η) - B 0) := by
    unfold shiftedExponent gaussianExponent linearExponent
    rw [quadraticForm_scaledHessian_zero hρ LF]
    ring
  rw [e]
  calc _ ≤ |x * (Q (liftField η) -
        iteratedFDeriv ℝ 2 Q 0 (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)) / 2)| +
        |B (liftField η) - B 0| := abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_pos hx]
        gcongr
private theorem polyBounded_slopeRemainder (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hK : 0 ≤ K) (hx : 0 < x) {y : ℝ} (hy : 0 < y) (hyx : y ^ 2 * x = 1) (l : Fin 2)
    (f : BondField ι → ℝ) :
    IsPolyBounded f (fun η => x * sqNorm η) (slopeRemainder ρ x Q B l) 2 (2 * K * y) := by
  have hc : ContinuousOn (fun η => parameterSlope (linearExponent x Q B) l η)
      (closedBalls ρ : Set (BondField ι)) := by
    have := continuousOn_iteratedFDeriv_lift (ρ := ρ) (A := linearExponent x Q B) (n := 1)
      (fun η hη => (contDiffAt_const.mul (contDiffAt_Q LF hη (by norm_num))).add
        (contDiffAt_B LF hη (by norm_num)))
      (Fin.cons (paramUnit l) noVec)
    exact this.congr fun η _ => parameterSlope_eq l _ η
  refine polyBounded_indicator f (by positivity) (fun η => mul_nonneg hx.le (sqNorm_nonneg η)) rfl
    ((hc.sub ((continuous_quadraticForm _).const_mul _).continuousOn).sub continuousOn_const)
    fun η hη => ?_
  have h1 := taylor_Q_slope hρ LF hη l
  have h2 := lipschitz_B_slope LF hη l
  have hs := (cubic_remainder_bound hy hyx hx (norm_nonneg η) (norm_sq_le_sqNorm η) hK).1
  refine le_trans ?_ hs
  have e : parameterSlope (linearExponent x Q B) l η -
      1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) l) η -
      iteratedFDeriv ℝ 1 B 0 (Fin.cons (paramUnit l) noVec) =
      x * (iteratedFDeriv ℝ 1 Q (liftField η) (Fin.cons (paramUnit l) noVec) -
        iteratedFDeriv ℝ 3 Q 0 (Fin.cons (paramUnit l)
          (Fin.cons (liftField η) (Fin.cons (liftField η) noVec))) / 2) +
        (iteratedFDeriv ℝ 1 B (liftField η) (Fin.cons (paramUnit l) noVec) -
          iteratedFDeriv ℝ 1 B 0 (Fin.cons (paramUnit l) noVec)) := by
    rw [parameterSlope_eq, iteratedFDeriv_linearExponent (contDiffAt_Q LF hη (by norm_num))
      (contDiffAt_B LF hη (by norm_num)), quadraticForm_partial hρ LF]
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos hx]
  gcongr
private theorem polyBounded_mixedRemainder (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B)
    (hK : 0 ≤ K) (hx : 0 < x) {y : ℝ} (hy : 0 < y) (hyx : y ^ 2 * x = 1) (f : BondField ι → ℝ) :
    IsPolyBounded f (fun η => x * sqNorm η) (mixedRemainder ρ x Q B) 2 (2 * K * y) := by
  have hc : ContinuousOn (fun η => parameterMixedDeriv (linearExponent x Q B) η)
      (closedBalls ρ : Set (BondField ι)) := by
    have := continuousOn_iteratedFDeriv_lift (ρ := ρ) (A := linearExponent x Q B) (n := 2)
      (fun η hη => (contDiffAt_const.mul (contDiffAt_Q LF hη (by norm_num))).add
        (contDiffAt_B LF hη (by norm_num)))
      (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec))
    exact this.congr fun η _ => parameterMixedDeriv_eq _ η
  refine polyBounded_indicator f (by positivity) (fun η => mul_nonneg hx.le (sqNorm_nonneg η)) rfl
    ((hc.sub ((continuous_quadraticForm _).const_mul _).continuousOn).sub continuousOn_const)
    fun η hη => ?_
  have h1 := taylor_Q_mixed hρ LF hη
  have h2 := lipschitz_B_mixed LF hη
  have hs := (cubic_remainder_bound hy hyx hx (norm_nonneg η) (norm_sq_le_sqNorm η) hK).1
  refine le_trans ?_ hs
  have e : parameterMixedDeriv (linearExponent x Q B) η -
      1 / 2 * quadraticForm (familyMixedDeriv (scaledHessian x Q)) η -
      iteratedFDeriv ℝ 2 B 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) =
      x * (iteratedFDeriv ℝ 2 Q (liftField η) (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) -
        iteratedFDeriv ℝ 4 Q 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1)
          (Fin.cons (liftField η) (Fin.cons (liftField η) noVec)))) / 2) +
        (iteratedFDeriv ℝ 2 B (liftField η) (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) -
          iteratedFDeriv ℝ 2 B 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec))) := by
    rw [parameterMixedDeriv_eq, iteratedFDeriv_linearExponent (contDiffAt_Q LF hη (by norm_num))
      (contDiffAt_B LF hη (by norm_num)), quadraticForm_mixed hρ LF]
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos hx]
  gcongr
private theorem det_ne_zero_of_form_lower {c : ℝ} (hc : 0 < c) (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    (hf : ∀ η : BondField ι, c * sqNorm η ≤ quadraticForm M η) : M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set η : BondField ι := fun b => WithLp.toLp 2 fun c => v (b, c) with hη
  have hcoord : ∀ i : ι × Fin 3, η i.1 i.2 = v i := fun i => rfl
  have hform : quadraticForm M η = 0 := by
    unfold quadraticForm
    have e : ∀ i, ∑ j, M i j * (η i.1 i.2 * η j.1 j.2) = v i * (M.mulVec v) i := by
      intro i
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcoord, hcoord]
      ring
    simp_rw [e, hMv]
    simp
  have hsq : sqNorm η = ∑ i, v i ^ 2 := by
    unfold sqNorm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [EuclideanSpace.real_norm_sq_eq]
  have h1 := hf η
  rw [hform, hsq] at h1
  have h2 : ∑ i, v i ^ 2 ≤ 0 := by
    by_contra hn
    rw [not_le] at hn
    have := mul_pos hc hn
    linarith
  apply hv
  funext i
  have h3 : v i ^ 2 ≤ ∑ i, v i ^ 2 :=
    Finset.single_le_sum (f := fun i => v i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h4 : v i ^ 2 ≤ 0 := h3.trans h2
  have h5 : v i ^ 2 = 0 := le_antisymm h4 (sq_nonneg _)
  simpa using h5
private theorem iteratedFDeriv_two_affine_comb {f h : (Fin 2 → ℝ) → ℝ} {u v κ : ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hh : ContDiffAt ℝ 2 h 0) (w : Fin 2 → Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 (fun τ => u * f τ + v * h τ + κ) 0 w =
      u * iteratedFDeriv ℝ 2 f 0 w + v * iteratedFDeriv ℝ 2 h 0 w := by
  have e : (fun τ => u * f τ + v * h τ + κ) = (u • f + v • h) + fun _ => κ := by
    funext τ
    simp
  have cf : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) f 0 := by exact_mod_cast hf
  have ch : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) h 0 := by exact_mod_cast hh
  have cu : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (u • f) 0 := contDiffAt_const.smul cf
  have cv : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (v • h) 0 := contDiffAt_const.smul ch
  have cuv : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (u • f + v • h) 0 := cu.add cv
  rw [e, iteratedFDeriv_add_apply cuv contDiffAt_const, iteratedFDeriv_add_apply cu cv,
    iteratedFDeriv_const_smul_apply cf, iteratedFDeriv_const_smul_apply ch,
    iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0)]
  simp
private theorem gaussianLogValue_second_deriv (hC2 : GaussianMeans.LogDetMixedDerivGaussian)
    (hρ : 0 < ρ) (LF : IsAdmissibleExponentFamily ρ lam K Q B) (hlam : 0 < lam) (hx : 0 < x) :
    ContDiffAt ℝ 2 (gaussianLogValue Q B) 0 ∧
      iteratedFDeriv ℝ 2 (gaussianLogValue Q B) 0 (fun l => Pi.single l 1) =
        -iteratedFDeriv ℝ 2 B 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) +
          (densityMean (gaussianDensity x Q) (fun η =>
              -(1 / 2 * quadraticForm (familyMixedDeriv (scaledHessian x Q)) η) +
                1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) 0) η *
                  (1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) 1) η)) -
            densityMean (gaussianDensity x Q)
                (fun η => 1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) 0) η) *
              densityMean (gaussianDensity x Q)
                (fun η => 1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) 1) η)) := by
  have hfl : ∀ η : BondField ι, x * lam * sqNorm η ≤ quadraticForm (scaledHessian x Q 0) η :=
    quadraticForm_lower hρ LF hx.le
  obtain ⟨hL, hform⟩ := hC2 ι (x * lam) (scaledHessian x Q) (by positivity)
    (fun i j => contDiffAt_scaledHessian hρ LF i j) (scaledHessian_isSymm hρ LF) hfl
  have hB2 : ContDiffAt ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) B (liftField 0) :=
    contDiffAt_B LF (mem_ball_zero hρ) (by norm_num)
  have hb : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun τ : Fin 2 → ℝ => B (τ, 0)) 0 := by
    have h2 : ContDiffAt ℝ (2 : WithTop ℕ∞) B
        ((fun τ : Fin 2 → ℝ => ((τ, 0) : ParamBondField ι)) 0) := by
      exact_mod_cast hB2
    exact h2.comp (0 : Fin 2 → ℝ) (by fun_prop)
  have hdet0 : (scaledHessian x Q 0).det ≠ 0 := det_ne_zero_of_form_lower (by positivity) _ hfl
  have hcont : ContinuousAt (fun τ => (scaledHessian x Q τ).det) 0 := by
    have hm : ContinuousAt (fun τ => scaledHessian x Q τ) 0 :=
      continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
        (contDiffAt_scaledHessian hρ LF i j).continuousAt
    exact (continuous_id.matrix_det).continuousAt.comp hm
  set κ : ℝ := 1 / 2 * ((Fintype.card (ι × Fin 3) : ℝ) * Real.log x) with hκ
  have hEq : gaussianLogValue Q B =ᶠ[𝓝 0] fun τ => (-1) * B (τ, 0) +
      (-(1 / 2)) * Real.log (scaledHessian x Q τ).det + κ := by
    filter_upwards [hcont.eventually_ne hdet0] with τ hτ
    have e : (scaledHessian x Q τ).det = x ^ Fintype.card (ι × Fin 3) * (familyHessian Q τ).det :=
      Matrix.det_smul _ _
    have hd : (familyHessian Q τ).det ≠ 0 := by
      intro h
      rw [e, h, mul_zero] at hτ
      exact hτ rfl
    rw [e, Real.log_mul (by positivity) hd, Real.log_pow]
    unfold gaussianLogValue
    rw [hκ]
    ring
  have hlin : ContDiffAt ℝ 2 (fun τ => (-1) * B (τ, 0) +
      (-(1 / 2)) * Real.log (scaledHessian x Q τ).det + κ) 0 :=
    ((contDiffAt_const.mul hb).add (contDiffAt_const.mul hL)).add contDiffAt_const
  refine ⟨hlin.congr_of_eventuallyEq hEq, ?_⟩
  have e1 := (hEq.iteratedFDeriv ℝ 2).eq_of_nhds
  rw [e1]
  rw [show iteratedFDeriv ℝ 2 (fun τ => (-1) * B (τ, 0) +
      (-(1 / 2)) * Real.log (scaledHessian x Q τ).det + κ) 0
      (fun l => Pi.single l 1) = _ from iteratedFDeriv_two_affine_comb hb hL _,
    second_deriv_param_at_zero hB2]
  rw [hform, liftField_zero]
  have hz : ∀ a b : ℝ, (-1) * a + b = -a + b := fun a b => by ring
  rw [hz]
  rfl
private theorem second_deriv_comparison (hC2 : GaussianMeans.LogDetMixedDerivGaussian)
    (hC1 : LaplaceAsymptotics.logCutoffIntegralSecondDeriv)
    (hCu : LaplaceAsymptotics.LogCutoffIntegralContDiffTwo)
    {N : ℕ} (hN : 1 ≤ N) (hNf : N = Module.finrank ℝ (BondField ι))
    {y Mm : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) (hp : IsCutoff ρ p) (hK : 0 ≤ K) (hx : 0 < x)
    (LF : IsAdmissibleExponentFamily ρ lam K Q B) (hy : 0 < y) (hyx : y ^ 2 * x = 1) (hKx : K ^ 2 ≤ x)
    (hKl : K ≤ x * lam / 2) (hMm : 1 ≤ Mm) (hmM : ∀ j ≤ 4, momentBound lam N j ≤ Mm)
    (hεs : 2 * K * y * Mm ≤ 1 / 4) (hδs : 4 / (ρ ^ 2 * x) * Mm ≤ 1 / 4)
    (hsm : 7 * (1 + K) ^ 2 * (2 * K * y + 4 / (ρ ^ 2 * x)) * Mm ^ 2 ≤ 1) :
    ContDiffAt ℝ 2 (logCutoffIntegral ρ p x Q B) 0 ∧ ContDiffAt ℝ 2 (gaussianLogValue Q B) 0 ∧
      |iteratedFDeriv ℝ 2 (logCutoffIntegral ρ p x Q B) 0 (fun l => Pi.single l 1) -
        iteratedFDeriv ℝ 2 (gaussianLogValue Q B) 0 (fun l => Pi.single l 1)| ≤
      37 * (1 + K) ^ 4 * Mm ^ 3 * (2 * K * y + 4 / (ρ ^ 2 * x)) := by
  have hQ3 : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 Q (0, η) := fun η hη => by
    exact_mod_cast contDiffAt_Q (n := 3) LF hη (by norm_num)
  have hB3 := LF.contDiff_B
  have hcut := hCu ι 2 ρ x p Q B hρ hp hQ3 hB3
  obtain ⟨hgc, hgs⟩ := gaussianLogValue_second_deriv hC2 hρ LF hlam hx
  refine ⟨hcut, hgc, ?_⟩
  have hform := hC1 ι ρ x p Q B hρ hp hQ3 hB3
  rw [hform, hgs]
  have L₁ := momentLaw_exponentDensity hρ hp LF hlam hK hKx hKl hx hN hNf
  have L₀ := momentLaw_cutoffGaussianDensity hρ hp LF hlam hx hN hNf
  have Lg := momentLaw_gaussianDensity hρ LF hlam hx hN hNf
  have hS : ∀ η : BondField ι, 0 ≤ x * sqNorm η := fun η => mul_nonneg hx.le (sqNorm_nonneg η)
  have hD : (exponentDensity ρ x p Q B : BondField ι → ℝ) =
      fun η => Real.exp (B 0) * rimWeightedDensity ρ p x Q B η := by
    funext η
    unfold exponentDensity rimWeightedDensity shiftedExponent linearExponent liftField
    have e : -(x * Q (0, η) + B (0, η) - B 0) = B 0 + -(x * Q (0, η) + B (0, η)) := by ring
    rw [e, Real.exp_add]
    ring
  have msw : ∀ g : BondField ι → ℝ,
      densityMean (rimWeightedDensity ρ p x Q B) g = densityMean (exponentDensity ρ x p Q B) g :=
    fun g => by
      rw [hD, densityMean_const_mul_density (Real.exp_ne_zero _)]
  rw [msw, msw, msw]
  have hb : ∀ η : BondField ι, exponentDensity ρ x p Q B η ≠ 0 →
      η ∈ (closedBalls ρ : Set (BondField ι)) :=
    fun η h b => (norm_lt_of_weight_ne_zero (left_ne_zero_of_mul h) b).le
  have k₀ : ∀ (l : Fin 2) (η : BondField ι), η ∈ (closedBalls ρ : Set (BondField ι)) →
      parameterSlope (linearExponent x Q B) l η =
        1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) l) η +
          iteratedFDeriv ℝ 1 B 0 (Fin.cons (paramUnit l) noVec) + slopeRemainder ρ x Q B l η := by
    intro l η hη
    unfold slopeRemainder
    rw [Set.indicator_of_mem hη]
    ring
  have k₂ : ∀ η : BondField ι, η ∈ (closedBalls ρ : Set (BondField ι)) →
      parameterMixedDeriv (linearExponent x Q B) η =
        1 / 2 * quadraticForm (familyMixedDeriv (scaledHessian x Q)) η +
          iteratedFDeriv ℝ 2 B 0 (Fin.cons (paramUnit 0) (Fin.cons (paramUnit 1) noVec)) +
          mixedRemainder ρ x Q B η := by
    intro η hη
    unfold mixedRemainder
    rw [Set.indicator_of_mem hη]
    ring
  rw [densityMean_congr (f := exponentDensity ρ x p Q B) (fun η h0 => by
      rw [k₂ η (hb η h0), k₀ 0 η (hb η h0), k₀ 1 η (hb η h0)]),
    densityMean_congr (f := exponentDensity ρ x p Q B) (g := parameterSlope (linearExponent x Q B) 0)
      (fun η h0 => k₀ 0 η (hb η h0)),
    densityMean_congr (f := exponentDensity ρ x p Q B) (g := parameterSlope (linearExponent x Q B) 1)
      (fun η h0 => k₀ 1 η (hb η h0))]
  have hf : ∀ η, exponentDensity ρ x p Q B η =
      cutoffGaussianDensity ρ x p Q η * Real.exp (-exponentRemainder ρ x Q B η) := by
    intro η
    by_cases h : radialWeightProd (cutoffFactor ρ p) η = 0
    · simp [exponentDensity, cutoffGaussianDensity, h]
    · have hη : η ∈ (closedBalls ρ : Set (BondField ι)) := fun b => (norm_lt_of_weight_ne_zero h b).le
      unfold exponentDensity cutoffGaussianDensity exponentRemainder
      rw [Set.indicator_of_mem hη, mul_assoc, ← Real.exp_add]
      congr 2
      ring
  have hWδ : ∀ η : BondField ι, radialWeightProd (cutoffFactor ρ p) η ≠ 1 →
      1 ≤ 4 / (ρ ^ 2 * x) * (1 + x * sqNorm η) := by
    intro η h
    have hex : ∃ b, 5 * ρ / 8 < ‖η b‖ := by
      by_contra hn
      exact h (weight_eq_one hρ hp fun b => not_lt.1 fun hb => hn ⟨b, hb⟩)
    obtain ⟨b, hbη⟩ := hex
    have h1 : ‖η b‖ ^ 2 ≤ sqNorm η :=
      Finset.single_le_sum (f := fun b => ‖η b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
    have h2 : (5 * ρ / 8) ^ 2 ≤ sqNorm η := by
      refine le_trans ?_ h1
      exact pow_le_pow_left₀ (by positivity) hbη.le 2
    have hc : 0 < ρ ^ 2 * x := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [sqNorm_nonneg η, mul_nonneg hx.le (sqNorm_nonneg η)]
  have hm : ∀ j, 0 ≤ momentBound lam N j := fun j => by
    have := gainRate_pos hlam N
    unfold momentBound
    positivity
  exact covariance_comparison
    (a₀ := fun η => 1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) 0) η)
    (a₁ := fun η => 1 / 2 * quadraticForm (familyPartialDeriv (scaledHessian x Q) 1) η)
    (a₂ := fun η => 1 / 2 * quadraticForm (familyMixedDeriv (scaledHessian x Q)) η)
    (r₀ := slopeRemainder ρ x Q B 0) (r₁ := slopeRemainder ρ x Q B 1) (r₂ := mixedRemainder ρ x Q B)
    (W := radialWeightProd (cutoffFactor ρ p)) L₁ L₀ Lg hf (fun _ => rfl) weight_nonneg
    (weight_le_one hρ hp) hWδ
    (polyBounded_exponentRemainder hρ LF hK hx hy hyx _) (polyBounded_partial_form hρ LF hK hx 0)
    (polyBounded_partial_form hρ LF hK hx 1)
    (polyBounded_mixed_form hρ LF hK hx) (polyBounded_slopeRemainder hρ LF hK hx hy hyx 0 _)
    (polyBounded_slopeRemainder hρ LF hK hx hy hyx 1 _)
    (polyBounded_mixedRemainder hρ LF hK hx hy hyx _) hK
    (by positivity) (by positivity) hMm hm hmM hεs hδs hsm
end Laws
section Numbers
private theorem threshold_arithmetic {lam ρ K x y Lb D : ℝ} (hlam : 0 < lam) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hx : 1 ≤ x) (hy : 0 < y) (hyx : y ^ 2 * x = 1) (hLb : 1 + K ≤ Lb) (hD : 1 ≤ D)
    (hC : (37 * D ^ 3 * (2 + 4 / ρ ^ 2) * (1 + 2 / lam)) * (Lb ^ 23 * y) ≤ 1) :
    K ^ 2 ≤ x ∧ K ≤ x * lam / 2 ∧ 2 * K * y * (D * Lb ^ 6) ≤ 1 / 4 ∧
      4 / (ρ ^ 2 * x) * (D * Lb ^ 6) ≤ 1 / 4 ∧
      7 * (1 + K) ^ 2 * (2 * K * y + 4 / (ρ ^ 2 * x)) * (D * Lb ^ 6) ^ 2 ≤ 1 ∧
      37 * (1 + K) ^ 4 * (D * Lb ^ 6) ^ 3 * (2 * K * y + 4 / (ρ ^ 2 * x)) ≤
        (37 * D ^ 3 * (2 + 4 / ρ ^ 2) * (1 + 2 / lam)) * (Lb ^ 23 * y) := by
  have hx0 : 0 < x := by linarith
  have hLb1 : 1 ≤ Lb := by linarith
  have hKL : K ≤ Lb := by linarith
  set P : ℝ := 2 + 4 / ρ ^ 2 with hP
  have hr : 0 < 4 / ρ ^ 2 := by positivity
  have hP0 : 0 < P := by linarith
  set w : ℝ := Lb ^ 23 * y with hw
  have hw0 : 0 < w := by positivity
  set C : ℝ := 37 * D ^ 3 * P * (1 + 2 / lam) with hCdef
  have hlam2 : 0 < 2 / lam := by positivity
  have hD3 : D ≤ D ^ 3 := le_self_pow₀ hD (by norm_num)
  have hD23 : D ^ 2 ≤ D ^ 3 := pow_le_pow_right₀ hD (by norm_num)
  have hD31 : 1 ≤ D ^ 3 := one_le_pow₀ hD
  have hPD : P ≤ P * D ^ 3 := le_mul_of_one_le_right hP0.le hD31
  have hC0 : 37 * D ^ 3 * P ≤ C := by
    rw [hCdef]
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hCl : 2 / lam ≤ C := by
    have h1 : 1 ≤ 37 * D ^ 3 * P := by linarith
    rw [hCdef]
    calc 2 / lam ≤ 1 * (1 + 2 / lam) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hy2 : y ^ 2 ≤ 1 := by
    have : y ^ 2 * 1 ≤ y ^ 2 * x := by gcongr
    linarith
  have hy1 : y ≤ 1 := (pow_le_one_iff_of_nonneg hy.le two_ne_zero).1 hy2
  have hyy : y ^ 2 ≤ y := by
    rw [sq]
    exact mul_le_of_le_one_left hy.le hy1
  have hinvx : 1 / x = y ^ 2 := by
    field_simp
    linarith
  have hwk : ∀ k : ℕ, k ≤ 23 → Lb ^ k * y ≤ w := fun k hk =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hLb1 hk) hy.le
  have hsmall : ∀ X : ℝ, X ≤ C → X * w ≤ 1 := fun X hX =>
    (mul_le_mul_of_nonneg_right hX hw0.le).trans hC
  have hKy : K * y ≤ Lb * y := mul_le_mul_of_nonneg_right hKL hy.le
  have hLy : Lb * y ≤ w := by
    simpa using hwk 1 (by norm_num)
  have h4 : 4 / (ρ ^ 2 * x) = 4 / ρ ^ 2 * y ^ 2 := by
    rw [← hinvx]
    field_simp
  set Eb : ℝ := 2 * K * y + 4 / (ρ ^ 2 * x) with hEb
  have hEbP : Eb ≤ P * (Lb * y) := by
    rw [hEb, h4, hP]
    have h1 : y ^ 2 ≤ Lb * y := hyy.trans (le_mul_of_one_le_left hy.le hLb1)
    have h2 : 4 / ρ ^ 2 * y ^ 2 ≤ 4 / ρ ^ 2 * (Lb * y) := mul_le_mul_of_nonneg_left h1 hr.le
    have e : (2 + 4 / ρ ^ 2) * (Lb * y) = 2 * (Lb * y) + 4 / ρ ^ 2 * (Lb * y) := by ring
    have e2 : 2 * K * y = 2 * (K * y) := by ring
    rw [e, e2]
    linarith
  have h1K : 1 + K ≤ Lb := hLb
  have h1K0 : 0 ≤ 1 + K := by linarith
  have hC1 : 1 ≤ C := by linarith
  have hLw : w ≤ 1 := by
    have := hsmall 1 hC1
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : K * y ≤ 1 := hKy.trans (hLy.trans hLw)
    have h2 : (K * y) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) h1
    calc K ^ 2 = (K * y) ^ 2 * x := by
          have : (K * y) ^ 2 * x = K ^ 2 * (y ^ 2 * x) := by ring
          rw [this, hyx, mul_one]
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right h2 hx0.le
      _ = x := one_mul x
  · have h1 : 2 / lam * w ≤ 1 := hsmall _ hCl
    have h2 : K * y ^ 2 ≤ w := by
      calc K * y ^ 2 = (K * y) * y := by ring
        _ ≤ w * 1 := mul_le_mul (hKy.trans hLy) hy1 hy.le hw0.le
        _ = w := mul_one w
    have h3 : K * y ^ 2 ≤ lam / 2 := by
      have h4 : w ≤ lam / 2 := by
        have e : 2 / lam * w = w / (lam / 2) := by
          field_simp
        rw [e, div_le_one (by positivity)] at h1
        exact h1
      linarith
    calc K = K * y ^ 2 * x := by
          have : K * y ^ 2 * x = K * (y ^ 2 * x) := by ring
          rw [this, hyx, mul_one]
      _ ≤ lam / 2 * x := mul_le_mul_of_nonneg_right h3 hx0.le
      _ = _ := by ring
  · have h1 : 2 * K * y * (D * Lb ^ 6) ≤ 2 * D * (Lb ^ 7 * y) := by
      have : K * Lb ^ 6 ≤ Lb ^ 7 := by
        calc K * Lb ^ 6 ≤ Lb * Lb ^ 6 := by gcongr
          _ = Lb ^ 7 := by ring
      calc 2 * K * y * (D * Lb ^ 6) = 2 * D * y * (K * Lb ^ 6) := by ring
        _ ≤ 2 * D * y * Lb ^ 7 := by gcongr
        _ = _ := by ring
    have h2 : 2 * D * (Lb ^ 7 * y) ≤ 2 * D * w := by
      have := hwk 7 (by norm_num)
      gcongr
    have h3 : 8 * D * w ≤ 1 := by
      refine hsmall _ (le_trans ?_ hC0)
      have : D ^ 3 ≤ P * D ^ 3 := le_mul_of_one_le_left (by positivity) (by linarith)
      linarith
    linarith
  · have h1 : 4 / (ρ ^ 2 * x) * (D * Lb ^ 6) ≤ 4 / ρ ^ 2 * D * (Lb ^ 6 * y) := by
      rw [h4]
      calc 4 / ρ ^ 2 * y ^ 2 * (D * Lb ^ 6) = 4 / ρ ^ 2 * D * (Lb ^ 6 * y ^ 2) := by ring
        _ ≤ _ := by gcongr
    have h2 : 4 / ρ ^ 2 * D * (Lb ^ 6 * y) ≤ 4 / ρ ^ 2 * D * w := by
      have := hwk 6 (by norm_num)
      gcongr
    have h3 : 4 * (4 / ρ ^ 2 * D) * w ≤ 1 := by
      refine hsmall _ (le_trans ?_ hC0)
      have : 4 / ρ ^ 2 ≤ P := by
        rw [hP]
        linarith
      have hh : 4 * (4 / ρ ^ 2 * D) ≤ 4 * (P * D ^ 3) := by gcongr
      linarith
    linarith
  · have h1 : (1 + K) ^ 2 ≤ Lb ^ 2 := pow_le_pow_left₀ h1K0 h1K 2
    have h2 : 7 * (1 + K) ^ 2 * Eb * (D * Lb ^ 6) ^ 2 ≤
        7 * Lb ^ 2 * (P * (Lb * y)) * (D * Lb ^ 6) ^ 2 := by gcongr
    have h3 : 7 * Lb ^ 2 * (P * (Lb * y)) * (D * Lb ^ 6) ^ 2 = 7 * P * D ^ 2 * (Lb ^ 15 * y) := by ring
    have h4' : 7 * P * D ^ 2 * (Lb ^ 15 * y) ≤ 7 * P * D ^ 2 * w := by
      have := hwk 15 (by norm_num)
      gcongr
    have h5 : 7 * P * D ^ 2 * w ≤ 1 := by
      refine hsmall _ (le_trans ?_ hC0)
      have h6 : 7 * P * D ^ 2 ≤ 7 * P * D ^ 3 := by gcongr
      linarith
    linarith
  · have h1 : (1 + K) ^ 4 ≤ Lb ^ 4 := pow_le_pow_left₀ h1K0 h1K 4
    have h2 : 37 * (1 + K) ^ 4 * (D * Lb ^ 6) ^ 3 * Eb ≤
        37 * Lb ^ 4 * (D * Lb ^ 6) ^ 3 * (P * (Lb * y)) := by gcongr
    have h3 : 37 * Lb ^ 4 * (D * Lb ^ 6) ^ 3 * (P * (Lb * y)) = 37 * D ^ 3 * P * w := by
      rw [hw]
      ring
    have h5 : 37 * D ^ 3 * P * w ≤ C * w := mul_le_mul_of_nonneg_right hC0 hw0.le
    linarith
private theorem momentBound_le {lam Lb : ℝ} {N j : ℕ} (hlam : 0 < lam) (hN : (N : ℝ) + 1 ≤ 4 * Lb)
    (hLb : 1 ≤ Lb) (hj : j ≤ 4) :
    momentBound lam N j ≤ (720 * (1 + 32 / lam) ^ 6 * Real.exp (lam / 8 + 2 / lam + 1)) * Lb ^ 6 := by
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht : 1 - contractionRatio N = 1 / ((N : ℝ) + 1) := one_sub_contractionRatio
  have ht1 : 1 - contractionRatio N ≤ 1 := by
    rw [ht, div_le_one hN0]
    have : (0 : ℝ) ≤ N := by positivity
    linarith
  have hl8 : 0 < lam / 8 := by positivity
  have h2l : 0 < 2 / lam := by positivity
  have hr : (gainRate lam N)⁻¹ ≤ (1 + 32 / lam) * Lb := by
    have e : (gainRate lam N)⁻¹ = ((N : ℝ) + 1) * (8 / lam) := by
      unfold gainRate
      rw [ht]
      field_simp
    rw [e]
    calc ((N : ℝ) + 1) * (8 / lam) ≤ 4 * Lb * (8 / lam) := by gcongr
      _ = 32 / lam * Lb := by ring
      _ ≤ _ := by
          have : 0 ≤ Lb := by linarith
          nlinarith
  have hΛ : 1 ≤ (1 + 32 / lam) * Lb := by
    have h32 : 0 < 32 / lam := by positivity
    have : (1 : ℝ) ≤ 1 + 32 / lam := by linarith
    exact one_le_mul_of_one_le_of_one_le this hLb
  have hr0 : 0 ≤ (gainRate lam N)⁻¹ := (inv_pos.2 (gainRate_pos hlam N)).le
  have hpow : ((gainRate lam N)⁻¹) ^ j ≤ ((1 + 32 / lam) * Lb) ^ 6 :=
    (pow_le_pow_left₀ hr0 hr j).trans (pow_le_pow_right₀ hΛ (by omega))
  have hfac : (j.factorial : ℝ) ≤ 720 := by
    have : j.factorial ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
    have h6 : Nat.factorial 6 = 720 := rfl
    rw [h6] at this
    exact_mod_cast this
  have hexp : Real.exp (gainRate lam N + gainLoss lam N + 1) ≤ Real.exp (lam / 8 + 2 / lam + 1) := by
    refine Real.exp_le_exp.2 ?_
    have h1 : gainRate lam N ≤ lam / 8 := by
      unfold gainRate
      exact mul_le_of_le_one_left hl8.le ht1
    have h2 : gainLoss lam N ≤ 2 / lam := by
      unfold gainLoss
      exact mul_le_of_le_one_left h2l.le ht1
    linarith
  unfold momentBound
  calc (j.factorial : ℝ) * ((gainRate lam N)⁻¹) ^ j * Real.exp (gainRate lam N + gainLoss lam N + 1)
      ≤ 720 * ((1 + 32 / lam) * Lb) ^ 6 * Real.exp (lam / 8 + 2 / lam + 1) := by gcongr
    _ = _ := by ring
end Numbers
end LaplaceMethod
open LaplaceMethod in
theorem laplaceMethodHessian_holds (hC1 : logCutoffIntegralSecondDeriv)
    (hC2 : GaussianMeans.LogDetMixedDerivGaussian)
    (hCu : LogCutoffIntegralContDiffTwo) :
    RunningCouplingSlope.LaplaceMethodHessian := by
  intro ρ lam hρ hlam
  set D : ℝ := 720 * (1 + 32 / lam) ^ 6 * Real.exp (lam / 8 + 2 / lam + 1) with hDdef
  have hD : 1 ≤ D := by
    have h1 : 1 ≤ (1 + 32 / lam) ^ 6 := one_le_pow₀ (by
      have : 0 < 32 / lam := by positivity
      linarith)
    have h2 : 1 ≤ Real.exp (lam / 8 + 2 / lam + 1) := Real.one_le_exp (by positivity)
    have h3 : 1 ≤ (1 + 32 / lam) ^ 6 * Real.exp (lam / 8 + 2 / lam + 1) :=
      one_le_mul_of_one_le_of_one_le h1 h2
    rw [hDdef, mul_assoc]
    linarith
  set C : ℝ := 37 * D ^ 3 * (2 + 4 / ρ ^ 2) * (1 + 2 / lam) with hCdef
  have hC0 : 0 < C := by positivity
  refine ⟨C, ((23 : ℕ) : ℝ), hC0, by positivity, ?_⟩
  intro ι _ _ _ p K x Q B hp hK hx hsm LF
  have hcard : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set Lb : ℝ := (Fintype.card ι : ℝ) + K with hLbdef
  have hLb : 1 + K ≤ Lb := by
    rw [hLbdef]
    linarith
  have hLb1 : 1 ≤ Lb := by linarith
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ (-(1 / 2) : ℝ) with hydef
  have hy : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hyx : y ^ 2 * x = 1 := by
    have e : y ^ 2 = x⁻¹ := by
      rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
      exact Real.rpow_neg_one x
    rw [e]
    exact inv_mul_cancel₀ hx0.ne'
  rw [Real.rpow_natCast] at hsm ⊢
  have hsm' : C * (Lb ^ 23 * y) ≤ 1 := by
    rw [← mul_assoc]
    exact hsm
  obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆⟩ := threshold_arithmetic hlam hρ hK hx hy hyx hLb hD hsm'
  have hNc : Module.finrank ℝ (BondField ι) = Fintype.card ι * 3 := by
    simp [Module.finrank_pi_fintype]
  have hN : 1 ≤ Module.finrank ℝ (BondField ι) := by
    rw [hNc]
    have := Fintype.card_pos (α := ι)
    omega
  have hN4 : ((Module.finrank ℝ (BondField ι) : ℕ) : ℝ) + 1 ≤ 4 * Lb := by
    rw [hNc]
    push_cast
    rw [hLbdef]
    linarith
  have hMm : 1 ≤ D * Lb ^ 6 := one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hLb1)
  obtain ⟨c₁, c₂, c₃⟩ := second_deriv_comparison hC2 hC1 hCu hN rfl hρ hlam hp hK hx0 LF hy hyx t₁ t₂
    hMm (fun j hj => momentBound_le hlam hN4 hLb1 hj) t₃ t₄ t₅
  refine ⟨c₁, c₂, c₃.trans ?_⟩
  rw [mul_assoc C]
  exact t₆
end LaplaceAsymptotics
end YangMills.Construction
end
