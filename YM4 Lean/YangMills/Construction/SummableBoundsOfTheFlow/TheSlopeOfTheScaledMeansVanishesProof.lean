import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAList
import YangMills.Construction.SummableBoundsOfTheFlow.FloorOfTheScaledExponents
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreSmoothInTheScale
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansHaveTheirBounds
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledPartsAreSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheSlopeOfTheScaledMeansVanishes
import YangMills.Construction.SummableBoundsOfTheFlow.TheTopDerivativesOfAScaledMeanAreCumulantsForm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.IteratedDerivative YangMills.Construction.Cumulants
namespace YangMills.Construction.ScaledVariables
section
private def VanishingSlopeAt (f : ℝ → ℝ) (a : ℝ) : Prop := Tendsto (fun l => (f l - a) / l) (𝓝[>] 0) (𝓝 0)
private theorem VanishingSlopeAt.const (a : ℝ) : VanishingSlopeAt (fun _ => a) a := by
  simp [VanishingSlopeAt]
private theorem VanishingSlopeAt.congr {f g : ℝ → ℝ} {a : ℝ} (h : VanishingSlopeAt f a)
    (e : ∀ᶠ l in 𝓝[>] (0 : ℝ), f l = g l) : VanishingSlopeAt g a := by
  refine Tendsto.congr' ?_ h
  filter_upwards [e] with l hl
  rw [hl]
private theorem VanishingSlopeAt.tendsto {f : ℝ → ℝ} {a : ℝ} (h : VanishingSlopeAt f a) :
    Tendsto f (𝓝[>] 0) (𝓝 a) := by
  have h1 : Tendsto (fun l : ℝ => l) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h2 := (h.mul h1).add_const a
  rw [zero_mul, zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with l hl
  have : l ≠ 0 := ne_of_gt hl
  field_simp
  ring
private theorem VanishingSlopeAt.add {f g : ℝ → ℝ} {a b : ℝ} (hf : VanishingSlopeAt f a)
    (hg : VanishingSlopeAt g b) : VanishingSlopeAt (fun l => f l + g l) (a + b) := by
  have h := Tendsto.add hf hg
  rw [add_zero] at h
  refine h.congr fun l => ?_
  ring
private theorem VanishingSlopeAt.mul {f g : ℝ → ℝ} {a b : ℝ} (hf : VanishingSlopeAt f a)
    (hg : VanishingSlopeAt g b) : VanishingSlopeAt (fun l => f l * g l) (a * b) := by
  have h := (hf.tendsto.mul hg).add (Tendsto.const_mul b hf)
  rw [mul_zero, mul_zero, add_zero] at h
  refine h.congr fun l => ?_
  ring
private theorem VanishingSlopeAt.const_mul {f : ℝ → ℝ} {a : ℝ} (c : ℝ) (hf : VanishingSlopeAt f a) :
    VanishingSlopeAt (fun l => c * f l) (c * a) := (VanishingSlopeAt.const c).mul hf
private theorem VanishingSlopeAt.inv {f : ℝ → ℝ} {a : ℝ} (hf : VanishingSlopeAt f a) (ha : a ≠ 0) :
    VanishingSlopeAt (fun l => (f l)⁻¹) a⁻¹ := by
  have h1 : Tendsto (fun l => (f l)⁻¹) (𝓝[>] 0) (𝓝 a⁻¹) := hf.tendsto.inv₀ ha
  have h2 := (h1.mul hf).const_mul (-a⁻¹)
  simp only [mul_zero] at h2
  refine h2.congr' ?_
  have h3 : ∀ᶠ l in 𝓝[>] (0 : ℝ), f l ≠ 0 := hf.tendsto.eventually_ne ha
  filter_upwards [h3] with l hl
  field_simp
  ring
private theorem VanishingSlopeAt.div {f g : ℝ → ℝ} {a b : ℝ} (hf : VanishingSlopeAt f a)
    (hg : VanishingSlopeAt g b) (hb : b ≠ 0) : VanishingSlopeAt (fun l => f l / g l) (a / b) := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv hb)
private theorem VanishingSlopeAt.sum {ι : Type} (s : Finset ι) {f : ι → ℝ → ℝ} {a : ι → ℝ}
    (h : ∀ i ∈ s, VanishingSlopeAt (f i) (a i)) :
    VanishingSlopeAt (fun l => ∑ i ∈ s, f i l) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using VanishingSlopeAt.const 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
private theorem VanishingSlopeAt.prod {ι : Type} (s : Finset ι) {f : ι → ℝ → ℝ} {a : ι → ℝ}
    (h : ∀ i ∈ s, VanishingSlopeAt (f i) (a i)) :
    VanishingSlopeAt (fun l => ∏ i ∈ s, f i l) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using VanishingSlopeAt.const 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
private theorem vanishingSlopeAt_integral {E : Type} [NormedAddCommGroup E] [MeasurableSpace E] (μ : Measure E)
    (Φ : ℝ → E → ℝ) (Q B : E → ℝ) (l₁ : ℝ) (hl₁ : 0 < l₁) (hB : Integrable B μ)
    (h0 : Integrable (Φ 0) μ) (hm : ∀ l, 0 < l → l ≤ l₁ → AEStronglyMeasurable (Φ l) μ)
    (hd : ∀ ζ l, 0 < l → l ≤ l₁ → |Φ l ζ - Φ 0 ζ| ≤ l * B ζ)
    (hQ : ∀ ζ, HasDerivAt (fun l => Φ l ζ) (Q ζ) 0)
    (he : ∀ ζ, ∀ᶠ l in 𝓝 (0 : ℝ), Φ (-l) (-ζ) = Φ l ζ) (hneg : ∫ ζ, Q (-ζ) ∂μ = ∫ ζ, Q ζ ∂μ) :
    VanishingSlopeAt (fun l => ∫ ζ, Φ l ζ ∂μ) (∫ ζ, Φ 0 ζ ∂μ) := by
  have hsmall : ∀ᶠ l in 𝓝[>] (0 : ℝ), l ∈ Ioc 0 l₁ := Ioc_mem_nhdsGT hl₁
  have hQodd : ∀ ζ, Q (-ζ) = -Q ζ := by
    intro ζ
    have h1 : HasDerivAt (fun l => Φ (-l) ζ) (-Q ζ) 0 := by
      have h2 : HasDerivAt (fun l => Φ l ζ) (Q ζ) (-(0 : ℝ)) := by simpa using hQ ζ
      exact show HasDerivAt ((fun l => Φ l ζ) ∘ Neg.neg) (-Q ζ) 0 from by
        simpa using h2.scomp (0 : ℝ) (hasDerivAt_neg 0)
    have h3 : (fun l => Φ (-l) ζ) =ᶠ[𝓝 0] fun l => Φ l (-ζ) := by
      have h5 := he (-ζ)
      simp only [neg_neg] at h5
      exact h5
    exact ((h1.congr_of_eventuallyEq h3.symm).unique (hQ (-ζ))).symm ▸ rfl
  have hquot : Tendsto (fun l => ∫ ζ, (Φ l ζ - Φ 0 ζ) / l ∂μ) (𝓝[>] 0) (𝓝 (∫ ζ, Q ζ ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hB ?_
    · filter_upwards [hsmall] with l hl
      simpa [div_eq_mul_inv] using ((hm l hl.1 hl.2).sub h0.1).mul_const l⁻¹
    · filter_upwards [hsmall] with l hl
      refine Eventually.of_forall fun ζ => ?_
      have := hd ζ l hl.1 hl.2
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hl.1, div_le_iff₀ hl.1]
      linarith
    · refine Eventually.of_forall fun ζ => ?_
      have h1 := (hQ ζ).hasDerivWithinAt (s := Ioi 0)
      have h2 := hasDerivWithinAt_iff_tendsto_slope.1 h1
      have h3 : 𝓝[Ioi (0 : ℝ) \ {0}] (0 : ℝ) = 𝓝[>] 0 := by
        congr 1
        ext x
        simp only [Set.mem_sdiff, mem_Ioi, mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
      rw [h3] at h2
      refine h2.congr fun l => ?_
      simp [slope_def_field]
  have hzero : ∫ ζ, Q ζ ∂μ = 0 := by
    have h1 := hneg
    simp only [hQodd, integral_neg] at h1
    linarith
  rw [hzero] at hquot
  refine hquot.congr' ?_
  filter_upwards [hsmall] with l hl
  have hi : Integrable (Φ l) μ := by
    refine Integrable.mono' (h0.abs.add (hB.const_mul l)) (hm l hl.1 hl.2) (Eventually.of_forall fun ζ => ?_)
    have := hd ζ l hl.1 hl.2
    have h3 : |Φ l ζ| ≤ |Φ 0 ζ| + |Φ l ζ - Φ 0 ζ| := by
      have := abs_add_le (Φ 0 ζ) (Φ l ζ - Φ 0 ζ)
      simpa using this
    simp only [Real.norm_eq_abs, Pi.add_apply]
    linarith
  rw [← integral_sub hi h0]
  simp only [div_eq_mul_inv]
  rw [integral_mul_const]
private theorem tendsto_deriv_of_vanishingSlopeAt {G : ℝ → ℝ} {a l₁ M : ℝ} (hl₁ : 0 < l₁)
    (hG : ∀ l, 0 < l → l ≤ l₁ → ContDiffAt ℝ (2 : ℕ) G l)
    (hb : ∀ l, 0 < l → l ≤ l₁ → |iteratedDeriv 2 G l| ≤ M) (hf : VanishingSlopeAt G a) :
    Tendsto (deriv G) (𝓝[>] 0) (𝓝 0) := by
  have dG : ∀ l, 0 < l → l ≤ l₁ → HasDerivAt G (deriv G l) l := fun l h0 h1 =>
    ((hG l h0 h1).differentiableAt (by norm_num)).hasDerivAt
  have d2 : ∀ l, 0 < l → l ≤ l₁ → HasDerivAt (deriv G) (iteratedDeriv 2 G l) l := by
    intro l h0 h1
    have h2 : DifferentiableAt ℝ (iteratedDeriv 1 G) l := by
      have h3 : iteratedDeriv 1 G = fun x => iteratedFDeriv ℝ 1 G x (fun _ => 1) :=
        funext fun _ => iteratedDeriv_eq_iteratedFDeriv
      have h4 := (hG l h0 h1).differentiableAt_iteratedFDeriv (m := 1) (by norm_num)
      rw [h3]
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ) ℝ (fun _ => 1)).differentiableAt.comp l h4
    rw [iteratedDeriv_one] at h2
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact h2.hasDerivAt
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb l₁ hl₁ le_rfl)
  have key : ∀ l, 0 < l → 2 * l ≤ l₁ → |G (2 * l) - G l - l * deriv G l| ≤ M * l * l := by
    intro l h0 h1
    have hle : ∀ s ∈ Icc l (2 * l), s ≤ l₁ ∧ 0 < s := fun s hs => ⟨hs.2.trans h1, h0.trans_le hs.1⟩
    have hs1 : ∀ s ∈ Icc l (2 * l), |deriv G s - deriv G l| ≤ M * l := by
      intro s hs
      have hsub := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := deriv G)
        (f' := iteratedDeriv 2 G) (C := M) (s := Icc l s) (x := l) (y := s)
        (fun x hx => (d2 x (h0.trans_le hx.1) ((hx.2.trans hs.2).trans h1)).hasDerivWithinAt)
        (fun x hx => by
          rw [Real.norm_eq_abs]
          exact hb x (h0.trans_le hx.1) ((hx.2.trans hs.2).trans h1))
        (convex_Icc l s) (left_mem_Icc.2 hs.1) (right_mem_Icc.2 hs.1)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hs.1)] at hsub
      refine hsub.trans (mul_le_mul_of_nonneg_left ?_ hM)
      linarith [hs.2]
    have hsub := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => G s - s * deriv G l) (f' := fun s => deriv G s - deriv G l) (C := M * l)
      (s := Icc l (2 * l)) (x := l) (y := 2 * l)
      (fun x hx => by
        have h2 := (dG x (hle x hx).2 (hle x hx).1).sub ((hasDerivAt_id x).mul_const (deriv G l))
        have h3 : HasDerivWithinAt (G - fun y => y * deriv G l) (deriv G x - deriv G l) (Icc l (2 * l)) x := by
          simpa using h2.hasDerivWithinAt
        exact h3)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hs1 x hx)
      (convex_Icc l (2 * l)) (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hsub
    have e1 : G (2 * l) - 2 * l * deriv G l - (G l - l * deriv G l) = G (2 * l) - G l - l * deriv G l := by ring
    have e2 : |2 * l - l| = l := by
      rw [show 2 * l - l = l by ring, abs_of_pos h0]
    rw [e1, e2] at hsub
    exact hsub
  have h2l : Tendsto (fun l : ℝ => 2 * l) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun l : ℝ => 2 * l) (𝓝 0) (𝓝 (2 * 0)) := (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with l hl
      exact mem_Ioi.2 (mul_pos two_pos (mem_Ioi.1 hl))
  have hT : Tendsto (fun l => 2 * ((G (2 * l) - a) / (2 * l)) - (G l - a) / l) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ((hf.comp h2l).const_mul 2).sub hf
    simpa [Function.comp_def] using h1
  have hlin : Tendsto (fun l : ℝ => M * l) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun l : ℝ => M * l) (𝓝 0) (𝓝 (M * 0)) := (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hd : Tendsto (fun l => deriv G l - (2 * ((G (2 * l) - a) / (2 * l)) - (G l - a) / l)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlin
    have hsm : ∀ᶠ l in 𝓝[>] (0 : ℝ), l ∈ Ioc 0 (l₁ / 2) := Ioc_mem_nhdsGT (by linarith)
    filter_upwards [hsm] with l hl
    have h1 := key l hl.1 (by linarith [hl.2])
    have h0 : l ≠ 0 := ne_of_gt hl.1
    have e : deriv G l - (2 * ((G (2 * l) - a) / (2 * l)) - (G l - a) / l) =
        -(G (2 * l) - G l - l * deriv G l) / l := by
      field_simp
      ring
    rw [e, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hl.1, div_le_iff₀ hl.1]
    exact h1
  have := hd.add hT
  simpa using this
private theorem integrable_one_add_norm_pow_mul_gaussian {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ)
    {c : ℝ} (C : ℝ) (hc : 0 < c) :
    Integrable (fun ζ : E => (1 + ‖ζ‖) ^ m * Real.exp (-(c * ‖ζ‖ ^ 2) + C * ‖ζ‖)) μ := by
  set N : ℕ := Module.finrank ℝ E + 1 with hN
  have h1 : Integrable (fun ζ : E => (1 + ‖ζ‖) ^ (-(N : ℝ))) μ :=
    integrable_one_add_norm (by rw [hN]; push_cast; linarith)
  set Dc : ℝ := (C + 1) ^ 2 / (4 * c) with hDc
  set A : ℝ := Real.exp (Dc + 1) * ((m + N).factorial : ℝ) with hA
  refine Integrable.mono' (h1.const_mul A) (by fun_prop) (Eventually.of_forall fun ζ => ?_)
  set x := ‖ζ‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have hq : -(c * x ^ 2) + C * x ≤ -(1 + x) + (Dc + 1) := by
    have e : c * (x - (C + 1) / (2 * c)) ^ 2 = c * x ^ 2 - (C + 1) * x + Dc := by
      rw [hDc]
      field_simp
      ring
    have := mul_nonneg hc.le (sq_nonneg (x - (C + 1) / (2 * c)))
    linarith
  have ht : 0 < 1 + x := by linarith
  have hp : (1 + x) ^ (m + N) ≤ ((m + N).factorial : ℝ) * Real.exp (1 + x) := by
    have := Real.pow_div_factorial_le_exp (1 + x) ht.le (m + N)
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hneg : (1 + x) ^ (-(N : ℝ)) = ((1 + x) ^ N)⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.rpow_natCast]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hneg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (1 + x) ^ m * Real.exp (-(c * x ^ 2) + C * x) * (1 + x) ^ N
      = (1 + x) ^ (m + N) * Real.exp (-(c * x ^ 2) + C * x) := by rw [pow_add]; ring
    _ ≤ (((m + N).factorial : ℝ) * Real.exp (1 + x)) * Real.exp (-(1 + x) + (Dc + 1)) := by
        gcongr
    _ = A := by
        rw [hA, mul_assoc, ← Real.exp_add]
        rw [show 1 + x + (-(1 + x) + (Dc + 1)) = Dc + 1 by ring]
        ring
end
section
variable {ι : Type} [Fintype ι]
private abbrev BondVars (ι : Type) : Type := ι → EuclideanSpace ℝ (Fin 3)
private def InBalls (ρ l : ℝ) (ζ : BondVars ι) : Prop := ∀ b, l * ‖ζ b‖ < ρ
private structure IsTempered (ρ l₁ K : ℝ) (m : ℕ) (H : ℝ → BondVars ι → ℝ) : Prop where
  diff : ∀ l ζ, InBalls ρ |l| ζ → DifferentiableAt ℝ (fun l' => H l' ζ) l
  bound : ∀ l ζ, 0 < l → l ≤ l₁ → InBalls ρ l ζ → |H l ζ| ≤ K * (1 + ‖ζ‖) ^ m
  slope : ∀ l ζ, 0 < l → l ≤ l₁ → InBalls ρ l ζ → |deriv (fun l' => H l' ζ) l| ≤ K * (1 + ‖ζ‖) ^ m
  even : ∀ l ζ, H (-l) (-ζ) = H l ζ
  cont : ∀ l, 0 ≤ l → l ≤ l₁ → ContinuousOn (H l) {ζ | InBalls ρ l ζ}
private theorem inBalls_of_norm {ρ l : ℝ} {ζ : BondVars ι} (hl : 0 ≤ l) (h : l * ‖ζ‖ < ρ) :
    InBalls ρ l ζ := fun b =>
  lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_le_pi_norm ζ b) hl) h
private theorem one_le_one_add_norm_pow (ζ : BondVars ι) (n : ℕ) : 1 ≤ (1 + ‖ζ‖) ^ n :=
  one_le_pow₀ (by linarith [norm_nonneg ζ])
private theorem one_add_norm_pow_le_pow (ζ : BondVars ι) {a b : ℕ} (h : a ≤ b) :
    (1 + ‖ζ‖) ^ a ≤ (1 + ‖ζ‖) ^ b :=
  pow_le_pow_right₀ (by linarith [norm_nonneg ζ]) h
private theorem IsTempered.bound_zero {ρ l₁ K : ℝ} {m : ℕ} {H : ℝ → BondVars ι → ℝ} (h : IsTempered ρ l₁ K m H)
    (hρ : 0 < ρ) (hl₁ : 0 < l₁) (ζ : BondVars ι) : |H 0 ζ| ≤ K * (1 + ‖ζ‖) ^ m := by
  have hb0 : InBalls ρ |(0 : ℝ)| ζ := fun b => by simpa using hρ
  have hc : Tendsto (fun l => H l ζ) (𝓝[>] 0) (𝓝 (H 0 ζ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (h.diff 0 ζ hb0).continuousAt.tendsto
  refine le_of_tendsto hc.abs ?_
  have hpos : 0 < ρ / (1 + ‖ζ‖) := div_pos hρ (by linarith [norm_nonneg ζ])
  filter_upwards [Ioc_mem_nhdsGT (lt_min hl₁ (half_pos hpos))] with l hl
  refine h.bound l ζ hl.1 (hl.2.trans (min_le_left _ _)) (inBalls_of_norm hl.1.le ?_)
  have h1 : l ≤ ρ / (1 + ‖ζ‖) / 2 := hl.2.trans (min_le_right _ _)
  have h2 : l < ρ / (1 + ‖ζ‖) := by linarith
  rw [lt_div_iff₀ (by linarith [norm_nonneg ζ])] at h2
  nlinarith [norm_nonneg ζ, hl.1]
private theorem IsTempered.mul {ρ l₁ K K' : ℝ} {m m' : ℕ} {H H' : ℝ → BondVars ι → ℝ}
    (h : IsTempered ρ l₁ K m H) (h' : IsTempered ρ l₁ K' m' H') (hK : 0 ≤ K) (hK' : 0 ≤ K') :
    IsTempered ρ l₁ (2 * K * K') (m + m') fun l ζ => H l ζ * H' l ζ where
  diff l ζ hb := (h.diff l ζ hb).mul (h'.diff l ζ hb)
  bound l ζ h0 h1 hb := by
    have a := h.bound l ζ h0 h1 hb
    have b := h'.bound l ζ h0 h1 hb
    rw [abs_mul]
    have hp : 0 ≤ (1 + ‖ζ‖) ^ m := by positivity
    have hp' : 0 ≤ (1 + ‖ζ‖) ^ m' := by positivity
    calc _ ≤ (K * (1 + ‖ζ‖) ^ m) * (K' * (1 + ‖ζ‖) ^ m') :=
          mul_le_mul a b (abs_nonneg _) (by positivity)
      _ = K * K' * (1 + ‖ζ‖) ^ (m + m') := by rw [pow_add]; ring
      _ ≤ 2 * K * K' * (1 + ‖ζ‖) ^ (m + m') := by
          have : 0 ≤ K * K' * (1 + ‖ζ‖) ^ (m + m') := by positivity
          nlinarith
  slope l ζ h0 h1 hb := by
    have hl' : InBalls ρ |l| ζ := by rwa [abs_of_pos h0]
    have a := h.bound l ζ h0 h1 hb
    have b := h'.bound l ζ h0 h1 hb
    have a' := h.slope l ζ h0 h1 hb
    have b' := h'.slope l ζ h0 h1 hb
    have e : deriv (fun l' => H l' ζ * H' l' ζ) l =
        deriv (fun l' => H l' ζ) l * H' l ζ + H l ζ * deriv (fun l' => H' l' ζ) l :=
      deriv_fun_mul (h.diff l ζ hl') (h'.diff l ζ hl')
    rw [e]
    have hp : 0 ≤ K * (1 + ‖ζ‖) ^ m := by positivity
    have hp' : 0 ≤ K' * (1 + ‖ζ‖) ^ m' := by positivity
    calc _ ≤ |deriv (fun l' => H l' ζ) l * H' l ζ| + |H l ζ * deriv (fun l' => H' l' ζ) l| := abs_add_le _ _
      _ ≤ (K * (1 + ‖ζ‖) ^ m) * (K' * (1 + ‖ζ‖) ^ m') + (K * (1 + ‖ζ‖) ^ m) * (K' * (1 + ‖ζ‖) ^ m') := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul a' b (abs_nonneg _) hp) (mul_le_mul a b' (abs_nonneg _) hp)
      _ = 2 * K * K' * (1 + ‖ζ‖) ^ (m + m') := by rw [pow_add]; ring
  even l ζ := by rw [h.even, h'.even]
  cont l h0 h1 := (h.cont l h0 h1).mul (h'.cont l h0 h1)
private theorem IsTempered.mono {ρ l₁ K K' : ℝ} {m m' : ℕ} {H : ℝ → BondVars ι → ℝ} (h : IsTempered ρ l₁ K m H)
    (hK : K ≤ K') (hm : m ≤ m') (hK0 : 0 ≤ K) : IsTempered ρ l₁ K' m' H where
  diff := h.diff
  bound l ζ h0 h1 hb := (h.bound l ζ h0 h1 hb).trans
    (mul_le_mul hK (one_add_norm_pow_le_pow ζ hm) (by positivity) (hK0.trans hK))
  slope l ζ h0 h1 hb := (h.slope l ζ h0 h1 hb).trans
    (mul_le_mul hK (one_add_norm_pow_le_pow ζ hm) (by positivity) (hK0.trans hK))
  even := h.even
  cont := h.cont
private theorem IsTempered.add {ρ l₁ K K' : ℝ} {m m' : ℕ} {H H' : ℝ → BondVars ι → ℝ}
    (h : IsTempered ρ l₁ K m H) (h' : IsTempered ρ l₁ K' m' H') (hK : 0 ≤ K) (hK' : 0 ≤ K') :
    IsTempered ρ l₁ (K + K') (max m m') fun l ζ => H l ζ + H' l ζ where
  diff l ζ hb := (h.diff l ζ hb).add (h'.diff l ζ hb)
  bound l ζ h0 h1 hb := by
    have a := (h.mono (le_refl K) (le_max_left m m') hK).bound l ζ h0 h1 hb
    have b := (h'.mono (le_refl K') (le_max_right m m') hK').bound l ζ h0 h1 hb
    calc _ ≤ |H l ζ| + |H' l ζ| := abs_add_le _ _
      _ ≤ _ := by rw [add_mul]; exact add_le_add a b
  slope l ζ h0 h1 hb := by
    have hl' : InBalls ρ |l| ζ := by rwa [abs_of_pos h0]
    have a := (h.mono (le_refl K) (le_max_left m m') hK).slope l ζ h0 h1 hb
    have b := (h'.mono (le_refl K') (le_max_right m m') hK').slope l ζ h0 h1 hb
    have e : deriv (fun l' => H l' ζ + H' l' ζ) l = deriv (fun l' => H l' ζ) l + deriv (fun l' => H' l' ζ) l :=
      deriv_fun_add (h.diff l ζ hl') (h'.diff l ζ hl')
    rw [e]
    calc _ ≤ |deriv (fun l' => H l' ζ) l| + |deriv (fun l' => H' l' ζ) l| := abs_add_le _ _
      _ ≤ _ := by rw [add_mul]; exact add_le_add a b
  even l ζ := by rw [h.even, h'.even]
  cont l h0 h1 := (h.cont l h0 h1).add (h'.cont l h0 h1)
private theorem isTempered_const (ρ l₁ a : ℝ) : IsTempered (ι := ι) ρ l₁ |a| 0 fun _ _ => a where
  diff _ _ _ := differentiableAt_const _
  bound _ _ _ _ _ := by simp
  slope _ ζ _ _ _ := by simp
  even _ _ := rfl
  cont _ _ _ := continuousOn_const
private def Tempered (ρ l₁ : ℝ) (H : ℝ → BondVars ι → ℝ) : Prop :=
  ∃ (K : ℝ) (m : ℕ), 0 ≤ K ∧ IsTempered ρ l₁ K m H
private theorem Tempered.mul {ρ l₁ : ℝ} {H H' : ℝ → BondVars ι → ℝ} (h : Tempered ρ l₁ H) (h' : Tempered ρ l₁ H') :
    Tempered ρ l₁ fun l ζ => H l ζ * H' l ζ := by
  obtain ⟨K, m, hK, g⟩ := h
  obtain ⟨K', m', hK', g'⟩ := h'
  exact ⟨2 * K * K', m + m', by positivity, g.mul g' hK hK'⟩
private theorem Tempered.add {ρ l₁ : ℝ} {H H' : ℝ → BondVars ι → ℝ} (h : Tempered ρ l₁ H) (h' : Tempered ρ l₁ H') :
    Tempered ρ l₁ fun l ζ => H l ζ + H' l ζ := by
  obtain ⟨K, m, hK, g⟩ := h
  obtain ⟨K', m', hK', g'⟩ := h'
  exact ⟨K + K', max m m', by positivity, g.add g' hK hK'⟩
private theorem tempered_const (ρ l₁ a : ℝ) : Tempered (ι := ι) ρ l₁ fun _ _ => a :=
  ⟨|a|, 0, abs_nonneg _, isTempered_const ρ l₁ a⟩
private theorem Tempered.prod {α : Type} (s : Finset α) {ρ l₁ : ℝ} {H : α → ℝ → BondVars ι → ℝ}
    (h : ∀ i ∈ s, Tempered ρ l₁ (H i)) : Tempered ρ l₁ fun l ζ => ∏ i ∈ s, H i l ζ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tempered_const ρ l₁ 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end
section
variable {ι : Type} [Fintype ι]
private def radialCutoff (r : ℝ → ℝ) (l : ℝ) (ζ : BondVars ι) : ℝ := ∏ b, r (|l| * ‖ζ b‖)
private structure IsCutoffProfile (ρ : ℝ) (r : ℝ → ℝ) : Prop where
  one : ∀ u, 0 ≤ u → u ≤ 5 * ρ / 8 → r u = 1
  zero : ∀ u, ρ ≤ u → r u = 0
  nonneg : ∀ u, 0 ≤ u → 0 ≤ r u
  le_one : ∀ u, 0 ≤ u → r u ≤ 1
  cont : ContinuousOn r (Ico 0 ρ)
private theorem radialCutoff_eq_zero {ρ l : ℝ} {r : ℝ → ℝ} (hr : IsCutoffProfile ρ r) {ζ : BondVars ι} (hl : 0 ≤ l)
    (h : ¬ InBalls ρ l ζ) : radialCutoff r l ζ = 0 := by
  unfold InBalls at h
  push Not at h
  obtain ⟨b, hb⟩ := h
  refine Finset.prod_eq_zero (Finset.mem_univ b) (hr.zero _ ?_)
  rwa [abs_of_nonneg hl]
private theorem radialCutoff_nonneg {ρ l : ℝ} {r : ℝ → ℝ} (hr : IsCutoffProfile ρ r) (ζ : BondVars ι) :
    0 ≤ radialCutoff r l ζ :=
  Finset.prod_nonneg fun b _ => hr.nonneg _ (by positivity)
private theorem radialCutoff_le_one {ρ l : ℝ} {r : ℝ → ℝ} (hr : IsCutoffProfile ρ r) (ζ : BondVars ι) :
    radialCutoff r l ζ ≤ 1 :=
  Finset.prod_le_one (fun b _ => hr.nonneg _ (by positivity)) fun b _ => hr.le_one _ (by positivity)
private theorem radialCutoff_eq_one {ρ l : ℝ} {r : ℝ → ℝ} (hr : IsCutoffProfile ρ r) {ζ : BondVars ι}
    (h : |l| * ‖ζ‖ ≤ 5 * ρ / 8) : radialCutoff r l ζ = 1 := by
  refine Finset.prod_eq_one fun b _ => hr.one _ (by positivity) ?_
  exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm ζ b) (abs_nonneg _)).trans h
private theorem isOpen_inBalls {ρ l : ℝ} : IsOpen {ζ : BondVars ι | InBalls ρ l ζ} := by
  have : {ζ : BondVars ι | InBalls ρ l ζ} = ⋂ b, {ζ : BondVars ι | l * ‖ζ b‖ < ρ} := by
    ext ζ
    simp [InBalls]
  rw [this]
  exact isOpen_iInter_of_finite fun b =>
    isOpen_lt (continuous_const.mul (continuous_norm.comp (continuous_apply b))) continuous_const
private theorem radialCutoff_continuousOn {ρ l : ℝ} {r : ℝ → ℝ} (hr : IsCutoffProfile ρ r) (hl : 0 ≤ l) :
    ContinuousOn (radialCutoff (ι := ι) r l) {ζ | InBalls ρ l ζ} := by
  unfold radialCutoff
  refine continuousOn_finsetProd _ fun b _ => ?_
  refine hr.cont.comp (by fun_prop) fun ζ hζ => ?_
  refine ⟨by positivity, ?_⟩
  rw [abs_of_nonneg hl]
  exact hζ b
private def weightedIntegrand (r : ℝ → ℝ) (u H : ℝ → BondVars ι → ℝ) (l : ℝ) (ζ : BondVars ι) : ℝ :=
  H l ζ * (radialCutoff r l ζ * Real.exp (-u l ζ))
variable {ρ l₁ K Ku c C : ℝ} {m mu : ℕ} {r : ℝ → ℝ} {u H : ℝ → BondVars ι → ℝ}
private def gaussianTail (c C : ℝ) (n : ℕ) (ζ : BondVars ι) : ℝ :=
  (1 + ‖ζ‖) ^ n * Real.exp (-(c * ‖ζ‖ ^ 2) + C * ‖ζ‖)
private theorem exp_neg_le_of_lower_bound {l : ℝ} {ζ : BondVars ι}
    (hf : c * ‖ζ‖ ^ 2 - C * ‖ζ‖ ≤ u l ζ) : Real.exp (-u l ζ) ≤ Real.exp (-(c * ‖ζ‖ ^ 2) + C * ‖ζ‖) :=
  Real.exp_le_exp.2 (by linarith)
private theorem weightedIntegrand_abs_le (hρ : 0 < ρ) (hl₁ : 0 < l₁) (hr : IsCutoffProfile ρ r)
    (hH : IsTempered ρ l₁ K m H) (hK : 0 ≤ K)
    (hf : ∀ l ζ, 0 ≤ l → l ≤ l₁ → InBalls ρ l ζ → c * ‖ζ‖ ^ 2 - C * ‖ζ‖ ≤ u l ζ) {l : ℝ} (h0 : 0 ≤ l)
    (h1 : l ≤ l₁) (ζ : BondVars ι) : |weightedIntegrand r u H l ζ| ≤ K * gaussianTail c C m ζ := by
  by_cases hb : InBalls ρ l ζ
  · have hH' : |H l ζ| ≤ K * (1 + ‖ζ‖) ^ m := by
      rcases h0.eq_or_lt with rfl | h0'
      · exact hH.bound_zero hρ hl₁ ζ
      · exact hH.bound l ζ h0' h1 hb
    have he := exp_neg_le_of_lower_bound (hf l ζ h0 h1 hb)
    have hw : radialCutoff r l ζ * Real.exp (-u l ζ) ≤ Real.exp (-(c * ‖ζ‖ ^ 2) + C * ‖ζ‖) := by
      have := mul_le_mul (radialCutoff_le_one (l := l) hr ζ) he (Real.exp_pos _).le zero_le_one
      linarith
    have hw0 : 0 ≤ radialCutoff r l ζ * Real.exp (-u l ζ) :=
      mul_nonneg (radialCutoff_nonneg hr ζ) (Real.exp_pos _).le
    unfold weightedIntegrand gaussianTail
    rw [abs_mul, abs_of_nonneg hw0]
    calc _ ≤ (K * (1 + ‖ζ‖) ^ m) * Real.exp (-(c * ‖ζ‖ ^ 2) + C * ‖ζ‖) := mul_le_mul hH' hw hw0 (by positivity)
      _ = _ := by ring
  · unfold weightedIntegrand
    rw [radialCutoff_eq_zero hr h0 hb]
    simp only [zero_mul, mul_zero, abs_zero]
    unfold gaussianTail
    positivity
private theorem weightedIntegrand_sub_abs_le (hρ : 0 < ρ) (hl₁ : 0 < l₁) (hr : IsCutoffProfile ρ r)
    (hH : IsTempered ρ l₁ K m H) (hK : 0 ≤ K) (hu : IsTempered ρ l₁ Ku mu u) (hKu : 0 ≤ Ku)
    (hf : ∀ l ζ, 0 ≤ l → l ≤ l₁ → InBalls ρ l ζ → c * ‖ζ‖ ^ 2 - C * ‖ζ‖ ≤ u l ζ) {l : ℝ} (h0 : 0 < l)
    (h1 : l ≤ l₁) (ζ : BondVars ι) : |weightedIntegrand r u H l ζ - weightedIntegrand r u H 0 ζ| ≤
      l * ((K + K * Ku + 16 * K / (5 * ρ)) * gaussianTail c C (m + mu + 1) ζ) := by
  have hG : 0 < Real.exp (-(c * ‖ζ‖ ^ 2) + C * ‖ζ‖) := Real.exp_pos _
  by_cases hc : l * ‖ζ‖ ≤ 5 * ρ / 8
  · have hin : ∀ s ∈ Icc 0 l, InBalls ρ |s| ζ ∧ radialCutoff r s ζ = 1 := by
      intro s hs
      have hs' : |s| = s := abs_of_nonneg hs.1
      have h2 : |s| * ‖ζ‖ ≤ 5 * ρ / 8 := by
        rw [hs']
        exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)).trans hc
      exact ⟨inBalls_of_norm (abs_nonneg _) (by linarith), radialCutoff_eq_one hr h2⟩
    set φ : ℝ → ℝ := fun s => H s ζ * Real.exp (-u s ζ) with hφ
    have hφd : ∀ s ∈ Icc 0 l, DifferentiableAt ℝ φ s := fun s hs =>
      (hH.diff s ζ (hin s hs).1).mul ((hu.diff s ζ (hin s hs).1).fun_neg.exp)
    obtain ⟨s, hs, hs2⟩ := exists_deriv_eq_slope φ h0
      (fun x hx => (hφd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hφd x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt)
    have hsI : s ∈ Icc 0 l := ⟨hs.1.le, hs.2.le⟩
    have hs0 : 0 < s := hs.1
    have hsl : s ≤ l₁ := hs.2.le.trans h1
    have hbs : InBalls ρ s ζ := by simpa [abs_of_pos hs0] using (hin s hsI).1
    have dH := (hH.diff s ζ (hin s hsI).1).hasDerivAt
    have du := (hu.diff s ζ (hin s hsI).1).hasDerivAt
    have dφ : deriv φ s = deriv (fun l' => H l' ζ) s * Real.exp (-u s ζ) +
        H s ζ * (Real.exp (-u s ζ) * (-deriv (fun l' => u l' ζ) s)) :=
      (dH.mul du.fun_neg.exp).deriv
    have he := exp_neg_le_of_lower_bound (hf s ζ hs0.le hsl hbs)
    have a := hH.bound s ζ hs0 hsl hbs
    have a' := hH.slope s ζ hs0 hsl hbs
    have b' := hu.slope s ζ hs0 hsl hbs
    have he0 := (Real.exp_pos (-u s ζ)).le
    have hP : (1 + ‖ζ‖) ^ m * (1 + ‖ζ‖) ^ mu ≤ (1 + ‖ζ‖) ^ (m + mu + 1) := by
      rw [← pow_add]
      exact one_add_norm_pow_le_pow ζ (by omega)
    have hP' : (1 + ‖ζ‖) ^ m ≤ (1 + ‖ζ‖) ^ (m + mu + 1) := one_add_norm_pow_le_pow ζ (by omega)
    have bd : |deriv φ s| ≤ (K + K * Ku + 16 * K / (5 * ρ)) * gaussianTail c C (m + mu + 1) ζ := by
      rw [dφ]
      have t1 : |deriv (fun l' => H l' ζ) s * Real.exp (-u s ζ)| ≤
          K * gaussianTail c C (m + mu + 1) ζ := by
        rw [abs_mul, abs_of_nonneg he0]
        unfold gaussianTail
        rw [← mul_assoc]
        exact mul_le_mul (a'.trans (mul_le_mul_of_nonneg_left hP' hK)) he he0 (by positivity)
      have t2 : |H s ζ * (Real.exp (-u s ζ) * (-deriv (fun l' => u l' ζ) s))| ≤
          K * Ku * gaussianTail c C (m + mu + 1) ζ := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg he0]
        have : |H s ζ| * |deriv (fun l' => u l' ζ) s| ≤ K * Ku * (1 + ‖ζ‖) ^ (m + mu + 1) := by
          calc _ ≤ (K * (1 + ‖ζ‖) ^ m) * (Ku * (1 + ‖ζ‖) ^ mu) :=
                mul_le_mul a b' (abs_nonneg _) (by positivity)
            _ = K * Ku * ((1 + ‖ζ‖) ^ m * (1 + ‖ζ‖) ^ mu) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
        unfold gaussianTail
        calc _ = (|H s ζ| * |deriv (fun l' => u l' ζ) s|) * Real.exp (-u s ζ) := by ring
          _ ≤ (K * Ku * (1 + ‖ζ‖) ^ (m + mu + 1)) * Real.exp (-(c * ‖ζ‖ ^ 2) + C * ‖ζ‖) :=
              mul_le_mul this he he0 (by positivity)
          _ = _ := by ring
      have ht : 0 ≤ gaussianTail c C (m + mu + 1) ζ := by unfold gaussianTail; positivity
      have h5 : 0 ≤ 16 * K / (5 * ρ) * gaussianTail c C (m + mu + 1) ζ := by positivity
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ K * gaussianTail c C (m + mu + 1) ζ + K * Ku * gaussianTail c C (m + mu + 1) ζ := add_le_add t1 t2
        _ ≤ _ := by
            rw [add_mul, add_mul]
            linarith
    have e1 : weightedIntegrand r u H l ζ = φ l := by
      simp [weightedIntegrand, hφ, (hin l ⟨h0.le, le_rfl⟩).2]
    have e2 : weightedIntegrand r u H 0 ζ = φ 0 := by
      simp [weightedIntegrand, hφ, (hin 0 ⟨le_rfl, h0.le⟩).2]
    rw [e1, e2]
    rw [hs2, sub_zero, abs_div, abs_of_pos h0, div_le_iff₀ h0] at bd
    linarith
  · push Not at hc
    have b1 := weightedIntegrand_abs_le hρ hl₁ hr hH hK hf h0.le h1 ζ
    have b2 := weightedIntegrand_abs_le hρ hl₁ hr hH hK hf le_rfl hl₁.le ζ
    have hx : 1 ≤ 8 / (5 * ρ) * (l * ‖ζ‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have ht0 : 0 ≤ K * gaussianTail c C m ζ := by unfold gaussianTail; positivity
    have hmono : (1 + ‖ζ‖) ^ m * ‖ζ‖ ≤ (1 + ‖ζ‖) ^ (m + mu + 1) := by
      calc _ ≤ (1 + ‖ζ‖) ^ m * (1 + ‖ζ‖) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (1 + ‖ζ‖) ^ (m + 1) := by rw [pow_succ]
        _ ≤ _ := one_add_norm_pow_le_pow ζ (by omega)
    have hstep : gaussianTail c C m ζ * ‖ζ‖ ≤ gaussianTail c C (m + mu + 1) ζ := by
      unfold gaussianTail
      calc _ = ((1 + ‖ζ‖) ^ m * ‖ζ‖) * Real.exp (-(c * ‖ζ‖ ^ 2) + C * ‖ζ‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hmono hG.le
    have ht1 : 0 ≤ gaussianTail c C (m + mu + 1) ζ := by unfold gaussianTail; positivity
    calc _ ≤ |weightedIntegrand r u H l ζ| + |weightedIntegrand r u H 0 ζ| := abs_sub _ _
      _ ≤ 2 * (K * gaussianTail c C m ζ) := by linarith
      _ ≤ 2 * (K * gaussianTail c C m ζ) * (8 / (5 * ρ) * (l * ‖ζ‖)) := le_mul_of_one_le_right (by positivity) hx
      _ = l * (16 * K / (5 * ρ) * (gaussianTail c C m ζ * ‖ζ‖)) := by
          field_simp
          ring
      _ ≤ l * (16 * K / (5 * ρ) * gaussianTail c C (m + mu + 1) ζ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep (by positivity)) h0.le
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ h0.le
          refine mul_le_mul_of_nonneg_right ?_ ht1
          have : 0 ≤ K * Ku := by positivity
          linarith
private theorem weightedIntegrand_aestronglyMeasurable (hr : IsCutoffProfile ρ r) (hH : IsTempered ρ l₁ K m H)
    (hu : IsTempered ρ l₁ Ku mu u) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ l₁) :
    AEStronglyMeasurable (weightedIntegrand r u H l) volume := by
  have hc : ContinuousOn (weightedIntegrand r u H l) {ζ | InBalls ρ l ζ} :=
    (hH.cont l h0 h1).mul ((radialCutoff_continuousOn hr h0).mul ((hu.cont l h0 h1).neg.rexp))
  have e : weightedIntegrand r u H l = indicator {ζ | InBalls ρ l ζ} (weightedIntegrand r u H l) := by
    ext ζ
    by_cases hb : InBalls ρ l ζ
    · simp [indicator, hb]
    · simp only [indicator, Set.mem_ofPred_eq, hb, if_false]
      simp [weightedIntegrand, radialCutoff_eq_zero hr h0 hb]
  rw [e]
  exact (aestronglyMeasurable_indicator_iff isOpen_inBalls.measurableSet).2
    (hc.aestronglyMeasurable isOpen_inBalls.measurableSet)
private theorem integrable_gaussianTail (hc : 0 < c) (n : ℕ) : Integrable (gaussianTail (ι := ι) c C n) volume :=
  integrable_one_add_norm_pow_mul_gaussian volume n C hc
private theorem weightedIntegrand_integrable (hρ : 0 < ρ) (hl₁ : 0 < l₁) (hr : IsCutoffProfile ρ r)
    (hH : IsTempered ρ l₁ K m H) (hK : 0 ≤ K) (hu : IsTempered ρ l₁ Ku mu u) (hc : 0 < c)
    (hf : ∀ l ζ, 0 ≤ l → l ≤ l₁ → InBalls ρ l ζ → c * ‖ζ‖ ^ 2 - C * ‖ζ‖ ≤ u l ζ) {l : ℝ} (h0 : 0 ≤ l)
    (h1 : l ≤ l₁) : Integrable (weightedIntegrand r u H l) volume :=
  Integrable.mono' ((integrable_gaussianTail hc m).const_mul K) (weightedIntegrand_aestronglyMeasurable hr hH hu h0 h1)
    (Eventually.of_forall fun ζ => weightedIntegrand_abs_le hρ hl₁ hr hH hK hf h0 h1 ζ)
private theorem weightedIntegrand_differentiableAt (hρ : 0 < ρ) (hr : IsCutoffProfile ρ r) (hH : IsTempered ρ l₁ K m H)
    (hu : IsTempered ρ l₁ Ku mu u) (ζ : BondVars ι) :
    DifferentiableAt ℝ (fun l => weightedIntegrand r u H l ζ) 0 := by
  have hb : InBalls ρ |(0 : ℝ)| ζ := fun b => by simpa using hρ
  have h1 : DifferentiableAt ℝ (fun l => H l ζ * Real.exp (-u l ζ)) 0 :=
    (hH.diff 0 ζ hb).mul ((hu.diff 0 ζ hb).fun_neg.exp)
  refine h1.congr_of_eventuallyEq ?_
  have hpos : 0 < 5 * ρ / 8 / (1 + ‖ζ‖) := div_pos (by positivity) (by linarith [norm_nonneg ζ])
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with l hl
  have h2 : |l| * ‖ζ‖ ≤ 5 * ρ / 8 := by
    have h3 : |l| < 5 * ρ / 8 / (1 + ‖ζ‖) := by simpa [Real.dist_eq] using hl
    rw [lt_div_iff₀ (by linarith [norm_nonneg ζ])] at h3
    nlinarith [norm_nonneg ζ, abs_nonneg l]
  simp [weightedIntegrand, radialCutoff_eq_one hr h2]
private theorem vanishingSlopeAt_weightedIntegral (hρ : 0 < ρ) (hl₁ : 0 < l₁) (hr : IsCutoffProfile ρ r)
    (hH : IsTempered ρ l₁ K m H) (hK : 0 ≤ K) (hu : IsTempered ρ l₁ Ku mu u) (hKu : 0 ≤ Ku) (hc : 0 < c)
    (hf : ∀ l ζ, 0 ≤ l → l ≤ l₁ → InBalls ρ l ζ → c * ‖ζ‖ ^ 2 - C * ‖ζ‖ ≤ u l ζ) :
    VanishingSlopeAt (fun l => ∫ ζ, weightedIntegrand r u H l ζ) (∫ ζ, weightedIntegrand r u H 0 ζ) := by
  refine vanishingSlopeAt_integral volume (weightedIntegrand r u H)
    (fun ζ => deriv (fun l => weightedIntegrand r u H l ζ) 0)
    (fun ζ => (K + K * Ku + 16 * K / (5 * ρ)) * gaussianTail c C (m + mu + 1) ζ) l₁ hl₁
    ((integrable_gaussianTail hc _).const_mul _)
    (weightedIntegrand_integrable hρ hl₁ hr hH hK hu hc hf le_rfl hl₁.le)
    (fun l h0 h1 => weightedIntegrand_aestronglyMeasurable hr hH hu h0.le h1)
    (fun ζ l h0 h1 => weightedIntegrand_sub_abs_le hρ hl₁ hr hH hK hu hKu hf h0 h1 ζ)
    (fun ζ => (weightedIntegrand_differentiableAt hρ hr hH hu ζ).hasDerivAt)
    (fun ζ => Eventually.of_forall fun l => by simp [weightedIntegrand, radialCutoff, hH.even, hu.even])
    (by
      have h1 := Measure.integral_comp_smul (volume : Measure (BondVars ι))
        (fun ζ => deriv (fun l => weightedIntegrand r u H l ζ) 0) (-1 : ℝ)
      simpa using h1)
private theorem vanishingSlopeAt_weightedMean (hρ : 0 < ρ) (hl₁ : 0 < l₁) (hr : IsCutoffProfile ρ r)
    (hH : Tempered ρ l₁ H) (hu : Tempered ρ l₁ u) (hc : 0 < c)
    (hf : ∀ l ζ, 0 ≤ l → l ≤ l₁ → InBalls ρ l ζ → c * ‖ζ‖ ^ 2 - C * ‖ζ‖ ≤ u l ζ) :
    VanishingSlopeAt (fun l => (∫ ζ, weightedIntegrand r u H l ζ) / ∫ ζ, weightedIntegrand r u (fun _ _ => 1) l ζ)
      ((∫ ζ, weightedIntegrand r u H 0 ζ) / ∫ ζ, weightedIntegrand r u (fun _ _ => 1) 0 ζ) := by
  obtain ⟨K, m, hK, gH⟩ := hH
  obtain ⟨Ku, mu, hKu, gu⟩ := hu
  have g1 : IsTempered (ι := ι) ρ l₁ |1| 0 fun _ _ => (1 : ℝ) := isTempered_const ρ l₁ 1
  refine (vanishingSlopeAt_weightedIntegral hρ hl₁ hr gH hK gu hKu hc hf).div
    (vanishingSlopeAt_weightedIntegral hρ hl₁ hr g1 (abs_nonneg _) gu hKu hc hf) ?_
  have hi := weightedIntegrand_integrable hρ hl₁ hr g1 (abs_nonneg _) gu hc hf le_rfl hl₁.le
  have hpos : ∀ ζ : BondVars ι, 0 < weightedIntegrand r u (fun _ _ => 1) 0 ζ := by
    intro ζ
    have : radialCutoff r 0 ζ = 1 := radialCutoff_eq_one hr (by simpa using (by positivity : 0 ≤ 5 * ρ / 8))
    simp [weightedIntegrand, this, Real.exp_pos]
  refine ne_of_gt ?_
  rw [integral_pos_iff_support_of_nonneg (fun ζ => (hpos ζ).le) hi]
  have : Function.support (weightedIntegrand r u (fun _ _ => (1 : ℝ)) 0) = (univ : Set (BondVars ι)) := by
    ext ζ
    simp [Function.mem_support, (hpos ζ).ne']
  rw [this]
  exact isOpen_univ.measure_pos volume univ_nonempty
end
section
variable {ι : Type} [Fintype ι]
private theorem inBalls_eventually {ρ l : ℝ} {ζ : BondVars ι} (h : InBalls ρ |l| ζ) :
    ∀ᶠ l' in 𝓝 l, InBalls ρ |l'| ζ := by
  refine eventually_all.2 fun b => ?_
  have hc : ContinuousAt (fun l' : ℝ => |l'| * ‖ζ b‖) l := by fun_prop
  exact hc.eventually_lt continuousAt_const (h b)
private theorem Tempered.congr {ρ l₁ : ℝ} {H H' : ℝ → BondVars ι → ℝ} (h : Tempered ρ l₁ H)
    (e : ∀ l ζ, InBalls ρ |l| ζ → H' l ζ = H l ζ) (ev : ∀ l ζ, H' (-l) (-ζ) = H' l ζ) : Tempered ρ l₁ H' := by
  obtain ⟨K, m, hK, g⟩ := h
  have hev : ∀ l ζ, InBalls ρ |l| ζ → (fun l' => H' l' ζ) =ᶠ[𝓝 l] fun l' => H l' ζ := fun l ζ hb => by
    filter_upwards [inBalls_eventually hb] with l' hl' using e l' ζ hl'
  have habs : ∀ (l : ℝ) (ζ : BondVars ι), 0 < l → InBalls ρ l ζ → InBalls ρ |l| ζ := fun l ζ h0 hb => by
    rwa [abs_of_pos h0]
  refine ⟨K, m, hK, ?_, ?_, ?_, ev, ?_⟩
  · intro l ζ hb
    exact (g.diff l ζ hb).congr_of_eventuallyEq (hev l ζ hb)
  · intro l ζ h0 h1 hb
    rw [e l ζ (habs l ζ h0 hb)]
    exact g.bound l ζ h0 h1 hb
  · intro l ζ h0 h1 hb
    rw [(hev l ζ (habs l ζ h0 hb)).deriv_eq]
    exact g.slope l ζ h0 h1 hb
  · intro l h0 h1
    refine (g.cont l h0 h1).congr fun ζ hζ => e l ζ ?_
    rw [abs_of_nonneg h0]
    exact hζ
private theorem Tempered.neg {ρ l₁ : ℝ} {H : ℝ → BondVars ι → ℝ} (h : Tempered ρ l₁ H) :
    Tempered ρ l₁ fun l ζ => -H l ζ := by
  refine (h.mul (tempered_const ρ l₁ (-1))).congr (fun l ζ _ => by ring) fun l ζ => ?_
  obtain ⟨K, m, _, g⟩ := h
  rw [g.even]
private theorem Tempered.atOrigin {ρ l₁ : ℝ} {H : ℝ → BondVars ι → ℝ} (h : Tempered ρ l₁ H) (hρ : 0 < ρ) :
    Tempered ρ l₁ fun l (_ : BondVars ι) => H l 0 := by
  obtain ⟨K, m, hK, g⟩ := h
  have hz : ∀ l : ℝ, InBalls ρ l (0 : BondVars ι) := fun l b => by simpa using hρ
  refine ⟨K, m, hK, ?_, ?_, ?_, ?_, ?_⟩
  · intro l ζ _
    exact g.diff l 0 (hz _)
  · intro l ζ h0 h1 _
    refine (g.bound l 0 h0 h1 (hz _)).trans (mul_le_mul_of_nonneg_left ?_ hK)
    simpa using one_le_one_add_norm_pow ζ m
  · intro l ζ h0 h1 _
    refine (g.slope l 0 h0 h1 (hz _)).trans (mul_le_mul_of_nonneg_left ?_ hK)
    simpa using one_le_one_add_norm_pow ζ m
  · intro l ζ
    have := g.even l 0
    simpa using this
  · intro l _ _
    exact continuousOn_const
private theorem differentiableAt_iteratedFDeriv_param (hA : DerivAlongRulesHold) {k : ℕ} (hk : k ≤ 5)
    (Φ : ℝ × (Fin k → ℝ) → ℝ) (l : ℝ) (h : ∀ᶠ l' in 𝓝 l, ContDiffAt ℝ 6 Φ (l', 0)) :
    DifferentiableAt ℝ (fun l' => iteratedFDeriv ℝ k (fun τ => Φ (l', τ)) 0 (fun i => Pi.single i 1)) l := by
  set m : Fin k → Fin k → ℝ := fun i => Pi.single i 1 with hm
  set A : (Fin k → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) := ContinuousLinearMap.inr ℝ ℝ (Fin k → ℝ) with hAdef
  set L : List (ℝ × (Fin k → ℝ)) := (List.ofFn m).map A with hL
  have hlen : L.length = k := by simp [hL]
  have heq : ∀ l', ContDiffAt ℝ 6 Φ (l', 0) →
      iteratedFDeriv ℝ k (fun τ => Φ (l', τ)) 0 m = derivAlong Φ L (l', 0) := by
    intro l' hc
    have h1 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ => Φ (l', τ)) 0 := by
      have h2 : ContDiffAt ℝ (k : WithTop ℕ∞) Φ (l', 0) := hc.of_le (by exact_mod_cast (by omega : k ≤ 6))
      have h3 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => ((l', τ) : ℝ × (Fin k → ℝ))) 0 := by fun_prop
      exact ContDiffAt.comp (0 : Fin k → ℝ) (g := Φ) h2 h3
    rw [(hA.1 (Fin k → ℝ) ℝ).iteratedFDeriv_eq _ 0 k m h1]
    have h4 := hA.2 (ℝ × (Fin k → ℝ)) (Fin k → ℝ) ℝ Φ A (l', 0) 0 (List.ofFn m)
      (by
        have : ((l', 0) : ℝ × (Fin k → ℝ)) + A 0 = (l', 0) := by simp
        rw [this]
        refine hc.of_le ?_
        simp only [List.length_ofFn]
        exact_mod_cast (by omega : k ≤ 6))
    have h5 : (fun t' : Fin k → ℝ => Φ (((l', 0) : ℝ × (Fin k → ℝ)) + A t')) = fun τ => Φ (l', τ) := by
      funext t'
      simp [hAdef]
    rw [h5] at h4
    rw [h4]
    simp [hL]
  have hg : ContDiffAt ℝ ((1 + L.length : ℕ) : WithTop ℕ∞) Φ (l, 0) := by
    refine (h.self_of_nhds).of_le ?_
    rw [hlen]
    exact_mod_cast (by omega : 1 + k ≤ 6)
  have h6 := (hA.1 (ℝ × (Fin k → ℝ)) ℝ).contDiffAt Φ (l, 0) 1 L hg
  have h7 : DifferentiableAt ℝ (derivAlong Φ L) (l, 0) := h6.differentiableAt (by norm_num)
  have h8 : DifferentiableAt ℝ (fun l' : ℝ => derivAlong Φ L (l', 0)) l :=
    DifferentiableAt.comp (f := fun l' : ℝ => ((l', 0) : ℝ × (Fin k → ℝ))) l h7 (by fun_prop)
  refine h8.congr_of_eventuallyEq ?_
  filter_upwards [h] with l' hl' using heq l' hl'
variable {F : BlockFrame}
private theorem one_add_localWeight_le {κ : ℝ} (hκ : 0 ≤ κ) (Y : F.Cell) (ζ : StepVariable (finiteCells F)) :
    1 + localWeight κ Y ζ ≤ (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) * (1 + ‖ζ‖) := by
  have h1 : localWeight κ Y ζ ≤ (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * ‖ζ‖ := by
    unfold localWeight
    calc _ ≤ ∑ _b : ↥(chordBonds (finiteCells F)), ‖ζ‖ := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h2 : Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ 1 :=
            Real.exp_le_one_iff.2 (by
              have : 0 ≤ 2 ^ 4 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ) := by positivity
              linarith)
          calc _ ≤ 1 * ‖ζ b‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
            _ ≤ ‖ζ‖ := by simpa using norm_le_pi_norm ζ b
      _ = _ := by simp
  nlinarith [norm_nonneg ζ]
private structure IsTameObservable (ρ l₁ : ℝ) (V : F.GaugeField F.top)
    (O : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) : Prop where
  even : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)) (V' : F.GaugeField F.top), O (-l) (-ζ) V' = O l ζ V'
  smooth : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), InBalls ρ |l| ζ →
    ContDiffAt ℝ 6 (fun q : ℝ × (Fin k → ℝ) => O q.1 ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) V)) (l, 0)
  tempered : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
    AreUnitVectors X → Tempered ρ l₁ fun l ζ => bondDeriv (O l ζ) V c X
private theorem isTameObservable_of_isSmoothObservable (hA : DerivAlongRulesHold) {κ ρ l₁ l₂ K : ℝ} {Y : F.Cell}
    {V : F.GaugeField F.top} {O : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (h : IsSmoothObservable κ ρ l₂ K Y V O) (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hl : l₁ ≤ l₂) :
    IsTameObservable ρ l₁ V O := by
  have hsm : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), InBalls ρ |l| ζ →
      ContDiffAt ℝ 6 (fun q : ℝ × (Fin k → ℝ) => O q.1 ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) V)) (l, 0) := by
    intro l ζ k c X hb
    have h1 := h.contDiffAt l ζ k c X hb
    have h2 : ContDiffAt ℝ 6 (fun q : ℝ × (Fin k → ℝ) =>
        (((q.1, ζ), q.2) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ))) (l, 0) := by fun_prop
    exact ContDiffAt.comp ((l, 0) : ℝ × (Fin k → ℝ)) h1 h2
  refine ⟨h.even, hsm, fun k c X hk hX => ?_⟩
  set n : ℝ := (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) with hn
  have hbd : ∀ (i : ℕ) (l : ℝ) (ζ : StepVariable (finiteCells F)), IsControlledOrder k i → 0 < l → l ≤ l₁ →
      InBalls ρ l ζ → |scaleDeriv O V c X i ζ l| ≤ K * (1 + n) ^ 7 * (1 + ‖ζ‖) ^ 7 := by
    intro i l ζ ho h0 h1 hb
    have h2 := h.deriv_le k i c X l ζ ho hX h0 (h1.trans hl) hb
    have h3 : Real.exp (-(2 ^ 4 * κ * (bondSpan Y c : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : 0 ≤ 2 ^ 4 * κ * (bondSpan Y c : ℝ) := by positivity
        linarith)
    have h4 : 0 ≤ 1 + localWeight κ Y ζ := by
      have : 0 ≤ localWeight κ Y ζ := Finset.sum_nonneg fun b _ => by positivity
      linarith
    have h5 : (1 + localWeight κ Y ζ) ^ 7 ≤ (1 + n) ^ 7 * (1 + ‖ζ‖) ^ 7 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ h4 (one_add_localWeight_le hκ Y ζ) 7
    calc _ ≤ K * (1 + localWeight κ Y ζ) ^ 7 * Real.exp (-(2 ^ 4 * κ * (bondSpan Y c : ℝ))) := h2
      _ ≤ K * (1 + localWeight κ Y ζ) ^ 7 * 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K * (1 + localWeight κ Y ζ) ^ 7 := mul_one _
      _ ≤ K * ((1 + n) ^ 7 * (1 + ‖ζ‖) ^ 7) := mul_le_mul_of_nonneg_left h5 hK
      _ = _ := by ring
  refine ⟨K * (1 + n) ^ 7, 7, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro l ζ hb
    refine differentiableAt_iteratedFDeriv_param hA (by omega)
      (fun q : ℝ × (Fin k → ℝ) => O q.1 ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) V)) l ?_
    filter_upwards [inBalls_eventually hb] with l' hl' using hsm l' ζ k c X hl'
  · intro l ζ h0 h1 hb
    have := hbd 0 l ζ (Or.inl ⟨hk, by norm_num⟩) h0 h1 hb
    simpa [scaleDeriv] using this
  · intro l ζ h0 h1 hb
    have := hbd 1 l ζ (Or.inl ⟨hk, by norm_num⟩) h0 h1 hb
    simpa [scaleDeriv, iteratedDeriv_one] using this
  · intro l ζ
    have : O (-l) (-ζ) = O l ζ := funext fun V' => h.even l ζ V'
    simp only [this]
  · intro l h0 h1 ζ₀ hζ₀
    have hlim := h.continuousOn k 0 c X (‖ζ₀‖ + 1) (Or.inl ⟨hk, by norm_num⟩)
    have hin : ((l, ζ₀) : ℝ × StepVariable (finiteCells F)) ∈ {q : ℝ × StepVariable (finiteCells F) |
        0 ≤ q.1 ∧ q.1 ≤ l₂ ∧ MemScaledBalls ρ q.1 q.2 ∧ ∀ b, ‖q.2 b‖ ≤ ‖ζ₀‖ + 1} :=
      ⟨h0, h1.trans hl, hζ₀, fun b => (norm_le_pi_norm ζ₀ b).trans (by linarith)⟩
    have h2 := hlim (l, ζ₀) hin
    have h3 : ContinuousWithinAt (fun ζ : StepVariable (finiteCells F) => scaleDeriv O V c X 0 ζ l)
        {ζ | InBalls ρ l ζ ∧ ∀ b, ‖ζ b‖ ≤ ‖ζ₀‖ + 1} ζ₀ :=
      ContinuousWithinAt.comp (t := {q : ℝ × StepVariable (finiteCells F) |
        0 ≤ q.1 ∧ q.1 ≤ l₂ ∧ MemScaledBalls ρ q.1 q.2 ∧ ∀ b, ‖q.2 b‖ ≤ ‖ζ₀‖ + 1})
        (g := fun q : ℝ × StepVariable (finiteCells F) => scaleDeriv O V c X 0 q.2 q.1)
        (f := fun ζ : StepVariable (finiteCells F) => (l, ζ)) h2
        (by fun_prop) (fun ζ hζ => ⟨h0, h1.trans hl, hζ.1, hζ.2⟩)
    have h4 : {ζ : StepVariable (finiteCells F) | InBalls ρ l ζ ∧ ∀ b, ‖ζ b‖ ≤ ‖ζ₀‖ + 1} ∈
        𝓝[{ζ | InBalls ρ l ζ}] ζ₀ := by
      have h5 : {ζ : StepVariable (finiteCells F) | ∀ b, ‖ζ b‖ ≤ ‖ζ₀‖ + 1} ∈ 𝓝 ζ₀ := by
        refine Filter.mem_of_superset (Metric.ball_mem_nhds ζ₀ one_pos) fun ζ hζ b => ?_
        have h6 : ‖ζ - ζ₀‖ < 1 := by simpa [dist_eq_norm] using hζ
        have h7 : ‖ζ‖ ≤ ‖ζ₀‖ + ‖ζ - ζ₀‖ := by
          have := norm_add_le ζ₀ (ζ - ζ₀)
          simpa using this
        exact (norm_le_pi_norm ζ b).trans (by linarith)
      exact Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds h5)
    have h8 := h3.mono_of_mem_nhdsWithin h4
    simpa [scaleDeriv, ContinuousWithinAt] using h8
end
section
variable {F : BlockFrame} {ρ l₁ : ℝ} {V : F.GaugeField F.top}
  {O O' : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
private theorem IsTameObservable.contDiffAt_param (h : IsTameObservable ρ l₁ V O) {l : ℝ}
    {ζ : StepVariable (finiteCells F)} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 6) (hb : InBalls ρ |l| ζ) :
    ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => O l ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 := by
  have h1 := (h.smooth l ζ k c X hb).of_le (m := (k : WithTop ℕ∞)) (by exact_mod_cast hk)
  have h2 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => ((l, τ) : ℝ × (Fin k → ℝ))) 0 := by fun_prop
  exact ContDiffAt.comp (g := fun q : ℝ × (Fin k → ℝ) => O q.1 ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) V))
    (0 : Fin k → ℝ) h1 h2
private theorem IsTameObservable.add (h : IsTameObservable ρ l₁ V O) (h' : IsTameObservable ρ l₁ V O') :
    IsTameObservable ρ l₁ V fun l ζ V' => O l ζ V' + O' l ζ V' := by
  refine ⟨fun l ζ V' => by rw [h.even, h'.even],
    fun l ζ k c X hb => (h.smooth l ζ k c X hb).add (h'.smooth l ζ k c X hb),
    fun k c X hk hX => ((h.tempered k c X hk hX).add (h'.tempered k c X hk hX)).congr (fun l ζ hb => ?_) fun l ζ => ?_⟩
  · have e := iteratedFDeriv_add_apply (𝕜 := ℝ) (x := (0 : Fin k → ℝ)) (h.contDiffAt_param c X (by omega) hb)
      (h'.contDiffAt_param c X (by omega) hb)
    exact congrArg (fun A => A fun i => (Pi.single i 1 : Fin k → ℝ)) e
  · simp only [h.even, h'.even]
private theorem IsTameObservable.const_mul (h : IsTameObservable ρ l₁ V O) (a : ℝ) :
    IsTameObservable ρ l₁ V fun l ζ V' => a * O l ζ V' := by
  refine ⟨fun l ζ V' => by rw [h.even], fun l ζ k c X hb => contDiffAt_const.mul (h.smooth l ζ k c X hb),
    fun k c X hk hX => ((tempered_const ρ l₁ a).mul (h.tempered k c X hk hX)).congr (fun l ζ hb => ?_) fun l ζ => ?_⟩
  · have e := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (x := (0 : Fin k → ℝ)) (a := a)
      (h.contDiffAt_param c X (by omega) hb)
    exact congrArg (fun A => A fun i => (Pi.single i 1 : Fin k → ℝ)) e
  · simp only [h.even]
private theorem isTameObservable_of_fixed (q : StepVariable (finiteCells F) → ℝ) (hq : Continuous q)
    (he : ∀ ζ, q (-ζ) = q ζ) {K : ℝ} {m : ℕ} (hK : 0 ≤ K) (hb : ∀ ζ, |q ζ| ≤ K * (1 + ‖ζ‖) ^ m) :
    IsTameObservable ρ l₁ V fun _ ζ _ => q ζ := by
  refine ⟨fun l ζ V' => he ζ, fun l ζ k c X _ => contDiffAt_const, fun k c X hk hX => ?_⟩
  by_cases hk0 : k = 0
  · subst hk0
    have h1 : Tempered (ι := ↥(chordBonds (finiteCells F))) ρ l₁ fun _ ζ => q ζ := by
      refine ⟨K, m, hK, fun _ _ _ => differentiableAt_const _, fun _ ζ _ _ _ => hb ζ, fun l ζ _ _ _ => ?_,
        fun _ ζ => he ζ, fun _ _ _ => hq.continuousOn⟩
      simp only [deriv_const, abs_zero]
      positivity
    refine h1.congr (fun l ζ _ => ?_) fun l ζ => ?_
    · simp [bondDeriv]
    · simp [bondDeriv, he]
  · refine (tempered_const ρ l₁ 0).congr (fun l ζ _ => ?_) fun l ζ => ?_
    · simp [bondDeriv, iteratedFDeriv_const_of_ne hk0]
    · simp [bondDeriv, iteratedFDeriv_const_of_ne hk0]
private theorem isTameObservable_zero : IsTameObservable (F := F) ρ l₁ V fun _ _ _ => 0 :=
  isTameObservable_of_fixed (fun _ => 0) continuous_const (fun _ => rfl) le_rfl (K := 0) (m := 0) (by simp)
private theorem IsTameObservable.sum {α : Type} (s : Finset α)
    {O : α → ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (h : ∀ i ∈ s, IsTameObservable ρ l₁ V (O i)) : IsTameObservable ρ l₁ V fun l ζ V' => ∑ i ∈ s, O i l ζ V' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTameObservable_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
private theorem isTameObservable_sum_sq (a : ℝ) (P : ↥(chordBonds (finiteCells F)) → Prop) [DecidablePred P] :
    IsTameObservable ρ l₁ V fun _ ζ _ => a * ∑ b : ↥(chordBonds (finiteCells F)), if P b then ‖ζ b‖ ^ 2 else 0 := by
  refine isTameObservable_of_fixed
    (fun ζ => a * ∑ b : ↥(chordBonds (finiteCells F)), if P b then ‖ζ b‖ ^ 2 else 0) ?_ ?_
    (K := |a| * (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ)) (m := 2) (by positivity) ?_
  · refine continuous_const.mul (continuous_finsetSum _ fun b _ => ?_)
    by_cases hP : P b
    · simp only [hP, if_true]
      fun_prop
    · simp only [hP, if_false]
      exact continuous_const
  · intro ζ
    simp
  · intro ζ
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 : ∀ b : ↥(chordBonds (finiteCells F)), |if P b then ‖ζ b‖ ^ 2 else 0| ≤ (1 + ‖ζ‖) ^ 2 := by
      intro b
      have h2 : ‖ζ b‖ ^ 2 ≤ (1 + ‖ζ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm ζ b).trans (by linarith)) 2
      by_cases hP : P b
      · simp only [hP, if_true]
        rwa [abs_of_nonneg (by positivity)]
      · simp only [hP, if_false, abs_zero]
        positivity
    calc _ ≤ ∑ b : ↥(chordBonds (finiteCells F)), |if P b then ‖ζ b‖ ^ 2 else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : ↥(chordBonds (finiteCells F)), (1 + ‖ζ‖) ^ 2 := Finset.sum_le_sum fun b _ => h1 b
      _ = _ := by simp
variable {a ρA lam : ℝ} {f : LocalFamily}
private theorem isTameObservable_cellTerm (Y : F.Cell)
    (h : IsTameObservable ρ l₁ V fun l ζ V' => rescaledCellRemainder a ρA lam l Y V' ζ) :
    IsTameObservable ρ l₁ V fun l ζ V' => rescaledCellTerm a ρA l Y V' ζ := by
  have h1 := h.add (isTameObservable_sum_sq (lam / 2) fun b => enclosingCell b.1.1 = Y)
  refine (congrArg (IsTameObservable ρ l₁ V) ?_).mp h1
  funext l ζ V'
  simp [rescaledCellRemainder]
private theorem isTameObservable_exponent (hw : ∀ Y : F.Cell, Y ∈ finiteCells F)
    (hb : ∀ Y : F.Cell, IsTameObservable ρ l₁ V fun l ζ V' => rescaledCellRemainder a ρA lam l Y V' ζ)
    (hr : ∀ Y : F.Cell, IsTameObservable ρ l₁ V fun l ζ V' => rescaledCellExpansion a ρA f l Y V' ζ) (ν : ℝ) :
    IsTameObservable ρ l₁ V fun l ζ V' => rescaledExponent a ρA f ν l V' ζ := by
  have h1 := (IsTameObservable.sum (finiteCells F) fun Y _ => isTameObservable_cellTerm Y (hb Y)).add
    ((IsTameObservable.sum (finiteCells F) fun Y _ => hr Y).const_mul (-ν))
  refine (congrArg (IsTameObservable ρ l₁ V) ?_).mp h1
  funext l ζ V'
  classical
  have e : ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρA f l Y V' ζ =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρA 0 f y (l • ζ) V' := by
    unfold rescaledCellExpansion cellCentredExpansion
    convert Finset.sum_fiberwise_of_maps_to (s := sitesOfCells (finiteCells F) F.depth) (t := finiteCells F)
      (g := enclosingCell) (fun y _ => hw _) (fun y => centredExpansion true a ρA 0 f y (l • ζ) V') using 1
  rw [e]
  unfold rescaledExponent
  ring
private theorem isTameObservable_lawExponent (hw : ∀ Y : F.Cell, Y ∈ finiteCells F)
    (hb : ∀ Y : F.Cell, IsTameObservable ρ l₁ V fun l ζ V' => rescaledCellRemainder a ρA lam l Y V' ζ)
    (hr : ∀ Y : F.Cell, IsTameObservable ρ l₁ V fun l ζ V' => rescaledCellExpansion a ρA f l Y V' ζ) (law : StepLaw) :
    IsTameObservable ρ l₁ V fun l ζ V' => rescaledLawExponent a ρA lam f l V' law ζ := by
  cases law with
  | tilted ν => exact isTameObservable_exponent hw hb hr ν
  | interpolated τ =>
    have h1 := ((isTameObservable_exponent hw hb hr 0).const_mul τ).add
      ((isTameObservable_sum_sq (ρ := ρ) (l₁ := l₁) (V := V) ((1 - τ) * (lam / 2)) fun _ => True))
    refine (congrArg (IsTameObservable ρ l₁ V) ?_).mp h1
    funext l ζ V'
    simp [rescaledLawExponent, mul_assoc]
end
section
private theorem isCutoffProfile_of_isCutoff {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (h : IsCutoff ρ p) :
    IsCutoffProfile ρ (cutoffFactor ρ p) := by
  refine ⟨fun u h0 h1 => ?_, fun u h0 => ?_, fun u _ => ?_, fun u h0 => ?_, ?_⟩
  · have hu : u < ρ := by linarith
    simp [cutoffFactor, hu, h.vanish_small u h0 h1]
  · simp [cutoffFactor, not_lt.2 h0]
  · unfold cutoffFactor
    split_ifs
    · positivity
    · exact le_rfl
  · unfold cutoffFactor
    split_ifs with hu
    · refine Real.exp_le_one_iff.2 ?_
      by_cases h5 : u ≤ 5 * ρ / 8
      · rw [h.vanish_small u h0 h5]
        simp
      · push Not at h5
        have hu0 : 0 < u := by linarith
        have hb : 5 * ρ / 8 / u ≤ 1 := by
          rw [div_le_one hu0]
          exact h5.le
        have hb0 : 0 < 5 * ρ / 8 / u := by positivity
        have hc := h.convex.2 (show (0 : ℝ) ∈ Ico 0 ρ from ⟨le_rfl, hρ⟩) (show u ∈ Ico 0 ρ from ⟨h0, hu⟩)
          (show 0 ≤ 1 - 5 * ρ / 8 / u by linarith) hb0.le (by ring)
        have e : (1 - 5 * ρ / 8 / u) • (0 : ℝ) + (5 * ρ / 8 / u) • u = 5 * ρ / 8 := by
          simp only [smul_eq_mul, mul_zero, zero_add]
          field_simp
        rw [e, h.vanish_small _ (by positivity) le_rfl, h.vanish_small 0 le_rfl (by positivity)] at hc
        simp only [smul_eq_mul, mul_zero, zero_add] at hc
        have : 0 ≤ p u := nonneg_of_mul_nonneg_right hc hb0
        linarith
    · exact zero_le_one
  · have h1 : ContinuousOn (fun u => Real.exp (-p u)) (Ico 0 ρ) := h.smooth.continuousOn.neg.rexp
    refine h1.congr fun u hu => ?_
    simp [cutoffFactor, hu.2]
variable {F : BlockFrame}
private theorem bondDeriv_of_arity_zero {G : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top}
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private def centredLawExponent (a ρA lam : ℝ) (f : LocalFamily) (law : StepLaw) (V : F.GaugeField F.top) (l : ℝ)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  rescaledLawExponent a ρA lam f l V law ζ - rescaledLawExponent a ρA lam f l V law 0
private theorem cutoffWeight_smul (ρ : ℝ) (p : ℝ → ℝ) (l : ℝ) (ζ : StepVariable (finiteCells F)) :
    cutoffWeight ρ p (l • ζ) = radialCutoff (cutoffFactor ρ p) l ζ := by
  unfold cutoffWeight radialCutoff
  refine Finset.prod_congr rfl fun b _ => ?_
  simp [norm_smul]
private theorem rescaledMean_eq_ratio {ρ : ℝ} {p : ℝ → ℝ} (hr : IsCutoffProfile ρ (cutoffFactor ρ p))
    (a ρA lam : ℝ) (f : LocalFamily) (law : StepLaw) (V : F.GaugeField F.top) {l : ℝ} (hl : 0 < l)
    (H : StepVariable (finiteCells F) → ℝ)
    (hid : ∀ ζ : StepVariable (finiteCells F), MemScaledBalls ρ l ζ →
      stepLawExponent a ρA lam (l⁻¹ ^ 2) f V law (l • ζ) = rescaledLawExponent a ρA lam f l V law ζ) :
    rescaledMean a ρA ρ lam l p f law V H =
      (∫ ζ, weightedIntegrand (cutoffFactor ρ p) (centredLawExponent a ρA lam f law V) (fun _ => H) l ζ) /
        ∫ ζ, weightedIntegrand (cutoffFactor ρ p) (centredLawExponent a ρA lam f law V) (fun _ _ => 1) l ζ := by
  set Ψ := stepLawExponent a ρA lam (l⁻¹ ^ 2) f V law with hΨ
  set u := centredLawExponent a ρA lam f law V with hu
  set E : ℝ := Real.exp (-rescaledLawExponent a ρA lam f l V law 0) with hE
  set A : ℝ := |l ^ Module.finrank ℝ (StepVariable (finiteCells F))| * E with hA
  have hl0 : l ≠ 0 := ne_of_gt hl
  have key : ∀ g : StepVariable (finiteCells F) → ℝ,
      ∫ η, g (l⁻¹ • η) * (cutoffWeight ρ p η * Real.exp (-Ψ η)) =
        A * ∫ ζ, weightedIntegrand (cutoffFactor ρ p) u (fun _ => g) l ζ := by
    intro g
    obtain ⟨w, hw⟩ : ∃ w : StepVariable (finiteCells F) → ℝ,
        w = fun ζ => g ζ * (cutoffWeight ρ p (l • ζ) * Real.exp (-Ψ (l • ζ))) := ⟨_, rfl⟩
    have h1 : ∀ η : StepVariable (finiteCells F), g (l⁻¹ • η) * (cutoffWeight ρ p η * Real.exp (-Ψ η)) =
        w (l⁻¹ • η) := by
      intro η
      simp only [hw, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [integral_congr_ae (Eventually.of_forall h1), Measure.integral_comp_inv_smul]
    have h2 : ∀ ζ : StepVariable (finiteCells F),
        w ζ = E * weightedIntegrand (cutoffFactor ρ p) u (fun _ => g) l ζ := by
      intro ζ
      simp only [hw]
      rw [cutoffWeight_smul]
      by_cases hb : MemScaledBalls ρ l ζ
      · rw [hid ζ hb]
        have : Real.exp (-rescaledLawExponent a ρA lam f l V law ζ) = E * Real.exp (-u l ζ) := by
          rw [hE, ← Real.exp_add, hu]
          congr 1
          simp only [centredLawExponent]
          ring
        simp only [weightedIntegrand]
        rw [this]
        ring
      · have : radialCutoff (cutoffFactor ρ p) l ζ = 0 := radialCutoff_eq_zero hr hl.le hb
        simp [weightedIntegrand, this]
    simp only [h2]
    rw [integral_const_mul, smul_eq_mul, hA]
    ring
  have hA0 : A ≠ 0 := by
    have : 0 < E := Real.exp_pos _
    have h3 : l ^ Module.finrank ℝ (StepVariable (finiteCells F)) ≠ 0 := pow_ne_zero _ hl0
    exact mul_ne_zero (abs_ne_zero.2 h3) this.ne'
  have hnum := key H
  have hden := key (fun _ => 1)
  simp only [one_mul] at hden
  unfold rescaledMean cutoffMean
  rw [hnum, hden, mul_div_mul_left _ _ hA0]
private theorem lower_bound_in_sup_norm {lam : ℝ} (hlam : 0 < lam) {w : ℝ} (ζ : StepVariable (finiteCells F))
    (h : lam / 4 * ∑ b, ‖ζ b‖ ^ 2 - Real.sqrt lam / 2 * ∑ b, ‖ζ b‖ ≤ w) :
    lam / 4 * ‖ζ‖ ^ 2 - Real.sqrt lam / 2 * (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * ‖ζ‖ ≤ w := by
  have h1 : ‖ζ‖ ^ 2 ≤ ∑ b, ‖ζ b‖ ^ 2 := by
    have h2 : ‖ζ‖ ≤ Real.sqrt (∑ b, ‖ζ b‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
      refine Real.le_sqrt_of_sq_le ?_
      exact Finset.single_le_sum (f := fun b => ‖ζ b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
    calc _ ≤ Real.sqrt (∑ b, ‖ζ b‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  have h3 : ∑ b, ‖ζ b‖ ≤ (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * ‖ζ‖ := by
    calc _ ≤ ∑ _b : ↥(chordBonds (finiteCells F)), ‖ζ‖ := Finset.sum_le_sum fun b _ => norm_le_pi_norm ζ b
      _ = _ := by simp
  have h4 : 0 ≤ Real.sqrt lam / 2 := by positivity
  have h5 := mul_le_mul_of_nonneg_left h3 h4
  have h6 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ lam / 4)
  nlinarith
theorem observableMeanSlopeVanishes
    (hP : YangMills.Construction.StepDensities.rescaledPartsSmoothStatement)
    (hF : rescaledExponentFloorStatement) (hC : topDerivsOfScaledMeanAreCumulants)
    (hB : scaledMeansBounded) (hS : scaledMeansSmoothInScale) (hA : DerivAlongRulesHold) :
    ObservableMeanSlopeVanishes := by
  unfold topDerivsOfScaledMeanAreCumulants ForallSmoothObservables at hC
  unfold scaledMeansBounded ForallSmoothObservables at hB
  unfold scaledMeansSmoothInScale ForallSmoothObservables at hS
  unfold ObservableMeanSlopeVanishes ForallSmoothObservables
  refine EventuallyOrdered.mono (EventuallyOrdered.and (EventuallyOrdered.and hP hF)
    (EventuallyOrdered.and hC (EventuallyOrdered.and hB hS))) ?_
  rintro T hT hn ⟨⟨cP, cF⟩, cC, cB, cS⟩ e
  obtain ⟨lP, KP, hlP, hKP, gP⟩ := cP e
  obtain ⟨lF, hlF, gF⟩ := cF e
  obtain ⟨lC, _, hlC, _, gC⟩ := cC e
  obtain ⟨lB, CB, hlB, _, gB⟩ := cB e
  obtain ⟨lS, _, hlS, _, gS⟩ := cS e
  refine ⟨min (min lP lF) (min lC (min lB lS)), 1, by positivity, one_pos, ?_⟩
  intro l₁ hl₁ hle t f F V Y law K Ob k c X hfam hTor hV hlaw hK hob hX hk
  have leP : l₁ ≤ lP := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have leF : l₁ ≤ lF := hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have leC : l₁ ≤ lC := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have leB : l₁ ≤ lB := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have leS : l₁ ≤ lS := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hκ : 0 ≤ T.κ := hT.κ_pos.le
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hlam : 0 < T.lam := hT.chain_admissible.positivity.2.2.1
  have hr : IsCutoffProfile T.ballRadius (cutoffFactor T.ballRadius T.p) := isCutoffProfile_of_isCutoff hρ hT.cutoff
  have hw : ∀ Y' : F.Cell, Y' ∈ finiteCells F := by
    obtain ⟨_, _, n, hs, hnn⟩ := hTor
    exact TopLevelSites.mem_finiteCells fun i => by
      rw [hs i]
      omega
  have hOb : IsTameObservable T.ballRadius l₁ V Ob :=
    isTameObservable_of_isSmoothObservable hA (hob V hV) hκ hK (by linarith)
  have hU : IsTameObservable T.ballRadius l₁ V fun l ζ V' => rescaledLawExponent T.a T.ρA T.lam f l V' law ζ :=
    isTameObservable_lawExponent hw
      (fun Y' => isTameObservable_of_isSmoothObservable hA (gP l₁ hl₁ leP t f F V Y' hfam hTor hV).1 hκ hKP le_rfl)
      (fun Y' => isTameObservable_of_isSmoothObservable hA (gP l₁ hl₁ leP t f F V Y' hfam hTor hV).2 hκ hKP le_rfl) law
  have hU0 : Tempered T.ballRadius l₁ fun l (ζ : StepVariable (finiteCells F)) =>
      rescaledLawExponent T.a T.ρA T.lam f l V law ζ := by
    have h1 := hU.tempered 0 Fin.elim0 Fin.elim0 (by omega) (fun i => i.elim0)
    refine h1.congr (fun l ζ _ => ?_) fun l ζ => hU.even l ζ V
    rw [bondDeriv_of_arity_zero]
  have hu : Tempered T.ballRadius l₁ (centredLawExponent T.a T.ρA T.lam f law V) := by
    refine (hU0.add (hU0.atOrigin hρ).neg).congr (fun l ζ _ => ?_) fun l ζ => ?_
    · simp [centredLawExponent, sub_eq_add_neg]
    · have h0 := hU.even l 0 V
      simp only [neg_zero] at h0
      simp only [centredLawExponent, hU.even l ζ V, h0]
  obtain ⟨hfl, hid, -, -⟩ := gF t f F V law hfam hTor hV hlaw
  have hc : 0 < T.lam / 4 := by positivity
  have hf : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 ≤ l → l ≤ l₁ → InBalls T.ballRadius l ζ →
      T.lam / 4 * ‖ζ‖ ^ 2 - Real.sqrt T.lam / 2 * (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * ‖ζ‖ ≤
        centredLawExponent T.a T.ρA T.lam f law V l ζ :=
    fun l ζ h0 h1 hb => lower_bound_in_sup_norm hlam ζ (hfl l ζ h0 (h1.trans leF) hb)
  have hcard : ∀ I : Finset (Fin k), I.card ≤ 3 := fun I => (Finset.card_le_univ I).trans (by simpa using hk)
  have hent : ∀ (I : Finset (Fin k)) (j : Option (Finset (Fin k))), Tempered T.ballRadius l₁ fun l ζ =>
      topDerivCumulantEntries T.a T.ρA T.lam f law Ob l V c X I j ζ := by
    intro I j
    cases j with
    | none => exact hOb.tempered _ _ _ (hcard I) fun i => hX _
    | some B => exact (hU.tempered _ _ _ (hcard B) fun i => hX _).neg
  have hblock : ∀ (I : Finset (Fin k)) (J : Finset (Option (Finset (Fin k)))), VanishingSlopeAt (fun l =>
      rescaledMean T.a T.ρA T.ballRadius T.lam l T.p f law V
        (blockProd (topDerivCumulantEntries T.a T.ρA T.lam f law Ob l V c X I) J))
      ((∫ ζ, weightedIntegrand (cutoffFactor T.ballRadius T.p) (centredLawExponent T.a T.ρA T.lam f law V)
          (fun l ζ => ∏ j ∈ J, topDerivCumulantEntries T.a T.ρA T.lam f law Ob l V c X I j ζ) 0 ζ) /
        ∫ ζ, weightedIntegrand (cutoffFactor T.ballRadius T.p) (centredLawExponent T.a T.ρA T.lam f law V)
          (fun _ _ => 1) 0 ζ) := by
    intro I J
    refine (vanishingSlopeAt_weightedMean hρ hl₁ hr (Tempered.prod J fun j _ => hent I j) hu hc hf).congr ?_
    filter_upwards [Ioc_mem_nhdsGT hl₁] with l hl
    exact (rescaledMean_eq_ratio hr T.a T.ρA T.lam f law V hl.1 _ fun ζ hb =>
      hid l ζ hl.1 (hl.2.trans leF) hb).symm
  have hflat := VanishingSlopeAt.sum (Finset.univ : Finset (Fin k)).powerset fun I _ =>
    VanishingSlopeAt.sum (Finset.univ : Finset (Finpartition (Finset.univ \ I))) fun π _ =>
      VanishingSlopeAt.sum (Finset.univ : Finset (Finpartition (insert none (π.parts.image some)))) fun σ _ =>
        (VanishingSlopeAt.prod σ.parts fun J _ => hblock I J).const_mul (cumulantWeight σ.parts.card)
  refine tendsto_deriv_of_vanishingSlopeAt (M := CB * K * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ)))) hl₁
    (fun l h0 h1 => ?_) (fun l h0 h1 => ?_) (hflat.congr ?_)
  · have h2 := gS l₁ hl₁ leS t f F V Y law K Ob k c X hfam hTor hV hlaw hK hob hX hk l h0 h1
    split_ifs at h2 with h3
    · exact h2
    · exact h2.of_le (by norm_num)
  · exact gB l₁ hl₁ leB t f F V Y law K Ob k c X hfam hTor hV hlaw hK hob hX 2 l (Or.inl ⟨hk, le_rfl⟩) h0 h1
  · filter_upwards [Ioc_mem_nhdsGT hl₁] with l hl
    rw [gC l₁ hl₁ leC t f F V Y law K Ob k c X hfam hTor hV hlaw hK hob hX hk l hl.1 hl.2]
    rfl
end
end YangMills.Construction.ScaledVariables
end
