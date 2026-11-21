import YangMills.Construction.ComplexAnalysis.JoukowskiRadiusProperties
import YangMills.Construction.ComplexAnalysis.SeparateToJointHolomorphy
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.TransferOperators.CharacterCoefficientsOfTheOneBondWeightProof
import Mathlib
open Set MeasureTheory Filter Topology
open scoped Real
noncomputable section
namespace YangMills.Construction.JointHolomorphy
def chebWeight (p : ℕ) : ℝ := if p = 0 then 1 else 2
theorem chebWeight_le_two (p : ℕ) : chebWeight p ≤ 2 := by
  unfold chebWeight; split_ifs <;> norm_num
theorem chebWeight_pos (p : ℕ) : 0 < chebWeight p := by
  unfold chebWeight; split_ifs <;> norm_num
def chebT (p : ℕ) (z : ℂ) : ℂ := (Polynomial.Chebyshev.T ℂ (p : ℤ)).eval z
theorem chebT_joukowski (p : ℕ) {ω : ℂ} (hω : ω ≠ 0) :
    chebT p ((1 / 2 : ℂ) * (ω + ω⁻¹)) = (1 / 2 : ℂ) * (ω ^ p + (ω ^ p)⁻¹) := by
  obtain ⟨θ, rfl⟩ : ∃ θ : ℂ, Complex.exp (θ * Complex.I) = ω :=
    ⟨Complex.log ω / Complex.I, by
      rw [div_mul_cancel₀ _ Complex.I_ne_zero, Complex.exp_log hω]⟩
  have h1 : (1 / 2 : ℂ) * (Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹)
      = Complex.cos θ := by
    rw [Complex.cos, ← Complex.exp_neg]; ring_nf
  rw [h1, chebT, Polynomial.Chebyshev.T_complex_cos, Complex.cos, ← Complex.exp_nat_mul,
    ← Complex.exp_neg]
  push_cast
  ring_nf
theorem chebT_cos (p : ℕ) (t : ℝ) :
    chebT p ((Real.cos t : ℝ) : ℂ) = ((Real.cos (p * t) : ℝ) : ℂ) := by
  rw [chebT, Complex.ofReal_cos, Polynomial.Chebyshev.T_complex_cos, Complex.ofReal_cos]
  push_cast
  rfl
theorem norm_chebT_joukowski_le (p : ℕ) {ω : ℂ} (hω : 1 ≤ ‖ω‖) :
    ‖chebT p ((1 / 2 : ℂ) * (ω + ω⁻¹))‖ ≤ ‖ω‖ ^ p := by
  have h0 : ω ≠ 0 := by
    intro h; simp [h] at hω; linarith
  rw [chebT_joukowski p h0, norm_mul]
  have h1 : (1 : ℝ) ≤ ‖ω‖ ^ p := one_le_pow₀ hω
  have h2 : ‖(ω ^ p)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow]; exact inv_le_one_of_one_le₀ h1
  have h3 : ‖ω ^ p + (ω ^ p)⁻¹‖ ≤ ‖ω‖ ^ p + 1 := by
    calc _ ≤ ‖ω ^ p‖ + ‖(ω ^ p)⁻¹‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_pow]; linarith
  have h4 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h4]; linarith
theorem norm_fourierCoeff_annulus_le (g : ℂ → ℂ) {ς A : ℝ} (hς : 1 < ς)
    (hg : ∀ ω : ℂ, ς⁻¹ < ‖ω‖ → ‖ω‖ < ς → DifferentiableAt ℂ g ω)
    (hA : ∀ ω : ℂ, ς⁻¹ < ‖ω‖ → ‖ω‖ < ς → ‖g ω‖ ≤ A) (p : ℕ) {r : ℝ} (h1 : 1 < r) (hr : r < ς) :
    ‖∫ θ in (0 : ℝ)..2 * π, g (Complex.exp (θ * Complex.I)) *
        Complex.exp (-((p : ℂ) * θ) * Complex.I)‖ ≤ 2 * π * A * (r ^ p)⁻¹ := by
  have hinv : ς⁻¹ < 1 := inv_lt_one_of_one_lt₀ hς
  have hr0 : 0 < r := by linarith
  set f : ℂ → ℂ := fun ω => (ω ^ p)⁻¹ * g ω with hf
  have hdiff : ∀ ω : ℂ, 1 ≤ ‖ω‖ → ‖ω‖ ≤ r → DifferentiableAt ℂ f ω := by
    intro ω ha hb
    have h0 : ω ≠ 0 := by
      intro h; simp [h] at ha; linarith
    exact ((differentiableAt_id.pow p).inv (pow_ne_zero p h0)).mul
      (hg ω (by linarith) (by linarith))
  have heq := Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
    (c := 0) (r := 1) (R := r) (f := f) (s := ∅) one_pos h1.le countable_empty
    (fun ω hω => by
      have ha : 1 ≤ ‖ω‖ := by simpa using hω.2
      have hb : ‖ω‖ ≤ r := by simpa using hω.1
      exact (hdiff ω ha hb).continuousAt.continuousWithinAt)
    (fun ω hω => by
      have ha : 1 < ‖ω‖ := by simpa using hω.1.2
      have hb : ‖ω‖ < r := by simpa using hω.1.1
      exact hdiff ω ha.le hb.le)
  have hleft : (∮ z in C(0, 1), (z - 0)⁻¹ • f z) = Complex.I *
      ∫ θ in (0 : ℝ)..2 * π, g (Complex.exp (θ * Complex.I)) *
        Complex.exp (-((p : ℂ) * θ) * Complex.I) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hne : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    simp only [deriv_circleMap, circleMap, Complex.ofReal_one, one_mul, zero_add, sub_zero,
      smul_eq_mul, hf]
    have hpw : (Complex.exp (θ * Complex.I) ^ p)⁻¹ = Complex.exp (-((p : ℂ) * θ) * Complex.I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_neg]; ring_nf
    rw [hpw]
    field_simp
  have hright : ‖∮ z in C(0, r), (z - 0)⁻¹ • f z‖ ≤ 2 * π * r * (r⁻¹ * ((r ^ p)⁻¹ * A)) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const hr0.le fun z hz => ?_
    have hz' : ‖z‖ = r := by simpa using hz
    have hb : ‖g z‖ ≤ A := hA z (by rw [hz']; linarith) (by rw [hz']; exact hr)
    rw [sub_zero, norm_smul, norm_inv, hz', norm_mul, norm_inv, norm_pow, hz']
    gcongr
  rw [heq.symm.trans rfl] at hleft
  have hnorm := congrArg norm hleft
  rw [norm_mul, Complex.norm_I, one_mul] at hnorm
  rw [← hnorm]
  calc _ ≤ _ := hright
    _ = _ := by field_simp
theorem norm_cosCoeff_le (h : ℂ → ℂ) {ς A : ℝ} (hς : 1 < ς)
    (hc : Continuous fun θ : ℝ => h ((Real.cos θ : ℝ) : ℂ))
    (hg : ∀ ω : ℂ, ς⁻¹ < ‖ω‖ → ‖ω‖ < ς → DifferentiableAt ℂ h ((1 / 2 : ℂ) * (ω + ω⁻¹)))
    (hA : ∀ ω : ℂ, ς⁻¹ < ‖ω‖ → ‖ω‖ < ς → ‖h ((1 / 2 : ℂ) * (ω + ω⁻¹))‖ ≤ A) (p : ℕ) :
    ‖∫ θ in (0 : ℝ)..π, h ((Real.cos θ : ℝ) : ℂ) * ((Real.cos (p * θ) : ℝ) : ℂ)‖ ≤
      π * A * (ς ^ p)⁻¹ := by
  set u : ℝ → ℂ := fun θ => h ((Real.cos θ : ℝ) : ℂ) * Complex.exp (-((p : ℂ) * θ) * Complex.I)
    with hu
  have huc : Continuous u := hc.mul (by fun_prop)
  have hper : Function.Periodic u (2 * π) := by
    intro θ
    have h1 : Complex.exp (-((p : ℂ) * ((θ + 2 * π : ℝ) : ℂ)) * Complex.I)
        = Complex.exp (-((p : ℂ) * θ) * Complex.I) := by
      have : -((p : ℂ) * ((θ + 2 * π : ℝ) : ℂ)) * Complex.I
          = -((p : ℂ) * θ) * Complex.I + ((-(p : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only [hu, Real.cos_add_two_pi, h1]
  have hsplit : (∫ θ in (0 : ℝ)..2 * π, u θ) =
      2 * ∫ θ in (0 : ℝ)..π, h ((Real.cos θ : ℝ) : ℂ) * ((Real.cos (p * θ) : ℝ) : ℂ) := by
    have e1 : (∫ θ in (0 : ℝ)..2 * π, u θ) = ∫ θ in (-π)..π, u θ := by
      have := hper.intervalIntegral_add_eq 0 (-π)
      simpa [two_mul, add_comm, add_assoc] using this
    have e2 : (∫ θ in (-π)..π, u θ) = (∫ θ in (-π)..0, u θ) + ∫ θ in (0 : ℝ)..π, u θ :=
      (intervalIntegral.integral_add_adjacent_intervals (huc.intervalIntegrable _ _)
        (huc.intervalIntegrable _ _)).symm
    have e3 : (∫ θ in (-π)..0, u θ) = ∫ θ in (0 : ℝ)..π, u (-θ) := by
      simp
    have hun : Continuous fun θ : ℝ => u (-θ) := huc.comp continuous_neg
    rw [e1, e2, e3, ← intervalIntegral.integral_add (hun.intervalIntegrable _ _)
      (huc.intervalIntegrable _ _), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hcos : ((Real.cos (p * θ) : ℝ) : ℂ) = (Complex.exp ((p : ℂ) * θ * Complex.I) +
        Complex.exp (-((p : ℂ) * θ) * Complex.I)) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos]; push_cast; ring_nf
    simp only [hu, Real.cos_neg, hcos]
    push_cast
    ring_nf
  have hbound : ∀ r : ℝ, 1 < r → r < ς →
      ‖∫ θ in (0 : ℝ)..π, h ((Real.cos θ : ℝ) : ℂ) * ((Real.cos (p * θ) : ℝ) : ℂ)‖ ≤
        π * A * (r ^ p)⁻¹ := by
    intro r h1 hr
    have hb := norm_fourierCoeff_annulus_le (fun ω => h ((1 / 2 : ℂ) * (ω + ω⁻¹))) hς ?_ hA p h1 hr
    · have hsame : (∫ θ in (0 : ℝ)..2 * π, (fun ω => h ((1 / 2 : ℂ) * (ω + ω⁻¹)))
          (Complex.exp (θ * Complex.I)) * Complex.exp (-((p : ℂ) * θ) * Complex.I)) =
          ∫ θ in (0 : ℝ)..2 * π, u θ := by
        refine intervalIntegral.integral_congr fun θ _ => ?_
        have : (1 / 2 : ℂ) * (Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹)
            = ((Real.cos θ : ℝ) : ℂ) := by
          rw [Complex.ofReal_cos, Complex.cos, ← Complex.exp_neg]; ring_nf
        simp only [hu, this]
      rw [hsame, hsplit, norm_mul] at hb
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2] at hb
      linarith
    · intro ω ha hb
      have h0 : ω ≠ 0 := by
        intro h0; simp [h0] at ha; linarith [inv_pos.2 (by linarith : (0 : ℝ) < ς)]
      have hin : DifferentiableAt ℂ (fun ω : ℂ => (1 / 2 : ℂ) * (ω + ω⁻¹)) ω :=
        (differentiableAt_id.add (differentiableAt_inv h0)).const_mul _
      exact (hg ω ha hb).comp ω hin
  have hlim : Tendsto (fun r : ℝ => π * A * (r ^ p)⁻¹) (𝓝[<] ς) (𝓝 (π * A * (ς ^ p)⁻¹)) := by
    have hne : ς ^ p ≠ 0 := pow_ne_zero _ (by linarith)
    have : ContinuousAt (fun r : ℝ => π * A * (r ^ p)⁻¹) ς :=
      continuousAt_const.mul ((continuousAt_id.pow p).inv₀ hne)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hς] with r hr using hbound r hr.1 hr.2
def halfPeriodMeasure : Measure ℝ := volume.restrict (Ioc 0 π)
instance isFiniteMeasure_halfPeriodMeasure : IsFiniteMeasure halfPeriodMeasure :=
  ⟨by simp [halfPeriodMeasure]⟩
def cubeMeasure (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => halfPeriodMeasure
instance isFiniteMeasure_cubeMeasure (n : ℕ) : IsFiniteMeasure (cubeMeasure n) := by
  unfold cubeMeasure; infer_instance
theorem cubeMeasure_eq_restrict (n : ℕ) :
    cubeMeasure n = (volume : Measure (Fin n → ℝ)).restrict (univ.pi fun _ => Ioc 0 π) := by
  rw [volume_pi, Measure.restrict_pi_pi]; rfl
theorem cubeMeasure_real_univ (n : ℕ) : (cubeMeasure n).real univ = π ^ n := by
  have h1 : halfPeriodMeasure univ = ENNReal.ofReal π := by simp [halfPeriodMeasure]
  have h2 : cubeMeasure n univ = ENNReal.ofReal π ^ n := by
    rw [cubeMeasure, ← Set.pi_univ, Measure.pi_pi]; simp [h1]
  rw [Measure.real, h2, ENNReal.toReal_pow, ENNReal.toReal_ofReal Real.pi_pos.le]
theorem integrable_cubeMeasure {n : ℕ} {E : Type} [NormedAddCommGroup E] {f : (Fin n → ℝ) → E}
    (hf : Continuous f) : Integrable f (cubeMeasure n) := by
  rw [cubeMeasure_eq_restrict]
  have hc : IsCompact (univ.pi fun _ : Fin n => Icc (0 : ℝ) π) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have h1 : IntegrableOn f (univ.pi fun _ : Fin n => Icc (0 : ℝ) π) :=
    hf.continuousOn.integrableOn_compact hc
  exact h1.mono_set (Set.pi_mono fun _ _ => Ioc_subset_Icc_self)
def cosMode (p : ℕ) (t : ℝ) : ℝ := chebWeight p / π * Real.cos (p * t)
def cosProduct {n : ℕ} (k : Fin n → ℕ) (α : Fin n → ℝ) : ℝ := ∏ j, Real.cos (k j * α j)
def cosModeProduct {n : ℕ} (k : Fin n → ℕ) (α : Fin n → ℝ) : ℝ := ∏ j, cosMode (k j) (α j)
theorem continuous_cosProduct {n : ℕ} (k : Fin n → ℕ) : Continuous (cosProduct k) := by
  unfold cosProduct; fun_prop
theorem continuous_cosModeProduct {n : ℕ} (k : Fin n → ℕ) : Continuous (cosModeProduct k) := by
  unfold cosModeProduct cosMode; fun_prop
theorem cosModeProduct_eq {n : ℕ} (k : Fin n → ℕ) (α : Fin n → ℝ) :
    cosModeProduct k α = (∏ j, chebWeight (k j) / π) * cosProduct k α := by
  simp only [cosModeProduct, cosMode, cosProduct, Finset.prod_mul_distrib]
theorem abs_cosMode_le (p : ℕ) (t : ℝ) : |cosMode p t| ≤ 2 / π := by
  have h0 := chebWeight_pos p
  rw [cosMode, abs_mul, abs_of_pos (div_pos h0 Real.pi_pos)]
  calc _ ≤ chebWeight p / π * 1 := by gcongr; exact Real.abs_cos_le_one _
    _ ≤ 2 / π := by
      rw [mul_one]; gcongr; exact chebWeight_le_two p
def cosCoeff {n : ℕ} (G : (Fin n → ℝ) → ℂ) (k : Fin n → ℕ) : ℂ :=
  ∫ α, G α * (cosModeProduct k α : ℂ) ∂cubeMeasure n
theorem norm_cosCoeff_le_of_slice {m : ℕ} {G : (Fin (m + 1) → ℝ) → ℂ} (hG : Continuous G) {B : ℝ}
    (k : Fin (m + 1) → ℕ) (j : Fin (m + 1))
    (hin : ∀ y : Fin m → ℝ,
      ‖∫ t in (0 : ℝ)..π, G (j.insertNth t y) * ((Real.cos (k j * t) : ℝ) : ℂ)‖ ≤ B) :
    ‖cosCoeff G k‖ ≤ 2 ^ (m + 1) / π * B := by
  set f : (Fin (m + 1) → ℝ) → ℂ := fun α => G α * (cosModeProduct k α : ℂ) with hf
  have hfc : Continuous f := hG.mul (Complex.continuous_ofReal.comp (continuous_cosModeProduct k))
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => halfPeriodMeasure) j
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j with he
  have h1 : cosCoeff G k = ∫ q, f (e.symm q) ∂(halfPeriodMeasure.prod (cubeMeasure m)) :=
    (mp.symm.integral_comp' f).symm
  have hint : Integrable (fun q => f (e.symm q)) (halfPeriodMeasure.prod (cubeMeasure m)) :=
    mp.symm.integrable_comp_of_integrable (integrable_cubeMeasure hfc)
  rw [h1, integral_prod_symm _ hint]
  set W : (Fin m → ℝ) → ℝ := fun y => ∏ i, cosMode (k (j.succAbove i)) (y i) with hW
  have hinner : ∀ y : Fin m → ℝ,
      ‖∫ t, f (e.symm (t, y)) ∂halfPeriodMeasure‖ ≤ (2 / π) ^ m * (2 / π * B) := by
    intro y
    have hsplit : ∀ t, f (e.symm (t, y)) = ((W y * (chebWeight (k j) / π) : ℝ) : ℂ) *
        (G (j.insertNth t y) * ((Real.cos (k j * t) : ℝ) : ℂ)) := by
      intro t
      have hsym : e.symm (t, y) = j.insertNth t y := rfl
      have hw : cosModeProduct k (j.insertNth t y) = cosMode (k j) t * W y := by
        rw [cosModeProduct, Fin.prod_univ_succAbove _ j]
        simp [hW]
      simp only [hf, hsym, hw, cosMode]
      push_cast
      ring
    have hI : (∫ t, G (j.insertNth t y) * ((Real.cos (k j * t) : ℝ) : ℂ) ∂halfPeriodMeasure) =
        ∫ t in (0 : ℝ)..π, G (j.insertNth t y) * ((Real.cos (k j * t) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_of_le Real.pi_pos.le]; rfl
    simp only [hsplit]
    rw [integral_const_mul, hI, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hWb : |W y| ≤ (2 / π) ^ m := by
      rw [hW]
      simp only [Finset.abs_prod]
      calc _ ≤ ∏ _i : Fin m, 2 / π :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => abs_cosMode_le _ _
        _ = _ := by simp [div_pow]
    have hwk : |chebWeight (k j) / π| ≤ 2 / π := by
      rw [abs_of_pos (div_pos (chebWeight_pos _) Real.pi_pos)]
      gcongr; exact chebWeight_le_two _
    calc _ ≤ (2 / π) ^ m * (2 / π) * B := by
          gcongr
          exact hin y
      _ = _ := by ring
  have := norm_integral_le_of_norm_le_const (μ := cubeMeasure m) (Eventually.of_forall hinner)
  rw [cubeMeasure_real_univ] at this
  refine this.trans (le_of_eq ?_)
  have hp : π ≠ 0 := Real.pi_ne_zero
  rw [div_pow]
  field_simp
  ring
theorem exists_mvPolynomial_approx {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContinuousOn u (univ.pi fun _ => Icc (-1 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℝ, ∀ x ∈ (univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1),
      |u x - MvPolynomial.eval x P| < ε := by
  set K : Set (Fin n → ℝ) := univ.pi fun _ => Icc (-1 : ℝ) 1 with hK
  have hc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have : CompactSpace K := isCompact_iff_compactSpace.1 hc
  let coord : Fin n → C(K, ℝ) := fun i =>
    ⟨fun x => x.1 i, (continuous_apply i).comp continuous_subtype_val⟩
  let A : Subalgebra ℝ C(K, ℝ) := (MvPolynomial.aeval coord).range
  have hev : ∀ (P : MvPolynomial (Fin n) ℝ) (x : K),
      (MvPolynomial.aeval coord P) x = MvPolynomial.eval x.1 P := by
    intro P x
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, coord]
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 fun h => hxy (Subtype.ext h)
    exact ⟨coord i, ⟨coord i, ⟨MvPolynomial.X i, by simp⟩, rfl⟩, hi⟩
  let w : C(K, ℝ) := ⟨fun x => u x.1, continuousOn_iff_continuous_domRestrict.1 hu⟩
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hsep w ε hε
  obtain ⟨P, hP⟩ := g.2
  refine ⟨P, fun x hx => ?_⟩
  have h1 : ‖(g : C(K, ℝ)) ⟨x, hx⟩ - w ⟨x, hx⟩‖ < ε :=
    lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm ((g : C(K, ℝ)) - w) ⟨x, hx⟩) hg
  rw [← hP] at h1
  have h2 : ((MvPolynomial.aeval coord).toRingHom P) ⟨x, hx⟩ = MvPolynomial.eval x P :=
    hev P ⟨x, hx⟩
  rw [Real.norm_eq_abs, h2, abs_sub_comm] at h1
  exact h1
def lowerIndex (p : ℕ) : ℕ := if p = 0 then 1 else p - 1
theorem cos_nat_mul_mul_cos (p : ℕ) (t : ℝ) :
    Real.cos (p * t) * Real.cos t =
      1 / 2 * Real.cos ((p + 1 : ℕ) * t) + 1 / 2 * Real.cos (lowerIndex p * t) := by
  rcases p with _ | q
  · simp [lowerIndex]; ring
  · have h1 : (((q + 1 + 1 : ℕ) : ℝ)) * t = ((q + 1 : ℕ) : ℝ) * t + t := by push_cast; ring
    have h2 : ((lowerIndex (q + 1) : ℕ) : ℝ) * t = ((q + 1 : ℕ) : ℝ) * t - t := by
      simp [lowerIndex]; ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]; ring
theorem cosProduct_update {n : ℕ} (k : Fin n → ℕ) (i : Fin n) (p : ℕ) (α : Fin n → ℝ) :
    cosProduct (Function.update k i p) α =
      Real.cos (p * α i) * ∏ j ∈ Finset.univ.erase i, Real.cos (k j * α j) := by
  rw [cosProduct, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
theorem cosProduct_mul_cos {n : ℕ} (k : Fin n → ℕ) (i : Fin n) (α : Fin n → ℝ) :
    cosProduct k α * Real.cos (α i) =
      1 / 2 * cosProduct (Function.update k i (k i + 1)) α +
        1 / 2 * cosProduct (Function.update k i (lowerIndex (k i))) α := by
  have h : cosProduct k α =
      Real.cos (k i * α i) * ∏ j ∈ Finset.univ.erase i, Real.cos (k j * α j) := by
    rw [cosProduct]
    exact (Finset.mul_prod_erase Finset.univ (fun j => Real.cos (k j * α j))
      (Finset.mem_univ i)).symm
  rw [cosProduct_update, cosProduct_update, h]
  have := cos_nat_mul_mul_cos (k i) (α i)
  linear_combination (∏ j ∈ Finset.univ.erase i, Real.cos (k j * α j)) * this
def cosVector {n : ℕ} (α : Fin n → ℝ) : Fin n → ℝ := fun j => Real.cos (α j)
theorem continuous_cosVector {n : ℕ} : Continuous (cosVector (n := n)) := by
  unfold cosVector; fun_prop
theorem integral_mul_mvPolynomial_cosProduct_eq_zero {n : ℕ} {v : (Fin n → ℝ) → ℝ}
    (hv : Continuous v)
    (h : ∀ k : Fin n → ℕ, ∫ α, v α * cosProduct k α ∂cubeMeasure n = 0)
    (P : MvPolynomial (Fin n) ℝ) :
    ∀ k : Fin n → ℕ,
      ∫ α, v α * MvPolynomial.eval (cosVector α) P * cosProduct k α ∂cubeMeasure n = 0 := by
  have hcont : ∀ (Q : MvPolynomial (Fin n) ℝ) (k : Fin n → ℕ),
      Continuous fun α => v α * MvPolynomial.eval (cosVector α) Q * cosProduct k α := fun Q k =>
    (hv.mul ((MvPolynomial.continuous_eval Q).comp continuous_cosVector)).mul
      (continuous_cosProduct k)
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro k
    have := h k
    calc _ = ∫ α, a * (v α * cosProduct k α) ∂cubeMeasure n := by
          refine integral_congr_ae (Eventually.of_forall fun α => ?_)
          simp only [MvPolynomial.eval_C]; ring
      _ = 0 := by rw [integral_const_mul, this, mul_zero]
  | add p q hp hq =>
    intro k
    calc _ = ∫ α, (v α * MvPolynomial.eval (cosVector α) p * cosProduct k α +
            v α * MvPolynomial.eval (cosVector α) q * cosProduct k α) ∂cubeMeasure n := by
          refine integral_congr_ae (Eventually.of_forall fun α => ?_)
          simp only [map_add]; ring
      _ = 0 := by
          rw [integral_add (integrable_cubeMeasure (hcont p k))
            (integrable_cubeMeasure (hcont q k)), hp k, hq k, add_zero]
  | mul_X p i hp =>
    intro k
    have h1 := hp (Function.update k i (k i + 1))
    have h2 := hp (Function.update k i (lowerIndex (k i)))
    calc _ = ∫ α, (1 / 2 * (v α * MvPolynomial.eval (cosVector α) p *
              cosProduct (Function.update k i (k i + 1)) α) +
            1 / 2 * (v α * MvPolynomial.eval (cosVector α) p *
              cosProduct (Function.update k i (lowerIndex (k i))) α)) ∂cubeMeasure n := by
          refine integral_congr_ae (Eventually.of_forall fun α => ?_)
          have := cosProduct_mul_cos k i α
          have hX : MvPolynomial.eval (cosVector α) (p * MvPolynomial.X i) =
              MvPolynomial.eval (cosVector α) p * Real.cos (α i) := by
            simp [cosVector]
          beta_reduce
          rw [hX]
          linear_combination (v α * MvPolynomial.eval (cosVector α) p) * this
      _ = 0 := by
          rw [integral_add ((integrable_cubeMeasure (hcont p _)).const_mul _)
            ((integrable_cubeMeasure (hcont p _)).const_mul _), integral_const_mul,
            integral_const_mul, h1, h2]
          simp
theorem eq_zero_on_cube_of_cosCoeff {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContinuousOn u (univ.pi fun _ => Icc (-1 : ℝ) 1))
    (h : ∀ k : Fin n → ℕ, ∫ α, u (cosVector α) * cosProduct k α ∂cubeMeasure n = 0) :
    ∀ x ∈ (univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1), u x = 0 := by
  have hmem : ∀ α : Fin n → ℝ, cosVector α ∈ (univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) :=
    fun α j _ => ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  set v : (Fin n → ℝ) → ℝ := fun α => u (cosVector α) with hvdef
  have hv : Continuous v := hu.comp_continuous continuous_cosVector hmem
  have hone : ∀ α : Fin n → ℝ, cosProduct (0 : Fin n → ℕ) α = 1 := by
    intro α; simp [cosProduct]
  have hsq : ∫ α, v α ^ 2 ∂cubeMeasure n = 0 := by
    have hnn : 0 ≤ ∫ α, v α ^ 2 ∂cubeMeasure n := integral_nonneg fun α => sq_nonneg _
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) hnn
    set M : ℝ := ∫ α, |v α| ∂cubeMeasure n with hM
    have hM0 : 0 ≤ M := integral_nonneg fun α => abs_nonneg _
    obtain ⟨P, hP⟩ := exists_mvPolynomial_approx hu (ε := ε / (M + 1)) (by positivity)
    have hPc : Continuous fun α => MvPolynomial.eval (cosVector α) P :=
      (MvPolynomial.continuous_eval P).comp continuous_cosVector
    have h0 := integral_mul_mvPolynomial_cosProduct_eq_zero hv h P 0
    simp only [hone, mul_one] at h0
    have hdiff : ∫ α, v α ^ 2 ∂cubeMeasure n =
        ∫ α, v α * (v α - MvPolynomial.eval (cosVector α) P) ∂cubeMeasure n := by
      have : ∀ α, v α * (v α - MvPolynomial.eval (cosVector α) P) =
          v α ^ 2 - v α * MvPolynomial.eval (cosVector α) P := fun α => by ring
      simp only [this]
      have hs := integral_sub (μ := cubeMeasure n) (f := fun α => v α ^ 2)
        (g := fun α => v α * MvPolynomial.eval (cosVector α) P)
        (integrable_cubeMeasure (hv.pow 2)) (integrable_cubeMeasure (hv.mul hPc))
      rw [hs, h0, sub_zero]
    rw [hdiff, zero_add]
    have hle : ∫ α, v α * (v α - MvPolynomial.eval (cosVector α) P) ∂cubeMeasure n ≤
        ∫ α, ε / (M + 1) * |v α| ∂cubeMeasure n := by
      refine integral_mono (integrable_cubeMeasure (hv.mul (hv.sub hPc)))
        (integrable_cubeMeasure (continuous_const.mul hv.abs)) fun α => ?_
      have h1 := hP _ (hmem α)
      calc _ ≤ |v α * (v α - MvPolynomial.eval (cosVector α) P)| := le_abs_self _
        _ = |v α| * |v α - MvPolynomial.eval (cosVector α) P| := abs_mul _ _
        _ ≤ |v α| * (ε / (M + 1)) := by gcongr
        _ = _ := mul_comm _ _
    rw [integral_const_mul] at hle
    refine hle.trans ?_
    rw [← hM, div_mul_eq_mul_div]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hae : (fun α => v α ^ 2) =ᵐ[cubeMeasure n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun α => sq_nonneg _)
      (integrable_cubeMeasure (hv.pow 2))).1 hsq
  set U : Set (Fin n → ℝ) := univ.pi fun _ => Ioo (0 : ℝ) π with hU
  have hUo : IsOpen U := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  rw [cubeMeasure_eq_restrict] at hae
  have hae2 : (fun α => v α ^ 2) =ᵐ[(volume : Measure (Fin n → ℝ)).restrict U] 0 :=
    ae_restrict_of_ae_restrict_of_subset (Set.pi_mono fun _ _ => Ioo_subset_Ioc_self) hae
  have heq := Measure.eqOn_open_of_ae_eq hae2 hUo (hv.pow 2).continuousOn continuousOn_const
  have hclosed : IsClosed {α : Fin n → ℝ | v α = 0} := isClosed_eq hv continuous_const
  have hsub : U ⊆ {α : Fin n → ℝ | v α = 0} := fun α hα => by
    have := heq hα
    simpa using this
  have hcl : closure U ⊆ {α : Fin n → ℝ | v α = 0} := closure_minimal hsub hclosed
  intro x hx
  have hα : (fun j => Real.arccos (x j)) ∈ closure U := by
    rw [hU, closure_pi_set]
    intro j _
    rw [closure_Ioo Real.pi_ne_zero.symm]
    exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have h1 := hcl hα
  have h2 : cosVector (fun j => Real.arccos (x j)) = x := by
    funext j
    exact Real.cos_arccos (hx j (mem_univ j)).1 (hx j (mem_univ j)).2
  simpa [hvdef, h2] using h1
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates YangMills.Construction.Ellipses YangMills.Construction.RealPower
theorem rpowPos_eq_exp {ς : ℝ} (h : 0 < ς) (t : ℝ) : rpowPos ς t = Real.exp (t * Real.log ς) := by
  simp [rpowPos, h]
def chebTerm {n : ℕ} (c : (Fin n → ℕ) → ℂ) (k : Fin n → ℕ) (z : ComplexCoordinates n) : ℂ :=
  c k * ∏ j, chebT (k j) (z j)
theorem norm_chebT_le_joukowskiRadius (hj : JoukowskiRadius.JoukowskiRadiusProperties)
    (p : ℕ) (z : ℂ) : ‖chebT p z‖ ≤ joukowskiRadius z ^ p := by
  obtain ⟨hge, -, -, -, -, -, hform, -⟩ := hj
  obtain ⟨ω, hz, hω⟩ := hform z
  have h1 : 1 ≤ ‖ω‖ := hω ▸ hge z
  have := norm_chebT_joukowski_le p h1
  rwa [← hz, hω] at this
theorem norm_chebTerm_le {n : ℕ} (hn : 1 ≤ n) {c : (Fin n → ℕ) → ℂ} {C L : ℝ} (hC : 0 ≤ C)
    (hL : 0 < L) (hc : ∀ k j, ‖c k‖ ≤ C * Real.exp (-(L * k j))) {ρ : ℂ → ℝ}
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ : ∀ p z, ‖chebT p z‖ ≤ ρ z ^ p) {s : Fin n → ℝ}
    (hs : ∀ j, 0 ≤ s j) (hsum : ∑ j, s j < 1) (k : Fin n → ℕ) {z : ComplexCoordinates n}
    (hz : ∀ j, ρ (z j) ≤ Real.exp (s j * L)) :
    ‖chebTerm c k z‖ ≤ C * ∏ j, Real.exp (-((1 - ∑ i, s i) / n * L)) ^ k j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set δ : ℝ := (1 - ∑ i, s i) / n with hδ
  have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hn0.le
  obtain ⟨j₀, -, hmax⟩ := Finset.exists_max_image Finset.univ k ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hprod : ∏ j, ‖chebT (k j) (z j)‖ ≤ ∏ j, Real.exp (s j * L) ^ k j :=
    Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ =>
      (hρ _ _).trans (pow_le_pow_left₀ (hρ0 _) (hz j) _)
  have e1 : ∏ j, Real.exp (s j * L) ^ k j = Real.exp (∑ j, (k j : ℝ) * (s j * L)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_nat_mul _ _).symm
  have e2 : ∏ j, Real.exp (-(δ * L)) ^ k j = Real.exp (∑ j, (k j : ℝ) * (-(δ * L))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_nat_mul _ _).symm
  have hw : ∑ j, (s j + δ) * (k j : ℝ) ≤ k j₀ := by
    calc _ ≤ ∑ j, (s j + δ) * (k j₀ : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have : (k j : ℝ) ≤ k j₀ := by exact_mod_cast hmax j (Finset.mem_univ j)
          exact mul_le_mul_of_nonneg_left this (add_nonneg (hs j) hδ0)
      _ = (∑ j, s j + n * δ) * k j₀ := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib]; simp
      _ = k j₀ := by
          rw [hδ]; field_simp; ring
  have hexp : -(L * k j₀) + ∑ j, (k j : ℝ) * (s j * L) ≤ ∑ j, (k j : ℝ) * (-(δ * L)) := by
    have h1 : ∑ j, (k j : ℝ) * (-(δ * L)) - ∑ j, (k j : ℝ) * (s j * L) =
        -(L * ∑ j, (s j + δ) * (k j : ℝ)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 := mul_le_mul_of_nonneg_left hw hL.le
    linarith
  rw [chebTerm, norm_mul, norm_prod, e2]
  calc _ ≤ (C * Real.exp (-(L * k j₀))) * Real.exp (∑ j, (k j : ℝ) * (s j * L)) :=
        mul_le_mul (hc k j₀) (e1 ▸ hprod) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (mul_nonneg hC (Real.exp_pos _).le)
    _ = C * Real.exp (-(L * k j₀) + ∑ j, (k j : ℝ) * (s j * L)) := by
        rw [Real.exp_add]; ring
    _ ≤ _ := by gcongr
theorem sum_prod_pow_le_geom {n : ℕ} {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1)
    (S : Finset (Fin n → ℕ)) : ∑ k ∈ S, ∏ j, q ^ k j ≤ ((1 - q)⁻¹) ^ n := by
  set P : ℕ := S.sup (fun k => Finset.univ.sup k) + 1 with hP
  have hsub : S ⊆ Fintype.piFinset fun _ => Finset.range P := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro j
    have h2 : k j ≤ Finset.univ.sup k := Finset.le_sup (f := k) (Finset.mem_univ j)
    have h3 : Finset.univ.sup k ≤ S.sup (fun k => Finset.univ.sup k) :=
      Finset.le_sup (f := fun k : Fin n → ℕ => Finset.univ.sup k) hk
    exact Finset.mem_range.2 (by omega)
  have hg : ∀ _ : Fin n, ∑ p ∈ Finset.range P, q ^ p ≤ (1 - q)⁻¹ := fun _ => by
    rw [← tsum_geometric_of_lt_one h0 h1]
    exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ fun _ _ => pow_nonneg h0 _
  calc _ ≤ ∑ k ∈ Fintype.piFinset (fun _ : Fin n => Finset.range P), ∏ j, q ^ k j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          Finset.prod_nonneg fun _ _ => pow_nonneg h0 _
    _ = ∏ _j : Fin n, ∑ p ∈ Finset.range P, q ^ p :=
        (Finset.prod_univ_sum (fun _ => Finset.range P) fun _ p => q ^ p).symm
    _ ≤ ∏ _j : Fin n, (1 - q)⁻¹ :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg h0 _)
          fun j _ => hg j
    _ = _ := by simp
theorem summable_prod_geom {n : ℕ} {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Summable fun k : Fin n → ℕ => ∏ j, q ^ k j :=
  summable_of_sum_le (fun _ => Finset.prod_nonneg fun _ _ => pow_nonneg h0 _)
    (sum_prod_pow_le_geom h0 h1)
def chebSeries {n : ℕ} (c : (Fin n → ℕ) → ℂ) (z : ComplexCoordinates n) : ℂ :=
  ∑' k, chebTerm c k z
theorem differentiable_chebTerm {n : ℕ} (c : (Fin n → ℕ) → ℂ) (k : Fin n → ℕ) :
    Differentiable ℂ (chebTerm c k) := by
  have hcheb : ∀ p, Differentiable ℂ (chebT p) := fun p => Polynomial.differentiable _
  have hj : ∀ j, Differentiable ℂ fun z : ComplexCoordinates n => chebT (k j) (z j) :=
    fun j => (hcheb _).comp (differentiable_apply j)
  show Differentiable ℂ fun z : ComplexCoordinates n => c k * ∏ j, chebT (k j) (z j)
  have hp : ∀ S : Finset (Fin n),
      Differentiable ℂ fun z : ComplexCoordinates n => ∏ j ∈ S, chebT (k j) (z j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hj a).mul ih
  exact (differentiable_const _).mul (hp Finset.univ)
theorem isHolomorphicIn_chebPartialSum {n : ℕ} (c : (Fin n → ℕ) → ℂ) (S : Finset (Fin n → ℕ))
    {O : Set (ComplexCoordinates n)} (hO : IsOpen O) :
    IsHolomorphicIn (N' := 1) O (fun z _ => ∑ k ∈ S, chebTerm c k z) := by
  have hd : Differentiable ℂ fun z : ComplexCoordinates n => ∑ k ∈ S, chebTerm c k z :=
    Differentiable.fun_sum fun k _ => differentiable_chebTerm c k
  refine ⟨hO, ?_, fun a _ j => Eventually.of_forall fun ζ => ?_⟩
  · exact (continuous_pi fun _ => hd.continuous).continuousOn
  · have hline : Differentiable ℂ fun ζ : ℂ => a + ζ • stdBasisVector j := by fun_prop
    exact differentiableAt_pi.2 fun _ => (hd.comp hline) ζ
theorem isHolomorphicIn_chebSeries (hlem : PowerSeriesHolomorphy.Properties) {n : ℕ}
    (c : (Fin n → ℕ) → ℂ) {O : Set (ComplexCoordinates n)} (hO : IsOpen O)
    {u : (Fin n → ℕ) → ℝ} (hu : Summable u) (hb : ∀ k, ∀ z ∈ O, ‖chebTerm c k z‖ ≤ u k) :
    IsHolomorphicIn (N' := 1) O (fun z _ => chebSeries c z) := by
  set pf : ℕ → Finset (Fin n → ℕ) := fun P => Fintype.piFinset fun _ => Finset.range P with hpf
  have hT : Tendsto pf atTop atTop := by
    refine tendsto_atTop_finset_of_monotone ?_ ?_
    · intro a b hab k hk
      rw [Fintype.mem_piFinset] at hk ⊢
      exact fun j => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 (hk j)) hab)
    · intro k
      refine ⟨Finset.univ.sup k + 1, ?_⟩
      rw [Fintype.mem_piFinset]
      intro j
      have h2 : k j ≤ Finset.univ.sup k := Finset.le_sup (f := k) (Finset.mem_univ j)
      exact Finset.mem_range.2 (by omega)
  have hU := tendstoUniformlyOn_tsum (f := fun k z => chebTerm c k z) hu (s := O) hb
  refine ((hlem.1 n O hO).2 1 (fun P z _ => ∑ k ∈ pf P, chebTerm c k z)
    (fun z _ => chebSeries c z) (fun P => isHolomorphicIn_chebPartialSum c _ hO) ?_)
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro ε hε
  refine (hT.eventually (hU ε hε)).mono fun P hP z hz => ?_
  exact (dist_pi_lt_iff hε).2 fun _ => hP z hz
theorem IsBoundedSliceExtension.differentiableAt {n : ℕ} {ς : ℝ} {hς : 1 < ς} {A : ℝ}
    {F : ComplexCoordinates n → ℂ} {j : Fin n} {x : ComplexCoordinates n} {h : ℂ → ℂ}
    (hx : IsBoundedSliceExtension ς hς A F j x h) {w : ℂ} (hw : w ∈ focalEllipse ς hς) :
    DifferentiableAt ℂ h w := by
  obtain ⟨⟨-, -, hd⟩, -, -⟩ := hx
  have hmem : (Equiv.funUnique (Fin 1) ℂ).symm w ∈
      (Equiv.funUnique (Fin 1) ℂ).symm '' focalEllipse ς hς := ⟨w, hw, rfl⟩
  have h1 := (hd _ hmem 0).self_of_nhds
  have h2 := (differentiableAt_pi.1 h1) 0
  have h3 : (fun ζ : ℂ => ((Equiv.funUnique (Fin 1) ℂ).symm ∘ h ∘
      (Equiv.funUnique (Fin 1) ℂ).symm.symm)
        ((Equiv.funUnique (Fin 1) ℂ).symm w + ζ • stdBasisVector 0) 0) = fun ζ => h (w + ζ) := by
    funext ζ
    simp [stdBasisVector]
  rw [h3] at h2
  have h4 : DifferentiableAt ℂ (fun ζ : ℂ => ζ - w) w := differentiableAt_id.sub_const w
  have h5 : DifferentiableAt ℂ (fun ζ : ℂ => h (w + ζ)) ((fun ζ : ℂ => ζ - w) w) := by
    simpa using h2
  have := DifferentiableAt.comp (g := fun ζ : ℂ => h (w + ζ)) (f := fun ζ : ℂ => ζ - w) w h5 h4
  simpa [Function.comp_def] using this
theorem exists_exponent_split {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ → ℝ} (hρ : ∀ z, 1 ≤ ρ z) {L : ℝ}
    (hL : 0 < L) {z : ComplexCoordinates n} (hz : Real.log (∏ j, ρ (z j)) < L) :
    ∃ s : Fin n → ℝ, (∀ j, 0 ≤ s j) ∧ ∑ j, s j < 1 ∧ ∀ j, ρ (z j) < Real.exp (s j * L) := by
  have hpos : ∀ j, 0 < ρ (z j) := fun j => lt_of_lt_of_le one_pos (hρ _)
  set σ : Fin n → ℝ := fun j => Real.log (ρ (z j)) / L with hσ
  have hsig : ∑ j, σ j < 1 := by
    rw [Real.log_prod fun j _ => (hpos j).ne'] at hz
    rw [hσ, ← Finset.sum_div, div_lt_one hL]
    exact hz
  have hσ0 : ∀ j, 0 ≤ σ j := fun j => div_nonneg (Real.log_nonneg (hρ _)) hL.le
  set d : ℝ := (1 - ∑ j, σ j) / (2 * n) with hd
  have hd0 : 0 < d := div_pos (by linarith) (by positivity)
  refine ⟨fun j => σ j + d, fun j => add_nonneg (hσ0 j) hd0.le, ?_, fun j => ?_⟩
  · rw [Finset.sum_add_distrib]
    have : ∑ _j : Fin n, d = (1 - ∑ j, σ j) / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hd]
      field_simp
    rw [this]; linarith
  · have h1 : Real.log (ρ (z j)) = σ j * L := by
      rw [hσ]; field_simp
    rw [← Real.log_lt_iff_lt_exp (hpos j), h1]
    have := mul_lt_mul_of_pos_right hd0 hL
    nlinarith
theorem integral_cos_int_mul (a : ℤ) :
    ∫ t in (0 : ℝ)..π, Real.cos (a * t) = if a = 0 then π else 0 := by apply _root_.YangMills.Construction.SpinHarmonics.BondWeightCoeffs.integral_cos_intCast_mul_zero_pi <;> assumption
theorem integral_cos_mul_cosMode (p q : ℕ) :
    ∫ t, Real.cos (p * t) * cosMode q t ∂halfPeriodMeasure = if p = q then 1 else 0 := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have h1 : ∫ t, Real.cos (p * t) * cosMode q t ∂halfPeriodMeasure =
      ∫ t in (0 : ℝ)..π, Real.cos (p * t) * cosMode q t := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]; rfl
  have h2 : ∀ t : ℝ, Real.cos (p * t) * cosMode q t = chebWeight q / π * (1 / 2) *
      (Real.cos (((p + q : ℕ) : ℤ) * t) + Real.cos ((((p : ℤ) - q : ℤ) : ℝ) * t)) := by
    intro t
    have e1 : (((p + q : ℕ) : ℤ) : ℝ) * t = p * t + q * t := by push_cast; ring
    have e2 : ((((p : ℤ) - q : ℤ) : ℝ)) * t = p * t - q * t := by push_cast; ring
    rw [e1, e2, Real.cos_add, Real.cos_sub, cosMode]; ring
  have hc : ∀ a : ℤ, Continuous fun t : ℝ => Real.cos (a * t) := fun a => by fun_prop
  rw [h1]
  simp only [h2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _), integral_cos_int_mul,
    integral_cos_int_mul]
  by_cases hpq : p = q
  · subst hpq
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp [chebWeight]; field_simp; norm_num
    · have : p ≠ 0 := hp.ne'
      simp [chebWeight, this]; field_simp
  · have h3 : (((p + q : ℕ) : ℤ)) ≠ 0 := by
      intro h; apply hpq; omega
    have h4 : ((p : ℤ) - q) ≠ 0 := by
      intro h; apply hpq; omega
    rw [if_neg h3, if_neg h4, if_neg hpq]
    simp
theorem integral_cosProduct_mul_cosModeProduct {n : ℕ} (k k' : Fin n → ℕ) :
    ∫ α, cosProduct k α * cosModeProduct k' α ∂cubeMeasure n = if k = k' then 1 else 0 := by
  have h1 : ∀ α : Fin n → ℝ, cosProduct k α * cosModeProduct k' α =
      ∏ j, Real.cos (k j * α j) * cosMode (k' j) (α j) := fun α => by
    rw [cosProduct, cosModeProduct, Finset.prod_mul_distrib]
  simp only [h1]
  rw [cubeMeasure, integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (fun j t => Real.cos (k j * t) * cosMode (k' j) t)]
  simp only [integral_cos_mul_cosMode]
  split_ifs with h
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
def cosComplexVector {n : ℕ} (α : Fin n → ℝ) : ComplexCoordinates n :=
  fun j => ((Real.cos (α j) : ℝ) : ℂ)
theorem continuous_cosComplexVector {n : ℕ} : Continuous (cosComplexVector (n := n)) := by
  unfold cosComplexVector; fun_prop
theorem chebTerm_cosComplexVector {n : ℕ} (c : (Fin n → ℕ) → ℂ) (k : Fin n → ℕ)
    (α : Fin n → ℝ) : chebTerm c k (cosComplexVector α) = c k * ((cosProduct k α : ℝ) : ℂ) := by
  simp only [chebTerm, cosComplexVector, cosProduct, chebT_cos]
  push_cast
  rfl
theorem abs_cosModeProduct_le {n : ℕ} (k : Fin n → ℕ) (α : Fin n → ℝ) :
    |cosModeProduct k α| ≤ (2 / π) ^ n := by
  rw [cosModeProduct, Finset.abs_prod]
  calc _ ≤ ∏ _i : Fin n, 2 / π :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => abs_cosMode_le _ _
    _ = _ := by simp [div_pow]
theorem integral_chebSeries_mul_cosModeProduct {n : ℕ} (c : (Fin n → ℕ) → ℂ)
    {u : (Fin n → ℕ) → ℝ} (hu : Summable u)
    (hb : ∀ k α, ‖chebTerm c k (cosComplexVector α)‖ ≤ u k) (k' : Fin n → ℕ) :
    ∫ α, chebSeries c (cosComplexVector α) * (cosModeProduct k' α : ℂ) ∂cubeMeasure n = c k' := by
  set Fk : (Fin n → ℕ) → (Fin n → ℝ) → ℂ :=
    fun k α => chebTerm c k (cosComplexVector α) * (cosModeProduct k' α : ℂ) with hFk
  have hcont : ∀ k, Continuous (Fk k) := fun k =>
    ((differentiable_chebTerm c k).continuous.comp continuous_cosComplexVector).mul
      (Complex.continuous_ofReal.comp (continuous_cosModeProduct k'))
  have hint : ∀ k, Integrable (Fk k) (cubeMeasure n) := fun k => integrable_cubeMeasure (hcont k)
  have hnorm : ∀ k α, ‖Fk k α‖ ≤ u k * (2 / π) ^ n := by
    intro k α
    rw [hFk]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hb k α) (abs_cosModeProduct_le k' α) (abs_nonneg _)
      ((norm_nonneg _).trans (hb k α))
  have hsum : Summable fun k => ∫ α, ‖Fk k α‖ ∂cubeMeasure n := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((hu.mul_right ((2 / π) ^ n)).mul_right (π ^ n))
    have := norm_integral_le_of_norm_le_const (μ := cubeMeasure n) (f := fun α => ‖Fk k α‖)
      (Eventually.of_forall fun α => by simpa using hnorm k α)
    rw [cubeMeasure_real_univ] at this
    exact (le_abs_self _).trans this
  have hs := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ α, ∑' k, Fk k α =
      chebSeries c (cosComplexVector α) * (cosModeProduct k' α : ℂ) := fun α => by
    rw [hFk, chebSeries]
    exact tsum_mul_right
  simp only [htsum] at hs
  have hterm : ∀ k, ∫ α, Fk k α ∂cubeMeasure n = if k = k' then c k' else 0 := by
    intro k
    have h1 : ∀ α, Fk k α = c k * ((cosProduct k α * cosModeProduct k' α : ℝ) : ℂ) := fun α => by
      rw [hFk]
      simp only [chebTerm_cosComplexVector]
      push_cast
      ring
    simp only [h1]
    rw [integral_const_mul, integral_complex_ofReal, integral_cosProduct_mul_cosModeProduct]
    split_ifs with h
    · subst h; simp
    · simp
  simp only [hterm] at hs
  exact hs.unique (hasSum_ite_eq k' (c k'))
theorem complex_eq_zero_on_cube_of_cosCoeff {n : ℕ} {Δ : (Fin n → ℝ) → ℂ}
    (hΔ : ContinuousOn Δ (univ.pi fun _ => Icc (-1 : ℝ) 1))
    (h : ∀ k : Fin n → ℕ, ∫ α, Δ (cosVector α) * (cosModeProduct k α : ℂ) ∂cubeMeasure n = 0) :
    ∀ x ∈ (univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1), Δ x = 0 := by
  have hmem : ∀ α : Fin n → ℝ, cosVector α ∈ (univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) :=
    fun α j _ => ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hD : Continuous fun α => Δ (cosVector α) := hΔ.comp_continuous continuous_cosVector hmem
  have hc : ∀ k : Fin n → ℕ, ∫ α, Δ (cosVector α) * (cosProduct k α : ℂ) ∂cubeMeasure n = 0 := by
    intro k
    have hw : (∏ j, chebWeight (k j) / π) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => (div_pos (chebWeight_pos _) Real.pi_pos).ne'
    have h1 := h k
    have h2 : ∀ α, Δ (cosVector α) * (cosModeProduct k α : ℂ) =
        ((∏ j, chebWeight (k j) / π : ℝ) : ℂ) * (Δ (cosVector α) * (cosProduct k α : ℂ)) :=
      fun α => by
        rw [cosModeProduct_eq]; push_cast; ring
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hw)
  have hint : ∀ k : Fin n → ℕ, Integrable (fun α => Δ (cosVector α) * (cosProduct k α : ℂ))
      (cubeMeasure n) := fun k =>
    integrable_cubeMeasure (hD.mul (Complex.continuous_ofReal.comp (continuous_cosProduct k)))
  have hre := eq_zero_on_cube_of_cosCoeff (u := fun x => (Δ x).re)
    (Complex.continuous_re.comp_continuousOn hΔ) (fun k => by
      have := Complex.reCLM.integral_comp_comm (hint k)
      rw [hc k] at this
      simpa using this)
  have him := eq_zero_on_cube_of_cosCoeff (u := fun x => (Δ x).im)
    (Complex.continuous_im.comp_continuousOn hΔ) (fun k => by
      have := Complex.imCLM.integral_comp_comm (hint k)
      rw [hc k] at this
      simpa using this)
  exact fun x hx => Complex.ext (hre x hx) (him x hx)
theorem cosComplexVector_mem {n : ℕ} (α : Fin n → ℝ) :
    cosComplexVector α ∈ realClosedCube n := fun j =>
  ⟨Complex.ofReal_im _, by
    simp only [cosComplexVector, Complex.ofReal_re]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩⟩
theorem norm_cosCoeff_le_exp (hj : JoukowskiRadius.JoukowskiRadiusProperties) {m : ℕ} {ς : ℝ}
    {hς : 1 < ς} {A : ℝ} {F : ComplexCoordinates (m + 1) → ℂ}
    (hF : ContinuousOn F (realClosedCube (m + 1)))
    (hsep : ∀ j : Fin (m + 1), ∀ x ∈ realClosedCube (m + 1),
      ∃ h : ℂ → ℂ, IsBoundedSliceExtension ς hς A F j x h)
    (k : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    ‖cosCoeff (fun α => F (cosComplexVector α)) k‖ ≤
      2 ^ (m + 1) * A * Real.exp (-(Real.log ς * k j)) := by
  have hς0 : 0 < ς := by linarith
  have hG : Continuous fun α => F (cosComplexVector α) :=
    hF.comp_continuous continuous_cosComplexVector cosComplexVector_mem
  refine (norm_cosCoeff_le_of_slice hG k j (B := π * A * (ς ^ k j)⁻¹) fun y => ?_).trans
    (le_of_eq ?_)
  · obtain ⟨h, hh⟩ := hsep j _ (cosComplexVector_mem (j.insertNth 0 y))
    have hval : ∀ t : ℝ, F (cosComplexVector (j.insertNth t y)) = h ((Real.cos t : ℝ) : ℂ) := by
      intro t
      rw [hh.2.2 (Real.cos t) ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩]
      congr 1
      funext i
      rcases eq_or_ne i j with rfl | hne
      · simp [cosComplexVector]
      · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hne
        simp [cosComplexVector]
    simp only [hval]
    have hin : ∀ ω : ℂ, ς⁻¹ < ‖ω‖ → ‖ω‖ < ς → (1 / 2 : ℂ) * (ω + ω⁻¹) ∈ focalEllipse ς hς := by
      intro ω ha hb
      have h0 : ω ≠ 0 := by
        intro h0
        have : (0 : ℝ) < ς⁻¹ := inv_pos.2 hς0
        simp [h0] at ha
        linarith
      show joukowskiRadius _ < ς
      rw [hj.2.2.2.2.2.1 ω h0]
      exact max_lt hb (inv_lt_of_inv_lt₀ hς0 ha)
    refine norm_cosCoeff_le h hς ?_
      (fun ω ha hb => IsBoundedSliceExtension.differentiableAt hh (hin ω ha hb))
      (fun ω ha hb => hh.2.1 _ (hin ω ha hb)) (k j)
    have : (fun θ : ℝ => h ((Real.cos θ : ℝ) : ℂ)) =
        fun θ : ℝ => F (cosComplexVector (j.insertNth θ y)) := funext fun θ => (hval θ).symm
    rw [this]
    exact hG.comp (Continuous.finInsertNth j continuous_id continuous_const)
  · have hexp : Real.exp (-(Real.log ς * k j)) = (ς ^ k j)⁻¹ := by
      rw [Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hς0]
    rw [hexp]
    have hp : π ≠ 0 := Real.pi_ne_zero
    field_simp
theorem separateImpliesJoint_holds (hj : JoukowskiRadius.JoukowskiRadiusProperties)
    (hlem : PowerSeriesHolomorphy.Properties) : SeparateImpliesJoint := by
  intro n hn ς hς A hA F hF hsep
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hς0 : 0 < ς := by linarith
  set L : ℝ := Real.log ς with hLdef
  have hL : 0 < L := Real.log_pos hς
  have hρ1 : ∀ z, 1 ≤ joukowskiRadius z := hj.1
  have hρ0 : ∀ z, 0 ≤ joukowskiRadius z := fun z => zero_le_one.trans (hρ1 z)
  have hρc : Continuous joukowskiRadius := hj.2.1
  have hDo : IsOpen (polyEllipseDomain (m + 1) hn ς hς) := (hj.2.2.2.2.1 ς hς (m + 1) hn).1
  have hcubeD : realClosedCube (m + 1) ⊆ polyEllipseDomain (m + 1) hn ς hς := by
    intro x hx
    refine (hj.2.2.2.2.1 ς hς (m + 1) hn).2 fun j => ⟨(x j).re, (hx j).2, ?_⟩
    exact Complex.ext rfl (by simp [(hx j).1])
  set c : (Fin (m + 1) → ℕ) → ℂ := cosCoeff (fun α => F (cosComplexVector α)) with hcdef
  set C : ℝ := 2 ^ (m + 1) * A with hCdef
  have hC : 0 ≤ C := by positivity
  have hdecay : ∀ k j, ‖c k‖ ≤ C * Real.exp (-(L * k j)) := norm_cosCoeff_le_exp hj hF hsep
  have hq : ∀ s : Fin (m + 1) → ℝ, ∑ j, s j < 1 →
      Real.exp (-((1 - ∑ i, s i) / ((m + 1 : ℕ) : ℝ) * L)) < 1 := by
    intro s hs
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    exact mul_pos (div_pos (by linarith) (by positivity)) hL
  have hterm : ∀ (s : Fin (m + 1) → ℝ), (∀ j, 0 ≤ s j) → ∑ j, s j < 1 → ∀ k z,
      (∀ j, joukowskiRadius (z j) ≤ Real.exp (s j * L)) →
      ‖chebTerm c k z‖ ≤ C * ∏ j, Real.exp (-((1 - ∑ i, s i) / ((m + 1 : ℕ) : ℝ) * L)) ^ k j :=
    fun s hs hsum k z hz =>
      norm_chebTerm_le hn hC hL hdecay hρ0 (norm_chebT_le_joukowskiRadius hj) hs hsum k hz
  have hsummable : ∀ s : Fin (m + 1) → ℝ, ∑ j, s j < 1 → Summable fun k : Fin (m + 1) → ℕ =>
      C * ∏ j, Real.exp (-((1 - ∑ i, s i) / ((m + 1 : ℕ) : ℝ) * L)) ^ k j :=
    fun s hs => (summable_prod_geom (Real.exp_pos _).le (hq s hs)).mul_left C
  have hOo : ∀ s : Fin (m + 1) → ℝ,
      IsOpen {z : ComplexCoordinates (m + 1) | ∀ j, joukowskiRadius (z j) < Real.exp (s j * L)} := by
    intro s
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt (hρc.comp (continuous_apply j)) continuous_const
  have hOholo : ∀ s : Fin (m + 1) → ℝ, (∀ j, 0 ≤ s j) → ∑ j, s j < 1 →
      IsHolomorphicIn (N' := 1)
        {z : ComplexCoordinates (m + 1) | ∀ j, joukowskiRadius (z j) < Real.exp (s j * L)}
        (fun z _ => chebSeries c z) := fun s hs hsum =>
    isHolomorphicIn_chebSeries hlem c (hOo s) (hsummable s hsum)
      fun k z hz => hterm s hs hsum k z fun j => (hz j).le
  have hcover : ∀ a ∈ polyEllipseDomain (m + 1) hn ς hς, ∃ s : Fin (m + 1) → ℝ,
      (∀ j, 0 ≤ s j) ∧ ∑ j, s j < 1 ∧ ∀ j, joukowskiRadius (a j) < Real.exp (s j * L) := by
    intro a ha
    refine exists_exponent_split hn hρ1 hL ?_
    exact Real.log_lt_log (Finset.prod_pos fun j _ => lt_of_lt_of_le one_pos (hρ1 _)) ha
  have hholo : IsHolomorphicIn (N' := 1) (polyEllipseDomain (m + 1) hn ς hς)
      (fun z _ => chebSeries c z) := by
    refine ⟨hDo, fun a ha => ?_, fun a ha j => ?_⟩
    · obtain ⟨s, hs, hsum, haO⟩ := hcover a ha
      exact (((hOholo s hs hsum).2.1 a haO).continuousAt
        ((hOo s).mem_nhds haO)).continuousWithinAt
    · obtain ⟨s, hs, hsum, haO⟩ := hcover a ha
      exact (hOholo s hs hsum).2.2 a haO j
  have hcs : ContinuousOn (chebSeries c) (polyEllipseDomain (m + 1) hn ς hς) :=
    (continuous_apply (0 : Fin 1)).comp_continuousOn hholo.2.1
  have hone : ∀ (α : Fin (m + 1) → ℝ) j,
      joukowskiRadius (cosComplexVector α j) ≤ Real.exp (0 * L) := by
    intro α j
    have : joukowskiRadius (cosComplexVector α j) = 1 := (hj.2.2.1 _).2
      ⟨Real.cos (α j), ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩, rfl⟩
    simp [this]
  have hzero : ∑ _j : Fin (m + 1), (0 : ℝ) < 1 := by simp
  have hcoef := integral_chebSeries_mul_cosModeProduct c (hsummable (fun _ => 0) hzero)
    (fun k α => hterm (fun _ => 0) (fun _ => le_rfl) hzero k (cosComplexVector α) (hone α))
  have hsc : Continuous fun α => chebSeries c (cosComplexVector α) :=
    hcs.comp_continuous continuous_cosComplexVector fun α => hcubeD (cosComplexVector_mem α)
  have hG : Continuous fun α => F (cosComplexVector α) :=
    hF.comp_continuous continuous_cosComplexVector cosComplexVector_mem
  set ι : (Fin (m + 1) → ℝ) → ComplexCoordinates (m + 1) := fun x j => ((x j : ℝ) : ℂ) with hι
  have hιc : Continuous ι := by
    rw [hι]; fun_prop
  have hιm : MapsTo ι (univ.pi fun _ => Icc (-1 : ℝ) 1) (realClosedCube (m + 1)) := fun x hx j =>
    ⟨Complex.ofReal_im _, by simpa [hι] using hx j (mem_univ j)⟩
  have hvanish := complex_eq_zero_on_cube_of_cosCoeff (Δ := fun x => chebSeries c (ι x) - F (ι x))
    (((hcs.mono hcubeD).comp hιc.continuousOn hιm).sub (hF.comp hιc.continuousOn hιm))
    (fun k => by
      have hw : Continuous fun α => ((cosModeProduct k α : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_cosModeProduct k)
      have hi := integral_sub (μ := cubeMeasure (m + 1))
        (f := fun α => chebSeries c (cosComplexVector α) * ((cosModeProduct k α : ℝ) : ℂ))
        (g := fun α => F (cosComplexVector α) * ((cosModeProduct k α : ℝ) : ℂ))
        (integrable_cubeMeasure (hsc.mul hw)) (integrable_cubeMeasure (hG.mul hw))
      have hsame : ∀ α, (chebSeries c (ι (cosVector α)) - F (ι (cosVector α))) *
          ((cosModeProduct k α : ℝ) : ℂ) =
          chebSeries c (cosComplexVector α) * ((cosModeProduct k α : ℝ) : ℂ) -
            F (cosComplexVector α) * ((cosModeProduct k α : ℝ) : ℂ) :=
        fun α => sub_mul _ _ _
      simp only [hsame]
      rw [hi, hcoef k]
      exact sub_self _)
  have heq : ∀ x ∈ realClosedCube (m + 1), chebSeries c x = F x := by
    intro x hx
    have hx' : ι (fun j => (x j).re) = x := by
      funext j
      exact Complex.ext rfl (by simp [hι, (hx j).1])
    have := hvanish (fun j => (x j).re) fun j _ => (hx j).2
    rw [hx'] at this
    exact sub_eq_zero.1 this
  refine ⟨⟨chebSeries c, hholo, hcubeD, heq, fun s hs hsum z hz => ?_⟩, ?_⟩
  · have hz' : ∀ j, joukowskiRadius (z j) ≤ Real.exp (s j * L) := fun j => by
      have := hz j
      rwa [rpowPos_eq_exp hς0] at this
    set q : ℝ := Real.exp (-((1 - ∑ i, s i) / ((m + 1 : ℕ) : ℝ) * L)) with hqdef
    have hq1 : q < 1 := hq s hsum
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hle := tsum_of_norm_bounded (hsummable s hsum).hasSum
      (fun k => hterm s hs hsum k z hz')
    have hsumle : ∑' k : Fin (m + 1) → ℕ, C * ∏ j, q ^ k j ≤ C * ((1 - q)⁻¹) ^ (m + 1) := by
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left
        ((summable_prod_geom hq0 hq1).tsum_le_of_sum_le (sum_prod_pow_le_geom hq0 hq1)) hC
    have hpow : rpowPos ς (-(1 - ∑ j, s j) / ((m + 1 : ℕ) : ℝ)) = q := by
      rw [rpowPos_eq_exp hς0, hqdef, neg_div, neg_mul]
    rw [hpow, zpow_neg, zpow_natCast, ← inv_pow]
    exact hle.trans hsumle
  · have hRA := ((hlem.1 (m + 1) _ hDo).1 1 _ hholo).2.2.2.2
    refine ⟨⟨{z | ∀ j, (z j).re ∈ Ioo (-1 : ℝ) 1}, ?_, ?_⟩, fun a ha => ?_⟩
    · simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun j =>
        (isOpen_Ioo.preimage (Complex.continuous_re.comp (continuous_apply j)))
    · ext z
      constructor
      · intro hz
        exact ⟨fun j => (hz j).2, fun j => (hz j).1⟩
      · rintro ⟨h1, h2⟩ j
        exact ⟨h2 j, h1 j⟩
    · have haC : a ∈ realClosedCube (m + 1) := fun j => ⟨(ha j).1, Ioo_subset_Icc_self (ha j).2⟩
      obtain ⟨co, hco⟩ := hRA.2 a ⟨hcubeD haC, fun j => (ha j).1⟩
      refine ⟨co, ?_⟩
      have hnear : ∀ᶠ z in 𝓝[realLocus (m + 1)] a, z ∈ realClosedCube (m + 1) := by
        have hopen : IsOpen {z : ComplexCoordinates (m + 1) | ∀ j, (z j).re ∈ Ioo (-1 : ℝ) 1} := by
          simp only [Set.ofPred_forall]
          exact isOpen_iInter_of_finite fun j =>
            (isOpen_Ioo.preimage (Complex.continuous_re.comp (continuous_apply j)))
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds fun j => (ha j).2)] with z h1 h2 j
        exact ⟨h1 j, Ioo_subset_Icc_self (h2 j)⟩
      filter_upwards [hco, hnear] with z h1 h2
      have : (fun _ : Fin 1 => F z) = fun _ => chebSeries c z := by rw [heq z h2]
      rw [this]
      exact h1
end YangMills.Construction.JointHolomorphy
end
