import YangMills.Construction.LawInAState.FormsOnAnEvent
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory Matrix ProbabilityTheory
open scoped ENNReal NNReal
namespace YangMills.Construction.QuadraticConcentration
section Gaussian
variable {ι : Type} [Fintype ι]
private lemma map_linear_eq_gaussianReal {C : ι → ι → ℝ} {μ : Measure (ι → ℝ)} (hμ : WickMoments.IsCenteredGaussian C μ) (t : ι → ℝ)
    (hpos : 0 ≤ ∑ i, ∑ j, t i * C i j * t j) :
    μ.map (fun ξ => ∑ i, t i * ξ i) = gaussianReal 0 (∑ i, ∑ j, t i * C i j * t j).toNNReal := by
  obtain ⟨hp, hc⟩ := hμ
  have hm : Measurable (fun ξ : ι → ℝ => ∑ i, t i * ξ i) := by fun_prop
  haveI : IsProbabilityMeasure (μ.map (fun ξ => ∑ i, t i * ξ i)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_charFun (funext fun s => ?_)
  rw [charFun_gaussianReal, charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  have h1 := hc (fun i => s * t i)
  have e1 : ∀ ξ : ι → ℝ, Complex.exp ((s : ℂ) * ((∑ i, t i * ξ i : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((∑ i, s * t i * ξ i : ℝ) : ℂ)) := by
    intro ξ
    congr 1
    have : (∑ i, s * t i * ξ i) = s * ∑ i, t i * ξ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; push_cast; ring
  simp_rw [e1]
  rw [h1]
  congr 1
  have e2 : (∑ i, ∑ j, s * t i * C i j * (s * t j)) = s ^ 2 * ∑ i, ∑ j, t i * C i j * t j := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e2, Real.coe_toNNReal _ hpos]
  push_cast
  ring
private def MemLpTwoPow (μ : Measure (ι → ℝ)) (g : (ι → ℝ) → ℝ) : Prop := ∀ n : ℕ, MemLp g ((2 : ℝ≥0∞) ^ n) μ
private lemma holderTriple_two_pow (n : ℕ) : ENNReal.HolderTriple ((2 : ℝ≥0∞) ^ (n + 1)) ((2 : ℝ≥0∞) ^ (n + 1)) ((2 : ℝ≥0∞) ^ n) := by
  refine ⟨?_⟩
  rw [pow_succ, ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp)), ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
private lemma MemLpTwoPow.mul {μ : Measure (ι → ℝ)} {f g : (ι → ℝ) → ℝ} (hf : MemLpTwoPow μ f) (hg : MemLpTwoPow μ g) :
    MemLpTwoPow μ (fun ξ => f ξ * g ξ) := fun n => by
  haveI := holderTriple_two_pow n
  exact (hg (n + 1)).mul' (hf (n + 1))
private lemma MemLpTwoPow.add {μ : Measure (ι → ℝ)} {f g : (ι → ℝ) → ℝ} (hf : MemLpTwoPow μ f) (hg : MemLpTwoPow μ g) :
    MemLpTwoPow μ (fun ξ => f ξ + g ξ) := fun n => (hf n).add (hg n)
private lemma MemLpTwoPow.const {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ] (c : ℝ) : MemLpTwoPow μ (fun _ => c) := fun n => memLp_const c
private lemma MemLpTwoPow.sum {μ : Measure (ι → ℝ)} {κ : Type} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ} (hf : ∀ i ∈ s, MemLpTwoPow μ (f i)) :
    MemLpTwoPow μ (fun ξ => ∑ i ∈ s, f i ξ) := fun n => by
  have := memLp_finsetSum' (p := (2 : ℝ≥0∞) ^ n) s (fun i hi => hf i hi n)
  convert this using 1
  ext ξ; simp
private lemma memLpTwoPow_coord {C : ι → ι → ℝ} {μ : Measure (ι → ℝ)} (hμ : WickMoments.IsCenteredGaussian C μ)
    (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) (i : ι) [DecidableEq ι] : MemLpTwoPow μ (fun ξ => ξ i) := fun n => by
  have h := map_linear_eq_gaussianReal hμ (Pi.single i 1) (hpos _)
  have hm : Measurable (fun ξ : ι → ℝ => ∑ j, (Pi.single i 1 : ι → ℝ) j * ξ j) := by fun_prop
  have e : (fun ξ : ι → ℝ => ∑ j, (Pi.single i 1 : ι → ℝ) j * ξ j) = fun ξ => ξ i := by
    ext ξ; simp [Pi.single_apply]
  have h2 : MemLp id ((2 : ℝ≥0∞) ^ n) (μ.map (fun ξ : ι → ℝ => ∑ j, (Pi.single i 1 : ι → ℝ) j * ξ j)) := by
    rw [h]; exact memLp_id_gaussianReal' _ (by simp)
  have h3 := (memLp_map_measure_iff (by fun_prop) hm.aemeasurable).1 h2
  rw [e] at h3
  exact h3
private lemma integral_linear_and_sq {C : ι → ι → ℝ} {μ : Measure (ι → ℝ)} (hμ : WickMoments.IsCenteredGaussian C μ) (t : ι → ℝ)
    (hpos : 0 ≤ ∑ i, ∑ j, t i * C i j * t j) :
    ∫ ξ, (∑ i, t i * ξ i) ∂μ = 0 ∧ ∫ ξ, (∑ i, t i * ξ i) ^ 2 ∂μ = ∑ i, ∑ j, t i * C i j * t j := by
  have h := map_linear_eq_gaussianReal hμ t hpos
  have hm : Measurable (fun ξ : ι → ℝ => ∑ i, t i * ξ i) := by fun_prop
  constructor
  · have := integral_map (μ := μ) hm.aemeasurable (f := fun x : ℝ => x) (by fun_prop)
    rw [h, integral_id_gaussianReal] at this
    exact this.symm
  · have := integral_map (μ := μ) hm.aemeasurable (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [h] at this
    have hv : ∫ x, x ^ 2 ∂gaussianReal 0 (∑ i, ∑ j, t i * C i j * t j).toNNReal = ∑ i, ∑ j, t i * C i j * t j := by
      have := variance_id_gaussianReal (μ := 0) (v := (∑ i, ∑ j, t i * C i j * t j).toNNReal)
      rw [variance_of_integral_eq_zero aemeasurable_id (by simp [integral_id_gaussianReal])] at this
      simpa [Real.coe_toNNReal _ hpos] using this
    rw [hv] at this
    exact this.symm
private lemma dotProduct_mulVec_eq_sum (y : ι → ℝ) (M : Matrix ι ι ℝ) : y ⬝ᵥ M.mulVec y = ∑ i, ∑ j, y i * (M i j * y j) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
private lemma integral_coord_mul_coord [DecidableEq ι] {C : ι → ι → ℝ} {μ : Measure (ι → ℝ)} (hμ : WickMoments.IsCenteredGaussian C μ)
    (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) (hs : ∀ i j, C i j = C j i) (i j : ι) :
    ∫ ξ, ξ i * ξ j ∂μ = C i j := by
  haveI := hμ.1
  have hi := memLpTwoPow_coord hμ hpos i
  have hj := memLpTwoPow_coord hμ hpos j
  have h1 := (integral_linear_and_sq hμ (Pi.single i 1 + Pi.single j 1) (hpos _)).2
  have h2 := (integral_linear_and_sq hμ (Pi.single i 1 - Pi.single j 1) (hpos _)).2
  have e1 : ∀ ξ : ι → ℝ, ∑ k, (Pi.single i 1 + Pi.single j 1 : ι → ℝ) k * ξ k = ξ i + ξ j := by
    intro ξ; simp [add_mul, Finset.sum_add_distrib, Pi.single_apply]
  have e2 : ∀ ξ : ι → ℝ, ∑ k, (Pi.single i 1 - Pi.single j 1 : ι → ℝ) k * ξ k = ξ i - ξ j := by
    intro ξ; simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  have c1 : ∑ k, ∑ l, (Pi.single i 1 + Pi.single j 1 : ι → ℝ) k * C k l * (Pi.single i 1 + Pi.single j 1 : ι → ℝ) l =
      C i i + C i j + C j i + C j j := by
    simp [add_mul, mul_add, Finset.sum_add_distrib, Pi.single_apply]; ring
  have c2 : ∑ k, ∑ l, (Pi.single i 1 - Pi.single j 1 : ι → ℝ) k * C k l * (Pi.single i 1 - Pi.single j 1 : ι → ℝ) l =
      C i i - C i j - C j i + C j j := by
    simp [sub_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]; ring
  simp_rw [e1] at h1
  simp_rw [e2] at h2
  rw [c1] at h1
  rw [c2] at h2
  have sub : MemLpTwoPow μ (fun ξ => ξ i + (-1) * ξ j) := hi.add ((MemLpTwoPow.const (-1)).mul hj)
  have ad : MemLpTwoPow μ (fun ξ => ξ i + ξ j) := hi.add hj
  have i1 : Integrable (fun ξ : ι → ℝ => (ξ i + ξ j) ^ 2) μ := by
    have := (ad.mul ad 0); simp only [pow_zero] at this
    rw [memLp_one_iff_integrable] at this
    simpa [sq] using this
  have i2 : Integrable (fun ξ : ι → ℝ => (ξ i - ξ j) ^ 2) μ := by
    have := (sub.mul sub 0); simp only [pow_zero] at this
    rw [memLp_one_iff_integrable] at this
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [sq]; ring
  have e3 : ∀ ξ : ι → ℝ, ξ i * ξ j = (1 / 4) * ((ξ i + ξ j) ^ 2 - (ξ i - ξ j) ^ 2) := by intro ξ; ring
  simp_rw [e3]
  rw [integral_const_mul, integral_sub i1 i2, h1, h2, hs j i]
  ring
private lemma memLpTwoPow_centeredQuadraticForm [DecidableEq ι] {C : ι → ι → ℝ} {μ : Measure (ι → ℝ)} (hμ : WickMoments.IsCenteredGaussian C μ)
    (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) (C' M : Matrix ι ι ℝ) (F : ι → ℝ) :
    MemLpTwoPow μ (centeredQuadraticForm C' M F) := by
  haveI := hμ.1
  have hc := memLpTwoPow_coord hμ hpos
  have hy : ∀ i, MemLpTwoPow μ (fun ξ => (F + ξ) i) := fun i => (MemLpTwoPow.const (F i)).add (hc i)
  have h1 : MemLpTwoPow μ (fun ξ => ∑ i, ∑ j, (F + ξ) i * (M i j * (F + ξ) j)) :=
    MemLpTwoPow.sum _ fun i _ => MemLpTwoPow.sum _ fun j _ => (hy i).mul ((MemLpTwoPow.const (M i j)).mul (hy j))
  have h2 := ((MemLpTwoPow.const (μ := μ) (1 / 2 : ℝ)).mul h1).add (MemLpTwoPow.const (-((1 / 2) * Matrix.trace (M * C'))))
  intro n
  have := h2 n
  refine this.ae_eq (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [centeredQuadraticForm, dotProduct_mulVec_eq_sum]
  ring
private lemma integral_centeredQuadraticForm [DecidableEq ι] {C : Matrix ι ι ℝ} {μ : Measure (ι → ℝ)} (hμ : WickMoments.IsCenteredGaussian (fun i j => C i j) μ)
    (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) (hs : C.IsSymm) (M : Matrix ι ι ℝ) (F : ι → ℝ) :
    ∫ ξ, centeredQuadraticForm C M F ξ ∂μ = (1 / 2) * (F ⬝ᵥ M.mulVec F) := by
  haveI := hμ.1
  have hc := memLpTwoPow_coord hμ hpos
  have hsym : ∀ i j, C i j = C j i := fun i j => by
    have := congrFun (congrFun hs j) i; simpa [Matrix.transpose_apply] using this
  have h2 := integral_coord_mul_coord hμ hpos hsym
  have m1 : ∀ i, ∫ ξ, ξ i ∂μ = 0 := fun i => by
    have := (integral_linear_and_sq hμ (Pi.single i 1) (hpos _)).1
    simpa [Pi.single_apply] using this
  have int1 : ∀ i, Integrable (fun ξ : ι → ℝ => ξ i) μ := fun i => by
    have := hc i 0; simp only [pow_zero] at this; exact memLp_one_iff_integrable.1 this
  have int2 : ∀ i j, Integrable (fun ξ : ι → ℝ => ξ i * ξ j) μ := fun i j => by
    have := (hc i).mul (hc j) 0; simp only [pow_zero] at this; exact memLp_one_iff_integrable.1 this
  have term : ∀ i j, ∫ ξ, (F + ξ) i * (M i j * (F + ξ) j) ∂μ = M i j * (F i * F j + C i j) := by
    intro i j
    have e : ∀ ξ : ι → ℝ, (F + ξ) i * (M i j * (F + ξ) j) =
        M i j * (F i * F j) + (M i j * F i) * ξ j + (M i j * F j) * ξ i + M i j * (ξ i * ξ j) := by
      intro ξ; simp only [Pi.add_apply]; ring
    simp_rw [e]
    have I0 : Integrable (fun _ : ι → ℝ => M i j * (F i * F j)) μ := integrable_const _
    have Ia : Integrable (fun ξ : ι → ℝ => (M i j * F i) * ξ j) μ := (int1 j).const_mul _
    have Ib : Integrable (fun ξ : ι → ℝ => (M i j * F j) * ξ i) μ := (int1 i).const_mul _
    have Ic : Integrable (fun ξ : ι → ℝ => M i j * (ξ i * ξ j)) μ := (int2 i j).const_mul _
    have I1 : Integrable (fun ξ : ι → ℝ => M i j * (F i * F j) + (M i j * F i) * ξ j) μ := I0.add Ia
    have I2 : Integrable (fun ξ : ι → ℝ => M i j * (F i * F j) + (M i j * F i) * ξ j + (M i j * F j) * ξ i) μ := I1.add Ib
    rw [integral_add I2 Ic, integral_add I1 Ib, integral_add I0 Ia]
    simp only [integral_const_mul, m1, h2]
    simp
    ring
  have intt : ∀ i j, Integrable (fun ξ : ι → ℝ => (F + ξ) i * (M i j * (F + ξ) j)) μ := fun i j => by
    have hy : ∀ i, MemLpTwoPow μ (fun ξ => (F + ξ) i) := fun i => (MemLpTwoPow.const (F i)).add (hc i)
    have := ((hy i).mul ((MemLpTwoPow.const (M i j)).mul (hy j))) 0
    simp only [pow_zero] at this; exact memLp_one_iff_integrable.1 this
  have hsum : ∫ ξ, (F + ξ) ⬝ᵥ M.mulVec (F + ξ) ∂μ = F ⬝ᵥ M.mulVec F + Matrix.trace (M * C) := by
    simp_rw [dotProduct_mulVec_eq_sum]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => intt i j]
    simp_rw [integral_finset_sum _ fun j _ => intt _ j, term]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    simp_rw [mul_add, Finset.sum_add_distrib, ← hsym]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : Integrable (fun ξ : ι → ℝ => (F + ξ) ⬝ᵥ M.mulVec (F + ξ)) μ := by
    simp_rw [dotProduct_mulVec_eq_sum]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => intt i j
  simp only [centeredQuadraticForm]
  rw [integral_sub (hint.const_mul _) (integrable_const _), integral_const_mul, hsum]
  simp
  ring
end Gaussian
section Norms
private lemma eLpNorm_le_of_integral_pow_le {α : Type} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ} {k : ℕ} (hk : Even k) (hk0 : k ≠ 0)
    (hg : MemLp g k μ) {b : ℝ} (hb : 0 ≤ b) (h : ∫ ξ, g ξ ^ k ∂μ ≤ b ^ k) : eLpNorm g k μ ≤ ENNReal.ofReal b := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hk0) (by simp)]
  simp only [ENNReal.toReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have e2 : ∀ x, ‖g x‖ ^ (k : ℝ) = g x ^ k := fun x => by
    rw [Real.rpow_natCast, Real.norm_eq_abs, hk.pow_abs]
  simp_rw [e2]
  calc (∫ x, g x ^ k ∂μ) ^ ((k : ℝ)⁻¹) ≤ (b ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (integral_nonneg fun x => hk.pow_nonneg _) h (by positivity)
    _ = b := Real.pow_rpow_inv_natCast hb hk0
private lemma integral_sq_le_of_eLpNorm_le {α : Type} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ} (hg : MemLp g 2 μ) {b : ℝ} (hb : 0 ≤ b)
    (h : eLpNorm g 2 μ ≤ ENNReal.ofReal b) : ∫ ξ, g ξ ^ 2 ∂μ ≤ b ^ 2 := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)] at h
  have h0 : 0 ≤ ∫ ξ, g ξ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e2 : ∀ x, ‖g x‖ ^ ((2 : ℝ≥0∞).toReal) = g x ^ 2 := fun x => by
    simp [Real.norm_eq_abs, sq_abs]
  simp_rw [e2] at h
  have h1 := (ENNReal.ofReal_le_ofReal_iff hb).1 h
  have h2 : (∫ ξ, g ξ ^ 2 ∂μ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = Real.sqrt (∫ ξ, g ξ ^ 2 ∂μ) := by
    rw [Real.sqrt_eq_rpow]; simp
  rw [h2] at h1
  calc ∫ ξ, g ξ ^ 2 ∂μ = Real.sqrt (∫ ξ, g ξ ^ 2 ∂μ) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ b ^ 2 := by gcongr
end Norms
section Means
variable {V : Type} [Fintype V]
private lemma average_add (f g : V → ℝ) : average (fun v => f v + g v) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]
private lemma average_sub (f g : V → ℝ) : average (fun v => f v - g v) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]
private lemma average_const_mul (c : ℝ) (f : V → ℝ) : average (fun v => c * f v) = c * average f := by
  simp only [average, ← Finset.mul_sum]; ring
private lemma average_const [Nonempty V] (c : ℝ) : average (fun _ : V => c) = c := by
  have : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, this]
private lemma abs_average_le {f g : V → ℝ} (h : ∀ v, |f v| ≤ g v) : |average f| ≤ average g := by
  simp only [average]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Fintype.card V : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => h v)) (by positivity)
private lemma eLpNorm_average_le [Nonempty V] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : ℝ≥0∞} (hp : 1 ≤ p) {h : V → Ω → ℝ}
    (hm : ∀ v, AEStronglyMeasurable (h v) P) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ v, eLpNorm (h v) p P ≤ ENNReal.ofReal B) :
    eLpNorm (fun u => average fun v => h v u) p P ≤ ENNReal.ofReal B := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : (fun u => average fun v => h v u) = ((Fintype.card V : ℝ)⁻¹) • (∑ v, h v) := by
    ext u; simp [average, Finset.sum_apply]
  rw [e, eLpNorm_const_smul]
  have h1 : eLpNorm (∑ v, h v) p P ≤ ∑ v, eLpNorm (h v) p P :=
    eLpNorm_sum_le (fun v _ => hm v) hp
  have h2 : ∑ v : V, eLpNorm (h v) p P ≤ (Fintype.card V : ℝ≥0∞) * ENNReal.ofReal B := by
    calc ∑ v : V, eLpNorm (h v) p P ≤ ∑ _v : V, ENNReal.ofReal B := Finset.sum_le_sum fun v _ => hB v
      _ = _ := by simp
  calc ‖((Fintype.card V : ℝ)⁻¹)‖ₑ * eLpNorm (∑ v, h v) p P
      ≤ ‖((Fintype.card V : ℝ)⁻¹)‖ₑ * ((Fintype.card V : ℝ≥0∞) * ENNReal.ofReal B) := by gcongr; exact h1.trans h2
    _ = ENNReal.ofReal B := by
      rw [← mul_assoc]
      have : ‖((Fintype.card V : ℝ)⁻¹)‖ₑ * (Fintype.card V : ℝ≥0∞) = 1 := by
        rw [Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          inv_mul_cancel₀ hc, ENNReal.ofReal_one]
      rw [this, one_mul]
end Means
section Event
variable {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω} {E : Set Ω} {Y : Ω → ι → ℝ}
  {𝓕 : Set ((ι → ℝ) × Measure (ι → ℝ))} {η : ℝ}
private lemma eLpNorm_indicator_le_of_dominated [IsProbabilityMeasure P] (hE : MeasurableSet E) (hη : η ≤ 1) (below : IsDominatedByGaussianShifts P E Y 𝓕 η)
    {G : (ι → ℝ) → ℝ} (hG : Measurable G) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ q ∈ 𝓕, eLpNorm (fun ξ => G (q.1 + ξ)) p q.2 ≤ ENNReal.ofReal b) :
    eLpNorm (E.indicator fun u => G (Y u)) p P ≤ ENNReal.ofReal (2 * b) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1).ne'
  have hr1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp1
  have hr0 : 0 < p.toReal := by linarith
  have hm : Measurable (fun y => ‖G y‖ₑ ^ p.toReal) := hG.enorm.pow_const _
  have hb' : ∀ q ∈ 𝓕, ∫⁻ ξ, ‖G (q.1 + ξ)‖ₑ ^ p.toReal ∂q.2 ≤ (ENNReal.ofReal b) ^ p.toReal := by
    intro q hq
    have h1 := h q hq
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt] at h1
    have h2 := ENNReal.rpow_le_rpow h1 hr0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one] at h2
  have k := below _ _ hm hb'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have e : ∫⁻ x, ‖E.indicator (fun u => G (Y u)) x‖ₑ ^ p.toReal ∂P = ∫⁻ u in E, ‖G (Y u)‖ₑ ^ p.toReal ∂P := by
    rw [← lintegral_indicator hE]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ E
    · simp [hu]
    · simp [hu, ENNReal.zero_rpow_of_pos hr0]
  rw [e]
  have hPE : P E ≤ 1 := prob_le_one
  have h2 : ENNReal.ofReal (1 + η) ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have k2 : ∫⁻ u in E, ‖G (Y u)‖ₑ ^ p.toReal ∂P ≤ 2 * (ENNReal.ofReal b) ^ p.toReal := by
    refine k.trans ?_
    gcongr
    calc ENNReal.ofReal (1 + η) * P E ≤ 2 * 1 := by gcongr
      _ = 2 := by simp
  calc (∫⁻ u in E, ‖G (Y u)‖ₑ ^ p.toReal ∂P) ^ (1 / p.toReal)
      ≤ (2 * (ENNReal.ofReal b) ^ p.toReal) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow k2 (by positivity)
    _ = 2 ^ (1 / p.toReal) * ENNReal.ofReal b := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hr0.ne', ENNReal.rpow_one]
    _ ≤ 2 * ENNReal.ofReal b := by
      gcongr
      rw [one_div]
      calc (2 : ℝ≥0∞) ^ (p.toReal)⁻¹ ≤ 2 ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (inv_le_one_of_one_le₀ hr1)
        _ = 2 := by simp
    _ = ENNReal.ofReal (2 * b) := by rw [ENNReal.ofReal_mul (by norm_num)]; simp
private lemma measurable_indicator_comp (hY : Measurable (E.indicator Y)) (hE : MeasurableSet E) {G : (ι → ℝ) → ℝ} (hG : Measurable G) :
    Measurable (E.indicator fun u => G (Y u)) := by
  have : (E.indicator fun u => G (Y u)) = E.indicator fun u => G (E.indicator Y u) := by
    ext u
    by_cases hu : u ∈ E <;> simp [hu]
  rw [this]
  exact (hG.comp hY).indicator hE
end Event
section Centering
variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {P : Measure Ω} {E : Set Ω} {Y : Ω → ι → ℝ}
  {𝓕 : Set ((ι → ℝ) × Measure (ι → ℝ))} {η : ℝ}
private lemma centeredQuadraticForm_zero_add (C M : Matrix ι ι ℝ) (F ξ : ι → ℝ) : centeredQuadraticForm C M 0 (F + ξ) = centeredQuadraticForm C M F ξ := by
  simp [centeredQuadraticForm]
private lemma measurable_centeredQuadraticForm (C M : Matrix ι ι ℝ) (F : ι → ℝ) : Measurable (centeredQuadraticForm C M F) := by
  have : centeredQuadraticForm C M F = fun ξ => (1 / 2) * (∑ i, ∑ j, (F i + ξ i) * (M i j * (F j + ξ j))) - (1 / 2) * Matrix.trace (M * C) := by
    funext ξ
    simp only [centeredQuadraticForm, dotProduct_mulVec_eq_sum, Pi.add_apply]
  rw [this]
  fun_prop
private lemma centeredQuadraticForm_zero_apply (C M : Matrix ι ι ℝ) (y : ι → ℝ) :
    centeredQuadraticForm C M 0 y = (1 / 2) * (y ⬝ᵥ M.mulVec y) - (1 / 2) * Matrix.trace (M * C) := by
  simp [centeredQuadraticForm]
private lemma abs_setIntegral_le_mul_sqrt [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 64 P) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : eLpNorm f 64 P ≤ ENNReal.ofReal D) {A : Set Ω} (hA : MeasurableSet A) {t : ℝ} (ht : 0 ≤ t) (hAt : P A ≤ ENNReal.ofReal t) :
    |∫ u in A, f u ∂P| ≤ D * Real.sqrt t := by
  have hf2 : eLpNorm f 2 P ≤ ENNReal.ofReal D :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hf.1).trans hD
  have h1 : eLpNorm f 1 (P.restrict A) ≤ eLpNorm f 2 (P.restrict A) * (P.restrict A Set.univ) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hf.1.restrict
  have h2 : eLpNorm f 2 (P.restrict A) ≤ eLpNorm f 2 P := eLpNorm_mono_measure _ Measure.restrict_le_self
  have h3 : (P.restrict A Set.univ) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≤ ENNReal.ofReal (Real.sqrt t) := by
    rw [Measure.restrict_apply_univ]
    have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by simp; norm_num
    rw [e, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ht (by norm_num)]
    exact ENNReal.rpow_le_rpow hAt (by norm_num)
  have h4 : eLpNorm f 1 (P.restrict A) ≤ ENNReal.ofReal (D * Real.sqrt t) := by
    rw [ENNReal.ofReal_mul hD0]
    exact h1.trans (mul_le_mul' (h2.trans hf2) h3)
  have hi : Integrable f (P.restrict A) := (hf.integrable (by norm_num)).restrict
  have h5 : ∫ u in A, ‖f u‖ ∂P ≤ D * Real.sqrt t := by
    rw [eLpNorm_one_eq_lintegral_enorm] at h4
    rw [integral_norm_eq_lintegral_enorm hi.1]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h4
  exact (abs_integral_le_integral_abs).trans (by simpa [Real.norm_eq_abs] using h5)
private lemma signed_integral_indicator_le [IsProbabilityMeasure P] (hE : MeasurableSet E) (below : IsDominatedByGaussianShifts P E Y 𝓕 η)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hY : Measurable (E.indicator Y)) {C M₀ : Matrix ι ι ℝ} (hs : C.IsSymm)
    (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) {a bO : ℝ} (ha : 0 ≤ a) (hbO : 0 < bO)
    (hq : ∀ q ∈ 𝓕, WickMoments.IsCenteredGaussian (fun i j => C i j) q.2 ∧ |q.1 ⬝ᵥ M₀.mulVec q.1| ≤ a ∧
      eLpNorm (centeredQuadraticForm C M₀ q.1) 32 q.2 ≤ ENNReal.ofReal bO)
    {s : ℝ} (hs1 : s ^ 2 = 1) (hs2 : |s| = 1) :
    Integrable (E.indicator fun u => centeredQuadraticForm C M₀ 0 (Y u)) P ∧
    s * ∫ u, E.indicator (fun u => centeredQuadraticForm C M₀ 0 (Y u)) u ∂P ≤ a + 2 * Real.sqrt η * bO := by
  set W : Ω → ℝ := E.indicator fun u => centeredQuadraticForm C M₀ 0 (Y u) with hW
  have hXm := measurable_centeredQuadraticForm C M₀ 0
  have hWm : Measurable W := measurable_indicator_comp hY hE hXm
  have hL32 : eLpNorm W 32 P ≤ ENNReal.ofReal (2 * bO) := by
    refine eLpNorm_indicator_le_of_dominated hE hη1 below hXm (by norm_num) (by simp) (by positivity) fun q hq' => ?_
    simpa only [centeredQuadraticForm_zero_add] using (hq q hq').2.2
  have hW32 : MemLp W 32 P := ⟨hWm.aestronglyMeasurable, hL32.trans_lt ENNReal.ofReal_lt_top⟩
  have hW2 : MemLp W 2 P := hW32.mono_exponent (by norm_num)
  have hWi : Integrable W P := hW32.integrable (by norm_num)
  have hW2i : Integrable (fun u => W u ^ 2) P := hW2.integrable_sq
  refine ⟨hWi, ?_⟩
  set I := ∫ u, W u ∂P with hI
  set J := ∫ u, W u ^ 2 ∂P with hJ
  set pE := P.real E with hpE
  have hpE1 : pE ≤ 1 := measureReal_le_one
  set lam := Real.sqrt η / bO with hlam
  have hsq : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hlam0 : 0 < lam := div_pos hsq hbO
  set B := 1 + lam * a + lam ^ 2 * bO ^ 2 with hB
  have gauss : ∀ q ∈ 𝓕, ∫⁻ ξ, ENNReal.ofReal ((1 + s * lam * centeredQuadraticForm C M₀ 0 (q.1 + ξ)) ^ 2) ∂q.2 ≤ ENNReal.ofReal B := by
    intro q hq'
    obtain ⟨hg, hq1, hq2⟩ := hq q hq'
    haveI := hg.1
    have hpos' : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * (fun i j => C i j) i j * t j := hpos
    have hall := memLpTwoPow_centeredQuadraticForm hg hpos' C M₀ q.1
    have h1 : MemLp (centeredQuadraticForm C M₀ q.1) 1 q.2 := by simpa using hall 0
    have h2 : MemLp (centeredQuadraticForm C M₀ q.1) 2 q.2 := by simpa using hall 1
    have hi1 := memLp_one_iff_integrable.1 h1
    have hi2 := h2.integrable_sq
    have hm := integral_centeredQuadraticForm hg hpos hs M₀ q.1
    have hsq2 : ∫ ξ, centeredQuadraticForm C M₀ q.1 ξ ^ 2 ∂q.2 ≤ bO ^ 2 :=
      integral_sq_le_of_eLpNorm_le h2 hbO.le ((eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) h2.1).trans hq2)
    simp_rw [centeredQuadraticForm_zero_add]
    have hexp : ∀ ξ, (1 + s * lam * centeredQuadraticForm C M₀ q.1 ξ) ^ 2 =
        1 + (2 * s * lam) * centeredQuadraticForm C M₀ q.1 ξ + lam ^ 2 * centeredQuadraticForm C M₀ q.1 ξ ^ 2 := by
      intro ξ
      have : (s * lam * centeredQuadraticForm C M₀ q.1 ξ) ^ 2 = lam ^ 2 * centeredQuadraticForm C M₀ q.1 ξ ^ 2 := by
        rw [mul_pow, mul_pow, hs1]; ring
      nlinarith [this]
    have J1 : Integrable (fun ξ => 1 + (2 * s * lam) * centeredQuadraticForm C M₀ q.1 ξ) q.2 := (integrable_const _).add (hi1.const_mul _)
    have J2 : Integrable (fun ξ => lam ^ 2 * centeredQuadraticForm C M₀ q.1 ξ ^ 2) q.2 := hi2.const_mul _
    have J3 : Integrable (fun ξ => (1 + s * lam * centeredQuadraticForm C M₀ q.1 ξ) ^ 2) q.2 := by
      simp_rw [hexp]; exact J1.add J2
    rw [← ofReal_integral_eq_lintegral_ofReal J3 (Filter.Eventually.of_forall fun ξ => sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    simp_rw [hexp]
    rw [integral_add J1 J2, integral_add (integrable_const _) (hi1.const_mul _), integral_const_mul, integral_const_mul, hm]
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul, mul_one]
    have h3 : (2 * s * lam) * ((1 / 2) * (q.1 ⬝ᵥ M₀.mulVec q.1)) ≤ lam * a := by
      have : (2 * s * lam) * ((1 / 2) * (q.1 ⬝ᵥ M₀.mulVec q.1)) = lam * (s * (q.1 ⬝ᵥ M₀.mulVec q.1)) := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ hlam0.le
      calc s * (q.1 ⬝ᵥ M₀.mulVec q.1) ≤ |s * (q.1 ⬝ᵥ M₀.mulVec q.1)| := le_abs_self _
        _ = |q.1 ⬝ᵥ M₀.mulVec q.1| := by rw [abs_mul, hs2, one_mul]
        _ ≤ a := hq1
    have h4 : lam ^ 2 * ∫ ξ, centeredQuadraticForm C M₀ q.1 ξ ^ 2 ∂q.2 ≤ lam ^ 2 * bO ^ 2 :=
      mul_le_mul_of_nonneg_left hsq2 (by positivity)
    rw [hB]
    linarith
  have hm : Measurable (fun y => ENNReal.ofReal ((1 + s * lam * centeredQuadraticForm C M₀ 0 y) ^ 2)) := ENNReal.measurable_ofReal.comp (((measurable_const.add (measurable_const.mul hXm))).pow_const 2)
  have k := below _ _ hm gauss
  have hPE : P E = ENNReal.ofReal pE := by
    rw [hpE, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hQ : ∀ u, E.indicator (fun u => (1 + s * lam * centeredQuadraticForm C M₀ 0 (Y u)) ^ 2) u =
      E.indicator (fun _ => (1 : ℝ)) u + (2 * s * lam) * W u + lam ^ 2 * W u ^ 2 := by
    intro u
    by_cases hu : u ∈ E
    · simp only [hW, Set.indicator_of_mem hu]
      have : (s * lam * centeredQuadraticForm C M₀ 0 (Y u)) ^ 2 = lam ^ 2 * centeredQuadraticForm C M₀ 0 (Y u) ^ 2 := by
        rw [mul_pow, mul_pow, hs1]; ring
      nlinarith [this]
    · simp [hW, Set.indicator_of_notMem hu]
  have I0 : Integrable (E.indicator fun _ => (1 : ℝ)) P := (integrable_const _).indicator hE
  have I1 : Integrable (fun u => E.indicator (fun _ => (1 : ℝ)) u + (2 * s * lam) * W u) P := I0.add (hWi.const_mul _)
  have I2 : Integrable (fun u => lam ^ 2 * W u ^ 2) P := hW2i.const_mul _
  have IQ : Integrable (E.indicator fun u => (1 + s * lam * centeredQuadraticForm C M₀ 0 (Y u)) ^ 2) P := by
    have : (E.indicator fun u => (1 + s * lam * centeredQuadraticForm C M₀ 0 (Y u)) ^ 2) =
        fun u => E.indicator (fun _ => (1 : ℝ)) u + (2 * s * lam) * W u + lam ^ 2 * W u ^ 2 := funext hQ
    rw [this]; exact I1.add I2
  have hval : ∫ u, E.indicator (fun u => (1 + s * lam * centeredQuadraticForm C M₀ 0 (Y u)) ^ 2) u ∂P = pE + (2 * s * lam) * I + lam ^ 2 * J := by
    simp_rw [hQ]
    rw [integral_add I1 I2, integral_add I0 (hWi.const_mul _), integral_const_mul, integral_const_mul, integral_indicator hE]
    simp [hpE, hI, hJ]
  have hlin : ∫⁻ u in E, ENNReal.ofReal ((1 + s * lam * centeredQuadraticForm C M₀ 0 (Y u)) ^ 2) ∂P =
      ENNReal.ofReal (pE + (2 * s * lam) * I + lam ^ 2 * J) := by
    rw [← hval, ofReal_integral_eq_lintegral_ofReal IQ
      (Filter.Eventually.of_forall fun u => Set.indicator_nonneg (fun _ _ => sq_nonneg _) u), ← lintegral_indicator hE]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ E <;> simp [hu]
  rw [hlin, hPE, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)] at k
  have k2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 k
  have t0 : 0 ≤ lam * a + lam ^ 2 * bO ^ 2 := by positivity
  have e1 : (1 + η) * pE * B - pE = pE * (η + (1 + η) * (lam * a + lam ^ 2 * bO ^ 2)) := by rw [hB]; ring
  have e2 : pE * (η + (1 + η) * (lam * a + lam ^ 2 * bO ^ 2)) ≤ η + 2 * (lam * a + lam ^ 2 * bO ^ 2) := by
    have : η + (1 + η) * (lam * a + lam ^ 2 * bO ^ 2) ≤ η + 2 * (lam * a + lam ^ 2 * bO ^ 2) := by nlinarith
    have h0 : 0 ≤ η + (1 + η) * (lam * a + lam ^ 2 * bO ^ 2) := by positivity
    nlinarith
  have e3 : (2 * s * lam) * I ≤ η + 2 * (lam * a + lam ^ 2 * bO ^ 2) := by
    have : 0 ≤ lam ^ 2 * J := by positivity
    linarith
  have e4 : lam * bO = Real.sqrt η := by rw [hlam]; field_simp
  have e5 : η = lam * (bO * Real.sqrt η) := by
    have : lam * (bO * Real.sqrt η) = (lam * bO) * Real.sqrt η := by ring
    rw [this, e4, Real.mul_self_sqrt hη0.le]
  have e6 : 2 * lam * (s * I) ≤ 2 * lam * (a + 2 * Real.sqrt η * bO) := by
    have h1 : lam ^ 2 * bO ^ 2 = lam * (bO * Real.sqrt η) := by
      have : lam ^ 2 * bO ^ 2 = lam * ((lam * bO) * bO) := by ring
      rw [this, e4]; ring
    have h2 : (2 * s * lam) * I = 2 * lam * (s * I) := by ring
    rw [h2, h1] at e3
    have h3 : 0 ≤ lam * (bO * Real.sqrt η) := by positivity
    nlinarith
  exact le_of_mul_le_mul_left e6 (by positivity)
end Centering
section Assembly
variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {P : Measure Ω} {E : Set Ω} {Y : Ω → ι → ℝ}
  {𝓕 : Set ((ι → ℝ) × Measure (ι → ℝ))} {η : ℝ}
private lemma abs_integral_sub_centering_le [IsProbabilityMeasure P] (hE : MeasurableSet E) {τ : ℝ} (hτ : P Eᶜ ≤ ENNReal.ofReal τ) (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1 / 2) (below : IsDominatedByGaussianShifts P E Y 𝓕 η)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hY : Measurable (E.indicator Y)) {C M₀ : Matrix ι ι ℝ} (hs : C.IsSymm)
    (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) {a bO : ℝ} (ha : 0 ≤ a) (hbO : 0 < bO)
    (hq : ∀ q ∈ 𝓕, WickMoments.IsCenteredGaussian (fun i j => C i j) q.2 ∧ |q.1 ⬝ᵥ M₀.mulVec q.1| ≤ a ∧
      eLpNorm (centeredQuadraticForm C M₀ q.1) 32 q.2 ≤ ENNReal.ofReal bO)
    {f : Ω → ℝ} {κ err D : ℝ} (herr : 0 ≤ err) (hD0 : 0 ≤ D)
    (mark : ∀ᵐ u ∂P, u ∈ E → |f u - κ - (1 / 2) * (Y u ⬝ᵥ M₀.mulVec (Y u))| ≤ err)
    (hf : MemLp f 64 P) (hD : eLpNorm f 64 P ≤ ENNReal.ofReal D) :
    |∫ w, f w ∂P - (κ + (1 / 2) * Matrix.trace (M₀ * C))| ≤
      (2 * Real.sqrt η * bO + a) + err + (3 * D + 2 * (2 * Real.sqrt η * bO + a) + 2 * err) * Real.sqrt τ := by
  obtain ⟨hWi, hup⟩ := signed_integral_indicator_le (s := 1) hE below hη0 hη1 hY hs hpos ha hbO hq (by norm_num) (by norm_num)
  obtain ⟨-, hdn⟩ := signed_integral_indicator_le (s := -1) hE below hη0 hη1 hY hs hpos ha hbO hq (by norm_num) (by norm_num)
  set X : Ω → ℝ := fun u => centeredQuadraticForm C M₀ 0 (Y u) with hX
  set I := ∫ u, E.indicator X u ∂P with hI
  set Zx := 2 * Real.sqrt η * bO + a with hZx
  have hIabs : |I| ≤ Zx := by
    rw [abs_le]; constructor <;> linarith
  set c := κ + (1 / 2) * Matrix.trace (M₀ * C) with hc
  have hfi : Integrable f P := hf.integrable (by norm_num)
  have hXi : IntegrableOn X E P := (integrable_indicator_iff hE).1 hWi
  have hIE : ∫ u in E, X u ∂P = I := (integral_indicator hE).symm
  set pE := P.real E with hpE
  have hpE1 : pE ≤ 1 := measureReal_le_one
  have hpE0 : 0 ≤ pE := measureReal_nonneg
  have hcompl : 1 - pE ≤ τ := by
    have h1 : P.real Eᶜ = 1 - pE := probReal_compl_eq_one_sub hE
    have h2 : P.real Eᶜ ≤ τ := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hτ0 hτ
    linarith
  set r := ∫ u in E, (f u - c - X u) ∂P with hr
  have hrabs : |r| ≤ err := by
    have hb : ∀ᵐ u ∂P.restrict E, ‖f u - c - X u‖ ≤ err := by
      rw [ae_restrict_iff' hE]
      filter_upwards [mark] with u hu hmem
      have e : f u - c - X u = f u - κ - (1 / 2) * (Y u ⬝ᵥ M₀.mulVec (Y u)) := by
        simp only [hX, hc, centeredQuadraticForm_zero_apply]; ring
      rw [Real.norm_eq_abs, e]
      exact hu hmem
    have := norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top P E) hb
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have : P.real E ≤ 1 := measureReal_le_one
    nlinarith
  have hr2 : r = (∫ u in E, f u ∂P) - c * pE - I := by
    have I1 : IntegrableOn f E P := hfi.integrableOn
    have I2 : IntegrableOn (fun _ : Ω => c) E P := integrableOn_const (measure_ne_top _ _)
    have I3 : IntegrableOn (fun u => f u - c) E P := I1.sub I2
    rw [hr, integral_sub I3 hXi, integral_sub I1 I2, hIE]
    simp [hpE, mul_comm]
  have hEf : |∫ u in E, f u ∂P| ≤ D := by
    have := abs_setIntegral_le_mul_sqrt hf hD0 hD hE (t := 1) (by norm_num) (by simpa using (prob_le_one : P E ≤ 1))
    simpa using this
  have hCf : |∫ u in Eᶜ, f u ∂P| ≤ D * Real.sqrt τ := abs_setIntegral_le_mul_sqrt hf hD0 hD hE.compl hτ0 hτ
  have hsplit : ∫ w, f w ∂P = (∫ u in E, f u ∂P) + ∫ u in Eᶜ, f u ∂P := (integral_add_compl hE hfi).symm
  have hcb : |c| ≤ 2 * (D + Zx + err) := by
    have h1 : c * pE = (∫ u in E, f u ∂P) - I - r := by rw [hr2]; ring
    have h2 : |c| * pE ≤ D + Zx + err := by
      calc |c| * pE = |c * pE| := by rw [abs_mul, abs_of_nonneg hpE0]
        _ = |(∫ u in E, f u ∂P) - I - r| := by rw [h1]
        _ ≤ |∫ u in E, f u ∂P| + |I| + |r| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
        _ ≤ D + Zx + err := by gcongr
    have h3 : 0 ≤ |c| := abs_nonneg _
    nlinarith
  have hsq : τ ≤ Real.sqrt τ := by
    have h1 : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ0
    have h2 : Real.sqrt τ ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have h3 := Real.sqrt_nonneg τ
    nlinarith
  have hfin : ∫ w, f w ∂P - c = I + r + (∫ u in Eᶜ, f u ∂P) - c * (1 - pE) := by
    rw [hsplit, hr2]; ring
  rw [hfin]
  have h5 : |c * (1 - pE)| ≤ 2 * (D + Zx + err) * Real.sqrt τ := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - pE)]
    exact mul_le_mul hcb (hcompl.trans hsq) (by linarith) (by positivity)
  calc |I + r + (∫ u in Eᶜ, f u ∂P) - c * (1 - pE)|
      ≤ |I| + |r| + |∫ u in Eᶜ, f u ∂P| + |c * (1 - pE)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ Zx + err + D * Real.sqrt τ + 2 * (D + Zx + err) * Real.sqrt τ := by gcongr
    _ = Zx + err + (3 * D + 2 * Zx + 2 * err) * Real.sqrt τ := by ring
private lemma eLpNorm_indicator_compl_le [IsProbabilityMeasure P] (hE : MeasurableSet E) {τ : ℝ} (hτ : P Eᶜ ≤ ENNReal.ofReal τ) (hτ0 : 0 ≤ τ)
    {G : Ω → ℝ} (hG : AEStronglyMeasurable G P) {B : ℝ} (hB0 : 0 ≤ B) (hB : eLpNorm G 32 P ≤ ENNReal.ofReal B) :
    eLpNorm (Eᶜ.indicator G) 16 P ≤ ENNReal.ofReal (B * τ ^ (1 / 32 : ℝ)) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hE.compl]
  have h1 : eLpNorm G 16 (P.restrict Eᶜ) ≤ eLpNorm G 32 (P.restrict Eᶜ) *
      (P.restrict Eᶜ Set.univ) ^ (1 / (16 : ℝ≥0∞).toReal - 1 / (32 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hG.restrict
  have h2 : eLpNorm G 32 (P.restrict Eᶜ) ≤ eLpNorm G 32 P := eLpNorm_mono_measure _ Measure.restrict_le_self
  have h3 : (P.restrict Eᶜ Set.univ) ^ (1 / (16 : ℝ≥0∞).toReal - 1 / (32 : ℝ≥0∞).toReal) ≤ ENNReal.ofReal (τ ^ (1 / 32 : ℝ)) := by
    rw [Measure.restrict_apply_univ]
    have e : (1 / (16 : ℝ≥0∞).toReal - 1 / (32 : ℝ≥0∞).toReal) = (1 / 32 : ℝ) := by simp; norm_num
    rw [e, ← ENNReal.ofReal_rpow_of_nonneg hτ0 (by norm_num)]
    exact ENNReal.rpow_le_rpow hτ (by norm_num)
  rw [ENNReal.ofReal_mul hB0]
  exact h1.trans (mul_le_mul' (h2.trans hB) h3)
private lemma eLpNorm_le_of_split {G : Ω → ℝ} (hE : MeasurableSet E) (hG : AEStronglyMeasurable G P) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : eLpNorm (E.indicator G) 16 P ≤ ENNReal.ofReal b) (h2 : eLpNorm (Eᶜ.indicator G) 16 P ≤ ENNReal.ofReal c) :
    eLpNorm G 16 P ≤ ENNReal.ofReal (b + c) := by
  have e : G = E.indicator G + Eᶜ.indicator G := (Set.indicator_self_add_compl E G).symm
  rw [e, ENNReal.ofReal_add hb hc]
  exact (eLpNorm_add_le (hG.indicator hE) (hG.indicator hE.compl) (by norm_num)).trans (add_le_add h1 h2)
private lemma eLpNorm_add_le_ofReal {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : Ω → ℝ} (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P) {b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : eLpNorm f p P ≤ ENNReal.ofReal b) (h2 : eLpNorm g p P ≤ ENNReal.ofReal c) :
    eLpNorm (fun u => f u + g u) p P ≤ ENNReal.ofReal (b + c) := by
  rw [ENNReal.ofReal_add hb hc]
  exact (eLpNorm_add_le hf hg hp).trans (add_le_add h1 h2)
private lemma eLpNorm_const_mul_le_ofReal {p : ℝ≥0∞} {f : Ω → ℝ} {c b : ℝ} (hc : 0 ≤ c) (h : eLpNorm f p P ≤ ENNReal.ofReal b) :
    eLpNorm (fun u => c * f u) p P ≤ ENNReal.ofReal (c * b) := by
  have e : (fun u => c * f u) = c • f := by ext u; simp
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hc, ENNReal.ofReal_mul hc]
  gcongr
private lemma eLpNorm_abs_le {p : ℝ≥0∞} {f : Ω → ℝ} {b : ℝ} (h : eLpNorm f p P ≤ ENNReal.ofReal b) :
    eLpNorm (fun u => |f u|) p P ≤ ENNReal.ofReal b := by
  have : eLpNorm (fun u => |f u|) p P = eLpNorm f p P := eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun u => by simp)
  rwa [this]
private lemma eLpNorm_const_le_ofReal [IsProbabilityMeasure P] {p : ℝ≥0∞} (hp : p ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun _ : Ω => c) p P ≤ ENNReal.ofReal c := by
  rw [eLpNorm_const _ hp (NeZero.ne P)]
  simp [Real.enorm_eq_ofReal hc]
end Assembly
section Main
variable {ι V Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [MeasurableSpace Ω] {P : Measure Ω} {E : Set Ω} {Y : Ω → ι → ℝ}
  {𝓕 : Set ((ι → ℝ) × Measure (ι → ℝ))} {η : ℝ}
private lemma MemLpTwoPow.average {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ] {h : V → (ι → ℝ) → ℝ} (hh : ∀ v, MemLpTwoPow μ (h v)) :
    MemLpTwoPow μ (fun ξ => QuadraticConcentration.average fun v => h v ξ) :=
  (MemLpTwoPow.const (μ := μ) ((Fintype.card V : ℝ)⁻¹)).mul (MemLpTwoPow.sum Finset.univ fun v _ => hh v)
private lemma trace_mul_self_nonneg {M : Matrix ι ι ℝ} (hs : M.IsSymm) : 0 ≤ Matrix.trace (M * M) := by
  have hsym : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hs i) j; simpa [Matrix.transpose_apply] using this
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by rw [hsym i j]; exact mul_self_nonneg _
private lemma trace_mul_transpose_nonneg (M : Matrix ι ι ℝ) : 0 ≤ Matrix.trace (M * Mᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
private lemma IsAdmissibleFormFamily.smul {F : ι → ℝ} {M : V → Matrix ι ι ℝ} {Near : V → V → Prop} {a A φ ε : ℝ}
    (h : IsAdmissibleFormFamily F M Near a A φ ε) (b : V → ℝ) (hb : ∀ v, |b v| ≤ 1) (hε : 0 ≤ ε) :
    IsAdmissibleFormFamily F (fun v => b v • M v) Near a A φ ε := by
  have sq1 : ∀ v, b v ^ 2 ≤ 1 := fun v => by
    have := hb v; rw [← sq_abs]; nlinarith [abs_nonneg (b v)]
  have mulle : ∀ v w, |b v * b w| ≤ 1 := fun v w => by
    rw [abs_mul]; nlinarith [hb v, hb w, abs_nonneg (b v), abs_nonneg (b w)]
  refine ⟨fun v => (h.symm v).smul _, fun v s t => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v w hn => ?_, fun v w hn => ?_, fun v w hn => ?_⟩
  · have e : s ⬝ᵥ (b v • M v).mulVec t = b v * (s ⬝ᵥ (M v).mulVec t) := by
      simp [Matrix.smul_mulVec, dotProduct_smul]
    rw [e, mul_pow]
    exact (mul_le_of_le_one_left (sq_nonneg _) (sq1 v)).trans (h.op v s t)
  · have e : Matrix.trace ((b v • M v) * (b v • M v)) = b v ^ 2 * Matrix.trace (M v * M v) := by
      simp [Matrix.trace_smul, smul_eq_mul, sq, mul_assoc]
    rw [e]
    exact (mul_le_of_le_one_left (trace_mul_self_nonneg (h.symm v)) (sq1 v)).trans (h.hs v)
  · have e : (b v • M v).mulVec F ⬝ᵥ (b v • M v).mulVec F = b v ^ 2 * ((M v).mulVec F ⬝ᵥ (M v).mulVec F) := by
      simp [Matrix.smul_mulVec, dotProduct_smul, smul_dotProduct, sq, mul_assoc]
    rw [e]
    have h0 : 0 ≤ (M v).mulVec F ⬝ᵥ (M v).mulVec F := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact (mul_le_of_le_one_left h0 (sq1 v)).trans (h.image v)
  · have e : F ⬝ᵥ (b v • M v).mulVec F = b v * (F ⬝ᵥ (M v).mulVec F) := by
      simp [Matrix.smul_mulVec, dotProduct_smul]
    rw [e, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hb v)).trans (h.self v)
  · have e : Matrix.trace ((b v • M v) * (b w • M w)) = (b v * b w) * Matrix.trace (M v * M w) := by
      simp [Matrix.trace_smul, smul_eq_mul, mul_assoc]
      ring
    rw [e, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (mulle v w)).trans (h.far_trace v w hn)
  · have e : Matrix.trace (((b v • M v) * (b w • M w)) * ((b v • M v) * (b w • M w))ᵀ) =
        (b v * b w) ^ 2 * Matrix.trace ((M v * M w) * (M v * M w)ᵀ) := by
      have : (b v • M v) * (b w • M w) = (b v * b w) • (M v * M w) := by
        simp [smul_smul, mul_comm]
      rw [this, Matrix.transpose_smul]
      simp [Matrix.trace_smul, smul_eq_mul, sq, mul_assoc]
    rw [e]
    have : (b v * b w) ^ 2 ≤ 1 := by
      have := mulle v w; rw [← sq_abs]; nlinarith [abs_nonneg (b v * b w)]
    exact (mul_le_of_le_one_left (trace_mul_transpose_nonneg _) this).trans (h.far_product v w hn)
  · have e : (b v • M v).mulVec F ⬝ᵥ (b w • M w).mulVec F = (b v * b w) * ((M v).mulVec F ⬝ᵥ (M w).mulVec F) := by
      simp [Matrix.smul_mulVec, dotProduct_smul, smul_dotProduct, mul_assoc]
      ring
    rw [e, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (mulle v w)).trans (h.far_image v w hn)
private lemma centeredQuadraticForm_smul (C M : Matrix ι ι ℝ) (b : ℝ) (F ξ : ι → ℝ) :
    centeredQuadraticForm C (b • M) F ξ = b * centeredQuadraticForm C M F ξ := by
  simp only [centeredQuadraticForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.smul_mul, Matrix.trace_smul]
  ring
private lemma eLpNorm_sub_integral_le [IsProbabilityMeasure P] {h : Ω → ℝ} (hm : MemLp h 64 P) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : eLpNorm h 64 P ≤ ENNReal.ofReal D) :
    AEStronglyMeasurable (fun u => h u - ∫ w, h w ∂P) P ∧ eLpNorm (fun u => h u - ∫ w, h w ∂P) 64 P ≤ ENNReal.ofReal (2 * D) := by
  have h1 : |∫ w, h w ∂P| ≤ D := by
    have := abs_setIntegral_le_mul_sqrt hm hD0 hD (A := Set.univ) MeasurableSet.univ (t := 1) (by norm_num) (by simp)
    simpa using this
  have hA : AEStronglyMeasurable (fun _ : Ω => -∫ w, h w ∂P) P := aestronglyMeasurable_const
  have hs : AEStronglyMeasurable (fun u => h u - ∫ w, h w ∂P) P := hm.1.sub aestronglyMeasurable_const
  refine ⟨hs, ?_⟩
  have e : (fun u => h u - ∫ w, h w ∂P) = fun u => h u + (-∫ w, h w ∂P) := by ext u; ring
  rw [e, two_mul]
  refine eLpNorm_add_le_ofReal (by norm_num) hm.1 hA hD0 hD0 hD ?_
  have := eLpNorm_const_le_ofReal (P := P) (p := 64) (by norm_num) (abs_nonneg (∫ w, h w ∂P))
  have e2 : eLpNorm (fun _ : Ω => -∫ w, h w ∂P) 64 P = eLpNorm (fun _ : Ω => |∫ w, h w ∂P|) 64 P :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun u => by simp)
  rw [e2]
  exact this.trans (ENNReal.ofReal_le_ofReal h1)
private lemma eLpNorm_average_centered_le [Nonempty V] [IsProbabilityMeasure P] (hE : MeasurableSet E) {τ : ℝ} (hτ : P Eᶜ ≤ ENNReal.ofReal τ) (hτ0 : 0 ≤ τ)
    {C : Matrix ι ι ℝ} {N : V → Matrix ι ι ℝ} {h : V → Ω → ℝ} {κ : V → ℝ} {Zb bM err D : ℝ} (hZ : 0 ≤ Zb) (hbM : 0 ≤ bM)
    (herr : 0 ≤ err) (hD0 : 0 ≤ D) (hY : Measurable (E.indicator Y))
    (hL : eLpNorm (E.indicator fun u => average fun v => centeredQuadraticForm C (N v) 0 (Y u)) 16 P ≤ ENNReal.ofReal (2 * bM))
    (mark : ∀ᵐ u ∂P, u ∈ E → ∀ v, |h v u - κ v - (1 / 2) * (Y u ⬝ᵥ (N v).mulVec (Y u))| ≤ err)
    (hz : ∀ v, |∫ w, h v w ∂P - (κ v + (1 / 2) * Matrix.trace (N v * C))| ≤ Zb)
    (hm : ∀ v, MemLp (h v) 64 P ∧ eLpNorm (h v) 64 P ≤ ENNReal.ofReal D) :
    eLpNorm (fun u => average fun v => h v u - ∫ w, h v w ∂P) 16 P ≤
      ENNReal.ofReal (2 * bM + err + Zb + 2 * D * τ ^ (1 / 32 : ℝ)) := by
  have hc := fun v => eLpNorm_sub_integral_le (hm v).1 hD0 (hm v).2
  have hG : AEStronglyMeasurable (fun u => average fun v => h v u - ∫ w, h v w ∂P) P := by
    simp only [average]
    exact aestronglyMeasurable_const.mul (Finset.aestronglyMeasurable_fun_sum _ fun v _ => (hc v).1)
  refine eLpNorm_le_of_split hE hG (by positivity) (by positivity) ?_ ?_
  · have hT : AEStronglyMeasurable (E.indicator fun u => average fun v => centeredQuadraticForm C (N v) 0 (Y u)) P := by
      have hmeas : Measurable (fun y : ι → ℝ => average fun v => centeredQuadraticForm C (N v) 0 y) := by
        simp only [average]
        exact measurable_const.mul (Finset.measurable_fun_sum _ fun v _ => measurable_centeredQuadraticForm C (N v) 0)
      exact (measurable_indicator_comp hY hE hmeas).aestronglyMeasurable
    have bound : ∀ᵐ u ∂P, ‖E.indicator (fun u => average fun v => h v u - ∫ w, h v w ∂P) u‖ ≤
        |E.indicator (fun u => average fun v => centeredQuadraticForm C (N v) 0 (Y u)) u| + (err + Zb) := by
      filter_upwards [mark] with u hu
      by_cases hmem : u ∈ E
      · simp only [Set.indicator_of_mem hmem, Real.norm_eq_abs]
        have e : ∀ v, h v u - ∫ w, h v w ∂P = centeredQuadraticForm C (N v) 0 (Y u) +
            ((h v u - κ v - (1 / 2) * (Y u ⬝ᵥ (N v).mulVec (Y u))) -
              (∫ w, h v w ∂P - (κ v + (1 / 2) * Matrix.trace (N v * C)))) := by
          intro v; rw [centeredQuadraticForm_zero_apply]; ring
        simp_rw [e]
        rw [average_add]
        refine (abs_add_le _ _).trans ?_
        gcongr
        have : |average fun v => (h v u - κ v - (1 / 2) * (Y u ⬝ᵥ (N v).mulVec (Y u))) -
              (∫ w, h v w ∂P - (κ v + (1 / 2) * Matrix.trace (N v * C)))| ≤ average fun _ : V => err + Zb :=
          abs_average_le fun v => (abs_sub _ _).trans (add_le_add (hu hmem v) (hz v))
        rwa [average_const] at this
      · simp only [Set.indicator_of_notMem hmem, norm_zero, abs_zero, zero_add]
        positivity
    have h1 := eLpNorm_mono_ae_real (p := 16) bound
    refine h1.trans ?_
    have := eLpNorm_add_le_ofReal (p := 16) (by norm_num) hT.norm aestronglyMeasurable_const (by positivity) (by positivity)
      (eLpNorm_abs_le hL) (eLpNorm_const_le_ofReal (P := P) (p := 16) (by norm_num) (by positivity : 0 ≤ err + Zb))
    refine (eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun u => by simp)).le.trans (this.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    linarith
  · refine eLpNorm_indicator_compl_le hE hτ hτ0 hG (B := 2 * D) (by positivity) ?_
    refine eLpNorm_average_le (by norm_num) (fun v => (hc v).1) (by positivity) fun v => ?_
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hc v).1).trans (hc v).2
end Main
section Final
private lemma average_expand {V : Type} [Fintype V] (X X' r r' z z' : V → ℝ) :
    average (fun v => (X v + r v - z v) * (X' v + r' v - z' v)) =
      average (fun v => X v * X' v) + average (fun v => X v * r' v) + average (fun v => r v * X' v) -
        average (fun v => z' v * X v) - average (fun v => z v * X' v) + average (fun v => (r v - z v) * (r' v - z' v)) := by
  simp only [← average_add, ← average_sub]
  congr 1
  funext v
  ring
private lemma eLpNorm_bounds_of_moment_bounds {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] {C : Matrix ι ι ℝ} {μ : Measure (ι → ℝ)}
    (hg : WickMoments.IsCenteredGaussian (fun i j => C i j) μ) (hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j)
    {F : ι → ℝ} {N N' : V → Matrix ι ι ℝ} {κ C₁ C₀ Bp Bm Bo : ℝ} (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₀) (hBp : 0 ≤ Bp) (hBm : 0 ≤ Bm) (hBo : 0 ≤ Bo)
    (T1 : ∫ ξ, (average (fun v => centeredQuadraticForm C (N v) F ξ * centeredQuadraticForm C (N' v) F ξ) - κ) ^ 16 ∂μ ≤ (C₁ * Bp) ^ 16)
    (T2 : ∫ ξ, average (fun v => centeredQuadraticForm C (N v) F ξ) ^ 16 ∂μ ≤ (C₁ * Bm) ^ 16)
    (T3 : ∀ v, ∫ ξ, centeredQuadraticForm C (N v) F ξ ^ 32 ∂μ ≤ (C₁ * Bo) ^ 32) :
    eLpNorm (fun ξ => average (fun v => centeredQuadraticForm C (N v) F ξ * centeredQuadraticForm C (N' v) F ξ) - κ) 16 μ ≤ ENNReal.ofReal (C₀ * Bp) ∧
    eLpNorm (fun ξ => average fun v => centeredQuadraticForm C (N v) F ξ) 16 μ ≤ ENNReal.ofReal (C₀ * Bm) ∧
    ∀ v, eLpNorm (centeredQuadraticForm C (N v) F) 32 μ ≤ ENNReal.ofReal (C₀ * Bo) := by
  haveI := hg.1
  have hC0 : 0 ≤ C₀ := hC₁.trans hC
  have hall : ∀ v, MemLpTwoPow μ (centeredQuadraticForm C (N v) F) := fun v => memLpTwoPow_centeredQuadraticForm hg hpos C (N v) F
  have hall' : ∀ v, MemLpTwoPow μ (centeredQuadraticForm C (N' v) F) := fun v => memLpTwoPow_centeredQuadraticForm hg hpos C (N' v) F
  have a1 : MemLpTwoPow μ (fun ξ => average (fun v => centeredQuadraticForm C (N v) F ξ * centeredQuadraticForm C (N' v) F ξ) + (-κ)) :=
    (MemLpTwoPow.average fun v => (hall v).mul (hall' v)).add (MemLpTwoPow.const _)
  have a2 : MemLpTwoPow μ (fun ξ => average fun v => centeredQuadraticForm C (N v) F ξ) := MemLpTwoPow.average hall
  have mono : ∀ (B : ℝ) (k : ℕ), 0 ≤ B → (C₁ * B) ^ k ≤ (C₀ * B) ^ k := fun B k hB => by
    gcongr
  refine ⟨?_, ?_, fun v => ?_⟩
  · have m : MemLp (fun ξ => average (fun v => centeredQuadraticForm C (N v) F ξ * centeredQuadraticForm C (N' v) F ξ) - κ) ((16 : ℕ) : ℝ≥0∞) μ := by
      have := a1 4
      simp only [sub_eq_add_neg]
      norm_num at this ⊢
      exact this
    have := eLpNorm_le_of_integral_pow_le (k := 16) (by decide) (by norm_num) m (mul_nonneg hC0 hBp) (T1.trans (mono Bp 16 hBp))
    simpa using this
  · have m : MemLp (fun ξ => average fun v => centeredQuadraticForm C (N v) F ξ) ((16 : ℕ) : ℝ≥0∞) μ := by
      have := a2 4
      norm_num at this ⊢
      exact this
    have := eLpNorm_le_of_integral_pow_le (k := 16) (by decide) (by norm_num) m (mul_nonneg hC0 hBm) (T2.trans (mono Bm 16 hBm))
    simpa using this
  · have m : MemLp (centeredQuadraticForm C (N v) F) ((32 : ℕ) : ℝ≥0∞) μ := by
      have := hall v 5
      norm_num at this ⊢
      exact this
    have := eLpNorm_le_of_integral_pow_le (k := 32) (by decide) (by norm_num) m (mul_nonneg hC0 hBo) ((T3 v).trans (mono Bo 32 hBo))
    simpa using this
private lemma eLpNorm_mul_le_ofReal {α : Type} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {p q : ℝ≥0∞} [ENNReal.HolderTriple p p q]
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {b c : ℝ} (hb : 0 ≤ b)
    (h1 : eLpNorm f p μ ≤ ENNReal.ofReal b) (h2 : eLpNorm g p μ ≤ ENNReal.ofReal c) :
    eLpNorm (fun u => f u * g u) q μ ≤ ENNReal.ofReal (b * c) := by
  have := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := p) (r := q) hg hf
  have e : f • g = fun u => f u * g u := by ext u; simp
  rw [e] at this
  rw [ENNReal.ofReal_mul hb]
  exact this.trans (mul_le_mul' h1 h2)
private instance holderTriple_sixtyFour : ENNReal.HolderTriple 64 64 32 := by
  have := holderTriple_two_pow 5; norm_num at this; exact this
private instance holderTriple_thirtyTwo : ENNReal.HolderTriple 32 32 16 := by
  have := holderTriple_two_pow 4; norm_num at this; exact this
set_option maxHeartbeats 3200000 in
theorem formsOnEventStatement_of_quadraticConcentration (hc : quadraticConcentrationStatement) : formsOnEventStatement := by
  intro a ha
  obtain ⟨C₁, hC₁, hconc⟩ := hc a ha
  refine ⟨max C₁ 1, le_max_right _ _, ?_⟩
  intro ι V Ω _ _ _ _ _ P E Y C 𝓕 M M' Near f g κ₀ κ₀' lam A φ ε ρ η err D τ H
  haveI hP := H.isProbability
  have hE := H.measurableSet
  have hlam := H.lam_pos
  have hA1 := H.one_le_A
  have hφ := H.φ_nonneg
  have hε := H.ε_nonneg
  have hρ := H.ρ_nonneg
  have herr := H.err_nonneg
  have hD0 := H.D_nonneg
  have hτ0 := H.τ_nonneg
  have hη0 := H.η_pos
  have hη1 := H.η_le
  have hY := H.measurable_indicator
  have below := H.dominated
  set C₀ := max C₁ 1 with hC₀
  have hC₀1 : 1 ≤ C₀ := le_max_right _ _
  have hCC : C₁ ≤ C₀ := le_max_left _ _
  set e₀ := Real.sqrt ρ + Real.sqrt ε with he₀
  set Bp := productAverageBound lam A φ ε e₀ with hBpd
  set Bm := averageBound lam A φ ε e₀ with hBmd
  set Bo := singleFormBound lam A φ with hBod
  have hBp : 0 ≤ Bp := by rw [hBpd]; unfold productAverageBound; positivity
  have hBm : 0 ≤ Bm := by rw [hBmd]; unfold averageBound; positivity
  have hBo : 0 < Bo := by
    rw [hBod]; unfold singleFormBound
    have : 0 < Real.sqrt A := Real.sqrt_pos.2 (by linarith)
    positivity
  set bP := C₀ * Bp with hbP
  set bM := C₀ * Bm with hbM
  set bO := C₀ * Bo with hbO
  have hbP0 : 0 ≤ bP := by positivity
  have hbM0 : 0 ≤ bM := by positivity
  have hbO0 : 0 < bO := by positivity
  have hpos : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j := fun t => by
    have := H.posSemidef t
    rw [dotProduct_mulVec_eq_sum] at this
    simpa [mul_assoc] using this
  have conc : ∀ (N N' : V → Matrix ι ι ℝ) (q : (ι → ℝ) × Measure (ι → ℝ)), WickMoments.IsCenteredGaussian (fun i j => C i j) q.2 →
      IsAdmissibleFormFamily q.1 N Near a A φ ε → IsAdmissibleFormFamily q.1 N' Near a A φ ε →
      eLpNorm (fun ξ => average (fun v => centeredQuadraticForm C (N v) q.1 ξ * centeredQuadraticForm C (N' v) q.1 ξ) -
        average (fun v => (1 / 2) * Matrix.trace (N v * C * N' v * C))) 16 q.2 ≤ ENNReal.ofReal bP ∧
      eLpNorm (fun ξ => average fun v => centeredQuadraticForm C (N v) q.1 ξ) 16 q.2 ≤ ENNReal.ofReal bM ∧
      ∀ v, eLpNorm (centeredQuadraticForm C (N v) q.1) 32 q.2 ≤ ENNReal.ofReal bO := by
    intro N N' q hg h1 h2
    obtain ⟨T1, T2, T3⟩ := hconc ι V C q.2 q.1 N N' Near lam A φ ε ρ hlam.le hA1 hφ hε hρ H.symm H.posSemidef H.quad_le hg h1 h2 H.near_card_le
    exact eLpNorm_bounds_of_moment_bounds hg hpos hC₁ hCC hBp hBm hBo.le T1 T2 T3
  have hqM : ∀ v, ∀ q ∈ 𝓕, WickMoments.IsCenteredGaussian (fun i j => C i j) q.2 ∧ |q.1 ⬝ᵥ (M v).mulVec q.1| ≤ A * φ ^ 2 ∧
      eLpNorm (centeredQuadraticForm C (M v) q.1) 32 q.2 ≤ ENNReal.ofReal bO := fun v q hq => by
    obtain ⟨hg, h1, h2⟩ := H.gaussian_family q hq
    exact ⟨hg, h1.self v, (conc M M' q hg h1 h2).2.2 v⟩
  have hqM' : ∀ v, ∀ q ∈ 𝓕, WickMoments.IsCenteredGaussian (fun i j => C i j) q.2 ∧ |q.1 ⬝ᵥ (M' v).mulVec q.1| ≤ A * φ ^ 2 ∧
      eLpNorm (centeredQuadraticForm C (M' v) q.1) 32 q.2 ≤ ENNReal.ofReal bO := fun v q hq => by
    obtain ⟨hg, h1, h2⟩ := H.gaussian_family q hq
    exact ⟨hg, h2.self v, (conc M' M q hg h2 h1).2.2 v⟩
  set Zb := centeringBound C₀ lam A φ η err D τ with hZb
  have hZpos : 0 < Zb := by
    rw [hZb]; unfold centeringBound
    have : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
    have h1 : 0 < 2 * Real.sqrt η * (C₀ * singleFormBound lam A φ) := by positivity
    positivity
  have hzf : ∀ v, |∫ w, f v w ∂P - (κ₀ v + (1 / 2) * Matrix.trace (M v * C))| ≤ Zb := fun v =>
    abs_integral_sub_centering_le hE H.compl_le hτ0 H.τ_le below hη0 hη1 hY H.symm hpos (by positivity) hbO0 (hqM v) herr hD0
      (H.approx_left.mono fun u hu hm => hu hm v) (H.memLp_left v).1 (H.memLp_left v).2
  have hzg : ∀ v, |∫ w, g v w ∂P - (κ₀' v + (1 / 2) * Matrix.trace (M' v * C))| ≤ Zb := fun v =>
    abs_integral_sub_centering_le hE H.compl_le hτ0 H.τ_le below hη0 hη1 hY H.symm hpos (by positivity) hbO0 (hqM' v) herr hD0
      (H.approx_right.mono fun u hu hm => hu hm v) (H.memLp_right v).1 (H.memLp_right v).2
  have meas_mean : ∀ (h : V → (ι → ℝ) → ℝ), (∀ v, Measurable (h v)) → Measurable (fun y => average fun v => h v y) := by
    intro h hh
    simp only [average]
    exact measurable_const.mul (Finset.measurable_fun_sum _ fun v _ => hh v)
  have tr_mean : ∀ (N N' : V → Matrix ι ι ℝ), (∀ q ∈ 𝓕, WickMoments.IsCenteredGaussian (fun i j => C i j) q.2 ∧ IsAdmissibleFormFamily q.1 N Near a A φ ε ∧
      IsAdmissibleFormFamily q.1 N' Near a A φ ε) →
      eLpNorm (E.indicator fun u => average fun v => centeredQuadraticForm C (N v) 0 (Y u)) 16 P ≤ ENNReal.ofReal (2 * bM) := by
    intro N N' hN
    refine eLpNorm_indicator_le_of_dominated hE hη1 below (meas_mean _ fun v => measurable_centeredQuadraticForm C (N v) 0) (by norm_num) (by simp) hbM0 fun q hq => ?_
    obtain ⟨hg, h1, h2⟩ := hN q hq
    simpa only [centeredQuadraticForm_zero_add] using (conc N N' q hg h1 h2).2.1
  refine ⟨?_, ?_, ?_⟩
  · set b : V → ℝ := fun v => (∫ w, f v w ∂P - (κ₀ v + (1 / 2) * Matrix.trace (M v * C))) / Zb with hbdef
    set b' : V → ℝ := fun v => (∫ w, g v w ∂P - (κ₀' v + (1 / 2) * Matrix.trace (M' v * C))) / Zb with hb'def
    have hb : ∀ v, |b v| ≤ 1 := fun v => by
      rw [hbdef]; simp only; rw [abs_div, abs_of_pos hZpos]; exact (div_le_one hZpos).2 (hzf v)
    have hb' : ∀ v, |b' v| ≤ 1 := fun v => by
      rw [hb'def]; simp only; rw [abs_div, abs_of_pos hZpos]; exact (div_le_one hZpos).2 (hzg v)
    set kap := average (fun v => (1 / 2) * Matrix.trace (M v * C * M' v * C)) with hkapd
    set X₁ : V → (ι → ℝ) → ℝ := fun v => centeredQuadraticForm C (M v) 0 with hX₁
    set X₂ : V → (ι → ℝ) → ℝ := fun v => centeredQuadraticForm C (M' v) 0 with hX₂
    have mX₁ : ∀ v, Measurable (X₁ v) := fun v => measurable_centeredQuadraticForm C (M v) 0
    have mX₂ : ∀ v, Measurable (X₂ v) := fun v => measurable_centeredQuadraticForm C (M' v) 0
    set G2 : (ι → ℝ) → ℝ := fun y => average fun v => X₁ v y * X₂ v y with hG2
    set G1 : (ι → ℝ) → ℝ := fun y => G2 y - kap with hG1
    set G4 : (ι → ℝ) → ℝ := fun y => average fun v => b' v * X₁ v y with hG4
    set G5 : (ι → ℝ) → ℝ := fun y => average fun v => b v * X₂ v y with hG5
    have mG2 : Measurable G2 := meas_mean _ fun v => (mX₁ v).mul (mX₂ v)
    have mG1 : Measurable G1 := mG2.sub_const _
    have mG4 : Measurable G4 := meas_mean _ fun v => (mX₁ v).const_mul _
    have mG5 : Measurable G5 := meas_mean _ fun v => (mX₂ v).const_mul _
    have T1 : eLpNorm (E.indicator fun u => G1 (Y u)) 16 P ≤ ENNReal.ofReal (2 * bP) := by
      refine eLpNorm_indicator_le_of_dominated hE hη1 below mG1 (by norm_num) (by simp) hbP0 fun q hq => ?_
      obtain ⟨hg, h1, h2⟩ := H.gaussian_family q hq
      simpa only [hG1, hG2, hX₁, hX₂, centeredQuadraticForm_zero_add] using (conc M M' q hg h1 h2).1
    have one16 : ∀ (N : Matrix ι ι ℝ) (q : (ι → ℝ) × Measure (ι → ℝ)), IsProbabilityMeasure q.2 →
        eLpNorm (centeredQuadraticForm C N q.1) 32 q.2 ≤ ENNReal.ofReal bO →
        eLpNorm (fun ξ => ‖centeredQuadraticForm C N 0 (q.1 + ξ)‖) 16 q.2 ≤ ENNReal.ofReal bO := by
      intro N q hq hb
      simp only [centeredQuadraticForm_zero_add]
      rw [eLpNorm_norm]
      exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (measurable_centeredQuadraticForm C N q.1).aestronglyMeasurable).trans hb
    have T2 : ∀ v, eLpNorm (E.indicator fun u => ‖X₁ v (Y u)‖) 16 P ≤ ENNReal.ofReal (2 * bO) := fun v =>
      eLpNorm_indicator_le_of_dominated hE hη1 below (mX₁ v).norm (by norm_num) (by simp) hbO0.le fun q hq =>
        one16 (M v) q (H.gaussian_family q hq).1.1 (hqM v q hq).2.2
    have T3 : ∀ v, eLpNorm (E.indicator fun u => ‖X₂ v (Y u)‖) 16 P ≤ ENNReal.ofReal (2 * bO) := fun v =>
      eLpNorm_indicator_le_of_dominated hE hη1 below (mX₂ v).norm (by norm_num) (by simp) hbO0.le fun q hq =>
        one16 (M' v) q (H.gaussian_family q hq).1.1 (hqM' v q hq).2.2
    have T4 : eLpNorm (E.indicator fun u => G4 (Y u)) 16 P ≤ ENNReal.ofReal (2 * bM) := by
      refine eLpNorm_indicator_le_of_dominated hE hη1 below mG4 (by norm_num) (by simp) hbM0 fun q hq => ?_
      obtain ⟨hg, h1, h2⟩ := H.gaussian_family q hq
      have := (conc (fun v => b' v • M v) M' q hg (h1.smul b' hb' hε) h2).2.1
      simp only [centeredQuadraticForm_smul] at this
      simpa only [hG4, hX₁, centeredQuadraticForm_zero_add] using this
    have T5 : eLpNorm (E.indicator fun u => G5 (Y u)) 16 P ≤ ENNReal.ofReal (2 * bM) := by
      refine eLpNorm_indicator_le_of_dominated hE hη1 below mG5 (by norm_num) (by simp) hbM0 fun q hq => ?_
      obtain ⟨hg, h1, h2⟩ := H.gaussian_family q hq
      have := (conc (fun v => b v • M' v) M q hg (h2.smul b hb hε) h1).2.1
      simp only [centeredQuadraticForm_smul] at this
      simpa only [hG5, hX₂, centeredQuadraticForm_zero_add] using this
    have T6 : eLpNorm (E.indicator fun u => G2 (Y u)) 16 P ≤ ENNReal.ofReal (2 * (bO * bO)) := by
      refine eLpNorm_indicator_le_of_dominated hE hη1 below mG2 (by norm_num) (by simp) (by positivity) fun q hq => ?_
      haveI := (H.gaussian_family q hq).1.1
      simp only [hG2, hX₁, hX₂, centeredQuadraticForm_zero_add]
      refine eLpNorm_average_le (by norm_num) (fun v => ((measurable_centeredQuadraticForm C (M v) q.1).mul (measurable_centeredQuadraticForm C (M' v) q.1)).aestronglyMeasurable)
        (by positivity) fun v => ?_
      exact eLpNorm_mul_le_ofReal (p := 32) (measurable_centeredQuadraticForm C (M v) q.1).aestronglyMeasurable
        (measurable_centeredQuadraticForm C (M' v) q.1).aestronglyMeasurable hbO0.le (hqM v q hq).2.2 (hqM' v q hq).2.2
    have hcf := fun v => eLpNorm_sub_integral_le (H.memLp_left v).1 hD0 (H.memLp_left v).2
    have hcg := fun v => eLpNorm_sub_integral_le (H.memLp_right v).1 hD0 (H.memLp_right v).2
    set G : Ω → ℝ := fun u => average (fun v => (f v u - ∫ w, f v w ∂P) * (g v u - ∫ w, g v w ∂P)) - kap with hGdef
    have hmm : AEStronglyMeasurable (fun u => average fun v => (f v u - ∫ w, f v w ∂P) * (g v u - ∫ w, g v w ∂P)) P := by
      simp only [average]
      exact aestronglyMeasurable_const.mul (Finset.aestronglyMeasurable_fun_sum _ fun v _ => (hcf v).1.mul (hcg v).1)
    have hGm : AEStronglyMeasurable G P := hmm.sub aestronglyMeasurable_const
    have hcompl : 1 / 2 ≤ P.real E := by
      have h1 : P.real Eᶜ = 1 - P.real E := probReal_compl_eq_one_sub hE
      have h2 : P.real Eᶜ ≤ τ := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal hτ0 H.compl_le
      have := H.τ_le
      linarith
    have hkap : |kap| ≤ 4 * bP + 4 * (bO * bO) := by
      have ind : (E.indicator fun _ : Ω => kap) = fun u => E.indicator (fun u => G2 (Y u)) u + -E.indicator (fun u => G1 (Y u)) u := by
        funext u
        by_cases hu : u ∈ E
        · simp [hu, hG1]
        · simp [hu]
      have m2 := (measurable_indicator_comp (G := G2) hY hE mG2).aestronglyMeasurable (μ := P)
      have m1 := (measurable_indicator_comp (G := G1) hY hE mG1).aestronglyMeasurable (μ := P)
      have k1 : eLpNorm (E.indicator fun _ : Ω => kap) 16 P ≤ ENNReal.ofReal (2 * (bO * bO) + 2 * bP) := by
        rw [ind]
        refine eLpNorm_add_le_ofReal (by norm_num) m2 m1.neg (by positivity) (by positivity) T6 ?_
        rw [eLpNorm_neg]; exact T1
      rw [eLpNorm_indicator_const hE (by norm_num) (by simp)] at k1
      have hp0 : 0 ≤ P.real E := measureReal_nonneg
      have hPE : P E = ENNReal.ofReal (P.real E) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      have e16 : (1 / (16 : ℝ≥0∞).toReal) = (1 / 16 : ℝ) := by simp
      rw [hPE, Real.enorm_eq_ofReal_abs, e16, ENNReal.ofReal_rpow_of_nonneg hp0 (by norm_num), ← ENNReal.ofReal_mul (abs_nonneg _)] at k1
      have k2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 k1
      have k3 : 1 / 2 ≤ (P.real E) ^ (1 / 16 : ℝ) := by
        have h1 : P.real E ≤ 1 := measureReal_le_one
        have h2 : (P.real E) ^ (1 : ℝ) ≤ (P.real E) ^ (1 / 16 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by linarith) h1 (by norm_num)
        rw [Real.rpow_one] at h2
        linarith
      have := abs_nonneg kap
      nlinarith
    set T2f : Ω → ℝ := fun u => average fun v => E.indicator (fun u => ‖X₁ v (Y u)‖) u with hT2f
    set T3f : Ω → ℝ := fun u => average fun v => E.indicator (fun u => ‖X₂ v (Y u)‖) u with hT3f
    have mT1 : Measurable (E.indicator fun u => G1 (Y u)) := measurable_indicator_comp hY hE mG1
    have mT4 : Measurable (E.indicator fun u => G4 (Y u)) := measurable_indicator_comp hY hE mG4
    have mT5 : Measurable (E.indicator fun u => G5 (Y u)) := measurable_indicator_comp hY hE mG5
    have mT2v : ∀ v, Measurable (E.indicator fun u => ‖X₁ v (Y u)‖) := fun v => measurable_indicator_comp hY hE (mX₁ v).norm
    have mT3v : ∀ v, Measurable (E.indicator fun u => ‖X₂ v (Y u)‖) := fun v => measurable_indicator_comp hY hE (mX₂ v).norm
    have mT2 : Measurable T2f := by
      simp only [hT2f, average]
      exact measurable_const.mul (Finset.measurable_fun_sum _ fun v _ => mT2v v)
    have mT3 : Measurable T3f := by
      simp only [hT3f, average]
      exact measurable_const.mul (Finset.measurable_fun_sum _ fun v _ => mT3v v)
    have L2 : eLpNorm T2f 16 P ≤ ENNReal.ofReal (2 * bO) :=
      eLpNorm_average_le (by norm_num) (fun v => (mT2v v).aestronglyMeasurable) (by positivity) T2
    have L3 : eLpNorm T3f 16 P ≤ ENNReal.ofReal (2 * bO) :=
      eLpNorm_average_le (by norm_num) (fun v => (mT3v v).aestronglyMeasurable) (by positivity) T3
    set S : Ω → ℝ := fun u => ‖E.indicator (fun u => G1 (Y u)) u‖ + err * ‖T2f u‖ + err * ‖T3f u‖ +
      Zb * ‖E.indicator (fun u => G4 (Y u)) u‖ + Zb * ‖E.indicator (fun u => G5 (Y u)) u‖ + (err + Zb) ^ 2 with hS
    have bound : ∀ᵐ u ∂P, ‖E.indicator G u‖ ≤ S u := by
      filter_upwards [H.approx_left, H.approx_right] with u h1 h2
      by_cases hmem : u ∈ E
      · have r1 := h1 hmem
        have r2 := h2 hmem
        simp only [hS, hT2f, hT3f, Set.indicator_of_mem hmem, Real.norm_eq_abs, hGdef]
        set r : V → ℝ := fun v => f v u - κ₀ v - (1 / 2) * (Y u ⬝ᵥ (M v).mulVec (Y u)) with hr
        set r' : V → ℝ := fun v => g v u - κ₀' v - (1 / 2) * (Y u ⬝ᵥ (M' v).mulVec (Y u)) with hr'
        set z : V → ℝ := fun v => ∫ w, f v w ∂P - (κ₀ v + (1 / 2) * Matrix.trace (M v * C)) with hz
        set z' : V → ℝ := fun v => ∫ w, g v w ∂P - (κ₀' v + (1 / 2) * Matrix.trace (M' v * C)) with hz'
        have e1 : ∀ v, f v u - ∫ w, f v w ∂P = X₁ v (Y u) + r v - z v := by
          intro v; simp only [hX₁, hr, hz, centeredQuadraticForm_zero_apply]; ring
        have e2 : ∀ v, g v u - ∫ w, g v w ∂P = X₂ v (Y u) + r' v - z' v := by
          intro v; simp only [hX₂, hr', hz', centeredQuadraticForm_zero_apply]; ring
        simp_rw [e1, e2]
        rw [average_expand]
        have t1 : |average fun v => X₁ v (Y u) * r' v| ≤ err * abs (average fun v => |X₁ v (Y u)|) := by
          have : |average fun v => X₁ v (Y u) * r' v| ≤ average fun v => err * |X₁ v (Y u)| :=
            abs_average_le fun v => by
              rw [abs_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right (r2 v) (abs_nonneg _)
          rw [average_const_mul] at this
          exact this.trans (mul_le_mul_of_nonneg_left (le_abs_self _) herr)
        have t2 : |average fun v => r v * X₂ v (Y u)| ≤ err * abs (average fun v => |X₂ v (Y u)|) := by
          have : |average fun v => r v * X₂ v (Y u)| ≤ average fun v => err * |X₂ v (Y u)| :=
            abs_average_le fun v => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (r1 v) (abs_nonneg _)
          rw [average_const_mul] at this
          exact this.trans (mul_le_mul_of_nonneg_left (le_abs_self _) herr)
        have t3 : (average fun v => z' v * X₁ v (Y u)) = Zb * G4 (Y u) := by
          simp only [hG4]
          rw [← average_const_mul]
          congr 1
          funext v
          simp only [hb'def, hz']
          field_simp
        have t4 : (average fun v => z v * X₂ v (Y u)) = Zb * G5 (Y u) := by
          simp only [hG5]
          rw [← average_const_mul]
          congr 1
          funext v
          simp only [hbdef, hz]
          field_simp
        have t5 : |average fun v => (r v - z v) * (r' v - z' v)| ≤ (err + Zb) ^ 2 := by
          have : |average fun v => (r v - z v) * (r' v - z' v)| ≤ average fun _ : V => (err + Zb) ^ 2 :=
            abs_average_le fun v => by
              rw [abs_mul, sq]
              have c1 : |r v - z v| ≤ err + Zb := (abs_sub _ _).trans (add_le_add (r1 v) (hzf v))
              have c2 : |r' v - z' v| ≤ err + Zb := (abs_sub _ _).trans (add_le_add (r2 v) (hzg v))
              exact mul_le_mul c1 c2 (abs_nonneg _) (by positivity)
          rwa [average_const] at this
        rw [t3, t4]
        have z1 : |Zb * G4 (Y u)| = Zb * |G4 (Y u)| := by rw [abs_mul, abs_of_pos hZpos]
        have z2 : |Zb * G5 (Y u)| = Zb * |G5 (Y u)| := by rw [abs_mul, abs_of_pos hZpos]
        rw [abs_le]
        have a1 := abs_le.1 t1
        have a2 := abs_le.1 t2
        have a5 := abs_le.1 t5
        have a3 := abs_le.1 (le_of_eq z1)
        have a4 := abs_le.1 (le_of_eq z2)
        have a6 := abs_le.1 (le_refl |G1 (Y u)|)
        constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, a6.1, a6.2]
      · simp only [Set.indicator_of_notMem hmem, norm_zero]
        positivity
    have on : eLpNorm (E.indicator G) 16 P ≤ ENNReal.ofReal
        (2 * bP + err * (2 * bO) + err * (2 * bO) + Zb * (2 * bM) + Zb * (2 * bM) + (err + Zb) ^ 2) := by
      refine (eLpNorm_mono_ae_real bound).trans ?_
      have one : (1 : ℝ≥0∞) ≤ 16 := by norm_num
      have n1 : eLpNorm (fun u => ‖E.indicator (fun u => G1 (Y u)) u‖) 16 P ≤ ENNReal.ofReal (2 * bP) := by rwa [eLpNorm_norm]
      have n2 : eLpNorm (fun u => err * ‖T2f u‖) 16 P ≤ ENNReal.ofReal (err * (2 * bO)) := eLpNorm_const_mul_le_ofReal herr (by rwa [eLpNorm_norm])
      have n3 : eLpNorm (fun u => err * ‖T3f u‖) 16 P ≤ ENNReal.ofReal (err * (2 * bO)) := eLpNorm_const_mul_le_ofReal herr (by rwa [eLpNorm_norm])
      have n4 : eLpNorm (fun u => Zb * ‖E.indicator (fun u => G4 (Y u)) u‖) 16 P ≤ ENNReal.ofReal (Zb * (2 * bM)) :=
        eLpNorm_const_mul_le_ofReal hZpos.le (by rwa [eLpNorm_norm])
      have n5 : eLpNorm (fun u => Zb * ‖E.indicator (fun u => G5 (Y u)) u‖) 16 P ≤ ENNReal.ofReal (Zb * (2 * bM)) :=
        eLpNorm_const_mul_le_ofReal hZpos.le (by rwa [eLpNorm_norm])
      have n6 := eLpNorm_const_le_ofReal (P := P) (p := 16) (by norm_num) (by positivity : 0 ≤ (err + Zb) ^ 2)
      have q1 := mT1.norm
      have q2 := (mT2.norm).const_mul err
      have q3 := (mT3.norm).const_mul err
      have q4 := (mT4.norm).const_mul Zb
      have q5 := (mT5.norm).const_mul Zb
      have s2 := eLpNorm_add_le_ofReal one q1.aestronglyMeasurable q2.aestronglyMeasurable (by positivity) (by positivity) n1 n2
      have s3 := eLpNorm_add_le_ofReal one (q1.add q2).aestronglyMeasurable q3.aestronglyMeasurable (by positivity) (by positivity) s2 n3
      have s4 := eLpNorm_add_le_ofReal one ((q1.add q2).add q3).aestronglyMeasurable q4.aestronglyMeasurable (by positivity) (by positivity) s3 n4
      have s5 := eLpNorm_add_le_ofReal one (((q1.add q2).add q3).add q4).aestronglyMeasurable q5.aestronglyMeasurable (by positivity) (by positivity) s4 n5
      exact eLpNorm_add_le_ofReal one ((((q1.add q2).add q3).add q4).add q5).aestronglyMeasurable aestronglyMeasurable_const (by positivity) (by positivity) s5 n6
    have hG32 : eLpNorm G 32 P ≤ ENNReal.ofReal (2 * D * (2 * D) + |kap|) := by
      have e : G = fun u => (average fun v => (f v u - ∫ w, f v w ∂P) * (g v u - ∫ w, g v w ∂P)) + (-kap) := by
        funext u; simp only [hGdef]; ring
      rw [e]
      refine eLpNorm_add_le_ofReal (by norm_num) hmm aestronglyMeasurable_const (by positivity) (abs_nonneg _) ?_ ?_
      · exact eLpNorm_average_le (by norm_num) (fun v => (hcf v).1.mul (hcg v).1) (by positivity) fun v =>
          eLpNorm_mul_le_ofReal (p := 64) (hcf v).1 (hcg v).1 (by positivity) (hcf v).2 (hcg v).2
      · have e2 : eLpNorm (fun _ : Ω => -kap) 32 P = eLpNorm (fun _ : Ω => |kap|) 32 P :=
          eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun u => by simp)
        rw [e2]
        exact eLpNorm_const_le_ofReal (by norm_num) (abs_nonneg _)
    have off := eLpNorm_indicator_compl_le hE H.compl_le hτ0 hGm (by positivity) hG32
    refine (eLpNorm_le_of_split hE hGm (by positivity) (by positivity) on off).trans (ENNReal.ofReal_le_ofReal ?_)
    have fin : productBoundOnEvent C₀ lam A φ ε ρ η err D τ = 2 * bP + 4 * bO * err + 4 * Zb * bM + (err + Zb) ^ 2 +
        (4 * D ^ 2 + 4 * bP + 4 * bO ^ 2) * τ ^ (1 / 32 : ℝ) := rfl
    rw [fin]
    have t := Real.rpow_nonneg hτ0 (1 / 32 : ℝ)
    have k := mul_le_mul_of_nonneg_right hkap t
    nlinarith
  · exact eLpNorm_average_centered_le hE H.compl_le hτ0 hZpos.le hbM0 herr hD0 hY (tr_mean M M' H.gaussian_family) H.approx_left hzf H.memLp_left
  · exact eLpNorm_average_centered_le hE H.compl_le hτ0 hZpos.le hbM0 herr hD0 hY
      (tr_mean M' M fun q hq => ⟨(H.gaussian_family q hq).1, (H.gaussian_family q hq).2.2, (H.gaussian_family q hq).2.1⟩) H.approx_right hzg H.memLp_right
end Final
end YangMills.Construction.QuadraticConcentration
end
