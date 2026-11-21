import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MeasureKernels
variable {Ξ Q W Zf : Type*} [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace W] [MeasurableSpace Zf]
theorem exists_markovKernel_of_density (μ : Measure W) [SFinite μ] {dens : Q × W → ENNReal} (hd : Measurable dens)
    {g : Q × W → Zf} (hg : Measurable g) {S : Set Q} (hS : MeasurableSet S)
    (hpos : ∀ q ∈ S, ∫⁻ w, dens (q, w) ∂μ ≠ 0) (htop : ∀ q ∈ S, ∫⁻ w, dens (q, w) ∂μ ≠ ⊤) (z₀ : Zf) :
    ∃ κ : Kernel Q Zf, IsMarkovKernel κ ∧ ∀ q ∈ S, ∀ Φ : Zf → ENNReal, Measurable Φ →
      ∫⁻ w, Φ (g (q, w)) * dens (q, w) ∂μ = (∫⁻ w, dens (q, w) ∂μ) * ∫⁻ ζ, Φ ζ ∂(κ q) := by
  classical
  let m : Q → ENNReal := fun q => ∫⁻ w, dens (q, w) ∂μ
  have hm : Measurable m := hd.lintegral_prod_right'
  have hdq : ∀ q, Measurable fun w => dens (q, w) := fun q => hd.comp measurable_prodMk_left
  have hgq : ∀ q, Measurable fun w => g (q, w) := fun q => hg.comp measurable_prodMk_left
  let mu : Q → Measure Zf := fun q => (μ.withDensity fun w => dens (q, w)).map fun w => g (q, w)
  have hmu : ∀ q (Φ : Zf → ENNReal), Measurable Φ → ∫⁻ ζ, Φ ζ ∂(mu q) = ∫⁻ w, Φ (g (q, w)) * dens (q, w) ∂μ := by
    intro q Φ hΦ
    simp only [mu]
    rw [lintegral_map hΦ (hgq q)]
    refine (lintegral_withDensity_eq_lintegral_mul μ (hdq q)
      (show Measurable fun w => Φ (g (q, w)) from hΦ.comp (hgq q))).trans ?_
    refine lintegral_congr fun w => ?_
    simp [mul_comm]
  have hmuB : ∀ B : Set Zf, MeasurableSet B → Measurable fun q => mu q B := by
    intro B hB
    have : (fun q => mu q B) = fun q => ∫⁻ w, B.indicator 1 (g (q, w)) * dens (q, w) ∂μ := by
      funext q
      rw [← hmu q _ (measurable_one.indicator hB), lintegral_indicator_one hB]
    rw [this]
    exact (((measurable_one.indicator hB).comp hg).mul hd).lintegral_prod_right'
  let nu : Q → Measure Zf := fun q => if q ∈ S then (m q)⁻¹ • mu q else Measure.dirac z₀
  have hnu : Measurable nu := by
    refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
    have : (fun q => nu q B) = fun q => if q ∈ S then (m q)⁻¹ * mu q B else Measure.dirac z₀ B := by
      funext q
      by_cases h : q ∈ S <;> simp [nu, h]
    rw [this]
    exact Measurable.ite hS (hm.inv.mul (hmuB B hB)) measurable_const
  refine ⟨⟨nu, hnu⟩, ⟨fun q => ?_⟩, fun q hq Φ hΦ => ?_⟩
  · show IsProbabilityMeasure (nu q)
    by_cases h : q ∈ S
    · have hu : mu q Set.univ = m q := by
        have := hmu q 1 measurable_one
        simpa [m] using this
      simp only [nu, if_pos h]
      refine ⟨?_⟩
      simp only [Measure.smul_apply, smul_eq_mul, hu]
      exact ENNReal.inv_mul_cancel (hpos q h) (htop q h)
    · simp only [nu, if_neg h]
      infer_instance
  · show _ = _ * ∫⁻ ζ, Φ ζ ∂(nu q)
    simp only [nu, if_pos hq]
    rw [lintegral_smul_measure, hmu q Φ hΦ, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel (hpos q hq) (htop q hq), one_mul]
theorem exists_measurable_density_between [MeasurableSpace.CountablyGenerated Zf] (κ η : Kernel Q Zf)
    [IsMarkovKernel κ] [IsMarkovKernel η]
    {S : Set Q} {E : Q → Set Zf} {lo hi : ℝ} (hlo : 0 < lo) (h1 : lo ≤ 1) (h2 : 1 ≤ hi)
    (h : ∀ q ∈ S, ∃ f : Zf → ENNReal, Measurable f ∧ κ q = (η q).withDensity f ∧ η q (E q)ᶜ = 0 ∧
      ∀ ζ ∈ E q, ENNReal.ofReal lo ≤ f ζ ∧ f ζ ≤ ENNReal.ofReal hi) :
    ∃ w : Q → Zf → ℝ, Measurable (Function.uncurry w) ∧ (∀ q ζ, lo ≤ w q ζ ∧ w q ζ ≤ hi) ∧
      ∀ q ∈ S, (η q).withDensity (fun ζ => ENNReal.ofReal (w q ζ)) = κ q := by
  classical
  let r := Kernel.rnDeriv κ η
  have hr : Measurable fun p : Q × Zf => r p.1 p.2 := Kernel.measurable_rnDeriv κ η
  let w : Q → Zf → ℝ := fun q ζ => if lo ≤ (r q ζ).toReal ∧ (r q ζ).toReal ≤ hi then (r q ζ).toReal else 1
  refine ⟨w, ?_, ?_, ?_⟩
  · have ht : Measurable fun p : Q × Zf => (r p.1 p.2).toReal := hr.ennreal_toReal
    refine Measurable.ite ?_ ht measurable_const
    exact (measurableSet_le measurable_const ht).inter (measurableSet_le ht measurable_const)
  · intro q ζ
    by_cases hc : lo ≤ (r q ζ).toReal ∧ (r q ζ).toReal ≤ hi
    · simp only [w, if_pos hc]
      exact hc
    · simp only [w, if_neg hc]
      exact ⟨h1, h2⟩
  · intro q hq
    obtain ⟨f, hf, hκ, hE, hb⟩ := h q hq
    have e1 : r q =ᵐ[η q] f := by
      have a1 : r q =ᵐ[η q] (κ q).rnDeriv (η q) := Kernel.rnDeriv_eq_rnDeriv_measure
      have a2 : (κ q).rnDeriv (η q) =ᵐ[η q] f := by
        rw [hκ]
        exact Measure.rnDeriv_withDensity _ hf
      exact a1.trans a2
    have e2 : (fun ζ => ENNReal.ofReal (w q ζ)) =ᵐ[η q] f := by
      have hEa : ∀ᵐ ζ ∂(η q), ζ ∈ E q := by
        rw [ae_iff]
        exact hE
      filter_upwards [e1, hEa] with ζ h3 h4
      obtain ⟨b1, b2⟩ := hb ζ h4
      have hftop : f ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top b2
      have c1 : lo ≤ (f ζ).toReal := by
        have := ENNReal.toReal_mono hftop b1
        rwa [ENNReal.toReal_ofReal hlo.le] at this
      have c2 : (f ζ).toReal ≤ hi := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top b2
        rwa [ENNReal.toReal_ofReal (by linarith)] at this
      simp only [w, h3]
      rw [if_pos ⟨c1, c2⟩, ENNReal.ofReal_toReal hftop]
    rw [hκ]
    exact withDensity_congr_ae e2
theorem setIntegral_comp_eq_setIntegral_kernel {P : Measure Ξ} [IsFiniteMeasure P] {e₁ : Ξ → Q} {e₂ : Ξ → W}
    (h₁ : Measurable e₁) (h₂ : Measurable e₂)
    {O : Set (Q × W)} (hO : MeasurableSet O) {g : Q × W → Zf} (hg : Measurable g)
    (κ : Kernel Q Zf) [IsMarkovKernel κ]
    (hind : ∀ B : Set (Q × Zf), MeasurableSet B →
      ∫⁻ u in (fun u => (e₁ u, e₂ u)) ⁻¹' O, B.indicator 1 (e₁ u, g (e₁ u, e₂ u)) ∂P =
        ∫⁻ u in (fun u => (e₁ u, e₂ u)) ⁻¹' O, κ (e₁ u) (Prod.mk (e₁ u) ⁻¹' B) ∂P)
    {F : Q × Zf → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ z, |F z| ≤ M) :
    ∫ u in (fun u => (e₁ u, e₂ u)) ⁻¹' O, F (e₁ u, g (e₁ u, e₂ u)) ∂P =
      ∫ u in (fun u => (e₁ u, e₂ u)) ⁻¹' O, ∫ ζ, F (e₁ u, ζ) ∂(κ (e₁ u)) ∂P := by
  set ev := (fun u => (e₁ u, e₂ u)) ⁻¹' O with hev
  set Pe := P.restrict ev with hPe
  let a : Ξ → Q × Zf := fun u => (e₁ u, g (e₁ u, e₂ u))
  have ha : Measurable a := h₁.prodMk (hg.comp (h₁.prodMk h₂))
  let ρ := Pe.map e₁
  have hΛ : Pe.map a = ρ ⊗ₘ κ := by
    ext B hB
    rw [Measure.map_apply ha hB, Measure.compProd_apply hB,
      lintegral_map (Kernel.measurable_kernel_prodMk_left hB) h₁, ← hind B hB]
    rw [← lintegral_indicator_one (ha hB)]
    refine lintegral_congr fun u => ?_
    by_cases h : a u ∈ B
    · simp [Set.indicator, h, a, show (e₁ u, g (e₁ u, e₂ u)) ∈ B from h]
    · simp [Set.indicator, h, a, show (e₁ u, g (e₁ u, e₂ u)) ∉ B from h]
  have hFs : StronglyMeasurable F := hF.stronglyMeasurable
  have hint : Integrable F (ρ ⊗ₘ κ) :=
    Integrable.of_bound hFs.aestronglyMeasurable M (ae_of_all _ fun z => by simpa using hM z)
  have s1 : ∫ u, F (a u) ∂Pe = ∫ z, F z ∂(Pe.map a) := (integral_map ha.aemeasurable hFs.aestronglyMeasurable).symm
  have s2 : ∫ z, F z ∂(ρ ⊗ₘ κ) = ∫ q, ∫ ζ, F (q, ζ) ∂(κ q) ∂ρ := Measure.integral_compProd hint
  have hin : StronglyMeasurable fun q => ∫ ζ, F (q, ζ) ∂(κ q) := by
    have : StronglyMeasurable (Function.uncurry fun (q : Q) (ζ : Zf) => F (q, ζ)) := hFs
    exact this.integral_kernel_prod_right'
  have s3 : ∫ q, ∫ ζ, F (q, ζ) ∂(κ q) ∂ρ = ∫ u, ∫ ζ, F (e₁ u, ζ) ∂(κ (e₁ u)) ∂Pe :=
    integral_map h₁.aemeasurable hin.aestronglyMeasurable
  rw [s1, hΛ, s2, s3]
end YangMills.Construction.MeasureKernels
end
