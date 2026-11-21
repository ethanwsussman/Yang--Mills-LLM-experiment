import YangMills.Construction.HilbertSpaces.JointSpectralMeasureOfAContractionAndAUnitaryProof
import YangMills.Construction.InfiniteLattice.EveryPairOfDirectionsAndTheJointCarrierProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.JointSpectrum.BorelCalculus
open MeasureTheory Set Filter Topology
open YangMills.Construction.JointSpectrum.SpectralIntegral YangMills.Construction.FamilyPolynomials YangMills.Construction.ScalarSpectralMeasures
open scoped ComplexConjugate ENNReal
set_option linter.unusedSectionVars false
section Analysis
variable {J : Type} [Fintype J] {ρ : Measure (SpectralDomain J)}
private lemma ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  induction a with
  | top => simp [ENNReal.mul_top]
  | coe a =>
    induction b with
    | top => simp [ENNReal.mul_top]
    | coe b =>
      have h := add_sq_le (a := a) (b := b)
      rw [mul_add] at h
      exact_mod_cast h
private lemma measurable_enorm_sq {u : SpectralDomain J → ℂ} (hu : Measurable u) :
    Measurable fun p => ‖u p‖ₑ ^ 2 :=
  hu.enorm.pow_const 2
private lemma sqNorm_add_le {u : SpectralDomain J → ℂ} (v : SpectralDomain J → ℂ)
    (hu : Measurable u) :
    sqNormLIntegral ρ (u + v) ≤ 2 * sqNormLIntegral ρ u + 2 * sqNormLIntegral ρ v := by
  unfold sqNormLIntegral
  calc ∫⁻ p, ‖(u + v) p‖ₑ ^ 2 ∂ρ
      ≤ ∫⁻ p, (2 * ‖u p‖ₑ ^ 2 + 2 * ‖v p‖ₑ ^ 2) ∂ρ := by
        refine lintegral_mono fun p => ?_
        calc ‖(u + v) p‖ₑ ^ 2 ≤ (‖u p‖ₑ + ‖v p‖ₑ) ^ 2 := by
              gcongr
              exact enorm_add_le _ _
          _ ≤ _ := ennreal_add_sq_le _ _
    _ = 2 * ∫⁻ p, ‖u p‖ₑ ^ 2 ∂ρ + 2 * ∫⁻ p, ‖v p‖ₑ ^ 2 ∂ρ := by
        rw [lintegral_add_left ((measurable_enorm_sq hu).const_mul 2),
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
private lemma sqNorm_congr {u v : SpectralDomain J → ℂ} (h : ∀ p, ‖u p‖ = ‖v p‖) :
    sqNormLIntegral ρ u = sqNormLIntegral ρ v := by
  unfold sqNormLIntegral
  refine lintegral_congr fun p => ?_
  rw [enorm_eq_iff_norm_eq.2 (h p)]
private lemma sqNorm_zero : sqNormLIntegral ρ (0 : SpectralDomain J → ℂ) = 0 := by
  simp [sqNormLIntegral]
private lemma sqNorm_smul (c : ℂ) (u : SpectralDomain J → ℂ) :
    sqNormLIntegral ρ (c • u) = ‖c‖ₑ ^ 2 * sqNormLIntegral ρ u := by
  unfold sqNormLIntegral
  rw [← lintegral_const_mul' _ _ (by simp [ENNReal.pow_eq_top_iff])]
  refine lintegral_congr fun p => ?_
  simp [mul_pow]
private lemma sqNorm_add_measure (ρ' : Measure (SpectralDomain J))
    (u : SpectralDomain J → ℂ) :
    sqNormLIntegral (ρ + ρ') u = sqNormLIntegral ρ u + sqNormLIntegral ρ' u := by
  unfold sqNormLIntegral
  rw [lintegral_add_measure]
private lemma sqNorm_le_of_bound [IsFiniteMeasure ρ] {u : SpectralDomain J → ℂ} {M : ℝ}
    (h : ∀ p, ‖u p‖ ≤ M) : sqNormLIntegral ρ u ≤ ENNReal.ofReal M ^ 2 * ρ univ := by
  unfold sqNormLIntegral
  calc ∫⁻ p, ‖u p‖ₑ ^ 2 ∂ρ ≤ ∫⁻ _, ENNReal.ofReal M ^ 2 ∂ρ := by
        refine lintegral_mono fun p => ?_
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h p)
    _ = _ := by simp
private lemma sqNorm_lt_top_of_bounded [IsFiniteMeasure ρ] {u : SpectralDomain J → ℂ}
    (h : IsBoundedFn u) : sqNormLIntegral ρ u < ∞ := by
  obtain ⟨M, hM⟩ := h
  refine (sqNorm_le_of_bound hM).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)
private lemma sqNorm_mul_le {r : SpectralDomain J → ℂ} {R : ℝ} (h : ∀ p, ‖r p‖ ≤ R)
    (u : SpectralDomain J → ℂ) :
    sqNormLIntegral ρ (r * u) ≤ ENNReal.ofReal R ^ 2 * sqNormLIntegral ρ u := by
  unfold sqNormLIntegral
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  refine lintegral_mono fun p => ?_
  simp only [Pi.mul_apply, enorm_mul, mul_pow]
  gcongr
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h p)
private lemma lintegral_enorm_mul_le_sqNorm {u v : SpectralDomain J → ℂ} (hu : Measurable u)
    (hv : Measurable v) :
    ∫⁻ p, ‖u p‖ₑ * ‖v p‖ₑ ∂ρ ≤
      sqNormLIntegral ρ u ^ (1 / 2 : ℝ) * sqNormLIntegral ρ v ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two
    hu.enorm.aemeasurable hv.enorm.aemeasurable
  simpa [sqNormLIntegral, ENNReal.rpow_two] using h
private lemma integrable_mul_of_sqNorm [IsFiniteMeasure ρ] {u v : SpectralDomain J → ℂ}
    (hu : Measurable u) (hv : Measurable v) (hu2 : sqNormLIntegral ρ u < ∞)
    (hv2 : sqNormLIntegral ρ v < ∞) : Integrable (fun p => u p * v p) ρ := by
  refine ⟨(hu.mul hv).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [enorm_mul]
  refine (lintegral_enorm_mul_le_sqNorm hu hv).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hu2.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hv2.ne)
private lemma tendsto_rpow_half_of_tendsto_zero {a : ℕ → ℝ≥0∞} (h : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun l => a l ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have h' := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp h
  simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using h'
private lemma tendsto_integral_mul_of_sqNorm [IsFiniteMeasure ρ] {u v : SpectralDomain J → ℂ}
    {U V : ℕ → SpectralDomain J → ℂ} (hu : Measurable u) (hv : Measurable v)
    (hU : ∀ l, Measurable (U l)) (hV : ∀ l, Measurable (V l))
    (hu2 : sqNormLIntegral ρ u < ∞) (hv2 : sqNormLIntegral ρ v < ∞)
    (hU2 : ∀ l, sqNormLIntegral ρ (U l) < ∞) (hV2 : ∀ l, sqNormLIntegral ρ (V l) < ∞)
    (hUt : Tendsto (fun l => sqNormLIntegral ρ (u - U l)) atTop (𝓝 0))
    (hVt : Tendsto (fun l => sqNormLIntegral ρ (v - V l)) atTop (𝓝 0)) :
    Tendsto (fun l => ∫ p, U l p * V l p ∂ρ) atTop (𝓝 (∫ p, u p * v p ∂ρ)) := by
  refine tendsto_integral_of_L1 _ (hu.mul hv).aestronglyMeasurable
    (Eventually.of_forall fun l => integrable_mul_of_sqNorm (hU l) (hV l) (hU2 l) (hV2 l)) ?_
  have ha := tendsto_rpow_half_of_tendsto_zero hUt
  have hb := tendsto_rpow_half_of_tendsto_zero hVt
  have hA : sqNormLIntegral ρ u ^ (1 / 2 : ℝ) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hu2.ne).ne
  have hB : sqNormLIntegral ρ v ^ (1 / 2 : ℝ) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hv2.ne).ne
  have hbound : Tendsto (fun l =>
      sqNormLIntegral ρ (u - U l) ^ (1 / 2 : ℝ) * sqNormLIntegral ρ (v - V l) ^ (1 / 2 : ℝ) +
      sqNormLIntegral ρ (u - U l) ^ (1 / 2 : ℝ) * sqNormLIntegral ρ v ^ (1 / 2 : ℝ) +
      sqNormLIntegral ρ u ^ (1 / 2 : ℝ) * sqNormLIntegral ρ (v - V l) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul ha (Or.inr (by simp)) hb (Or.inr (by simp))
    have h2 := ENNReal.Tendsto.mul_const (b := sqNormLIntegral ρ v ^ (1 / 2 : ℝ)) ha (Or.inr hB)
    have h3 := ENNReal.Tendsto.const_mul (a := sqNormLIntegral ρ u ^ (1 / 2 : ℝ)) hb (Or.inr hA)
    simpa using (h1.add h2).add h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) fun l => ?_
  have hm1 : Measurable (u - U l) := hu.sub (hU l)
  have hm2 : Measurable (v - V l) := hv.sub (hV l)
  calc ∫⁻ p, ‖U l p * V l p - u p * v p‖ₑ ∂ρ
      ≤ ∫⁻ p, (‖(u - U l) p‖ₑ * ‖(v - V l) p‖ₑ + ‖(u - U l) p‖ₑ * ‖v p‖ₑ +
          ‖u p‖ₑ * ‖(v - V l) p‖ₑ) ∂ρ := by
        refine lintegral_mono fun p => ?_
        have e : U l p * V l p - u p * v p =
            (u p - U l p) * (v p - V l p) - (u p - U l p) * v p - u p * (v p - V l p) := by
          ring
        rw [e]
        refine (enorm_sub_le).trans ?_
        refine add_le_add (enorm_sub_le.trans ?_) ?_
        · simp [enorm_mul]
        · simp [enorm_mul]
    _ = ∫⁻ p, ‖(u - U l) p‖ₑ * ‖(v - V l) p‖ₑ ∂ρ + ∫⁻ p, ‖(u - U l) p‖ₑ * ‖v p‖ₑ ∂ρ +
          ∫⁻ p, ‖u p‖ₑ * ‖(v - V l) p‖ₑ ∂ρ := by
        rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
    _ ≤ _ := by
        gcongr
        · exact lintegral_enorm_mul_le_sqNorm hm1 hm2
        · exact lintegral_enorm_mul_le_sqNorm hm1 hv
        · exact lintegral_enorm_mul_le_sqNorm hu hm2
end Analysis
section Polynomials
variable {J : Type} [Fintype J]
private lemma continuous_spectralMonomial (n : ℕ) (y : J → ℤ) :
    Continuous (spectralMonomial n y : SpectralDomain J → ℂ) := by apply _root_.YangMills.Construction.LatticeConventions.DirectionPairsSupport.continuous_spectralMonomial <;> assumption
private lemma continuous_of_mem_spectralPolynomials {q : SpectralDomain J → ℂ}
    (hq : q ∈ spectralPolynomials J) : Continuous q := by
  obtain ⟨s, c, h⟩ := hq
  have : q = fun p => ∑ i ∈ s, c i * spectralMonomial i.1 i.2 p := funext h
  rw [this]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_spectralMonomial _ _)
abbrev _root_.YangMills.SharedProofs.p14551 := @continuous_of_mem_spectralPolynomials
private lemma measurable_of_mem_spectralPolynomials {q : SpectralDomain J → ℂ}
    (hq : q ∈ spectralPolynomials J) : Measurable q :=
  (continuous_of_mem_spectralPolynomials hq).measurable
private lemma isBoundedFn_of_mem_spectralPolynomials {q : SpectralDomain J → ℂ}
    (hq : q ∈ spectralPolynomials J) : IsBoundedFn q := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_of_mem_spectralPolynomials hq).continuousOn
  exact ⟨M, fun p => hM p (mem_univ p)⟩
private lemma spectralMonomial_mem (n : ℕ) (y : J → ℤ) :
    spectralMonomial n y ∈ spectralPolynomials J :=
  ⟨{(n, y)}, fun _ => 1, fun p => by simp⟩
private lemma spectralSum_singleton (n : ℕ) (y : J → ℤ) :
    spectralSum {(n, y)} (fun _ => 1) = (spectralMonomial n y : SpectralDomain J → ℂ) := by
  funext p
  simp [spectralSum]
end Polynomials
section System
variable {𝒦 : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {J : Type} [Fintype J] [Nonempty J]
private structure CalculusInputs (S : CommutingFamily 𝒦 J) : Prop where
  fin : ∀ ψ, IsFiniteMeasure (spectralMeasure S ψ)
  isScalar : ∀ ψ, IsSpectralMeasureOf S ψ (spectralMeasure S ψ)
  uniq : ∀ ψ ρ, IsSpectralMeasureOf S ψ ρ → ρ = spectralMeasure S ψ
  mass : ∀ ψ, spectralMeasure S ψ univ = ‖ψ‖ₑ ^ 2
  inner_poly : ∀ ψ, ∀ q ∈ spectralPolynomials J,
    inner ℂ ψ (polynomialCalculus S q ψ) = ∫ p, q p ∂(spectralMeasure S ψ)
  smul : ∀ (c : ℂ) (ψ : 𝒦), spectralMeasure S (c • ψ) = (‖c‖ₑ ^ 2) • spectralMeasure S ψ
  add_le : ∀ (ψ ψ' : 𝒦) (B : Set (SpectralDomain J)), MeasurableSet B →
    spectralMeasure S (ψ + ψ') B ≤ 2 * spectralMeasure S ψ B + 2 * spectralMeasure S ψ' B
  seq : ∀ (ρ : Measure (SpectralDomain J)) [IsFiniteMeasure ρ] (f : SpectralDomain J → ℂ),
    Measurable f → sqNormLIntegral ρ f < ∞ →
      ∃ q : ℕ → SpectralDomain J → ℂ, (∀ l, q l ∈ spectralPolynomials J) ∧
        Tendsto (fun l => sqNormLIntegral ρ (f - q l)) atTop (𝓝 0)
  limit : ∀ (ψ : 𝒦) (f : SpectralDomain J → ℂ), Measurable f →
    sqNormLIntegral (spectralMeasure S ψ) f < ∞ → IsL2CalculusLimit S ψ f (l2Calculus S ψ f)
  norm_limit : ∀ (ψ : 𝒦) (f : SpectralDomain J → ℂ), Measurable f →
    sqNormLIntegral (spectralMeasure S ψ) f < ∞ →
      ‖l2Calculus S ψ f‖ₑ ^ 2 = sqNormLIntegral (spectralMeasure S ψ) f
  poly_add : ∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
    q + q' ∈ spectralPolynomials J
  poly_smul : ∀ (a : ℂ), ∀ q ∈ spectralPolynomials J, a • q ∈ spectralPolynomials J
  poly_mul : ∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
    q * q' ∈ spectralPolynomials J
  poly_conj : ∀ q ∈ spectralPolynomials J, (fun p => conj (q p)) ∈ spectralPolynomials J
  op_sum : ∀ (s : Finset (ℕ × (J → ℤ))) (c : ℕ × (J → ℤ) → ℂ),
    polynomialCalculus S (spectralSum s c) = familySum S s c
  op_add : ∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
    polynomialCalculus S (q + q') = polynomialCalculus S q + polynomialCalculus S q'
  op_smul : ∀ (a : ℂ), ∀ q ∈ spectralPolynomials J,
    polynomialCalculus S (a • q) = a • polynomialCalculus S q
  op_mul : ∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
    polynomialCalculus S (q * q') = polynomialCalculus S q * polynomialCalculus S q'
  op_conj : ∀ q ∈ spectralPolynomials J,
    polynomialCalculus S (fun p => conj (q p)) = star (polynomialCalculus S q)
private lemma calculusInputs (hP : PolynomialCalculusStatement)
    (hM : ScalarSpectralMeasuresStatement) (S : CommutingFamily 𝒦 J) : CalculusInputs S := by
  obtain ⟨_, hseq, -, hb, hsmul, -, hadd, hd⟩ := hM 𝒦 J S
  obtain ⟨-, -, hsum, -, hpadd, hpsmul, hpmul, hpconj, hoadd, hosmul, homul, hoconj, -, -⟩ :=
    hP 𝒦 J S
  exact
    { fin := fun ψ => (hb ψ).1.1
      isScalar := fun ψ => (hb ψ).1
      uniq := fun ψ => (hb ψ).2.1
      mass := fun ψ => (hb ψ).2.2.1
      inner_poly := fun ψ q hq => ((hb ψ).2.2.2 q hq).1
      smul := hsmul
      add_le := hadd
      seq := hseq
      limit := fun ψ f hf h => (hd ψ f hf h).1
      norm_limit := fun ψ f hf h => (hd ψ f hf h).2.2.2
      poly_add := hpadd
      poly_smul := hpsmul
      poly_mul := hpmul
      poly_conj := hpconj
      op_sum := hsum
      op_add := hoadd
      op_smul := hosmul
      op_mul := homul
      op_conj := hoconj }
variable {S : CommutingFamily 𝒦 J}
private lemma mem_integralDomain {f : SpectralDomain J → ℂ} {ψ : 𝒦} :
    ψ ∈ integralDomain S f ↔ sqNormLIntegral (spectralMeasure S ψ) f < ∞ :=
  Iff.rfl
private lemma spectralIntegral_of_mem {f : SpectralDomain J → ℂ} {ψ : 𝒦}
    (h : ψ ∈ integralDomain S f) : spectralIntegral S f ψ = l2Calculus S ψ f := by
  unfold YangMills.Construction.JointSpectrum.SpectralIntegral.spectralIntegral
  rw [if_pos h]
private lemma spectralIntegral_of_not_mem {f : SpectralDomain J → ℂ} {ψ : 𝒦}
    (h : ψ ∉ integralDomain S f) : spectralIntegral S f ψ = 0 := by
  unfold YangMills.Construction.JointSpectrum.SpectralIntegral.spectralIntegral
  rw [if_neg h]
private lemma CalculusInputs.tendsto (H : CalculusInputs S) {f : SpectralDomain J → ℂ} {ψ : 𝒦}
    {q : ℕ → SpectralDomain J → ℂ} (hf : Measurable f) (hψ : ψ ∈ integralDomain S f)
    (hq : PolynomialL2Approximation S ψ f q) :
    Tendsto (fun l => polynomialCalculus S (q l) ψ) atTop (𝓝 (spectralIntegral S f ψ)) := by
  rw [spectralIntegral_of_mem hψ]
  exact H.limit ψ f hf hψ q hq
private lemma CalculusInputs.norm_integral (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ : 𝒦} (hf : Measurable f) (hψ : ψ ∈ integralDomain S f) :
    ‖spectralIntegral S f ψ‖ₑ ^ 2 = sqNormLIntegral (spectralMeasure S ψ) f := by
  rw [spectralIntegral_of_mem hψ]
  exact H.norm_limit ψ f hf hψ
private lemma CalculusInputs.exists_approx (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ : 𝒦} (hf : Measurable f) (hψ : ψ ∈ integralDomain S f) :
    ∃ q, PolynomialL2Approximation S ψ f q := by
  haveI := H.fin ψ
  obtain ⟨q, hq, ht⟩ := H.seq _ f hf hψ
  exact ⟨q, hq, ht⟩
private lemma CalculusInputs.exists_approx₂ (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ ψ' : 𝒦} (hf : Measurable f) (hψ : ψ ∈ integralDomain S f)
    (hψ' : ψ' ∈ integralDomain S f) :
    ∃ q, PolynomialL2Approximation S ψ f q ∧ PolynomialL2Approximation S ψ' f q := by
  haveI := H.fin ψ
  haveI := H.fin ψ'
  obtain ⟨q, hq, ht⟩ := H.seq (spectralMeasure S ψ + spectralMeasure S ψ') f hf (by
    rw [sqNorm_add_measure]
    exact ENNReal.add_lt_top.2 ⟨hψ, hψ'⟩)
  refine ⟨q, ⟨hq, ?_⟩, ⟨hq, ?_⟩⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => zero_le) fun l => ?_
    simp only [sqNorm_add_measure]
    exact le_self_add
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => zero_le) fun l => ?_
    simp only [sqNorm_add_measure]
    exact le_add_self
private lemma CalculusInputs.sq_add_vec (H : CalculusInputs S) (ψ ψ' : 𝒦)
    (u : SpectralDomain J → ℂ) :
    sqNormLIntegral (spectralMeasure S (ψ + ψ')) u ≤
      2 * sqNormLIntegral (spectralMeasure S ψ) u +
        2 * sqNormLIntegral (spectralMeasure S ψ') u := by
  have hle : spectralMeasure S (ψ + ψ') ≤
      (2 : ℝ≥0∞) • spectralMeasure S ψ + (2 : ℝ≥0∞) • spectralMeasure S ψ' := by
    refine Measure.le_iff.2 fun B hB => ?_
    simpa using H.add_le ψ ψ' B hB
  unfold sqNormLIntegral
  calc ∫⁻ p, ‖u p‖ₑ ^ 2 ∂spectralMeasure S (ψ + ψ')
      ≤ ∫⁻ p, ‖u p‖ₑ ^ 2 ∂((2 : ℝ≥0∞) • spectralMeasure S ψ +
          (2 : ℝ≥0∞) • spectralMeasure S ψ') :=
        lintegral_mono' hle le_rfl
    _ = _ := by
        rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
        rfl
private lemma CalculusInputs.sq_smul_vec (H : CalculusInputs S) (c : ℂ) (ψ : 𝒦)
    (u : SpectralDomain J → ℂ) :
    sqNormLIntegral (spectralMeasure S (c • ψ)) u =
      ‖c‖ₑ ^ 2 * sqNormLIntegral (spectralMeasure S ψ) u := by
  unfold sqNormLIntegral
  rw [H.smul, lintegral_smul_measure]
  rfl
private lemma tendsto_two_mul_add_two_mul {a b : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto (fun l => 2 * a l + 2 * b l) atTop (𝓝 0) := by
  have h1 := ENNReal.Tendsto.const_mul (a := 2) ha (Or.inr ENNReal.ofNat_ne_top)
  have h2 := ENNReal.Tendsto.const_mul (a := 2) hb (Or.inr ENNReal.ofNat_ne_top)
  simpa using h1.add h2
private lemma CalculusInputs.add_mem (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ ψ' : 𝒦} (hψ : ψ ∈ integralDomain S f) (hψ' : ψ' ∈ integralDomain S f) :
    ψ + ψ' ∈ integralDomain S f := by
  refine (H.sq_add_vec ψ ψ' f).trans_lt ?_
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hψ, ENNReal.mul_lt_top (by simp) hψ'⟩
private lemma CalculusInputs.smul_mem (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ : 𝒦} (c : ℂ) (hψ : ψ ∈ integralDomain S f) : c • ψ ∈ integralDomain S f := by
  rw [mem_integralDomain, H.sq_smul_vec]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (by simp)) hψ
private lemma CalculusInputs.zero_mem (H : CalculusInputs S) (f : SpectralDomain J → ℂ) :
    (0 : 𝒦) ∈ integralDomain S f := by
  rw [mem_integralDomain]
  have h := H.sq_smul_vec 0 (0 : 𝒦) f
  rw [smul_zero] at h
  rw [h]
  simp
private lemma CalculusInputs.approx_add (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ ψ' : 𝒦} {q : ℕ → SpectralDomain J → ℂ} (a : PolynomialL2Approximation S ψ f q)
    (b : PolynomialL2Approximation S ψ' f q) : PolynomialL2Approximation S (ψ + ψ') f q := by
  refine ⟨a.1, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_two_mul_add_two_mul a.2 b.2) (fun _ => zero_le) fun l => H.sq_add_vec ψ ψ' _
private lemma CalculusInputs.approx_smul (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ : 𝒦} (c : ℂ) {q : ℕ → SpectralDomain J → ℂ} (a : PolynomialL2Approximation S ψ f q) :
    PolynomialL2Approximation S (c • ψ) f q := by
  refine ⟨a.1, ?_⟩
  simp only [H.sq_smul_vec]
  have h := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ ^ 2) a.2
    (Or.inr (ENNReal.pow_ne_top (by simp)))
  simpa using h
private lemma CalculusInputs.integral_add (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ ψ' : 𝒦} (hf : Measurable f) (hψ : ψ ∈ integralDomain S f)
    (hψ' : ψ' ∈ integralDomain S f) :
    spectralIntegral S f (ψ + ψ') = spectralIntegral S f ψ + spectralIntegral S f ψ' := by
  obtain ⟨q, a, b⟩ := H.exists_approx₂ hf hψ hψ'
  refine tendsto_nhds_unique (H.tendsto hf (H.add_mem hψ hψ') (H.approx_add a b)) ?_
  refine ((H.tendsto hf hψ a).add (H.tendsto hf hψ' b)).congr fun l => ?_
  simp
private lemma CalculusInputs.integral_smul (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ : 𝒦} (c : ℂ) (hf : Measurable f) (hψ : ψ ∈ integralDomain S f) :
    spectralIntegral S f (c • ψ) = c • spectralIntegral S f ψ := by
  obtain ⟨q, a⟩ := H.exists_approx hf hψ
  refine tendsto_nhds_unique (H.tendsto hf (H.smul_mem c hψ) (H.approx_smul c a)) ?_
  refine ((H.tendsto hf hψ a).const_smul c).congr fun l => ?_
  simp
private lemma CalculusInputs.inner_integral (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ : 𝒦} (hf : Measurable f) (hψ : ψ ∈ integralDomain S f) :
    inner ℂ ψ (spectralIntegral S f ψ) = ∫ p, f p ∂(spectralMeasure S ψ) := by
  haveI := H.fin ψ
  obtain ⟨q, a⟩ := H.exists_approx hf hψ
  have t1 : Tendsto (fun l => inner ℂ ψ (polynomialCalculus S (q l) ψ)) atTop
      (𝓝 (inner ℂ ψ (spectralIntegral S f ψ))) :=
    Tendsto.inner tendsto_const_nhds (H.tendsto hf hψ a)
  have hone : IsBoundedFn (1 : SpectralDomain J → ℂ) := ⟨1, fun p => by simp⟩
  have t2 := tendsto_integral_mul_of_sqNorm (ρ := spectralMeasure S ψ) (u := f)
    (v := (1 : SpectralDomain J → ℂ)) (U := q) (V := fun _ => 1) hf measurable_const
    (fun l => measurable_of_mem_spectralPolynomials (a.1 l)) (fun _ => measurable_const) hψ
    (sqNorm_lt_top_of_bounded hone)
    (fun l => sqNorm_lt_top_of_bounded (isBoundedFn_of_mem_spectralPolynomials (a.1 l)))
    (fun _ => sqNorm_lt_top_of_bounded hone) a.2 (by simp [sqNorm_zero])
  simp only [Pi.one_apply, mul_one] at t2
  refine tendsto_nhds_unique t1 (t2.congr fun l => ?_)
  exact (H.inner_poly ψ _ (a.1 l)).symm
private lemma CalculusInputs.mem_domain_of_bounded (H : CalculusInputs S)
    {f : SpectralDomain J → ℂ} (hb : IsBoundedFn f) (ψ : 𝒦) : ψ ∈ integralDomain S f := by
  haveI := H.fin ψ
  exact sqNorm_lt_top_of_bounded hb
private lemma CalculusInputs.norm_le (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    (hf : Measurable f) (hb : IsBoundedFn f) (ψ : 𝒦) :
    ‖spectralIntegral S f ψ‖ ≤ (⨆ p, ‖f p‖) * ‖ψ‖ := by
  haveI := H.fin ψ
  obtain ⟨M, hM⟩ := hb
  have hbdd : BddAbove (range fun p => ‖f p‖) := ⟨M, by rintro _ ⟨p, rfl⟩; exact hM p⟩
  have hnn : 0 ≤ ⨆ p, ‖f p‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have h1 := H.norm_integral hf (H.mem_domain_of_bounded ⟨M, hM⟩ ψ)
  have h2 := sqNorm_le_of_bound (ρ := spectralMeasure S ψ) (u := f) (fun p => le_ciSup hbdd p)
  rw [← h1, H.mass, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow hnn,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  rw [← mul_pow] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h2
private lemma clm_eq_of_inner_self {C C' : 𝒦 →L[ℂ] 𝒦}
    (h : ∀ ψ, inner ℂ ψ (C ψ) = inner ℂ ψ (C' ψ)) : C = C' := by apply _root_.YangMills.Construction.ContractionUnitary.JointSpectral.eq_of_inner_self <;> assumption
private lemma CalculusInputs.exists_bounded (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    (hf : Measurable f) (hb : IsBoundedFn f) :
    ∃ C : 𝒦 →L[ℂ] 𝒦, ⇑C = spectralIntegral S f ∧ ‖C‖ ≤ ⨆ p, ‖f p‖ := by
  have hnn : 0 ≤ ⨆ p, ‖f p‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  let L : 𝒦 →ₗ[ℂ] 𝒦 :=
    { toFun := spectralIntegral S f
      map_add' := fun x y => H.integral_add hf (H.mem_domain_of_bounded hb x)
        (H.mem_domain_of_bounded hb y)
      map_smul' := fun c x => H.integral_smul c hf (H.mem_domain_of_bounded hb x) }
  exact ⟨L.mkContinuous _ (H.norm_le hf hb), rfl, LinearMap.mkContinuous_norm_le _ hnn _⟩
private lemma approx_of_mem_spectralPolynomials {q : SpectralDomain J → ℂ}
    (hq : q ∈ spectralPolynomials J) (ψ : 𝒦) :
    PolynomialL2Approximation S ψ q (fun _ => q) :=
  ⟨fun _ => hq, by simp [sqNorm_zero]⟩
private lemma CalculusInputs.integral_polynomial (H : CalculusInputs S)
    {q : SpectralDomain J → ℂ} (hq : q ∈ spectralPolynomials J) :
    spectralIntegral S q = ⇑(polynomialCalculus S q) := by
  funext ψ
  exact tendsto_nhds_unique (H.tendsto (measurable_of_mem_spectralPolynomials hq)
    (H.mem_domain_of_bounded (isBoundedFn_of_mem_spectralPolynomials hq) ψ)
    (approx_of_mem_spectralPolynomials hq ψ)) tendsto_const_nhds
private lemma CalculusInputs.op_monomial (H : CalculusInputs S) (n : ℕ) (y : J → ℤ) :
    polynomialCalculus S (spectralMonomial n y) = familyMonomial S n y := by
  rw [← spectralSum_singleton, H.op_sum]
  simp [familySum]
private lemma CalculusInputs.approx_comb (H : CalculusInputs S) {f g : SpectralDomain J → ℂ}
    {ψ : 𝒦} (c : ℂ) (hf : Measurable f) {q r : ℕ → SpectralDomain J → ℂ}
    (a : PolynomialL2Approximation S ψ f q) (b : PolynomialL2Approximation S ψ g r) :
    PolynomialL2Approximation S ψ (f + c • g) (fun l => q l + c • r l) := by
  refine ⟨fun l => H.poly_add _ (a.1 l) _ (H.poly_smul c _ (b.1 l)), ?_⟩
  have hc := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ ^ 2) b.2
    (Or.inr (ENNReal.pow_ne_top (by simp)))
  simp only [mul_zero] at hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_two_mul_add_two_mul a.2 hc) (fun _ => zero_le) fun l => ?_
  have e : f + c • g - (q l + c • r l) = (f - q l) + c • (g - r l) := by
    funext p
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [e]
  rw [← sqNorm_smul]
  exact sqNorm_add_le _ (hf.sub (measurable_of_mem_spectralPolynomials (a.1 l)))
private lemma CalculusInputs.comb_mem (H : CalculusInputs S) {f g : SpectralDomain J → ℂ}
    {ψ : 𝒦} (c : ℂ) (hf : Measurable f) (hψ : ψ ∈ integralDomain S f)
    (hψ' : ψ ∈ integralDomain S g) : ψ ∈ integralDomain S (f + c • g) := by
  refine (sqNorm_add_le _ hf).trans_lt ?_
  rw [sqNorm_smul]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hψ, ENNReal.mul_lt_top (by simp)
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (by simp)) hψ')⟩
private lemma CalculusInputs.integral_comb (H : CalculusInputs S) {f g : SpectralDomain J → ℂ}
    {ψ : 𝒦} (c : ℂ) (hf : Measurable f) (hg : Measurable g) (hψ : ψ ∈ integralDomain S f)
    (hψ' : ψ ∈ integralDomain S g) :
    spectralIntegral S (f + c • g) ψ = spectralIntegral S f ψ + c • spectralIntegral S g ψ := by
  obtain ⟨q, a⟩ := H.exists_approx hf hψ
  obtain ⟨r, b⟩ := H.exists_approx hg hψ'
  refine tendsto_nhds_unique (H.tendsto (hf.add (hg.const_smul c)) (H.comb_mem c hf hψ hψ')
    (H.approx_comb c hf a b)) ?_
  refine ((H.tendsto hf hψ a).add ((H.tendsto hg hψ' b).const_smul c)).congr fun l => ?_
  rw [H.op_add _ (a.1 l) _ (H.poly_smul c _ (b.1 l)), H.op_smul c _ (b.1 l)]
  simp
private lemma integralDomain_smul {f : SpectralDomain J → ℂ} {c : ℂ} (hc : c ≠ 0) :
    integralDomain S (c • f) = integralDomain S f := by
  ext ψ
  rw [mem_integralDomain, mem_integralDomain, sqNorm_smul]
  constructor
  · intro h
    by_contra hn
    rw [not_lt, top_le_iff] at hn
    rw [hn, ENNReal.mul_top (by simpa using hc)] at h
    exact lt_irrefl _ h
  · exact fun h => ENNReal.mul_lt_top (ENNReal.pow_lt_top (by simp)) h
private lemma integralDomain_conj (f : SpectralDomain J → ℂ) :
    integralDomain S (fun p => conj (f p)) = integralDomain S f := by
  ext ψ
  rw [mem_integralDomain, mem_integralDomain, sqNorm_congr fun p => RCLike.norm_conj _]
private lemma CalculusInputs.approx_conj (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ : 𝒦} {q : ℕ → SpectralDomain J → ℂ} (a : PolynomialL2Approximation S ψ f q) :
    PolynomialL2Approximation S ψ (fun p => conj (f p)) (fun l p => conj (q l p)) := by
  refine ⟨fun l => H.poly_conj _ (a.1 l), ?_⟩
  refine a.2.congr fun l => ?_
  refine sqNorm_congr fun p => ?_
  simp only [Pi.sub_apply, ← map_sub, RCLike.norm_conj]
private lemma CalculusInputs.inner_adjoint (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    {ψ ψ' : 𝒦} (hf : Measurable f) (hψ : ψ ∈ integralDomain S f)
    (hψ' : ψ' ∈ integralDomain S f) :
    inner ℂ ψ' (spectralIntegral S f ψ) =
      inner ℂ (spectralIntegral S (fun p => conj (f p)) ψ') ψ := by
  obtain ⟨q, a, b⟩ := H.exists_approx₂ hf hψ hψ'
  have hcf : Measurable fun p => conj (f p) := Complex.continuous_conj.measurable.comp hf
  have hψc : ψ' ∈ integralDomain S (fun p => conj (f p)) := by rwa [integralDomain_conj]
  have t1 : Tendsto (fun l => inner ℂ ψ' (polynomialCalculus S (q l) ψ)) atTop
      (𝓝 (inner ℂ ψ' (spectralIntegral S f ψ))) :=
    Tendsto.inner tendsto_const_nhds (H.tendsto hf hψ a)
  have t2 : Tendsto (fun l => inner ℂ (polynomialCalculus S (fun p => conj (q l p)) ψ') ψ)
      atTop (𝓝 (inner ℂ (spectralIntegral S (fun p => conj (f p)) ψ') ψ)) :=
    Tendsto.inner (H.tendsto hcf hψc (H.approx_conj b)) tendsto_const_nhds
  refine tendsto_nhds_unique t1 (t2.congr fun l => ?_)
  rw [H.op_conj _ (a.1 l), ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
private lemma CalculusInputs.star_bounded (H : CalculusInputs S) {f : SpectralDomain J → ℂ}
    (hf : Measurable f) (hb : IsBoundedFn f) :
    ∃ C : 𝒦 →L[ℂ] 𝒦, ⇑C = spectralIntegral S f ∧
      ⇑(star C) = spectralIntegral S (fun p => conj (f p)) := by
  obtain ⟨C, hC, -⟩ := H.exists_bounded hf hb
  refine ⟨C, hC, ?_⟩
  funext x
  refine ext_inner_left ℂ fun v => ?_
  have hD := H.mem_domain_of_bounded hb
  have hDc : ∀ ψ, ψ ∈ integralDomain S (fun p => conj (f p)) := fun ψ => by
    rw [integralDomain_conj]
    exact hD ψ
  have hcf : Measurable fun p => conj (f p) := Complex.continuous_conj.measurable.comp hf
  have h := H.inner_adjoint hcf (hDc x) (hDc v)
  simp only [Complex.conj_conj] at h
  rw [h, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, hC]
private lemma CalculusInputs.approx_mul (H : CalculusInputs S) {g r : SpectralDomain J → ℂ}
    {ψ : 𝒦} (hr : r ∈ spectralPolynomials J) {q : ℕ → SpectralDomain J → ℂ}
    (a : PolynomialL2Approximation S ψ g q) :
    PolynomialL2Approximation S ψ (r * g) (fun l => r * q l) := by
  obtain ⟨R, hR⟩ := isBoundedFn_of_mem_spectralPolynomials hr
  refine ⟨fun l => H.poly_mul _ hr _ (a.1 l), ?_⟩
  have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal R ^ 2) a.2
    (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  simp only [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) fun l => ?_
  simp only [← mul_sub]
  exact sqNorm_mul_le hR _
private lemma CalculusInputs.mul_mem (H : CalculusInputs S) {g r : SpectralDomain J → ℂ}
    {ψ : 𝒦} (hr : IsBoundedFn r) (hψ : ψ ∈ integralDomain S g) :
    ψ ∈ integralDomain S (r * g) := by
  obtain ⟨R, hR⟩ := hr
  refine (sqNorm_mul_le hR g).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hψ
private lemma CalculusInputs.scalar_of_integral (H : CalculusInputs S)
    {g : SpectralDomain J → ℂ} {ψ : 𝒦} (hg : Measurable g) (hψ : ψ ∈ integralDomain S g) :
    spectralMeasure S (spectralIntegral S g ψ) =
      (spectralMeasure S ψ).withDensity (fun p => ‖g p‖ₑ ^ 2) := by
  haveI := H.fin ψ
  symm
  refine H.uniq _ _ ⟨isFiniteMeasure_withDensity hψ.ne, fun n y => ?_⟩
  obtain ⟨q, a⟩ := H.exists_approx hg hψ
  have hr : spectralMonomial n y ∈ spectralPolynomials J := spectralMonomial_mem n y
  have hrb := isBoundedFn_of_mem_spectralPolynomials hr
  have hrm := measurable_of_mem_spectralPolynomials hr
  have hqm := fun l => measurable_of_mem_spectralPolynomials (a.1 l)
  have hqb := fun l => isBoundedFn_of_mem_spectralPolynomials (a.1 l)
  have hcm : Measurable fun p => conj (g p) := Complex.continuous_conj.measurable.comp hg
  have hcqm : ∀ l, Measurable fun p => conj (q l p) := fun l =>
    Complex.continuous_conj.measurable.comp (hqm l)
  have tφ := H.tendsto hg hψ a
  have t1 : Tendsto (fun l => inner ℂ (polynomialCalculus S (q l) ψ)
      (familyMonomial S n y (polynomialCalculus S (q l) ψ))) atTop
      (𝓝 (inner ℂ (spectralIntegral S g ψ)
        (familyMonomial S n y (spectralIntegral S g ψ)))) :=
    Tendsto.inner tφ (((familyMonomial S n y).continuous.tendsto _).comp tφ)
  have t2 := tendsto_integral_mul_of_sqNorm (ρ := spectralMeasure S ψ)
    (u := fun p => conj (g p))
    (v := spectralMonomial n y * g) (U := fun l p => conj (q l p))
    (V := fun l => spectralMonomial n y * q l)
    hcm (hrm.mul hg) hcqm (fun l => hrm.mul (hqm l))
    (by rw [← mem_integralDomain, integralDomain_conj]; exact hψ) (H.mul_mem hrb hψ)
    (fun l => H.mem_domain_of_bounded (by
      rw [IsBoundedFn] at *
      obtain ⟨M, hM⟩ := hqb l
      exact ⟨M, fun p => by simpa using hM p⟩) ψ)
    (fun l => H.mul_mem hrb (H.mem_domain_of_bounded (hqb l) ψ))
    (H.approx_conj a).2 (H.approx_mul hr a).2
  refine tendsto_nhds_unique t1 ?_
  have e : ∫ p, spectralMonomial n y p ∂((spectralMeasure S ψ).withDensity
        fun p => ‖g p‖ₑ ^ 2) =
      ∫ p, conj (g p) * (spectralMonomial n y * g) p ∂(spectralMeasure S ψ) := by
    rw [integral_withDensity_eq_integral_toReal_smul (measurable_enorm_sq hg)
      (Eventually.of_forall fun p => ENNReal.pow_lt_top enorm_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [ENNReal.toReal_pow, toReal_enorm, Complex.real_smul, Pi.mul_apply]
    push_cast
    rw [← Complex.conj_mul' (g p)]
    ring
  rw [e]
  refine t2.congr fun l => ?_
  have hQ : (fun p => conj (q l p)) * (spectralMonomial n y * q l) ∈ spectralPolynomials J :=
    H.poly_mul _ (H.poly_conj _ (a.1 l)) _ (H.poly_mul _ hr _ (a.1 l))
  have h := H.inner_poly ψ _ hQ
  simp only [Pi.mul_apply] at h ⊢
  rw [← h, H.op_mul _ (H.poly_conj _ (a.1 l)) _ (H.poly_mul _ hr _ (a.1 l)),
    H.op_conj _ (a.1 l), H.op_mul _ hr _ (a.1 l), H.op_monomial,
    ContinuousLinearMap.star_eq_adjoint]
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right]
private lemma CalculusInputs.sq_of_integral (H : CalculusInputs S)
    {g h : SpectralDomain J → ℂ} {ψ : 𝒦} (hg : Measurable g) (hψ : ψ ∈ integralDomain S g)
    (hh : Measurable h) :
    sqNormLIntegral (spectralMeasure S (spectralIntegral S g ψ)) h =
      sqNormLIntegral (spectralMeasure S ψ) (h * g) := by
  unfold sqNormLIntegral
  rw [H.scalar_of_integral hg hψ,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_enorm_sq hg) (measurable_enorm_sq hh)]
  refine lintegral_congr fun p => ?_
  simp [mul_pow, mul_comm]
private lemma CalculusInputs.op_integral (H : CalculusInputs S) {g r : SpectralDomain J → ℂ}
    {ψ : 𝒦} (hr : r ∈ spectralPolynomials J) (hg : Measurable g)
    (hψ : ψ ∈ integralDomain S g) :
    polynomialCalculus S r (spectralIntegral S g ψ) = spectralIntegral S (r * g) ψ := by
  obtain ⟨q, a⟩ := H.exists_approx hg hψ
  have t1 := ((polynomialCalculus S r).continuous.tendsto _).comp (H.tendsto hg hψ a)
  refine tendsto_nhds_unique t1 ?_
  refine (H.tendsto ((measurable_of_mem_spectralPolynomials hr).mul hg)
    (H.mul_mem (isBoundedFn_of_mem_spectralPolynomials hr) hψ) (H.approx_mul hr a)).congr
    fun l => ?_
  rw [H.op_mul _ hr _ (a.1 l)]
  rfl
private lemma tendsto_of_enorm_sub_sq {x : ℕ → 𝒦} {v : 𝒦}
    (h : Tendsto (fun l => ‖x l - v‖ₑ ^ 2) atTop (𝓝 0)) : Tendsto x atTop (𝓝 v) := by
  have h' := tendsto_rpow_half_of_tendsto_zero h
  have e : ∀ a : ℝ≥0∞, (a ^ 2) ^ (1 / 2 : ℝ) = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [e] at h'
  rw [tendsto_iff_edist_tendsto_0]
  simpa only [edist_eq_enorm_sub] using h'
private lemma CalculusInputs.integral_integral (H : CalculusInputs S)
    {f g : SpectralDomain J → ℂ} {ψ : 𝒦} (hf : Measurable f) (hg : Measurable g)
    (hψ : ψ ∈ integralDomain S g) (hfg : ψ ∈ integralDomain S (f * g)) :
    spectralIntegral S g ψ ∈ integralDomain S f ∧
      spectralIntegral S f (spectralIntegral S g ψ) = spectralIntegral S (f * g) ψ := by
  have hφ : spectralIntegral S g ψ ∈ integralDomain S f := by
    rw [mem_integralDomain, H.sq_of_integral hg hψ hf]
    exact hfg
  refine ⟨hφ, ?_⟩
  obtain ⟨r, a⟩ := H.exists_approx hf hφ
  refine tendsto_nhds_unique (H.tendsto hf hφ a) (tendsto_of_enorm_sub_sq ?_)
  have key : ∀ l, ‖polynomialCalculus S (r l) (spectralIntegral S g ψ) -
      spectralIntegral S (f * g) ψ‖ₑ ^ 2 =
      sqNormLIntegral (spectralMeasure S (spectralIntegral S g ψ)) (f - r l) := fun l => by
    have hrm := measurable_of_mem_spectralPolynomials (a.1 l)
    have hrg : ψ ∈ integralDomain S (r l * g) :=
      H.mul_mem (isBoundedFn_of_mem_spectralPolynomials (a.1 l)) hψ
    have hW := H.comb_mem (-1) (hf.mul hg) hfg hrg
    have hWm : Measurable (f * g + (-1 : ℂ) • (r l * g)) :=
      (hf.mul hg).add ((hrm.mul hg).const_smul _)
    have hcomb := H.integral_comb (-1) (hf.mul hg) (hrm.mul hg) hfg hrg
    have hn := H.norm_integral hWm hW
    rw [H.sq_of_integral hg hψ (hf.sub hrm), H.op_integral (a.1 l) hg hψ, enorm_sub_rev]
    have e : f * g + (-1 : ℂ) • (r l * g) = (f - r l) * g := by
      funext p
      simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [e] at hn hcomb
    rw [← hn, hcomb, sub_eq_add_neg]
    simp
  simp only [key]
  exact a.2
private lemma isBoundedFn_mul {f g : SpectralDomain J → ℂ} (hf : IsBoundedFn f)
    (hg : IsBoundedFn g) : IsBoundedFn (f * g) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨M', hM'⟩ := hg
  refine ⟨M * M', fun p => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hM p) (hM' p) (norm_nonneg _) ((norm_nonneg _).trans (hM p))
private lemma CalculusInputs.integral_mul_bounded (H : CalculusInputs S)
    {f g : SpectralDomain J → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfb : IsBoundedFn f) (hgb : IsBoundedFn g) :
    spectralIntegral S (f * g) = spectralIntegral S f ∘ spectralIntegral S g := by
  funext ψ
  exact (H.integral_integral hf hg (H.mem_domain_of_bounded hgb ψ)
    (H.mem_domain_of_bounded (isBoundedFn_mul hfb hgb) ψ)).2.symm
private lemma measurable_indicator_one {T : Set (SpectralDomain J)} (hT : MeasurableSet T) :
    Measurable (T.indicator (1 : SpectralDomain J → ℂ)) :=
  measurable_one.indicator hT
private lemma isBoundedFn_indicator_one (T : Set (SpectralDomain J)) :
    IsBoundedFn (T.indicator (1 : SpectralDomain J → ℂ)) := by
  refine ⟨1, fun p => ?_⟩
  by_cases h : p ∈ T <;> simp [h]
private lemma CalculusInputs.inner_spectral (H : CalculusInputs S)
    {T : Set (SpectralDomain J)} (hT : MeasurableSet T) (ψ : 𝒦) :
    inner ℂ ψ (jointSpectralMeasure S T ψ) = (((spectralMeasure S ψ).real T : ℝ) : ℂ) := by
  haveI := H.fin ψ
  unfold jointSpectralMeasure
  rw [H.inner_integral (measurable_indicator_one hT)
    (H.mem_domain_of_bounded (isBoundedFn_indicator_one T) ψ)]
  have h : ∫ p, T.indicator (1 : SpectralDomain J → ℂ) p ∂(spectralMeasure S ψ) =
      (spectralMeasure S ψ).real T • (1 : ℂ) := integral_indicator_const (1 : ℂ) hT
  rw [h]
  simp
private lemma CalculusInputs.norm_spectral (H : CalculusInputs S)
    {T : Set (SpectralDomain J)} (hT : MeasurableSet T) (ψ : 𝒦) :
    ‖jointSpectralMeasure S T ψ‖ₑ ^ 2 = spectralMeasure S ψ T := by
  unfold jointSpectralMeasure
  rw [H.norm_integral (measurable_indicator_one hT)
    (H.mem_domain_of_bounded (isBoundedFn_indicator_one T) ψ)]
  unfold sqNormLIntegral
  rw [← lintegral_indicator_one hT]
  refine lintegral_congr fun p => ?_
  by_cases h : p ∈ T <;> simp [h]
private lemma CalculusInputs.spectral_inter (H : CalculusInputs S)
    {T T' : Set (SpectralDomain J)} (hT : MeasurableSet T) (hT' : MeasurableSet T') :
    jointSpectralMeasure S T ∘ jointSpectralMeasure S T' = jointSpectralMeasure S (T ∩ T') := by
  unfold jointSpectralMeasure
  rw [← H.integral_mul_bounded (measurable_indicator_one hT) (measurable_indicator_one hT')
    (isBoundedFn_indicator_one T) (isBoundedFn_indicator_one T'), inter_indicator_one]
private lemma projectionValuedMeasure_ext {P P' : ProjectionValuedMeasure J 𝒦}
    (h : P.E = P'.E) : P = P' := by
  obtain ⟨E, _, _, _⟩ := P
  obtain ⟨E', _, _, _⟩ := P'
  simp only at h
  subst h
  rfl
private lemma conj_indicator_one (T : Set (SpectralDomain J)) :
    (fun p => conj (T.indicator (1 : SpectralDomain J → ℂ) p)) = T.indicator 1 := by
  funext p
  by_cases h : p ∈ T <;> simp [h]
private lemma CalculusInputs.exists_pvm (H : CalculusInputs S) :
    ∃ P : ProjectionValuedMeasure J 𝒦,
      (∀ T, ⇑(P.E T) = jointSpectralMeasure S T.1) ∧
      HasSystemMoments S P ∧
      ∀ P' : ProjectionValuedMeasure J 𝒦, HasSystemMoments S P' → P' = P := by
  have hex : ∀ T : {T : Set (SpectralDomain J) // MeasurableSet T},
      ∃ C : 𝒦 →L[ℂ] 𝒦, ⇑C = jointSpectralMeasure S T.1 ∧
        ⇑(star C) = jointSpectralMeasure S T.1 := by
    intro T
    obtain ⟨C, h, h'⟩ := H.star_bounded (measurable_indicator_one T.2)
      (isBoundedFn_indicator_one T.1)
    rw [conj_indicator_one] at h'
    exact ⟨C, h, h'⟩
  choose C hC hC' using hex
  have hinner : ∀ T ψ, inner ℂ ψ (C T ψ) = (((spectralMeasure S ψ).real T.1 : ℝ) : ℂ) := by
    intro T ψ
    rw [hC T]
    exact H.inner_spectral T.2 ψ
  let P : ProjectionValuedMeasure J 𝒦 :=
    { E := C
      isStarProjection := fun T => by
        refine ⟨?_, DFunLike.coe_injective ((hC' T).trans (hC T).symm)⟩
        refine DFunLike.coe_injective ?_
        have h := H.spectral_inter T.2 T.2
        rw [inter_self] at h
        rw [hC T, ← h]
        funext ψ
        simp [hC T]
      E_univ := by
        refine clm_eq_of_inner_self fun ψ => ?_
        haveI := H.fin ψ
        rw [hinner]
        simp [measureReal_def, H.mass, ENNReal.toReal_pow, inner_self_eq_norm_sq_to_K]
      exists_scalarMeasure := fun ψ => ⟨spectralMeasure S ψ, H.fin ψ, fun T => hinner T ψ⟩ }
  refine ⟨P, hC, fun ψ => ⟨spectralMeasure S ψ, H.fin ψ, fun T => hinner T ψ,
    (H.isScalar ψ).2⟩, fun P' hP' => projectionValuedMeasure_ext ?_⟩
  funext T
  refine clm_eq_of_inner_self fun ψ => ?_
  obtain ⟨μ, hfin, hμ, hmom⟩ := hP' ψ
  have e : μ = spectralMeasure S ψ := H.uniq ψ μ ⟨hfin, hmom⟩
  rw [hμ T, e]
  exact (hinner T ψ).symm
private lemma CalculusInputs.null_union (H : CalculusInputs S)
    (𝒯 : Set (Set (SpectralDomain J))) (hc : 𝒯.Countable)
    (h : ∀ T ∈ 𝒯, MeasurableSet T ∧ jointSpectralMeasure S T = 0) :
    MeasurableSet (⋃₀ 𝒯) ∧ jointSpectralMeasure S (⋃₀ 𝒯) = 0 := by
  have hm : MeasurableSet (⋃₀ 𝒯) := MeasurableSet.sUnion hc fun T hT => (h T hT).1
  refine ⟨hm, ?_⟩
  funext ψ
  have h0 : spectralMeasure S ψ (⋃₀ 𝒯) = 0 := by
    refine (measure_sUnion_null_iff hc).2 fun T hT => ?_
    rw [← H.norm_spectral (h T hT).1 ψ, (h T hT).2]
    simp
  have h1 := H.norm_spectral hm ψ
  rw [h0] at h1
  simpa using h1
private lemma CalculusInputs.congr_of_null (H : CalculusInputs S) {f g : SpectralDomain J → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (h : jointSpectralMeasure S {p | f p ≠ g p} = 0) :
    integralDomain S f = integralDomain S g ∧ spectralIntegral S f = spectralIntegral S g := by
  have hm : MeasurableSet {p | f p ≠ g p} := (measurableSet_eq_fun hf hg).compl
  have hae : ∀ ψ, f =ᵐ[spectralMeasure S ψ] g := fun ψ => by
    rw [Filter.EventuallyEq, ae_iff, ← H.norm_spectral hm ψ, h]
    simp
  have hsq : ∀ ψ (u v : SpectralDomain J → ℂ), u =ᵐ[spectralMeasure S ψ] v →
      sqNormLIntegral (spectralMeasure S ψ) u = sqNormLIntegral (spectralMeasure S ψ) v := by
    intro ψ u v huv
    refine lintegral_congr_ae ?_
    filter_upwards [huv] with p hp
    rw [hp]
  have hD : integralDomain S f = integralDomain S g := by
    ext ψ
    rw [mem_integralDomain, mem_integralDomain, hsq ψ f g (hae ψ)]
  refine ⟨hD, ?_⟩
  funext ψ
  by_cases hψ : ψ ∈ integralDomain S f
  · obtain ⟨q, a⟩ := H.exists_approx hf hψ
    have b : PolynomialL2Approximation S ψ g q := by
      refine ⟨a.1, a.2.congr fun l => hsq ψ _ _ ?_⟩
      filter_upwards [hae ψ] with p hp
      simp [hp]
    exact tendsto_nhds_unique (H.tendsto hf hψ a) (H.tendsto hg (hD ▸ hψ) b)
  · rw [spectralIntegral_of_not_mem hψ, spectralIntegral_of_not_mem (hD ▸ hψ)]
end System
theorem borelCalculusStatement_of_polynomialCalculus (h₁ : PolynomialCalculusStatement)
    (h₂ : ScalarSpectralMeasuresStatement) : BorelCalculusStatement := by
  intro 𝒦 _ _ _ J _ _ S
  have H : CalculusInputs S := calculusInputs h₁ h₂ S
  refine ⟨fun f hf => ⟨⟨⟨⟨⟨integralDomain S f, fun hx hy => H.add_mem hx hy⟩, H.zero_mem f⟩,
      fun c x hx => H.smul_mem c hx⟩, rfl⟩,
      fun ψ hψ ψ' hψ' => H.integral_add hf hψ hψ',
      fun c ψ hψ => H.integral_smul c hf hψ,
      fun ψ hψ => ⟨H.norm_integral hf hψ, H.inner_integral hf hψ⟩,
      fun hb => ⟨eq_univ_of_forall (H.mem_domain_of_bounded hb), ?_⟩⟩,
    fun q hq => ⟨eq_univ_of_forall
        (H.mem_domain_of_bounded (isBoundedFn_of_mem_spectralPolynomials hq)),
      H.integral_polynomial hq⟩,
    fun n y => ⟨eq_univ_of_forall
        (H.mem_domain_of_bounded
          (isBoundedFn_of_mem_spectralPolynomials (spectralMonomial_mem n y))), by
      rw [H.integral_polynomial (spectralMonomial_mem n y), H.op_monomial]⟩,
    fun f g hf hg c ψ hψ hψ' => ⟨H.comb_mem c hf hψ hψ', H.integral_comb c hf hg hψ hψ'⟩,
    fun f _ c hc => integralDomain_smul hc,
    fun f hf => ⟨integralDomain_conj f, fun ψ hψ ψ' hψ' => H.inner_adjoint hf hψ hψ',
      fun hb => H.star_bounded hf hb⟩,
    fun g hg ψ hψ => ⟨H.scalar_of_integral hg hψ,
      fun f hf hfg => H.integral_integral hf hg hψ hfg⟩,
    fun f g hf hg hfb hgb => ⟨H.integral_mul_bounded hf hg hfb hgb, ?_⟩,
    H.exists_pvm,
    fun T ψ hT => ⟨H.inner_spectral hT ψ, H.norm_spectral hT ψ⟩,
    fun T T' hT hT' => H.spectral_inter hT hT',
    H.null_union,
    fun f g hf hg h => H.congr_of_null hf hg h⟩
  · obtain ⟨C, hC, hn⟩ := H.exists_bounded (f := f) hf hb
    refine ⟨C, hC, hn, fun C' hC' => clm_eq_of_inner_self fun ψ => ?_⟩
    rw [hC' ψ, hC, H.inner_integral hf (H.mem_domain_of_bounded hb ψ)]
  · rw [← H.integral_mul_bounded hf hg hfb hgb, ← H.integral_mul_bounded hg hf hgb hfb, mul_comm]
end YangMills.Construction.JointSpectrum.BorelCalculus
