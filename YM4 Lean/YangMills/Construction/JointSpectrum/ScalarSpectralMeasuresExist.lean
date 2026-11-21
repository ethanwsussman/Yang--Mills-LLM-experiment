import YangMills.Construction.JointSpectrum.BorelFunctionalCalculusOfPolynomials
import Mathlib
set_option autoImplicit false
open YangMills.Construction.JointSpectrum MeasureTheory YangMills.Construction.FamilyPolynomials Set Filter Topology
open scoped ENNReal ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ScalarSpectralMeasures
section Functions
variable {J : Type} [Fintype J]
private lemma continuous_spectralMonomial (n : ℕ) (y : J → ℤ) :
    Continuous (spectralMonomial n y : SpectralDomain J → ℂ) := by apply _root_.YangMills.Construction.LatticeConventions.DirectionPairsSupport.continuous_spectralMonomial <;> assumption
private lemma spectralMonomial_mem (n : ℕ) (y : J → ℤ) :
    spectralMonomial n y ∈ spectralPolynomials J :=
  ⟨{(n, y)}, fun _ => 1, fun p => by simp⟩
private lemma spectralSum_singleton (n : ℕ) (y : J → ℤ) :
    spectralSum {(n, y)} (fun _ => 1) = (spectralMonomial n y : SpectralDomain J → ℂ) := by
  funext p
  simp [spectralSum]
private lemma spectralMonomial_zero_zero :
    (spectralMonomial 0 0 : SpectralDomain J → ℂ) = 1 := by
  funext p
  simp [spectralMonomial, torusMonomial]
private lemma dense_spectralPolynomials
    (hadd : ∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
      q + q' ∈ spectralPolynomials J)
    (hsmul : ∀ (a : ℂ), ∀ q ∈ spectralPolynomials J, a • q ∈ spectralPolynomials J)
    (hmul : ∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
      q * q' ∈ spectralPolynomials J)
    (hconj : ∀ q ∈ spectralPolynomials J, (fun p => conj (q p)) ∈ spectralPolynomials J) :
    Dense {g : C(SpectralDomain J, ℂ) | (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J} := by
  have hone : (1 : SpectralDomain J → ℂ) ∈ spectralPolynomials J := by
    rw [← spectralMonomial_zero_zero]
    exact spectralMonomial_mem 0 0
  let A : StarSubalgebra ℂ C(SpectralDomain J, ℂ) :=
    { carrier := {g | (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J}
      mul_mem' := fun {a b} ha hb => hmul _ ha _ hb
      add_mem' := fun {a b} ha hb => hadd _ ha _ hb
      algebraMap_mem' := fun r => by
        have hr := hsmul r 1 hone
        have e : ((algebraMap ℂ C(SpectralDomain J, ℂ) r : C(SpectralDomain J, ℂ)) :
            SpectralDomain J → ℂ) = r • (1 : SpectralDomain J → ℂ) := by
          funext p
          simp [Algebra.algebraMap_eq_smul_one]
        show ((algebraMap ℂ C(SpectralDomain J, ℂ) r : C(SpectralDomain J, ℂ)) :
            SpectralDomain J → ℂ) ∈ spectralPolynomials J
        rw [e]
        exact hr
      star_mem' := fun {a} ha => hconj _ ha }
  have hsep : A.SeparatesPoints := by
    intro p p' hne
    by_cases h1 : p.1 = p'.1
    · have h2 : p.2 ≠ p'.2 := fun h2 => hne (Prod.ext h1 h2)
      obtain ⟨α, hα⟩ := Function.ne_iff.1 h2
      classical
      let g : C(SpectralDomain J, ℂ) :=
        ⟨spectralMonomial 0 (Pi.single α 1), continuous_spectralMonomial _ _⟩
      refine ⟨g, ⟨g, spectralMonomial_mem _ _, rfl⟩, ?_⟩
      intro e
      apply hα
      have e' : spectralMonomial 0 (Pi.single α 1) p = spectralMonomial 0 (Pi.single α 1) p' := e
      have key : ∀ z : J → Circle, torusMonomial z (Pi.single α 1) = (z α : ℂ) := by
        intro z
        unfold torusMonomial
        rw [Finset.prod_eq_single α]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · simp
      simp only [spectralMonomial, pow_zero, one_mul, key] at e'
      exact Circle.ext e'
    · let g : C(SpectralDomain J, ℂ) := ⟨spectralMonomial 1 0, continuous_spectralMonomial _ _⟩
      refine ⟨g, ⟨g, spectralMonomial_mem _ _, rfl⟩, ?_⟩
      intro e
      apply h1
      have e' : spectralMonomial 1 0 p = spectralMonomial 1 0 p' := e
      simp only [spectralMonomial, torusMonomial, pow_one, Pi.zero_apply, zpow_zero,
        Finset.prod_const_one, mul_one] at e'
      exact Subtype.ext (by exact_mod_cast e')
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hc : closure (A : Set C(SpectralDomain J, ℂ)) = univ := by
    have := congrArg (fun B : StarSubalgebra ℂ C(SpectralDomain J, ℂ) =>
      (B : Set C(SpectralDomain J, ℂ))) htop
    simpa using this
  exact dense_iff_closure_eq.2 hc
omit [Fintype J] in
private lemma sqNormLIntegral_eq_eLpNorm_sq (ρ : Measure (SpectralDomain J))
    (f : SpectralDomain J → ℂ) : sqNormLIntegral ρ f = eLpNorm f 2 ρ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := ρ) (f := f) (p := (2 : NNReal)) two_ne_zero
  simpa [sqNormLIntegral, ENNReal.rpow_two] using h.symm
private lemma exists_polynomial_eLpNorm_sub_le
    (hd : Dense {g : C(SpectralDomain J, ℂ) | (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J})
    (ρ : Measure (SpectralDomain J)) [IsFiniteMeasure ρ] {f : SpectralDomain J → ℂ}
    (hf : Measurable f) (hfin : sqNormLIntegral ρ f < ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ spectralPolynomials J, eLpNorm (f - q) 2 ρ ≤ ENNReal.ofReal ε := by
  have hmem : MemLp f 2 ρ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    have hsq : eLpNorm f 2 ρ ^ 2 < ∞ := by rwa [← sqNormLIntegral_eq_eLpNorm_sq]
    exact (ENNReal.pow_lt_top_iff.1 hsq).resolve_right two_ne_zero
  have hhalf : ENNReal.ofReal (ε / 2) ≠ 0 := by simpa using half_pos hε
  obtain ⟨g, hg, -⟩ := hmem.exists_boundedContinuous_eLpNorm_sub_le (by norm_num) hhalf
  set M : ℝ≥0∞ := ρ univ ^ (2 : ℝ≥0∞).toReal⁻¹ with hM
  have hMtop : M ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top ρ univ)
  have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  set δ : ℝ := ε / 2 / (M.toReal + 1) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨q, hq, hdist⟩ := hd.exists_dist_lt g.toContinuousMap hδ
  refine ⟨q, hq, ?_⟩
  have hbound : eLpNorm ((g : SpectralDomain J → ℂ) - (q : SpectralDomain J → ℂ)) 2 ρ ≤
      ENNReal.ofReal (ε / 2) := by
    have h1 : ∀ᵐ p ∂ρ, ‖((g : SpectralDomain J → ℂ) - (q : SpectralDomain J → ℂ)) p‖ ≤ δ :=
      Eventually.of_forall fun p => by
        have h2 := ContinuousMap.dist_apply_le_dist (f := g.toContinuousMap) (g := q) p
        rw [dist_eq_norm] at h2
        exact h2.trans hdist.le
    refine (eLpNorm_le_of_ae_bound h1).trans ?_
    calc ρ univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal δ
        = ENNReal.ofReal M.toReal * ENNReal.ofReal δ := by
          rw [ENNReal.ofReal_toReal hMtop]
      _ = ENNReal.ofReal (M.toReal * δ) := (ENNReal.ofReal_mul hM0).symm
      _ ≤ ENNReal.ofReal (ε / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 : M.toReal * δ = ε / 2 * (M.toReal / (M.toReal + 1)) := by
            rw [hδdef]; ring
          have h4 : M.toReal / (M.toReal + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          rw [h3]
          nlinarith [half_pos hε]
  have hgm : AEStronglyMeasurable (g : SpectralDomain J → ℂ) ρ :=
    g.continuous.aestronglyMeasurable
  have hqm : AEStronglyMeasurable (q : SpectralDomain J → ℂ) ρ :=
    q.continuous.aestronglyMeasurable
  calc eLpNorm (f - (q : SpectralDomain J → ℂ)) 2 ρ
      = eLpNorm ((f - (g : SpectralDomain J → ℂ)) +
          ((g : SpectralDomain J → ℂ) - (q : SpectralDomain J → ℂ))) 2 ρ := by
        congr 1
        funext p
        simp
    _ ≤ eLpNorm (f - (g : SpectralDomain J → ℂ)) 2 ρ +
        eLpNorm ((g : SpectralDomain J → ℂ) - (q : SpectralDomain J → ℂ)) 2 ρ :=
        eLpNorm_add_le (hf.aestronglyMeasurable.sub hgm) (hgm.sub hqm) (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hg hbound
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
        congr 1
        ring
private lemma exists_polynomial_approximation
    (hd : Dense {g : C(SpectralDomain J, ℂ) | (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J})
    (ρ : Measure (SpectralDomain J)) [IsFiniteMeasure ρ] (f : SpectralDomain J → ℂ)
    (hf : Measurable f) (hfin : sqNormLIntegral ρ f < ∞) :
    ∃ q : ℕ → SpectralDomain J → ℂ, (∀ l, q l ∈ spectralPolynomials J) ∧
      Tendsto (fun l => sqNormLIntegral ρ (f - q l)) atTop (𝓝 0) := by
  have hstep : ∀ l : ℕ, ∃ q ∈ spectralPolynomials J,
      eLpNorm (f - q) 2 ρ ≤ ENNReal.ofReal (1 / ((l : ℝ) + 1)) := fun l =>
    exists_polynomial_eLpNorm_sub_le hd ρ hf hfin (by positivity)
  choose q hq hle using hstep
  refine ⟨q, hq, ?_⟩
  have h0 : Tendsto (fun l : ℕ => ENNReal.ofReal (1 / ((l : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  have h1 : Tendsto (fun l => eLpNorm (f - q l) 2 ρ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hle
  have h2 := ((ENNReal.continuous_pow 2).tendsto 0).comp h1
  simpa [Function.comp_def, sqNormLIntegral_eq_eLpNorm_sq] using h2
private lemma integrable_of_continuous_on_domain (ρ : Measure (SpectralDomain J))
    [IsFiniteMeasure ρ] {g : SpectralDomain J → ℂ} (hg : Continuous g) : Integrable g ρ :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
private lemma integral_spectralSum (ρ : Measure (SpectralDomain J)) [IsFiniteMeasure ρ]
    (s : Finset (ℕ × (J → ℤ))) (c : ℕ × (J → ℤ) → ℂ) :
    ∫ p, spectralSum s c p ∂ρ = ∑ i ∈ s, c i * ∫ p, spectralMonomial i.1 i.2 p ∂ρ := by
  have h := integral_finsetSum (μ := ρ) s (f := fun i p => c i * spectralMonomial i.1 i.2 p)
    fun i _ => integrable_of_continuous_on_domain ρ
      (continuous_const.mul (continuous_spectralMonomial _ _))
  unfold spectralSum
  rw [h]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
private def integralFunctionalOf (ρ : Measure (SpectralDomain J)) [IsFiniteMeasure ρ] :
    C(SpectralDomain J, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ p, g p ∂ρ
      map_add' := fun g g' =>
        integral_add (integrable_of_continuous_on_domain ρ g.continuous)
          (integrable_of_continuous_on_domain ρ g'.continuous)
      map_smul' := fun a g => integral_const_mul a _ }
    (ρ.real univ) fun g => by
      have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := g) (C := ‖g‖)
        (Eventually.of_forall g.norm_coe_le_norm)
      simpa [mul_comm] using h
private lemma eq_of_spectralMoments
    (hd : Dense {g : C(SpectralDomain J, ℂ) | (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J})
    (ρ ρ' : Measure (SpectralDomain J)) [IsFiniteMeasure ρ] [IsFiniteMeasure ρ']
    (h : ∀ (n : ℕ) (y : J → ℤ),
      ∫ p, spectralMonomial n y p ∂ρ = ∫ p, spectralMonomial n y p ∂ρ') : ρ = ρ' := by
  have hc : (integralFunctionalOf ρ : C(SpectralDomain J, ℂ) → ℂ) = integralFunctionalOf ρ' := by
    refine Continuous.ext_on hd (integralFunctionalOf ρ).continuous
      (integralFunctionalOf ρ').continuous ?_
    intro g hg
    obtain ⟨s, c, hsc⟩ := hg
    have hgs : (g : SpectralDomain J → ℂ) = spectralSum s c := funext hsc
    show ∫ p, g p ∂ρ = ∫ p, g p ∂ρ'
    simp only [hgs, integral_spectralSum, h]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun u => ?_
  have h1 := congrFun hc ⟨fun p => (u p : ℂ), by fun_prop⟩
  have h2 : ((∫ p, u p ∂ρ : ℝ) : ℂ) = ((∫ p, u p ∂ρ' : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    exact h1
  exact_mod_cast h2
end Functions
section Operators
variable {𝒦 : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {J : Type} [Fintype J] [Nonempty J]
private lemma dense_of_family (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) :
    Dense {g : C(SpectralDomain J, ℂ) | (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J} := by
  obtain ⟨-, -, -, -, hadd, hsmul, hmul, hconj, -⟩ := h 𝒦 J S
  exact dense_spectralPolynomials hadd hsmul hmul hconj
private lemma polynomialCalculus_spectralMonomial (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) (n : ℕ) (y : J → ℤ) :
    polynomialCalculus S (spectralMonomial n y) = familyMonomial S n y := by
  obtain ⟨-, -, hop, -⟩ := h 𝒦 J S
  have h1 := hop {(n, y)} (fun _ => 1)
  rw [spectralSum_singleton] at h1
  rw [h1]
  simp [familySum]
private lemma familyMonomial_zero_zero (S : CommutingFamily 𝒦 J) : familyMonomial S 0 0 = 1 := by
  have h2 := Finset.noncommProd_eq_pow_card (Finset.univ : Finset J)
    (fun α => S.B α ^ (0 : J → ℤ) α) (fun α _ α' _ _ => S.commute_zpow_unitary 0 α α') 1
    (fun α _ => by simp)
  have h1 : S.unitaryMonomial 0 = 1 := by
    unfold CommutingFamily.unitaryMonomial
    exact (congrArg Subtype.val h2).trans (by simp)
  simp [familyMonomial, h1]
private lemma exists_clm_extension {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : Submodule ℂ E) (hd : Dense (Q : Set E)) (Λ : Q →ₗ[ℂ] ℂ) (C : ℝ)
    (hb : ∀ g : Q, ‖Λ g‖ ≤ C * ‖(g : E)‖) : ∃ L : E →L[ℂ] ℂ, ∀ g : Q, L g = Λ g :=
  ⟨LinearMap.extendOfNorm (E := Q) (𝕜 := ℂ) (𝕜₂ := ℂ) (σ₁₂ := RingHom.id ℂ) Λ Q.subtype,
    fun g => LinearMap.extendOfNorm_eq (f := Λ) (e := Q.subtype) hd.denseRange_val ⟨C, hb⟩ g⟩
private lemma exists_momentFunctional (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) (ψ : 𝒦) :
    ∃ L : C(SpectralDomain J, ℂ) →L[ℂ] ℂ,
      ∀ g : C(SpectralDomain J, ℂ), (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J →
        L g = inner ℂ ψ (polynomialCalculus S g ψ) := by
  obtain ⟨-, -, -, h0, hadd, hsmul, -, -, hopadd, hopsmul, -, -, -, hnorm⟩ := h 𝒦 J S
  let Q : Submodule ℂ C(SpectralDomain J, ℂ) :=
    { carrier := {g | (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J}
      add_mem' := fun {a b} ha hb => hadd _ ha _ hb
      zero_mem' := h0
      smul_mem' := fun c g hg => hsmul c _ hg }
  let Λ : Q →ₗ[ℂ] ℂ :=
    { toFun := fun g => inner ℂ ψ (polynomialCalculus S (g : C(SpectralDomain J, ℂ)) ψ)
      map_add' := fun a b => by
        show inner ℂ ψ (polynomialCalculus S
          (((a : C(SpectralDomain J, ℂ)) : SpectralDomain J → ℂ) +
            ((b : C(SpectralDomain J, ℂ)) : SpectralDomain J → ℂ)) ψ) = _
        rw [hopadd _ a.2 _ b.2]
        simp
      map_smul' := fun c a => by
        show inner ℂ ψ (polynomialCalculus S
          (c • ((a : C(SpectralDomain J, ℂ)) : SpectralDomain J → ℂ)) ψ) = _
        rw [hopsmul _ _ a.2]
        simp }
  have hbound : ∀ g : Q, ‖Λ g‖ ≤ ‖ψ‖ ^ 2 * ‖(g : C(SpectralDomain J, ℂ))‖ := by
    intro g
    have h1 : ‖polynomialCalculus S (g : C(SpectralDomain J, ℂ))‖ ≤
        ‖(g : C(SpectralDomain J, ℂ))‖ :=
      (hnorm _ g.2).trans (ciSup_le fun p => ContinuousMap.norm_coe_le_norm _ p)
    calc ‖Λ g‖ ≤ ‖ψ‖ * ‖polynomialCalculus S (g : C(SpectralDomain J, ℂ)) ψ‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * (‖polynomialCalculus S (g : C(SpectralDomain J, ℂ))‖ * ‖ψ‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖ψ‖ * (‖(g : C(SpectralDomain J, ℂ))‖ * ‖ψ‖) := by gcongr
      _ = ‖ψ‖ ^ 2 * ‖(g : C(SpectralDomain J, ℂ))‖ := by ring
  obtain ⟨L, hL⟩ := exists_clm_extension Q (dense_of_family h S) Λ _ hbound
  exact ⟨L, fun g hg => hL ⟨g, hg⟩⟩
private lemma momentFunctional_star (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) (ψ : 𝒦) (L : C(SpectralDomain J, ℂ) →L[ℂ] ℂ)
    (hL : ∀ g : C(SpectralDomain J, ℂ), (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J →
      L g = inner ℂ ψ (polynomialCalculus S g ψ)) (g : C(SpectralDomain J, ℂ)) :
    L (star g) = conj (L g) := by
  obtain ⟨-, -, -, -, -, -, -, hconj, -, -, -, hopconj, -⟩ := h 𝒦 J S
  have e : (fun g => L (star g)) = fun g => conj (L g) := by
    refine Continuous.ext_on (dense_of_family h S) (L.continuous.comp continuous_star)
      (Complex.continuous_conj.comp L.continuous) ?_
    intro g hg
    have hs : ((star g : C(SpectralDomain J, ℂ)) : SpectralDomain J → ℂ) =
        fun p => conj (g p) := rfl
    have h1 : L (star g) = inner ℂ ψ (star (polynomialCalculus S g) ψ) := by
      rw [hL _ (by rw [hs]; exact hconj _ hg), hs, hopconj _ hg]
    show L (star g) = conj (L g)
    rw [h1, hL g hg, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
  exact congrFun e g
private def complexOfReal (u : C(SpectralDomain J, ℝ)) : C(SpectralDomain J, ℂ) :=
  ⟨fun p => (u p : ℂ), by fun_prop⟩
private lemma momentFunctional_re_nonneg (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) (ψ : 𝒦) (L : C(SpectralDomain J, ℂ) →L[ℂ] ℂ)
    (hL : ∀ g : C(SpectralDomain J, ℂ), (g : SpectralDomain J → ℂ) ∈ spectralPolynomials J →
      L g = inner ℂ ψ (polynomialCalculus S g ψ))
    (u : C(SpectralDomain J, ℝ)) (hu : ∀ p, 0 ≤ u p) : 0 ≤ (L (complexOfReal u)).re := by
  obtain ⟨-, -, -, -, hadd, hsmul, -, hconj, -, -, -, -, hpos, -⟩ := h 𝒦 J S
  have hd := dense_of_family h S
  have hone : (1 : SpectralDomain J → ℂ) ∈ spectralPolynomials J := by
    rw [← spectralMonomial_zero_zero]
    exact spectralMonomial_mem 0 0
  have key : ∀ ε : ℝ, 0 < ε → -(‖L‖ * (2 * ε)) ≤ (L (complexOfReal u)).re := by
    intro ε hε
    obtain ⟨q, hq, hdist⟩ := hd.exists_dist_lt (complexOfReal u) hε
    let r : C(SpectralDomain J, ℂ) := (1 / 2 : ℂ) • (q + star q) + (ε : ℂ) • 1
    have hr : (r : SpectralDomain J → ℂ) ∈ spectralPolynomials J :=
      hadd _ (hsmul _ _ (hadd _ hq _ (hconj _ hq))) _ (hsmul _ _ hone)
    have hrval : ∀ p, r p = (((q p).re + ε : ℝ) : ℂ) := by
      intro p
      have e : r p = (1 / 2 : ℂ) * (q p + conj (q p)) + (ε : ℂ) := by
        simp [r]
      rw [e, Complex.add_conj]
      push_cast
      ring
    have hclose : ∀ p, |u p - (q p).re| < ε := by
      intro p
      have h1 := ContinuousMap.dist_apply_le_dist (f := complexOfReal u) (g := q) p
      rw [dist_eq_norm] at h1
      have h2 := Complex.abs_re_le_norm (complexOfReal u p - q p)
      have e : (complexOfReal u p - q p).re = u p - (q p).re := by
        simp [complexOfReal]
      rw [e] at h2
      exact (h2.trans h1).trans_lt hdist
    have hrpos : ∀ p, 0 ≤ (r : SpectralDomain J → ℂ) p := by
      intro p
      rw [hrval]
      have h1 := abs_lt.1 (hclose p)
      have h2 := hu p
      exact Complex.zero_le_real.2 (by linarith [h1.2])
    have hop0 : 0 ≤ polynomialCalculus S r := hpos _ hr hrpos
    have hin : 0 ≤ (L r).re := by
      rw [hL r hr]
      have h1 := ((ContinuousLinearMap.nonneg_iff_isPositive _).1 hop0).re_inner_nonneg_right ψ
      simpa using h1
    have hnorm : ‖complexOfReal u - r‖ ≤ 2 * ε := by
      rw [ContinuousMap.norm_le _ (by positivity)]
      intro p
      show ‖complexOfReal u p - r p‖ ≤ 2 * ε
      rw [hrval]
      have e : complexOfReal u p - (((q p).re + ε : ℝ) : ℂ) = ((u p - (q p).re - ε : ℝ) : ℂ) := by
        simp [complexOfReal]
        ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      have h1 := abs_lt.1 (hclose p)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    have h1 : ‖L (complexOfReal u) - L r‖ ≤ ‖L‖ * (2 * ε) := by
      rw [← map_sub]
      exact (L.le_opNorm _).trans (by gcongr)
    have h2 := Complex.abs_re_le_norm (L (complexOfReal u) - L r)
    rw [Complex.sub_re] at h2
    have h3 := abs_le.1 (h2.trans h1)
    linarith [h3.1]
  refine le_of_forall_pos_le_add fun e he => ?_
  have h1 := key (e / (2 * (‖L‖ + 1))) (by positivity)
  have h3 : ‖L‖ * (2 * (e / (2 * (‖L‖ + 1)))) ≤ e := by
    have h4 : ‖L‖ * (2 * (e / (2 * (‖L‖ + 1)))) = e * (‖L‖ / (‖L‖ + 1)) := by
      field_simp
    have h5 : ‖L‖ / (‖L‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    rw [h4]
    nlinarith
  linarith
private lemma exists_isSpectralMeasureOf (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) (ψ : 𝒦) : ∃ ρ, IsSpectralMeasureOf S ψ ρ := by
  obtain ⟨L, hL⟩ := exists_momentFunctional h S ψ
  let Λ₀ : CompactlySupportedContinuousMap (SpectralDomain J) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun u => (L (complexOfReal (u : C(SpectralDomain J, ℝ)))).re
      map_add' := fun u v => by
        have e : complexOfReal ((u + v : CompactlySupportedContinuousMap _ ℝ) :
            C(SpectralDomain J, ℝ)) = complexOfReal (u : C(SpectralDomain J, ℝ)) +
              complexOfReal (v : C(SpectralDomain J, ℝ)) := by
          ext p
          simp [complexOfReal]
        rw [e, map_add, Complex.add_re]
      map_smul' := fun a u => by
        have e : complexOfReal ((a • u : CompactlySupportedContinuousMap _ ℝ) :
            C(SpectralDomain J, ℝ)) =
              (a : ℂ) • complexOfReal (u : C(SpectralDomain J, ℝ)) := by
          ext p
          simp [complexOfReal]
        rw [e, map_smul]
        simp }
  let Λ := PositiveLinearMap.mk₀ Λ₀ fun u hu =>
    momentFunctional_re_nonneg h S ψ L hL (u : C(SpectralDomain J, ℝ))
      (CompactlySupportedContinuousMap.le_def.1 hu)
  let m := RealRMK.rieszMeasure Λ
  have hreal : ∀ u : C(SpectralDomain J, ℝ),
      L (complexOfReal u) = ((∫ p, u p ∂m : ℝ) : ℂ) := by
    intro u
    have h1 : ∫ p, u p ∂m = (L (complexOfReal u)).re :=
      RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv u)
    have h2 : conj (L (complexOfReal u)) = L (complexOfReal u) := by
      rw [← momentFunctional_star h S ψ L hL]
      congr 1
      ext p
      simp [complexOfReal]
    rw [h1]
    exact (Complex.conj_eq_iff_re.1 h2).symm
  have hall : ∀ g : C(SpectralDomain J, ℂ), L g = ∫ p, g p ∂m := by
    intro g
    let u : C(SpectralDomain J, ℝ) := ⟨fun p => (g p).re, by fun_prop⟩
    let v : C(SpectralDomain J, ℝ) := ⟨fun p => (g p).im, by fun_prop⟩
    have hg : g = complexOfReal u + Complex.I • complexOfReal v := by
      ext p
      simp [complexOfReal, u, v, mul_comm Complex.I]
    have hint := integral_re_add_im (𝕜 := ℂ) (integrable_of_continuous_on_domain m g.continuous)
    rw [← hint]
    conv_lhs => rw [hg]
    rw [map_add, map_smul, hreal u, hreal v]
    simp [u, v, mul_comm Complex.I]
  refine ⟨m, inferInstance, fun n y => ?_⟩
  have h1 := hL ⟨spectralMonomial n y, continuous_spectralMonomial n y⟩ (spectralMonomial_mem n y)
  rw [hall] at h1
  have h2 : inner ℂ ψ (polynomialCalculus S (spectralMonomial n y) ψ) =
      ∫ p, spectralMonomial n y p ∂m := h1.symm
  rwa [polynomialCalculus_spectralMonomial h S] at h2
private lemma spectralMeasure_spec (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) (ψ : 𝒦) : IsSpectralMeasureOf S ψ (spectralMeasure S ψ) :=
  Classical.epsilon_spec (exists_isSpectralMeasureOf h S ψ)
private lemma inner_polynomialCalculus (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) {ψ : 𝒦} {ρ : Measure (SpectralDomain J)}
    (hρ : IsSpectralMeasureOf S ψ ρ) {q : SpectralDomain J → ℂ} (hq : q ∈ spectralPolynomials J) :
    inner ℂ ψ (polynomialCalculus S q ψ) = ∫ p, q p ∂ρ := by
  obtain ⟨-, -, hop, -⟩ := h 𝒦 J S
  have := hρ.1
  obtain ⟨s, c, hsc⟩ := hq
  have hq' : q = spectralSum s c := funext hsc
  rw [hq', hop, integral_spectralSum]
  simp only [familySum, sum_apply, smul_apply, inner_sum, inner_smul_right]
  exact Finset.sum_congr rfl fun i _ => by rw [hρ.2]
omit [Nonempty J] in
private lemma continuous_of_mem_spectralPolynomials {q : SpectralDomain J → ℂ}
    (hq : q ∈ spectralPolynomials J) : Continuous q := by apply _root_.YangMills.SharedProofs.p14551 <;> assumption
private lemma enorm_polynomialCalculus_sq (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) {ψ : 𝒦} {ρ : Measure (SpectralDomain J)}
    (hρ : IsSpectralMeasureOf S ψ ρ) {q : SpectralDomain J → ℂ} (hq : q ∈ spectralPolynomials J) :
    ‖polynomialCalculus S q ψ‖ₑ ^ 2 = sqNormLIntegral ρ q := by
  obtain ⟨-, -, -, -, -, -, hmul, hconj, -, -, hopmul, hopconj, -⟩ := h 𝒦 J S
  have := hρ.1
  have hcont := continuous_of_mem_spectralPolynomials hq
  have h1 := inner_polynomialCalculus h S hρ (hmul _ (hconj _ hq) _ hq)
  rw [hopmul _ (hconj _ hq) _ hq, hopconj _ hq] at h1
  have h2 : inner ℂ ψ ((star (polynomialCalculus S q) * polynomialCalculus S q) ψ) =
      ((‖polynomialCalculus S q ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [show (star (polynomialCalculus S q) * polynomialCalculus S q) ψ =
        star (polynomialCalculus S q) (polynomialCalculus S q ψ) from rfl,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    simp
  have h3 : ∫ p, ((fun p => conj (q p)) * q) p ∂ρ = ((∫ p, ‖q p‖ ^ 2 ∂ρ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext p
    simp [Complex.conj_mul']
  have h4 : ‖polynomialCalculus S q ψ‖ ^ 2 = ∫ p, ‖q p‖ ^ 2 ∂ρ := by
    exact_mod_cast (h2.symm.trans h1).trans h3
  have hcn : Continuous fun p => ‖q p‖ ^ 2 := by fun_prop
  have h5 := ofReal_integral_eq_lintegral_ofReal (μ := ρ) (f := fun p => ‖q p‖ ^ 2)
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Eventually.of_forall fun p => by positivity)
  have h6 : ∀ {E : Type} [NormedAddCommGroup E] (z : E), ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
    intro E _ z
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  unfold sqNormLIntegral
  rw [h6, h4, h5]
  simp_rw [h6]
private lemma l2Calculus_spec (h : PolynomialCalculusStatement)
    (S : CommutingFamily 𝒦 J) (ψ : 𝒦) (f : SpectralDomain J → ℂ) (hf : Measurable f)
    (hfin : sqNormLIntegral (spectralMeasure S ψ) f < ∞) :
    IsL2CalculusLimit S ψ f (l2Calculus S ψ f) ∧
      (∀ v, IsL2CalculusLimit S ψ f v → v = l2Calculus S ψ f) ∧
      (∃ q, PolynomialL2Approximation S ψ f q) ∧
      ‖l2Calculus S ψ f‖ₑ ^ 2 = sqNormLIntegral (spectralMeasure S ψ) f := by
  obtain ⟨-, -, -, -, hadd, hsmul, -, -, hopadd, hopsmul, -⟩ := h 𝒦 J S
  have hspec := spectralMeasure_spec h S ψ
  have := hspec.1
  have hen : ∀ q ∈ spectralPolynomials J,
      ‖polynomialCalculus S q ψ‖ₑ = eLpNorm q 2 (spectralMeasure S ψ) := by
    intro q hq
    have h1 := enorm_polynomialCalculus_sq h S hspec hq
    rw [sqNormLIntegral_eq_eLpNorm_sq] at h1
    exact (ENNReal.pow_right_strictMono two_ne_zero).injective h1
  have hmeas : ∀ q ∈ spectralPolynomials J, AEStronglyMeasurable q (spectralMeasure S ψ) :=
    fun q hq => (continuous_of_mem_spectralPolynomials hq).aestronglyMeasurable
  have hfm : AEStronglyMeasurable f (spectralMeasure S ψ) := hf.aestronglyMeasurable
  have hdiff : ∀ q ∈ spectralPolynomials J, ∀ q' ∈ spectralPolynomials J,
      edist (polynomialCalculus S q ψ) (polynomialCalculus S q' ψ) ≤
        eLpNorm (f - q) 2 (spectralMeasure S ψ) + eLpNorm (f - q') 2 (spectralMeasure S ψ) := by
    intro q hq q' hq'
    have hneg := hsmul (-1) q' hq'
    have e1 : polynomialCalculus S q ψ - polynomialCalculus S q' ψ =
        polynomialCalculus S (q + (-1 : ℂ) • q') ψ := by
      rw [hopadd _ hq _ hneg, hopsmul _ _ hq']
      simp [sub_eq_add_neg]
    rw [edist_eq_enorm_sub, e1, hen _ (hadd _ hq _ hneg)]
    have e2 : q + (-1 : ℂ) • q' = (f - q') - (f - q) := by
      funext p
      simp
      ring
    rw [e2, add_comm]
    exact eLpNorm_sub_le (hfm.sub (hmeas _ hq')) (hfm.sub (hmeas _ hq)) (by norm_num)
  have htend : ∀ q, PolynomialL2Approximation S ψ f q →
      Tendsto (fun l => eLpNorm (f - q l) 2 (spectralMeasure S ψ)) atTop (𝓝 0) := by
    intro q hq
    have h1 := ((ENNReal.continuous_rpow_const (y := ((2 : ℕ) : ℝ)⁻¹)).tendsto 0).comp hq.2
    have h0 : (0 : ℝ≥0∞) ^ ((2 : ℕ) : ℝ)⁻¹ = 0 := ENNReal.zero_rpow_of_pos (by positivity)
    rw [h0] at h1
    refine h1.congr fun l => ?_
    show sqNormLIntegral (spectralMeasure S ψ) (f - q l) ^ ((2 : ℕ) : ℝ)⁻¹ = _
    rw [sqNormLIntegral_eq_eLpNorm_sq, ENNReal.pow_rpow_inv_natCast two_ne_zero]
  obtain ⟨q₀, hq₀, hq₀t⟩ :=
    exists_polynomial_approximation (dense_of_family h S) (spectralMeasure S ψ) f hf hfin
  have happ : PolynomialL2Approximation S ψ f q₀ := ⟨hq₀, hq₀t⟩
  have he₀ := htend q₀ happ
  have hcauchy : CauchySeq fun l => polynomialCalculus S (q₀ l) ψ := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 he₀).2 _ hε2)
    refine ⟨N, fun a ha b hb => ?_⟩
    calc edist (polynomialCalculus S (q₀ a) ψ) (polynomialCalculus S (q₀ b) ψ)
        ≤ eLpNorm (f - q₀ a) 2 (spectralMeasure S ψ) +
            eLpNorm (f - q₀ b) 2 (spectralMeasure S ψ) :=
          hdiff _ (hq₀ a) _ (hq₀ b)
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hN a ha) (hN b hb)
      _ = ε := ENNReal.add_halves ε
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : IsL2CalculusLimit S ψ f v := by
    intro q hq
    rw [tendsto_iff_edist_tendsto_0]
    have hv0 := tendsto_iff_edist_tendsto_0.1 hv
    have hsum : Tendsto (fun l => eLpNorm (f - q l) 2 (spectralMeasure S ψ) +
        eLpNorm (f - q₀ l) 2 (spectralMeasure S ψ) +
          edist (polynomialCalculus S (q₀ l) ψ) v) atTop (𝓝 0) := by
      simpa using ((htend q hq).add he₀).add hv0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) fun l => ?_
    exact (edist_triangle _ _ _).trans (add_le_add (hdiff _ (hq.1 l) _ (hq₀ l)) le_rfl)
  have hspecv : IsL2CalculusLimit S ψ f (l2Calculus S ψ f) := Classical.epsilon_spec ⟨v, hlim⟩
  have huniq : ∀ w, IsL2CalculusLimit S ψ f w → w = l2Calculus S ψ f := fun w hw =>
    tendsto_nhds_unique (hw q₀ happ) (hspecv q₀ happ)
  refine ⟨hspecv, huniq, ⟨q₀, happ⟩, ?_⟩
  have hvt := hspecv q₀ happ
  rw [sqNormLIntegral_eq_eLpNorm_sq]
  congr 1
  have hnt : Tendsto (fun l => eLpNorm (q₀ l) 2 (spectralMeasure S ψ)) atTop
      (𝓝 ‖l2Calculus S ψ f‖ₑ) := by
    have h1 := (continuous_enorm.tendsto (l2Calculus S ψ f)).comp hvt
    exact h1.congr fun l => hen _ (hq₀ l)
  apply le_antisymm
  · have hup : Tendsto (fun l => eLpNorm f 2 (spectralMeasure S ψ) +
        eLpNorm (f - q₀ l) 2 (spectralMeasure S ψ)) atTop
        (𝓝 (eLpNorm f 2 (spectralMeasure S ψ))) := by
      simpa using (tendsto_const_nhds (x := eLpNorm f 2 (spectralMeasure S ψ))).add he₀
    refine le_of_tendsto_of_tendsto hnt hup (Eventually.of_forall fun l => ?_)
    have e : q₀ l = f - (f - q₀ l) := by
      funext p
      simp
    calc eLpNorm (q₀ l) 2 (spectralMeasure S ψ)
        = eLpNorm (f - (f - q₀ l)) 2 (spectralMeasure S ψ) := by rw [← e]
      _ ≤ _ := eLpNorm_sub_le hfm (hfm.sub (hmeas _ (hq₀ l))) (by norm_num)
  · have hup : Tendsto (fun l => eLpNorm (q₀ l) 2 (spectralMeasure S ψ) +
        eLpNorm (f - q₀ l) 2 (spectralMeasure S ψ)) atTop (𝓝 ‖l2Calculus S ψ f‖ₑ) := by
      simpa using hnt.add he₀
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hup (Eventually.of_forall fun l => ?_)
    have e : f = q₀ l + (f - q₀ l) := by
      funext p
      simp
    calc eLpNorm f 2 (spectralMeasure S ψ)
        = eLpNorm (q₀ l + (f - q₀ l)) 2 (spectralMeasure S ψ) := by rw [← e]
      _ ≤ _ := eLpNorm_add_le (hmeas _ (hq₀ l)) (hfm.sub (hmeas _ (hq₀ l))) (by norm_num)
end Operators
theorem scalarSpectralMeasuresStatement_holds (h : PolynomialCalculusStatement) :
    ScalarSpectralMeasuresStatement := by
  intro 𝒦 _ _ _ J _ _ S
  have hd := dense_of_family h S
  have hspec := spectralMeasure_spec h S
  have huniq : ∀ (ψ : 𝒦) (ρ : Measure (SpectralDomain J)), IsSpectralMeasureOf S ψ ρ →
      ρ = spectralMeasure S ψ := by
    intro ψ ρ hρ
    have := hρ.1
    have := (hspec ψ).1
    refine eq_of_spectralMoments hd ρ _ fun n y => ?_
    rw [← hρ.2, ← (hspec ψ).2]
  have hpar : ∀ ψ ψ' : 𝒦,
      spectralMeasure S (ψ + ψ') + spectralMeasure S (ψ - ψ') =
        (2 : ℝ≥0∞) • spectralMeasure S ψ + (2 : ℝ≥0∞) • spectralMeasure S ψ' := by
    intro ψ ψ'
    have := (hspec ψ).1
    have := (hspec ψ').1
    have := (hspec (ψ + ψ')).1
    have := (hspec (ψ - ψ')).1
    have : IsFiniteMeasure ((2 : ℝ≥0∞) • spectralMeasure S ψ) :=
      Measure.smul_finite _ (by simp)
    have : IsFiniteMeasure ((2 : ℝ≥0∞) • spectralMeasure S ψ') :=
      Measure.smul_finite _ (by simp)
    refine eq_of_spectralMoments hd _ _ fun n y => ?_
    have hc := continuous_spectralMonomial (J := J) n y
    rw [integral_add_measure (integrable_of_continuous_on_domain _ hc)
        (integrable_of_continuous_on_domain _ hc),
      integral_add_measure (integrable_of_continuous_on_domain _ hc)
        (integrable_of_continuous_on_domain _ hc),
      integral_smul_measure, integral_smul_measure, ← (hspec ψ).2, ← (hspec ψ').2,
      ← (hspec (ψ + ψ')).2, ← (hspec (ψ - ψ')).2]
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    simp only [ENNReal.toReal_ofNat, Complex.real_smul]
    push_cast
    ring
  refine ⟨hd, fun ρ _ f hf hfin => exists_polynomial_approximation hd ρ f hf hfin,
    fun ρ ρ' _ _ hmom => eq_of_spectralMoments hd ρ ρ' hmom, fun ψ => ⟨hspec ψ, huniq ψ, ?_,
      fun q hq => ⟨inner_polynomialCalculus h S (hspec ψ) hq,
        enorm_polynomialCalculus_sq h S (hspec ψ) hq⟩⟩,
    fun c ψ => ?_, hpar, fun ψ ψ' B _ => ?_, fun ψ f hf hfin => l2Calculus_spec h S ψ f hf hfin⟩
  · have hone : (1 : SpectralDomain J → ℂ) ∈ spectralPolynomials J := by
      rw [← spectralMonomial_zero_zero]
      exact spectralMonomial_mem 0 0
    have h1 := enorm_polynomialCalculus_sq h S (hspec ψ) hone
    rw [← spectralMonomial_zero_zero, polynomialCalculus_spectralMonomial h S,
      familyMonomial_zero_zero, spectralMonomial_zero_zero] at h1
    simpa [sqNormLIntegral] using h1.symm
  · have := (hspec ψ).1
    have hfin : (‖c‖ₑ ^ 2 : ℝ≥0∞) ≠ ∞ := ENNReal.pow_ne_top enorm_ne_top
    have : IsFiniteMeasure ((‖c‖ₑ ^ 2 : ℝ≥0∞) • spectralMeasure S ψ) := Measure.smul_finite _ hfin
    refine (huniq (c • ψ) _ ⟨inferInstance, fun n y => ?_⟩).symm
    rw [integral_smul_measure, ← (hspec ψ).2]
    have e : ((‖c‖ₑ ^ 2 : ℝ≥0∞)).toReal = ‖c‖ ^ 2 := by
      simp [ENNReal.toReal_pow]
    rw [e, Complex.real_smul, map_smul, inner_smul_left, inner_smul_right]
    push_cast
    rw [← Complex.conj_mul']
    ring
  · have h1 := congrArg (fun μ : Measure (SpectralDomain J) => μ B) (hpar ψ ψ')
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    exact le_self_add
end YangMills.Construction.ScalarSpectralMeasures
