import YangMills.Construction.Measures.MomentsDetermineSpaceAndMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Measures.MomentDetermination
section Lemmas
variable {ι Ω Ω' : Type}
  [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [TopologicalSpace Ω'] [CompactSpace Ω'] [MeasurableSpace Ω'] [BorelSpace Ω']
lemma integrable_of_continuousMap_compact (μ : Measure Ω) [IsFiniteMeasure μ] (f : C(Ω, ℝ)) :
    Integrable (fun x => f x) μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
omit [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] in
lemma listProd_map_apply (F : ι → C(Ω, ℝ)) (l : List ι) (x : Ω) :
    (l.map F).prod x = (l.map (fun i => F i x)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]
omit [CompactSpace Ω] [BorelSpace Ω] [CompactSpace Ω'] [BorelSpace Ω'] in
lemma integral_listProd_eq_of_moments (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (F : ι → C(Ω, ℝ)) (F' : ι → C(Ω', ℝ))
    (hmom : ∀ q : ℕ, 1 ≤ q → ∀ t : Fin q → ι,
      ∫ x, ∏ j, F (t j) x ∂μ = ∫ x, ∏ j, F' (t j) x ∂μ') (l : List ι) :
    ∫ x, (l.map F).prod x ∂μ = ∫ x, (l.map F').prod x ∂μ' := by
  cases l with
  | nil => simp
  | cons i l =>
    have hq := hmom (i :: l).length (by simp) (fun j => (i :: l)[j.1])
    simp only [listProd_map_apply]
    simp only [← Fin.prod_univ_fun_getElem]
    exact hq
lemma integral_aeval_mul_listProd_eq (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (F : ι → C(Ω, ℝ)) (F' : ι → C(Ω', ℝ))
    (hmom : ∀ q : ℕ, 1 ≤ q → ∀ t : Fin q → ι,
      ∫ x, ∏ j, F (t j) x ∂μ = ∫ x, ∏ j, F' (t j) x ∂μ')
    (P : MvPolynomial ι ℝ) (l : List ι) :
    ∫ x, (MvPolynomial.aeval F P * (l.map F).prod) x ∂μ =
      ∫ x, (MvPolynomial.aeval F' P * (l.map F').prod) x ∂μ' := by
  induction P using MvPolynomial.induction_on generalizing l with
  | C a =>
    have hl := integral_listProd_eq_of_moments μ μ' F F' hmom l
    simp only [MvPolynomial.aeval_C, ← Algebra.smul_def, ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, hl]
  | add P Q hP hQ =>
    have e : ∀ {Z : Type} [TopologicalSpace Z] (G : ι → C(Z, ℝ)),
        MvPolynomial.aeval G (P + Q) * (l.map G).prod =
          MvPolynomial.aeval G P * (l.map G).prod + MvPolynomial.aeval G Q * (l.map G).prod := by
      intro Z _ G
      rw [map_add, add_mul]
    rw [e F, e F']
    simp only [ContinuousMap.add_apply]
    rw [integral_add (integrable_of_continuousMap_compact μ _)
        (integrable_of_continuousMap_compact μ _),
      integral_add (integrable_of_continuousMap_compact μ' _)
        (integrable_of_continuousMap_compact μ' _), hP, hQ]
  | mul_X P i hP =>
    have e : ∀ {Z : Type} [TopologicalSpace Z] (G : ι → C(Z, ℝ)),
        MvPolynomial.aeval G (P * MvPolynomial.X i) * (l.map G).prod =
          MvPolynomial.aeval G P * ((i :: l).map G).prod := by
      intro Z _ G
      simp [mul_assoc]
    rw [e F, e F']
    exact hP (i :: l)
lemma integral_aeval_eq_of_moments (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (F : ι → C(Ω, ℝ)) (F' : ι → C(Ω', ℝ))
    (hmom : ∀ q : ℕ, 1 ≤ q → ∀ t : Fin q → ι,
      ∫ x, ∏ j, F (t j) x ∂μ = ∫ x, ∏ j, F' (t j) x ∂μ')
    (P : MvPolynomial ι ℝ) :
    ∫ x, MvPolynomial.aeval F P x ∂μ = ∫ x, MvPolynomial.aeval F' P x ∂μ' := by
  simpa using integral_aeval_mul_listProd_eq μ μ' F F' hmom P []
omit [BorelSpace Ω'] in
lemma norm_le_of_even_moments_eq (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hsupp : measureSupport μ = Set.univ)
    (f : C(Ω, ℝ)) (g : C(Ω', ℝ))
    (heven : ∀ k : ℕ, ∫ x, f x ^ (2 * k) ∂μ = ∫ x, g x ^ (2 * k) ∂μ') : ‖f‖ ≤ ‖g‖ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨b, hgb, hbf⟩ := exists_between hlt
  have hb : 0 < b := lt_of_le_of_lt (norm_nonneg g) hgb
  obtain ⟨x₀, hx₀⟩ : ∃ x, b < |f x| := by
    by_contra hno
    push Not at hno
    exact absurd ((ContinuousMap.norm_le f hb.le).2 (fun x => by simpa using hno x))
      (not_le.2 hbf)
  set U : Set Ω := {x | b < |f x|} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const f.continuous.abs
  have hpos : 0 < μ U := by
    have hx : x₀ ∈ measureSupport μ := by rw [hsupp]; trivial
    exact hx U hUopen hx₀
  set m : ℝ := μ.real U with hm
  have hmpos : 0 < m := by
    rw [hm, measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top μ U)
  set a : ℝ := ‖g‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg g
  have key : ∀ k : ℕ, m ≤ ((a / b) ^ 2) ^ k := by
    intro k
    have hlow : b ^ (2 * k) * m ≤ ∫ x, f x ^ (2 * k) ∂μ := by
      have hnn : 0 ≤ᵐ[μ] fun x => f x ^ (2 * k) :=
        Filter.Eventually.of_forall (fun x => by
          show (0 : ℝ) ≤ f x ^ (2 * k)
          rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k)
      have hint : Integrable (fun x => f x ^ (2 * k)) μ :=
        integrable_of_continuousMap_compact μ (f ^ (2 * k))
      refine le_trans ?_ (mul_meas_ge_le_integral_of_nonneg hnn hint (b ^ (2 * k)))
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro x hx
      have hx' : b < |f x| := hx
      have hsq : b ^ 2 ≤ f x ^ 2 := by
        rw [← sq_abs (f x)]
        exact pow_le_pow_left₀ hb.le hx'.le 2
      show b ^ (2 * k) ≤ f x ^ (2 * k)
      rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) hsq k
    have hup : ∫ x, g x ^ (2 * k) ∂μ' ≤ a ^ (2 * k) := by
      have hbd : ∀ᵐ x ∂μ', ‖g x ^ (2 * k)‖ ≤ a ^ (2 * k) :=
        Filter.Eventually.of_forall (fun x => by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (g.norm_coe_le_norm x) _)
      have hn := norm_integral_le_of_norm_le_const hbd
      simp only [probReal_univ, mul_one] at hn
      exact le_trans (le_abs_self _) hn
    have hchain : b ^ (2 * k) * m ≤ a ^ (2 * k) := by
      rw [← heven k] at hup
      exact le_trans hlow hup
    have hbk : 0 < b ^ (2 * k) := by positivity
    rw [← pow_mul, div_pow]
    rw [le_div_iff₀ hbk]
    linarith [hchain, mul_comm m (b ^ (2 * k))]
  have hr0 : 0 ≤ (a / b) ^ 2 := sq_nonneg _
  have hr1 : (a / b) ^ 2 < 1 := by
    have h1 : a / b < 1 := (div_lt_one hb).2 hgb
    have h0 : 0 ≤ a / b := div_nonneg ha0 hb.le
    nlinarith
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hm0 : m ≤ 0 := ge_of_tendsto' hlim key
  linarith
lemma norm_aeval_eq_of_integrals (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hsupp : measureSupport μ = Set.univ) (hsupp' : measureSupport μ' = Set.univ)
    (F : ι → C(Ω, ℝ)) (F' : ι → C(Ω', ℝ))
    (hint : ∀ P : MvPolynomial ι ℝ,
      ∫ x, MvPolynomial.aeval F P x ∂μ = ∫ x, MvPolynomial.aeval F' P x ∂μ')
    (P : MvPolynomial ι ℝ) : ‖MvPolynomial.aeval F P‖ = ‖MvPolynomial.aeval F' P‖ := by
  have heven : ∀ k : ℕ, ∫ x, MvPolynomial.aeval F P x ^ (2 * k) ∂μ =
      ∫ x, MvPolynomial.aeval F' P x ^ (2 * k) ∂μ' := by
    intro k
    simpa using hint (P ^ (2 * k))
  exact le_antisymm (norm_le_of_even_moments_eq μ μ' hsupp _ _ heven)
    (norm_le_of_even_moments_eq μ' μ hsupp' _ _ (fun k => (heven k).symm))
omit [MeasurableSpace Ω] [BorelSpace Ω] [MeasurableSpace Ω'] [BorelSpace Ω'] in
lemma exists_point_values_eq [Nonempty Ω']
    (F : ι → C(Ω, ℝ)) (F' : ι → C(Ω', ℝ))
    (hnorm : ∀ P : MvPolynomial ι ℝ, ‖MvPolynomial.aeval F P‖ = ‖MvPolynomial.aeval F' P‖)
    (ξ : Ω) :
    ∃ η : Ω', ∀ i, F' i η = F i ξ := by
  have hclosed : ∀ i, IsClosed {η : Ω' | F' i η = F i ξ} := fun i =>
    isClosed_eq (F' i).continuous continuous_const
  have hfin : ∀ S : Finset ι, (Set.univ ∩ ⋂ i ∈ S, {η : Ω' | F' i η = F i ξ}).Nonempty := by
    intro S
    classical
    set P : MvPolynomial ι ℝ :=
      ∑ i ∈ S, (MvPolynomial.X i - MvPolynomial.C (F i ξ)) ^ 2 with hP
    have hval : ∀ {Z : Type} [TopologicalSpace Z] (G : ι → C(Z, ℝ)) (z : Z),
        MvPolynomial.aeval G P z = ∑ i ∈ S, (G i z - F i ξ) ^ 2 := by
      intro Z _ G z
      simp [hP, map_sum, ContinuousMap.sum_apply]
    set c : ℝ := ‖MvPolynomial.aeval F' P‖ with hc
    have hc0 : 0 ≤ c := norm_nonneg _
    set Q : MvPolynomial ι ℝ := MvPolynomial.C c - P with hQ
    have hQval : ∀ {Z : Type} [TopologicalSpace Z] (G : ι → C(Z, ℝ)) (z : Z),
        MvPolynomial.aeval G Q z = c - MvPolynomial.aeval G P z := by
      intro Z _ G z
      simp [hQ]
    have hξ : MvPolynomial.aeval F P ξ = 0 := by
      rw [hval]; simp
    have hlow : c ≤ ‖MvPolynomial.aeval F Q‖ := by
      have hle := (MvPolynomial.aeval F Q).norm_coe_le_norm ξ
      rw [hQval, hξ, sub_zero, Real.norm_eq_abs, abs_of_nonneg hc0] at hle
      exact hle
    rw [hnorm Q] at hlow
    obtain ⟨η, -, hη⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (f := fun z => |MvPolynomial.aeval F' Q z|)
      (continuous_abs.comp (ContinuousMap.continuous _)).continuousOn
    have hmax : ‖MvPolynomial.aeval F' Q‖ ≤ |MvPolynomial.aeval F' Q η| := by
      refine (ContinuousMap.norm_le _ (abs_nonneg _)).2 (fun z => ?_)
      simpa using hη (Set.mem_univ z)
    have hge : c ≤ |c - MvPolynomial.aeval F' P η| := by
      rw [← hQval]; exact le_trans hlow hmax
    have hnn : 0 ≤ MvPolynomial.aeval F' P η := by
      rw [hval]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hle : MvPolynomial.aeval F' P η ≤ c := by
      have hb := (MvPolynomial.aeval F' P).norm_coe_le_norm η
      exact le_trans (le_abs_self _) hb
    have hzero : MvPolynomial.aeval F' P η = 0 := by
      rw [abs_of_nonneg (by linarith)] at hge
      linarith
    rw [hval, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at hzero
    refine ⟨η, trivial, ?_⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro i hi
    have hsq := hzero i hi
    have h2 : F' i η - F i ξ = 0 := by simpa using hsq
    linarith
  obtain ⟨η, -, hη⟩ := isCompact_univ.inter_iInter_nonempty
    (fun i => {η : Ω' | F' i η = F i ξ}) hclosed hfin
  exact ⟨η, fun i => by simpa using Set.mem_iInter.1 hη i⟩
lemma abs_integral_sub_le_norm (ν : Measure Ω) [IsProbabilityMeasure ν] (f g : C(Ω, ℝ)) :
    |∫ x, f x ∂ν - ∫ x, g x ∂ν| ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_of_continuousMap_compact ν f)
    (integrable_of_continuousMap_compact ν g)]
  have hb : ∀ᵐ x ∂ν, ‖f x - g x‖ ≤ ‖f - g‖ :=
    Filter.Eventually.of_forall (fun x => by simpa using (f - g).norm_coe_le_norm x)
  have hn := norm_integral_le_of_norm_le_const hb
  simpa using hn
lemma measure_eq_of_integral_aeval_eq_of_separates [TopologicalSpace.MetrizableSpace Ω']
    (ν ν' : Measure Ω') [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (F' : ι → C(Ω', ℝ)) (hsep : ∀ a b : Ω', a ≠ b → ∃ i, F' i a ≠ F' i b)
    (hint : ∀ P : MvPolynomial ι ℝ,
      ∫ x, MvPolynomial.aeval F' P x ∂ν = ∫ x, MvPolynomial.aeval F' P x ∂ν') : ν = ν' := by
  let := TopologicalSpace.metrizableSpaceMetric Ω'
  set A : Subalgebra ℝ C(Ω', ℝ) :=
    (MvPolynomial.aeval F' : MvPolynomial ι ℝ →ₐ[ℝ] C(Ω', ℝ)).range with hA
  have hsepA : A.SeparatesPoints := by
    intro a b hab
    obtain ⟨i, hi⟩ := hsep a b hab
    exact ⟨F' i, ⟨F' i, ⟨MvPolynomial.X i, by simp⟩, rfl⟩, hi⟩
  have hdense := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsepA
  have hall : ∀ g : C(Ω', ℝ), ∫ x, g x ∂ν = ∫ x, g x ∂ν' := by
    intro g
    have hg : g ∈ closure (A : Set C(Ω', ℝ)) := by
      exact show g ∈ A.topologicalClosure from by rw [hdense]; trivial
    refine eq_of_abs_sub_le_all (fun ε hε => ?_)
    obtain ⟨f, hf, hd⟩ := Metric.mem_closure_iff.1 hg (ε / 2) (by positivity)
    obtain ⟨P, rfl⟩ := hf
    have hd' : ‖g - MvPolynomial.aeval F' P‖ < ε / 2 := by
      simpa [dist_eq_norm] using hd
    have h1 := abs_integral_sub_le_norm ν g (MvPolynomial.aeval F' P)
    have h2 := abs_integral_sub_le_norm ν' g (MvPolynomial.aeval F' P)
    have h3 := hint P
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => hall f.toContinuousMap)
end Lemmas
theorem mixedMoments_determine_holds : mixedMoments_determine := by
  intro ι Ω₁ Ω₂ _ _ _ _ _ _ _ _ _ _ μ₁ μ₂ f₁ f₂ hprob₁ hprob₂ hsupp₁ hsupp₂ hcont₁ hcont₂
    hsep₁ hsep₂ hmom
  set F₁ : ι → C(Ω₁, ℝ) := fun i => ⟨f₁ i, hcont₁ i⟩ with hF₁
  set F₂ : ι → C(Ω₂, ℝ) := fun i => ⟨f₂ i, hcont₂ i⟩ with hF₂
  have hne₁ : Nonempty Ω₁ := nonempty_of_isProbabilityMeasure μ₁
  have hne₂ : Nonempty Ω₂ := nonempty_of_isProbabilityMeasure μ₂
  have hint : ∀ P : MvPolynomial ι ℝ,
      ∫ x, MvPolynomial.aeval F₁ P x ∂μ₁ = ∫ x, MvPolynomial.aeval F₂ P x ∂μ₂ :=
    integral_aeval_eq_of_moments μ₁ μ₂ F₁ F₂ hmom
  have hnorm := norm_aeval_eq_of_integrals μ₁ μ₂ hsupp₁ hsupp₂ F₁ F₂ hint
  have hex : ∀ ξ : Ω₁, ∃ η : Ω₂, ∀ i, f₂ i η = f₁ i ξ :=
    exists_point_values_eq F₁ F₂ hnorm
  have hex' : ∀ η : Ω₂, ∃ ξ : Ω₁, ∀ i, f₁ i ξ = f₂ i η :=
    exists_point_values_eq F₂ F₁ (fun P => (hnorm P).symm)
  choose T hT using hex
  choose S hS using hex'
  have hinj₁ : ∀ a b : Ω₁, (∀ i, f₁ i a = f₁ i b) → a = b := by
    intro a b hab
    by_contra hne
    obtain ⟨i, hi⟩ := hsep₁ a b hne
    exact hi (hab i)
  have hinj₂ : ∀ a b : Ω₂, (∀ i, f₂ i a = f₂ i b) → a = b := by
    intro a b hab
    by_contra hne
    obtain ⟨i, hi⟩ := hsep₂ a b hne
    exact hi (hab i)
  have hST : ∀ ξ, S (T ξ) = ξ := fun ξ =>
    hinj₁ _ _ (fun i => by rw [hS, hT])
  have hTS : ∀ η, T (S η) = η := fun η =>
    hinj₂ _ _ (fun i => by rw [hT, hS])
  have hemb₁ : Topology.IsEmbedding (fun (x : Ω₁) (i : ι) => f₁ i x) :=
    (Continuous.isClosedEmbedding (continuous_pi hcont₁)
      (fun a b hab => hinj₁ a b (fun i => congrFun hab i))).isEmbedding
  have hemb₂ : Topology.IsEmbedding (fun (x : Ω₂) (i : ι) => f₂ i x) :=
    (Continuous.isClosedEmbedding (continuous_pi hcont₂)
      (fun a b hab => hinj₂ a b (fun i => congrFun hab i))).isEmbedding
  have hTc : Continuous T := by
    rw [hemb₂.continuous_iff]
    have hcomp : (fun (x : Ω₂) (i : ι) => f₂ i x) ∘ T = fun (x : Ω₁) (i : ι) => f₁ i x := by
      funext x i
      exact hT x i
    rw [hcomp]
    exact continuous_pi hcont₁
  have hSc : Continuous S := by
    rw [hemb₁.continuous_iff]
    have hcomp : (fun (x : Ω₁) (i : ι) => f₁ i x) ∘ S = fun (x : Ω₂) (i : ι) => f₂ i x := by
      funext x i
      exact hS x i
    rw [hcomp]
    exact continuous_pi hcont₂
  have hhomeo : IsHomeomorph T :=
    (Homeomorph.mk ⟨T, S, hST, hTS⟩ hTc hSc).isHomeomorph
  refine ⟨T, fun i => funext (hT · i), ?_, hhomeo, ?_⟩
  · intro R hR
    funext ξ
    exact hinj₂ _ _ (fun i => by
      have hRi := congrFun (hR i) ξ
      simp only [Function.comp_apply] at hRi
      rw [hRi, hT])
  · have hmap : IsProbabilityMeasure (Measure.map T μ₁) :=
      Measure.isProbabilityMeasure_map hTc.measurable.aemeasurable
    refine measure_eq_of_integral_aeval_eq_of_separates _ _ F₂ hsep₂ (fun P => ?_)
    rw [integral_map hTc.measurable.aemeasurable
      (ContinuousMap.continuous _).aestronglyMeasurable, ← hint P]
    congr 1
    funext ξ
    have hcomp : ∀ r : MvPolynomial ι ℝ,
        MvPolynomial.aeval F₂ r (T ξ) = MvPolynomial.aeval F₁ r ξ := by
      intro r
      induction r using MvPolynomial.induction_on with
      | C a => simp
      | add P Q hP hQ => simp [hP, hQ]
      | mul_X P i hP =>
        simp only [map_mul, MvPolynomial.aeval_X, ContinuousMap.mul_apply, hP]
        congr 1
        exact hT ξ i
    exact hcomp P
end YangMills.Construction.Measures.MomentDetermination
