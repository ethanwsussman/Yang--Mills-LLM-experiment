import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeightProof
import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import YangMills.Construction.Matrices.HaarRelabelInversion
import YangMills.Construction.ReflectionPositivity.GaugeAveragedCrossingIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.ReflectionPositivity.CrossingWeight Filter Topology
open YangMills.Construction.Matrices
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CrossingGaugeAverage
section ProductsOfSums
variable {J E R : Type} [Fintype E] [NormedField R]
theorem summable_norm_prod_pi (a : E → J → R) (ha : ∀ b, Summable fun j => ‖a b j‖) :
    Summable fun γ : E → J => ‖∏ b, a b (γ b)‖ := by
  classical
  refine summable_of_sum_le (c := ∏ b, ∑' j, ‖a b j‖) (fun _ => norm_nonneg _) ?_
  intro T
  let u : E → Finset J := fun b => T.image fun γ => γ b
  have hsub : T ⊆ Fintype.piFinset u := fun γ hγ =>
    Fintype.mem_piFinset.2 fun b => Finset.mem_image_of_mem _ hγ
  calc ∑ γ ∈ T, ‖∏ b, a b (γ b)‖
      ≤ ∑ γ ∈ Fintype.piFinset u, ‖∏ b, a b (γ b)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _
    _ = ∏ b, ∑ j ∈ u b, ‖a b j‖ := by
        simp_rw [norm_prod]
        exact (Finset.prod_univ_sum u fun b j => ‖a b j‖).symm
    _ ≤ ∏ b, ∑' j, ‖a b j‖ :=
        Finset.prod_le_prod (fun b _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          fun b _ => (ha b).sum_le_tsum _ fun _ _ => norm_nonneg _
theorem hasSum_prod_pi [CompleteSpace R] (a : E → J → R) (s : E → R)
    (ha : ∀ b, Summable fun j => ‖a b j‖)
    (hs : ∀ b, HasSum (a b) (s b)) : HasSum (fun γ : E → J => ∏ b, a b (γ b)) (∏ b, s b) := by
  classical
  have hsum : Summable fun γ : E → J => ∏ b, a b (γ b) := (summable_norm_prod_pi a ha).of_norm
  have hlim : Tendsto (fun T : Finset (E → J) => ∑ γ ∈ T, ∏ b, a b (γ b)) atTop
      (𝓝 (∑' γ : E → J, ∏ b, a b (γ b))) := by
    simpa [HasSum] using hsum.hasSum
  have hmono : Tendsto (fun u : Finset J => Fintype.piFinset fun _ : E => u) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone ?_ ?_
    · intro u v huv
      exact Fintype.piFinset_subset _ _ fun _ => huv
    · intro γ
      exact ⟨Finset.univ.image γ, Fintype.mem_piFinset.2 fun b =>
        Finset.mem_image_of_mem _ (Finset.mem_univ b)⟩
  have hprod : Tendsto (fun u : Finset J => ∏ b, ∑ j ∈ u, a b j) atTop (𝓝 (∏ b, s b)) :=
    tendsto_finsetProd _ fun b _ => by simpa [HasSum] using hs b
  have hcomp : (fun u : Finset J => ∏ b, ∑ j ∈ u, a b j) =
      (fun T : Finset (E → J) => ∑ γ ∈ T, ∏ b, a b (γ b)) ∘
        fun u : Finset J => Fintype.piFinset fun _ : E => u := by
    funext u
    exact Finset.prod_univ_sum (fun _ => u) a
  rw [hcomp] at hprod
  have heq := tendsto_nhds_unique (hlim.comp hmono) hprod
  rw [← heq]
  exact hsum.hasSum
end ProductsOfSums
theorem fullTrace_conj (g a : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.fullTrace ((g * a * g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ComplexMatrix2.fullTrace (a : ComplexMatrix2) := by apply _root_.YangMills.Construction.InfiniteLattice.SUTwoTrace.fullTrace_conj <;> assumption
instance specialUnitary_secondCountable : SecondCountableTopology ComplexMatrix2.specialUnitary := by
  have : SecondCountableTopology ComplexMatrix2 := by
    unfold ComplexMatrix2
    exact inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology _
variable {S E : Type}
theorem linkWeight_gaugeAct_gaugeAct [Fintype E] (β : ℝ) (o t : E → S)
    (W W' : S → ComplexMatrix2.specialUnitary) (X X' : E → ComplexMatrix2.specialUnitary) :
    linkWeight β (gaugeAct o t W X) (gaugeAct o t W' X') =
      linkWeight β (gaugeAct o t (W'⁻¹ * W) X) X' := by
  unfold linkWeight
  refine Finset.prod_congr rfl fun b _ => ?_
  have h : gaugeAct o t W X b * (gaugeAct o t W' X' b)⁻¹ =
      W' (o b) * (gaugeAct o t (W'⁻¹ * W) X b * (X' b)⁻¹) * (W' (o b))⁻¹ := by
    simp only [gaugeAct, Pi.mul_apply, Pi.inv_apply]
    group
  rw [h, fullTrace_conj]
theorem continuous_gaugeAct {Y : Type} [TopologicalSpace Y] (o t : E → S)
    {w : Y → S → ComplexMatrix2.specialUnitary} {x : Y → E → ComplexMatrix2.specialUnitary}
    (hw : Continuous w) (hx : Continuous x) :
    Continuous fun y => gaugeAct o t (w y) (x y) := by
  refine continuous_pi fun b => ?_
  exact (((continuous_apply (o b)).comp hw).mul ((continuous_apply b).comp hx)).mul
    ((continuous_apply (t b)).comp hw).inv
theorem continuous_linkWeight [Fintype E] {Y : Type} [TopologicalSpace Y] (β : ℝ)
    {x₁ x₂ : Y → E → ComplexMatrix2.specialUnitary} (h₁ : Continuous x₁) (h₂ : Continuous x₂) :
    Continuous fun y => (linkWeight β (x₁ y) (x₂ y) : ℂ) := by
  refine Complex.continuous_ofReal.comp ?_
  unfold linkWeight
  refine continuous_finsetProd _ fun b _ => Real.continuous_exp.comp ?_
  refine continuous_const.add (continuous_const.mul (Complex.continuous_re.comp ?_))
  have h : Continuous fun y => x₁ y b * (x₂ y b)⁻¹ :=
    ((continuous_apply b).comp h₁).mul ((continuous_apply b).comp h₂).inv
  exact (Continuous.matrix_trace continuous_id).comp (continuous_subtype_val.comp h)
section Expansion
variable [Fintype E] {F : CharacterFamily} {β : ℝ}
theorem linkCoeff_nonneg (hF : F.Expands β) (γ : E → F.index) :
    0 ≤ linkCoeff F β γ :=
  Finset.prod_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (hF.1 (γ b))
theorem hasSum_linkCoeff (hF : F.Expands β) :
    HasSum (linkCoeff (E := E) F β) (Real.exp (β * (Fintype.card E : ℝ))) := by
  have hs := hF.2.1
  have h := hasSum_prod_pi (E := E) (fun _ j => Real.exp (-β) * F.coeff j)
    (fun _ => Real.exp (-β) * Real.exp (2 * β))
    (fun _ => summable_norm_iff.2 (hs.summable.mul_left _)) (fun _ => hs.mul_left _)
  have e : ∏ _b : E, (Real.exp (-β) * Real.exp (2 * β)) =
      Real.exp (β * (Fintype.card E : ℝ)) := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [e] at h
  exact h
theorem norm_linkProduct_le_one (hF : F.Expands β) (γ : E → F.index)
    (X : E → ComplexMatrix2.specialUnitary) :
    ‖linkProduct F γ X‖ ≤ 1 := by
  unfold linkProduct
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun b _ => hF.2.2.2.1 _ _
theorem continuous_linkProduct {Y : Type} [TopologicalSpace Y] (hF : F.Expands β)
    (γ : E → F.index) {x : Y → E → ComplexMatrix2.specialUnitary} (hx : Continuous x) :
    Continuous fun y => linkProduct F γ (x y) :=
  continuous_finsetProd _ fun b _ => (hF.2.2.1 (γ b)).comp ((continuous_apply b).comp hx)
theorem hasSum_linkWeight (hF : F.Expands β) (X₁ X₂ : E → ComplexMatrix2.specialUnitary) :
    HasSum (fun γ : E → F.index => (linkCoeff F β γ : ℂ) * linkProduct F γ X₁ *
      conj (linkProduct F γ X₂)) (linkWeight β X₁ X₂ : ℂ) := by
  have h := hasSum_prod_pi (E := E)
    (fun b j => ((Real.exp (-β) : ℝ) : ℂ) * F.summand j (X₁ b, X₂ b))
    (fun b => ((Real.exp (-β) : ℝ) : ℂ) * weightAt β (X₁ b, X₂ b))
    (fun b => by
      simp only [norm_mul]
      exact (hF.2.2.2.2.2.1 (X₁ b, X₂ b)).mul_left _)
    (fun b => (hF.2.2.2.2.1 (X₁ b, X₂ b)).mul_left _)
  have e1 : (fun γ : E → F.index =>
      ∏ b, ((Real.exp (-β) : ℝ) : ℂ) * F.summand (γ b) (X₁ b, X₂ b)) =
      fun γ => (linkCoeff F β γ : ℂ) * linkProduct F γ X₁ * conj (linkProduct F γ X₂) := by
    funext γ
    simp only [linkCoeff, linkProduct, CharacterFamily.summand, map_prod,
      Complex.ofReal_prod, Complex.ofReal_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    ring
  have e2 : ∏ b, ((Real.exp (-β) : ℝ) : ℂ) * weightAt β (X₁ b, X₂ b) =
      (linkWeight β X₁ X₂ : ℂ) := by
    simp only [linkWeight, weightAt, Complex.ofReal_prod, Real.exp_add, Complex.ofReal_mul]
  rw [e1, e2] at h
  exact h
variable [Finite S]
theorem integrable_of_continuous_compact {Y : Type} [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {f : Y → ℂ} (hf : Continuous f) : Integrable f μ := by
  have := hf.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  simpa using this
theorem continuous_gaugeAveraged [IsProbabilityMeasure (ComplexMatrix2.haarPi S)]
    (hF : F.Expands β) (o t : E → S) (γ : E → F.index) :
    Continuous (gaugeAveraged F o t γ) := by
  have hc : Continuous fun p : (E → ComplexMatrix2.specialUnitary) ×
      (S → ComplexMatrix2.specialUnitary) =>
      linkProduct F γ (gaugeAct o t p.2 p.1) :=
    continuous_linkProduct hF γ (continuous_gaugeAct o t continuous_snd continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := ComplexMatrix2.haarPi S)
    (f := fun (X : E → ComplexMatrix2.specialUnitary) (W : S → ComplexMatrix2.specialUnitary) =>
      linkProduct F γ (gaugeAct o t W X)) hc
    (isCompact_univ (X := S → ComplexMatrix2.specialUnitary))
  simp only [Measure.restrict_univ] at h
  exact h
theorem norm_gaugeAveraged_le_one [IsProbabilityMeasure (ComplexMatrix2.haarPi S)]
    (hF : F.Expands β) (o t : E → S) (γ : E → F.index) (X : E → ComplexMatrix2.specialUnitary) :
    ‖gaugeAveraged F o t γ X‖ ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := ComplexMatrix2.haarPi S) (C := 1)
    (f := fun W => linkProduct F γ (gaugeAct o t W X))
    (Eventually.of_forall fun W => norm_linkProduct_le_one hF γ _)
  simpa [gaugeAveraged] using h
omit [Finite S] in
theorem continuous_linkWeight_pair (o t : E → S) (X X' : E → ComplexMatrix2.specialUnitary) :
    Continuous fun z : (S → ComplexMatrix2.specialUnitary) × (S → ComplexMatrix2.specialUnitary) =>
      (linkWeight β (gaugeAct o t z.2 X) (gaugeAct o t z.1 X') : ℂ) :=
  continuous_linkWeight β (continuous_gaugeAct o t continuous_snd continuous_const)
    (continuous_gaugeAct o t continuous_fst continuous_const)
theorem integral_linkWeight_gaugeAct [(ComplexMatrix2.haarPi S).IsMulLeftInvariant]
    (o t : E → S) (X X' : E → ComplexMatrix2.specialUnitary)
    (W' : S → ComplexMatrix2.specialUnitary) :
    ∫ W, (linkWeight β (gaugeAct o t W X) (gaugeAct o t W' X') : ℂ) ∂ComplexMatrix2.haarPi S =
      weightIntegral β o t (X, X') := by
  simp_rw [linkWeight_gaugeAct_gaugeAct]
  exact integral_mul_left_eq_self
    (fun W => (linkWeight β (gaugeAct o t W X) X' : ℂ)) W'⁻¹
theorem hasSum_averagedSummand [IsProbabilityMeasure (ComplexMatrix2.haarPi S)]
    [(ComplexMatrix2.haarPi S).IsMulLeftInvariant] (hF : F.Expands β) (o t : E → S)
    (x : (E → ComplexMatrix2.specialUnitary) × (E → ComplexMatrix2.specialUnitary)) :
    HasSum (fun γ => averagedSummand F β o t γ x) (weightIntegral β o t x) := by
  obtain ⟨X, X'⟩ := x
  have := F.countable
  set μ := ComplexMatrix2.haarPi S with hμ
  have hα := hasSum_linkCoeff (E := E) hF
  have hG : ∀ γ : E → F.index, Continuous fun z : (S → ComplexMatrix2.specialUnitary) ×
      (S → ComplexMatrix2.specialUnitary) =>
      (linkCoeff F β γ : ℂ) * linkProduct F γ (gaugeAct o t z.2 X) *
        conj (linkProduct F γ (gaugeAct o t z.1 X')) := fun γ =>
    (continuous_const.mul (continuous_linkProduct hF γ
      (continuous_gaugeAct o t continuous_snd continuous_const))).mul
      (Complex.continuous_conj.comp (continuous_linkProduct hF γ
        (continuous_gaugeAct o t continuous_fst continuous_const)))
  have h := hasSum_integral_of_dominated_convergence (μ := μ.prod μ)
    (F := fun (γ : E → F.index)
      (z : (S → ComplexMatrix2.specialUnitary) × (S → ComplexMatrix2.specialUnitary)) =>
      (linkCoeff F β γ : ℂ) * linkProduct F γ (gaugeAct o t z.2 X) *
        conj (linkProduct F γ (gaugeAct o t z.1 X')))
    (f := fun z => (linkWeight β (gaugeAct o t z.2 X) (gaugeAct o t z.1 X') : ℂ))
    (fun γ _ => linkCoeff F β γ)
    (fun γ => (hG γ).aestronglyMeasurable)
    (fun γ => Eventually.of_forall fun z => by
      have h0 := linkCoeff_nonneg hF γ
      have h1 := norm_linkProduct_le_one hF γ (gaugeAct o t z.2 X)
      have h2 := norm_linkProduct_le_one hF γ (gaugeAct o t z.1 X')
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg h0]
      calc linkCoeff F β γ * ‖linkProduct F γ (gaugeAct o t z.2 X)‖ *
            ‖linkProduct F γ (gaugeAct o t z.1 X')‖
          ≤ linkCoeff F β γ * 1 * 1 := by gcongr
        _ = linkCoeff F β γ := by ring)
    (Eventually.of_forall fun _ => hα.summable)
    (integrable_const _)
    (Eventually.of_forall fun z => hasSum_linkWeight hF _ _)
  have e1 : (fun γ : E → F.index => ∫ z, (linkCoeff F β γ : ℂ) *
      linkProduct F γ (gaugeAct o t z.2 X) *
        conj (linkProduct F γ (gaugeAct o t z.1 X')) ∂μ.prod μ) =
      fun γ => averagedSummand F β o t γ (X, X') := by
    funext γ
    have e := integral_prod_mul (μ := μ) (ν := μ)
      (fun W' => conj (linkProduct F γ (gaugeAct o t W' X')))
      (fun W => linkProduct F γ (gaugeAct o t W X))
    have e' : ∫ z, (linkCoeff F β γ : ℂ) *
        linkProduct F γ (gaugeAct o t z.2 X) *
          conj (linkProduct F γ (gaugeAct o t z.1 X')) ∂μ.prod μ =
        (linkCoeff F β γ : ℂ) *
          ∫ z, conj (linkProduct F γ (gaugeAct o t z.1 X')) *
            linkProduct F γ (gaugeAct o t z.2 X) ∂μ.prod μ := by
      rw [← integral_const_mul]
      congr 1
      funext z
      ring
    rw [e', e, integral_conj]
    simp only [averagedSummand, gaugeAveraged, hμ]
    ring
  have e2 : ∫ z, (linkWeight β (gaugeAct o t z.2 X) (gaugeAct o t z.1 X') : ℂ) ∂μ.prod μ =
      weightIntegral β o t (X, X') := by
    rw [integral_prod _ (integrable_of_continuous_compact _ (continuous_linkWeight_pair o t X X'))]
    simp only [hμ, integral_linkWeight_gaugeAct]
    simp
  rw [e1, e2] at h
  exact h
end Expansion
theorem gaugeAverageStatement_holds (hCrossing : PositiveTypeStatement)
    (hGroup : ComplexMatrix2.FiniteProductGroupStatement)
    (hRelabel : ComplexMatrix2.RelabelInvertPreservesHaar) : GaugeAverageStatement := by
  intro β hβ S E _ _ o t
  have hF := hCrossing β hβ.le
  obtain ⟨-, -, hprob, hinv, -⟩ := hGroup.2.1 S
  have := hprob
  have := hinv
  have := (chosenExpansion β).countable
  have hα := hasSum_linkCoeff (E := E) hF
  have hbound : ∀ γ x, ‖averagedSummand (chosenExpansion β) β o t γ x‖ ≤
      linkCoeff (chosenExpansion β) β γ := by
    intro γ x
    have h0 := linkCoeff_nonneg hF γ
    have h1 := norm_gaugeAveraged_le_one hF o t γ x.1
    have h2 := norm_gaugeAveraged_le_one hF o t γ x.2
    simp only [averagedSummand]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg h0]
    calc linkCoeff (chosenExpansion β) β γ * ‖gaugeAveraged (chosenExpansion β) o t γ x.1‖ *
          ‖gaugeAveraged (chosenExpansion β) o t γ x.2‖
        ≤ linkCoeff (chosenExpansion β) β γ * 1 * 1 := by gcongr
      _ = linkCoeff (chosenExpansion β) β γ := by ring
  refine ⟨linkCoeff_nonneg hF, hα, continuous_gaugeAveraged hF o t,
    norm_gaugeAveraged_le_one hF o t, ?_, hasSum_averagedSummand hF o t, ?_, ?_⟩
  · intro X X'
    have hc : Continuous fun W : S → ComplexMatrix2.specialUnitary =>
        (linkWeight β (gaugeAct o t W X) X' : ℂ) :=
      continuous_linkWeight β (continuous_gaugeAct o t continuous_id continuous_const)
        continuous_const
    obtain ⟨C, hC⟩ := (isCompact_univ (X := S → ComplexMatrix2.specialUnitary)).exists_bound_of_continuousOn
      hc.continuousOn
    have h := (hRelabel S S id (fun _ => -1) Function.bijective_id fun _ => Or.inr rfl).2
      (fun W => (linkWeight β (gaugeAct o t W X) X' : ℂ)) hc.measurable
      ⟨C, fun W => hC W (Set.mem_univ W)⟩
    have e : ComplexMatrix2.relabelInvert (M := S) id (fun _ => (-1 : ℤ)) =
        fun W : S → ComplexMatrix2.specialUnitary => W⁻¹ := by
      funext W b
      simp [ComplexMatrix2.relabelInvert]
    rw [e] at h
    exact h.symm
  · exact fun x => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun γ => hbound γ x)
      hα.summable
  · have h := HasSumUniformlyOn.of_norm_le_summable (s := Set.univ) hα.summable
      (fun γ x _ => hbound γ x)
    have e : (fun x => ∑' γ, averagedSummand (chosenExpansion β) β o t γ x) =
        weightIntegral β o t := by
      funext x
      exact (hasSum_averagedSummand hF o t x).tsum_eq
    rwa [e] at h
end YangMills.Construction.ReflectionPositivity.CrossingGaugeAverage
end
