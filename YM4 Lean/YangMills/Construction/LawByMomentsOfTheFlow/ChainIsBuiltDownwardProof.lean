import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellFormProof
import YangMills.Construction.ColdStepAtMirrorFrames.ACutExists
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import YangMills.Construction.LawByMomentsOfTheFlow.CanonicalGaussianInTheTreeGauge
import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormsOfTheChain
import Mathlib
import YangMills.Construction.LawByMomentsOfTheFlow.ExactSquareOfAStep
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorus
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainHasItsGaussianProof
import YangMills.Construction.SummableBoundsOfTheFlow.ChainResponsesAreMixedResponses
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open ResponseInTheExpansion WeightedResponses CompletedForms
def chainBuiltDownwardStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y =>
    (∀ (u n : ℕ) [NeZero n], 64 ≤ n → (fluctuationCov Tb.coupling (Tb.stepParameters y).side 1 u n).PosSemidef) ∧
    ∀ (s n : ℕ) [NeZero n], 64 ≤ n → ∃ μ : Measure (LevelChain (Tb.stepParameters y).side s n),
      IsCanonicalGaussian (levelEnergy Tb.coupling s n) μ ∧
      ∀ (j : ℕ) (hj : j + 1 ≤ s), μ.map (truncateTop (j + 1) s n hj) =
        ((μ.map (truncateTop j s n (Nat.le_of_succ_le hj))).prod
          (fluctuationGaussian Tb.coupling (Tb.stepParameters y).side 1 (s - j - 1)
            (fineSide (Tb.stepParameters y).side j n))).map
          fun w => extendChain Tb.coupling Tb.ρA (s - j - 1) j n w.1 w.2
end YangMills.Construction.MomentLaw
end

set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
namespace ChainDownward
open TorusFields TorusPaths TorusLumps StepCosts TopLevelSites BlockAverages WeightedResponses CompletedForms
open ColdStepAtMirrorFrames LevelComparisons MomentMethod
section Forms
variable {V : Type} [AddCommGroup V] [Module ℝ V]
private structure IsPsd (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop where
  comm : ∀ x y, B x y = B y x
  nonneg : ∀ x, 0 ≤ B x x
private theorem IsPsd.sq_le {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (h : IsPsd B) (x y : V) : (B x y) ^ 2 ≤ B x x * B y y :=
  LinearMap.BilinForm.apply_sq_le_of_symm (B := B) h.nonneg ⟨fun x y => h.comm x y⟩ x y
private theorem IsPsd.vanish {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (h : IsPsd B) {x : V} (hx : B x x = 0) (y : V) : B x y = 0 := by
  have h1 := h.sq_le x y
  rw [hx, zero_mul] at h1
  exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h1 (sq_nonneg _))
private theorem variance_of_form {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hB : IsPsd B) (w : V) :
    gaussianVariance (fun x => B x x) (B w) = B w w := by
  unfold gaussianVariance
  rcases (hB.nonneg w).eq_or_lt with h0 | hpos
  · have hsub : {t | ∃ x, 0 < B x x ∧ t = (B w x) ^ 2 / B x x} ⊆ {0} := by
      rintro t ⟨x, hx, rfl⟩
      simp [hB.vanish h0.symm x]
    rcases Set.subset_singleton_iff_eq.1 hsub with h | h
    · rw [h, Real.sSup_empty]
      exact h0
    · rw [h, csSup_singleton]
      exact h0
  · apply IsGreatest.csSup_eq
    refine ⟨⟨w, hpos, ?_⟩, ?_⟩
    · field_simp
    · rintro t ⟨x, hx, rfl⟩
      rw [div_le_iff₀ hx]
      exact hB.sq_le w x
private theorem exists_vector (T : Submodule ℝ V) [FiniteDimensional ℝ T] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (f : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ T, B x x = 0 → f x = 0) :
    ∃ w ∈ T, ∀ x ∈ T, f x = B w x := by
  let φ : T →ₗ[ℝ] Module.Dual ℝ T := B.domRestrict₁₂ T T
  let g : Module.Dual ℝ T := f.domRestrict T
  have hφ : ∀ x y : T, φ x y = B x y := fun _ _ => rfl
  have hg : g ∈ LinearMap.range φ.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro t ht
    have h1 : φ t = 0 := ht
    have h2 : B t t = 0 := by
      rw [← hφ, h1]
      rfl
    exact hf t t.2 h2
  obtain ⟨ℓ, hℓ⟩ := hg
  refine ⟨((Module.evalEquiv ℝ T).symm ℓ : T), Subtype.coe_prop _, fun x hx => ?_⟩
  have h1 : g ⟨x, hx⟩ = φ.dualMap ℓ ⟨x, hx⟩ := by rw [hℓ]
  have h2 : φ.dualMap ℓ ⟨x, hx⟩ = ℓ (φ ⟨x, hx⟩) := rfl
  rw [h2, ← Module.apply_evalEquiv_symm_apply, hφ, hs] at h1
  exact h1
abbrev _root_.YangMills.SharedProofs.p88707 := @exists_vector
private def IsSumOfSquares (E : V → ℝ) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (l : J → V →ₗ[ℝ] ℝ), ∀ x, E x = ∑ j, l j x ^ 2
private theorem IsSumOfSquares.add {E F : V → ℝ} (hE : IsSumOfSquares E) (hF : IsSumOfSquares F) :
    IsSumOfSquares fun x => E x + F x := by
  obtain ⟨J, _, l, hl⟩ := hE
  obtain ⟨I, _, m, hm⟩ := hF
  refine ⟨J ⊕ I, inferInstance, Sum.elim l m, fun x => ?_⟩
  simp [Fintype.sum_sum_type, hl, hm]
private theorem IsSumOfSquares.comp {W : Type} [AddCommGroup W] [Module ℝ W] {E : W → ℝ} (hE : IsSumOfSquares E)
    (A : V →ₗ[ℝ] W) : IsSumOfSquares fun x => E (A x) := by
  obtain ⟨J, _, l, hl⟩ := hE
  exact ⟨J, inferInstance, fun j => (l j).comp A, fun x => by simp [hl]⟩
private theorem IsSumOfSquares.ofSum {I : Type} [Fintype I] (c : ℝ) (hc : 0 ≤ c) (m : I → V →ₗ[ℝ] ℝ) :
    IsSumOfSquares fun x => c * ∑ i, m i x ^ 2 := by
  refine ⟨I, inferInstance, fun i => Real.sqrt c • m i, fun x => ?_⟩
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt hc, Finset.mul_sum]
private theorem form_of_squares {E : V → ℝ} (hE : IsSumOfSquares E) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, IsPsd B ∧ ∀ x, B x x = E x := by
  obtain ⟨J, _, l, hl⟩ := hE
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => ∑ j, l j x * l j y)
    (fun x x' y => by simp only [map_add, add_mul, Finset.sum_add_distrib])
    (fun r x y => by simp only [map_smul, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp only [map_add, mul_add, Finset.sum_add_distrib])
    (fun r x y => by
      simp only [map_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
  have hB : ∀ x y, B x y = ∑ j, l j x * l j y := fun _ _ => rfl
  refine ⟨B, ⟨fun x y => ?_, fun x => ?_⟩, fun x => ?_⟩
  · rw [hB, hB]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · rw [hB]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  · rw [hB, hl]
    exact Finset.sum_congr rfl fun _ _ => (sq _).symm
private theorem exists_canonical [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : V → ℝ} (hE : IsSumOfSquares E) :
    ∃ μ : Measure V, IsCanonicalGaussian E μ := by
  obtain ⟨J, _, l, hl⟩ := hE
  let T : V →ₗ[ℝ] EuclideanSpace ℝ J :=
    (WithLp.linearEquiv 2 ℝ (J → ℝ)).symm.toLinearMap ∘ₗ LinearMap.pi l
  have hT : ∀ x, E x = ‖T x‖ ^ 2 := fun x => by
    rw [hl, EuclideanSpace.norm_sq_eq]
    simp [T]
  let W : Submodule ℝ (EuclideanSpace ℝ J) := LinearMap.range T
  let T' : V →ₗ[ℝ] W := T.rangeRestrict
  have hT' : ∀ x, E x = ‖T' x‖ ^ 2 := fun x => by rw [hT]; rfl
  obtain ⟨S, hS⟩ := T'.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict T)
  have hS' : ∀ w, T' (S w) = w := fun w => LinearMap.congr_fun hS w
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hSc : Continuous S := S.continuous_of_finiteDimensional
  refine ⟨(stdGaussian W).map S, ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map hSc.measurable.aemeasurable
  intro f hf
  have hfc : Continuous f := f.continuous_of_finiteDimensional
  let L : StrongDual ℝ W := LinearMap.toContinuousLinearMap (f ∘ₗ S)
  have hfL : ∀ x, f x = L (T' x) := fun x => by
    have h0 : E (x - S (T' x)) = 0 := by
      rw [hT', map_sub, hS', sub_self, norm_zero]; norm_num
    have := hf _ h0
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hvar : gaussianVariance E f = ‖L‖ ^ 2 := by
    unfold gaussianVariance
    apply le_antisymm
    · by_cases hne : {w | ∃ x, 0 < E x ∧ w = f x ^ 2 / E x}.Nonempty
      · refine csSup_le hne ?_
        rintro w ⟨x, hx, rfl⟩
        rw [div_le_iff₀ hx, hfL, hT', ← mul_pow, sq_le_sq, abs_of_nonneg (by positivity : 0 ≤ ‖L‖ * ‖T' x‖)]
        exact (L.le_opNorm (T' x))
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
        positivity
    · by_cases hL : L = 0
      · rw [hL, ContinuousLinearMap.opNorm_zero, zero_pow two_ne_zero]
        refine Real.sSup_nonneg ?_
        rintro w ⟨x, hx, rfl⟩
        exact div_nonneg (sq_nonneg _) hx.le
      · let v : W := (InnerProductSpace.toDual ℝ W).symm L
        have hv : ‖v‖ = ‖L‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map L
        have hLv : L v = ‖L‖ ^ 2 := by
          have : inner ℝ v v = L v := InnerProductSpace.toDual_symm_apply
          rw [← this, real_inner_self_eq_norm_sq, hv]
        have hpos : 0 < ‖L‖ :=
          lt_of_le_of_ne (norm_nonneg L) fun h => hL ((ContinuousLinearMap.opNorm_zero_iff L).mp h.symm)
        have hEv : E (S v) = ‖L‖ ^ 2 := by rw [hT', hS', hv]
        have hb : BddAbove {w | ∃ x, 0 < E x ∧ w = f x ^ 2 / E x} := ⟨‖L‖ ^ 2, by
          rintro w ⟨x, hx, rfl⟩
          rw [div_le_iff₀ hx, hfL, hT', ← mul_pow, sq_le_sq, abs_of_nonneg (by positivity : 0 ≤ ‖L‖ * ‖T' x‖)]
          exact L.le_opNorm (T' x)⟩
        refine le_csSup_of_le hb ⟨S v, by rw [hEv]; exact pow_pos hpos 2, rfl⟩ ?_
        rw [hEv, hfL, hS', hLv]
        have h : (‖L‖ ^ 2) ^ 2 / ‖L‖ ^ 2 = ‖L‖ ^ 2 := by field_simp
        exact h.ge
  rw [Measure.map_map hfc.measurable hSc.measurable]
  have hcomp : (⇑f ∘ ⇑S) = ⇑L := rfl
  rw [hcomp, IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian, hvar]
private structure Carries [MeasurableSpace V] (T : Submodule ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (μ : Measure V) : Prop where
  prob : IsProbabilityMeasure μ
  law : ∀ w ∈ T, ∀ f : V →ₗ[ℝ] ℝ, (∀ x ∈ T, f x = B w x) → μ.map f = gaussianReal 0 (B w w).toNNReal
private theorem carries_of_canonical [MeasurableSpace V] {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hB : IsPsd B) {μ : Measure V}
    (h : IsCanonicalGaussian (fun x => B x x) μ) : Carries ⊤ B μ := by
  refine ⟨h.isProbabilityMeasure, fun w _ f hf => ?_⟩
  have hfw : f = B w := LinearMap.ext fun x => hf x Submodule.mem_top
  rw [hfw, ← variance_of_form hB w]
  refine h.map_eq (B w) fun x hx => ?_
  rw [hB.comm]
  exact hB.vanish hx w
private theorem Carries.step {W U : Type} [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]
    [MeasurableSpace V] [MeasurableSpace W] [MeasurableSpace U]
    (hV : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) (hW : ∀ f : W →ₗ[ℝ] ℝ, Measurable f) (hU : ∀ f : U →ₗ[ℝ] ℝ, Measurable f)
    {T : Submodule ℝ V} {T' : Submodule ℝ U} {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {B' : U →ₗ[ℝ] U →ₗ[ℝ] ℝ} {μ : Measure V} {ν : Measure W}
    (hB : IsPsd B) (hC : IsPsd C) (hB' : IsPsd B') (hμ : Carries T B μ) (hν : Carries ⊤ C ν)
    (g : V × W →ₗ[ℝ] U) (hg : Measurable g)
    (hE : ∀ x y, B' (g (x, y)) (g (x, y)) = B x x + C y y)
    (hin : ∀ x ∈ T, ∀ y, g (x, y) ∈ T') (hout : ∀ z ∈ T', ∃ x ∈ T, ∃ y, g (x, y) = z) :
    Carries T' B' ((μ.prod ν).map g) := by
  have := hμ.prob
  have := hν.prob
  have hpol : ∀ x y x' y', B' (g (x, y)) (g (x', y')) = B x x' + C y y' := by
    intro x y x' y'
    have e1 := hE (x + x') (y + y')
    have e2 : g (x + x', y + y') = g (x, y) + g (x', y') := by
      rw [← map_add]
      rfl
    rw [e2] at e1
    simp only [map_add, LinearMap.add_apply] at e1
    have c1 := hB.comm x' x
    have c2 := hC.comm y' y
    have c3 := hB'.comm (g (x', y')) (g (x, y))
    rw [hE, hE] at e1
    linarith
  refine ⟨Measure.isProbabilityMeasure_map hg.aemeasurable, fun w' hw' f hf => ?_⟩
  obtain ⟨w, hw, y₀, rfl⟩ := hout w' hw'
  let f₁ : V →ₗ[ℝ] ℝ := (f ∘ₗ g) ∘ₗ LinearMap.inl ℝ V W
  let f₂ : W →ₗ[ℝ] ℝ := (f ∘ₗ g) ∘ₗ LinearMap.inr ℝ V W
  have h₁ : μ.map f₁ = gaussianReal 0 (B w w).toNNReal := hμ.law w hw f₁ fun x hx => by
    show f (g (x, 0)) = _
    rw [hf _ (hin x hx 0), hpol]
    simp
  have h₂ : ν.map f₂ = gaussianReal 0 (C y₀ y₀).toNNReal := hν.law y₀ Submodule.mem_top f₂ fun y _ => by
    show f (g (0, y)) = _
    rw [hf _ (hin 0 T.zero_mem y), hpol]
    simp
  have hsplit : (⇑f ∘ ⇑g) = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map f₁ f₂ := by
    funext p
    show f (g p) = f (g (p.1, 0)) + f (g (0, p.2))
    rw [← map_add, ← map_add]
    simp
  have hprod := Measure.map_prod_map μ ν (hV f₁) (hW f₂)
  have hconv := @gaussianReal_conv_gaussianReal 0 0 (B w w).toNNReal (C y₀ y₀).toNNReal
  rw [Measure.map_map (hU f) hg, hpol, Real.toNNReal_add (hB.nonneg w) (hC.nonneg y₀), hsplit,
    ← Measure.map_map (by fun_prop) ((hV f₁).prodMap (hW f₂)), ← hprod, h₁, h₂]
  rw [add_zero] at hconv
  exact hconv
private theorem Carries.canonical [MeasurableSpace V] [FiniteDimensional ℝ V] {T : Submodule ℝ V} {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    {μ : Measure V} (hB : IsPsd B) (h : Carries T B μ)
    (hT : ∀ f : V →ₗ[ℝ] ℝ, (∀ x, B x x = 0 → f x = 0) → (∀ x ∈ T, f x = 0) → f = 0) :
    IsCanonicalGaussian (fun x => B x x) μ := by
  refine ⟨h.prob, fun f hf => ?_⟩
  obtain ⟨w, hw, hfw⟩ := exists_vector T B hB.comm f fun x _ hx => hf x hx
  have h0 : f - B w = 0 := hT _ (fun x hx => ?_) (fun x hx => ?_)
  · have hfe : f = B w := sub_eq_zero.1 h0
    rw [h.law w hw f hfw, hfe, variance_of_form hB w]
  · rw [LinearMap.sub_apply, hf x hx, hB.comm w x, hB.vanish hx w, sub_zero]
  · rw [LinearMap.sub_apply, hfw x hx, sub_self]
private theorem no_functional [MeasurableSpace V] [MeasurableSingletonClass V] [FiniteDimensional ℝ V] {T : Submodule ℝ V}
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hB : IsPsd B) {ν : Measure V}
    (hν : IsCanonicalGaussian (fun x => B x x) ν) (hT : ∀ᵐ x ∂ν, x ∈ T)
    (f : V →ₗ[ℝ] ℝ) (hf : ∀ x, B x x = 0 → f x = 0) (hfT : ∀ x ∈ T, f x = 0) : f = 0 := by
  have := hν.isProbabilityMeasure
  obtain ⟨v, -, hv⟩ := exists_vector ⊤ B hB.comm f fun x _ hx => hf x hx
  have hfv : f = B v := LinearMap.ext fun x => hv x Submodule.mem_top
  have h1 : ν.map f = gaussianReal 0 (B v v).toNNReal := by
    rw [hν.map_eq f hf, hfv, variance_of_form hB v]
  have h2 : ν.map f = Measure.dirac 0 := by
    have e : (⇑f) =ᵐ[ν] fun _ => (0 : ℝ) := hT.mono fun x hx => hfT x hx
    rw [Measure.map_congr e, Measure.map_const, measure_univ, one_smul]
  have h3 : Var[id; gaussianReal 0 (B v v).toNNReal] = 0 := by
    rw [← h1, h2]
    exact variance_dirac 0
  rw [variance_id_gaussianReal] at h3
  have h4 : B v v ≤ 0 := by
    have h5 : (B v v).toNNReal = 0 := by exact_mod_cast h3
    exact Real.toNNReal_eq_zero.1 h5
  have h6 : B v v = 0 := le_antisymm h4 (hB.nonneg v)
  rw [hfv]
  exact LinearMap.ext fun x => hB.vanish h6 x
end Forms
section Blocks
variable {ι : Type} [Fintype ι]
private def blockForm (H : Matrix ι ι ℝ) :
    EuclideanSpace ℝ (Fin 3 × ι) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3 × ι) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun η ζ => ∑ e : Fin 3, (fun b => η (e, b)) ⬝ᵥ H.mulVec (fun b => ζ (e, b)))
    (fun η η' ζ => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← add_dotProduct]
      rfl)
    (fun r η ζ => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← smul_eq_mul, ← smul_dotProduct]
      rfl)
    (fun η ζ ζ' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← dotProduct_add, ← Matrix.mulVec_add]
      rfl)
    (fun r η ζ => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← smul_eq_mul, ← dotProduct_smul, ← Matrix.mulVec_smul]
      rfl)
private theorem blockForm_apply (H : Matrix ι ι ℝ) (η ζ : EuclideanSpace ℝ (Fin 3 × ι)) :
    blockForm H η ζ = ∑ e : Fin 3, (fun b => η (e, b)) ⬝ᵥ H.mulVec (fun b => ζ (e, b)) := rfl
variable [DecidableEq ι]
private theorem mulVec_symm {H : Matrix ι ι ℝ} (hH : H.PosDef) (v w : ι → ℝ) : v ⬝ᵥ H.mulVec w = w ⬝ᵥ H.mulVec v := by
  have hT : H.transpose = H := by
    have h := hH.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
abbrev _root_.YangMills.SharedProofs.p101518 := @mulVec_symm
private theorem blockForm_psd {H : Matrix ι ι ℝ} (hH : H.PosDef) : IsPsd (blockForm H) := by
  refine ⟨fun η ζ => ?_, fun η => ?_⟩
  · rw [blockForm_apply, blockForm_apply]
    exact Finset.sum_congr rfl fun e _ => mulVec_symm hH _ _
  · rw [blockForm_apply]
    refine Finset.sum_nonneg fun e _ => ?_
    have h := hH.posSemidef.dotProduct_mulVec_nonneg (fun b => η (e, b))
    simpa using h
private theorem block_mulVec {S : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ} {G : Matrix ι ι ℝ}
    (hS : ∀ i j, S i j = if i.1 = j.1 then G i.2 j.2 else 0) (c : Fin 3 × ι → ℝ) (i : Fin 3 × ι) :
    S.mulVec c i = G.mulVec (fun b => c (i.1, b)) i.2 := by
  simp only [Matrix.mulVec, dotProduct, hS, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i.1]
  · simp
  · intro e _ he
    simp [Ne.symm he]
  · simp
private theorem block_dot {S : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ} {G : Matrix ι ι ℝ}
    (hS : ∀ i j, S i j = if i.1 = j.1 then G i.2 j.2 else 0) (c : Fin 3 × ι → ℝ) :
    c ⬝ᵥ S.mulVec c = ∑ e : Fin 3, (fun b => c (e, b)) ⬝ᵥ G.mulVec (fun b => c (e, b)) := by
  simp only [dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => ?_
  rw [block_mulVec hS]
private theorem block_psd {S : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ} {G : Matrix ι ι ℝ} (hG : G.PosDef)
    (hS : ∀ i j, S i j = if i.1 = j.1 then G i.2 j.2 else 0) : S.PosSemidef := by
  have hGs : ∀ b b', G b b' = G b' b := fun b b' => by
    have h := hG.isHermitian.apply b' b
    simpa using h
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, hS]
    by_cases h : i.1 = j.1
    · rw [if_pos h, if_pos h.symm, hGs]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · have h1 : star x = x := by
      funext i
      simp
    rw [h1, block_dot hS]
    refine Finset.sum_nonneg fun e _ => ?_
    have h := hG.posSemidef.dotProduct_mulVec_nonneg (fun b => x (e, b))
    simpa using h
private theorem law_of_coefficients {κ : Type} [Fintype κ] [DecidableEq κ] {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (c : κ → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ κ) S).map (fun x => ∑ i, c i * x i) =
      gaussianReal 0 (c ⬝ᵥ S.mulVec c).toNNReal := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ κ) S with hμ
  let v : EuclideanSpace ℝ κ := WithLp.toLp 2 c
  let l : StrongDual ℝ (EuclideanSpace ℝ κ) := innerSL ℝ v
  have hl : (fun x : EuclideanSpace ℝ κ => ∑ i, c i * x i) = ⇑l := by
    funext x
    simp [l, v, PiLp.inner_apply, mul_comm]
  have h1 : μ[l] = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp [hμ]
    · exact IsGaussian.integrable_id
  have h2 : Var[l; μ] = c ⬝ᵥ S.mulVec c := by
    have e1 := covarianceBilin_self (μ := μ) IsGaussian.memLp_two_id v
    rw [hμ, covarianceBilin_multivariateGaussian hS, ← hμ] at e1
    rw [show (⇑l) = fun u => inner ℝ v u from rfl, ← e1]
  rw [hl, IsGaussian.map_eq_gaussianReal, h1, h2]
end Blocks
section Chains
variable {L : ℕ} [NeZero L]
@[reducible] private def chainBondFintype (L : ℕ) [NeZero L] : (s n : ℕ) → [NeZero n] → Fintype (LevelBond L s n)
  | 0, n, _ => inferInstanceAs (Fintype (TorusBond n))
  | s + 1, n, _ => by
    letI := chainBondFintype L s (n * L)
    exact inferInstanceAs (Fintype (LevelBond L s (n * L) ⊕ TorusBond n))
private instance (s n : ℕ) [NeZero n] : Fintype (LevelBond L s n) := chainBondFintype L s n
private theorem wordSum_add {m : ℕ} (A B : TorusBond m → ℝ) (w : BondWord m) :
    sumAlongWord (A + B) w = sumAlongWord A w + sumAlongWord B w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
variable {n : ℕ}
private theorem contourMeanOf_add [NeZero n] (A B : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourAverage L (A + B) c = contourAverage L A c + contourAverage L B c := by
  simp only [contourAverage, wordSum_add, Finset.sum_add_distrib, mul_add]
private theorem contourMeanOf_smul [NeZero n] (r : ℝ) (A : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourAverage L (r • A) c = r * contourAverage L A c := by apply _root_.YangMills.SharedProofs.p14469 <;> assumption
private theorem chainTop_add : ∀ (s n : ℕ) (X Y : LevelChain L s n), chainTop s n (X + Y) = chainTop s n X + chainTop s n Y
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainTop_smul : ∀ (s n : ℕ) (r : ℝ) (X : LevelChain L s n), chainTop s n (r • X) = r • chainTop s n X
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainBelowTop_add {s : ℕ} (X Y : LevelChain L (s + 1) n) :
    chainLower (X + Y) = chainLower X + chainLower Y := rfl
private theorem chainBelowTop_smul {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) :
    chainLower (r • X) = r • chainLower X := rfl
private theorem inTree_add : ∀ (s n : ℕ) [NeZero n] (X Y : LevelChain L s n), IsTreeGauge s n X → IsTreeGauge s n Y →
    IsTreeGauge s n (X + Y)
  | 0, _, _, _, _, _, _ => trivial
  | s + 1, n, _, X, Y, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨fun e b hb => by
      rw [chainBelowTop_add, chainTop_add, Pi.add_apply, Pi.add_apply, h1 e b hb, h3 e b hb, add_zero],
    inTree_add s (n * L) _ _ h2 h4⟩
private theorem inTree_smul : ∀ (s n : ℕ) [NeZero n] (r : ℝ) (X : LevelChain L s n), IsTreeGauge s n X →
    IsTreeGauge s n (r • X)
  | 0, _, _, _, _, _ => trivial
  | s + 1, n, _, r, X, ⟨h1, h2⟩ => ⟨fun e b hb => by
      rw [chainBelowTop_smul, chainTop_smul, Pi.smul_apply, Pi.smul_apply, h1 e b hb, smul_zero],
    inTree_smul s (n * L) r _ h2⟩
private theorem inTree_zero : ∀ (s n : ℕ) [NeZero n], IsTreeGauge s n (0 : LevelChain L s n)
  | 0, _, _ => trivial
  | s + 1, n, _ => ⟨fun e b _ => by
      have h := chainTop_smul s (n * L) 0 (chainLower (0 : LevelChain L (s + 1) n))
      rw [zero_smul] at h
      have h' : chainLower (0 : LevelChain L (s + 1) n) = 0 := rfl
      rw [h', h]
      simp, inTree_zero s (n * L)⟩
private def treeGauge (s n : ℕ) [NeZero n] : Submodule ℝ (LevelChain L s n) where
  carrier := {X | IsTreeGauge s n X}
  add_mem' := fun {X Y} hX hY => inTree_add s n X Y hX hY
  zero_mem' := inTree_zero s n
  smul_mem' := fun r X hX => inTree_smul s n r X hX
private def joinTop {s n : ℕ} (B : LevelChain L s (n * L)) (A : ColourForm n) : LevelChain L (s + 1) n := fun e =>
  (Sum.elim (B e) (A e) : LevelBond L s (n * L) ⊕ TorusBond n → ℝ)
private theorem responseMap_add (a ρA : ℝ) (u : ℕ) [NeZero n] (A B : TorusBond n → ℝ) :
    responseMap a ρA L u (A + B) = responseMap a ρA L u A + responseMap a ρA L u B := by
  funext b
  simp only [responseMap, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem responseMap_smul (a ρA : ℝ) (u : ℕ) [NeZero n] (r : ℝ) (A : TorusBond n → ℝ) :
    responseMap a ρA L u (r • A) = r • responseMap a ρA L u A := by
  funext b
  simp only [responseMap, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
abbrev _root_.YangMills.SharedProofs.p84206 := @responseMap_smul
private theorem carried_add (a ρA : ℝ) (u : ℕ) [NeZero n] (X Y : ColourForm n) :
    pushColours a ρA L u (X + Y) = pushColours a ρA L u X + pushColours a ρA L u Y :=
  funext fun e => responseMap_add a ρA u (X e) (Y e)
private theorem carried_smul (a ρA : ℝ) (u : ℕ) [NeZero n] (r : ℝ) (X : ColourForm n) :
    pushColours a ρA L u (r • X) = r • pushColours a ρA L u X :=
  funext fun e => responseMap_smul a ρA u r (X e)
private theorem liftFluctuation_add {u : ℕ} [NeZero n] (η ζ : StepFluctuation L u n) :
    extendFluctuation (η + ζ) = extendFluctuation η + extendFluctuation ζ := by
  classical
  funext e c
  simp only [extendFluctuation, extendChart, PiLp.add_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp
private theorem liftFluctuation_smul {u : ℕ} [NeZero n] (r : ℝ) (η : StepFluctuation L u n) :
    extendFluctuation (r • η) = r • extendFluctuation η := by
  classical
  funext e c
  simp only [extendFluctuation, extendChart, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp
private theorem grow_add (a ρA : ℝ) (u : ℕ) : ∀ (j n : ℕ) [NeZero n] (Z Z' : LevelChain L j n)
    (η ζ : StepFluctuation L u (fineSide L j n)),
    extendChain a ρA u j n (Z + Z') (η + ζ) = extendChain a ρA u j n Z η + extendChain a ρA u j n Z' ζ
  | 0, n, _, Z, Z', η, ζ => by
    funext e c
    rcases c with c | c
    · show pushColours a ρA L u (chainTop 0 n (Z + Z')) e c + extendFluctuation (η + ζ) e c =
        (pushColours a ρA L u (chainTop 0 n Z) e c + extendFluctuation η e c) +
          (pushColours a ρA L u (chainTop 0 n Z') e c + extendFluctuation ζ e c)
      rw [chainTop_add, carried_add, liftFluctuation_add]
      show (pushColours a ρA L u (chainTop 0 n Z) e c + pushColours a ρA L u (chainTop 0 n Z') e c) +
        (extendFluctuation η e c + extendFluctuation ζ e c) = _
      ring
    · rfl
  | j + 1, n, _, Z, Z', η, ζ => by
    funext e c
    rcases c with c | c
    · exact congrFun (congrFun (grow_add a ρA u j (n * L) (chainLower Z) (chainLower Z') η ζ) e) c
    · exact congrFun (congrFun (chainTop_add (j + 1) n Z Z') e) c
private theorem grow_smul (a ρA : ℝ) (u : ℕ) : ∀ (j n : ℕ) [NeZero n] (r : ℝ) (Z : LevelChain L j n)
    (η : StepFluctuation L u (fineSide L j n)),
    extendChain a ρA u j n (r • Z) (r • η) = r • extendChain a ρA u j n Z η
  | 0, n, _, r, Z, η => by
    funext e c
    rcases c with c | c
    · show pushColours a ρA L u (chainTop 0 n (r • Z)) e c + extendFluctuation (r • η) e c =
        r * (pushColours a ρA L u (chainTop 0 n Z) e c + extendFluctuation η e c)
      rw [chainTop_smul, carried_smul, liftFluctuation_smul]
      show r * pushColours a ρA L u (chainTop 0 n Z) e c + r * extendFluctuation η e c = _
      ring
    · rfl
  | j + 1, n, _, r, Z, η => by
    funext e c
    rcases c with c | c
    · exact congrFun (congrFun (grow_smul a ρA u j (n * L) r (chainLower Z) η) e) c
    · exact congrFun (congrFun (chainTop_smul (j + 1) n r Z) e) c
private def growLinear (a ρA : ℝ) (u j n : ℕ) [NeZero n] :
    LevelChain L j n × StepFluctuation L u (fineSide L j n) →ₗ[ℝ] LevelChain L (j + 1) n where
  toFun w := extendChain a ρA u j n w.1 w.2
  map_add' w w' := grow_add a ρA u j n w.1 w'.1 w.2 w'.2
  map_smul' r w := grow_smul a ρA u j n r w.1 w.2
private theorem top_grow (a ρA : ℝ) (u : ℕ) : ∀ (j n : ℕ) [NeZero n] (Z : LevelChain L j n)
    (η : StepFluctuation L u (fineSide L j n)), chainTop (j + 1) n (extendChain a ρA u j n Z η) = chainTop j n Z
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, _, _ => rfl
private theorem topChain_add : ∀ (j s n : ℕ) (h : j ≤ s) (X Y : LevelChain L s n),
    truncateTop j s n h (X + Y) = truncateTop j s n h X + truncateTop j s n h Y
  | 0, s, n, _, X, Y => chainTop_add s n X Y
  | _ + 1, 0, _, h, _, _ => absurd h (by omega)
  | j + 1, s + 1, n, h, X, Y => by
    funext e c
    rcases c with c | c
    · exact congrFun (congrFun (topChain_add j s (n * L) (Nat.le_of_succ_le_succ h) (chainLower X) (chainLower Y)) e) c
    · rfl
private theorem topChain_smul : ∀ (j s n : ℕ) (h : j ≤ s) (r : ℝ) (X : LevelChain L s n),
    truncateTop j s n h (r • X) = r • truncateTop j s n h X
  | 0, s, n, _, r, X => chainTop_smul s n r X
  | _ + 1, 0, _, h, _, _ => absurd h (by omega)
  | j + 1, s + 1, n, h, r, X => by
    funext e c
    rcases c with c | c
    · exact congrFun (congrFun (topChain_smul j s (n * L) (Nat.le_of_succ_le_succ h) r (chainLower X)) e) c
    · rfl
private def topLinear (j s n : ℕ) (h : j ≤ s) : LevelChain L s n →ₗ[ℝ] LevelChain L j n where
  toFun := truncateTop j s n h
  map_add' := topChain_add j s n h
  map_smul' r X := topChain_smul j s n h r X
private theorem measurable_top (j s n : ℕ) [NeZero n] (h : j ≤ s) : Measurable (truncateTop (L := L) j s n h) :=
  (LinearMap.continuous_of_finiteDimensional (topLinear (L := L) j s n h)).measurable
private theorem top_of_grow (a ρA : ℝ) (u : ℕ) : ∀ (j n : ℕ) [NeZero n] (h : j ≤ j + 1) (Z : LevelChain L j n)
    (η : StepFluctuation L u (fineSide L j n)), truncateTop j (j + 1) n h (extendChain a ρA u j n Z η) = Z
  | 0, _, _, _, _, _ => rfl
  | j + 1, n, _, h, Z, η => by
    funext e c
    rcases c with c | c
    · exact congrFun (congrFun (top_of_grow a ρA u j (n * L) (Nat.le_of_succ_le_succ h) (chainLower Z) η) e) c
    · rfl
private theorem top_of_top : ∀ (j s n : ℕ) (h : j + 1 ≤ s) (h' : j ≤ j + 1) (h'' : j ≤ s) (X : LevelChain L s n),
    truncateTop j (j + 1) n h' (truncateTop (j + 1) s n h X) = truncateTop j s n h'' X
  | _, 0, _, h, _, _, _ => absurd h (by omega)
  | 0, _ + 1, _, _, _, _, _ => rfl
  | j + 1, s + 1, n, h, h', h'', X => by
    funext e c
    rcases c with c | c
    · exact congrFun (congrFun (top_of_top j s (n * L) (Nat.le_of_succ_le_succ h) (Nat.le_of_succ_le_succ h')
        (Nat.le_of_succ_le_succ h'') (chainLower X)) e) c
    · rfl
private theorem top_self : ∀ (s n : ℕ) (h : s ≤ s) (X : LevelChain L s n), truncateTop s s n h X = X
  | 0, _, _, _ => rfl
  | s + 1, n, h, X => by
    funext e c
    rcases c with c | c
    · exact congrFun (congrFun (top_self s (n * L) (Nat.le_of_succ_le_succ h) (chainLower X)) e) c
    · rfl
end Chains
private structure ChainFacts (a ρA : ℝ) (L N : ℕ) [NeZero L] : Prop where
  a_pos : 0 < a
  one_le : 1 ≤ L
  square : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (Y : TorusBond n → ℝ) (η : ChartBondIndex L u n → ℝ),
    maxwellForm a L u (fun b => responseMap a ρA L u Y b + extendChart η b)
        (fun b => responseMap a ρA L u Y b + extendChart η b) +
      a * ∑ c : TorusBond n, (contourAverage L (fun b => responseMap a ρA L u Y b + extendChart η b) c - Y c) ^ 2 =
    maxwellForm a L (u + 1) Y Y + η ⬝ᵥ ((trivialHessian a L u n).mulVec η)
  trees : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (Y : TorusBond n → ℝ), ∀ b ∉ chartBonds L n, responseMap a ρA L u Y b = 0
  lift_read : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (X : ColourForm (n * L)) (e : Fin 3), (∀ b ∉ chartBonds L n, X e b = 0) →
    extendChart (u := u) (fun b => chartValues (u := u) X e b) = X e
  lift_off : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (η : ChartBondIndex L u n → ℝ), ∀ b ∉ chartBonds L n, extendChart η b = 0
  bare : ∀ (m : ℕ) [NeZero m] (A A' : TorusBond m → ℝ), maxwellForm a L 0 A A' =
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p * curl A' p
  posDef : ∀ (u n : ℕ) [NeZero n], N ≤ n → (trivialHessian a L u n).PosDef
  tree_law : ∀ (s n : ℕ) [NeZero n], N ≤ n → ∃ ν : Measure (LevelChain L s n),
    IsCanonicalGaussian (levelEnergy a s n) ν ∧ ∀ᵐ X ∂ν, IsTreeGauge s n X
section Energy
variable {a ρA : ℝ} {L N : ℕ} [NeZero L]
private def partEnergy (a : ℝ) (u : ℕ) : (j n : ℕ) → [NeZero n] → LevelChain L j n → ℝ
  | 0, n, _, X => kineticForm a L u (chainTop 0 n X)
  | j + 1, n, _, X => partEnergy a u j (n * L) (chainLower X) + a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2
private theorem side_step (P : ChainFacts a ρA L N) {n : ℕ} (hn : N ≤ n) : N ≤ n * L :=
  hn.trans (Nat.le_mul_of_pos_right n P.one_le)
private theorem side_bare (P : ChainFacts a ρA L N) : ∀ (d : ℕ) {n : ℕ}, N ≤ n → N ≤ fineSide L d n
  | 0, _, hn => hn
  | d + 1, _, hn => side_bare P d (side_step P hn)
private def contourLin {n : ℕ} [NeZero n] (c : TorusBond n) : (TorusBond (n * L) → ℝ) →ₗ[ℝ] ℝ where
  toFun A := contourAverage L A c
  map_add' A B := contourMeanOf_add A B c
  map_smul' t A := contourMeanOf_smul t A c
private def curlLin {m : ℕ} (p : TorusPlaquette m) : (TorusBond m → ℝ) →ₗ[ℝ] ℝ where
  toFun A := curl A p
  map_add' A B := by simp only [curl, Pi.add_apply]; ring
  map_smul' t A := by simp only [curl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
private def responseLin (a ρA : ℝ) (L : ℕ) [NeZero L] (u n : ℕ) [NeZero n] : (TorusBond n → ℝ) →ₗ[ℝ] (TorusBond (n * L) → ℝ) where
  toFun := responseMap a ρA L u
  map_add' := responseMap_add a ρA u
  map_smul' := responseMap_smul a ρA u
private def belowLin (s n : ℕ) : LevelChain L (s + 1) n →ₗ[ℝ] LevelChain L s (n * L) where
  toFun := chainLower
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def topLin : (s n : ℕ) → LevelChain L s n →ₗ[ℝ] ColourForm n
  | 0, _ => LinearMap.id
  | _ + 1, _ =>
    { toFun := fun X e b => X e (Sum.inr b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem topLin_apply (s n : ℕ) (X : LevelChain L s n) : topLin s n X = chainTop s n X := by
  cases s <;> rfl
private def colourLin {n : ℕ} (e : Fin 3) : ColourForm n →ₗ[ℝ] (TorusBond n → ℝ) := LinearMap.proj e
private def nuLin (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusBond n) : LevelChain L (s + 1) n →ₗ[ℝ] ℝ :=
  LinearMap.proj c ∘ₗ colourLin e ∘ₗ topLin (s + 1) n -
    contourLin c ∘ₗ colourLin e ∘ₗ topLin s (n * L) ∘ₗ belowLin s n
private theorem nuLin_apply (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusBond n) (X : LevelChain L (s + 1) n) :
    nuLin s n e c X = chainDefect X e c := by
  simp only [nuLin, LinearMap.sub_apply, LinearMap.comp_apply, topLin_apply]
  rfl
private theorem liftChart_zero {u n : ℕ} [NeZero n] (b : TorusBond (n * L)) :
    extendChart (u := u) (0 : ChartBondIndex L u n → ℝ) b = 0 := by
  classical
  simp [extendChart]
private def fitLin (a ρA : ℝ) (L : ℕ) [NeZero L] (u m : ℕ) [NeZero m] (c : TorusBond m) : (TorusBond m → ℝ) →ₗ[ℝ] ℝ :=
  contourLin c ∘ₗ responseLin a ρA L u m - LinearMap.proj c
private theorem sos_maxwell (P : ChainFacts a ρA L N) : ∀ (u m : ℕ) [NeZero m], N ≤ m →
    IsSumOfSquares fun A : TorusBond m → ℝ => maxwellForm a L u A A
  | 0, m, _, _ => by
    refine ⟨{p // p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m))}, inferInstance, fun p => curlLin p.1, fun A => ?_⟩
    show maxwellForm a L 0 A A = ∑ p : {p // p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m))}, curl A p.1 ^ 2
    rw [P.bare, ← Finset.sum_coe_sort (plaquettesIn (Finset.univ : Finset (TorusSite m)))]
    exact Finset.sum_congr rfl fun p _ => (sq _).symm
  | u + 1, m, _, hm => by
    have h1 := (sos_maxwell P u (m * L) (side_step P hm)).comp (responseLin a ρA L u m)
    have h2 := IsSumOfSquares.ofSum (V := TorusBond m → ℝ) a P.a_pos.le fun c : TorusBond m => fitLin a ρA L u m c
    have h3 := h1.add h2
    have e : (fun A : TorusBond m → ℝ => maxwellForm a L (u + 1) A A) = fun A =>
        maxwellForm a L u (responseLin a ρA L u m A) (responseLin a ρA L u m A) +
          a * ∑ c : TorusBond m, fitLin a ρA L u m c A ^ 2 := by
      funext A
      have h := P.square u m hm A 0
      have e1 : (fun b => responseMap a ρA L u A b + extendChart (u := u) (0 : ChartBondIndex L u m → ℝ) b) =
          responseMap a ρA L u A :=
        funext fun b => by rw [liftChart_zero, add_zero]
      rw [e1, zero_dotProduct, add_zero] at h
      exact h.symm
    rw [e]
    exact h3
private theorem sos_part (P : ChainFacts a ρA L N) (u : ℕ) : ∀ (j n : ℕ) [NeZero n], N ≤ n →
    IsSumOfSquares (partEnergy (L := L) a u j n)
  | 0, n, _, hn => by
    have h := sos_maxwell P u n hn
    have h3 := ((h.comp (colourLin (n := n) 0 ∘ₗ topLin (L := L) 0 n)).add
      (h.comp (colourLin (n := n) 1 ∘ₗ topLin (L := L) 0 n))).add (h.comp (colourLin (n := n) 2 ∘ₗ topLin (L := L) 0 n))
    have e : partEnergy (L := L) a u 0 n = fun X =>
        maxwellForm a L u ((colourLin (n := n) 0 ∘ₗ topLin (L := L) 0 n) X) ((colourLin (n := n) 0 ∘ₗ topLin (L := L) 0 n) X) +
        maxwellForm a L u ((colourLin (n := n) 1 ∘ₗ topLin (L := L) 0 n) X) ((colourLin (n := n) 1 ∘ₗ topLin (L := L) 0 n) X) +
        maxwellForm a L u ((colourLin (n := n) 2 ∘ₗ topLin (L := L) 0 n) X) ((colourLin (n := n) 2 ∘ₗ topLin (L := L) 0 n) X) := by
      funext X
      show ∑ e : Fin 3, maxwellForm a L u (chainTop 0 n X e) (chainTop 0 n X e) = _
      rw [Fin.sum_univ_three]
      rfl
    rw [e]
    exact h3
  | j + 1, n, _, hn => by
    have h1 := (sos_part P u j (n * L) (side_step P hn)).comp (belowLin j n)
    have h2 := IsSumOfSquares.ofSum (V := LevelChain L (j + 1) n) a P.a_pos.le
      fun i : TorusBond n × Fin 3 => nuLin (L := L) j n i.2 i.1
    have h3 := h1.add h2
    have e : partEnergy (L := L) a u (j + 1) n = fun X =>
        partEnergy a u j (n * L) (belowLin j n X) + a * ∑ i : TorusBond n × Fin 3, nuLin (L := L) j n i.2 i.1 X ^ 2 := by
      funext X
      have hsum : ∑ i : TorusBond n × Fin 3, nuLin (L := L) j n i.2 i.1 X ^ 2 =
          ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 :=
        (Fintype.sum_prod_type' (fun (c : TorusBond n) (e : Fin 3) => nuLin (L := L) j n e c X ^ 2)).trans
          (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by rw [nuLin_apply])
      rw [hsum]
      rfl
    rw [e]
    exact h3
private theorem part_zero (P : ChainFacts a ρA L N) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    partEnergy a 0 s n X = levelEnergy a s n X
  | 0, n, _, X => by
    show ∑ e : Fin 3, maxwellForm a L 0 (chainTop 0 n X e) (chainTop 0 n X e) = _
    simp only [levelEnergy, P.bare]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun e _ => (sq _).symm
  | s + 1, n, _, X => by
    simp only [partEnergy, levelEnergy]
    rw [part_zero P s (n * L)]
private theorem step_colours (P : ChainFacts a ρA L N) (u n : ℕ) [NeZero n] (hn : N ≤ n) (A : ColourForm n)
    (η : StepFluctuation L u n) :
    ∑ e : Fin 3, maxwellForm a L u (fun b => responseMap a ρA L u (A e) b + extendChart (fun c => η (e, c)) b)
        (fun b => responseMap a ρA L u (A e) b + extendChart (fun c => η (e, c)) b) +
      a * ∑ c : TorusBond n, ∑ e : Fin 3,
        (A e c - contourAverage L (fun b => responseMap a ρA L u (A e) b + extendChart (fun c => η (e, c)) b) c) ^ 2 =
    ∑ e : Fin 3, maxwellForm a L (u + 1) (A e) (A e) + blockForm (trivialHessian a L u n) η η := by
  have hsq : ∀ e : Fin 3, maxwellForm a L u (fun b => responseMap a ρA L u (A e) b + extendChart (fun c => η (e, c)) b)
        (fun b => responseMap a ρA L u (A e) b + extendChart (fun c => η (e, c)) b) +
      a * ∑ c : TorusBond n,
        (A e c - contourAverage L (fun b => responseMap a ρA L u (A e) b + extendChart (fun c => η (e, c)) b) c) ^ 2 =
      maxwellForm a L (u + 1) (A e) (A e) +
        (fun c => η (e, c)) ⬝ᵥ ((trivialHessian a L u n).mulVec (fun c => η (e, c))) := by
    intro e
    rw [← P.square u n hn (A e) (fun c => η (e, c))]
    congr 2
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin 3)) = Finset.univ) fun e _ => hsq e
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm] at hs
  exact hs
private theorem energy_grow (P : ChainFacts a ρA L N) (u : ℕ) : ∀ (j n : ℕ) [NeZero n], N ≤ n → ∀ (Z : LevelChain L j n)
    (η : StepFluctuation L u (fineSide L j n)),
    partEnergy a u (j + 1) n (extendChain a ρA u j n Z η) =
      partEnergy a (u + 1) j n Z + blockForm (trivialHessian a L u (fineSide L j n)) η η
  | 0, n, _, hn, Z, η => by
    exact step_colours P u n hn (chainTop 0 n Z) η
  | j + 1, n, _, hn, Z, η => by
    have ih := energy_grow P u j (n * L) (side_step P hn) (chainLower Z) η
    have hnu : ∀ (e : Fin 3) (c : TorusBond n), chainDefect (extendChain a ρA u (j + 1) n Z η) e c = chainDefect Z e c :=
      fun e c => by
      have h : chainTop (j + 1) (n * L) (chainLower (extendChain a ρA u (j + 1) n Z η)) = chainTop j (n * L) (chainLower Z) :=
        top_grow a ρA u j (n * L) (chainLower Z) η
      show chainTop (j + 1 + 1) n (extendChain a ρA u (j + 1) n Z η) e c -
        contourAverage L (chainTop (j + 1) (n * L) (chainLower (extendChain a ρA u (j + 1) n Z η)) e) c = _
      rw [h]
      rfl
    show partEnergy a u (j + 1) (n * L) (extendChain a ρA u j (n * L) (chainLower Z) η) +
        a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect (extendChain a ρA u (j + 1) n Z η) e c ^ 2 =
      (partEnergy a (u + 1) j (n * L) (chainLower Z) + a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect Z e c ^ 2) +
        blockForm (trivialHessian a L u (fineSide L j (n * L))) η η
    rw [ih]
    simp only [hnu]
    ring
end Energy
section Chart
variable {L n u : ℕ} [NeZero L] [NeZero n]
private theorem period_depth (L u n : ℕ) [NeZero L] [NeZero n] (i : Fin 4) :
    (torusFrame L u n).period (torusFrame L u n).depth i = n * L :=
  period_depth_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private def frameBond (L u : ℕ) {n : ℕ} (b : TorusBond (n * L)) :
    (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4 :=
  (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
private def torusBond (L u n : ℕ) [NeZero L] [NeZero n] (b : ChartBondIndex L u n) : TorusBond (n * L) :=
  (toTorusSite (n * L) b.1.1, b.1.2)
private theorem frameBond_torusBond (b : ChartBondIndex L u n) : frameBond L u (torusBond L u n b) = b.1 :=
  Prod.ext (torusSiteInFrame_toTorusSite (period_depth L u n) _) rfl
private theorem torusBond_frameBond (c : TorusBond (n * L)) :
    (toTorusSite (n * L) (frameBond L u c).1, (frameBond L u c).2) = c :=
  Prod.ext (toTorusSite_torusSiteInFrame (period_depth L u n) c.1) rfl
private theorem mem_chart_iff (hL : Odd L) (h2 : 2 ≤ n) (b : TorusBond (n * L)) :
    b ∈ chartBonds L n ↔ ¬ IsAxialTreeBond (F := torusFrame L u n) (frameBond L u b) := by apply _root_.YangMills.DeltaSharedProofs.p2283 <;> assumption
private theorem torusBond_mem (hL : Odd L) (h2 : 2 ≤ n) (b : ChartBondIndex L u n) : torusBond L u n b ∈ chartBonds L n := by
  classical
  rw [mem_chart_iff (u := u) hL h2, frameBond_torusBond]
  have h := b.2
  unfold chordBonds at h
  exact (Finset.mem_filter.1 h).2
abbrev _root_.YangMills.DeltaSharedProofs.p502481 := @torusBond_mem
private theorem exists_torusBond (h6 : chartEquivarianceStatement) (hL : Odd L) (h2 : 2 ≤ n) {c : TorusBond (n * L)}
    (hc : c ∈ chartBonds L n) : ∃ b : ChartBondIndex L u n, torusBond L u n b = c :=
  ⟨⟨frameBond L u c, (h6 (torusFrame L u n) 0 hL fun _ => h2).mem_chordBonds_of_not_tree _ ((mem_chart_iff hL h2 c).1 hc)⟩,
    torusBond_frameBond c⟩
private theorem coord_eq (X : ColourForm (n * L)) (e : Fin 3) (b : ChartBondIndex L u n) :
    chartValues (u := u) X e b = X e (torusBond L u n b) := by
  classical
  unfold chartValues
  rw [Finset.sum_eq_single (torusBond L u n b)]
  · exact if_pos (frameBond_torusBond b)
  · intro c _ hc
    rw [if_neg]
    intro h1
    apply hc
    exact (torusBond_frameBond (u := u) c).symm.trans
      (congrArg (fun q => ((toTorusSite (n * L) q.1, q.2) : TorusBond (n * L))) h1)
  · simp
abbrev _root_.YangMills.DeltaSharedProofs.p501607 := @coord_eq
private theorem lift_tb (η : ChartBondIndex L u n → ℝ) (b : ChartBondIndex L u n) : extendChart η (torusBond L u n b) = η b := by
  classical
  unfold extendChart
  rw [Finset.sum_eq_single b]
  · exact if_pos (frameBond_torusBond b)
  · intro b' _ hb
    rw [if_neg]
    intro h1
    exact hb (Subtype.ext ((frameBond_torusBond b).symm.trans h1).symm)
  · simp
abbrev _root_.YangMills.DeltaSharedProofs.p501933 := @lift_tb
private theorem lift_off_chart (hL : Odd L) (h2 : 2 ≤ n) (η : ChartBondIndex L u n → ℝ) {c : TorusBond (n * L)}
    (hc : c ∉ chartBonds L n) : extendChart η c = 0 := by
  classical
  unfold extendChart
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg]
  intro h1
  apply hc
  have e : c = torusBond L u n b :=
    (torusBond_frameBond (u := u) c).symm.trans
      (congrArg (fun q => ((toTorusSite (n * L) q.1, q.2) : TorusBond (n * L))) h1)
  rw [e]
  exact torusBond_mem hL h2 b
abbrev _root_.YangMills.SharedProofs.p85564 := @lift_off_chart
private theorem lift_of_read (h6 : chartEquivarianceStatement) (hL : Odd L) (h2 : 2 ≤ n) (X : ColourForm (n * L)) (e : Fin 3)
    (hX : ∀ b ∉ chartBonds L n, X e b = 0) :
    extendChart (u := u) (fun b => chartValues (u := u) X e b) = X e := by
  funext c
  by_cases hc : c ∈ chartBonds L n
  · obtain ⟨b, rfl⟩ := exists_torusBond (u := u) h6 hL h2 hc
    rw [lift_tb, coord_eq]
  · rw [lift_off_chart hL h2 _ hc, hX c hc]
abbrev _root_.YangMills.SharedProofs.p20242 := @lift_of_read
end Chart
section Tree
variable {a ρA : ℝ} {L N : ℕ} [NeZero L]
private theorem tree_one (P : ChainFacts a ρA L N) (u n : ℕ) [NeZero n] (hn : N ≤ n) (A : ColourForm n)
    (η : StepFluctuation L u n) (e : Fin 3) (b : TorusBond (n * L)) (hb : b ∉ chartBonds L n) :
    responseMap a ρA L u (A e) b + extendChart (fun c => η (e, c)) b = 0 := by
  rw [P.trees u n hn _ b hb, P.lift_off u n hn _ b hb, add_zero]
private theorem tree_grow (P : ChainFacts a ρA L N) (u : ℕ) : ∀ (j n : ℕ) [NeZero n], N ≤ n → ∀ (Z : LevelChain L j n)
    (η : StepFluctuation L u (fineSide L j n)), IsTreeGauge j n Z → IsTreeGauge (j + 1) n (extendChain a ρA u j n Z η)
  | 0, n, _, hn, Z, η, _ => ⟨fun e b hb => by
      exact tree_one P u n hn (chainTop 0 n Z) η e b hb, trivial⟩
  | j + 1, n, _, hn, Z, η, ⟨h1, h2⟩ => ⟨fun e b hb => by
      have h : chainTop (j + 1) (n * L) (chainLower (extendChain a ρA u (j + 1) n Z η)) = chainTop j (n * L) (chainLower Z) :=
        top_grow a ρA u j (n * L) (chainLower Z) η
      rw [h]
      exact h1 e b hb, tree_grow P u j (n * L) (side_step P hn) _ η h2⟩
private theorem peel_one (P : ChainFacts a ρA L N) (u n : ℕ) [NeZero n] (hn : N ≤ n) (A : ColourForm n) (X : ColourForm (n * L))
    (h1 : ∀ e, ∀ b ∉ chartBonds L n, X e b = 0) : ∃ η : StepFluctuation L u n,
      ∀ e b, responseMap a ρA L u (A e) b + extendChart (fun c => η (e, c)) b = X e b := by
  let R : ColourForm (n * L) := fun e b => X e b - responseMap a ρA L u (A e) b
  have hR : ∀ e, ∀ b ∉ chartBonds L n, R e b = 0 := fun e b hb => by
    show X e b - responseMap a ρA L u (A e) b = 0
    rw [h1 e b hb, P.trees u n hn _ b hb, sub_zero]
  refine ⟨WithLp.toLp 2 fun i => chartValues (u := u) R i.1 i.2, fun e b => ?_⟩
  have h2 := congrFun (P.lift_read u n hn R e (hR e)) b
  have h3 : extendChart (fun c => (WithLp.toLp 2 (fun i : Fin 3 × ChartBondIndex L u n => chartValues (u := u) R i.1 i.2) :
      StepFluctuation L u n) (e, c)) b = R e b := h2
  rw [h3]
  show _ + (X e b - _) = _
  ring
private theorem peel (P : ChainFacts a ρA L N) (u : ℕ) : ∀ (j n : ℕ) [NeZero n], N ≤ n → ∀ X : LevelChain L (j + 1) n,
    IsTreeGauge (j + 1) n X → ∃ Z : LevelChain L j n, IsTreeGauge j n Z ∧
      ∃ η : StepFluctuation L u (fineSide L j n), extendChain a ρA u j n Z η = X
  | 0, n, _, hn, X, ⟨h1, _⟩ => by
    obtain ⟨η, hη⟩ := peel_one P u n hn (chainTop 1 n X) (chainTop 0 (n * L) (chainLower X)) h1
    refine ⟨chainTop 1 n X, trivial, η, ?_⟩
    funext e c
    rcases c with c | c
    · exact hη e c
    · rfl
  | j + 1, n, _, hn, X, ⟨h1, h2⟩ => by
    obtain ⟨Z', hZ', η, hη⟩ := peel P u j (n * L) (side_step P hn) (chainLower X) h2
    refine ⟨joinTop Z' (chainTop (j + 1 + 1) n X), ⟨fun e b hb => ?_, hZ'⟩, η, ?_⟩
    · have h3 := h1 e b hb
      rw [← hη, top_grow] at h3
      exact h3
    · funext e c
      rcases c with c | c
      · exact congrFun (congrFun hη e) c
      · rfl
end Tree
section Laws
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem carries_block [DecidableEq (Fin 3 × ι)] {S : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ} {H : Matrix ι ι ℝ}
    (hH : H.PosDef) (hS : ∀ i j, S i j = if i.1 = j.1 then H⁻¹ i.2 j.2 else 0) :
    Carries ⊤ (blockForm H) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3 × ι)) S) := by
  have hSp := block_psd hH.inv hS
  refine ⟨inferInstance, fun w _ f hf => ?_⟩
  let c : Fin 3 × ι → ℝ := fun i => H.mulVec (fun b => w (i.1, b)) i.2
  have hfc : (⇑f) = fun x => ∑ i, c i * x i := by
    funext x
    rw [hf x Submodule.mem_top, blockForm_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mulVec_symm hH]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [hfc, law_of_coefficients hSp]
  congr 2
  rw [block_dot hS, blockForm_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hU := (Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit
  have e1 : H⁻¹.mulVec (fun b => c (e, b)) = fun b => w (e, b) := by
    have e2 : (fun b => c (e, b)) = H.mulVec (fun b => w (e, b)) := rfl
    rw [e2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
  rw [e1]
  exact dotProduct_comm _ _
end Laws
section Built
variable {a ρA : ℝ} {L N : ℕ} [NeZero L]
open Classical in
private theorem covariance_entry (a : ℝ) (L : ℕ) [NeZero L] (u n : ℕ) (i j : Fin 3 × ChartBondIndex L u n) :
    fluctuationCov a L 1 u n i j = if i.1 = j.1 then (trivialHessian a L u n)⁻¹ i.2 j.2 else 0 := by
  simp [fluctuationCov]
open Classical in
private theorem covariance_psd (P : ChainFacts a ρA L N) (u n : ℕ) [NeZero n] (hn : N ≤ n) :
    (fluctuationCov a L 1 u n).PosSemidef :=
  block_psd (P.posDef u n hn).inv (covariance_entry a L u n)
open Classical in
private theorem carries_fluctuation (P : ChainFacts a ρA L N) (u m : ℕ) [NeZero m] (hm : N ≤ m) :
    Carries ⊤ (blockForm (trivialHessian a L u m)) (fluctuationGaussian a L 1 u m) :=
  carries_block (P.posDef u m hm) (covariance_entry a L u m)
private theorem measurable_fluctuation (u m : ℕ) (f : StepFluctuation L u m →ₗ[ℝ] ℝ) : Measurable f :=
  (LinearMap.continuous_of_finiteDimensional f).measurable
private def builtLaw (a ρA : ℝ) (L : ℕ) [NeZero L] (s n : ℕ) [NeZero n] (ρ₀ : Measure (LevelChain L 0 n)) :
    (j : ℕ) → Measure (LevelChain L j n)
  | 0 => ρ₀
  | j + 1 => ((builtLaw a ρA L s n ρ₀ j).prod (fluctuationGaussian a L 1 (s - j - 1) (fineSide L j n))).map
      fun w => extendChain a ρA (s - j - 1) j n w.1 w.2
private theorem built (P : ChainFacts a ρA L N) (s n : ℕ) [NeZero n] (hn : N ≤ n) :
    ∃ μ : Measure (LevelChain L s n), IsCanonicalGaussian (levelEnergy a s n) μ ∧
      ∀ (j : ℕ) (hj : j + 1 ≤ s), μ.map (truncateTop (j + 1) s n hj) =
        ((μ.map (truncateTop j s n (Nat.le_of_succ_le hj))).prod
          (fluctuationGaussian a L 1 (s - j - 1) (fineSide L j n))).map
          fun w => extendChain a ρA (s - j - 1) j n w.1 w.2 := by
  obtain ⟨ν, hν, hνT⟩ := P.tree_law s n hn
  have hs0 := sos_part P s 0 n hn
  obtain ⟨B₀, hB₀, hE₀⟩ := form_of_squares hs0
  obtain ⟨ρ₀, hρ₀⟩ := exists_canonical hs0
  have hρ₀' : IsCanonicalGaussian (fun x => B₀ x x) ρ₀ := by
    have e : (fun x => B₀ x x) = partEnergy a s 0 n := funext hE₀
    rw [e]
    exact hρ₀
  have hV : ∀ (j : ℕ) (f : LevelChain L j n →ₗ[ℝ] ℝ), Measurable f :=
    fun j f => (LinearMap.continuous_of_finiteDimensional f).measurable
  have hgrow : ∀ u j : ℕ, Measurable fun w : LevelChain L j n × StepFluctuation L u (fineSide L j n) =>
      extendChain a ρA u j n w.1 w.2 :=
    fun u j => (LinearMap.continuous_of_finiteDimensional (growLinear (L := L) a ρA u j n)).measurable
  have hstage : ∀ j, j ≤ s → ∃ B : LevelChain L j n →ₗ[ℝ] LevelChain L j n →ₗ[ℝ] ℝ, IsPsd B ∧
      (∀ x, B x x = partEnergy a (s - j) j n x) ∧ Carries (treeGauge j n) B (builtLaw a ρA L s n ρ₀ j) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨B₀, hB₀, fun x => hE₀ x, ?_⟩
      have htop : treeGauge (L := L) 0 n = ⊤ := eq_top_iff.2 fun x _ => trivial
      rw [htop]
      exact carries_of_canonical hB₀ hρ₀'
    | succ j ih =>
      intro hj
      obtain ⟨B, hB, hBE, hC⟩ := ih (by omega)
      have hm := side_bare P j hn
      have hu : s - j - 1 + 1 = s - j := by omega
      have hu' : s - (j + 1) = s - j - 1 := by omega
      obtain ⟨B', hB', hBE'⟩ := form_of_squares (sos_part P (s - j - 1) (j + 1) n hn)
      refine ⟨B', hB', fun x => by rw [hu']; exact hBE' x, ?_⟩
      show Carries _ _ (((builtLaw a ρA L s n ρ₀ j).prod (fluctuationGaussian a L 1 (s - j - 1) (fineSide L j n))).map
        (growLinear (L := L) a ρA (s - j - 1) j n))
      refine Carries.step (hV j) (measurable_fluctuation (s - j - 1) _) (hV (j + 1)) hB
        (blockForm_psd (P.posDef _ _ hm)) hB' hC (carries_fluctuation P _ _ hm) (growLinear a ρA (s - j - 1) j n) (hgrow _ _)
        (fun x y => ?_) (fun x hx y => tree_grow P _ j n hn x y hx) (fun z hz => ?_)
      · show B' (extendChain a ρA (s - j - 1) j n x y) (extendChain a ρA (s - j - 1) j n x y) = _
        rw [hBE', energy_grow P _ j n hn, hu, hBE]
      · obtain ⟨Z, hZ, η, rfl⟩ := peel P (s - j - 1) j n hn z hz
        exact ⟨Z, hZ, η, rfl⟩
  have hprob : ∀ j, j ≤ s → IsProbabilityMeasure (builtLaw a ρA L s n ρ₀ j) := fun j hj => by
    obtain ⟨B, -, -, hC⟩ := hstage j hj
    exact hC.prob
  obtain ⟨B, hB, hBE, hC⟩ := hstage s le_rfl
  have hfun : (fun x => B x x) = levelEnergy a s n := funext fun x => by
    rw [hBE, Nat.sub_self, part_zero P]
  have hν' : IsCanonicalGaussian (fun x => B x x) ν := by
    rw [hfun]
    exact hν
  have hcan : IsCanonicalGaussian (fun x => B x x) (builtLaw a ρA L s n ρ₀ s) :=
    hC.canonical hB fun f hf hfT => no_functional hB hν' (T := treeGauge s n) hνT f hf hfT
  have hdown : ∀ (d j : ℕ) (h : j ≤ s), j + d = s →
      (builtLaw a ρA L s n ρ₀ s).map (truncateTop j s n h) = builtLaw a ρA L s n ρ₀ j := by
    intro d
    induction d with
    | zero =>
      intro j h hd
      have hjs : j = s := by omega
      subst hjs
      have e : truncateTop (L := L) j j n h = id := funext (top_self j n h)
      rw [e, Measure.map_id]
    | succ d ih =>
      intro j h hd
      have h1 : j + 1 ≤ s := by omega
      have e := ih (j + 1) h1 (by omega)
      have e2 : truncateTop (L := L) j s n h = truncateTop j (j + 1) n (Nat.le_succ j) ∘ truncateTop (j + 1) s n h1 :=
        funext fun X => (top_of_top j s n h1 _ h X).symm
      have := hprob j h
      have hm := side_bare P j hn
      have := (carries_fluctuation P (s - j - 1) _ hm).prob
      rw [e2, ← Measure.map_map (measurable_top _ _ _ _) (measurable_top _ _ _ _), e]
      show (((builtLaw a ρA L s n ρ₀ j).prod (fluctuationGaussian a L 1 (s - j - 1) (fineSide L j n))).map
        fun w => extendChain a ρA (s - j - 1) j n w.1 w.2).map _ = _
      rw [Measure.map_map (measurable_top _ _ _ _) (hgrow _ _)]
      have e3 : (truncateTop (L := L) j (j + 1) n (Nat.le_succ j) ∘
          fun w : LevelChain L j n × StepFluctuation L (s - j - 1) (fineSide L j n) =>
            extendChain a ρA (s - j - 1) j n w.1 w.2) = Prod.fst :=
        funext fun w => top_of_grow a ρA (s - j - 1) j n _ w.1 w.2
      rw [e3, Measure.map_fst_prod, measure_univ, one_smul]
  refine ⟨builtLaw a ρA L s n ρ₀ s, hfun ▸ hcan, fun j hj => ?_⟩
  rw [hdown (s - (j + 1)) (j + 1) hj (by omega), hdown (s - j) j (Nat.le_of_succ_le hj) (by omega)]
  rfl
end Built
private theorem at_fresh (hC : ExistsCutoff) {Pr : ColdStepAtMirrorFrames.StepParameters → Prop} (h : EventuallyOrdered Pr)
    (a : ℝ) (ha : 1 ≤ a) :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ c : ColdChainParameters, c.Admissible a L →
      ∃ (Ct κ η₃ : ℝ) (nss : ℕ) (σ : ℝ) (p : ℝ → ℝ) (Cs E : ℝ) (n₀ : ℕ) (CE y₁ : ℝ),
        Pr ⟨a, L, c, Ct, κ, η₃, nss, σ, p, Cs, E, n₀, CE, y₁⟩ := by
  obtain ⟨L₀, g⟩ := h a ha
  refine ⟨L₀, fun L hL hL₀ c hc => ?_⟩
  obtain ⟨Ct₀, g⟩ := g L hL hL₀ c hc
  obtain ⟨κ₀, hκ₀, g⟩ := g Ct₀ le_rfl
  obtain ⟨η₀, hη₀, g⟩ := g κ₀ hκ₀ le_rfl
  have hη : 0 < min η₀ 1 := lt_min hη₀ one_pos
  obtain ⟨N₀, g⟩ := g (min η₀ 1) hη (min_le_right _ _) (min_le_left _ _)
  obtain ⟨σ₀, hσ₀, g⟩ := g N₀ le_rfl
  obtain ⟨p, hp⟩ := hC (σ₀ / 64) (by positivity)
  obtain ⟨C₀, g⟩ := g σ₀ hσ₀ le_rfl p hp
  obtain ⟨m₀, g⟩ := g C₀ le_rfl 1 le_rfl
  obtain ⟨C₁, g⟩ := g (max m₀ 1) (le_max_left _ _)
  obtain ⟨y₀, g⟩ := g C₁ le_rfl
  exact ⟨Ct₀, κ₀, min η₀ 1, N₀, σ₀, p, C₀, 1, max m₀ 1, C₁, y₀,
    g y₀ le_rfl ⟨ha, hL, hc, hκ₀, hη, min_le_right _ _, hσ₀, hp, le_rfl⟩ (le_max_right _ _)⟩
abbrev _root_.YangMills.SharedProofs.p26215 := @at_fresh
end ChainDownward
open ChainDownward TorusFields TorusPaths TorusLumps StepCosts TopLevelSites BlockAverages WeightedResponses CompletedForms
open ColdStepAtMirrorFrames LevelComparisons MomentMethod
theorem chainBuiltDownward (hS : completedSquareStatement) (hB : bareMaxwellFormStatement)
    (hH : trivialHessianPosDefStatement) (hG : canonicalGaussianTreeGaugeStatement)
    (hM : responsesAreInterpResponsesStatement) (hC : ExistsCutoff)
    (h6 : chartEquivarianceStatement) : chainBuiltDownwardStatement := by
  classical
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, g₁⟩ := hS a ha
  obtain ⟨L₃, g₃⟩ := at_fresh hC hM a ha
  refine ⟨max L₁ L₃, rt₁, C₁, hrt₁, ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hCH hrt hCd
  subst hTa hTL
  obtain ⟨y₁, g₁'⟩ := g₁ Tb.side hodd ((le_max_left _ _).trans hL) Tb rfl rfl hD hCS hCH hrt hCd
  obtain ⟨c₀, nss, hT, -⟩ := id hCS
  have hcH : c₀.Admissible Tb.coupling Tb.side := hT.2.2.2.2.2.2.2
  have hρ : 0 < c₀.ρA := by
    rw [hT.2.2.1]
    exact hD.chain.2.2.2.1
  obtain ⟨Ct, κ, η₃, nss', σ, p, Cs, E, n₀, CE, y₃, hResp⟩ := g₃ Tb.side hodd ((le_max_right _ _).trans hL) c₀ hcH
  obtain ⟨Cr, -, hresp⟩ := @hResp Tb.side_ne
  refine ⟨y₁, fun y hy hret hrow => ?_⟩
  have hsqY := g₁' y hy hret hrow
  have hoddL : Odd (Tb.stepParameters y).side := hD.L_odd
  have htrees : ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ (Y : TorusBond n → ℝ), ∀ b ∉ chartBonds (Tb.stepParameters y).side n,
      responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u Y b = 0 := by
    intro u n _ hn Y b hb
    unfold responseMap
    refine Finset.sum_eq_zero fun c _ => ?_
    have h1 := (hresp u n c hn).1.vanishes b hb
    have h2 : responseKernel Tb.coupling c₀.ρA Tb.side u b c = 0 := h1
    rw [hT.2.2.1] at h2
    show responseKernel Tb.coupling Tb.ρA Tb.side u b c * Y c = 0
    rw [h2, zero_mul]
  have P : ChainFacts Tb.coupling Tb.ρA (Tb.stepParameters y).side 64 :=
    { a_pos := lt_of_lt_of_le one_pos hD.a_ge
      one_le := Nat.pos_of_ne_zero (NeZero.ne _)
      square := fun u n _ hn Y η => hsqY u n hn Y η
      trees := fun u n _ hn Y b hb => htrees u n hn Y b hb
      lift_read := fun u n _ hn X e hX => lift_of_read h6 hoddL (by omega) X e hX
      lift_off := fun u n _ hn η b hb => lift_off_chart hoddL (by omega) η hb
      bare := fun m _ A A' => hB _ _ m A A'
      posDef := fun u n _ hn => (hH Tb.coupling Tb.side c₀ hD.a_ge hD.L_odd hD.L_ge hcH hρ u n hn).1
      tree_law := fun s n _ hn => hG _ Tb.coupling hoddL (le_trans zero_le_one hD.a_ge) s n (by omega) }
  exact ⟨fun u n _ hn => covariance_psd P u n hn, fun s n _ hn => built P s n hn⟩
end YangMills.Construction.MomentLaw
end
