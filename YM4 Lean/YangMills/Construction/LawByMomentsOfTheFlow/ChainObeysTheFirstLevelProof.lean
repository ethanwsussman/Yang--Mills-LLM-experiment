import YangMills.Construction.LawByMomentsOfTheFlow.CanonicalGaussianInTheTreeGaugeProof
import YangMills.Construction.LawByMomentsOfTheFlow.ChainIsBuiltDownwardProof
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
import YangMills.Construction.LawByMomentsOfTheFlow.ClassicalFormsKillClosedForms
import YangMills.Construction.LawByMomentsOfTheFlow.FirstFormIsTheSquareOfTheCurl
import YangMills.Construction.LawByMomentsOfTheFlow.FormsReadCurvature
import YangMills.Construction.LawByMomentsOfTheFlow.LeastValueOfAStep
import YangMills.Construction.LawByMomentsOfTheFlow.RecursionOfTheClassicalForms
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def levelChainFirstOrderStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S => ∀ d : ℕ, S.lastSeparated + d = S.data.windowLevel →
    ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ →
    (∀ i : Fin Λ.k, ∃ c₀ : ℝ, (μ[S.completedAt d (S.data.period Λ.stepParams.side) i |
        MeasurableSpace.comap (fun X (e : Fin 3) (p : TorusFields.TorusPlaquette (WeightedResponses.fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
          WeightedResponses.curl (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) e) p) inferInstance]) =ᵐ[μ]
      fun X => S.halfForm d (S.data.period Λ.stepParams.side) i X + c₀) ∧
    jointCumulant μ (fun i => S.completedAt d (S.data.period Λ.stepParams.side) i) =
      jointCumulant μ (fun i => S.observableAt (S.lastSeparated + d) (S.data.period Λ.stepParams.side) i)
end YangMills.Construction.MomentLaw
end

set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps TorusPaths WeightedResponses ResponseInTheExpansion RenormalizationStepParameters
namespace LevelChainFirstOrder
section Functionals
variable {V : Type} [AddCommGroup V] [Module ℝ V]
private def Annihilates (E : V → ℝ) (f : V →ₗ[ℝ] ℝ) : Prop := ∀ x, E x = 0 → f x = 0
private theorem Annihilates.smul {E : V → ℝ} {f : V →ₗ[ℝ] ℝ} (c : ℝ) (hf : Annihilates E f) : Annihilates E (c • f) :=
  fun x hx => by simp [hf x hx]
private theorem Annihilates.sum {E : V → ℝ} {ι : Type} (s : Finset ι) (f : ι → V →ₗ[ℝ] ℝ)
    (hf : ∀ i ∈ s, Annihilates E (f i)) : Annihilates E (∑ i ∈ s, f i) :=
  fun x hx => by
    rw [LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i hi => hf i hi x hx
private theorem gaussianVariance_nonneg (E : V → ℝ) (hE : ∀ x, 0 ≤ E x) (f : V →ₗ[ℝ] ℝ) : 0 ≤ gaussianVariance E f :=
  Real.sSup_nonneg (by
    rintro t ⟨x, hx, rfl⟩
    exact div_nonneg (sq_nonneg _) (hE x))
variable [MeasurableSpace V] {E : V → ℝ} {μ : Measure V}
private theorem memLp_of_annihilates (h : IsCanonicalGaussian E μ) {f : V →ₗ[ℝ] ℝ} (hf : Annihilates E f)
    (hm : Measurable f) (p : ENNReal) (hp : p ≠ ⊤) : MemLp f p μ := by
  have h1 : MemLp id p (μ.map f) := by
    rw [h.map_eq f hf]
    exact memLp_id_gaussianReal' p hp
  exact (memLp_map_measure_iff h1.aestronglyMeasurable hm.aemeasurable).1 h1
private theorem integral_of_annihilates (h : IsCanonicalGaussian E μ) {f : V →ₗ[ℝ] ℝ} (hf : Annihilates E f)
    (hm : Measurable f) : ∫ x, f x ∂μ = 0 := by
  have h1 : ∫ y, y ∂(μ.map f) = ∫ x, f x ∂μ :=
    integral_map hm.aemeasurable aestronglyMeasurable_id
  rw [← h1, h.map_eq f hf]
  exact integral_id_gaussianReal
private theorem variance_of_annihilates (h : IsCanonicalGaussian E μ) (hE : ∀ x, 0 ≤ E x) {f : V →ₗ[ℝ] ℝ}
    (hf : Annihilates E f) (hm : Measurable f) : Var[f; μ] = gaussianVariance E f := by
  rw [← variance_id_map hm.aemeasurable, h.map_eq f hf, variance_id_gaussianReal,
    Real.coe_toNNReal _ (gaussianVariance_nonneg E hE f)]
private theorem isGaussianProcess_of_annihilates (h : IsCanonicalGaussian E μ) (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) :
    IsGaussianProcess (fun (f : {f : V →ₗ[ℝ] ℝ // Annihilates E f}) (x : V) => f.1 x) μ := by
  classical
  have := h.isProbabilityMeasure
  refine ⟨fun I => ⟨?_⟩⟩
  have hX : Measurable (fun x : V => I.restrict (fun f : {f : V →ₗ[ℝ] ℝ // Annihilates E f} => f.1 x)) :=
    measurable_pi_lambda _ fun i => hm _
  refine isGaussian_of_map_eq_gaussianReal fun Lc => ?_
  let ℓ : V →ₗ[ℝ] ℝ := ∑ i : I, (Lc.toLinearMap fun j => if i = j then 1 else 0) • i.1.1
  have hℓ : Annihilates E ℓ := Annihilates.sum _ _ fun i _ => Annihilates.smul _ i.1.2
  have hc : (⇑Lc ∘ fun x : V => I.restrict (fun f : {f : V →ₗ[ℝ] ℝ // Annihilates E f} => f.1 x)) = ⇑ℓ := by
    funext x
    simp only [Function.comp, ℓ, LinearMap.sum_apply, LinearMap.smul_apply]
    have := LinearMap.pi_apply_eq_sum_univ Lc.toLinearMap
      (I.restrict fun f : {f : V →ₗ[ℝ] ℝ // Annihilates E f} => f.1 x)
    simp only [ContinuousLinearMap.coe_coe] at this ⊢
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [smul_eq_mul, mul_comm]
  refine ⟨0, (gaussianVariance E ℓ).toNNReal, ?_⟩
  rw [Measure.map_map Lc.continuous.measurable hX, hc]
  exact h.map_eq ℓ hℓ
private theorem indepFun_of_uncorrelated (h : IsCanonicalGaussian E μ) (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f)
    {I J : Type} (F : I → V →ₗ[ℝ] ℝ) (G : J → V →ₗ[ℝ] ℝ) (hF : ∀ i, Annihilates E (F i))
    (hG : ∀ j, Annihilates E (G j)) (hc : ∀ i j, cov[F i, G j; μ] = 0) :
    IndepFun (fun x i => F i x) (fun x j => G j x) μ := by
  have hp := (isGaussianProcess_of_annihilates h hm).comp_right
    (Sum.elim (fun i => (⟨F i, hF i⟩ : {f : V →ₗ[ℝ] ℝ // Annihilates E f})) (fun j => ⟨G j, hG j⟩))
  refine IsGaussianProcess.indepFun_of_covariance_eq_zero (X := fun i x => F i x) (Y := fun j x => G j x) ?_
    (fun i => (hm _).aemeasurable) (fun j => (hm _).aemeasurable) hc
  have e : Sum.elim (fun i x => F i x) (fun j x => G j x) =
      (fun (f : {f : V →ₗ[ℝ] ℝ // Annihilates E f}) (x : V) => f.1 x) ∘
      (Sum.elim (fun i => (⟨F i, hF i⟩ : {f : V →ₗ[ℝ] ℝ // Annihilates E f})) (fun j => ⟨G j, hG j⟩)) := by
    funext z
    cases z <;> rfl
  rw [e]
  exact hp
private abbrev generated {I : Type} (H : I → V →ₗ[ℝ] ℝ) : MeasurableSpace V :=
  MeasurableSpace.comap (fun x i => H i x) MeasurableSpace.pi
private theorem generated_le (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) {I : Type} (H : I → V →ₗ[ℝ] ℝ) :
    generated H ≤ (inferInstance : MeasurableSpace V) :=
  (measurable_pi_lambda _ fun i => hm (H i)).comap_le
private theorem setIntegral_mul_of_uncorrelated (h : IsCanonicalGaussian E μ) (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f)
    {I : Type} (H : I → V →ₗ[ℝ] ℝ) (hH : ∀ i, Annihilates E (H i)) {α β : V →ₗ[ℝ] ℝ} (hα : Annihilates E α)
    (hβ : Annihilates E β) (c₁ : cov[α, β; μ] = 0) (c₂ : ∀ i, cov[H i, β; μ] = 0) {S : Set V}
    (hS : MeasurableSet[generated H] S) : ∫ x in S, α x * β x ∂μ = 0 := by
  classical
  have := h.isProbabilityMeasure
  obtain ⟨T, hT, rfl⟩ := hS
  let F : Option I → V →ₗ[ℝ] ℝ := fun o => o.elim α H
  have hF : ∀ o, Annihilates E (F o) := fun o => by cases o <;> simp [F, hα, hH]
  have hind := indepFun_of_uncorrelated h hm F (fun _ : Unit => β) hF (fun _ => hβ)
    (fun o _ => by cases o <;> simp [F, c₁, c₂])
  have hsub : Measurable fun u : Option I → ℝ => fun i => u (some i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  let φ : (Option I → ℝ) → ℝ := fun u => if (fun i => u (some i)) ∈ T then u none else 0
  have hφ : Measurable φ := Measurable.ite (hsub hT) (measurable_pi_apply _) measurable_const
  let ψ : (Unit → ℝ) → ℝ := fun z => z ()
  have hψ : Measurable ψ := measurable_pi_apply _
  have hi := hind.comp hφ hψ
  have hmS : MeasurableSet ((fun x i => H i x) ⁻¹' T) := (measurable_pi_lambda _ fun i => hm (H i)) hT
  have e1 : ∫ x in (fun x i => H i x) ⁻¹' T, α x * β x ∂μ =
      ∫ x, (φ ∘ fun x o => F o x) x * (ψ ∘ fun x _ => β x) x ∂μ := by
    rw [← integral_indicator hmS]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ (fun x i => H i x) ⁻¹' T
    · have hx' : (fun i => H i x) ∈ T := hx
      simp [φ, ψ, F, hx']
    · have hx' : (fun i => H i x) ∉ T := hx
      simp [φ, F, hx']
  have hb : ∫ x, (ψ ∘ fun x _ => β x) x ∂μ = 0 := integral_of_annihilates h hβ (hm β)
  rw [e1, hi.integral_fun_mul_eq_mul_integral
    (hφ.comp (measurable_pi_lambda _ fun o => hm (F o))).aestronglyMeasurable
    (hψ.comp (measurable_pi_lambda _ fun _ => hm β)).aestronglyMeasurable, hb, mul_zero]
private theorem setIntegral_mul_of_independent (h : IsCanonicalGaussian E μ) (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f)
    {I : Type} (H : I → V →ₗ[ℝ] ℝ) (hH : ∀ i, Annihilates E (H i)) {β β' : V →ₗ[ℝ] ℝ} (hβ : Annihilates E β)
    (hβ' : Annihilates E β') (c₁ : ∀ i, cov[H i, β; μ] = 0) (c₂ : ∀ i, cov[H i, β'; μ] = 0) {S : Set V}
    (hS : MeasurableSet[generated H] S) : ∫ x in S, β x * β' x ∂μ = μ.real S * ∫ x, β x * β' x ∂μ := by
  classical
  have := h.isProbabilityMeasure
  obtain ⟨T, hT, rfl⟩ := hS
  let G : Bool → V →ₗ[ℝ] ℝ := fun b => cond b β β'
  have hG : ∀ b, Annihilates E (G b) := fun b => by cases b <;> simp [G, hβ, hβ']
  have hind := indepFun_of_uncorrelated h hm H G hH hG (fun i b => by cases b <;> simp [G, c₁, c₂])
  let φ : (I → ℝ) → ℝ := fun u => if u ∈ T then 1 else 0
  have hφ : Measurable φ := Measurable.ite hT measurable_const measurable_const
  let ψ : (Bool → ℝ) → ℝ := fun z => z true * z false
  have hψ : Measurable ψ := (measurable_pi_apply _).mul (measurable_pi_apply _)
  have hi := hind.comp hφ hψ
  have hmS : MeasurableSet ((fun x i => H i x) ⁻¹' T) := (measurable_pi_lambda _ fun i => hm (H i)) hT
  have e1 : ∫ x in (fun x i => H i x) ⁻¹' T, β x * β' x ∂μ =
      ∫ x, (φ ∘ fun x i => H i x) x * (ψ ∘ fun x b => G b x) x ∂μ := by
    rw [← integral_indicator hmS]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ (fun x i => H i x) ⁻¹' T
    · have hx' : (fun i => H i x) ∈ T := hx
      simp [φ, ψ, G, hx']
    · have hx' : (fun i => H i x) ∉ T := hx
      simp [φ, hx']
  have e2 : ∫ x, (φ ∘ fun x i => H i x) x ∂μ = μ.real ((fun x i => H i x) ⁻¹' T) := by
    have : (φ ∘ fun x i => H i x) = ((fun x i => H i x) ⁻¹' T).indicator fun _ => (1 : ℝ) := by
      funext x
      by_cases hx : x ∈ (fun x i => H i x) ⁻¹' T
      · have hx' : (fun i => H i x) ∈ T := hx
        simp [φ, hx']
      · have hx' : (fun i => H i x) ∉ T := hx
        simp [φ, hx']
    rw [this, integral_indicator hmS]
    simp
  have e3 : ∫ x, (ψ ∘ fun x b => G b x) x ∂μ = ∫ x, β x * β' x ∂μ := rfl
  rw [e1, hi.integral_fun_mul_eq_mul_integral
    (hφ.comp (measurable_pi_lambda _ fun i => hm (H i))).aestronglyMeasurable
    (hψ.comp (measurable_pi_lambda _ fun b => hm (G b))).aestronglyMeasurable, e2, e3]
private def HasMeanOnSets (C : Set V → Prop) (μ : Measure V) (g : V → ℝ) : Prop :=
  Integrable g μ ∧ ∃ c : ℝ, ∀ S, C S → ∫ x in S, g x ∂μ = μ.real S * c
private theorem HasMeanOnSets.add {C : Set V → Prop} {f g : V → ℝ} (hf : HasMeanOnSets C μ f)
    (hg : HasMeanOnSets C μ g) : HasMeanOnSets C μ fun x => f x + g x := by
  obtain ⟨i₁, c₁, h₁⟩ := hf
  obtain ⟨i₂, c₂, h₂⟩ := hg
  refine ⟨i₁.add i₂, c₁ + c₂, fun S hS => ?_⟩
  rw [integral_add i₁.integrableOn i₂.integrableOn, h₁ S hS, h₂ S hS]
  ring
private theorem HasMeanOnSets.const_mul {C : Set V → Prop} {f : V → ℝ} (r : ℝ) (hf : HasMeanOnSets C μ f) :
    HasMeanOnSets C μ fun x => r * f x := by
  obtain ⟨i₁, c₁, h₁⟩ := hf
  refine ⟨i₁.const_mul r, r * c₁, fun S hS => ?_⟩
  rw [integral_const_mul, h₁ S hS]
  ring
private theorem HasMeanOnSets.const {C : Set V → Prop} [IsFiniteMeasure μ] (r : ℝ) :
    HasMeanOnSets C μ fun _ => r :=
  ⟨integrable_const r, r, fun S _ => by simp⟩
private theorem HasMeanOnSets.sum {C : Set V → Prop} [IsFiniteMeasure μ] {ι : Type} (s : Finset ι) (f : ι → V → ℝ)
    (hf : ∀ i ∈ s, HasMeanOnSets C μ (f i)) : HasMeanOnSets C μ fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasMeanOnSets.const (μ := μ) (C := C) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end Functionals
section Marginals
variable {V U : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
private structure IsMarginal (E₀ : V → ℝ) (B : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (W : V →ₗ[ℝ] U) : Prop where
  form_le : ∀ x, B (W x) (W x) ≤ E₀ x
  exists_eq : ∀ w, ∃ x, W x = w ∧ E₀ x = B w w
private theorem sq_apply_le_mul (B : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x) (hp : ∀ x, 0 ≤ B x x)
    (x y : U) : (B x y) ^ 2 ≤ B x x * B y y :=
  LinearMap.BilinForm.apply_sq_le_of_symm (B := B) hp ⟨fun x y => hs x y⟩ x y
private theorem IsMarginal.annihilates {E₀ : V → ℝ} {B : U →ₗ[ℝ] U →ₗ[ℝ] ℝ} {W : V →ₗ[ℝ] U}
    (hW : IsMarginal E₀ B W) (hs : ∀ x y, B x y = B y x) (hp : ∀ x, 0 ≤ B x x) (w : U) :
    Annihilates E₀ ((B w) ∘ₗ W) := fun x hx => by
  have h0 : B (W x) (W x) = 0 := le_antisymm (hx ▸ hW.form_le x) (hp _)
  have h1 := sq_apply_le_mul B hs hp w (W x)
  rw [h0, mul_zero] at h1
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h1 (sq_nonneg _))
private theorem IsMarginal.variance {E₀ : V → ℝ} {B : U →ₗ[ℝ] U →ₗ[ℝ] ℝ} {W : V →ₗ[ℝ] U} (hW : IsMarginal E₀ B W)
    (hs : ∀ x y, B x y = B y x) (hp : ∀ x, 0 ≤ B x x) (hE : ∀ x, 0 ≤ E₀ x) (w : U) :
    gaussianVariance E₀ ((B w) ∘ₗ W) = B w w := by
  unfold gaussianVariance
  have hup : ∀ t ∈ {t | ∃ x, 0 < E₀ x ∧ t = ((B w ∘ₗ W) x) ^ 2 / E₀ x}, t ≤ B w w := by
    rintro t ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hx]
    have h1 := sq_apply_le_mul B hs hp w (W x)
    exact h1.trans (mul_le_mul_of_nonneg_left (hW.form_le x) (hp w))
  rcases (hp w).eq_or_lt with h0 | hpos
  · rw [← h0]
    refine le_antisymm ?_ (Real.sSup_nonneg ?_)
    · exact Real.sSup_le (fun t ht => h0 ▸ hup t ht) le_rfl
    · rintro t ⟨x, hx, rfl⟩
      exact div_nonneg (sq_nonneg _) hx.le
  · apply IsGreatest.csSup_eq
    refine ⟨?_, hup⟩
    obtain ⟨x, hx, hxe⟩ := hW.exists_eq w
    refine ⟨x, hxe ▸ hpos, ?_⟩
    simp only [LinearMap.comp_apply, hx, hxe]
    field_simp
variable [MeasurableSpace V] {E₀ : V → ℝ} {μ : Measure V}
private theorem IsMarginal.covariance_eq {B : U →ₗ[ℝ] U →ₗ[ℝ] ℝ} {W : V →ₗ[ℝ] U} (hW : IsMarginal E₀ B W)
    (hs : ∀ x y, B x y = B y x) (hp : ∀ x, 0 ≤ B x x) (hE : ∀ x, 0 ≤ E₀ x) (h : IsCanonicalGaussian E₀ μ)
    (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) (w w' : U) :
    cov[(B w) ∘ₗ W, (B w') ∘ₗ W; μ] = B w w' := by
  have := h.isProbabilityMeasure
  have k₁ := hW.annihilates hs hp w
  have k₂ := hW.annihilates hs hp w'
  have k₃ := hW.annihilates hs hp (w + w')
  have hadd : ⇑((B (w + w')) ∘ₗ W) = ⇑((B w) ∘ₗ W) + ⇑((B w') ∘ₗ W) := by
    funext x
    simp
  have h1 := variance_add (memLp_of_annihilates h k₁ (hm _) 2 (by norm_num))
    (memLp_of_annihilates h k₂ (hm _) 2 (by norm_num))
  rw [← hadd, variance_of_annihilates h hE k₃ (hm _), variance_of_annihilates h hE k₁ (hm _),
    variance_of_annihilates h hE k₂ (hm _), hW.variance hs hp hE, hW.variance hs hp hE, hW.variance hs hp hE] at h1
  have h2 : B (w + w') (w + w') = B w w + 2 * B w w' + B w' w' := by
    simp only [map_add, LinearMap.add_apply, hs w' w]
    ring
  linarith
end Marginals
section Chains
variable {L : ℕ} [NeZero L]
@[reducible] private def levelBondFintype (L : ℕ) [NeZero L] : (s n : ℕ) → [NeZero n] → Fintype (LevelBond L s n)
  | 0, n, _ => inferInstanceAs (Fintype (TorusBond n))
  | s + 1, n, _ => by
    letI := levelBondFintype L s (n * L)
    exact inferInstanceAs (Fintype (LevelBond L s (n * L) ⊕ TorusBond n))
private instance (s n : ℕ) [NeZero n] : Fintype (LevelBond L s n) := levelBondFintype L s n
private theorem sumAlongWord_add {m : ℕ} (A B : TorusBond m → ℝ) (w : BondWord m) :
    sumAlongWord (A + B) w = sumAlongWord A w + sumAlongWord B w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
variable {n : ℕ}
private theorem contourAverage_add [NeZero n] (A B : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (A + B) c = _root_.YangMills.Construction.MomentLaw.contourAverage L A c + _root_.YangMills.Construction.MomentLaw.contourAverage L B c := by
  simp only [_root_.YangMills.Construction.MomentLaw.contourAverage, sumAlongWord_add, Finset.sum_add_distrib, mul_add]
private theorem contourAverage_smul [NeZero n] (r : ℝ) (A : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (r • A) c = r * _root_.YangMills.Construction.MomentLaw.contourAverage L A c := by apply _root_.YangMills.SharedProofs.p14469 <;> assumption
private theorem chainTop_add : ∀ (s n : ℕ) (X Y : LevelChain L s n),
    chainTop s n (X + Y) = chainTop s n X + chainTop s n Y
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainTop_smul : ∀ (s n : ℕ) (r : ℝ) (X : LevelChain L s n),
    chainTop s n (r • X) = r • chainTop s n X
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainLower_add {s : ℕ} (X Y : LevelChain L (s + 1) n) :
    chainLower (X + Y) = chainLower X + chainLower Y := rfl
private theorem chainLower_smul {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) :
    chainLower (r • X) = r • chainLower X := rfl
private theorem chainDefect_add [NeZero n] {s : ℕ} (X Y : LevelChain L (s + 1) n) (e : Fin 3) (c : TorusBond n) :
    chainDefect (X + Y) e c = chainDefect X e c + chainDefect Y e c := by apply _root_.YangMills.SharedProofs.p32985 <;> assumption
private theorem chainDefect_smul [NeZero n] {s : ℕ} (r : ℝ) (X : LevelChain L (s + 1) n) (e : Fin 3)
    (c : TorusBond n) : chainDefect (r • X) e c = r * chainDefect X e c := by apply _root_.YangMills.SharedProofs.p30900 <;> assumption
private def levelPairing (a : ℝ) : (s n : ℕ) → [NeZero n] → LevelChain L s n → LevelChain L s n → ℝ
  | 0, n, _, X, Y => ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), ∑ e : Fin 3,
      curl (chainTop 0 n X e) p * curl (chainTop 0 n Y e) p
  | s + 1, n, _, X, Y => levelPairing a s (n * L) (chainLower X) (chainLower Y) +
      a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c * chainDefect Y e c
private theorem curl_add {m : ℕ} (A B : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (A + B) p = curl A p + curl B p := by apply _root_.YangMills.SharedProofs.p35838 <;> assumption
private theorem curl_smul {m : ℕ} (r : ℝ) (A : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (r • A) p = r * curl A p := by apply _root_.YangMills.SharedProofs.p39240 <;> assumption
private theorem levelPairing_comm (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (X Y : LevelChain L s n),
    levelPairing a s n X Y = levelPairing a s n Y X
  | 0, n, _, X, Y => by
    simp only [levelPairing]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ => mul_comm _ _
  | s + 1, n, _, X, Y => by
    simp only [levelPairing]
    rw [levelPairing_comm a s (n * L)]
    congr 2
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => mul_comm _ _
private theorem levelPairing_add (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (X X' Y : LevelChain L s n),
    levelPairing a s n (X + X') Y = levelPairing a s n X Y + levelPairing a s n X' Y
  | 0, n, _, X, X', Y => by
    simp only [levelPairing, chainTop_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show chainTop 0 n X e + chainTop 0 n X' e = (chainTop 0 n X + chainTop 0 n X') e from rfl,
      Pi.add_apply, curl_add]
    ring
  | s + 1, n, _, X, X', Y => by
    simp only [levelPairing, chainLower_add]
    rw [levelPairing_add a s (n * L)]
    have : ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect (X + X') e c * chainDefect Y e c =
        ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c * chainDefect Y e c +
          ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X' e c * chainDefect Y e c := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [chainDefect_add]
      ring
    rw [this]
    ring
private theorem levelPairing_smul (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (r : ℝ) (X Y : LevelChain L s n),
    levelPairing a s n (r • X) Y = r * levelPairing a s n X Y
  | 0, n, _, r, X, Y => by
    simp only [levelPairing, chainTop_smul, Pi.smul_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show r • chainTop 0 n X e = (r • chainTop 0 n X) e from rfl, Pi.smul_apply, curl_smul]
    ring
  | s + 1, n, _, r, X, Y => by
    simp only [levelPairing, chainLower_smul]
    rw [levelPairing_smul a s (n * L)]
    have : ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect (r • X) e c * chainDefect Y e c =
        r * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c * chainDefect Y e c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [chainDefect_smul]
      ring
    rw [this]
    ring
private def levelForm (a : ℝ) (s n : ℕ) [NeZero n] : LevelChain L s n →ₗ[ℝ] LevelChain L s n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (levelPairing a s n) (levelPairing_add a s n) (levelPairing_smul a s n)
    (fun X Y Y' => by
      rw [levelPairing_comm a s n X, levelPairing_add, levelPairing_comm a s n Y, levelPairing_comm a s n Y'])
    (fun r X Y => by
      rw [levelPairing_comm a s n X, levelPairing_smul, levelPairing_comm a s n Y]
      rfl)
private theorem levelForm_apply (a : ℝ) (s n : ℕ) [NeZero n] (X Y : LevelChain L s n) :
    levelForm a s n X Y = levelPairing a s n X Y := rfl
private theorem levelForm_comm (a : ℝ) (s n : ℕ) [NeZero n] (X Y : LevelChain L s n) :
    levelForm a s n X Y = levelForm a s n Y X := levelPairing_comm a s n X Y
private theorem levelForm_self (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    levelForm a s n X X = levelEnergy a s n X
  | 0, n, _, X => by
    simp only [levelForm_apply, levelPairing, levelEnergy]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun e _ => (sq _).symm
  | s + 1, n, _, X => by
    have ih := levelForm_self a s (n * L) (chainLower X)
    rw [levelForm_apply] at ih ⊢
    simp only [levelPairing, levelEnergy]
    rw [ih]
    congr 2
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => (sq _).symm
private theorem levelEnergy_nonneg {a : ℝ} (ha : 0 ≤ a) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    0 ≤ levelEnergy a s n X
  | 0, n, _, X => by
    simp only [levelEnergy]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  | s + 1, n, _, X => by
    simp only [levelEnergy]
    exact add_nonneg (levelEnergy_nonneg ha s (n * L) _)
      (mul_nonneg ha (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
private theorem levelEnergy_succ (a : ℝ) (s n : ℕ) [NeZero n] (X : LevelChain L (s + 1) n) :
    levelEnergy a (s + 1) n X = levelEnergy a s (n * L) (chainLower X) +
      a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 := by
  simp only [levelEnergy]
private theorem kineticForm_eq (a : ℝ) (L u : ℕ) {n : ℕ} [NeZero n] (X : ColourForm n) :
    kineticForm a L u X = ∑ e : Fin 3, maxwellForm a L u (X e) (X e) := rfl
private def attachTop {s n : ℕ} (B : LevelChain L s (n * L)) (A : ColourForm n) : LevelChain L (s + 1) n :=
  fun e => Sum.elim (B e) (A e)
private theorem chainLower_attachTop {s n : ℕ} (B : LevelChain L s (n * L)) (A : ColourForm n) :
    chainLower (attachTop B A) = B := rfl
private def lowerLinear (s n : ℕ) : LevelChain L (s + 1) n →ₗ[ℝ] LevelChain L s (n * L) where
  toFun := chainLower
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def topLinear (s n : ℕ) : LevelChain L s n →ₗ[ℝ] ColourForm n where
  toFun := chainTop s n
  map_add' := chainTop_add s n
  map_smul' r X := chainTop_smul s n r X
private def curlFunctional {m : ℕ} (e : Fin 3) (p : TorusPlaquette m) : ColourForm m →ₗ[ℝ] ℝ where
  toFun A := curl (A e) p
  map_add' A B := curl_add (A e) (B e) p
  map_smul' r A := by simpa using curl_smul r (A e) p
private def evalFunctional {m : ℕ} (e : Fin 3) (c : TorusBond m) : ColourForm m →ₗ[ℝ] ℝ where
  toFun A := A e c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def contourFunctional [NeZero n] (e : Fin 3) (c : TorusBond n) : ColourForm (n * L) →ₗ[ℝ] ℝ where
  toFun A := _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c
  map_add' A B := contourAverage_add (A e) (B e) c
  map_smul' r A := by simpa using contourAverage_smul r (A e) c
private theorem responseMap_add (a ρ : ℝ) (u : ℕ) [NeZero n] (A B : TorusBond n → ℝ) :
    responseMap a ρ L u (A + B) = responseMap a ρ L u A + responseMap a ρ L u B := by
  funext b
  simp only [responseMap, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem responseMap_smul (a ρ : ℝ) (u : ℕ) [NeZero n] (r : ℝ) (A : TorusBond n → ℝ) :
    responseMap a ρ L u (r • A) = r • responseMap a ρ L u A := by apply _root_.YangMills.SharedProofs.p84206 <;> assumption
private def pushLinear (a ρ : ℝ) (u n : ℕ) [NeZero n] : ColourForm n →ₗ[ℝ] ColourForm (n * L) where
  toFun := pushColours a ρ L u
  map_add' X Y := by
    funext e
    exact responseMap_add a ρ u (X e) (Y e)
  map_smul' r X := by
    funext e
    exact responseMap_smul a ρ u r (X e)
private def pushedChain (a ρ : ℝ) : (s n : ℕ) → [NeZero n] → ColourForm n → LevelChain L s n
  | 0, _, _, A => A
  | s + 1, n, _, A => attachTop (pushedChain a ρ s (n * L) (pushColours a ρ L s A)) A
private theorem chainTop_pushedChain (a ρ : ℝ) : ∀ (s n : ℕ) [NeZero n] (A : ColourForm n),
    chainTop s n (pushedChain (L := L) a ρ s n A) = A
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
end Chains
private structure ScaleFlowBounds (a ρ cK : ℝ) (L n₀ : ℕ) [NeZero L] : Prop where
  a_pos : 0 < a
  cK_pos : 0 < cK
  L_pos : 0 < L
  le_step : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ (W : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ),
    maxwellForm a L (u + 1) B B ≤ maxwellForm a L u W W + a * ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L W c - B c) ^ 2
  eq_step : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ B : TorusBond n → ℝ, maxwellForm a L (u + 1) B B =
    maxwellForm a L u (responseMap a ρ L u B) (responseMap a ρ L u B) +
      a * ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L u B) c - B c) ^ 2
  form_zero : ∀ (m : ℕ) [NeZero m] (A : TorusBond m → ℝ),
    maxwellForm a L 0 A A = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2
  coercive : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ A : TorusBond n → ℝ,
    2 * cK * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 ≤ maxwellForm a L u A A
section Energy
variable {L : ℕ} [NeZero L] {a ρ cK : ℝ} {n₀ : ℕ}
private theorem ScaleFlowBounds.le_mul_side (F : ScaleFlowBounds a ρ cK L n₀) {n : ℕ} (hn : n₀ ≤ n) : n₀ ≤ n * L :=
  hn.trans (Nat.le_mul_of_pos_right n F.L_pos)
private theorem levelEnergy_zero (F : ScaleFlowBounds a ρ cK L n₀) (n : ℕ) [NeZero n] (X : LevelChain L 0 n) :
    levelEnergy a 0 n X = kineticForm a L 0 (chainTop 0 n X) := by
  have h : levelEnergy a 0 n X = ∑ e : Fin 3, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      curl (chainTop 0 n X e) p ^ 2 := by
    simp only [levelEnergy]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [h, kineticForm_eq]
  exact Finset.sum_congr rfl fun e _ => (F.form_zero n _).symm
private theorem kineticForm_top_le (F : ScaleFlowBounds a ρ cK L n₀) : ∀ (s n : ℕ) [NeZero n], n₀ ≤ n →
    ∀ X : LevelChain L s n, kineticForm a L s (chainTop s n X) ≤ levelEnergy a s n X := by
  intro s
  induction s with
  | zero =>
    intro n _ _ X
    exact (levelEnergy_zero F n X).ge
  | succ s ih =>
    intro n _ hn X
    have h := ih (n * L) (F.le_mul_side hn) (chainLower X)
    have h2 : ∀ e, maxwellForm a L (s + 1) (chainTop (s + 1) n X e) (chainTop (s + 1) n X e) ≤
        maxwellForm a L s (chainTop s (n * L) (chainLower X) e) (chainTop s (n * L) (chainLower X) e) +
          a * ∑ c : TorusBond n, chainDefect X e c ^ 2 := by
      intro e
      have h3 := F.le_step s n hn (chainTop s (n * L) (chainLower X) e) (chainTop (s + 1) n X e)
      have h4 : ∑ c : TorusBond n,
          (_root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) (chainLower X) e) c - chainTop (s + 1) n X e c) ^ 2 =
          ∑ c : TorusBond n, chainDefect X e c ^ 2 :=
        Finset.sum_congr rfl fun c _ => by
          unfold chainDefect
          ring
      rwa [h4] at h3
    rw [levelEnergy_succ, kineticForm_eq]
    have h5 := Finset.sum_le_sum fun e (_ : e ∈ (Finset.univ : Finset (Fin 3))) => h2 e
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))] at h5
    rw [kineticForm_eq] at h
    linarith
private theorem levelEnergy_pushedChain (F : ScaleFlowBounds a ρ cK L n₀) : ∀ (s n : ℕ) [NeZero n], n₀ ≤ n →
    ∀ Y : ColourForm n, levelEnergy a s n (pushedChain (L := L) a ρ s n Y) = kineticForm a L s Y := by
  intro s
  induction s with
  | zero =>
    intro n _ _ Y
    exact levelEnergy_zero F n Y
  | succ s ih =>
    intro n _ hn Y
    have hE := ih (n * L) (F.le_mul_side hn) (pushColours a ρ L s Y)
    have h2 : levelEnergy a (s + 1) n (pushedChain (L := L) a ρ (s + 1) n Y) =
        levelEnergy a s (n * L) (pushedChain (L := L) a ρ s (n * L) (pushColours a ρ L s Y)) +
        a * ∑ c : TorusBond n, ∑ e : Fin 3, (Y e c - _root_.YangMills.Construction.MomentLaw.contourAverage L
          (chainTop s (n * L) (pushedChain (L := L) a ρ s (n * L) (pushColours a ρ L s Y)) e) c) ^ 2 := rfl
    rw [h2, chainTop_pushedChain, hE, kineticForm_eq, kineticForm_eq, Finset.sum_comm, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [F.eq_step s n hn (Y e)]
    have h6 : ∑ c : TorusBond n, (Y e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (pushColours a ρ L s Y e) c) ^ 2 =
        ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L s (Y e)) c - Y e c) ^ 2 :=
      Finset.sum_congr rfl fun c _ => by
        show (Y e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L s (Y e)) c) ^ 2 = _
        ring
    rw [h6]
    rfl
private theorem maxwellForm_self_nonneg (F : ScaleFlowBounds a ρ cK L n₀) (u : ℕ) {m : ℕ} [NeZero m] (hm : n₀ ≤ m)
    (A : TorusBond m → ℝ) : 0 ≤ maxwellForm a L u A A :=
  (mul_nonneg (mul_nonneg zero_le_two F.cK_pos.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
    (F.coercive u m hm A)
private theorem curl_eq_zero_of_ordered {m : ℕ} [NeZero m] {A : TorusBond m → ℝ}
    (h : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p = 0) (p : TorusPlaquette m) :
    curl A p = 0 := by
  obtain ⟨x, μ', ν⟩ := p
  rcases lt_trichotomy μ' ν with hl | he | hg
  · exact h _ (by simp [plaquettesIn, hl])
  · subst he
    simp only [curl]
    ring
  · have := h (x, ν, μ') (by simp [plaquettesIn, hg])
    simp only [curl] at this ⊢
    linarith
abbrev _root_.YangMills.SharedProofs.p30341 := @curl_eq_zero_of_ordered
private theorem curl_eq_zero_of_form (F : ScaleFlowBounds a ρ cK L n₀) (u : ℕ) {m : ℕ} [NeZero m] (hm : n₀ ≤ m)
    {A : TorusBond m → ℝ} (h : maxwellForm a L u A A = 0) (p : TorusPlaquette m) : curl A p = 0 := by
  refine curl_eq_zero_of_ordered (fun p hp => ?_) p
  have h1 := F.coercive u m hm A
  rw [h] at h1
  have h2 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2 ≤ 0 := by
    by_contra hc
    push_neg at hc
    have := mul_pos (mul_pos two_pos F.cK_pos) hc
    linarith
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1
    (le_antisymm h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  exact pow_eq_zero_iff two_ne_zero |>.1 (h3 p hp)
private theorem maxwellForm_top_eq_zero (F : ScaleFlowBounds a ρ cK L n₀) {s n : ℕ} [NeZero n] (hn : n₀ ≤ n)
    {X : LevelChain L s n} (h : levelEnergy a s n X = 0) (e : Fin 3) :
    maxwellForm a L s (chainTop s n X e) (chainTop s n X e) = 0 := by
  have h1 := kineticForm_top_le F s n hn X
  rw [h, kineticForm_eq] at h1
  exact (Finset.sum_eq_zero_iff_of_nonneg fun e _ => maxwellForm_self_nonneg F s hn _).1
    (le_antisymm h1 (Finset.sum_nonneg fun e _ => maxwellForm_self_nonneg F s hn _)) e (Finset.mem_univ _)
private theorem levelEnergy_lower_eq_zero (F : ScaleFlowBounds a ρ cK L n₀) {s n : ℕ} [NeZero n]
    {X : LevelChain L (s + 1) n} (h : levelEnergy a (s + 1) n X = 0) :
    levelEnergy a s (n * L) (chainLower X) = 0 := by
  rw [levelEnergy_succ] at h
  have h1 := levelEnergy_nonneg F.a_pos.le s (n * L) (chainLower X)
  have h2 : 0 ≤ a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 :=
    mul_nonneg F.a_pos.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  linarith
private theorem chainDefect_eq_zero (F : ScaleFlowBounds a ρ cK L n₀) {s n : ℕ} [NeZero n] {X : LevelChain L (s + 1) n}
    (h : levelEnergy a (s + 1) n X = 0) (e : Fin 3) (c : TorusBond n) : chainDefect X e c = 0 := by
  have h0 := levelEnergy_lower_eq_zero F h
  rw [levelEnergy_succ, h0, zero_add] at h
  have h1 := (mul_eq_zero.1 h).resolve_left F.a_pos.ne'
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _).1 h1 c
    (Finset.mem_univ _)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h2 e (Finset.mem_univ _)
  exact pow_eq_zero_iff two_ne_zero |>.1 h3
private theorem pushed_of_form_eq_zero (F : ScaleFlowBounds a ρ cK L n₀) {u n : ℕ} [NeZero n] (hn : n₀ ≤ n)
    {A : TorusBond n → ℝ} (h : maxwellForm a L (u + 1) A A = 0) :
    maxwellForm a L u (responseMap a ρ L u A) (responseMap a ρ L u A) = 0 ∧
      ∀ c, _root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L u A) c - A c = 0 := by
  have h1 := F.eq_step u n hn A
  rw [h] at h1
  have h2 := maxwellForm_self_nonneg F u (F.le_mul_side hn) (responseMap a ρ L u A)
  have h3 : 0 ≤ a * ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L u A) c - A c) ^ 2 :=
    mul_nonneg F.a_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine ⟨by linarith, fun c => ?_⟩
  have h4 : a * ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L u A) c - A c) ^ 2 = 0 := by linarith
  have h5 := (mul_eq_zero.1 h4).resolve_left F.a_pos.ne'
  exact pow_eq_zero_iff two_ne_zero |>.1
    ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h5 c (Finset.mem_univ _))
private theorem levelForm_expand (a : ℝ) (s n : ℕ) [NeZero n] (w z : LevelChain L s n) (r : ℝ) :
    levelForm a s n (w + r • z) (w + r • z) =
      levelForm a s n w w + 2 * r * levelForm a s n w z + r ^ 2 * levelForm a s n z z := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, levelForm_comm a s n z w]
  ring
private theorem levelForm_pushedChain_eq_zero (F : ScaleFlowBounds a ρ cK L n₀) (s n : ℕ) [NeZero n] (hn : n₀ ≤ n)
    (A : ColourForm n) (z : LevelChain L s n) (hz : chainTop s n z = 0) :
    levelForm a s n (pushedChain (L := L) a ρ s n A) z = 0 := by
  set w := pushedChain (L := L) a ρ s n A with hw
  have key : ∀ r : ℝ, 0 ≤ 2 * r * levelForm a s n w z + r ^ 2 * levelForm a s n z z := by
    intro r
    have h1 := kineticForm_top_le F s n hn (w + r • z)
    rw [chainTop_add, chainTop_smul, hz, smul_zero, add_zero, hw, chainTop_pushedChain, ← hw, ← levelForm_self,
      levelForm_expand] at h1
    have h2 := levelEnergy_pushedChain (ρ := ρ) F s n hn A
    rw [← hw, ← levelForm_self] at h2
    linarith
  set b := levelForm a s n w z
  set e := levelForm a s n z z
  have he : 0 ≤ e := by
    have := levelEnergy_nonneg F.a_pos.le s n z
    rwa [← levelForm_self] at this
  by_contra hb
  have hb2 : 0 < b ^ 2 := by positivity
  have h3 := key (-b / (e + 1))
  have hne : e + 1 ≠ 0 := by positivity
  have h4 : 2 * (-b / (e + 1)) * b + (-b / (e + 1)) ^ 2 * e = -(b ^ 2 * (e + 2)) / (e + 1) ^ 2 := by
    field_simp
    ring
  rw [h4] at h3
  have h5 : -(b ^ 2 * (e + 2)) / (e + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  linarith
end Energy
section Pushed
variable {L : ℕ} [NeZero L] {a ρ cK : ℝ} {n₀ : ℕ}
private theorem exists_representing {U : Type} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    (B : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x) (f : U →ₗ[ℝ] ℝ) (hf : ∀ x, B x x = 0 → f x = 0) :
    ∃ w, ∀ x, f x = B w x := by
  have hg : f ∈ LinearMap.range (LinearMap.dualMap B) := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro t ht
    have h1 : B t = 0 := ht
    exact hf t (by rw [h1]; rfl)
  obtain ⟨ℓ, hℓ⟩ := hg
  refine ⟨(Module.evalEquiv ℝ U).symm ℓ, fun x => ?_⟩
  have h1 : f x = (LinearMap.dualMap B ℓ) x := by rw [hℓ]
  have h2 : (LinearMap.dualMap B ℓ) x = ℓ (B x) := rfl
  rw [h2, ← Module.apply_evalEquiv_symm_apply, hs] at h1
  exact h1
private theorem levelForm_symm (a : ℝ) (s n : ℕ) [NeZero n] (x y : LevelChain L s n) :
    levelForm a s n x y = levelForm a s n y x := levelForm_comm a s n x y
private theorem levelForm_self_nonneg {a : ℝ} (ha : 0 ≤ a) (s n : ℕ) [NeZero n] (x : LevelChain L s n) :
    0 ≤ levelForm a s n x x := by
  rw [levelForm_self]
  exact levelEnergy_nonneg ha s n x
private theorem covariance_top_eq_zero (F : ScaleFlowBounds a ρ cK L n₀) {V : Type} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {E₀ : V → ℝ} {μ : Measure V} (h : IsCanonicalGaussian E₀ μ) (hE : ∀ x, 0 ≤ E₀ x)
    (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) {s n : ℕ} [NeZero n] (hn : n₀ ≤ n) {W : V →ₗ[ℝ] LevelChain L s n}
    (hW : IsMarginal E₀ (levelForm a s n) W) {g f : LevelChain L s n →ₗ[ℝ] ℝ}
    (hg : Annihilates (levelEnergy a s n) g) (hf : Annihilates (levelEnergy a s n) f)
    (hgt : ∀ X, g (pushedChain (L := L) a ρ s n (chainTop s n X)) = g X)
    (hf0 : ∀ A, f (pushedChain (L := L) a ρ s n A) = 0) :
    cov[g ∘ₗ W, f ∘ₗ W; μ] = 0 := by
  obtain ⟨wg, hwg⟩ := exists_representing (levelForm a s n) (levelForm_symm a s n) g
    fun x hx => hg x (by rwa [← levelForm_self])
  obtain ⟨wf, hwf⟩ := exists_representing (levelForm a s n) (levelForm_symm a s n) f
    fun x hx => hf x (by rwa [← levelForm_self])
  have eg : g = levelForm a s n wg := LinearMap.ext hwg
  have ef : f = levelForm a s n wf := LinearMap.ext hwf
  have hc := hW.covariance_eq (levelForm_symm a s n) (levelForm_self_nonneg F.a_pos.le s n) hE h hm wg wf
  rw [← eg, ← ef] at hc
  rw [hc, hwg, levelForm_symm, ← hwf]
  set P := pushedChain (L := L) a ρ s n (chainTop s n wg) with hP
  have hz : chainTop s n (wg - P) = 0 := by
    have e1 : wg = P + (wg - P) := by abel
    have e2 := chainTop_add s n P (wg - P)
    rw [← e1, hP, chainTop_pushedChain] at e2
    have e3 : chainTop s n (pushedChain (L := L) a ρ s n (chainTop s n wg) +
        (wg - pushedChain (L := L) a ρ s n (chainTop s n wg))) = chainTop s n wg := by
      rw [add_sub_cancel]
    rw [chainTop_add, chainTop_pushedChain] at e3
    exact left_eq_add.1 e3.symm
  have h1 : levelForm a s n (wg - P) (wg - P) = 0 := by
    have h2 := levelForm_pushedChain_eq_zero (ρ := ρ) F s n hn (chainTop s n wg) (wg - P) hz
    rw [← hP] at h2
    have e : levelForm a s n (wg - P) (wg - P) = levelForm a s n wg (wg - P) - levelForm a s n P (wg - P) := by
      rw [map_sub (levelForm a s n) wg P]
      rfl
    rw [e, h2, sub_zero, ← hwg, map_sub, hP, hgt, sub_self]
  have h3 : f (wg - P) = 0 := hf _ (by rwa [← levelForm_self])
  rw [map_sub, hf0, sub_zero] at h3
  exact h3
private theorem IsMarginal.comp_annihilates {V : Type} [AddCommGroup V] [Module ℝ V] {E₀ : V → ℝ} {s n : ℕ}
    [NeZero n] {W : V →ₗ[ℝ] LevelChain L s n} (ha : 0 ≤ a) (hW : IsMarginal E₀ (levelForm a s n) W)
    {f : LevelChain L s n →ₗ[ℝ] ℝ} (hf : Annihilates (levelEnergy a s n) f) : Annihilates E₀ (f ∘ₗ W) :=
  fun x hx => by
    have h1 := hW.form_le x
    rw [hx, levelForm_self] at h1
    exact hf _ (le_antisymm h1 (levelEnergy_nonneg ha s n _))
private theorem IsMarginal.lower {V : Type} [AddCommGroup V] [Module ℝ V] {E₀ : V → ℝ} {s n : ℕ} [NeZero n]
    {W : V →ₗ[ℝ] LevelChain L (s + 1) n} (ha : 0 ≤ a) (hW : IsMarginal E₀ (levelForm a (s + 1) n) W) :
    IsMarginal E₀ (levelForm a s (n * L)) (lowerLinear s n ∘ₗ W) where
  form_le x := by
    have h1 := hW.form_le x
    rw [levelForm_self, levelEnergy_succ] at h1
    have h2 : 0 ≤ a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect (W x) e c ^ 2 :=
      mul_nonneg ha (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [levelForm_self]
    show levelEnergy a s (n * L) (chainLower (W x)) ≤ E₀ x
    linarith
  exists_eq w' := by
    let w : LevelChain L (s + 1) n := attachTop w' fun e c => _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) w' e) c
    obtain ⟨x, hx, hxe⟩ := hW.exists_eq w
    refine ⟨x, ?_, ?_⟩
    · show chainLower (W x) = w'
      rw [hx]
      rfl
    · rw [hxe, levelForm_self, levelForm_self, levelEnergy_succ]
      have : ∀ (c : TorusBond n) (e : Fin 3), chainDefect w e c = 0 := fun c e => by
        show _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) w' e) c - _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) w' e) c = 0
        exact sub_self _
      simp [this, w, chainLower_attachTop]
private theorem isMarginal_id (a : ℝ) (s n : ℕ) [NeZero n] : IsMarginal (levelEnergy a s n) (levelForm a s n)
    (LinearMap.id : LevelChain L s n →ₗ[ℝ] LevelChain L s n) where
  form_le x := (levelForm_self a s n x).le
  exists_eq w := ⟨w, rfl, (levelForm_self a s n w).symm⟩
private def stepLinear (a ρ : ℝ) (s n : ℕ) [NeZero n] : LevelChain L (s + 1) n →ₗ[ℝ] ColourForm (n * L) :=
  topLinear s (n * L) ∘ₗ lowerLinear s n - pushLinear a ρ s n ∘ₗ topLinear (s + 1) n
private def pushedTop (a ρ : ℝ) (s n : ℕ) [NeZero n] : LevelChain L (s + 1) n →ₗ[ℝ] ColourForm (n * L) :=
  pushLinear a ρ s n ∘ₗ topLinear (s + 1) n
private def curlPushed (a ρ : ℝ) (s n : ℕ) [NeZero n] (e : Fin 3) (p : TorusPlaquette (n * L)) :
    LevelChain L (s + 1) n →ₗ[ℝ] ℝ :=
  curlFunctional e p ∘ₗ pushedTop a ρ s n
private def curlStep (a ρ : ℝ) (s n : ℕ) [NeZero n] (e : Fin 3) (p : TorusPlaquette (n * L)) :
    LevelChain L (s + 1) n →ₗ[ℝ] ℝ :=
  curlFunctional e p ∘ₗ stepLinear a ρ s n
private def fitPushed (a ρ : ℝ) (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusBond n) :
    LevelChain L (s + 1) n →ₗ[ℝ] ℝ :=
  contourFunctional e c ∘ₗ pushedTop a ρ s n - evalFunctional e c ∘ₗ topLinear (s + 1) n
private def contourStep (a ρ : ℝ) (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusBond n) :
    LevelChain L (s + 1) n →ₗ[ℝ] ℝ :=
  contourFunctional e c ∘ₗ stepLinear a ρ s n
section Annihilation
variable {s n : ℕ} [NeZero n]
private theorem curl_sub {m : ℕ} (A B : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (A - B) p = curl A p - curl B p := by
  simp only [curl, Pi.sub_apply]
  ring
private theorem annihilates_curlPushed (F : ScaleFlowBounds a ρ cK L n₀) (hn : n₀ ≤ n) (e : Fin 3)
    (p : TorusPlaquette (n * L)) : Annihilates (levelEnergy a (s + 1) n) (curlPushed (L := L) a ρ s n e p) :=
  fun X hX => by
    have h1 := maxwellForm_top_eq_zero F hn hX e
    exact curl_eq_zero_of_form F s (F.le_mul_side hn) (pushed_of_form_eq_zero (ρ := ρ) F hn h1).1 p
private theorem annihilates_fitPushed (F : ScaleFlowBounds a ρ cK L n₀) (hn : n₀ ≤ n) (e : Fin 3) (c : TorusBond n) :
    Annihilates (levelEnergy a (s + 1) n) (fitPushed (L := L) a ρ s n e c) := fun X hX => by
  have h1 := maxwellForm_top_eq_zero F hn hX e
  exact (pushed_of_form_eq_zero (ρ := ρ) F hn h1).2 c
private theorem annihilates_curlStep (F : ScaleFlowBounds a ρ cK L n₀) (hn : n₀ ≤ n) (e : Fin 3)
    (p : TorusPlaquette (n * L)) : Annihilates (levelEnergy a (s + 1) n) (curlStep (L := L) a ρ s n e p) :=
  fun X hX => by
    have h1 := maxwellForm_top_eq_zero F hn hX e
    have h2 := curl_eq_zero_of_form F s (F.le_mul_side hn) (pushed_of_form_eq_zero (ρ := ρ) F hn h1).1 p
    have h3 := curl_eq_zero_of_form F s (F.le_mul_side hn)
      (maxwellForm_top_eq_zero F (F.le_mul_side hn) (levelEnergy_lower_eq_zero F hX) e) p
    show curl (chainTop s (n * L) (chainLower X) e - responseMap a ρ L s (chainTop (s + 1) n X e)) p = 0
    rw [curl_sub, h2, h3, sub_zero]
private theorem contourAverage_sub (A B : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (A - B) c = _root_.YangMills.Construction.MomentLaw.contourAverage L A c - _root_.YangMills.Construction.MomentLaw.contourAverage L B c := by
  have h1 := contourAverage_add (L := L) (A - B) B c
  rw [sub_add_cancel] at h1
  linarith
private theorem chainDefect_split (a ρ : ℝ) (X : LevelChain L (s + 1) n) (e : Fin 3) (c : TorusBond n) :
    chainDefect X e c = -(fitPushed (L := L) a ρ s n e c X + contourStep (L := L) a ρ s n e c X) := by
  show chainTop (s + 1) n X e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) (chainLower X) e) c =
    -(_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L s (chainTop (s + 1) n X e)) c - chainTop (s + 1) n X e c +
      _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) (chainLower X) e - responseMap a ρ L s (chainTop (s + 1) n X e)) c)
  rw [contourAverage_sub]
  ring
private theorem curl_lower_split (a ρ : ℝ) (X : LevelChain L (s + 1) n) (e : Fin 3) (p : TorusPlaquette (n * L)) :
    curl (chainTop s (n * L) (chainLower X) e) p =
      curlPushed (L := L) a ρ s n e p X + curlStep (L := L) a ρ s n e p X := by
  show _ = curl (responseMap a ρ L s (chainTop (s + 1) n X e)) p +
    curl (chainTop s (n * L) (chainLower X) e - responseMap a ρ L s (chainTop (s + 1) n X e)) p
  rw [curl_sub]
  ring
private theorem annihilates_contourStep (F : ScaleFlowBounds a ρ cK L n₀) (hn : n₀ ≤ n) (e : Fin 3) (c : TorusBond n) :
    Annihilates (levelEnergy a (s + 1) n) (contourStep (L := L) a ρ s n e c) := fun X hX => by
  have h1 := chainDefect_split (L := L) a ρ X e c
  rw [chainDefect_eq_zero F hX, annihilates_fitPushed F hn e c X hX, zero_add] at h1
  linarith
private theorem chainTop_lower_pushedChain (a ρ : ℝ) (A : ColourForm n) :
    chainTop s (n * L) (chainLower (pushedChain (L := L) a ρ (s + 1) n A)) = pushColours a ρ L s A :=
  chainTop_pushedChain a ρ s (n * L) _
private theorem stepLinear_pushedChain (a ρ : ℝ) (A : ColourForm n) :
    stepLinear (L := L) a ρ s n (pushedChain (L := L) a ρ (s + 1) n A) = 0 := by
  show chainTop s (n * L) (chainLower (pushedChain (L := L) a ρ (s + 1) n A)) -
    pushColours a ρ L s (chainTop (s + 1) n (pushedChain (L := L) a ρ (s + 1) n A)) = 0
  rw [chainTop_lower_pushedChain, chainTop_pushedChain, sub_self]
private theorem curlStep_pushedChain (a ρ : ℝ) (e : Fin 3) (p : TorusPlaquette (n * L)) (A : ColourForm n) :
    curlStep (L := L) a ρ s n e p (pushedChain (L := L) a ρ (s + 1) n A) = 0 := by
  simp only [curlStep, LinearMap.comp_apply, stepLinear_pushedChain, map_zero]
private theorem contourStep_pushedChain (a ρ : ℝ) (e : Fin 3) (c : TorusBond n) (A : ColourForm n) :
    contourStep (L := L) a ρ s n e c (pushedChain (L := L) a ρ (s + 1) n A) = 0 := by
  simp only [contourStep, LinearMap.comp_apply, stepLinear_pushedChain, map_zero]
private theorem curlPushed_top (a ρ : ℝ) (e : Fin 3) (p : TorusPlaquette (n * L)) (X : LevelChain L (s + 1) n) :
    curlPushed (L := L) a ρ s n e p (pushedChain (L := L) a ρ (s + 1) n (chainTop (s + 1) n X)) =
      curlPushed (L := L) a ρ s n e p X := by
  show curl (responseMap a ρ L s (chainTop (s + 1) n
    (pushedChain (L := L) a ρ (s + 1) n (chainTop (s + 1) n X)) e)) p = _
  rw [chainTop_pushedChain]
  rfl
private theorem fitPushed_top (a ρ : ℝ) (e : Fin 3) (c : TorusBond n) (X : LevelChain L (s + 1) n) :
    fitPushed (L := L) a ρ s n e c (pushedChain (L := L) a ρ (s + 1) n (chainTop (s + 1) n X)) =
      fitPushed (L := L) a ρ s n e c X := by
  show _root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L s (chainTop (s + 1) n
      (pushedChain (L := L) a ρ (s + 1) n (chainTop (s + 1) n X)) e)) c -
    chainTop (s + 1) n (pushedChain (L := L) a ρ (s + 1) n (chainTop (s + 1) n X)) e c = _
  rw [chainTop_pushedChain]
  rfl
end Annihilation
private def stepIncrement (a : ℝ) (s n : ℕ) [NeZero n] (q : BondBilinear (n * L)) (q' : BondBilinear n)
    (hc : TorusBond n → ℝ) (X : LevelChain L (s + 1) n) : ℝ :=
  1 / 2 * colourEval q (chainTop s (n * L) (chainLower X)) (chainTop s (n * L) (chainLower X)) +
    a * ∑ c : TorusBond n, hc c * (1 / 2 * ∑ e : Fin 3, chainDefect X e c ^ 2 - 3 / (2 * a)) -
    1 / 2 * colourEval q' (chainTop (s + 1) n X) (chainTop (s + 1) n X)
private def stepExpansion (a ρ : ℝ) (s n : ℕ) [NeZero n] (κ : TorusPlaquette (n * L) → TorusPlaquette (n * L) → ℝ)
    (hc : TorusBond n → ℝ) (X : LevelChain L (s + 1) n) : ℝ :=
  (∑ e : Fin 3,
    (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        κ p p' / 2 * (curlPushed (L := L) a ρ s n e p X * curlStep (L := L) a ρ s n e p' X) +
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        κ p p' / 2 * (curlPushed (L := L) a ρ s n e p' X * curlStep (L := L) a ρ s n e p X) +
      ∑ c : TorusBond n, (a * hc c) * (fitPushed (L := L) a ρ s n e c X * contourStep (L := L) a ρ s n e c X) +
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        κ p p' / 2 * (curlStep (L := L) a ρ s n e p X * curlStep (L := L) a ρ s n e p' X) +
      ∑ c : TorusBond n, (a / 2 * hc c) *
        (contourStep (L := L) a ρ s n e c X * contourStep (L := L) a ρ s n e c X))) +
    -(3 / 2 * ∑ c : TorusBond n, hc c)
private theorem stepIncrement_eq (a ρ : ℝ) (ha : a ≠ 0) (s n : ℕ) [NeZero n] (q : BondBilinear (n * L))
    (q' : BondBilinear n) (hc : TorusBond n → ℝ) (κ : TorusPlaquette (n * L) → TorusPlaquette (n * L) → ℝ)
    (hκ : ∀ A A' : TorusBond (n * L) → ℝ, bilinearEval q A A' =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))), κ p p' * curl A p * curl A' p')
    (hrec : ∀ A : TorusBond n → ℝ, bilinearEval q' A A =
      bilinearEval q (responseMap a ρ L s A) (responseMap a ρ L s A) +
      a * ∑ c : TorusBond n, hc c * (contourAverage L (responseMap a ρ L s A) c - A c) ^ 2)
    (X : LevelChain L (s + 1) n) : stepIncrement a s n q q' hc X = stepExpansion a ρ s n κ hc X := by
  set P := plaquettesIn (Finset.univ : Finset (TorusSite (n * L)))
  set G := fun e p => curlPushed (L := L) a ρ s n e p X with hG
  set Dd := fun e p => curlStep (L := L) a ρ s n e p X with hD
  set Fi := fun e c => fitPushed (L := L) a ρ s n e c X with hF
  set Bb := fun e c => contourStep (L := L) a ρ s n e c X with hB
  have h1 : ∀ e, bilinearEval q (chainTop s (n * L) (chainLower X) e) (chainTop s (n * L) (chainLower X) e) =
      ∑ p ∈ P, ∑ p' ∈ P, κ p p' * (G e p + Dd e p) * (G e p' + Dd e p') := fun e => by
    rw [hκ]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => by
      rw [curl_lower_split a ρ X e p, curl_lower_split a ρ X e p']
  have h2 : ∀ e, bilinearEval q' (chainTop (s + 1) n X e) (chainTop (s + 1) n X e) =
      ∑ p ∈ P, ∑ p' ∈ P, κ p p' * G e p * G e p' + a * ∑ c : TorusBond n, hc c * Fi e c ^ 2 := fun e => by
    rw [hrec, hκ]
    rfl
  have h3 : a * ∑ c : TorusBond n, hc c * (1 / 2 * ∑ e : Fin 3, chainDefect X e c ^ 2 - 3 / (2 * a)) =
      ∑ e : Fin 3, (a / 2 * ∑ c : TorusBond n, hc c * (Fi e c + Bb e c) ^ 2) +
        -(3 / 2 * ∑ c : TorusBond n, hc c) := by
    have e1 : ∀ c : TorusBond n, a * (hc c * (1 / 2 * ∑ e : Fin 3, chainDefect X e c ^ 2 - 3 / (2 * a))) =
        ∑ e : Fin 3, a / 2 * (hc c * (Fi e c + Bb e c) ^ 2) + -(3 / 2 * hc c) := fun c => by
      have e2 : ∑ e : Fin 3, chainDefect X e c ^ 2 = ∑ e : Fin 3, (Fi e c + Bb e c) ^ 2 :=
        Finset.sum_congr rfl fun e _ => by rw [chainDefect_split a ρ X e c]; ring
      have e3 : ∑ e : Fin 3, a / 2 * (hc c * (Fi e c + Bb e c) ^ 2) =
          a / 2 * hc c * ∑ e : Fin 3, (Fi e c + Bb e c) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
      rw [e2, e3]
      field_simp
      ring
    rw [Finset.mul_sum, Finset.sum_congr rfl fun c _ => e1 c, Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.mul_sum, Finset.sum_neg_distrib]
  have h4 : ∀ e, 1 / 2 * bilinearEval q (chainTop s (n * L) (chainLower X) e)
        (chainTop s (n * L) (chainLower X) e) +
      a / 2 * ∑ c : TorusBond n, hc c * (Fi e c + Bb e c) ^ 2 -
      1 / 2 * bilinearEval q' (chainTop (s + 1) n X e) (chainTop (s + 1) n X e) =
      ∑ p ∈ P, ∑ p' ∈ P, κ p p' / 2 * (G e p * Dd e p') + ∑ p ∈ P, ∑ p' ∈ P, κ p p' / 2 * (G e p' * Dd e p) +
        ∑ c : TorusBond n, (a * hc c) * (Fi e c * Bb e c) + ∑ p ∈ P, ∑ p' ∈ P, κ p p' / 2 * (Dd e p * Dd e p') +
        ∑ c : TorusBond n, (a / 2 * hc c) * (Bb e c * Bb e c) := fun e => by
    rw [h1, h2]
    have t1 : ∑ p ∈ P, ∑ p' ∈ P, κ p p' * (G e p + Dd e p) * (G e p' + Dd e p') =
        ∑ p ∈ P, ∑ p' ∈ P, κ p p' * G e p * G e p' + 2 * ∑ p ∈ P, ∑ p' ∈ P, κ p p' / 2 * (G e p * Dd e p') +
          2 * ∑ p ∈ P, ∑ p' ∈ P, κ p p' / 2 * (G e p' * Dd e p) +
          2 * ∑ p ∈ P, ∑ p' ∈ P, κ p p' / 2 * (Dd e p * Dd e p') := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => by ring
    have t2 : a / 2 * ∑ c : TorusBond n, hc c * (Fi e c + Bb e c) ^ 2 =
        a / 2 * ∑ c : TorusBond n, hc c * Fi e c ^ 2 +
        ∑ c : TorusBond n, (a * hc c) * (Fi e c * Bb e c) +
        ∑ c : TorusBond n, (a / 2 * hc c) * (Bb e c * Bb e c) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [t1, t2]
    ring
  unfold stepIncrement stepExpansion
  show 1 / 2 * ∑ e : Fin 3, bilinearEval q (chainTop s (n * L) (chainLower X) e)
      (chainTop s (n * L) (chainLower X) e) +
    a * ∑ c : TorusBond n, hc c * (1 / 2 * ∑ e : Fin 3, chainDefect X e c ^ 2 - 3 / (2 * a)) -
    1 / 2 * ∑ e : Fin 3, bilinearEval q' (chainTop (s + 1) n X e) (chainTop (s + 1) n X e) = _
  rw [h3, ← Finset.sum_congr rfl fun e _ => h4 e]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
variable {V : Type} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V] {E₀ : V → ℝ} {μ : Measure V}
private def IsUncorrelatedWith (a ρ : ℝ) {I : Type} (H : I → V →ₗ[ℝ] ℝ) (μ : Measure V) (s n : ℕ) [NeZero n]
    (W : V →ₗ[ℝ] LevelChain L s n) : Prop :=
  ∀ f : LevelChain L s n →ₗ[ℝ] ℝ, Annihilates (levelEnergy a s n) f →
    (∀ A, f (pushedChain (L := L) a ρ s n A) = 0) → ∀ i, cov[H i, f ∘ₗ W; μ] = 0
private theorem IsUncorrelatedWith.lower {I : Type} {H : I → V →ₗ[ℝ] ℝ} (F : ScaleFlowBounds a ρ cK L n₀) {s n : ℕ}
    [NeZero n] {W : V →ₗ[ℝ] LevelChain L (s + 1) n} (hU : IsUncorrelatedWith (L := L) a ρ H μ (s + 1) n W) :
    IsUncorrelatedWith (L := L) a ρ H μ s (n * L) (lowerLinear s n ∘ₗ W) := fun f hf hf0 i =>
  hU (f ∘ₗ lowerLinear s n) (fun X hX => hf _ (levelEnergy_lower_eq_zero F hX)) (fun A => hf0 _) i
private theorem hasMeanOnSets_stepIncrement (F : ScaleFlowBounds a ρ cK L n₀) (h : IsCanonicalGaussian E₀ μ)
    (hE : ∀ x, 0 ≤ E₀ x) (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) {I : Type} (H : I → V →ₗ[ℝ] ℝ)
    (hH : ∀ i, Annihilates E₀ (H i)) {s n : ℕ} [NeZero n] (hn : n₀ ≤ n) (q : BondBilinear (n * L))
    (q' : BondBilinear n) (hc : TorusBond n → ℝ) (κ : TorusPlaquette (n * L) → TorusPlaquette (n * L) → ℝ)
    (hκ : ∀ A A' : TorusBond (n * L) → ℝ, bilinearEval q A A' =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))), κ p p' * curl A p * curl A' p')
    (hrec : ∀ A : TorusBond n → ℝ, bilinearEval q' A A =
      bilinearEval q (responseMap a ρ L s A) (responseMap a ρ L s A) +
      a * ∑ c : TorusBond n, hc c * (contourAverage L (responseMap a ρ L s A) c - A c) ^ 2)
    {W : V →ₗ[ℝ] LevelChain L (s + 1) n} (hW : IsMarginal E₀ (levelForm a (s + 1) n) W)
    (hU : IsUncorrelatedWith (L := L) a ρ H μ (s + 1) n W) :
    HasMeanOnSets (fun S => MeasurableSet[generated H] S) μ fun x => stepIncrement a s n q q' hc (W x) := by
  have := h.isProbabilityMeasure
  have ha := F.a_pos
  have kg := fun e p => hW.comp_annihilates ha.le (annihilates_curlPushed (s := s) (ρ := ρ) F hn e p)
  have kf := fun e c => hW.comp_annihilates ha.le (annihilates_fitPushed (s := s) (ρ := ρ) F hn e c)
  have kd := fun e p => hW.comp_annihilates ha.le (annihilates_curlStep (s := s) (ρ := ρ) F hn e p)
  have kb := fun e c => hW.comp_annihilates ha.le (annihilates_contourStep (s := s) (ρ := ρ) F hn e c)
  have cov_t := fun {g f : LevelChain L (s + 1) n →ₗ[ℝ] ℝ} (hg) (hf) (hgt) (hf0) =>
    covariance_top_eq_zero (ρ := ρ) (g := g) (f := f) F h hE hm hn hW hg hf hgt hf0
  have mean_pair : ∀ {α β : V →ₗ[ℝ] ℝ}, Annihilates E₀ α → Annihilates E₀ β → cov[α, β; μ] = 0 →
      (∀ i, cov[H i, β; μ] = 0) →
      HasMeanOnSets (fun S => MeasurableSet[generated H] S) μ fun x => α x * β x := fun hα hβ c₁ c₂ =>
    ⟨(memLp_of_annihilates h hα (hm _) 2 (by norm_num)).integrable_mul
      (memLp_of_annihilates h hβ (hm _) 2 (by norm_num)), 0,
      fun S hS => by rw [setIntegral_mul_of_uncorrelated h hm H hH hα hβ c₁ c₂ hS, mul_zero]⟩
  have mean_sq : ∀ {β β' : V →ₗ[ℝ] ℝ}, Annihilates E₀ β → Annihilates E₀ β' → (∀ i, cov[H i, β; μ] = 0) →
      (∀ i, cov[H i, β'; μ] = 0) →
      HasMeanOnSets (fun S => MeasurableSet[generated H] S) μ fun x => β x * β' x := fun hβ hβ' c₁ c₂ =>
    ⟨(memLp_of_annihilates h hβ (hm _) 2 (by norm_num)).integrable_mul
      (memLp_of_annihilates h hβ' (hm _) 2 (by norm_num)), _,
      fun S hS => setIntegral_mul_of_independent h hm H hH hβ hβ' c₁ c₂ hS⟩
  have ud := fun e p => hU _ (annihilates_curlStep (s := s) (ρ := ρ) F hn e p) (curlStep_pushedChain a ρ e p)
  have ub := fun e c => hU _ (annihilates_contourStep (s := s) (ρ := ρ) F hn e c) (contourStep_pushedChain a ρ e c)
  obtain ⟨-⟩ := (⟨⟩ : True)
  have hT : HasMeanOnSets (fun S => MeasurableSet[generated H] S) μ fun x => stepExpansion a ρ s n κ hc (W x) := by
    refine HasMeanOnSets.add (HasMeanOnSets.sum _ _ fun e _ => ?_) (HasMeanOnSets.const _)
    refine HasMeanOnSets.add (HasMeanOnSets.add (HasMeanOnSets.add (HasMeanOnSets.add ?_ ?_) ?_) ?_) ?_
    · refine HasMeanOnSets.sum _ _ fun p _ => HasMeanOnSets.sum _ _ fun p' _ => HasMeanOnSets.const_mul _ ?_
      exact mean_pair (kg e p) (kd e p') (cov_t (annihilates_curlPushed F hn e p) (annihilates_curlStep F hn e p')
        (curlPushed_top a ρ e p) (curlStep_pushedChain a ρ e p')) (ud e p')
    · refine HasMeanOnSets.sum _ _ fun p _ => HasMeanOnSets.sum _ _ fun p' _ => HasMeanOnSets.const_mul _ ?_
      exact mean_pair (kg e p') (kd e p) (cov_t (annihilates_curlPushed F hn e p') (annihilates_curlStep F hn e p)
        (curlPushed_top a ρ e p') (curlStep_pushedChain a ρ e p)) (ud e p)
    · refine HasMeanOnSets.sum _ _ fun c _ => HasMeanOnSets.const_mul _ ?_
      exact mean_pair (kf e c) (kb e c) (cov_t (annihilates_fitPushed F hn e c) (annihilates_contourStep F hn e c)
        (fitPushed_top a ρ e c) (contourStep_pushedChain a ρ e c)) (ub e c)
    · refine HasMeanOnSets.sum _ _ fun p _ => HasMeanOnSets.sum _ _ fun p' _ => HasMeanOnSets.const_mul _ ?_
      exact mean_sq (kd e p) (kd e p') (ud e p) (ud e p')
    · refine HasMeanOnSets.sum _ _ fun c _ => HasMeanOnSets.const_mul _ ?_
      exact mean_sq (kb e c) (kb e c) (ub e c) (ub e c)
  have e : (fun x => stepIncrement a s n q q' hc (W x)) = fun x => stepExpansion a ρ s n κ hc (W x) :=
    funext fun x => stepIncrement_eq a ρ ha.ne' s n q q' hc κ hκ hrec (W x)
  rw [e]
  exact hT
end Pushed
section Levels
variable {L : ℕ} [NeZero L] {a ρ cK : ℝ} {n₀ : ℕ}
private structure LevelBounds (a ρ : ℝ) (L n₀ : ℕ) [NeZero L] (Good : ℕ → ℕ → Prop)
    (w : ∀ m, PlaquetteWeight m) (Qf : ∀ (u n : ℕ) [NeZero n], BondBilinear n) : Prop where
  lower : ∀ s n, Good (s + 1) n → Good s (n * L)
  side_ge : ∀ s n, Good s n → n₀ ≤ n
  represent : ∀ (s n : ℕ) [NeZero n], Good s n → ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ,
    ∀ A A' : TorusBond n → ℝ,
    bilinearEval (Qf s n) A A' = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), κ p p' * curl A p * curl A' p'
  recursion : ∀ (s n : ℕ) [NeZero n], Good (s + 1) n → ∀ A : TorusBond n → ℝ,
    bilinearEval (Qf (s + 1) n) A A =
      bilinearEval (Qf s (n * L)) (responseMap a ρ L s A) (responseMap a ρ L s A) +
      a * ∑ c : TorusBond n, bondBlockMean L (s + 1) n (w _) c *
        (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L s A) c - A c) ^ 2
  initial : ∀ (n : ℕ) [NeZero n], Good 0 n → ∀ X : ColourForm n,
    1 / 2 * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), w n p * curlNorm X p ^ 2 =
      1 / 2 * colourEval (Qf 0 n) X X
private def remainder (a : ℝ) (w : ∀ m, PlaquetteWeight m) (Qf : ∀ (u n : ℕ) [NeZero n], BondBilinear n)
    (s n : ℕ) [NeZero n] (X : LevelChain L s n) : ℝ :=
  completedObservable a s n (w _) X - 1 / 2 * colourEval (Qf s n) (chainTop s n X) (chainTop s n X)
private theorem remainder_succ (a : ℝ) (w : ∀ m, PlaquetteWeight m) (Qf : ∀ (u n : ℕ) [NeZero n], BondBilinear n)
    (s n : ℕ) [NeZero n] (X : LevelChain L (s + 1) n) :
    remainder a w Qf (s + 1) n X = remainder a w Qf s (n * L) (chainLower X) +
      stepIncrement a s n (Qf s (n * L)) (Qf (s + 1) n) (bondBlockMean L (s + 1) n (w _)) X := by
  have e : completedObservable a (s + 1) n (w _) X = completedObservable a s (n * L) (w _) (chainLower X) +
      a * ∑ c : TorusBond n, bondBlockMean L (s + 1) n (w _) c *
        (1 / 2 * ∑ e : Fin 3, chainDefect X e c ^ 2 - 3 / (2 * a)) := rfl
  unfold remainder stepIncrement
  rw [e]
  ring
variable {V : Type} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V] {E₀ : V → ℝ} {μ : Measure V}
private theorem hasMeanOnSets_remainder (F : ScaleFlowBounds a ρ cK L n₀) (h : IsCanonicalGaussian E₀ μ)
    (hE : ∀ x, 0 ≤ E₀ x) (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) {I : Type} (H : I → V →ₗ[ℝ] ℝ)
    (hH : ∀ i, Annihilates E₀ (H i)) {Good : ℕ → ℕ → Prop} {w : ∀ m, PlaquetteWeight m}
    {Qf : ∀ (u n : ℕ) [NeZero n], BondBilinear n} (Lv : LevelBounds a ρ L n₀ Good w Qf) :
    ∀ (s n : ℕ) [NeZero n], Good s n → ∀ W : V →ₗ[ℝ] LevelChain L s n,
      IsMarginal E₀ (levelForm a s n) W → IsUncorrelatedWith (L := L) a ρ H μ s n W →
      HasMeanOnSets (fun S => MeasurableSet[generated H] S) μ fun x => remainder a w Qf s n (W x) := by
  have := h.isProbabilityMeasure
  intro s
  induction s with
  | zero =>
    intro n _ hG W _ _
    have e : (fun x => remainder (L := L) a w Qf 0 n (W x)) = fun _ => 0 := by
      funext x
      have := Lv.initial n hG (W x)
      unfold remainder
      simp only [completedObservable]
      show 1 / 2 * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), w _ p * curlNorm (W x) p ^ 2 -
        1 / 2 * colourEval (Qf 0 n) (W x) (W x) = 0
      exact sub_eq_zero.2 this
    rw [e]
    exact HasMeanOnSets.const 0
  | succ s ih =>
    intro n _ hG W hW hU
    obtain ⟨κ, hκ⟩ := Lv.represent s (n * L) (Lv.lower s n hG)
    have e : (fun x => remainder a w Qf (s + 1) n (W x)) =
        fun x => remainder a w Qf s (n * L) ((lowerLinear s n ∘ₗ W) x) +
        stepIncrement a s n (Qf s (n * L)) (Qf (s + 1) n) (bondBlockMean L (s + 1) n (w _)) (W x) :=
      funext fun x => remainder_succ a w Qf s n (W x)
    rw [e]
    exact (ih (n * L) (Lv.lower s n hG) _ (hW.lower F.a_pos.le) (hU.lower F)).add
      (hasMeanOnSets_stepIncrement F h hE hm H hH (Lv.side_ge _ _ hG) _ _ _ κ hκ (Lv.recursion s n hG) hW hU)
end Levels
section Moments
variable {Ω : Type} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
private def HasAllMoments (μ : Measure Ω) (f : Ω → ℝ) : Prop := ∀ p : ℕ, MemLp f p μ
private theorem HasAllMoments.add {f g : Ω → ℝ} (hf : HasAllMoments μ f) (hg : HasAllMoments μ g) :
    HasAllMoments μ fun x => f x + g x :=
  fun p => (hf p).add (hg p)
private theorem HasAllMoments.const [IsFiniteMeasure μ] (c : ℝ) : HasAllMoments μ fun _ => c :=
  fun _ => memLp_const c
private theorem HasAllMoments.mul {f g : Ω → ℝ} (hf : HasAllMoments μ f) (hg : HasAllMoments μ g) :
    HasAllMoments μ fun x => f x * g x := fun p => by
  have h1 := hf (2 * p)
  have h2 := hg (2 * p)
  haveI : ENNReal.HolderTriple ((2 * p : ℕ) : ENNReal) ((2 * p : ℕ) : ENNReal) (p : ENNReal) := ⟨by
    have e : (((2 * p : ℕ) : ENNReal))⁻¹ = 2⁻¹ * (p : ENNReal)⁻¹ := by
      push_cast
      exact ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)
    rw [e, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
  exact h2.mul' h1
private theorem HasAllMoments.const_mul {f : Ω → ℝ} [IsFiniteMeasure μ] (c : ℝ) (hf : HasAllMoments μ f) :
    HasAllMoments μ fun x => c * f x :=
  (HasAllMoments.const c).mul hf
private theorem HasAllMoments.sum [IsFiniteMeasure μ] {ι : Type} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, HasAllMoments μ (f i)) : HasAllMoments μ fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAllMoments.const (μ := μ) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
private theorem HasAllMoments.prod [IsFiniteMeasure μ] {ι : Type} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, HasAllMoments μ (f i)) : HasAllMoments μ fun x => ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAllMoments.const (μ := μ) 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
private theorem HasAllMoments.integrable {f : Ω → ℝ} (hf : HasAllMoments μ f) : Integrable f μ := by
  have := hf 1
  simpa using memLp_one_iff_integrable.1 (by simpa using this)
private theorem HasAllMoments.aestronglyMeasurable {f : Ω → ℝ} (hf : HasAllMoments μ f) :
    AEStronglyMeasurable f μ := hf.integrable.aestronglyMeasurable
private theorem integral_mul_prod_centred [IsProbabilityMeasure μ] {k : ℕ} {Ix : Type} [Fintype Ix]
    [DecidableEq Ix] (O : Fin k → Ω → ℝ) (T : Ix → Ω → ℝ) (wt : Fin k → Ix → ℝ) (m : Ix → MeasurableSpace Ω)
    (hO : ∀ i, HasAllMoments μ (O i)) (hT : ∀ ι, HasAllMoments μ (T ι))
    (hdis : ∀ ι i i', wt i ι ≠ 0 → wt i' ι ≠ 0 → i = i')
    (hmean : ∀ ι i, wt i ι ≠ 0 → ∫ x, T ι x ∂μ = 0)
    (hind : ∀ ι i, wt i ι ≠ 0 → ∀ G : Ω → ℝ, Measurable[m ι] G → IndepFun (T ι) G μ)
    (hOm : ∀ ι i i', wt i ι ≠ 0 → Measurable[m ι] (O i'))
    (hTm : ∀ ι κ i, wt i ι ≠ 0 → κ ≠ ι → Measurable[m ι] (T κ)) (J : Finset (Fin k)) :
    ∀ F : Ω → ℝ, HasAllMoments μ F → (∀ ι i, wt i ι ≠ 0 → Measurable[m ι] F) →
      ∫ x, F x * ∏ i ∈ J, (O i x + ∑ ι, wt i ι * T ι x) ∂μ = ∫ x, F x * ∏ i ∈ J, O i x ∂μ := by
  classical
  have hψ : ∀ i, HasAllMoments μ fun x => O i x + ∑ ι, wt i ι * T ι x := fun i =>
    (hO i).add (HasAllMoments.sum _ fun ι _ => (hT ι).const_mul _)
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    intro F hF hFm
    simp only [Finset.prod_insert hj]
    let R : Ω → ℝ := fun x => ∏ i ∈ J, (O i x + ∑ ι, wt i ι * T ι x)
    have hRm : HasAllMoments μ R := HasAllMoments.prod _ fun i _ => hψ i
    have e1 : ∀ x, F x * ((O j x + ∑ ι, wt j ι * T ι x) * R x) =
        (F x * O j x) * R x + ∑ ι, wt j ι * (T ι x * (F x * R x)) := fun x => by
      rw [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun ι _ => by ring
    have e0 : ∫ x, F x * ((O j x + ∑ ι, wt j ι * T ι x) * ∏ i ∈ J, (O i x + ∑ ι, wt i ι * T ι x)) ∂μ =
        ∫ x, ((F x * O j x) * R x + ∑ ι, wt j ι * (T ι x * (F x * R x))) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => e1 x)
    rw [e0]
    have i₁ : Integrable (fun x => (F x * O j x) * R x) μ := ((hF.mul (hO j)).mul hRm).integrable
    have i₂ : ∀ ι, Integrable (fun x => wt j ι * (T ι x * (F x * R x))) μ := fun ι =>
      (((hT ι).mul (hF.mul hRm)).const_mul _).integrable
    rw [integral_add i₁ (integrable_finset_sum _ fun ι _ => i₂ ι), integral_finset_sum _ fun ι _ => i₂ ι]
    have e2 : ∀ ι, ∫ x, wt j ι * (T ι x * (F x * R x)) ∂μ = 0 := fun ι => by
      by_cases hw : wt j ι = 0
      · simp [hw]
      · rw [integral_const_mul]
        have hRι : Measurable[m ι] R := by
          refine Finset.measurable_fun_prod _ fun i hi => ?_
          have hij : i ≠ j := fun e => hj (e ▸ hi)
          have h0 : wt i ι = 0 := by
            by_contra hne
            exact hij (hdis ι i j hne hw)
          refine (hOm ι j i hw).add (Finset.measurable_fun_sum _ fun κ _ => ?_)
          by_cases hκ : κ = ι
          · subst hκ
            simp [h0, measurable_const]
          · exact (hTm ι κ j hw hκ).const_mul _
        have hG : Measurable[m ι] fun x => F x * R x := (hFm ι j hw).mul hRι
        rw [(hind ι j hw _ hG).integral_fun_mul_eq_mul_integral (hT ι).aestronglyMeasurable
          (hF.mul hRm).aestronglyMeasurable, hmean ι j hw]
        simp
    simp only [e2, Finset.sum_const_zero, add_zero]
    rw [ih (fun x => F x * O j x) (hF.mul (hO j)) fun ι i hw => (hFm ι i hw).mul (hOm ι i j hw)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show F x * O j x * _ = F x * (O j x * _)
      ring)
end Moments
section Noise
variable {L : ℕ} [NeZero L] {a ρ cK : ℝ} {n₀ : ℕ}
@[reducible] private def chainNoiseFintype (L : ℕ) [NeZero L] : (s n : ℕ) → [NeZero n] → Fintype (ChainNoise L s n)
  | 0, n, _ => inferInstanceAs (Fintype (Fin 3 × TorusPlaquette n))
  | s + 1, n, _ => by
    letI := chainNoiseFintype L s (n * L)
    exact inferInstanceAs (Fintype (ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n)))
private instance (s n : ℕ) [NeZero n] : Fintype (ChainNoise L s n) := chainNoiseFintype L s n
private def defectLinear (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusBond n) : LevelChain L (s + 1) n →ₗ[ℝ] ℝ :=
  evalFunctional e c ∘ₗ topLinear (s + 1) n - contourFunctional e c ∘ₗ topLinear s (n * L) ∘ₗ lowerLinear s n
private def noiseFunctional : (s n : ℕ) → [NeZero n] → ChainNoise L s n → LevelChain L s n →ₗ[ℝ] ℝ
  | 0, n, _, i => curlFunctional (show Fin 3 × TorusPlaquette n from i).1
      (show Fin 3 × TorusPlaquette n from i).2 ∘ₗ topLinear 0 n
  | s + 1, n, _, i => Sum.elim (fun j => noiseFunctional s (n * L) j ∘ₗ lowerLinear s n)
      (fun j => defectLinear s n j.1 j.2)
      (show ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n) from i)
private def IsStepNoise : (s n : ℕ) → ChainNoise L s n → Prop
  | 0, _, _ => False
  | s + 1, n, i => Sum.elim (IsStepNoise s (n * L)) (fun _ => True)
      (show ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n) from i)
private def baseNoise : (s n : ℕ) → Fin 3 → TorusPlaquette (fineSide L s n) → ChainNoise L s n
  | 0, _, e, p => (show Fin 3 × TorusPlaquette _ from (e, p))
  | s + 1, n, e, p => (show ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n) from Sum.inl (baseNoise s (n * L) e p))
private theorem not_isStepNoise_baseNoise : ∀ (s n : ℕ) (e : Fin 3) (p : TorusPlaquette (fineSide L s n)),
    ¬ IsStepNoise (L := L) s n (baseNoise s n e p)
  | 0, _, _, _ => id
  | s + 1, n, e, p => not_isStepNoise_baseNoise s (n * L) e p
private theorem noiseFunctional_baseNoise : ∀ (s n : ℕ) [NeZero n] (e : Fin 3)
    (p : TorusPlaquette (fineSide L s n)) (X : LevelChain L s n),
    noiseFunctional s n (baseNoise s n e p) X = curl (chainBottom s n X e) p
  | 0, _, _, _, _, _ => rfl
  | s + 1, n, _, e, p, X => noiseFunctional_baseNoise s (n * L) e p (chainLower X)
private theorem annihilates_noiseFunctional (F : ScaleFlowBounds a ρ cK L n₀) : ∀ (s n : ℕ) [NeZero n], n₀ ≤ n →
    ∀ ι : ChainNoise L s n, Annihilates (levelEnergy a s n) (noiseFunctional s n ι)
  | 0, n, _, hn, i => fun X hX => curl_eq_zero_of_form F 0 hn (maxwellForm_top_eq_zero F hn hX _) _
  | s + 1, n, _, hn, i => by
    revert i
    show ∀ i : ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n),
      Annihilates (levelEnergy a (s + 1) n) (noiseFunctional (s + 1) n i)
    rintro (j | j)
    · exact fun X hX => annihilates_noiseFunctional F s (n * L) (F.le_mul_side hn) j _
        (levelEnergy_lower_eq_zero F hX)
    · exact fun X hX => chainDefect_eq_zero F hX j.1 j.2
open Classical in
private def defectUnit (a : ℝ) (s n : ℕ) (e : Fin 3) (c : TorusBond n) : LevelChain L (s + 1) n :=
  attachTop 0 fun e' c' => if e' = e ∧ c' = c then a⁻¹ else 0
private theorem chainDefect_defectUnit (a : ℝ) (s n : ℕ) [NeZero n] (e e' : Fin 3) (c c' : TorusBond n) :
    chainDefect (defectUnit (L := L) a s n e c) e' c' = open Classical in if e' = e ∧ c' = c then a⁻¹ else 0 := by
  have h0 : chainTop s (n * L) (chainLower (defectUnit (L := L) a s n e c)) = 0 := (topLinear s (n * L)).map_zero
  have h1 : _root_.YangMills.Construction.MomentLaw.contourAverage L ((0 : ColourForm (n * L)) e') c' = 0 := (contourFunctional (L := L) e' c').map_zero
  show chainTop (s + 1) n (defectUnit (L := L) a s n e c) e' c' -
    _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) (chainLower (defectUnit (L := L) a s n e c)) e') c' = _
  rw [h0, h1, sub_zero]
  rfl
private theorem levelForm_defectUnit (ha : a ≠ 0) (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusBond n)
    (X : LevelChain L (s + 1) n) : levelForm a (s + 1) n (defectUnit (L := L) a s n e c) X = chainDefect X e c := by
  classical
  have h0 : levelPairing a s (n * L) (chainLower (defectUnit (L := L) a s n e c)) (chainLower X) = 0 := by
    show levelForm a s (n * L) 0 (chainLower X) = 0
    rw [map_zero]
    rfl
  show levelPairing a s (n * L) (chainLower (defectUnit (L := L) a s n e c)) (chainLower X) +
    a * ∑ c' : TorusBond n, ∑ e' : Fin 3, chainDefect (defectUnit (L := L) a s n e c) e' c' * chainDefect X e' c' = _
  rw [h0, zero_add, Finset.sum_eq_single c, Finset.sum_eq_single e]
  · rw [chainDefect_defectUnit]
    simp [ha]
  · intro e' _ he
    rw [chainDefect_defectUnit]
    simp [he]
  · simp
  · intro c' _ hc
    refine Finset.sum_eq_zero fun e' _ => ?_
    rw [chainDefect_defectUnit]
    simp [hc]
  · simp
variable {V : Type} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V] {E₀ : V → ℝ} {μ : Measure V}
private theorem covariance_levelForm (hA : 0 ≤ a) (h : IsCanonicalGaussian E₀ μ) (hE : ∀ x, 0 ≤ E₀ x)
    (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) {s n : ℕ} [NeZero n] {W : V →ₗ[ℝ] LevelChain L s n}
    (hW : IsMarginal E₀ (levelForm a s n) W) (w : LevelChain L s n) {g : LevelChain L s n →ₗ[ℝ] ℝ}
    (hg : Annihilates (levelEnergy a s n) g) : cov[(levelForm a s n w) ∘ₗ W, g ∘ₗ W; μ] = g w := by
  obtain ⟨wg, hwg⟩ := exists_representing (levelForm a s n) (levelForm_symm a s n) g
    fun x hx => hg x (by rwa [← levelForm_self])
  have eg : g = levelForm a s n wg := LinearMap.ext hwg
  have hc := hW.covariance_eq (levelForm_symm a s n) (levelForm_self_nonneg hA s n) hE h hm w wg
  rw [← eg] at hc
  rw [hc, levelForm_symm, ← hwg]
private theorem defectLinear_eq (ha : a ≠ 0) (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusBond n) :
    (defectLinear (L := L) s n e c) = levelForm a (s + 1) n (defectUnit (L := L) a s n e c) :=
  LinearMap.ext fun X => (levelForm_defectUnit ha s n e c X).symm
private theorem covariance_topNoise (F : ScaleFlowBounds a ρ cK L n₀) (h : IsCanonicalGaussian E₀ μ)
    (hE : ∀ x, 0 ≤ E₀ x) (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) {s n : ℕ} [NeZero n] (hn : n₀ ≤ n)
    {W : V →ₗ[ℝ] LevelChain L (s + 1) n} (hW : IsMarginal E₀ (levelForm a (s + 1) n) W)
    (j : Fin 3 × TorusBond n) (κ : ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n)) (hκ : κ ≠ Sum.inr j) :
    cov[defectLinear (L := L) s n j.1 j.2 ∘ₗ W, noiseFunctional (s + 1) n κ ∘ₗ W; μ] = 0 := by
  rw [defectLinear_eq (a := a) F.a_pos.ne', covariance_levelForm F.a_pos.le h hE hm hW _
    (annihilates_noiseFunctional F (s + 1) n hn κ)]
  rcases κ with i | i
  · show noiseFunctional s (n * L) i (chainLower (defectUnit (L := L) a s n j.1 j.2)) = 0
    exact (noiseFunctional s (n * L) i).map_zero
  · show chainDefect (defectUnit (L := L) a s n j.1 j.2) i.1 i.2 = 0
    rw [chainDefect_defectUnit]
    have : ¬ (i.1 = j.1 ∧ i.2 = j.2) := fun e => hκ (by
      rw [show i = j from Prod.ext e.1 e.2])
    simp [this]
private theorem covariance_noise (F : ScaleFlowBounds a ρ cK L n₀) (h : IsCanonicalGaussian E₀ μ) (hE : ∀ x, 0 ≤ E₀ x)
    (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) : ∀ (s n : ℕ) [NeZero n], n₀ ≤ n → ∀ W : V →ₗ[ℝ] LevelChain L s n,
      IsMarginal E₀ (levelForm a s n) W → ∀ ι κ : ChainNoise L s n, IsStepNoise s n ι → ι ≠ κ →
      cov[noiseFunctional s n ι ∘ₗ W, noiseFunctional s n κ ∘ₗ W; μ] = 0 := by
  intro s
  induction s with
  | zero => intro n _ _ W _ ι κ hι
            exact absurd hι id
  | succ s ih =>
    intro n _ hn W hW
    show ∀ ι κ : ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n), IsStepNoise (s + 1) n ι → ι ≠ κ → _
    rintro (i | i) (j | j) hs hne
    · exact ih (n * L) (F.le_mul_side hn) (lowerLinear s n ∘ₗ W) (hW.lower F.a_pos.le) i j hs
        (fun e => hne (by rw [e]))
    · rw [covariance_comm]
      exact covariance_topNoise F h hE hm hn hW j (Sum.inl i) (by simp)
    · exact covariance_topNoise F h hE hm hn hW i (Sum.inl j) (by simp)
    · exact covariance_topNoise F h hE hm hn hW i (Sum.inr j) (fun e => hne e.symm)
private theorem variance_noise (F : ScaleFlowBounds a ρ cK L n₀) (h : IsCanonicalGaussian E₀ μ) (hE : ∀ x, 0 ≤ E₀ x)
    (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) : ∀ (s n : ℕ) [NeZero n], n₀ ≤ n → ∀ W : V →ₗ[ℝ] LevelChain L s n,
      IsMarginal E₀ (levelForm a s n) W → ∀ ι : ChainNoise L s n, IsStepNoise s n ι →
      Var[noiseFunctional s n ι ∘ₗ W; μ] = a⁻¹ := by
  intro s
  induction s with
  | zero => intro n _ _ W _ ι hι
            exact absurd hι id
  | succ s ih =>
    intro n _ hn W hW
    show ∀ ι : ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n), IsStepNoise (s + 1) n ι → _
    rintro (i | i) hs
    · exact ih (n * L) (F.le_mul_side hn) (lowerLinear s n ∘ₗ W) (hW.lower F.a_pos.le) i hs
    · show Var[defectLinear (L := L) s n i.1 i.2 ∘ₗ W; μ] = a⁻¹
      rw [← covariance_self (hm _).aemeasurable]
      have hk : Annihilates (levelEnergy a (s + 1) n) (defectLinear (L := L) s n i.1 i.2) :=
        annihilates_noiseFunctional F (s + 1) n hn (Sum.inr i)
      conv_lhs => rw [defectLinear_eq (a := a) F.a_pos.ne']
      rw [← defectLinear_eq (a := a) F.a_pos.ne' s n i.1 i.2]
      conv_lhs => arg 1; rw [defectLinear_eq (a := a) F.a_pos.ne']
      rw [covariance_levelForm F.a_pos.le h hE hm hW _ hk]
      show chainDefect (defectUnit (L := L) a s n i.1 i.2) i.1 i.2 = a⁻¹
      rw [chainDefect_defectUnit]
      simp
private def noiseWeight (a : ℝ) (w : ∀ m, PlaquetteWeight m) : (s n : ℕ) → [NeZero n] → ChainNoise L s n → ℝ
  | 0, _, _, _ => 0
  | s + 1, n, _, i => Sum.elim (noiseWeight a w s (n * L)) (fun j => a * bondBlockMean L (s + 1) n (w _) j.2)
      (show ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n) from i)
private theorem isStepNoise_of_weight (a : ℝ) (w : ∀ m, PlaquetteWeight m) :
    ∀ (s n : ℕ) [NeZero n] (ι : ChainNoise L s n), noiseWeight a w s n ι ≠ 0 → IsStepNoise s n ι
  | 0, _, _, _ => fun h => absurd rfl h
  | s + 1, n, _, i => by
    revert i
    show ∀ i : ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n), _
    rintro (j | j) h
    · exact isStepNoise_of_weight a w s (n * L) j h
    · trivial
private theorem sum_chainNoise_succ (s n : ℕ) [NeZero n] (f : ChainNoise L (s + 1) n → ℝ) :
    ∑ ι, f ι = ∑ j : ChainNoise L s (n * L), f (Sum.inl j) + ∑ j : Fin 3 × TorusBond n, f (Sum.inr j) :=
  Fintype.sum_sum_type (α₁ := ChainNoise L s (n * L)) (α₂ := Fin 3 × TorusBond n) f
private theorem completedObservable_eq (a : ℝ) (w : ∀ m, PlaquetteWeight m) :
    ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    completedObservable a s n (w _) X = baseObservable (L := L) (w _) X +
      ∑ ι, noiseWeight a w s n ι * (1 / 2 * noiseFunctional s n ι X ^ 2 - 1 / (2 * a))
  | 0, n, _, X => by
    simp only [noiseWeight, zero_mul, Finset.sum_const_zero, add_zero]
    rfl
  | s + 1, n, _, X => by
    rw [sum_chainNoise_succ]
    have ih := completedObservable_eq a w s (n * L) (chainLower X)
    have e1 : ∀ j : ChainNoise L s (n * L), noiseWeight (L := L) a w (s + 1) n (Sum.inl j) *
        (1 / 2 * noiseFunctional (L := L) (s + 1) n (Sum.inl j) X ^ 2 - 1 / (2 * a)) =
        noiseWeight a w s (n * L) j * (1 / 2 * noiseFunctional s (n * L) j (chainLower X) ^ 2 - 1 / (2 * a)) :=
      fun _ => rfl
    have e2 : ∑ j : Fin 3 × TorusBond n, noiseWeight (L := L) a w (s + 1) n (Sum.inr j) *
        (1 / 2 * noiseFunctional (L := L) (s + 1) n (Sum.inr j) X ^ 2 - 1 / (2 * a)) =
        a * ∑ c : TorusBond n, bondBlockMean L (s + 1) n (w _) c *
          (1 / 2 * ∑ e : Fin 3, chainDefect X e c ^ 2 - 3 / (2 * a)) := by
      rw [Fintype.sum_prod_type_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      show ∑ e : Fin 3, a * bondBlockMean L (s + 1) n (w _) c * (1 / 2 * chainDefect X e c ^ 2 - 1 / (2 * a)) = _
      simp only [Fin.sum_univ_three]
      ring
    rw [Finset.sum_congr rfl fun j _ => e1 j, e2]
    have e0 : completedObservable a (s + 1) n (w _) X = completedObservable a s (n * L) (w _) (chainLower X) +
        a * ∑ c : TorusBond n, bondBlockMean L (s + 1) n (w _) c *
          (1 / 2 * ∑ e : Fin 3, chainDefect X e c ^ 2 - 3 / (2 * a)) := rfl
    rw [e0, ih]
    have e3 : baseObservable (L := L) (s := s + 1) (n := n) (w _) X =
        baseObservable (L := L) (s := s) (n := n * L) (w _) (chainLower X) := rfl
    rw [e3]
    ring
private theorem baseObservable_eq {s n : ℕ} [NeZero n] (h : PlaquetteWeight (fineSide L s n))
    (X : LevelChain L s n) :
    baseObservable (L := L) h X = 1 / 2 * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L s n))),
      h p * ∑ e : Fin 3, noiseFunctional s n (baseNoise s n e p) X ^ 2 := by
  unfold baseObservable
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [noiseFunctional_baseNoise]
private def otherNoises (s n : ℕ) [NeZero n] (W : V →ₗ[ℝ] LevelChain L s n) (ι : ChainNoise L s n) :
    {κ : ChainNoise L s n // κ ≠ ι} → V →ₗ[ℝ] ℝ := fun κ => noiseFunctional s n κ.1 ∘ₗ W
private theorem integral_prod_completed_eq (F : ScaleFlowBounds a ρ cK L n₀) (h : IsCanonicalGaussian E₀ μ)
    (hE : ∀ x, 0 ≤ E₀ x) (hm : ∀ f : V →ₗ[ℝ] ℝ, Measurable f) {s n : ℕ} [NeZero n] (hn : n₀ ≤ n)
    {W : V →ₗ[ℝ] LevelChain L s n} (hW : IsMarginal E₀ (levelForm a s n) W) {k : ℕ}
    (w : Fin k → ∀ m, PlaquetteWeight m)
    (hdis : ∀ (ι : ChainNoise L s n) i i', noiseWeight a (w i) s n ι ≠ 0 → noiseWeight a (w i') s n ι ≠ 0 → i = i')
    (J : Finset (Fin k)) :
    ∫ x, ∏ i ∈ J, completedObservable a s n (w i _) (W x) ∂μ =
      ∫ x, ∏ i ∈ J, baseObservable (L := L) (w i _) (W x) ∂μ := by
  classical
  have := h.isProbabilityMeasure
  have hkn : ∀ ι, Annihilates E₀ (noiseFunctional s n ι ∘ₗ W) := fun ι =>
    hW.comp_annihilates F.a_pos.le (annihilates_noiseFunctional F s n hn ι)
  have hν : ∀ ι, HasAllMoments μ (noiseFunctional s n ι ∘ₗ W) := fun ι p =>
    memLp_of_annihilates h (hkn ι) (hm _) p (by simp)
  have hO : ∀ i, HasAllMoments μ fun x => baseObservable (L := L) (w i _) (W x) := fun i => by
    simp only [baseObservable_eq]
    refine HasAllMoments.const_mul _ (HasAllMoments.sum _ fun p _ =>
      HasAllMoments.const_mul _ (HasAllMoments.sum _ fun e _ => ?_))
    simpa [sq] using (hν (baseNoise s n e p)).mul (hν (baseNoise s n e p))
  have hT : ∀ ι, HasAllMoments μ fun x => 1 / 2 * noiseFunctional s n ι (W x) ^ 2 - 1 / (2 * a) := fun ι => by
    have := (((hν ι).mul (hν ι)).const_mul (1 / 2)).add (HasAllMoments.const (-(1 / (2 * a))))
    simpa [sq, sub_eq_add_neg] using this
  have hfield : ∀ (ι : ChainNoise L s n) (κ : {κ : ChainNoise L s n // κ ≠ ι}),
      Measurable[generated (otherNoises s n W ι)] fun x => noiseFunctional s n κ.1 (W x) := fun ι κ => by
    have h1 : @Measurable V _ (generated (otherNoises s n W ι)) _ (fun x i => otherNoises s n W ι i x) :=
      comap_measurable _
    exact (measurable_pi_apply κ).comp h1
  have hmean : ∀ (ι : ChainNoise L s n) (i : Fin k), noiseWeight a (w i) s n ι ≠ 0 →
      ∫ x, (1 / 2 * noiseFunctional s n ι (W x) ^ 2 - 1 / (2 * a)) ∂μ = 0 := by
    intro ι i hw
    have hs := isStepNoise_of_weight a (w i) s n ι hw
    have hv := variance_noise F h hE hm s n hn W hW ι hs
    have h2 : MemLp (noiseFunctional s n ι ∘ₗ W) 2 μ := memLp_of_annihilates h (hkn ι) (hm _) 2 (by simp)
    have h0 : ∫ x, (noiseFunctional s n ι ∘ₗ W) x ∂μ = 0 := integral_of_annihilates h (hkn ι) (hm _)
    rw [variance_eq_sub h2] at hv
    have h3 : ∫ x, (noiseFunctional s n ι (W x)) ^ 2 ∂μ = a⁻¹ := by
      have e : ∫ x, ((⇑(noiseFunctional s n ι ∘ₗ W)) ^ 2) x ∂μ -
          (∫ x, (noiseFunctional s n ι ∘ₗ W) x ∂μ) ^ 2 = a⁻¹ := hv
      rw [h0] at e
      simpa using e
    have h4 : Integrable (fun x => noiseFunctional s n ι (W x) ^ 2) μ := h2.integrable_sq
    rw [integral_sub (h4.const_mul _) (integrable_const _), integral_const_mul, h3]
    have ha := F.a_pos.ne'
    simp
    field_simp
    norm_num
  have hind : ∀ (ι : ChainNoise L s n) (i : Fin k), noiseWeight a (w i) s n ι ≠ 0 → ∀ G : V → ℝ,
      Measurable[generated (otherNoises s n W ι)] G →
      IndepFun (fun x => 1 / 2 * noiseFunctional s n ι (W x) ^ 2 - 1 / (2 * a)) G μ := by
    intro ι i hw G hG
    have hs := isStepNoise_of_weight a (w i) s n ι hw
    have H1 := indepFun_of_uncorrelated h hm (fun _ : Unit => noiseFunctional s n ι ∘ₗ W) (otherNoises s n W ι)
      (fun _ => hkn ι) (fun κ => hkn κ.1)
      (fun _ κ => covariance_noise F h hE hm s n hn W hW ι κ.1 hs (Ne.symm κ.2))
    let ψ : (Unit → ℝ) → ℝ := fun z => 1 / 2 * z () ^ 2 - 1 / (2 * a)
    have hψ : Measurable ψ := (((measurable_pi_apply ()).pow_const 2).const_mul _).sub_const _
    have H2 : IndepFun (fun x => 1 / 2 * noiseFunctional s n ι (W x) ^ 2 - 1 / (2 * a))
        (fun x κ => otherNoises s n W ι κ x) μ :=
      H1.comp hψ measurable_id
    rw [IndepFun_iff_Indep] at H2 ⊢
    exact indep_of_indep_of_le_right H2 hG.comap_le
  have hOm : ∀ (ι : ChainNoise L s n) (i i' : Fin k), noiseWeight a (w i) s n ι ≠ 0 →
      Measurable[generated (otherNoises s n W ι)] fun x => baseObservable (L := L) (w i' _) (W x) := by
    intro ι i i' hw
    have hs := isStepNoise_of_weight a (w i) s n ι hw
    simp only [baseObservable_eq]
    refine Measurable.const_mul (Finset.measurable_fun_sum _ fun p _ => Measurable.const_mul
      (Finset.measurable_fun_sum _ fun e _ => ?_) _) _
    have hne : baseNoise (L := L) s n e p ≠ ι := fun e' => not_isStepNoise_baseNoise s n e p (e' ▸ hs)
    exact (hfield ι ⟨_, hne⟩).pow_const 2
  have hTm : ∀ (ι κ : ChainNoise L s n) (i : Fin k), noiseWeight a (w i) s n ι ≠ 0 → κ ≠ ι →
      Measurable[generated (otherNoises s n W ι)] fun x => 1 / 2 * noiseFunctional s n κ (W x) ^ 2 - 1 / (2 * a) :=
    fun ι κ i _ hκ => (((hfield ι ⟨κ, hκ⟩).pow_const 2).const_mul _).sub_const _
  have key := integral_mul_prod_centred (μ := μ) (fun i x => baseObservable (L := L) (w i _) (W x))
    (fun ι x => 1 / 2 * noiseFunctional s n ι (W x) ^ 2 - 1 / (2 * a)) (fun i => noiseWeight a (w i) s n)
    (fun ι => generated (otherNoises s n W ι)) hO hT hdis hmean hind hOm hTm J (fun _ => 1)
    (HasAllMoments.const 1) (fun _ _ _ => measurable_const)
  simp only [one_mul] at key
  rw [← key]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    Finset.prod_congr rfl fun i _ => completedObservable_eq a (w i) s n (W x))
end Noise
section Forms
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
private theorem bilinearEval_sum {ι : Type} (s : Finset ι) (q : ι → BondBilinear n) (A A' : TorusBond n → ℝ) :
    bilinearEval (n := n) (fun b b' => ∑ y ∈ s, q y b b') A A' = ∑ y ∈ s, bilinearEval (q y) A A' := by
  simp only [bilinearEval, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
abbrev _root_.YangMills.SharedProofs.p776 := @bilinearEval_sum
private theorem bilinearEval_add (q r : BondBilinear n) (A A' : TorusBond n → ℝ) :
    bilinearEval (n := n) (fun b b' => q b b' + r b b') A A' = bilinearEval q A A' + bilinearEval r A A' := by
  simp only [bilinearEval, mul_add, add_mul, Finset.sum_add_distrib]
private theorem bilinearEval_pullback (a ρ : ℝ) (u : ℕ) (q : BondBilinear (n * L)) (A A' : TorusBond n → ℝ) :
    bilinearEval (pullbackForm a ρ L u q) A A' =
      bilinearEval q (responseMap a ρ L u A) (responseMap a ρ L u A') := by
  have e1 : bilinearEval (pullbackForm a ρ L u q) A A' = ∑ c : TorusBond n, ∑ c' : TorusBond n,
      ∑ b : TorusBond (n * L), ∑ b' : TorusBond (n * L),
      (responseKernel a ρ L u b c * A c) * q b b' * (responseKernel a ρ L u b' c' * A' c') := by
    unfold bilinearEval pullbackForm
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b' _ => by ring
  have e2 : bilinearEval q (responseMap a ρ L u A) (responseMap a ρ L u A') =
      ∑ b : TorusBond (n * L), ∑ b' : TorusBond (n * L), ∑ c : TorusBond n, ∑ c' : TorusBond n,
      (responseKernel a ρ L u b c * A c) * q b b' * (responseKernel a ρ L u b' c' * A' c') := by
    unfold bilinearEval responseMap
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul_sum]
  rw [e1, e2, Finset.sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]
private theorem bilinearEval_rankOne (k : ℝ) (f A : TorusBond n → ℝ) :
    bilinearEval (n := n) (fun c c' => k * (f c * f c')) A A = k * (∑ c, f c * A c) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  unfold bilinearEval
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c' _ => by ring
private theorem contourAverage_sum {ι : Type} (s : Finset ι) (r : ι → ℝ) (f : ι → TorusBond (n * L) → ℝ)
    (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (fun b => ∑ j ∈ s, f j b * r j) c = ∑ j ∈ s, _root_.YangMills.Construction.MomentLaw.contourAverage L (f j) c * r j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : _root_.YangMills.Construction.MomentLaw.contourAverage L (0 : TorusBond (n * L) → ℝ) c = 0 := by
      simpa using contourAverage_smul (L := L) 0 (0 : TorusBond (n * L) → ℝ) c
    simp only [Finset.sum_empty]
    exact e
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have e := contourAverage_add (L := L) (fun b => f j b * r j) (fun b => ∑ j ∈ s, f j b * r j) c
    have e2 := contourAverage_smul (L := L) (r j) (f j) c
    have e3 : (r j • f j) = fun b => f j b * r j := by
      funext b
      simp [mul_comm]
    rw [e3] at e2
    show _root_.YangMills.Construction.MomentLaw.contourAverage L ((fun b => f j b * r j) + fun b => ∑ j ∈ s, f j b * r j) c = _
    rw [e, ih, e2]
    ring
private theorem sum_fitDefect_mul (a ρ : ℝ) (u : ℕ) (A : TorusBond n → ℝ) (c'' : TorusBond n) :
    ∑ c, fitDefect L a ρ u c'' c * A c = _root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L u A) c'' - A c'' := by
  classical
  have e1 : _root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L u A) c'' =
      ∑ c, _root_.YangMills.Construction.MomentLaw.contourAverage L (fun b => responseKernel a ρ L u b c) c'' * A c :=
    contourAverage_sum _ A (fun c b => responseKernel a ρ L u b c) c''
  have e2 : ∑ c, bondIndicator c c'' * A c = A c'' := by
    simp [bondIndicator]
  rw [e1, ← e2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => by
    unfold fitDefect
    ring
private theorem sum_blockMean_fit (a : ℝ) (hv : TorusSite n → ℝ) (f : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, a / 2 * hv Y * ∑ i : Fin 4, (f (Y, i) ^ 2 + f (Y - unitStep n i, i) ^ 2) =
      a * ∑ c : TorusBond n, (hv c.1 + hv (c.1 + unitStep n c.2)) / 2 * f c ^ 2 := by
  have e1 : ∀ i : Fin 4, ∑ Y : TorusSite n, hv Y * f (Y - unitStep n i, i) ^ 2 =
      ∑ Y : TorusSite n, hv (Y + unitStep n i) * f (Y, i) ^ 2 := fun i => by
    refine Fintype.sum_equiv (Equiv.subRight (unitStep n i)) _ _ fun Y => ?_
    simp
  have e2 : ∑ c : TorusBond n, (hv c.1 + hv (c.1 + unitStep n c.2)) / 2 * f c ^ 2 =
      1 / 2 * ∑ Y : TorusSite n, ∑ i : Fin 4, hv Y * f (Y, i) ^ 2 +
      1 / 2 * ∑ i : Fin 4, ∑ Y : TorusSite n, hv (Y + unitStep n i) * f (Y, i) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm (s := (Finset.univ : Finset (Fin 4))), Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ Y : TorusSite n, a / 2 * hv Y * ∑ i : Fin 4, (f (Y, i) ^ 2 + f (Y - unitStep n i, i) ^ 2) =
      a / 2 * ∑ Y : TorusSite n, ∑ i : Fin 4, hv Y * f (Y, i) ^ 2 +
      a / 2 * ∑ i : Fin 4, ∑ Y : TorusSite n, hv Y * f (Y - unitStep n i, i) ^ 2 := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4))), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e3, e2, Finset.sum_congr rfl fun i _ => e1 i]
  ring
private theorem sum_sitesInBlocks (g : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, g y = ∑ y, g y := by
  classical
  have e : ∀ Y : TorusSite n, sitesInBlocks L {Y} = Finset.univ.filter fun x => parentBlock L x = Y := fun Y => by
    ext x
    simp [sitesInBlocks]
  simp only [e]
  exact Finset.sum_fiberwise _ _ _
private theorem bilinearEval_recursion (a ρ : ℝ) {s τ : ℕ} (hτ : τ = s) (Qn : TorusSite n → BondBilinear n)
    (q : TorusSite (n * L) → BondBilinear (n * L)) (hv : TorusSite n → ℝ) (hc : TorusBond n → ℝ)
    (hhat : ∀ c : TorusBond n, (hv c.1 + hv (c.1 + unitStep n c.2)) / 2 = hc c)
    (R : ∀ (Y : TorusSite n) (c c' : TorusBond n), Qn Y c c' =
      ∑ y ∈ sitesInBlocks L {Y}, pullbackForm a ρ L τ (q y) c c' + a / 2 * hv Y * ∑ i : Fin 4,
        (fitDefect L a ρ τ (Y, i) c * fitDefect L a ρ τ (Y, i) c' +
          fitDefect L a ρ τ (Y - unitStep n i, i) c * fitDefect L a ρ τ (Y - unitStep n i, i) c'))
    (A : TorusBond n → ℝ) :
    bilinearEval (n := n) (fun b b' => ∑ Y, Qn Y b b') A A =
      bilinearEval (n := n * L) (fun b b' => ∑ y, q y b b') (responseMap a ρ L s A) (responseMap a ρ L s A) +
        a * ∑ c : TorusBond n, hc c * (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L s A) c - A c) ^ 2 := by
  subst hτ
  set f : TorusBond n → ℝ := fun c => _root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L τ A) c - A c with hf
  have each : ∀ Y, bilinearEval (Qn Y) A A =
      ∑ y ∈ sitesInBlocks L {Y}, bilinearEval (q y) (responseMap a ρ L τ A) (responseMap a ρ L τ A) +
      a / 2 * hv Y * ∑ i : Fin 4, (f (Y, i) ^ 2 + f (Y - unitStep n i, i) ^ 2) := fun Y => by
    have e : Qn Y = fun c c' => (∑ y ∈ sitesInBlocks L {Y}, pullbackForm a ρ L τ (q y) c c') +
        ∑ i : Fin 4, (a / 2 * hv Y * (fitDefect L a ρ τ (Y, i) c * fitDefect L a ρ τ (Y, i) c') +
          a / 2 * hv Y * (fitDefect L a ρ τ (Y - unitStep n i, i) c *
            fitDefect L a ρ τ (Y - unitStep n i, i) c')) := by
      funext c c'
      rw [R Y c c', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, bilinearEval_add, bilinearEval_sum, bilinearEval_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun y _ => bilinearEval_pullback a ρ τ (q y) A A
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [bilinearEval_add, bilinearEval_rankOne, bilinearEval_rankOne, sum_fitDefect_mul, sum_fitDefect_mul]
      ring
  rw [bilinearEval_sum, Finset.sum_congr rfl fun Y _ => each Y, Finset.sum_add_distrib, sum_sitesInBlocks,
    bilinearEval_sum, sum_blockMean_fit]
  simp only [hhat, hf]
abbrev _root_.YangMills.SharedProofs.p28188 := @bilinearEval_recursion
end Forms
section Descent
variable {L : ℕ} [NeZero L] {a ρ cK : ℝ} {n₀ : ℕ}
private def descendLinear (t : ℕ) : (d n : ℕ) → LevelChain L (t + d) n →ₗ[ℝ] LevelChain L t (fineSide L d n)
  | 0, _ => LinearMap.id
  | d + 1, n => descendLinear t d (n * L) ∘ₗ lowerLinear (t + d) n
private theorem descendLinear_apply (t : ℕ) : ∀ (d n : ℕ) (X : LevelChain L (t + d) n),
    descendLinear t d n X = chainDescend t d n X
  | 0, _, _ => rfl
  | d + 1, n, X => descendLinear_apply t d (n * L) (chainLower X)
private theorem isMarginal_descend {V : Type} [AddCommGroup V] [Module ℝ V] {E₀ : V → ℝ} (ha : 0 ≤ a) (t : ℕ) :
    ∀ (d n : ℕ) [NeZero n] (W : V →ₗ[ℝ] LevelChain L (t + d) n), IsMarginal E₀ (levelForm a (t + d) n) W →
      IsMarginal E₀ (levelForm a t (fineSide L d n)) (descendLinear t d n ∘ₗ W)
  | 0, _, _, W, hW => hW
  | d + 1, n, _, W, hW => by
    have := isMarginal_descend ha t d (n * L) (lowerLinear (t + d) n ∘ₗ W) (hW.lower ha)
    exact this
private theorem baseObservable_descend (w : ∀ m, PlaquetteWeight m) (t : ℕ) :
    ∀ (d n : ℕ) [NeZero n] (X : LevelChain L (t + d) n),
    baseObservable (L := L) (s := t + d) (n := n) (w _) X =
      baseObservable (L := L) (s := t) (n := fineSide L d n) (w _) (chainDescend t d n X)
  | 0, _, _, _ => rfl
  | d + 1, n, _, X => baseObservable_descend w t d (n * L) (chainLower X)
private theorem noiseWeight_disjoint (w₁ w₂ : ∀ m, PlaquetteWeight m) (G : ℕ → ℕ → Prop)
    (hd : ∀ s n, G (s + 1) n → G s (n * L))
    (hb : ∀ (s n : ℕ) [NeZero n], G (s + 1) n → ∀ c : TorusBond n, bondBlockMean L (s + 1) n (w₁ _) c ≠ 0 →
      bondBlockMean L (s + 1) n (w₂ _) c ≠ 0 → False) :
    ∀ (s n : ℕ) [NeZero n], G s n → ∀ ι : ChainNoise L s n, noiseWeight a w₁ s n ι ≠ 0 →
      noiseWeight a w₂ s n ι ≠ 0 → False
  | 0, _, _, _, _ => fun h => absurd rfl h
  | s + 1, n, _, hG, ι => by
    revert ι
    show ∀ ι : ChainNoise L s (n * L) ⊕ (Fin 3 × TorusBond n), _
    rintro (j | j) h₁ h₂
    · exact noiseWeight_disjoint w₁ w₂ G hd hb s (n * L) (hd s n hG) j h₁ h₂
    · exact hb s n hG j.2 (right_ne_zero_of_mul h₁) (right_ne_zero_of_mul h₂)
private theorem exists_of_blockMean_ne_zero : ∀ (t n : ℕ) [NeZero n] (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)), blockMean L t n Y h ≠ 0 → ∃ p, IsPlaquetteAt L t Y p ∧ h p ≠ 0
  | 0, n, _, Y, h => fun hne => by
    have h1 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), vertexMultiplicity Y p * h p ≠ 0 :=
      right_ne_zero_of_mul hne
    obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have h2 := left_ne_zero_of_mul hpn
    have h3 : Y ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
      by_contra hc
      refine h2 ?_
      simp only [vertexMultiplicity]
      rw [List.count_eq_zero_of_not_mem hc]
      simp
    exact ⟨p, ⟨(Finset.mem_filter.1 hp).2.1, Y, h3, Finset.mem_singleton_self Y⟩, right_ne_zero_of_mul hpn⟩
  | t + 1, n, _, Y, h => fun hne => by
    have h1 : ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y h ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨y, hy, hyn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    obtain ⟨p, ⟨hp1, c, hc1, hc2⟩, hp2⟩ := exists_of_blockMean_ne_zero t (n * L) y h hyn
    exact ⟨p, ⟨hp1, c, hc1, Finset.mem_biUnion.2 ⟨y, hy, hc2⟩⟩, hp2⟩
end Descent
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private def totalQuadratic (i : Fin Λ.k) (u n : ℕ) [NeZero n] : BondBilinear n := fun b b' =>
  ∑ y : TorusSite n, classicalQuadratic S.tower S.resp u n (S.weight i _) y b b'
private def AtStage (s n : ℕ) : Prop := s ≤ S.data.windowLevel ∧ n = S.levelSide s
private theorem stage_depth (u : ℕ) : (S.tower.stage u).depth = u := by
  induction u with
  | zero => exact S.startsAtWilson.depth_eq
  | succ u ih =>
    show (S.tower.stage u).depth + 1 = u + 1
    rw [ih]
abbrev _root_.YangMills.SharedProofs.p98506 := @stage_depth
private theorem stage_anchorRadius (t : ℕ) : (S.tower.stage t).anchorRadius = Λ.table.ρA := by
  induction t with
  | zero =>
    have e := congrArg (fun z : StageWithResponse Λ.stepParams => z.1.anchorRadius) (S.stage_eq 0 (Nat.zero_le _))
    exact e.trans S.isInitial.anchorRadius_eq
  | succ t ih => exact ih
abbrev _root_.YangMills.SharedProofs.p56052 := @stage_anchorRadius
private theorem atStage_lower (s n : ℕ) (h : AtStage S (s + 1) n) : AtStage S s (n * Λ.stepParams.side) := by
  obtain ⟨hs, hn⟩ := h
  refine ⟨by omega, ?_⟩
  subst hn
  show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (s + 1)) * Λ.stepParams.side =
    S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - s)
  have : S.data.windowLevel - s = S.data.windowLevel - (s + 1) + 1 := by omega
  rw [this, pow_succ, mul_assoc]
private theorem atStage_side_ge (hL : 0 < Λ.stepParams.side) (s n : ℕ) (h : AtStage S s n) :
    Λ.stepParams.n₀ ≤ n := by
  obtain ⟨-, hn⟩ := h
  subst hn
  show Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - s)
  calc Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ hL
    _ ≤ S.data.period Λ.stepParams.side := S.side_le
    _ ≤ _ := Nat.le_mul_of_pos_right _ (pow_pos hL _)
private theorem atStage_fineSide {t d : ℕ} (h : t + d = S.data.windowLevel) :
    AtStage S t (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) := by
  refine ⟨by omega, ?_⟩
  rw [fineSide_eq]
  show _ = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - t)
  have : S.data.windowLevel - t = d := by omega
  rw [this]
private theorem levelBounds {cK : ℝ} (F : ScaleFlowBounds Λ.stepParams.coupling Λ.table.ρA cK Λ.stepParams.side Λ.stepParams.n₀)
    (R : (∀ t, t < S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
      ∀ (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage (t + 1)).depth n))
      (Y : TorusSite n) (c c' : TorusBond n),
      classicalQuadratic S.tower S.resp (t + 1) n h Y c c' =
        ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y}, pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius
          Λ.stepParams.side (S.tower.stage t).depth
          (classicalQuadratic S.tower S.resp t (n * Λ.stepParams.side) h y) c c' +
        Λ.stepParams.coupling / 2 * blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h * ∑ i : Fin 4,
          (fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius (S.tower.stage t).depth
              (Y, i) c *
              fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
                (S.tower.stage t).depth (Y, i) c' +
            fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius (S.tower.stage t).depth
              (Y - unitStep n i, i) c *
              fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
                (S.tower.stage t).depth (Y - unitStep n i, i) c')) ∧
    ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (h : PlaquetteWeight n)
      (h' : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage 0).depth n)), HEq h h' →
      ∀ A : TorusBond n → ℝ, ∑ y : TorusSite n, bilinearEval (classicalQuadratic S.tower S.resp 0 n h' y) A A =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), h p * curl A p ^ 2)
    (Kl : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      AnnihilatesClosedForms (classicalQuadratic S.tower S.resp t n h y))
    (Fr : ∀ u ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], n = S.levelSide u → ∀ (y : TorusSite n) (sz : ℝ)
      (q : BondBilinear n), 0 < sz → IsDecayingAbout Λ.stepParams sz y q → AnnihilatesClosedForms q →
      ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ,
        ∀ X X' : TorusBond n → ℝ, bilinearEval q X X' = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
          ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), κ p p' * curl X p * curl X' p')
    (i : Fin Λ.k) :
    LevelBounds Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side Λ.stepParams.n₀ (AtStage S)
      (fun m => S.weight i m) (fun u n [NeZero n] => totalQuadratic S i u n) where
  lower := atStage_lower S
  side_ge := atStage_side_ge S F.L_pos
  represent s n _ hG := by
    have hn := atStage_side_ge S F.L_pos s n hG
    have hk : AnnihilatesClosedForms (totalQuadratic S i s n) := by
      have h1 : ∀ A A' : TorusBond n → ℝ, bilinearEval (totalQuadratic S i s n) A A' =
          ∑ y : TorusSite n, bilinearEval (classicalQuadratic S.tower S.resp s n (S.weight i _) y) A A' :=
        fun A A' => bilinearEval_sum _ _ A A'
      refine ⟨fun φ A => ?_, fun v A => ?_⟩
      · constructor
        · rw [h1]
          exact Finset.sum_eq_zero fun y _ => ((Kl s hG.1 n hn y _).1 φ A).1
        · rw [h1]
          exact Finset.sum_eq_zero fun y _ => ((Kl s hG.1 n hn y _).1 φ A).2
      · constructor
        · rw [h1]
          exact Finset.sum_eq_zero fun y _ => ((Kl s hG.1 n hn y _).2 v A).1
        · rw [h1]
          exact Finset.sum_eq_zero fun y _ => ((Kl s hG.1 n hn y _).2 v A).2
    have hw : ∀ m, 0 < Λ.stepParams.weight m := fun m => mul_pos (lt_max_of_lt_left one_pos) (Real.exp_pos _)
    set q := totalQuadratic S i s n with hq
    let y : TorusSite n := 0
    let sz : ℝ := 1 + ∑ b : TorusBond n, ∑ b' : TorusBond n, |q b b'| * Λ.stepParams.weight (tripleDiam y b b')
    have hsum : 0 ≤ ∑ b : TorusBond n, ∑ b' : TorusBond n, |q b b'| * Λ.stepParams.weight (tripleDiam y b b') :=
      Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun b' _ => mul_nonneg (abs_nonneg _) (hw _).le
    have hsz : 0 < sz := by positivity
    have hsize : IsDecayingAbout Λ.stepParams sz y q := fun b b' => by
      rw [le_div_iff₀ (hw _)]
      have h1 : |q b b'| * Λ.stepParams.weight (tripleDiam y b b') ≤
          ∑ b' : TorusBond n, |q b b'| * Λ.stepParams.weight (tripleDiam y b b') :=
        Finset.single_le_sum (f := fun b' => |q b b'| * Λ.stepParams.weight (tripleDiam y b b'))
          (fun b' _ => mul_nonneg (abs_nonneg _) (hw _).le) (Finset.mem_univ b')
      have h2 : ∑ b' : TorusBond n, |q b b'| * Λ.stepParams.weight (tripleDiam y b b') ≤
          ∑ b : TorusBond n, ∑ b' : TorusBond n, |q b b'| * Λ.stepParams.weight (tripleDiam y b b') :=
        Finset.single_le_sum (f := fun b => ∑ b' : TorusBond n, |q b b'| * Λ.stepParams.weight (tripleDiam y b b'))
          (fun b _ => Finset.sum_nonneg fun b' _ => mul_nonneg (abs_nonneg _) (hw _).le) (Finset.mem_univ b)
      show _ ≤ 1 + _
      linarith
    exact Fr s hG.1 n hG.2 y sz q hsz hsize hk
  recursion s n _ hG A := by
    have hn := atStage_side_ge S F.L_pos (s + 1) n hG
    have hK : s < S.data.windowLevel := hG.1
    have hat_eq : ∀ v, v = s → ∀ Y : TorusSite n,
        blockMean Λ.stepParams.side (v + 1) n Y (S.weight i (fineSide Λ.stepParams.side (v + 1) n)) =
        blockMean Λ.stepParams.side (s + 1) n Y (S.weight i (fineSide Λ.stepParams.side (s + 1) n)) := by
      rintro v rfl Y
      rfl
    refine bilinearEval_recursion (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA (stage_depth S s)
      (fun Y => classicalQuadratic S.tower S.resp (s + 1) n (S.weight i _) Y)
      (fun y => classicalQuadratic S.tower S.resp s (n * Λ.stepParams.side) (S.weight i _) y)
      (fun Y => blockMean Λ.stepParams.side ((S.tower.stage s).depth + 1) n Y
        (S.weight i (fineSide Λ.stepParams.side ((S.tower.stage s).depth + 1) n)))
      (bondBlockMean Λ.stepParams.side (s + 1) n (S.weight i _)) (fun c => ?_) (fun Y c c' => ?_) A
    · show (_ + _) / 2 = (_ + _) / 2
      rw [hat_eq _ (stage_depth S s), hat_eq _ (stage_depth S s)]
    · have := R.1 s hK n hn (S.weight i _) Y c c'
      rw [stage_anchorRadius] at this
      exact this
  initial n _ hG X := by
    have hn := atStage_side_ge S F.L_pos 0 n hG
    have heq : HEq (S.weight i n) (S.weight i (fineSide Λ.stepParams.side (S.tower.stage 0).depth n)) := by
      have e : n = fineSide Λ.stepParams.side (S.tower.stage 0).depth n := by
        rw [stage_depth]
        rfl
      exact congr_arg_heq (S.weight i) e
    have h1 : ∀ e : Fin 3, bilinearEval (totalQuadratic S i 0 n) (X e) (X e) =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), S.weight i n p * curl (X e) p ^ 2 := fun e => by
      rw [← R.2 n hn _ _ heq (X e)]
      exact bilinearEval_sum _ _ _ _
    show _ = 1 / 2 * ∑ e : Fin 3, bilinearEval (totalQuadratic S i 0 n) (X e) (X e)
    rw [Finset.sum_congr rfl fun e _ => h1 e, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.mul_sum]
private theorem supportForm_eq (hL : 0 < Λ.stepParams.side)
    (Kl : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      (∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = 0) →
        classicalQuadratic S.tower S.resp t n h y = 0)
    (i : Fin Λ.k) {s n : ℕ} [NeZero n] (hG : AtStage S s n) : S.supportForm s n i = totalQuadratic S i s n := by
  classical
  funext b b'
  show ∑ y ∈ S.supportAt s n i, _ = ∑ y : TorusSite n, _
  refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
  have hy' : ¬ ∃ p, IsPlaquetteAt Λ.stepParams.side s y p ∧
      S.weight i (fineSide Λ.stepParams.side s n) p ≠ 0 := fun h =>
    hy (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hz : ∀ v, v = s → ∀ p : TorusPlaquette (fineSide Λ.stepParams.side v n),
      IsPlaquetteAt Λ.stepParams.side v y p → S.weight i (fineSide Λ.stepParams.side v n) p = 0 := by
    rintro v rfl p hp
    by_contra hne
    exact hy' ⟨p, hp, hne⟩
  rw [Kl s hG.1 n (atStage_side_ge S hL s n hG) y _ (hz _ (stage_depth S s))]
  rfl
private theorem not_both_blockMean_ne_zero {s n : ℕ} [NeZero n] (hs : s + 1 ≤ S.lastSeparated)
    (hn : n = S.levelSide (s + 1)) {i i' : Fin Λ.k} (hne : i ≠ i') (c : TorusBond n)
    (h₁ : bondBlockMean Λ.stepParams.side (s + 1) n (S.weight i _) c ≠ 0)
    (h₂ : bondBlockMean Λ.stepParams.side (s + 1) n (S.weight i' _) c ≠ 0) : False := by
  classical
  subst hn
  have hfar : S.data.SeparatedBelow Λ.stepParams S.β S.lastSeparated :=
    Nat.findGreatest_spec (P := S.data.SeparatedBelow Λ.stepParams S.β) (Nat.zero_le _)
      (fun u hu => absurd hu (Nat.not_lt_zero _))
  have h8 := (hfar s hs).2
  have ends : ∀ j : Fin Λ.k,
      bondBlockMean Λ.stepParams.side (s + 1) (S.levelSide (s + 1)) (S.weight j _) c ≠ 0 →
      ∃ y ∈ S.data.supportSites Λ.stepParams.side (s + 1) j, y = c.1 ∨ y = c.1 + unitStep _ c.2 := fun j h => by
    by_cases h0 : blockMean Λ.stepParams.side (s + 1) _ c.1 (S.weight j _) = 0
    · have h3 : blockMean Λ.stepParams.side (s + 1) _ (c.1 + unitStep _ c.2) (S.weight j _) ≠ 0 := fun h4 => h (by
        unfold bondBlockMean
        rw [h0, h4]
        simp)
      obtain ⟨p, hp, hp2⟩ := exists_of_blockMean_ne_zero _ _ _ _ h3
      exact ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, p, hp, hp2⟩, Or.inr rfl⟩
    · obtain ⟨p, hp, hp2⟩ := exists_of_blockMean_ne_zero _ _ _ _ h0
      exact ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, p, hp, hp2⟩, Or.inl rfl⟩
  obtain ⟨y₁, m₁, e₁⟩ := ends i h₁
  obtain ⟨y₂, m₂, e₂⟩ := ends i' h₂
  have hd : TorusFields.supDist y₁ y₂ ≤ 1 := by
    rcases e₁ with rfl | rfl <;> rcases e₂ with rfl | rfl
    · rw [supDist_self]
      omega
    · exact _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le _ _
    · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le _ _
    · rw [supDist_self]
      omega
  have within_of : ∀ (A : Finset (TorusSite (S.data.sideAt Λ.stepParams.side (s + 1)))) y, y ∈ A →
      y ∈ thickening 2 A := fun A y hy =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, y, hy, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
  have hg : S.data.separation Λ.stepParams.side s ≤ TorusFields.supDist y₁ y₂ :=
    Nat.sInf_le ⟨i, i', hne, y₁, within_of _ _ m₁, y₂, within_of _ _ m₂, rfl⟩
  omega
end Point
section Statement
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem momentPoint_statement {cK : ℝ}
    (F : ScaleFlowBounds Λ.stepParams.coupling Λ.table.ρA cK Λ.stepParams.side Λ.stepParams.n₀)
    (R : (∀ t, t < S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
      ∀ (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage (t + 1)).depth n))
      (Y : TorusSite n) (c c' : TorusBond n),
      classicalQuadratic S.tower S.resp (t + 1) n h Y c c' =
        ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y}, pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius
          Λ.stepParams.side (S.tower.stage t).depth
          (classicalQuadratic S.tower S.resp t (n * Λ.stepParams.side) h y) c c' +
        Λ.stepParams.coupling / 2 * blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h * ∑ i : Fin 4,
          (fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius (S.tower.stage t).depth
              (Y, i) c *
              fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
                (S.tower.stage t).depth (Y, i) c' +
            fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius (S.tower.stage t).depth
              (Y - unitStep n i, i) c *
              fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
                (S.tower.stage t).depth (Y - unitStep n i, i) c')) ∧
    ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (h : PlaquetteWeight n)
      (h' : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage 0).depth n)), HEq h h' →
      ∀ A : TorusBond n → ℝ, ∑ y : TorusSite n, bilinearEval (classicalQuadratic S.tower S.resp 0 n h' y) A A =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), h p * curl A p ^ 2)
    (Kl : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      AnnihilatesClosedForms (classicalQuadratic S.tower S.resp t n h y))
    (Kz : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      (∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = 0) →
        classicalQuadratic S.tower S.resp t n h y = 0)
    (Fr : ∀ u ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], n = S.levelSide u → ∀ (y : TorusSite n) (sz : ℝ)
      (q : BondBilinear n), 0 < sz → IsDecayingAbout Λ.stepParams sz y q → AnnihilatesClosedForms q →
      ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ,
        ∀ X X' : TorusBond n → ℝ, bilinearEval q X X' = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
          ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), κ p p' * curl X p * curl X' p')
    (d : ℕ) (hd : S.lastSeparated + d = S.data.windowLevel)
    (μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)))
    (hμ : IsCanonicalGaussian
      (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ) :
    (∀ i : Fin Λ.k, ∃ c₀ : ℝ, (μ[S.completedAt d (S.data.period Λ.stepParams.side) i |
        MeasurableSpace.comap (fun X (e : Fin 3)
          (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
          curl (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) e) p)
          inferInstance]) =ᵐ[μ]
      fun X => S.halfForm d (S.data.period Λ.stepParams.side) i X + c₀) ∧
    jointCumulant μ (fun i => S.completedAt d (S.data.period Λ.stepParams.side) i) =
      jointCumulant μ (fun i => S.observableAt (S.lastSeparated + d) (S.data.period Λ.stepParams.side) i) := by
  classical
  have := hμ.isProbabilityMeasure
  have ha := F.a_pos
  have hG : AtStage S S.lastSeparated (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) :=
    atStage_fineSide S hd
  have hn₀ := atStage_side_ge S F.L_pos _ _ hG
  have hE : ∀ x : LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side),
      0 ≤ levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side) x := fun x =>
    levelEnergy_nonneg ha.le (S.lastSeparated + d) (S.data.period Λ.stepParams.side) x
  have hm : ∀ f : LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side) →ₗ[ℝ] ℝ,
      Measurable f := fun f =>
    f.continuous_of_finiteDimensional.measurable
  have hW : IsMarginal (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side))
      (levelForm Λ.stepParams.coupling S.lastSeparated (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)))
      (descendLinear S.lastSeparated d (S.data.period Λ.stepParams.side)) := by
    have := isMarginal_descend (L := Λ.stepParams.side) ha.le S.lastSeparated d (S.data.period Λ.stepParams.side)
      LinearMap.id (isMarginal_id Λ.stepParams.coupling _ _)
    simpa using this
  refine ⟨fun i => ?_, ?_⟩
  · set W := descendLinear (L := Λ.stepParams.side) S.lastSeparated d (S.data.period Λ.stepParams.side) with hWd
    have Lv := levelBounds S F R Kl Fr i
    let g₀ : Fin 3 × TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) →
        LevelChain Λ.stepParams.side S.lastSeparated (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))
          →ₗ[ℝ] ℝ :=
      fun j => curlFunctional j.1 j.2 ∘ₗ topLinear S.lastSeparated _
    have kg : ∀ j, Annihilates (levelEnergy Λ.stepParams.coupling S.lastSeparated
        (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) (g₀ j) := fun j X hX =>
      curl_eq_zero_of_form F S.lastSeparated hn₀ (maxwellForm_top_eq_zero F hn₀ hX j.1) j.2
    let H : Fin 3 × TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) →
        LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side) →ₗ[ℝ] ℝ :=
      fun j => g₀ j ∘ₗ W
    have hH : ∀ j, Annihilates (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d)
        (S.data.period Λ.stepParams.side)) (H j) := fun j => hW.comp_annihilates ha.le (kg j)
    have hU : IsUncorrelatedWith (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA H μ S.lastSeparated _ W :=
      fun f hf hf0 j =>
      covariance_top_eq_zero (ρ := Λ.table.ρA) F hμ hE hm hn₀ hW (kg j) hf (fun X => by
        show curl (chainTop S.lastSeparated _ (pushedChain (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA
          S.lastSeparated _ (chainTop S.lastSeparated _ X)) j.1) j.2 = _
        rw [chainTop_pushedChain]
        rfl) hf0
    obtain ⟨hi, c, hc⟩ := hasMeanOnSets_remainder F hμ hE hm H hH Lv S.lastSeparated _ hG W hW hU
    obtain ⟨κ, hκ⟩ := Lv.represent S.lastSeparated _ hG
    have hQ := supportForm_eq S F.L_pos Kz i hG
    have hHe : ∀ (j) (X : LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
        H j X = curl (chainTop S.lastSeparated _
          (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) j.1) j.2 := fun j X => by
      show curl (chainTop S.lastSeparated _ (W X) j.1) j.2 = _
      rw [hWd, descendLinear_apply]
    have hhalf : ∀ X, S.halfForm d (S.data.period Λ.stepParams.side) i X = ∑ e : Fin 3,
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide Λ.stepParams.side d
          (S.data.period Λ.stepParams.side)))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide Λ.stepParams.side d
          (S.data.period Λ.stepParams.side)))),
          (κ p p' / 2) * (H (e, p) X * H (e, p') X) := fun X => by
      show 1 / 2 * colourEval (S.supportForm S.lastSeparated _ i) _ _ = _
      rw [hQ]
      show 1 / 2 * ∑ e : Fin 3, bilinearEval (totalQuadratic S i S.lastSeparated _) _ _ = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [hκ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [hHe, hHe]
      ring
    have hhalf_int : Integrable (S.halfForm d (S.data.period Λ.stepParams.side) i) μ := by
      rw [funext hhalf]
      refine integrable_finset_sum _ fun e _ => integrable_finset_sum _ fun p _ =>
        integrable_finset_sum _ fun p' _ => Integrable.const_mul ?_ _
      exact (memLp_of_annihilates hμ (hH _) (hm _) 2 (by norm_num)).integrable_mul
        (memLp_of_annihilates hμ (hH _) (hm _) 2 (by norm_num))
    have hsum : ∀ X, S.completedAt d (S.data.period Λ.stepParams.side) i X =
        S.halfForm d (S.data.period Λ.stepParams.side) i X +
          remainder Λ.stepParams.coupling (fun m => S.weight i m) (fun u n [NeZero n] => totalQuadratic S i u n)
            S.lastSeparated _ (W X) := fun X => by
      have e : W X = chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X := descendLinear_apply _ _ _ _
      rw [e]
      unfold remainder
      show _ = 1 / 2 * colourEval (S.supportForm S.lastSeparated _ i) _ _ + _
      rw [hQ]
      show completedObservable _ _ _ _ _ = _
      ring
    have hsub : ∀ A, MeasurableSet[MeasurableSpace.comap (fun X (e : Fin 3)
        (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
        curl (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) e) p)
        inferInstance] A → MeasurableSet[generated H] A := by
      rintro _ ⟨T, hT, rfl⟩
      refine ⟨(fun u e p => u (e, p)) ⁻¹' T, (measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun p =>
        measurable_pi_apply _) hT, ?_⟩
      ext X
      simp only [Set.mem_preimage, hHe]
    have hle : MeasurableSpace.comap (fun X (e : Fin 3)
        (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
        curl (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) e) p)
        inferInstance ≤
        (inferInstance : MeasurableSpace
          (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side))) := fun A hA =>
      generated_le hm H A (hsub A hA)
    have hmeasH : ∀ j, Measurable[MeasurableSpace.comap (fun X (e : Fin 3)
        (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
        curl (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) e) p)
        inferInstance] (H j) := fun j => by
      have h1 : Measurable[MeasurableSpace.comap (fun X (e : Fin 3)
          (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
          curl (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) e) p)
          inferInstance]
        (fun X (e : Fin 3) (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
          curl (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) e) p) :=
        comap_measurable _
      have h2 := (measurable_pi_apply j.2).comp ((measurable_pi_apply j.1).comp h1)
      have e : ⇑(H j) = (fun f => f j.2) ∘ (fun f => f j.1) ∘ fun X (e : Fin 3)
          (p : TorusPlaquette (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) =>
          curl (chainTop S.lastSeparated _ (chainDescend S.lastSeparated d (S.data.period Λ.stepParams.side) X) e) p :=
        funext fun X => hHe j X
      rw [e]
      exact h2
    refine ⟨c, (ae_eq_condExp_of_forall_setIntegral_eq hle ?_ ?_ ?_ ?_).symm⟩
    · rw [funext hsum]
      exact hhalf_int.add hi
    · intro A _ _
      exact (hhalf_int.add (integrable_const c)).integrableOn
    · intro A hA _
      have h1 := hc A (hsub A hA)
      rw [funext hsum, integral_add hhalf_int.integrableOn hi.integrableOn, integral_add hhalf_int.integrableOn
        (integrable_const c).integrableOn, h1]
      simp
    · refine Measurable.aestronglyMeasurable ?_
      rw [funext hhalf]
      refine Measurable.add_const (Finset.measurable_fun_sum _ fun e _ => Finset.measurable_fun_sum _ fun p _ =>
        Finset.measurable_fun_sum _ fun p' _ => Measurable.const_mul ((hmeasH _).mul (hmeasH _)) _) _
  · have hdis : ∀ (ι : ChainNoise Λ.stepParams.side S.lastSeparated
        (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side))) (i i' : Fin Λ.k),
        noiseWeight (L := Λ.stepParams.side) Λ.stepParams.coupling (S.weight i) S.lastSeparated
          (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) ι ≠ 0 →
          noiseWeight (L := Λ.stepParams.side) Λ.stepParams.coupling (S.weight i') S.lastSeparated
            (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) ι ≠ 0 → i = i' :=
        fun ι i i' h₁ h₂ => by
      by_contra hne
      refine noiseWeight_disjoint (S.weight i) (S.weight i') (fun s n => s ≤ S.lastSeparated ∧ n = S.levelSide s)
        (fun s n hg => ?_)
        (fun s n _ hg c g₁ g₂ => not_both_blockMean_ne_zero S hg.1 hg.2 hne c g₁ g₂) S.lastSeparated _
        ⟨le_rfl, hG.2⟩ ι h₁ h₂
      exact ⟨by have := hg.1; omega, (atStage_lower S s n ⟨by have := hg.1; omega, hg.2⟩).2⟩
    unfold jointCumulant
    refine Finset.sum_congr rfl fun π _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun J _ => ?_
    have key := integral_prod_completed_eq F hμ hE hm hn₀ hW (fun i m => S.weight i m) hdis J
    have e1 : ∀ X, ∏ i ∈ J, S.completedAt d (S.data.period Λ.stepParams.side) i X =
        ∏ i ∈ J, completedObservable Λ.stepParams.coupling S.lastSeparated _ (S.weight i _)
          (descendLinear S.lastSeparated d (S.data.period Λ.stepParams.side) X) := fun X =>
      Finset.prod_congr rfl fun i _ => by
        rw [descendLinear_apply]
        rfl
    have e2 : ∀ X, ∏ i ∈ J, S.observableAt (S.lastSeparated + d) (S.data.period Λ.stepParams.side) i X =
        ∏ i ∈ J, baseObservable (L := Λ.stepParams.side) (S.weight i _)
          (descendLinear S.lastSeparated d (S.data.period Λ.stepParams.side) X) := fun X =>
      Finset.prod_congr rfl fun i _ => by
        rw [descendLinear_apply]
        exact baseObservable_descend (fun m => S.weight i m) S.lastSeparated d _ X
    simp only [e1, e2]
    exact key
end Statement
private theorem scaleFlowBounds_of (Tb : ParameterAssignment) (y : ℝ) (hD : Tb.Admissible) (h₁ : stepMinimumAt Tb y)
    (h₂ : GradientMaxwellPropertiesAt Tb y) (h₃ : maxwellFormAtZeroStatement) :
    ScaleFlowBounds Tb.coupling Tb.ρA Tb.coercivity (Tb.stepParameters y).side Tb.n₀ where
  a_pos := by linarith [hD.a_ge]
  cK_pos := hD.cK_pos
  L_pos := (show Odd (Tb.stepParameters y).side from hD.L_odd).pos
  le_step u n _ hn W B := (h₁ u n hn).1 W B
  eq_step u n _ hn B := (h₁ u n hn).2 B
  form_zero m _ A := h₃ Tb.coupling (Tb.stepParameters y).side m A
  coercive u n _ hn A := (h₂ u n hn).2.2 A
end LevelChainFirstOrder
open LevelChainFirstOrder in
theorem levelChainFirstOrder (h₁ : classicalQuadraticRecursionStatement)
    (h₂ : classicalFormsAnnihilateClosedStatement) (h₃ : formsReadCurvatureStatement) (h₄ : stepMinimumStatement)
    (h₅ : gradientMaxwellStatement) (h₆ : maxwellFormAtZeroStatement) :
    levelChainFirstOrderStatement := by
  intro a ha
  obtain ⟨L1, r1, C1, hr1, g1⟩ := h₁ a ha
  obtain ⟨L2, r2, C2, hr2, g2⟩ := h₂ a ha
  obtain ⟨L3, r3, C3, hr3, g3⟩ := h₃ a ha
  obtain ⟨L4, r4, C4, hr4, g4⟩ := h₄ a ha
  obtain ⟨L5, r5, C5, hr5, g5⟩ := h₅ a ha
  refine ⟨max L1 (max L2 (max L3 (max L4 L5))), fun c => min (r1 c) (min (r2 c) (min (r3 c) (min (r4 c) (r5 c)))),
    max C1 (max C2 (max C3 (max C4 C5))),
    fun c => lt_min (hr1 c) (lt_min (hr2 c) (lt_min (hr3 c) (lt_min (hr4 c) (hr5 c)))), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hCH hrt hC Kr hKr
  have l1 : L1 ≤ L := (le_max_left _ _).trans hL
  have l2 : L2 ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have l3 : L3 ≤ L := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hL
  have l4 : L4 ≤ L :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hL
  have l5 : L5 ≤ L :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hL
  have t1 : Tb.rt ≤ r1 Tb.toChainParameters := hrt.trans (min_le_left _ _)
  have t2 : Tb.rt ≤ r2 Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t3 : Tb.rt ≤ r3 Tb.toChainParameters :=
    hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have t4 : Tb.rt ≤ r4 Tb.toChainParameters :=
    hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have t5 : Tb.rt ≤ r5 Tb.toChainParameters :=
    hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have c1 : C1 ≤ Tb.derivBound := (le_max_left _ _).trans hC
  have c2 : C2 ≤ Tb.derivBound := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have c3 : C3 ≤ Tb.derivBound := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hC
  have c4 : C4 ≤ Tb.derivBound :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hC
  have c5 : C5 ≤ Tb.derivBound :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hC
  obtain ⟨y1, f1⟩ := g1 L hodd l1 Tb hTa hTL hD hCS hCH t1 c1 Kr hKr
  obtain ⟨y2, f2⟩ := g2 L hodd l2 Tb hTa hTL hD hCS hCH t2 c2 Kr hKr
  obtain ⟨y3, f3⟩ := g3 L hodd l3 Tb hTa hTL hD hCS hCH t3 c3 Kr hKr
  obtain ⟨y4, f4⟩ := g4 L hodd l4 Tb hTa hTL hD hCS hCH t4 c4
  obtain ⟨y5, f5⟩ := g5 L hodd l5 Tb hTa hTL hD hCS hCH t5 c5
  refine ⟨max y1 (max y2 (max y3 (max y4 y5))), fun y hy hR hWl g hg hgy k _ hk2 hk8 R d hd' => ?_⟩
  have b1 : y1 ≤ y := (le_max_left _ _).trans hy
  have b2 : y2 ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have b3 : y3 ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have b4 : y4 ≤ y :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have b5 : y5 ≤ y :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  obtain ⟨Ca, _, _, _, _, Ha⟩ := f1 y b1 hR hWl g hg hgy k hk2 hk8 R d hd'
  obtain ⟨Cb, _, _, _, _, Hb⟩ := f2 y b2 hR hWl g hg hgy k hk2 hk8 R d hd'
  obtain ⟨Cc, _, _, _, _, Hc⟩ := f3 y b3 hR hWl g hg hgy k hk2 hk8 R d hd'
  have F := LevelChainFirstOrder.scaleFlowBounds_of Tb y hD (f4 y b4 hR hWl) (f5 y b5 hR hWl) h₆
  refine ⟨fun _ => 0, 1, y, one_pos, le_rfl, fun S d' hd μ hμ => ?_⟩
  exact momentPoint_statement S F (Ha S)
    (fun t ht n _ hn z h => ((Hb S t ht n hn z h).2.1))
    (fun t ht n _ hn z h hz => ((Hb S t ht n hn z h).2.2.2 hz).2)
    (fun u hu n _ hn z sz q hs hz hk => by
      obtain ⟨κ, hκ, -⟩ := (Hc S u hu n hn z sz q hs hz).1 hk
      exact ⟨κ, hκ⟩) d' hd μ hμ
end YangMills.Construction.MomentLaw
end
