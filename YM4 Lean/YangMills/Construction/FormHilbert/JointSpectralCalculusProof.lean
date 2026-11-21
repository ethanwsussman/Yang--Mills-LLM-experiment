import YangMills.Construction.FormHilbert.JointSpectralCalculus
import YangMills.Construction.InfiniteLattice.EveryPairOfDirectionsAndTheJointCarrierProof
import YangMills.Construction.JointSpectrum.FirstMomentUniqueness
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.FormHilbert
open YangMills.Construction.JointSpectrum
open YangMills.Construction.ScalarSpectralMeasures (sqNormLIntegral IsSpectralMeasureOf)
open YangMills.Construction.JointSpectrum.SpectralIntegral
  (integralDomain jointSpectralMeasure spectralIntegral)
open YangMills.Construction.JointSpectrum.FirstMoments
  (HasFirstMoments IsDiagonalMeasure EqJointSpectralMeasure)
section Functions
variable {J : Type} [Fintype J]
private lemma continuous_spectralMonomial (n : ℕ) (y : J → ℤ) :
    Continuous (spectralMonomial n y : SpectralDomain J → ℂ) := by apply _root_.YangMills.Construction.LatticeConventions.DirectionPairsSupport.continuous_spectralMonomial <;> assumption
private lemma norm_spectralMonomial_le (n : ℕ) (y : J → ℤ) (p : SpectralDomain J) :
    ‖spectralMonomial n y p‖ ≤ 1 := by
  unfold spectralMonomial torusMonomial
  rw [norm_mul, norm_pow, norm_prod]
  have h₁ : ‖(((p.1 : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
    exact p.1.2.2
  have h₂ : ∏ α, ‖((p.2 α : Circle) : ℂ) ^ y α‖ = 1 :=
    Finset.prod_eq_one fun α _ => by rw [norm_zpow, Circle.norm_coe, one_zpow]
  rw [h₂, mul_one]
  exact pow_le_one₀ (norm_nonneg _) h₁
private lemma isBddMeasurable_spectralMonomial (n : ℕ) (y : J → ℤ) :
    IsBddMeasurable (spectralMonomial n y : SpectralDomain J → ℂ) :=
  ⟨(continuous_spectralMonomial n y).measurable, 1, norm_spectralMonomial_le n y⟩
private lemma IsBddMeasurable.add_mul {φ φ' : SpectralDomain J → ℂ} (h : IsBddMeasurable φ)
    (h' : IsBddMeasurable φ') (c : ℂ) : IsBddMeasurable fun p => φ p + c * φ' p := by
  obtain ⟨m, C, hC⟩ := h
  obtain ⟨m', C', hC'⟩ := h'
  refine ⟨m.add (measurable_const.mul m'), C + ‖c‖ * C', fun p => ?_⟩
  calc ‖φ p + c * φ' p‖ ≤ ‖φ p‖ + ‖c * φ' p‖ := norm_add_le _ _
    _ ≤ C + ‖c‖ * C' := by
        rw [norm_mul]
        exact add_le_add (hC p) (mul_le_mul_of_nonneg_left (hC' p) (norm_nonneg _))
private lemma IsBddMeasurable.mul {φ φ' : SpectralDomain J → ℂ} (h : IsBddMeasurable φ)
    (h' : IsBddMeasurable φ') : IsBddMeasurable fun p => φ p * φ' p := by
  obtain ⟨m, C, hC⟩ := h
  obtain ⟨m', C', hC'⟩ := h'
  refine ⟨m.mul m', C * C', fun p => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC p) (hC' p) (norm_nonneg _) ((norm_nonneg _).trans (hC p))
private lemma IsBddMeasurable.conj {φ : SpectralDomain J → ℂ} (h : IsBddMeasurable φ) :
    IsBddMeasurable fun p => conj (φ p) := by
  obtain ⟨m, C, hC⟩ := h
  exact ⟨Complex.continuous_conj.measurable.comp m, C, fun p => by simpa using hC p⟩
private lemma isBddMeasurable_indicator {T : Set (SpectralDomain J)} (hT : MeasurableSet T) :
    IsBddMeasurable (T.indicator (1 : SpectralDomain J → ℂ)) := by
  refine ⟨measurable_one.indicator hT, 1, fun p => ?_⟩
  by_cases hp : p ∈ T <;> simp [hp]
private lemma isBddMeasurable_level :
    IsBddMeasurable fun p : SpectralDomain J => (((p.1 : ℝ)) : ℂ) := by
  refine ⟨(by fun_prop : Continuous fun p : SpectralDomain J => (((p.1 : ℝ)) : ℂ)).measurable,
    1, fun p => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
  exact p.1.2.2
private lemma isBddMeasurable_phase (l : J) :
    IsBddMeasurable fun p : SpectralDomain J => ((p.2 l : Circle) : ℂ) :=
  ⟨(by fun_prop : Continuous fun p : SpectralDomain J => ((p.2 l : Circle) : ℂ)).measurable,
    1, fun p => (Circle.norm_coe _).le⟩
private lemma IsBddMeasurable.pow {φ : SpectralDomain J → ℂ} (h : IsBddMeasurable φ) (n : ℕ) :
    IsBddMeasurable fun p => φ p ^ n := by
  obtain ⟨m, C, hC⟩ := h
  refine ⟨m.pow_const n, C ^ n, fun p => ?_⟩
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC p) n
private def cesaroMean (l : J) (n : ℕ) (p : SpectralDomain J) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, ((p.2 l : Circle) : ℂ) ^ k
private lemma norm_cesaroMean_le (l : J) (n : ℕ) (p : SpectralDomain J) :
    ‖cesaroMean l n p‖ ≤ 1 := by
  have h : ‖∑ k ∈ Finset.range n, ((p.2 l : Circle) : ℂ) ^ k‖ ≤ n := by
    calc ‖∑ k ∈ Finset.range n, ((p.2 l : Circle) : ℂ) ^ k‖
        ≤ ∑ k ∈ Finset.range n, ‖((p.2 l : Circle) : ℂ) ^ k‖ := norm_sum_le _ _
      _ = n := by simp [norm_pow, Circle.norm_coe]
  unfold cesaroMean
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (inv_mul_le_one₀ (by exact_mod_cast hn)).mpr h
private lemma tendsto_cesaroMean (l : J) (p : SpectralDomain J) :
    Tendsto (fun n => cesaroMean l n p) atTop
      (𝓝 ((phaseOneSet l).1.indicator (1 : SpectralDomain J → ℂ) p)) := by
  unfold cesaroMean
  by_cases h : p ∈ (phaseOneSet l).1
  · have h₁ : p.2 l = 1 := h
    rw [indicator_of_mem h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [h₁, hn']
  · have h₁ : ((p.2 l : Circle) : ℂ) ≠ 1 := fun e => h (Circle.ext (by simpa using e))
    rw [indicator_of_notMem h]
    refine squeeze_zero_norm (a := fun n : ℕ => 2 / ‖((p.2 l : Circle) : ℂ) - 1‖ * (n : ℝ)⁻¹)
      (fun n => ?_) ?_
    · rw [geom_sum_eq h₁, norm_mul, norm_inv, Complex.norm_natCast, mul_comm, norm_div]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖((p.2 l : Circle) : ℂ) ^ n - 1‖ ≤ ‖((p.2 l : Circle) : ℂ) ^ n‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ = 2 := by
            rw [norm_pow, Circle.norm_coe, one_pow, norm_one]
            norm_num
    · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (2 / ‖((p.2 l : Circle) : ℂ) - 1‖)
private lemma measurable_sqrtLevel :
    Measurable fun p : SpectralDomain J => (p.1 : ℝ) ^ (1 / 2 : ℝ) :=
  (measurable_subtype_coe.comp measurable_fst).pow_const _
private lemma abs_sqrtLevel_le (p : SpectralDomain J) : |(p.1 : ℝ) ^ (1 / 2 : ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (Real.rpow_nonneg p.1.2.1 _)]
  exact Real.rpow_le_one p.1.2.1 p.1.2.2 (by norm_num)
private lemma isBddMeasurable_sqrtLevel :
    IsBddMeasurable fun p : SpectralDomain J => (((p.1 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
  ⟨Complex.measurable_ofReal.comp measurable_sqrtLevel, 1, fun p => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_sqrtLevel_le p⟩
private lemma integral_norm_sq_eq_sqNorm (m : Measure (SpectralDomain J))
    {φ : SpectralDomain J → ℂ} (hφ : Measurable φ) :
    ∫ p, ‖φ p‖ ^ 2 ∂m = (sqNormLIntegral m φ).toReal := by
  unfold sqNormLIntegral
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun p => sq_nonneg _)
    (hφ.norm.pow_const 2).aestronglyMeasurable]
  refine congrArg ENNReal.toReal (lintegral_congr fun p => ?_)
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
end Functions
section HilbertSpace
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
private lemma ofReal_sq_norm {E : Type} [NormedAddCommGroup E] (x : E) :
    ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
private lemma range_eq_orthSet {P Q : H →L[ℂ] H} (hP : IsStarProjection P)
    (h : Q + P = 1) : range Q = orthSet (range P) := by
  have hsa := (isSelfAdjoint_iff_inner_eq P).mp hP.isSelfAdjoint
  have hid : ∀ a, P (P a) = P a := fun a =>
    congrArg (fun T : H →L[ℂ] H => T a) hP.isIdempotentElem.eq
  have hq : ∀ a, Q a = a - P a := fun a => by
    have := congrArg (fun T : H →L[ℂ] H => T a) h
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] at this
    exact eq_sub_of_add_eq this
  ext χ
  constructor
  · rintro ⟨v, rfl⟩ ψ ⟨u, rfl⟩
    rw [hq, ← hsa, map_sub, hid, sub_self, inner_zero_right]
  · intro hχ
    have h₀ : inner ℂ (P χ) χ = 0 := hχ (P χ) ⟨χ, rfl⟩
    have h₁ : inner ℂ (P χ) (P χ) = 0 := by
      rw [← hsa χ (P χ), hid, hsa, h₀]
    have h₂ : P χ = 0 := inner_self_eq_zero.mp h₁
    exact ⟨χ, by rw [hq, h₂, sub_zero]⟩
private lemma closure_range_eq_orthSet {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) :
    closure (range R) = orthSet {ψ | R ψ = 0} := by
  have hsa := (isSelfAdjoint_iff_inner_eq R).mp hR
  have h₁ := Submodule.orthogonal_orthogonal_eq_closure (LinearMap.range (R : H →ₗ[ℂ] H))
  ext χ
  have h₂ : χ ∈ closure (range R) ↔
      χ ∈ (LinearMap.range (R : H →ₗ[ℂ] H)).topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    rfl
  rw [h₂, ← h₁, Submodule.mem_orthogonal]
  constructor
  · intro h ψ hψ
    refine h ψ ?_
    rw [Submodule.mem_orthogonal]
    rintro u ⟨v, rfl⟩
    have hψ' : R ψ = 0 := hψ
    change inner ℂ (R v) ψ = 0
    rw [← hsa, hψ', inner_zero_right]
  · intro h u hu
    refine h u ?_
    rw [Submodule.mem_orthogonal] at hu
    have h₃ : inner ℂ (R (R u)) u = 0 := hu _ ⟨R u, rfl⟩
    rw [← hsa] at h₃
    exact inner_self_eq_zero.mp h₃
end HilbertSpace
section Bridge
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type} [Fintype J] [Nonempty J]
private lemma hasSpectralMoments_iff (S : CommutingFamily H J) (ψ : H)
    (m : Measure (SpectralDomain J)) : HasSpectralMoments S ψ m ↔ IsSpectralMeasureOf S ψ m :=
  ⟨fun h => ⟨h.1, fun n y => (h.2 n y).symm⟩, fun h => ⟨h.1, fun n y => (h.2 n y).symm⟩⟩
private lemma spectralMomentMeasure_eq (S : CommutingFamily H J) (ψ : H) :
    spectralMomentMeasure S ψ = ScalarSpectralMeasures.spectralMeasure S ψ := by
  have h : HasSpectralMoments S ψ = IsSpectralMeasureOf S ψ :=
    funext fun m => propext (hasSpectralMoments_iff S ψ m)
  unfold spectralMomentMeasure ScalarSpectralMeasures.spectralMeasure
  rw [h]
private lemma quadMeasure_real (E : BorelPVM J H) (ψ : H)
    (Δ : MeasSubset J) : (E.quadMeasure ψ).real Δ.1 = ‖E Δ ψ‖ ^ 2 := by
  rw [measureReal_def, E.quadMeasure_apply ψ Δ, ENNReal.toReal_ofReal (by positivity)]
private lemma isFiniteMeasure_quadMeasure (E : BorelPVM J H) (ψ : H) :
    IsFiniteMeasure (E.quadMeasure ψ) :=
  ⟨(E.quadMeasure_apply ψ ⟨univ, MeasurableSet.univ⟩).trans_lt ENNReal.ofReal_lt_top⟩
private lemma inner_proj_eq_real (E : BorelPVM J H) (ψ : H) (Δ : MeasSubset J) :
    inner ℂ ψ (E Δ ψ) = (((E.quadMeasure ψ).real Δ.1 : ℝ) : ℂ) := by
  rw [quadMeasure_real, E.inner_apply_eq_norm_sq]
private def toPVM (E : BorelPVM J H) : ProjectionValuedMeasure J H where
  E := E.proj
  isStarProjection := E.isStarProj
  E_univ := E.proj_univ
  exists_scalarMeasure ψ :=
    ⟨E.quadMeasure ψ, isFiniteMeasure_quadMeasure E ψ, fun Δ => inner_proj_eq_real E ψ Δ⟩
private lemma measure_eq_of_real {μ ν : Measure (SpectralDomain J)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ Δ : MeasSubset J, μ.real Δ.1 = ν.real Δ.1) : μ = ν :=
  Measure.ext fun s hs =>
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top ν s)).mp (h ⟨s, hs⟩)
private lemma hasFirstMoments_toPVM {S : CommutingFamily H J} {E : BorelPVM J H}
    (hE : IsJointPVM S E) : HasFirstMoments S (toPVM E) := by
  intro ψ ρ hρ
  have hfin := hρ.1
  have hfin' := isFiniteMeasure_quadMeasure E ψ
  have hρE : ρ = E.quadMeasure ψ := measure_eq_of_real fun Δ =>
    Complex.ofReal_injective ((hρ.2 Δ).symm.trans (inner_proj_eq_real E ψ Δ))
  rw [hρE]
  exact ⟨hE.1 ψ, fun α => hE.2 α ψ⟩
private lemma proj_eq_joint (hF : FirstMoments.FirstMomentUniquenessStatement)
    {S : CommutingFamily H J} {E : BorelPVM J H}
    (hE : IsJointPVM S E) (Δ : MeasSubset J) :
    ⇑(E Δ) = jointSpectralMeasure S Δ.1 :=
  funext fun ψ => (hF H J S).2 (toPVM E) (hasFirstMoments_toPVM hE) Δ ψ
private lemma ext_of_proj_eq {E E' : BorelPVM J H}
    (h : ∀ Δ, ⇑(E Δ) = ⇑(E' Δ)) : E = E' := by
  obtain ⟨f, _, _, _, _⟩ := E
  obtain ⟨g, _, _, _, _⟩ := E'
  have hfg : f = g := funext fun Δ => DFunLike.coe_injective (h Δ)
  subst hfg
  rfl
private lemma exists_isJointPVM (hC : BorelCalculus.BorelCalculusStatement)
    (hF : FirstMoments.FirstMomentUniquenessStatement) (S : CommutingFamily H J) :
    ∃ E, IsJointPVM S E := by
  obtain ⟨P, hP, hM⟩ := (hF H J S).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, c11, -, -⟩ := hC H J S
  let E : BorelPVM J H :=
    { proj := P.E
      isStarProj := P.isStarProjection
      proj_univ := P.E_univ
      proj_inter := fun Δ Δ' => by
        refine ContinuousLinearMap.ext fun ψ => ?_
        have h := congrFun (c11 Δ.1 Δ'.1 Δ.2 Δ'.2) ψ
        rw [ContinuousLinearMap.mul_apply, hP Δ (P.E Δ' ψ), hP Δ' ψ,
          hP ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ ψ]
        exact h.symm
      hasSum_iUnion := fun ψ Δ hd => by
        obtain ⟨μ, hμ, hv⟩ := P.exists_scalarMeasure ψ
        have hm := measure_iUnion (μ := μ) (f := fun k => (Δ k).1) hd fun k => (Δ k).2
        have hs : (∑' k, μ (Δ k).1) ≠ ∞ := hm ▸ measure_ne_top μ _
        have h₁ := ENNReal.hasSum_toReal hs
        rw [← ENNReal.tsum_toReal_eq fun k => measure_ne_top μ _, ← hm] at h₁
        simp only [hv]
        exact Complex.hasSum_ofReal.mpr h₁ }
  have hsc : ∀ ψ, IsDiagonalMeasure P ψ (E.quadMeasure ψ) := fun ψ =>
    ⟨isFiniteMeasure_quadMeasure E ψ, fun Δ => inner_proj_eq_real E ψ Δ⟩
  exact ⟨E, fun ψ => (hM ψ _ (hsc ψ)).1, fun α ψ => (hM ψ _ (hsc ψ)).2 α⟩
section Calculus
variable {S : CommutingFamily H J} {E : BorelPVM J H}
  (hC : BorelCalculus.BorelCalculusStatement)
  (hF : FirstMoments.FirstMomentUniquenessStatement)
  (hE : IsJointPVM S E)
include hC hF hE
private lemma quadMeasure_eq (ψ : H) :
    E.quadMeasure ψ = ScalarSpectralMeasures.spectralMeasure S ψ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -, -, -⟩ := hC H J S
  refine Measure.ext fun s hs => (E.quadMeasure_apply ψ ⟨s, hs⟩).trans ?_
  rw [ofReal_sq_norm, ← (c10 s ψ hs).2, proj_eq_joint hF hE ⟨s, hs⟩]
private lemma spectralOp_spec {φ : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ) :
    integralDomain S φ = univ ∧ ⇑(E.spectralOp φ) = spectralIntegral S φ ∧
      E.IsSpectralIntegral φ (E.spectralOp φ) ∧
      (∀ A, E.IsSpectralIntegral φ A → A = E.spectralOp φ) := by
  obtain ⟨c1, -⟩ := hC H J S
  obtain ⟨-, -, -, hinner, hb⟩ := c1 φ hφ.1
  obtain ⟨hdom, C, hCf, -, hCu⟩ := hb hφ.2
  have hI : E.IsSpectralIntegral φ C := fun ψ => by
    rw [quadMeasure_eq hC hF hE, hCf]
    exact (hinner ψ (by simp [hdom])).2
  have hex : ∃ A, E.IsSpectralIntegral φ A := ⟨C, hI⟩
  have hspec : E.IsSpectralIntegral φ (E.spectralOp φ) := by
    unfold BorelPVM.spectralOp
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have huniq : ∀ A, E.IsSpectralIntegral φ A → A = C := fun A hA =>
    hCu A fun ψ => by rw [hA ψ, quadMeasure_eq hC hF hE]
  have hEq : E.spectralOp φ = C := huniq _ hspec
  exact ⟨hdom, by rw [hEq, hCf], hspec, fun A hA => (huniq A hA).trans hEq.symm⟩
private lemma mem_integralDomain {φ : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ) (ψ : H) :
    ψ ∈ integralDomain S φ := by
  rw [(spectralOp_spec hC hF hE hφ).1]
  exact mem_univ ψ
private lemma spectralOp_apply {φ : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ) (ψ : H) :
    E.spectralOp φ ψ = spectralIntegral S φ ψ :=
  congrFun (spectralOp_spec hC hF hE hφ).2.1 ψ
private lemma spectralOp_add_mul_eq {φ φ' : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ)
    (hφ' : IsBddMeasurable φ') (c : ℂ) :
    E.spectralOp (fun p => φ p + c * φ' p) = E.spectralOp φ + c • E.spectralOp φ' := by
  obtain ⟨-, -, -, c4, -⟩ := hC H J S
  refine ContinuousLinearMap.ext fun ψ => ?_
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    spectralOp_apply hC hF hE hφ, spectralOp_apply hC hF hE hφ',
    spectralOp_apply hC hF hE (hφ.add_mul hφ' c)]
  exact (c4 φ φ' hφ.1 hφ'.1 c ψ (mem_integralDomain hC hF hE hφ ψ)
    (mem_integralDomain hC hF hE hφ' ψ)).2
private lemma spectralOp_mul_eq {φ φ' : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ)
    (hφ' : IsBddMeasurable φ') :
    E.spectralOp (fun p => φ p * φ' p) = E.spectralOp φ * E.spectralOp φ' := by
  obtain ⟨-, -, -, -, -, -, -, c8, -⟩ := hC H J S
  refine ContinuousLinearMap.ext fun ψ => ?_
  rw [ContinuousLinearMap.mul_apply, spectralOp_apply hC hF hE hφ,
    spectralOp_apply hC hF hE hφ', spectralOp_apply hC hF hE (hφ.mul hφ')]
  exact congrFun (c8 φ φ' hφ.1 hφ'.1 hφ.2 hφ'.2).1 ψ
private lemma spectralOp_commute {φ φ' : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ)
    (hφ' : IsBddMeasurable φ') : Commute (E.spectralOp φ) (E.spectralOp φ') := by
  change E.spectralOp φ * E.spectralOp φ' = E.spectralOp φ' * E.spectralOp φ
  rw [← spectralOp_mul_eq hC hF hE hφ hφ', ← spectralOp_mul_eq hC hF hE hφ' hφ]
  exact congrArg E.spectralOp (funext fun p => mul_comm _ _)
private lemma spectralOp_indicator_eq {T : Set (SpectralDomain J)} (hT : MeasurableSet T) :
    E.spectralOp (T.indicator 1) = E ⟨T, hT⟩ :=
  DFunLike.coe_injective ((spectralOp_spec hC hF hE (isBddMeasurable_indicator hT)).2.1.trans
    (proj_eq_joint hF hE ⟨T, hT⟩).symm)
private lemma spectralOp_const_one : E.spectralOp (fun _ => (1 : ℂ)) = 1 := by
  have h := spectralOp_indicator_eq hC hF hE (T := univ) MeasurableSet.univ
  rw [indicator_univ] at h
  exact h.trans E.proj_univ
private lemma spectralOp_const_zero : E.spectralOp (fun _ => (0 : ℂ)) = 0 :=
  ((spectralOp_spec hC hF hE (φ := fun _ => 0) ⟨measurable_const, 0, fun _ => by simp⟩).2.2.2 0
    fun ψ => by simp).symm
private lemma spectralOp_level : E.spectralOp (fun p => (((p.1 : ℝ)) : ℂ)) = S.A :=
  ((spectralOp_spec hC hF hE isBddMeasurable_level).2.2.2 _ hE.1).symm
private lemma spectralOp_phase (l : J) :
    E.spectralOp (fun p => ((p.2 l : Circle) : ℂ)) = (S.B l : H →L[ℂ] H) :=
  ((spectralOp_spec hC hF hE (isBddMeasurable_phase l)).2.2.2 _ (hE.2 l)).symm
private lemma spectralOp_pow_eq {φ : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ) (n : ℕ) :
    E.spectralOp (fun p => φ p ^ n) = E.spectralOp φ ^ n := by
  induction n with
  | zero => simpa using spectralOp_const_one hC hF hE
  | succ n ih =>
      rw [pow_succ, ← ih, ← spectralOp_mul_eq hC hF hE (hφ.pow n) hφ]
      exact congrArg E.spectralOp (funext fun p => pow_succ _ _)
private lemma spectralOp_const_mul_eq {φ : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ)
    (c : ℂ) : E.spectralOp (fun p => c * φ p) = c • E.spectralOp φ := by
  have hz : IsBddMeasurable fun _ : SpectralDomain J => (0 : ℂ) :=
    ⟨measurable_const, 0, fun _ => by simp⟩
  have h := spectralOp_add_mul_eq hC hF hE hz hφ c
  rw [spectralOp_const_zero hC hF hE, zero_add] at h
  simpa using h
private lemma spectralOp_finsetSum (g : ℕ → SpectralDomain J → ℂ)
    (hg : ∀ k, IsBddMeasurable (g k)) (n : ℕ) :
    IsBddMeasurable (fun p => ∑ k ∈ Finset.range n, g k p) ∧
      E.spectralOp (fun p => ∑ k ∈ Finset.range n, g k p) =
        ∑ k ∈ Finset.range n, E.spectralOp (g k) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact ⟨⟨measurable_const, 0, fun _ => by simp⟩, spectralOp_const_zero hC hF hE⟩
  | succ n ih =>
      have h₁ := ih.1.add_mul (hg n) 1
      have h₂ := spectralOp_add_mul_eq hC hF hE ih.1 (hg n) 1
      simp only [one_mul, one_smul] at h₁ h₂
      simp only [Finset.sum_range_succ]
      exact ⟨h₁, by rw [h₂, ih.2]⟩
private lemma inner_spectralOp_conj {φ : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ)
    (ψ ψ' : H) :
    inner ℂ ψ' (E.spectralOp φ ψ) = inner ℂ (E.spectralOp (fun p => conj (φ p)) ψ') ψ := by
  obtain ⟨-, -, -, -, -, c6, -⟩ := hC H J S
  rw [spectralOp_apply hC hF hE hφ, spectralOp_apply hC hF hE hφ.conj]
  exact (c6 φ hφ.1).2.1 ψ (mem_integralDomain hC hF hE hφ ψ) ψ'
    (mem_integralDomain hC hF hE hφ ψ')
private lemma norm_spectralOp_apply_sq {φ : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ)
    (ψ : H) :
    ‖E.spectralOp φ ψ‖ ^ 2 = ∫ p, ‖φ p‖ ^ 2 ∂(spectralMomentMeasure S ψ) := by
  obtain ⟨c1, -⟩ := hC H J S
  have h := ((c1 φ hφ.1).2.2.2.1 ψ (mem_integralDomain hC hF hE hφ ψ)).1
  rw [spectralMomentMeasure_eq, integral_norm_sq_eq_sqNorm _ hφ.1, ← h,
    spectralOp_apply hC hF hE hφ, ENNReal.toReal_pow, toReal_enorm]
private lemma norm_spectralOp_le_iSup {φ : SpectralDomain J → ℂ} (hφ : IsBddMeasurable φ) :
    ‖E.spectralOp φ‖ ≤ ⨆ p, ‖φ p‖ := by
  obtain ⟨c1, -⟩ := hC H J S
  obtain ⟨-, C, hCf, hCn, -⟩ := (c1 φ hφ.1).2.2.2.2 hφ.2
  have hEq : E.spectralOp φ = C :=
    DFunLike.coe_injective ((spectralOp_spec hC hF hE hφ).2.1.trans hCf.symm)
  rw [hEq]
  exact hCn
private lemma boundedFunctionalCalculus_of : BoundedFunctionalCalculus S E where
  exists_spectralOp φ hφ := ⟨_, (spectralOp_spec hC hF hE hφ).2.2.1⟩
  spectralOp_add_smul φ φ' hφ hφ' c := spectralOp_add_mul_eq hC hF hE hφ hφ' c
  spectralOp_mul φ φ' hφ hφ' := spectralOp_mul_eq hC hF hE hφ hφ'
  inner_spectralOp φ hφ ψ ψ' := inner_spectralOp_conj hC hF hE hφ ψ ψ'
  norm_spectralOp_sq φ hφ ψ := norm_spectralOp_apply_sq hC hF hE hφ ψ
  integral_norm_sq_le φ hφ ψ := by
    rw [← norm_spectralOp_apply_sq hC hF hE hφ ψ, ← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    exact ((E.spectralOp φ).le_opNorm ψ).trans
      (mul_le_mul_of_nonneg_right (norm_spectralOp_le_iSup hC hF hE hφ) (norm_nonneg _))
  spectralOp_monomial n w := by
    obtain ⟨-, -, c3, -⟩ := hC H J S
    exact DFunLike.coe_injective
      ((spectralOp_spec hC hF hE (isBddMeasurable_spectralMonomial n w)).2.1.trans (c3 n w).2)
  momentMeasure_spectralOp φ hφ ψ := by
    obtain ⟨-, -, -, -, -, -, c7, -⟩ := hC H J S
    rw [spectralMomentMeasure_eq, spectralMomentMeasure_eq, spectralOp_apply hC hF hE hφ,
      (c7 φ hφ.1 ψ (mem_integralDomain hC hF hE hφ ψ)).1]
    unfold densityMeasure
    exact congrArg _ (funext fun p => (ofReal_sq_norm (φ p)).symm)
  spectralOp_congr φ φ' hφ hφ' Δ hΔ hoff := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, c13⟩ := hC H J S
    have hT : MeasurableSet {p | φ p ≠ φ' p} := (measurableSet_eq_fun hφ.1 hφ'.1).compl
    have hsub : {p | φ p ≠ φ' p} ∩ Δ.1 = {p | φ p ≠ φ' p} :=
      inter_eq_left.mpr fun p hp => by_contra fun h => hp (hoff p h)
    have h₀ : E ⟨{p | φ p ≠ φ' p}, hT⟩ = 0 := by
      have h₁ := E.proj_inter ⟨{p | φ p ≠ φ' p}, hT⟩ Δ
      have h₂ : (⟨{p | φ p ≠ φ' p} ∩ Δ.1, hT.inter Δ.2⟩ : MeasSubset J) =
          ⟨{p | φ p ≠ φ' p}, hT⟩ := Subtype.ext hsub
      rw [h₂] at h₁
      change E.proj _ = 0
      rw [h₁]
      rw [hΔ, mul_zero]
    have h₃ : jointSpectralMeasure S {p | φ p ≠ φ' p} = 0 := by
      rw [← show ⇑(E ⟨{p | φ p ≠ φ' p}, hT⟩) = _ from proj_eq_joint hF hE ⟨_, hT⟩, h₀]
      rfl
    exact DFunLike.coe_injective (((spectralOp_spec hC hF hE hφ).2.1.trans
      (c13 φ φ' hφ.1 hφ'.1 h₃).2).trans (spectralOp_spec hC hF hE hφ').2.1.symm)
variable (hU : CalculusApplications.CalculusApplicationsStatement)
include hU
private lemma boundedPointwise_of : BoundedPointwiseStrongConvergence E := by
  rintro φs φ hm hφ ⟨B, hB⟩ ht ψ
  obtain ⟨-, -, -, -, -, c6, -⟩ := hU H J S
  obtain ⟨A, D, hA, hD, hT⟩ := c6 φs φ hm hφ ⟨B, hB⟩ ht
  have hbφ : IsBddMeasurable φ :=
    ⟨hφ, B, fun p => le_of_tendsto (ht p).norm (Filter.Eventually.of_forall fun k => hB k p)⟩
  have e₁ : E.spectralOp φ = D :=
    DFunLike.coe_injective ((spectralOp_spec hC hF hE hbφ).2.1.trans hD.symm)
  have e₂ : ∀ k, E.spectralOp (φs k) = A k := fun k =>
    DFunLike.coe_injective ((spectralOp_spec hC hF hE ⟨hm k, B, hB k⟩).2.1.trans (hA k).symm)
  simp only [e₁, e₂]
  exact tendsto_iff_norm_sub_tendsto_zero.mp (hT ψ)
private lemma proj_eq_zero_iff_joint (Δ : MeasSubset J) :
    E Δ = 0 ↔ jointSpectralMeasure S Δ.1 = 0 := by
  rw [← proj_eq_joint hF hE Δ]
  exact ⟨fun h => by rw [h]; rfl, fun h => ContinuousLinearMap.ext fun ψ => congrFun h ψ⟩
private lemma realFunctionalCalculus_of : RealFunctionalCalculus E := by
  intro φ hφ hb
  obtain ⟨c1, -⟩ := hU H J S
  obtain ⟨C, hCf, hsa, hpos⟩ := c1 φ hφ hb
  obtain ⟨B, hB⟩ := hb
  have hbb : IsBddMeasurable fun p => (φ p : ℂ) :=
    ⟨Complex.measurable_ofReal.comp hφ, B, fun p => by simpa using hB p⟩
  have e : E.spectralOp (fun p => (φ p : ℂ)) = C :=
    DFunLike.coe_injective ((spectralOp_spec hC hF hE hbb).2.1.trans hCf.symm)
  rw [e]
  refine ⟨hsa, hpos.trans ?_⟩
  unfold BorelPVM.IsSupportedOn
  rw [proj_eq_zero_iff_joint hC hF hE hU]
  have hset : {p | 0 ≤ φ p}ᶜ = {p | φ p < 0} := by
    ext p
    simp
  change _ ↔ jointSpectralMeasure S ({p | 0 ≤ φ p}ᶜ) = 0
  rw [hset]
private lemma isOrthProjOnto_of_joint (Δ : MeasSubset J) {P : H →L[ℂ] H} {M : Set H}
    (hP : ⇑P = jointSpectralMeasure S Δ.1)
    (h : YangMills.Construction.HilbertSpaceBasics.IsOrthProjOnto P M) :
    IsOrthProjOnto (E Δ) M := by
  have e : E Δ = P := DFunLike.coe_injective ((proj_eq_joint hF hE Δ).trans hP.symm)
  exact ⟨E.isStarProj Δ, by rw [e]; exact h.2⟩
private lemma kernelProjections_of : KernelProjections S E where
  oneLevel := by
    obtain ⟨-, -, -, ⟨P, hP, h⟩, -⟩ := hU H J S
    refine isOrthProjOnto_of_joint hC hF hE hU (levelOneSet J) (hP.trans ?_) h
    refine congrArg _ ?_
    ext p
    change (p.1 : ℝ) = 1 ↔ p.1 = 1
    exact ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
  zeroLevel := by
    obtain ⟨-, -, ⟨P, hP, h⟩, -⟩ := hU H J S
    refine isOrthProjOnto_of_joint hC hF hE hU (levelZeroSet J) (hP.trans ?_) h
    refine congrArg _ ?_
    ext p
    change (p.1 : ℝ) = 0 ↔ p.1 = 0
    exact ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
  phaseFixed l := by
    obtain ⟨-, -, -, -, c5, -⟩ := hU H J S
    obtain ⟨P, hP, h⟩ := c5 l
    exact isOrthProjOnto_of_joint hC hF hE hU (phaseOneSet l) hP h
  tendsto_pow := by
    have hT := (levelOneSet J).2
    have h := boundedPointwise_of hC hF hE hU (fun k p => (((p.1 : ℝ)) : ℂ) ^ k)
      ((levelOneSet J).1.indicator 1)
      (fun k => (isBddMeasurable_level.pow k).1) (isBddMeasurable_indicator hT).1
      ⟨1, fun k p => by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
        exact pow_le_one₀ p.1.2.1 p.1.2.2⟩
      (fun p => by
        by_cases hp : p ∈ (levelOneSet J).1
        · have h₁ : (p.1 : ℝ) = 1 := congrArg Subtype.val (show p.1 = 1 from hp)
          rw [indicator_of_mem hp, h₁]
          simp
        · have h₁ : (p.1 : ℝ) ≠ 1 := fun e => hp (Subtype.ext e)
          have h₂ : ‖(((p.1 : ℝ)) : ℂ)‖ < 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
            exact lt_of_le_of_ne p.1.2.2 h₁
          rw [indicator_of_notMem hp]
          exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h₂)
    have e₁ : (fun k => E.spectralOp fun p => (((p.1 : ℝ)) : ℂ) ^ k) = fun k => S.A ^ k :=
      funext fun k => by
        rw [spectralOp_pow_eq hC hF hE isBddMeasurable_level, spectralOp_level hC hF hE]
    rw [e₁, spectralOp_indicator_eq hC hF hE hT] at h
    exact h
  tendsto_cesaro l := by
    have hT := (phaseOneSet l).2
    have hg : ∀ k, IsBddMeasurable fun p : SpectralDomain J => ((p.2 l : Circle) : ℂ) ^ k :=
      fun k => (isBddMeasurable_phase l).pow k
    have hmean : ∀ n, IsBddMeasurable (cesaroMean (J := J) l n) := fun n =>
      ⟨measurable_const.mul (spectralOp_finsetSum hC hF hE _ hg n).1.1, 1,
        norm_cesaroMean_le l n⟩
    have h := boundedPointwise_of hC hF hE hU (cesaroMean l)
      ((phaseOneSet l).1.indicator 1) (fun n => (hmean n).1)
      (isBddMeasurable_indicator hT).1 ⟨1, norm_cesaroMean_le l⟩ (tendsto_cesaroMean l)
    have e₁ : (fun n => E.spectralOp (cesaroMean l n)) =
        fun n : ℕ => (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, (S.B l : H →L[ℂ] H) ^ k :=
      funext fun n => by
        have h₁ := spectralOp_finsetSum hC hF hE _ hg n
        change E.spectralOp
          (fun p => (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, ((p.2 l : Circle) : ℂ) ^ k) = _
        rw [spectralOp_const_mul_eq hC hF hE h₁.1, h₁.2]
        refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
        rw [spectralOp_pow_eq hC hF hE (isBddMeasurable_phase l), spectralOp_phase hC hF hE]
    rw [e₁, spectralOp_indicator_eq hC hF hE hT] at h
    exact h
private lemma spectralSqrtProperties_of : SpectralSqrtProperties S E := by
  have hb := isBddMeasurable_sqrtLevel (J := J)
  have hK := kernelProjections_of hC hF hE hU
  have hsa : IsSelfAdjoint (spectralSqrt E) :=
    (realFunctionalCalculus_of hC hF hE hU _ measurable_sqrtLevel ⟨1, abs_sqrtLevel_le⟩).1
  have hker : {ψ | spectralSqrt E ψ = 0} = {ψ | S.A ψ = 0} := by
    obtain ⟨-, c2, -⟩ := hU H J S
    obtain ⟨P, C, hP, hCf, h⟩ := c2 _ hb.1 hb.2
    have e : spectralSqrt E = C :=
      DFunLike.coe_injective ((spectralOp_spec hC hF hE hb).2.1.trans hCf.symm)
    have hset : {p : SpectralDomain J | (((p.1 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 0} =
        (levelZeroSet J).1 := by
      ext p
      simp only [mem_setOf_eq, Complex.ofReal_eq_zero]
      rw [Real.rpow_eq_zero p.1.2.1 (by norm_num)]
      change (p.1 : ℝ) = 0 ↔ p.1 = 0
      exact ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
    have hpr := isOrthProjOnto_of_joint hC hF hE hU (levelZeroSet J)
      (hP.trans (congrArg _ hset)) h
    rw [e]
    exact hpr.2.symm.trans hK.zeroLevel.2
  have hPQ : E (positiveLevelSet J) + E (levelZeroSet J) = 1 := by
    have h := spectralOp_add_mul_eq hC hF hE
      (isBddMeasurable_indicator (positiveLevelSet J).2)
      (isBddMeasurable_indicator (levelZeroSet J).2) 1
    rw [spectralOp_indicator_eq hC hF hE (positiveLevelSet J).2,
      spectralOp_indicator_eq hC hF hE (levelZeroSet J).2, one_smul] at h
    refine h.symm.trans (Eq.trans ?_ (spectralOp_const_one hC hF hE))
    refine congrArg E.spectralOp (funext fun p => ?_)
    by_cases hp : p ∈ (positiveLevelSet J).1
    · have hz : p ∉ (levelZeroSet J).1 := fun hz => by
        have h₀ : (p.1 : ℝ) = 0 := congrArg Subtype.val (show p.1 = 0 from hz)
        exact (ne_of_gt (show (0 : ℝ) < p.1 from hp)) h₀
      rw [indicator_of_mem hp, indicator_of_notMem hz]
      simp
    · have hz : p ∈ (levelZeroSet J).1 := by
        change p.1 = 0
        exact Subtype.ext (le_antisymm (not_lt.mp hp) p.1.2.1)
      rw [indicator_of_notMem hp, indicator_of_mem hz]
      simp
  have hrange : range (E (positiveLevelSet J)) = orthSet {ψ | S.A ψ = 0} := by
    rw [range_eq_orthSet (E.isStarProj _) hPQ, hK.zeroLevel.2]
  refine ⟨hsa, ?_, ?_, fun l => ?_, ?_, hrange⟩
  · refine ((spectralOp_mul_eq hC hF hE hb hb).symm.trans ?_).trans (spectralOp_level hC hF hE)
    refine congrArg E.spectralOp (funext fun p => ?_)
    rw [← Complex.ofReal_mul, ← Real.sqrt_eq_rpow, Real.mul_self_sqrt p.1.2.1]
  · have h := spectralOp_commute hC hF hE hb isBddMeasurable_level
    rw [spectralOp_level hC hF hE] at h
    exact h
  · have h := spectralOp_commute hC hF hE hb (isBddMeasurable_phase l)
    rw [spectralOp_phase hC hF hE] at h
    exact h
  · rw [closure_range_eq_orthSet hsa, hker, hrange]
end Calculus
end Bridge
theorem jointSpectralCalculusTheorem_of_calculus
    (hS : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (hC : BorelCalculus.BorelCalculusStatement)
    (hU : CalculusApplications.CalculusApplicationsStatement)
    (hF : FirstMoments.FirstMomentUniquenessStatement) :
    JointSpectralCalculusTheorem := by
  intro H _ _ _ J _ _ S
  refine ⟨fun ψ => ?_, ?_, fun E hE => ⟨?_, boundedFunctionalCalculus_of hC hF hE,
    boundedPointwise_of hC hF hE hU, realFunctionalCalculus_of hC hF hE hU,
    kernelProjections_of hC hF hE hU, spectralSqrtProperties_of hC hF hE hU, ?_⟩⟩
  · obtain ⟨-, -, -, c4, -⟩ := hS H J S
    have h₁ := (hasSpectralMoments_iff S ψ _).mpr (c4 ψ).1
    have h₂ : HasSpectralMoments S ψ (spectralMomentMeasure S ψ) := by
      rw [spectralMomentMeasure_eq]
      exact h₁
    exact ⟨⟨_, h₁, fun m hm => (c4 ψ).2.1 m ((hasSpectralMoments_iff S ψ m).mp hm)⟩, h₂⟩
  · obtain ⟨E, hE⟩ := exists_isJointPVM hC hF S
    exact ⟨E, hE, fun E' hE' => ext_of_proj_eq fun Δ =>
      (proj_eq_joint hF hE' Δ).trans (proj_eq_joint hF hE Δ).symm⟩
  · intro ψ Δ
    rw [spectralMomentMeasure_eq, ← quadMeasure_eq hC hF hE ψ]
    exact inner_proj_eq_real E ψ Δ
  · intro H' _ _ _ S' E' hE' W hW
    obtain ⟨-, -, -, -, -, -, c7⟩ := hU H' J S'
    have hiso : LatticeBasics.IsIsometricMap (W : H' →ₗ[ℂ] H) := fun ψ => by
      have h := hW.inner_map ψ ψ
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
      have h' : ‖W ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'
    obtain ⟨t₁, t₂, -⟩ := c7 H S (W : H' →ₗ[ℂ] H) hiso
      (fun ψ => DFunLike.congr_fun hW.intertwine_A ψ)
      (fun l ψ => DFunLike.congr_fun (hW.intertwine_B l) ψ)
    refine ⟨fun ψ => ?_, fun φ hφ => ContinuousLinearMap.ext fun ψ => ?_⟩
    · rw [spectralMomentMeasure_eq, spectralMomentMeasure_eq]
      exact (t₁ ψ).symm
    · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        spectralOp_apply hC hF hE' hφ, spectralOp_apply hC hF hE hφ]
      exact ((t₂ φ hφ.1 ψ).2 (mem_integralDomain hC hF hE' hφ ψ)).symm
end YangMills.Construction.FormHilbert
