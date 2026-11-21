import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.HilbertWellDefined
open OneLoopNotation ComplexHilbert SesquilinearForms HilbertToolkit ProjectionMeasures
theorem isPosSemidefHermitianForm_of_isPosSemidefForm {V : Type} [AddCommGroup V] [Module ℂ V]
    {q : V → V → ℂ} (hq : IsPosSemidefForm q) :
    FormCompletion.IsPosSemidefHermitianForm q := by
  have him : ∀ F, (q F F).im = 0 := fun F => (Complex.le_def.1 (hq.nonneg F)).2.symm
  have hre : ∀ F, 0 ≤ (q F F).re := fun F => by simpa using (Complex.le_def.1 (hq.nonneg F)).1
  refine ⟨hq.add_left, hq.smul_left, hq.add_right, hq.smul_right, fun F F' => ?_, hre⟩
  have h₁ := him (F + F')
  have h₂ := him (F + Complex.I • F')
  simp only [hq.add_left, hq.add_right, hq.smul_left, hq.smul_right] at h₁ h₂
  simp [him] at h₁ h₂
  apply Complex.ext
  · simp
    linarith
  · simp
    linarith
theorem formPairCondition_holds (hc : FormCompletion.FormCompletionIsHilbertSpace) :
    FormPairCondition := by
  intro V _ _ q hq
  have hh := isPosSemidefHermitianForm_of_isPosSemidefForm hq
  refine ⟨hh, ?_⟩
  obtain ⟨hA, hB, -⟩ := hc V q hh
  obtain ⟨-, -, -, -, hadd, hsmul, -, -⟩ := hA
  obtain ⟨-, -, -, -, -, hmap, hinner, -, hdense⟩ := hB
  let cl : V →ₗ[ℂ] FormQuotientCompletion q :=
    { toFun := quotientClass q
      map_add' := fun F F' => FormCompletion.asMap_injective (by
        simp only [quotientClass, FormCompletion.asMap_add, hmap, hadd])
      map_smul' := fun z F => FormCompletion.asMap_injective (by
        simp only [quotientClass, RingHom.id_apply, FormCompletion.asMap_smul, hmap, hsmul]) }
  refine ⟨cl, fun _ => rfl, ?_, hinner⟩
  change seqClosureOf (Set.range (FormCompletion.classVec q)) = Set.univ
  rw [seqClosureOf_eq_closure]
  exact hdense.closure_eq
theorem adjointSelfAdjointCondition_holds : AdjointSelfAdjointCondition := by
  intro H _ _ _ A
  have hex : IsAdjointOp A (ContinuousLinearMap.adjoint A) := fun χ χ' =>
    ContinuousLinearMap.adjoint_inner_left A χ' χ
  have hsp : IsAdjointOp A (adjointOp A) := Classical.epsilon_spec ⟨_, hex⟩
  constructor
  · intro h x y
    have h₁ := hsp x y
    rw [h] at h₁
    exact h₁.symm
  · intro h
    refine ContinuousLinearMap.ext fun χ => ext_inner_right ℂ fun χ' => ?_
    rw [hsp χ χ']
    exact h χ χ'
theorem decomp_sum_integral_simpleFunc {μ : FourBorelSet → ℂ} {r : ℕ} {c : Fin r → ℂ}
    {m : Fin r → Measure (Fin 4 → ℝ)} (hw : HasMeasureDecomposition μ c m)
    (s : SimpleFunc (Fin 4 → ℝ) ℂ) :
    ∑ k, c k * ∫ p, s p ∂(m k) =
      ∑ x ∈ s.range, μ ⟨s ⁻¹' {x}, s.measurableSet_fiber x⟩ * x := by
  have h₁ : ∀ k, ∫ p, s p ∂(m k) = ∑ x ∈ s.range, (((m k) (s ⁻¹' {x})).toReal : ℂ) * x := by
    intro k
    have := hw.isFinite k
    rw [SimpleFunc.integral_eq_sum s (SimpleFunc.integrable_of_isFiniteMeasure s)]
    simp [Complex.real_smul, measureReal_def]
  simp only [h₁, hw.apply_eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => by ring
theorem tendsto_decomp_sum_integral {μ : FourBorelSet → ℂ} {r : ℕ} {c : Fin r → ℂ}
    {m : Fin r → Measure (Fin 4 → ℝ)} (hw : HasMeasureDecomposition μ c m)
    {u : (Fin 4 → ℝ) → ℂ} {b : ℝ} (s : ℕ → SimpleFunc (Fin 4 → ℝ) ℂ)
    (hbound : ∀ n p, ‖s n p‖ ≤ b) (hlim : ∀ p, Tendsto (fun n => s n p) atTop (𝓝 (u p))) :
    Tendsto (fun n => ∑ k, c k * ∫ p, s n p ∂(m k)) atTop (𝓝 (∑ k, c k * ∫ p, u p ∂(m k))) := by
  refine tendsto_finsetSum _ fun k _ => Tendsto.const_mul _ ?_
  have := hw.isFinite k
  exact tendsto_integral_of_dominated_convergence (fun _ => b)
    (fun n => (s n).aestronglyMeasurable) (integrable_const b)
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
theorem decomp_sum_integral_eq {μ : FourBorelSet → ℂ} {u : (Fin 4 → ℝ) → ℂ}
    (hu : IsBddMeasurableFun u)
    {r : ℕ} {c : Fin r → ℂ} {m : Fin r → Measure (Fin 4 → ℝ)} (hw : HasMeasureDecomposition μ c m)
    {r' : ℕ} {c' : Fin r' → ℂ} {m' : Fin r' → Measure (Fin 4 → ℝ)}
    (hw' : HasMeasureDecomposition μ c' m') :
    ∑ k, c k * ∫ p, u p ∂(m k) = ∑ k, c' k * ∫ p, u p ∂(m' k) := by
  obtain ⟨hm, b, hb⟩ := hu
  have hs := hm.stronglyMeasurable
  have hb₀ : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have hbound : ∀ n p, ‖hs.approxBounded b n p‖ ≤ b := fun n p =>
    hs.norm_approxBounded_le hb₀ n p
  have hlim : ∀ p, Tendsto (fun n => hs.approxBounded b n p) atTop (𝓝 (u p)) := fun p =>
    hs.tendsto_approxBounded_of_norm_le (hb p)
  have h₁ := tendsto_decomp_sum_integral hw _ hbound hlim
  have h₂ := tendsto_decomp_sum_integral hw' _ hbound hlim
  simp only [decomp_sum_integral_simpleFunc hw] at h₁
  simp only [decomp_sum_integral_simpleFunc hw'] at h₂
  exact tendsto_nhds_unique h₁ h₂
theorem integralIndependence_holds : IntegralIndependence := by
  intro μ u hμ hu
  obtain ⟨r, c, m, hw⟩ := hμ
  have hex : ∃ z, IsDecompIntegral μ u z := ⟨_, r, c, m, hw, rfl⟩
  refine ⟨hex, fun z hz => ?_⟩
  have hsp : IsDecompIntegral μ u (complexMeasureIntegral μ u) := Classical.epsilon_spec hex
  obtain ⟨r₁, c₁, m₁, hw₁, rfl⟩ := hz
  obtain ⟨r₂, c₂, m₂, hw₂, he⟩ := hsp
  rw [he]
  exact decomp_sum_integral_eq hu hw₁ hw₂
section Weak
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Type} [TopologicalSpace P] [MeasureSpace P] [OpensMeasurableSpace P]
  {C : Set P} {Ξ : P → H} {φ : P → ℂ}
theorem integrableOn_weakIntegrand_inner (hi : HasWeakIntegrandData C Ξ φ) (χ : H) :
    IntegrableOn (fun x => φ x * ⟪χ, Ξ x⟫_ℂ) C := by
  obtain ⟨b, hb⟩ := hi.norm_bdd
  have hφ : Integrable φ (volume.restrict C) := hi.integrableOn
  have hm : AEStronglyMeasurable (fun x => ⟪χ, Ξ x⟫_ℂ) (volume.restrict C) :=
    (hi.continuousOn_inner χ).aestronglyMeasurable hi.measurableSet
  refine Integrable.mono' (hφ.norm.mul_const (‖χ‖ * b)) (hφ.aestronglyMeasurable.mul hm) ?_
  filter_upwards [ae_restrict_mem hi.measurableSet] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm χ (Ξ x)).trans
    (mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg χ))) (norm_nonneg _)
theorem exists_norm_integral_weakIntegrand_le (hi : HasWeakIntegrandData C Ξ φ) :
    ∃ M : ℝ, ∀ χ : H, ‖∫ x in C, φ x * ⟪χ, Ξ x⟫_ℂ‖ ≤ M * ‖χ‖ := by
  obtain ⟨b, hb⟩ := hi.norm_bdd
  have hφ : Integrable φ (volume.restrict C) := hi.integrableOn
  refine ⟨(∫ x in C, ‖φ x‖) * b, fun χ => ?_⟩
  have h₁ := norm_integral_le_of_norm_le (hφ.norm.mul_const (b * ‖χ‖))
    (f := fun x => φ x * ⟪χ, Ξ x⟫_ℂ) (by
      filter_upwards [ae_restrict_mem hi.measurableSet] with x hx
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm χ (Ξ x)).trans ?_) (norm_nonneg _)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg χ))
  rw [integral_mul_const] at h₁
  linarith [h₁, mul_assoc (∫ x in C, ‖φ x‖) b ‖χ‖]
theorem exists_hasWeakIntegral (hi : HasWeakIntegrandData C Ξ φ) :
    ∃ v, HasWeakIntegral C Ξ φ v := by
  obtain ⟨M, hM⟩ := exists_norm_integral_weakIntegrand_le hi
  let f : H →ₗ[ℂ] ℂ :=
    { toFun := fun χ => conj (∫ x in C, φ x * ⟪χ, Ξ x⟫_ℂ)
      map_add' := fun χ χ' => by
        simp only [inner_add_left, mul_add]
        rw [integral_add (integrableOn_weakIntegrand_inner hi χ)
          (integrableOn_weakIntegrand_inner hi χ'), map_add]
      map_smul' := fun z χ => by
        have h₁ : ∀ x, φ x * ⟪z • χ, Ξ x⟫_ℂ = conj z * (φ x * ⟪χ, Ξ x⟫_ℂ) := fun x => by
          rw [inner_smul_left]
          ring
        simp only [h₁, integral_const_mul, map_mul, Complex.conj_conj, RingHom.id_apply,
          smul_eq_mul] }
  let F : StrongDual ℂ H := f.mkContinuous M fun χ => by
    change ‖conj (∫ x in C, φ x * ⟪χ, Ξ x⟫_ℂ)‖ ≤ _
    rw [RCLike.norm_conj]
    exact hM χ
  refine ⟨(InnerProductSpace.toDual ℂ H).symm F, fun χ => ?_⟩
  have h₁ : ⟪(InnerProductSpace.toDual ℂ H).symm F, χ⟫_ℂ = conj (∫ x in C, φ x * ⟪χ, Ξ x⟫_ℂ) :=
    InnerProductSpace.toDual_symm_apply
  rw [← inner_conj_symm, h₁, Complex.conj_conj]
end Weak
theorem weakIntegralUnique_holds : WeakIntegralUnique := by
  intro H _ _ _ P _ _ _ C Ξ φ hi
  have hsp : HasWeakIntegral C Ξ φ (weakInt C Ξ φ) :=
    Classical.epsilon_spec (exists_hasWeakIntegral hi)
  refine ⟨hsp, fun v hv => ext_inner_left ℂ fun χ => ?_⟩
  rw [hv χ, hsp χ]
theorem wellDefinedStatement_holds (hc : FormCompletion.FormCompletionIsHilbertSpace) :
    WellDefinedStatement :=
  ⟨formPairCondition_holds hc, adjointSelfAdjointCondition_holds, integralIndependence_holds,
    weakIntegralUnique_holds⟩
end YangMills.Construction.HilbertWellDefined
