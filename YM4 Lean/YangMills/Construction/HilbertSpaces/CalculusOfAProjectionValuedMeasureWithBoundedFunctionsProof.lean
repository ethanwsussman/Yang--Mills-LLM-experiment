import YangMills.Construction.EuclideanSpectral.ProjMeasureBoundedCalculus
import YangMills.Construction.HilbertSpaces.CalculusOfAProjectionValuedMeasureWithBoundedFunctions
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.PVMCalculus
open OneLoopNotation ComplexHilbert HilbertToolkit ProjectionMeasures
abbrev euclidEquiv : (Fin 4 → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 4) :=
  MeasurableEquiv.toLp 2 (Fin 4 → ℝ)
def toEuclideanBorel (S : FourBorelSet) : EuclideanSpectral.BorelSubset 4 :=
  ⟨euclidEquiv.symm ⁻¹' S.1, euclidEquiv.symm.measurable S.2⟩
theorem ofEuclideanBorel_toEuclideanBorel (S : FourBorelSet) :
    ofEuclideanBorel (toEuclideanBorel S) = S :=
  Subtype.ext (by
    ext p
    simp [ofEuclideanBorel, toEuclideanBorel])
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isAdjointOp_adjointOp (A : BddOp H) : IsAdjointOp A (adjointOp A) :=
  Classical.epsilon_spec (p := IsAdjointOp A)
    ⟨ContinuousLinearMap.adjoint A, fun x y => ContinuousLinearMap.adjoint_inner_left A y x⟩
theorem adjointOp_eq_of_isAdjointOp {A B : BddOp H} (h : IsAdjointOp A B) : adjointOp A = B :=
  ContinuousLinearMap.ext fun y => ext_inner_right ℂ fun x => by
    rw [isAdjointOp_adjointOp A, h]
theorem isOrthProjection_iff (A : BddOp H) :
    IsOrthProjection A ↔ (∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) ∧ ∀ x, A (A x) = A x := by
  constructor
  · intro h
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · have := isAdjointOp_adjointOp A x y
      rwa [h.adjoint_self] at this
    · have := congrArg (fun B : BddOp H => B x) h.idempotent
      simpa [pow_two] using this.symm
  · rintro ⟨h₁, h₂⟩
    exact ⟨adjointOp_eq_of_isAdjointOp h₁, ContinuousLinearMap.ext fun x => by simp [pow_two, h₂]⟩
theorem inner_eq_polarization (A : H →ₗ[ℂ] H) (x y : H) :
    ⟪x, A y⟫_ℂ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, Complex.I ^ (-(k : ℤ)) *
      ⟪x + Complex.I ^ k • y, A (x + Complex.I ^ k • y)⟫_ℂ := by
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, h2]; ring
  have hz1 : Complex.I ^ (-1 : ℤ) = -Complex.I := by simp [zpow_neg]
  have hz2 : Complex.I ^ (-2 : ℤ) = -1 := by
    rw [zpow_neg]; norm_cast; rw [h2]; norm_num
  have hz3 : Complex.I ^ (-3 : ℤ) = Complex.I := by
    rw [zpow_neg]; norm_cast; rw [h3]; simp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add, map_smul, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, h2, h3]
  norm_num [hz1, hz2, hz3]
  ring_nf
  simp only [Complex.I_sq]
  ring
end Operators
section Exponentials
theorem isBddMeasurableFun_expChar (a : Fin 4 → ℝ) :
    IsBddMeasurableFun (expChar a) := by
  have hc : Continuous (expChar a) := by
    unfold expChar dotFour
    fun_prop
  refine ⟨hc.measurable, 1, fun p => ?_⟩
  rw [expChar, mul_comm, Complex.norm_exp_ofReal_mul_I]
theorem expChar_neg (a p : Fin 4 → ℝ) : expChar (-a) p = conj (expChar a p) := by
  simp [expChar, dotFour, ← Complex.exp_conj]
theorem measure_eq_of_integral_expChar (ν₁ ν₂ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂]
    (h : ∀ a, ∫ p, expChar a p ∂ν₁ = ∫ p, expChar a p ∂ν₂) : ν₁ = ν₂ := by
  apply euclidEquiv.map_measurableEquiv_injective
  have := Measure.isFiniteMeasure_map ν₁ euclidEquiv
  have := Measure.isFiniteMeasure_map ν₂ euclidEquiv
  apply Measure.ext_of_charFun
  funext t
  have ht : ∀ ν : Measure (Fin 4 → ℝ), charFun (ν.map euclidEquiv) t =
      ∫ p, expChar (WithLp.ofLp t) p ∂ν := fun ν => by
    rw [charFun_apply, integral_map_equiv]
    congr 1
    funext p
    simp [expChar, dotFour, PiLp.inner_apply, mul_comm]
  rw [ht, ht, h]
theorem isFiniteMeasure_sum_smul {r : ℕ} (m : Fin r → Measure (Fin 4 → ℝ))
    (hm : ∀ k, IsFiniteMeasure (m k)) (c : Fin r → NNReal) :
    IsFiniteMeasure (∑ k, c k • m k) :=
  Finset.sum_induction _ (fun ν : Measure (Fin 4 → ℝ) => IsFiniteMeasure ν)
    (fun _ _ h₁ h₂ => inferInstance) inferInstance (fun k _ => inferInstance)
theorem integral_sum_smul {r : ℕ} (m : Fin r → Measure (Fin 4 → ℝ))
    (hm : ∀ k, IsFiniteMeasure (m k)) (c : Fin r → NNReal) {g : (Fin 4 → ℝ) → ℂ}
    (hg : IsBddMeasurableFun g) :
    ∫ p, g p ∂(∑ k, c k • m k) = ∑ k, ((c k : ℝ) : ℂ) * ∫ p, g p ∂(m k) := by
  obtain ⟨hgm, b, hb⟩ := hg
  rw [integral_finsetSum_measure fun k _ =>
    Integrable.of_bound hgm.aestronglyMeasurable b (Eventually.of_forall hb)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
theorem sum_mul_measure_eq_zero {r : ℕ} (m : Fin r → Measure (Fin 4 → ℝ))
    (hm : ∀ k, IsFiniteMeasure (m k)) (f : Fin r → ℝ)
    (h : ∀ a, ∑ k, ((f k : ℝ) : ℂ) * ∫ p, expChar a p ∂(m k) = 0)
    {s : Set (Fin 4 → ℝ)} (hs : MeasurableSet s) : ∑ k, f k * (m k s).toReal = 0 := by
  have key : ∀ g, IsBddMeasurableFun g → ∑ k, ((f k : ℝ) : ℂ) * ∫ p, g p ∂(m k) =
      ∫ p, g p ∂(∑ k, (f k).toNNReal • m k) - ∫ p, g p ∂(∑ k, (-f k).toNNReal • m k) := fun g hg => by
    rw [integral_sum_smul m hm _ hg, integral_sum_smul m hm _ hg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_mul, ← Complex.ofReal_sub, Real.coe_toNNReal', Real.coe_toNNReal',
      max_zero_sub_max_neg_zero_eq_self]
  have h₁ := isFiniteMeasure_sum_smul m hm fun k => (f k).toNNReal
  have h₂ := isFiniteMeasure_sum_smul m hm fun k => (-f k).toNNReal
  have e : (∑ k, (f k).toNNReal • m k) = ∑ k, (-f k).toNNReal • m k :=
    measure_eq_of_integral_expChar _ _ fun a => sub_eq_zero.1 (by
      rw [← key _ (isBddMeasurableFun_expChar a)]
      exact h a)
  have hb : IsBddMeasurableFun (s.indicator fun _ => (1 : ℂ)) :=
    ⟨measurable_const.indicator hs, 1, fun p => by
      by_cases hp : p ∈ s <;> simp [hp]⟩
  have h₃ := key _ hb
  rw [e, sub_self] at h₃
  have h₄ : ∀ k, ∫ p, s.indicator (fun _ => (1 : ℂ)) p ∂(m k) = (((m k s).toReal : ℝ) : ℂ) :=
    fun k => by
      rw [integral_indicator_const _ hs]
      simp [Measure.real]
  simp only [h₄] at h₃
  exact_mod_cast h₃
theorem complexMeasureDeterminedByCharFun_holds
    (hW : HilbertWellDefined.WellDefinedStatement) :
    ComplexMeasureDeterminedByCharFun := by
  rintro μ ⟨r, c, m, hw⟩ h S
  have hm := hw.isFinite
  have hS : ∀ a, ∑ k, c k * ∫ p, expChar a p ∂(m k) = 0 := fun a => by
    rw [(hW.2.2.1 μ _ ⟨r, c, m, hw⟩ (isBddMeasurableFun_expChar a)).2 _
      ⟨r, c, m, hw, rfl⟩]
    exact h a
  have hconj : ∀ a, ∑ k, conj (c k) * ∫ p, expChar a p ∂(m k) = 0 := fun a => by
    have h₁ := congrArg conj (hS (-a))
    simp only [map_sum, map_mul, map_zero, ← integral_conj, expChar_neg,
      Complex.conj_conj] at h₁
    exact h₁
  have hre : ∀ a, ∑ k, (((c k).re : ℝ) : ℂ) * ∫ p, expChar a p ∂(m k) = 0 := fun a => by
    have h₁ : ∑ k, (((c k).re : ℝ) : ℂ) * ∫ p, expChar a p ∂(m k) =
        (1 / 2 : ℂ) * (∑ k, c k * ∫ p, expChar a p ∂(m k) +
          ∑ k, conj (c k) * ∫ p, expChar a p ∂(m k)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← add_mul, Complex.add_conj]
      push_cast
      ring
    rw [h₁, hS, hconj]
    simp
  have him : ∀ a, ∑ k, (((c k).im : ℝ) : ℂ) * ∫ p, expChar a p ∂(m k) = 0 := fun a => by
    have h₁ : ∑ k, (((c k).im : ℝ) : ℂ) * ∫ p, expChar a p ∂(m k) =
        (1 / (2 * Complex.I)) * (∑ k, c k * ∫ p, expChar a p ∂(m k) -
          ∑ k, conj (c k) * ∫ p, expChar a p ∂(m k)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← sub_mul, Complex.sub_conj]
      push_cast
      field_simp
    rw [h₁, hS, hconj]
    simp
  have r₁ := sum_mul_measure_eq_zero m hm _ hre S.2
  have r₂ := sum_mul_measure_eq_zero m hm _ him S.2
  rw [hw.apply_eq S]
  have h₁ : ∑ k, c k * (((m k S.1).toReal : ℝ) : ℂ) =
      ((∑ k, (c k).re * (m k S.1).toReal : ℝ) : ℂ) +
        ((∑ k, (c k).im * (m k S.1).toReal : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    nth_rewrite 1 [← Complex.re_add_im (c k)]
    ring
  rw [h₁, r₁, r₂]
  simp
end Exponentials
section Bridge
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def toProjMeasure (E : FourBorelSet → BddOp H) (hE : IsPVM E) :
    EuclideanSpectral.ProjMeasure H 4 where
  toFun B := (E (ofEuclideanBorel B) : H →ₗ[ℂ] H)
  isOrthProj B := by
    obtain ⟨h₁, h₂⟩ := (isOrthProjection_iff _).1 (hE.isProj (ofEuclideanBorel B))
    exact ⟨LinearMap.ext fun x => h₂ x, h₁⟩
  univ_eq_id := by
    have h : ofEuclideanBorel (EuclideanSpectral.BorelSubset.univ 4) =
        FourBorelSet.univ := Subtype.ext rfl
    rw [h, hE.univ_eq]
    rfl
  hasSum_diag ψ B hB := by
    have h := hE.sigma_additive ψ (fun k => ofEuclideanBorel (B k)) (fun k l hkl =>
      (hB hkl).preimage _)
    have heq : FourBorelSet.iUnion (fun k => ofEuclideanBorel (B k)) =
        ofEuclideanBorel (EuclideanSpectral.BorelSubset.unionSeq B) :=
      Subtype.ext (by
        ext p
        simp [FourBorelSet.iUnion, ofEuclideanBorel,
          EuclideanSpectral.BorelSubset.unionSeq])
    rw [heq] at h
    exact h
variable {E : FourBorelSet → BddOp H} (hE : IsPVM E)
theorem toProjMeasure_apply (B : EuclideanSpectral.BorelSubset 4) (x : H) :
    toProjMeasure E hE B x = E (ofEuclideanBorel B) x := rfl
theorem toProjMeasure_toEuclideanBorel (S : FourBorelSet) :
    toProjMeasure E hE (toEuclideanBorel S) = (E S : H →ₗ[ℂ] H) :=
  LinearMap.ext fun x => by rw [toProjMeasure_apply, ofEuclideanBorel_toEuclideanBorel]; rfl
theorem eq_toProjMeasure (F : EuclideanSpectral.ProjMeasure H 4)
    (h : ∀ B, ⇑(F B) = ⇑(E (ofEuclideanBorel B))) : F = toProjMeasure E hE := by
  have h₁ : F.toFun = (toProjMeasure E hE).toFun :=
    funext fun B => LinearMap.ext fun x => congrFun (h B) x
  generalize toProjMeasure E hE = G at h₁ ⊢
  cases F
  cases G
  cases h₁
  rfl
def diagPos (ψ : H) : Measure (Fin 4 → ℝ) :=
  ((toProjMeasure E hE).diagMeasure ψ).map euclidEquiv.symm
variable (hF : EuclideanSpectral.ProjMeasureBasicFacts)
  (hC : EuclideanSpectral.ProjMeasureBoundedCalculus)
  (hW : HilbertWellDefined.WellDefinedStatement)
include hE hF
theorem isFiniteMeasure_diagPos (ψ : H) : IsFiniteMeasure (diagPos hE ψ) := by
  have h := ((hF H 4 (toProjMeasure E hE)).2.2.1 ψ).1.1
  exact Measure.isFiniteMeasure_map _ _
theorem inner_apply_eq_diagPos (ψ : H) (S : FourBorelSet) :
    ⟪ψ, E S ψ⟫_ℂ = (((diagPos hE ψ S.1).toReal : ℝ) : ℂ) := by
  have h := ((hF H 4 (toProjMeasure E hE)).2.2.1 ψ).1.2 (toEuclideanBorel S)
  have h₁ : (toProjMeasure E hE).diag ψ (toEuclideanBorel S) = ⟪ψ, E S ψ⟫_ℂ := by
    change ⟪ψ, E (ofEuclideanBorel (toEuclideanBorel S)) ψ⟫_ℂ = _
    rw [ofEuclideanBorel_toEuclideanBorel]
  rw [← h₁, h, diagPos, Measure.map_apply euclidEquiv.symm.measurable S.2]
  rfl
theorem eq_diagPos {ψ : H} (m : Measure (Fin 4 → ℝ)) [IsFiniteMeasure m]
    (h : ∀ S : FourBorelSet, ⟪ψ, E S ψ⟫_ℂ = (((m S.1).toReal : ℝ) : ℂ)) : m = diagPos hE ψ := by
  have := isFiniteMeasure_diagPos hE hF ψ
  refine Measure.ext fun s hs => ?_
  have h₁ := (h ⟨s, hs⟩).symm.trans (inner_apply_eq_diagPos hE hF ψ ⟨s, hs⟩)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    (Complex.ofReal_injective h₁)
omit hF in
theorem integral_diagPos (ψ : H) (u : (Fin 4 → ℝ) → ℂ) :
    ∫ p, u p ∂(diagPos hE ψ) =
      ∫ x, (u ∘ euclidEquiv.symm) x ∂((toProjMeasure E hE).diagMeasure ψ) :=
  integral_map_equiv _ _
theorem integrable_diagPos (ψ : H) {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) :
    Integrable u (diagPos hE ψ) := by
  have := isFiniteMeasure_diagPos hE hF ψ
  obtain ⟨hm, b, hb⟩ := hu
  exact Integrable.of_bound hm.aestronglyMeasurable b (Eventually.of_forall hb)
theorem hasMeasureDecomposition_spectralScalarMeasure (x y : H) :
    HasMeasureDecomposition (spectralScalarMeasure E x y)
      (fun k : Fin 4 => (1 / 4 : ℂ) * Complex.I ^ (-((k : ℕ) : ℤ)))
      (fun k : Fin 4 => diagPos hE (x + Complex.I ^ (k : ℕ) • y)) where
  length_pos := by norm_num
  isFinite k := isFiniteMeasure_diagPos hE hF _
  apply_eq S := by
    have h := inner_eq_polarization (E S : H →ₗ[ℂ] H) x y
    rw [Finset.sum_range, Finset.mul_sum] at h
    refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
    have h₁ := inner_apply_eq_diagPos hE hF (x + Complex.I ^ (k : ℕ) • y) S
    change _ * (_ * ⟪x + Complex.I ^ (k : ℕ) • y, E S (x + Complex.I ^ (k : ℕ) • y)⟫_ℂ) = _
    rw [h₁]
    ring
theorem isFinComplexMeasure_spectralScalarMeasure (x y : H) :
    IsFinComplexMeasure (spectralScalarMeasure E x y) :=
  ⟨4, _, _, hasMeasureDecomposition_spectralScalarMeasure hE hF x y⟩
include hW
theorem complexMeasureIntegral_spectralScalarMeasure (x y : H) {u : (Fin 4 → ℝ) → ℂ}
    (hu : IsBddMeasurableFun u) :
    complexMeasureIntegral (spectralScalarMeasure E x y) u =
      ∑ k : Fin 4, ((1 / 4 : ℂ) * Complex.I ^ (-((k : ℕ) : ℤ))) *
        ∫ p, u p ∂(diagPos hE (x + Complex.I ^ (k : ℕ) • y)) :=
  ((hW.2.2.1 _ u (isFinComplexMeasure_spectralScalarMeasure hE hF x y) hu).2 _
    ⟨4, _, _, hasMeasureDecomposition_spectralScalarMeasure hE hF x y, rfl⟩).symm
theorem hasWeakIntegrals_of_inner_self {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u)
    (A : BddOp H) (h : ∀ ψ, ⟪ψ, A ψ⟫_ℂ = ∫ p, u p ∂(diagPos hE ψ)) :
    HasWeakIntegrals E u A := by
  intro x y
  rw [complexMeasureIntegral_spectralScalarMeasure hE hF hW x y hu]
  have h₁ := inner_eq_polarization (A : H →ₗ[ℂ] H) x y
  rw [Finset.sum_range, Finset.mul_sum] at h₁
  refine h₁.trans (Finset.sum_congr rfl fun k _ => ?_)
  change _ * (_ * ⟪x + Complex.I ^ (k : ℕ) • y, A (x + Complex.I ^ (k : ℕ) • y)⟫_ℂ) = _
  rw [h]
  ring
omit hF hW hE in
theorem eq_of_hasWeakIntegrals {u : (Fin 4 → ℝ) → ℂ} {A B : BddOp H}
    (hA : HasWeakIntegrals E u A) (hB : HasWeakIntegrals E u B) : A = B :=
  ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => by rw [hA, hB]
theorem pvmIntegral_eq_of_inner_self {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u)
    (A : BddOp H) (h : ∀ ψ, ⟪ψ, A ψ⟫_ℂ = ∫ p, u p ∂(diagPos hE ψ)) :
    pvmIntegral E u = A := by
  have hg := hasWeakIntegrals_of_inner_self hE hF hW hu A h
  exact eq_of_hasWeakIntegrals
    (Classical.epsilon_spec (p := HasWeakIntegrals E u) ⟨A, hg⟩) hg
omit hW hF hE in
theorem isBoundedBorelFn_comp_symm {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) :
    EuclideanSpectral.ProjMeasure.IsBoundedBorelFn (u ∘ euclidEquiv.symm) := by
  obtain ⟨hm, b, hb⟩ := hu
  exact ⟨hm.comp euclidEquiv.symm.measurable, b, fun x => hb _⟩
omit hW hE in
theorem isWeakIntegralOp_boundedIntegral (F : EuclideanSpectral.ProjMeasure H 4)
    {f : EuclideanSpace ℝ (Fin 4) → ℂ}
    (hf : EuclideanSpectral.ProjMeasure.IsBoundedBorelFn f) :
    F.IsWeakIntegralOp f (F.boundedIntegral f) :=
  Classical.epsilon_spec (p := F.IsWeakIntegralOp f)
    (((hF H 4 F).2.2.2.2.2.2 f hf.1 hf.2).1.exists)
omit hW in
theorem apply_empty : E ⟨∅, MeasurableSet.empty⟩ = 0 := by
  have h := (hF H 4 (toProjMeasure E hE)).2.2.2.2.1.1
  have e : toEuclideanBorel ⟨∅, MeasurableSet.empty⟩ = ⟨∅, MeasurableSet.empty⟩ := Subtype.ext rfl
  apply ContinuousLinearMap.coe_injective
  rw [← toProjMeasure_toEuclideanBorel hE, e, h]
  rfl
omit hW in
theorem mul_apply_eq_inter (S S' : FourBorelSet) : E S * E S' = E ⟨S.1 ∩ S'.1, S.2.inter S'.2⟩ := by
  have h := (hF H 4 (toProjMeasure E hE)).2.2.2.2.1.2.2 (toEuclideanBorel S) (toEuclideanBorel S')
  have e : (⟨(toEuclideanBorel S).1 ∩ (toEuclideanBorel S').1,
      (toEuclideanBorel S).2.inter (toEuclideanBorel S').2⟩ :
        EuclideanSpectral.BorelSubset 4) =
      toEuclideanBorel ⟨S.1 ∩ S'.1, S.2.inter S'.2⟩ := Subtype.ext rfl
  rw [e, toProjMeasure_toEuclideanBorel, toProjMeasure_toEuclideanBorel,
    toProjMeasure_toEuclideanBorel] at h
  exact ContinuousLinearMap.coe_injective h
omit hW in
theorem isSupportedOn_univ : IsSupportedOn E FourBorelSet.univ := by
  have e : FourBorelSet.univ.compl = ⟨∅, MeasurableSet.empty⟩ := Subtype.ext (by
    simp [FourBorelSet.univ, FourBorelSet.compl])
  rw [IsSupportedOn, e]
  exact apply_empty hE hF
omit hF hW in
theorem isSupportedOn_iff_supports (B : EuclideanSpectral.BorelSubset 4) :
    IsSupportedOn E (ofEuclideanBorel B) ↔
      EuclideanSpectral.ProjMeasure.Supports B (toProjMeasure E hE) := by
  have e : ofEuclideanBorel B.compl = (ofEuclideanBorel B).compl :=
    Subtype.ext (by
      ext p
      simp [ofEuclideanBorel, FourBorelSet.compl,
        EuclideanSpectral.BorelSubset.compl])
  change E (ofEuclideanBorel B).compl = 0 ↔ (E (ofEuclideanBorel B.compl) : H →ₗ[ℂ] H) = 0
  rw [e]
  exact ⟨fun h => by rw [h]; rfl, fun h => ContinuousLinearMap.coe_injective h⟩
include hC
omit hW in
theorem exists_bddOp_eq_boundedIntegral {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u)
    {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) :
    ∃ T : BddOp H,
      (∀ x, T x = (toProjMeasure E hE).boundedIntegral (u ∘ euclidEquiv.symm) x) ∧
      ‖T‖ ≤ ⨆ p : S₀.1, ‖u p‖ := by
  have hcar : EuclideanSpectral.ProjMeasure.Supports
      (toEuclideanBorel S₀) (toProjMeasure E hE) := by
    rw [← isSupportedOn_iff_supports hE, ofEuclideanBorel_toEuclideanBorel]
    exact hS
  obtain ⟨-, T, hT, hn⟩ := (hC H 4 (toProjMeasure E hE)).2.1.2.2 _ (isBoundedBorelFn_comp_symm hu) _ hcar
  refine ⟨T, fun x => by rw [← hT]; rfl, hn.trans_eq ?_⟩
  have e : (fun x => ‖(u ∘ euclidEquiv.symm) x‖) '' (toEuclideanBorel S₀).1 =
      Set.range (fun p : S₀.1 => ‖u p‖) := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨euclidEquiv.symm x, hx⟩, rfl⟩
    · rintro ⟨⟨p, hp⟩, rfl⟩
      exact ⟨euclidEquiv p, by simpa [toEuclideanBorel] using hp, by simp⟩
  rw [e]
  rfl
theorem pvmIntegral_apply {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) (x : H) :
    pvmIntegral E u x = (toProjMeasure E hE).boundedIntegral (u ∘ euclidEquiv.symm) x := by
  obtain ⟨T, hT, -⟩ := exists_bddOp_eq_boundedIntegral hE hF hC hu (isSupportedOn_univ hE hF)
  have h : pvmIntegral E u = T := pvmIntegral_eq_of_inner_self hE hF hW hu T fun ψ => by
    rw [hT, isWeakIntegralOp_boundedIntegral hF _ (isBoundedBorelFn_comp_symm hu) ψ, integral_diagPos]
  rw [h, hT]
theorem inner_pvmIntegral_self {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) (ψ : H) :
    ⟪ψ, pvmIntegral E u ψ⟫_ℂ = ∫ p, u p ∂(diagPos hE ψ) := by
  rw [pvmIntegral_apply hE hF hC hW hu,
    isWeakIntegralOp_boundedIntegral hF _ (isBoundedBorelFn_comp_symm hu) ψ, integral_diagPos]
theorem hasWeakIntegrals_pvmIntegral {u : (Fin 4 → ℝ) → ℂ}
    (hu : IsBddMeasurableFun u) : HasWeakIntegrals E u (pvmIntegral E u) :=
  hasWeakIntegrals_of_inner_self hE hF hW hu _ (inner_pvmIntegral_self hE hF hC hW hu)
theorem norm_pvmIntegral_apply_sq {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) (x : H) :
    ‖pvmIntegral E u x‖ ^ 2 = ∫ p, ‖u p‖ ^ 2 ∂(diagPos hE x) := by
  rw [pvmIntegral_apply hE hF hC hW hu,
    (hC H 4 (toProjMeasure E hE)).2.1.1 _ (isBoundedBorelFn_comp_symm hu) x]
  exact (integral_map_equiv euclidEquiv.symm (fun p => ‖u p‖ ^ 2)).symm
omit hC hW in
theorem scalarMeasureFacts_holds {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) :
    ScalarMeasureFacts E S₀ := by
  refine ⟨apply_empty hE hF, mul_apply_eq_inter hE hF, fun x => ⟨?_, ?_, ?_⟩, fun x y =>
    ⟨fun S => inner_eq_polarization (E S : H →ₗ[ℂ] H) x y, isFinComplexMeasure_spectralScalarMeasure hE hF x y⟩⟩
  · exact ⟨diagPos hE x, isFiniteMeasure_diagPos hE hF x, inner_apply_eq_diagPos hE hF x⟩
  · simp [spectralScalarMeasure, hE.univ_eq, inner_self_eq_norm_sq_to_K]
  · rw [IsSupportedOn] at hS
    simp [spectralScalarMeasure, hS]
theorem pvmIntegral_linear_comb (c c' : ℂ) {u u' : (Fin 4 → ℝ) → ℂ}
    (hu : IsBddMeasurableFun u) (hu' : IsBddMeasurableFun u') :
    pvmIntegral E (fun p => c * u p + c' * u' p) =
      c • pvmIntegral E u + c' • pvmIntegral E u' := by
  obtain ⟨hm, b, hb⟩ := id hu
  obtain ⟨hm', b', hb'⟩ := id hu'
  have hl : IsBddMeasurableFun fun p => c * u p + c' * u' p :=
    ⟨(measurable_const.mul hm).add (measurable_const.mul hm'), ‖c‖ * b + ‖c'‖ * b', fun p => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb' p) (norm_nonneg _)⟩
  refine pvmIntegral_eq_of_inner_self hE hF hW hl _ fun ψ => ?_
  have h₁ := integrable_diagPos hE hF ψ hu
  have h₂ := integrable_diagPos hE hF ψ hu'
  rw [integral_add (h₁.const_mul c) (h₂.const_mul c'), integral_const_mul, integral_const_mul]
  change ⟪ψ, c • pvmIntegral E u ψ + c' • pvmIntegral E u' ψ⟫_ℂ = _
  simp only [inner_add_right, inner_smul_right, inner_pvmIntegral_self hE hF hC hW hu,
    inner_pvmIntegral_self hE hF hC hW hu']
theorem pvmIntegralBasic_holds {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) :
    PvmIntegralBasic E S₀ := by
  refine ⟨fun u hu => ⟨hasWeakIntegrals_pvmIntegral hE hF hC hW hu, fun A hA =>
    eq_of_hasWeakIntegrals hA (hasWeakIntegrals_pvmIntegral hE hF hC hW hu), ?_⟩,
    fun c c' u u' hu hu' => pvmIntegral_linear_comb hE hF hC hW c c' hu hu'⟩
  obtain ⟨T, hT, hn⟩ := exists_bddOp_eq_boundedIntegral hE hF hC hu hS
  have h : pvmIntegral E u = T := ContinuousLinearMap.ext fun x => by
    rw [pvmIntegral_apply hE hF hC hW hu, hT]
  rw [h]
  exact hn
omit hC in
theorem pvmIntegral_indicator_one (S : FourBorelSet) :
    pvmIntegral E (S.1.indicator fun _ => (1 : ℂ)) = E S := by
  have hb : IsBddMeasurableFun (S.1.indicator fun _ => (1 : ℂ)) :=
    ⟨measurable_const.indicator S.2, 1, fun p => by
      by_cases hp : p ∈ S.1 <;> simp [hp]⟩
  refine pvmIntegral_eq_of_inner_self hE hF hW hb _ fun ψ => ?_
  have := isFiniteMeasure_diagPos hE hF ψ
  rw [inner_apply_eq_diagPos hE hF ψ S, integral_indicator_const _ S.2]
  simp [Measure.real]
theorem pvmIntegralRules_holds : PvmIntegralRules E := by
  have hcalc := hC H 4 (toProjMeasure E hE)
  refine ⟨fun u u' hu hu' => ?_, fun u hu => ?_, pvmIntegral_indicator_one hE hF hW, ?_⟩
  · obtain ⟨hm, b, hb⟩ := id hu
    obtain ⟨hm', b', hb'⟩ := id hu'
    have hl : IsBddMeasurableFun fun p => u p * u' p :=
      ⟨hm.mul hm', b * b', fun p => by
        rw [norm_mul]
        exact mul_le_mul (hb p) (hb' p) (norm_nonneg _) ((norm_nonneg _).trans (hb p))⟩
    refine ContinuousLinearMap.ext fun x => ?_
    change _ = pvmIntegral E u (pvmIntegral E u' x)
    rw [pvmIntegral_apply hE hF hC hW hl, pvmIntegral_apply hE hF hC hW hu',
      pvmIntegral_apply hE hF hC hW hu]
    exact congrArg (fun L : H →ₗ[ℂ] H => L x)
      (hcalc.2.2.1 _ _ (isBoundedBorelFn_comp_symm hu) (isBoundedBorelFn_comp_symm hu'))
  · obtain ⟨hm, b, hb⟩ := id hu
    have hl : IsBddMeasurableFun fun p => conj (u p) :=
      ⟨Complex.continuous_conj.measurable.comp hm, b, fun p => by simpa using hb p⟩
    refine adjointOp_eq_of_isAdjointOp fun x y => ?_
    rw [pvmIntegral_apply hE hF hC hW hl, pvmIntegral_apply hE hF hC hW hu]
    exact hcalc.2.2.2.1 _ (isBoundedBorelFn_comp_symm hu) x y
  · have h := pvmIntegral_indicator_one hE hF hW FourBorelSet.univ
    rw [hE.univ_eq] at h
    simpa [FourBorelSet.univ] using h
omit hC hW in
theorem ae_mem_diagPos {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) (ψ : H) :
    ∀ᵐ p ∂(diagPos hE ψ), p ∈ S₀.1 := by
  have := isFiniteMeasure_diagPos hE hF ψ
  have h := inner_apply_eq_diagPos hE hF ψ S₀.compl
  rw [IsSupportedOn] at hS
  rw [hS] at h
  have h₁ : (diagPos hE ψ S₀.compl.1).toReal = 0 := by
    have : (((diagPos hE ψ S₀.compl.1).toReal : ℝ) : ℂ) = 0 := by
      rw [← h]
      simp
    exact_mod_cast this
  have h₂ := (ENNReal.toReal_eq_zero_iff _).1 h₁
  exact ae_iff.2 (h₂.resolve_right (measure_ne_top _ _))
omit hE hF hC hW in
theorem isBddMeasurableFun_indicator {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u)
    (S : FourBorelSet) : IsBddMeasurableFun (S.1.indicator u) := by
  obtain ⟨hm, b, hb⟩ := hu
  refine ⟨hm.indicator S.2, |b|, fun p => ?_⟩
  by_cases hp : p ∈ S.1
  · simpa [hp] using (hb p).trans (le_abs_self b)
  · simp [hp]
theorem pvmIntegral_indicator_of_supported {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀)
    {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) :
    pvmIntegral E (S₀.1.indicator u) = pvmIntegral E u := by
  refine pvmIntegral_eq_of_inner_self hE hF hW (isBddMeasurableFun_indicator hu S₀) _ fun ψ => ?_
  rw [inner_pvmIntegral_self hE hF hC hW hu]
  exact integral_congr_ae ((ae_mem_diagPos hE hF hS ψ).mono fun p hp =>
    (Set.indicator_of_mem hp u).symm)
omit hE hF hC hW in
theorem isBddMeasurableFun_one_mul_add_neg_one_mul {u u' : (Fin 4 → ℝ) → ℂ}
    (hu : IsBddMeasurableFun u) (hu' : IsBddMeasurableFun u') :
    IsBddMeasurableFun fun p => (1 : ℂ) * u p + (-1 : ℂ) * u' p := by
  obtain ⟨hm, b, hb⟩ := hu
  obtain ⟨hm', b', hb'⟩ := hu'
  refine ⟨(measurable_const.mul hm).add (measurable_const.mul hm'), b + b', fun p => ?_⟩
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> simpa using by first | exact hb p | exact hb' p
theorem tendsto_pvmIntegral_apply {w : ℕ → (Fin 4 → ℝ) → ℂ} {g : (Fin 4 → ℝ) → ℂ} {b : ℝ}
    (hw : ∀ j, IsBddMeasurableFun (w j)) (hg : IsBddMeasurableFun g)
    (hb : ∀ j p, ‖w j p‖ ≤ b) (hgb : ∀ p, ‖g p‖ ≤ b)
    (hl : ∀ p, Tendsto (fun j => w j p) atTop (𝓝 (g p))) (x : H) :
    Tendsto (fun j => pvmIntegral E (w j) x) atTop (𝓝 (pvmIntegral E g x)) := by
  have := isFiniteMeasure_diagPos hE hF x
  have hd := fun j => isBddMeasurableFun_one_mul_add_neg_one_mul (hw j) hg
  have hsq : ∀ j, ‖pvmIntegral E (w j) x - pvmIntegral E g x‖ ^ 2 =
      ∫ p, ‖(1 : ℂ) * w j p + (-1 : ℂ) * g p‖ ^ 2 ∂(diagPos hE x) := fun j => by
    rw [← norm_pvmIntegral_apply_sq hE hF hC hW (hd j) x,
      pvmIntegral_linear_comb hE hF hC hW 1 (-1) (hw j) hg]
    simp [sub_eq_add_neg]
  have hint : Tendsto (fun j => ∫ p, ‖(1 : ℂ) * w j p + (-1 : ℂ) * g p‖ ^ 2 ∂(diagPos hE x))
      atTop (𝓝 (∫ _, (0 : ℝ) ∂(diagPos hE x))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (b + b) ^ 2)
      (fun j => ((hd j).1.norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun j => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
    · have h₁ : ‖(1 : ℂ) * w j p + (-1 : ℂ) * g p‖ ≤ b + b := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · simpa using hb j p
        · simpa using hgb p
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    · have h₁ : Tendsto (fun j => (1 : ℂ) * w j p + (-1 : ℂ) * g p) atTop
          (𝓝 ((1 : ℂ) * g p + (-1 : ℂ) * g p)) :=
        ((hl p).const_mul 1).add tendsto_const_nhds
      have h₂ := (h₁.norm).pow 2
      simpa using h₂
  simp only [integral_zero] at hint
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h₃ := (Real.continuous_sqrt.tendsto 0).comp hint
  simp only [Real.sqrt_zero] at h₃
  refine h₃.congr fun j => ?_
  simp only [Function.comp_apply, ← hsq j]
  exact Real.sqrt_sq (norm_nonneg _)
theorem pvmIntegralNormAndConvergence_holds {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) :
    PvmIntegralNormAndConvergence E S₀ := by
  refine ⟨fun u hu x => ?_, fun T v τ u hv hb hl => ?_⟩
  · obtain ⟨hm, b, hb⟩ := id hu
    have hw : IsBddMeasurableFun fun p => ((‖u p‖ ^ 2 : ℝ) : ℂ) :=
      ⟨Complex.measurable_ofReal.comp (hm.norm.pow_const 2), b ^ 2, fun p => by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb p) 2⟩
    rw [← hasWeakIntegrals_pvmIntegral hE hF hC hW hw x x,
      inner_pvmIntegral_self hE hF hC hW hw, norm_pvmIntegral_apply_sq hE hF hC hW hu]
    exact (integral_ofReal).symm
  · obtain ⟨b, hb⟩ := hb
    have hwb : ∀ j p, ‖S₀.1.indicator (v (τ j)) p‖ ≤ |b| := fun j p => by
      by_cases hp : p ∈ S₀.1
      · simpa [hp] using (hb (τ j) p hp).trans (le_abs_self b)
      · simp [hp]
    have hwl : ∀ p, Tendsto (fun j => S₀.1.indicator (v (τ j)) p) atTop
        (𝓝 (S₀.1.indicator u p)) := fun p => by
      by_cases hp : p ∈ S₀.1
      · simpa [hp] using hl p hp
      · simp [hp]
    have hgm : Measurable (S₀.1.indicator u) :=
      measurable_of_tendsto_metrizable (fun j => ((hv (τ j)).1.indicator S₀.2))
        (tendsto_pi_nhds.2 hwl)
    have hgb : ∀ p, ‖S₀.1.indicator u p‖ ≤ |b| := fun p =>
      le_of_tendsto (hwl p).norm (Eventually.of_forall fun j => hwb j p)
    have hg : IsBddMeasurableFun (S₀.1.indicator u) := ⟨hgm, |b|, hgb⟩
    have main : ∀ x : H, Tendsto (fun j => pvmIntegral E (v (τ j)) x) atTop
        (𝓝 (pvmIntegral E (S₀.1.indicator u) x)) := fun x => by
      have h := tendsto_pvmIntegral_apply hE hF hC hW
        (fun j => isBddMeasurableFun_indicator (hv (τ j)) S₀) hg hwb hgb hwl x
      simpa only [pvmIntegral_indicator_of_supported hE hF hC hW hS (hv _)] using h
    refine ⟨main, fun hu x => ?_⟩
    rw [← pvmIntegral_indicator_of_supported hE hF hC hW hS hu]
    exact main x
omit hC hW in
theorem apply_eq_zero_of_subset {S S' : FourBorelSet} (hs : S.1 ⊆ S'.1) (h : E S' = 0) :
    E S = 0 := by
  have h₁ := mul_apply_eq_inter hE hF S S'
  have e : (⟨S.1 ∩ S'.1, S.2.inter S'.2⟩ : FourBorelSet) = S :=
    Subtype.ext (Set.inter_eq_left.2 hs)
  rw [e, h, mul_zero] at h₁
  exact h₁.symm
theorem pushforwardFacts_holds {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) :
    PushforwardFacts E S₀ := by
  intro m hm
  have hP : IsPVM (pushforward E m hm) := by
    refine ⟨fun S => hE.isProj _, ?_, fun x S hd => ?_⟩
    · have e : (⟨m ⁻¹' FourBorelSet.univ.1, hm FourBorelSet.univ.2⟩ : FourBorelSet) =
          FourBorelSet.univ := Subtype.ext rfl
      rw [pushforward, e, hE.univ_eq]
    · have h := hE.sigma_additive x (fun k => ⟨m ⁻¹' (S k).1, hm (S k).2⟩)
        (fun k l hkl => (hd hkl).preimage _)
      have e : FourBorelSet.iUnion (fun k => (⟨m ⁻¹' (S k).1, hm (S k).2⟩ : FourBorelSet)) =
          ⟨m ⁻¹' (FourBorelSet.iUnion S).1, hm (FourBorelSet.iUnion S).2⟩ :=
        Subtype.ext (by
          ext p
          simp [FourBorelSet.iUnion])
      rw [e] at h
      exact h
  refine ⟨hP, fun S₁ hs => ?_, fun u hu => ?_⟩
  · refine apply_eq_zero_of_subset hE hF (S' := S₀.compl) (fun p hp hp₀ => hp (hs hp₀)) hS
  · obtain ⟨hum, b, hb⟩ := id hu
    have hc : IsBddMeasurableFun (u ∘ m) := ⟨hum.comp hm, b, fun p => hb _⟩
    refine pvmIntegral_eq_of_inner_self hP hF hW hu _ fun ψ => ?_
    have := isFiniteMeasure_diagPos hE hF ψ
    have := Measure.isFiniteMeasure_map (diagPos hE ψ) m
    have e : (diagPos hE ψ).map m = diagPos hP ψ := eq_diagPos hP hF _ fun S => by
      rw [Measure.map_apply hm S.2]
      exact inner_apply_eq_diagPos hE hF ψ ⟨m ⁻¹' S.1, hm S.2⟩
    rw [inner_pvmIntegral_self hE hF hC hW hc, ← e,
      integral_map hm.aemeasurable hum.aestronglyMeasurable]
    rfl
section Conjugate
variable {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
omit hE hF hC hW in
theorem unitaryIsometry_apply {V : H' →ₗ[ℂ] H} (hV : IsUnitaryMap V)
    (x : H') : unitaryIsometry hV x = V x := rfl
omit hE hF hC hW in
theorem inner_unitaryConj {V : H' →ₗ[ℂ] H} (hV : IsUnitaryMap V)
    (A : BddOp H) (x y : H') :
    ⟪x, unitaryConj hV A y⟫_ℂ = ⟪V x, A (V y)⟫_ℂ := by
  have h := (unitaryIsometry hV).inner_map_map x ((unitaryIsometry hV).symm (A (V y)))
  rw [LinearIsometryEquiv.apply_symm_apply, unitaryIsometry_apply] at h
  exact h.symm
omit hE hF hC hW in
theorem unitaryConj_apply_unitaryConj_apply {V : H' →ₗ[ℂ] H} (hV : IsUnitaryMap V)
    (A B : BddOp H) (x : H') :
    unitaryConj hV A (unitaryConj hV B x) = unitaryConj hV (A * B) x := by
  change (unitaryIsometry hV).symm (A (unitaryIsometry hV
    ((unitaryIsometry hV).symm (B (unitaryIsometry hV x))))) =
      (unitaryIsometry hV).symm (A (B (unitaryIsometry hV x)))
  rw [LinearIsometryEquiv.apply_symm_apply]
end Conjugate
theorem unitaryConjFacts_holds {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) :
    UnitaryConjFacts E S₀ := by
  intro H' _ _ _ V hV
  have hP : IsPVM (fun S => unitaryConj hV (E S)) := by
    refine ⟨fun S => ?_, ?_, fun x S hd => ?_⟩
    · obtain ⟨h₁, h₂⟩ := (isOrthProjection_iff _).1 (hE.isProj S)
      refine (isOrthProjection_iff _).2 ⟨fun x y => ?_, fun x => ?_⟩
      · rw [inner_unitaryConj, ← inner_conj_symm, inner_unitaryConj, inner_conj_symm, h₁]
      · rw [unitaryConj_apply_unitaryConj_apply]
        have : E S * E S = E S := ContinuousLinearMap.ext h₂
        rw [this]
    · refine ContinuousLinearMap.ext fun x => ?_
      rw [hE.univ_eq]
      change (unitaryIsometry hV).symm (unitaryIsometry hV x) = x
      simp
    · have h := hE.sigma_additive (V x) S hd
      simpa only [inner_unitaryConj] using h
  refine ⟨hP, ?_, fun u hu => ?_⟩
  · change unitaryConj hV (E S₀.compl) = 0
    rw [IsSupportedOn] at hS
    rw [hS]
    refine ContinuousLinearMap.ext fun x => ?_
    change (unitaryIsometry hV).symm 0 = 0
    simp
  · refine pvmIntegral_eq_of_inner_self hP hF hW hu _ fun ψ => ?_
    have := isFiniteMeasure_diagPos hE hF (V ψ)
    have e : diagPos hE (V ψ) = diagPos hP ψ := eq_diagPos hP hF _ fun S => by
      rw [inner_unitaryConj]
      exact inner_apply_eq_diagPos hE hF (V ψ) S
    rw [inner_unitaryConj, inner_pvmIntegral_self hE hF hC hW hu, e]
omit hE hF hC in
theorem complexMeasureIntegral_zero {u : (Fin 4 → ℝ) → ℂ} (hu : IsBddMeasurableFun u) :
    complexMeasureIntegral (fun _ => 0) u = 0 := by
  have hw : HasMeasureDecomposition (fun _ : FourBorelSet => (0 : ℂ)) (fun _ : Fin 1 => (0 : ℂ))
      (fun _ => (0 : Measure (Fin 4 → ℝ))) :=
    ⟨by norm_num, fun _ => inferInstance, fun S => by simp⟩
  exact ((hW.2.2.1 _ u ⟨1, _, _, hw⟩ hu).2 0 ⟨1, _, _, hw, by simp⟩).symm
theorem restrictionFacts_holds {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) :
    RestrictionFacts E S₀ := by
  intro Y hYc hY
  refine ⟨hYc.completeSpace_coe, ?_⟩
  intro _
  have hP : IsPVM (fun S => restrictInvariant Y (E S) (hY S)) := by
    refine ⟨fun S => ?_, ?_, fun x S hd => ?_⟩
    · obtain ⟨h₁, h₂⟩ := (isOrthProjection_iff _).1 (hE.isProj S)
      exact (isOrthProjection_iff _).2 ⟨fun x y => h₁ _ _, fun x => Subtype.ext (h₂ _)⟩
    · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
      change E FourBorelSet.univ x = x
      rw [hE.univ_eq]
      rfl
    · exact hE.sigma_additive (x : H) S hd
  refine ⟨hP, ?_, fun u hu y => ?_⟩
  · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    change E S₀.compl x = 0
    rw [IsSupportedOn] at hS
    rw [hS]
    rfl
  · have hT : ∀ y ∈ Y, pvmIntegral E u y ∈ Y := fun y hy => by
      rw [← Submodule.orthogonal_orthogonal Y, Submodule.mem_orthogonal]
      intro x hx
      rw [hasWeakIntegrals_pvmIntegral hE hF hC hW hu x y]
      have e : spectralScalarMeasure E x y = fun _ => 0 := funext fun S =>
        (Submodule.mem_orthogonal' _ _).1 hx _ (hY S y hy)
      rw [e]
      exact complexMeasureIntegral_zero hW hu
    have h : pvmIntegral (fun S => restrictInvariant Y (E S) (hY S)) u =
        restrictInvariant Y (pvmIntegral E u) hT := by
      refine pvmIntegral_eq_of_inner_self hP hF hW hu _ fun ψ => ?_
      have := isFiniteMeasure_diagPos hE hF (ψ : H)
      have e : diagPos hE (ψ : H) = diagPos hP ψ := eq_diagPos hP hF _ fun S =>
        inner_apply_eq_diagPos hE hF (ψ : H) S
      rw [← e, ← inner_pvmIntegral_self hE hF hC hW hu]
      rfl
    rw [h]
    rfl
omit hE hF hC hW in
theorem diagDouble_apply (A : BddOp H) (z : WithLp 2 (H × H)) :
    diagDouble A z = WithLp.toLp 2 (A (WithLp.ofLp z).1, A (WithLp.ofLp z).2) := rfl
omit hE hF hC hW in
theorem inner_diagDouble (A : BddOp H) (z w : WithLp 2 (H × H)) :
    ⟪z, diagDouble A w⟫_ℂ =
      ⟪(WithLp.ofLp z).1, A (WithLp.ofLp w).1⟫_ℂ + ⟪(WithLp.ofLp z).2, A (WithLp.ofLp w).2⟫_ℂ := by
  rw [diagDouble_apply, WithLp.prod_inner_apply]
theorem doubleFacts_holds {S₀ : FourBorelSet} (hS : IsSupportedOn E S₀) :
    DoubleFacts E S₀ := by
  have hP : IsPVM (fun S => diagDouble (E S)) := by
    refine ⟨fun S => ?_, ?_, fun x S hd => ?_⟩
    · obtain ⟨h₁, h₂⟩ := (isOrthProjection_iff _).1 (hE.isProj S)
      refine (isOrthProjection_iff _).2 ⟨fun x y => ?_, fun x => ?_⟩
      · rw [inner_diagDouble, diagDouble_apply, WithLp.prod_inner_apply]
        simp [h₁]
      · simp [diagDouble_apply, h₂]
    · refine ContinuousLinearMap.ext fun x => ?_
      rw [hE.univ_eq]
      simp [diagDouble_apply]
      rfl
    · simpa only [inner_diagDouble] using
        (hE.sigma_additive (WithLp.ofLp x).1 S hd).add
          (hE.sigma_additive (WithLp.ofLp x).2 S hd)
  refine ⟨hP, ?_, fun u hu => ?_⟩
  · rw [IsSupportedOn] at hS ⊢
    rw [hS]
    refine ContinuousLinearMap.ext fun x => ?_
    simp [diagDouble_apply]
  · refine pvmIntegral_eq_of_inner_self hP hF hW hu _ fun ψ => ?_
    have h₁ := isFiniteMeasure_diagPos hE hF (WithLp.ofLp ψ).1
    have h₂ := isFiniteMeasure_diagPos hE hF (WithLp.ofLp ψ).2
    have e : diagPos hE (WithLp.ofLp ψ).1 + diagPos hE (WithLp.ofLp ψ).2 = diagPos hP ψ :=
      eq_diagPos hP hF _ fun S => by
        rw [inner_diagDouble, inner_apply_eq_diagPos hE hF _ S, inner_apply_eq_diagPos hE hF _ S,
          Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        simp
    rw [inner_diagDouble, inner_pvmIntegral_self hE hF hC hW hu,
      inner_pvmIntegral_self hE hF hC hW hu, ← e,
      integral_add_measure (integrable_diagPos hE hF _ hu) (integrable_diagPos hE hF _ hu)]
theorem pvmDeterminedByCharFun_holds : PvmDeterminedByCharFun E := by
  intro E' hP h
  funext S
  have hm : ∀ ψ, diagPos hP ψ = diagPos hE ψ := fun ψ => by
    have := isFiniteMeasure_diagPos hE hF ψ
    have := isFiniteMeasure_diagPos hP hF ψ
    refine measure_eq_of_integral_expChar _ _ fun a => ?_
    have hb := isBddMeasurableFun_expChar a
    rw [← inner_pvmIntegral_self hP hF hC hW hb, h a, inner_pvmIntegral_self hE hF hC hW hb]
  have hd : ∀ ψ, ⟪ψ, E' S ψ⟫_ℂ = ⟪ψ, E S ψ⟫_ℂ := fun ψ => by
    rw [inner_apply_eq_diagPos hP hF, inner_apply_eq_diagPos hE hF, hm]
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  have h₁ := inner_eq_polarization (E' S : H →ₗ[ℂ] H) x y
  have h₂ := inner_eq_polarization (E S : H →ₗ[ℂ] H) x y
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact hd _
theorem pvmNotionsAgree_holds : PvmNotionsAgree E := by
  intro E' h
  obtain rfl := eq_toProjMeasure hE E' h
  exact ⟨fun B => isSupportedOn_iff_supports hE B, fun x B => rfl, fun u hu =>
    funext (pvmIntegral_apply hE hF hC hW hu)⟩
omit hE hF hC hW in
theorem norm_orthProj_apply_le {P : H →ₗ[ℂ] H}
    (hP : EuclideanSpectral.IsOrthProj P) (x : H) : ‖P x‖ ≤ ‖x‖ := by
  rcases (norm_nonneg (P x)).eq_or_lt with h | h
  · rw [← h]
    exact norm_nonneg _
  have h₁ : ⟪P x, P x⟫_ℂ = ⟪x, P x⟫_ℂ := by
    rw [hP.symm, ← LinearMap.comp_apply, hP.idem]
  have h₂ : ‖P x‖ * ‖P x‖ ≤ ‖x‖ * ‖P x‖ := by
    have h₃ : ‖⟪P x, P x⟫_ℂ‖ = ‖P x‖ * ‖P x‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two]
    rw [← h₃, h₁]
    exact norm_inner_le_norm _ _
  exact le_of_mul_le_mul_right h₂ h
def orthProjToBddOp {P : H →ₗ[ℂ] H}
    (hP : EuclideanSpectral.IsOrthProj P) : BddOp H :=
  P.mkContinuous 1 fun x => by simpa using norm_orthProj_apply_le hP x
omit hE hF hC hW in
theorem isOrthProjection_orthProjToBddOp {P : H →ₗ[ℂ] H}
    (hP : EuclideanSpectral.IsOrthProj P) :
    IsOrthProjection (orthProjToBddOp hP) :=
  (isOrthProjection_iff _).2 ⟨hP.symm, fun x => LinearMap.congr_fun hP.idem x⟩
omit hE hF hC hW in
theorem projectionNotionsAgree_holds : ProjectionNotionsAgree H := by
  refine ⟨fun f => ⟨?_, ?_⟩, fun F => ⟨?_, ?_⟩⟩
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨h₁, h₂⟩ := (isOrthProjection_iff A).1 hA
    exact ⟨(A : H →ₗ[ℂ] H), ⟨LinearMap.ext h₂, h₁⟩, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨orthProjToBddOp hP, isOrthProjection_orthProjToBddOp hP, rfl⟩
  · rintro ⟨E, hE, h⟩
    exact ⟨toProjMeasure E hE, fun B => h _⟩
  · rintro ⟨E', h⟩
    refine ⟨fun S => orthProjToBddOp (E'.isOrthProj (toEuclideanBorel S)),
      ⟨fun S => isOrthProjection_orthProjToBddOp _, ?_, fun x S hd => ?_⟩, fun S => ?_⟩
    · have e : toEuclideanBorel FourBorelSet.univ =
          EuclideanSpectral.BorelSubset.univ 4 := Subtype.ext rfl
      refine ContinuousLinearMap.ext fun x => ?_
      change E' (toEuclideanBorel FourBorelSet.univ) x = x
      rw [e]
      exact LinearMap.congr_fun E'.univ_eq_id x
    · have h₁ := E'.hasSum_diag x (fun k => toEuclideanBorel (S k))
        (fun k l hkl => (hd hkl).preimage _)
      have e : EuclideanSpectral.BorelSubset.unionSeq
          (fun k => toEuclideanBorel (S k)) = toEuclideanBorel (FourBorelSet.iUnion S) :=
        Subtype.ext (by
          ext p
          simp [FourBorelSet.iUnion, EuclideanSpectral.BorelSubset.unionSeq,
            toEuclideanBorel])
      rw [e] at h₁
      exact h₁
    · have h₁ := h (toEuclideanBorel S)
      rw [ofEuclideanBorel_toEuclideanBorel] at h₁
      exact h₁
end Bridge
theorem boundedFunctionalCalculus_holds
    (hF : EuclideanSpectral.ProjMeasureBasicFacts)
    (hC : EuclideanSpectral.ProjMeasureBoundedCalculus)
    (hW : HilbertWellDefined.WellDefinedStatement) : BoundedFunctionalCalculus :=
  ⟨complexMeasureDeterminedByCharFun_holds hW, fun _ _ _ _ =>
    ⟨projectionNotionsAgree_holds, fun _ _ hE hS =>
      ⟨scalarMeasureFacts_holds hE hF hS,
        pvmIntegralBasic_holds hE hF hC hW hS,
        pvmIntegralRules_holds hE hF hC hW,
        pvmIntegralNormAndConvergence_holds hE hF hC hW hS,
        pushforwardFacts_holds hE hF hC hW hS,
        unitaryConjFacts_holds hE hF hC hW hS,
        restrictionFacts_holds hE hF hC hW hS,
        doubleFacts_holds hE hF hC hW hS,
        pvmDeterminedByCharFun_holds hE hF hC hW,
        pvmNotionsAgree_holds hE hF hC hW⟩⟩⟩
end YangMills.Construction.PVMCalculus
