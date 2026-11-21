import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfG
import YangMills.Construction.Matrices.FieldsOnCoefficientSpacesOfG
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjectionsProof
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernelProof
import YangMills.Construction.TransferOperators.FieldsKeepProductCoefficientSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics.FieldsPreserveIsotypicSpans
open SeveralVariables
section Factors
variable {J : Type} [Finite J]
def prodExcept (χ : J → C(specialUnitary, ℂ)) (b : J) (u : J → specialUnitary) : ℂ :=
  ∏ᶠ (b' : J) (_ : b' ≠ b), χ b' (u b')
theorem coordProduct_eq_mul_prodExcept (χ : J → C(specialUnitary, ℂ)) (b : J)
    (u : J → specialUnitary) :
    coordProduct χ u = χ b (u b) * prodExcept χ b u :=
  (mul_finprod_cond_ne b (Set.toFinite _)).symm
open Classical in
theorem prodExcept_update (χ : J → C(specialUnitary, ℂ)) (b : J) (θ : C(specialUnitary, ℂ))
    (u : J → specialUnitary) :
    prodExcept (Function.update χ b θ) b u = prodExcept χ b u := by
  refine finprod_congr fun b' => finprod_congr fun h => ?_
  rw [Function.update_of_ne h]
open Classical in
theorem prodExcept_shiftAt (χ : J → C(specialUnitary, ℂ)) (b : J) (ι : Fin 3) (t : ℝ)
    (u : J → specialUnitary) :
    prodExcept χ b (shiftAt u b ι t) = prodExcept χ b u := by
  refine finprod_congr fun b' => finprod_congr fun h => ?_
  simp [shiftAt, Function.update_of_ne h]
omit [Finite J] in
theorem shiftAt_apply_self (u : J → specialUnitary) (b : J) (ι : Fin 3) (t : ℝ) :
    shiftAt u b ι t b = u b * oneParam ι t := by
  simp [shiftAt]
open Classical in
theorem hasDerivAt_coordProduct_update (χ : J → C(specialUnitary, ℂ)) (b : J) (ι : Fin 3)
    (θ θ' : C(specialUnitary, ℂ))
    (h : ∀ g, HasDerivAt (fun t : ℝ => θ (g * oneParam ι t)) (θ' g) 0)
    (u : J → specialUnitary) :
    HasDerivAt (fun t : ℝ => coordProduct (Function.update χ b θ) (shiftAt u b ι t))
      (coordProduct (Function.update χ b θ') u) 0 := by
  have e : (fun t : ℝ => coordProduct (Function.update χ b θ) (shiftAt u b ι t)) =
      fun t => θ (u b * oneParam ι t) * prodExcept χ b u := by
    funext t
    rw [coordProduct_eq_mul_prodExcept _ b, prodExcept_update, prodExcept_shiftAt,
      shiftAt_apply_self, Function.update_self]
  rw [e, coordProduct_eq_mul_prodExcept _ b, prodExcept_update, Function.update_self]
  exact (h (u b)).mul_const _
theorem exists_rightFieldOne_deriv (hF : AllRightFieldFacts) (m : HalfNatural) (ι : Fin 3)
    {θ : C(specialUnitary, ℂ)} (hθ : θ ∈ coeffSpan m) :
    ∃ θ' ∈ coeffSpan m, (∀ g, θ' g = rightFieldOne ι θ g) ∧
      ∀ g, HasDerivAt (fun t : ℝ => θ (g * oneParam ι t)) (θ' g) 0 := by
  obtain ⟨θ', hm, he⟩ := (hF m).rightFieldOne_mem ι θ hθ
  refine ⟨θ', hm, he, fun g => ?_⟩
  have hd := (hF m).hasDirDerivAt ι θ hθ (fun _ => g)
  have e : (fun t : ℝ => asSingletonFamily θ (shiftAt (fun _ => g) () ι t)) =
      fun t => θ (g * oneParam ι t) := by
    funext t
    simp [asSingletonFamily, shiftAt]
  unfold HasDirDerivAt at hd
  rw [e] at hd
  rw [he]
  exact hd.hasDerivAt
theorem prodCoeffSpan_induction {l : J → HalfNatural} {p : C(J → specialUnitary, ℂ) → Prop}
    (mem : ∀ χ : J → C(specialUnitary, ℂ), (∀ b, χ b ∈ coeffSpan (l b)) → p (coordProduct χ))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (smul : ∀ (c : ℂ) x, p x → p (c • x))
    {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan l) : p ψ := by
  refine Submodule.span_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ => add x y)
    (fun c x _ => smul c x) hψ
  rintro x ⟨χ, hχ, rfl⟩
  exact mem χ hχ
open Classical in
theorem coordProduct_update_mem {l : J → HalfNatural} {χ : J → C(specialUnitary, ℂ)}
    (hχ : ∀ b, χ b ∈ coeffSpan (l b))
    {b : J} {θ : C(specialUnitary, ℂ)} (hθ : θ ∈ coeffSpan (l b)) :
    coordProduct (Function.update χ b θ) ∈ prodCoeffSpan l := by
  refine Submodule.subset_span ⟨_, fun b' => ?_, rfl⟩
  by_cases h : b' = b
  · subst h
    simpa using hθ
  · simpa [Function.update_of_ne h] using hχ b'
theorem exists_hasDerivAt_shiftAt (hF : AllRightFieldFacts) (l : J → HalfNatural) (b : J)
    (ι : Fin 3) {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan l) :
    ∃ φ ∈ prodCoeffSpan l,
      ∀ u, HasDerivAt (fun t : ℝ => ψ (shiftAt u b ι t)) (φ u) 0 := by
  classical
  refine prodCoeffSpan_induction (l := l) (p := fun ψ => ∃ φ ∈ prodCoeffSpan l,
    ∀ u, HasDerivAt (fun t : ℝ => ψ (shiftAt u b ι t)) (φ u) 0) ?_ ?_ ?_ ?_ hψ
  · intro χ hχ
    obtain ⟨θ, hm, -, hd⟩ := exists_rightFieldOne_deriv hF (l b) ι (hχ b)
    refine ⟨coordProduct (Function.update χ b θ), coordProduct_update_mem hχ hm, fun u => ?_⟩
    have h := hasDerivAt_coordProduct_update χ b ι (χ b) θ hd u
    rwa [Function.update_eq_self] at h
  · exact ⟨0, zero_mem _, fun u => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  · rintro x y ⟨φ, hφ, h⟩ ⟨φ', hφ', h'⟩
    exact ⟨φ + φ', add_mem hφ hφ', fun u => (h u).add (h' u)⟩
  · rintro c x ⟨φ, hφ, h⟩
    exact ⟨c • φ, Submodule.smul_mem _ c hφ, fun u => (h u).const_mul c⟩
omit [Finite J] in
theorem rightField_eq_of_hasDerivAt {b : J} {ι : Fin 3} {F : (J → specialUnitary) → ℂ}
    {φ : C(J → specialUnitary, ℂ)}
    (h : ∀ u, HasDerivAt (fun t : ℝ => F (shiftAt u b ι t)) (φ u) 0) :
    rightField b ι F = φ :=
  funext fun u => (h u).deriv
theorem exists_mem_eq_rightField (hF : AllRightFieldFacts) (l : J → HalfNatural) (b : J)
    (ι : Fin 3) {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan l) :
    ∃ φ ∈ prodCoeffSpan l, (φ : (J → specialUnitary) → ℂ) = rightField b ι ψ := by
  obtain ⟨φ, hφ, h⟩ := exists_hasDerivAt_shiftAt hF l b ι hψ
  exact ⟨φ, hφ, (rightField_eq_of_hasDerivAt h).symm⟩
theorem sum_rightField_rightField_eq (hF : AllRightFieldFacts) (l : J → HalfNatural) (b : J)
    {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan l) (u : J → specialUnitary) :
    -∑ ι, rightField b ι (rightField b ι ψ) u =
      (((l b).toReal * ((l b).toReal + 1) : ℝ) : ℂ) * ψ u := by
  classical
  have main : ∃ φ₁ φ₂ : Fin 3 → C(J → specialUnitary, ℂ),
      (∀ ι u, HasDerivAt (fun t : ℝ => ψ (shiftAt u b ι t)) (φ₁ ι u) 0) ∧
      (∀ ι u, HasDerivAt (fun t : ℝ => φ₁ ι (shiftAt u b ι t)) (φ₂ ι u) 0) ∧
      ∀ u, -∑ ι, φ₂ ι u = (((l b).toReal * ((l b).toReal + 1) : ℝ) : ℂ) * ψ u := by
    refine prodCoeffSpan_induction (l := l) (p := fun ψ => ∃ φ₁ φ₂ : Fin 3 → C(J → specialUnitary, ℂ),
      (∀ ι u, HasDerivAt (fun t : ℝ => ψ (shiftAt u b ι t)) (φ₁ ι u) 0) ∧
      (∀ ι u, HasDerivAt (fun t : ℝ => φ₁ ι (shiftAt u b ι t)) (φ₂ ι u) 0) ∧
      ∀ u, -∑ ι, φ₂ ι u = (((l b).toReal * ((l b).toReal + 1) : ℝ) : ℂ) * ψ u) ?_ ?_ ?_ ?_ hψ
    · intro χ hχ
      have h₁ := fun ι => exists_rightFieldOne_deriv hF (l b) ι (hχ b)
      choose θ hθ he hd using h₁
      have h₂ := fun ι => exists_rightFieldOne_deriv hF (l b) ι (hθ ι)
      choose θ₂ _ he₂ hd₂ using h₂
      refine ⟨fun ι => coordProduct (Function.update χ b (θ ι)),
        fun ι => coordProduct (Function.update χ b (θ₂ ι)), fun ι u => ?_, fun ι u => ?_,
        fun u => ?_⟩
      · have h := hasDerivAt_coordProduct_update χ b ι (χ b) (θ ι) (hd ι) u
        rwa [Function.update_eq_self] at h
      · exact hasDerivAt_coordProduct_update χ b ι (θ ι) (θ₂ ι) (hd₂ ι) u
      · have hv : ∀ ι, coordProduct (Function.update χ b (θ₂ ι)) u =
            rightFieldOne ι (rightFieldOne ι (χ b)) (u b) * prodExcept χ b u := by
          intro ι
          have hc : (θ ι : specialUnitary → ℂ) = rightFieldOne ι (χ b) := funext (he ι)
          rw [coordProduct_eq_mul_prodExcept _ b, prodExcept_update, Function.update_self, he₂, hc]
        have hc := (hF (l b)).casimirOp_eq (χ b) (hχ b) (u b)
        unfold casimirOp at hc
        simp only [hv]
        rw [← Finset.sum_mul, ← neg_mul, hc, coordProduct_eq_mul_prodExcept χ b]
        ring
    · refine ⟨0, 0, fun ι u => ?_, fun ι u => ?_, fun u => by simp⟩ <;>
        simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · rintro x y ⟨φ₁, φ₂, h₁, h₂, h₃⟩ ⟨φ₁', φ₂', h₁', h₂', h₃'⟩
      refine ⟨φ₁ + φ₁', φ₂ + φ₂', fun ι u => (h₁ ι u).add (h₁' ι u),
        fun ι u => (h₂ ι u).add (h₂' ι u), fun u => ?_⟩
      have e₁ := h₃ u
      have e₂ := h₃' u
      simp only [Pi.add_apply, ContinuousMap.add_apply, Finset.sum_add_distrib]
      linear_combination e₁ + e₂
    · rintro c x ⟨φ₁, φ₂, h₁, h₂, h₃⟩
      refine ⟨c • φ₁, c • φ₂, fun ι u => (h₁ ι u).const_mul c,
        fun ι u => (h₂ ι u).const_mul c, fun u => ?_⟩
      have e₁ := h₃ u
      simp only [Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      linear_combination c * e₁
  obtain ⟨φ₁, φ₂, h₁, h₂, h₃⟩ := main
  have e₁ : ∀ ι, rightField b ι ψ = φ₁ ι := fun ι => rightField_eq_of_hasDerivAt (h₁ ι)
  have e₂ : ∀ ι, rightField b ι (φ₁ ι) = φ₂ ι := fun ι => rightField_eq_of_hasDerivAt (h₂ ι)
  simp only [e₁, e₂]
  exact h₃ u
end Factors
section Norms
variable {J : Type} [Finite J]
theorem toHaarL2_eq_toLp (f : C(J → specialUnitary, ℂ)) :
    toHaarL2 (f : (J → specialUnitary) → ℂ) = ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ f := by apply _root_.YangMills.Construction.SpinHarmonics.IsotypicPartSums.toHaarL2_continuousMap <;> assumption
theorem norm_toHaarL2_sq (f : C(J → specialUnitary, ℂ)) :
    ((‖toHaarL2 (f : (J → specialUnitary) → ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∫ u, star (f u) * f u ∂haarPi J := by
  have h := ContinuousMap.inner_toLp (μ := haarPi J) (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K, ← toHaarL2_eq_toLp] at h
  push_cast
  have h' : ((‖toHaarL2 (f : (J → specialUnitary) → ℂ)‖ : ℂ)) ^ 2 = _ := h
  rw [h']
  exact integral_congr_ae (ae_of_all _ fun u => by simp [mul_comm])
theorem halfNatural_toReal_nonneg (m : HalfNatural) : 0 ≤ m.toReal := by apply _root_.YangMills.Construction.TransferOperators.SqrtLinkFacts.halfNatural_toReal_nonneg <;> assumption
omit [Finite J] in
theorem nonneg_weightSum (l : J → HalfNatural) : 0 ≤ weightSum l :=
  finsum_nonneg fun b => halfNatural_toReal_nonneg (l b)
theorem toReal_le_weightSum (l : J → HalfNatural) (b : J) : (l b).toReal ≤ weightSum l :=
  single_le_finsum b (Set.toFinite _) fun b' => halfNatural_toReal_nonneg (l b')
theorem casimirEigen_le (l : J → HalfNatural) (b : J) :
    (l b).toReal * ((l b).toReal + 1) ≤ (1 + weightSum l) ^ 2 := by
  have h₀ := halfNatural_toReal_nonneg (l b)
  have h₁ := toReal_le_weightSum l b
  nlinarith
theorem norm_le_mul_norm_toHaarL2 (hK : SeveralVariablesFacts) [Nonempty J] (l : J → HalfNatural)
    {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan l) :
    ‖ψ‖ ≤ (∏ᶠ b, (2 * (l b).toReal + 1)) * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ := by
  classical
  have facts := hK J l ⟨0⟩
  have hB := facts.1
  have hD := facts.2.2.2.1
  set S := indicesWithSpins l with hS
  have hexp : ∃ c : PeterWeylIndex J → ℂ, ψ = ∑ α ∈ S, c α • peterWeylFn α := by
    rw [← hB.2.2.1] at hψ
    refine Submodule.span_induction (p := fun x _ => ∃ c : PeterWeylIndex J → ℂ,
      x = ∑ α ∈ S, c α • peterWeylFn α) ?_ ⟨0, by simp⟩ ?_ ?_ hψ
    · rintro x ⟨α, hα, rfl⟩
      have hm : α ∈ S := (finite_indicesWithSpins l).mem_toFinset.2 hα
      refine ⟨fun a => if a = α then 1 else 0, ?_⟩
      simp [hm]
    · rintro x y _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
      exact ⟨c + c', by simp [add_smul, Finset.sum_add_distrib]⟩
    · rintro a x _ ⟨c, rfl⟩
      exact ⟨a • c, by simp [Finset.smul_sum, mul_smul]⟩
  obtain ⟨c, hc⟩ := hexp
  have hclass : toHaarL2 (ψ : (J → specialUnitary) → ℂ) = ∑ α ∈ S, c α • peterWeylVec α := by
    rw [toHaarL2_eq_toLp, hc, map_sum]
    simp [peterWeylVec]
  have hnorm : ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ ^ 2 = ∑ α ∈ S, ‖c α‖ ^ 2 := by
    have h := hB.1.inner_sum c c S
    rw [← hclass, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    have h' : ((‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ : ℂ)) ^ 2 = _ := h
    rw [h']
    exact Finset.sum_congr rfl fun α _ => by rw [Complex.conj_mul']
  have hone : 0 ≤ ∏ᶠ b, (2 * (l b).toReal + 1) :=
    finprod_nonneg fun b => by have := halfNatural_toReal_nonneg (l b); linarith
  refine (ContinuousMap.norm_le _ (mul_nonneg hone (norm_nonneg _))).2 fun u => ?_
  have hsum : ∑ α ∈ S, ‖peterWeylFn α u‖ ^ 2 = (∏ᶠ b, (2 * (l b).toReal + 1)) ^ 2 := by
    rw [finprod_pow (Set.toFinite _)]
    apply Complex.ofReal_injective
    rw [← (hD.1 u).2.2, hB.2.2.2.1 u u]
    push_cast
    exact Finset.sum_congr rfl fun α _ => by rw [Complex.star_def, Complex.mul_conj']
  have hval : ψ u = ∑ α ∈ S, c α * peterWeylFn α u := by
    rw [hc]
    simp [ContinuousMap.sum_apply]
  calc ‖ψ u‖ ≤ ∑ α ∈ S, ‖c α‖ * ‖peterWeylFn α u‖ := by
        rw [hval]
        exact norm_sum_le_of_le _ fun α _ => (norm_mul _ _).le
    _ ≤ √(∑ α ∈ S, ‖c α‖ ^ 2) * √(∑ α ∈ S, ‖peterWeylFn α u‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = (∏ᶠ b, (2 * (l b).toReal + 1)) * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ := by
        rw [← hnorm, hsum, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hone, mul_comm]
theorem mem_smoothOrder_one (hC : FieldCalculus.AllRules)
    (hK : SeveralVariablesFacts) [Nonempty J] (l : J → HalfNatural)
    {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan l) :
    (ψ : (J → specialUnitary) → ℂ) ∈ smoothOrder 1 := by
  have hpoly := ((hK J l ⟨0⟩).2.2.2.2.2.1).2.1 ψ hψ
  have hsmooth := ((hC.2.2 J).2.2.2.2.2.1).1 _ hpoly
  exact Set.mem_iInter.1 hsmooth 1
theorem norm_toHaarL2_rightField_le (hF : AllRightFieldFacts)
    (hC : FieldCalculus.AllRules) (hK : SeveralVariablesFacts) [Nonempty J]
    (l : J → HalfNatural) (b : J) (ι : Fin 3) {ψ φ : C(J → specialUnitary, ℂ)}
    (hψ : ψ ∈ prodCoeffSpan l) (hφ : (φ : (J → specialUnitary) → ℂ) = rightField b ι ψ) :
    ‖toHaarL2 (φ : (J → specialUnitary) → ℂ)‖ ≤
      (1 + weightSum l) * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ := by
  have h₁ := fun ι' => exists_mem_eq_rightField hF l b ι' hψ
  choose D hD eD using h₁
  have h₂ := fun ι' => exists_mem_eq_rightField hF l b ι' (hD ι')
  choose D₂ _ eD₂ using h₂
  have hskew := (hC.2.2 J).2.2.2.2.2.2.1
  have hsk : ∀ ι', ((‖toHaarL2 (D ι' : (J → specialUnitary) → ℂ)‖ ^ 2 : ℝ) : ℂ) =
      -∫ u, star (ψ u) * D₂ ι' u ∂haarPi J := by
    intro ι'
    have h := (hskew b ι' ψ (D ι') (mem_smoothOrder_one hC hK l hψ)
      (mem_smoothOrder_one hC hK l (hD ι'))).2
    rw [← eD, ← eD₂] at h
    rw [norm_toHaarL2_sq]
    exact h
  have hint : ∀ ι', Integrable (fun u => star (ψ u) * D₂ ι' u) (haarPi J) := fun ι' =>
    ((star ψ * D₂ ι').continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcas : ∀ u, -∑ ι', D₂ ι' u =
      (((l b).toReal * ((l b).toReal + 1) : ℝ) : ℂ) * ψ u := by
    intro u
    have h := sum_rightField_rightField_eq hF l b hψ u
    simp only [← eD, ← eD₂] at h
    exact h
  have hsum : ∑ ι', ‖toHaarL2 (D ι' : (J → specialUnitary) → ℂ)‖ ^ 2 =
      (l b).toReal * ((l b).toReal + 1) * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    simp only [hsk]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun ι' _ => hint ι',
      Complex.ofReal_mul, norm_toHaarL2_sq, ← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    have h := hcas u
    simp only [← Finset.mul_sum]
    linear_combination (star (ψ u)) * h
  have hD' : φ = D ι := DFunLike.coe_injective (hφ.trans (eD ι).symm)
  have hle : ‖toHaarL2 (φ : (J → specialUnitary) → ℂ)‖ ^ 2 ≤
      ((1 + weightSum l) * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖) ^ 2 := by
    rw [hD', mul_pow]
    calc ‖toHaarL2 (D ι : (J → specialUnitary) → ℂ)‖ ^ 2
        ≤ ∑ ι', ‖toHaarL2 (D ι' : (J → specialUnitary) → ℂ)‖ ^ 2 :=
          Finset.single_le_sum (f := fun ι' => ‖toHaarL2 (D ι' : (J → specialUnitary) → ℂ)‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ ι)
      _ ≤ _ := by
          rw [hsum]
          exact mul_le_mul_of_nonneg_right (casimirEigen_le l b) (by positivity)
  have hnn : 0 ≤ (1 + weightSum l) * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ :=
    mul_nonneg (by have := nonneg_weightSum l; linarith) (norm_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) hnn).1 hle
theorem exists_mem_eq_fieldWord (hF : AllRightFieldFacts)
    (hC : FieldCalculus.AllRules) (hK : SeveralVariablesFacts) [Nonempty J]
    (l : J → HalfNatural) {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan l)
    (w : List (J × Fin 3)) :
    ∃ φ ∈ prodCoeffSpan l, (φ : (J → specialUnitary) → ℂ) = fieldWord w ψ ∧
      ‖toHaarL2 (φ : (J → specialUnitary) → ℂ)‖ ≤
        (1 + weightSum l) ^ w.length * ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖ := by
  induction w with
  | nil => exact ⟨ψ, hψ, rfl, by simp⟩
  | cons p w ih =>
    obtain ⟨φ, hφ, e, hb⟩ := ih
    obtain ⟨φ', hφ', e'⟩ := exists_mem_eq_rightField hF l p.1 p.2 hφ
    have hnn : 0 ≤ 1 + weightSum l := by have := nonneg_weightSum l; linarith
    refine ⟨φ', hφ', ?_, ?_⟩
    · rw [e', e]
      rfl
    · calc ‖toHaarL2 (φ' : (J → specialUnitary) → ℂ)‖
          ≤ (1 + weightSum l) * ‖toHaarL2 (φ : (J → specialUnitary) → ℂ)‖ :=
            norm_toHaarL2_rightField_le hF hC hK l p.1 p.2 hφ e'
        _ ≤ (1 + weightSum l) * ((1 + weightSum l) ^ w.length *
              ‖toHaarL2 (ψ : (J → specialUnitary) → ℂ)‖) := mul_le_mul_of_nonneg_left hb hnn
        _ = _ := by simp only [List.length_cons]; ring
end Norms
theorem holds (hF : AllRightFieldFacts) (hC : FieldCalculus.AllRules)
    (hK : SeveralVariablesFacts) : FieldsPreserveIsotypicSpans.Statement := by
  intro J _ _ l ψ hψ
  refine ⟨fun w => ?_, fun b u => sum_rightField_rightField_eq hF l b hψ u,
    norm_le_mul_norm_toHaarL2 hK l hψ, fun w => ?_⟩
  · obtain ⟨φ, hφ, e, -⟩ := exists_mem_eq_fieldWord hF hC hK l hψ w
    exact ⟨φ, hφ, e⟩
  · obtain ⟨φ, -, e, hb⟩ := exists_mem_eq_fieldWord hF hC hK l hψ w
    rw [← e]
    exact hb
end YangMills.Construction.SpinHarmonics.FieldsPreserveIsotypicSpans
end
