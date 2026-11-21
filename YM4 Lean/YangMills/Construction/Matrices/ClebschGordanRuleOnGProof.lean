import YangMills.Construction.Matrices.ClebschGordanRuleOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MvPolynomial Matrices Matrices.ComplexMatrix2
namespace ClebschGordanProof
abbrev WZPolynomial : Type := MvPolynomial (Fin 2 ⊕ Fin 2) ℂ
def tensorExponent (l : HalfNatural) (ι : Fin 2) (a : Fin (l.doubled + 1)) : Fin 2 ⊕ Fin 2 →₀ ℕ :=
  Finsupp.single (.inl ι) 1 + (monomialExponent l a).mapDomain Sum.inr
theorem tensorMonomial_eq_monomial (l : HalfNatural) (ι : Fin 2) (a : Fin (l.doubled + 1)) :
    tensorMonomial l ι a =
      monomial (tensorExponent l ι a) (((monomialNorm l a : ℝ) : ℂ)⁻¹) := by
  rw [tensorMonomial, normalizedMonomial_eq_monomial, rename_monomial, X, monomial_mul,
    one_mul, tensorExponent]
theorem tensorExponent_inl (l : HalfNatural) (ι i : Fin 2) (a : Fin (l.doubled + 1)) :
    tensorExponent l ι a (.inl i) = if ι = i then 1 else 0 := by
  have h : (monomialExponent l a).mapDomain Sum.inr (.inl i : Fin 2 ⊕ Fin 2) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  simp [tensorExponent, h, Finsupp.single_apply]
theorem tensorExponent_inr (l : HalfNatural) (ι j : Fin 2) (a : Fin (l.doubled + 1)) :
    tensorExponent l ι a (.inr j) = monomialExponent l a j := by
  have h : (monomialExponent l a).mapDomain Sum.inr (.inr j : Fin 2 ⊕ Fin 2) =
      monomialExponent l a j :=
    Finsupp.mapDomain_apply Sum.inr_injective _ _
  simp [tensorExponent, h]
theorem tensorExponent_injective (l : HalfNatural) :
    Function.Injective fun p : Fin 2 × Fin (l.doubled + 1) => tensorExponent l p.1 p.2 := by
  rintro ⟨ι, a⟩ ⟨κ, c⟩ h
  have h₁ : tensorExponent l ι a (.inl ι) = tensorExponent l κ c (.inl ι) :=
    DFunLike.congr_fun h _
  have h₂ : tensorExponent l ι a (.inr 0) = tensorExponent l κ c (.inr 0) :=
    DFunLike.congr_fun h _
  rw [tensorExponent_inl, tensorExponent_inl] at h₁
  rw [tensorExponent_inr, tensorExponent_inr] at h₂
  have hικ : ι = κ := by
    by_contra hne
    have hne' : ¬κ = ι := fun e => hne e.symm
    simp [hne'] at h₁
  have hac : a = c := by
    apply Fin.ext
    simpa [monomialExponent] using h₂
  rw [hικ, hac]
theorem exists_tensorExponent_eq {l : HalfNatural} {m : Fin 2 ⊕ Fin 2 →₀ ℕ}
    (hm : Finsupp.weight wzDegree m = (1, l.doubled)) :
    ∃ p : Fin 2 × Fin (l.doubled + 1), tensorExponent l p.1 p.2 = m := by
  have hw : m (.inl 0) + m (.inl 1) = 1 ∧ m (.inr 0) + m (.inr 1) = l.doubled := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hm
    have h₁ := congrArg Prod.fst hm
    have h₂ := congrArg Prod.snd hm
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, wzDegree, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero] at h₁ h₂
    exact ⟨h₁, h₂⟩
  obtain ⟨hw₁, hw₂⟩ := hw
  have ha : m (.inr 0) < l.doubled + 1 := by omega
  have hz : ∀ (ι : Fin 2) (j : Fin 2),
      tensorExponent l ι ⟨m (.inr 0), ha⟩ (.inr j) = m (.inr j) := by
    intro ι j
    rw [tensorExponent_inr]
    fin_cases j
    · simp [monomialExponent]
    · simp [monomialExponent]
      omega
  by_cases h0 : m (.inl 0) = 1
  · refine ⟨(0, ⟨m (.inr 0), ha⟩), ?_⟩
    ext i
    rcases i with i | j
    · rw [tensorExponent_inl]
      fin_cases i
      · simp [h0]
      · simp
        omega
    · exact hz 0 j
  · refine ⟨(1, ⟨m (.inr 0), ha⟩), ?_⟩
    ext i
    rcases i with i | j
    · rw [tensorExponent_inl]
      fin_cases i
      · simp
        omega
      · simp
        omega
    · exact hz 1 j
def tensorCoord (l : HalfNatural) (ι : Fin 2) (a : Fin (l.doubled + 1)) : WZPolynomial →ₗ[ℂ] ℂ :=
  ((monomialNorm l a : ℝ) : ℂ) • lcoeff ℂ (tensorExponent l ι a)
theorem tensorCoord_tensorMonomial (l : HalfNatural) (p q : Fin 2 × Fin (l.doubled + 1)) :
    tensorCoord l p.1 p.2 (tensorMonomial l q.1 q.2) = if p = q then 1 else 0 := by
  have hne : ((monomialNorm l p.2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (monomialNorm_pos l p.2).ne'
  simp only [tensorCoord, LinearMap.smul_apply, lcoeff_apply,
    tensorMonomial_eq_monomial, coeff_monomial, smul_eq_mul]
  by_cases h : p = q
  · subst h
    simp [hne]
  · have hne₂ : tensorExponent l q.1 q.2 ≠ tensorExponent l p.1 p.2 := fun e =>
      h (tensorExponent_injective l e).symm
    simp [h, hne₂]
theorem tensorCoord_sum (l : HalfNatural) (f : Fin 2 × Fin (l.doubled + 1) → ℂ)
    (p : Fin 2 × Fin (l.doubled + 1)) :
    tensorCoord l p.1 p.2
      ((∑ q, f q • tensorBasisVec l q.1 q.2 : bihomogeneousSpace l) : WZPolynomial) = f p := by
  rw [AddSubmonoidClass.coe_finsetSum, map_sum]
  simp only [Submodule.coe_smul, map_smul, tensorBasisVec, tensorCoord_tensorMonomial]
  simp
theorem sum_tensorCoord_smul (l : HalfNatural) (P : bihomogeneousSpace l) :
    ∑ p : Fin 2 × Fin (l.doubled + 1),
      tensorCoord l p.1 p.2 (P : WZPolynomial) • tensorBasisVec l p.1 p.2 = P := by
  have hne : ∀ a, ((monomialNorm l a : ℝ) : ℂ) ≠ 0 := fun a =>
    Complex.ofReal_ne_zero.mpr (monomialNorm_pos l a).ne'
  have hterm : ∀ p : Fin 2 × Fin (l.doubled + 1),
      ((tensorCoord l p.1 p.2 (P : WZPolynomial) • tensorBasisVec l p.1 p.2 :
        bihomogeneousSpace l) : WZPolynomial) =
        monomial (tensorExponent l p.1 p.2) (coeff (tensorExponent l p.1 p.2) (P : WZPolynomial)) := by
    intro p
    simp only [tensorCoord, tensorBasisVec, Submodule.coe_smul, LinearMap.smul_apply,
      lcoeff_apply, tensorMonomial_eq_monomial, smul_eq_mul, smul_monomial]
    congr 1
    field_simp [hne p.2]
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [hterm]
  ext m
  rw [coeff_sum]
  simp only [coeff_monomial]
  have hP : (P : WZPolynomial).IsWeightedHomogeneous wzDegree (1, l.doubled) :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp P.2
  by_cases hm : Finsupp.weight wzDegree m = (1, l.doubled)
  · obtain ⟨p₀, hp₀⟩ := exists_tensorExponent_eq hm
    rw [Finset.sum_eq_single p₀]
    · simp [hp₀]
    · intro q _ hq
      have : tensorExponent l q.1 q.2 ≠ m := fun e =>
        hq (tensorExponent_injective l (e.trans hp₀.symm))
      simp [this]
    · simp
  · have h0 : coeff m (P : WZPolynomial) = 0 := by
      by_contra hc
      exact hm (hP hc)
    rw [h0]
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs with h
    · rw [h, h0]
    · rfl
theorem linearIndependent_tensorBasis (l : HalfNatural) : LinearIndependent ℂ
    (fun p : Fin 2 × Fin (l.doubled + 1) => tensorBasisVec l p.1 p.2) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf p
  have h := tensorCoord_sum l f p
  rw [hf] at h
  simpa using h.symm
theorem span_tensorBasis (l : HalfNatural) : Submodule.span ℂ
    (Set.range fun p : Fin 2 × Fin (l.doubled + 1) => tensorBasisVec l p.1 p.2) = ⊤ := by
  refine eq_top_iff.mpr fun P _ => ?_
  rw [← sum_tensorCoord_smul l P]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
def tensorBasis (l : HalfNatural) :
    Module.Basis (Fin 2 × Fin (l.doubled + 1)) ℂ (bihomogeneousSpace l) :=
  Module.Basis.mk (linearIndependent_tensorBasis l) (span_tensorBasis l).ge
instance (l : HalfNatural) : FiniteDimensional ℂ (bihomogeneousSpace l) :=
  Module.Finite.of_basis (tensorBasis l)
theorem finrank_bihomogeneousSpace (l : HalfNatural) :
    Module.finrank ℂ (bihomogeneousSpace l) = 2 * (l.doubled + 1) := by
  rw [Module.finrank_eq_card_basis (tensorBasis l)]
  simp
theorem linearIndependent_monomialBasis (l : HalfNatural) :
    LinearIndependent ℂ (monomialBasis l) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf a
  have h := congrArg (monomialCoord l a) hf
  simpa [map_sum, monomialCoord_monomialBasis] using h
def homogeneousBasis (l : HalfNatural) :
    Module.Basis (Fin (l.doubled + 1)) ℂ (homogeneousSpace l) :=
  Module.Basis.mk (linearIndependent_monomialBasis l) fun P _ => by
    rw [← sum_monomialCoord_smul_monomialBasis l P]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
instance (n : ℕ) : FiniteDimensional ℂ (homogeneousSubmodule (Fin 2) ℂ n) :=
  Module.Finite.of_basis (homogeneousBasis ⟨n⟩)
theorem finrank_homogeneousSpace_eq (l : HalfNatural) :
    Module.finrank ℂ (homogeneousSpace l) = l.doubled + 1 := by
  rw [Module.finrank_eq_card_basis (homogeneousBasis l)]
  simp
theorem spinCoeff_eq_monomialCoord (l : HalfNatural) (a c : Fin (l.doubled + 1))
    (g : specialUnitary) :
    spinCoeff l a c g = monomialCoord l a (spinRep l g (monomialBasis l c)) := by
  simp [spinCoeff, homogeneousInner, monomialCoord_monomialBasis]
theorem exists_mem_coeffSpan_eq_form (t : HalfNatural) (μ : homogeneousSpace t →ₗ[ℂ] ℂ)
    (Q : homogeneousSpace t) :
    ∃ ψ ∈ coeffSpan t, ∀ g, ψ g = μ (spinRep t g Q) := by
  refine ⟨∑ a, ∑ c, (μ (monomialBasis t a) * monomialCoord t c Q) • spinCoeffMap t a c,
    Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, c), rfl⟩), fun g => ?_⟩
  have hc : ∀ c, spinRep t g (monomialBasis t c) =
      ∑ a, spinCoeff t a c g • monomialBasis t a := by
    intro c
    simp only [spinCoeff_eq_monomialCoord]
    exact (sum_monomialCoord_smul_monomialBasis t _).symm
  have hQ : spinRep t g Q =
      ∑ c, monomialCoord t c Q • ∑ a, spinCoeff t a c g • monomialBasis t a := by
    conv_lhs => rw [← sum_monomialCoord_smul_monomialBasis t Q]
    simp only [map_sum, map_smul, hc]
  rw [hQ]
  simp only [map_sum, map_smul, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change μ (monomialBasis t a) * monomialCoord t c Q * spinCoeff t a c g = _
  ring
theorem aeval_rowSubst_rename (g : ComplexMatrix2) (A : MvPolynomial (Fin 2) ℂ) :
    aeval (rowSubst g) (rename Sum.inr A : WZPolynomial) =
      rename Sum.inr (aeval (columnForms g) A) := by
  rw [aeval_rename]
  have h : ((rename Sum.inr : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] WZPolynomial).comp
      (aeval (columnForms g))) = aeval (rowSubst g ∘ Sum.inr) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [columnForms, rowSubst]
  exact (DFunLike.congr_fun h A).symm
theorem tensorRep_tensorBasisVec_eq (l : HalfNatural) (g : specialUnitary) (κ : Fin 2)
    (c : Fin (l.doubled + 1)) :
    tensorRep l g (tensorBasisVec l κ c) =
      ∑ ι, ∑ a, ((g : ComplexMatrix2) ι κ * spinCoeff l a c g) • tensorBasisVec l ι a := by
  have hc : aeval (columnForms (g : ComplexMatrix2)) (normalizedMonomial l c) =
      ∑ a, spinCoeff l a c g • normalizedMonomial l a := by
    have h := congrArg Subtype.val
      (sum_monomialCoord_smul_monomialBasis l (spinRep l g (monomialBasis l c)))
    rw [AddSubmonoidClass.coe_finsetSum] at h
    simp only [← spinCoeff_eq_monomialCoord, Submodule.coe_smul] at h
    exact h.symm
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]
  change aeval (rowSubst (g : ComplexMatrix2)) (tensorMonomial l κ c) =
    ∑ ι, ∑ a, ((g : ComplexMatrix2) ι κ * spinCoeff l a c g) • tensorMonomial l ι a
  rw [tensorMonomial, map_mul, aeval_rowSubst_rename, hc, aeval_X, map_sum,
    Fin.sum_univ_two, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [rowSubst, tensorMonomial, smul_eq_C_mul, map_mul, rename_C]
  ring
def wzDeterminant : WZPolynomial := X (.inl 0) * X (.inr 1) - X (.inl 1) * X (.inr 0)
def polarization : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] WZPolynomial where
  toFun Q := ∑ i, X (.inl i) * rename Sum.inr (pderiv i Q)
  map_add' P Q := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c Q := by simp
theorem polarization_apply (Q : MvPolynomial (Fin 2) ℂ) :
    polarization Q = ∑ i, X (.inl i) * rename Sum.inr (pderiv i Q) := rfl
def detMul : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] WZPolynomial where
  toFun R := wzDeterminant * rename Sum.inr R
  map_add' P Q := by simp [mul_add]
  map_smul' c Q := by simp
theorem detMul_apply (R : MvPolynomial (Fin 2) ℂ) :
    detMul R = wzDeterminant * rename Sum.inr R := rfl
theorem X_mul_rename_mem (l : HalfNatural) (ι : Fin 2) {A : MvPolynomial (Fin 2) ℂ}
    (hA : A ∈ homogeneousSpace l) :
    X (.inl ι) * rename Sum.inr A ∈ bihomogeneousSpace l := by
  have h := congrArg Subtype.val (sum_monomialCoord_smul_monomialBasis l ⟨A, hA⟩)
  rw [AddSubmonoidClass.coe_finsetSum] at h
  simp only [Submodule.coe_smul] at h
  rw [← h, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul, mul_smul_comm]
  exact (bihomogeneousSpace l).smul_mem _ (tensorBasisVec l ι a).2
theorem polarization_mem (l : HalfNatural) {Q : MvPolynomial (Fin 2) ℂ}
    (hQ : Q ∈ homogeneousSpace l.addHalf) : polarization Q ∈ bihomogeneousSpace l := by
  refine Submodule.sum_mem _ fun i _ => X_mul_rename_mem l i ?_
  rw [mem_homogeneousSubmodule] at hQ ⊢
  simpa [HalfNatural.addHalf] using hQ.pderiv (i := i)
theorem detMul_mem (n : ℕ) {R : MvPolynomial (Fin 2) ℂ}
    (hR : R ∈ homogeneousSpace ⟨n⟩) : detMul R ∈ bihomogeneousSpace ⟨n + 1⟩ := by
  have h₁ : ∀ i : Fin 2, X i * R ∈ homogeneousSpace ⟨n + 1⟩ := by
    intro i
    rw [mem_homogeneousSubmodule] at hR ⊢
    simpa [add_comm] using (isHomogeneous_X ℂ i).mul hR
  have h₂ : detMul R = X (.inl 0) * rename Sum.inr (X 1 * R) -
      X (.inl 1) * rename Sum.inr (X 0 * R) := by
    simp only [detMul_apply, wzDeterminant, map_mul, rename_X]
    ring
  rw [h₂]
  exact Submodule.sub_mem _ (X_mul_rename_mem _ 0 (h₁ 1)) (X_mul_rename_mem _ 1 (h₁ 0))
def polarizationMap (l : HalfNatural) :
    homogeneousSpace l.addHalf →ₗ[ℂ] bihomogeneousSpace l :=
  (polarization ∘ₗ (homogeneousSpace l.addHalf).subtype).codRestrict _
    fun Q => polarization_mem l Q.2
def detMulMap (n : ℕ) : homogeneousSpace ⟨n⟩ →ₗ[ℂ] bihomogeneousSpace ⟨n + 1⟩ :=
  (detMul ∘ₗ (homogeneousSpace ⟨n⟩).subtype).codRestrict _
    fun R => detMul_mem n R.2
theorem pderiv_columnForms (g : ComplexMatrix2) (k j : Fin 2) :
    pderiv k (columnForms g j) = C (g k j) := by
  simp only [columnForms, map_add, pderiv_C_mul, pderiv_X]
  fin_cases k <;> simp
theorem pderiv_aeval_columnForms (g : ComplexMatrix2) (k : Fin 2) (Q : MvPolynomial (Fin 2) ℂ) :
    pderiv k (aeval (columnForms g) Q) =
      ∑ i, C (g k i) * aeval (columnForms g) (pderiv i Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, pderiv_mul, hp, pderiv_columnForms, map_add, Fin.sum_univ_two,
      pderiv_X]
    fin_cases j <;> simp <;> ring
theorem aeval_rowSubst_polarization (g : ComplexMatrix2) (Q : MvPolynomial (Fin 2) ℂ) :
    aeval (rowSubst g) (polarization Q) = polarization (aeval (columnForms g) Q) := by
  simp only [polarization_apply, Fin.sum_univ_two, map_add, map_mul, aeval_X,
    aeval_rowSubst_rename, pderiv_aeval_columnForms, rename_C, rowSubst]
  ring
theorem aeval_rowSubst_wzDeterminant (g : specialUnitary) :
    aeval (rowSubst (g : ComplexMatrix2)) wzDeterminant = wzDeterminant := by
  have hdet : (g : ComplexMatrix2) 0 0 * (g : ComplexMatrix2) 1 1 -
      (g : ComplexMatrix2) 0 1 * (g : ComplexMatrix2) 1 0 = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
    rwa [Matrix.det_fin_two] at h
  have hC := congrArg (C : ℂ → WZPolynomial) hdet
  simp only [map_sub, map_mul, map_one] at hC
  simp only [wzDeterminant, map_sub, map_mul, aeval_X, rowSubst]
  linear_combination (X (.inl 0) * X (.inr 1) - X (.inl 1) * X (.inr 0) : WZPolynomial) * hC
theorem aeval_rowSubst_detMul (g : specialUnitary) (R : MvPolynomial (Fin 2) ℂ) :
    aeval (rowSubst (g : ComplexMatrix2)) (detMul R) =
      detMul (aeval (columnForms (g : ComplexMatrix2)) R) := by
  simp only [detMul_apply, map_mul, aeval_rowSubst_rename, aeval_rowSubst_wzDeterminant]
theorem polarizationMap_spinRep (l : HalfNatural) (g : specialUnitary)
    (Q : homogeneousSpace l.addHalf) :
    polarizationMap l (spinRep l.addHalf g Q) = tensorRep l g (polarizationMap l Q) :=
  Subtype.ext (aeval_rowSubst_polarization (g : ComplexMatrix2) Q.1).symm
theorem detMulMap_spinRep (n : ℕ) (g : specialUnitary) (R : homogeneousSpace ⟨n⟩) :
    detMulMap n (spinRep ⟨n⟩ g R) = tensorRep ⟨n + 1⟩ g (detMulMap n R) :=
  Subtype.ext (aeval_rowSubst_detMul g R.1).symm
def diagonalSubst : WZPolynomial →ₐ[ℂ] MvPolynomial (Fin 2) ℂ := aeval (Sum.elim X X)
theorem diagonalSubst_rename (A : MvPolynomial (Fin 2) ℂ) :
    diagonalSubst (rename Sum.inr A) = A := by
  rw [diagonalSubst, aeval_rename, Sum.elim_comp_inr, aeval_X_left_apply]
theorem diagonalSubst_polarization {n : ℕ} {Q : MvPolynomial (Fin 2) ℂ}
    (hQ : Q.IsHomogeneous n) : diagonalSubst (polarization Q) = n • Q := by
  simp only [polarization_apply, map_sum, map_mul, diagonalSubst_rename]
  rw [← hQ.sum_X_mul_pderiv]
  simp [diagonalSubst]
theorem diagonalSubst_wzDeterminant : diagonalSubst wzDeterminant = 0 := by
  simp [diagonalSubst, wzDeterminant, mul_comm]
theorem wzDeterminant_ne_zero : wzDeterminant ≠ 0 := by
  intro h
  have h₁ := congrArg (eval (Sum.elim ![1, 0] ![0, 1] : Fin 2 ⊕ Fin 2 → ℂ)) h
  simp [wzDeterminant] at h₁
theorem eq_zero_of_polarization_add_detMul_eq_zero {n : ℕ} {Q R : MvPolynomial (Fin 2) ℂ}
    (hQ : Q.IsHomogeneous (n + 1)) (h : polarization Q + detMul R = 0) :
    Q = 0 ∧ R = 0 := by
  have hd := congrArg diagonalSubst h
  rw [map_add, diagonalSubst_polarization hQ, detMul_apply, map_mul,
    diagonalSubst_wzDeterminant, zero_mul, add_zero, map_zero] at hd
  have hQ₀ : Q = 0 := by
    rcases smul_eq_zero.mp hd with h₀ | h₀
    · omega
    · exact h₀
  refine ⟨hQ₀, ?_⟩
  rw [hQ₀, map_zero, zero_add, detMul_apply] at h
  have hr := (mul_eq_zero.mp h).resolve_left wzDeterminant_ne_zero
  exact rename_injective _ Sum.inr_injective (by simpa using hr)
theorem exists_intertwining_equiv_of_injective {G A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
    (U : A →ₗ[ℂ] B) (hU : Function.Injective U)
    (hdim : Module.finrank ℂ A = Module.finrank ℂ B)
    (a : G → A → A) (b : G → B → B) (hab : ∀ g x, U (a g x) = b g (U x)) :
    ∃ T : B ≃ₗ[ℂ] A, ∀ g P, T (b g P) = a g (T P) := by
  refine ⟨(U.linearEquivOfInjective hU hdim).symm, fun g P => ?_⟩
  rw [LinearEquiv.symm_apply_eq, LinearMap.linearEquivOfInjective_apply, hab]
  congr 1
  exact ((U.linearEquivOfInjective hU hdim).apply_symm_apply P).symm
theorem exists_equiv_of_doubled_eq_zero (l : HalfNatural) (h : l.doubled = 0) :
    ∃ T : bihomogeneousSpace l ≃ₗ[ℂ] homogeneousSpace l.addHalf,
      ∀ (g : specialUnitary) (P : bihomogeneousSpace l),
        T (tensorRep l g P) = spinRep l.addHalf g (T P) := by
  refine exists_intertwining_equiv_of_injective (polarizationMap l) ?_ ?_ _ _
    (polarizationMap_spinRep l)
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Q hQ
    have hQ₁ : polarization Q.1 + detMul 0 = 0 := by
      rw [map_zero, add_zero]
      exact congrArg Subtype.val hQ
    have hh : Q.1.IsHomogeneous (l.doubled + 1) := (mem_homogeneousSubmodule _ _).mp Q.2
    exact Subtype.ext (eq_zero_of_polarization_add_detMul_eq_zero hh hQ₁).1
  · rw [finrank_homogeneousSpace_eq, finrank_bihomogeneousSpace]
    simp [HalfNatural.addHalf, h]
theorem exists_equiv_of_succ (n : ℕ) :
    ∃ T : bihomogeneousSpace ⟨n + 1⟩ ≃ₗ[ℂ]
        homogeneousSpace (HalfNatural.addHalf ⟨n + 1⟩) × homogeneousSpace ⟨n⟩,
      ∀ (g : specialUnitary) (P : bihomogeneousSpace ⟨n + 1⟩),
        T (tensorRep ⟨n + 1⟩ g P) =
          (spinRep (HalfNatural.addHalf ⟨n + 1⟩) g (T P).1, spinRep ⟨n⟩ g (T P).2) := by
  refine exists_intertwining_equiv_of_injective
    ((polarizationMap ⟨n + 1⟩).coprod (detMulMap n)) ?_ ?_
    (fun g x => (spinRep (HalfNatural.addHalf ⟨n + 1⟩) g x.1, spinRep ⟨n⟩ g x.2))
    (fun g P => tensorRep ⟨n + 1⟩ g P) ?_
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨Q, R⟩ hQR
    have h₁ : polarization Q.1 + detMul R.1 = 0 := congrArg Subtype.val hQR
    have hh : Q.1.IsHomogeneous (n + 1 + 1) := (mem_homogeneousSubmodule _ _).mp Q.2
    obtain ⟨hq, hr⟩ := eq_zero_of_polarization_add_detMul_eq_zero hh h₁
    exact Prod.ext (Subtype.ext hq) (Subtype.ext hr)
  · have h₁ := finrank_homogeneousSpace_eq (HalfNatural.addHalf ⟨n + 1⟩)
    have h₂ := finrank_homogeneousSpace_eq ⟨n⟩
    have h₃ := finrank_bihomogeneousSpace ⟨n + 1⟩
    rw [Module.finrank_prod, h₁, h₂, h₃]
    simp only [HalfNatural.addHalf]
    omega
  · rintro g ⟨Q, R⟩
    simp only [LinearMap.coprod_apply, map_add, polarizationMap_spinRep, detMulMap_spinRep]
theorem entryMap_mul_mem_of_forms (l : HalfNatural) (S : Submodule ℂ C(specialUnitary, ℂ))
    (h : ∀ (μ : bihomogeneousSpace l →ₗ[ℂ] ℂ) (P : bihomogeneousSpace l),
      ∃ φ ∈ S, ∀ g, φ g = μ (tensorRep l g P))
    (ι κ : Fin 2) {ψ : C(specialUnitary, ℂ)} (hψ : ψ ∈ coeffSpan l) :
    entryMap ι κ * ψ ∈ S := by
  have hle : coeffSpan l ≤ S.comap (LinearMap.mulLeft ℂ (entryMap ι κ)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨a, c⟩, rfl⟩
    obtain ⟨φ, hφ, hg⟩ := h ((tensorCoord l ι a) ∘ₗ (bihomogeneousSpace l).subtype)
      (tensorBasisVec l κ c)
    have hφ₂ : entryMap ι κ * spinCoeffMap l a c = φ := by
      ext g
      rw [hg]
      have e := (Fintype.sum_prod_type' (fun (ι' : Fin 2) (a' : Fin (l.doubled + 1)) =>
        ((g : ComplexMatrix2) ι' κ * spinCoeff l a' c g) • tensorBasisVec l ι' a')).symm
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, tensorRep_tensorBasisVec_eq]
      rw [e]
      exact (tensorCoord_sum l
        (fun q => (g : ComplexMatrix2) q.1 κ * spinCoeff l q.2 c g) (ι, a)).symm
    change entryMap ι κ * spinCoeffMap l a c ∈ S
    rw [hφ₂]
    exact hφ
  exact hle hψ
theorem entryMap_mul_mem_of_doubled_eq_zero (l : HalfNatural) (h : l.doubled = 0) (ι κ : Fin 2)
    {ψ : C(specialUnitary, ℂ)} (hψ : ψ ∈ coeffSpan l) :
    entryMap ι κ * ψ ∈ coeffSpanPred l ⊔ coeffSpan l.addHalf := by
  refine entryMap_mul_mem_of_forms l _ (fun μ P => ?_) ι κ hψ
  obtain ⟨T, hT⟩ := exists_equiv_of_doubled_eq_zero l h
  obtain ⟨φ, hφ, hg⟩ := exists_mem_coeffSpan_eq_form l.addHalf (μ ∘ₗ T.symm.toLinearMap) (T P)
  refine ⟨φ, Submodule.mem_sup_right hφ, fun g => ?_⟩
  rw [hg, LinearMap.comp_apply, ← hT]
  simp
theorem entryMap_mul_mem_of_succ (n : ℕ) (ι κ : Fin 2) {ψ : C(specialUnitary, ℂ)}
    (hψ : ψ ∈ coeffSpan ⟨n + 1⟩) :
    entryMap ι κ * ψ ∈
      coeffSpanPred ⟨n + 1⟩ ⊔ coeffSpan (HalfNatural.addHalf ⟨n + 1⟩) := by
  refine entryMap_mul_mem_of_forms ⟨n + 1⟩ _ (fun μ P => ?_) ι κ hψ
  obtain ⟨T, hT⟩ := exists_equiv_of_succ n
  obtain ⟨φ₁, hφ₁, hg₁⟩ := exists_mem_coeffSpan_eq_form (HalfNatural.addHalf ⟨n + 1⟩)
    (μ ∘ₗ T.symm.toLinearMap ∘ₗ LinearMap.inl ℂ _ _) (T P).1
  obtain ⟨φ₂, hφ₂, hg₂⟩ := exists_mem_coeffSpan_eq_form ⟨n⟩
    (μ ∘ₗ T.symm.toLinearMap ∘ₗ LinearMap.inr ℂ _ _) (T P).2
  refine ⟨φ₂ + φ₁, Submodule.add_mem_sup (show φ₂ ∈ coeffSpanPred ⟨n + 1⟩ from hφ₂) hφ₁,
    fun g => ?_⟩
  have hP : tensorRep ⟨n + 1⟩ g P =
      T.symm (spinRep (HalfNatural.addHalf ⟨n + 1⟩) g (T P).1, spinRep ⟨n⟩ g (T P).2) := by
    rw [← hT, T.symm_apply_apply]
  rw [hP, ContinuousMap.add_apply, hg₁, hg₂]
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearEquiv.coe_coe, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
theorem allClebschGordan : AllClebschGordan := fun l =>
  { linearIndependent_tensorBasisVec := linearIndependent_tensorBasis l
    span_tensorBasisVec := span_tensorBasis l
    tensorRep_tensorBasisVec := tensorRep_tensorBasisVec_eq l
    equiv_of_doubled_eq_zero := exists_equiv_of_doubled_eq_zero l
    equiv_of_doubled_eq_succ := fun n h => by
      obtain ⟨t⟩ := l
      obtain rfl : t = n + 1 := h
      exact exists_equiv_of_succ n
    entryMap_mul_mem := fun ι κ ψ hψ => by
      obtain ⟨t⟩ := l
      cases t with
      | zero => exact entryMap_mul_mem_of_doubled_eq_zero _ rfl ι κ hψ
      | succ n => exact entryMap_mul_mem_of_succ n ι κ hψ }
end ClebschGordanProof
end YangMills.Construction.SpinHarmonics
