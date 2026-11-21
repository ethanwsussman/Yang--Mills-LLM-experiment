import YangMills.Construction.Lattice.EmptySupremumPauliMatricesAndFormsOnFiniteSets
import Mathlib
set_option autoImplicit false
open MeasureTheory MvPolynomial
open YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2
open scoped Matrix.Norms.L2Operator ENNReal
noncomputable section
namespace YangMills.Construction
namespace SpinHarmonics
structure HalfNatural where
  doubled : ℕ
  deriving DecidableEq
def HalfNatural.toReal (l : HalfNatural) : ℝ := (l.doubled : ℝ) / 2
abbrev homogeneousSpace (l : HalfNatural) : Submodule ℂ (MvPolynomial (Fin 2) ℂ) :=
  homogeneousSubmodule (Fin 2) ℂ l.doubled
def monomialNorm (l : HalfNatural) (a : Fin (l.doubled + 1)) : ℝ :=
  Real.sqrt (((a : ℕ).factorial : ℝ) * ((l.doubled - (a : ℕ)).factorial : ℝ))
theorem monomialNorm_pos (l : HalfNatural) (a : Fin (l.doubled + 1)) : 0 < monomialNorm l a :=
  Real.sqrt_pos.mpr (by positivity)
def monomialExponent (l : HalfNatural) (a : Fin (l.doubled + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (a : ℕ) + Finsupp.single 1 (l.doubled - (a : ℕ))
def normalizedMonomial (l : HalfNatural) (a : Fin (l.doubled + 1)) : MvPolynomial (Fin 2) ℂ :=
  C (((monomialNorm l a : ℝ) : ℂ)⁻¹) * X 0 ^ (a : ℕ) * X 1 ^ (l.doubled - (a : ℕ))
theorem normalizedMonomial_eq_monomial (l : HalfNatural) (a : Fin (l.doubled + 1)) :
    normalizedMonomial l a = monomial (monomialExponent l a) (((monomialNorm l a : ℝ) : ℂ)⁻¹) := by
  simp only [normalizedMonomial, monomialExponent, X_pow_eq_monomial, C_mul_monomial, mul_one,
    monomial_mul]
theorem degree_monomialExponent (l : HalfNatural) (a : Fin (l.doubled + 1)) :
    (monomialExponent l a).degree = l.doubled := by
  have ha : (a : ℕ) ≤ l.doubled := Nat.lt_succ_iff.mp a.2
  rw [monomialExponent, map_add, Finsupp.degree_single, Finsupp.degree_single]
  omega
def monomialBasis (l : HalfNatural) (a : Fin (l.doubled + 1)) : homogeneousSpace l :=
  ⟨normalizedMonomial l a, by
    rw [normalizedMonomial_eq_monomial, mem_homogeneousSubmodule]
    exact isHomogeneous_monomial _ (degree_monomialExponent l a)⟩
def monomialCoord (l : HalfNatural) (a : Fin (l.doubled + 1)) : homogeneousSpace l →ₗ[ℂ] ℂ :=
  ((monomialNorm l a : ℝ) : ℂ) • (lcoeff ℂ (monomialExponent l a)).comp (homogeneousSpace l).subtype
def homogeneousInner (l : HalfNatural) (P Q : homogeneousSpace l) : ℂ :=
  ∑ a, star (monomialCoord l a P) * monomialCoord l a Q
theorem monomialExponent_injective (l : HalfNatural) : Function.Injective (monomialExponent l) := by
  intro a c h
  have h0 := DFunLike.congr_fun h 0
  simp [monomialExponent] at h0
  exact Fin.ext h0
theorem monomialCoord_monomialBasis (l : HalfNatural) (a c : Fin (l.doubled + 1)) :
    monomialCoord l a (monomialBasis l c) = if a = c then 1 else 0 := by
  have hne : ((monomialNorm l a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (monomialNorm_pos l a).ne'
  simp only [monomialCoord, monomialBasis, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, lcoeff_apply, normalizedMonomial_eq_monomial, coeff_monomial,
    smul_eq_mul]
  by_cases h : a = c
  · subst h
    simp [hne]
  · have : monomialExponent l c ≠ monomialExponent l a := fun e => h (monomialExponent_injective l e).symm
    simp [h, this]
theorem homogeneousInner_monomialBasis (l : HalfNatural) (a c : Fin (l.doubled + 1)) :
    homogeneousInner l (monomialBasis l a) (monomialBasis l c) = if a = c then 1 else 0 := by
  simp only [homogeneousInner, monomialCoord_monomialBasis]
  by_cases h : a = c
  · subst h
    simp
  · have h' : ¬c = a := fun e => h e.symm
    simp [h, h']
theorem sum_monomialCoord_smul_monomialBasis (l : HalfNatural) (P : homogeneousSpace l) :
    ∑ a, monomialCoord l a P • monomialBasis l a = P := by
  have hne : ∀ a, ((monomialNorm l a : ℝ) : ℂ) ≠ 0 := fun a =>
    Complex.ofReal_ne_zero.mpr (monomialNorm_pos l a).ne'
  have hterm : ∀ a, ((monomialCoord l a P • monomialBasis l a : homogeneousSpace l) :
      MvPolynomial (Fin 2) ℂ) = monomial (monomialExponent l a) (coeff (monomialExponent l a) P.1) := by
    intro a
    simp only [monomialCoord, monomialBasis, Submodule.coe_smul, LinearMap.smul_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, lcoeff_apply,
      normalizedMonomial_eq_monomial, smul_eq_mul, smul_monomial]
    congr 1
    field_simp [hne a]
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [hterm]
  ext m
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hm : m.degree = l.doubled
  · have h0 : m 0 < l.doubled + 1 := by
      have : m.degree = m 0 + m 1 := by
        simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
      omega
    have hmx : monomialExponent l ⟨m 0, h0⟩ = m := by
      have : m.degree = m 0 + m 1 := by
        simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
      ext i
      fin_cases i
      · simp [monomialExponent]
      · simp [monomialExponent]
        omega
    rw [Finset.sum_eq_single ⟨m 0, h0⟩]
    · simp [hmx]
    · intro b _ hb
      have : monomialExponent l b ≠ m := fun e => hb (monomialExponent_injective l (e.trans hmx.symm))
      simp [this]
    · simp
  · have hP : coeff m P.1 = 0 := ((mem_homogeneousSubmodule _ _).mp P.2).coeff_eq_zero hm
    rw [hP]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : monomialExponent l b ≠ m := fun e => hm (e ▸ degree_monomialExponent l b)
    simp [this]
theorem star_homogeneousInner (l : HalfNatural) (P Q : homogeneousSpace l) :
    star (homogeneousInner l P Q) = homogeneousInner l Q P := by
  simp [homogeneousInner, mul_comm]
def rowMul (z : Fin 2 → ℂ) (g : ComplexMatrix2) (j : Fin 2) : ℂ := z 0 * g 0 j + z 1 * g 1 j
def columnForms (g : ComplexMatrix2) (j : Fin 2) : MvPolynomial (Fin 2) ℂ :=
  C (g 0 j) * X 0 + C (g 1 j) * X 1
theorem isHomogeneous_columnForms (g : ComplexMatrix2) (i : Fin 2) :
    (columnForms g i).IsHomogeneous 1 := by
  have hl : ∀ (j : Fin 2) (c : ℂ), (C c * X j : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
    intro j c
    simpa using (isHomogeneous_C (Fin 2) c).mul (isHomogeneous_X ℂ j)
  exact (hl 0 _).add (hl 1 _)
def spinRep (l : HalfNatural) (g : specialUnitary) : homogeneousSpace l →ₗ[ℂ] homogeneousSpace l :=
  (aeval (columnForms (g : ComplexMatrix2)) :
      MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ).toLinearMap.restrict
    fun P hP => by
      rw [mem_homogeneousSubmodule] at hP ⊢
      simpa using hP.aeval _ (isHomogeneous_columnForms (g : ComplexMatrix2))
theorem eval_spinRep (l : HalfNatural) (g : specialUnitary) (P : homogeneousSpace l)
    (z : Fin 2 → ℂ) :
    eval z (spinRep l g P : MvPolynomial (Fin 2) ℂ) =
      eval (rowMul z (g : ComplexMatrix2)) (P : MvPolynomial (Fin 2) ℂ) := by
  have key : ∀ p : MvPolynomial (Fin 2) ℂ,
      eval z (aeval (columnForms (g : ComplexMatrix2)) p) = eval (rowMul z (g : ComplexMatrix2)) p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, aeval_X, eval_X]
      simp [columnForms, rowMul, mul_comm]
  exact key P
def spinCoeff (l : HalfNatural) (a c : Fin (l.doubled + 1)) (g : specialUnitary) : ℂ :=
  homogeneousInner l (monomialBasis l a) (spinRep l g (monomialBasis l c))
theorem continuous_coeff_aeval_linearForms {T : Type*} [TopologicalSpace T]
    (f : T → Fin 2 → MvPolynomial (Fin 2) ℂ)
    (hf : ∀ i m, Continuous fun x => coeff m (f x i)) (P : MvPolynomial (Fin 2) ℂ) :
    ∀ m, Continuous fun x => coeff m (aeval (f x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro m
    simpa [algebraMap_eq] using continuous_const
  | add p q hp hq =>
    intro m
    simp only [map_add, coeff_add]
    exact (hp m).add (hq m)
  | mul_X p i hp =>
    intro m
    simp only [map_mul, aeval_X, coeff_mul]
    exact continuous_finsetSum _ fun d _ => (hp d.1).mul (hf i d.2)
theorem continuous_coeff_columnForms (i : Fin 2) (m : Fin 2 →₀ ℕ) :
    Continuous fun g : specialUnitary => coeff m (columnForms (g : ComplexMatrix2) i) := by
  have he : ∀ r s : Fin 2, Continuous fun g : specialUnitary => (g : ComplexMatrix2) r s := fun r s =>
    Continuous.matrix_elem (A := fun g : specialUnitary => (g : ComplexMatrix2)) continuous_subtype_val r s
  simp only [columnForms, coeff_add, coeff_C_mul]
  exact ((he _ _).mul continuous_const).add ((he _ _).mul continuous_const)
theorem continuous_spinCoeff (l : HalfNatural) (a c : Fin (l.doubled + 1)) :
    Continuous (spinCoeff l a c) := by
  have h : ∀ d, Continuous fun g : specialUnitary =>
      monomialCoord l d (spinRep l g (monomialBasis l c)) := fun d =>
    continuous_const.mul (continuous_coeff_aeval_linearForms
      (fun g : specialUnitary => columnForms (g : ComplexMatrix2))
      continuous_coeff_columnForms (normalizedMonomial l c) (monomialExponent l d))
  have h₂ : spinCoeff l a c = fun g : specialUnitary => ∑ d, star (monomialCoord l d (monomialBasis l a)) *
      monomialCoord l d (spinRep l g (monomialBasis l c)) := rfl
  rw [h₂]
  exact continuous_finsetSum _ fun d _ => continuous_const.mul (h d)
def spinCoeffMap (l : HalfNatural) (a c : Fin (l.doubled + 1)) : C(specialUnitary, ℂ) :=
  ⟨spinCoeff l a c, continuous_spinCoeff l a c⟩
def coeffSpan (l : HalfNatural) : Submodule ℂ C(specialUnitary, ℂ) :=
  Submodule.span ℂ (Set.range fun p : Fin (l.doubled + 1) × Fin (l.doubled + 1) =>
    spinCoeffMap l p.1 p.2)
def coeffSpanBelowZero : Submodule ℂ C(specialUnitary, ℂ) := ⊥
def spinCharacter (l : HalfNatural) : C(specialUnitary, ℂ) := ∑ a, spinCoeffMap l a a
def coeffSpanL2 (l : HalfNatural) : Submodule ℂ (Lp ℂ 2 haarProb) :=
  (coeffSpan l).map (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ).toLinearMap
instance (l : HalfNatural) : FiniteDimensional ℂ (coeffSpan l) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
instance (l : HalfNatural) : FiniteDimensional ℂ (coeffSpanL2 l) := by
  unfold coeffSpanL2
  infer_instance
def coeffProjection (l : HalfNatural) : Lp ℂ 2 haarProb →L[ℂ] Lp ℂ 2 haarProb :=
  (coeffSpanL2 l).starProjection
def IsConjInvariant {α : Type*} (F : specialUnitary → α) : Prop :=
  ∀ g h : specialUnitary, F (h * g * h⁻¹) = F g
def diagPhaseMatrix (φ : ℝ) : ComplexMatrix2 :=
  !![Complex.exp (Complex.I * φ), 0; 0, Complex.exp (-(Complex.I * φ))]
theorem diagPhaseMatrix_mem (φ : ℝ) : diagPhaseMatrix φ ∈ specialUnitary := by
  have h₁ : Complex.exp (Complex.I * φ) * Complex.exp (-(Complex.I * φ)) = 1 := by
    rw [← Complex.exp_add]; simp
  have h₂ : Complex.exp (-(Complex.I * φ)) * Complex.exp (Complex.I * φ) = 1 := by
    rw [mul_comm, h₁]
  have hc : (starRingEnd ℂ) (Complex.exp (Complex.I * φ)) = Complex.exp (-(Complex.I * φ)) := by
    rw [← Complex.exp_conj]
    simp
  have hc' : (starRingEnd ℂ) (Complex.exp (-(Complex.I * φ))) = Complex.exp (Complex.I * φ) := by
    rw [← hc, Complex.conj_conj]
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagPhaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, hc, hc',
        h₁, h₂]
  · simp [diagPhaseMatrix, Matrix.det_fin_two, h₁]
def diagPhase (φ : ℝ) : specialUnitary := ⟨diagPhaseMatrix φ, diagPhaseMatrix_mem φ⟩
def lieGenerator (ι : Fin 3) : ComplexMatrix2 := (Complex.I / 2) • pauli ι
theorem matExp_mul_matExp_neg (Z : ComplexMatrix2) : matExp Z * matExp (-Z) = 1 := by
  rw [matExp, matExp, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))
theorem det_matExp_of_trace_eq_zero {Z : ComplexMatrix2} (hz : fullTrace Z = 0) :
    (matExp Z).det = 1 := by
  let W : ComplexMatrix2ˣ :=
    ⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hW : ((W⁻¹ : ComplexMatrix2ˣ) : ComplexMatrix2) = !![0, -1; 1, 0] := rfl
  have hW' : (W : ComplexMatrix2) = !![0, 1; -1, 0] := rfl
  have h₁ : Z 1 1 = -Z 0 0 := by
    have : Z 0 0 + Z 1 1 = 0 := by simpa [fullTrace, Matrix.trace_fin_two] using hz
    linear_combination this
  have hconj : (W : ComplexMatrix2) * Z.transpose * ((W⁻¹ : ComplexMatrix2ˣ) : ComplexMatrix2) = -Z := by
    rw [hW, hW']
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [h₁]
  have hexp : (W : ComplexMatrix2) * (matExp Z).transpose * ((W⁻¹ : ComplexMatrix2ˣ) : ComplexMatrix2) =
      matExp (-Z) := by
    rw [← hconj, matExp, matExp, Matrix.exp_units_conj, Matrix.exp_transpose]
  have hid : ∀ A : ComplexMatrix2,
      A * ((W : ComplexMatrix2) * A.transpose * ((W⁻¹ : ComplexMatrix2ˣ) : ComplexMatrix2)) = A.det • 1 := by
    intro A
    rw [hW, hW']
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp [Matrix.det_fin_two] <;> ring
  have h := hid (matExp Z)
  rw [hexp, matExp_mul_matExp_neg] at h
  have h₀ := congrFun (congrFun h 0) 0
  simpa using h₀.symm
theorem matExp_mem_of_skewAdjoint {Z : ComplexMatrix2} (hZ : star Z = -Z) (hz : fullTrace Z = 0) :
    matExp Z ∈ specialUnitary := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, det_matExp_of_trace_eq_zero hz⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, matExp, ← Matrix.exp_conjTranspose,
    ← Matrix.star_eq_conjTranspose, hZ]
  exact matExp_mul_matExp_neg Z
theorem matExp_real_smul_lieGenerator_mem (ι : Fin 3) (t : ℝ) :
    matExp ((t : ℂ) • lieGenerator ι) ∈ specialUnitary := by
  apply matExp_mem_of_skewAdjoint
  · ext i j
    fin_cases ι <;> fin_cases i <;> fin_cases j <;>
      simp [lieGenerator, pauli, pauliOne, pauliTwo, pauliThree] <;> ring
  · fin_cases ι <;>
      simp [fullTrace, lieGenerator, pauli, pauliOne, pauliTwo, pauliThree, Matrix.trace_fin_two]
def oneParam (ι : Fin 3) (t : ℝ) : specialUnitary :=
  ⟨matExp ((t : ℂ) • lieGenerator ι), matExp_real_smul_lieGenerator_mem ι t⟩
variable {J : Type*}
open Classical in
def shiftAt (u : J → specialUnitary) (b : J) (ι : Fin 3) (t : ℝ) : J → specialUnitary :=
  Function.update u b (u b * oneParam ι t)
def HasDirDerivAt (b : J) (ι : Fin 3) (F : (J → specialUnitary) → ℂ) (u : J → specialUnitary) : Prop :=
  DifferentiableAt ℝ (fun t : ℝ => F (shiftAt u b ι t)) 0
def rightField (b : J) (ι : Fin 3) (F : (J → specialUnitary) → ℂ) (u : J → specialUnitary) : ℂ :=
  deriv (fun t : ℝ => F (shiftAt u b ι t)) 0
def rightFieldOne (ι : Fin 3) (F : specialUnitary → ℂ) (g : specialUnitary) : ℂ :=
  deriv (fun t : ℝ => F (g * oneParam ι t)) 0
theorem rightField_of_unique [Unique J] (b : J) (ι : Fin 3) (F : specialUnitary → ℂ)
    (u : J → specialUnitary) :
    rightField b ι (fun v => F (v b)) u = rightFieldOne ι F (u b) := by
  simp [rightField, rightFieldOne, shiftAt]
def casimirOp (F : specialUnitary → ℂ) (g : specialUnitary) : ℂ :=
  -∑ ι, rightFieldOne ι (rightFieldOne ι F) g
def smoothOrder : ℕ → Set ((J → specialUnitary) → ℂ)
  | 0 => {F | Continuous F}
  | q + 1 => {F | Continuous F ∧ ∀ (b : J) (ι : Fin 3),
      (∀ u, HasDirDerivAt b ι F u) ∧ rightField b ι F ∈ smoothOrder q}
def smoothSet : Set ((J → specialUnitary) → ℂ) := ⋂ q, smoothOrder q
def fieldWord (w : List (J × Fin 3)) (F : (J → specialUnitary) → ℂ) : (J → specialUnitary) → ℂ :=
  w.foldr (fun p H => rightField p.1 p.2 H) F
abbrev EntryVar (J : Type*) : Type _ := (J × Fin 2 × Fin 2) ⊕ (J × Fin 2 × Fin 2)
def entryEval (u : J → specialUnitary) : EntryVar J → ℂ
  | .inl (b, i, j) => (u b : ComplexMatrix2) i j
  | .inr (b, i, j) => star ((u b : ComplexMatrix2) i j)
def IsEntryPolynomial (F : (J → specialUnitary) → ℂ) : Prop :=
  ∃ p : MvPolynomial (EntryVar J) ℂ, ∀ u, F u = eval (entryEval u) p
end SpinHarmonics
end YangMills.Construction
