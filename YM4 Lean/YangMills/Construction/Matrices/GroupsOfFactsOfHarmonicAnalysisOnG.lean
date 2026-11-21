import YangMills.Construction.HilbertSpace.SchattenTraceKernels
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 MvPolynomial
open scoped Matrix.Norms.L2Operator ENNReal
noncomputable section
namespace YangMills.Construction
namespace SpinHarmonics
def HalfNatural.oneHalf : HalfNatural := ⟨1⟩
def HalfNatural.addHalf (j : HalfNatural) : HalfNatural := ⟨j.doubled + 1⟩
def entryValues (U : specialUnitary) (q : Fin 2 × Fin 2) : ℂ :=
  (U : Matrices.ComplexMatrix2) q.1 q.2
def entryMap (r s : Fin 2) : C(specialUnitary, ℂ) :=
  ⟨fun U => (U : Matrices.ComplexMatrix2) r s,
    Continuous.matrix_elem (A := fun U : specialUnitary => (U : Matrices.ComplexMatrix2))
      continuous_subtype_val r s⟩
def IsPolyInEntries (f : specialUnitary → ℂ) : Prop :=
  ∃ q : MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ U, f U = eval (entryValues U) q
def IsInCoeffSpan (j : HalfNatural) (f : specialUnitary → ℂ) : Prop :=
  ∃ φ ∈ coeffSpan j, ∀ U, φ U = f U
def coeffSpanPred (j : HalfNatural) : Submodule ℂ C(specialUnitary, ℂ) :=
  match j.doubled with
  | 0 => coeffSpanBelowZero
  | m + 1 => coeffSpan ⟨m⟩
def linearMonomial (s : Fin 2) : homogeneousSpace HalfNatural.oneHalf :=
  ⟨X s, by
    rw [mem_homogeneousSubmodule]
    exact isHomogeneous_X ℂ s⟩
def scaledCoeffL2 (j : HalfNatural) (q : Fin (j.doubled + 1) × Fin (j.doubled + 1)) :
    Lp ℂ 2 haarProb :=
  ((Real.sqrt (2 * j.toReal + 1) : ℝ) : ℂ) •
    ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ (spinCoeffMap j q.1 q.2)
def asSingletonFamily (f : specialUnitary → ℂ) (x : Unit → specialUnitary) : ℂ := f (x ())
def IsC1 (f : specialUnitary → ℂ) : Prop :=
  asSingletonFamily f ∈ smoothOrder (J := Unit) 1
def wzDegree : Fin 2 ⊕ Fin 2 → ℕ × ℕ
  | .inl _ => (1, 0)
  | .inr _ => (0, 1)
def bihomogeneousSpace (j : HalfNatural) : Submodule ℂ (MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) :=
  weightedHomogeneousSubmodule ℂ wzDegree (1, j.doubled)
def rowSubst (M : Matrices.ComplexMatrix2) : Fin 2 ⊕ Fin 2 → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ
  | .inl k => C (M 0 k) * X (.inl 0) + C (M 1 k) * X (.inl 1)
  | .inr k => C (M 0 k) * X (.inr 0) + C (M 1 k) * X (.inr 1)
theorem isWeightedHomogeneous_rowSubst (M : Matrices.ComplexMatrix2) (v : Fin 2 ⊕ Fin 2) :
    (rowSubst M v).IsWeightedHomogeneous wzDegree (wzDegree v) := by
  have hterm : ∀ (k : Fin 2 ⊕ Fin 2) (a : ℂ),
      (C a * X k : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).IsWeightedHomogeneous wzDegree (wzDegree k) :=
    fun k a => (isWeightedHomogeneous_X ℂ wzDegree k).C_mul a
  rcases v with k | k
  · exact (hterm (.inl 0) _).add (hterm (.inl 1) _)
  · exact (hterm (.inr 0) _).add (hterm (.inr 1) _)
theorem isWeightedHomogeneous_aeval_rowSubst (M : Matrices.ComplexMatrix2)
    {Q : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ}
    {n : ℕ × ℕ} (hQ : Q.IsWeightedHomogeneous wzDegree n) :
    (aeval (rowSubst M) Q).IsWeightedHomogeneous wzDegree n := by
  rw [aeval_def, eval₂_eq]
  refine IsWeightedHomogeneous.sum _ _ n fun e he => ?_
  have hwt : Finsupp.weight wzDegree e = n := hQ (mem_support_iff.mp he)
  have hprod := IsWeightedHomogeneous.prod e.support (fun v => rowSubst M v ^ e v)
    (fun v => e v • wzDegree v) (fun v _ => (isWeightedHomogeneous_rowSubst M v).pow (e v))
  have hsum : ∑ v ∈ e.support, e v • wzDegree v = n := by
    rw [← hwt, Finsupp.weight_apply, Finsupp.sum]
  rw [hsum] at hprod
  exact hprod.C_mul _
def tensorRep (j : HalfNatural) (U : specialUnitary) :
    bihomogeneousSpace j →ₗ[ℂ] bihomogeneousSpace j :=
  (aeval (rowSubst (U : Matrices.ComplexMatrix2)) :
      MvPolynomial (Fin 2 ⊕ Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).toLinearMap.restrict
    fun _ hQ => isWeightedHomogeneous_aeval_rowSubst (U : Matrices.ComplexMatrix2) hQ
def tensorMonomial (j : HalfNatural) (r : Fin 2) (m : Fin (j.doubled + 1)) :
    MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  X (.inl r) * rename Sum.inr (normalizedMonomial j m)
def tensorBasisVec (j : HalfNatural) (r : Fin 2) (m : Fin (j.doubled + 1)) :
    bihomogeneousSpace j :=
  ⟨tensorMonomial j r m, by
    have hm : (m : ℕ) ≤ j.doubled := Nat.lt_succ_iff.mp m.2
    have hy : ∀ k : Fin 2, (X (.inr k) : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).IsWeightedHomogeneous
        wzDegree (0, 1) := fun k => isWeightedHomogeneous_X ℂ wzDegree (.inr k)
    have hhom := (isWeightedHomogeneous_X ℂ wzDegree (.inl r)).mul
      ((((hy 0).pow (m : ℕ)).mul ((hy 1).pow (j.doubled - (m : ℕ)))).C_mul
        (((monomialNorm j m : ℝ) : ℂ)⁻¹))
    have hdeg : wzDegree (.inl r) + ((m : ℕ) • ((0, 1) : ℕ × ℕ) +
        (j.doubled - (m : ℕ)) • ((0, 1) : ℕ × ℕ)) = (1, j.doubled) := by
      simp [wzDegree]
      omega
    rw [hdeg] at hhom
    rw [bihomogeneousSpace, mem_weightedHomogeneousSubmodule]
    simpa [tensorMonomial, normalizedMonomial, mul_assoc] using hhom⟩
structure SpinRepFacts (j j' : HalfNatural) : Prop where
  finrank_homogeneousSpace : Module.finrank ℂ (homogeneousSpace j) = j.doubled + 1
  spinRep_mul : ∀ U V : specialUnitary,
    spinRep j (U * V) = spinRep j U ∘ₗ spinRep j V
  spinRep_one : spinRep j 1 = LinearMap.id
  spinRep_isometry : ∀ (U : specialUnitary) (P Q : homogeneousSpace j),
    homogeneousInner j (spinRep j U P) (spinRep j U Q) = homogeneousInner j P Q
  spinCoeff_inv : ∀ (U : specialUnitary) (m n : Fin (j.doubled + 1)),
    spinCoeff j m n U⁻¹ = star (spinCoeff j n m U)
  spinCoeff_isHomogeneous : ∀ m n : Fin (j.doubled + 1),
    ∃ q : MvPolynomial (Fin 2 × Fin 2) ℝ, q.IsHomogeneous j.doubled ∧
      ∀ U, spinCoeff j m n U = aeval (entryValues U) q
  spinRep_oneHalf : ∀ (U : specialUnitary) (s : Fin 2),
    spinRep HalfNatural.oneHalf U (linearMonomial s) =
      ∑ r, (U : Matrices.ComplexMatrix2) r s • linearMonomial r
  range_spinCoeffMap_oneHalf :
    Set.range (fun q : Fin (HalfNatural.oneHalf.doubled + 1) × Fin (HalfNatural.oneHalf.doubled + 1) =>
      spinCoeffMap HalfNatural.oneHalf q.1 q.2) =
    Set.range (fun q : Fin 2 × Fin 2 => entryMap q.1 q.2)
  eq_smul_id_of_commute : ∀ T : homogeneousSpace j →ₗ[ℂ] homogeneousSpace j,
    (∀ U, T ∘ₗ spinRep j U = spinRep j U ∘ₗ T) → ∃ a : ℂ, T = a • LinearMap.id
  eq_bot_or_top_of_invariant : ∀ W : Submodule ℂ (homogeneousSpace j),
    (∀ U, ∀ P ∈ W, spinRep j U P ∈ W) → W = ⊥ ∨ W = ⊤
  eq_zero_of_intertwines : j ≠ j' → ∀ T : homogeneousSpace j →ₗ[ℂ] homogeneousSpace j',
    (∀ U, T ∘ₗ spinRep j U = spinRep j' U ∘ₗ T) → T = 0
structure PeterWeylFacts (j j' : HalfNatural) : Prop where
  integral_star_spinCoeff_mul : ∀ (m n : Fin (j.doubled + 1)) (m' n' : Fin (j'.doubled + 1)),
    ∫ U, star (spinCoeff j m n U) * spinCoeff j' m' n' U ∂haarProb =
      (if j = j' ∧ (m : ℕ) = m' ∧ (n : ℕ) = n' then 1 else 0) / ((2 * j.toReal + 1 : ℝ) : ℂ)
  finrank_coeffSpan : Module.finrank ℂ (coeffSpan j) = (j.doubled + 1) ^ 2
  orthonormal_scaledCoeffL2 : Orthonormal ℂ (scaledCoeffL2 j)
  span_scaledCoeffL2 :
    Submodule.span ℂ (Set.range (scaledCoeffL2 j)) = coeffSpanL2 j
  isPolyInEntries_of_mem : ∀ φ ∈ coeffSpan j, IsPolyInEntries φ
  isPolyInEntries_iff : ∀ f : specialUnitary → ℂ,
    IsPolyInEntries f ↔ ∃ φ ∈ ⨆ k, coeffSpan k, ∀ U, φ U = f U
  leftTranslate_mem : ∀ φ ∈ coeffSpan j, ∀ V : specialUnitary,
    IsInCoeffSpan j fun U => φ (V * U)
  rightTranslate_mem : ∀ φ ∈ coeffSpan j, ∀ V : specialUnitary,
    IsInCoeffSpan j fun U => φ (U * V)
  star_mem : ∀ φ ∈ coeffSpan j, IsInCoeffSpan j fun U => star (φ U)
  comp_inv_mem : ∀ φ ∈ coeffSpan j, IsInCoeffSpan j fun U => φ U⁻¹
  coeffSpanL2_isOrtho : ∀ k k' : HalfNatural, k ≠ k' → (coeffSpanL2 k).IsOrtho (coeffSpanL2 k')
  hasSum_coeffProjection : ∀ f : Lp ℂ 2 haarProb, HasSum (fun k => coeffProjection k f) f
structure SpinCharacterFacts (j : HalfNatural) : Prop where
  im_eq_zero : ∀ U, (spinCharacter j U).im = 0
  isConjInvariant : IsConjInvariant (spinCharacter j)
  apply_inv : ∀ U, spinCharacter j U⁻¹ = spinCharacter j U
  apply_one : spinCharacter j 1 = ((2 * j.toReal + 1 : ℝ) : ℂ)
  norm_le : ∀ U, ‖spinCharacter j U‖ ≤ 2 * j.toReal + 1
  oneHalf_eq_fullTrace : ∀ U : specialUnitary,
    spinCharacter HalfNatural.oneHalf U = fullTrace (U : Matrices.ComplexMatrix2)
  exists_conj_diagPhase : ∀ U : specialUnitary,
    ∃ V : specialUnitary, ∃ θ ∈ Set.Icc 0 Real.pi, U = V * diagPhase θ * V⁻¹
  of_eq_conj_diagPhase : ∀ (U V : specialUnitary), ∀ θ ∈ Set.Icc 0 Real.pi,
    U = V * diagPhase θ * V⁻¹ →
      (∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (U : Matrices.ComplexMatrix2)) μ ↔
        μ = Complex.exp (Complex.I * θ) ∨ μ = Complex.exp (-(Complex.I * θ))) ∧
      halfTrace (U : Matrices.ComplexMatrix2) = (Real.cos θ : ℂ) ∧
      spinCharacter j U * (Real.sin θ : ℂ) = (Real.sin ((2 * j.toReal + 1) * θ) : ℂ)
def WeylIntegralFormula : Prop :=
  ∀ f : C(specialUnitary, ℂ), IsConjInvariant f →
    ∫ U, f U ∂haarProb =
      ((2 / Real.pi : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..Real.pi, f (diagPhase θ) * ((Real.sin θ ^ 2 : ℝ) : ℂ)
structure CoeffProjectionFacts (j j' : HalfNatural) : Prop where
  hasKernel : Schatten.HasKernel haarProb
    (fun q : specialUnitary × specialUnitary =>
      ((2 * j.toReal + 1 : ℝ) : ℂ) * spinCharacter j (q.1 * q.2⁻¹)) (coeffProjection j)
  kernel_eq_sum : ∀ U U' : specialUnitary,
    ((2 * j.toReal + 1 : ℝ) : ℂ) * spinCharacter j (U * U'⁻¹) =
      ((2 * j.toReal + 1 : ℝ) : ℂ) *
        ∑ m, ∑ n, spinCoeff j m n U * star (spinCoeff j m n U')
  translate : ∀ (V V' : specialUnitary) (f f' : Lp ℂ 2 haarProb),
    f' =ᵐ[haarProb] (fun U => f (V * U * V')) →
      coeffProjection j f' =ᵐ[haarProb] fun U => coeffProjection j f (V * U * V')
  apply_of_isConjInvariant : ∀ f : specialUnitary → ℂ, Measurable f → IsConjInvariant f →
    ∀ hf : MemLp f 2 haarProb,
      coeffProjection j (hf.toLp f) =
        (∫ U, star (spinCharacter j U) * f U ∂haarProb) •
          ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ (spinCharacter j)
  integral_spinCharacter_mul : ∀ U U' : specialUnitary,
    ∫ V, spinCharacter j (U * V⁻¹) * spinCharacter j' (V * U'⁻¹) ∂haarProb =
      (if j = j' then 1 else 0) * ((2 * j.toReal + 1 : ℝ) : ℂ)⁻¹ * spinCharacter j (U * U'⁻¹)
structure ClebschGordanFacts (j : HalfNatural) : Prop where
  linearIndependent_tensorBasisVec : LinearIndependent ℂ
    (fun q : Fin 2 × Fin (j.doubled + 1) => tensorBasisVec j q.1 q.2)
  span_tensorBasisVec : Submodule.span ℂ
    (Set.range fun q : Fin 2 × Fin (j.doubled + 1) => tensorBasisVec j q.1 q.2) = ⊤
  tensorRep_tensorBasisVec : ∀ (U : specialUnitary) (s : Fin 2) (n : Fin (j.doubled + 1)),
    tensorRep j U (tensorBasisVec j s n) =
      ∑ r, ∑ m, ((U : Matrices.ComplexMatrix2) r s * spinCoeff j m n U) • tensorBasisVec j r m
  equiv_of_doubled_eq_zero : j.doubled = 0 →
    ∃ T : bihomogeneousSpace j ≃ₗ[ℂ] homogeneousSpace j.addHalf,
      ∀ (U : specialUnitary) (Q : bihomogeneousSpace j),
        T (tensorRep j U Q) = spinRep j.addHalf U (T Q)
  equiv_of_doubled_eq_succ : ∀ k : ℕ, j.doubled = k + 1 →
    ∃ T : bihomogeneousSpace j ≃ₗ[ℂ] homogeneousSpace j.addHalf × homogeneousSpace ⟨k⟩,
      ∀ (U : specialUnitary) (Q : bihomogeneousSpace j),
        T (tensorRep j U Q) =
          (spinRep j.addHalf U (T Q).1, spinRep ⟨k⟩ U (T Q).2)
  entryMap_mul_mem : ∀ (r s : Fin 2), ∀ φ ∈ coeffSpan j,
    entryMap r s * φ ∈ coeffSpanPred j ⊔ coeffSpan j.addHalf
structure RightFieldFacts (j : HalfNatural) : Prop where
  integral_rightFieldOne_mul : ∀ (r : Fin 3) (f h : specialUnitary → ℂ),
    IsC1 f → IsC1 h →
      ∫ U, rightFieldOne r f U * h U ∂haarProb = -∫ U, f U * rightFieldOne r h U ∂haarProb
  hasDirDerivAt : ∀ (r : Fin 3), ∀ φ ∈ coeffSpan j, ∀ x : Unit → specialUnitary,
    HasDirDerivAt () r (asSingletonFamily φ) x
  rightFieldOne_mem : ∀ (r : Fin 3), ∀ φ ∈ coeffSpan j,
    IsInCoeffSpan j (rightFieldOne r φ)
  casimirOp_eq : ∀ φ ∈ coeffSpan j, ∀ U,
    casimirOp φ U = ((j.toReal * (j.toReal + 1) : ℝ) : ℂ) * φ U
def ConjInvariantKernelFormula (j : HalfNatural) : Prop :=
  ∀ f : C(specialUnitary, ℂ), IsConjInvariant f → ∀ φ ∈ coeffSpan j, ∀ U : specialUnitary,
    ∫ V, f (U * V⁻¹) * φ V ∂haarProb =
      ((2 * j.toReal + 1 : ℝ) : ℂ)⁻¹ * (∫ W, star (spinCharacter j W) * f W ∂haarProb) * φ U
end SpinHarmonics
end YangMills.Construction
