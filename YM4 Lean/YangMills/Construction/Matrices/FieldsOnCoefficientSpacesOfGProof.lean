import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfG
import YangMills.Construction.Matrices.FieldsOnCoefficientSpacesOfG
import YangMills.Construction.Matrices.RepresentationsOfGAreUnitaryAndIrreducible
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Matrices.ComplexMatrix2 MvPolynomial
open scoped Matrix.Norms.L2Operator
namespace SpinHarmonics.RightFieldProof
def genDerivation (ι : Fin 3) :
    Derivation ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial (Fin 2) ℂ) :=
  mkDerivation ℂ (columnForms (lieGenerator ι))
def eulerDeriv : Derivation ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial (Fin 2) ℂ) :=
  mkDerivation ℂ X
theorem eulerDeriv_of_isHomogeneous {n : ℕ} {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsHomogeneous n) : eulerDeriv P = n • P := by
  have h : eulerDeriv = (X 0 : MvPolynomial (Fin 2) ℂ) • pderiv 0 +
      (X 1 : MvPolynomial (Fin 2) ℂ) • pderiv 1 := by
    apply derivation_ext
    intro i
    fin_cases i <;> simp [eulerDeriv, mkDerivation_X, pderiv_X]
  have e := hP.sum_X_mul_pderiv
  rw [Fin.sum_univ_two] at e
  rw [h, ← e]
  simp
theorem genDerivation_X (ι : Fin 3) (j : Fin 2) :
    genDerivation ι (X j) = columnForms (lieGenerator ι) j :=
  mkDerivation_X ℂ _ j
theorem derivation_C_mul_left (D : Derivation ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial (Fin 2) ℂ))
    (c : ℂ) (q : MvPolynomial (Fin 2) ℂ) : D (C c * q) = C c * D q := by
  rw [Derivation.leibniz, derivation_C]
  simp
theorem derivation_derivation_mul
    (D : Derivation ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial (Fin 2) ℂ))
    (p q : MvPolynomial (Fin 2) ℂ) :
    D (D (p * q)) = p * D (D q) + 2 * D p * D q + q * D (D p) := by
  simp only [Derivation.leibniz, map_add, smul_eq_mul]
  ring
section Table
def halfConst : MvPolynomial (Fin 2) ℂ := C (1 / 2)
def halfImag : MvPolynomial (Fin 2) ℂ := C (Complex.I / 2)
theorem halfImag_mul_self : halfImag * halfImag = -(halfConst * halfConst) := by
  rw [halfImag, halfConst, ← C_mul, ← C_mul, ← C_neg]
  congr 1
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 4 : ℂ) * this
theorem genDerivation_zero_X_zero : genDerivation 0 (X 0) = halfImag * X 1 := by
  simp [genDerivation_X, columnForms, lieGenerator, pauli, pauliOne, halfImag]
theorem genDerivation_zero_X_one : genDerivation 0 (X 1) = halfImag * X 0 := by
  simp [genDerivation_X, columnForms, lieGenerator, pauli, pauliOne, halfImag]
theorem genDerivation_one_X_zero : genDerivation 1 (X 0) = -(halfConst * X 1) := by
  have : (Complex.I / 2 * Complex.I) = -(1 / 2) := by
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * this
  simp [genDerivation_X, columnForms, lieGenerator, pauli, pauliTwo, halfConst, this]
theorem genDerivation_one_X_one : genDerivation 1 (X 1) = halfConst * X 0 := by
  have : (Complex.I / 2 * -Complex.I) = 1 / 2 := by
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-1 / 2 : ℂ) * this
  simp [genDerivation_X, columnForms, lieGenerator, pauli, pauliTwo, halfConst, this]
theorem genDerivation_two_X_zero : genDerivation 2 (X 0) = halfImag * X 0 := by
  simp [genDerivation_X, columnForms, lieGenerator, pauli, pauliThree, halfImag]
theorem genDerivation_two_X_one : genDerivation 2 (X 1) = -(halfImag * X 1) := by
  simp [genDerivation_X, columnForms, lieGenerator, pauli, pauliThree, halfImag]
theorem derivation_halfImag_mul
    (D : Derivation ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial (Fin 2) ℂ))
    (q : MvPolynomial (Fin 2) ℂ) : D (halfImag * q) = halfImag * D q :=
  derivation_C_mul_left D _ q
theorem derivation_halfConst_mul
    (D : Derivation ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial (Fin 2) ℂ))
    (q : MvPolynomial (Fin 2) ℂ) : D (halfConst * q) = halfConst * D q :=
  derivation_C_mul_left D _ q
theorem sum_genDerivation_X_mul (i j : Fin 2) :
    genDerivation 0 (X j) * genDerivation 0 (X i) +
        genDerivation 1 (X j) * genDerivation 1 (X i) +
        genDerivation 2 (X j) * genDerivation 2 (X i) =
      -(halfConst * halfConst) * (X j * X i) := by
  have hs := halfImag_mul_self
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, genDerivation_zero_X_zero,
      genDerivation_zero_X_one, genDerivation_one_X_zero, genDerivation_one_X_one,
      genDerivation_two_X_zero, genDerivation_two_X_one]
  · linear_combination (X 1 * X 1 + X 0 * X 0) * hs
  · ring
  · ring
  · linear_combination (X 0 * X 0 + X 1 * X 1) * hs
theorem neg_sum_genDerivation_sq_X (i : Fin 2) :
    -(genDerivation 0 (genDerivation 0 (X i)) + genDerivation 1 (genDerivation 1 (X i)) +
        genDerivation 2 (genDerivation 2 (X i))) =
      3 * (halfConst * halfConst) * X i := by
  have hs := halfImag_mul_self
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, genDerivation_zero_X_zero,
      genDerivation_zero_X_one, genDerivation_one_X_zero, genDerivation_one_X_one,
      genDerivation_two_X_zero, genDerivation_two_X_one, derivation_halfImag_mul,
      derivation_halfConst_mul, map_neg]
  · linear_combination (-2 * X 0) * hs
  · linear_combination (-2 * X 1) * hs
theorem sum_genDerivation_mul_genDerivation_X (i : Fin 2) (p : MvPolynomial (Fin 2) ℂ) :
    genDerivation 0 p * genDerivation 0 (X i) + genDerivation 1 p * genDerivation 1 (X i) +
        genDerivation 2 p * genDerivation 2 (X i) =
      -(halfConst * halfConst) * (eulerDeriv p * X i) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [derivation_C]
  | add p q hp hq =>
    simp only [map_add]
    linear_combination hp + hq
  | mul_X p j hp =>
    have hX := sum_genDerivation_X_mul i j
    have hE : eulerDeriv (X j) = X j := mkDerivation_X ℂ _ j
    simp only [Derivation.leibniz, smul_eq_mul, hE]
    linear_combination X j * hp + p * hX
theorem neg_sum_genDerivation_sq_eq_euler (p : MvPolynomial (Fin 2) ℂ) :
    -(genDerivation 0 (genDerivation 0 p) + genDerivation 1 (genDerivation 1 p) +
        genDerivation 2 (genDerivation 2 p)) =
      halfConst * halfConst * (eulerDeriv (eulerDeriv p) + 2 * eulerDeriv p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [derivation_C]
  | add p q hp hq =>
    simp only [map_add]
    linear_combination hp + hq
  | mul_X p j hp =>
    have hB := sum_genDerivation_mul_genDerivation_X j p
    have hX := neg_sum_genDerivation_sq_X j
    have hE : eulerDeriv (X j) = X j := mkDerivation_X ℂ _ j
    rw [derivation_derivation_mul, derivation_derivation_mul, derivation_derivation_mul,
      derivation_derivation_mul]
    simp only [hE, Derivation.leibniz, smul_eq_mul]
    linear_combination X j * hp + p * hX - 2 * hB
theorem neg_sum_genDerivation_sq_of_isHomogeneous (l : HalfNatural) {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsHomogeneous l.doubled) :
    -(genDerivation 0 (genDerivation 0 P) + genDerivation 1 (genDerivation 1 P) +
        genDerivation 2 (genDerivation 2 P)) =
      ((l.toReal * (l.toReal + 1) : ℝ) : ℂ) • P := by
  rw [neg_sum_genDerivation_sq_eq_euler, eulerDeriv_of_isHomogeneous hP, map_nsmul,
    eulerDeriv_of_isHomogeneous hP, smul_eq_C_mul, halfConst]
  simp only [nsmul_eq_mul]
  have hn : ((l.doubled : ℕ) : MvPolynomial (Fin 2) ℂ) = C (l.doubled : ℂ) :=
    (map_natCast C _).symm
  have h2 : (2 : MvPolynomial (Fin 2) ℂ) = C 2 := (map_ofNat C 2).symm
  rw [hn, h2]
  simp only [← C_mul, ← mul_assoc, ← C_add, ← add_mul]
  congr 2
  simp only [HalfNatural.toReal]
  push_cast
  ring
end Table
theorem hasDerivAt_coeff_aeval_of_forms (f : ℝ → Fin 2 → MvPolynomial (Fin 2) ℂ)
    (Y : Fin 2 → MvPolynomial (Fin 2) ℂ)
    (hf : ∀ i m, HasDerivAt (fun t => coeff m (f t i)) (coeff m (Y i)) 0)
    (h0 : f 0 = X) (P : MvPolynomial (Fin 2) ℂ) :
    ∀ m, HasDerivAt (fun t => coeff m (aeval (f t) P)) (coeff m (mkDerivation ℂ Y P)) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro m
    simpa [derivation_C, algebraMap_eq] using
      hasDerivAt_const (0 : ℝ) (coeff m (C a : MvPolynomial (Fin 2) ℂ))
  | add p q hp hq =>
    intro m
    simp only [map_add, coeff_add]
    exact (hp m).add (hq m)
  | mul_X p i hp =>
    intro m
    simp only [map_mul, aeval_X, coeff_mul]
    have h := HasDerivAt.fun_sum (u := Finset.HasAntidiagonal.antidiagonal m)
      (fun d _ => (hp d.1).mul (hf i d.2))
    refine HasDerivAt.congr_deriv h ?_
    symm
    rw [Derivation.leibniz, mkDerivation_X, smul_eq_mul, smul_eq_mul, coeff_add, coeff_mul,
      mul_comm (X i), coeff_mul, ← Finset.sum_add_distrib]
    simp only [h0, aeval_X_left_apply]
    exact Finset.sum_congr rfl fun d _ => add_comm _ _
theorem oneParam_zero (ι : Fin 3) : (oneParam ι 0 : Matrices.ComplexMatrix2) = 1 := by
  simp [oneParam]
theorem columnForms_one (j : Fin 2) : columnForms (1 : Matrices.ComplexMatrix2) j = X j := by
  fin_cases j <;> simp [columnForms, Matrix.one_apply]
theorem hasDerivAt_oneParam_apply (hG : FieldCalculus.OneParameterSubgroups) (ι : Fin 3)
    (r s : Fin 2) :
    HasDerivAt (fun t : ℝ => (oneParam ι t : Matrices.ComplexMatrix2) r s) (lieGenerator ι r s) 0 := by
  have he : (fun t : ℝ => (oneParam ι t : Matrices.ComplexMatrix2) r s) = fun t : ℝ =>
      ((Real.cos (t / 2) : ℝ) : ℂ) * (1 : Matrices.ComplexMatrix2) r s +
        (Complex.I * ((Real.sin (t / 2) : ℝ) : ℂ)) * pauli ι r s := by
    funext t
    have h := (hG ι t 0).1
    change matExp ((t : ℂ) • lieGenerator ι) r s = _
    rw [h]
    simp
  have hc : HasDerivAt (fun t : ℝ => ((Real.cos (t / 2) : ℝ) : ℂ)) 0 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).div_const 2).cos
    have h' := h.ofReal_comp
    simpa using h'
  have hs : HasDerivAt (fun t : ℝ => ((Real.sin (t / 2) : ℝ) : ℂ)) (1 / 2) 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).div_const 2).sin
    have h' := h.ofReal_comp
    simpa using h'
  rw [he]
  have h := (hc.mul_const ((1 : Matrices.ComplexMatrix2) r s)).add
    ((hs.const_mul Complex.I).mul_const (pauli ι r s))
  refine HasDerivAt.congr_deriv h ?_
  simp only [lieGenerator, Matrix.smul_apply, smul_eq_mul]
  ring
theorem hasDerivAt_coeff_columnForms_oneParam (hG : FieldCalculus.OneParameterSubgroups)
    (ι : Fin 3) (j : Fin 2) (m : Fin 2 →₀ ℕ) :
    HasDerivAt (fun t : ℝ => coeff m (columnForms (oneParam ι t : Matrices.ComplexMatrix2) j))
      (coeff m (columnForms (lieGenerator ι) j)) 0 := by
  simp only [columnForms, coeff_add, coeff_C_mul]
  exact ((hasDerivAt_oneParam_apply hG ι 0 j).mul_const _).add
    ((hasDerivAt_oneParam_apply hG ι 1 j).mul_const _)
theorem hasDerivAt_coeff_spinRep_oneParam (hG : FieldCalculus.OneParameterSubgroups) (ι : Fin 3)
    (l : HalfNatural) (P : homogeneousSpace l) (m : Fin 2 →₀ ℕ) :
    HasDerivAt
      (fun t : ℝ => coeff m (spinRep l (oneParam ι t) P : MvPolynomial (Fin 2) ℂ))
      (coeff m (genDerivation ι P)) 0 :=
  hasDerivAt_coeff_aeval_of_forms (fun t => columnForms (oneParam ι t : Matrices.ComplexMatrix2))
    (columnForms (lieGenerator ι)) (hasDerivAt_coeff_columnForms_oneParam hG ι)
    (by
      funext j
      simp only [oneParam_zero, columnForms_one]) P m
theorem genDerivation_mem_homogeneousSpace (hG : FieldCalculus.OneParameterSubgroups) (ι : Fin 3)
    (l : HalfNatural) (P : homogeneousSpace l) : genDerivation ι P ∈ homogeneousSpace l := by
  rw [mem_homogeneousSubmodule]
  intro d hd
  by_contra hne
  apply hd
  have hz : (fun t : ℝ =>
      coeff d (spinRep l (oneParam ι t) P : MvPolynomial (Fin 2) ℂ)) =
      fun _ => 0 := by
    funext t
    have hQ := (mem_homogeneousSubmodule _ _).mp (spinRep l (oneParam ι t) P).2
    by_contra h
    exact hne (hQ h)
  have h := hasDerivAt_coeff_spinRep_oneParam hG ι l P d
  rw [hz] at h
  exact h.unique (hasDerivAt_const _ _)
def genOnSpace (hG : FieldCalculus.OneParameterSubgroups) (ι : Fin 3) (l : HalfNatural)
    (P : homogeneousSpace l) : homogeneousSpace l :=
  ⟨genDerivation ι P, genDerivation_mem_homogeneousSpace hG ι l P⟩
def coeffPairing (l : HalfNatural) (a : Fin (l.doubled + 1)) (g : specialUnitary) :
    homogeneousSpace l →ₗ[ℂ] ℂ :=
  (∑ b, star (monomialCoord l b (monomialBasis l a)) • monomialCoord l b) ∘ₗ spinRep l g
theorem coeffPairing_apply (l : HalfNatural) (a : Fin (l.doubled + 1)) (g : specialUnitary)
    (P : homogeneousSpace l) :
    coeffPairing l a g P = homogeneousInner l (monomialBasis l a) (spinRep l g P) := by
  simp [coeffPairing, homogeneousInner]
theorem coeffPairing_monomialBasis (l : HalfNatural) (a c : Fin (l.doubled + 1))
    (g : specialUnitary) : coeffPairing l a g (monomialBasis l c) = spinCoeff l a c g :=
  coeffPairing_apply l a g _
theorem linearMap_eq_sum_monomialCoord (l : HalfNatural) (L : homogeneousSpace l →ₗ[ℂ] ℂ)
    (Q : homogeneousSpace l) :
    L Q = ∑ d, monomialCoord l d Q * L (monomialBasis l d) := by
  conv_lhs => rw [← sum_monomialCoord_smul_monomialBasis l Q]
  simp [map_sum]
theorem coeffPairing_mul (hR : SpinRepsUnitaryIrreducible.Statement) (l : HalfNatural)
    (a : Fin (l.doubled + 1)) (g h : specialUnitary) (P : homogeneousSpace l) :
    coeffPairing l a (g * h) P = coeffPairing l a g (spinRep l h P) := by
  rw [coeffPairing_apply, coeffPairing_apply, (hR l l).spinRep_mul]
  rfl
theorem hasDerivAt_monomialCoord_spinRep (hG : FieldCalculus.OneParameterSubgroups) (ι : Fin 3)
    (l : HalfNatural) (d : Fin (l.doubled + 1)) (P : homogeneousSpace l) :
    HasDerivAt (fun t : ℝ => monomialCoord l d (spinRep l (oneParam ι t) P))
      (monomialCoord l d (genOnSpace hG ι l P)) 0 :=
  (hasDerivAt_coeff_spinRep_oneParam hG ι l P (monomialExponent l d)).const_mul
    ((monomialNorm l d : ℝ) : ℂ)
theorem hasDerivAt_coeffPairing (hG : FieldCalculus.OneParameterSubgroups)
    (hR : SpinRepsUnitaryIrreducible.Statement) (ι : Fin 3) (l : HalfNatural)
    (a : Fin (l.doubled + 1)) (g : specialUnitary) (P : homogeneousSpace l) :
    HasDerivAt (fun t : ℝ => coeffPairing l a (g * oneParam ι t) P)
      (coeffPairing l a g (genOnSpace hG ι l P)) 0 := by
  have he : (fun t : ℝ => coeffPairing l a (g * oneParam ι t) P) = fun t : ℝ =>
      ∑ d, monomialCoord l d (spinRep l (oneParam ι t) P) *
        coeffPairing l a g (monomialBasis l d) := by
    funext t
    rw [coeffPairing_mul hR, linearMap_eq_sum_monomialCoord]
  rw [he, linearMap_eq_sum_monomialCoord l (coeffPairing l a g) (genOnSpace hG ι l P)]
  exact HasDerivAt.fun_sum fun d _ => (hasDerivAt_monomialCoord_spinRep hG ι l d P).mul_const _
def coeffPairingSum (l : HalfNatural) (P : Fin (l.doubled + 1) → homogeneousSpace l)
    (g : specialUnitary) : ℂ :=
  ∑ a, coeffPairing l a g (P a)
theorem exists_coeffPairingSum (l : HalfNatural) {ψ : C(specialUnitary, ℂ)}
    (hψ : ψ ∈ coeffSpan l) :
    ∃ P : Fin (l.doubled + 1) → homogeneousSpace l, ∀ g, ψ g = coeffPairingSum l P g := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨⟨a, c⟩, rfl⟩
    refine ⟨Pi.single a (monomialBasis l c), fun g => ?_⟩
    rw [coeffPairingSum, Finset.sum_eq_single a]
    · rw [Pi.single_eq_same, coeffPairing_monomialBasis]
      rfl
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · simp
  · exact ⟨0, fun g => by simp [coeffPairingSum]⟩
  · rintro ψ₁ ψ₂ - - ⟨P₁, h₁⟩ ⟨P₂, h₂⟩
    refine ⟨P₁ + P₂, fun g => ?_⟩
    simp [coeffPairingSum, h₁, h₂, Finset.sum_add_distrib]
  · rintro c ψ₁ - ⟨P₁, h₁⟩
    refine ⟨c • P₁, fun g => ?_⟩
    simp [coeffPairingSum, h₁, Finset.mul_sum]
theorem isInCoeffSpan_coeffPairingSum (l : HalfNatural)
    (P : Fin (l.doubled + 1) → homogeneousSpace l) :
    IsInCoeffSpan l (coeffPairingSum l P) := by
  refine ⟨∑ a, ∑ d, monomialCoord l d (P a) • spinCoeffMap l a d,
    Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun d _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, d), rfl⟩), fun g => ?_⟩
  simp only [coeffPairingSum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [linearMap_eq_sum_monomialCoord l (coeffPairing l a g) (P a)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeffPairing_monomialBasis]
  rfl
theorem hasDerivAt_coeffPairingSum (hG : FieldCalculus.OneParameterSubgroups)
    (hR : SpinRepsUnitaryIrreducible.Statement) (ι : Fin 3) (l : HalfNatural)
    (P : Fin (l.doubled + 1) → homogeneousSpace l) (g : specialUnitary) :
    HasDerivAt (fun t : ℝ => coeffPairingSum l P (g * oneParam ι t))
      (coeffPairingSum l (fun a => genOnSpace hG ι l (P a)) g) 0 :=
  HasDerivAt.fun_sum fun a _ => hasDerivAt_coeffPairing hG hR ι l a g (P a)
theorem rightFieldOne_coeffPairingSum (hG : FieldCalculus.OneParameterSubgroups)
    (hR : SpinRepsUnitaryIrreducible.Statement) (ι : Fin 3) (l : HalfNatural)
    (P : Fin (l.doubled + 1) → homogeneousSpace l) :
    rightFieldOne ι (coeffPairingSum l P) =
      coeffPairingSum l (fun a => genOnSpace hG ι l (P a)) :=
  funext fun g => (hasDerivAt_coeffPairingSum hG hR ι l P g).deriv
theorem casimirOp_coeffPairingSum (hG : FieldCalculus.OneParameterSubgroups)
    (hR : SpinRepsUnitaryIrreducible.Statement) (l : HalfNatural)
    (P : Fin (l.doubled + 1) → homogeneousSpace l) (g : specialUnitary) :
    casimirOp (coeffPairingSum l P) g =
      ((l.toReal * (l.toReal + 1) : ℝ) : ℂ) * coeffPairingSum l P g := by
  simp only [casimirOp, rightFieldOne_coeffPairingSum hG hR, Fin.sum_univ_three]
  simp only [coeffPairingSum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hQ : -(genOnSpace hG 0 l (genOnSpace hG 0 l (P a)) +
      genOnSpace hG 1 l (genOnSpace hG 1 l (P a)) +
      genOnSpace hG 2 l (genOnSpace hG 2 l (P a))) =
      ((l.toReal * (l.toReal + 1) : ℝ) : ℂ) • P a :=
    Subtype.ext
      (neg_sum_genDerivation_sq_of_isHomogeneous l ((mem_homogeneousSubmodule _ _).mp (P a).2))
  rw [← smul_eq_mul, ← map_smul, ← hQ]
  simp only [map_neg, map_add]
theorem integral_haarPi_unit (G : specialUnitary → ℂ) :
    ∫ u, G (u ()) ∂haarPi Unit = ∫ g, G g ∂haarProb := by
  rw [haarPi, Measure.infinitePi_eq_pi]
  exact (measurePreserving_funUnique haarProb Unit).integral_comp' G
theorem rightField_asSingletonFamily (ι : Fin 3) (F : specialUnitary → ℂ)
    (u : Unit → specialUnitary) :
    rightField () ι (asSingletonFamily F) u = rightFieldOne ι F (u ()) :=
  rightField_of_unique () ι F u
theorem integral_rightFieldOne_mul_eq (hC : FieldCalculus.AllRules) (ι : Fin 3)
    (F H : specialUnitary → ℂ) (hF : IsC1 F) (hH : IsC1 H) :
    ∫ g, rightFieldOne ι F g * H g ∂haarProb = -∫ g, F g * rightFieldOne ι H g ∂haarProb := by
  have h := ((hC.2.2 Unit).2.2.2.2.2.2.1 () ι (asSingletonFamily F) (asSingletonFamily H)
    hF hH).1
  simp only [rightField_asSingletonFamily] at h
  rw [← integral_haarPi_unit (fun g => rightFieldOne ι F g * H g),
    ← integral_haarPi_unit (fun g => F g * rightFieldOne ι H g)]
  exact h
theorem rightFieldFacts_of (hC : FieldCalculus.AllRules)
    (hR : SpinRepsUnitaryIrreducible.Statement) (l : HalfNatural) : RightFieldFacts l where
  integral_rightFieldOne_mul := integral_rightFieldOne_mul_eq hC
  hasDirDerivAt := by
    intro ι ψ hψ u
    obtain ⟨P, hP⟩ := exists_coeffPairingSum l hψ
    have hf : (fun t : ℝ => asSingletonFamily ψ (shiftAt u () ι t)) =
        fun t : ℝ => coeffPairingSum l P (u () * oneParam ι t) := by
      funext t
      simp [asSingletonFamily, shiftAt, hP]
    unfold HasDirDerivAt
    rw [hf]
    exact (hasDerivAt_coeffPairingSum hC.1 hR ι l P (u ())).differentiableAt
  rightFieldOne_mem := by
    intro ι ψ hψ
    obtain ⟨P, hP⟩ := exists_coeffPairingSum l hψ
    rw [show (ψ : specialUnitary → ℂ) = coeffPairingSum l P from funext hP,
      rightFieldOne_coeffPairingSum hC.1 hR]
    exact isInCoeffSpan_coeffPairingSum l _
  casimirOp_eq := by
    intro ψ hψ g
    obtain ⟨P, hP⟩ := exists_coeffPairingSum l hψ
    rw [show (ψ : specialUnitary → ℂ) = coeffPairingSum l P from funext hP]
    exact casimirOp_coeffPairingSum hC.1 hR l P g
theorem allRightFieldFacts (hC : FieldCalculus.AllRules)
    (hR : SpinRepsUnitaryIrreducible.Statement) : AllRightFieldFacts :=
  fun l => rightFieldFacts_of hC hR l
end SpinHarmonics.RightFieldProof
end YangMills.Construction
