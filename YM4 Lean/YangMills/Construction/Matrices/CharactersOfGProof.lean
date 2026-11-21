import YangMills.Construction.Matrices.CharactersOfG
import YangMills.Construction.Matrices.RepresentationsOfGAreUnitaryAndIrreducible
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2 MvPolynomial
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.SpinHarmonics
namespace SpinCharacters
theorem spinCoeff_eq_monomialCoord (l : HalfNatural) (a c : Fin (l.doubled + 1))
    (g : specialUnitary) :
    spinCoeff l a c g = monomialCoord l a (spinRep l g (monomialBasis l c)) := by
  simp only [spinCoeff, homogeneousInner, monomialCoord_monomialBasis]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
theorem spinRep_monomialBasis (l : HalfNatural) (c : Fin (l.doubled + 1)) (g : specialUnitary) :
    spinRep l g (monomialBasis l c) = ∑ a, spinCoeff l a c g • monomialBasis l a := by
  simp only [spinCoeff_eq_monomialCoord]
  exact (sum_monomialCoord_smul_monomialBasis l _).symm
def coeffMatrix (l : HalfNatural) (g : specialUnitary) :
    Matrix (Fin (l.doubled + 1)) (Fin (l.doubled + 1)) ℂ :=
  Matrix.of fun a c => spinCoeff l a c g
theorem coeffMatrix_mul (H : SpinRepsUnitaryIrreducible.Statement) (l : HalfNatural)
    (g h : specialUnitary) : coeffMatrix l (g * h) = coeffMatrix l g * coeffMatrix l h := by
  ext a c
  simp only [coeffMatrix, Matrix.of_apply, Matrix.mul_apply]
  rw [spinCoeff_eq_monomialCoord, (H l l).spinRep_mul, LinearMap.comp_apply,
    spinRep_monomialBasis l c h, map_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, map_smul, ← spinCoeff_eq_monomialCoord, smul_eq_mul, mul_comm]
theorem coeffMatrix_one (H : SpinRepsUnitaryIrreducible.Statement) (l : HalfNatural) :
    coeffMatrix l 1 = 1 := by
  ext a c
  simp only [coeffMatrix, Matrix.of_apply, spinCoeff, (H l l).spinRep_one,
    LinearMap.id_apply, homogeneousInner_monomialBasis, Matrix.one_apply]
theorem spinCharacter_eq_sum (l : HalfNatural) (g : specialUnitary) :
    spinCharacter l g = ∑ a, spinCoeff l a a g := by
  simp [spinCharacter, spinCoeffMap]
theorem spinCharacter_eq_trace (l : HalfNatural) (g : specialUnitary) :
    spinCharacter l g = (coeffMatrix l g).trace := by
  simp [spinCharacter_eq_sum, Matrix.trace, coeffMatrix]
theorem isConjInvariant_spinCharacter (H : SpinRepsUnitaryIrreducible.Statement)
    (l : HalfNatural) : IsConjInvariant (spinCharacter l) := by
  intro g h
  rw [spinCharacter_eq_trace, spinCharacter_eq_trace, coeffMatrix_mul H, coeffMatrix_mul H,
    Matrix.trace_mul_comm, ← mul_assoc, ← coeffMatrix_mul H, ← coeffMatrix_mul H,
    inv_mul_cancel, one_mul]
theorem spinRep_diagPhase_monomialBasis (l : HalfNatural) (φ : ℝ) (c : Fin (l.doubled + 1)) :
    spinRep l (diagPhase φ) (monomialBasis l c) =
      (Complex.exp (Complex.I * φ) ^ (c : ℕ) *
        Complex.exp (-(Complex.I * φ)) ^ (l.doubled - (c : ℕ))) • monomialBasis l c := by
  apply Subtype.ext
  have h0 : columnForms (diagPhase φ : ComplexMatrix2) 0 = C (Complex.exp (Complex.I * φ)) * X 0 := by
    simp [columnForms, diagPhase, diagPhaseMatrix]
  have h1 : columnForms (diagPhase φ : ComplexMatrix2) 1 =
      C (Complex.exp (-(Complex.I * φ))) * X 1 := by
    simp [columnForms, diagPhase, diagPhaseMatrix]
  change aeval (columnForms (diagPhase φ : ComplexMatrix2)) (normalizedMonomial l c) =
    (Complex.exp (Complex.I * φ) ^ (c : ℕ) *
        Complex.exp (-(Complex.I * φ)) ^ (l.doubled - (c : ℕ))) • normalizedMonomial l c
  rw [MvPolynomial.smul_eq_C_mul]
  simp only [normalizedMonomial, map_mul, map_pow, aeval_C, aeval_X, h0, h1, algebraMap_eq]
  ring
def weightSum (n : ℕ) (φ : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1),
    Complex.exp (Complex.I * φ) ^ i * Complex.exp (-(Complex.I * φ)) ^ (n - i)
theorem spinCharacter_diagPhase (l : HalfNatural) (φ : ℝ) :
    spinCharacter l (diagPhase φ) = weightSum l.doubled φ := by
  rw [spinCharacter_eq_sum, weightSum, ← Fin.sum_univ_eq_sum_range (fun i =>
    Complex.exp (Complex.I * φ) ^ i * Complex.exp (-(Complex.I * φ)) ^ (l.doubled - i))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [spinCoeff_eq_monomialCoord, spinRep_diagPhase_monomialBasis, map_smul,
    monomialCoord_monomialBasis]
  simp
theorem conj_cexp_I_mul (φ : ℝ) :
    conj (Complex.exp (Complex.I * φ)) = Complex.exp (-(Complex.I * φ)) := by
  rw [← Complex.exp_conj]
  simp
theorem conj_cexp_neg_I_mul (φ : ℝ) :
    conj (Complex.exp (-(Complex.I * φ))) = Complex.exp (Complex.I * φ) := by
  rw [← conj_cexp_I_mul, Complex.conj_conj]
theorem conj_weightSum (n : ℕ) (φ : ℝ) : conj (weightSum n φ) = weightSum n φ := by
  have h := geom_sum₂_comm (Complex.exp (-(Complex.I * φ))) (Complex.exp (Complex.I * φ)) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  simp only [weightSum, map_sum, map_mul, map_pow, conj_cexp_I_mul, conj_cexp_neg_I_mul]
  exact h
theorem norm_cexp_neg_I_mul (φ : ℝ) : ‖Complex.exp (-(Complex.I * φ))‖ = 1 := by
  have h : -(Complex.I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I (-φ)
theorem norm_weightSum_le (n : ℕ) (φ : ℝ) : ‖weightSum n φ‖ ≤ n + 1 := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_cexp_neg_I_mul]
theorem cexp_I_sub_cexp_neg_I (θ : ℝ) :
    Complex.exp (Complex.I * θ) - Complex.exp (-(Complex.I * θ)) =
      2 * Complex.I * (Real.sin θ : ℂ) := by
  have h₁ : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := mul_comm _ _
  have h₂ : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h₂, h₁, Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]
  ring
theorem weightSum_mul_sin (n : ℕ) (φ : ℝ) :
    weightSum n φ * (Real.sin φ : ℂ) = (Real.sin (((n : ℝ) + 1) * φ) : ℂ) := by
  have hg := geom_sum₂_mul (Complex.exp (Complex.I * φ)) (Complex.exp (-(Complex.I * φ))) (n + 1)
  simp only [Nat.add_sub_cancel] at hg
  have hx : Complex.exp (Complex.I * φ) ^ (n + 1) =
      Complex.exp (Complex.I * ((((n : ℝ) + 1) * φ : ℝ) : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hy : Complex.exp (-(Complex.I * φ)) ^ (n + 1) =
      Complex.exp (-(Complex.I * ((((n : ℝ) + 1) * φ : ℝ) : ℂ))) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [cexp_I_sub_cexp_neg_I, hx, hy, cexp_I_sub_cexp_neg_I] at hg
  have h2 : (2 * Complex.I : ℂ) ≠ 0 := by simp
  apply mul_left_cancel₀ h2
  change (2 * Complex.I) * ((∑ i ∈ Finset.range (n + 1), _) * _) = _
  linear_combination hg
theorem two_mul_toReal_add_one (l : HalfNatural) : 2 * l.toReal + 1 = (l.doubled : ℝ) + 1 := by
  simp only [HalfNatural.toReal]
  ring
def idxZero : Fin (HalfNatural.oneHalf.doubled + 1) := ⟨0, Nat.succ_pos _⟩
def idxOne : Fin (HalfNatural.oneHalf.doubled + 1) := ⟨1, Nat.lt_succ_self _⟩
theorem monomialBasis_oneHalf_zero :
    monomialBasis HalfNatural.oneHalf idxZero = linearMonomial 1 := by
  apply Subtype.ext
  simp [monomialBasis, normalizedMonomial, linearMonomial, monomialNorm, HalfNatural.oneHalf,
    idxZero]
theorem monomialBasis_oneHalf_one :
    monomialBasis HalfNatural.oneHalf idxOne = linearMonomial 0 := by
  apply Subtype.ext
  simp [monomialBasis, normalizedMonomial, linearMonomial, monomialNorm, HalfNatural.oneHalf,
    idxOne]
theorem spinCharacter_oneHalf (H : SpinRepsUnitaryIrreducible.Statement) (g : specialUnitary) :
    spinCharacter HalfNatural.oneHalf g = fullTrace (g : ComplexMatrix2) := by
  have hsum : spinCharacter HalfNatural.oneHalf g =
      spinCoeff HalfNatural.oneHalf idxZero idxZero g +
        spinCoeff HalfNatural.oneHalf idxOne idxOne g := by
    rw [spinCharacter_eq_sum]
    exact Fin.sum_univ_two (fun a : Fin 2 => spinCoeff HalfNatural.oneHalf a a g)
  have hne : idxZero ≠ idxOne := by
    intro h
    have h' := congrArg Fin.val h
    simp [idxZero, idxOne] at h'
  have c00 : monomialCoord HalfNatural.oneHalf idxZero (linearMonomial 1) = 1 := by
    rw [← monomialBasis_oneHalf_zero, monomialCoord_monomialBasis]
    simp
  have c01 : monomialCoord HalfNatural.oneHalf idxZero (linearMonomial 0) = 0 := by
    rw [← monomialBasis_oneHalf_one, monomialCoord_monomialBasis]
    simp [hne]
  have c10 : monomialCoord HalfNatural.oneHalf idxOne (linearMonomial 1) = 0 := by
    rw [← monomialBasis_oneHalf_zero, monomialCoord_monomialBasis]
    simp [hne.symm]
  have c11 : monomialCoord HalfNatural.oneHalf idxOne (linearMonomial 0) = 1 := by
    rw [← monomialBasis_oneHalf_one, monomialCoord_monomialBasis]
    simp
  have hhalf := (H HalfNatural.oneHalf HalfNatural.oneHalf).spinRep_oneHalf g
  rw [hsum, spinCoeff_eq_monomialCoord, spinCoeff_eq_monomialCoord, monomialBasis_oneHalf_zero,
    monomialBasis_oneHalf_one, hhalf, hhalf]
  simp only [Fin.sum_univ_two, map_add, map_smul, c00, c01, c10, c11, fullTrace,
    Matrix.trace_fin_two]
  simp
  ring
theorem specialUnitary_entries (g : specialUnitary) :
    (g : ComplexMatrix2) 1 1 = conj ((g : ComplexMatrix2) 0 0) ∧
      (g : ComplexMatrix2) 0 1 = -conj ((g : ComplexMatrix2) 1 0) ∧
      conj ((g : ComplexMatrix2) 0 0) * (g : ComplexMatrix2) 0 0 +
        conj ((g : ComplexMatrix2) 1 0) * (g : ComplexMatrix2) 1 0 = 1 := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp g.2
  have hs : star (g : ComplexMatrix2) * (g : ComplexMatrix2) = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hadj : star (g : ComplexMatrix2) = (g : ComplexMatrix2).adjugate := by
    have hm : (g : ComplexMatrix2) * (g : ComplexMatrix2).adjugate = 1 := by
      rw [Matrix.mul_adjugate, hd, one_smul]
    calc star (g : ComplexMatrix2)
        = star (g : ComplexMatrix2) * ((g : ComplexMatrix2) * (g : ComplexMatrix2).adjugate) := by
          rw [hm, mul_one]
      _ = (g : ComplexMatrix2).adjugate := by rw [← mul_assoc, hs, one_mul]
  rw [Matrix.adjugate_fin_two] at hadj
  have e00 := congrFun (congrFun hadj 0) 0
  have e10 := congrFun (congrFun hadj 1) 0
  have e := congrFun (congrFun hs 0) 0
  simp [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10 e
  refine ⟨e00.symm, ?_, e⟩
  have h := congrArg conj e10
  simpa using h
theorem of_columns_mem_specialUnitary (a b : ℂ) (hab : a * conj a + b * conj b = 1) :
    (!![a, -conj b; b, conj a] : ComplexMatrix2) ∈ specialUnitary := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
    · linear_combination hab
    · ring
    · ring
    · linear_combination hab
  · simp [Matrix.det_fin_two]
    linear_combination hab
theorem exists_conj_diagPhase_of_eigenvector (g : specialUnitary) (a b : ℂ) (θ : ℝ)
    (hab : a * conj a + b * conj b = 1)
    (e₁ : (g : ComplexMatrix2) 0 0 * a + (g : ComplexMatrix2) 0 1 * b =
      Complex.exp (Complex.I * θ) * a)
    (e₂ : (g : ComplexMatrix2) 1 0 * a + (g : ComplexMatrix2) 1 1 * b =
      Complex.exp (Complex.I * θ) * b) :
    ∃ h : specialUnitary, g = h * diagPhase θ * h⁻¹ := by
  obtain ⟨h11, h01, -⟩ := specialUnitary_entries g
  refine ⟨⟨_, of_columns_mem_specialUnitary a b hab⟩, eq_mul_inv_of_mul_eq ?_⟩
  have c₁ := congrArg conj e₁
  have c₂ := congrArg conj e₂
  rw [h01] at e₁ c₁
  rw [h11] at e₂ c₂
  simp only [map_add, map_mul, map_neg, Complex.conj_conj, conj_cexp_I_mul] at c₁ c₂
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagPhase, diagPhaseMatrix, h01, h11]
  · linear_combination e₁
  · linear_combination -c₂
  · linear_combination e₂
  · linear_combination c₁
theorem exists_conj_diagPhase (g : specialUnitary) :
    ∃ h : specialUnitary, ∃ φ ∈ Set.Icc 0 Real.pi, g = h * diagPhase φ * h⁻¹ := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : ComplexMatrix2))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hev := hv.apply_eq_smul
  rw [Matrix.toLin'_apply] at hev
  have f₁ := congrFun hev 0
  have f₂ := congrFun hev 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at f₁ f₂
  have hv0 : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    simp only [ne_eq, not_or, not_not] at hc
    apply hv.2
    funext i
    fin_cases i
    · exact hc.1
    · exact hc.2
  set T : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1) with hT
  have hTpos : 0 < T := by
    rcases hv0 with h | h
    · have := Complex.normSq_pos.mpr h
      have := Complex.normSq_nonneg (v 1)
      linarith
    · have := Complex.normSq_pos.mpr h
      have := Complex.normSq_nonneg (v 0)
      linarith
  set c : ℝ := (Real.sqrt T)⁻¹ with hc
  have hcT : c * c * T = 1 := by
    have hs : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
    have hne : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hTpos).ne'
    rw [hc]
    field_simp
    nlinarith
  set a : ℂ := (c : ℂ) * v 0 with ha
  set b : ℂ := (c : ℂ) * v 1 with hb
  have hab : a * conj a + b * conj b = 1 := by
    have h₁ : v 0 * conj (v 0) = (Complex.normSq (v 0) : ℂ) := Complex.mul_conj _
    have h₂ : v 1 * conj (v 1) = (Complex.normSq (v 1) : ℂ) := Complex.mul_conj _
    have h₃ : (c : ℂ) * c * (T : ℂ) = 1 := by exact_mod_cast hcT
    simp only [ha, hb, map_mul, Complex.conj_ofReal]
    rw [hT] at h₃
    push_cast at h₃
    linear_combination h₃ + (c : ℂ) * c * h₁ + (c : ℂ) * c * h₂
  obtain ⟨h11, h01, hpr⟩ := specialUnitary_entries g
  have e₁ : (g : ComplexMatrix2) 0 0 * a + (g : ComplexMatrix2) 0 1 * b = μ * a := by
    simp only [ha, hb]
    linear_combination (c : ℂ) * f₁
  have e₂ : (g : ComplexMatrix2) 1 0 * a + (g : ComplexMatrix2) 1 1 * b = μ * b := by
    simp only [ha, hb]
    linear_combination (c : ℂ) * f₂
  have c₁ := congrArg conj e₁
  have c₂ := congrArg conj e₂
  rw [h01] at e₁ c₁
  rw [h11] at e₂ c₂
  simp only [map_add, map_mul, map_neg, Complex.conj_conj] at c₁ c₂
  have hμμ : μ * conj μ = 1 := by
    linear_combination (1 - μ * conj μ) * hab - (conj μ * conj a) * e₁
      - ((g : ComplexMatrix2) 0 0 * a - conj ((g : ComplexMatrix2) 1 0) * b) * c₁
      - (conj μ * conj b) * e₂
      - ((g : ComplexMatrix2) 1 0 * a + conj ((g : ComplexMatrix2) 0 0) * b) * c₂
      + (a * conj a + b * conj b) * hpr
  have hnorm : ‖μ‖ = 1 := by
    have h₁ : ((Complex.normSq μ : ℝ) : ℂ) = 1 := by rw [← Complex.mul_conj]; exact hμμ
    have h₂ : Complex.normSq μ = 1 := by exact_mod_cast h₁
    rw [Complex.normSq_eq_norm_sq] at h₂
    nlinarith [norm_nonneg μ]
  set θ : ℝ := Complex.arg μ with hθ
  have hμexp : Complex.exp (Complex.I * θ) = μ := by
    have := Complex.norm_mul_exp_arg_mul_I μ
    rw [hnorm] at this
    simpa [mul_comm, hθ] using this
  have hconj : Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) = conj μ := by
    rw [← hμexp, conj_cexp_I_mul]
    congr 1
    push_cast
    ring
  by_cases hpos : 0 ≤ θ
  · obtain ⟨h, hh⟩ := exists_conj_diagPhase_of_eigenvector g a b θ hab
      (by rw [hμexp, h01]; exact e₁) (by rw [hμexp, h11]; exact e₂)
    exact ⟨h, θ, ⟨hpos, Complex.arg_le_pi μ⟩, hh⟩
  · have hneg : θ < 0 := not_le.mp hpos
    have hge : -Real.pi < θ := Complex.neg_pi_lt_arg μ
    obtain ⟨h, hh⟩ := exists_conj_diagPhase_of_eigenvector g (-conj b) (conj a) (-θ)
      (by simp only [map_neg, Complex.conj_conj]; linear_combination hab)
      (by rw [hconj, h01]; linear_combination -c₂)
      (by rw [hconj, h11]; linear_combination c₁)
    exact ⟨h, -θ, ⟨by linarith, by linarith⟩, hh⟩
theorem hasEigenvalue_conj {T A B : ComplexMatrix2} (hBA : B * A = 1) {μ : ℂ}
    (hT : Module.End.HasEigenvalue (Matrix.toLin' T) μ) :
    Module.End.HasEigenvalue (Matrix.toLin' (A * T * B)) μ := by
  obtain ⟨v, hv⟩ := hT.exists_hasEigenvector
  have hev := hv.apply_eq_smul
  rw [Matrix.toLin'_apply] at hev
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := A *ᵥ v) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_mulVec, mul_assoc,
      mul_assoc, hBA, mul_one, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul]
  · intro h0
    apply hv.2
    have h : B *ᵥ (A *ᵥ v) = B *ᵥ 0 := by rw [h0]
    rwa [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec, Matrix.mulVec_zero] at h
theorem hasEigenvalue_diagPhaseMatrix (φ : ℝ) (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' (diagPhaseMatrix φ)) μ ↔
      μ = Complex.exp (Complex.I * φ) ∨ μ = Complex.exp (-(Complex.I * φ)) := by
  constructor
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hev := hv.apply_eq_smul
    rw [Matrix.toLin'_apply] at hev
    have f₀ := congrFun hev 0
    have f₁ := congrFun hev 1
    simp [diagPhaseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at f₀ f₁
    by_cases h0 : v 0 = 0
    · right
      have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv.2
        funext i
        fin_cases i
        · exact h0
        · exact h1
      exact (f₁.resolve_right h1).symm
    · left
      exact (f₀.resolve_right h0).symm
  · rintro (rfl | rfl)
    · refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, 0]) ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        ext i
        fin_cases i <;> simp [diagPhaseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · intro h
        simpa using congrFun h 0
    · refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![0, 1]) ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        ext i
        fin_cases i <;> simp [diagPhaseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · intro h
        simpa using congrFun h 1
end SpinCharacters
theorem allCharacterFacts_holds (H : SpinRepsUnitaryIrreducible.Statement) :
    AllCharacterFacts := by
  intro l
  have hclass := SpinCharacters.isConjInvariant_spinCharacter H l
  have hvalue := SpinCharacters.two_mul_toReal_add_one l
  have hconjugate : ∀ (g h : specialUnitary) (φ : ℝ), g = h * diagPhase φ * h⁻¹ →
      spinCharacter l g = SpinCharacters.weightSum l.doubled φ := by
    intro g h φ hg
    rw [hg, hclass, SpinCharacters.spinCharacter_diagPhase]
  have hreal : ∀ g, conj (spinCharacter l g) = spinCharacter l g := by
    intro g
    obtain ⟨h, φ, -, hg⟩ := SpinCharacters.exists_conj_diagPhase g
    rw [hconjugate g h φ hg, SpinCharacters.conj_weightSum]
  refine ⟨fun g => Complex.conj_eq_iff_im.mp (hreal g), hclass, ?_, ?_, ?_,
    SpinCharacters.spinCharacter_oneHalf H, SpinCharacters.exists_conj_diagPhase, ?_⟩
  · intro g
    have h : spinCharacter l g⁻¹ = conj (spinCharacter l g) := by
      simp only [SpinCharacters.spinCharacter_eq_sum, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (H l l).spinCoeff_inv g a a
    rw [h, hreal]
  · rw [SpinCharacters.spinCharacter_eq_trace, SpinCharacters.coeffMatrix_one H, Matrix.trace_one,
      hvalue]
    simp
  · intro g
    obtain ⟨h, φ, -, hg⟩ := SpinCharacters.exists_conj_diagPhase g
    rw [hconjugate g h φ hg, hvalue]
    exact SpinCharacters.norm_weightSum_le l.doubled φ
  · intro g h φ _ hg
    refine ⟨?_, ?_, ?_⟩
    · intro μ
      have hHK : ((h⁻¹ : specialUnitary) : ComplexMatrix2) * (h : ComplexMatrix2) = 1 := by
        rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
      have hKH : (h : ComplexMatrix2) * ((h⁻¹ : specialUnitary) : ComplexMatrix2) = 1 := by
        rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
      have hgm : (g : ComplexMatrix2) =
          (h : ComplexMatrix2) * diagPhaseMatrix φ * ((h⁻¹ : specialUnitary) : ComplexMatrix2) := by
        rw [hg]
        rfl
      rw [← SpinCharacters.hasEigenvalue_diagPhaseMatrix]
      constructor
      · intro hμ
        have h₁ := SpinCharacters.hasEigenvalue_conj (T := (g : ComplexMatrix2)) hKH hμ
        have h₂ : ((h⁻¹ : specialUnitary) : ComplexMatrix2) * (g : ComplexMatrix2) *
            (h : ComplexMatrix2) = diagPhaseMatrix φ := by
          rw [hgm]
          calc _ = (((h⁻¹ : specialUnitary) : ComplexMatrix2) * (h : ComplexMatrix2)) *
                diagPhaseMatrix φ *
                (((h⁻¹ : specialUnitary) : ComplexMatrix2) * (h : ComplexMatrix2)) := by
                  simp only [mul_assoc]
            _ = diagPhaseMatrix φ := by rw [hHK, one_mul, mul_one]
        rwa [h₂] at h₁
      · intro hμ
        rw [hgm]
        exact SpinCharacters.hasEigenvalue_conj hHK hμ
    · have hHK : ((h⁻¹ : specialUnitary) : ComplexMatrix2) * (h : ComplexMatrix2) = 1 := by
        rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
      have hgm : (g : ComplexMatrix2) =
          (h : ComplexMatrix2) * diagPhaseMatrix φ * ((h⁻¹ : specialUnitary) : ComplexMatrix2) := by
        rw [hg]
        rfl
      have hc : Complex.exp (Complex.I * φ) + Complex.exp (-(Complex.I * φ)) =
          2 * (Real.cos φ : ℂ) := by
        rw [Complex.ofReal_cos, Complex.cos, mul_comm Complex.I, neg_mul, add_comm]
        ring_nf
      rw [hgm, halfTrace, fullTrace, Matrix.trace_mul_comm, ← mul_assoc, hHK, one_mul,
        Matrix.trace_fin_two]
      simp only [diagPhaseMatrix]
      simp
      simp only [Complex.ofReal_cos] at hc
      linear_combination (1 / 2 : ℂ) * hc
    · rw [hconjugate g h φ hg, SpinCharacters.weightSum_mul_sin, hvalue]
end YangMills.Construction.SpinHarmonics
