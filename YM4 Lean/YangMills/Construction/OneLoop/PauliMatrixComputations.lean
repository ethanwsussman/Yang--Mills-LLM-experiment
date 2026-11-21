import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.OneLoop
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.ComplexMatrix2
private theorem leviCivita_xyz : leviCivitaSymbol 0 1 2 = 1 := by
  have h : Function.Bijective (![0, 1, 2] : Fin 3 → Fin 3) := by decide
  have e : Equiv.ofBijective (![0, 1, 2] : Fin 3 → Fin 3) h = 1 := by
    ext i; fin_cases i <;> rfl
  simp only [leviCivitaSymbol, dif_pos h, e]
  simp
private theorem leviCivita_yzx : leviCivitaSymbol 1 2 0 = 1 := by
  have h : Function.Bijective (![1, 2, 0] : Fin 3 → Fin 3) := by decide
  have e : Equiv.Perm.sign (Equiv.ofBijective (![1, 2, 0] : Fin 3 → Fin 3) h) = 1 := by
    have : Equiv.ofBijective (![1, 2, 0] : Fin 3 → Fin 3) h =
        Equiv.swap 0 1 * Equiv.swap 1 2 := by
      ext i; fin_cases i <;> rfl
    rw [this]; decide
  simp only [leviCivitaSymbol, dif_pos h, e]
  simp
private theorem leviCivita_zxy : leviCivitaSymbol 2 0 1 = 1 := by
  have h : Function.Bijective (![2, 0, 1] : Fin 3 → Fin 3) := by decide
  have e : Equiv.Perm.sign (Equiv.ofBijective (![2, 0, 1] : Fin 3 → Fin 3) h) = 1 := by
    have : Equiv.ofBijective (![2, 0, 1] : Fin 3 → Fin 3) h =
        Equiv.swap 1 2 * Equiv.swap 0 1 := by
      ext i; fin_cases i <;> rfl
    rw [this]; decide
  simp only [leviCivitaSymbol, dif_pos h, e]
  simp
private theorem leviCivita_yxz : leviCivitaSymbol 1 0 2 = -1 := by
  have h : Function.Bijective (![1, 0, 2] : Fin 3 → Fin 3) := by decide
  have e : Equiv.Perm.sign (Equiv.ofBijective (![1, 0, 2] : Fin 3 → Fin 3) h) = -1 := by
    have : Equiv.ofBijective (![1, 0, 2] : Fin 3 → Fin 3) h = Equiv.swap 0 1 := by
      ext i; fin_cases i <;> rfl
    rw [this]; decide
  simp only [leviCivitaSymbol, dif_pos h, e]
  simp
private theorem leviCivita_zyx : leviCivitaSymbol 2 1 0 = -1 := by
  have h : Function.Bijective (![2, 1, 0] : Fin 3 → Fin 3) := by decide
  have e : Equiv.Perm.sign (Equiv.ofBijective (![2, 1, 0] : Fin 3 → Fin 3) h) = -1 := by
    have : Equiv.ofBijective (![2, 1, 0] : Fin 3 → Fin 3) h = Equiv.swap 0 2 := by
      ext i; fin_cases i <;> rfl
    rw [this]; decide
  simp only [leviCivitaSymbol, dif_pos h, e]
  simp
private theorem leviCivita_xzy : leviCivitaSymbol 0 2 1 = -1 := by
  have h : Function.Bijective (![0, 2, 1] : Fin 3 → Fin 3) := by decide
  have e : Equiv.Perm.sign (Equiv.ofBijective (![0, 2, 1] : Fin 3 → Fin 3) h) = -1 := by
    have : Equiv.ofBijective (![0, 2, 1] : Fin 3 → Fin 3) h = Equiv.swap 1 2 := by
      ext i; fin_cases i <;> rfl
    rw [this]; decide
  simp only [leviCivitaSymbol, dif_pos h, e]
  simp
private theorem leviCivita_of_not_bijective (a b c : Fin 3)
    (h : ¬ Function.Bijective (![a, b, c] : Fin 3 → Fin 3)) :
    leviCivitaSymbol a b c = 0 := by
  simp only [leviCivitaSymbol, dif_neg h]
private theorem leviCivita_repeat_first (a c : Fin 3) : leviCivitaSymbol a a c = 0 :=
  leviCivita_of_not_bijective a a c (by revert a c; decide)
private theorem leviCivita_xy_repeat : leviCivitaSymbol 0 1 0 = 0 ∧ leviCivitaSymbol 0 1 1 = 0 :=
  ⟨leviCivita_of_not_bijective _ _ _ (by decide), leviCivita_of_not_bijective _ _ _ (by decide)⟩
private theorem leviCivita_yx_repeat : leviCivitaSymbol 1 0 0 = 0 ∧ leviCivitaSymbol 1 0 1 = 0 :=
  ⟨leviCivita_of_not_bijective _ _ _ (by decide), leviCivita_of_not_bijective _ _ _ (by decide)⟩
private theorem leviCivita_xz_repeat : leviCivitaSymbol 0 2 0 = 0 ∧ leviCivitaSymbol 0 2 2 = 0 :=
  ⟨leviCivita_of_not_bijective _ _ _ (by decide), leviCivita_of_not_bijective _ _ _ (by decide)⟩
private theorem leviCivita_zx_repeat : leviCivitaSymbol 2 0 0 = 0 ∧ leviCivitaSymbol 2 0 2 = 0 :=
  ⟨leviCivita_of_not_bijective _ _ _ (by decide), leviCivita_of_not_bijective _ _ _ (by decide)⟩
private theorem leviCivita_yz_repeat : leviCivitaSymbol 1 2 1 = 0 ∧ leviCivitaSymbol 1 2 2 = 0 :=
  ⟨leviCivita_of_not_bijective _ _ _ (by decide), leviCivita_of_not_bijective _ _ _ (by decide)⟩
private theorem leviCivita_zy_repeat : leviCivitaSymbol 2 1 1 = 0 ∧ leviCivitaSymbol 2 1 2 = 0 :=
  ⟨leviCivita_of_not_bijective _ _ _ (by decide), leviCivita_of_not_bijective _ _ _ (by decide)⟩
private theorem pauliFamily_mul (a b : Fin 3) : pauliFamily a * pauliFamily b =
    (if a = b then (1 : ComplexMatrix2) else 0) +
      Complex.I • ∑ c, leviCivitaSymbol a b c • pauliFamily c := by
  rw [sum_smul_pauliFamily]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, leviCivita_xyz, leviCivita_yzx,
      leviCivita_zxy, leviCivita_yxz, leviCivita_zyx, leviCivita_xzy, leviCivita_repeat_first,
      leviCivita_xy_repeat.1, leviCivita_xy_repeat.2, leviCivita_yx_repeat.1,
      leviCivita_yx_repeat.2, leviCivita_xz_repeat.1, leviCivita_xz_repeat.2,
      leviCivita_zx_repeat.1, leviCivita_zx_repeat.2, leviCivita_yz_repeat.1,
      leviCivita_yz_repeat.2, leviCivita_zy_repeat.1, leviCivita_zy_repeat.2] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliFamily, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
private theorem leviCivita_swap (a b c : Fin 3) :
    leviCivitaSymbol b a c = -leviCivitaSymbol a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, leviCivita_xyz, leviCivita_yzx,
      leviCivita_zxy, leviCivita_yxz, leviCivita_zyx, leviCivita_xzy, leviCivita_repeat_first,
      leviCivita_xy_repeat.1, leviCivita_xy_repeat.2, leviCivita_yx_repeat.1,
      leviCivita_yx_repeat.2, leviCivita_xz_repeat.1, leviCivita_xz_repeat.2,
      leviCivita_zx_repeat.1, leviCivita_zx_repeat.2, leviCivita_yz_repeat.1,
      leviCivita_yz_repeat.2, leviCivita_zy_repeat.1, leviCivita_zy_repeat.2] <;> simp
private theorem pauliFamily_commutator (a b : Fin 3) :
    pauliFamily a * pauliFamily b - pauliFamily b * pauliFamily a =
      (2 * Complex.I) • ∑ c, leviCivitaSymbol a b c • pauliFamily c := by
  rw [pauliFamily_mul a b, pauliFamily_mul b a]
  have hif : (if b = a then (1 : ComplexMatrix2) else 0) =
      if a = b then (1 : ComplexMatrix2) else 0 := by
    simp only [eq_comm]
  have hsum : ∑ c, leviCivitaSymbol b a c • pauliFamily c =
      -∑ c, leviCivitaSymbol a b c • pauliFamily c := by
    simp only [leviCivita_swap a b, neg_smul, Finset.sum_neg_distrib]
  rw [hif, hsum, two_mul, add_smul]
  simp only [smul_neg]
  abel
private theorem pauliFamily_mem_traceless (a : Fin 3) : pauliFamily a ∈ traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    pauliFamily a ∈ hermitianTraceless := by apply _root_.YangMills.Construction.Matrices.PowerExpCharts.pauliFamily_mem_hermitianTraceless <;> assumption
abbrev _root_.YangMills.SharedProofs.p1437 := @pauliFamily_mem_hermitianTraceless
private theorem halfTrace_sum_mul_sum (x y : Fin 3 → ℂ) :
    halfTrace ((∑ a, x a • pauliFamily a) * ∑ a, y a • pauliFamily a) = ∑ a, x a * y a := by apply _root_.YangMills.Construction.LieInnerProductProof.halfTracePairing_pauliCombination <;> assumption
private theorem sum_smul_pauliFamily_sq (x : Fin 3 → ℂ) :
    (∑ a, x a • pauliFamily a) ^ 2 = (∑ a, x a * x a) • (1 : ComplexMatrix2) := by
  rw [sum_smul_pauliFamily, pow_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination (-(x 1 * x 1)) * Complex.I_sq
private theorem sq_eq_traceForm_smul_one (X : traceless) :
    (X : ComplexMatrix2) ^ 2 = traceForm X X • (1 : ComplexMatrix2) := by
  obtain ⟨x, hx, -⟩ := existsUnique_traceless_eq_sum_pauliFamily X.2
  have hform : traceForm X X = ∑ a, x a * x a := by
    simp only [traceForm]
    rw [hx]
    exact halfTrace_sum_mul_sum x x
  rw [hform, hx, sum_smul_pauliFamily_sq]
private theorem operatorNorm_sq_eq_traceForm (X : traceless)
    (hX : (X : ComplexMatrix2) ∈ hermitianTraceless) :
    ((operatorNorm (X : ComplexMatrix2) ^ 2 : ℝ) : ℂ) = traceForm X X := by
  let A : LieElement := (⟨(X : ComplexMatrix2), hX⟩ : hermitianTraceless)
  let c : ℝ := (1 / 2) * ∑ i, ∑ j, ‖A.toMatrix i j‖ ^ 2
  have hc0 : 0 ≤ c := by positivity
  have hc : traceForm X X = (c : ℂ) := by
    have h := LieElement.fullTrace_mul_self A
    have h' : fullTrace ((X : ComplexMatrix2) * (X : ComplexMatrix2)) =
        ((∑ i, ∑ j, ‖A.toMatrix i j‖ ^ 2 : ℝ) : ℂ) := h
    simp only [traceForm, halfTrace]
    rw [h']
    simp only [c]
    push_cast
    ring
  have hstar : star (X : ComplexMatrix2) = (X : ComplexMatrix2) := hX.1.symm
  have hn : ‖(X : ComplexMatrix2)‖ * ‖(X : ComplexMatrix2)‖ = c := by
    rw [← CStarRing.norm_star_mul_self, hstar, ← pow_two, sq_eq_traceForm_smul_one, hc,
      norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg hc0]
  rw [hc, pow_two]
  exact congrArg _ hn
private theorem halfTrace_pow_of_sq (Y : ComplexMatrix2) (r : ℂ)
    (hY : Y ^ 2 = r ^ 2 • (1 : ComplexMatrix2)) (h0 : fullTrace Y = 0) (n : ℕ) :
    halfTrace (Y ^ n) = (r ^ n + (-r) ^ n) / 2 := by
  have key : ∀ n, halfTrace (Y ^ n) = (r ^ n + (-r) ^ n) / 2 ∧
      halfTrace (Y ^ (n + 1)) = (r ^ (n + 1) + (-r) ^ (n + 1)) / 2 := by
    intro n
    induction n with
    | zero =>
      constructor
      · simp [halfTrace, fullTrace, Matrix.trace_one]
      · simp [halfTrace, h0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hpow : Y ^ (n + 1 + 1) = r ^ 2 • Y ^ n := by
        rw [show n + 1 + 1 = n + 2 from rfl, pow_add, hY, Matrix.mul_smul, mul_one]
      have htr : halfTrace (Y ^ (n + 1 + 1)) = r ^ 2 * halfTrace (Y ^ n) := by
        rw [hpow]
        simp only [halfTrace, fullTrace, Matrix.trace_smul, smul_eq_mul]
        ring
      rw [htr, ih.1]
      ring
  exact (key n).1
private theorem halfTrace_matExp_I_smul (Y : ComplexMatrix2) (r : ℝ)
    (hY : Y ^ 2 = (r : ℂ) ^ 2 • (1 : ComplexMatrix2)) (h0 : fullTrace Y = 0) :
    halfTrace (matExp (Complex.I • Y)) = ((Real.cos r : ℝ) : ℂ) := by
  let φ : ComplexMatrix2 →+ ℂ :=
    { toFun := halfTrace
      map_zero' := by simp [halfTrace, fullTrace]
      map_add' := fun A B => by
        simp only [halfTrace, fullTrace, Matrix.trace_add]
        ring }
  have hφ : Continuous φ := by
    change Continuous fun A : ComplexMatrix2 => (1 / 2 : ℂ) * Matrix.trace A
    exact continuous_const.mul (Continuous.matrix_trace continuous_id)
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Complex.I • Y) ^ n)
      (matExp (Complex.I • Y)) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) _
  have h2 := h1.map φ hφ
  have h3 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • ((r : ℂ) * Complex.I) ^ n)
      (Complex.exp ((r : ℂ) * Complex.I)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) _
  have h4 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (-(r : ℂ) * Complex.I) ^ n)
      (Complex.exp (-(r : ℂ) * Complex.I)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) _
  have h5 := (h3.add h4).div_const 2
  have terms : (φ ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Complex.I • Y) ^ n) =
      fun n : ℕ => (((n.factorial : ℂ)⁻¹) • ((r : ℂ) * Complex.I) ^ n +
        ((n.factorial : ℂ)⁻¹) • (-(r : ℂ) * Complex.I) ^ n) / 2 := by
    funext n
    have t := halfTrace_pow_of_sq Y (r : ℂ) hY h0 n
    change halfTrace (((n.factorial : ℂ)⁻¹) • (Complex.I • Y) ^ n) = _
    rw [smul_pow]
    simp only [halfTrace, fullTrace, Matrix.trace_smul, smul_eq_mul] at t ⊢
    rw [mul_pow, mul_pow]
    linear_combination ((n.factorial : ℂ)⁻¹ * Complex.I ^ n) * t
  rw [terms] at h2
  have := h2.unique h5
  rw [Complex.ofReal_cos, Complex.cos]
  exact this
private theorem exists_orthonormalBasis_pauliFamily :
    ∃ e : OrthonormalBasis (Fin 3) ℝ LieElement, ∀ a, (e a).toMatrix = pauliFamily a := by
  let v : Fin 3 → LieElement :=
    fun a => (⟨pauliFamily a, pauliFamily_mem_hermitianTraceless a⟩ : hermitianTraceless)
  let L : LieElement →ₗ[ℝ] ComplexMatrix2 :=
    { toFun := LieElement.toMatrix
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro a b
    change (halfTrace (pauliFamily a * pauliFamily b)).re = _
    fin_cases a <;> fin_cases b <;>
      simp [pauliFamily, pauliX, pauliY, pauliZ, halfTrace, fullTrace, Matrix.trace_fin_two] <;>
      norm_num
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    intro X _
    obtain ⟨x, hx, -⟩ := LieElement.existsUnique_toMatrix_eq_real_sum X
    have hs : X = ∑ a, x a • v a := by
      apply Subtype.ext
      change X.toMatrix = L (∑ a, x a • v a)
      rw [map_sum, hx]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, show L (v a) = pauliFamily a from rfl]
      ext i j
      simp
    rw [hs]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨OrthonormalBasis.mk hon hsp, fun a => ?_⟩
  rw [OrthonormalBasis.coe_mk]
  rfl
private theorem exists_basis_pauliFamily :
    ∃ e : Module.Basis (Fin 3) ℂ traceless,
      ∀ a, ((e a : traceless) : ComplexMatrix2) = pauliFamily a := by
  let w : Fin 3 → traceless := fun a => ⟨pauliFamily a, pauliFamily_mem_traceless a⟩
  have hcoe : ∀ g : Fin 3 → ℂ,
      ((∑ a, g a • w a : traceless) : ComplexMatrix2) = ∑ a, g a • pauliFamily a := by
    intro g
    simp [w]
  have hli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨y, -, hu⟩ := existsUnique_traceless_eq_sum_pauliFamily (traceless.zero_mem)
    have h₁ : (0 : ComplexMatrix2) = ∑ a, g a • pauliFamily a := by
      rw [← hcoe, hg]
      rfl
    have h₂ : (0 : ComplexMatrix2) = ∑ a, (0 : Fin 3 → ℂ) a • pauliFamily a := by simp
    exact congrFun ((hu g h₁).trans (hu 0 h₂).symm) i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range w) := by
    intro X _
    obtain ⟨x, hx, -⟩ := existsUnique_traceless_eq_sum_pauliFamily X.2
    have hs : X = ∑ a, x a • w a := by
      apply Subtype.ext
      rw [hcoe, ← hx]
    rw [hs]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, fun a => ?_⟩
  rw [Module.Basis.mk_apply]
private theorem traceForm_conjugateOnTraceless (g : specialLinear) (X Y : traceless) :
    traceForm (conjugateOnTraceless (g : ComplexMatrix2) X)
      (conjugateOnTraceless (g : ComplexMatrix2) Y) = traceForm X Y := by
  have hconj : ∀ Z : traceless,
      ((conjugateOnTraceless (g : ComplexMatrix2) Z : traceless) : ComplexMatrix2) =
        (g : ComplexMatrix2) * (Z : ComplexMatrix2) * (g : ComplexMatrix2)⁻¹ := fun _ => rfl
  have hdet : IsUnit (g : ComplexMatrix2).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  have hu : (g : ComplexMatrix2)⁻¹ * (g : ComplexMatrix2) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hp : (g : ComplexMatrix2) * (X : ComplexMatrix2) * (g : ComplexMatrix2)⁻¹ *
        ((g : ComplexMatrix2) * (Y : ComplexMatrix2) * (g : ComplexMatrix2)⁻¹) =
      (g : ComplexMatrix2) * ((X : ComplexMatrix2) * (Y : ComplexMatrix2)) *
        (g : ComplexMatrix2)⁻¹ := by
    calc (g : ComplexMatrix2) * (X : ComplexMatrix2) * (g : ComplexMatrix2)⁻¹ *
          ((g : ComplexMatrix2) * (Y : ComplexMatrix2) * (g : ComplexMatrix2)⁻¹)
        = (g : ComplexMatrix2) * (X : ComplexMatrix2) *
            ((g : ComplexMatrix2)⁻¹ * (g : ComplexMatrix2)) * (Y : ComplexMatrix2) *
              (g : ComplexMatrix2)⁻¹ := by
          simp only [mul_assoc]
      _ = (g : ComplexMatrix2) * ((X : ComplexMatrix2) * (Y : ComplexMatrix2)) *
            (g : ComplexMatrix2)⁻¹ := by
          rw [hu, mul_one]
          simp only [mul_assoc]
  simp only [traceForm, hconj]
  rw [hp]
  simp only [halfTrace, fullTrace]
  rw [Matrix.trace_mul_comm, ← mul_assoc, hu, one_mul]
theorem pauliMatrixRelations_of_conjugationDeterminant (h : ComplexMatrix2.ConjugationDeterminant) :
    PauliMatrixRelations := by
  refine ⟨pauliFamily_mul, pauliFamily_commutator, exists_orthonormalBasis_pauliFamily,
    exists_basis_pauliFamily, ?_, sq_eq_traceForm_smul_one, ?_, operatorNorm_sq_eq_traceForm,
    ?_, traceForm_conjugateOnTraceless, ?_⟩
  · intro X Y x y hX hY
    simp only [traceForm]
    rw [hX, hY]
    exact halfTrace_sum_mul_sum x y
  · intro X Y
    have h₁ := norm_sub_le ((X : ComplexMatrix2) * (Y : ComplexMatrix2))
      ((Y : ComplexMatrix2) * (X : ComplexMatrix2))
    have h₂ := norm_mul_le (X : ComplexMatrix2) (Y : ComplexMatrix2)
    have h₃ := norm_mul_le (Y : ComplexMatrix2) (X : ComplexMatrix2)
    simp only [operatorNorm]
    linarith [mul_comm ‖(X : ComplexMatrix2)‖ ‖(Y : ComplexMatrix2)‖]
  · intro Y hY
    let X : traceless := ⟨Y, hY.2⟩
    have hs : Y ^ 2 = ((operatorNorm Y : ℝ) : ℂ) ^ 2 • (1 : ComplexMatrix2) := by
      have h₁ := sq_eq_traceForm_smul_one X
      rw [← operatorNorm_sq_eq_traceForm X hY] at h₁
      simpa [X] using h₁
    exact halfTrace_matExp_I_smul Y (operatorNorm Y) hs hY.2
  · intro g hg
    have hdet : IsUnit (g : ComplexMatrix2).det := by
      rw [(Matrix.mem_specialUnitaryGroup_iff.mp hg).2]
      exact isUnit_one
    exact ((h g hdet).2.2 hg).1
end YangMills.Construction.OneLoop
end
