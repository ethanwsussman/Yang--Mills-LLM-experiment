import YangMills.Construction.Matrices.ExpSurjectivityAndComplexification
import Mathlib
open scoped Matrix.Norms.L2Operator Pointwise
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace ExpSurjective
theorem inv_eq_star_of_mem_unitaryGroup {W : ComplexMatrix2}
    (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) : W⁻¹ = star W :=
  Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 hW)
theorem matExp_unitary_conj_diagonal {W : ComplexMatrix2}
    (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) (d : Fin 2 → ℂ) :
    matExp (W * Matrix.diagonal d * star W) =
      W * Matrix.diagonal (fun i => Complex.exp (d i)) * star W := by
  have hu : IsUnit W :=
    ⟨⟨W, star W, Matrix.mem_unitaryGroup_iff.1 hW, Matrix.mem_unitaryGroup_iff'.1 hW⟩, rfl⟩
  rw [← inv_eq_star_of_mem_unitaryGroup hW, matExp, Matrix.exp_conj W _ hu, Matrix.exp_diagonal]
  congr 3
  funext i
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]
theorem det_unitary_conj_diagonal {W : ComplexMatrix2}
    (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) (d : Fin 2 → ℂ) :
    (W * Matrix.diagonal d * star W).det = d 0 * d 1 := by
  have h : W.det * (star W).det = 1 := by
    rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.1 hW, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]
  linear_combination (d 0 * d 1) * h
theorem exists_unitary_diagonalization {A : ComplexMatrix2} (hA : A.IsHermitian) :
    ∃ W ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ l : Fin 2 → ℝ,
      A = W * Matrix.diagonal (fun i => (l i : ℂ)) * star W ∧ fullTrace A = l 0 + l 1 := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvectorUnitary.2, hA.eigenvalues, ?_, ?_⟩
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  · have h := hA.trace_eq_sum_eigenvalues
    rw [Fin.sum_univ_two] at h
    exact h
theorem I_smul_conj_diagonal (W : ComplexMatrix2) (l : Fin 2 → ℂ) :
    Complex.I • (W * Matrix.diagonal l * star W) =
      W * Matrix.diagonal (fun i => Complex.I * l i) * star W := by
  have h : Matrix.diagonal (fun i => Complex.I * l i) = Complex.I • Matrix.diagonal l := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [h, Matrix.mul_smul, Matrix.smul_mul]
theorem conj_real_diagonal_mem_hermitianTraceless {W : ComplexMatrix2}
    (hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) (l : Fin 2 → ℝ) (hl : l 0 + l 1 = 0) :
    W * Matrix.diagonal (fun i => (l i : ℂ)) * star W ∈ hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, ← mul_assoc]
    congr 3
    funext i
    simp
  · rw [fullTrace, Matrix.trace_mul_cycle, Matrix.mem_unitaryGroup_iff'.1 hW, one_mul,
      Matrix.trace_fin_two]
    simp only [Matrix.diagonal_apply_eq]
    exact_mod_cast hl
theorem matExp_I_smul_mem_specialUnitary {Y : ComplexMatrix2} (hY : Y ∈ hermitianTraceless) :
    matExp (Complex.I • Y) ∈ specialUnitary := by
  obtain ⟨hh, ht⟩ := hY
  have hH : Y.IsHermitian := hh.symm
  obtain ⟨W, hW, l, hs, hl⟩ := exists_unitary_diagonalization hH
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    have hstar : star (matExp (Complex.I • Y)) = matExp (-(Complex.I • Y)) := by
      have h1 : (Complex.I • Y).conjTranspose = -(Complex.I • Y) := by
        rw [Matrix.conjTranspose_smul, ← hh]
        simp
      rw [← h1]
      exact (Matrix.exp_conjTranspose _).symm
    rw [hstar, matExp, matExp, Matrix.exp_neg]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
  · have hI : Complex.I • Y =
        W * Matrix.diagonal (fun i => Complex.I * (l i : ℂ)) * star W := by
      conv_lhs => rw [hs]
      exact I_smul_conj_diagonal W _
    rw [hI, matExp_unitary_conj_diagonal hW, det_unitary_conj_diagonal hW, ← Complex.exp_add,
      ← mul_add, ← hl, ht]
    simp
theorem exists_hermitianTraceless_matExp_eq {v : ComplexMatrix2} (hv : v ∈ specialUnitary) :
    ∃ Y ∈ hermitianTraceless, matExp (Complex.I • Y) = v := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hv
  have hvs : v * star v = 1 := Matrix.mem_unitaryGroup_iff.1 hu
  have hadj : star v = v.adjugate := by
    calc star v = (v.adjugate * v) * star v := by
          rw [Matrix.adjugate_mul, hd, one_smul, one_mul]
      _ = v.adjugate := by rw [mul_assoc, hvs, mul_one]
  have s00 : (star v) 0 0 = v 1 1 := by rw [hadj]; simp [Matrix.adjugate_fin_two]
  have s11 : (star v) 1 1 = v 0 0 := by rw [hadj]; simp [Matrix.adjugate_fin_two]
  have s01 : (star v) 0 1 = - v 0 1 := by rw [hadj]; simp [Matrix.adjugate_fin_two]
  have s10 : (star v) 1 0 = - v 1 0 := by rw [hadj]; simp [Matrix.adjugate_fin_two]
  have hconj : (starRingEnd ℂ) (v 0 0) = v 1 1 := by
    rw [← s00, Matrix.star_apply]
    rfl
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (c : ℂ) = (v 0 0 + v 1 1) / 2 := by
    refine ⟨(v 0 0).re, ?_⟩
    rw [← hconj, Complex.add_conj]
    push_cast
    ring
  set H : ComplexMatrix2 := (-(Complex.I / 2)) • (v - star v) with hHdef
  have hH : H.IsHermitian := by
    have hs : star (-(Complex.I / 2)) = Complex.I / 2 := by simp; ring
    rw [Matrix.IsHermitian, hHdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hs,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, ← neg_sub v, smul_neg,
      neg_smul]
  have htr : fullTrace H = 0 := by
    rw [hHdef, fullTrace, Matrix.trace_smul, Matrix.trace_fin_two]
    simp only [Matrix.sub_apply, s00, s11]
    simp
  have hdec : v = (c : ℂ) • (1 : ComplexMatrix2) + Complex.I • H := by
    have hI2 := Complex.I_mul_I
    ext i j
    revert i j
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [hHdef, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, s00, hc,
        Matrix.one_apply_eq, smul_eq_mul]
      linear_combination ((v 0 0 - v 1 1) / 2) * hI2
    · simp only [hHdef, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, s01, hc,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul]
      linear_combination (v 0 1) * hI2
    · simp only [hHdef, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, s10, hc,
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul]
      linear_combination (v 1 0) * hI2
    · simp only [hHdef, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, s11, hc,
        Matrix.one_apply_eq, smul_eq_mul]
      linear_combination ((v 1 1 - v 0 0) / 2) * hI2
  obtain ⟨W, hW, l, hs, hl⟩ := exists_unitary_diagonalization hH
  have hl1 : l 1 = - l 0 := by
    rw [htr] at hl
    have : l 0 + l 1 = 0 := by exact_mod_cast hl.symm
    linarith
  have hWs : W * star W = 1 := Matrix.mem_unitaryGroup_iff.1 hW
  have hvW : v = W * Matrix.diagonal (fun i => (c : ℂ) + Complex.I * (l i : ℂ)) * star W := by
    have hdiag : Matrix.diagonal (fun i => (c : ℂ) + Complex.I * (l i : ℂ)) =
        (c : ℂ) • (1 : ComplexMatrix2) + Matrix.diagonal (fun i => Complex.I * (l i : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
    rw [hdiag, mul_add, add_mul, ← I_smul_conj_diagonal, ← hs, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, hWs]
    exact hdec
  set μ : ℂ := (c : ℂ) + Complex.I * (l 0 : ℂ) with hμ
  set ν : ℂ := (c : ℂ) + Complex.I * (l 1 : ℂ) with hν
  have hμν : μ * ν = 1 := by
    rw [← hd, hvW, det_unitary_conj_diagonal hW]
  have hconjμ : (starRingEnd ℂ) μ = ν := by
    simp [hμ, hν, hl1]
  have hnorm : ‖μ‖ = 1 := by
    have h1 : ((Complex.normSq μ : ℝ) : ℂ) = 1 := by
      rw [← Complex.mul_conj, hconjμ, hμν]
    have h2 : Complex.normSq μ = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg μ]
  set θ : ℝ := Complex.arg μ with hθ
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) = μ := by
    have := Complex.norm_mul_exp_arg_mul_I μ
    rw [hnorm] at this
    simpa [mul_comm] using this
  have hexp' : Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) = ν := by
    have h1 : Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) = μ⁻¹ := by
      rw [← hexp, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [h1]
    exact (eq_inv_of_mul_eq_one_right hμν).symm
  refine ⟨W * Matrix.diagonal (fun i => ((![θ, -θ] i : ℝ) : ℂ)) * star W,
    conj_real_diagonal_mem_hermitianTraceless hW _ (by simp), ?_⟩
  rw [I_smul_conj_diagonal, matExp_unitary_conj_diagonal hW]
  conv_rhs => rw [hvW]
  congr 3
  funext i
  revert i
  simp only [Fin.forall_fin_two]
  exact ⟨by simpa using hexp, by simpa using hexp'⟩
theorem image_matExp_I_smul_eq :
    (fun Y : ComplexMatrix2 => matExp (Complex.I • Y)) '' (hermitianTraceless : Set ComplexMatrix2) =
      (specialUnitary : Set ComplexMatrix2) := by
  ext v
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact matExp_I_smul_mem_specialUnitary hY
  · intro hv
    obtain ⟨Y, hY, rfl⟩ := exists_hermitianTraceless_matExp_eq hv
    exact ⟨Y, hY, rfl⟩
theorem specialUnitary_connectedSpace : ConnectedSpace specialUnitary := by
  let _ : NormedAlgebra ℚ ComplexMatrix2 := NormedAlgebra.restrictScalars ℚ ℂ ComplexMatrix2
  have hcont : Continuous fun Y : ComplexMatrix2 => matExp (Complex.I • Y) :=
    NormedSpace.exp_continuous.comp (continuous_const_smul _)
  have hconn : IsConnected (specialUnitary : Set ComplexMatrix2) := by
    rw [← image_matExp_I_smul_eq]
    exact IsConnected.image
      (hermitianTraceless.convex.isConnected ⟨0, hermitianTraceless.zero_mem⟩) _
      hcont.continuousOn
  exact isConnected_iff_connectedSpace.1 hconn
theorem hermitianTraceless_inf_I_smul_eq_bot :
    hermitianTraceless ⊓ Complex.I • hermitianTraceless = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨hX, hX'⟩
  obtain ⟨Y, hY, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hX'
  have h1 : Complex.I • Y = (Complex.I • Y).conjTranspose := hX.1
  have h2 : (Complex.I • Y).conjTranspose = -(Complex.I • Y) := by
    rw [Matrix.conjTranspose_smul, ← hY.1]
    simp
  have h3 : (2 : ℂ) • (Complex.I • Y) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    rw [h2]
    simp
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
theorem exists_hermitianTraceless_add_I_smul {A : ComplexMatrix2} (hA : A ∈ traceless) :
    ∃ X ∈ hermitianTraceless, ∃ Y ∈ hermitianTraceless, A = X + Complex.I • Y := by
  have htr : fullTrace A = 0 := hA
  have htrs : fullTrace (star A) = 0 := by
    rw [fullTrace, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
    have : Matrix.trace A = 0 := htr
    rw [this, star_zero]
  refine ⟨(1 / 2 : ℂ) • (A + star A), ⟨?_, ?_⟩, (-(Complex.I / 2)) • (A - star A), ⟨?_, ?_⟩, ?_⟩
  · have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hs, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, add_comm]
  · have h1 : fullTrace A = Matrix.trace A := rfl
    have h2 : fullTrace (star A) = Matrix.trace (star A) := rfl
    rw [fullTrace, Matrix.trace_smul, Matrix.trace_add, ← h1, ← h2, htr, htrs]
    simp
  · have hs : star (-(Complex.I / 2)) = Complex.I / 2 := by simp; ring
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hs, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, ← neg_sub A, smul_neg, neg_smul]
  · have h1 : fullTrace A = Matrix.trace A := rfl
    have h2 : fullTrace (star A) = Matrix.trace (star A) := rfl
    rw [fullTrace, Matrix.trace_smul, Matrix.trace_sub, ← h1, ← h2, htr, htrs]
    simp
  · have hI2 := Complex.I_mul_I
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (((A i j) - (star A) i j) / 2) * hI2
theorem hermitianTraceless_sup_I_smul_eq :
    hermitianTraceless ⊔ Complex.I • hermitianTraceless = traceless.restrictScalars ℝ := by
  apply le_antisymm
  · refine sup_le (fun X hX => hX.2) ?_
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hX
    exact traceless.smul_mem _ hY.2
  · intro A hA
    obtain ⟨X, hX, Y, hY, rfl⟩ := exists_hermitianTraceless_add_I_smul hA
    exact Submodule.add_mem_sup hX
      ((Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨Y, hY, rfl⟩)
theorem exists_complex_basis_of_real_basis (ι : Type) (b : Module.Basis ι ℝ hermitianTraceless) :
    ∃ c : Module.Basis ι ℂ traceless, ∀ i, (c i : ComplexMatrix2) = (b i : ComplexMatrix2) := by
  let e : ι → traceless := fun i => ⟨b i, (b i).2.2⟩
  have hli : LinearIndependent ℂ e := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hm : ∑ j ∈ s, g j • (b j : ComplexMatrix2) = 0 := by
      have := congrArg (Subtype.val) hg
      simpa [e] using this
    have hXY : ((∑ j ∈ s, (g j).re • b j : hermitianTraceless) : ComplexMatrix2) =
        Complex.I • (-(∑ j ∈ s, (g j).im • b j : hermitianTraceless) : hermitianTraceless) := by
      have hsplit : ∀ j, g j • (b j : ComplexMatrix2) =
          (g j).re • (b j : ComplexMatrix2) + Complex.I • ((g j).im • (b j : ComplexMatrix2)) := by
        intro j
        conv_lhs => rw [← Complex.re_add_im (g j)]
        rw [add_smul, mul_comm, mul_smul]
        simp only [Complex.coe_smul]
      simp only [hsplit, Finset.sum_add_distrib, ← Finset.smul_sum] at hm
      simp only [Submodule.coe_sum, Submodule.coe_neg, Submodule.coe_smul, smul_neg]
      exact eq_neg_of_add_eq_zero_left hm
    have hmem : ((∑ j ∈ s, (g j).re • b j : hermitianTraceless) : ComplexMatrix2) ∈
        hermitianTraceless ⊓ Complex.I • hermitianTraceless :=
      ⟨Subtype.coe_prop _, hXY ▸ (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨_, Subtype.coe_prop _, rfl⟩⟩
    rw [hermitianTraceless_inf_I_smul_eq_bot, Submodule.mem_bot] at hmem
    have hX0 : (∑ j ∈ s, (g j).re • b j : hermitianTraceless) = 0 := Subtype.ext hmem
    have hY0 : (∑ j ∈ s, (g j).im • b j : hermitianTraceless) = 0 := by
      rw [hmem] at hXY
      have h2 := (smul_eq_zero.1 hXY.symm).resolve_left Complex.I_ne_zero
      have h3 : (-(∑ j ∈ s, (g j).im • b j : hermitianTraceless) : hermitianTraceless) = 0 :=
        Subtype.ext h2
      exact neg_eq_zero.1 h3
    have hr := linearIndependent_iff'.1 b.linearIndependent s _ hX0 i hi
    have him := linearIndependent_iff'.1 b.linearIndependent s _ hY0 i hi
    exact Complex.ext hr him
  have hreal : ∀ x : hermitianTraceless,
      (⟨x, x.2.2⟩ : traceless) ∈ Submodule.span ℂ (Set.range e) := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Set.range b) := by
      rw [b.span_eq]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      have := Submodule.smul_mem _ (r : ℂ) hy
      convert this using 1
      apply Subtype.ext
      simp
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rintro ⟨A, hA⟩ -
    obtain ⟨X, hX, Y, hY, hXY⟩ := exists_hermitianTraceless_add_I_smul hA
    have h1 := hreal ⟨X, hX⟩
    have h2 := Submodule.smul_mem _ Complex.I (hreal ⟨Y, hY⟩)
    have h3 := Submodule.add_mem _ h1 h2
    convert h3 using 1
    exact Subtype.ext hXY
  refine ⟨Module.Basis.mk hli hspan, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
theorem expSurjectivityAndComplexification_holds : ExpSurjectivityAndComplexification := by
  refine ⟨fun Y hY => matExp_I_smul_mem_specialUnitary hY,
    fun v hv => exists_hermitianTraceless_matExp_eq hv, ⟨specialUnitary_connectedSpace, ?_⟩,
    hermitianTraceless_inf_I_smul_eq_bot, hermitianTraceless_sup_I_smul_eq,
    exists_complex_basis_of_real_basis⟩
  intro S _
  have := specialUnitary_connectedSpace
  infer_instance
end ExpSurjective
end YangMills.Construction.Matrices.ComplexMatrix2
