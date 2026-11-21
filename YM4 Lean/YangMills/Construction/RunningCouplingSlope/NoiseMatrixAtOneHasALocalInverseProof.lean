import YangMills.Construction.RunningCouplingSlope.MixedDerivativeByCellsProof
import YangMills.Construction.RunningCouplingSlope.TheOrbitMapReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainHasABoundedInverseAtOneProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.NoiseInverse
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
section MatrixNorms
variable {T : Type} [Fintype T] [DecidableEq T]
private theorem opNorm_one_le : ‖(1 : Matrix T T ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
private theorem exists_selfAdjoint_sqrt {A : Matrix T T ℂ} (hA : A.PosSemidef) :
    ∃ r : Matrix T T ℂ, r.conjTranspose = r ∧ r * r = A := by
  have hnonneg : (0 : Matrix T T ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.2 hA
  refine ⟨CFC.sqrt A, ?_, CFC.sqrt_mul_sqrt_self A hnonneg⟩
  exact (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
private theorem opNorm_le_one_of_posSemidef_of_le_one {C : Matrix T T ℂ} (hC : C.PosSemidef)
    (hC' : (1 - C).PosSemidef) : ‖C‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg C (Matrix.nonneg_iff_posSemidef.2 hC)).2
    (Matrix.le_iff.2 hC')
private theorem isUnit_one_add_and_norm_inv_le {P : Matrix T T ℂ} (hP : P.PosSemidef) :
    IsUnit (1 + P) ∧ ‖(1 + P)⁻¹‖ ≤ 1 := by
  have hpd : (1 + P).PosDef := Matrix.PosDef.one.add_posSemidef hP
  have hu : IsUnit (1 + P) := hpd.isUnit
  refine ⟨hu, ?_⟩
  obtain ⟨a, ha⟩ := hu
  have h0 : (0 : Matrix T T ℂ) ≤ (a : Matrix T T ℂ) := by
    rw [ha]
    exact Matrix.nonneg_iff_posSemidef.2 hpd.posSemidef
  have h1 : (1 : Matrix T T ℂ) ≤ (a : Matrix T T ℂ) := by
    rw [ha, Matrix.le_iff]
    simpa using hP
  have h2 := (CStarAlgebra.inv_le_one_iff_one_le h0).2 h1
  have e : (1 + P)⁻¹ = ((a⁻¹ : (Matrix T T ℂ)ˣ) : Matrix T T ℂ) := by
    rw [← ha]
    exact Matrix.inv_eq_right_inv (by simp)
  have h3 : (0 : Matrix T T ℂ) ≤ ((a⁻¹ : (Matrix T T ℂ)ˣ) : Matrix T T ℂ) := by
    rw [← e]
    exact Matrix.nonneg_iff_posSemidef.2 hpd.posSemidef.inv
  have h4 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ h3).2 h2
  rwa [e]
private theorem opNorm_le_one_of_isometry {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (P : Matrix A B ℂ) (hP : P.conjTranspose * P = 1) : ‖P‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hP] at h
  have h1 := opNorm_one_le (T := B)
  nlinarith [norm_nonneg P]
private theorem opNorm_fromBlocks_le (A B C D : Matrix T T ℂ) :
    ‖Matrix.fromBlocks A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix (T ⊕ T) T ℂ, P = Matrix.fromRows 1 0 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (T ⊕ T) T ℂ, Q = Matrix.fromRows 0 1 := ⟨_, rfl⟩
  have nP : ‖P‖ ≤ 1 := opNorm_le_one_of_isometry P (by
    rw [hP, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
    simp)
  have nQ : ‖Q‖ ≤ 1 := opNorm_le_one_of_isometry Q (by
    rw [hQ, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
    simp)
  have term : ∀ (X Y : Matrix (T ⊕ T) T ℂ) (Z : Matrix T T ℂ), ‖X‖ ≤ 1 → ‖Y‖ ≤ 1 →
      ‖X * Z * Y.conjTranspose‖ ≤ ‖Z‖ := by
    intro X Y Z hX hY
    calc ‖X * Z * Y.conjTranspose‖ ≤ ‖X * Z‖ * ‖Y.conjTranspose‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖X‖ * ‖Z‖ * ‖Y‖ := by
          rw [Matrix.l2_opNorm_conjTranspose]
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖Z‖ * 1 := by gcongr
      _ = ‖Z‖ := by ring
  have e : Matrix.fromBlocks A B C D = P * A * P.conjTranspose + P * B * Q.conjTranspose +
      Q * C * P.conjTranspose + Q * D * Q.conjTranspose := by
    rw [hP, hQ]
    simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul]
    simp
    ext (i | i) (j | j) <;> simp
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (term _ _ _ nP nP) (term _ _ _ nP nQ)))
    (term _ _ _ nQ nP))) (term _ _ _ nQ nQ))
private def schurInvBound (c g : ℝ) : ℝ := (1 + (c + 1) * g) * c
private theorem exists_right_inv_schur {C Γ : Matrix T T ℂ} (hC : C.PosSemidef)
    (hC' : (1 - C).PosSemidef) (hΓ : Γ.PosSemidef) (hu : IsUnit (Matrix.det C)) {c g : ℝ}
    (hc : ‖C⁻¹‖ ≤ c) (hg : ‖Γ‖ ≤ g) :
    ∃ F : Matrix T T ℂ, (C + (1 - C) * Γ) * F = 1 ∧ ‖F‖ ≤ schurInvBound c g := by
  obtain ⟨s, hs, hss⟩ := exists_selfAdjoint_sqrt hC
  obtain ⟨r, hr, hrr⟩ := exists_selfAdjoint_sqrt hΓ
  have hCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hu
  have hiC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hu
  have hCh : (C⁻¹).conjTranspose = C⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hC.1.eq]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = C⁻¹ - 1 := ⟨_, rfl⟩
  have hνp : ν.PosSemidef := by
    have e : ν = C⁻¹ * s * (1 - C) * (C⁻¹ * s).conjTranspose := by
      rw [Matrix.conjTranspose_mul, hs, hCh, hν]
      have e2 : C⁻¹ * s * (1 - C) * (s * C⁻¹) = C⁻¹ * (s * s) * C⁻¹ - C⁻¹ * (s * (C * s)) * C⁻¹ := by
        noncomm_ring
      have e3 : s * (C * s) = C * C := by
        nth_rewrite 1 [← hss]
        rw [← hss]
        noncomm_ring
      rw [e2, e3, hss, hiC, Matrix.one_mul, ← Matrix.mul_assoc, hiC, Matrix.one_mul, hCi]
    rw [e]
    exact hC'.mul_mul_conjTranspose_same _
  obtain ⟨hBu, hBn⟩ := isUnit_one_add_and_norm_inv_le (hνp.mul_mul_conjTranspose_same r)
  rw [hr] at hBu hBn
  obtain ⟨Bi, hBi⟩ : ∃ Bi, Bi = (1 + r * ν * r)⁻¹ := ⟨_, rfl⟩
  rw [← hBi] at hBn
  have hBB : (1 + r * ν * r) * Bi = 1 := by
    rw [hBi]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBu)
  obtain ⟨W, hW⟩ : ∃ W, W = 1 - ν * r * Bi * r := ⟨_, rfl⟩
  have hAW : (1 + ν * Γ) * W = 1 := by
    have e : (1 + ν * Γ) * W = 1 + ν * r * (r - (1 + r * ν * r) * Bi * r) := by
      rw [hW, ← hrr]
      noncomm_ring
    rw [e, hBB]
    simp
  have hrn : ‖r‖ * ‖r‖ ≤ g := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self r
    rw [hr, hrr] at h
    linarith
  have hνn : ‖ν‖ ≤ c + 1 := by
    rw [hν]
    exact (norm_sub_le _ _).trans (add_le_add hc opNorm_one_le)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hc
  have hg0 : 0 ≤ g := (norm_nonneg _).trans hg
  have hWn : ‖W‖ ≤ 1 + (c + 1) * g := by
    rw [hW]
    refine (norm_sub_le _ _).trans (add_le_add opNorm_one_le ?_)
    calc ‖ν * r * Bi * r‖ ≤ ‖ν‖ * ‖r‖ * ‖Bi‖ * ‖r‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (c + 1) * ‖r‖ * 1 * ‖r‖ := by gcongr
      _ = (c + 1) * (‖r‖ * ‖r‖) := by ring
      _ ≤ (c + 1) * g := by gcongr
  refine ⟨W * C⁻¹, ?_, ?_⟩
  · have e : C + (1 - C) * Γ = C * (1 + ν * Γ) := by
      have e1 : C * ν = 1 - C := by
        rw [hν, Matrix.mul_sub, hCi, Matrix.mul_one]
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, e1]
    rw [e, Matrix.mul_assoc, ← Matrix.mul_assoc _ W, hAW, Matrix.one_mul, hCi]
  · refine (norm_mul_le _ _).trans ?_
    unfold schurInvBound
    gcongr
private def blockInvBound (c g : ℝ) : ℝ :=
  schurInvBound c g * 2 + schurInvBound c g + (1 + g * (schurInvBound c g * 2)) +
    (1 + g * schurInvBound c g)
private theorem noiseBlocks_isUnit_and_norm_inv_le {C Γ : Matrix T T ℂ} (hC : C.PosSemidef)
    (hC' : (1 - C).PosSemidef) (hΓ : Γ.PosSemidef) (hu : IsUnit (Matrix.det C)) {c g : ℝ}
    (hc : ‖C⁻¹‖ ≤ c) (hg : ‖Γ‖ ≤ g) :
    IsUnit (Matrix.det (Matrix.fromBlocks (-Γ - C) (-C) (-C) (1 - C))) ∧
      ‖(Matrix.fromBlocks (-Γ - C) (-C) (-C) (1 - C))⁻¹‖ ≤ blockInvBound c g := by
  obtain ⟨F, hF, hFn⟩ := exists_right_inv_schur hC hC' hΓ hu hc hg
  obtain ⟨W, hW⟩ : ∃ W, W = Matrix.fromBlocks (-(F * (1 - C))) (-(F * C))
      (-1 + Γ * (F * (1 - C))) (1 + Γ * (F * C)) := ⟨_, rfl⟩
  have hNW : Matrix.fromBlocks (-Γ - C) (-C) (-C) (1 - C) * W = 1 := by
    have hE : C * F + (1 - C) * Γ * F = 1 := by
      rw [← Matrix.add_mul]
      exact hF
    have a1 : (-Γ - C) * -(F * (1 - C)) + -C * (-1 + Γ * (F * (1 - C))) =
        (C * F + (1 - C) * Γ * F) * (1 - C) + C := by noncomm_ring
    have a2 : (-Γ - C) * -(F * C) + -C * (1 + Γ * (F * C)) =
        (C * F + (1 - C) * Γ * F) * C - C := by noncomm_ring
    have a3 : -C * -(F * (1 - C)) + (1 - C) * (-1 + Γ * (F * (1 - C))) =
        (C * F + (1 - C) * Γ * F) * (1 - C) - (1 - C) := by noncomm_ring
    have a4 : -C * -(F * C) + (1 - C) * (1 + Γ * (F * C)) =
        (C * F + (1 - C) * Γ * F) * C + (1 - C) := by noncomm_ring
    rw [hW, Matrix.fromBlocks_multiply, a1, a2, a3, a4, hE, ← Matrix.fromBlocks_one]
    simp
  have hdet : IsUnit (Matrix.det (Matrix.fromBlocks (-Γ - C) (-C) (-C) (1 - C))) := by
    have := congrArg Matrix.det hNW
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  refine ⟨hdet, ?_⟩
  rw [Matrix.inv_eq_right_inv hNW, hW]
  have hC1 : ‖(1 : Matrix T T ℂ) - C‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      linarith [opNorm_one_le (T := T), opNorm_le_one_of_posSemidef_of_le_one hC hC'])
  have hC0 : ‖C‖ ≤ 1 := opNorm_le_one_of_posSemidef_of_le_one hC hC'
  have hk0 : 0 ≤ schurInvBound c g := (norm_nonneg _).trans hFn
  have hg0 : 0 ≤ g := (norm_nonneg _).trans hg
  have b1 : ‖F * (1 - C)‖ ≤ schurInvBound c g * 2 :=
    (norm_mul_le _ _).trans (mul_le_mul hFn hC1 (norm_nonneg _) hk0)
  have b2 : ‖F * C‖ ≤ schurInvBound c g :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg F, norm_nonneg C])
  refine (opNorm_fromBlocks_le _ _ _ _).trans ?_
  unfold blockInvBound
  rw [norm_neg, norm_neg]
  refine add_le_add (add_le_add (add_le_add b1 b2) ?_) ?_
  · refine (norm_add_le _ _).trans (add_le_add (by rw [norm_neg]; exact opNorm_one_le) ?_)
    exact (norm_mul_le _ _).trans (mul_le_mul hg b1 (norm_nonneg _) hg0)
  · refine (norm_add_le _ _).trans (add_le_add opNorm_one_le ?_)
    exact (norm_mul_le _ _).trans (mul_le_mul hg b2 (norm_nonneg _) hg0)
end MatrixNorms
section CellBlocks
variable {L n k : ℕ}
private theorem cellDist_nonneg (y y' : Vertex L n k k) : 0 ≤ cellDist y y' := by apply _root_.YangMills.SharedProofs.p2231 <;> assumption
private theorem cellDist_self (y : Vertex L n k k) : cellDist y y = 0 := by apply _root_.YangMills.SharedProofs.p28613 <;> assumption
variable {T : Type} [Fintype T] [DecidableEq T] (c : T → Vertex L n k k)
private theorem blockBetween_neg (A : Matrix T T ℂ) (y' y : Vertex L n k k) :
    blockBetween c c (-A) y' y = -blockBetween c c A y' y := by
  ext p q
  simp only [blockBetween, Matrix.neg_apply]
  split_ifs <;> simp
private theorem blockBetween_add (A B : Matrix T T ℂ) (y' y : Vertex L n k k) :
    blockBetween c c (A + B) y' y = blockBetween c c A y' y + blockBetween c c B y' y := by
  ext p q
  simp only [blockBetween, Matrix.add_apply]
  split_ifs <;> simp
private theorem norm_blockBetween_one_le (y' y : Vertex L n k k) {θ : ℝ} :
    ‖blockBetween c c (1 : Matrix T T ℂ) y' y‖ ≤ Real.exp (-(θ * cellDist y' y)) := by
  classical
  by_cases h : y' = y
  · subst h
    rw [cellDist_self]
    have e : blockBetween c c (1 : Matrix T T ℂ) y' y' =
        Matrix.diagonal fun p => if c p = y' then 1 else 0 := by
      ext p q
      by_cases hpq : p = q
      · subst hpq
        simp [blockBetween]
      · simp [blockBetween, hpq]
    rw [e, Matrix.l2_opNorm_diagonal]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    split_ifs <;> simp
  · have e : blockBetween c c (1 : Matrix T T ℂ) y' y = 0 := by
      ext p q
      by_cases hpq : p = q
      · subst hpq
        simp only [blockBetween, Matrix.zero_apply]
        rw [if_neg]
        rintro ⟨h2, h3⟩
        exact h (h2.symm.trans h3)
      · simp [blockBetween, hpq]
    rw [e, norm_zero]
    exact (Real.exp_pos _).le
private theorem noiseBlocks_isLocalOnCells {Γ C : Matrix T T ℂ} {M₂ M₃ θ₂ θ₃ : ℝ}
    (hΓ : IsLocalOnCells c c Γ M₂ θ₂ fun _ => 1) (hC : IsLocalOnCells c c C M₃ θ₃ fun _ => 1)
    (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) :
    IsLocalOnCells (Sum.elim c c) (Sum.elim c c)
      (Matrix.fromBlocks (-Γ - C) (-C) (-C) (1 - C)) (4 * (M₂ + M₃ + 1)) (min θ₂ θ₃)
      fun _ => 1 := by
  intro y' y
  obtain ⟨m, hm⟩ : ∃ m, m = Real.exp (-(min θ₂ θ₃ * cellDist y' y)) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact Real.exp_pos _
  have hd := cellDist_nonneg y' y
  have bΓ : ‖blockBetween c c Γ y' y‖ ≤ M₂ * m := by
    refine (hΓ y' y).trans ?_
    rw [mul_one, hm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM₂
    have := mul_le_mul_of_nonneg_right (min_le_left θ₂ θ₃) hd
    linarith
  have bC : ‖blockBetween c c C y' y‖ ≤ M₃ * m := by
    refine (hC y' y).trans ?_
    rw [mul_one, hm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM₃
    have := mul_le_mul_of_nonneg_right (min_le_right θ₂ θ₃) hd
    linarith
  have b1 : ‖blockBetween c c (1 : Matrix T T ℂ) y' y‖ ≤ m := by
    rw [hm]
    exact norm_blockBetween_one_le c y' y
  have e : blockBetween (Sum.elim c c) (Sum.elim c c)
      (Matrix.fromBlocks (-Γ - C) (-C) (-C) (1 - C)) y' y =
      Matrix.fromBlocks (blockBetween c c (-Γ - C) y' y) (blockBetween c c (-C) y' y)
        (blockBetween c c (-C) y' y) (blockBetween c c (1 - C) y' y) := by
    ext (p | p) (q | q) <;> simp [blockBetween] <;> congr
  rw [e, mul_one, ← hm]
  have e1 : blockBetween c c (-Γ - C) y' y =
      -blockBetween c c Γ y' y + -blockBetween c c C y' y := by
    rw [sub_eq_add_neg, blockBetween_add, blockBetween_neg, blockBetween_neg]
  have e2 : blockBetween c c (1 - C) y' y =
      blockBetween c c 1 y' y + -blockBetween c c C y' y := by
    rw [sub_eq_add_neg, blockBetween_add, blockBetween_neg]
  refine (opNorm_fromBlocks_le _ _ _ _).trans ?_
  rw [e1, e2, blockBetween_neg]
  have n1 := norm_add_le (-blockBetween c c Γ y' y) (-blockBetween c c C y' y)
  have n2 := norm_add_le (blockBetween c c (1 : Matrix T T ℂ) y' y) (-blockBetween c c C y' y)
  rw [norm_neg, norm_neg] at n1
  rw [norm_neg] at n2
  rw [norm_neg]
  nlinarith [mul_nonneg hM₂ hm0.le, mul_nonneg hM₃ hm0.le]
private theorem twoSourceBackground_zero_zero (L n k : ℕ) (w : Fin 4 → ℤ) :
    twoSourceBackground L n k w 0 0 = trivialField L n k 0 := by apply _root_.YangMills.SharedProofs.p56412 <;> assumption
end CellBlocks
theorem noiseMatrixAtTrivialLocalInverse_of_local (hBd : LocalMatricesBoundedAndInverseLocal)
    (hNC : FlatNoiseCovariancePositive)
    (hF : FreeInversesLocal)
    (hA : BackgroundMeansAreLocal) :
    NoiseMatrixAtTrivialLocalInverse := by
  intro a ha L hL
  obtain ⟨M₁, θ₁, hM₁, hθ₁, hF'⟩ := hF L hL
  obtain ⟨M₂, θ₂, hM₂, hθ₂, hA'⟩ := hA a ha L hL
  obtain ⟨hb, hinv⟩ := hBd
  obtain ⟨S₁, hS₁, hb₁⟩ := hb θ₁ hθ₁
  obtain ⟨S₂, hS₂, hb₂⟩ := hb θ₂ hθ₂
  obtain ⟨M₃, θ₃, hM₃, hθ₃, hi₃⟩ := hinv M₁ θ₁ 1 hM₁ hθ₁ one_pos
  obtain ⟨K, hK⟩ : ∃ K, K = blockInvBound (S₁ * M₁) (S₂ * M₂) + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by
    have hc : 0 ≤ S₁ * M₁ := by positivity
    have hg : 0 ≤ S₂ * M₂ := by positivity
    have hE : 0 ≤ schurInvBound (S₁ * M₁) (S₂ * M₂) := by
      unfold schurInvBound
      positivity
    rw [hK]
    unfold blockInvBound
    positivity
  obtain ⟨M, θ, hM, hθ, hi⟩ := hinv (4 * (M₂ + M₃ + 1)) (min θ₂ θ₃) K (by positivity)
    (lt_min hθ₂ hθ₃) hK0
  refine ⟨M, θ, hM, hθ, fun k hk => ?_⟩
  obtain ⟨n₁, h₁⟩ := hF' k hk
  obtain ⟨n₂, h₂⟩ := hA' k hk
  refine ⟨max n₁ n₂, fun n hn hn0 => ?_⟩
  intro _ _ _ _ _ _ _ _
  obtain ⟨hXu, -, -, -, hCu, hCl, -⟩ := h₁ n (le_of_max_le_left hn) hn0
  have hGl := (h₂ n (le_of_max_le_right hn) hn0 0).2.2.2.2.value_local
  have hXi : IsUnit (Matrix.det (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Xi)) := by
    have e : xiConjugated L n k 0 0 0 = periodicEdgeResolventSqrt L n k *
        Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Xi *
          periodicEdgeResolventSqrt L n k := by
      rw [xiConjugated, twoSourceBackground_zero_zero]
    rw [e, Matrix.det_mul, Matrix.det_mul] at hXu
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hXu)
  have hGl' : IsLocalOnCells edgeCell edgeCell
      (Matrix.of (noiseCovariance a L n k (trivialField L n k 0) k)) M₂ θ₂ fun _ => 1 := by
    have e : noiseAlong a L n k 0 0 0 =
        Matrix.of (noiseCovariance a L n k (trivialField L n k 0) k) := by
      rw [noiseAlong, twoSourceBackground_zero_zero]
    rwa [e] at hGl
  obtain ⟨hQ, hGp, hCX⟩ := hNC a ha L hL k n hk hn0
  obtain ⟨hC0, hC1⟩ := hCX hXi
  obtain ⟨C, hC⟩ : ∃ C, C = topCovariance (trivialField L n k 0) := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = Matrix.of (noiseCovariance a L n k (trivialField L n k 0) k) :=
    ⟨_, rfl⟩
  rw [← hC] at hCu hCl hC0 hC1
  rw [← hΓ] at hGl' hGp
  have hN : noiseBlockMatrix a (trivialField L n k 0) =
      Matrix.fromBlocks (-Γ - C) (-C) (-C) (1 - C) := by
    rw [noiseBlockMatrix, meanQTranspose, hQ, hC, hΓ]
    rfl
  rw [hN]
  have hCn : ‖C‖ ≤ 1 := opNorm_le_one_of_posSemidef_of_le_one hC0 hC1
  have hCin : ‖C⁻¹‖ ≤ S₁ * M₁ := hb₁ L n k _ _ _ _ _ _ hL hn0 hM₁.le hCl
  have hΓn : ‖Γ‖ ≤ S₂ * M₂ := hb₂ L n k _ _ _ _ _ _ hL hn0 hM₂.le hGl'
  have hCloc : IsLocalOnCells edgeCell edgeCell C M₃ θ₃ fun _ => 1 := by
    have hu' : IsUnit (Matrix.det C⁻¹) := by
      rw [Matrix.det_nonsing_inv]
      exact (Ring.inverse_unit hCu.unit ▸ hCu.unit⁻¹.isUnit)
    have h := hi₃ L n k _ edgeCell C⁻¹ hL hn0 hCl hu' (by
      rw [Matrix.nonsing_inv_nonsing_inv C hCu]
      exact hCn)
    rwa [Matrix.nonsing_inv_nonsing_inv C hCu] at h
  obtain ⟨hNu, hNn⟩ := noiseBlocks_isUnit_and_norm_inv_le hC0 hC1 hGp hCu hCin hΓn
  refine ⟨hNu, hi L n k _ doubledEdgeCell _ hL hn0 ?_ hNu (hNn.trans ?_)⟩
  · exact noiseBlocks_isLocalOnCells edgeCell hGl' hCloc hM₂.le hM₃.le
  · rw [hK]
    linarith
end YangMills.Construction.RunningCouplingSlope.NoiseInverse
end
