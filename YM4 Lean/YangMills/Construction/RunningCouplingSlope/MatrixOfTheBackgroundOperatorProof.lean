import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.MatrixOfTheBackgroundOperator
import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASide
import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescend
import YangMills.Construction.Towers.KernelAlgebraOfTheScaledPicture
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpaces
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnASide
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernel
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.RescaledConditions
private theorem eq_of_symm_of_quadForm_eq {I : Type} [Fintype I] [DecidableEq I] (P Q : I → I → ℂ)
    (hP : ∀ i j, P i j = P j i) (hQ : ∀ i j, Q i j = Q j i)
    (h : ∀ x : I → ℝ, ∑ i, ∑ j, (x i : ℂ) * P i j * (x j : ℂ) =
      ∑ i, ∑ j, (x i : ℂ) * Q i j * (x j : ℂ)) (i j : I) : P i j = Q i j := by
  have c : ∀ (a i' : I), (((Pi.single a (1 : ℝ) : I → ℝ) i' : ℝ) : ℂ) = if i' = a then 1 else 0 := by
    intro a i'
    by_cases h : i' = a
    · subst h
      simp
    · simp [h]
  have form : ∀ (R : I → I → ℂ) (a b : I), ∑ i', ∑ j', (((Pi.single a (1 : ℝ) + Pi.single b (1 : ℝ) : I → ℝ) i' : ℝ) : ℂ) * R i' j' *
      (((Pi.single a (1 : ℝ) + Pi.single b (1 : ℝ) : I → ℝ) j' : ℝ) : ℂ) =
      R a a + R a b + R b a + R b b := by
    intro R a b
    simp only [Pi.add_apply, Complex.ofReal_add, c, add_mul, mul_add, Finset.sum_add_distrib]
    simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
    ring
  have one : ∀ (R : I → I → ℂ) (a : I), ∑ i', ∑ j', (((Pi.single a (1 : ℝ) : I → ℝ) i' : ℝ) : ℂ) * R i' j' *
      (((Pi.single a (1 : ℝ) : I → ℝ) j' : ℝ) : ℂ) = R a a := by
    intro R a
    simp only [c]
    simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
  have hd : ∀ a, P a a = Q a a := fun a => by
    have := h (Pi.single a 1)
    rwa [one, one] at this
  have h2 := h (Pi.single i 1 + Pi.single j 1)
  rw [form, form, hd i, hd j, hP j i, hQ j i] at h2
  have h3 : (2 : ℂ) * P i j = 2 * Q i j := by linear_combination h2
  exact mul_left_cancel₀ two_ne_zero h3
private theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem basisForm_mem_complexEdgeForms {L n k j : ℕ}
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) (a : Fin 3)
    (b : PositiveEdge L n k j) : basisForm a b ∈ complexEdgeForms L n k j := by
  classical
  refine ⟨fun c hc => ?_, fun c => ?_⟩
  · simp only [basisForm, extendOddly, if_pos hc]
    split_ifs
    · exact pauliFamily_mem_traceless a
    · exact Matrices.ComplexMatrix2.traceless.zero_mem
  · simp only [basisForm, extendOddly]
    rcases hX c with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · rw [if_neg hn, if_pos hp, show c.opposite.opposite = c from rfl]
    · rw [if_pos hp, if_neg hn, neg_neg]
theorem backgroundHessianMatrix_holds
    (h₁ : PauliCoordsOrthonormal)
    (h₂ : Tower.RescaledBackgroundFormFiniteSide.Statement)
    (h₃ : Tower.OperatorBlocksDescend.BlocksDescend)
    (h₄ : Tower.RescaledKernelAlgebra.Claim)
    (h₅ : Tower.RealQuadraticTransposes.Statement)
    (h₆ : Tower.RescaledIterRelations)
    (h₇ : Tower.HessianKernel.KernelProperties) :
    BackgroundHessianMatrix := by
  intro L hL k n hk hn _
  classical
  obtain ⟨Ψ, hΨ, hpair⟩ := (h₁ L n k 0 hL hn (Nat.zero_le k)).1
  have e₁ : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : Matrices.ComplexMatrix2)), ∀ B : edgeFormSpace L n k 0,
      backgroundForm L n k U B B = ((backgroundHessianForm U 0 0 B : ℝ) : ℂ) :=
    h₂ L hL k hk n hn
  have e₂ := h₃ L hL k hk n hn
  have e₃ := (h₅ L n k hL hn hk).2
  unfold EventuallyNearIdentity at e₂ e₃ ⊢
  filter_upwards [e₁, e₂, e₃] with U f₁ f₂ f₃
  obtain ⟨hsmall, -⟩ := f₂
  obtain ⟨-, -, hop⟩ := f₃
  have hrel := h₆ L hL k hk n hn U hsmall
  have hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup := hsmall.1
  set p := rescaledOperators L n k U with hp
  have hLpos : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have heta : 0 < p.eta := zpow_pos hLpos _
  have htop : 0 < p.coarse := zpow_pos hLpos _
  have hfinI : Finite (Fin 3 × PositiveEdge L n k 0) := inferInstance
  have cons := h₄ _ _ _ _ p heta htop
    ⟨hrel.row_finite.2.2.1, hrel.row_finite.2.2.2.2.2, hrel.row_finite.1,
      hrel.row_finite.2.2.2.2.1, fun _ => Set.toFinite _⟩ hrel.R_comp_Rt
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hXor : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have hBS := ((h₇ L hL k 0 (Nat.zero_le k)).1 n hn U hU).1
  have hH : ∀ ι ι', p.H ι ι' = p.H ι' ι := by
    intro ι ι'
    have m : ∀ ι : Fin 3 × PositiveEdge L n k 0,
        finestMesh L k • basisForm ι.1 ι.2 ∈ complexEdgeForms L n k 0 := fun ι =>
      Submodule.smul_of_tower_mem _ _ (basisForm_mem_complexEdgeForms hXor ι.1 ι.2)
    have h := (hBS 0 _ (m ι) _ (m ι) _ (m ι')).2.2
    change _ * complexActionHessian U _ _ = _ * complexActionHessian U _ _
    rw [h]
  have hXs : ∀ ι ι', p.X ι ι' = p.X ι' ι := by
    intro ι ι'
    rw [cons.X_eq]
    have := cons.correction_symm ι ι'
    simp only [RescaledKernelAlgebra.gaugeCorrection] at this
    simp only [gaugeFixedKernel, Pi.add_apply, hH ι ι', this]
  obtain ⟨T₀, hT₀, -⟩ := hop.existsUnique_hessian 0 0
  have hT : IsBackgroundHessian U 0 0 (backgroundHessian U 0 0) :=
    Classical.epsilon_spec (p := IsBackgroundHessian U 0 0) ⟨T₀, hT₀⟩
  set Top := backgroundHessian U 0 0 with hTop
  let τ : (Fin 3 × PositiveEdge L n k 0 → ℝ) →ₗ[ℝ] (Fin 3 × PositiveEdge L n k 0 → ℝ) :=
    Ψ.toLinearMap ∘ₗ Top ∘ₗ Ψ.symm.toLinearMap
  let A := LinearMap.toMatrix' τ
  have hτ : ∀ x i, τ x i = ∑ j, A i j * x j := by
    intro x i
    have := congrFun (LinearMap.toMatrix'_mulVec τ x) i
    rw [← this]
    rfl
  have hsumΨ : ∀ (x : Fin 3 × PositiveEdge L n k 0 → ℝ) (y : edgeFormSpace L n k 0),
      edgeFormPairing ((Ψ.symm x : edgeFormSpace L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2)
        (y : Edge L n k 0 → Matrices.ComplexMatrix2) =
        ((∑ i, x i * Ψ y i : ℝ) : ℂ) := by
    intro x y
    rw [hpair]
    simp
  have hAs : ∀ i j, A i j = A j i := by
    intro i j
    have h := hT.1 (Ψ.symm (Pi.single i 1)) (Ψ.symm (Pi.single j 1))
    have l1 := hsumΨ (Pi.single i 1) (Top (Ψ.symm (Pi.single j 1)))
    have r1 := hsumΨ (Pi.single j 1) (Top (Ψ.symm (Pi.single i 1)))
    have sym : ∀ f g : edgeFormSpace L n k 0,
        edgeFormPairing (f : Edge L n k 0 → Matrices.ComplexMatrix2) (g : Edge L n k 0 → Matrices.ComplexMatrix2) =
        edgeFormPairing (g : Edge L n k 0 → Matrices.ComplexMatrix2) (f : Edge L n k 0 → Matrices.ComplexMatrix2) := by
      intro f g
      rw [hpair, hpair]
      simp [mul_comm]
    rw [sym (Top (Ψ.symm (Pi.single i 1))) (Ψ.symm (Pi.single j 1))] at h
    rw [l1, r1] at h
    have h' := Complex.ofReal_injective h
    have e1 := hτ (Pi.single j 1) i
    have e2 := hτ (Pi.single i 1) j
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ite_mul, one_mul, zero_mul] at h' e1 e2
    rw [← e1, ← e2]
    exact h'
  have hform : ∀ x : Fin 3 × PositiveEdge L n k 0 → ℝ,
      ∑ i, ∑ j, ((x i : ℝ) : ℂ) * ((A i j : ℝ) : ℂ) * ((x j : ℝ) : ℂ) =
        ∑ i, ∑ j, ((x i : ℝ) : ℂ) * (((finestMesh L k ^ 2 : ℝ) : ℂ) * p.X i j) *
          ((x j : ℝ) : ℂ) := by
    intro x
    set B : edgeFormSpace L n k 0 := Ψ.symm x with hB
    have q1 := hT.2 B
    have q2 := f₁ B
    have eB : (B : Edge L n k 0 → Matrices.ComplexMatrix2) =
        p.eta • ((Ψ.symm (p.eta⁻¹ • x) : edgeFormSpace L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2) := by
      have : B = p.eta • Ψ.symm (p.eta⁻¹ • x) := by
        rw [hB, ← map_smul, smul_smul, mul_inv_cancel₀ heta.ne', one_smul]
      exact congrArg Subtype.val this
    have hb : ((Ψ.symm (p.eta⁻¹ • x) : edgeFormSpace L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2) ∈
        complexEdgeForms L n k 0 := by
      have f := (Ψ.symm (p.eta⁻¹ • x)).2
      exact ⟨fun b hb => (f.1 b hb).2, f.2⟩
    have hfinB : Finite (PositiveEdge L n k 0) :=
      Finite.of_surjective (Prod.snd : Fin 3 × PositiveEdge L n k 0 → _) Prod.snd_surjective
    have q3 : backgroundForm L n k U B B = PeriodicOperators.wPairing (meshWeight p.eta)
        (toPauliCoeffs (restrictToPositiveEdges
          ((Ψ.symm (p.eta⁻¹ • x) : edgeFormSpace L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2)))
        (applyKernel (gaugeFixedKernel p) (toPauliCoeffs (restrictToPositiveEdges
          ((Ψ.symm (p.eta⁻¹ • x) : edgeFormSpace L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2)))) := by
      rw [eB]
      exact hrel.background_eq _ hb (Set.toFinite _)
    rw [q2, ← q1, hsumΨ] at q3
    have c1 : toPauliCoeffs (restrictToPositiveEdges
        ((Ψ.symm (p.eta⁻¹ • x) : edgeFormSpace L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2)) =
        fun ι => ((p.eta⁻¹ * x ι : ℝ) : ℂ) := by
      funext ι
      have h := hΨ (Ψ.symm (p.eta⁻¹ • x)) ι
      simp only [LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] at h
      exact h
    rw [c1, ← cons.X_eq] at q3
    have l : (((∑ i, x i * Ψ (Top B) i : ℝ)) : ℂ) =
        ∑ i, ∑ j, ((x i : ℝ) : ℂ) * ((A i j : ℝ) : ℂ) * ((x j : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      have : Ψ (Top B) i = ∑ j, A i j * x j := by
        rw [← hτ]
        simp [τ, hB]
      rw [this]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← l, q3]
    simp only [PeriodicOperators.wPairing, applyKernel, meshWeight, tsum_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hne : ((p.eta : ℝ) : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
    have he : finestMesh L k = p.eta := rfl
    rw [he]
    push_cast
    field_simp
  have hAX := eq_of_symm_of_quadForm_eq (fun i j => ((A i j : ℝ) : ℂ))
    (fun i j => ((finestMesh L k ^ 2 : ℝ) : ℂ) * p.X i j)
    (fun i j => by rw [hAs i j]) (fun i j => by rw [hXs i j]) hform
  intro B ι
  rw [hΨ]
  have : Ψ (Top B) ι = ∑ j, A ι j * Ψ B j := by
    rw [← hτ]
    simp [τ]
  rw [this]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hAX ι j, hΨ]
  simp only [Complex.ofReal_pow]
end YangMills.Construction.RunningCouplingSlope
end
