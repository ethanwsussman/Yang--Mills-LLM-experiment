import YangMills.Construction.RunningCouplingSlope.GhostOfTheSoftChainIsTheMixedGhostProof
import YangMills.Construction.RunningCouplingSlope.SaddleDeterminantInCoordinates
import YangMills.Construction.RunningCouplingSlope.SoftSaddleIsTheMixedSaddle
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainHasABoundedInverseAtOneProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Matrix Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace SaddleSchur
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
section Blocks
variable {I T J : Type} [Fintype I] [Fintype T] [Fintype J] [DecidableEq I] [DecidableEq T]
  [DecidableEq J]
private theorem det_fromBlocks_scaled (x y x' y' : ℂ) (A : Matrix I I ℂ) (B : Matrix I T ℂ)
    (C : Matrix T I ℂ) (D : Matrix T T ℂ) :
    det (fromBlocks ((x * x') • A) ((x * y') • B) ((y * x') • C) ((y * y') • D)) =
      x ^ Fintype.card I * y ^ Fintype.card T * det (fromBlocks A B C D) *
        (x' ^ Fintype.card I * y' ^ Fintype.card T) := by apply _root_.YangMills.SharedProofs.p77281 <;> assumption
private theorem det_schur_diagonal (X' : Matrix I I ℂ) (Mq : Matrix T I ℂ) (Mn : Matrix T J ℂ)
    (d : J → ℂ) (hd : ∀ j, d j ≠ 0) :
    det (fromBlocks (fromBlocks X' 0 0 (diagonal d)) (fromCols Mq Mn).transpose (fromCols Mq Mn)
      (0 : Matrix T T ℂ)) =
      (∏ j, d j) * det (fromBlocks X' Mq.transpose Mq
        (-(Mn * diagonal (fun j => (d j)⁻¹) * Mn.transpose))) := by
  have hA : det (diagonal d) ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hd j
  have hinv : (diagonal d)⁻¹ = diagonal fun j => (d j)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal]
    have : (fun j => d j * (d j)⁻¹) = fun _ => (1 : ℂ) := by
      funext j
      exact mul_inv_cancel₀ (hd j)
    rw [this, diagonal_one]
  let _ : Invertible (diagonal d) := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.2 hA)
  let e : (I ⊕ J) ⊕ T ≃ J ⊕ (I ⊕ T) :=
    { toFun := fun x => match x with
        | .inl (.inl i) => .inr (.inl i)
        | .inl (.inr j) => .inl j
        | .inr t => .inr (.inr t)
      invFun := fun x => match x with
        | .inl j => .inl (.inr j)
        | .inr (.inl i) => .inl (.inl i)
        | .inr (.inr t) => .inr t
      left_inv := by rintro ((i | j) | t) <;> rfl
      right_inv := by rintro (j | i | t) <;> rfl }
  have e1 : fromBlocks (fromBlocks X' 0 0 (diagonal d)) (fromCols Mq Mn).transpose (fromCols Mq Mn)
      (0 : Matrix T T ℂ) = (fromBlocks (diagonal d) (fromCols 0 Mn.transpose) (fromRows 0 Mn)
        (fromBlocks X' Mq.transpose Mq 0)).submatrix e e := by
    ext x y
    rcases x with (i | j) | t <;> rcases y with (i' | j') | t' <;> simp [e]
  rw [e1, det_submatrix_equiv_self, det_fromBlocks₁₁, invOf_eq_nonsing_inv, hinv, det_diagonal]
  congr 2
  ext x y
  rcases x with i | t <;> rcases y with i' | t' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type]
end Blocks
private theorem pauliCoeff_smul_add {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (z : ℂ) (a : Fin 3) : pauliCoeff a (z • X + Y) = z * pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.pauliCoeff_smul_add <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem halfTrace_mul_self {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.halfTrace (X * X) = ∑ a, pauliCoeff a X * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p101009 <;> assumption
variable {L n k j : ℕ}
private theorem ofPauliCoeffs_pauliCoeffs
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {B : Edge L n k j → Matrices.ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    (edgePauliCoordinates L n k j).ofCoeffs ((edgePauliCoordinates L n k j).coeffs B) = B := by apply _root_.YangMills.SharedProofs.p21342 <;> assumption
private theorem toPauliCoeffs_smul_add {A B : Edge L n k j → Matrices.ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n k j) (hB : B ∈ complexEdgeForms L n k j) (z : ℂ)
    (t : Fin 3 × PositiveEdge L n k j) :
    toPauliCoeffs (restrictToPositiveEdges (z • A + B)) t =
      z * toPauliCoeffs (restrictToPositiveEdges A) t + toPauliCoeffs (restrictToPositiveEdges B) t :=
  pauliCoeff_smul_add (hA.1 _ t.2.2) (hB.1 _ t.2.2) z t.1
private theorem toPauliCoeffs_zero (t : Fin 3 × PositiveEdge L n k j) :
    toPauliCoeffs (restrictToPositiveEdges (0 : Edge L n k j → Matrices.ComplexMatrix2)) t = 0 :=
  pauliCoeff_zero t.1
private theorem tangentForms_of_noise_zero (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (ξ : LevelForms L n k) (h : ∀ i, ξ.2 i = 0) (j : ℕ) :
    tangentForms U ξ j = meanCovariant U j ξ.1 := by apply _root_.YangMills.SharedProofs.p88273 <;> assumption
private theorem eq_of_symmetric_form {E K : Type} [AddCommGroup E] [Module ℝ E] [Fintype K]
    (Φ : E ≃ₗ[ℝ] (K → ℝ)) (S S' : E →ₗ[ℝ] E)
    (hS : ∀ x y, ∑ κ, Φ x κ * Φ (S y) κ = ∑ κ, Φ (S x) κ * Φ y κ)
    (hS' : ∀ x y, ∑ κ, Φ x κ * Φ (S' y) κ = ∑ κ, Φ (S' x) κ * Φ y κ)
    (hq : ∀ x, ∑ κ, Φ x κ * Φ (S x) κ = ∑ κ, Φ x κ * Φ (S' x) κ) : S = S' := by
  have hpol : ∀ (R : E →ₗ[ℝ] E), (∀ x y, ∑ κ, Φ x κ * Φ (R y) κ = ∑ κ, Φ (R x) κ * Φ y κ) →
      ∀ x y, 2 * ∑ κ, Φ x κ * Φ (R y) κ = ∑ κ, Φ (x + y) κ * Φ (R (x + y)) κ -
        ∑ κ, Φ x κ * Φ (R x) κ - ∑ κ, Φ y κ * Φ (R y) κ := by
    intro R hR x y
    have h1 : ∑ κ, Φ y κ * Φ (R x) κ = ∑ κ, Φ x κ * Φ (R y) κ := by
      rw [hR y x]
      exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
    simp only [map_add, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    rw [h1]
    ring
  have hxy : ∀ x y, ∑ κ, Φ x κ * Φ (S y) κ = ∑ κ, Φ x κ * Φ (S' y) κ := by
    intro x y
    have h1 := hpol S hS x y
    have h2 := hpol S' hS' x y
    rw [hq, hq x, hq y] at h1
    linarith
  refine LinearMap.ext fun y => Φ.injective ?_
  have h3 := hxy (S y - S' y) y
  have h4 : ∑ κ, Φ (S y - S' y) κ * Φ (S y - S' y) κ = 0 := by
    simp only [map_sub, Pi.sub_apply]
    simp only [map_sub, Pi.sub_apply] at h3
    rw [← sub_eq_zero] at h3
    rw [← h3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun κ _ => by ring
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun κ _ => mul_self_nonneg _).1 h4
  funext κ
  have h6 := mul_self_eq_zero.1 (h5 κ (Finset.mem_univ κ))
  simp only [map_sub, Pi.sub_apply] at h6
  linarith
private theorem traceFinsumPairing_zero_left {ι : Type*} (f : ι → Matrices.ComplexMatrix2) :
    traceFinsumPairing (0 : ι → Matrices.ComplexMatrix2) f = 0 := by
  simp [traceFinsumPairing, Matrices.ComplexMatrix2.halfTrace]
end SaddleSchur
open SaddleSchur YangMills.Construction.Tower YangMills.Construction.PeriodicOperators in
theorem quietSaddleDet_eq_saddleMatrixDet
    (h₁ : SaddleDetInOrthonormalCoords) (h₂ : PauliCoordsOrthonormal)
    (h₃ : BackgroundHessianMatrix) (h₄ : ShiftedGaugeMapAtQuietPoint)
    (h₅ : NoiseCovarianceAsPlainChainSum) (h₆ : MeanKernelsRepresent)
    (h₇ : ChainActionHessianAtQuiet) (h₈ : MeanDerivOnForms.Claim)
    (h₉ : MeanIteratesTendToOne)
    (h₁₀ : YangMills.Construction.Tower.RealQuadraticTransposes.Statement)
    (h₁₁ : YangMills.Construction.Tower.FiniteSideFormSpaces) :
    QuietSaddleDetEqSaddleMatrixDet := by
  intro a ha L hL k n hk hn _ _ _ _ _ _ _ _
  classical
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨by omega⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hX : ∀ i, i ≤ k → ∀ b : Edge L n k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun i hi b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have hfinB : ∀ j, Finite (PositiveEdge L n k j) := fun j => by
    have : Finite (Edge L n k j) := PeriodicLattice.instFiniteBond _
    exact Subtype.finite
  let _ : ∀ j, Fintype (PositiveEdge L n k j) := fun j => @Fintype.ofFinite _ (hfinB j)
  obtain ⟨Ψ₀, hΨ₀, hp₀⟩ := (h₂ L n k 0 hL hn (Nat.zero_le _)).1
  obtain ⟨ΨT, hΨT, hpT⟩ := (h₂ L n k k hL hn le_rfl).1
  have hc : ∀ i : Fin k, ∃ Ψ : edgeFormSpace L n k (i + 1) ≃ₗ[ℝ]
      (Fin 3 × PositiveEdge L n k (i + 1) → ℝ),
      (∀ (f : edgeFormSpace L n k (i + 1)) ι, toPauliCoeffs (restrictToPositiveEdges
        (f : Edge L n k (i + 1) → Matrices.ComplexMatrix2)) ι = ((Ψ f ι : ℝ) : ℂ)) ∧
      ∀ f g : edgeFormSpace L n k (i + 1), edgeFormPairing
        (f : Edge L n k (i + 1) → Matrices.ComplexMatrix2)
        (g : Edge L n k (i + 1) → Matrices.ComplexMatrix2) = ((∑ ι, Ψ f ι * Ψ g ι : ℝ) : ℂ) :=
    fun i => (h₂ L n k (i + 1) hL hn i.2).1
  choose Ψ hΨ hp using hc
  let Φ : LevelForms L n k ≃ₗ[ℝ]
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ) :=
    { toFun := fun ξ => Sum.elim (Ψ₀ ξ.1) fun κ => Ψ κ.1 (ξ.2 κ.1) κ.2
      map_add' := fun ξ ξ' => by
        funext κ
        rcases κ with ι | κ <;> simp
      map_smul' := fun r ξ => by
        funext κ
        rcases κ with ι | κ <;> simp
      invFun := fun y => (Ψ₀.symm fun ι => y (.inl ι), fun i => (Ψ i).symm fun ι => y (.inr ⟨i, ι⟩))
      left_inv := fun ξ => by
        refine Prod.ext ?_ (funext fun i => ?_)
        · exact Ψ₀.symm_apply_apply ξ.1
        · exact (Ψ i).symm_apply_apply (ξ.2 i)
      right_inv := fun y => by
        funext κ
        rcases κ with ι | ⟨i, ι⟩ <;> simp }
  have hΦl : ∀ ξ ι, Φ ξ (.inl ι) = Ψ₀ ξ.1 ι := fun _ _ => rfl
  have hΦr : ∀ ξ κ, Φ ξ (.inr κ) = Ψ κ.1 (ξ.2 κ.1) κ.2 := fun _ _ => rfl
  have hchain : ∀ ξ ξ' : LevelForms L n k, levelPairing (formValues ξ) (formValues ξ') =
      ∑ κ, Φ ξ κ * Φ ξ' κ := by
    intro ξ ξ'
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [levelPairing, formValues, hΦl, hΦr]
    congr 1
    · rw [hp₀]
      exact Complex.ofReal_re _
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp i]
      exact Complex.ofReal_re _
  let core : InnerProductSpace.Core ℝ (LevelForms L n k) :=
    { inner := fun ξ ξ' => ∑ κ, Φ ξ κ * Φ ξ' κ
      conj_inner_symm := fun ξ ξ' => by
        simp only [conj_trivial]
        exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
      re_inner_nonneg := fun ξ => by
        simp only [RCLike.re_to_real]
        exact Finset.sum_nonneg fun κ _ => mul_self_nonneg _
      add_left := fun ξ ξ' ξ'' => by
        simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      smul_left := fun ξ ξ' r => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, conj_trivial, Finset.mul_sum, mul_assoc]
      definite := fun ξ h => by
        have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun κ _ => mul_self_nonneg _).1 h
        apply Φ.injective
        funext κ
        simpa using h5 κ (Finset.mem_univ κ) }
  have hEc : LevelFormsEuclidean L n k :=
    ⟨Module.Finite.equiv Φ.symm, core, fun ξ ξ' => (hchain ξ ξ').symm⟩
  have hEk : EdgeFormsEuclidean L n k k := by
    obtain ⟨-, hf, -, c, hc⟩ := h₁₁ L n k k hL hn le_rfl
    refine ⟨hf, c, fun B B' => ?_⟩
    rw [hc]
    simp
  have hE : LevelFormsEuclidean L n k ∧ EdgeFormsEuclidean L n k k := ⟨hEc, hEk⟩
  haveI := hE.1.1
  haveI := hE.2.1
  set η : ℝ := finestMesh L k with hη
  have heta : 0 < η := zpow_pos hLpos _
  have hetaC : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have htop : meshAt L k k = 1 := by
    change (L : ℝ) ^ ((k : ℤ) - (k : ℤ)) = 1
    simp
  refine ⟨a ^ Fintype.card (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) *
    (η ^ 2) ^ Fintype.card (Fin 3 × PositiveEdge L n k 0), by positivity, ?_⟩
  have hev : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : Matrices.ComplexMatrix2)),
      ∀ i ∈ Finset.range k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
        meanRadius (meanIterate U i) c = (((meanRadius (meanIterate U i) c).re : ℝ) : ℂ) ∧
          0 < (meanRadius (meanIterate U i) c).re := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    filter_upwards [(h₉ L hL k n hn i hik.le).eventually (h₈ L hL n k i hn hik)] with U f c hc
    exact ⟨(f.2.1 c hc).1, (f.2.1 c hc).2.1⟩
  have e₃ := h₃ L hL k n hk hn
  have e₄ := h₄ L hL k n hk hn
  have e₅ := h₅ a ha L hL k n hk hn
  have e₆ := h₆ L hL k n hk hn
  have e₇ := h₇ a L hL k n hn
  have e₉ := (h₁₀ L n k hL hn hk).2
  unfold EventuallyNearIdentity at e₃ e₄ e₅ e₆ e₇ e₉ ⊢
  filter_upwards [e₃, e₄, e₅, e₆, e₇, e₉, hev] with U f₃ f₄ f₅ f₆ f₇ f₉ f₈
  set p := rescaledOperators L n k U with hp
  have hptop : p.coarse = 1 := htop
  have hpη : p.eta = η := rfl
  set X := quietPoint U with hXdef
  let r : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ := fun κ =>
    (meanRadius (meanIterate U κ.1) κ.2.2.1).re
  have hr : ∀ κ, 0 < r κ := fun κ =>
    (f₈ κ.1 (Finset.mem_range.2 κ.1.2) κ.2.2.1 κ.2.2.2).2
  let d : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ := fun κ => a * r κ
  have hd : ∀ κ, 0 < d κ := fun κ => mul_pos ha (hr κ)
  obtain ⟨T₁, hT₁, -⟩ := f₉.2.2.existsUnique_hessian 0 0
  have hXop : IsBackgroundHessian U 0 0 (backgroundHessian U 0 0) :=
    Classical.epsilon_spec (p := IsBackgroundHessian U 0 0) ⟨T₁, hT₁⟩
  set Xop := backgroundHessian U 0 0 with hXopdef
  let A : (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ) →ₗ[ℝ]
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ) :=
    { toFun := fun y => Sum.elim (Ψ₀ (Xop (Ψ₀.symm fun ι => y (.inl ι)))) fun κ => d κ * y (.inr κ)
      map_add' := fun y y' => by
        funext κ
        rcases κ with ι | κ
        · have : (fun ι => (y + y') (.inl ι)) = (fun ι => y (.inl ι)) + fun ι => y' (.inl ι) := rfl
          change Ψ₀ (Xop (Ψ₀.symm fun ι => (y + y') (.inl ι))) ι =
            Ψ₀ (Xop (Ψ₀.symm fun ι => y (.inl ι))) ι + Ψ₀ (Xop (Ψ₀.symm fun ι => y' (.inl ι))) ι
          rw [this, map_add, map_add, map_add]
          rfl
        · simp only [Sum.elim_inr, Pi.add_apply, mul_add]
      map_smul' := fun c y => by
        funext κ
        rcases κ with ι | κ
        · have : (fun ι => (c • y) (.inl ι)) = c • fun ι => y (.inl ι) := rfl
          change Ψ₀ (Xop (Ψ₀.symm fun ι => (c • y) (.inl ι))) ι =
            c • Ψ₀ (Xop (Ψ₀.symm fun ι => y (.inl ι))) ι
          rw [this, map_smul, map_smul, map_smul]
          rfl
        · simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
  let T₀ : LevelForms L n k →ₗ[ℝ] LevelForms L n k :=
    Φ.symm.toLinearMap ∘ₗ A ∘ₗ Φ.toLinearMap
  have hT₀ : ∀ ξ, Φ (T₀ ξ) = A (Φ ξ) := fun ξ => by simp [T₀]
  have hT₀l : ∀ ξ ι, Φ (T₀ ξ) (.inl ι) = Ψ₀ (Xop ξ.1) ι := by
    intro ξ ι
    rw [hT₀]
    change Ψ₀ (Xop (Ψ₀.symm fun ι => Ψ₀ ξ.1 ι)) ι = _
    simp
  have hT₀r : ∀ ξ κ, Φ (T₀ ξ) (.inr κ) = d κ * Φ ξ (.inr κ) := by
    intro ξ κ
    rw [hT₀]
    rfl
  have hsym₀ : ∀ B B' : edgeFormSpace L n k 0,
      ∑ ι, Ψ₀ B ι * Ψ₀ (Xop B') ι = ∑ ι, Ψ₀ (Xop B) ι * Ψ₀ B' ι := by
    intro B B'
    have := hXop.1 B B'
    rw [hp₀, hp₀] at this
    exact Complex.ofReal_injective this
  have hform₀ : ∀ B : edgeFormSpace L n k 0,
      ∑ ι, Ψ₀ B ι * Ψ₀ (Xop B) ι = backgroundHessianForm U 0 0 B := by
    intro B
    have := hXop.2 B
    rw [hp₀] at this
    exact Complex.ofReal_injective this
  have hzeroL : ∀ y : LevelValues L n k, levelPairing (formValues (0 : LevelForms L n k)) y = 0 := by
    intro y
    have h0 : ∀ {i : ℕ} (g : Edge L n k i → Matrices.ComplexMatrix2),
        (edgeFormPairing (0 : Edge L n k i → Matrices.ComplexMatrix2) g).re = 0 := by
      intro i g
      have : edgeFormPairing (0 : Edge L n k i → Matrices.ComplexMatrix2) g = 0 :=
        traceFinsumPairing_zero_left _
      rw [this]
      rfl
    simp only [levelPairing, formValues]
    have e1 : ((0 : LevelForms L n k).1 : Edge L n k 0 → Matrices.ComplexMatrix2) = 0 := rfl
    have e2 : ∀ i : Fin k,
        ((0 : LevelForms L n k).2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) = 0 :=
      fun _ => rfl
    simp only [e1, e2, h0, Finset.sum_const_zero, add_zero]
  have hbq : ∀ B : edgeFormSpace L n k 0, backgroundHessianForm U 0 0 B =
      YangMills.Construction.Tower.leftSecondDeriv (plaquetteAction L n k) U B B +
        traceFinsumNorm (gaugeSliceResidual U B : Vertex L n k 0 → Matrices.ComplexMatrix2) ^ 2 := by
    intro B
    have h1 : sourceQuadraticForm U 0 0 B = 0 := by
      have h0 : ∀ g : Edge L n k 0 → Matrices.ComplexMatrix2,
          (edgeFormPairing (((0 : edgeFormSpace L n k 0)) : Edge L n k 0 → Matrices.ComplexMatrix2)
            g).re = 0 := by
        intro g
        have : edgeFormPairing ((0 : edgeFormSpace L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2)
            g = 0 := traceFinsumPairing_zero_left _
        rw [this]
        rfl
      have h2 : ∀ g : PositiveEdge L n k k → Matrices.ComplexMatrix2,
          (traceFinsumPairing (restrictToPositiveEdges
            ((0 : edgeFormSpace L n k k) : Edge L n k k → Matrices.ComplexMatrix2)) g).re = 0 := by
        intro g
        have : traceFinsumPairing (restrictToPositiveEdges
            ((0 : edgeFormSpace L n k k) : Edge L n k k → Matrices.ComplexMatrix2)) g = 0 :=
          traceFinsumPairing_zero_left _
        rw [this]
        rfl
      simp only [sourceQuadraticForm, h0, h2, mul_zero, add_zero, sub_zero]
    simp only [backgroundHessianForm, h1, add_zero]
  have hmem : ∀ ξ : LevelForms L n k, gaugedRightValue a X 0 0 ξ =
      YangMills.Construction.RunningCouplingSlope.leftSecondDeriv (chainAction a) X ξ ξ +
        traceFinsumNorm (gaugeSliceResidual U ξ.1 : Vertex L n k 0 → Matrices.ComplexMatrix2) ^ 2 := by
    intro ξ
    have h2 : ∀ g : PositiveEdge L n k k → Matrices.ComplexMatrix2,
        (traceFinsumPairing (restrictToPositiveEdges
          ((0 : edgeFormSpace L n k k) : Edge L n k k → Matrices.ComplexMatrix2)) g).re = 0 := by
      intro g
      have : traceFinsumPairing (restrictToPositiveEdges
          ((0 : edgeFormSpace L n k k) : Edge L n k k → Matrices.ComplexMatrix2)) g = 0 :=
        traceFinsumPairing_zero_left _
      rw [this]
      rfl
    simp only [gaugedRightValue, gaugedFormValue, hzeroL, h2, mul_zero, add_zero, sub_zero]
    rfl
  have hnoise : ∀ ξ : LevelForms L n k, a * ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (meanRadius (meanIterate U i) c.1).re *
        (Matrices.ComplexMatrix2.halfTrace
          (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → Matrices.ComplexMatrix2) c.1 *
          ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → Matrices.ComplexMatrix2) c.1)).re =
      ∑ κ, Φ ξ (.inr κ) * (d κ * Φ ξ (.inr κ)) := by
    intro ξ
    rw [Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hsl : ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → Matrices.ComplexMatrix2) c.1 ∈
        Matrices.ComplexMatrix2.traceless :=
      ((ξ.2 i).2.1 c.1 c.2).2
    have hco : ∀ a' : Fin 3, pauliCoeff a'
        (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → Matrices.ComplexMatrix2) c.1) =
        ((Ψ i (ξ.2 i) (a', c) : ℝ) : ℂ) := fun a' => hΨ i (ξ.2 i) (a', c)
    rw [halfTrace_mul_self hsl]
    simp only [hco]
    have e : (∑ a' : Fin 3, ((Ψ i (ξ.2 i) (a', c) : ℝ) : ℂ) * ((Ψ i (ξ.2 i) (a', c) : ℝ) : ℂ)).re =
        ∑ a' : Fin 3, Ψ i (ξ.2 i) (a', c) * Ψ i (ξ.2 i) (a', c) := by
      rw [← Complex.ofReal_re (∑ a' : Fin 3, Ψ i (ξ.2 i) (a', c) * Ψ i (ξ.2 i) (a', c))]
      push_cast
      rfl
    rw [e, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    change a * ((meanRadius (meanIterate U i) c.1).re * _) =
      _ * (a * (meanRadius (meanIterate U i) c.1).re * _)
    rw [hΦr]
    ring
  have hsoft₀ : IsGaugedOperator a X 0 0 T₀ := by
    refine ⟨fun ξ ξ' => ?_, fun ξ => ?_⟩
    · rw [hchain, hchain, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [hT₀l, hT₀r, hΦl]
      rw [hsym₀]
      congr 1
      exact Finset.sum_congr rfl fun κ _ => by ring
    · rw [hchain, Fintype.sum_sum_type, hmem, f₇ ξ, hnoise]
      simp only [hT₀l, hT₀r, hΦl]
      rw [hform₀, hbq]
      ring
  have hsoft : IsGaugedOperator a X 0 0 (gaugedOperator a X 0 0) :=
    Classical.epsilon_spec (p := IsGaugedOperator a X 0 0) ⟨T₀, hsoft₀⟩
  have hTeq : gaugedOperator a X 0 0 = T₀ := by
    refine eq_of_symmetric_form Φ _ _ (fun x y => ?_) (fun x y => ?_) fun x => ?_
    · rw [← hchain, ← hchain]
      exact hsoft.1 x y
    · rw [← hchain, ← hchain]
      exact hsoft₀.1 x y
    · rw [← hchain, ← hchain, hsoft.2 x, hsoft₀.2 x]
  set M := shiftedGaugeMap X with hMdef
  have hMv : ∀ ξ, (M ξ : Edge L n k k → Matrices.ComplexMatrix2) = tangentForms U ξ k :=
    fun ξ => (f₄ ξ).2
  obtain ⟨-, fQ, -, fre, -, -, -⟩ := f₆
  let Qs : Matrix (Fin 3 × PositiveEdge L n k k) (Fin 3 × PositiveEdge L n k 0) ℂ :=
    ((η : ℂ))⁻¹ • Matrix.of (meanKernelQ L n k U)
  let Mn : Matrix (Fin 3 × PositiveEdge L n k k) (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ℂ :=
    fun t κ => ((ΨT (M (Φ.symm (Pi.single (.inr κ) 1))) t : ℝ) : ℂ)
  have hQs : ∀ ι t, ((ΨT (M (Φ.symm (Pi.single (.inl ι) 1))) t : ℝ) : ℂ) = Qs t ι := by
    intro ι t
    set ξ := Φ.symm (Pi.single (.inl ι) 1) with hξ
    have hno : ∀ i, ξ.2 i = 0 := by
      intro i
      change (Ψ i).symm (fun ι' => (Pi.single (.inl ι) (1 : ℝ) :
        (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
          (.inr ⟨i, ι'⟩)) = 0
      have : (fun ι' => (Pi.single (.inl ι) (1 : ℝ) :
        (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
          (.inr ⟨i, ι'⟩)) = 0 := by
        funext ι'
        simp
      rw [this, map_zero]
    have hB : (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) ∈ edgeFormSpace L n k 0 := ξ.1.2
    have hBc : (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) ∈ complexEdgeForms L n k 0 :=
      ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
    have hcoef : ∀ ι', toPauliCoeffs (restrictToPositiveEdges
        (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2)) ι' = if ι' = ι then 1 else 0 := by
      intro ι'
      rw [hΨ₀, ← hΦl, hξ, LinearEquiv.apply_symm_apply]
      by_cases h : ι' = ι
      · rw [if_pos h, h]
        simp
      · simp [h]
    have g := congrFun (fQ (toPauliCoeffs (restrictToPositiveEdges
      (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2)))).2 t
    change applyKernel (meanKernelQ L n k U) (toPauliCoeffs (restrictToPositiveEdges
      (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2))) t = toPauliCoeffs (restrictToPositiveEdges
        (finestMesh L k • meanCovariant U k ((edgePauliCoordinates L n k 0).ofCoeffs
          ((edgePauliCoordinates L n k 0).coeffs (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2))))) t at g
    rw [ofPauliCoeffs_pauliCoeffs (hX 0 (Nat.zero_le _)) hBc] at g
    have hm : meanCovariant U k (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) ∈
        edgeFormSpace L n k k :=
      fre k le_rfl _ hB
    have hmc : meanCovariant U k (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) ∈
        complexEdgeForms L n k k :=
      ⟨fun b hb => (hm.1 b hb).2, hm.2⟩
    have e : finestMesh L k • meanCovariant U k (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) =
        ((η : ℝ) : ℂ) • meanCovariant U k (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) + 0 := by
      rw [add_zero]
      funext b
      exact (Complex.coe_smul _ _).symm
    rw [e, toPauliCoeffs_smul_add hmc (complexEdgeForms L n k k).zero_mem, toPauliCoeffs_zero,
      add_zero] at g
    simp only [applyKernel, tsum_fintype, hcoef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at g
    have hMξ : (M ξ : Edge L n k k → Matrices.ComplexMatrix2) =
        meanCovariant U k (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) := by
      rw [hMv, tangentForms_of_noise_zero U ξ hno]
    change _ = ((η : ℂ))⁻¹ * meanKernelQ L n k U t ι
    rw [g, ← hΨT, hMξ]
    field_simp
  have hMact : ∀ (x : LevelForms L n k) t, ((ΨT (M x) t : ℝ) : ℂ) =
      ∑ κ, (fromCols Qs Mn) t κ * ((Φ x κ : ℝ) : ℂ) := by
    intro x t
    let Lm : (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ)
        →ₗ[ℝ] (Fin 3 × PositiveEdge L n k k → ℝ) :=
      ΨT.toLinearMap ∘ₗ M ∘ₗ Φ.symm.toLinearMap
    have h1 := congrFun (LinearMap.toMatrix'_mulVec Lm (Φ x)) t
    have h2 : Lm (Φ x) t = ΨT (M x) t := by simp [Lm]
    rw [← h2, ← h1]
    simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    congr 1
    rw [LinearMap.toMatrix'_apply]
    rcases κ with ι | κ
    · rw [fromCols_apply_inl, ← hQs]
      rfl
    · rw [fromCols_apply_inr]
      rfl
  let E : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → LevelForms L n k := fun κ =>
    Φ.symm (Pi.single (.inr κ) 1)
  have hE0 : ∀ κ, (E κ).1 = 0 := by
    intro κ
    change Ψ₀.symm (fun ι => (Pi.single (.inr κ) (1 : ℝ) :
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
        (.inl ι)) = 0
    have : (fun ι => (Pi.single (.inr κ) (1 : ℝ) :
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
        (.inl ι)) = 0 := by
      funext ι
      simp
    rw [this, map_zero]
  have hE1 : ∀ κ i, i ≠ κ.1 → (E κ).2 i = 0 := by
    intro κ i hi
    change (Ψ i).symm (fun ι => (Pi.single (.inr κ) (1 : ℝ) :
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
        (.inr ⟨i, ι⟩)) = 0
    have : (fun ι => (Pi.single (.inr κ) (1 : ℝ) :
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
        (.inr ⟨i, ι⟩)) = 0 := by
      funext ι
      refine Pi.single_eq_of_ne (fun h => ?_) _
      exact hi (Sigma.mk.inj (Sum.inr.inj h)).1
    rw [this, map_zero]
  have hE2 : ∀ κ ι, toPauliCoeffs (restrictToPositiveEdges
      (((E κ).2 κ.1 : edgeFormSpace L n k (κ.1 + 1)) : Edge L n k (κ.1 + 1) → Matrices.ComplexMatrix2)) ι =
        if ι = κ.2 then 1 else 0 := by
    rintro ⟨i, ι₀⟩ ι
    rw [hΨ i]
    change (((Φ (E ⟨i, ι₀⟩) (.inr ⟨i, ι⟩) : ℝ)) : ℂ) = _
    simp only [E, LinearEquiv.apply_symm_apply]
    by_cases h : ι = ι₀
    · rw [if_pos h, h]
      simp
    · have h' : (Sum.inr ⟨i, ι⟩ : Fin 3 × PositiveEdge L n k 0 ⊕
          (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))) ≠ .inr ⟨i, ι₀⟩ := by
        intro h2
        exact h (eq_of_heq (Sigma.mk.inj (Sum.inr.inj h2)).2)
      rw [Pi.single_eq_of_ne h', if_neg h]
      simp
  have hΓ := f₅ E hE0 hE1 hE2 k le_rfl
  have hMnco : ∀ κ t, toPauliCoeffs (restrictToPositiveEdges (tangentForms U (E κ) k)) t = Mn t κ := by
    intro κ t
    rw [← hMv]
    exact hΨT _ t
  have hΓm : Matrix.of (noiseCovariance a L n k U k) =
      Mn * diagonal (fun κ => (((d κ : ℝ) : ℂ))⁻¹) * Mn.transpose := by
    ext t t'
    rw [Matrix.of_apply, hΓ t t', finsum_eq_sum_of_fintype, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun κ _ => ?_
    have e : (((a * (meanRadius (meanIterate U κ.1) κ.2.2.1).re)⁻¹ : ℝ) : ℂ) =
        (((d κ : ℝ) : ℂ))⁻¹ := Complex.ofReal_inv _
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, hMnco, hMnco, e]
    ring
  let X' : Matrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × PositiveEdge L n k 0) ℂ :=
    fun ι ι' => ((η ^ 2 : ℝ) : ℂ) * p.X ι ι'
  let Dg : Matrix (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))
      (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ℂ := diagonal fun κ => ((d κ : ℝ) : ℂ)
  have hXact : ∀ (x : LevelForms L n k)
      (κ : Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))),
      ((Φ (gaugedOperator a X 0 0 x) κ : ℝ) : ℂ) = ∑ κ', (fromBlocks X' 0 0 Dg) κ κ' *
          ((Φ x κ' : ℝ) : ℂ) := by
    intro x κ
    rw [hTeq, Fintype.sum_sum_type]
    rcases κ with ι | κ
    · have h₁' : ((Ψ₀ (Xop x.1) ι : ℝ) : ℂ) = ∑ j, X' ι j * ((Φ x (.inl j) : ℝ) : ℂ) := by
        rw [← hΨ₀, f₃ x.1 ι]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΨ₀, hΦl]
      have z : ∀ b, (fromBlocks X' 0 0 Dg) (.inl ι) (.inr b) * ((Φ x (.inr b) : ℝ) : ℂ) = 0 :=
        fun b => by
          change (0 : ℂ) * _ = 0
          exact zero_mul _
      rw [hT₀l, h₁']
      simp only [z, Finset.sum_const_zero, add_zero]
      rfl
    · have z : ∀ b, (fromBlocks X' 0 0 Dg) (.inr κ) (.inl b) * ((Φ x (.inl b) : ℝ) : ℂ) = 0 :=
        fun b => by
          change (0 : ℂ) * _ = 0
          exact zero_mul _
      rw [hT₀r]
      simp only [z, Finset.sum_const_zero, zero_add]
      rw [Finset.sum_eq_single κ (fun b _ hb => by
        change Dg κ b * _ = 0
        rw [show Dg κ b = 0 from diagonal_apply_ne _ (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h)]
      change _ = Dg κ κ * _
      rw [show Dg κ κ = ((d κ : ℝ) : ℂ) from diagonal_apply_eq _ _]
      push_cast
      rfl
  have key := h₁ (LevelForms L n k) (edgeFormSpace L n k k) _ _ hE.1.2.choose hE.2.2.choose Φ ΨT
    (fun x y => by
      have := hE.1.2.choose_spec x y
      rw [this, hchain])
    (fun x y => by
      have := hE.2.2.choose_spec x y
      rw [this, hpT]
      simp)
    (gaugedOperator a X 0 0) M (fromBlocks X' 0 0 Dg) (fromCols Qs Mn) hXact hMact
  have hdC : ∀ κ, (((d κ : ℝ) : ℂ)) ≠ 0 := fun κ => by exact_mod_cast (hd κ).ne'
  have hdn := det_schur_diagonal X' Qs Mn (fun κ => ((d κ : ℝ) : ℂ)) hdC
  have hs : fromBlocks X' Qs.transpose Qs
      (-(Mn * diagonal (fun κ => (((d κ : ℝ) : ℂ))⁻¹) * Mn.transpose)) =
      fromBlocks ((((η : ℂ) ^ 2) * 1) • Matrix.of p.X)
        ((((η : ℂ) ^ 2) * (η : ℂ)) • meanQTranspose L n k U)
        ((((η : ℂ))⁻¹ * 1) • Matrix.of (meanKernelQ L n k U))
        ((((η : ℂ))⁻¹ * (η : ℂ)) • (-Matrix.of (noiseCovariance a L n k U k))) := by
    congr 1
    · ext ι ι'
      simp [X']
    · ext ι t
      have : meanQTranspose L n k U ι t =
          (((meshAt L k k ^ 4 / finestMesh L k ^ 4 : ℝ)) : ℂ) * meanKernelQ L n k U t ι := rfl
      change ((η : ℂ))⁻¹ * meanKernelQ L n k U t ι =
        (((η : ℂ) ^ 2) * (η : ℂ)) * meanQTranspose L n k U ι t
      rw [this, htop, ← hη]
      push_cast
      field_simp
    · simp [Qs]
    · rw [inv_mul_cancel₀ hetaC, one_smul, hΓm]
  have hprod : ‖∏ κ, (((d κ : ℝ) : ℂ))‖ =
      a ^ Fintype.card (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) *
        Real.exp (3 * logRadiusSum X) := by
    have h1 : ‖∏ κ, (((d κ : ℝ) : ℂ))‖ = ∏ κ, d κ := by
      rw [norm_prod]
      exact Finset.prod_congr rfl fun κ _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd κ)]
    have h2 : ∏ κ, d κ =
        a ^ Fintype.card (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) * ∏ κ, r κ := by
      simp only [d]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have h3 : ∏ κ, r κ = Real.exp (3 * logRadiusSum X) := by
      rw [logRadiusSum, Finset.mul_sum, Real.exp_sum, Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [finsum_eq_sum_of_fintype, Fintype.prod_prod_type_right, Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun c _ => ?_
      have hrc : 0 < (meanRadius (levelField X i) c.1).re :=
        (f₈ i (Finset.mem_range.2 i.2) c.1 c.2).2
      have hx : ∀ x : Fin 3, r ⟨i, (x, c)⟩ = (meanRadius (levelField X i) c.1).re := fun _ => rfl
      simp only [hx, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [show (3 : ℝ) * Real.log (meanRadius (levelField X i) c.1).re =
        ((3 : ℕ) : ℝ) * Real.log (meanRadius (levelField X i) c.1).re by norm_num,
        Real.exp_nat_mul, Real.exp_log hrc]
    rw [h1, h2, h3]
  rw [levelSaddleDet, dif_pos hE]
  refine key.trans ?_
  rw [hdn, hs, det_fromBlocks_scaled, norm_mul, hprod]
  have hm : fromBlocks (Matrix.of p.X) (meanQTranspose L n k U) (Matrix.of (meanKernelQ L n k U))
      (-Matrix.of (noiseCovariance a L n k U k)) = saddleMatrix a U := rfl
  rw [hm]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heta,
    one_pow, mul_one, norm_one]
  have h1 : η⁻¹ ^ Fintype.card (Fin 3 × PositiveEdge L n k k) *
      η ^ Fintype.card (Fin 3 × PositiveEdge L n k k) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ heta.ne', one_pow]
  linear_combination (a ^ Fintype.card (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) *
    Real.exp (3 * logRadiusSum X) * (η ^ 2) ^ Fintype.card (Fin 3 × PositiveEdge L n k 0) *
    ‖det (saddleMatrix a U)‖) * h1
end YangMills.Construction.RunningCouplingSlope
end
