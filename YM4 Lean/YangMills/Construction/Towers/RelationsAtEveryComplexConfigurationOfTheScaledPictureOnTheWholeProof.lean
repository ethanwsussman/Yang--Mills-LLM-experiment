import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations
open Matrices
open PeriodicOperators
open Tower.HessianKernel (IsSymmBilinearOn finiteSupportComplexForms)
open Tower.RescaledConditions (GeneralRelations)
open Tower.ScalarMultipleKernels (CoeffsRealHomogeneous)
section Kernels
variable {N N' : Type}
theorem applySummable_of_rowFinite {T : KernelMatrix N N'} (hT : RowFinite T) (f : N → ℂ) :
    ApplySummable T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applySummable_of_rowFinite <;> assumption
theorem rowFinite_smul {T : KernelMatrix N N'} (hT : RowFinite T) (z : ℂ) :
    RowFinite (z • T) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.rowFinite_smul <;> assumption
theorem rowFinite_add {T T' : KernelMatrix N N'} (hT : RowFinite T) (hT' : RowFinite T') :
    RowFinite (T + T') := fun i' =>
  ((hT i').union (hT' i')).subset fun i h => by
    by_contra hc
    have h₁ : T i' i = 0 := by
      by_contra e
      exact hc (Or.inl e)
    have h₂ : T' i' i = 0 := by
      by_contra e
      exact hc (Or.inr e)
    exact h (by simp [h₁, h₂])
theorem applyKernel_smul_kernel (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel (z • T) f = z • applyKernel T f := by
  funext i'
  simp only [applyKernel, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left
theorem applyKernel_smul (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
theorem applyKernel_add_kernel {T T' : KernelMatrix N N'} {f : N → ℂ} (hT : ApplySummable T f)
    (hT' : ApplySummable T' f) :
    applyKernel (T + T') f = applyKernel T f + applyKernel T' f := by
  funext i'
  simp only [applyKernel, Pi.add_apply, add_mul]
  exact Summable.tsum_add (Summable.of_norm (hT i')) (Summable.of_norm (hT' i'))
end Kernels
theorem transposeOfValues_mem {S S' : PairedFunctionSpace}
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    (g : S'.index → ComplexMatrix2) :
    PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule := by
  by_cases h : g ∈ S'.complexSubmodule
  · rw [PairedFunctionSpace.transposeOfValues, dif_pos h]
    exact Subtype.property _
  · rw [PairedFunctionSpace.transposeOfValues, dif_neg h]
    exact S.complexSubmodule.zero_mem
theorem generalRelations_of_bases (products : RowFiniteKernels.ApplyComp)
    (r₀ b₀ : PauliComponentsOfSymmetricKernel) {S B : Type} (p : RescaledOperators r₀.Place b₀.Place S B)
    (Dm : (r₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2)
    (A : (b₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2)
    (Dk : PauliComponentsOfSymmetricKernel.HasLocalKernel r₀ b₀ Dm)
    (hD : p.D = (p.eta : ℂ)⁻¹ • r₀.kernel b₀ Dm)
    (hDt : p.Dt = (p.eta : ℂ)⁻¹ • swapKernel (r₀.kernel b₀ Dm))
    (Hk : KernelMatrix (Fin 3 × b₀.Place) (Fin 3 × b₀.Place))
    (hH : p.H = ((p.eta : ℂ) ^ 2)⁻¹ • Hk) (hHr : RowFinite Hk)
    (hA : ∀ f, b₀.coeffs (A (b₀.ofCoeffs f)) = applyKernel Hk f)
    (hAm : ∀ f, A (b₀.ofCoeffs f) ∈ b₀.space.complexSubmodule)
    (mem₀ : ∀ c, r₀.ofCoeffs c ∈ r₀.space.complexSubmodule)
    (right₀ : ∀ l ∈ r₀.space.complexSubmodule, r₀.ofCoeffs (r₀.coeffs l) = l)
    (right₁ : ∀ B' ∈ b₀.space.complexSubmodule, b₀.ofCoeffs (b₀.coeffs B') = B')
    (add₁ : ∀ B' ∈ b₀.space.complexSubmodule, ∀ B'' ∈ b₀.space.complexSubmodule,
      b₀.coeffs (B' + B'') = b₀.coeffs B' + b₀.coeffs B'')
    (hDm : ∀ l ∈ r₀.space.complexSubmodule, Dm l ∈ b₀.space.complexSubmodule) :
    GeneralRelations r₀ b₀ p Dm A := by
  have hz : ((p.eta : ℂ) ^ 2)⁻¹ = (p.eta : ℂ)⁻¹ * (p.eta : ℂ)⁻¹ := by
    rw [pow_two, mul_inv]
  have gD : Represents p.D ((p.eta : ℂ)⁻¹ • r₀.mapOnCoeffs b₀ Dm) := by
    rw [hD]
    exact Dk.smul_represents _
  have gDt : Represents p.Dt ((p.eta : ℂ)⁻¹ • r₀.transposeOnCoeffs b₀ Dm) := by
    rw [hDt]
    exact Dk.smul_swap_represents _
  have rD : RowFinite p.D := by
    rw [hD]
    exact Dk.smul_row_finite _
  have rDt : RowFinite p.Dt := by
    rw [hDt]
    exact Dk.smul_swap_row_finite _
  have rH : RowFinite p.H := by
    rw [hH]
    exact rowFinite_smul hHr _
  have P₁ := (products _ _ p.D rD).2 _ p.Dt rDt
  have P₂ := (products _ _ p.Dt rDt).2 _ p.D rD
  have map_smul' : ∀ (z : ℂ) g, r₀.mapOnCoeffs b₀ Dm (z • g) = z • r₀.mapOnCoeffs b₀ Dm g :=
    fun z g => by
      rw [← (Dk.represents _).2, ← (Dk.represents _).2, applyKernel_smul]
  have transpose_smul' : ∀ (z : ℂ) g,
      r₀.transposeOnCoeffs b₀ Dm (z • g) = z • r₀.transposeOnCoeffs b₀ Dm g := fun z g => by
    rw [← (Dk.swap_represents _).2, ← (Dk.swap_represents _).2, applyKernel_smul]
  refine ⟨gDt, fun f => ⟨applySummable_of_rowFinite rH f, ?_⟩, fun f => ⟨(P₁.2.2 f).1, ?_⟩,
    fun f => ⟨applySummable_of_rowFinite (rowFinite_add rH P₂.2.1) f, ?_⟩, P₁.1, P₂.1⟩
  · rw [hH, applyKernel_smul_kernel, ← hA]
    rfl
  · have key : r₀.transposeOnCoeffs b₀ Dm (r₀.mapOnCoeffs b₀ Dm f) =
        r₀.mapOnCoeffs r₀ (fun l =>
          PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (Dm l)) f := by
      show r₀.coeffs (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm
        (b₀.ofCoeffs (b₀.coeffs (Dm (r₀.ofCoeffs f))))) = _
      rw [right₁ _ (hDm _ (mem₀ f))]
      rfl
    have e : applyKernel p.Delta f = applyKernel (compKernel p.Dt p.D) f := rfl
    rw [e, (P₁.2.2 f).2.2, (gD f).2, (gDt _).2, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
      transpose_smul', key, smul_smul, hz]
  · have key : r₀.mapOnCoeffs b₀ Dm (r₀.transposeOnCoeffs b₀ Dm f) =
        b₀.coeffs (Dm (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm
          (b₀.ofCoeffs f))) := by
      show b₀.coeffs (Dm (r₀.ofCoeffs (r₀.coeffs
        (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (b₀.ofCoeffs f))))) = _
      rw [right₀ _ (transposeOfValues_mem _ _)]
    have e : applyKernel p.K f = applyKernel (p.H + compKernel p.D p.Dt) f := rfl
    have e' : (((p.eta : ℂ) ^ 2)⁻¹ • b₀.mapOnCoeffs b₀ fun B' =>
        A B' + Dm (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm B')) f =
        ((p.eta : ℂ) ^ 2)⁻¹ • b₀.coeffs (A (b₀.ofCoeffs f) +
          Dm (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (b₀.ofCoeffs f))) := rfl
    rw [e, e', add₁ _ (hAm f) _ (hDm _ (transposeOfValues_mem _ _)),
      applyKernel_add_kernel (applySummable_of_rowFinite rH f) (P₂.2.2 f).1, (P₂.2.2 f).2.2,
      (gDt f).2, (gD _).2, hH, applyKernel_smul_kernel, hA, Pi.smul_apply, Pi.smul_apply,
      map_smul', key, smul_smul, ← hz, smul_add]
section Coefficients
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem sum_smul_pauliFamily_mem (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_real_smul (r : ℝ) (a : Fin 3) (X : ComplexMatrix2) :
    pauliCoeff a (r • X) = (r : ℂ) * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.IterTransposesOnTorus.pauliCoeff_real_smul <;> assumption
end Coefficients
section Forms
variable {a : ℝ}
def extendFromCoeffs (c : Fin 3 × PositiveEdge a → ℂ) : InfiniteLattice.Link a → ComplexMatrix2 :=
  open Classical in
  extendOddly fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
theorem xor_isPositivelyOriented (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) : extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem extendFromCoeffs_apply (c : Fin 3 × PositiveEdge a → ℂ) (b : PositiveEdge a) :
    extendFromCoeffs c b.1 = ofPauliCoeffs c b := by
  classical
  simp only [extendFromCoeffs, extendOddly, if_pos b.2, dif_pos b.2]
theorem toPauliCoeffs_extendFromCoeffs (c : Fin 3 × PositiveEdge a → ℂ) :
    toPauliCoeffs (restrictToPositiveEdges (extendFromCoeffs c)) = c := by
  funext i
  show pauliCoeff i.1 (extendFromCoeffs c i.2.1) = c i
  rw [extendFromCoeffs_apply]
  exact pauliCoeff_sum_smul (fun e => c (e, i.2)) i.1
theorem extendFromCoeffs_mem (ha : 0 < a) (c : Fin 3 × PositiveEdge a → ℂ) :
    extendFromCoeffs c ∈ complexEdgeForms a := by
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite ha _ b⟩
  have e := extendFromCoeffs_apply c ⟨b, hb⟩
  have e' : extendFromCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := e
  rw [e']
  exact sum_smul_pauliFamily_mem fun e => c (e, ⟨b, hb⟩)
theorem extendFromCoeffs_toPauliCoeffs (ha : 0 < a) {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) :
    extendFromCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) = B := by
  have hpos : ∀ b (hb : b.IsPositivelyOriented),
      extendFromCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) b = B b := fun b hb =>
    (extendFromCoeffs_apply _ ⟨b, hb⟩).trans (sum_pauliCoeff_smul (hB.1 b hb))
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact hpos b hb
  · have hrb : b.opposite.IsPositivelyOriented := by
      rcases xor_isPositivelyOriented ha b with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hb
      · exact h
    have e := extendOddly_opposite ha (fun b => open Classical in
      if h : b.IsPositivelyOriented then
        ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) ⟨b, h⟩ else 0) b
    have e' : extendFromCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) b.opposite =
        -extendFromCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) b := e
    rw [hpos _ hrb, hB.2 b] at e'
    exact (neg_injective e').symm
theorem toPauliCoeffs_add {B B' : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) (hB' : B' ∈ complexEdgeForms a) :
    toPauliCoeffs (restrictToPositiveEdges (B + B')) =
      toPauliCoeffs (restrictToPositiveEdges B) + toPauliCoeffs (restrictToPositiveEdges B') := by
  funext i
  exact pauliCoeff_add (hB.1 i.2.1 i.2.2) (hB'.1 i.2.1 i.2.2) i.1
theorem covDiff_mem (hA : ComplexMatrix2.ConjugationPreservesTraceless) (ha : 0 < a)
    {U : InfiniteLattice.Link a → ComplexMatrix2} (hU : ∀ b, U b ∈ ComplexMatrix2.unitDeterminant)
    {l : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.tracelessFunctions _) :
    covDiff U l ∈ complexEdgeForms a := by
  classical
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite ha _ b⟩
  have e : covDiff U l b = ComplexMatrix2.conjugateBy (U b) (l b.terminal) - l b.initial :=
    if_pos hb
  rw [e]
  exact ComplexMatrix2.traceless.sub_mem ((hA.2.2 _ (hA.1 _ (hU b))).2.2.2.1 (hl _ (mem_univ _)))
    (hl _ (mem_univ _))
end Forms
section Forms
variable {L k : ℕ}
theorem bilinear_real_smul_smul {α : Type} {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsSymmBilinearOn 𝒮 Q) (h0 : (0 : α → ComplexMatrix2) ∈ 𝒮) (r : ℝ)
    {E E' : α → ComplexMatrix2} (hE : E ∈ 𝒮) (hE' : E' ∈ 𝒮) (hY : (r : ℂ) • E' ∈ 𝒮) :
    Q (r • E) (r • E') = (r : ℂ) * ((r : ℂ) * Q E E') := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.symmBilinear_real_smul_smul <;> assumption
theorem basisForm_mem (ha : 0 < meshAt L k 0) (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    basisForm (L := L) (k := k) (j := 0) a b ∈ complexEdgeForms (meshAt L k 0) := by
  classical
  unfold basisForm
  refine ⟨fun b' hb' => ?_, fun b' => extendOddly_opposite ha _ b'⟩
  simp only [extendOddly, if_pos hb']
  split_ifs
  · exact pauliFamily_mem_traceless a
  · exact ComplexMatrix2.traceless.zero_mem
theorem basisForm_finiteSupport (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    HasFiniteEdgeSupport (basisForm (L := L) (k := k) (j := 0) a b) := by
  classical
  refine (Set.finite_singleton b.1).subset fun b' hb' => ?_
  by_contra hne
  apply hb'.2
  have hne' : b' ≠ b.1 := hne
  simp only [basisForm, extendOddly, if_pos hb'.1, if_neg hne']
theorem zero_mem_finiteSupport :
    (0 : Edge L k 0 → ComplexMatrix2) ∈ finiteSupportComplexForms L k 0 := by
  refine ⟨(complexEdgeForms _).zero_mem, ?_⟩
  refine Set.finite_empty.subset fun b hb => ?_
  exact hb.2 rfl
theorem smul_mem_finiteSupport (z : ℂ) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ finiteSupportComplexForms L k 0) : z • B ∈ finiteSupportComplexForms L k 0 := by
  refine ⟨(complexEdgeForms _).smul_mem z hB.1, hB.2.subset fun b hb => ⟨hb.1, fun h0 => ?_⟩⟩
  apply hb.2
  simp [h0]
end Forms
theorem relations_at_field (h₁ : Tower.ThreeMapKernels.Claim)
    (h₂ : Tower.HessianKernel.KernelProperties)
    (h₃ : Tower.ScalarMultipleKernels.Statement)
    (h₄ : RowFiniteKernels.Claim)
    (h₅ : ComplexMatrix2.ConjugationPreservesTraceless)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {k : ℕ} (hk : 1 ≤ k)
    {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) :
    GeneralRelations (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
      (rescaledOperators L k U) (covDiff U) (complexHessianOperator U) := by
  classical
  have hpos : 0 < meshAt L k 0 := by
    have h0 : (0 : ℝ) < L := by
      have := hL.2
      have : 0 < L := by omega
      exact_mod_cast this
    exact zpow_pos h0 _
  have hη : finestMesh L k ≠ 0 := hpos.ne'
  have hηc : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη
  have A := (h₁ L hL k hk).2
  have Uq := (A.1 0 0 (Nat.zero_le _) (Nat.zero_le _)).2.1
  have Dk := A.2.1 U hU
  have hom : CoeffsRealHomogeneous (edgePauliCoordinates L k 0) := fun z f => by
    funext i
    exact pauliCoeff_real_smul z i.1 _
  obtain ⟨M₁, M₂⟩ := h₃ _ _ _ hom Dk Uq (finestMesh L k)⁻¹ (finestMesh L k) (finestMesh L k)
  obtain ⟨bil, -, standingConstraints, -, -, -⟩ := (h₂ L hL k 0 (Nat.zero_le _)).2 U hU
  have mem : ∀ (a : Fin 3) (b : PositiveEdge (meshAt L k 0)),
      basisForm a b ∈ finiteSupportComplexForms L k 0 := fun a b =>
    ⟨basisForm_mem hpos a b, basisForm_finiteSupport a b⟩
  have hop : ∀ B, complexHessianOperator U B = extendFromCoeffs
      (applyKernel (complexHessianKernel U) (toPauliCoeffs (restrictToPositiveEdges B))) :=
    fun _ => rfl
  refine generalRelations_of_bases h₄.1 _ _ _ _ _ Dk ?_ ?_ (complexHessianKernel U) ?_ standingConstraints
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine M₁.trans ?_
    show (((finestMesh L k)⁻¹ : ℝ) : ℂ) • _ = ((finestMesh L k : ℝ) : ℂ)⁻¹ • _
    rw [Complex.ofReal_inv]
  · have c : (((finestMesh L k)⁻¹ * (finestMesh L k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ) =
        ((finestMesh L k : ℝ) : ℂ)⁻¹ := by
      rw [mul_inv_cancel₀ (pow_ne_zero 4 hη), mul_one, Complex.ofReal_inv]
    exact M₂.trans (congrArg (fun w : ℂ => w • swapKernel
      ((vertexCoordinate (Vertex L k 0)).kernel (edgePauliCoordinates L k 0) (covDiff U))) c)
  · funext i i'
    show (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * complexActionHessian U
        (finestMesh L k • basisForm i.1 i.2) (finestMesh L k • basisForm i'.1 i'.2) =
      (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ * complexActionHessian U
        (basisForm i.1 i.2) (basisForm i'.1 i'.2)
    rw [bilinear_real_smul_smul bil zero_mem_finiteSupport (finestMesh L k) (mem i.1 i.2)
      (mem i'.1 i'.2) (smul_mem_finiteSupport _ (mem i'.1 i'.2))]
    push_cast
    field_simp
  · intro (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ)
    exact (toPauliCoeffs_extendFromCoeffs (applyKernel (complexHessianKernel U)
      (toPauliCoeffs (restrictToPositiveEdges (extendFromCoeffs f))))).trans
        (congrArg (applyKernel (complexHessianKernel U)) (toPauliCoeffs_extendFromCoeffs f))
  · intro f
    show complexHessianOperator U (extendFromCoeffs f) ∈ complexEdgeForms _
    rw [hop]
    exact extendFromCoeffs_mem hpos _
  · intro c i _
    exact sum_smul_pauliFamily_mem fun e => c (e, i)
  · intro l hl
    exact funext fun i => sum_pauliCoeff_smul (hl i (mem_univ i))
  · intro B hB
    exact extendFromCoeffs_toPauliCoeffs hpos hB
  · intro B hB B' hB'
    exact toPauliCoeffs_add hB hB'
  · intro l hl
    exact covDiff_mem h₅ hpos hU.1 hl
theorem statement_holds (h₁ : Tower.ThreeMapKernels.Claim)
    (h₂ : Tower.HessianKernel.KernelProperties)
    (h₃ : Tower.ScalarMultipleKernels.Statement)
    (h₄ : RowFiniteKernels.Claim)
    (h₅ : ComplexMatrix2.ConjugationPreservesTraceless) : Statement := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.relations_at_field <;> assumption
end YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations
end
