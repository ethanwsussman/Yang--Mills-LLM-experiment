import YangMills.Construction.Towers.KernelsOfTheTwoOperatorsAreProductsProof
import YangMills.Construction.Towers.EntriesOfTheConfigurationOfAField
import YangMills.Construction.Towers.KernelsOfTheScaledOperatorsAtEveryComplexConfigurationProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.TheMassiveKernelsUnderTheDilation
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.ScalingKernels
open Matrices
open PeriodicOperators
open PeriodicOperators.ConstantOpFun (addSmulKernel)
open Scaling
open CovDiffTransposes
  (matrixKernel LatticeTransposeData transposeComp compTranspose)
open HessianKernel (IsSymmBilinearOn finiteSupportComplexForms)
section Kernels
variable {N N' : Type}
open Classical in
def basisVector (ι : N) : N → ℂ := fun κ => if κ = ι then 1 else 0
theorem basisVector_equiv (e : N ≃ N') (ι κ : N) : basisVector (e ι) (e κ) = basisVector ι κ := by
  classical
  simp [basisVector]
theorem entry_eq_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (h : Represents T M)
    (ι : N) (ι' : N') : T ι' ι = M (basisVector ι) ι' := by
  classical
  rw [← (h _).2]
  unfold applyKernel
  rw [tsum_eq_single ι]
  · simp [basisVector]
  · intro b hb
    simp [basisVector, hb]
theorem kernelOfMap_eq {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (h : Represents T M) :
    kernelOfMap M = T := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledTrivialRelationsProof.kernelOfMap_eq <;> assumption
end Kernels
section Coefficients
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_real_smul {r : ℝ} (hr : r ≠ 0) (a : Fin 3) (X : ComplexMatrix2) :
    pauliCoeff a (r • X) = (r : ℂ) * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.RescaledKernels.pauliCoeff_real_smul <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem pauliCoeff_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) (a : Fin 3) (x : σ) :
    pauliCoeff a (ofPauliCoeffs c x) = c (a, x) :=
  pauliCoeff_sum_smul (fun b => c (b, x)) a
end Coefficients
section Forms
variable {a : ℝ}
theorem opposite_isPositivelyOriented_of_not {c : InfiniteLattice.Link a}
    (hc : ¬ c.IsPositivelyOriented) : c.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem extendOddly_mem (ha : 0 < a) {g : InfiniteLattice.Link a → ComplexMatrix2}
    (hg : ∀ b, b.IsPositivelyOriented → g b ∈ ComplexMatrix2.traceless) :
    FullSpace.extendOddly g ∈ FullSpace.complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendOddly_mem <;> assumption
end Forms
section Maps
variable {L : ℕ} (hL : 0 < L) (k : ℕ)
abbrev vertexScale : FullSpace.Vertex L k 0 ≃+ FullSpace.Vertex L 0 0 :=
  FullSpace.scaleVertex hL (Nat.zero_le k) 0
abbrev edgeScale : FullSpace.Edge L k 0 ≃ FullSpace.Edge L 0 0 :=
  FullSpace.scaleEdge hL (Nat.zero_le k) 0
abbrev faceScale : FullSpace.Face L k 0 ≃ FullSpace.Face L 0 0 :=
  FullSpace.scaleFace hL (Nat.zero_le k) 0
theorem edgeScale_opposite (b : FullSpace.Edge L k 0) :
    (edgeScale hL k b).opposite = edgeScale hL k b.opposite :=
  InfiniteLattice.Link.ext rfl rfl
theorem vertexScale_add_axisStep (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    vertexScale hL k (x + InfiniteLattice.axisStep (meshAt L k 0) μ) =
      vertexScale hL k x + InfiniteLattice.axisStep (meshAt L 0 0) μ := by
  rw [map_add, FullSpace.scaleVertex_axisStep]
theorem edgeScale_forwardFrom (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    edgeScale hL k (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (vertexScale hL k x) μ :=
  InfiniteLattice.Link.ext rfl (vertexScale_add_axisStep hL k x μ)
def vertexIndexScale : Fin 3 × FullSpace.Vertex L k 0 ≃ Fin 3 × FullSpace.Vertex L 0 0 :=
  (Equiv.refl (Fin 3)).prodCongr (vertexScale hL k).toEquiv
def positiveEdgeScale :
    FullSpace.PositiveEdge (meshAt L k 0) ≃ FullSpace.PositiveEdge (meshAt L 0 0) :=
  scalePosEdge hL k
def edgeIndexScale : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) ≃
    Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) :=
  (Equiv.refl (Fin 3)).prodCongr (positiveEdgeScale hL k)
theorem extendOddly_edgeScale {g : FullSpace.Edge L k 0 → ComplexMatrix2}
    {g' : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → g' (edgeScale hL k b) = g b) (b : FullSpace.Edge L k 0) :
    FullSpace.extendOddly g' (edgeScale hL k b) = FullSpace.extendOddly g b := by
  classical
  by_cases hb : b.IsPositivelyOriented
  · have hb' : (edgeScale hL k b).IsPositivelyOriented :=
      (scaleEdge_isPositivelyOriented_iff hL k b).2 hb
    simp only [FullSpace.extendOddly, if_pos hb', if_pos hb]
    exact h b hb
  · have hb' : ¬ (edgeScale hL k b).IsPositivelyOriented := fun e =>
      hb ((scaleEdge_isPositivelyOriented_iff hL k b).1 e)
    simp only [FullSpace.extendOddly, if_neg hb', if_neg hb]
    rw [edgeScale_opposite, h _ (opposite_isPositivelyOriented_of_not hb)]
theorem ofCoeffs_scaled (g : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ)
    (b : FullSpace.Edge L k 0) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (fun ι => g ((edgeIndexScale hL k).symm ι))
        (edgeScale hL k b) =
      (FullSpace.edgePauliCoordinates L k 0).ofCoeffs g b := by
  classical
  show FullSpace.extendOddly (fun c : FullSpace.Edge L 0 0 => if h : c.IsPositivelyOriented then
        ofPauliCoeffs (fun ι => g ((edgeIndexScale hL k).symm ι)) ⟨c, h⟩ else 0)
        (edgeScale hL k b) =
    FullSpace.extendOddly (fun c : FullSpace.Edge L k 0 => if h : c.IsPositivelyOriented then
        ofPauliCoeffs g ⟨c, h⟩ else 0) b
  refine extendOddly_edgeScale hL k (fun b hb => ?_) b
  have hb' : (edgeScale hL k b).IsPositivelyOriented :=
    (scaleEdge_isPositivelyOriented_iff hL k b).2 hb
  simp only [dif_pos hb, dif_pos hb', ofPauliCoeffs]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : (edgeIndexScale hL k).symm (a, ⟨edgeScale hL k b, hb'⟩) = (a, ⟨b, hb⟩) :=
    (Equiv.symm_apply_eq _).2 rfl
  rw [e]
theorem expTwist_edgeScale {A : FullSpace.Edge L k 0 → ComplexMatrix2}
    {A' : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (h : ∀ b, A' (edgeScale hL k b) = A b) (b : FullSpace.Edge L k 0) :
    FullSpace.expTwist A' (fun _ => 1) (edgeScale hL k b) = FullSpace.expTwist A (fun _ => 1) b := by
  classical
  by_cases hb : b.IsPositivelyOriented
  · have hb' : (edgeScale hL k b).IsPositivelyOriented :=
      (scaleEdge_isPositivelyOriented_iff hL k b).2 hb
    simp only [FullSpace.expTwist, if_pos hb', if_pos hb, h]
  · have hb' : ¬ (edgeScale hL k b).IsPositivelyOriented := fun e =>
      hb ((scaleEdge_isPositivelyOriented_iff hL k b).1 e)
    simp only [FullSpace.expTwist, if_neg hb', if_neg hb, edgeScale_opposite, h]
theorem expField_scaled (g : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ)
    (b : FullSpace.Edge L k 0) :
    FullSpace.expField (fun ι => g ((edgeIndexScale hL k).symm ι)) (edgeScale hL k b) =
      FullSpace.BackgroundJets.gaugeFieldOfForm L k g b :=
  expTwist_edgeScale hL k (ofCoeffs_scaled hL k g) b
theorem covDiff_scaled {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    {U₀ : FullSpace.Edge L 0 0 → ComplexMatrix2} (hU : ∀ b, U₀ (edgeScale hL k b) = U b)
    {l : FullSpace.Vertex L k 0 → ComplexMatrix2} {l₀ : FullSpace.Vertex L 0 0 → ComplexMatrix2}
    (hl : ∀ x, l₀ (vertexScale hL k x) = l x) (b : FullSpace.Edge L k 0) :
    FullSpace.covDiff U₀ l₀ (edgeScale hL k b) = FullSpace.covDiff U l b :=
  extendOddly_edgeScale hL k (fun b _ => by
    show ComplexMatrix2.conjugateBy (U₀ (edgeScale hL k b)) (l₀ (vertexScale hL k b.terminal)) -
      l₀ (vertexScale hL k b.initial) = _
    rw [hU, hl, hl]) b
theorem ofPauliCoeffs_basisVector_scaled (ι : Fin 3 × FullSpace.Vertex L k 0)
    (x : FullSpace.Vertex L k 0) :
    ofPauliCoeffs (basisVector (vertexIndexScale hL k ι)) (vertexScale hL k x) =
      ofPauliCoeffs (basisVector ι) x := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : basisVector (vertexIndexScale hL k ι) (a, vertexScale hL k x) = basisVector ι (a, x) :=
    basisVector_equiv (vertexIndexScale hL k) ι (a, x)
  rw [e]
end Maps
section Difference
variable {L : ℕ}
def covDiffMatrix (k : ℕ) (U : FullSpace.Edge L k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × FullSpace.Vertex L k 0) (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) :=
  matrixKernel (vertexCoordinate (FullSpace.Vertex L k 0)) (FullSpace.edgePauliCoordinates L k 0)
    (FullSpace.covDiff U)
theorem covDiffMatrix_apply (k : ℕ) (U : FullSpace.Edge L k 0 → ComplexMatrix2)
    (ι' : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) (ι : Fin 3 × FullSpace.Vertex L k 0) :
    covDiffMatrix k U ι' ι =
      pauliCoeff ι'.1 (FullSpace.covDiff U (ofPauliCoeffs (basisVector ι)) ι'.2.1) := by
  classical
  show pauliCoeff ι'.1 (FullSpace.covDiff U (ofPauliCoeffs _) ι'.2.1) = _
  refine congrArg (fun l => pauliCoeff ι'.1
    (FullSpace.covDiff U (ofPauliCoeffs l) ι'.2.1)) (funext fun κ => ?_)
  unfold basisVector
  congr
theorem covDiffMatrix_scaled (hL : 0 < L) (k : ℕ) {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    {U₀ : FullSpace.Edge L 0 0 → ComplexMatrix2} (hU : ∀ b, U₀ (edgeScale hL k b) = U b)
    (ι' : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) (ι : Fin 3 × FullSpace.Vertex L k 0) :
    covDiffMatrix 0 U₀ (edgeIndexScale hL k ι') (vertexIndexScale hL k ι) =
      covDiffMatrix k U ι' ι := by
  rw [covDiffMatrix_apply, covDiffMatrix_apply]
  exact congrArg (pauliCoeff ι'.1)
    (covDiff_scaled hL k hU (ofPauliCoeffs_basisVector_scaled hL k ι) ι'.2.1)
theorem rescaled_D_apply {k : ℕ} {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hη : finestMesh L k ≠ 0)
    (h : Represents (FullSpace.rescaledOperators L k U).D
      ((vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k 0)
        fun l => (finestMesh L k)⁻¹ • FullSpace.covDiff U l))
    (ι' : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) (ι : Fin 3 × FullSpace.Vertex L k 0) :
    (FullSpace.rescaledOperators L k U).D ι' ι =
      (((finestMesh L k)⁻¹ : ℝ) : ℂ) * covDiffMatrix k U ι' ι := by
  rw [entry_eq_of_represents h, covDiffMatrix_apply]
  exact pauliCoeff_real_smul (inv_ne_zero hη) ι'.1
    (FullSpace.covDiff U (ofPauliCoeffs (basisVector ι)) ι'.2.1)
end Difference
section Picture
variable {S₀ B₀ S B : Type} (p : RescaledOperators S₀ B₀ S B)
theorem Dt_apply (hη : p.eta ≠ 0) (ι : Fin 3 × B₀) (ι' : Fin 3 × S₀) : p.Dt ι' ι = p.D ι ι' := by
  have h : p.eta ^ 4 / p.eta ^ 4 = 1 := div_self (pow_ne_zero _ hη)
  show (((p.eta ^ 4 / p.eta ^ 4 : ℝ)) : ℂ) * p.D ι ι' = _
  rw [h]
  simp
theorem Delta_apply (hη : p.eta ≠ 0) (ι' ι : Fin 3 × S₀) :
    p.Delta ι' ι = ∑' b, p.D b ι' * p.D b ι := by
  show ∑' b, p.Dt ι' b * p.D b ι = _
  simp only [Dt_apply p hη]
theorem compKernel_D_Dt_apply (hη : p.eta ≠ 0) (ι' ι : Fin 3 × B₀) :
    compKernel p.D p.Dt ι' ι = ∑' x, p.D ι' x * p.D ι x := by
  show ∑' x, p.D ι' x * p.Dt x ι = _
  simp only [Dt_apply p hη]
end Picture
section UnitLattice
variable {L : ℕ}
theorem summable_norm_of_finite_support {N : Type} {g : N → ℂ} (h : {κ | g κ ≠ 0}.Finite) :
    Summable fun κ => ‖g κ‖ := by
  refine summable_of_hasFiniteSupport (h.subset ?_)
  intro κ hκ h0
  apply hκ
  have h0' : g κ = 0 := by simpa using h0
  simp [h0']
theorem edgePauliCoordinates_ofCoeffs_apply (c : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c b.1 = ofPauliCoeffs c b := by
  classical
  show FullSpace.extendOddly (fun c' : FullSpace.Edge L 0 0 => if h : c'.IsPositivelyOriented then
      ofPauliCoeffs c ⟨c', h⟩ else 0) b.1 = _
  simp only [FullSpace.extendOddly, if_pos b.2, dif_pos b.2]
theorem edgePauliCoordinates_ofCoeffs_mem (ha : 0 < meshAt L 0 0)
    (c : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c ∈
      (FullSpace.edgePauliCoordinates L 0 0).space.complexSubmodule := by
  classical
  show FullSpace.extendOddly (fun c' : FullSpace.Edge L 0 0 => if h : c'.IsPositivelyOriented then
      ofPauliCoeffs c ⟨c', h⟩ else 0) ∈ FullSpace.complexEdgeForms (meshAt L 0 0)
  refine extendOddly_mem ha fun b hb => ?_
  simp only [dif_pos hb]
  exact ofPauliCoeffs_mem c _
theorem edgePauliCoordinates_coeffs_ofCoeffs (c : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).coeffs ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_coeffs_ofCoeffs <;> assumption
theorem coeffs_complexHessianOperator (U B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (ι : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0)) :
    (FullSpace.edgePauliCoordinates L 0 0).coeffs (FullSpace.complexHessianOperator U B) ι =
      applyKernel (FullSpace.complexHessianKernel U) ((FullSpace.edgePauliCoordinates L 0 0).coeffs B) ι := by
  classical
  show pauliCoeff ι.1 (FullSpace.complexHessianOperator U B ι.2.1) = _
  simp only [FullSpace.complexHessianOperator, FullSpace.extendOddly, if_pos ι.2.2, dif_pos ι.2.2]
  exact pauliCoeff_ofPauliCoeffs _ ι.1 ι.2
theorem applyKernel_add {N N' : Type} {T S : KernelMatrix N N'} {c : N → ℂ} {κ' : N'}
    (h₁ : Summable fun ι => T κ' ι * c ι) (h₂ : Summable fun ι => S κ' ι * c ι) :
    applyKernel (T + S) c κ' = applyKernel T c κ' + applyKernel S c κ' := by
  unfold applyKernel
  simp only [Pi.add_apply, add_mul]
  exact h₁.tsum_add h₂
theorem of_coeffs_ofCoeffs {r : PauliComponentsOfSymmetricKernel} {c : r.Index → ℂ} (hc : r.coeffs (r.ofCoeffs c) = c)
    {P : (r.Index → ℂ) → Prop} (h : P (r.coeffs (r.ofCoeffs c))) : P c :=
  hc ▸ h
theorem represents_of_isRepresentedBy {r r' : PauliComponentsOfSymmetricKernel}
    {M : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    {K : KernelMatrix r.Index r'.Index}
    (h : CovDiffTransposes.IsRepresentedBy r r' M K)
    (hm : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule) (hc : ∀ c, r.coeffs (r.ofCoeffs c) = c) :
    Represents K (r.mapOnCoeffs r' M) := by
  intro c
  have hg := h _ (hm c)
  rw [hc] at hg
  exact ⟨fun κ' => summable_norm_of_finite_support (hg κ').1, funext fun κ' => (hg κ').2.symm⟩
abbrev TransposeDataAt (U : FullSpace.Edge L 0 0 → ComplexMatrix2) : Prop :=
  LatticeTransposeData (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
    (vertexCoordinate (FullSpace.Face L 0 0)) (FullSpace.covDiff U)
    FullSpace.vertexCoboundary FullSpace.edgeCoboundary
    (FullSpace.complexHessianOperator U) (FullSpace.complexHessianKernel U)
theorem gaugeLaplacianKernel_apply {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (C : TransposeDataAt U) (x' x : Fin 3 × FullSpace.Vertex L 0 0) :
    FullSpace.gaugeLaplacianKernel U x' x =
      ∑' b, covDiffMatrix 0 U b x' * covDiffMatrix 0 U b x := by
  have g : Represents (compKernel (swapKernel (covDiffMatrix 0 U)) (covDiffMatrix 0 U))
      ((vertexCoordinate (FullSpace.Vertex L 0 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
        (FullSpace.gaugeLaplacian U)) :=
    represents_of_isRepresentedBy C.transposeComp_represents.2 (fun c x _ => ofPauliCoeffs_mem c x)
      fun c => funext fun ι => pauliCoeff_ofPauliCoeffs c ι.1 ι.2
  have e : FullSpace.gaugeLaplacianKernel U =
      compKernel (swapKernel (covDiffMatrix 0 U)) (covDiffMatrix 0 U) := kernelOfMap_eq g
  rw [e]
  rfl
theorem massiveHessianKernel_apply (ha : 0 < meshAt L 0 0) {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (C : TransposeDataAt U) (κ' κ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.massiveHessianKernel U κ' κ = FullSpace.complexHessianKernel U κ' κ +
      ∑' x, covDiffMatrix 0 U κ' x * covDiffMatrix 0 U κ x := by
  have gP := represents_of_isRepresentedBy C.compTranspose_represents.2
    (edgePauliCoordinates_ofCoeffs_mem ha) edgePauliCoordinates_coeffs_ofCoeffs
  have g : Represents (FullSpace.complexHessianKernel U +
      compKernel (covDiffMatrix 0 U) (swapKernel (covDiffMatrix 0 U)))
      ((FullSpace.edgePauliCoordinates L 0 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian U)) := by
    intro c
    have hf := edgePauliCoordinates_ofCoeffs_mem ha c
    obtain ⟨h₁, h₂, -⟩ := C.operator_mem _ hf
    obtain ⟨-, h₄⟩ := C.compTranspose_mem _ hf
    have hc := edgePauliCoordinates_coeffs_ofCoeffs c
    have s₁ : ∀ κ', Summable fun ι => ‖FullSpace.complexHessianKernel U κ' ι * c ι‖ := fun κ' =>
      of_coeffs_ofCoeffs hc
        (P := fun c => Summable fun ι => ‖FullSpace.complexHessianKernel U κ' ι * c ι‖) (h₁ κ')
    have s₂ := (gP c).1
    refine ⟨fun κ' => ?_, funext fun κ' => ?_⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ι => ?_) ((s₁ κ').add (s₂ κ'))
      rw [Pi.add_apply, Pi.add_apply, add_mul]
      exact norm_add_le _ _
    · have e₁ : (FullSpace.edgePauliCoordinates L 0 0).coeffs (FullSpace.complexHessianOperator U
          ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c)) κ' =
          applyKernel (FullSpace.complexHessianKernel U) c κ' :=
        of_coeffs_ofCoeffs hc (P := fun d => (FullSpace.edgePauliCoordinates L 0 0).coeffs
          (FullSpace.complexHessianOperator U ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c)) κ' =
            applyKernel (FullSpace.complexHessianKernel U) d κ')
          (coeffs_complexHessianOperator U _ κ')
      have e₂ := congrFun (gP c).2 κ'
      have h₂' : FullSpace.complexHessianOperator U ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c) ∈
        FullSpace.complexEdgeForms (meshAt L 0 0) := h₂
      have h₄' : compTranspose (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
          (FullSpace.covDiff U) ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c) ∈
        FullSpace.complexEdgeForms (meshAt L 0 0) := h₄
      refine (applyKernel_add (s₁ κ').of_norm (s₂ κ').of_norm).trans ?_
      refine Eq.trans ?_ (pauliCoeff_add (h₂'.1 _ κ'.2.2) (h₄'.1 _ κ'.2.2) κ'.1).symm
      exact congrArg₂ (· + ·) e₁.symm e₂
  have e : FullSpace.massiveHessianKernel U = FullSpace.complexHessianKernel U +
      compKernel (covDiffMatrix 0 U) (swapKernel (covDiffMatrix 0 U)) :=
    kernelOfMap_eq g
  rw [e]
  rfl
end UnitLattice
section Action
variable {L : ℕ}
theorem add_mem_finiteSupport {k : ℕ} {B B' : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ finiteSupportComplexForms L k 0) (hB' : B' ∈ finiteSupportComplexForms L k 0) :
    B + B' ∈ finiteSupportComplexForms L k 0 := by
  refine ⟨(FullSpace.complexEdgeForms _).add_mem hB.1 hB'.1,
    (hB.2.union hB'.2).subset fun b hb => ?_⟩
  by_cases h : B b = 0
  · exact Or.inr ⟨hb.1, fun h' => hb.2 (by simp [h, h'])⟩
  · exact Or.inl ⟨hb.1, h⟩
theorem apply_add_add {α : Type} {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsSymmBilinearOn 𝒮 Q) {E E' : α → ComplexMatrix2} (hE : E ∈ 𝒮) (hE' : E' ∈ 𝒮)
    (hS : E + E' ∈ 𝒮) : Q (E + E') (E + E') = Q E E + 2 * Q E E' + Q E' E' := by
  have t := (hQ 1 E hE E' hE' _ hS).1
  have t₁ := (hQ 1 E hE E' hE' E hE).2.1
  have t₂ := (hQ 1 E hE E' hE' E' hE').2.1
  have s := (hQ 0 E hE E hE E' hE').2.2
  simp only [one_smul, one_mul] at t t₁ t₂
  rw [t, t₁, t₂, s]
  ring
theorem apply_real_smul_real_smul {α : Type} {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsSymmBilinearOn 𝒮 Q) (h0 : (0 : α → ComplexMatrix2) ∈ 𝒮) (r : ℝ)
    {E E' : α → ComplexMatrix2}
    (hE : E ∈ 𝒮) (hE' : E' ∈ 𝒮) (hY : (r : ℂ) • E' ∈ 𝒮) :
    Q (r • E) (r • E') = (r : ℂ) * ((r : ℂ) * Q E E') := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.symmBilinear_real_smul_smul <;> assumption
theorem basisForm_mem {k : ℕ} (ha : 0 < meshAt L k 0) (a : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L k 0)) :
    FullSpace.basisForm (L := L) (k := k) (j := 0) a b ∈ finiteSupportComplexForms L k 0 := by
  classical
  refine ⟨extendOddly_mem ha fun b' _ => ?_, ?_⟩
  · split_ifs
    · exact pauliFamily_mem_traceless a
    · exact ComplexMatrix2.traceless.zero_mem
  · refine (Set.finite_singleton b.1).subset fun b' hb' => ?_
    by_contra hne
    apply hb'.2
    have hne' : b' ≠ b.1 := hne
    simp only [FullSpace.basisForm, FullSpace.extendOddly, if_pos hb'.1, if_neg hne']
theorem zero_mem_finiteSupport {k : ℕ} :
    (0 : FullSpace.Edge L k 0 → ComplexMatrix2) ∈ finiteSupportComplexForms L k 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.zero_mem_finiteSupport <;> assumption
theorem smul_mem_finiteSupport {k : ℕ} (z : ℂ) {B : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ finiteSupportComplexForms L k 0) : z • B ∈ finiteSupportComplexForms L k 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.smul_mem_finiteSupport <;> assumption
variable (hL : 0 < L) (k : ℕ)
def pushForward (B : FullSpace.Edge L k 0 → ComplexMatrix2) : FullSpace.Edge L 0 0 → ComplexMatrix2 :=
  fun b => B ((edgeScale hL k).symm b)
theorem pushForward_edgeScale (B : FullSpace.Edge L k 0 → ComplexMatrix2) (b : FullSpace.Edge L k 0) :
    pushForward hL k B (edgeScale hL k b) = B b := by
  simp [pushForward]
theorem pushForward_mem {B : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ finiteSupportComplexForms L k 0) :
    pushForward hL k B ∈ finiteSupportComplexForms L 0 0 := by
  obtain ⟨⟨h, r⟩, hfin⟩ := hB
  refine ⟨⟨fun b hb => ?_, fun b => ?_⟩, ?_⟩
  · obtain ⟨b, rfl⟩ := (edgeScale hL k).surjective b
    rw [pushForward_edgeScale]
    exact h b ((scaleEdge_isPositivelyOriented_iff hL k b).1 hb)
  · obtain ⟨b, rfl⟩ := (edgeScale hL k).surjective b
    rw [edgeScale_opposite, pushForward_edgeScale, pushForward_edgeScale, r]
  · refine (hfin.image (edgeScale hL k)).subset fun b hb => ?_
    obtain ⟨b, rfl⟩ := (edgeScale hL k).surjective b
    refine ⟨b, ⟨(scaleEdge_isPositivelyOriented_iff hL k b).1 hb.1, fun h0 => hb.2 ?_⟩, rfl⟩
    rw [pushForward_edgeScale]
    exact h0
theorem pushForward_basisForm (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L k 0)) :
    pushForward hL k (FullSpace.basisForm (L := L) (k := k) (j := 0) a b) =
      FullSpace.basisForm (L := L) (k := 0) (j := 0) a (positiveEdgeScale hL k b) := by
  classical
  funext c
  obtain ⟨c, rfl⟩ := (edgeScale hL k).surjective c
  rw [pushForward_edgeScale]
  refine (extendOddly_edgeScale hL k (fun c _ => ?_) c).symm
  show (if edgeScale hL k c = edgeScale hL k b.1 then ComplexMatrix2.pauliFamily a else 0) =
    if c = b.1 then ComplexMatrix2.pauliFamily a else 0
  simp only [EmbeddingLike.apply_eq_iff_eq]
theorem faceEdge_scaled (p : FullSpace.Face L k 0) (i : Fin 4) :
    FullSpace.faceEdge (faceScale hL k p) i = edgeScale hL k (FullSpace.faceEdge p i) := by
  have e₁ : ∀ (x : FullSpace.Vertex L k 0) (μ : Fin 4),
      InfiniteLattice.Link.forwardFrom (vertexScale hL k x) μ =
        edgeScale hL k (InfiniteLattice.Link.forwardFrom x μ) := fun x μ =>
    (edgeScale_forwardFrom hL k x μ).symm
  have e₂ : ∀ (x : FullSpace.Vertex L k 0) (μ ν : Fin 4),
      InfiniteLattice.Link.forwardFrom
          (vertexScale hL k x + InfiniteLattice.axisStep (meshAt L 0 0) μ) ν =
        edgeScale hL k (InfiniteLattice.Link.forwardFrom
          (x + InfiniteLattice.axisStep (meshAt L k 0) μ) ν) := fun x μ ν => by
    rw [edgeScale_forwardFrom, vertexScale_add_axisStep]
  fin_cases i
  · exact e₁ _ _
  · exact e₂ _ _ _
  · exact e₂ _ _ _
  · exact e₁ _ _
theorem faceVariable_eq {a : ℝ} (V : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.faceVariable V p = V (FullSpace.faceEdge p 0) * (V (FullSpace.faceEdge p 1) *
      (V (FullSpace.faceEdge p 2).opposite * V (FullSpace.faceEdge p 3).opposite)) := by
  simp [FullSpace.faceVariable, FullSpace.linkHolonomy, FullSpace.faceBoundary,
    FullSpace.faceEdge, FullSpace.faceEdges]
variable {U : FullSpace.Edge L k 0 → ComplexMatrix2} {U₀ : FullSpace.Edge L 0 0 → ComplexMatrix2}
theorem faceVariable_scaled (hU : ∀ b, U₀ (edgeScale hL k b) = U b)
    (p : FullSpace.Face L k 0) :
    FullSpace.faceVariable U₀ (faceScale hL k p) = FullSpace.faceVariable U p := by
  simp only [faceVariable_eq, faceEdge_scaled, edgeScale_opposite, hU]
theorem faceTransports_scaled (hU : ∀ b, U₀ (edgeScale hL k b) = U b)
    (p : FullSpace.Face L k 0) :
    FullSpace.faceTransports U₀ (faceScale hL k p) = FullSpace.faceTransports U p := by
  simp only [FullSpace.faceTransports, faceEdge_scaled, hU,
    faceVariable_scaled hL k hU]
theorem transportedForm_scaled (hU : ∀ b, U₀ (edgeScale hL k b) = U b)
    (B : FullSpace.Edge L k 0 → ComplexMatrix2) (p : FullSpace.Face L k 0) :
    FullSpace.transportedForm U₀ (pushForward hL k B) (faceScale hL k p) =
      FullSpace.transportedForm U B p := by
  funext i
  simp only [FullSpace.transportedForm, faceTransports_scaled hL k hU, faceEdge_scaled,
    pushForward_edgeScale]
theorem complexActionHessian_diag_scaled (h : FaceTermDerivatives.Statement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hU : ∀ b, U₀ (edgeScale hL k b) = U b)
    (hm : U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hm₀ : U₀ ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    {B : FullSpace.Edge L k 0 → ComplexMatrix2} (hB : B ∈ finiteSupportComplexForms L k 0) :
    FullSpace.complexActionHessian U₀ (pushForward hL k B) (pushForward hL k B) =
      FullSpace.complexActionHessian U B B := by
  have hC := pushForward_mem hL k hB
  have e := (((h L hs k 0 (Nat.zero_le k)).2 B hB.1).2 hB.2).1 U hm
  have e₀ := (((h L hs 0 0 le_rfl).2 _ hC.1).2 hC.2).1 U₀ hm₀
  rw [← e.1, ← e₀.1, ← finsum_comp_equiv (faceScale hL k)]
  refine finsum_congr fun p => ?_
  rw [transportedForm_scaled hL k hU, faceVariable_scaled hL k hU]
theorem complexActionHessian_scaled (h : FaceTermDerivatives.Statement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hU : ∀ b, U₀ (edgeScale hL k b) = U b)
    (hm : U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hm₀ : U₀ ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (bil : IsSymmBilinearOn (finiteSupportComplexForms L k 0)
      (FullSpace.complexActionHessian U))
    (bil₀ : IsSymmBilinearOn (finiteSupportComplexForms L 0 0)
      (FullSpace.complexActionHessian U₀))
    {B B' : FullSpace.Edge L k 0 → ComplexMatrix2} (hB : B ∈ finiteSupportComplexForms L k 0)
    (hB' : B' ∈ finiteSupportComplexForms L k 0) :
    FullSpace.complexActionHessian U₀ (pushForward hL k B) (pushForward hL k B') =
      FullSpace.complexActionHessian U B B' := by
  have hC := pushForward_mem hL k hB
  have hC' := pushForward_mem hL k hB'
  have p := apply_add_add bil hB hB' (add_mem_finiteSupport hB hB')
  have p₀ := apply_add_add bil₀ hC hC' (add_mem_finiteSupport hC hC')
  have d := complexActionHessian_diag_scaled hL k h hs hU hm hm₀ hB
  have d' := complexActionHessian_diag_scaled hL k h hs hU hm hm₀ hB'
  have dS := complexActionHessian_diag_scaled hL k h hs hU hm hm₀ (add_mem_finiteSupport hB hB')
  have e : pushForward hL k (B + B') = pushForward hL k B + pushForward hL k B' := rfl
  rw [e, p, p₀, d, d'] at dS
  linear_combination (1 / 2 : ℂ) * dS
theorem complexHessianKernel_scaled (h : FaceTermDerivatives.Statement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hU : ∀ b, U₀ (edgeScale hL k b) = U b)
    (hm : U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hm₀ : U₀ ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup)
    (bil : IsSymmBilinearOn (finiteSupportComplexForms L k 0)
      (FullSpace.complexActionHessian U))
    (bil₀ : IsSymmBilinearOn (finiteSupportComplexForms L 0 0)
      (FullSpace.complexActionHessian U₀))
    (ha : 0 < meshAt L k 0) (ι' ι : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) :
    FullSpace.complexHessianKernel U₀ (edgeIndexScale hL k ι') (edgeIndexScale hL k ι) =
      FullSpace.complexHessianKernel U ι' ι := by
  show FullSpace.complexActionHessian U₀
      (FullSpace.basisForm ι'.1 (positiveEdgeScale hL k ι'.2))
      (FullSpace.basisForm ι.1 (positiveEdgeScale hL k ι.2)) =
    FullSpace.complexActionHessian U (FullSpace.basisForm ι'.1 ι'.2)
      (FullSpace.basisForm ι.1 ι.2)
  rw [← pushForward_basisForm, ← pushForward_basisForm]
  exact complexActionHessian_scaled hL k h hs hU hm hm₀ bil bil₀ (basisForm_mem ha _ _)
    (basisForm_mem ha _ _)
end Action
theorem rescaled_H_apply {L k : ℕ} {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hη : finestMesh L k ≠ 0) (ha : 0 < meshAt L k 0)
    (bil : IsSymmBilinearOn (finiteSupportComplexForms L k 0)
      (FullSpace.complexActionHessian U))
    (ι' ι : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) :
    (FullSpace.rescaledOperators L k U).H ι' ι =
      ((((finestMesh L k : ℝ) : ℂ)) ^ 2)⁻¹ * FullSpace.complexHessianKernel U ι' ι := by
  have hc : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη
  show (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * FullSpace.complexActionHessian U _ _ = _
  rw [apply_real_smul_real_smul bil zero_mem_finiteSupport (finestMesh L k) (basisForm_mem ha _ _)
    (basisForm_mem ha _ _) (smul_mem_finiteSupport _ (basisForm_mem ha _ _))]
  show _ * (_ * (_ * FullSpace.complexHessianKernel U ι' ι)) = _
  push_cast
  field_simp
theorem idKernel_equiv {I I' : PeriodicData} (e : I.Carrier ≃ I'.Carrier) (ι' ι : I.Carrier) :
    idKernel I' (e ι') (e ι) = idKernel I ι' ι := by
  classical
  simp [idKernel]
theorem add_mul_eq_inv_sq_mul {c a b z e e' w : ℂ} (hc : c ≠ 0) (h : a = (c ^ 2)⁻¹ * b)
    (hw : w = c ^ 2 * z) (he : e' = e) : a + z * e = (c ^ 2)⁻¹ * (b + w * e') := by
  subst h hw he
  field_simp
theorem massiveKernelsScale (h₁ : RescaledKernels.KernelsWellFormedEverywhere)
    (h₂ : CovDiffTransposes.Claim)
    (h₃ : HessianKernel.KernelProperties)
    (h₄ : FaceTermDerivatives.Statement)
    (h₅ : FullSpace.GaugeFieldOfFormEntries) : MassiveKernelsScale := by
  intro L hL hs k hk z f
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have ha : 0 < meshAt L k 0 := zpow_pos hL0 _
  have ha₀ : 0 < meshAt L 0 0 := zpow_pos hL0 _
  have hη : finestMesh L k ≠ 0 := ha.ne'
  have hc : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη
  set U : FullSpace.Edge L k 0 → ComplexMatrix2 := FullSpace.BackgroundJets.gaugeFieldOfForm L k f
    with hUdef
  set U₀ : FullSpace.Edge L 0 0 → ComplexMatrix2 := FullSpace.expField (scaledField hL k f)
    with hU₀def
  have hU : ∀ b, U₀ (edgeScale hL k b) = U b := expField_scaled hL k f
  have hm : U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := (h₅ L hs k).1 f
  have hm₀ : U₀ ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
    (h₅ L hs 0).1 (scaledField hL k f)
  have C : TransposeDataAt U₀ := ((h₂ L hs 0 0 le_rfl).2 U₀ hm₀).1
  have gD := ((h₁ L hs k hk).2 U hm).represents
  have hp : (FullSpace.rescaledOperators L k U).eta ≠ 0 := hη
  have bil := ((h₃ L hs k 0 (Nat.zero_le k)).2 U hm).1
  have bil₀ := ((h₃ L hs 0 0 le_rfl).2 U₀ hm₀).1
  have sumVertex : ∀ ι' ι : Fin 3 × FullSpace.Vertex L k 0,
      (FullSpace.rescaledOperators L k U).Delta ι' ι = ((((finestMesh L k : ℝ) : ℂ)) ^ 2)⁻¹ *
        FullSpace.gaugeLaplacianKernel U₀ (vertexIndexScale hL k ι')
          (vertexIndexScale hL k ι) := fun ι' ι => by
    rw [Delta_apply _ hp, gaugeLaplacianKernel_apply C, ← Equiv.tsum_eq (edgeIndexScale hL k),
      ← tsum_mul_left]
    refine tsum_congr fun b => ?_
    rw [rescaled_D_apply hη gD, rescaled_D_apply hη gD, covDiffMatrix_scaled hL k hU,
      covDiffMatrix_scaled hL k hU]
    push_cast
    field_simp
  have sumEdge : ∀ ι' ι : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0),
      (FullSpace.rescaledOperators L k U).K ι' ι = ((((finestMesh L k : ℝ) : ℂ)) ^ 2)⁻¹ *
        FullSpace.massiveHessianKernel U₀ (edgeIndexScale hL k ι')
          (edgeIndexScale hL k ι) := fun ι' ι => by
    have eK : (FullSpace.rescaledOperators L k U).K ι' ι =
        (FullSpace.rescaledOperators L k U).H ι' ι +
        compKernel (FullSpace.rescaledOperators L k U).D
          (FullSpace.rescaledOperators L k U).Dt ι' ι := rfl
    rw [eK, compKernel_D_Dt_apply _ hp, rescaled_H_apply hη ha bil, massiveHessianKernel_apply ha₀ C,
      complexHessianKernel_scaled hL k h₄ hs hU hm hm₀ bil bil₀ ha, mul_add]
    congr 1
    rw [← Equiv.tsum_eq (vertexIndexScale hL k), ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [rescaled_D_apply hη gD, rescaled_D_apply hη gD, covDiffMatrix_scaled hL k hU,
      covDiffMatrix_scaled hL k hU]
    push_cast
    field_simp
  have hz : ((finestMesh L k ^ 2 * z : ℝ) : ℂ) =
      (((finestMesh L k : ℝ) : ℂ)) ^ 2 * (z : ℂ) := by
    push_cast
    ring
  refine ⟨fun ι' ι => ?_, fun ι' ι => ?_⟩
  · exact add_mul_eq_inv_sq_mul hc (sumVertex ι' ι) hz
      (idKernel_equiv (scaleVertexIndex hL k) ι' ι)
  · exact add_mul_eq_inv_sq_mul hc (sumEdge ι' ι) hz
      (idKernel_equiv (scaleEdgeIndex hL k) ι' ι)
end YangMills.Construction.Tower.MassiveOpFunctions.ScalingKernels
end
