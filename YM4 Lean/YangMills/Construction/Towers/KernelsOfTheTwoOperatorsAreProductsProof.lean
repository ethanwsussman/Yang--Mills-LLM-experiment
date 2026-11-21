import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.KernelsOfTheScaledOperatorsAtEveryComplexConfigurationProof
import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import YangMills.Construction.Towers.TransposesOfTheCovariantDifferenceAndOfTheDifferences
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
namespace Tower
namespace TwoOperatorKernelProducts
open PeriodicOperators (KernelMatrix Represents swapKernel compKernel)
open CovDiffTransposes (matrixKernel)
variable {L : ℕ}
def covDiffKernel (U : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (vertexCoordinate (FullSpace.Vertex L 0 0)).Index (FullSpace.edgePauliCoordinates L 0 0).Index :=
  matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
    (FullSpace.covDiff U)
structure KernelConditions (U : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) : Prop where
  represents_gaugeLaplacian : Represents (FullSpace.gaugeLaplacianKernel U)
    ((vertexCoordinate (FullSpace.Vertex L 0 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
      (FullSpace.gaugeLaplacian U))
  gaugeLaplacianKernel_eq : FullSpace.gaugeLaplacianKernel U =
    compKernel (swapKernel (covDiffKernel U)) (covDiffKernel U)
  represents_massiveHessian : Represents (FullSpace.massiveHessianKernel U)
    ((FullSpace.edgePauliCoordinates L 0 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0)
      (FullSpace.massiveHessian U))
  massiveHessianKernel_eq : ∀ ι' ι, FullSpace.massiveHessianKernel U ι' ι =
    FullSpace.complexHessianKernel U ι' ι +
      compKernel (covDiffKernel U) (swapKernel (covDiffKernel U)) ι' ι
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup, KernelConditions U
end TwoOperatorKernelProducts
end Tower
end YangMills.Construction
end

open Set
noncomputable section
namespace YangMills.Construction.Tower.TwoOperatorKernelProducts
open Matrices
open PeriodicOperators (Represents RowFinite KernelMatrix ApplySummable ApplySummableAt
  applyKernel kernelOfMap compKernel swapKernel)
open CovDiffTransposes (LatticeTransposeData matrixKernel)
section KernelMatrices
variable {N N' N'' : Type}
theorem applyKernel_indicator (T : KernelMatrix N N') (j : N') (i : N) :
    (open Classical in applyKernel T (fun k => if k = i then 1 else 0) j) = T j i := by
  classical
  unfold applyKernel
  rw [tsum_eq_single i]
  · simp
  · intro k hk
    simp [hk]
theorem kernelMatrix_unique_of_represents {M : (N → ℂ) → N' → ℂ} {T T' : KernelMatrix N N'}
    (h : Represents T M) (h' : Represents T' M) : T = T' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.kernelUnique <;> assumption
theorem kernelOfMap_eq {M : (N → ℂ) → N' → ℂ} {T : KernelMatrix N N'} (h : Represents T M) :
    kernelOfMap M = T :=
  kernelMatrix_unique_of_represents (Classical.epsilon_spec (p := fun T => Represents T M) ⟨T, h⟩) h
theorem applySummable_of_rowFinite {T : KernelMatrix N N'} (h : RowFinite T) (f : N → ℂ) :
    ApplySummable T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applySummable_of_rowFinite <;> assumption
theorem rowFinite_compKernel {T : KernelMatrix N' N''} {S : KernelMatrix N N'}
    (hT : RowFinite T) (hS : RowFinite S) : RowFinite (compKernel T S) := by apply _root_.YangMills.Construction.Tower.RescaledKernels.rowFinite_compKernel <;> assumption
theorem applySummable_add {T S : KernelMatrix N N'} {f : N → ℂ} (hT : ApplySummable T f)
    (hS : ApplySummable S f) : ApplySummable (fun j i => T j i + S j i) f := by
  intro j
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) ((hT j).add (hS j))
  rw [add_mul]
  exact norm_add_le _ _
theorem applyKernel_add {T S : KernelMatrix N N'} {f : N → ℂ} (hT : ApplySummable T f)
    (hS : ApplySummable S f) (j : N') :
    applyKernel (fun j i => T j i + S j i) f j =
      applyKernel T f j + applyKernel S f j := by
  have s₁ : Summable fun i => T j i * f i := (hT j).of_norm
  have s₂ : Summable fun i => S j i * f i := (hS j).of_norm
  show ∑' i, (T j i + S j i) * f i = ∑' i, T j i * f i + ∑' i, S j i * f i
  rw [← s₁.tsum_add s₂]
  exact tsum_congr fun i => add_mul _ _ _
end KernelMatrices
section PauliCoefficients
theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
end PauliCoefficients
section Links
open InfiniteLattice
variable {a : ℝ}
theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
end Links
section UnitLattice
variable {L : ℕ}
theorem meshAt_zero_pos (L : ℕ) : 0 < meshAt L 0 0 := by
  simp [meshAt]
theorem vertex_ofCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) :
    (vertexCoordinate σ).ofCoeffs c ∈ (vertexCoordinate σ).space.complexSubmodule :=
  fun i _ => ofPauliCoeffs_mem c i
theorem vertex_coeffs_ofCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    (vertexCoordinate σ).coeffs ((vertexCoordinate σ).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
def positiveValues (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    FullSpace.Edge L 0 0 → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
theorem edge_ofCoeffs_eq (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c = FullSpace.extendOddly (positiveValues c) := rfl
theorem edge_ofCoeffs_apply (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ)
    {b : FullSpace.Edge L 0 0} (hb : b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ :=
  (congrFun (edge_ofCoeffs_eq c) b).trans ((extendOddly_of_positive _ hb).trans (dif_pos hb))
theorem edge_ofCoeffs_mem (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c ∈
      (FullSpace.edgePauliCoordinates L 0 0).space.complexSubmodule := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  swap
  · exact (congrFun (edge_ofCoeffs_eq c) b.opposite).trans
      ((extendOddly_opposite (meshAt_zero_pos L) (positiveValues c) b).trans
        (congrArg Neg.neg (congrFun (edge_ofCoeffs_eq c) b).symm))
  rw [edge_ofCoeffs_apply c hb]
  exact ofPauliCoeffs_mem c _
theorem edge_coeffs_ofCoeffs (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).coeffs ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c) = c := by
  have e : FullSpace.restrictToPositiveEdges ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c) =
      ofPauliCoeffs c :=
    funext fun b => edge_ofCoeffs_apply c b.2
  show toPauliCoeffs (FullSpace.restrictToPositiveEdges _) = c
  rw [e]
  exact toPauliCoeffs_ofPauliCoeffs c
abbrev UnitTransposeData (U : FullSpace.Edge L 0 0 → ComplexMatrix2) : Prop :=
  LatticeTransposeData (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
    (vertexCoordinate (FullSpace.Face L 0 0)) (FullSpace.covDiff U)
    FullSpace.vertexCoboundary FullSpace.edgeCoboundary
    (FullSpace.complexHessianOperator U) (FullSpace.complexHessianKernel U)
theorem compKernel_represents_laplacian {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hC : UnitTransposeData U) :
    Represents (compKernel (swapKernel (covDiffKernel U)) (covDiffKernel U))
      ((vertexCoordinate (FullSpace.Vertex L 0 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
        (FullSpace.gaugeLaplacian U)) := by
  have hrows : RowFinite (compKernel (swapKernel (covDiffKernel U)) (covDiffKernel U)) :=
    rowFinite_compKernel hC.covDiff.column_finite hC.covDiff.row_finite
  refine fun f => ⟨applySummable_of_rowFinite hrows f, funext fun k => ?_⟩
  have e := (hC.transposeComp_represents.2 ((vertexCoordinate (FullSpace.Vertex L 0 0)).ofCoeffs f)
    (vertex_ofCoeffs_mem f) k).2
  have hc : (vertexCoordinate (FullSpace.Vertex L 0 0)).coeffs
      ((vertexCoordinate (FullSpace.Vertex L 0 0)).ofCoeffs f) = f := vertex_coeffs_ofCoeffs f
  rw [hc] at e
  exact e.symm
theorem add_represents_massive {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hC : UnitTransposeData U) :
    Represents (fun j i => FullSpace.complexHessianKernel U j i +
        compKernel (covDiffKernel U) (swapKernel (covDiffKernel U)) j i)
      ((FullSpace.edgePauliCoordinates L 0 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian U)) := by
  have hP : RowFinite (compKernel (covDiffKernel U) (swapKernel (covDiffKernel U))) :=
    rowFinite_compKernel hC.covDiff.row_finite hC.covDiff.column_finite
  intro f
  have hB := edge_ofCoeffs_mem f
  have hc : (FullSpace.edgePauliCoordinates L 0 0).coeffs ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) = f :=
    edge_coeffs_ofCoeffs f
  have hA : ApplySummable (FullSpace.complexHessianKernel U) f := by
    have h := (hC.operator_mem _ hB).1
    rwa [hc] at h
  have hF := applySummable_of_rowFinite hP f
  refine ⟨applySummable_add hA hF, funext fun k => ?_⟩
  refine (applyKernel_add hA hF k).trans ?_
  have e₂ := (hC.compTranspose_represents.2 _ hB k).2
  rw [hc] at e₂
  have e₁ : FullSpace.complexHessianOperator U ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) k.2.1 =
      ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel U) f) k.2 := by
    have e : toPauliCoeffs
        (FullSpace.restrictToPositiveEdges ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f)) = f :=
      edge_coeffs_ofCoeffs f
    have e₀ : FullSpace.complexHessianOperator U ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) k.2.1 =
        ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel U)
          (toPauliCoeffs
            (FullSpace.restrictToPositiveEdges ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f)))) k.2 := by
      show FullSpace.extendOddly _ _ = _
      rw [extendOddly_of_positive _ k.2.2]
      exact dif_pos k.2.2
    rw [e₀, e]
  have m₁ : FullSpace.complexHessianOperator U ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) k.2.1 ∈
      ComplexMatrix2.traceless := by
    rw [e₁]
    exact ofPauliCoeffs_mem _ _
  have m₂ := (hC.compTranspose_mem _ hB).2.1 k.2.1 k.2.2
  have e₃ : pauliCoeff k.1 (FullSpace.complexHessianOperator U
      ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs f) k.2.1) =
      applyKernel (FullSpace.complexHessianKernel U) f k := by
    rw [e₁]
    exact congrFun (toPauliCoeffs_ofPauliCoeffs _) k
  exact (congrArg₂ (· + ·) e₃.symm e₂.symm).trans (pauliCoeff_add k.1 m₁ m₂).symm
end UnitLattice
theorem statement_of_transposes (hX : CovDiffTransposes.Claim) : Statement := by
  intro L hL U hU
  have hC : UnitTransposeData U := ((hX L hL 0 0 le_rfl).2 U hU).1
  have eL : FullSpace.gaugeLaplacianKernel U =
      compKernel (swapKernel (covDiffKernel U)) (covDiffKernel U) :=
    kernelOfMap_eq (compKernel_represents_laplacian hC)
  have eM : FullSpace.massiveHessianKernel U = fun j i => FullSpace.complexHessianKernel U j i +
      compKernel (covDiffKernel U) (swapKernel (covDiffKernel U)) j i :=
    kernelOfMap_eq (add_represents_massive hC)
  refine ⟨?_, eL, ?_, fun j i => congrFun (congrFun eM j) i⟩
  · rw [eL]
    exact compKernel_represents_laplacian hC
  · rw [eM]
    exact add_represents_massive hC
end YangMills.Construction.Tower.TwoOperatorKernelProducts
end
