import YangMills.Construction.Towers.AssertionsOnTheLinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
open PeriodicOperators (KernelMatrix applyKernel compKernel unitKernel Represents RowFinite
  ApplySummable CompSummable)
namespace RescaledConditions
def linearMapKernel (r r' : PauliComponentsOfSymmetricKernel)
    (T : r.space.complexSubmodule →ₗ[ℂ] r'.space.complexSubmodule) :
    KernelMatrix r.Index r'.Index :=
  open Classical in fun ι' ι =>
    if h : r.ofCoeffs (fun κ => unitKernel r.Index κ ι) ∈ r.space.complexSubmodule then
      r'.coeffs (T ⟨_, h⟩ : r'.space.complexSubmodule) ι' else 0
def TransposeKernelScaling (r r' : PauliComponentsOfSymmetricKernel) (a a' : ℝ) : Prop :=
  ∀ T : r.space.complexSubmodule →ₗ[ℂ] r'.space.complexSubmodule,
    PairedFunctionSpace.PreservesFiniteSupport T →
    ∀ g : r'.space.complexSubmodule,
      ApplySummable (meshTranspose a a' (linearMapKernel r r' T)) (r'.coeffs g) ∧
      applyKernel (meshTranspose a a' (linearMapKernel r r' T)) (r'.coeffs g) =
        (((a' ^ 4 * (a ^ 4)⁻¹ : ℝ)) : ℂ) •
          r.coeffs (PairedFunctionSpace.transposeMap T g : r.space.complexSubmodule)
section Kernels
variable {S₀ B₀ S B : Type}
def complementProj (p : RescaledOperators S₀ B₀ S B) : KernelMatrix (Fin 3 × S₀) (Fin 3 × S₀) :=
  unitKernel (Fin 3 × S₀) - compKernel p.Rt p.R
def gaugeFixedKernel (p : RescaledOperators S₀ B₀ S B) :
    KernelMatrix (Fin 3 × B₀) (Fin 3 × B₀) :=
  p.H + compKernel (compKernel p.D (complementProj p)) p.Dt
def sumDiagScale (x y x' y' : ℂ) (M : KernelMatrix (S ⊕ B) (S ⊕ B)) :
    KernelMatrix (S ⊕ B) (S ⊕ B) :=
  fun ι' ι => Sum.elim (fun _ => x) (fun _ => y) ι' * M ι' ι * Sum.elim (fun _ => x') (fun _ => y') ι
def SaddleScaling (p : RescaledOperators S₀ B₀ S B)
    (forms : KernelMatrix (Fin 3 × B₀ ⊕ Fin 3 × B) (Fin 3 × B₀ ⊕ Fin 3 × B))
    (sites : KernelMatrix (Fin 3 × S₀ ⊕ Fin 3 × S) (Fin 3 × S₀ ⊕ Fin 3 × S)) : Prop :=
  forms = sumDiagScale ((p.eta : ℂ) ^ 2) (p.eta : ℂ)⁻¹ 1 (p.eta : ℂ) p.saddleX ∧
    sites = sumDiagScale ((p.eta : ℂ) ^ 2) 1 1 ((p.eta : ℂ) ^ 2) p.saddleDelta
end Kernels
def GeneralRelations (r₀ b₀ : PauliComponentsOfSymmetricKernel) {S B : Type}
    (p : RescaledOperators r₀.Place b₀.Place S B)
    (Dm : (r₀.space.index → Matrices.ComplexMatrix2) → b₀.space.index → Matrices.ComplexMatrix2)
    (A : (b₀.space.index → Matrices.ComplexMatrix2) → b₀.space.index → Matrices.ComplexMatrix2) :
    Prop :=
  Represents p.Dt ((p.eta : ℂ)⁻¹ • r₀.transposeOnCoeffs b₀ Dm) ∧
  Represents p.H (((p.eta : ℂ) ^ 2)⁻¹ • b₀.mapOnCoeffs b₀ A) ∧
  Represents p.Delta (((p.eta : ℂ) ^ 2)⁻¹ • r₀.mapOnCoeffs r₀ fun l =>
    PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (Dm l)) ∧
  Represents p.K (((p.eta : ℂ) ^ 2)⁻¹ • b₀.mapOnCoeffs b₀ fun B' =>
    A B' + Dm (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm B')) ∧
  CompSummable p.Dt p.D ∧ CompSummable p.D p.Dt
def AverageTransposes (L k : ℕ) (r₀ b₀ r b : PauliComponentsOfSymmetricKernel)
    (p : RescaledOperators r₀.Place b₀.Place r.Place b.Place)
    (Qm : (b₀.space.index → Matrices.ComplexMatrix2) → b.space.index → Matrices.ComplexMatrix2)
    (Rm : (r₀.space.index → Matrices.ComplexMatrix2) → r.space.index → Matrices.ComplexMatrix2) :
    Prop :=
  Represents p.Rt (((L : ℂ) ^ (4 * k)) • r₀.transposeOnCoeffs r Rm) ∧
  Represents p.Qt (((p.eta : ℂ) ^ 3)⁻¹ • b₀.transposeOnCoeffs b Qm) ∧
  CompSummable p.Qt p.Q ∧ CompSummable p.D p.Rt ∧ CompSummable p.R p.Dt
structure CoreRelations (r₀ b₀ r b : PauliComponentsOfSymmetricKernel)
    (p : RescaledOperators r₀.Place b₀.Place r.Place b.Place)
    (Dm : (r₀.space.index → Matrices.ComplexMatrix2) → b₀.space.index → Matrices.ComplexMatrix2)
    (Qm : (b₀.space.index → Matrices.ComplexMatrix2) → b.space.index → Matrices.ComplexMatrix2)
    (Rm : (r₀.space.index → Matrices.ComplexMatrix2) → r.space.index → Matrices.ComplexMatrix2)
    (Wm : (r.space.index → Matrices.ComplexMatrix2) → b.space.index → Matrices.ComplexMatrix2)
    (DW : KernelMatrix (Fin 3 × r.Place) (Fin 3 × b.Place))
    (background : (b₀.space.index → Matrices.ComplexMatrix2) →
      (b₀.space.index → Matrices.ComplexMatrix2) → ℂ) : Prop where
  R_comp_Rt : compKernel p.R p.Rt = unitKernel (Fin 3 × r.Place)
  Q_comp_D : compKernel p.Q p.D = compKernel DW p.R
  background_eq : ∀ b' ∈ b₀.space.complexSubmodule, b₀.space.IsFinitelySupported b' →
    background (p.eta • b') (p.eta • b') =
      PeriodicOperators.wPairing (meshWeight p.eta) (b₀.coeffs b')
        (applyKernel (gaugeFixedKernel p) (b₀.coeffs b'))
  R_represents : Represents p.R (r₀.mapOnCoeffs r Rm)
  Q_represents : Represents p.Q (b₀.mapOnCoeffs b fun B' => p.eta • Qm B')
  D_represents : Represents p.D (r₀.mapOnCoeffs b₀ fun l => (p.eta)⁻¹ • Dm l)
  DW_represents : Represents DW (r.mapOnCoeffs b Wm)
  row_finite : RowFinite p.R ∧ RowFinite p.Q ∧ RowFinite p.D ∧ RowFinite DW ∧
    RowFinite p.Rt ∧ RowFinite p.Dt
  comp_summable : CompSummable p.R p.Rt ∧ CompSummable p.Q p.D ∧ CompSummable DW p.R ∧
    CompSummable p.Rt p.R
  complementProj_row_finite : RowFinite (complementProj p)
  comp_assoc : compKernel (compKernel p.D (complementProj p)) p.Dt =
    compKernel p.D (compKernel (complementProj p) p.Dt)
structure TrivialRelations (r₀ b₀ r b q₀ : PauliComponentsOfSymmetricKernel)
    (p : RescaledOperators r₀.Place b₀.Place r.Place b.Place)
    (site : (r₀.space.index → Matrices.ComplexMatrix2) → b₀.space.index → Matrices.ComplexMatrix2)
    (bond : (b₀.space.index → Matrices.ComplexMatrix2) → q₀.space.index → Matrices.ComplexMatrix2)
    (top : (r.space.index → Matrices.ComplexMatrix2) → b.space.index → Matrices.ComplexMatrix2)
    (Qm : (b₀.space.index → Matrices.ComplexMatrix2) → b.space.index → Matrices.ComplexMatrix2)
    (Rm : (r₀.space.index → Matrices.ComplexMatrix2) → r.space.index → Matrices.ComplexMatrix2) :
    Prop where
  vertex_represents : Represents (r₀.kernel b₀ site) (r₀.mapOnCoeffs b₀ site)
  edge_represents : Represents (b₀.kernel q₀ bond) (b₀.mapOnCoeffs q₀ bond)
  coarse_represents : Represents (r.kernel b top) (r.mapOnCoeffs b top)
  D_eq : p.D = r₀.kernel b₀ site
  Q_represents : Represents p.Q (b₀.mapOnCoeffs b fun B' => p.eta • Qm B')
  R_represents : Represents p.R (r₀.mapOnCoeffs r Rm)
  comp_summable :
    CompSummable p.Q (r₀.kernel b₀ site) ∧ CompSummable (r.kernel b top) p.R ∧
    CompSummable (meshTranspose p.eta p.eta (b₀.kernel q₀ bond)) (b₀.kernel q₀ bond) ∧
    CompSummable (r₀.kernel b₀ site) (meshTranspose p.eta p.eta (r₀.kernel b₀ site)) ∧
    CompSummable (meshTranspose p.eta p.eta (r₀.kernel b₀ site)) (r₀.kernel b₀ site)
  Q_comp_d : compKernel p.Q (r₀.kernel b₀ site) = compKernel (r.kernel b top) p.R
  H_eq : p.H = compKernel (meshTranspose p.eta p.eta (b₀.kernel q₀ bond))
    (b₀.kernel q₀ bond)
  K_eq : p.K = compKernel (meshTranspose p.eta p.eta (b₀.kernel q₀ bond))
      (b₀.kernel q₀ bond) +
    compKernel (r₀.kernel b₀ site) (meshTranspose p.eta p.eta (r₀.kernel b₀ site))
  Delta_eq : p.Delta = compKernel (meshTranspose p.eta p.eta (r₀.kernel b₀ site))
    (r₀.kernel b₀ site)
  X_eq : p.X = compKernel (meshTranspose p.eta p.eta (b₀.kernel q₀ bond))
      (b₀.kernel q₀ bond) +
    compKernel (compKernel (r₀.kernel b₀ site) (complementProj p))
      (meshTranspose p.eta p.eta (r₀.kernel b₀ site))
section Periodic
open TrivialLinearization (baseVerticesOfCube)
def levelRestriction (L n k j : ℕ) : Fin 3 → PauliComponentsOfSymmetricKernel
  | 0 => vertexCoordinate (Vertex L n k j)
  | 1 => edgePauliCoordinates L n k j
  | 2 => vertexCoordinate (Face L n k j)
def crossingIncidences (L n k : ℕ) (c : Edge L n k k) : Set (Vertex L n k 0 × Edge L n k 0) :=
  {q | q.1 ∈ baseVerticesOfCube L n k k c.source ∧ q.2 ∈ PeriodicLattice.crossingPath c q.1}
def TrivialStep (L n k i : ℕ) : Prop :=
  PeriodicLattice.complexBlockAverageStep i (trivialField L n k i) =
      trivialField L n k (i + 1) ∧
  (∀ (y : Vertex L n k (i + 1)),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
    PeriodicLattice.complexMeanContourHolonomy (trivialField L n k i) y x = 1) ∧
  smoothingStep L n k i (trivialField L n k i) = trivialField L n k (i + 1) ∧
  (∀ (y : Vertex L n k (i + 1)),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
    PeriodicLattice.meanContourHolonomy (trivialField L n k i) y x = 1) ∧
  (∀ B ∈ (edgePairedSpace L n k i).complexSubmodule,
    complexSmoothingDeriv (trivialField L n k i) B = linearSmoothing L n k i B ∧
    contourLogDrift (trivialField L n k i) B = cubeContourAverage L n k i B ∧
    covariantSmoothingDeriv (trivialField L n k i) B = crossingSmoothing L n k i B) ∧
  ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k i),
    adjointCubeAverage (trivialField L n k i) l = vertexSmoothing L n k i l
def TrivialAverages (L n k : ℕ) : Prop :=
  (∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k 0), ∀ y : Vertex L n k k,
    ofPauliCoeffs (applyKernel (rescaledOperators L n k (trivialField L n k 0)).R
        (toPauliCoeffs l)) y =
      (finestMesh L k ^ 4) • ∑ᶠ x ∈ baseVerticesOfCube L n k k y, l x) ∧
  (∀ y : Vertex L n k k, ((baseVerticesOfCube L n k k y).ncard : ℝ) = (finestMesh L k ^ 4)⁻¹) ∧
  (∀ b' ∈ (edgePairedSpace L n k 0).complexSubmodule, ∀ c : PositiveEdge L n k k,
    ofPauliCoeffs (applyKernel (rescaledOperators L n k (trivialField L n k 0)).Q
        (toPauliCoeffs (restrictToPositiveEdges b'))) c =
      (finestMesh L k ^ 5) • ∑ᶠ q ∈ crossingIncidences L n k c.1, b' q.2) ∧
  ∀ c : PositiveEdge L n k k,
    ((crossingIncidences L n k c.1).ncard : ℝ) = (finestMesh L k ^ 5)⁻¹
def OnTorus (L n k : ℕ) : Prop :=
  (∀ (i i' : Fin 3) (j j' : ℕ), j ≤ k → j' ≤ k →
    TransposeKernelScaling (levelRestriction L n k j i) (levelRestriction L n k j' i')
      (meshAt L k j) (meshAt L k j')) ∧
  (∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
    GeneralRelations (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
      (rescaledOperators L n k U) (covDiff U) (complexHessianOperator U)) ∧
  (∀ U ∈ smallIterateFields L n k,
    AverageTransposes L k (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
      (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k) (rescaledOperators L n k U)
      (iterCovariantDeriv L n k U k) (iterAdjointCubeAverage L n k U k) ∧
    CoreRelations (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
      (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k) (rescaledOperators L n k U)
      (covDiff U) (iterCovariantDeriv L n k U k)
      (iterAdjointCubeAverage L n k U k)
      (covDiff (PeriodicLattice.complexBlockFieldAtLevel k U))
      (covDiffKernel L n k k (PeriodicLattice.complexBlockFieldAtLevel k U))
      (backgroundForm L n k U) ∧
    SaddleScaling (rescaledOperators L n k U) (backgroundSaddle L n k U)
      (laplacianSaddle L n k U)) ∧
  trivialField L n k 0 ∈ smallIterateFields L n k ∧
  (∀ i < k, TrivialStep L n k i) ∧
  TrivialRelations (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
    (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k) (vertexCoordinate (Face L n k 0))
    (rescaledOperators L n k (trivialField L n k 0)) scaledVertexCoboundary
    scaledEdgeCoboundary scaledVertexCoboundary (crossingSmoothingIter L n k k)
    (vertexSmoothingIter L n k k) ∧
  TrivialAverages L n k
def BackgroundFormMatchesHessian (L n k : ℕ) : Prop :=
  EventuallyNearIdentity (fieldSpace L n k 0) fun U => ∀ B : edgeFormSpace L n k 0,
    backgroundForm L n k U B B = ((backgroundHessianForm U 0 0 B : ℝ) : ℂ)
end Periodic
end RescaledConditions
namespace FullSpace
namespace RescaledConditions
open YangMills.Construction.Tower.RescaledConditions (TransposeKernelScaling GeneralRelations
  AverageTransposes CoreRelations SaddleScaling TrivialRelations)
open YangMills.Construction.Tower.FullSpace.TrivialLinearization (baseVerticesOfCube)
def levelRestriction (L k j : ℕ) : Fin 3 → PauliComponentsOfSymmetricKernel
  | 0 => vertexCoordinate (Vertex L k j)
  | 1 => edgePauliCoordinates L k j
  | 2 => vertexCoordinate (Face L k j)
def crossingIncidences (L k : ℕ) (c : Edge L k k) : Set (Vertex L k 0 × Edge L k 0) :=
  {q | q.1 ∈ baseVerticesOfCube L k k c.initial ∧ q.2 ∈ crossingPath c q.1}
def TrivialStep (L k i : ℕ) : Prop :=
  smoothingMap L k i (fun _ => 1) = (fun _ => 1) ∧
  (∀ (y : Vertex L k (i + 1)), ∀ x ∈ cubeVertices L (meshAt L k i) y,
    complexContourMean L (fun _ => 1) y x = 1) ∧
  (∀ B ∈ (edgePairedSpace (meshAt L k i)).complexSubmodule,
    complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) B =
      linearSmoothing (a := meshAt L k (i + 1)) L B ∧
    contourLogDrift (L := L) (k := k) (j := i) (fun _ => 1) B =
      cubeContourAverage (a := meshAt L k (i + 1)) L B ∧
    covariantSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) B =
      crossingSmoothing (a := meshAt L k (i + 1)) L B) ∧
  ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i),
    adjointCubeAverage (L := L) (k := k) (j := i) (fun _ => 1) l =
      vertexSmoothing (a := meshAt L k (i + 1)) L l
def TrivialAverages (L k : ℕ) : Prop :=
  (∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k 0), ∀ y : Vertex L k k,
    ofPauliCoeffs (applyKernel (rescaledOperators L k fun _ => 1).R (toPauliCoeffs l)) y =
      (finestMesh L k ^ 4) • ∑ᶠ x ∈ baseVerticesOfCube L k k y, l x) ∧
  (∀ y : Vertex L k k, ((baseVerticesOfCube L k k y).ncard : ℝ) = (finestMesh L k ^ 4)⁻¹) ∧
  (∀ b' ∈ (edgePairedSpace (meshAt L k 0)).complexSubmodule, ∀ c : PositiveEdge (meshAt L k k),
    ofPauliCoeffs (applyKernel (rescaledOperators L k fun _ => 1).Q
        (toPauliCoeffs (restrictToPositiveEdges b'))) c =
      (finestMesh L k ^ 5) • ∑ᶠ q ∈ crossingIncidences L k c.1, b' q.2) ∧
  ∀ c : PositiveEdge (meshAt L k k),
    ((crossingIncidences L k c.1).ncard : ℝ) = (finestMesh L k ^ 5)⁻¹
def OnFullSpace (L k : ℕ) : Prop :=
  (∀ (i i' : Fin 3) (j j' : ℕ), j ≤ k → j' ≤ k →
    TransposeKernelScaling (levelRestriction L k j i) (levelRestriction L k j' i')
      (meshAt L k j) (meshAt L k j')) ∧
  (∀ U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
    GeneralRelations (vertexCoordinate (Vertex L k 0))
      (edgePauliCoordinates L k 0) (rescaledOperators L k U) (covDiff U)
      (complexHessianOperator U)) ∧
  (∀ U ∈ smallIterateFields L k,
    AverageTransposes L k (vertexCoordinate (Vertex L k 0))
      (edgePauliCoordinates L k 0) (vertexCoordinate (Vertex L k k))
      (edgePauliCoordinates L k k) (rescaledOperators L k U)
      (iterCovariantDeriv L k U k) (iterAdjointCubeAverage L k U k) ∧
    CoreRelations (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
      (vertexCoordinate (Vertex L k k)) (edgePauliCoordinates L k k) (rescaledOperators L k U)
      (covDiff U) (iterCovariantDeriv L k U k)
      (iterAdjointCubeAverage L k U k) (covDiff (complexIter L k k U))
      (covDiffKernel L k k (complexIter L k k U))
      (backgroundForm L k U) ∧
    SaddleScaling (rescaledOperators L k U) (backgroundSaddle L k U)
      (laplacianSaddle L k U)) ∧
  (fun _ => 1) ∈ smallIterateFields L k ∧
  (∀ i < k, TrivialStep L k i) ∧
  TrivialRelations (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
    (vertexCoordinate (Vertex L k k)) (edgePauliCoordinates L k k)
    (vertexCoordinate (Face L k 0)) (rescaledOperators L k fun _ => 1) scaledVertexCoboundary
    scaledEdgeCoboundary scaledVertexCoboundary (crossingSmoothingIter L k k)
    (vertexSmoothingIter L k k) ∧
  TrivialAverages L k
end RescaledConditions
end FullSpace
end Tower
end YangMills.Construction
end
