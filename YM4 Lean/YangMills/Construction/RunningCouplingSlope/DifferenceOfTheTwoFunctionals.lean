import YangMills.Construction.Lattice.SiteCoordinates
import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.CriticalBranchResponse
variable {L n k : ℕ}
def chainMinusBackground (a : ℝ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) : ℝ :=
  chainFreeEnergy a (quietPoint U) 0 0 - Tower.backgroundFunctional U 0 0
def pauliUnitForm (L n k : ℕ) (w : Fin 4 → ℤ) : Tower.Edge L n k k → Matrices.ComplexMatrix2 :=
  open Classical in
  Tower.extendOddly fun b =>
    if b = PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 w) SlopeCoefficient.secondAxis then
      Matrices.ComplexMatrix2.pauliFamily 2 else 0
def differenceKernelFinite (a : ℝ) (L n k : ℕ) (w : Fin 4 → ℤ) : ℝ :=
  Tower.leftSecondDeriv (chainMinusBackground a) (Tower.trivialField L n k 0)
    (meshScaledResponse L n k (pauliUnitForm L n k 0) : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
    (meshScaledResponse L n k (pauliUnitForm L n k w) : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
def IsDifferenceKernelLimit (a : ℝ) (L k : ℕ) (κ : (Fin 4 → ℤ) → ℝ) : Prop :=
  ∀ w, Tendsto (fun n => differenceKernelFinite a L n k w) atTop (𝓝 (κ w))
def invRadiusDiag (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) (m : ℕ) :
    KernelMatrix (Fin 3 × Tower.PositiveEdge L n k (m + 1)) (Fin 3 × Tower.PositiveEdge L n k (m + 1)) :=
  open Classical in
  fun ι' ι => if ι' = ι then (meanRadius (meanIterate U m) ι.2.1)⁻¹ else 0
def meanStepKernel (L n k : ℕ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) (m : ℕ) :
    KernelMatrix (Fin 3 × Tower.PositiveEdge L n k m) (Fin 3 × Tower.PositiveEdge L n k (m + 1)) :=
  (Tower.edgePauliCoordinates L n k m).kernel (Tower.edgePauliCoordinates L n k (m + 1))
    fun B => (L : ℝ)⁻¹ • meanCovariantStep (meanIterate U m) B
def noiseCovariance (a : ℝ) (L n k : ℕ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    (m : ℕ) → KernelMatrix (Fin 3 × Tower.PositiveEdge L n k m) (Fin 3 × Tower.PositiveEdge L n k m)
  | 0 => 0
  | m + 1 =>
    ((a⁻¹ : ℝ) : ℂ) • invRadiusDiag U m +
      (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) •
        compKernel (compKernel (meanStepKernel L n k U m) (noiseCovariance a L n k U m))
          (Tower.meshTranspose (Tower.meshAt L k m) (Tower.meshAt L k (m + 1))
            (meanStepKernel L n k U m))
section Determinants
variable [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
  [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
  [DecidableEq (Fin 3 × Tower.PositiveEdge L n k 0)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
  [DecidableEq (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k k)]
def xiInv (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k 0) (Fin 3 × Tower.PositiveEdge L n k 0) ℂ :=
  (Matrix.of (Tower.rescaledOperators L n k U).Xi)⁻¹
def yInv (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix (Fin 3 × Tower.Vertex L n k 0) (Fin 3 × Tower.Vertex L n k 0) ℂ :=
  (Matrix.of (Tower.rescaledOperators L n k U).Y)⁻¹
def meanQTranspose (L n k : ℕ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k 0) (Fin 3 × Tower.PositiveEdge L n k k) ℂ :=
  Matrix.of (Tower.meshTranspose (Tower.finestMesh L k) (Tower.meshAt L k k) (meanKernelQ L n k U))
def topCovariance (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k k) (Fin 3 × Tower.PositiveEdge L n k k) ℂ :=
  Matrix.of (Tower.rescaledOperators L n k U).Q * xiInv U * Matrix.of (Tower.rescaledOperators L n k U).Qt
def noiseBlockMatrix (a : ℝ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k k ⊕ Fin 3 × Tower.PositiveEdge L n k k)
      (Fin 3 × Tower.PositiveEdge L n k k ⊕ Fin 3 × Tower.PositiveEdge L n k k) ℂ :=
  Matrix.fromBlocks
    (-Matrix.of (noiseCovariance a L n k U k) -
      Matrix.of (meanKernelQ L n k U) * xiInv U * meanQTranspose L n k U)
    (-(Matrix.of (meanKernelQ L n k U) * xiInv U * Matrix.of (Tower.rescaledOperators L n k U).Qt))
    (-(Matrix.of (Tower.rescaledOperators L n k U).Q * xiInv U * meanQTranspose L n k U))
    (1 - topCovariance U)
def topLogDeterminants (a : ℝ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) : ℝ :=
  -(1 / 2) * Real.log ‖Matrix.det (noiseBlockMatrix a U)‖ +
    1 / 2 * Real.log ‖Matrix.det (topCovariance U)‖ +
    Real.log ‖Matrix.det (Matrix.of (meanKernelR L n k U) * yInv U *
      Matrix.of (Tower.rescaledOperators L n k U).Rt)‖ -
    Real.log ‖Matrix.det (Matrix.of (Tower.rescaledOperators L n k U).R * yInv U *
      Matrix.of (Tower.rescaledOperators L n k U).Rt)‖
end Determinants
end RunningCouplingSlope
end YangMills.Construction
end
