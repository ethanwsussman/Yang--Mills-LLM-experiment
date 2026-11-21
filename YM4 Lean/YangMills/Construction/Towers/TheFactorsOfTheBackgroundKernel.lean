import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
structure BackgroundKernelFactors (S B S' : Type) where
  hess : KernelMatrix B B
  brk : KernelMatrix B S
  quad : KernelMatrix B B
  sigma : KernelMatrix B S
  diff : KernelMatrix S B
  avg : KernelMatrix S S'
  scale : ℂ
namespace BackgroundKernelFactors
variable {S B S' : Type} (F : BackgroundKernelFactors S B S')
def tauKernel : KernelMatrix B B := unitKernel B + compKernel F.diff F.sigma
def complementKernel : KernelMatrix S S :=
  unitKernel S - F.scale • compKernel (swapKernel F.avg) F.avg
def assembled : KernelMatrix B B :=
  F.hess + (2 : ℂ) • compKernel (swapKernel F.sigma) F.brk +
    compKernel (compKernel (swapKernel F.sigma) F.brk)
      (compKernel F.diff F.sigma) -
    compKernel (compKernel (swapKernel F.tauKernel) F.quad) F.tauKernel +
    compKernel (compKernel F.diff F.complementKernel)
      (compKernel F.complementKernel (swapKernel F.diff))
end BackgroundKernelFactors
end YangMills.Construction.PeriodicOperators
namespace YangMills.Construction.LocalKernels.Periodisation
open YangMills.Construction.PeriodicOperators (KernelMatrix BackgroundKernelFactors swapKernel)
open YangMills.Construction.Tower
section MapsOnPairs
variable {k : ℕ} (L n : ℕ)
def pairKernelOfMap (A A' : CellClass k)
    (φ : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2) :
    KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs) :=
  Classical.epsilon fun T => IsRepresentedOnPairs L A A' (fun g => φ g) T
def pairMatrixOfMap (A A' : CellClass k)
    (φ : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) :
    KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n) :=
  Classical.epsilon fun M => ∀ g : (CellClass.quotSpace L n A).complexSubmodule,
    CellClass.quotCoeffsOn L n A' (φ g) =
      YangMills.Construction.PeriodicOperators.applyKernel M (CellClass.quotCoeffsOn L n A g)
end MapsOnPairs
section SixFactors
variable (L n k : ℕ)
def fullFactors (U J : Edge L n k 0 → Matrices.ComplexMatrix2) (μ : Edge L n k k → Matrices.ComplexMatrix2) :
    BackgroundKernelFactors (Idx L (verticesAtZero k).colourPairs) (Idx L (edgesAtZero k).colourPairs)
      (Idx L (CellClass.vertexClass k k le_rfl).colourPairs) where
  hess := pairKernelOfMap L (edgesAtZero k) (edgesAtZero k)
    (FullSpace.complexHessianOperator (liftGaugeField L n k 0 U))
  brk := Classical.epsilon (IsBracketKernel L n k 0 (Nat.zero_le k) U J)
  quad := Classical.epsilon (IsQuadraticKernel L n k U μ)
  sigma := YangMills.Construction.PeriodicOperators.compKernel
    (pairKernelOfMap L (CellClass.vertexClass k k le_rfl) (verticesAtZero k) (fullZeroExtend L k))
    (pairKernelOfMap L (edgesAtZero k) (CellClass.vertexClass k k le_rfl)
      (FullSpace.iterContourLogDrift L k (liftGaugeField L n k 0 U) k))
  diff := pairKernelOfMap L (verticesAtZero k) (edgesAtZero k)
    (FullSpace.covDiff (liftGaugeField L n k 0 U))
  avg := pairKernelOfMap L (verticesAtZero k) (CellClass.vertexClass k k le_rfl)
    (FullSpace.iterAdjointCubeAverage L k (liftGaugeField L n k 0 U) k)
  scale := ((L : ℝ) ^ (4 * k) : ℝ)
def quotFactors (U J : Edge L n k 0 → Matrices.ComplexMatrix2) (μ : Edge L n k k → Matrices.ComplexMatrix2) :
    BackgroundKernelFactors ((verticesAtZero k).colourPairs.ImageCarrier L n)
      ((edgesAtZero k).colourPairs.ImageCarrier L n)
      ((CellClass.vertexClass k k le_rfl).colourPairs.ImageCarrier L n) where
  hess := pairMatrixOfMap L n (edgesAtZero k) (edgesAtZero k) (complexHessianOperator U)
  brk := Classical.epsilon (IsBracketMatrix L n k 0 (Nat.zero_le k) U J)
  quad := Classical.epsilon (IsQuadraticMatrix L n k U μ)
  sigma := YangMills.Construction.PeriodicOperators.compKernel
    (pairMatrixOfMap L n (CellClass.vertexClass k k le_rfl) (verticesAtZero k) (zeroExtend L n k))
    (pairMatrixOfMap L n (edgesAtZero k) (CellClass.vertexClass k k le_rfl)
      (iterContourLogDrift L n k U k))
  diff := pairMatrixOfMap L n (verticesAtZero k) (edgesAtZero k) (covDiff U)
  avg := pairMatrixOfMap L n (verticesAtZero k) (CellClass.vertexClass k k le_rfl)
    (iterAdjointCubeAverage L n k U k)
  scale := ((L : ℝ) ^ (4 * k) : ℝ)
end SixFactors
section Descent
variable {k : ℕ} (L n : ℕ)
structure BackgroundFactorsDescend {I₀ I₁ I₂ : WeightedIndexSet k}
    (F : BackgroundKernelFactors (Idx L I₀) (Idx L I₁) (Idx L I₂))
    (M : BackgroundKernelFactors (I₀.ImageCarrier L n) (I₁.ImageCarrier L n) (I₂.ImageCarrier L n)) :
    Prop where
  hess : KernelDescends L n I₁ I₁ F.hess M.hess
  hess_swap : KernelDescends L n I₁ I₁ (swapKernel F.hess) (swapKernel M.hess)
  brk : KernelDescends L n I₁ I₀ F.brk M.brk
  brk_swap : KernelDescends L n I₀ I₁ (swapKernel F.brk) (swapKernel M.brk)
  quad : KernelDescends L n I₁ I₁ F.quad M.quad
  quad_swap : KernelDescends L n I₁ I₁ (swapKernel F.quad) (swapKernel M.quad)
  sigma : KernelDescends L n I₁ I₀ F.sigma M.sigma
  sigma_swap : KernelDescends L n I₀ I₁ (swapKernel F.sigma) (swapKernel M.sigma)
  diff : KernelDescends L n I₀ I₁ F.diff M.diff
  diff_swap : KernelDescends L n I₁ I₀ (swapKernel F.diff) (swapKernel M.diff)
  avg : KernelDescends L n I₀ I₂ F.avg M.avg
  avg_swap : KernelDescends L n I₂ I₀ (swapKernel F.avg) (swapKernel M.avg)
  scale : F.scale = M.scale
end Descent
end YangMills.Construction.LocalKernels.Periodisation
namespace YangMills.Construction.Tower
open AsDifferentials (complexQuadraticTerm)
variable {L n k : ℕ}
def backgroundBilinear (U J : Edge L n k 0 → Matrices.ComplexMatrix2)
    (μ : Edge L n k k → Matrices.ComplexMatrix2)
    (B B' : Edge L n k 0 → Matrices.ComplexMatrix2) : ℂ :=
  backgroundForm L n k U B B' +
    (2 * edgeFormPairing J (levelBracketTerm U (backgroundGaugeParameter U B) B') +
      edgeFormPairing J (levelBracketTerm U (backgroundGaugeParameter U B)
        (covDiff U (backgroundGaugeParameter U B'))) -
      traceFinsumPairing (restrictToPositiveEdges μ)
        (complexQuadraticTerm L n k U (B + covDiff U (backgroundGaugeParameter U B))
          (B' + covDiff U (backgroundGaugeParameter U B'))))
end YangMills.Construction.Tower
end
