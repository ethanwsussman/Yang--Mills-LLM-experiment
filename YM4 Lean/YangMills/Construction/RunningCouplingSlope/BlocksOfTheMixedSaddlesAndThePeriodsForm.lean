import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import YangMills.Construction.RunningCouplingSlope.PlainChainAtAPeriodicExtension
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def SumsOverPeriodsTo (I I' : PeriodicOperators.PeriodicData) {P P' : Type}
    (T : I'.Carrier → I.Carrier → ℂ) (q : I.Carrier → P) (q' : I'.Carrier → P')
    (M : P' → P → ℂ) (s : ℕ) : Prop :=
  ∀ ι' ι, PeriodicOperators.periodization I I' T s ι' ι = M (q' ι') (q ι)
def colourEdgeImage (L n k j : ℕ) (ι : (PeriodicOperators.colourEdges L k j).Carrier) :
    Fin 3 × Tower.PositiveEdge L n k j :=
  (ι.1, LocalKernels.projPositiveEdge L n k j ι.2)
def colourVertexImage (L n k j : ℕ) (ι : (PeriodicOperators.colourVertices L k j).Carrier) :
    Fin 3 × Tower.Vertex L n k j :=
  (ι.1, Tower.FullSpace.projVertex L n k j ι.2)
structure MixedSaddleBlocksPeriodize (a : ℝ) (L n k : ℕ)
    (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  X : SumsOverPeriodsTo (PeriodicOperators.colourEdges L k 0) (PeriodicOperators.colourEdges L k 0)
    (Tower.FullSpace.rescaledOperators L k (LocalKernels.liftGaugeField L n k 0 U)).X
    (colourEdgeImage L n k 0) (colourEdgeImage L n k 0) (Tower.rescaledOperators L n k U).X
    (LocalKernels.Periodisation.periodSide L n)
  Qt : SumsOverPeriodsTo (PeriodicOperators.colourEdges L k k) (PeriodicOperators.colourEdges L k 0)
    (Tower.meshTranspose (Tower.finestMesh L k) (Tower.meshAt L k k)
      (FullLattice.meanKernelQ L k (LocalKernels.liftGaugeField L n k 0 U)))
    (colourEdgeImage L n k k) (colourEdgeImage L n k 0) (meanQTranspose L n k U)
    (LocalKernels.Periodisation.periodSide L n)
  Q : SumsOverPeriodsTo (PeriodicOperators.colourEdges L k 0) (PeriodicOperators.colourEdges L k k)
    (FullLattice.meanKernelQ L k (LocalKernels.liftGaugeField L n k 0 U))
    (colourEdgeImage L n k 0) (colourEdgeImage L n k k) (meanKernelQ L n k U)
    (LocalKernels.Periodisation.periodSide L n)
  covariance : SumsOverPeriodsTo (PeriodicOperators.colourEdges L k k)
    (PeriodicOperators.colourEdges L k k)
    (FullLattice.noiseCovariance a L k (LocalKernels.liftGaugeField L n k 0 U) k)
    (colourEdgeImage L n k k) (colourEdgeImage L n k k) (noiseCovariance a L n k U k)
    (LocalKernels.Periodisation.periodSide L n)
  Delta : SumsOverPeriodsTo (PeriodicOperators.colourVertices L k 0)
    (PeriodicOperators.colourVertices L k 0)
    (Tower.FullSpace.rescaledOperators L k (LocalKernels.liftGaugeField L n k 0 U)).Delta
    (colourVertexImage L n k 0) (colourVertexImage L n k 0) (Tower.rescaledOperators L n k U).Delta
    (LocalKernels.Periodisation.periodSide L n)
  Rt : SumsOverPeriodsTo (PeriodicOperators.colourVertices L k k)
    (PeriodicOperators.colourVertices L k 0)
    (Tower.FullSpace.rescaledOperators L k (LocalKernels.liftGaugeField L n k 0 U)).Rt
    (colourVertexImage L n k k) (colourVertexImage L n k 0) (Tower.rescaledOperators L n k U).Rt
    (LocalKernels.Periodisation.periodSide L n)
  R : SumsOverPeriodsTo (PeriodicOperators.colourVertices L k 0)
    (PeriodicOperators.colourVertices L k k)
    (FullLattice.meanKernelR L k (LocalKernels.liftGaugeField L n k 0 U))
    (colourVertexImage L n k 0) (colourVertexImage L n k k) (meanKernelR L n k U)
    (LocalKernels.Periodisation.periodSide L n)
def MixedSaddleBlocksPeriodizeNearIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ (a : ℝ) (k n : ℕ), 1 ≤ k → 0 < n →
    ∀ U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2, MeanChainNearIdentity ρ L n k U →
      MixedSaddleBlocksPeriodize a L n k U
end YangMills.Construction.RunningCouplingSlope
end
