import YangMills.Construction.Towers.BoundOfAnInterpolationRemainderBetweenTwoRoots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets
open PeriodicOperators
def edgeSqrtJet (L k : ℕ) : JetQuad (colourEdges L k 0) (colourEdges L k 0) :=
  JetQuad.ofKernel (colourEdges L k 0) (colourEdges L k 0) (FreeResolvents.edgeResolventSqrt L k)
def edgeInvSqrtJet (L k : ℕ) : JetQuad (colourEdges L k 0) (colourEdges L k 0) :=
  JetQuad.ofKernel (colourEdges L k 0) (colourEdges L k 0)
    (FreeResolvents.edgeResolventInvSqrt L k)
def vertexToEdgeJet (L k : ℕ) (p : Fin 4 → ℂ) (μ ν : Fin 4) :
    JetQuad (colourVertices L k k) (colourEdges L k 0) :=
  JetQuad.mul p (JetQuad.mul p (edgeSqrtJet L k) (covDerivJet L k p μ ν))
    (JetQuad.transposeAt p (vertexSmoothingJet L k p μ ν))
def EdgeJetsInterpolate : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ a b g : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ g ∧
    ∀ k : ℕ, 1 ≤ k → ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μ ν : Fin 4,
      RootInterpolation.RootInterpolationData p (edgeOperatorJet L k p μ ν)
        (edgeCorrectionJet L k p μ ν) (edgeSqrtJet L k) (edgeInvSqrtJet L k)
        (FreeResolvents.edgeResolvent L k) (edgeSmoothingJet L k p μ ν)
        (vertexToEdgeJet L k p μ ν) a b g
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.EdgeRootJets
end
