import YangMills.Construction.Towers.BoundOfAnInterpolationRemainderBetweenTwoRoots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.VertexRootJets
open PeriodicOperators
def vertexSqrtJet (L k : ℕ) : JetQuad (colourVertices L k 0) (colourVertices L k 0) :=
  JetQuad.ofKernel (colourVertices L k 0) (colourVertices L k 0)
    (FreeResolvents.vertexResolventSqrt L k)
def vertexInvSqrtJet (L k : ℕ) : JetQuad (colourVertices L k 0) (colourVertices L k 0) :=
  JetQuad.ofKernel (colourVertices L k 0) (colourVertices L k 0)
    (FreeResolvents.vertexResolventInvSqrt L k)
def VertexJetsInterpolate : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ a b g : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ g ∧
    ∀ k : ℕ, 1 ≤ k → ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μ ν : Fin 4,
      RootInterpolation.RootInterpolationData p (vertexOperatorJet L k p μ ν)
        (vertexCorrectionJet L k p μ ν) (vertexSqrtJet L k) (vertexInvSqrtJet L k)
        (FreeResolvents.vertexResolvent L k) (vertexSmoothingJet L k p μ ν)
        (JetQuad.zeroJet (colourVertices L k k) (colourVertices L k 0)) a b g
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.VertexRootJets
end
