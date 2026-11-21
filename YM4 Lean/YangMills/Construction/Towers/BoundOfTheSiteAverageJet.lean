import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open PeriodicOperators
open BackgroundJets
def VertexSmoothingJetBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ μ₁ μ₂ : Fin 4, ∀ p ∈ momentumPolydisc stripHalfWidth,
      JetQuad.jetNorm stripHalfWidth p (vertexSmoothingJet L k p μ₁ μ₂) ≤ ENNReal.ofReal C
end YangMills.Construction.Tower.FullSpace
end
