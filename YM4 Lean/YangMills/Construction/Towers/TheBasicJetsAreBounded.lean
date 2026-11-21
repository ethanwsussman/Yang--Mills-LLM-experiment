import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.BoundedBasicJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
def halfFaceTraceDefectJet (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) :
    JetQuad (colourFaces L k 0) (colourFaces L k 0) :=
  (halfFaceTraceJet L k p μPlus μMinus).add
    (JetQuad.smul (-1) (JetQuad.one (colourFaces L k 0)))
structure JetNormsBounded (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) (C : ℝ) : Prop where
  covDerivDefect :
    JetQuad.jetNorm stripHalfWidth p (covDerivDefectJet L k p μPlus μMinus) ≤ ENNReal.ofReal C
  holonomyDefect :
    JetQuad.jetNorm stripHalfWidth p (holonomyDefectJet L k p μPlus μMinus) ≤ ENNReal.ofReal C
  halfFaceTrace :
    JetQuad.jetNorm stripHalfWidth p (halfFaceTraceJet L k p μPlus μMinus) ≤ ENNReal.ofReal C
  curvature :
    JetQuad.jetNorm stripHalfWidth p (curvatureJet L k p μPlus μMinus) ≤ ENNReal.ofReal C
  edgeSmoothing :
    JetQuad.jetNorm stripHalfWidth p (edgeSmoothingJet L k p μPlus μMinus) ≤ ENNReal.ofReal C
  vertexSmoothing :
    JetQuad.jetNorm stripHalfWidth p (vertexSmoothingJet L k p μPlus μMinus) ≤ ENNReal.ofReal C
structure ZeroComponentsVanish (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) : Prop where
  covDerivDefect : ∀ κ ∈ imStrip (2 * stripHalfWidth),
    (covDerivDefectJet L k p μPlus μMinus).f00 κ = 0
  holonomyDefect : ∀ κ ∈ imStrip (2 * stripHalfWidth),
    (holonomyDefectJet L k p μPlus μMinus).f00 κ = 0
  halfFaceTraceDefect : ∀ κ ∈ imStrip (2 * stripHalfWidth),
    (halfFaceTraceDefectJet L k p μPlus μMinus).f00 κ = 0
  curvature : ∀ κ ∈ imStrip (2 * stripHalfWidth),
    (curvatureJet L k p μPlus μMinus).f00 κ = 0
def BasicJetsBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ μPlus μMinus : Fin 4, ∀ p ∈ momentumPolydisc stripHalfWidth,
      JetNormsBounded L k p μPlus μMinus C) ∧
    ∀ k : ℕ, 1 ≤ k → ∀ μPlus μMinus : Fin 4, ∀ p ∈ momentumPolydisc stripHalfWidth,
      ZeroComponentsVanish L k p μPlus μMinus
end YangMills.Construction.Tower.BoundedBasicJets
end
