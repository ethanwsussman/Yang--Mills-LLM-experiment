import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PlaneWaveCalculus
open YangMills.Construction.PeriodicOperators (colourVertices colourEdges colourFaces openImStrip)
open YangMills.Construction.Tower.PlaneWaves
def PlaneWaveCalculusHolds : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ m ∈ freqBox L k, -m ∈ freqBox L k) ∧
    VertexCoeffFacts L k ∧ EdgeCoeffFacts L k ∧ FaceCoeffFacts L k ∧
    SymbolFormulas L k ∧ CoboundarySymbols L k ∧ SmoothingSymbols L k ∧
    WeightRelations L k ∧ FreeOpsRealFiniteRange L k ∧
    ∀ υ : ℝ, 0 < υ → ∀ t : (Fin 4 → ℂ) → ℂ,
      (∀ q ∈ openImStrip υ, ∀ e : Fin 4 → ℤ, t (periodShift L k q e) = t q) →
        MultiplierMatrixFacts (colourVertices L k 0) (ScalesVertexCoeffs L k t)
          (vertexFourierMultiplier L k t) υ t ∧
        MultiplierMatrixFacts (colourEdges L k 0) (ScalesEdgeCoeffs L k t)
          (edgeFourierMultiplier L k t) υ t ∧
        MultiplierMatrixFacts (colourFaces L k 0) (ScalesFaceCoeffs L k t)
          (faceFourierMultiplier L k t) υ t
end PlaneWaveCalculus
end Tower
end YangMills.Construction
end
