import YangMills.Construction.PeriodicOperators.Jets
import YangMills.Construction.Towers.PlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
namespace PlaneWaves
open PeriodicOperators (QuotHom colourVertices colourEdges colourFaces)
def ScalesVertexCoeffs (L k : ℕ) (t : (Fin 4 → ℂ) → ℂ) (κ : Fin 4 → ℂ)
    (A : QuotHom (colourVertices L k 0) (colourVertices L k 0)) : Prop :=
  ∀ f, ∀ p ∈ freqBox L k,
    vertexFourierCoeff L k (A f) p = t (shiftedFreq κ p) • vertexFourierCoeff L k f p
def ScalesEdgeCoeffs (L k : ℕ) (t : (Fin 4 → ℂ) → ℂ) (κ : Fin 4 → ℂ)
    (A : QuotHom (colourEdges L k 0) (colourEdges L k 0)) : Prop :=
  ∀ b, ∀ μ : Fin 4, ∀ p ∈ freqBox L k,
    edgeFourierCoeff L k (A b) μ p = t (shiftedFreq κ p) • edgeFourierCoeff L k b μ p
def ScalesFaceCoeffs (L k : ℕ) (t : (Fin 4 → ℂ) → ℂ) (κ : Fin 4 → ℂ)
    (A : QuotHom (colourFaces L k 0) (colourFaces L k 0)) : Prop :=
  ∀ F, ∀ (μ ν : Fin 4) (hμν : μ < ν), ∀ p ∈ freqBox L k,
    faceFourierCoeff L k (A F) μ ν hμν p =
      t (shiftedFreq κ p) • faceFourierCoeff L k F μ ν hμν p
def vertexFourierMultiplier (L k : ℕ) (t : (Fin 4 → ℂ) → ℂ) (κ : Fin 4 → ℂ) :
    QuotHom (colourVertices L k 0) (colourVertices L k 0) :=
  Classical.epsilon (ScalesVertexCoeffs L k t κ)
def edgeFourierMultiplier (L k : ℕ) (t : (Fin 4 → ℂ) → ℂ) (κ : Fin 4 → ℂ) :
    QuotHom (colourEdges L k 0) (colourEdges L k 0) :=
  Classical.epsilon (ScalesEdgeCoeffs L k t κ)
def faceFourierMultiplier (L k : ℕ) (t : (Fin 4 → ℂ) → ℂ) (κ : Fin 4 → ℂ) :
    QuotHom (colourFaces L k 0) (colourFaces L k 0) :=
  Classical.epsilon (ScalesFaceCoeffs L k t κ)
end PlaneWaves
end YangMills.Construction.Tower
end
