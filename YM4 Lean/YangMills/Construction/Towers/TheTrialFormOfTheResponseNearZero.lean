import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TrialResponse
open YangMills.Construction.PeriodicOperators (colourEdges wNorm symbolHom)
open YangMills.Construction.Tower.PlaneWaveCalculus (topEdgeComponent)
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.PlaneWaves (edgeWeight edgeFourierCoeff freqBox)
open YangMills.Construction.Tower.ResponseProperties (InFundamentalStrip euclidNorm)
open YangMills.Construction.Tower.FreeStrip (halfSupRate)
def IsTrialField (L j : ℕ) (p : Fin 4 → ℂ) (v : (colourEdges L j j).UnitQuot → ℂ)
    (g : (colourEdges L j 0).UnitQuot → ℂ) : Prop :=
  (∀ μ, edgeFourierCoeff L j g μ 0 = (edgeWeight L j p μ)⁻¹ • topEdgeComponent L j v μ) ∧
  ∀ m ∈ freqBox L j, m ≠ 0 → ∀ μ, edgeFourierCoeff L j g μ m = 0
def TrialFieldNearZero : Prop :=
  ∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ j : ℕ, 1 ≤ j →
    ∃ C : ℝ, ∃ N ∈ nhds (0 : Fin 4 → ℂ), ∀ p ∈ N, InFundamentalStrip δ₀ p →
      ∀ v : (colourEdges L j j).UnitQuot → ℂ, ∃ g : (colourEdges L j 0).UnitQuot → ℂ,
        IsTrialField L j p v g ∧
        symbolHom (colourEdges L j 0) (colourEdges L j j) (trivialRescaledOperators L j).Q p g = v ∧
        wNorm ((colourEdges L j 0).quotWeight 1)
            (symbolHom (colourEdges L j 0) (colourEdges L j 0) (trivialRescaledOperators L j).X p g) ≤
          C * (euclidNorm p ^ 2 * pauliFamilyNorm (topEdgeComponent L j v)) ∧
        pauliFamilyNorm (fun μ => edgeFourierCoeff L j g μ 0 - topEdgeComponent L j v μ) ≤
          C * (euclidNorm p * pauliFamilyNorm (topEdgeComponent L j v))
end YangMills.Construction.Tower.TrialResponse
end
