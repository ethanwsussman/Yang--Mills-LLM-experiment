import YangMills.Construction.Towers.ResponseFieldOnTheTorus
import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import YangMills.Construction.Towers.TheResponseSymbolNearTheStrip
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseSymbolNearZero
open PeriodicOperators (colourEdges)
open PeriodicOperators.LogDetSecondDerivs (descendField)
open ResponseProperties (euclidNorm)
open TorusResponseField (constantFinestForm)
open ResponseSymbolNearStrip (IsTracelessTuple)
open FullSpace (backgroundResponseSymbol coarseResponseSymbol sourceResponseSymbol)
def constantFormOnQuot (L k : ℕ) (ξ : Fin 4 → Matrices.ComplexMatrix2) :
    (colourEdges L k 0).UnitQuot → ℂ :=
  descendField (colourEdges L k 0) 1
    ((FullSpace.edgePauliCoordinates L k 0).coeffs (constantFinestForm L k ξ))
def ComponentsNearZero : Prop :=
  ∀ δ₀ ∈ FreeStrip.halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ∀ ε : Fin 4 → Matrices.ComplexMatrix2, IsTracelessTuple ε →
      ∃ C : ℝ, ∃ N ∈ nhds (0 : Fin 4 → ℂ), ∀ p ∈ N,
        (∀ c, ‖sourceResponseSymbol L k p ε c‖ ≤ C * euclidNorm p ^ 2) ∧
        (∀ c, ‖coarseResponseSymbol L k p ε c‖ ≤ C * euclidNorm p ^ 2) ∧
        ∀ c, ‖backgroundResponseSymbol L k p ε c -
            constantFormOnQuot L k (((finestMesh L k : ℝ) : ℂ) • ε) c‖ ≤
          C * euclidNorm p
end YangMills.Construction.Tower.ResponseSymbolNearZero
end
