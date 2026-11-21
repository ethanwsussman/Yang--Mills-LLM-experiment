import YangMills.Construction.Towers.PlaneWavePropagatorCalculusFacts
import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRoots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SaddleStability
open PeriodicOperators (colourEdges wNorm symbolHom)
open PlaneWaveCalculus (topEdgeComponent)
open FreeResolvents (trivialRescaledOperators)
def UniformBoundNearZero : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ C : ℝ, ∃ N ∈ nhds (0 : Fin 4 → ℂ), ∀ p ∈ N,
      ∀ (b : (colourEdges L k 0).UnitQuot → ℂ) (n : (colourEdges L k k).UnitQuot → ℂ),
        wNorm ((colourEdges L k 0).quotWeight 1) b +
            pauliFamilyNorm (topEdgeComponent L k n) ≤
          C * (wNorm ((colourEdges L k 0).quotWeight 1)
                (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X p b -
                  symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt p n) +
              pauliFamilyNorm (topEdgeComponent L k
                (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q p b)))
end YangMills.Construction.Tower.SaddleStability
end
