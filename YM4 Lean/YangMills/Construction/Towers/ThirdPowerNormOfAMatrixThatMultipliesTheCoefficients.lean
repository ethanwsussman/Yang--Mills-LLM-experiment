import YangMills.Construction.LinearAlgebra.TraceOfSixFoldProduct
import YangMills.Construction.Towers.MatricesThatMultiplyTheCoefficients
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.PlaneWaves
def ScalingMatrixSchattenCube : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ [Finite (PeriodicOperators.colourEdges L k 0).UnitQuot]
      [Finite (PeriodicOperators.colourVertices L k 0).UnitQuot]
      (t : (Fin 4 → ℂ) → ℂ) (κ : Fin 4 → ℂ),
      (∀ A, Tower.PlaneWaves.ScalesEdgeCoeffs L k t κ A →
        RealPower.rpowPos (TraceBound.schattenThreeNorm
            (PeriodicOperators.wInner ((PeriodicOperators.colourEdges L k 0).quotWeight 1)) A) 3 =
          12 * ∑ m ∈ Tower.PlaneWaves.freqBox L k,
            RealPower.rpowPos ‖t (Tower.PlaneWaves.shiftedFreq κ m)‖ 3) ∧
      ∀ A, Tower.PlaneWaves.ScalesVertexCoeffs L k t κ A →
        RealPower.rpowPos (TraceBound.schattenThreeNorm
            (PeriodicOperators.wInner ((PeriodicOperators.colourVertices L k 0).quotWeight 1)) A) 3 =
          3 * ∑ m ∈ Tower.PlaneWaves.freqBox L k,
            RealPower.rpowPos ‖t (Tower.PlaneWaves.shiftedFreq κ m)‖ 3
end YangMills.Construction.Tower.PlaneWaves
end
