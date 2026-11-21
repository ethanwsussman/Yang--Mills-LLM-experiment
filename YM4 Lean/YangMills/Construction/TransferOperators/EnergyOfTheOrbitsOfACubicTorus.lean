import YangMills.Construction.TransferOperators.TransferOperatorOfACubicTorus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices.ComplexMatrix2 (specialUnitary)
noncomputable section
namespace YangMills.Construction.TransferOperators.SliceEnergyProperties
def Statement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (Λ : CubicPeriodSublattice) (μ : Fin 4),
    Continuous (Λ.sliceEnergy (μ := μ) β) ∧
    (∀ u, (Λ.sliceEnergy (μ := μ) β u).im = 0 ∧ 0 ≤ (Λ.sliceEnergy (μ := μ) β u).re) ∧
    ∀ (g : Λ.VertexOrbits μ → specialUnitary) (u : Λ.LinkOrbits μ → specialUnitary),
      Λ.sliceEnergy β (Λ.orbitGaugeAct g u) = Λ.sliceEnergy β u
end YangMills.Construction.TransferOperators.SliceEnergyProperties
end
