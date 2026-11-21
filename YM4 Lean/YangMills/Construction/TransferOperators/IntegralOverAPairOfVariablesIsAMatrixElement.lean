import YangMills.Construction.TransferOperators.TransferOperatorOfACubicTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators
namespace CubicPeriodSublattice
variable (Γ : CubicPeriodSublattice) {μ : Fin 4}
def pairIntegrand (β : ℝ) (α' α : PeterWeylIndex (Γ.LinkOrbits μ))
    (p : (Γ.VertexOrbits μ → Matrices.ComplexMatrix2.specialUnitary) ×
      (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary)) : ℂ :=
  star (peterWeylFn α' (Γ.orbitGaugeAct p.1 p.2)) * Complex.exp (-Γ.sliceEnergy β p.2) *
    peterWeylFn α p.2
end CubicPeriodSublattice
namespace PairIntegralMatrixEntry
def Statement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (Γ : CubicPeriodSublattice) (μ : Fin 4) (α' α : PeterWeylIndex (Γ.LinkOrbits μ)),
    Integrable (Γ.pairIntegrand β α' α)
        ((Matrices.ComplexMatrix2.haarPi (Γ.VertexOrbits μ)).prod
          (Matrices.ComplexMatrix2.haarPi (Γ.LinkOrbits μ))) ∧
      (sqrtPeterWeylCoeff β α' : ℂ) * (sqrtPeterWeylCoeff β α : ℂ) *
          ∫ p, Γ.pairIntegrand β α' α p
            ∂(Matrices.ComplexMatrix2.haarPi (Γ.VertexOrbits μ)).prod
              (Matrices.ComplexMatrix2.haarPi (Γ.LinkOrbits μ)) =
        peterWeylEntry (Γ.transfer μ β) α' α
end PairIntegralMatrixEntry
end YangMills.Construction.TransferOperators
end
