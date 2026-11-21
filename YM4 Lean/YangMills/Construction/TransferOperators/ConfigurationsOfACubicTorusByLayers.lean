import YangMills.Construction.TransferOperators.TransferOperatorOfACubicTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.Matrices.ComplexMatrix2 (specialUnitary haarPi)
noncomputable section
namespace YangMills.Construction.TransferOperators
namespace CubicPeriodSublattice
variable (Λ : CubicPeriodSublattice) (μ : Fin 4)
def labelQuotientLink :
    (ZMod Λ.side × Λ.LinkOrbits μ) ⊕ (ZMod Λ.side × Λ.VertexOrbits μ) → Λ.lattice.QuotientLink :=
  Sum.elim (fun p => Λ.spatialQuotientLink p.1 p.2) fun p => Λ.temporalQuotientLink p.1 p.2
def slicePairs (U : Λ.lattice.QuotientField) :
    ZMod Λ.side → (Λ.VertexOrbits μ → specialUnitary) × (Λ.LinkOrbits μ → specialUnitary) :=
  fun c => (Λ.temporalSliceField U c, Λ.sliceField U (c + 1))
end CubicPeriodSublattice
namespace SliceDecomposition
def Statement : Prop :=
  ∀ (Λ : CubicPeriodSublattice) (μ : Fin 4),
    Function.Bijective (Λ.labelQuotientLink μ) ∧
      MeasurePreserving (Λ.slicePairs μ) Λ.lattice.quotientHaar
        (Measure.pi fun _ : ZMod Λ.side =>
          (haarPi (Λ.VertexOrbits μ)).prod (haarPi (Λ.LinkOrbits μ)))
end SliceDecomposition
end YangMills.Construction.TransferOperators
end
