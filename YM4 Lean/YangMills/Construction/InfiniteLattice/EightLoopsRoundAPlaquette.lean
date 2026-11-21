import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import Mathlib
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open Matrices
def linkOfUnitDistance (x y : LatticePoint 1)
    (h : TorusMetric.euclidNormVec ((x : AmbientSpace) - (y : AmbientSpace)) = 1) : Link 1 where
  initial := x
  terminal := y
  isAdjacent := isAdjacent_of_euclidNormVec x y (by
    have hs : TorusMetric.euclidNormVec ((y : AmbientSpace) - (x : AmbientSpace)) =
        TorusMetric.euclidNormVec ((x : AmbientSpace) - (y : AmbientSpace)) := by
      unfold TorusMetric.euclidNormVec
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Pi.sub_apply]
        ring
    rw [hs, h, abs_one])
def PlaquetteLoopTraces : Prop :=
  (∀ (p : ElementaryPlaquette 1) (y₁ y₂ y₃ y₄ : LatticePoint 1),
    ({y₁, y₂, y₃, y₄} : Set (LatticePoint 1)) = p.cornerSet →
    ∀ (h₁₂ : TorusMetric.euclidNormVec ((y₁ : AmbientSpace) - (y₂ : AmbientSpace)) = 1)
      (h₂₃ : TorusMetric.euclidNormVec ((y₂ : AmbientSpace) - (y₃ : AmbientSpace)) = 1)
      (h₃₄ : TorusMetric.euclidNormVec ((y₃ : AmbientSpace) - (y₄ : AmbientSpace)) = 1)
      (h₄₁ : TorusMetric.euclidNormVec ((y₄ : AmbientSpace) - (y₁ : AmbientSpace)) = 1)
      (U : GaugeField 1),
      (ComplexMatrix2.fullTrace ((U (linkOfUnitDistance y₁ y₂ h₁₂) *
          U (linkOfUnitDistance y₂ y₃ h₂₃) * U (linkOfUnitDistance y₃ y₄ h₃₄) *
          U (linkOfUnitDistance y₄ y₁ h₄₁) :
            ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
        (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re) ∧
  (∀ g₁ g₂ : ComplexMatrix2.specialUnitary,
    (ComplexMatrix2.fullTrace ((g₁ * g₂ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
      (ComplexMatrix2.fullTrace ((g₂ * g₁ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re) ∧
  (∀ g₁ : ComplexMatrix2.specialUnitary,
    (ComplexMatrix2.fullTrace ((g₁⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
      (ComplexMatrix2.fullTrace (g₁ : ComplexMatrix2)).re) ∧
  ∀ (p : ElementaryPlaquette 1) (U : GaugeField 1), 0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2
end YangMills.Construction.InfiniteLattice
