import YangMills.Construction.InfiniteLattice.SingleBondWeight
import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import YangMills.Construction.Matrices.SpecialLinearConjugation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open Matrices
def SpecialUnitaryTraceFacts : Prop :=
  ComplexMatrix2.symplecticUnit ∈ ComplexMatrix2.specialUnitary ∧
  ∀ w : ComplexMatrix2.specialUnitary,
    (w : ComplexMatrix2) 1 1 = star ((w : ComplexMatrix2) 0 0) ∧
    (w : ComplexMatrix2) 1 0 = -star ((w : ComplexMatrix2) 0 1) ∧
    (∀ i j, ∃ k l, ((w⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j =
        (w : ComplexMatrix2) k l ∨
      ((w⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j = -(w : ComplexMatrix2) k l) ∧
    (∀ i j, ∃ k l, ComplexMatrix2.conjEntries (w : ComplexMatrix2) i j = (w : ComplexMatrix2) k l ∨
      ComplexMatrix2.conjEntries (w : ComplexMatrix2) i j = -(w : ComplexMatrix2) k l) ∧
    ComplexMatrix2.conjEntries (w : ComplexMatrix2) =
      ComplexMatrix2.symplecticUnit * (w : ComplexMatrix2) * ComplexMatrix2.symplecticUnit⁻¹ ∧
    (ComplexMatrix2.fullTrace (w : ComplexMatrix2)).im = 0 ∧
    ComplexMatrix2.fullTrace ((w⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ComplexMatrix2.fullTrace (w : ComplexMatrix2) ∧
    ‖ComplexMatrix2.fullTrace (w : ComplexMatrix2)‖ ≤ 2
def SingleBondWeightRealClassFunction (β : ℝ) : Prop :=
  (∀ w : ComplexMatrix2.specialUnitary, (singleBondWeight β w).im = 0) ∧
  Continuous (fun w : ComplexMatrix2.specialUnitary => (singleBondWeight β w).re) ∧
  (∀ g w : ComplexMatrix2.specialUnitary, singleBondWeight β (g * w * g⁻¹) = singleBondWeight β w) ∧
  ∀ w : ComplexMatrix2.specialUnitary, singleBondWeight β w⁻¹ = singleBondWeight β w
def SingleBondWeightBounds (β : ℝ) : Prop :=
  ∀ w : ComplexMatrix2.specialUnitary,
    Real.exp (-2 * β) ≤ (singleBondWeight β w).re ∧ (singleBondWeight β w).re ≤ 1
def FaceFactorEqSingleBondWeight (β : ℝ) : Prop :=
  (∀ (p : ElementaryPlaquette 1) (U : GaugeField 1),
    ((Real.exp (-β * faceEnergy U p) : ℝ) : ℂ) = singleBondWeight β (faceHolonomy U p)) ∧
  ∀ (p : ElementaryPlaquette 1) (U : GaugeField 1) (b₀ b₁ b₂ b₃ : Link 1),
    ({b₀.initial, b₁.initial, b₂.initial, b₃.initial} : Set (LatticePoint 1)) = p.cornerSet →
    b₀.terminal = b₁.initial → b₁.terminal = b₂.initial → b₂.terminal = b₃.initial →
    b₃.terminal = b₀.initial →
    ((Real.exp (-β * faceEnergy U p) : ℝ) : ℂ) = singleBondWeight β (U b₀ * U b₁ * U b₂ * U b₃)
def TraceAndSingleBondWeight : Prop :=
  SpecialUnitaryTraceFacts ∧
  ∀ β : ℝ, 0 < β →
    SingleBondWeightRealClassFunction β ∧ SingleBondWeightBounds β ∧
      FaceFactorEqSingleBondWeight β
end YangMills.Construction.InfiniteLattice
end
