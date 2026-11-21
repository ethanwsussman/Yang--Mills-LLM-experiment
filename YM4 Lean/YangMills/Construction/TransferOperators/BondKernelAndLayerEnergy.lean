import YangMills.Construction.InfiniteLattice.SingleBondWeight
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.TransferOperators.LayersStacksTransportedVariablesAndBlocks
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.TransferOperators
def linkProductKernel (β : ℝ) {B : Type} (u u' : B → ComplexMatrix2.specialUnitary) : ℂ :=
  ∏ᶠ b, singleBondWeight β (u b * (u' b)⁻¹)
def linkProductOperator (β : ℝ) (B : Type) [Finite B] : HaarL2 B →L[ℂ] HaarL2 B :=
  Schatten.kernelOp (ComplexMatrix2.haarPi B) fun q => linkProductKernel β q.1 q.2
def singleLinkOperator (β : ℝ) :
    Lp ℂ 2 ComplexMatrix2.haarProb →L[ℂ] Lp ℂ 2 ComplexMatrix2.haarProb :=
  Schatten.kernelOp ComplexMatrix2.haarProb fun q => singleBondWeight β (q.1 * q.2⁻¹)
variable {μ : Fin 4}
def plaquetteHolonomy (p : SlicePlaquette μ) {S : Set (SliceLink μ)} (hS : p.links ⊆ S)
    (u : S → ComplexMatrix2.specialUnitary) : ComplexMatrix2.specialUnitary :=
  u ⟨p.bottomLink, hS (by simp [SlicePlaquette.links])⟩ *
    u ⟨p.rightLink, hS (by simp [SlicePlaquette.links])⟩ *
    (u ⟨p.topLink, hS (by simp [SlicePlaquette.links])⟩)⁻¹ *
    (u ⟨p.leftLink, hS (by simp [SlicePlaquette.links])⟩)⁻¹
namespace Block
variable (B : Block μ)
def touchingPlaquettes : Set (SlicePlaquette μ) := {p | ∃ e ∈ B.links, e ∈ p.links}
theorem links_subset_thickened (p : B.touchingPlaquettes) : p.1.links ⊆ B.thickened := by
  obtain ⟨e', he', hp⟩ := p.2
  exact fun e he => Or.inr ⟨p.1, he, e', he', hp⟩
def gluedConfiguration (u : B.links → ComplexMatrix2.specialUnitary)
    (η : ↥(B.thickened \ (B.links : Set (SliceLink μ))) → ComplexMatrix2.specialUnitary) :
    B.thickened → ComplexMatrix2.specialUnitary :=
  open Classical in
  fun e => if h : e.1 ∈ B.links then u ⟨e.1, h⟩ else η ⟨e.1, e.2, h⟩
def sliceEnergy (β : ℝ) (u : B.links → ComplexMatrix2.specialUnitary)
    (η : ↥(B.thickened \ (B.links : Set (SliceLink μ))) → ComplexMatrix2.specialUnitary) : ℂ :=
  (β : ℂ) * ∑ᶠ p : B.touchingPlaquettes,
    (1 - (1 / 2 : ℂ) *
      ComplexMatrix2.fullTrace
        ((plaquetteHolonomy p.1 (B.links_subset_thickened p) (B.gluedConfiguration u η) :
          ComplexMatrix2.specialUnitary) : ComplexMatrix2))
end Block
end YangMills.Construction.TransferOperators
end
