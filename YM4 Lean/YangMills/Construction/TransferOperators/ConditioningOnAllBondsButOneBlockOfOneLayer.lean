import YangMills.Construction.InfiniteLattice.WilsonWindows
import YangMills.Construction.TransferOperators.BondKernelAndLayerEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
open MeasureTheory Set InfiniteLattice
variable {μ : Fin 4}
def Stack.IsInteriorLevel (S : Stack) (j : ℤ) : Prop := S.lower < j ∧ j < S.upper
theorem spatialLink_injective (j : ℤ) : Function.Injective (spatialLink μ j) := by
  intro b b' h
  have h₁ : pointAtLevel μ j b.source = pointAtLevel μ j b'.source :=
    congrArg (fun c : PositiveLink 1 => c.1.initial) h
  have h₂ : pointAtLevel μ j b.target = pointAtLevel μ j b'.target :=
    congrArg (fun c : PositiveLink 1 => c.1.terminal) h
  exact Subtype.ext (Link.ext (add_left_cancel (a := j • axisStep 1 μ) h₁)
    (add_left_cancel (a := j • axisStep 1 μ) h₂))
namespace Block
variable (B : Block μ)
def sliceWindow (j : ℤ) : LinkWindow 1 :=
  open Classical in
  { links := B.links.image fun b => (spatialLink μ j b).1
    isPositive := fun c hc => by
      classical
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hc
      exact (spatialLink μ j b).2 }
@[reducible] def complementSigma (j : ℤ) : MeasurableSpace (GaugeField 1) :=
  (B.sliceWindow j).exteriorSigma
def sliceLinkOfWindow (j : ℤ) (c : (B.sliceWindow j).links) : B.links :=
  have h : ∃ b ∈ B.links, (spatialLink μ j b).1 = c.1 := by
    classical
    exact Finset.mem_image.mp c.2
  ⟨h.choose, h.choose_spec.1⟩
theorem sliceLinkOfWindow_spatialLink (j : ℤ) (b : B.links)
    (h : (spatialLink μ j b.1).1 ∈ (B.sliceWindow j).links) :
    B.sliceLinkOfWindow j ⟨(spatialLink μ j b.1).1, h⟩ = b := by
  have h' : ∃ b' ∈ B.links, (spatialLink μ j b').1 = (spatialLink μ j b.1).1 := by
    classical
    exact Finset.mem_image.mp h
  exact Subtype.ext (spatialLink_injective j (Subtype.ext h'.choose_spec.2))
end Block
namespace Stack
variable (S : Stack) (B : Block μ)
def transportedAssignments (U : GaugeField 1) (j : ℤ)
    (v : B.links → Matrices.ComplexMatrix2.specialUnitary) :
    (B.sliceWindow j).Assignments :=
  fun c =>
    (S.parallelTransport μ U j (B.sliceLinkOfWindow j c).1.source)⁻¹ * v (B.sliceLinkOfWindow j c) *
      S.parallelTransport μ U j (B.sliceLinkOfWindow j c).1.target
def withTransported (U : GaugeField 1) (j : ℤ)
    (v : B.links → Matrices.ComplexMatrix2.specialUnitary) : GaugeField 1 :=
  (B.sliceWindow j).glue zero_lt_one (S.transportedAssignments B U j v) U
theorem spatialLinkVariable_withTransported (U : GaugeField 1) (j : ℤ)
    (v : B.links → Matrices.ComplexMatrix2.specialUnitary) (b : B.links) :
    spatialLinkVariable μ (S.withTransported B U j v) j b.1 =
      (S.parallelTransport μ U j b.1.source)⁻¹ * v b * S.parallelTransport μ U j b.1.target := by
  have hm : (spatialLink μ j b.1).1 ∈ (B.sliceWindow j).links := by
    classical
    exact Finset.mem_image.mpr ⟨b.1, b.2, rfl⟩
  have key : (S.withTransported B U j v) (spatialLink μ j b.1).1 =
      S.transportedAssignments B U j v ⟨_, hm⟩ := dif_pos hm
  rw [spatialLinkVariable, key, transportedAssignments, B.sliceLinkOfWindow_spatialLink j b hm]
def rimValues (U : GaugeField 1) (j : ℤ) :
    ↥(B.thickened \ (B.links : Set (SliceLink μ))) → Matrices.ComplexMatrix2.specialUnitary :=
  S.transportedRestriction μ U j (B.thickened \ (B.links : Set (SliceLink μ)))
def blockValues (U : GaugeField 1) (j : ℤ) : B.links → Matrices.ComplexMatrix2.specialUnitary :=
  S.transportedRestriction μ U j (B.links : Set (SliceLink μ))
def localPartition (β : ℝ) (U : GaugeField 1) (j : ℤ) : ℂ :=
  ∫ v : B.links → Matrices.ComplexMatrix2.specialUnitary,
    Complex.exp (-B.sliceEnergy β v (S.rimValues B U j)) *
      linkProductKernel β (S.blockValues B U (j - 1)) v *
        linkProductKernel β v (S.blockValues B U (j + 1))
    ∂Matrices.ComplexMatrix2.haarPi B.links
end Stack
end YangMills.Construction.TransferOperators
end
