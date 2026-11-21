import YangMills.Construction.TransferOperators.BondKernelAndLayerEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open InfiniteLattice SpinHarmonics Matrices.ComplexMatrix2
namespace TransferOperators
variable {μ : Fin 4}
namespace SlicePlaquette
variable (p : SlicePlaquette μ)
def cornerSites : Set (SliceSite μ) := {y | (y : LatticePoint 1) ∈ p.1.cornerSet}
theorem origin_mem_cornerSites : p.origin ∈ p.cornerSites :=
  Or.inl rfl
theorem links_subset_linksWithin_cornerSites : p.links ⊆ linksWithin p.cornerSites := by
  have h₀ : ((p.origin : SliceSite μ) : LatticePoint 1) ∈ p.1.cornerSet := Or.inl rfl
  have h₁ : p.1.corner + axisStep 1 p.1.lowAxis ∈ p.1.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have h₂ : p.1.corner + axisStep 1 p.1.lowAxis + axisStep 1 p.1.highAxis ∈ p.1.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have h₃ : p.1.corner + axisStep 1 p.1.highAxis ∈ p.1.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have h₄ : p.1.corner + axisStep 1 p.1.highAxis + axisStep 1 p.1.lowAxis ∈ p.1.cornerSet := by
    rw [add_right_comm]
    exact h₂
  rintro b (rfl | rfl | rfl | rfl)
  · exact ⟨h₀, h₁⟩
  · exact ⟨h₁, h₂⟩
  · exact ⟨h₃, h₄⟩
  · exact ⟨h₀, h₃⟩
theorem injective_cornerAxes :
    Function.Injective fun p : SlicePlaquette μ => (p.1.corner, p.1.lowAxis, p.1.highAxis) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Subtype.ext (ElementaryPlaquette.ext h.1 h.2.1 h.2.2)
theorem finite_setOf_mem_links (b : SliceLink μ) :
    {p : SlicePlaquette μ | b ∈ p.links}.Finite := by
  have hT : ({b.1.initial} ∪ range fun ρ : Fin 4 => b.1.initial - axisStep 1 ρ :
      Set (LatticePoint 1)).Finite :=
    (finite_singleton _).union (finite_range _)
  refine Set.Finite.of_finite_image (f := fun p : SlicePlaquette μ =>
    (p.1.corner, p.1.lowAxis, p.1.highAxis)) ?_ injective_cornerAxes.injOn
  refine (hT.prod (finite_univ (α := Fin 4 × Fin 4))).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨?_, mem_univ _⟩
  rcases hp with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨p.1.lowAxis, add_sub_cancel_right _ _⟩
  · exact Or.inr ⟨p.1.highAxis, add_sub_cancel_right _ _⟩
  · exact Or.inl rfl
theorem links_finite : p.links.Finite := by
  unfold SlicePlaquette.links
  exact Set.toFinite _
end SlicePlaquette
namespace Block
variable (B : Block μ)
theorem subset_thickened : (B.links : Set (SliceLink μ)) ⊆ B.thickened :=
  subset_union_left
theorem thickened_finite : B.thickened.Finite := by
  refine (B.links.finite_toSet.union ((B.links.finite_toSet.biUnion fun b' _ =>
    (SlicePlaquette.finite_setOf_mem_links b').biUnion fun p _ =>
      p.links_finite))).subset ?_
  rintro b (hb | ⟨p, hb, b', hb', hp⟩)
  · exact Or.inl hb
  · exact Or.inr (mem_iUnion₂.2 ⟨b', hb', mem_iUnion₂.2 ⟨p, hp, hb⟩⟩)
instance instFiniteThickened : Finite B.thickened := B.thickened_finite.to_subtype
def thickenedBlock : Block μ where
  links := B.thickened_finite.toFinset
  links_nonempty := by
    obtain ⟨b, hb⟩ := B.links_nonempty
    exact ⟨b, B.thickened_finite.mem_toFinset.2 (B.subset_thickened hb)⟩
theorem thickened_subset_linksWithin : B.thickened ⊆ linksWithin B.thickenedBlock.vertices :=
  fun b hb =>
    have h : b ∈ B.thickenedBlock.links := B.thickened_finite.mem_toFinset.2 hb
    ⟨⟨b, h, Or.inl rfl⟩, ⟨b, h, Or.inr rfl⟩⟩
theorem links_subset_linksWithin_thickenedBlock :
    (B.links : Set (SliceLink μ)) ⊆ linksWithin B.thickenedBlock.vertices :=
  B.subset_thickened.trans B.thickened_subset_linksWithin
theorem collar_subset_linksWithin_thickenedBlock :
    B.thickened \ (B.links : Set (SliceLink μ)) ⊆ linksWithin B.thickenedBlock.vertices :=
  sdiff_subset.trans B.thickened_subset_linksWithin
def sliceEnergyOnThickened (β : ℝ) (w : B.thickened → specialUnitary) : ℂ :=
  B.sliceEnergy β (fun b => w ⟨b.1, B.subset_thickened b.2⟩) fun b => w ⟨b.1, b.2.1⟩
end Block
namespace KernelSymmetryAndGaugeInvariance
def Statement : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ (B : Type) [Finite B] [Nonempty B],
      (∀ u u' : B → specialUnitary,
        linkProductKernel β u u' = linkProductKernel β u' u ∧
        (linkProductKernel β u u').im = 0 ∧
        Real.exp (-2 * β * (Nat.card B : ℝ)) ≤ (linkProductKernel β u u').re ∧
        (linkProductKernel β u u').re ≤ 1) ∧
      (fun w : B ⊕ B → specialUnitary =>
        linkProductKernel β (fun b => w (Sum.inl b)) fun b => w (Sum.inr b)) ∈ smoothSet) ∧
    (∀ (μ : Fin 4) (B : Block μ) (g : B.vertices → specialUnitary)
      (u u' : ↥(B.links : Set (SliceLink μ)) → specialUnitary),
      linkProductKernel β
          (gaugeAct (v := B.vertices) (fun b hb => ⟨⟨b, hb, Or.inl rfl⟩, ⟨b, hb, Or.inr rfl⟩⟩) g u)
          (gaugeAct (v := B.vertices) (fun b hb => ⟨⟨b, hb, Or.inl rfl⟩, ⟨b, hb, Or.inr rfl⟩⟩) g u') =
        linkProductKernel β u u') ∧
    (∀ (μ : Fin 4) (p : SlicePlaquette μ) (u : p.links → specialUnitary)
      (g : p.cornerSites → specialUnitary),
      plaquetteHolonomy p Subset.rfl (gaugeAct p.links_subset_linksWithin_cornerSites g u) =
        g ⟨p.origin, p.origin_mem_cornerSites⟩ * plaquetteHolonomy p Subset.rfl u *
          (g ⟨p.origin, p.origin_mem_cornerSites⟩)⁻¹) ∧
    (∀ (μ : Fin 4) (B : Block μ),
      IsRealEntryPolynomial (B.sliceEnergyOnThickened β) ∧
      ∀ (u : B.links → specialUnitary)
        (η : ↥(B.thickened \ (B.links : Set (SliceLink μ))) → specialUnitary)
        (g : B.thickenedBlock.vertices → specialUnitary),
        B.sliceEnergy β (gaugeAct B.links_subset_linksWithin_thickenedBlock g u)
            (gaugeAct B.collar_subset_linksWithin_thickenedBlock g η) =
          B.sliceEnergy β u η)
end KernelSymmetryAndGaugeInvariance
end TransferOperators
end YangMills.Construction
end
