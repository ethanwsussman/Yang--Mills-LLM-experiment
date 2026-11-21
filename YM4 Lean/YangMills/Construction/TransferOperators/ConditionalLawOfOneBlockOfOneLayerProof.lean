import YangMills.Construction.InfiniteLattice.EquilibriumEquationsGaugeInvarianceAndCompactness
import YangMills.Construction.TransferOperators.ConditionalLawOfOneBlockOfOneLayer
import YangMills.Construction.TransferOperators.ObjectsOfTheStepBetweenSymmetricStacks
import YangMills.Construction.TransferOperators.TemporalGaugeOfAStack
import YangMills.Construction.TransferOperators.TorusWeightIsAProductOverLayersProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice Matrices
namespace TransferOperators.BlockConditionalLaw
variable {μ : Fin 4}
theorem axisStep_injective : Function.Injective (axisStep (1 : ℝ)) := by
  intro ρ σ h
  by_contra hne
  have hc : (Pi.single ρ (1 : ℝ) : AmbientSpace) ρ = (Pi.single σ (1 : ℝ) : AmbientSpace) ρ :=
    congrFun (congrArg Subtype.val h) ρ
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hc
  norm_num at hc
theorem eq_and_eq_of_forwardFrom_eq {x x' : LatticePoint 1} {ρ ρ' : Fin 4}
    (h : Link.forwardFrom x ρ = Link.forwardFrom x' ρ') : x = x' ∧ ρ = ρ' := by
  have h₁ : x = x' := congrArg Link.initial h
  have h₂ : x + axisStep 1 ρ = x' + axisStep 1 ρ' := congrArg Link.terminal h
  subst h₁
  exact ⟨rfl, axisStep_injective (add_left_cancel h₂)⟩
theorem sliceLink_eq_forwardFrom (b : SliceLink μ) : b.1 = Link.forwardFrom b.1.initial b.axis :=
  Link.ext rfl (by
    have h := b.terminal_sub_initial
    change b.1.terminal = b.1.initial + axisStep 1 b.axis
    rw [← h]
    abel)
theorem spatialLink_eq_forwardFrom (j : ℤ) (b : SliceLink μ) :
    (spatialLink μ j b).1 = Link.forwardFrom (pointAtLevel μ j b.source) b.axis :=
  Link.ext rfl (pointAtLevel_target μ j b)
theorem pointAtLevel_sub_one (j : ℤ) (y : SliceSite μ) :
    pointAtLevel μ (j - 1) y = pointAtLevel μ j y - axisStep 1 μ := by
  have h := pointAtLevel_succ μ (j - 1) y
  rw [sub_add_cancel] at h
  rw [h]
  abel
theorem pointAtLevel_injective (j : ℤ) : Function.Injective (pointAtLevel μ j) := fun _ _ h =>
  Subtype.ext (add_left_cancel h)
section Plaquettes
open CutoffLattice (faceOfPair)
theorem faceOfPair_of_lt (x : LatticePoint 1) {ρ σ : Fin 4} (h : ρ < σ) (hne : ρ ≠ σ) :
    faceOfPair x ρ σ hne = ⟨x, ρ, σ, h⟩ :=
  dif_pos h
theorem faceOfPair_of_gt (x : LatticePoint 1) {ρ σ : Fin 4} (h : σ < ρ) (hne : ρ ≠ σ) :
    faceOfPair x ρ σ hne = ⟨x, σ, ρ, h⟩ :=
  dif_neg (not_lt.mpr h.le)
theorem corner_faceOfPair (x : LatticePoint 1) {ρ σ : Fin 4} (hne : ρ ≠ σ) :
    (faceOfPair x ρ σ hne).corner = x := by apply _root_.YangMills.Construction.TransferOperators.SliceProduct.faceOfPair_corner <;> assumption
theorem axes_faceOfPair (x : LatticePoint 1) {ρ σ : Fin 4} (hne : ρ ≠ σ) :
    ((faceOfPair x ρ σ hne).lowAxis = ρ ∧ (faceOfPair x ρ σ hne).highAxis = σ) ∨
      ((faceOfPair x ρ σ hne).lowAxis = σ ∧ (faceOfPair x ρ σ hne).highAxis = ρ) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [faceOfPair_of_lt x h]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [faceOfPair_of_gt x h]
    exact Or.inr ⟨rfl, rfl⟩
theorem forwardFrom_mem_edges_faceOfPair (x : LatticePoint 1) {ρ σ : Fin 4} (hne : ρ ≠ σ) :
    Link.forwardFrom x ρ ∈ (faceOfPair x ρ σ hne).edges := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [faceOfPair_of_lt x h]
    simp [ElementaryPlaquette.edges]
  · rw [faceOfPair_of_gt x h]
    simp [ElementaryPlaquette.edges]
theorem forwardFrom_add_mem_edges_faceOfPair (x : LatticePoint 1) {ρ σ : Fin 4} (hne : ρ ≠ σ) :
    Link.forwardFrom (x + axisStep 1 σ) ρ ∈ (faceOfPair x ρ σ hne).edges := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [faceOfPair_of_lt x h]
    simp [ElementaryPlaquette.edges]
  · rw [faceOfPair_of_gt x h]
    simp [ElementaryPlaquette.edges]
theorem exists_faceOfPair_of_forwardFrom_mem_edges {p : ElementaryPlaquette 1}
    {x : LatticePoint 1} {ρ : Fin 4} (h : Link.forwardFrom x ρ ∈ p.edges) :
    ∃ (σ : Fin 4) (hσ : ρ ≠ σ), p = faceOfPair x ρ σ hσ ∨
      p = faceOfPair (x - axisStep 1 σ) ρ σ hσ := by
  obtain ⟨y, f, s, hlt⟩ := p
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · obtain ⟨rfl, rfl⟩ := eq_and_eq_of_forwardFrom_eq h
    exact ⟨s, hlt.ne, Or.inl (faceOfPair_of_lt _ hlt _).symm⟩
  · obtain ⟨rfl, rfl⟩ := eq_and_eq_of_forwardFrom_eq h
    refine ⟨f, hlt.ne', Or.inr ?_⟩
    rw [faceOfPair_of_gt _ hlt, add_sub_cancel_right]
  · obtain ⟨rfl, rfl⟩ := eq_and_eq_of_forwardFrom_eq h
    refine ⟨s, hlt.ne, Or.inr ?_⟩
    rw [faceOfPair_of_lt _ hlt, add_sub_cancel_right]
  · obtain ⟨rfl, rfl⟩ := eq_and_eq_of_forwardFrom_eq h
    exact ⟨f, hlt.ne', Or.inl (faceOfPair_of_gt _ hlt _).symm⟩
def slicePlaquetteOfPair (y : SliceSite μ) {ρ σ : Fin 4} (hρ : ρ ≠ μ) (hσ : σ ≠ μ) (h : ρ ≠ σ) :
    SlicePlaquette μ :=
  ⟨faceOfPair (y : LatticePoint 1) ρ σ h, by
    intro c hc
    rcases lt_or_gt_of_ne h with hlt | hlt
    · rw [faceOfPair_of_lt _ hlt] at hc
      simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact y.2
      · exact add_axisStep_mem_sliceLattice y.2 hρ
      · exact add_axisStep_mem_sliceLattice (add_axisStep_mem_sliceLattice y.2 hρ) hσ
      · exact add_axisStep_mem_sliceLattice y.2 hσ
    · rw [faceOfPair_of_gt _ hlt] at hc
      simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact y.2
      · exact add_axisStep_mem_sliceLattice y.2 hσ
      · exact add_axisStep_mem_sliceLattice (add_axisStep_mem_sliceLattice y.2 hσ) hρ
      · exact add_axisStep_mem_sliceLattice y.2 hρ⟩
theorem shiftedPlaquette_slicePlaquetteOfPair (j : ℤ) (y : SliceSite μ) {ρ σ : Fin 4}
    (hρ : ρ ≠ μ) (hσ : σ ≠ μ) (h : ρ ≠ σ) :
    shiftedPlaquette μ j (slicePlaquetteOfPair y hρ hσ h) =
      faceOfPair (pointAtLevel μ j y) ρ σ h := by
  have hs : (y : LatticePoint 1) + j • axisStep 1 μ = pointAtLevel μ j y := add_comm _ _
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [faceOfPair_of_lt _ hlt]
    simp only [shiftedPlaquette, slicePlaquetteOfPair, faceOfPair_of_lt _ hlt,
      CutoffLattice.translateFace, CutoffLattice.face, hs]
  · rw [faceOfPair_of_gt _ hlt]
    simp only [shiftedPlaquette, slicePlaquetteOfPair, faceOfPair_of_gt _ hlt,
      CutoffLattice.translateFace, CutoffLattice.face, hs]
theorem mem_links_of_mem_edges {p : SlicePlaquette μ} {b : SliceLink μ}
    (h : b.1 ∈ p.1.edges) : b ∈ p.links := by
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [SlicePlaquette.links, mem_insert_iff, mem_singleton_iff]
  rcases h with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
theorem spatialLink_mem_edges_shiftedPlaquette (j : ℤ) {p : SlicePlaquette μ} {b : SliceLink μ}
    (h : b ∈ p.links) : (spatialLink μ j b).1 ∈ (shiftedPlaquette μ j p).edges := by
  have key : ∀ (z : LatticePoint 1) (σ : Fin 4), b.1 = Link.forwardFrom z σ →
      (spatialLink μ j b).1 = Link.forwardFrom (z + j • axisStep 1 μ) σ := by
    intro z σ hb
    obtain ⟨h₁, h₂⟩ := eq_and_eq_of_forwardFrom_eq ((sliceLink_eq_forwardFrom b).symm.trans hb)
    rw [spatialLink_eq_forwardFrom, h₂, ← h₁, pointAtLevel, add_comm]
    rfl
  have hm : ∀ z : LatticePoint 1, (z + axisStep 1 p.1.lowAxis + j • axisStep 1 μ) =
      z + j • axisStep 1 μ + axisStep 1 p.1.lowAxis := fun z => add_right_comm _ _ _
  have hm' : ∀ z : LatticePoint 1, (z + axisStep 1 p.1.highAxis + j • axisStep 1 μ) =
      z + j • axisStep 1 μ + axisStep 1 p.1.highAxis := fun z => add_right_comm _ _ _
  simp only [SlicePlaquette.links, mem_insert_iff, mem_singleton_iff] at h
  simp only [shiftedPlaquette, CutoffLattice.translateFace, CutoffLattice.face,
    ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (key _ _ rfl)
  · refine Or.inr (Or.inl ?_)
    rw [key (p.1.corner + axisStep 1 p.1.lowAxis) _ rfl, hm]
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [key (p.1.corner + axisStep 1 p.1.highAxis) _ rfl, hm']
  · exact Or.inr (Or.inr (Or.inr (key _ _ rfl)))
theorem corner_temporalPlaquette (j : ℤ) (b : SliceLink μ) :
    (temporalPlaquette μ j b).corner = pointAtLevel μ j b.source :=
  corner_faceOfPair _ _
theorem temporalPlaquette_injective (j : ℤ) : Function.Injective (temporalPlaquette μ j) := by
  intro b b' h
  have ht : b.source = b'.source := pointAtLevel_injective j (by
    rw [← corner_temporalPlaquette, ← corner_temporalPlaquette, h])
  have hf := congrArg ElementaryPlaquette.lowAxis h
  have hs := congrArg ElementaryPlaquette.highAxis h
  have hd : b.axis = b'.axis := by
    rcases axes_faceOfPair (pointAtLevel μ j b.source) b.axis_ne with
        ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      rcases axes_faceOfPair (pointAtLevel μ j b'.source) b'.axis_ne with
        ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
    · exact h₁.symm.trans (hf.trans h₃)
    · exact absurd (h₁.symm.trans (hf.trans h₃)) b.axis_ne
    · exact absurd (h₃.symm.trans (hf.symm.trans h₁)) b'.axis_ne
    · exact h₂.symm.trans (hs.trans h₄)
  refine Subtype.ext ?_
  rw [sliceLink_eq_forwardFrom b, sliceLink_eq_forwardFrom b', hd]
  exact congrArg (fun y : SliceSite μ => Link.forwardFrom (y : LatticePoint 1) b'.axis) ht
theorem shiftedPlaquette_injective (j : ℤ) : Function.Injective (shiftedPlaquette μ j) := by
  intro p q h
  have h₁ : p.1.corner + j • axisStep 1 μ = q.1.corner + j • axisStep 1 μ :=
    congrArg ElementaryPlaquette.corner h
  have h₂ : p.1.lowAxis = q.1.lowAxis := by
    have h' := congrArg ElementaryPlaquette.lowAxis h
    exact h'
  have h₃ : p.1.highAxis = q.1.highAxis := by
    have h' := congrArg ElementaryPlaquette.highAxis h
    exact h'
  exact SlicePlaquette.injective_cornerAxes (Prod.ext (add_right_cancel h₁) (Prod.ext h₂ h₃))
theorem shiftedPlaquette_ne_temporalPlaquette (j j' : ℤ) (p : SlicePlaquette μ)
    (b : SliceLink μ) : shiftedPlaquette μ j p ≠ temporalPlaquette μ j' b := by
  intro h
  have hf : p.1.lowAxis = (temporalPlaquette μ j' b).lowAxis := by
    have h' := congrArg ElementaryPlaquette.lowAxis h
    exact h'
  have hs : p.1.highAxis = (temporalPlaquette μ j' b).highAxis := by
    have h' := congrArg ElementaryPlaquette.highAxis h
    exact h'
  rcases axes_faceOfPair (pointAtLevel μ j' b.source) b.axis_ne with
    ⟨-, h₂⟩ | ⟨h₁, -⟩
  · exact p.highAxis_ne (hs.trans h₂)
  · exact p.lowAxis_ne (hf.trans h₁)
theorem temporalPlaquette_ne_of_ne {j j' : ℤ} (hj : j ≠ j') (b b' : SliceLink μ) :
    temporalPlaquette μ j b ≠ temporalPlaquette μ j' b' := by
  intro h
  have h₁ := congrArg ElementaryPlaquette.corner h
  rw [corner_temporalPlaquette, corner_temporalPlaquette] at h₁
  have c : ((pointAtLevel μ j b.source : LatticePoint 1) : AmbientSpace) μ =
    ((pointAtLevel μ j' b'.source : LatticePoint 1) : AmbientSpace) μ :=
    congrFun (congrArg Subtype.val h₁) μ
  rw [coe_pointAtLevel_apply_axis, coe_pointAtLevel_apply_axis] at c
  exact hj (by exact_mod_cast c)
end Plaquettes
section Window
variable (B : Block μ)
theorem spatialLink_mem_sliceWindow_iff {j j' : ℤ} {b : SliceLink μ} :
    (spatialLink μ j' b).1 ∈ (B.sliceWindow j).links ↔ j' = j ∧ b ∈ B.links := by
  classical
  constructor
  · intro h
    obtain ⟨b', hb', e⟩ := Finset.mem_image.mp h
    obtain ⟨rfl, rfl⟩ := eq_and_eq_of_spatialLink_eq e
    exact ⟨rfl, hb'⟩
  · rintro ⟨rfl, hb⟩
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
theorem temporalLink_notMem_sliceWindow (j j' : ℤ) (y : SliceSite μ) :
    (temporalLink μ j' y).1 ∉ (B.sliceWindow j).links := by
  classical
  intro h
  obtain ⟨b', -, e⟩ := Finset.mem_image.mp h
  exact spatialLink_ne_temporalLink _ _ _ _ e
theorem touchingPlaquettes_finite : B.touchingPlaquettes.Finite := by apply _root_.YangMills.Construction.TransferOperators.Block.touchingPlaquettes_finite <;> assumption
theorem facesMeeting_sliceWindow (j : ℤ) :
    facesMeeting ((B.sliceWindow j).links : Set (Link 1)) =
      (shiftedPlaquette μ j '' B.touchingPlaquettes ∪
        temporalPlaquette μ j '' (B.links : Set (SliceLink μ))) ∪
        temporalPlaquette μ (j - 1) '' (B.links : Set (SliceLink μ)) := by
  classical
  ext p
  constructor
  · rintro ⟨c, hc, hcL⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hcL)
    have hc' : Link.forwardFrom (pointAtLevel μ j b.source) b.axis ∈ p.edges := by
      rw [← spatialLink_eq_forwardFrom]
      exact hc
    obtain ⟨σ, hσ, h | h⟩ := exists_faceOfPair_of_forwardFrom_mem_edges hc'
    · by_cases hσμ : σ = μ
      · subst hσμ
        exact Or.inl (Or.inr ⟨b, hb, h.symm⟩)
      · refine Or.inl (Or.inl ⟨slicePlaquetteOfPair b.source b.axis_ne hσμ hσ, ⟨b, hb, ?_⟩, ?_⟩)
        · refine mem_links_of_mem_edges ?_
          rw [sliceLink_eq_forwardFrom b]
          exact forwardFrom_mem_edges_faceOfPair (b.source : LatticePoint 1) hσ
        · rw [shiftedPlaquette_slicePlaquetteOfPair, h]
    · by_cases hσμ : σ = μ
      · subst hσμ
        refine Or.inr ⟨b, hb, ?_⟩
        rw [h, temporalPlaquette]
        simp only [pointAtLevel_sub_one]
      · have hm : (b.source : LatticePoint 1) - axisStep 1 σ ∈ sliceLattice μ := by
          have h₁ : ((b.source : LatticePoint 1) : AmbientSpace) μ = 0 := b.source.2
          change ((b.source : LatticePoint 1) : AmbientSpace) μ -
            (Pi.single σ (1 : ℝ) : AmbientSpace) μ = 0
          rw [h₁, Pi.single_eq_of_ne (Ne.symm hσμ), sub_zero]
        refine Or.inl (Or.inl ⟨slicePlaquetteOfPair ⟨_, hm⟩ b.axis_ne hσμ hσ, ⟨b, hb, ?_⟩, ?_⟩)
        · refine mem_links_of_mem_edges ?_
          have hf := forwardFrom_add_mem_edges_faceOfPair
            ((b.source : LatticePoint 1) - axisStep 1 σ) hσ
          rw [sub_add_cancel] at hf
          rw [sliceLink_eq_forwardFrom b]
          exact hf
        · rw [shiftedPlaquette_slicePlaquetteOfPair, h]
          congr 1
          change j • axisStep 1 μ + ((b.source : LatticePoint 1) - axisStep 1 σ) =
            j • axisStep 1 μ + (b.source : LatticePoint 1) - axisStep 1 σ
          abel
  · rintro ((⟨q, ⟨b, hb, hq⟩, rfl⟩ | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩)
    · exact ⟨_, spatialLink_mem_edges_shiftedPlaquette j hq,
        (spatialLink_mem_sliceWindow_iff B).2 ⟨rfl, hb⟩⟩
    · refine ⟨_, ?_, (spatialLink_mem_sliceWindow_iff B).2 ⟨rfl, hb⟩⟩
      change (spatialLink μ j b).1 ∈ (temporalPlaquette μ j b).edges
      rw [spatialLink_eq_forwardFrom]
      exact forwardFrom_mem_edges_faceOfPair _ b.axis_ne
    · refine ⟨_, ?_, (spatialLink_mem_sliceWindow_iff B).2 ⟨rfl, hb⟩⟩
      change (spatialLink μ j b).1 ∈ (temporalPlaquette μ (j - 1) b).edges
      have hf := forwardFrom_add_mem_edges_faceOfPair (pointAtLevel μ (j - 1) b.source) b.axis_ne
      rw [← pointAtLevel_succ, sub_add_cancel] at hf
      rw [spatialLink_eq_forwardFrom]
      exact hf
theorem finsum_facesMeeting_sliceWindow (j : ℤ) (f : ElementaryPlaquette 1 → ℝ) :
    ∑ᶠ p ∈ facesMeeting ((B.sliceWindow j).links : Set (Link 1)), f p =
      ∑ᶠ p : B.touchingPlaquettes, f (shiftedPlaquette μ j p.1) +
        ∑ b : B.links, f (temporalPlaquette μ j b.1) +
        ∑ b : B.links, f (temporalPlaquette μ (j - 1) b.1) := by
  have hfin₁ : (shiftedPlaquette μ j '' B.touchingPlaquettes).Finite :=
    (touchingPlaquettes_finite B).image _
  have hfin₂ : (temporalPlaquette μ j '' (B.links : Set (SliceLink μ))).Finite :=
    B.links.finite_toSet.image _
  have hfin₃ : (temporalPlaquette μ (j - 1) '' (B.links : Set (SliceLink μ))).Finite :=
    B.links.finite_toSet.image _
  have hd₁ : Disjoint (shiftedPlaquette μ j '' B.touchingPlaquettes)
      (temporalPlaquette μ j '' (B.links : Set (SliceLink μ))) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨q, -, rfl⟩ ⟨b, -, h⟩
    exact shiftedPlaquette_ne_temporalPlaquette _ _ _ _ h.symm
  have hd₂ : Disjoint (shiftedPlaquette μ j '' B.touchingPlaquettes ∪
      temporalPlaquette μ j '' (B.links : Set (SliceLink μ)))
      (temporalPlaquette μ (j - 1) '' (B.links : Set (SliceLink μ))) := by
    refine Set.disjoint_left.2 ?_
    rintro _ (⟨q, -, rfl⟩ | ⟨b, -, rfl⟩) ⟨b', -, h⟩
    · exact shiftedPlaquette_ne_temporalPlaquette _ _ _ _ h.symm
    · exact temporalPlaquette_ne_of_ne (by omega) _ _ h.symm
  rw [facesMeeting_sliceWindow, finsum_mem_union hd₂ (hfin₁.union hfin₂) hfin₃,
    finsum_mem_union hd₁ hfin₁ hfin₂,
    finsum_mem_image (shiftedPlaquette_injective j).injOn,
    finsum_mem_image (temporalPlaquette_injective j).injOn,
    finsum_mem_image (temporalPlaquette_injective (j - 1)).injOn,
    finsum_mem_coe_finset, finsum_mem_coe_finset,
    finsum_set_coe_eq_finsum_mem B.touchingPlaquettes
      (f := fun p => f (shiftedPlaquette μ j p)),
    Finset.sum_coe_sort B.links fun b => f (temporalPlaquette μ j b),
    Finset.sum_coe_sort B.links fun b => f (temporalPlaquette μ (j - 1) b)]
end Window
section Replacement
variable (S : Stack) (B : Block μ)
theorem glue_apply_of_notMem (W : LinkWindow 1) (V : W.Assignments) (U : GaugeField 1)
    {c : Link 1} (hc : c.IsPositivelyOriented) (hW : c ∉ W.links) :
    (W.glue zero_lt_one V U) c = U c := by
  have h' : c.opposite ∉ W.links := fun h =>
    Link.opposite_not_isPositivelyOriented zero_lt_one hc (W.isPositive _ h)
  exact (dif_neg hW).trans (dif_neg h')
theorem temporalLinkVariable_withTransported (U : GaugeField 1) (j j' : ℤ)
    (v : B.links → ComplexMatrix2.specialUnitary) (y : SliceSite μ) :
    temporalLinkVariable μ (S.withTransported B U j v) j' y = temporalLinkVariable μ U j' y :=
  glue_apply_of_notMem _ _ _ (temporalLink μ j' y).2 (temporalLink_notMem_sliceWindow B j j' y)
theorem parallelTransport_withTransported (U : GaugeField 1) (j j' : ℤ)
    (v : B.links → ComplexMatrix2.specialUnitary) (y : SliceSite μ) :
    S.parallelTransport μ (S.withTransported B U j v) j' y = S.parallelTransport μ U j' y := by
  simp only [Stack.parallelTransport, temporalLinkVariable_withTransported]
theorem transportedLinkVariable_withTransported_self (U : GaugeField 1) (j : ℤ)
    (v : B.links → ComplexMatrix2.specialUnitary) (b : B.links) :
    S.transportedLinkVariable μ (S.withTransported B U j v) j b.1 = v b := by
  rw [Stack.transportedLinkVariable, parallelTransport_withTransported,
    parallelTransport_withTransported, Stack.spatialLinkVariable_withTransported]
  group
theorem transportedLinkVariable_withTransported_of_not (U : GaugeField 1) (j j' : ℤ)
    (v : B.links → ComplexMatrix2.specialUnitary) {b' : SliceLink μ}
    (h : ¬ (j' = j ∧ b' ∈ B.links)) :
    S.transportedLinkVariable μ (S.withTransported B U j v) j' b' =
      S.transportedLinkVariable μ U j' b' := by
  have hv : spatialLinkVariable μ (S.withTransported B U j v) j' b' =
      spatialLinkVariable μ U j' b' :=
    glue_apply_of_notMem _ _ _ (spatialLink μ j' b').2
      fun hm => h ((spatialLink_mem_sliceWindow_iff B).1 hm)
  rw [Stack.transportedLinkVariable, Stack.transportedLinkVariable,
    parallelTransport_withTransported, parallelTransport_withTransported, hv]
end Replacement
section Density
variable (S : Stack) (B : Block μ) {β : ℝ} {j : ℤ}
theorem ofReal_exp_neg_mul_add (A T₁ T₂ : ℝ) :
    ((Real.exp (-β * (A + T₁ + T₂)) : ℝ) : ℂ) =
      Complex.exp (-((β : ℂ) * (A : ℂ))) * Complex.exp (-(β : ℂ) * (T₁ : ℂ)) *
        Complex.exp (-(β : ℂ) * (T₂ : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring
theorem exp_neg_mul_sum_eq_linkProductKernel (a : B.links → ℝ)
    (u u' : B.links → ComplexMatrix2.specialUnitary)
    (h : ∀ b, ((a b : ℝ) : ℂ) = 1 - (1 / 2 : ℂ) *
      ComplexMatrix2.fullTrace ((u b * (u' b)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)) :
    Complex.exp (-(β : ℂ) * ((∑ b, a b : ℝ) : ℂ)) = linkProductKernel β u u' := by
  rw [linkProductKernel, finprod_eq_prod_of_fintype, Complex.ofReal_sum, Finset.mul_sum,
    Complex.exp_sum]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [h b, singleBondWeight]
theorem localWeight_withTransported_eq_densityAt
    (hE : TemporalGauge.FaceEnergiesInTransported μ β S)
    (hj : S.IsInteriorLevel j) (U : GaugeField 1) (v : B.links → ComplexMatrix2.specialUnitary) :
    (((B.sliceWindow j).localWeight β (S.withTransported B U j v) : ℝ) : ℂ) =
      S.densityAt B β U j v := by
  obtain ⟨hlo, hhi⟩ := hj
  obtain ⟨hT, -, hL⟩ := hE (S.withTransported B U j v)
  have hA : (β : ℂ) * ((∑ᶠ p : B.touchingPlaquettes,
      faceEnergy (S.withTransported B U j v) (shiftedPlaquette μ j p.1) : ℝ) : ℂ) =
      B.sliceEnergy β v (S.rimValues B U j) := by
    have : Finite B.touchingPlaquettes := (touchingPlaquettes_finite B).to_subtype
    have hc := map_finsum Complex.ofRealHom
      (f := fun p : B.touchingPlaquettes =>
        faceEnergy (S.withTransported B U j v) (shiftedPlaquette μ j p.1))
      (Set.toFinite _)
    have hfam : S.transportedRestriction μ (S.withTransported B U j v) j
        (B.links : Set (SliceLink μ)) = v :=
      funext fun b => transportedLinkVariable_withTransported_self S B U j v b
    have hbd : S.transportedRestriction μ (S.withTransported B U j v) j
        (B.thickened \ (B.links : Set (SliceLink μ))) = S.rimValues B U j :=
      funext fun b => transportedLinkVariable_withTransported_of_not S B U j j v fun h => b.2.2 h.2
    have hL' := hL j B hlo.le hhi.le
    rw [hfam, hbd] at hL'
    rw [← hL']
    congr 1
  have hUp : Complex.exp (-(β : ℂ) * ((∑ b : B.links,
      faceEnergy (S.withTransported B U j v) (temporalPlaquette μ j b.1) : ℝ) : ℂ)) =
      linkProductKernel β v (S.blockValues B U (j + 1)) := by
    refine exp_neg_mul_sum_eq_linkProductKernel B _ _ _ fun b => ?_
    rw [hT j b.1 hlo.le hhi, transportedLinkVariable_withTransported_self,
      transportedLinkVariable_withTransported_of_not S B U j (j + 1) v (fun h => by omega)]
    rfl
  have hDown : Complex.exp (-(β : ℂ) * ((∑ b : B.links,
      faceEnergy (S.withTransported B U j v) (temporalPlaquette μ (j - 1) b.1) : ℝ) : ℂ)) =
      linkProductKernel β (S.blockValues B U (j - 1)) v := by
    refine exp_neg_mul_sum_eq_linkProductKernel B _ _ _ fun b => ?_
    rw [hT (j - 1) b.1 (by omega) (by omega), sub_add_cancel,
      transportedLinkVariable_withTransported_self,
      transportedLinkVariable_withTransported_of_not S B U j (j - 1) v (fun h => by omega)]
    rfl
  rw [LinkWindow.localWeight, finsum_facesMeeting_sliceWindow, ofReal_exp_neg_mul_add, hA, hUp,
    hDown, Stack.densityAt, Block.sliceDensity]
  ring
end Density
section ChangeOfVariables
variable (S : Stack) (B : Block μ)
theorem spatialLink_sliceLinkOfWindow (j : ℤ) (c : (B.sliceWindow j).links) :
    (spatialLink μ j (B.sliceLinkOfWindow j c).1).1 = c.1 := by
  have h : ∃ b ∈ B.links, (spatialLink μ j b).1 = c.1 := by
    classical
    exact Finset.mem_image.mp c.2
  exact h.choose_spec.2
def sliceWindowLinksEquiv (j : ℤ) : (B.sliceWindow j).links ≃ B.links :=
  Equiv.ofBijective (B.sliceLinkOfWindow j) ⟨fun c c' h => Subtype.ext (by
      rw [← spatialLink_sliceLinkOfWindow B j c, ← spatialLink_sliceLinkOfWindow B j c', h]),
    fun b => ⟨⟨(spatialLink μ j b.1).1, (spatialLink_mem_sliceWindow_iff B).2 ⟨rfl, b.2⟩⟩,
      B.sliceLinkOfWindow_spatialLink j b _⟩⟩
theorem measurePreserving_reindex (j : ℤ) :
    MeasurePreserving (fun (v : B.links → ComplexMatrix2.specialUnitary)
        (c : (B.sliceWindow j).links) => v (B.sliceLinkOfWindow j c))
      (ComplexMatrix2.haarPi B.links) (ComplexMatrix2.haarPi (B.sliceWindow j).links) := by
  have hmap := Measure.infinitePi_map_piCongrLeft
    (X := fun _ : (B.sliceWindow j).links => ComplexMatrix2.specialUnitary)
    (μ := fun _ : (B.sliceWindow j).links => ComplexMatrix2.haarProb)
    (sliceWindowLinksEquiv B j).symm
  have hfun : (MeasurableEquiv.piCongrLeft
      (fun _ : (B.sliceWindow j).links => ComplexMatrix2.specialUnitary)
      (sliceWindowLinksEquiv B j).symm : (B.links → ComplexMatrix2.specialUnitary) → _) =
      fun (v : B.links → ComplexMatrix2.specialUnitary) (c : (B.sliceWindow j).links) =>
        v (B.sliceLinkOfWindow j c) := by
    funext v c
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, sliceWindowLinksEquiv]
    rfl
  rw [hfun] at hmap
  exact ⟨by fun_prop, hmap⟩
theorem measurePreserving_transportedAssignments {j : ℤ}
    (hH : GibbsHaarKernels.HaarPiInvariance (B.sliceWindow j).links)
    (U : GaugeField 1) :
    MeasurePreserving (S.transportedAssignments B U j) (ComplexMatrix2.haarPi B.links)
      (B.sliceWindow j).haarProd :=
  (hH.1 (fun c => (S.parallelTransport μ U j (B.sliceLinkOfWindow j c).1.source)⁻¹)
    (fun c => S.parallelTransport μ U j (B.sliceLinkOfWindow j c).1.target)).comp
      (measurePreserving_reindex B j)
theorem measurableEmbedding_transportedAssignments (j : ℤ) (U : GaugeField 1) :
    MeasurableEmbedding (S.transportedAssignments B U j) := by
  have hc : Continuous (S.transportedAssignments B U j) :=
    continuous_pi fun c => (continuous_const.mul (continuous_apply _)).mul continuous_const
  have hi : Function.Injective (S.transportedAssignments B U j) := by
    intro v v' h
    funext b
    obtain ⟨c, rfl⟩ := (sliceWindowLinksEquiv B j).surjective b
    have hc' := congrFun h c
    simp only [Stack.transportedAssignments] at hc'
    exact mul_left_cancel (mul_right_cancel hc')
  exact (hc.isClosedEmbedding hi).measurableEmbedding
theorem blockAverage_eq_conditionalExpectation {β : ℝ} {j : ℤ}
    (hE : TemporalGauge.FaceEnergiesInTransported μ β S)
    (hH : GibbsHaarKernels.HaarPiInvariance (B.sliceWindow j).links)
    (hj : S.IsInteriorLevel j) (F : GaugeField 1 → ℂ) (U : GaugeField 1) :
    S.blockAverage B β j F U =
      (B.sliceWindow j).conditionalExpectation zero_lt_one β F U := by
  have hφ := measurePreserving_transportedAssignments S B hH U
  have he := measurableEmbedding_transportedAssignments S B j U
  have hnum : ∫ V, F ((B.sliceWindow j).glue zero_lt_one V U) *
        ((B.sliceWindow j).localWeight β ((B.sliceWindow j).glue zero_lt_one V U) : ℂ)
        ∂(B.sliceWindow j).haarProd =
      ∫ v, F (S.withTransported B U j v) * S.densityAt B β U j v
        ∂ComplexMatrix2.haarPi B.links := by
    rw [← hφ.integral_comp he]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    beta_reduce
    rw [← localWeight_withTransported_eq_densityAt S B hE hj U v]
    rfl
  have hden : ((∫ V, (B.sliceWindow j).localWeight β
        ((B.sliceWindow j).glue zero_lt_one V U) ∂(B.sliceWindow j).haarProd : ℝ) : ℂ) =
      S.localPartition B β U j := by
    rw [S.localPartition_eq_integral_densityAt B β U j, ← hφ.integral_comp he,
      ← integral_complex_ofReal]
    exact integral_congr_ae (ae_of_all _ fun v => localWeight_withTransported_eq_densityAt S B hE hj U v)
  rw [LinkWindow.conditionalExpectation, hnum, hden, Stack.blockAverage, one_div,
    div_eq_inv_mul]
end ChangeOfVariables
theorem exteriorSigma_le (W : LinkWindow 1) :
    W.exteriorSigma ≤ (inferInstance : MeasurableSpace (GaugeField 1)) := by
  refine iSup₂_le fun b _ => ?_
  have hc : Continuous fun U : GaugeField 1 => U b :=
    (continuous_apply b).comp
      (continuous_subtype_val
        (p := fun U : Link 1 → ComplexMatrix2.specialUnitary => ∀ b, U b.opposite = (U b)⁻¹))
  exact hc.measurable.comap_le
theorem norm_conditionalExpectation_le (W : LinkWindow 1) (β : ℝ) {F : GaugeField 1 → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ U, ‖F U‖ ≤ C) (U : GaugeField 1) :
    ‖W.conditionalExpectation zero_lt_one β F U‖ ≤ C := by
  have hpos : ∀ V, 0 < W.localWeight β (W.glue zero_lt_one V U) := fun V => Real.exp_pos _
  rw [LinkWindow.conditionalExpectation]
  by_cases hD : ∫ V, W.localWeight β (W.glue zero_lt_one V U) ∂W.haarProd = 0
  · rw [hD]
    simpa using hC
  have hint : Integrable (fun V => W.localWeight β (W.glue zero_lt_one V U)) W.haarProd := by
    by_contra h
    exact hD (integral_undef h)
  have hDpos : 0 < ∫ V, W.localWeight β (W.glue zero_lt_one V U) ∂W.haarProd :=
    lt_of_le_of_ne (integral_nonneg fun V => (hpos V).le) (Ne.symm hD)
  have hN : ‖∫ V, F (W.glue zero_lt_one V U) *
        (W.localWeight β (W.glue zero_lt_one V U) : ℂ) ∂W.haarProd‖ ≤
      ∫ V, C * W.localWeight β (W.glue zero_lt_one V U) ∂W.haarProd :=
    norm_integral_le_of_norm_le (hint.const_mul C) (ae_of_all _ fun V => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hpos V).le]
      exact mul_le_mul_of_nonneg_right (hF _) (hpos V).le)
  rw [integral_const_mul] at hN
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hDpos.le, div_le_iff₀ hDpos]
  exact hN
theorem blockConditionalLawStatement_holds (h₁ : InfiniteLattice.GibbsClassStructure)
    (h₂ : GibbsHaarKernels.Statement)
    (h₃ : TemporalGauge.MainStatement)
    (h₄ : KernelSymmetryAndGaugeInvariance.Statement) :
    BlockConditionalLawStatement := by
  intro μ β hβ S j hj B
  have hE : TemporalGauge.FaceEnergiesInTransported μ β S :=
    (h₃ μ S).2.1 β hβ
  have : Nonempty (B.sliceWindow j).links := by
    obtain ⟨b, hb⟩ := B.links_nonempty
    exact ⟨⟨(spatialLink μ j b).1, (spatialLink_mem_sliceWindow_iff B).2 ⟨rfl, hb⟩⟩⟩
  have hH : GibbsHaarKernels.HaarPiInvariance (B.sliceWindow j).links := h₂.2.1 _
  refine ⟨fun U v => ⟨fun j' _ y => parallelTransport_withTransported S B U j j' v y,
      fun b => transportedLinkVariable_withTransported_self S B U j v b,
      fun j' _ b' h => transportedLinkVariable_withTransported_of_not S B U j j' v h⟩, ?_, ?_, ?_⟩
  · intro F hF
    have hfun : S.blockAverage B β j F =
        (B.sliceWindow j).conditionalExpectation zero_lt_one β F :=
      funext fun U => blockAverage_eq_conditionalExpectation S B hE hH hj F U
    obtain ⟨hmeas, hν⟩ := (h₁ 1 zero_lt_one β hβ).1 (B.sliceWindow j) F hF
    have hobs : IsBoundedObservable
        ((B.sliceWindow j).conditionalExpectation zero_lt_one β F) := by
      obtain ⟨-, C, hC⟩ := hF
      refine ⟨hmeas.mono (exteriorSigma_le _) le_rfl, max C 0, fun U => ?_⟩
      exact norm_conditionalExpectation_le _ β (le_max_right _ _)
        (fun U => (hC U).trans (le_max_left _ _)) U
    rw [hfun]
    refine ⟨fun U => rfl, hmeas, fun ν hνm => ?_⟩
    obtain ⟨hH', hae, hint⟩ := hν ν hνm
    refine ⟨hae.symm, ⟨hobs, hmeas, fun H hHo hHm => ?_⟩, hint⟩
    simpa only [mul_comm] using hH' H hHm hHo.2
  · intro U U' hη hw' hw
    funext v
    simp only [Stack.densityAt, hη, hw', hw]
  · intro η w' w v
    have : Nonempty B.links := B.links_nonempty.to_subtype
    have hs := fun u u' : B.links → ComplexMatrix2.specialUnitary =>
      ((h₄ β hβ).1 B.links).1 u u' |>.1
    rw [Block.sliceDensity, Block.sliceDensity, hs w' v, hs v w]
    ring
end TransferOperators.BlockConditionalLaw
end YangMills.Construction
end
