import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASideProof
import YangMills.Construction.Towers.DilationCarriesValuesAtAStepOfTheWholeSpaceProof
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import YangMills.Construction.Towers.WhatTheDilationKeeps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
open QuotientLattices
theorem transportTotal_comp {X Y V : Type*} (e : X ≃ Y) (f : X → V) :
    transportTotal e f ∘ e = f := by
  funext σ
  exact transportTotal_apply e f σ
namespace ScalingInvariance
variable {L n k j i : ℕ}
theorem scaleEdge_opposite (hL : 0 < L) (hj : j ≤ k) (b : Edge L n k i) :
    scaleEdge hL hj i b.opposite = (scaleEdge hL hj i b).opposite :=
  PeriodicLattice.Bond.ext rfl rfl
theorem scaleEdge_forwardFrom (hL : 0 < L) (hj : j ≤ k) (x : Vertex L n k i) (μ : Fin 4) :
    scaleEdge hL hj i (PeriodicLattice.Bond.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (scaleVertex hL hj i x) μ := by apply _root_.YangMills.Construction.Tower.ScalingPreservesStepsAtSide.scaleEdge_forwardFrom <;> assumption
theorem boundaryBonds_scaleFace (hL : 0 < L) (hj : j ≤ k) (p : Face L n k i) :
    (scaleFace hL hj i p).boundaryBonds = scalePath hL hj i p.boundaryBonds := by
  have hb : (scaleFace hL hj i p).origin = scaleVertex hL hj i p.origin := rfl
  have h₁ : (scaleFace hL hj i p).firstAxis = p.firstAxis := rfl
  have h₂ : (scaleFace hL hj i p).secondAxis = p.secondAxis := rfl
  simp only [PeriodicLattice.Plaquette.boundaryBonds, scalePath, transportList, List.map_cons,
    List.map_nil, scaleEdge_opposite, scaleEdge_forwardFrom, map_add, scaleVertex_unitStep,
    hb, h₁, h₂]
theorem isGaugeField_iff (hL : 0 < L) (hj : j ≤ k) (G : Set Matrices.ComplexMatrix2)
    (S : Set (Edge L n k i)) (V : Edge L n k i → Matrices.ComplexMatrix2) :
    PeriodicLattice.IsGaugeField G S V ↔
      PeriodicLattice.IsGaugeField G (scaleEdge hL hj i '' S)
        (transportTotal (scaleEdge hL hj i) V) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [transportTotal_apply]
      exact h₁ b hb
    · rintro _ ⟨b, hb, rfl⟩
      rw [← scaleEdge_opposite, transportTotal_apply, transportTotal_apply]
      exact h₂ b hb
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have h := h₁ _ (mem_image_of_mem _ hb)
      rwa [transportTotal_apply] at h
    · have h := h₂ _ (mem_image_of_mem _ hb)
      rwa [← scaleEdge_opposite, transportTotal_apply, transportTotal_apply] at h
theorem pathHolonomy_image (hL : 0 < L) (hj : j ≤ k) (V : Edge L n k i → Matrices.ComplexMatrix2)
    (γ : List (Edge L n k i)) :
    PeriodicLattice.pathHolonomy (transportTotal (scaleEdge hL hj i) V)
      (scalePath hL hj i γ) = PeriodicLattice.pathHolonomy V γ := by apply _root_.YangMills.Construction.Tower.ScalingPreservesStepsAtSide.pathHolonomy_transportTotal <;> assumption
theorem bondFormSumAlong_image (hL : 0 < L) (hj : j ≤ k)
    (B : Edge L n k i → Matrices.ComplexMatrix2) (γ : List (Edge L n k i)) :
    PeriodicLattice.bondFormSumAlong (transportTotal (scaleEdge hL hj i) B)
      (scalePath hL hj i γ) = PeriodicLattice.bondFormSumAlong B γ := by apply _root_.YangMills.Construction.Tower.ScalingPreservesStepsAtSide.bondFormSumAlong_transportTotal <;> assumption
theorem scalingPreservesOnEdges (hL : 0 < L) (hj : j ≤ k) (S : Set (Edge L n k i))
    (hS : PeriodicLattice.IsReversalClosed S) : ScalingPreservesOnEdges hL hj i S where
  reversal_closed := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.opposite, hS b hb, scaleEdge_opposite hL hj b⟩
  compactField_iff V := isGaugeField_iff hL hj _ S V
  complexField_iff V := isGaugeField_iff hL hj _ S V
  holonomy_eq V _ γ _ _ := pathHolonomy_image hL hj V γ
  plaquetteHolonomy_eq V _ p _ := by
    simp only [PeriodicLattice.plaquetteHolonomy, boundaryBonds_scaleFace, pathHolonomy_image]
  antisymm_iff B := by
    constructor
    · rintro h _ ⟨b, hb, rfl⟩
      rw [← scaleEdge_opposite, transportTotal_apply, transportTotal_apply]
      exact h b hb
    · intro h b hb
      have h' := h _ (mem_image_of_mem _ hb)
      rwa [← scaleEdge_opposite, transportTotal_apply, transportTotal_apply] at h'
  sumAlong_eq B γ _ _ := bondFormSumAlong_image hL hj B γ
theorem scalingPreservesGaugeAct (hL : 0 < L) (hj : j ≤ k) :
    ScalingPreservesGaugeAct (L := L) hL hj n i := by
  intro V u _ _
  funext b'
  obtain ⟨b, rfl⟩ := (scaleEdge hL hj i).surjective b'
  rw [transportTotal_apply]
  have h₁ : transportTotal (scaleVertex hL hj i).toEquiv u (scaleVertex hL hj i b.source) =
      u b.source := transportTotal_apply _ u b.source
  have h₂ : transportTotal (scaleVertex hL hj i).toEquiv u (scaleVertex hL hj i b.target) =
      u b.target := transportTotal_apply _ u b.target
  change u b.source * V b * (u b.target)⁻¹ =
    transportTotal (scaleVertex hL hj i).toEquiv u (scaleVertex hL hj i b.source) *
      transportTotal (scaleEdge hL hj i) V (scaleEdge hL hj i b) *
      (transportTotal (scaleVertex hL hj i).toEquiv u (scaleVertex hL hj i b.target))⁻¹
  rw [h₁, h₂, transportTotal_apply]
theorem areNeighbours_of_bond (b : Edge L n k i) :
    AreNeighbours (torusAxisSteps L n k i) (b.source : PeriodicLattice.FourTorus L n)
      (b.target : PeriodicLattice.FourTorus L n) := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · refine ⟨1, μ, ?_⟩
    have h' := congrArg Subtype.val h
    simpa [IsSignedAxisStep, torusAxisSteps] using h'
  · refine ⟨-1, μ, ?_⟩
    have h' := congrArg Subtype.val h
    simpa [IsSignedAxisStep, torusAxisSteps] using h'
theorem exists_bond_of_areNeighbours (x x' : Vertex L n k i)
    (h : AreNeighbours (torusAxisSteps L n k i) (x : PeriodicLattice.FourTorus L n)
      (x' : PeriodicLattice.FourTorus L n)) :
    ∃ b : Edge L n k i, b.source = x ∧ b.target = x' := by
  obtain ⟨ε, μ, h⟩ := h
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨⟨x, x', μ, Or.inl (Subtype.ext ?_)⟩, rfl, rfl⟩
    simpa [IsSignedAxisStep, torusAxisSteps] using h
  · refine ⟨⟨x, x', μ, Or.inr (Subtype.ext ?_)⟩, rfl, rfl⟩
    simpa [IsSignedAxisStep, torusAxisSteps] using h
section Symmetry
variable {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
theorem vertexImage_coe (hM : MapsSublatticeOnto k i f) (x : Vertex L n k i) :
    ((vertexImage f x : Vertex L n k i) : PeriodicLattice.FourTorus L n) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_torus_vertexImage <;> assumption
theorem vertexPreimage_spec (hM : MapsSublatticeOnto k i f) (x : Vertex L n k i) :
    f (vertexPreimage f x : Vertex L n k i) = x := by
  obtain ⟨y, hy, e⟩ := (Set.Subset.antisymm_iff.mp hM).2 (SetLike.mem_coe.mpr x.2)
  exact Classical.epsilon_spec (p := fun x' : Vertex L n k i => f x' = x) ⟨⟨y, hy⟩, e⟩
theorem edgeImage_spec (hf : IsDistancePreserving f) (hM : MapsSublatticeOnto k i f)
    (hN : NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k i))
      (PeriodicLattice.meshSize L (refinementIndex k i)) (torusAxisSteps L n k i))
    (b : Edge L n k i) :
    (edgeImage f b).source = vertexImage f b.source ∧
      (edgeImage f b).target = vertexImage f b.target := by
  have hn := (hN.2 f hf hM).2.1 b.source b.source.2 b.target b.target.2 (areNeighbours_of_bond b)
  obtain ⟨w, hw⟩ := exists_bond_of_areNeighbours (vertexImage f b.source) (vertexImage f b.target)
    (by rw [vertexImage_coe hM, vertexImage_coe hM]; exact hn)
  exact Classical.epsilon_spec (p := fun b' : Edge L n k i =>
    b'.source = vertexImage f b.source ∧ b'.target = vertexImage f b.target) ⟨w, hw⟩
theorem edgePreimage_spec (hf : IsDistancePreserving f) (hM : MapsSublatticeOnto k i f)
    (hN : NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k i))
      (PeriodicLattice.meshSize L (refinementIndex k i)) (torusAxisSteps L n k i))
    (b : Edge L n k i) :
    (edgePreimage f b).source = vertexPreimage f b.source ∧
      (edgePreimage f b).target = vertexPreimage f b.target := by
  have hP := hN.2 f hf hM
  have hinv : ∀ y : Vertex L n k i,
      ((vertexPreimage f y : Vertex L n k i) : PeriodicLattice.FourTorus L n) =
      Function.invFunOn f (PeriodicLattice.sublattice L n (refinementIndex k i) :
        Set (PeriodicLattice.FourTorus L n)) y := fun y => by
    have hy : ∃ c ∈ (PeriodicLattice.sublattice L n (refinementIndex k i) :
        Set (PeriodicLattice.FourTorus L n)), f c = y :=
      ⟨_, SetLike.mem_coe.mpr (vertexPreimage f y : Vertex L n k i).2, vertexPreimage_spec hM y⟩
    exact hP.1 (SetLike.mem_coe.mpr (vertexPreimage f y : Vertex L n k i).2)
      (Function.invFunOn_mem hy)
      ((vertexPreimage_spec hM y).trans (Function.invFunOn_eq hy).symm)
  have hn := hP.2.2 b.source b.source.2 b.target b.target.2 (areNeighbours_of_bond b)
  obtain ⟨w, hw⟩ := exists_bond_of_areNeighbours (vertexPreimage f b.source)
    (vertexPreimage f b.target) (by rw [hinv, hinv]; exact hn)
  exact Classical.epsilon_spec (p := fun b' : Edge L n k i =>
    b'.source = vertexPreimage f b.source ∧ b'.target = vertexPreimage f b.target) ⟨w, hw⟩
theorem conjMap_scaling (hL : 0 < L) (x : PeriodicLattice.FourTorus L n) :
    conjMap (scaling hL n k j).toEquiv f (scaling hL n k j x) = scaling hL n k j (f x) := by
  simp [conjMap]
theorem scaleVertex_vertexImage (hL : 0 < L) (hj : j ≤ k) (hM : MapsSublatticeOnto k i f)
    (hM' : MapsSublatticeOnto j i (conjMap (scaling hL n k j).toEquiv f)) (x : Vertex L n k i) :
    scaleVertex hL hj i (vertexImage f x) =
      vertexImage (conjMap (scaling hL n k j).toEquiv f) (scaleVertex hL hj i x) := by
  apply Subtype.ext
  rw [vertexImage_coe hM', coe_scaleVertex, coe_scaleVertex, vertexImage_coe hM, conjMap_scaling]
theorem scaleEdge_edgeImage (hL : 0 < L) (hj : j ≤ k) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto k i f)
    (hM' : MapsSublatticeOnto j i (conjMap (scaling hL n k j).toEquiv f))
    (hN : NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k i))
      (PeriodicLattice.meshSize L (refinementIndex k i)) (torusAxisSteps L n k i))
    (b : Edge L n k i) :
    scaleEdge hL hj i (edgeImage f b) =
      edgeImage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b) := by
  have hb := edgeImage_spec hf hM hN b
  have ht : (scaleEdge hL hj i (edgeImage f b)).source =
      vertexImage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b).source := by
    change scaleVertex hL hj i (edgeImage f b).source =
      vertexImage (conjMap (scaling hL n k j).toEquiv f) (scaleVertex hL hj i b.source)
    rw [hb.1, scaleVertex_vertexImage hL hj hM hM']
  have hh : (scaleEdge hL hj i (edgeImage f b)).target =
      vertexImage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b).target := by
    change scaleVertex hL hj i (edgeImage f b).target =
      vertexImage (conjMap (scaling hL n k j).toEquiv f) (scaleVertex hL hj i b.target)
    rw [hb.2, scaleVertex_vertexImage hL hj hM hM']
  have hw := Classical.epsilon_spec (p := fun b' : Edge L (scaledExponent n k j) j i =>
    b'.source = vertexImage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b).source ∧
    b'.target = vertexImage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b).target)
    ⟨_, ht, hh⟩
  exact PeriodicLattice.Bond.ext (ht.trans hw.1.symm) (hh.trans hw.2.symm)
theorem vertexPreimage_scaleVertex (hL : 0 < L) (hj : j ≤ k)
    (hinj : InjOn f (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
      Set (PeriodicLattice.FourTorus L n)))
    (hM : MapsSublatticeOnto k i f)
    (hM' : MapsSublatticeOnto j i (conjMap (scaling hL n k j).toEquiv f)) (x : Vertex L n k i) :
    vertexPreimage (conjMap (scaling hL n k j).toEquiv f) (scaleVertex hL hj i x) =
      scaleVertex hL hj i (vertexPreimage f x) := by
  obtain ⟨y, hy⟩ := (scaleVertex hL hj i (n := n)).surjective
    (vertexPreimage (conjMap (scaling hL n k j).toEquiv f) (scaleVertex hL hj i x))
  have h := vertexPreimage_spec hM' (scaleVertex hL hj i x)
  rw [← hy, coe_scaleVertex, coe_scaleVertex, conjMap_scaling] at h
  have hfy : f y = x := (scaling hL n k j).injective h
  have hyx : y = vertexPreimage f x := Subtype.ext (hinj (SetLike.mem_coe.mpr y.2)
    (SetLike.mem_coe.mpr (vertexPreimage f x : Vertex L n k i).2)
    (hfy.trans (vertexPreimage_spec hM x).symm))
  rw [← hy, hyx]
theorem edgePreimage_scaleEdge (hL : 0 < L) (hj : j ≤ k) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto k i f)
    (hM' : MapsSublatticeOnto j i (conjMap (scaling hL n k j).toEquiv f))
    (hN : NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k i))
      (PeriodicLattice.meshSize L (refinementIndex k i)) (torusAxisSteps L n k i))
    (b : Edge L n k i) :
    edgePreimage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b) =
      scaleEdge hL hj i (edgePreimage f b) := by
  have hinj := (hN.2 f hf hM).1
  have hb := edgePreimage_spec hf hM hN b
  have ht : (scaleEdge hL hj i (edgePreimage f b)).source =
      vertexPreimage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b).source := by
    change scaleVertex hL hj i (edgePreimage f b).source =
      vertexPreimage (conjMap (scaling hL n k j).toEquiv f) (scaleVertex hL hj i b.source)
    rw [hb.1, vertexPreimage_scaleVertex hL hj hinj hM hM']
  have hh : (scaleEdge hL hj i (edgePreimage f b)).target =
      vertexPreimage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b).target := by
    change scaleVertex hL hj i (edgePreimage f b).target =
      vertexPreimage (conjMap (scaling hL n k j).toEquiv f) (scaleVertex hL hj i b.target)
    rw [hb.2, vertexPreimage_scaleVertex hL hj hinj hM hM']
  have hw := Classical.epsilon_spec (p := fun b' : Edge L (scaledExponent n k j) j i =>
    b'.source = vertexPreimage (conjMap (scaling hL n k j).toEquiv f)
      (scaleEdge hL hj i b).source ∧
    b'.target = vertexPreimage (conjMap (scaling hL n k j).toEquiv f)
      (scaleEdge hL hj i b).target) ⟨_, ht, hh⟩
  exact PeriodicLattice.Bond.ext (hw.1.trans ht.symm) (hw.2.trans hh.symm)
theorem scalingPreservesSymmetry (hL : 0 < L) (hj : j ≤ k) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto k i f)
    (hI : IsDistancePreserving (conjMap (scaling hL n k j).toEquiv f))
    (hM' : MapsSublatticeOnto j i (conjMap (scaling hL n k j).toEquiv f))
    (hN : NeighboursAtSpacing (torusDist L n) (PeriodicLattice.sublattice L n (refinementIndex k i))
      (PeriodicLattice.meshSize L (refinementIndex k i)) (torusAxisSteps L n k i)) :
    ScalingPreservesSymmetry hL hj i f where
  distancePreserving := hI
  mapsSublattice := hM'
  edge_comm b := scaleEdge_edgeImage hL hj hf hM hM' hN b
  field_comm V _ := by
    funext b'
    obtain ⟨b, rfl⟩ := (scaleEdge hL hj i).surjective b'
    rw [transportTotal_apply]
    simp only [pushField]
    rw [edgePreimage_scaleEdge hL hj hf hM hM' hN, transportTotal_apply]
  siteFunction_comm l := by
    funext y
    obtain ⟨x, rfl⟩ := (scaleVertex hL hj i).toEquiv.surjective y
    rw [transportTotal_apply]
    simp only [pushSiteFunction]
    change l (vertexPreimage f x) = transportTotal (scaleVertex hL hj i).toEquiv l
      (vertexPreimage (conjMap (scaling hL n k j).toEquiv f) (scaleVertex hL hj i x))
    rw [vertexPreimage_scaleVertex hL hj (hN.2 f hf hM).1 hM hM']
    exact (transportTotal_apply (scaleVertex hL hj i).toEquiv l _).symm
end Symmetry
end ScalingInvariance
namespace FullSpace.ScalingInvariance
open InfiniteLattice (AmbientSpace)
variable {L k j i : ℕ}
theorem scaleEdge_opposite (hL : 0 < L) (hj : j ≤ k) (b : Edge L k i) :
    scaleEdge hL hj i b.opposite = (scaleEdge hL hj i b).opposite :=
  InfiniteLattice.Link.ext rfl rfl
theorem scaleEdge_forwardFrom (hL : 0 < L) (hj : j ≤ k) (x : Vertex L k i) (μ : Fin 4) :
    scaleEdge hL hj i (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (scaleVertex hL hj i x) μ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfValues.scaleEdge_forwardFrom <;> assumption
theorem faceBoundary_scaleFace (hL : 0 < L) (hj : j ≤ k) (p : Face L k i) :
    faceBoundary (scaleFace hL hj i p) = scalePath hL hj i (faceBoundary p) := by
  have hb : (scaleFace hL hj i p).corner = scaleVertex hL hj i p.corner := rfl
  have h₁ : (scaleFace hL hj i p).lowAxis = p.lowAxis := rfl
  have h₂ : (scaleFace hL hj i p).highAxis = p.highAxis := rfl
  simp only [faceBoundary, scalePath, transportList, List.map_cons,
    List.map_nil, scaleEdge_opposite, scaleEdge_forwardFrom, map_add, scaleVertex_axisStep,
    hb, h₁, h₂]
theorem isFieldOn_iff (hL : 0 < L) (hj : j ≤ k) (G : Set Matrices.ComplexMatrix2)
    (S : Set (Edge L k i)) (V : Edge L k i → Matrices.ComplexMatrix2) :
    IsFieldOn G S V ↔
      IsFieldOn G (scaleEdge hL hj i '' S) (transportTotal (scaleEdge hL hj i) V) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [transportTotal_apply]
      exact h₁ b hb
    · rintro _ ⟨b, hb, rfl⟩
      rw [← scaleEdge_opposite, transportTotal_apply, transportTotal_apply]
      exact h₂ b hb
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have h := h₁ _ (mem_image_of_mem _ hb)
      rwa [transportTotal_apply] at h
    · have h := h₂ _ (mem_image_of_mem _ hb)
      rwa [← scaleEdge_opposite, transportTotal_apply, transportTotal_apply] at h
theorem linkHolonomy_image (hL : 0 < L) (hj : j ≤ k) (V : Edge L k i → Matrices.ComplexMatrix2)
    (γ : List (Edge L k i)) :
    FullSpace.linkHolonomy (transportTotal (scaleEdge hL hj i) V)
      (scalePath hL hj i γ) = FullSpace.linkHolonomy V γ := by
  simp only [FullSpace.linkHolonomy, scalePath, transportList, List.map_map, transportTotal_comp]
theorem sumAlong_image (hL : 0 < L) (hj : j ≤ k) (B : Edge L k i → Matrices.ComplexMatrix2)
    (γ : List (Edge L k i)) :
    sumAlong (transportTotal (scaleEdge hL hj i) B)
      (scalePath hL hj i γ) = sumAlong B γ := by
  simp only [sumAlong, scalePath, transportList, List.map_map, transportTotal_comp]
theorem scalingPreservesOnEdges (hL : 0 < L) (hj : j ≤ k) (S : Set (Edge L k i))
    (hS : ∀ b ∈ S, b.opposite ∈ S) : ScalingPreservesOnEdges hL hj i S where
  reversal_closed := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.opposite, hS b hb, scaleEdge_opposite hL hj b⟩
  compactField_iff V := isFieldOn_iff hL hj _ S V
  complexField_iff V := isFieldOn_iff hL hj _ S V
  holonomy_eq V _ γ _ _ := linkHolonomy_image hL hj V γ
  faceVariable_eq V _ p _ := by
    simp only [FullSpace.faceVariable, faceBoundary_scaleFace, linkHolonomy_image]
  antisymm_iff B := by
    constructor
    · rintro h _ ⟨b, hb, rfl⟩
      rw [← scaleEdge_opposite, transportTotal_apply, transportTotal_apply]
      exact h b hb
    · intro h b hb
      have h' := h _ (mem_image_of_mem _ hb)
      rwa [← scaleEdge_opposite, transportTotal_apply, transportTotal_apply] at h'
  sumAlong_eq B γ _ _ := sumAlong_image hL hj B γ
theorem scalingPreservesGaugeAct (hL : 0 < L) (hj : j ≤ k) :
    ScalingPreservesGaugeAct (L := L) hL hj i := by
  intro V u _ _
  funext b'
  obtain ⟨b, rfl⟩ := (scaleEdge hL hj i).surjective b'
  rw [transportTotal_apply]
  have h₁ : transportTotal (scaleVertex hL hj i).toEquiv u (scaleVertex hL hj i b.initial) =
      u b.initial := transportTotal_apply _ u b.initial
  have h₂ : transportTotal (scaleVertex hL hj i).toEquiv u (scaleVertex hL hj i b.terminal) =
      u b.terminal := transportTotal_apply _ u b.terminal
  change u b.initial * V b * (u b.terminal)⁻¹ =
    transportTotal (scaleVertex hL hj i).toEquiv u (scaleVertex hL hj i b.initial) *
      transportTotal (scaleEdge hL hj i) V (scaleEdge hL hj i b) *
      (transportTotal (scaleVertex hL hj i).toEquiv u (scaleVertex hL hj i b.terminal))⁻¹
  rw [h₁, h₂, transportTotal_apply]
section SingleLattice
variable {a : ℝ}
theorem areNeighbours_of_link (b : InfiniteLattice.Link a) :
    AreNeighbours (spaceAxisSteps a) (b.initial : AmbientSpace) (b.terminal : AmbientSpace) := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · refine ⟨1, μ, ?_⟩
    have h' := congrArg Subtype.val h
    simpa [IsSignedAxisStep, spaceAxisSteps] using h'
  · refine ⟨-1, μ, ?_⟩
    have h' := congrArg Subtype.val h
    simpa [IsSignedAxisStep, spaceAxisSteps] using h'
theorem exists_link_of_areNeighbours (x x' : InfiniteLattice.LatticePoint a)
    (h : AreNeighbours (spaceAxisSteps a) (x : AmbientSpace) (x' : AmbientSpace)) :
    ∃ b : InfiniteLattice.Link a, b.initial = x ∧ b.terminal = x' := by
  obtain ⟨ε, μ, h⟩ := h
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨⟨x, x', μ, Or.inl (Subtype.ext ?_)⟩, rfl, rfl⟩
    simpa [IsSignedAxisStep, spaceAxisSteps] using h
  · refine ⟨⟨x, x', μ, Or.inr (Subtype.ext ?_)⟩, rfl, rfl⟩
    simpa [IsSignedAxisStep, spaceAxisSteps] using h
variable {f : AmbientSpace → AmbientSpace}
theorem vertexImage_coe (hM : MapsSublatticeOnto a f) (x : InfiniteLattice.LatticePoint a) :
    ((vertexImage f x : InfiniteLattice.LatticePoint a) : AmbientSpace) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_space_vertexImage <;> assumption
theorem vertexPreimage_spec (hM : MapsSublatticeOnto a f) (x : InfiniteLattice.LatticePoint a) :
    f (vertexPreimage f x : InfiniteLattice.LatticePoint a) = x := by
  obtain ⟨y, hy, e⟩ := (Set.Subset.antisymm_iff.mp hM).2 (SetLike.mem_coe.mpr x.2)
  exact Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a => f x' = x) ⟨⟨y, hy⟩, e⟩
theorem edgeImage_spec (hf : IsDistancePreserving f) (hM : MapsSublatticeOnto a f)
    (hN : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup a) a (spaceAxisSteps a))
    (b : InfiniteLattice.Link a) :
    (edgeImage f b).initial = vertexImage f b.initial ∧
      (edgeImage f b).terminal = vertexImage f b.terminal := by
  have hn := (hN.2 f hf hM).2.1 b.initial b.initial.2 b.terminal b.terminal.2
    (areNeighbours_of_link b)
  obtain ⟨w, hw⟩ := exists_link_of_areNeighbours (vertexImage f b.initial)
    (vertexImage f b.terminal) (by rw [vertexImage_coe hM, vertexImage_coe hM]; exact hn)
  exact Classical.epsilon_spec (p := fun b' : InfiniteLattice.Link a =>
    b'.initial = vertexImage f b.initial ∧ b'.terminal = vertexImage f b.terminal) ⟨w, hw⟩
theorem edgePreimage_spec (hf : IsDistancePreserving f) (hM : MapsSublatticeOnto a f)
    (hN : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup a) a (spaceAxisSteps a))
    (b : InfiniteLattice.Link a) :
    (edgePreimage f b).initial = vertexPreimage f b.initial ∧
      (edgePreimage f b).terminal = vertexPreimage f b.terminal := by
  have hP := hN.2 f hf hM
  have hinv : ∀ y : InfiniteLattice.LatticePoint a,
      ((vertexPreimage f y : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      Function.invFunOn f (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) y := fun y => by
    have hy : ∃ c ∈ (InfiniteLattice.latticeSubgroup a : Set AmbientSpace), f c = y :=
      ⟨_, SetLike.mem_coe.mpr (vertexPreimage f y : InfiniteLattice.LatticePoint a).2,
        vertexPreimage_spec hM y⟩
    exact hP.1 (SetLike.mem_coe.mpr (vertexPreimage f y : InfiniteLattice.LatticePoint a).2)
      (Function.invFunOn_mem hy)
      ((vertexPreimage_spec hM y).trans (Function.invFunOn_eq hy).symm)
  have hn := hP.2.2 b.initial b.initial.2 b.terminal b.terminal.2 (areNeighbours_of_link b)
  obtain ⟨w, hw⟩ := exists_link_of_areNeighbours (vertexPreimage f b.initial)
    (vertexPreimage f b.terminal) (by rw [hinv, hinv]; exact hn)
  exact Classical.epsilon_spec (p := fun b' : InfiniteLattice.Link a =>
    b'.initial = vertexPreimage f b.initial ∧ b'.terminal = vertexPreimage f b.terminal) ⟨w, hw⟩
end SingleLattice
section Symmetry
variable {f : AmbientSpace → AmbientSpace}
theorem conjMap_scaling (hL : 0 < L) (x : AmbientSpace) :
    conjMap (scaling hL k j).toEquiv f (scaling hL k j x) = scaling hL k j (f x) := by
  simp [conjMap]
theorem scaleVertex_vertexImage (hL : 0 < L) (hj : j ≤ k)
    (hM : MapsSublatticeOnto (meshAt L k i) f)
    (hM' : MapsSublatticeOnto (meshAt L j i) (conjMap (scaling hL k j).toEquiv f))
    (x : Vertex L k i) :
    scaleVertex hL hj i (vertexImage f x) =
      vertexImage (conjMap (scaling hL k j).toEquiv f) (scaleVertex hL hj i x) := by
  apply Subtype.ext
  rw [vertexImage_coe hM', coe_scaleVertex, coe_scaleVertex, vertexImage_coe hM, conjMap_scaling]
theorem scaleEdge_edgeImage (hL : 0 < L) (hj : j ≤ k) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto (meshAt L k i) f)
    (hM' : MapsSublatticeOnto (meshAt L j i) (conjMap (scaling hL k j).toEquiv f))
    (hN : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup (meshAt L k i))
      (meshAt L k i) (spaceAxisSteps (meshAt L k i))) (b : Edge L k i) :
    scaleEdge hL hj i (edgeImage f b) =
      edgeImage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b) := by
  have hb := edgeImage_spec hf hM hN b
  have ht : (scaleEdge hL hj i (edgeImage f b)).initial =
      vertexImage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b).initial := by
    change scaleVertex hL hj i (edgeImage f b).initial =
      vertexImage (conjMap (scaling hL k j).toEquiv f) (scaleVertex hL hj i b.initial)
    rw [hb.1, scaleVertex_vertexImage hL hj hM hM']
  have hh : (scaleEdge hL hj i (edgeImage f b)).terminal =
      vertexImage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b).terminal := by
    change scaleVertex hL hj i (edgeImage f b).terminal =
      vertexImage (conjMap (scaling hL k j).toEquiv f) (scaleVertex hL hj i b.terminal)
    rw [hb.2, scaleVertex_vertexImage hL hj hM hM']
  have hw := Classical.epsilon_spec (p := fun b' : Edge L j i =>
    b'.initial = vertexImage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b).initial ∧
    b'.terminal = vertexImage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b).terminal)
    ⟨_, ht, hh⟩
  exact InfiniteLattice.Link.ext (ht.trans hw.1.symm) (hh.trans hw.2.symm)
theorem vertexPreimage_scaleVertex (hL : 0 < L) (hj : j ≤ k)
    (hinj : InjOn f (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace))
    (hM : MapsSublatticeOnto (meshAt L k i) f)
    (hM' : MapsSublatticeOnto (meshAt L j i) (conjMap (scaling hL k j).toEquiv f))
    (x : Vertex L k i) :
    vertexPreimage (conjMap (scaling hL k j).toEquiv f) (scaleVertex hL hj i x) =
      scaleVertex hL hj i (vertexPreimage f x) := by
  obtain ⟨y, hy⟩ := (scaleVertex hL hj i).surjective
    (vertexPreimage (conjMap (scaling hL k j).toEquiv f) (scaleVertex hL hj i x))
  have h := vertexPreimage_spec hM' (scaleVertex hL hj i x)
  rw [← hy, coe_scaleVertex, coe_scaleVertex, conjMap_scaling] at h
  have hfy : f y = x := (scaling hL k j).injective h
  have hyx : y = vertexPreimage f x := Subtype.ext (hinj (SetLike.mem_coe.mpr y.2)
    (SetLike.mem_coe.mpr (vertexPreimage f x : Vertex L k i).2)
    (hfy.trans (vertexPreimage_spec hM x).symm))
  rw [← hy, hyx]
theorem edgePreimage_scaleEdge (hL : 0 < L) (hj : j ≤ k) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto (meshAt L k i) f)
    (hM' : MapsSublatticeOnto (meshAt L j i) (conjMap (scaling hL k j).toEquiv f))
    (hN : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup (meshAt L k i))
      (meshAt L k i) (spaceAxisSteps (meshAt L k i))) (b : Edge L k i) :
    edgePreimage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b) =
      scaleEdge hL hj i (edgePreimage f b) := by
  have hinj := (hN.2 f hf hM).1
  have hb := edgePreimage_spec hf hM hN b
  have ht : (scaleEdge hL hj i (edgePreimage f b)).initial =
      vertexPreimage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b).initial := by
    change scaleVertex hL hj i (edgePreimage f b).initial =
      vertexPreimage (conjMap (scaling hL k j).toEquiv f) (scaleVertex hL hj i b.initial)
    rw [hb.1, vertexPreimage_scaleVertex hL hj hinj hM hM']
  have hh : (scaleEdge hL hj i (edgePreimage f b)).terminal =
      vertexPreimage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b).terminal := by
    change scaleVertex hL hj i (edgePreimage f b).terminal =
      vertexPreimage (conjMap (scaling hL k j).toEquiv f) (scaleVertex hL hj i b.terminal)
    rw [hb.2, vertexPreimage_scaleVertex hL hj hinj hM hM']
  have hw := Classical.epsilon_spec (p := fun b' : Edge L j i =>
    b'.initial = vertexPreimage (conjMap (scaling hL k j).toEquiv f)
      (scaleEdge hL hj i b).initial ∧
    b'.terminal = vertexPreimage (conjMap (scaling hL k j).toEquiv f)
      (scaleEdge hL hj i b).terminal) ⟨_, ht, hh⟩
  exact InfiniteLattice.Link.ext (hw.1.trans ht.symm) (hw.2.trans hh.symm)
theorem scalingPreservesSymmetry (hL : 0 < L) (hj : j ≤ k) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto (meshAt L k i) f)
    (hI : IsDistancePreserving (conjMap (scaling hL k j).toEquiv f))
    (hM' : MapsSublatticeOnto (meshAt L j i) (conjMap (scaling hL k j).toEquiv f))
    (hN : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup (meshAt L k i))
      (meshAt L k i) (spaceAxisSteps (meshAt L k i))) :
    ScalingPreservesSymmetry hL hj i f where
  distancePreserving := hI
  mapsSublattice := hM'
  edge_comm b := scaleEdge_edgeImage hL hj hf hM hM' hN b
  field_comm V _ := by
    funext b'
    obtain ⟨b, rfl⟩ := (scaleEdge hL hj i).surjective b'
    rw [transportTotal_apply]
    simp only [pushField]
    rw [edgePreimage_scaleEdge hL hj hf hM hM' hN, transportTotal_apply]
  siteFunction_comm l := by
    funext y
    obtain ⟨x, rfl⟩ := (scaleVertex hL hj i).toEquiv.surjective y
    rw [transportTotal_apply]
    simp only [pushSiteFunction]
    change l (vertexPreimage f x) = transportTotal (scaleVertex hL hj i).toEquiv l
      (vertexPreimage (conjMap (scaling hL k j).toEquiv f) (scaleVertex hL hj i x))
    rw [vertexPreimage_scaleVertex hL hj (hN.2 f hf hM).1 hM hM']
    exact (transportTotal_apply (scaleVertex hL hj i).toEquiv l _).symm
end Symmetry
end FullSpace.ScalingInvariance
end Tower
namespace ScalingCompatibility
theorem proof (h₁ : Tower.ScalingPropertiesStatement)
    (h₂ : QuotientLattices.TorusAndSpaceLatticeProperties) : Statement := by
  intro L hs hL k j i hj hi
  have hik : i ≤ k := hi.trans hj
  obtain ⟨hfin, hwhole⟩ := h₁ L k j hs hj
  refine ⟨fun n hn => ⟨fun S hS => Tower.ScalingInvariance.scalingPreservesOnEdges hL hj S hS,
      Tower.ScalingInvariance.scalingPreservesGaugeAct hL hj, fun f hf hM => ?_⟩,
    fun S hS => Tower.FullSpace.ScalingInvariance.scalingPreservesOnEdges hL hj S hS,
    Tower.FullSpace.ScalingInvariance.scalingPreservesGaugeAct hL hj, fun f hf hM => ?_⟩
  · have hD := hfin n hn
    have hN := (h₂ L hs n i k hn hik).2.2.2.2.2.2.2.1
    exact Tower.ScalingInvariance.scalingPreservesSymmetry hL hj hf hM
      ((hD.distancePreserving_iff f).mpr hf)
      ((hD.mapsSublatticeOnto_iff i hi f).mpr hM) hN
  · have hN := (h₂ L hs 1 i k le_rfl hik).2.2.2.2.2.2.2.2
    have hsp : PeriodicLattice.meshSize L (QuotientLattices.refinementIndex k i) =
        Tower.meshAt L k i := Tower.meshSize_levelDepth L k i
    rw [hsp] at hN
    exact Tower.FullSpace.ScalingInvariance.scalingPreservesSymmetry hL hj hf hM
      ((hwhole.distancePreserving_iff f).mpr hf)
      ((hwhole.mapsSublatticeOnto_iff i hi f).mpr hM) hN
end ScalingCompatibility
end YangMills.Construction
end
