import YangMills.Construction.Lattice.SidesOfAPlaquetteArePositiveAndEndAtCorners
import YangMills.Construction.ReflectionPositivity.BondsAndPlaquettesAreNotDegenerateProof
import YangMills.Construction.ReflectionPositivity.FourSetsOfHeightsAndTheLinkPositionHalfASideOn
import YangMills.Construction.ReflectionPositivity.ReflectionInALinkMirrorProof
import YangMills.Construction.ReflectionPositivity.SitesBondsAndPlaquettesOnTheTwoSides
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.HalfSpaces
variable {D : MirrorData}
private theorem spacing_pos : 0 < D.spacing := by apply _root_.YangMills.Construction.ReflectionPositivity.PlaquetteNondegeneracy.meshSpacing_pos <;> assumption
private theorem centeredRep_eq_of_mem (C : LinkLevel D) {y : D.Torus} {r : ℝ}
    (h : (r : D.CircleCoord) = y D.dir) (hr : r ∈ Ico (C.pos - D.side / 2) (C.pos + D.side / 2)) :
    C.centeredRep y = r :=
  ((C.existsUnique_isCenteredRep y).unique ⟨h, hr⟩ (C.isCenteredRep_centeredRep y)).symm
private theorem coe_centeredRep (C : LinkLevel D) (y : D.Torus) :
    ((C.centeredRep y : ℝ) : D.CircleCoord) = y D.dir :=
  (C.isCenteredRep_centeredRep y).1
private theorem centeredRep_congr (C : LinkLevel D) {y y' : D.Torus} (h : y D.dir = y' D.dir) :
    C.centeredRep y = C.centeredRep y' :=
  centeredRep_eq_of_mem C (by rw [coe_centeredRep, h]) (C.isCenteredRep_centeredRep y').2
private theorem coe_add_side_eq (r : ℝ) :
    ((r + D.side : ℝ) : D.CircleCoord) = (r : D.CircleCoord) := by
  change ((r + PeriodicLattice.torusSide D.L D.m : ℝ) :
    AddCircle (PeriodicLattice.torusSide D.L D.m)) = _
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
private theorem centeredRep_vertex (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    (C : LinkLevel D) (x : D.Vertex) :
    ∃ j : ℤ, -(D.sitesPerSide : ℤ) ≤ j ∧ j ≤ (D.sitesPerSide : ℤ) - 1 ∧
      C.centeredRep (x : D.Torus) = levelAt C j := by
  obtain ⟨n₀, hn₀⟩ := C.isLinkLevel
  obtain ⟨n, hn⟩ := x.2
  have ha := spacing_pos (D := D)
  have hmem := (C.isCenteredRep_centeredRep (x : D.Torus)).2
  have hrep : ((C.centeredRep (x : D.Torus) : ℝ) : D.CircleCoord) =
      (((n D.dir : ℝ) * D.spacing : ℝ) : D.CircleCoord) := by
    rw [coe_centeredRep]
    exact hn D.dir
  have h0 : ((C.centeredRep (x : D.Torus) - (n D.dir : ℝ) * D.spacing : ℝ) : D.CircleCoord) = 0 := by
    rw [AddCircle.coe_sub, hrep, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
  have hside : PeriodicLattice.torusSide D.L D.m = 2 * (D.sitesPerSide : ℝ) * D.spacing := by
    change D.side = _
    linarith
  rw [zsmul_eq_mul] at hk
  have hk' : (k : ℝ) * (2 * (D.sitesPerSide : ℝ) * D.spacing) =
      C.centeredRep (x : D.Torus) - (n D.dir : ℝ) * D.spacing := by
    rw [← hside]
    exact hk
  have hform : C.centeredRep (x : D.Torus) =
      C.pos + (((n D.dir + 2 * (D.sitesPerSide : ℤ) * k - n₀ - 1 : ℤ) : ℝ) + 1 / 2) * D.spacing := by
    push_cast
    rw [hn₀]
    linear_combination -hk'
  generalize n D.dir + 2 * (D.sitesPerSide : ℤ) * k - n₀ - 1 = j at hform
  refine ⟨j, ?_, ?_, hform⟩
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : (j : ℝ) + 1 ≤ -(D.sitesPerSide : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 hlt
    have h2 := hmem.1
    rw [hform, hs] at h2
    nlinarith
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : (D.sitesPerSide : ℝ) ≤ (j : ℝ) := by
      have : (D.sitesPerSide : ℤ) ≤ j := by omega
      exact_mod_cast this
    have h2 := hmem.2
    rw [hform, hs] at h2
    nlinarith
private theorem exists_vertex_of_levelAt (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    (C : LinkLevel D) (j : ℤ) (h₁ : -(D.sitesPerSide : ℤ) ≤ j) (h₂ : j ≤ (D.sitesPerSide : ℤ) - 1) :
    ∃ x : D.Vertex, C.centeredRep (x : D.Torus) = levelAt C j := by
  obtain ⟨n₀, hn₀⟩ := C.isLinkLevel
  have ha := spacing_pos (D := D)
  have h₁' : -(D.sitesPerSide : ℝ) ≤ (j : ℝ) := by exact_mod_cast h₁
  have h₂' : (j : ℝ) ≤ (D.sitesPerSide : ℝ) - 1 := by exact_mod_cast h₂
  refine ⟨(n₀ + 1 + j) • PeriodicLattice.unitStep D.L D.m (D.K : ℕ) D.dir,
    centeredRep_eq_of_mem C ?_ ?_⟩
  · have e : levelAt C j = ((n₀ + 1 + j : ℤ) : ℝ) * D.spacing := by
      rw [levelAt, hn₀]
      push_cast
      ring
    have e' : ((n₀ + 1 + j : ℤ) : ℝ) * D.spacing = (n₀ + 1 + j) • D.spacing := by rw [zsmul_eq_mul]
    rw [e, e']
    have e'' : ((((n₀ + 1 + j) • PeriodicLattice.unitStep D.L D.m (D.K : ℕ) D.dir : D.Vertex) :
        D.Torus) D.dir) = (n₀ + 1 + j) • ((D.spacing : ℝ) : D.CircleCoord) := by
      simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
      rfl
    rw [e'']
    exact map_zsmul
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (PeriodicLattice.torusSide D.L D.m))) _ _
  · rw [hs, levelAt]
    constructor <;> nlinarith
private theorem levelAt_mem_lower (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    (C : LinkLevel D) {j : ℤ} (h₁ : -(D.sitesPerSide : ℤ) ≤ j) (h₂ : j ≤ -1) :
    C.pos - D.side / 2 < levelAt C j ∧ levelAt C j < C.pos := by
  have ha := spacing_pos (D := D)
  have h₁' : -(D.sitesPerSide : ℝ) ≤ (j : ℝ) := by exact_mod_cast h₁
  have h₂' : (j : ℝ) ≤ -1 := by exact_mod_cast h₂
  rw [hs, levelAt]
  constructor <;> nlinarith
private theorem levelAt_mem_upper (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    (C : LinkLevel D) {j : ℤ} (h₁ : 0 ≤ j) (h₂ : j ≤ (D.sitesPerSide : ℤ) - 1) :
    C.pos < levelAt C j ∧ levelAt C j < C.pos + D.side / 2 := by
  have ha := spacing_pos (D := D)
  have h₁' : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h₁
  have h₂' : (j : ℝ) ≤ (D.sitesPerSide : ℝ) - 1 := by exact_mod_cast h₂
  rw [hs, levelAt]
  constructor <;> nlinarith
section Sides
variable (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing) {C : LinkLevel D}
  (hF : LevelPartition.PartsAsLevelSets C)
include hF
private theorem mem_openSlab_pos (y : D.Torus) :
    y ∈ C.openSlab .pos ↔ C.pos < C.centeredRep y ∧ C.centeredRep y < C.pos + D.side / 2 := by
  rw [hF.1]
  exact Iff.rfl
private theorem mem_openSlab_neg (y : D.Torus) :
    y ∈ C.openSlab .neg ↔ C.pos - D.side / 2 < C.centeredRep y ∧ C.centeredRep y < C.pos := by
  rw [hF.2.1]
  exact Iff.rfl
private theorem vertex_pos_iff (x : D.Vertex) :
    (x : D.Torus) ∈ C.halfVertices .pos ↔ C.pos < C.centeredRep (x : D.Torus) := by
  constructor
  · rintro ⟨-, h⟩
    exact ((mem_openSlab_pos hF _).1 h).1
  · intro h
    exact ⟨x.2, (mem_openSlab_pos hF _).2 ⟨h, (C.isCenteredRep_centeredRep (x : D.Torus)).2.2⟩⟩
include hs
private theorem vertex_neg_iff (x : D.Vertex) :
    (x : D.Torus) ∈ C.halfVertices .neg ↔ C.centeredRep (x : D.Torus) < C.pos := by
  constructor
  · rintro ⟨-, h⟩
    exact ((mem_openSlab_neg hF _).1 h).2
  · intro h
    refine ⟨x.2, (mem_openSlab_neg hF _).2 ⟨?_, h⟩⟩
    obtain ⟨j, h₁, h₂, e⟩ := centeredRep_vertex hs C x
    rw [e] at h ⊢
    have hj : j ≤ -1 := by
      by_contra hlt
      have := (levelAt_mem_upper hs C (j := j) (by omega) h₂).1
      linarith
    exact (levelAt_mem_lower hs C h₁ hj).1
omit hF in
private theorem centeredRep_ne_pos (x : D.Vertex) : C.centeredRep (x : D.Torus) ≠ C.pos := by
  obtain ⟨j, h₁, h₂, e⟩ := centeredRep_vertex hs C x
  rw [e]
  rcases lt_or_ge j 0 with h | h
  · exact (levelAt_mem_lower hs C h₁ (by omega)).2.ne
  · exact (levelAt_mem_upper hs C h h₂).1.ne'
private theorem vertex_pos_or_neg (x : D.Vertex) :
    (x : D.Torus) ∈ C.halfVertices .pos ∨ (x : D.Torus) ∈ C.halfVertices .neg := by
  rcases lt_or_gt_of_ne (centeredRep_ne_pos hs (C := C) x) with h | h
  · exact Or.inr ((vertex_neg_iff hs hF x).2 h)
  · exact Or.inl ((vertex_pos_iff hF x).2 h)
private theorem vertex_not_pos_and_neg (x : D.Vertex) (h₁ : (x : D.Torus) ∈ C.halfVertices .pos)
    (h₂ : (x : D.Torus) ∈ C.halfVertices .neg) : False :=
  lt_asymm ((vertex_pos_iff hF x).1 h₁) ((vertex_neg_iff hs hF x).1 h₂)
private theorem mem_halfVertices_of_centeredRep_eq {x y : D.Vertex}
    (h : C.centeredRep (x : D.Torus) = C.centeredRep (y : D.Torus)) (σ : SlabSide)
    (hx : (x : D.Torus) ∈ C.halfVertices σ) : (y : D.Torus) ∈ C.halfVertices σ := by
  cases σ
  · exact (vertex_pos_iff hF y).2 (h ▸ (vertex_pos_iff hF x).1 hx)
  · exact (vertex_neg_iff hs hF y).2 (h ▸ (vertex_neg_iff hs hF x).1 hx)
end Sides
private theorem coord_shiftBy_of_ne (x : D.Vertex) {ν : Fin 4} (h : ν ≠ D.dir) :
    (shiftBy x ν : D.Torus) D.dir = (x : D.Torus) D.dir := by
  simp [shiftBy, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h.symm]
private theorem coord_shiftBy_dir (x : D.Vertex) :
    (shiftBy x D.dir : D.Torus) D.dir = (x : D.Torus) D.dir + ((D.spacing : ℝ) : D.CircleCoord) := by
  simp [shiftBy, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
  rfl
private theorem centeredRep_shiftBy_of_ne (C : LinkLevel D) (x : D.Vertex) {ν : Fin 4}
    (h : ν ≠ D.dir) : C.centeredRep (shiftBy x ν : D.Torus) = C.centeredRep (x : D.Torus) :=
  centeredRep_congr C (coord_shiftBy_of_ne x h)
private theorem heightStep (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    (hn : 2 ≤ D.sitesPerSide) (C : LinkLevel D) : HeightStep C := by
  have ha := spacing_pos (D := D)
  refine ⟨fun x ν h => centeredRep_shiftBy_of_ne C x h, fun x h => ?_, fun x h => ?_⟩
  · obtain ⟨j, h₁, h₂, e⟩ := centeredRep_vertex hs C x
    have hne : j ≠ (D.sitesPerSide : ℤ) - 1 := by
      rintro rfl
      apply h
      rw [e, levelAt, hs]
      push_cast
      ring
    have h₃ : (j : ℝ) ≤ (D.sitesPerSide : ℝ) - 2 := by
      have : j ≤ (D.sitesPerSide : ℤ) - 2 := by omega
      exact_mod_cast this
    have h₁' : -(D.sitesPerSide : ℝ) ≤ (j : ℝ) := by exact_mod_cast h₁
    refine centeredRep_eq_of_mem C ?_ ?_
    · rw [AddCircle.coe_add, coe_centeredRep, coord_shiftBy_dir]
    · rw [e, levelAt, hs]
      constructor <;> nlinarith
  · have hn' : (2 : ℝ) ≤ D.sitesPerSide := by exact_mod_cast hn
    refine centeredRep_eq_of_mem C ?_ ?_
    · have e : C.pos - D.side / 2 + D.spacing / 2 + D.side =
          C.centeredRep (x : D.Torus) + D.spacing := by
        rw [h]
        ring
      rw [← coe_add_side_eq, e, AddCircle.coe_add, coe_centeredRep, coord_shiftBy_dir]
    · rw [hs]
      constructor <;> nlinarith
private theorem vertexSplitting (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    {C : LinkLevel D} (hF : LevelPartition.PartsAsLevelSets C) (hT : LinkReflection.ActsOnTorus C) :
    VertexSplitting C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext r
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨j, h₁, h₂, h₃⟩ := centeredRep_vertex hs C x
      exact ⟨j, h₁, h₂, h₃⟩
    · rintro ⟨j, h₁, h₂, rfl⟩
      exact exists_vertex_of_levelAt hs C j h₁ h₂
  · intro x j h₁ h₂ h₃
    exact (vertex_neg_iff hs hF x).2 (h₃ ▸ (levelAt_mem_lower hs C h₁ h₂).2)
  · intro x j h₁ h₂ h₃
    exact (vertex_pos_iff hF x).2 (h₃ ▸ (levelAt_mem_upper hs C h₁ h₂).1)
  · intro x hx
    have e : C.mirrorSet = D.nearPlane C.pos ∪ D.farPlane C.pos := image_union _ _ _
    rw [e] at hx
    rcases hx with h | h
    · rw [hF.2.2.1] at h
      exact centeredRep_ne_pos hs x h
    · rw [hF.2.2.2] at h
      have h' : C.centeredRep (x : D.Torus) = C.pos - D.side / 2 := h
      have hpos := LinkLevel.side_pos (D := D)
      rcases vertex_pos_or_neg hs hF x with h₁ | h₁
      · have := ((mem_openSlab_pos hF _).1 h₁.2).1
        linarith
      · have := ((mem_openSlab_neg hF _).1 h₁.2).1
        linarith
  · ext y
    constructor
    · intro hy
      exact vertex_pos_or_neg hs hF ⟨y, hy⟩
    · rintro (h | h) <;> exact h.1
  · refine Set.disjoint_left.2 fun y h₁ h₂ => ?_
    exact vertex_not_pos_and_neg hs hF ⟨y, h₁.1⟩ h₁ h₂
  · rw [LinkLevel.halfVertices, LinkLevel.halfVertices, image_inter hT.1.injective, hT.2.2.1,
      hT.2.2.2.2.1]
  · rw [LinkLevel.halfVertices, LinkLevel.halfVertices, image_inter hT.1.injective, hT.2.2.1,
      hT.2.2.2.2.2]
private theorem coord_refl_of_ne (C : LinkLevel D) (y : D.Torus) {ν : Fin 4} (h : ν ≠ D.dir) :
    C.refl y ν = y ν := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkReflection.refl_apply_of_ne <;> assumption
private theorem coord_refl_dir (C : LinkLevel D) (y : D.Torus) :
    C.refl y D.dir = ((2 * C.pos : ℝ) : D.CircleCoord) - y D.dir := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkReflection.refl_apply_dir <;> assumption
private theorem shiftBy_eq_refl (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    (hn : 2 ≤ D.sitesPerSide) {C : LinkLevel D} (hF : LevelPartition.PartsAsLevelSets C)
    (x : D.Vertex)
    (h : ((x : D.Torus) ∈ C.halfVertices .pos ∧ (shiftBy x D.dir : D.Torus) ∈ C.halfVertices .neg) ∨
      ((x : D.Torus) ∈ C.halfVertices .neg ∧ (shiftBy x D.dir : D.Torus) ∈ C.halfVertices .pos)) :
    (shiftBy x D.dir : D.Torus) = C.refl x := by
  have ha := spacing_pos (D := D)
  have hrule := heightStep hs hn C
  funext ν
  by_cases hν : ν = D.dir
  · subst hν
    rw [coord_shiftBy_dir, coord_refl_dir, ← coe_centeredRep C (x : D.Torus), ← AddCircle.coe_add,
      ← AddCircle.coe_sub]
    by_cases hr : C.centeredRep (x : D.Torus) = C.pos + D.side / 2 - D.spacing / 2
    · rw [← coe_add_side_eq (2 * C.pos - C.centeredRep (x : D.Torus)), hr]
      congr 1
      ring
    · have e₁ := hrule.2.1 x hr
      obtain ⟨j, h₁, h₂, e⟩ := centeredRep_vertex hs C x
      have hj : j = -1 := by
        rcases h with ⟨hp, hm⟩ | ⟨hm, hp⟩
        · exfalso
          have a₁ := (vertex_pos_iff hF x).1 hp
          have a₂ := (vertex_neg_iff hs hF (shiftBy x D.dir)).1 hm
          rw [e₁] at a₂
          linarith
        · have a₁ := (vertex_neg_iff hs hF x).1 hm
          have a₂ := (vertex_pos_iff hF (shiftBy x D.dir)).1 hp
          rw [e₁] at a₂
          rw [e, levelAt] at a₁ a₂
          have b₁ : j ≤ -1 := by
            by_contra hh
            have : (0 : ℝ) ≤ j := by exact_mod_cast (by omega : (0 : ℤ) ≤ j)
            nlinarith
          have b₂ : -1 ≤ j := by
            by_contra hh
            have : (j : ℝ) ≤ -2 := by exact_mod_cast (by omega : j ≤ -2)
            nlinarith
          omega
      subst hj
      congr 1
      rw [e, levelAt]
      push_cast
      ring
  · rw [coord_refl_of_ne C _ hν]
    simp [shiftBy, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
private theorem transversal_edge_facts (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    {C : LinkLevel D} (hF : LevelPartition.PartsAsLevelSets C) {b : D.Edge}
    (hb : b ∈ C.transversalEdges) :
    b.target = shiftBy b.source D.dir ∧ C.Straddles b := by
  obtain ⟨⟨ν, hν⟩, hp, hm⟩ := hb
  have hhead : b.target = shiftBy b.source ν := by
    rw [shiftBy, ← hν]
    abel
  have hjoin : C.Straddles b := by
    rcases vertex_pos_or_neg hs hF b.source with h₁ | h₁ <;>
      rcases vertex_pos_or_neg hs hF b.target with h₂ | h₂
    · exact absurd ⟨⟨ν, hν⟩, h₁, h₂⟩ hp
    · exact Or.inr ⟨h₁, h₂⟩
    · exact Or.inl ⟨h₁, h₂⟩
    · exact absurd ⟨⟨ν, hν⟩, h₁, h₂⟩ hm
  refine ⟨?_, hjoin⟩
  by_cases h : ν = D.dir
  · rw [hhead, h]
  · exfalso
    have e : C.centeredRep (b.source : D.Torus) = C.centeredRep (b.target : D.Torus) := by
      rw [hhead]
      exact (centeredRep_shiftBy_of_ne C _ h).symm
    rcases hjoin with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact vertex_not_pos_and_neg hs hF b.target h₂
        (mem_halfVertices_of_centeredRep_eq hs hF e .neg h₁)
    · exact vertex_not_pos_and_neg hs hF b.target
        (mem_halfVertices_of_centeredRep_eq hs hF e .pos h₁) h₂
private theorem orientedAcross_of_neg {C : LinkLevel D} {b : D.Edge}
    (h₁ : (b.source : D.Torus) ∈ C.halfVertices .neg)
    (h₂ : (b.target : D.Torus) ∈ C.halfVertices .pos) :
    C.orientedAcross b = b :=
  if_pos ⟨h₁, h₂⟩
private theorem orientedAcross_of_pos (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    {C : LinkLevel D} (hF : LevelPartition.PartsAsLevelSets C) {b : D.Edge}
    (h₁ : (b.source : D.Torus) ∈ C.halfVertices .pos) : C.orientedAcross b = b.opposite :=
  if_neg fun h => vertex_not_pos_and_neg hs hF b.source h₁ h.1
private theorem endOn_pos_eq_refl (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    (hn : 2 ≤ D.sitesPerSide) {C : LinkLevel D} (hF : LevelPartition.PartsAsLevelSets C)
    (hI : Function.Involutive C.refl) {b : D.Edge} (hb : b ∈ C.transversalEdges) :
    (C.endOn .pos b : D.Torus) = C.refl (C.endOn .neg b) := by
  obtain ⟨hh, hj⟩ := transversal_edge_facts hs hF hb
  rcases hj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have e := orientedAcross_of_neg h₁ h₂
    simp only [LinkLevel.endOn, e]
    rw [hh]
    exact shiftBy_eq_refl hs hn hF _ (Or.inr ⟨h₁, by rw [← hh]; exact h₂⟩)
  · have e := orientedAcross_of_pos hs hF h₁
    simp only [LinkLevel.endOn, e]
    have e' : (b.target : D.Torus) = C.refl b.source := by
      rw [hh]
      exact shiftBy_eq_refl hs hn hF _ (Or.inl ⟨h₁, by rw [← hh]; exact h₂⟩)
    change (b.source : D.Torus) = C.refl b.target
    rw [e', hI]
private theorem transversalEdgeProperties (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing)
    (hn : 2 ≤ D.sitesPerSide) {C : LinkLevel D} (hF : LevelPartition.PartsAsLevelSets C)
    (hI : Function.Involutive C.refl) : TransversalEdgeProperties C := by
  intro b hb
  obtain ⟨hh, hj⟩ := transversal_edge_facts hs hF hb
  refine ⟨Or.inl ?_, ⟨hb, hj⟩, endOn_pos_eq_refl hs hn hF hI hb, fun U => ?_⟩
  · rw [hh]
    simp [shiftBy]
  · rcases C.orientedAcross_eq_or b with e | e
    · exact Or.inl (by rw [LinkLevel.transversalVariable, e])
    · exact Or.inr (by rw [LinkLevel.transversalVariable, e]; exact U.2.2 b (mem_univ _))
section Mirror
variable {C : LinkLevel D} {s : D.Symmetry}
private theorem opposite_not_positive
    (hX : ∀ b : D.Edge, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {b : D.Edge} (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases hX b with ⟨_, h₂⟩ | ⟨_, h₂⟩
  · exact h₂
  · exact absurd h h₂
private theorem opposite_positive
    (hX : ∀ b : D.Edge, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {b : D.Edge} (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases hX b with ⟨h₁, _⟩ | ⟨h₁, _⟩
  · exact absurd h₁ h
  · exact h₁
private theorem positiveReflectedEdge_of_pos (hsθ : s.toFun = C.refl) {b : D.Edge}
    (h : (MirrorData.Symmetry.bondImage s b).IsPositivelyOriented) :
    C.positiveReflectedEdge b = MirrorData.Symmetry.bondImage s b := by
  have e : C.reflectedEdge b = MirrorData.Symmetry.bondImage s b :=
    (C.bondMap_eq_reflectedEdge s hsθ b).symm
  rw [LinkLevel.positiveReflectedEdge, e, if_pos h]
private theorem positiveReflectedEdge_of_not_pos (hsθ : s.toFun = C.refl) {b : D.Edge}
    (h : ¬(MirrorData.Symmetry.bondImage s b).IsPositivelyOriented) :
    C.positiveReflectedEdge b = (MirrorData.Symmetry.bondImage s b).opposite := by
  have e : C.reflectedEdge b = MirrorData.Symmetry.bondImage s b :=
    (C.bondMap_eq_reflectedEdge s hsθ b).symm
  rw [LinkLevel.positiveReflectedEdge, e, if_neg h]
private theorem positiveReflectedEdge_eq (hsθ : s.toFun = C.refl)
    (hX : ∀ b : D.Edge, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {b b' : D.Edge} (hb' : b'.IsPositivelyOriented)
    (h : MirrorData.Symmetry.bondImage s b = b' ∨
      MirrorData.Symmetry.bondImage s b = b'.opposite) : C.positiveReflectedEdge b = b' := by
  rcases h with h | h
  · rw [positiveReflectedEdge_of_pos hsθ (h ▸ hb'), h]
  · rw [positiveReflectedEdge_of_not_pos hsθ (h ▸ opposite_not_positive hX hb'), h]
    rfl
private theorem bondImage_eq_or (hsθ : s.toFun = C.refl) (b : D.Edge) :
    MirrorData.Symmetry.bondImage s b = C.positiveReflectedEdge b ∨
      MirrorData.Symmetry.bondImage s b = (C.positiveReflectedEdge b).opposite := by
  by_cases h : (MirrorData.Symmetry.bondImage s b).IsPositivelyOriented
  · exact Or.inl (positiveReflectedEdge_of_pos hsθ h).symm
  · rw [positiveReflectedEdge_of_not_pos hsθ h]
    exact Or.inr rfl
private theorem positiveReflectedEdge_mem (hsθ : s.toFun = C.refl)
    (hB : LinkReflection.ActsOnBonds C s)
    (hX : ∀ b : D.Edge, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {σ τ : SlabSide} (hθ : ∀ y ∈ C.halfVertices σ, C.refl y ∈ C.halfVertices τ) {b : D.Edge}
    (hb : b ∈ C.halfEdges σ) : C.positiveReflectedEdge b ∈ C.halfEdges τ := by
  obtain ⟨h₁, h₂⟩ := hB.1 b
  have a₁ := hθ _ hb.2.1
  have a₂ := hθ _ hb.2.2
  rw [← h₁] at a₁
  rw [← h₂] at a₂
  by_cases hp : (MirrorData.Symmetry.bondImage s b).IsPositivelyOriented
  · rw [positiveReflectedEdge_of_pos hsθ hp]
    exact ⟨hp, a₁, a₂⟩
  · rw [positiveReflectedEdge_of_not_pos hsθ hp]
    exact ⟨opposite_positive hX hp, a₂, a₁⟩
private theorem positiveReflectedEdge_bijOn (hsθ : s.toFun = C.refl)
    (hB : LinkReflection.ActsOnBonds C s)
    (hX : ∀ b : D.Edge, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hθp : ∀ y ∈ C.halfVertices .pos, C.refl y ∈ C.halfVertices .neg)
    (hθm : ∀ y ∈ C.halfVertices .neg, C.refl y ∈ C.halfVertices .pos) :
    BijOn C.positiveReflectedEdge (C.halfEdges .pos) (C.halfEdges .neg) := by
  have hinj := hB.2.1.injective
  refine ⟨fun b hb => positiveReflectedEdge_mem hsθ hB hX hθp hb, ?_, ?_⟩
  · intro b₁ h₁ b₂ h₂ e
    have key : ∀ {b b' : D.Edge}, b.IsPositivelyOriented → b'.IsPositivelyOriented →
        MirrorData.Symmetry.bondImage s b =
          (MirrorData.Symmetry.bondImage s b').opposite → False := by
      intro b b' hb hb' h
      rw [← hB.2.2.1] at h
      have := hinj h
      rw [this] at hb
      exact opposite_not_positive hX hb' hb
    rcases bondImage_eq_or hsθ b₁ with a₁ | a₁ <;> rcases bondImage_eq_or hsθ b₂ with a₂ | a₂
    · exact hinj (by rw [a₁, a₂, e])
    · exact (key h₁.1 h₂.1 (by rw [a₂, a₁, e]; rfl)).elim
    · exact (key h₁.1 h₂.1 (by rw [a₂, a₁, e])).elim
    · exact hinj (by rw [a₁, a₂, e])
  · intro b' hb'
    have hinv : MirrorData.Symmetry.bondImage s (MirrorData.Symmetry.bondImage s b') = b' :=
      hB.2.1 b'
    obtain ⟨h₁, h₂⟩ := hB.1 b'
    have a₁ := hθm _ hb'.2.1
    have a₂ := hθm _ hb'.2.2
    rw [← h₁] at a₁
    rw [← h₂] at a₂
    by_cases hp : (MirrorData.Symmetry.bondImage s b').IsPositivelyOriented
    · exact ⟨_, ⟨hp, a₁, a₂⟩, positiveReflectedEdge_eq hsθ hX hb'.1 (Or.inl hinv)⟩
    · refine ⟨_, ⟨opposite_positive hX hp, a₂, a₁⟩,
        positiveReflectedEdge_eq hsθ hX hb'.1 (Or.inr ?_)⟩
      rw [hB.2.2.1, hinv]
private theorem pullbackOnPositiveEdges (hsθ : s.toFun = C.refl)
    (hB : LinkReflection.ActsOnBonds C s) : PullbackOnPositiveEdges C s := by
  intro U b hb
  constructor
  · intro hnp
    obtain ⟨ν, hν⟩ := hb.1
    have hpar : b.IsParallelToAxis ν := Or.inl hν
    have hne : ν ≠ D.dir := by
      rintro rfl
      exact hnp hpar
    rw [positiveReflectedEdge_of_pos hsθ ((hB.2.2.2 b ν hb.1 hpar).2.1 hne)]
    rfl
  · intro hp
    have hneg := (hB.2.2.2 b D.dir hb.1 hp).2.2 rfl
    rw [positiveReflectedEdge_of_not_pos hsθ hneg]
    exact U.2.2 (MirrorData.Symmetry.bondImage s b).opposite (mem_univ _)
private theorem faceImage_mem (hsθ : s.toFun = C.refl)
    (hP : LinkReflection.ActsOnPlaquettes C s)
    {σ τ : SlabSide} (hθ : ∀ y ∈ C.halfVertices σ, C.refl y ∈ C.halfVertices τ) {p : D.Face}
    (hp : p ∈ C.halfFaces σ) :
    MirrorData.Symmetry.faceImage s p ∈ C.halfFaces τ := by
  intro x hx
  have e : (MirrorData.Symmetry.faceImage s p).vertices = _ := hP.1 p
  rw [e] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  change s.toFun z ∈ _
  rw [hsθ]
  exact hθ _ (hp z hz)
private theorem image_halfFaces (hsθ : s.toFun = C.refl)
    (hP : LinkReflection.ActsOnPlaquettes C s)
    (hθp : ∀ y ∈ C.halfVertices .pos, C.refl y ∈ C.halfVertices .neg)
    (hθm : ∀ y ∈ C.halfVertices .neg, C.refl y ∈ C.halfVertices .pos) :
    MirrorData.Symmetry.faceImage s '' C.halfFaces .pos = C.halfFaces .neg := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact faceImage_mem hsθ hP hθp hp
  · intro hq
    exact ⟨_, faceImage_mem hsθ hP hθm hq, hP.2.1 q⟩
end Mirror
section Plaquettes
variable {C : LinkLevel D}
private theorem centeredRep_vertex_of_transverse {p : D.Face} (h₁ : p.firstAxis ≠ D.dir)
    (h₂ : p.secondAxis ≠ D.dir) {z : D.Vertex} (hz : z ∈ p.vertices) :
    C.centeredRep (z : D.Torus) = C.centeredRep (p.origin : D.Torus) := by
  simp only [PeriodicLattice.Plaquette.vertices, mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rfl
  · exact centeredRep_shiftBy_of_ne C _ h₁
  · exact (centeredRep_shiftBy_of_ne C _ h₂).trans (centeredRep_shiftBy_of_ne C _ h₁)
  · exact centeredRep_shiftBy_of_ne C _ h₂
private theorem vertices_eq {p : D.Face} (h : C.ContainsMirrorAxis p) :
    p.vertices = {p.origin, shiftBy p.origin D.dir, shiftBy p.origin (C.complementaryAxis p),
      shiftBy (shiftBy p.origin (C.complementaryAxis p)) D.dir} := by
  have e : p.origin + PeriodicLattice.unitStep D.L D.m (D.K : ℕ) p.firstAxis +
      PeriodicLattice.unitStep D.L D.m (D.K : ℕ) p.secondAxis =
      p.origin + PeriodicLattice.unitStep D.L D.m (D.K : ℕ) p.secondAxis +
        PeriodicLattice.unitStep D.L D.m (D.K : ℕ) p.firstAxis := add_right_comm _ _ _
  rcases h with h | h
  · have ho : C.complementaryAxis p = p.secondAxis := if_pos h.symm
    rw [ho, h]
    ext z
    simp only [PeriodicLattice.Plaquette.vertices, mem_insert_iff, mem_singleton_iff, shiftBy, e]
    tauto
  · have hne : p.firstAxis ≠ D.dir := by
      rw [h]
      exact ne_of_lt p.firstAxis_lt_secondAxis
    have ho : C.complementaryAxis p = p.firstAxis := if_neg hne
    rw [ho, h]
    ext z
    simp only [PeriodicLattice.Plaquette.vertices, mem_insert_iff, mem_singleton_iff, shiftBy]
    tauto
private theorem complementaryAxis_ne {p : D.Face} (h : C.ContainsMirrorAxis p) :
    C.complementaryAxis p ≠ D.dir := by
  rcases h with h | h
  · have ho : C.complementaryAxis p = p.secondAxis := if_pos h.symm
    rw [ho, h]
    exact (ne_of_lt p.firstAxis_lt_secondAxis).symm
  · have hne : p.firstAxis ≠ D.dir := by
      rw [h]
      exact ne_of_lt p.firstAxis_lt_secondAxis
    have ho : C.complementaryAxis p = p.firstAxis := if_neg hne
    rw [ho]
    exact hne
variable (hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing) (hF : LevelPartition.PartsAsLevelSets C)
include hs hF
private theorem containsMirrorAxis_of_transversal {p : D.Face} (hp : p ∈ C.transversalFaces) :
    C.ContainsMirrorAxis p := by
  by_contra hd
  have h₁ : p.firstAxis ≠ D.dir := fun e => hd (Or.inl e.symm)
  have h₂ : p.secondAxis ≠ D.dir := fun e => hd (Or.inr e.symm)
  have key : ∀ σ, (p.origin : D.Torus) ∈ C.halfVertices σ → p ∈ C.halfFaces σ :=
    fun σ hx z hz =>
      mem_halfVertices_of_centeredRep_eq hs hF (centeredRep_vertex_of_transverse h₁ h₂ hz).symm σ hx
  rcases vertex_pos_or_neg hs hF p.origin with h | h
  · exact hp.1 (key _ h)
  · exact hp.2 (key _ h)
private theorem mem_halfFaces_of_origin {p : D.Face} (hd : C.ContainsMirrorAxis p) {σ : SlabSide}
    (h₁ : (p.origin : D.Torus) ∈ C.halfVertices σ)
    (h₂ : (shiftBy p.origin D.dir : D.Torus) ∈ C.halfVertices σ) : p ∈ C.halfFaces σ := by
  have hne := complementaryAxis_ne hd
  intro z hz
  rw [vertices_eq hd] at hz
  simp only [mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact mem_halfVertices_of_centeredRep_eq hs hF (centeredRep_shiftBy_of_ne C _ hne).symm σ h₁
  · have e : shiftBy (shiftBy p.origin (C.complementaryAxis p)) D.dir =
        shiftBy (shiftBy p.origin D.dir) (C.complementaryAxis p) := add_right_comm _ _ _
    rw [e]
    exact mem_halfVertices_of_centeredRep_eq hs hF (centeredRep_shiftBy_of_ne C _ hne).symm σ h₂
private theorem transversal_face_sides {p : D.Face} (hp : p ∈ C.transversalFaces) :
    ((p.origin : D.Torus) ∈ C.halfVertices .neg ∧
      (shiftBy p.origin D.dir : D.Torus) ∈ C.halfVertices .pos) ∨
    ((p.origin : D.Torus) ∈ C.halfVertices .pos ∧
      (shiftBy p.origin D.dir : D.Torus) ∈ C.halfVertices .neg) := by
  have hd := containsMirrorAxis_of_transversal hs hF hp
  rcases vertex_pos_or_neg hs hF p.origin with h₁ | h₁ <;>
    rcases vertex_pos_or_neg hs hF (shiftBy p.origin D.dir) with h₂ | h₂
  · exact absurd (mem_halfFaces_of_origin hs hF hd h₁ h₂) hp.1
  · exact Or.inr ⟨h₁, h₂⟩
  · exact Or.inl ⟨h₁, h₂⟩
  · exact absurd (mem_halfFaces_of_origin hs hF hd h₁ h₂) hp.2
private theorem transversal_face_corners {p : D.Face} (hp : p ∈ C.transversalFaces) :
    C.lowerEdge p ∈ C.transversalEdges ∧ C.upperEdge p ∈ C.transversalEdges ∧
    C.HasStraddlingEdges p ∧
    (∀ σ : SlabSide, C.upperCorner σ p = shiftBy (C.lowerCorner σ p) (C.complementaryAxis p)) ∧
    ({C.lowerCorner .neg p, C.lowerCorner .pos p, C.upperCorner .pos p,
      C.upperCorner .neg p} : Set D.Vertex) = p.vertices := by
  have hd := containsMirrorAxis_of_transversal hs hF hp
  have hne := complementaryAxis_ne hd
  have hcomm : shiftBy (shiftBy p.origin (C.complementaryAxis p)) D.dir =
      shiftBy (shiftBy p.origin D.dir) (C.complementaryAxis p) := add_right_comm _ _ _
  have hy : ∀ {σ : SlabSide}, (p.origin : D.Torus) ∈ C.halfVertices σ →
      (shiftBy p.origin (C.complementaryAxis p) : D.Torus) ∈ C.halfVertices σ := fun {σ} h =>
    mem_halfVertices_of_centeredRep_eq hs hF (centeredRep_shiftBy_of_ne C _ hne).symm σ h
  have hy' : ∀ {σ : SlabSide}, (shiftBy p.origin D.dir : D.Torus) ∈ C.halfVertices σ →
      (shiftBy (shiftBy p.origin (C.complementaryAxis p)) D.dir : D.Torus) ∈ C.halfVertices σ := by
    intro σ h
    rw [hcomm]
    exact mem_halfVertices_of_centeredRep_eq hs hF (centeredRep_shiftBy_of_ne C _ hne).symm σ h
  have notPos : ∀ {b : D.Edge}, (b.source : D.Torus) ∈ C.halfVertices .neg →
      (b.target : D.Torus) ∈ C.halfVertices .pos → b.IsPositivelyOriented →
      b ∈ C.transversalEdges := by
    intro b h₁ h₂ hb
    exact ⟨hb, fun h => vertex_not_pos_and_neg hs hF b.source h.2.1 h₁,
      fun h => vertex_not_pos_and_neg hs hF b.target h₂ h.2.2⟩
  have notNeg : ∀ {b : D.Edge}, (b.source : D.Torus) ∈ C.halfVertices .pos →
      (b.target : D.Torus) ∈ C.halfVertices .neg → b.IsPositivelyOriented →
      b ∈ C.transversalEdges := by
    intro b h₁ h₂ hb
    exact ⟨hb, fun h => vertex_not_pos_and_neg hs hF b.target h.2.2 h₂,
      fun h => vertex_not_pos_and_neg hs hF b.source h₁ h.2.1⟩
  have pos₁ : (C.lowerEdge p).IsPositivelyOriented := ⟨D.dir, by simp [LinkLevel.lowerEdge,
    PeriodicLattice.Bond.forwardFrom]⟩
  have pos₂ : (C.upperEdge p).IsPositivelyOriented := ⟨D.dir, by simp [LinkLevel.upperEdge,
    PeriodicLattice.Bond.forwardFrom]⟩
  rcases transversal_face_sides hs hF hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have m₁ : (C.lowerEdge p).source.1 ∈ C.halfVertices .neg := h₁
    have m₂ : (C.lowerEdge p).target.1 ∈ C.halfVertices .pos := h₂
    have m₃ : (C.upperEdge p).source.1 ∈ C.halfVertices .neg := hy h₁
    have m₄ : (C.upperEdge p).target.1 ∈ C.halfVertices .pos := hy' h₂
    have e₁ := orientedAcross_of_neg m₁ m₂
    have e₂ := orientedAcross_of_neg m₃ m₄
    have c₁ : C.lowerCorner .neg p = p.origin := by
      change (C.orientedAcross (C.lowerEdge p)).source = _
      rw [e₁]
      rfl
    have c₂ : C.lowerCorner .pos p = shiftBy p.origin D.dir := by
      change (C.orientedAcross (C.lowerEdge p)).target = _
      rw [e₁]
      rfl
    have c₃ : C.upperCorner .neg p = shiftBy p.origin (C.complementaryAxis p) := by
      change (C.orientedAcross (C.upperEdge p)).source = _
      rw [e₂]
      rfl
    have c₄ : C.upperCorner .pos p = shiftBy (shiftBy p.origin (C.complementaryAxis p)) D.dir := by
      change (C.orientedAcross (C.upperEdge p)).target = _
      rw [e₂]
      rfl
    refine ⟨notPos m₁ m₂ pos₁, notPos m₃ m₄ pos₂,
      ⟨⟨notPos m₁ m₂ pos₁, Or.inl ⟨m₁, m₂⟩⟩, ⟨notPos m₃ m₄ pos₂, Or.inl ⟨m₃, m₄⟩⟩⟩, ?_, ?_⟩
    · intro σ
      cases σ
      · rw [c₂, c₄, hcomm]
      · rw [c₁, c₃]
    · rw [vertices_eq hd, c₁, c₂, c₃, c₄]
      ext z
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
  · have m₁ : (C.lowerEdge p).source.1 ∈ C.halfVertices .pos := h₁
    have m₂ : (C.lowerEdge p).target.1 ∈ C.halfVertices .neg := h₂
    have m₃ : (C.upperEdge p).source.1 ∈ C.halfVertices .pos := hy h₁
    have m₄ : (C.upperEdge p).target.1 ∈ C.halfVertices .neg := hy' h₂
    have e₁ := orientedAcross_of_pos hs hF m₁
    have e₂ := orientedAcross_of_pos hs hF m₃
    have c₁ : C.lowerCorner .pos p = p.origin := by
      change (C.orientedAcross (C.lowerEdge p)).target = _
      rw [e₁]
      rfl
    have c₂ : C.lowerCorner .neg p = shiftBy p.origin D.dir := by
      change (C.orientedAcross (C.lowerEdge p)).source = _
      rw [e₁]
      rfl
    have c₃ : C.upperCorner .pos p = shiftBy p.origin (C.complementaryAxis p) := by
      change (C.orientedAcross (C.upperEdge p)).target = _
      rw [e₂]
      rfl
    have c₄ : C.upperCorner .neg p = shiftBy (shiftBy p.origin (C.complementaryAxis p)) D.dir := by
      change (C.orientedAcross (C.upperEdge p)).source = _
      rw [e₂]
      rfl
    refine ⟨notNeg m₁ m₂ pos₁, notNeg m₃ m₄ pos₂,
      ⟨⟨notNeg m₁ m₂ pos₁, Or.inr ⟨m₁, m₂⟩⟩, ⟨notNeg m₃ m₄ pos₂, Or.inr ⟨m₃, m₄⟩⟩⟩, ?_, ?_⟩
    · intro σ
      cases σ
      · rw [c₁, c₃]
      · rw [c₂, c₄, hcomm]
    · rw [vertices_eq hd, c₁, c₂, c₃, c₄]
      ext z
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
private theorem transversalFaceProperties (hn : 2 ≤ D.sitesPerSide)
    (hI : Function.Involutive C.refl)
    {s : D.Symmetry} (hsθ : s.toFun = C.refl) (hB : LinkReflection.ActsOnBonds C s)
    (hX : ∀ b : D.Edge, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hHol : PlaquetteNondegeneracy.TraceIndependentOfTraversal D) :
    TransversalFaceProperties C := by
  intro p hp
  have hd := containsMirrorAxis_of_transversal hs hF hp
  obtain ⟨hc₁, hc₂, hJ, hstep, hcor⟩ := transversal_face_corners hs hF hp
  have hcb : ∀ σ, (C.cornerEdge σ p).source = C.lowerCorner σ p ∧
      (C.cornerEdge σ p).target = C.upperCorner σ p := by
    intro σ
    have h : ∃ b : D.Edge, b.source = C.lowerCorner σ p ∧ b.target = C.upperCorner σ p :=
      ⟨PeriodicLattice.Bond.forwardFrom (C.lowerCorner σ p) (C.complementaryAxis p), rfl,
        (hstep σ).symm⟩
    have e : C.cornerEdge σ p = h.choose := dif_pos h
    rw [e]
    exact h.choose_spec
  have hpos : ∀ σ, (C.cornerEdge σ p).IsPositivelyOriented := fun σ => ⟨C.complementaryAxis p, by
    rw [(hcb σ).1, (hcb σ).2, hstep σ]
    simp [shiftBy]⟩
  have hmem : ∀ σ, C.cornerEdge σ p ∈ C.halfEdges σ := fun σ => ⟨hpos σ,
    by rw [(hcb σ).1]; exact C.endOn_mem hJ.1.2 σ,
    by rw [(hcb σ).2]; exact C.endOn_mem hJ.2.2 σ⟩
  have hθ₁ : C.refl (C.lowerCorner .pos p) = C.lowerCorner .neg p := by
    have e := endOn_pos_eq_refl hs hn hF hI hc₁
    change (C.lowerCorner .pos p : D.Torus) = C.refl (C.lowerCorner .neg p) at e
    rw [e, hI]
  have hθ₂ : C.refl (C.upperCorner .pos p) = C.upperCorner .neg p := by
    have e := endOn_pos_eq_refl hs hn hF hI hc₂
    change (C.upperCorner .pos p : D.Torus) = C.refl (C.upperCorner .neg p) at e
    rw [e, hI]
  have hmirror : C.positiveReflectedEdge (C.cornerEdge .pos p) = C.cornerEdge .neg p := by
    refine positiveReflectedEdge_eq hsθ hX (hpos .neg) (Or.inl ?_)
    obtain ⟨a₁, a₂⟩ := hB.1 (C.cornerEdge .pos p)
    refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [a₁, (hcb .pos).1, (hcb .neg).1]
      exact hθ₁
    · rw [a₂, (hcb .pos).2, (hcb .neg).2]
      exact hθ₂
  refine ⟨hd, hc₁, hc₂, hJ, ?_, hstep, fun σ => hcb σ, hmem .pos, hmem .neg, hmirror,
    fun U => ?_⟩
  · rw [← hcor]
    ext z
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  · have hol := hHol p (C.lowerCorner .neg p) (C.lowerCorner .pos p) (C.upperCorner .pos p)
      (C.upperCorner .neg p) (C.orientedAcross (C.lowerEdge p)) (C.cornerEdge .pos p)
      (C.orientedAcross (C.upperEdge p)).opposite (C.cornerEdge .neg p).opposite hcor rfl rfl
      (hcb .pos).1 (hcb .pos).2 rfl rfl (hcb .neg).2 (hcb .neg).1 U.1 U.2
    have e₂ : U.1 (C.orientedAcross (C.upperEdge p)).opposite =
        (C.transversalVariable (C.upperEdge p) U)⁻¹ := U.2.2 _ (mem_univ _)
    have e₃ : U.1 (C.cornerEdge .neg p).opposite = (U.1 (C.cornerEdge .neg p))⁻¹ :=
      U.2.2 _ (mem_univ _)
    rw [e₂, e₃] at hol
    exact hol.symm
private theorem mem_halfFaces_pos_of_barycenter {p : D.Face}
    (h : p.barycenter ∈ C.openSlab .pos) : p ∈ C.halfFaces .pos := by
  have ha := spacing_pos (D := D)
  obtain ⟨hb₁, hb₂⟩ := (mem_openSlab_pos hF _).1 h
  have hcoe : ((C.centeredRep p.barycenter : ℝ) : D.CircleCoord) = p.barycenter D.dir :=
    coe_centeredRep C _
  by_cases hd : C.ContainsMirrorAxis p
  · have hbar : p.barycenter D.dir =
        (p.origin : D.Torus) D.dir + ((D.spacing / 2 : ℝ) : D.CircleCoord) := by
      rcases hd with e | e
      · have hne : D.dir ≠ p.secondAxis := by
          rw [e]
          exact ne_of_lt p.firstAxis_lt_secondAxis
        simp only [PeriodicLattice.Plaquette.barycenter, Pi.add_apply, PeriodicLattice.pointOnAxis,
          Pi.single_eq_of_ne hne, add_zero]
        rw [e, Pi.single_eq_same]
        rfl
      · have hne : D.dir ≠ p.firstAxis := by
          rw [e]
          exact (ne_of_lt p.firstAxis_lt_secondAxis).symm
        simp only [PeriodicLattice.Plaquette.barycenter, Pi.add_apply, PeriodicLattice.pointOnAxis,
          Pi.single_eq_of_ne hne, add_zero]
        rw [e, Pi.single_eq_same]
        rfl
    obtain ⟨j, h₁, h₂, e⟩ := centeredRep_vertex hs C p.origin
    have h0 : ((C.centeredRep p.barycenter - (C.centeredRep (p.origin : D.Torus) + D.spacing / 2) :
        ℝ) : D.CircleCoord) = 0 := by
      rw [AddCircle.coe_sub, AddCircle.coe_add, coe_centeredRep, coe_centeredRep, hbar, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
    have hside : PeriodicLattice.torusSide D.L D.m = 2 * (D.sitesPerSide : ℝ) * D.spacing := by
      change D.side = _
      linarith
    rw [zsmul_eq_mul] at hk
    have hk' : (k : ℝ) * (2 * (D.sitesPerSide : ℝ) * D.spacing) =
        C.centeredRep p.barycenter - (C.centeredRep (p.origin : D.Torus) + D.spacing / 2) := by
      rw [← hside]
      exact hk
    have hform : C.centeredRep p.barycenter =
        C.pos + ((j + 1 + 2 * (D.sitesPerSide : ℤ) * k : ℤ) : ℝ) * D.spacing := by
      rw [e, levelAt] at hk'
      push_cast
      linear_combination -hk'
    generalize j + 1 + 2 * (D.sitesPerSide : ℤ) * k = t at hform
    rw [hform] at hb₁ hb₂
    rw [hs] at hb₂
    have ht₁ : 1 ≤ t := by
      by_contra hh
      have : (t : ℝ) ≤ 0 := by exact_mod_cast (by omega : t ≤ 0)
      nlinarith
    have ht₂ : t ≤ (D.sitesPerSide : ℤ) - 1 := by
      by_contra hh
      have : (D.sitesPerSide : ℝ) ≤ t := by exact_mod_cast (by omega : (D.sitesPerSide : ℤ) ≤ t)
      nlinarith
    have ht₁' : (1 : ℝ) ≤ t := by exact_mod_cast ht₁
    have ht₂' : (t : ℝ) ≤ (D.sitesPerSide : ℝ) - 1 := by exact_mod_cast ht₂
    have hrep : ((C.centeredRep p.barycenter - D.spacing / 2 : ℝ) : D.CircleCoord) =
        (p.origin : D.Torus) D.dir := by
      rw [AddCircle.coe_sub, hcoe, hbar]
      abel
    have hx : C.centeredRep (p.origin : D.Torus) = C.centeredRep p.barycenter - D.spacing / 2 := by
      refine centeredRep_eq_of_mem C hrep ?_
      rw [hform, hs]
      constructor <;> nlinarith
    have hrep' : ((C.centeredRep p.barycenter + D.spacing / 2 : ℝ) : D.CircleCoord) =
        (shiftBy p.origin D.dir : D.Torus) D.dir := by
      rw [coord_shiftBy_dir, ← hrep, ← AddCircle.coe_add]
      congr 1
      ring
    have hy : C.centeredRep (shiftBy p.origin D.dir : D.Torus) =
        C.centeredRep p.barycenter + D.spacing / 2 := by
      refine centeredRep_eq_of_mem C hrep' ?_
      rw [hform, hs]
      constructor <;> nlinarith
    refine mem_halfFaces_of_origin hs hF hd ((vertex_pos_iff hF _).2 ?_)
      ((vertex_pos_iff hF _).2 ?_)
    · rw [hx, hform]
      nlinarith
    · rw [hy, hform]
      nlinarith
  · have h₁ : p.firstAxis ≠ D.dir := fun e => hd (Or.inl e.symm)
    have h₂ : p.secondAxis ≠ D.dir := fun e => hd (Or.inr e.symm)
    have hbar : p.barycenter D.dir = (p.origin : D.Torus) D.dir := by
      simp only [PeriodicLattice.Plaquette.barycenter, Pi.add_apply, PeriodicLattice.pointOnAxis,
        Pi.single_eq_of_ne h₁.symm, Pi.single_eq_of_ne h₂.symm, add_zero]
    have hx : C.centeredRep (p.origin : D.Torus) = C.centeredRep p.barycenter :=
      centeredRep_congr C hbar.symm
    intro z hz
    refine (vertex_pos_iff hF z).2 ?_
    rw [centeredRep_vertex_of_transverse h₁ h₂ hz, hx]
    exact hb₁
end Plaquettes
theorem halfSpaceStructure_holds (h₁ : LevelPartition.Claim)
    (h₂ : PlaquetteNondegeneracy.NondegeneracyStatement)
    (h₃ : LinkReflection.LinkReflectionProperties)
    (h₄ : PeriodicLattice.EdgesPositiveWithEndpointsAtVertices) : HalfSpaceStructure := by
  intro D C
  obtain ⟨⟨-, -, hF⟩, -⟩ := h₁ D C
  obtain ⟨hA, hDir, -, -, hHol⟩ := h₂ D
  obtain ⟨hT, s, hsθ, hB, -, hP, -⟩ := h₃ D C
  have hs : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing := hA.2.2.1
  have hn : 2 ≤ D.sitesPerSide := hA.2.1
  have hX : ∀ b : D.Edge, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => (hDir.2 b).2
  have hSites := vertexSplitting hs hF hT
  have hθp : ∀ y ∈ C.halfVertices .pos, C.refl y ∈ C.halfVertices .neg := fun y hy => by
    rw [← hSites.2.2.2.2.2.2.1]
    exact ⟨y, hy, rfl⟩
  have hθm : ∀ y ∈ C.halfVertices .neg, C.refl y ∈ C.halfVertices .pos := fun y hy => by
    rw [← hSites.2.2.2.2.2.2.2]
    exact ⟨y, hy, rfl⟩
  refine ⟨hSites, heightStep hs hn C, transversalEdgeProperties hs hn hF hT.1,
    positiveReflectedEdge_bijOn hsθ hB hX hθp hθm, ?_,
    transversalFaceProperties hs hF hn hT.1 hsθ hB hX hHol,
    fun p hp => mem_halfFaces_pos_of_barycenter hs hF hp, s, hsθ, pullbackOnPositiveEdges hsθ hB,
    image_halfFaces hsθ hP hθp hθm⟩
  intro σ p hp b hb
  obtain ⟨b₁, b₂, b₃⟩ := h₄ D.L D.m (D.K : ℕ) p b hb
  exact ⟨b₁, hp _ b₂, hp _ b₃⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.HalfSpaces
end
