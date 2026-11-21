import YangMills.Construction.ReflectionPositivity.BondsAndPlaquettesAreNotDegenerate
import YangMills.Construction.ReflectionPositivity.FourSetsOfHeightsAndTheLinkPositionHalfASideOn
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LevelPartition
variable {D : MirrorData}
private theorem mem_proj_image_iff (S : Set ℝ) (y : D.Torus) :
    y ∈ D.proj '' {z | z D.dir ∈ S} ↔ ∃ r ∈ S, D.IsRep (y D.dir) r := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z D.dir, hz, (D.isRep_iff _ _ _).2 ⟨z, rfl, rfl⟩⟩
  · rintro ⟨r, hr, hrep⟩
    obtain ⟨z, hz, rfl⟩ := (D.isRep_iff _ _ _).1 hrep
    exact ⟨z, hr, hz⟩
private theorem coe_add_torusSide (r : ℝ) :
    ((r + D.side : ℝ) : D.CircleCoord) = (r : D.CircleCoord) := by
  change ((r + PeriodicLattice.torusSide D.L D.m : ℝ) :
    AddCircle (PeriodicLattice.torusSide D.L D.m)) = _
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
private theorem proj_image_shift (I J : Set ℝ) (hJ : ∀ r, r ∈ J ↔ r - D.side ∈ I) :
    D.proj '' {z | z D.dir ∈ J} = D.proj '' {z | z D.dir ∈ I} := by
  ext y
  rw [mem_proj_image_iff, mem_proj_image_iff]
  constructor
  · rintro ⟨r, hr, hrep⟩
    refine ⟨r - D.side, (hJ r).1 hr, ?_⟩
    have e := coe_add_torusSide (D := D) (r - D.side)
    rw [sub_add_cancel] at e
    exact e.symm.trans hrep
  · rintro ⟨r, hr, hrep⟩
    refine ⟨r + D.side, (hJ _).2 (by simpa using hr), ?_⟩
    exact (coe_add_torusSide (D := D) r).trans hrep
private theorem eq_centeredRep (C : LinkLevel D) {y : D.Torus} {r : ℝ}
    (hrep : D.IsRep (y D.dir) r) (hr : r ∈ Ico (C.pos - D.side / 2) (C.pos + D.side / 2)) :
    r = C.centeredRep y :=
  (C.existsUnique_isCenteredRep y).unique ⟨hrep, hr⟩ (C.isCenteredRep_centeredRep y)
private theorem proj_image_eq_centeredRepSet (C : LinkLevel D) {I : Set ℝ}
    (hI : I ⊆ Ico (C.pos - D.side / 2) (C.pos + D.side / 2)) :
    D.proj '' {z | z D.dir ∈ I} = C.centeredRepSet I := by
  ext y
  rw [mem_proj_image_iff]
  constructor
  · rintro ⟨r, hr, hrep⟩
    have e := eq_centeredRep C hrep (hI hr)
    change C.centeredRep y ∈ I
    rwa [← e]
  · intro hy
    exact ⟨C.centeredRep y, hy, (C.isCenteredRep_centeredRep y).1⟩
private theorem openSlab_pos_eq (c : ℝ) :
    D.openSlab c .pos = D.proj '' {z | z D.dir ∈ Ioo c (c + D.side / 2)} := by
  unfold MirrorData.openSlab
  congr 1
  ext z
  simp only [SlabSide.toReal, mem_ofPred_eq, mem_Ioo]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
private theorem openSlab_neg_eq (c : ℝ) :
    D.openSlab c .neg = D.proj '' {z | z D.dir ∈ Ioo (c - D.side / 2) c} := by
  unfold MirrorData.openSlab
  congr 1
  ext z
  simp only [SlabSide.toReal, mem_ofPred_eq, mem_Ioo]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
private theorem partsAsLevelSets (C : LinkLevel D) : PartsAsLevelSets C := by
  have hp : 0 < D.side := LinkLevel.side_pos (D := D)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LinkLevel.openSlab, openSlab_pos_eq]
    exact proj_image_eq_centeredRepSet C fun r hr => ⟨by linarith [hr.1], hr.2⟩
  · rw [LinkLevel.openSlab, openSlab_neg_eq]
    exact proj_image_eq_centeredRepSet C fun r hr => ⟨hr.1.le, by linarith [hr.2]⟩
  · refine proj_image_eq_centeredRepSet C (I := {C.pos}) ?_
    rintro r rfl
    exact ⟨by linarith, by linarith⟩
  · have e : D.farPlane C.pos = D.proj '' {z | z D.dir ∈ ({C.pos - D.side / 2} : Set ℝ)} :=
      proj_image_shift _ ({C.pos + D.side / 2} : Set ℝ) fun r => by
        simp only [mem_singleton_iff]
        constructor <;> intro hr <;> linarith
    rw [e]
    refine proj_image_eq_centeredRepSet C ?_
    rintro r rfl
    exact ⟨le_refl _, by linarith⟩
private theorem partsPartition (C : LinkLevel D) : PartsPartition C := by
  have hp : 0 < D.side := LinkLevel.side_pos (D := D)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := partsAsLevelSets C
  let I : Fin 4 → Set ℝ :=
    ![Ioo C.pos (C.pos + D.side / 2), Ioo (C.pos - D.side / 2) C.pos, {C.pos},
      {C.pos - D.side / 2}]
  have key : ∀ i, parts C i = C.centeredRepSet (I i) := by
    intro i
    fin_cases i
    exacts [h₁, h₂, h₃, h₄]
  have hI : ∀ i j, i ≠ j → ∀ r, r ∈ I i → r ∈ I j → False := by
    intro i j hij r hi hj
    fin_cases i <;> fin_cases j <;>
      first
      | exact hij rfl
      | (simp [I] at hi hj
         first
         | linarith [hi.1, hi.2, hj.1, hj.2]
         | linarith [hi.1, hi.2, hj]
         | linarith [hi, hj.1, hj.2]
         | linarith [hi, hj])
  constructor
  · intro i j hij
    change Disjoint (parts C i) (parts C j)
    rw [key, key, Set.disjoint_left]
    intro y hi hj
    exact hI i j hij _ hi hj
  · refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨ha, hb⟩ := (C.isCenteredRep_centeredRep y).2
    rcases lt_trichotomy (C.centeredRep y) C.pos with hlt | heq | hgt
    · rcases ha.eq_or_lt with he | hl
      · exact ⟨3, by rw [key]; exact he.symm⟩
      · exact ⟨1, by rw [key]; exact ⟨hl, hlt⟩⟩
    · exact ⟨2, by rw [key]; exact heq⟩
    · exact ⟨0, by rw [key]; exact ⟨hgt, hb⟩⟩
private theorem proj_add_side_smul (w : Fin 4 → ℝ) :
    D.proj (w + D.side • PeriodicLattice.coordVec D.dir) = D.proj w := by
  funext ν
  by_cases hν : ν = D.dir
  · subst hν
    simpa [MirrorData.proj, TorusMetric.torusProj, PeriodicLattice.coordVec] using
      coe_add_torusSide (D := D) (w D.dir)
  · simp [MirrorData.proj, TorusMetric.torusProj, PeriodicLattice.coordVec,
      Pi.single_eq_of_ne hν]
private theorem reflect_add_half_side (c : ℝ) : D.reflect (c + D.side / 2) = D.reflect c := by
  refine (D.existsUnique_induces c).unique ?_ (D.induces_reflect c)
  have hind := D.induces_reflect (c + D.side / 2)
  funext x
  have hx := congrFun hind x
  simp only [Function.comp_apply] at hx ⊢
  rw [hx, ← proj_add_side_smul (D.reflectVec c x)]
  congr 1
  have e : 2 * (c + D.side / 2) = 2 * c + D.side := by ring
  simp only [MirrorData.reflectVec]
  rw [e, add_smul, add_assoc]
private theorem halfPeriodShift (C : LinkLevel D)
    (hhalf : D.side / 2 = (D.sitesPerSide : ℝ) * D.spacing) : HalfPeriodShift C := by
  have hfar : D.proj '' {z | z D.dir = C.pos + D.side / 2 + D.side / 2} =
      D.proj '' {z | z D.dir = C.pos} :=
    proj_image_shift ({C.pos} : Set ℝ) ({C.pos + D.side / 2 + D.side / 2} : Set ℝ) fun r => by
      simp only [mem_singleton_iff]
      constructor <;> intro hr <;> linarith
  refine ⟨by rw [hhalf], ?_, reflect_add_half_side C.pos, ?_, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := C.isLinkLevel
    refine ⟨n + (D.sitesPerSide : ℤ), ?_⟩
    rw [hhalf, hn]
    push_cast
    ring
  · unfold MirrorData.mirrorSet
    rw [image_union, image_union, hfar, union_comm]
  · rw [openSlab_pos_eq, openSlab_neg_eq]
    refine proj_image_shift _ _ fun r => ?_
    simp only [mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · rw [openSlab_neg_eq, openSlab_pos_eq, add_sub_cancel_right]
theorem claim_of_nondegeneracy (hnd : PlaquetteNondegeneracy.NondegeneracyStatement) :
    Claim := by
  intro D C
  obtain ⟨-, -, hhalf, -⟩ := (hnd D).1
  exact ⟨⟨fun y r hy hr => eq_centeredRep C hy ⟨hr.1.le, hr.2⟩, partsPartition C,
    partsAsLevelSets C⟩, halfPeriodShift C hhalf⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LevelPartition
end
