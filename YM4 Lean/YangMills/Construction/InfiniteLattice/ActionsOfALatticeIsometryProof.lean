import YangMills.Construction.InfiniteLattice.ActionsOfALatticeIsometry
import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndCopies
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.InfiniteLattice.SymmetryActions
variable {a : ℝ}
def IsAxisStep (i : Fin 4) (D : LatticePoint a) : Prop := D = axisStep a i ∨ D = -axisStep a i
theorem quad_swap (x D E : LatticePoint a) :
    ({x, x + D, x + D + E, x + E} : Set (LatticePoint a)) = {x, x + E, x + E + D, x + D} := by
  have hswap : x + E + D = x + D + E := add_right_comm x E D
  rw [hswap]
  ext y
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem exists_cornerSet_of_lt {i j : Fin 4} (hij : i < j) (x D E : LatticePoint a)
    (hD : IsAxisStep i D) (hE : IsAxisStep j E) :
    ∃ q : ElementaryPlaquette a, q.cornerSet = {x, x + D, x + D + E, x + E} := by
  rcases hD with rfl | rfl <;> rcases hE with rfl | rfl
  · exact ⟨⟨x, i, j, hij⟩, rfl⟩
  · refine ⟨⟨x + -axisStep a j, i, j, hij⟩, ?_⟩
    have k₁ : x + -axisStep a j + axisStep a i + axisStep a j = x + axisStep a i := by abel
    have k₂ : x + -axisStep a j + axisStep a j = x := by abel
    have k₃ : x + -axisStep a j + axisStep a i = x + axisStep a i + -axisStep a j := by abel
    change ({x + -axisStep a j, x + -axisStep a j + axisStep a i,
      x + -axisStep a j + axisStep a i + axisStep a j,
      x + -axisStep a j + axisStep a j} : Set (LatticePoint a)) = _
    rw [k₁, k₃, k₂]
    ext y
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  · refine ⟨⟨x + -axisStep a i, i, j, hij⟩, ?_⟩
    have k₁ : x + -axisStep a i + axisStep a i + axisStep a j = x + axisStep a j := by abel
    have k₂ : x + -axisStep a i + axisStep a i = x := by abel
    change ({x + -axisStep a i, x + -axisStep a i + axisStep a i,
      x + -axisStep a i + axisStep a i + axisStep a j,
      x + -axisStep a i + axisStep a j} : Set (LatticePoint a)) = _
    rw [k₁, k₂]
    ext y
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  · refine ⟨⟨x + -axisStep a i + -axisStep a j, i, j, hij⟩, ?_⟩
    have k₁ : x + -axisStep a i + -axisStep a j + axisStep a i + axisStep a j = x := by abel
    have k₂ : x + -axisStep a i + -axisStep a j + axisStep a i = x + -axisStep a j := by abel
    have k₃ : x + -axisStep a i + -axisStep a j + axisStep a j = x + -axisStep a i := by abel
    change ({x + -axisStep a i + -axisStep a j, x + -axisStep a i + -axisStep a j + axisStep a i,
      x + -axisStep a i + -axisStep a j + axisStep a i + axisStep a j,
      x + -axisStep a i + -axisStep a j + axisStep a j} : Set (LatticePoint a)) = _
    rw [k₁, k₂, k₃]
    ext y
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
theorem exists_cornerSet_of_ne {i j : Fin 4} (hij : i ≠ j) (x D E : LatticePoint a)
    (hD : IsAxisStep i D) (hE : IsAxisStep j E) :
    ∃ q : ElementaryPlaquette a, q.cornerSet = {x, x + D, x + D + E, x + E} := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact exists_cornerSet_of_lt hlt x D E hD hE
  · rw [quad_swap]
    exact exists_cornerSet_of_lt hlt x E D hE hD
theorem exists_cornerSet_eq_image (g : LatticeSymmetry a) (hg : g.toFun ∈ affineHyperoctahedralMaps a)
    (p : ElementaryPlaquette a) : ∃ q : ElementaryPlaquette a, q.cornerSet = g.pointMap '' p.cornerSet := by
  obtain ⟨L, hL, v, hfun⟩ := hg
  obtain ⟨σ, ε, hε, hsig⟩ := (mem_hyperoctahedralLinearGroup_iff_signedPerm L).mp hL
  have hdiff : ∀ (y d : LatticePoint a), ∃ D : LatticePoint a, (D : AmbientSpace) = L d ∧
      g.pointMap (y + d) = g.pointMap y + D := by
    intro y d
    refine ⟨g.pointMap (y + d) - g.pointMap y, ?_, by abel⟩
    change g.toFun ((y : AmbientSpace) + d) - g.toFun y = L d
    rw [hfun]
    simp only [latticeMotion, map_add]
    abel
  have hstep : ∀ i : Fin 4, ∀ D : LatticePoint a, (D : AmbientSpace) = L (axisStep a i) →
      IsAxisStep (σ i) D := by
    intro i D hD
    have hunit : ((axisStep a i : LatticePoint a) : AmbientSpace) = a • basisVector i := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp [axisStep, basisVector]
      · simp [axisStep, basisVector, Pi.single_eq_of_ne hk]
    have hD' : (D : AmbientSpace) = (ε i * a) • basisVector (σ i) := by
      rw [hD, hunit, map_smul, hsig, smul_smul, mul_comm]
    rcases hε i with hsgn | hsgn
    · left
      refine Subtype.ext (funext fun k => ?_)
      rw [hD', hsgn]
      by_cases hk : k = σ i
      · subst hk
        simp [axisStep, basisVector]
      · simp [axisStep, basisVector, Pi.single_eq_of_ne hk]
    · right
      refine Subtype.ext (funext fun k => ?_)
      rw [hD', hsgn]
      by_cases hk : k = σ i
      · subst hk
        simp [axisStep, basisVector]
      · simp [axisStep, basisVector, Pi.single_eq_of_ne hk]
  obtain ⟨D, hD, eD⟩ := hdiff p.corner (axisStep a p.lowAxis)
  obtain ⟨E, hE, eE⟩ := hdiff p.corner (axisStep a p.highAxis)
  obtain ⟨E', hE', eE'⟩ := hdiff (p.corner + axisStep a p.lowAxis) (axisStep a p.highAxis)
  have hEE : E' = E := Subtype.ext (hE'.trans hE.symm)
  subst hEE
  have hne : σ p.lowAxis ≠ σ p.highAxis := fun heq => p.lowAxis_lt_highAxis.ne (σ.injective heq)
  obtain ⟨q, hq⟩ := exists_cornerSet_of_ne hne (g.pointMap p.corner) D E' (hstep _ _ hD) (hstep _ _ hE)
  refine ⟨q, ?_⟩
  rw [hq]
  simp only [ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton, eD, eE, eE']
theorem mem_latticeMotions_of_isInverse {g h : LatticeSymmetry a}
    (hg : g.toFun ∈ affineHyperoctahedralMaps a) (hh : h.IsInverse g) :
    h.toFun ∈ affineHyperoctahedralMaps a := by
  obtain ⟨L, hL, v, hfun⟩ := hg
  refine ⟨L⁻¹, hyperoctahedralLinearGroup.inv_mem hL, h.pointMap 0, funext fun x => ?_⟩
  have hx : ∀ y, L (h.toFun y) + (v : AmbientSpace) = y := fun y => by
    have hy := hh.2 y
    rwa [hfun] at hy
  have h₀ := hx 0
  have h₁ := hx x
  have h₂ : L (h.toFun x) = L ((L⁻¹ : AmbientSpace ≃ₗ[ℝ] AmbientSpace) x + h.toFun 0) := by
    have h₃ : L ((L⁻¹ : AmbientSpace ≃ₗ[ℝ] AmbientSpace) x) = x := LinearEquiv.apply_symm_apply L x
    have h₄ : L (h.toFun 0) = -(v : AmbientSpace) := eq_neg_of_add_eq_zero_left h₀
    rw [map_add, h₃, h₄]
    exact eq_add_neg_of_add_eq h₁
  exact L.injective h₂
theorem cornerSet_plaquetteMap {g : LatticeSymmetry a}
    (hg : ∀ p : ElementaryPlaquette a, ∃ q : ElementaryPlaquette a, q.cornerSet = g.pointMap '' p.cornerSet)
    (p : ElementaryPlaquette a) : (g.plaquetteMap p).cornerSet = g.pointMap '' p.cornerSet := by
  classical
  have hdef : g.plaquetteMap p = (hg p).choose := dif_pos (hg p)
  rw [hdef]
  exact (hg p).choose_spec
theorem linkMap_comp (g k : LatticeSymmetry a) (l : Link a) :
    (g.comp k).linkMap l = g.linkMap (k.linkMap l) :=
  rfl
theorem pointMap_pointMap {h g : LatticeSymmetry a} (hinv : Function.LeftInverse h.toFun g.toFun)
    (x : LatticePoint a) : h.pointMap (g.pointMap x) = x :=
  Subtype.ext (hinv x)
theorem linkMap_linkMap {h g : LatticeSymmetry a} (hinv : Function.LeftInverse h.toFun g.toFun)
    (l : Link a) : h.linkMap (g.linkMap l) = l :=
  Link.ext (pointMap_pointMap hinv _) (pointMap_pointMap hinv _)
theorem actsOnLinks (g k : LatticeSymmetry a) (h : LatticeSymmetry a) (hh : h.IsInverse g) :
    g.ActsOnLinks k :=
  ⟨fun _ => rfl, fun _ => rfl, linkMap_comp g k,
    Function.bijective_iff_has_inverse.mpr
      ⟨h.linkMap, linkMap_linkMap hh.1, linkMap_linkMap hh.2⟩⟩
theorem plaquetteMap_plaquetteMap (ha : 0 < a) {h g : LatticeSymmetry a}
    (hh : ∀ p : ElementaryPlaquette a, ∃ q : ElementaryPlaquette a, q.cornerSet = h.pointMap '' p.cornerSet)
    (hg : ∀ p : ElementaryPlaquette a, ∃ q : ElementaryPlaquette a, q.cornerSet = g.pointMap '' p.cornerSet)
    (hinv : Function.LeftInverse h.toFun g.toFun) (p : ElementaryPlaquette a) :
    h.plaquetteMap (g.plaquetteMap p) = p := by
  apply ElementaryPlaquette.cornerSet_injective ha
  rw [cornerSet_plaquetteMap hh, cornerSet_plaquetteMap hg, image_image]
  simp only [pointMap_pointMap hinv, image_id']
theorem actsOnFaces (ha : 0 < a) {g k h : LatticeSymmetry a}
    (hg : g.toFun ∈ affineHyperoctahedralMaps a) (hk : k.toFun ∈ affineHyperoctahedralMaps a)
    (hh : h.IsInverse g) : g.ActsOnFaces k := by
  have eg := exists_cornerSet_eq_image g hg
  have ek := exists_cornerSet_eq_image k hk
  have eh := exists_cornerSet_eq_image h (mem_latticeMotions_of_isInverse hg hh)
  have egk : ∀ p : ElementaryPlaquette a, ∃ q : ElementaryPlaquette a,
      q.cornerSet = (g.comp k).pointMap '' p.cornerSet := by
    intro p
    refine ⟨g.plaquetteMap (k.plaquetteMap p), ?_⟩
    rw [cornerSet_plaquetteMap eg, cornerSet_plaquetteMap ek, image_image]
    rfl
  refine ⟨fun p => ?_, cornerSet_plaquetteMap eg, fun p => ?_, ?_⟩
  · obtain ⟨q, hq⟩ := eg p
    exact ⟨q, hq, fun q' hq' => ElementaryPlaquette.cornerSet_injective ha (hq'.trans hq.symm)⟩
  · apply ElementaryPlaquette.cornerSet_injective ha
    rw [cornerSet_plaquetteMap egk, cornerSet_plaquetteMap eg, cornerSet_plaquetteMap ek, image_image]
    rfl
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨h.plaquetteMap, plaquetteMap_plaquetteMap ha eh eg hh.1,
        plaquetteMap_plaquetteMap ha eg eh hh.2⟩
theorem pullbackField_pullbackField {h g : LatticeSymmetry a}
    (hinv : Function.LeftInverse h.toFun g.toFun) (U : GaugeField a) :
    g.pullbackField (h.pullbackField U) = U :=
  Subtype.ext (funext fun l => congrArg U.1 (linkMap_linkMap hinv l))
theorem actsOnFields (hc : PullbackFieldIsHomeomorph a)
    (g k h : LatticeSymmetry a) (hh : h.IsInverse g) : g.ActsOnFields k :=
  ⟨fun _ _ => rfl, rfl, h, hh,
    { toFun := g.pullbackField
      invFun := h.pullbackField
      left_inv := pullbackField_pullbackField hh.2
      right_inv := pullbackField_pullbackField hh.1
      continuous_toFun := (hc g).2.continuous
      continuous_invFun := (hc h).2.continuous }, rfl, rfl⟩
theorem isBoundedLocal_iff_mem (F : GaugeField a → ℂ) :
    FieldsAtSpacing.IsBoundedLocal F ↔ F ∈ localRegionObservables a univ := by
  simp only [localRegionObservables, mem_iUnion, exists_prop, univ_inter]
  rfl
theorem actsOnBoundedObservables
    (hd : FieldsAtSpacing.continuousFiniteLinkFunctions a =
      {F | FieldsAtSpacing.IsBoundedLocal F ∧ Continuous F})
    (hc : PullbackFieldIsHomeomorph a)
    (hk : ActOnPreservesAlgebraAndRegions a)
    (hm : ActOnComp a)
    (hl : ActOnLinearIsometric a)
    (hloc : ActOnLocalRegions a)
    (hi : LatticeSymmetryInverses a)
    (g k h : LatticeSymmetry a) (hh : h.IsInverse g) : g.ActsOnBoundedObservables k := by
  have into : ∀ (q : LatticeSymmetry a) (F : GaugeField a → ℂ),
      F ∈ FieldsAtSpacing.continuousFiniteLinkFunctions a →
      q.actOn F ∈ FieldsAtSpacing.continuousFiniteLinkFunctions a := by
    intro q F hF
    rw [hd] at hF ⊢
    obtain ⟨hL, hC⟩ := hF
    refine ⟨?_, hC.comp (hc q).2.continuous⟩
    have hmem : q.actOn F ∈ (fun F : GaugeField a → ℂ => q.actOn F) ''
        localRegionObservables a univ := ⟨F, (isBoundedLocal_iff_mem F).mp hL, rfl⟩
    have huniv : q.setImage univ = univ := image_univ_of_surjective (hi q).1.2
    rw [hloc.1 q univ, huniv] at hmem
    exact (isBoundedLocal_iff_mem _).mpr hmem
  refine ⟨fun F hF => ((hk g).1 F F hF hF).1, fun F hF => ((hm g k).2 F hF).symm,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun F hF => ((hl g).2 F hF).2.2.2, (hk g).2, ?_⟩
  refine Subset.antisymm ?_ fun F hF => ?_
  · rintro _ ⟨F, hF, rfl⟩
    exact into g F hF
  · have hO : IsBoundedObservable F := by
      rw [hd] at hF
      exact ((FieldsAtSpacing.isBoundedLocal_iff F).mp hF.1).1
    exact ⟨h.actOn F, into h F hF, (((hi g).2.2 h hh).1 F hO).2.symm⟩
theorem latticeSymmetryActions_holds (h₁ : SymmetryActionOnObservables)
    (h₂ : FieldsAtSpacing.LinkFunctionsStatement) : LatticeSymmetryActions := by
  intro a ha g k hg hk
  have hc : PullbackFieldIsHomeomorph a := (h₁ ⟨a, ha⟩).2.1
  have hpres : ActOnPreservesAlgebraAndRegions a := (h₁ ⟨a, ha⟩).2.2.1
  have hm : ActOnComp a := (h₁ ⟨a, ha⟩).2.2.2.1
  have hl : ActOnLinearIsometric a := (h₁ ⟨a, ha⟩).2.2.2.2.2.1
  have hloc : ActOnLocalRegions a := (h₁ ⟨a, ha⟩).2.2.2.2.2.2.2.2.1
  have hi : LatticeSymmetryInverses a := (h₁ ⟨a, ha⟩).2.2.2.2.2.2.2.2.2.1
  have hd := (h₂ a ha ∅ (empty_subset _)).2.2.2.1.2.2.2
  obtain ⟨h, hh⟩ := (hi g).2.1
  exact ⟨actsOnLinks g k h hh, actsOnFaces ha hg hk hh, actsOnFields hc g k h hh,
    actsOnBoundedObservables hd hc hpres hm hl hloc hi g k h hh⟩
end YangMills.Construction.InfiniteLattice.SymmetryActions
