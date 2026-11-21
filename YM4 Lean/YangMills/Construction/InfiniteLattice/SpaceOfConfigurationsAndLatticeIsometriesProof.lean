import YangMills.Construction.InfiniteLattice.ActionsOfALatticeIsometryProof
import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheoryProof
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAsMotionsAndTheirActionProof
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfFourSpaceAsBijections
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.InfiniteLattice.FieldSymmetries
variable {a : ℝ}
def idSymmetry (a : ℝ) : LatticeSymmetry a where
  toFun := id
  preservesDist _ _ := rfl
  image_eq := image_id _
def invSymmetry (g : LatticeSymmetry a) : LatticeSymmetry a where
  toFun := g.toEquivAmbient.symm
  preservesDist x y := by
    have hd := g.preservesDist (g.toEquivAmbient.symm x) (g.toEquivAmbient.symm y)
    have hap : ∀ z, g.toFun (g.toEquivAmbient.symm z) = z :=
      fun z => g.toEquivAmbient.apply_symm_apply z
    rw [hap, hap] at hd
    exact hd.symm
  image_eq := by
    have hap : ∀ z, g.toEquivAmbient.symm (g.toFun z) = z :=
      fun z => g.toEquivAmbient.symm_apply_apply z
    conv_lhs => rw [← g.image_eq]
    rw [image_image]
    simp [hap]
theorem toFun_invSymmetry (g : LatticeSymmetry a) (x : AmbientSpace) :
    g.toFun ((invSymmetry g).toFun x) = x :=
  g.toEquivAmbient.apply_symm_apply x
theorem invSymmetry_toFun (g : LatticeSymmetry a) (x : AmbientSpace) :
    (invSymmetry g).toFun (g.toFun x) = x :=
  g.toEquivAmbient.symm_apply_apply x
theorem pointMap_invSymmetry (g : LatticeSymmetry a) (x : LatticePoint a) :
    g.pointMap ((invSymmetry g).pointMap x) = x :=
  Subtype.ext (toFun_invSymmetry g x)
theorem invSymmetry_pointMap (g : LatticeSymmetry a) (x : LatticePoint a) :
    (invSymmetry g).pointMap (g.pointMap x) = x :=
  Subtype.ext (invSymmetry_toFun g x)
theorem pointMap_injective (g : LatticeSymmetry a) : Function.Injective g.pointMap :=
  Function.LeftInverse.injective (invSymmetry_pointMap g)
theorem linkMap_invSymmetry (g : LatticeSymmetry a) (l : Link a) :
    g.linkMap ((invSymmetry g).linkMap l) = l :=
  Link.ext (pointMap_invSymmetry g _) (pointMap_invSymmetry g _)
theorem invSymmetry_linkMap (g : LatticeSymmetry a) (l : Link a) :
    (invSymmetry g).linkMap (g.linkMap l) = l :=
  Link.ext (invSymmetry_pointMap g _) (invSymmetry_pointMap g _)
theorem linkMap_opposite (g : LatticeSymmetry a) (l : Link a) :
    g.linkMap l.opposite = (g.linkMap l).opposite :=
  Link.ext rfl rfl
theorem linkMap_bijective (g : LatticeSymmetry a) : Function.Bijective g.linkMap :=
  ⟨Function.LeftInverse.injective (invSymmetry_linkMap g),
    Function.RightInverse.surjective (linkMap_invSymmetry g)⟩
theorem pullbackField_comp (g g' : LatticeSymmetry a) :
    (g.comp g').pullbackField = g'.pullbackField ∘ g.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetriesAsMotions.pullbackField_comp <;> assumption
theorem pullbackField_invSymmetry (g : LatticeSymmetry a) (U : GaugeField a) :
    (invSymmetry g).pullbackField (g.pullbackField U) = U := by
  refine Subtype.ext (funext fun l => ?_)
  change U.1 (g.linkMap ((invSymmetry g).linkMap l)) = U.1 l
  rw [linkMap_invSymmetry]
theorem invSymmetry_pullbackField (g : LatticeSymmetry a) (U : GaugeField a) :
    g.pullbackField ((invSymmetry g).pullbackField U) = U := by
  refine Subtype.ext (funext fun l => ?_)
  change U.1 ((invSymmetry g).linkMap (g.linkMap l)) = U.1 l
  rw [invSymmetry_linkMap]
def pullbackHomeomorph (g : LatticeSymmetry a) : GaugeField a ≃ₜ GaugeField a where
  toFun := g.pullbackField
  invFun := (invSymmetry g).pullbackField
  left_inv := pullbackField_invSymmetry g
  right_inv := invSymmetry_pullbackField g
  continuous_toFun := g.continuous_pullbackField
  continuous_invFun := (invSymmetry g).continuous_pullbackField
theorem pullbackField_surjective (g : LatticeSymmetry a) :
    Function.Surjective g.pullbackField :=
  (pullbackHomeomorph g).surjective
theorem supNorm_actOn (g : LatticeSymmetry a) (F : GaugeField a → ℂ) :
    observableSupNorm (g.actOn F) = observableSupNorm F :=
  (pullbackField_surjective g).iSup_comp fun U => ‖F U‖
theorem actOn_invSymmetry (g : LatticeSymmetry a) (F : GaugeField a → ℂ) :
    g.actOn ((invSymmetry g).actOn F) = F :=
  funext fun U => congrArg F (pullbackField_invSymmetry g U)
theorem linkMap_mem_linksWithin (g : LatticeSymmetry a) {S : Set AmbientSpace} {l : Link a}
    (hl : l ∈ (linksWithin S : Set (Link a))) :
    g.linkMap l ∈ (linksWithin (g.imageSet S) : Set (Link a)) :=
  ⟨mem_image_of_mem _ hl.1, mem_image_of_mem _ hl.2⟩
theorem measurable_pullbackField (g : LatticeSymmetry a) (S : Set AmbientSpace) :
    @Measurable _ _ (regionSigma (a := a) (g.imageSet S)) (regionSigma (a := a) S)
      g.pullbackField := by
  refine @measurable_iff_comap_le _ _ (regionSigma (a := a) (g.imageSet S))
    (regionSigma (a := a) S) _ |>.2 ?_
  simp only [regionSigma, linkSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun l hl => ?_
  exact le_iSup₂_of_le (g.linkMap l) (linkMap_mem_linksWithin g hl) le_rfl
theorem actOn_mem (g : LatticeSymmetry a) {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : F ∈ regionObservables a S) : g.actOn F ∈ regionObservables a (g.imageSet S) :=
  ⟨hF.1.actOn g, fun _ ht => measurable_pullbackField g S (hF.2 ht)⟩
theorem image_actOn (g : LatticeSymmetry a) (S : Set AmbientSpace) :
    (fun F => g.actOn F) '' regionObservables a S = regionObservables a (g.imageSet S) := by
  refine Subset.antisymm ?_ fun F hF => ?_
  · rintro _ ⟨F, hF, rfl⟩
    exact actOn_mem g hF
  · refine ⟨(invSymmetry g).actOn F, ?_, actOn_invSymmetry g F⟩
    have hm := actOn_mem (invSymmetry g) hF
    have e : (invSymmetry g).imageSet (g.imageSet S) = S := by
      simp only [LatticeSymmetry.imageSet, image_image, invSymmetry_toFun, image_id']
    rwa [e] at hm
theorem countable_link (a : ℝ) : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem compactSpace_gaugeField : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem secondCountable_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem metrizableSpace_gaugeField : TopologicalSpace.MetrizableSpace (GaugeField a) := by apply _root_.YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs.metrizableSpace_gaugeField <;> assumption
theorem borel_eq_linkSigma :
    (inferInstance : MeasurableSpace (GaugeField a)) = linkSigma (univ : Set (Link a)) := by
  have := countable_link a
  have := secondCountable_specialUnitary
  have hpi : borel (Link a → Matrices.ComplexMatrix2.specialUnitary) = MeasurableSpace.pi :=
    (BorelSpace.measurable_eq (α := Link a → Matrices.ComplexMatrix2.specialUnitary)).symm
  have hcomap : (inferInstance : MeasurableSpace (GaugeField a)) =
      MeasurableSpace.comap
        (fun U : GaugeField a => (U.1 : Link a → Matrices.ComplexMatrix2.specialUnitary))
        MeasurableSpace.pi := by
    rw [← hpi]
    exact borel_comap
  rw [hcomap]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, linkSigma,
    mem_univ, iSup_pos]
  rfl
theorem euclidNormVec_of_signedPerm {τ : Equiv.Perm (Fin 4)} {ε : Fin 4 → ℝ}
    (hε : ∀ μ, ε μ = 1 ∨ ε μ = -1) {x y : AmbientSpace} (h : ∀ μ, y μ = ε μ * x (τ μ)) :
    TorusMetric.euclidNormVec y = TorusMetric.euclidNormVec x := by
  have hsq : ∀ μ, y μ ^ 2 = x (τ μ) ^ 2 := fun μ => by
    rw [h]
    rcases hε μ with e | e <;> simp [e]
  rw [TorusMetric.euclidNormVec, TorusMetric.euclidNormVec,
    Finset.sum_congr rfl fun μ _ => hsq μ]
  exact congrArg Real.sqrt (Equiv.sum_comp τ fun ν => x ν ^ 2)
theorem isLatticeLinearIsometry_of_signedPerm (R : AmbientSpace →ₗ[ℝ] AmbientSpace)
    (τ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℝ)
    (hε : ∀ μ, ε μ = 1 ∨ ε μ = -1) (h : ∀ x μ, R x μ = ε μ * x (τ μ)) :
    IsLatticeLinearIsometry a R := by
  have hint : ∀ μ, ∃ k : ℤ, ε μ = k := fun μ => by
    rcases hε μ with e | e
    · exact ⟨1, by simp [e]⟩
    · exact ⟨-1, by simp [e]⟩
  choose k hk using hint
  have hsq : ∀ μ, ε μ * ε μ = 1 := fun μ => by
    rcases hε μ with e | e <;> simp [e]
  refine ⟨fun x y => ?_, ?_⟩
  · rw [← map_sub]
    exact euclidNormVec_of_signedPerm hε (h _)
  · ext y
    constructor
    · rintro ⟨x, ⟨n, hn⟩, rfl⟩
      refine (⟨fun μ => k μ * n (τ μ), fun μ => ?_⟩ : R x ∈ latticeSubgroup a)
      rw [h, hn, hk]
      push_cast
      ring
    · rintro ⟨m, hm⟩
      refine ⟨fun ν => ε (τ.symm ν) * y (τ.symm ν),
        (⟨fun ν => k (τ.symm ν) * m (τ.symm ν), fun ν => ?_⟩ : _ ∈ latticeSubgroup a), ?_⟩
      · rw [hm, hk]
        push_cast
        ring
      · funext μ
        rw [h]
        simp only [Equiv.symm_apply_apply]
        rw [← mul_assoc, hsq, one_mul]
def ofLinear (R : AmbientSpace →ₗ[ℝ] AmbientSpace) (h : IsLatticeLinearIsometry a R) :
    LatticeSymmetry a :=
  ⟨R, h.1, h.2⟩
theorem exists_linear_eq_of_isLatticeLinearIsometry (ha : a ≠ 0)
    (R : AmbientSpace →ₗ[ℝ] AmbientSpace) (h : IsLatticeLinearIsometry a R) :
    ∃ w ∈ hyperoctahedralLinearGroup, ⇑w = ⇑R := by
  obtain ⟨w, hw, v, hv⟩ := (ofLinear R h).toFun_mem_latticeMotions ha
  have hfun : ∀ x, R x = w x + (v : AmbientSpace) := fun x => congrFun hv x
  have hv0 : (v : AmbientSpace) = 0 := by
    have h0 := hfun 0
    simpa using h0.symm
  exact ⟨w, hw, funext fun x => by rw [hfun, hv0, add_zero]⟩
theorem toMatrix_mem_of_exists_linear {R : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (h : ∃ w ∈ hyperoctahedralLinearGroup, ⇑w = ⇑R) :
    LinearMap.toMatrix' R ∈ PeriodicLattice.signedPermMatrices := by
  obtain ⟨w, hw, e⟩ := h
  obtain ⟨π, s, hs⟩ := (mem_hyperoctahedralLinearGroup_iff w).1 hw
  refine ⟨π, fun μ => ((s μ : ℤ) : ℝ), fun μ => ?_, fun x μ => ?_⟩
  · rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
  · rw [LinearMap.toMatrix'_mulVec, ← e]
    exact hs x μ
theorem isLatticeLinearIsometry_of_toMatrix {R : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (h : LinearMap.toMatrix' R ∈ PeriodicLattice.signedPermMatrices) :
    IsLatticeLinearIsometry a R := by
  obtain ⟨τ, ε, hε, he⟩ := h
  exact isLatticeLinearIsometry_of_signedPerm R τ ε hε fun x μ => by
    rw [← he x μ, LinearMap.toMatrix'_mulVec]
theorem isLatticeLinearIsometry_iff_toMatrix (ha : a ≠ 0) (R : AmbientSpace →ₗ[ℝ] AmbientSpace) :
    IsLatticeLinearIsometry a R ↔
      LinearMap.toMatrix' R ∈ PeriodicLattice.signedPermMatrices :=
  ⟨fun h => toMatrix_mem_of_exists_linear (exists_linear_eq_of_isLatticeLinearIsometry ha R h),
    isLatticeLinearIsometry_of_toMatrix⟩
theorem isLatticeLinearIsometry_iff_exists (ha : a ≠ 0) (R : AmbientSpace →ₗ[ℝ] AmbientSpace) :
    IsLatticeLinearIsometry a R ↔ ∃ w ∈ hyperoctahedralLinearGroup, ⇑w = ⇑R :=
  ⟨exists_linear_eq_of_isLatticeLinearIsometry ha R,
    fun h => isLatticeLinearIsometry_of_toMatrix (toMatrix_mem_of_exists_linear h)⟩
theorem exists_symmetry_iff_mem_latticeMotions (ha : a ≠ 0) (f : AmbientSpace → AmbientSpace) :
    (∃ g : LatticeSymmetry a, g.toFun = f) ↔ f ∈ affineHyperoctahedralMaps a := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.toFun_mem_latticeMotions ha
  · rintro ⟨w, hw, v, rfl⟩
    have hR : IsLatticeLinearIsometry a w.toLinearMap :=
      (isLatticeLinearIsometry_iff_exists ha _).2 ⟨w, hw, rfl⟩
    exact ⟨(shift v).comp (ofLinear _ hR), (latticeMotion_eq_comp w v).symm⟩
def symmetryGroup (a : ℝ) : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := {σ | ∃ g : LatticeSymmetry a, g.toFun = ⇑σ}
  mul_mem' := by
    rintro σ σ' ⟨g, hg⟩ ⟨g', hg'⟩
    refine ⟨g.comp g', ?_⟩
    rw [Equiv.Perm.coe_mul, ← hg, ← hg']
    rfl
  one_mem' := ⟨idSymmetry a, rfl⟩
  inv_mem' := by
    rintro σ ⟨g, hg⟩
    refine ⟨invSymmetry g, funext fun x => ?_⟩
    rw [Equiv.Perm.eq_inv_iff_eq, ← hg]
    exact toFun_invSymmetry g x
theorem exists_symmetry_iff_mem_symmetryGroup (f : AmbientSpace → AmbientSpace) :
    (∃ g : LatticeSymmetry a, g.toFun = f) ↔ ∃ σ ∈ symmetryGroup a, ⇑σ = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.toEquivAmbient, ⟨g, rfl⟩, rfl⟩
  · rintro ⟨σ, ⟨g, hg⟩, rfl⟩
    exact ⟨g, hg⟩
theorem euclidNormVec_neg (v : AmbientSpace) :
    TorusMetric.euclidNormVec (-v) = TorusMetric.euclidNormVec v := by
  simp [TorusMetric.euclidNormVec]
theorem axisStep_ne_neg (ha : 0 < a) (μ ν : Fin 4) : axisStep a μ ≠ -axisStep a ν := by
  intro h
  have hc : (Pi.single μ a : AmbientSpace) μ = -(Pi.single ν a : AmbientSpace) μ :=
    congrFun (congrArg Subtype.val h) μ
  rw [Pi.single_eq_same] at hc
  by_cases e : μ = ν
  · subst e
    rw [Pi.single_eq_same] at hc
    linarith
  · rw [Pi.single_eq_of_ne e] at hc
    linarith
theorem axisStep_ne_zero (ha : 0 < a) (μ : Fin 4) : axisStep a μ ≠ 0 := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.axisStep_ne_zero <;> assumption
theorem axisStep_ne_axisStep (ha : 0 < a) {μ ν : Fin 4} (e : μ ≠ ν) :
    axisStep a μ ≠ axisStep a ν := by
  intro h
  have hc : (Pi.single μ a : AmbientSpace) μ = (Pi.single ν a : AmbientSpace) μ :=
    congrFun (congrArg Subtype.val h) μ
  rw [Pi.single_eq_same, Pi.single_eq_of_ne e] at hc
  exact ha.ne' hc
theorem exists_link_iff (ha : 0 < a) (x y : LatticePoint a) :
    (∃ l : Link a, l.initial = x ∧ l.terminal = y) ↔
      TorusMetric.euclidNormVec ((x : AmbientSpace) - y) = a := by
  constructor
  · rintro ⟨l, rfl, rfl⟩
    obtain ⟨μ, h | h⟩ := l.isAdjacent
    · have h' : (l.terminal : AmbientSpace) - (l.initial : AmbientSpace) =
          (Pi.single μ a : AmbientSpace) :=
        congrArg Subtype.val h
      rw [← neg_sub, euclidNormVec_neg, h', euclidNormVec_single, abs_of_pos ha]
    · have h' : (l.terminal : AmbientSpace) - (l.initial : AmbientSpace) =
          -(Pi.single μ a : AmbientSpace) :=
        congrArg Subtype.val h
      rw [← neg_sub, h', neg_neg, euclidNormVec_single, abs_of_pos ha]
  · intro h
    have hd : TorusMetric.euclidNormVec ((y : AmbientSpace) - x) = |a| := by
      rw [← neg_sub, euclidNormVec_neg, h, abs_of_pos ha]
    exact ⟨⟨x, y, isAdjacent_of_euclidNormVec x y hd⟩, rfl, rfl⟩
theorem xor_isPositivelyOriented (ha : 0 < a) (l : Link a) :
    Xor l.IsPositivelyOriented l.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
def quadSet (z u u' : LatticePoint a) : Set (LatticePoint a) := {z, z + u, z + u + u', z + u'}
theorem quadSet_comm (z u u' : LatticePoint a) : quadSet z u u' = quadSet z u' u := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetryActions.quad_swap <;> assumption
theorem quadSet_neg (z u u' : LatticePoint a) : quadSet z (-u) u' = quadSet (z - u) u u' := by
  have e₁ : z - u + u = z := sub_add_cancel _ _
  have e₂ : z + -u = z - u := (sub_eq_add_neg _ _).symm
  ext y
  simp only [quadSet, mem_insert_iff, mem_singleton_iff, e₁, e₂]
  tauto
theorem exists_plaquette_of_axisSteps (z : LatticePoint a) {ρ ρ' : Fin 4} (h : ρ ≠ ρ') :
    ∃ p : ElementaryPlaquette a, p.cornerSet = quadSet z (axisStep a ρ) (axisStep a ρ') := by
  rcases lt_or_gt_of_ne h with h | h
  · exact ⟨⟨z, ρ, ρ', h⟩, rfl⟩
  · exact ⟨⟨z, ρ', ρ, h⟩, quadSet_comm _ _ _⟩
theorem exists_plaquette_iff (P : Set (LatticePoint a)) :
    (∃ p : ElementaryPlaquette a, p.cornerSet = P) ↔
      ∃ (z u u' : LatticePoint a) (ρ ρ' : Fin 4), ρ ≠ ρ' ∧
        (u = axisStep a ρ ∨ u = -axisStep a ρ) ∧ (u' = axisStep a ρ' ∨ u' = -axisStep a ρ') ∧
        P = {z, z + u, z + u + u', z + u'} := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.corner, axisStep a p.lowAxis, axisStep a p.highAxis, p.lowAxis, p.highAxis,
      p.lowAxis_lt_highAxis.ne, Or.inl rfl, Or.inl rfl, rfl⟩
  · rintro ⟨z, u, u', ρ, ρ', h, rfl | rfl, rfl | rfl, rfl⟩
    · exact exists_plaquette_of_axisSteps z h
    · change ∃ p : ElementaryPlaquette a, p.cornerSet = quadSet z (axisStep a ρ) (-axisStep a ρ')
      rw [quadSet_comm, quadSet_neg, quadSet_comm]
      exact exists_plaquette_of_axisSteps _ h
    · change ∃ p : ElementaryPlaquette a, p.cornerSet = quadSet z (-axisStep a ρ) (axisStep a ρ')
      rw [quadSet_neg]
      exact exists_plaquette_of_axisSteps _ h
    · change ∃ p : ElementaryPlaquette a, p.cornerSet = quadSet z (-axisStep a ρ) (-axisStep a ρ')
      rw [quadSet_neg, quadSet_comm, quadSet_neg, quadSet_comm]
      exact exists_plaquette_of_axisSteps _ h
theorem ncard_cornerSet (ha : 0 < a) (p : ElementaryPlaquette a) : p.cornerSet.ncard = 4 := by
  have hne := p.lowAxis_lt_highAxis.ne
  have hs := axisStep_ne_zero ha p.lowAxis
  have hs' := axisStep_ne_zero ha p.highAxis
  have hd := axisStep_ne_axisStep ha hne
  have hn : axisStep a p.lowAxis + axisStep a p.highAxis ≠ 0 := fun h =>
    axisStep_ne_neg ha p.lowAxis p.highAxis (eq_neg_of_add_eq_zero_left h)
  have hc : p.cornerSet = {p.corner, p.corner + axisStep a p.lowAxis,
      p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
      p.corner + axisStep a p.highAxis} := rfl
  rw [hc]
  generalize axisStep a p.lowAxis = s at *
  generalize axisStep a p.highAxis = s' at *
  have h₁ : p.corner ≠ p.corner + s := by simpa using hs
  have h₂ : p.corner ≠ p.corner + s + s' := by
    rw [add_assoc]
    simpa using hn
  have h₃ : p.corner ≠ p.corner + s' := by simpa using hs'
  have h₄ : p.corner + s ≠ p.corner + s + s' := by simpa using hs'
  have h₅ : p.corner + s ≠ p.corner + s' := by simpa using hd
  have h₆ : p.corner + s + s' ≠ p.corner + s' := by
    rw [add_right_comm]
    simpa using hs
  rw [ncard_insert_of_notMem (by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨h₁, h₂, h₃⟩),
    ncard_insert_of_notMem (by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨h₄, h₅⟩),
    ncard_pair h₆]
theorem apply_single_of_signedPerm {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    {π : Equiv.Perm (Fin 4)} {s : Fin 4 → ℤˣ}
    (hs : ∀ x μ, w x μ = ((s μ : ℤ) : ℝ) * x (π μ)) (ρ : Fin 4) (t : ℝ) :
    w (Pi.single ρ t) = Pi.single (π.symm ρ) (((s (π.symm ρ) : ℤ) : ℝ) * t) := by
  funext μ
  rw [hs]
  by_cases e : μ = π.symm ρ
  · subst e
    simp
  · have e' : π μ ≠ ρ := fun h => e (by rw [← h]; simp)
    rw [Pi.single_eq_of_ne e', Pi.single_eq_of_ne e, mul_zero]
theorem exists_axisStep_image (ha : a ≠ 0) (g : LatticeSymmetry a) :
    ∃ (σ : Fin 4 → Fin 4) (D : Fin 4 → LatticePoint a), Function.Injective σ ∧
      (∀ ρ, D ρ = axisStep a (σ ρ) ∨ D ρ = -axisStep a (σ ρ)) ∧
      ∀ z ρ, g.pointMap (z + axisStep a ρ) = g.pointMap z + D ρ := by
  obtain ⟨w, hw, v, hv⟩ := g.toFun_mem_latticeMotions ha
  obtain ⟨π, s, hs⟩ := (mem_hyperoctahedralLinearGroup_iff w).1 hw
  have hfun : ∀ x, g.toFun x = w x + (v : AmbientSpace) := fun x => congrFun hv x
  have hD : ∀ ρ, ∃ D : LatticePoint a,
      (D = axisStep a (π.symm ρ) ∨ D = -axisStep a (π.symm ρ)) ∧
      (D : AmbientSpace) = w (Pi.single ρ a) := by
    intro ρ
    rcases Int.units_eq_one_or (s (π.symm ρ)) with e | e
    · refine ⟨axisStep a (π.symm ρ), Or.inl rfl, ?_⟩
      rw [apply_single_of_signedPerm hs, e]
      simp [axisStep]
    · refine ⟨-axisStep a (π.symm ρ), Or.inr rfl, ?_⟩
      rw [apply_single_of_signedPerm hs, e]
      simp [axisStep, Pi.single_neg]
  choose D hD₁ hD₂ using hD
  refine ⟨π.symm, D, π.symm.injective, hD₁, fun z ρ => Subtype.ext ?_⟩
  change g.toFun ((z : AmbientSpace) + Pi.single ρ a) = g.toFun z + (D ρ : AmbientSpace)
  rw [hfun, hfun, map_add, hD₂]
  abel
theorem exists_plaquette_image (ha : 0 < a) (g : LatticeSymmetry a) (p : ElementaryPlaquette a) :
    ∃ p' : ElementaryPlaquette a, p'.cornerSet = g.pointMap '' p.cornerSet := by
  obtain ⟨σ, D, hσ, hD, h⟩ := exists_axisStep_image ha.ne' g
  refine (exists_plaquette_iff _).2 ⟨g.pointMap p.corner, D p.lowAxis, D p.highAxis,
    σ p.lowAxis, σ p.highAxis, hσ.ne p.lowAxis_lt_highAxis.ne, hD _, hD _, ?_⟩
  change g.pointMap '' {p.corner, p.corner + axisStep a p.lowAxis,
    p.corner + axisStep a p.lowAxis + axisStep a p.highAxis, p.corner + axisStep a p.highAxis} = _
  simp only [image_insert_eq, image_singleton, h]
theorem cornerSet_plaquetteMap (ha : 0 < a) (g : LatticeSymmetry a) (p : ElementaryPlaquette a) :
    (g.plaquetteMap p).cornerSet = g.pointMap '' p.cornerSet := by
  have h := exists_plaquette_image ha g p
  unfold LatticeSymmetry.plaquetteMap
  rw [dif_pos h]
  exact h.choose_spec
theorem plaquetteMap_bijective (ha : 0 < a) (g : LatticeSymmetry a) :
    Function.Bijective g.plaquetteMap := by
  constructor
  · intro p q h
    refine ElementaryPlaquette.cornerSet_injective ha ?_
    have hc := congrArg ElementaryPlaquette.cornerSet h
    rw [cornerSet_plaquetteMap ha, cornerSet_plaquetteMap ha] at hc
    exact (pointMap_injective g).image_injective hc
  · intro q
    refine ⟨(invSymmetry g).plaquetteMap q, ElementaryPlaquette.cornerSet_injective ha ?_⟩
    rw [cornerSet_plaquetteMap ha, cornerSet_plaquetteMap ha, image_image]
    simp [pointMap_invSymmetry]
theorem symmetryProperties : FieldSpace.SymmetryProperties := by
  intro a ha
  refine ⟨⟨compactSpace_gaugeField, metrizableSpace_gaugeField, borel_eq_linkSigma⟩,
    fun g g' => ⟨(pullbackHomeomorph g).isHomeomorph, pullbackField_comp g g',
      fun F F' hF _ => ⟨hF.actOn g, supNorm_actOn g F, ?_, rfl, rfl, ?_⟩,
      image_actOn g⟩,
    fun v S => image_actOn (shift v) S,
    fun R => ⟨isLatticeLinearIsometry_iff_toMatrix ha.ne' R,
      isLatticeLinearIsometry_iff_exists ha.ne' R⟩,
    exists_symmetry_iff_mem_latticeMotions ha.ne',
    ⟨symmetryGroup a, exists_symmetry_iff_mem_symmetryGroup⟩,
    exists_link_iff ha, xor_isPositivelyOriented ha,
    fun g => ⟨linkMap_bijective g, linkMap_opposite g⟩,
    exists_plaquette_iff, ncard_cornerSet ha, ElementaryPlaquette.cornerSet_injective ha,
    fun g => ⟨cornerSet_plaquetteMap ha g, plaquetteMap_bijective ha g⟩⟩
  · exact fun hc => hc.comp g.continuous_pullbackField
  · exact funext fun U => congrArg F (congrFun (pullbackField_comp g g') U)
end YangMills.Construction.InfiniteLattice.FieldSymmetries
