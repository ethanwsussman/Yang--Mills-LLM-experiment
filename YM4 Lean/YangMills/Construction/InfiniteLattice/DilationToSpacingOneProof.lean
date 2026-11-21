import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.InfiniteLattice.ReflectionsLatticeMirrorsAndTuplesOnTheTwoSidesProof
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.InfiniteLattice.CopyOfAStateOnADilatedLattice
import YangMills.Construction.InfiniteLattice.DilationToSpacingOne
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.EquilibriumClassIsTheSetOfGibbsStates
import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.Lattice.ConfigurationsAreAProduct
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice YangMills.Construction.NormalFamilies
open scoped Matrix Pointwise
noncomputable section
namespace YangMills.Construction.UnitSpacing
variable {a : ℝ}
local instance specialUnitary_secondCountable :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  haveI : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
theorem pointRescale_pointScale (ha : 0 < a) (x : LatticePoint 1) :
    pointRescale ha (pointScale a (mul_one a).symm x) = x :=
  Subtype.ext (by
    change a⁻¹ • a • (x : AmbientSpace) = x
    rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul])
theorem pointScale_pointRescale (ha : 0 < a) (x : LatticePoint a) :
    pointScale a (mul_one a).symm (pointRescale ha x) = x :=
  Subtype.ext (by
    change a • a⁻¹ • (x : AmbientSpace) = x
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul])
def pointAddEquiv (ha : 0 < a) : LatticePoint a ≃+ LatticePoint 1 where
  toFun := pointRescale ha
  invFun := pointScale a (mul_one a).symm
  left_inv := pointScale_pointRescale ha
  right_inv := pointRescale_pointScale ha
  map_add' := (pointRescale ha).map_add
theorem pointRescale_axisStep (ha : 0 < a) (μ : Fin 4) :
    pointRescale ha (axisStep a μ) = axisStep 1 μ :=
  pointScale_axisStep (one_eq_inv_mul_spacing ha) μ
def linkEquiv (ha : 0 < a) : Link a ≃ Link 1 where
  toFun := rescaledLink ha
  invFun := linkScale a (mul_one a).symm
  left_inv _ := InfiniteLattice.Link.ext (pointScale_pointRescale ha _) (pointScale_pointRescale ha _)
  right_inv _ := InfiniteLattice.Link.ext (pointRescale_pointScale ha _) (pointRescale_pointScale ha _)
theorem rescaledLink_isPositivelyOriented_iff (ha : 0 < a) (b : Link a) :
    (rescaledLink ha b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  refine ⟨?_, rescaledLink_isPositivelyOriented ha⟩
  rintro ⟨μ, h⟩
  refine ⟨μ, (pointAddEquiv ha).injective ?_⟩
  change pointRescale ha (b.terminal - b.initial) = pointRescale ha (axisStep a μ)
  rw [map_sub, pointRescale_axisStep]
  exact h
def faceEquiv (ha : 0 < a) : ElementaryPlaquette a ≃ ElementaryPlaquette 1 where
  toFun := rescaledPlaquette ha
  invFun := plaquetteScale a (mul_one a).symm
  left_inv p := InfiniteLattice.ElementaryPlaquette.ext (pointScale_pointRescale ha p.corner) rfl rfl
  right_inv p := InfiniteLattice.ElementaryPlaquette.ext (pointRescale_pointScale ha p.corner) rfl rfl
theorem rescaledLink_forwardFrom (ha : 0 < a) (x : LatticePoint a) (μ : Fin 4) :
    rescaledLink ha (Link.forwardFrom x μ) = Link.forwardFrom (pointRescale ha x) μ :=
  InfiniteLattice.Link.ext rfl (by
    change pointRescale ha (x + axisStep a μ) = pointRescale ha x + axisStep 1 μ
    rw [map_add, pointRescale_axisStep])
theorem edges_rescaledPlaquette (ha : 0 < a) (p : ElementaryPlaquette a) :
    (rescaledPlaquette ha p).edges = p.edges.map (rescaledLink ha) := by
  simp [ElementaryPlaquette.edges, rescaledPlaquette_eq, rescaledLink_forwardFrom, map_add,
    pointRescale_axisStep]
theorem image_cornerSet (ha : 0 < a) (p : ElementaryPlaquette a) :
    pointRescale ha '' p.cornerSet = (rescaledPlaquette ha p).cornerSet := by
  simp only [ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton, map_add,
    pointRescale_axisStep]
  rfl
theorem image_linkSet (ha : 0 < a) (p : ElementaryPlaquette a) :
    rescaledLink ha '' p.linkSet = (rescaledPlaquette ha p).linkSet := by
  ext b'
  change b' ∈ rescaledLink ha '' {b | b ∈ p.edges} ↔ b' ∈ (rescaledPlaquette ha p).edges
  rw [edges_rescaledPlaquette, List.mem_map]
  rfl
theorem faceEnergy_fieldRescale (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (ha : 0 < a) (U : GaugeField a) (p : ElementaryPlaquette a) :
    faceEnergy (fieldRescale ha U) (rescaledPlaquette ha p) = faceEnergy U p :=
  ((hcopy a a⁻¹ 1 ha (inv_pos.2 ha) (one_eq_inv_mul_spacing ha)).2.1.2 p U).2
theorem exists_homeomorph_fieldRescale (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (ha : 0 < a) : ∃ e : GaugeField a ≃ₜ GaugeField 1, ⇑e = fieldRescale ha := by
  obtain ⟨e, he, -⟩ := (hcopy a a⁻¹ 1 ha (inv_pos.2 ha) (one_eq_inv_mul_spacing ha)).2.1.1
  exact ⟨e, he⟩
theorem latticeStructureTransfers (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (ha : 0 < a) : LatticeStructureTransfers ha := by
  obtain ⟨hsite, hbond, himage, -, hplaq, -⟩ :=
    (hcopy a a⁻¹ 1 ha (inv_pos.2 ha) (one_eq_inv_mul_spacing ha)).1
  refine ⟨hsite, hbond, ?_, hplaq, fun p => ⟨image_cornerSet ha p, image_linkSet ha p⟩,
    exists_homeomorph_fieldRescale hcopy ha, fun p U => faceEnergy_fieldRescale hcopy ha U p⟩
  have h := (hbond.injective.injOn (s := positiveLinks a)).bijOn_image
  rwa [show linkScale a⁻¹ (one_eq_inv_mul_spacing ha) '' positiveLinks a = positiveLinks 1 from
    himage] at h
theorem boundedObservable_comp {X : Type} {a' : ℝ} [MeasurableSpace X] {F : GaugeField a' → ℂ}
    (hF : IsBoundedObservable F) {g : X → GaugeField a'} (hg : Measurable g) :
    Measurable (F ∘ g) ∧ ∃ C : ℝ, ∀ U, ‖(F ∘ g) U‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF.2
  exact ⟨hF.1.comp hg, C, fun U => hC _⟩
theorem scaleByInv_injective (ha : 0 < a) : Function.Injective (scaleByInv a) :=
  fun _ _ h => smul_right_injective _ (inv_ne_zero ha.ne') h
theorem linksLieIn_singleton (b : Link a) (S : Set AmbientSpace) :
    LinksLieIn {b} S ↔ ((b.initial : AmbientSpace) ∈ S ∧ (b.terminal : AmbientSpace) ∈ S) := by
  simp [LinksLieIn]
theorem rescaledLink_mem_linksInside (ha : 0 < a) (S : Set AmbientSpace) (b : Link a) :
    rescaledLink ha b ∈ linksInside 1 (scaleByInvImage a S) ↔ b ∈ linksInside a S := by
  simp only [linksInside, mem_ofPred_eq, linksLieIn_singleton]
  exact and_congr (rescaledLink_isPositivelyOriented_iff ha b)
    (and_congr ((scaleByInv_injective ha).mem_set_image)
      ((scaleByInv_injective ha).mem_set_image))
theorem precompRescale_image_regionObservables
    (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (ha : 0 < a) (h₁ : MeasurableIffDependsOnly 1)
    (h₂ : MeasurableIffDependsOnly a) (S : Set AmbientSpace) :
    precompRescale ha '' regionObservables 1 (scaleByInvImage a S) = regionObservables a S := by
  obtain ⟨e, he⟩ := exists_homeomorph_fieldRescale hcopy ha
  rw [h₂.2.2.1 S, h₁.2.2.1 (scaleByInvImage a S)]
  ext F'
  constructor
  · rintro ⟨F, ⟨hF, hd⟩, rfl⟩
    refine ⟨boundedObservable_comp hF (measurable_fieldRescale ha),
      fun U U' h => hd _ _ fun b' hb' => ?_⟩
    obtain ⟨b, rfl⟩ := (linkEquiv ha).surjective b'
    change fieldRescale ha U (rescaledLink ha b) =
      fieldRescale ha U' (rescaledLink ha b)
    rw [fieldRescale_rescaledLink, fieldRescale_rescaledLink]
    exact h b ((rescaledLink_mem_linksInside ha S b).1 hb')
  · rintro ⟨hF', hd⟩
    refine ⟨F' ∘ e.symm, ⟨boundedObservable_comp hF' e.symm.continuous.measurable,
      fun W W' h => hd _ _ fun b hb => ?_⟩, ?_⟩
    · have h₃ : ∀ W : GaugeField 1, e.symm W b = W (rescaledLink ha b) := fun W => by
        have h₄ := fieldRescale_rescaledLink ha (e.symm W) b
        rw [← he, e.apply_symm_apply] at h₄
        exact h₄.symm
      rw [h₃, h₃]
      exact h _ ((rescaledLink_mem_linksInside ha S b).2 hb)
    · funext U
      change F' (e.symm (fieldRescale ha U)) = F' U
      rw [← he, e.symm_apply_apply]
theorem observablesTransfer (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (ha : 0 < a) (h₁ : MeasurableIffDependsOnly 1) (h₂ : MeasurableIffDependsOnly a) :
    ObservablesTransfer ha := by
  obtain ⟨e, he⟩ := exists_homeomorph_fieldRescale hcopy ha
  have himage := precompRescale_image_regionObservables hcopy ha h₁ h₂
  have hinv : ∀ F : GaugeField 1 → ℂ, F = precompRescale ha F ∘ e.symm := fun F => by
    funext W
    change F W = F (fieldRescale ha (e.symm W))
    rw [← he, e.apply_symm_apply]
  refine ⟨⟨fun F hF => boundedObservable_comp hF (measurable_fieldRescale ha), ?_, ?_⟩,
    himage, ?_⟩
  · intro F _ G _ h
    rw [hinv F, hinv G, h]
  · intro F' hF'
    refine ⟨F' ∘ e.symm, boundedObservable_comp hF' e.symm.continuous.measurable, ?_⟩
    funext U
    change F' (e.symm (fieldRescale ha U)) = F' U
    rw [← he, e.symm_apply_apply]
  · ext F'
    constructor
    · rintro ⟨F, ⟨hF, ⟨S, hS, hm⟩, hc⟩, rfl⟩
      have hS' : scaleByInvImage a (a • S) = S := by
        ext x
        simp [scaleByInvImage, scaleByInv, mem_smul_set, smul_smul, inv_mul_cancel₀ ha.ne']
      have h₃ : precompRescale ha F ∈ regionObservables a (a • S) := by
        rw [← himage, hS']
        exact ⟨F, ⟨hF, hm⟩, rfl⟩
      refine ⟨h₃.1, ⟨a • S, hS.smul₀ a, h₃.2⟩, ?_⟩
      exact hc.comp (he ▸ e.continuous)
    · rintro ⟨hF', ⟨S, hS, hm⟩, hc⟩
      have h₃ : F' ∈ precompRescale ha '' regionObservables 1 (scaleByInvImage a S) := by
        rw [himage]
        exact ⟨hF', hm⟩
      obtain ⟨F, hF, rfl⟩ := h₃
      refine ⟨F, ⟨hF.1, ⟨scaleByInvImage a S, hS.smul₀ a⁻¹, hF.2⟩, ?_⟩, rfl⟩
      rw [hinv F]
      exact hc.comp e.symm.continuous
theorem euclidNormVec_smul (t : ℝ) (v : AmbientSpace) :
    TorusMetric.euclidNormVec (t • v) = |t| * TorusMetric.euclidNormVec v := by apply _root_.YangMills.DeltaSharedProofs.p501477 <;> assumption
def conjugateSymmetry (ha : 0 < a) (r : LatticeSymmetry a) : LatticeSymmetry 1 where
  toFun := conjugateByScaling a r.toFun
  preservesDist x y := by
    have h₁ : conjugateByScaling a r.toFun x - conjugateByScaling a r.toFun y =
        a⁻¹ • (r.toFun (a • x) - r.toFun (a • y)) := by
      simp only [conjugateByScaling, scaleByInv, smul_sub]
    rw [h₁, euclidNormVec_smul, r.preservesDist, ← smul_sub, euclidNormVec_smul,
      abs_of_pos (inv_pos.2 ha), abs_of_pos ha, inv_mul_cancel_left₀ ha.ne']
  image_eq := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (pointRescale ha (r.pointMap (pointScale a (mul_one a).symm ⟨y, hy⟩))).2
    · intro hx
      have hax : a • x ∈ (latticeSubgroup a : Set AmbientSpace) :=
        (pointScale a (mul_one a).symm ⟨x, hx⟩).2
      rw [← r.image_eq] at hax
      obtain ⟨z, hz, hzx⟩ := hax
      refine ⟨a⁻¹ • z, (pointRescale ha ⟨z, hz⟩).2, ?_⟩
      change a⁻¹ • r.toFun (a • a⁻¹ • z) = x
      rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul, hzx, smul_smul, inv_mul_cancel₀ ha.ne',
        one_smul]
theorem fieldRescale_pullbackField (ha : 0 < a) (r : LatticeSymmetry a) (U : GaugeField a) :
    fieldRescale ha (r.pullbackField U) =
      (conjugateSymmetry ha r).pullbackField (fieldRescale ha U) := by
  refine Subtype.ext (funext fun b => ?_)
  change fieldRescale ha (r.pullbackField U) b =
    fieldRescale ha U ((conjugateSymmetry ha r).linkMap b)
  rw [fieldRescale_apply, fieldRescale_apply]
  change U (r.linkMap (linkScale a (mul_one a).symm b)) = _
  refine congrArg U.1 (InfiniteLattice.Link.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · change r.toFun (a • (b.initial : AmbientSpace)) =
      a • a⁻¹ • r.toFun (a • (b.initial : AmbientSpace))
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · change r.toFun (a • (b.terminal : AmbientSpace)) =
      a • a⁻¹ • r.toFun (a • (b.terminal : AmbientSpace))
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
theorem symmetriesTransfer (ha : 0 < a) : SymmetriesTransfer ha := fun r =>
  ⟨conjugateSymmetry ha r, rfl, fun F _ => by
    funext U
    change F (fieldRescale ha (r.pullbackField U)) =
      F ((conjugateSymmetry ha r).pullbackField (fieldRescale ha U))
    rw [fieldRescale_pullbackField]⟩
theorem symmetryConjugates (ha : 0 < a) : SymmetryConjugates ha := by
  refine ⟨fun v => ?_, fun w _ => ?_, fun n _ c => ?_⟩
  · funext x
    change a⁻¹ • (a • x + (v : AmbientSpace)) = x + a⁻¹ • (v : AmbientSpace)
    rw [smul_add, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  · funext x
    change a⁻¹ • w (a • x) = w x
    rw [map_smul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  · funext x
    change a⁻¹ • (a • x - (2 * (n ⬝ᵥ (a • x) - c)) • dualVector n) =
      x - (2 * (n ⬝ᵥ x - c / a)) • dualVector n
    rw [smul_sub, smul_smul, inv_mul_cancel₀ ha.ne', one_smul, smul_smul, dotProduct_smul,
      smul_eq_mul]
    congr 2
    field_simp
theorem exists_linearHeight_eq {n : AmbientSpace} (hn : n ∈ normalSet) (x : LatticePoint a) :
    ∃ k : ℤ, linearHeight n (x : AmbientSpace) = (k : ℝ) * a := by
  obtain ⟨F, rfl⟩ := exists_reflectionClass hn
  obtain ⟨p, hp⟩ := x.2
  refine ⟨∑ κ, F.intNormal κ * p κ, ?_⟩
  simp only [linearHeight, dotProduct, ReflectionClass.realNormal, hp]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun κ _ => by ring
theorem isAllowedLevel_iff_div (ha : 0 < a) (n : AmbientSpace) (c : ℝ) :
    IsAllowedLevel a n c ↔ IsAllowedLevel 1 n (c / a) := by
  have h₁ : ∀ k : ℤ, c = (k : ℝ) * (a / 2) ↔ c / a = (k : ℝ) * (1 / 2) := fun k => by
    rw [div_eq_iff ha.ne']
    constructor <;> intro h <;> rw [h] <;> ring
  have h₂ : ∀ k : ℤ, c = (k : ℝ) * a ↔ c / a = (k : ℝ) * 1 := fun k => by
    rw [mul_one, div_eq_iff ha.ne']
  simp only [IsAllowedLevel, h₁, h₂]
def unitPair (ha : 0 < a) (P : NormalLevelPair a) : NormalLevelPair 1 :=
  ⟨P.normal, P.normal_mem, P.level / a, (isAllowedLevel_iff_div ha _ _).1 P.allowed⟩
theorem isSitePair_unitPair (ha : 0 < a) (P : NormalLevelPair a) :
    P.IsSitePair ↔ (unitPair ha P).IsSitePair := by
  have h : ∀ k : ℤ, P.level = (k : ℝ) * a ↔ P.level / a = (k : ℝ) * 1 := fun k => by
    rw [mul_one, div_eq_iff ha.ne']
  simp only [NormalLevelPair.IsSitePair, unitPair, h]
theorem isLinkPair_unitPair (ha : 0 < a) (P : NormalLevelPair a) :
    P.IsLinkPair ↔ (unitPair ha P).IsLinkPair := by
  have h : ∀ k : ℤ, P.level = (k : ℝ) * a + a / 2 ↔ P.level / a = (k : ℝ) * 1 + 1 / 2 :=
    fun k => by
      rw [div_eq_iff ha.ne']
      constructor <;> intro h <;> rw [h] <;> ring
  simp only [NormalLevelPair.IsLinkPair, unitPair, h]
theorem scaleByInvImage_closedHalfSpace (ha : 0 < a) (n : AmbientSpace) (c : ℝ) (ε : ℤˣ) :
    scaleByInvImage a (closedHalfSpace n c ε) = closedHalfSpace n (c / a) ε := by
  have key : ∀ x : AmbientSpace, n ⬝ᵥ scaleByInv a x - c / a = a⁻¹ * (n ⬝ᵥ x - c) :=
    fun x => by
      simp only [scaleByInv, dotProduct_smul, smul_eq_mul]
      field_simp
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 ≤ _ * (n ⬝ᵥ scaleByInv a x - c / a)
    rw [key, mul_left_comm]
    exact mul_nonneg (inv_pos.2 ha).le hx
  · intro hy
    have hy' : scaleByInv a (a • y) = y := by
      simp [scaleByInv, smul_smul, inv_mul_cancel₀ ha.ne']
    refine ⟨a • y, ?_, hy'⟩
    have h := key (a • y)
    rw [hy'] at h
    change 0 ≤ _ * (n ⬝ᵥ y - c / a) at hy
    rw [h, mul_left_comm] at hy
    exact (mul_nonneg_iff_of_pos_left (inv_pos.2 ha)).1 hy
theorem realNormal_mem_normalSet (F : ReflectionClass) : F.realNormal ∈ normalSet := by apply _root_.YangMills.Construction.InfiniteLattice.EuclideanMirrors.MirrorReflections.realNormal_mem_reflectionNormals <;> assumption
theorem isAllowedLevel_of_latticeMirror (P : LatticeMirror a) :
    IsAllowedLevel a P.cls.realNormal P.level := by
  obtain ⟨F, c, hc⟩ := P
  cases F with
  | axial μ =>
    refine ⟨fun _ => hc, fun h => ?_⟩
    rw [normSq_eq_dotProduct, ReflectionClass.realNormal_dot_axial] at h
    norm_num at h
  | diagonal μ lam hlt s =>
    refine ⟨fun h => ?_, fun _ => hc⟩
    rw [normSq_eq_dotProduct, ReflectionClass.realNormal_dot_diagonal] at h
    norm_num at h
theorem mirrorsTransfer (ha : 0 < a) : MirrorsTransfer a := by
  refine ⟨fun n hn x => exists_linearHeight_eq hn x, fun n _ c => isAllowedLevel_iff_div ha n c,
    fun P => ?_, fun H hH => ?_⟩
  · refine ⟨unitPair ha P, rfl, rfl, ⟨P.reflectSymmetry, rfl⟩, isSitePair_unitPair ha P,
      isLinkPair_unitPair ha P, Iff.rfl, ?_, fun ε => scaleByInvImage_closedHalfSpace ha _ _ ε⟩
    refine ⟨P.toLatticeMirror, ?_⟩
    change {x | P.toLatticeMirror.cls.realNormal ⬝ᵥ x = P.level} = _
    rw [P.toLatticeMirror_realNormal]
  · obtain ⟨M, rfl⟩ := hH
    exact ⟨⟨M.cls.realNormal, realNormal_mem_normalSet _, M.level,
      isAllowedLevel_of_latticeMirror M⟩, rfl⟩
theorem rescaledLink_mem_rescaledWindow (ha : 0 < a) (W : LinkWindow a) (b : Link a) :
    rescaledLink ha b ∈ (rescaledWindow ha W).links ↔ b ∈ W.links := by
  simp only [rescaledWindow, Finset.mem_image]
  constructor
  · rintro ⟨b', hb', h⟩
    rwa [← (linkEquiv ha).injective h]
  · exact fun h => ⟨b, h, rfl⟩
def windowLinkEquiv (ha : 0 < a) (W : LinkWindow a) : W.links ≃ (rescaledWindow ha W).links :=
  Equiv.subtypeEquiv (linkEquiv ha) fun b => (rescaledLink_mem_rescaledWindow ha W b).symm
theorem reindexFactors_apply_equiv {S S' : Type} (u : S ≃ S')
    (g : S → Matrices.ComplexMatrix2.specialUnitary) (s : S) :
    PeriodicLattice.reindexFactors u g (u s) = g s := by
  simp [PeriodicLattice.reindexFactors]
theorem glue_of_mem {a' : ℝ} (ha : 0 < a') (W : LinkWindow a') (V : W.Assignments)
    (U : GaugeField a') {b : Link a'} (h : b ∈ W.links) : W.glue ha V U b = V ⟨b, h⟩ :=
  dif_pos h
theorem glue_of_opposite_mem {a' : ℝ} (ha : 0 < a') (W : LinkWindow a') (V : W.Assignments)
    (U : GaugeField a') {b : Link a'} (h : b ∉ W.links) (h' : b.opposite ∈ W.links) :
    W.glue ha V U b = (V ⟨b.opposite, h'⟩)⁻¹ :=
  (dif_neg h).trans (dif_pos h')
theorem glue_of_not_mem {a' : ℝ} (ha : 0 < a') (W : LinkWindow a') (V : W.Assignments)
    (U : GaugeField a') {b : Link a'} (h : b ∉ W.links) (h' : b.opposite ∉ W.links) :
    W.glue ha V U b = U b :=
  (dif_neg h).trans (dif_neg h')
theorem fieldRescale_glue (ha : 0 < a) (W : LinkWindow a) (V : W.Assignments) (U : GaugeField a) :
    fieldRescale ha (W.glue ha V U) =
      (rescaledWindow ha W).glue one_pos (PeriodicLattice.reindexFactors (windowLinkEquiv ha W) V)
        (fieldRescale ha U) := by
  refine Subtype.ext (funext fun b' => ?_)
  obtain ⟨b, rfl⟩ := (linkEquiv ha).surjective b'
  change fieldRescale ha (W.glue ha V U) (rescaledLink ha b) =
    (rescaledWindow ha W).glue one_pos (PeriodicLattice.reindexFactors (windowLinkEquiv ha W) V)
        (fieldRescale ha U) (rescaledLink ha b)
  rw [fieldRescale_rescaledLink]
  by_cases h : b ∈ W.links
  · have h' := (rescaledLink_mem_rescaledWindow ha W b).2 h
    rw [glue_of_mem ha W V U h, glue_of_mem one_pos _ _ _ h']
    exact (reindexFactors_apply_equiv (windowLinkEquiv ha W) V ⟨b, h⟩).symm
  · have h' : rescaledLink ha b ∉ (rescaledWindow ha W).links :=
      fun h₁ => h ((rescaledLink_mem_rescaledWindow ha W b).1 h₁)
    by_cases hr : b.opposite ∈ W.links
    · have hr' : (rescaledLink ha b).opposite ∈ (rescaledWindow ha W).links :=
        (rescaledLink_mem_rescaledWindow ha W b.opposite).2 hr
      rw [glue_of_opposite_mem ha W V U h hr, glue_of_opposite_mem one_pos _ _ _ h' hr']
      exact congrArg (·⁻¹) (reindexFactors_apply_equiv (windowLinkEquiv ha W) V ⟨b.opposite, hr⟩).symm
    · have hr' : (rescaledLink ha b).opposite ∉ (rescaledWindow ha W).links :=
        fun h₁ => hr ((rescaledLink_mem_rescaledWindow ha W b.opposite).1 h₁)
      rw [glue_of_not_mem ha W V U h hr, glue_of_not_mem one_pos _ _ _ h' hr',
        fieldRescale_rescaledLink]
theorem localWeight_fieldRescale (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (ha : 0 < a) (W : LinkWindow a) (β : ℝ) (U : GaugeField a) :
    (rescaledWindow ha W).localWeight β (fieldRescale ha U) = W.localWeight β U := by
  have hp : ∀ p, faceEquiv ha p ∈
      facesMeeting ((rescaledWindow ha W).links : Set (Link 1)) ↔
        p ∈ facesMeeting (W.links : Set (Link a)) := by
    intro p
    constructor
    · rintro ⟨b', hb, hb'⟩
      have hb₂ : b' ∈ (rescaledPlaquette ha p).edges := hb
      rw [edges_rescaledPlaquette, List.mem_map] at hb₂
      obtain ⟨b, hb₃, rfl⟩ := hb₂
      exact ⟨b, hb₃, (rescaledLink_mem_rescaledWindow ha W b).1 hb'⟩
    · rintro ⟨b, hb, hb'⟩
      refine ⟨rescaledLink ha b, ?_, (rescaledLink_mem_rescaledWindow ha W b).2 hb'⟩
      change _ ∈ (rescaledPlaquette ha p).edges
      rw [edges_rescaledPlaquette]
      exact List.mem_map_of_mem hb
  have hsum : ∑ᶠ p ∈ facesMeeting (W.links : Set (Link a)), faceEnergy U p =
      ∑ᶠ p' ∈ facesMeeting ((rescaledWindow ha W).links : Set (Link 1)),
        faceEnergy (fieldRescale ha U) p' :=
    finsum_mem_eq_of_bijOn (faceEquiv ha) ((faceEquiv ha).bijOn hp)
      fun p _ => (faceEnergy_fieldRescale hcopy ha U p).symm
  unfold LinkWindow.localWeight
  rw [hsum]
theorem conditionalExpectation_precompRescale
    (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hren : GaugeFieldProduct.ReindexingFactors) (ha : 0 < a) (β : ℝ) (W : LinkWindow a)
    (F : GaugeField 1 → ℂ) (U : GaugeField a) :
    W.conditionalExpectation ha β (precompRescale ha F) U =
      (rescaledWindow ha W).conditionalExpectation one_pos β F (fieldRescale ha U) := by
  obtain ⟨⟨e, he⟩, hH⟩ := hren _ _ (windowLinkEquiv ha W)
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hW : (rescaledWindow ha W).haarProd = W.haarProd.map e := by
    rw [he]
    exact hH.symm
  have hins : ∀ V, (rescaledWindow ha W).glue one_pos (e V) (fieldRescale ha U) =
      fieldRescale ha (W.glue ha V U) := fun V => by
    rw [he, fieldRescale_glue]
  unfold LinkWindow.conditionalExpectation
  rw [hW, hemb.integral_map, hemb.integral_map]
  simp only [hins, localWeight_fieldRescale hcopy]
  rfl
theorem kernelAndGaugeTransfer (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hren : GaugeFieldProduct.ReindexingFactors) (ha : 0 < a) (β : ℝ) :
    KernelAndGaugeTransfer ha β := by
  refine ⟨fun W F _ => funext fun U => conditionalExpectation_precompRescale hcopy hren ha β W F U,
    fun h => ?_⟩
  refine ⟨⟨fun x => h.toFun (pointScale a (mul_one a).symm x), ?_⟩, fun _ => rfl, fun U => ?_⟩
  · exact h.finite_ne_one.preimage (f := pointScale a (mul_one a).symm)
      ((pointAddEquiv ha).symm.injective.injOn)
  · refine Subtype.ext (funext fun b => ?_)
    change fieldRescale ha (h.act U) b = _ * fieldRescale ha U b * _
    rw [fieldRescale_apply, fieldRescale_apply]
    rfl
theorem gibbsClassesTransfer (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hforms : InfiniteLattice.GibbsClassEqGibbsStates) (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    GibbsClassesTransfer ha β := by
  obtain ⟨-, hC, -, -, -, hGibbs, hInv⟩ :=
    hcopy a a⁻¹ 1 ha (inv_pos.2 ha) (one_eq_inv_mul_spacing ha)
  obtain ⟨⟨e, he', -⟩, -⟩ := hC
  have he : ⇑e = fieldRescale ha := he'
  have hcl := hforms.2.1 a ha β hβ
  have hcl₁ := hforms.2.1 1 one_pos β hβ
  have hm : Measurable (fieldRescale ha) := measurable_fieldRescale ha
  have hme : Measurable e.symm := e.symm.continuous.measurable
  have hpre : ∀ ν' : Measure (GaugeField 1), dilatedState ha (ν'.map e.symm) = ν' := by
    intro ν'
    rw [dilatedState_eq_map, Measure.map_map hm hme]
    have h₁ : fieldRescale ha ∘ e.symm = id := by
      rw [← he]
      exact e.self_comp_symm
    rw [h₁, Measure.map_id]
  have hback : ∀ ν : Measure (GaugeField a), (dilatedState ha ν).map e.symm = ν := by
    intro ν
    rw [dilatedState_eq_map, Measure.map_map hme hm]
    have h₁ : e.symm ∘ fieldRescale ha = id := by
      rw [← he]
      exact e.symm_comp_self
    rw [h₁, Measure.map_id]
  have hprob : ∀ ν' : Measure (GaugeField 1), IsProbabilityMeasure ν' →
      IsProbabilityMeasure (ν'.map e.symm) := fun ν' _ =>
    Measure.isProbabilityMeasure_map hme.aemeasurable
  have hG : ∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν →
      (ν ∈ gibbsClass ha β ↔ dilatedState ha ν ∈ gibbsClass one_pos β) := by
    intro ν h
    rw [hcl.1, hcl₁.1]
    exact hGibbs β hβ ν h
  have hback₁ : ∀ ν' ∈ gibbsClass (a := 1) one_pos β,
      ν'.map e.symm ∈ gibbsClass ha β := fun ν' hν' =>
    (hG _ (hprob ν' hν'.1)).2 (by rw [hpre]; exact hν')
  have hI : ∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν → ∀ v : LatticePoint a,
      (IsSymmetricUnder ν (shift v) ↔
        IsSymmetricUnder (dilatedState ha ν) (shift (pointRescale ha v))) :=
    fun ν h v => (hInv.1 ν h).1 v
  refine ⟨fun ν hν => (hG ν hν.1).1 hν, fun ν' hν' => ⟨ν'.map e.symm, hback₁ ν' hν', hpre ν', ?_⟩,
    fun Q => ?_, ?_⟩
  · intro ν₂ _ h
    rw [← hback ν₂, h]
  · ext ν'
    constructor
    · rintro ⟨ν, ⟨hc, hinv⟩, rfl⟩
      refine ⟨(hG ν hc.1).1 hc, fun v' hv' => ?_⟩
      obtain ⟨v, hv, rfl⟩ := AddSubgroup.mem_map.1 hv'
      exact (hI ν hc.1 v).1 (hinv v hv)
    · rintro ⟨hc, hinv⟩
      refine ⟨ν'.map e.symm, ⟨hback₁ ν' hc, fun v hv => ?_⟩, hpre ν'⟩
      refine (hI _ (hprob ν' hc.1) v).2 ?_
      rw [hpre]
      exact hinv _ (AddSubgroup.mem_map_of_mem _ hv)
  · rw [hcl.2, hcl₁.2]
    exact (hInv.2 β hβ).image_eq
theorem exists_periodSublattice_image {a' c lam : ℝ} (hlam : 0 < lam) (hc : c = lam * a')
    (P : PeriodSublattice a') :
    ∃ P' : PeriodSublattice c, P'.periods = P.periods.map
      (AddMonoidHom.mk' (pointScale lam hc) fun x y =>
        Subtype.ext (smul_add lam (x : AmbientSpace) y)) := by
  set f : LatticePoint a' →+ LatticePoint c :=
    AddMonoidHom.mk' (pointScale lam hc) fun x y =>
      Subtype.ext (smul_add lam (x : AmbientSpace) y) with hf
  refine ⟨⟨P.periods.map f, ?_, ?_⟩, rfl⟩
  · obtain ⟨v, hv, hli⟩ := P.exists_linearIndependent
    refine ⟨fun i => f (v i), fun i => AddSubgroup.mem_map_of_mem _ (hv i), ?_⟩
    exact hli.map' (LinearEquiv.smulOfNeZero ℝ AmbientSpace lam hlam.ne').toLinearMap
      (LinearEquiv.ker _)
  · intro γ hγ hne
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.1 hγ
    have hg₀ : g ≠ 0 := by
      rintro rfl
      exact hne (map_zero f)
    have h := P.le_norm_of_ne_zero g hg hg₀
    change minimalPeriodRatio * c ≤ ‖lam • (g : AmbientSpace)‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hc]
    calc minimalPeriodRatio * (lam * a') = lam * (minimalPeriodRatio * a') := by ring
      _ ≤ lam * ‖(g : AmbientSpace)‖ := mul_le_mul_of_nonneg_left h hlam.le
theorem exists_periodSublattice_iff (ha : 0 < a) (Γ : AddSubgroup (LatticePoint a)) :
    (∃ P : PeriodSublattice a, P.periods = Γ) ↔
      ∃ P' : PeriodSublattice 1, P'.periods = subgroupRescale ha Γ := by
  constructor
  · rintro ⟨P, rfl⟩
    exact exists_periodSublattice_image (inv_pos.2 ha) (one_eq_inv_mul_spacing ha) P
  · rintro ⟨P', hP'⟩
    obtain ⟨P, hP⟩ := exists_periodSublattice_image ha (mul_one a).symm P'
    refine ⟨P, hP.trans ?_⟩
    rw [hP', subgroupRescale, AddSubgroup.map_map]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : pointScale a (mul_one a).symm (pointRescale ha y) = y :=
        pointScale_pointRescale ha y
      change pointScale a (mul_one a).symm (pointRescale ha y) ∈ Γ
      rwa [h]
    · intro hx
      exact ⟨x, hx, pointScale_pointRescale ha x⟩
def positiveLinkEquiv (ha : 0 < a) : PositiveLink a ≃ PositiveLink 1 :=
  Equiv.subtypeEquiv (linkEquiv ha) fun b => (rescaledLink_isPositivelyOriented_iff ha b).symm
theorem positiveLinkEquiv_translate (ha : 0 < a) (b : PositiveLink a) (γ : LatticePoint a) :
    positiveLinkEquiv ha (b.translate γ) =
      (positiveLinkEquiv ha b).translate (pointRescale ha γ) :=
  Subtype.ext (InfiniteLattice.Link.ext ((pointRescale ha).map_add _ _)
    ((pointRescale ha).map_add _ _))
def shiftedFace {a' : ℝ} (p : ElementaryPlaquette a') (γ : LatticePoint a') :
    ElementaryPlaquette a' :=
  ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem cornerSet_shiftedFace {a' : ℝ} (p : ElementaryPlaquette a') (γ : LatticePoint a') :
    (shiftedFace p γ).cornerSet = (shift γ).pointMap '' p.cornerSet := by apply _root_.YangMills.DeltaSharedProofs.p501596 <;> assumption
theorem plaquetteMap_shift {a' : ℝ} (ha : 0 < a') (p : ElementaryPlaquette a')
    (γ : LatticePoint a') : (shift γ).plaquetteMap p = shiftedFace p γ := by
  have h : ∃ p' : ElementaryPlaquette a', p'.cornerSet = (shift γ).pointMap '' p.cornerSet :=
    ⟨_, cornerSet_shiftedFace p γ⟩
  unfold LatticeSymmetry.plaquetteMap
  rw [dif_pos h]
  exact ElementaryPlaquette.cornerSet_injective ha
    (h.choose_spec.trans (cornerSet_shiftedFace p γ).symm)
theorem faceEquiv_shiftedFace (ha : 0 < a) (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    faceEquiv ha (shiftedFace p γ) = shiftedFace (faceEquiv ha p) (pointRescale ha γ) :=
  InfiniteLattice.ElementaryPlaquette.ext ((pointRescale ha).map_add _ _) rfl rfl
section Quotients
variable (ha : 0 < a) (P : PeriodSublattice a) (P' : PeriodSublattice 1)
  (h : P'.periods = subgroupRescale ha P.periods)
include h
theorem image_linkOrbit (b : PositiveLink a) :
    positiveLinkEquiv ha '' P.linkOrbit b = P'.linkOrbit (positiveLinkEquiv ha b) := by
  ext b'
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨pointRescale ha γ, h ▸ AddSubgroup.mem_map_of_mem _ hγ,
      positiveLinkEquiv_translate ha b γ⟩
  · rintro ⟨γ', hγ', rfl⟩
    rw [h] at hγ'
    obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.1 hγ'
    exact ⟨_, ⟨γ, hγ, rfl⟩, positiveLinkEquiv_translate ha b γ⟩
theorem image_plaquetteOrbit (p : ElementaryPlaquette a) :
    faceEquiv ha '' P.plaquetteOrbit p = P'.plaquetteOrbit (faceEquiv ha p) := by
  ext q'
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    refine ⟨pointRescale ha γ, h ▸ AddSubgroup.mem_map_of_mem _ hγ, ?_⟩
    rw [plaquetteMap_shift ha, plaquetteMap_shift one_pos, faceEquiv_shiftedFace]
  · rintro ⟨γ', hγ', rfl⟩
    rw [h] at hγ'
    obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.1 hγ'
    refine ⟨_, ⟨γ, hγ, rfl⟩, ?_⟩
    rw [plaquetteMap_shift ha, plaquetteMap_shift one_pos, faceEquiv_shiftedFace]
def quotientLinkEquiv : P.QuotientLink ≃ P'.QuotientLink :=
  Equiv.subtypeEquiv (Equiv.Set.congr (positiveLinkEquiv ha)) (by
    intro s
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨positiveLinkEquiv ha b, (image_linkOrbit ha P P' h b).symm⟩
    · rintro ⟨b', hb'⟩
      obtain ⟨b, rfl⟩ := (positiveLinkEquiv ha).surjective b'
      exact ⟨b, Set.image_injective.2 (positiveLinkEquiv ha).injective
        ((image_linkOrbit ha P P' h b).trans hb')⟩)
def quotientPlaquetteEquiv : P.QuotientPlaquette ≃ P'.QuotientPlaquette :=
  Equiv.subtypeEquiv (Equiv.Set.congr (faceEquiv ha)) (by
    intro s
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨faceEquiv ha p, (image_plaquetteOrbit ha P P' h p).symm⟩
    · rintro ⟨p', hp'⟩
      obtain ⟨p, rfl⟩ := (faceEquiv ha).surjective p'
      exact ⟨p, Set.image_injective.2 (faceEquiv ha).injective
        ((image_plaquetteOrbit ha P P' h p).trans hp')⟩)
theorem quotientLinkEquiv_linkClass (b : PositiveLink a) :
    quotientLinkEquiv ha P P' h (P.linkClass b) = P'.linkClass (positiveLinkEquiv ha b) :=
  Subtype.ext (image_linkOrbit ha P P' h b)
theorem lift_reindexFactors (U : P.QuotientField) :
    P'.lift (PeriodicLattice.reindexFactors (quotientLinkEquiv ha P P' h) U) =
      fieldRescale ha (P.lift U) := by
  refine Subtype.ext (funext fun b' => ?_)
  obtain ⟨b, rfl⟩ := (linkEquiv ha).surjective b'
  change P'.liftValue _ (rescaledLink ha b) =
    fieldRescale ha (P.lift U) (rescaledLink ha b)
  rw [fieldRescale_rescaledLink]
  change _ = P.liftValue U b
  by_cases hb : b.IsPositivelyOriented
  · have hb' := rescaledLink_isPositivelyOriented ha hb
    unfold PeriodSublattice.liftValue
    rw [dif_pos hb, dif_pos hb']
    have h₁ : P'.linkClass ⟨rescaledLink ha b, hb'⟩ =
        quotientLinkEquiv ha P P' h (P.linkClass ⟨b, hb⟩) :=
      (quotientLinkEquiv_linkClass ha P P' h ⟨b, hb⟩).symm
    rw [h₁, reindexFactors_apply_equiv]
  · have hb' : ¬(rescaledLink ha b).IsPositivelyOriented :=
      fun h₁ => hb ((rescaledLink_isPositivelyOriented_iff ha b).1 h₁)
    have hr := PeriodSublattice.isPositivelyOriented_opposite_of_not hb
    have hr' : (rescaledLink ha b).opposite.IsPositivelyOriented :=
      rescaledLink_isPositivelyOriented ha hr
    unfold PeriodSublattice.liftValue
    rw [dif_neg hb, dif_neg hb', dif_pos hr, dif_pos hr']
    have h₁ : P'.linkClass ⟨(rescaledLink ha b).opposite, hr'⟩ =
        quotientLinkEquiv ha P P' h (P.linkClass ⟨b.opposite, hr⟩) :=
      (quotientLinkEquiv_linkClass ha P P' h ⟨b.opposite, hr⟩).symm
    rw [h₁, reindexFactors_apply_equiv]
theorem quotientFaceEnergy_reindexFactors (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hext : P.LiftIsFaithful) (hext' : P'.LiftIsFaithful) (U : P.QuotientField)
    (p : P.QuotientPlaquette) :
    P'.quotientFaceEnergy (PeriodicLattice.reindexFactors (quotientLinkEquiv ha P P' h) U)
        (quotientPlaquetteEquiv ha P P' h p) = P.quotientFaceEnergy U p := by
  obtain ⟨q, hq⟩ := P.quotientPlaquette_nonempty p
  have hq' : faceEquiv ha q ∈
      ((quotientPlaquetteEquiv ha P P' h p : P'.QuotientPlaquette) :
        Set (ElementaryPlaquette 1)) :=
    mem_image_of_mem _ hq
  rw [← hext.faceEnergy_lift U p q hq, ← hext'.faceEnergy_lift _ _ _ hq',
    lift_reindexFactors ha P P' h U]
  exact faceEnergy_fieldRescale hcopy ha _ q
theorem boltzmannWeight_reindexFactors (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hext : P.LiftIsFaithful) (hext' : P'.LiftIsFaithful) (β : ℝ) (U : P.QuotientField) :
    P'.boltzmannWeight β (PeriodicLattice.reindexFactors (quotientLinkEquiv ha P P' h) U) =
      P.boltzmannWeight β U := by
  unfold PeriodSublattice.boltzmannWeight
  rw [← finsum_comp_equiv (quotientPlaquetteEquiv ha P P' h)]
  simp only [quotientFaceEnergy_reindexFactors ha P P' h hcopy hext hext']
theorem gibbsMeasure_map_reindexFactors (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hren : GaugeFieldProduct.ReindexingFactors) (hfin : Finite P.QuotientLink)
    (hfin' : Finite P'.QuotientLink) (hext : P.LiftIsFaithful)
    (hext' : P'.LiftIsFaithful) (β : ℝ) :
    (P.gibbsMeasure β).map (PeriodicLattice.reindexFactors (quotientLinkEquiv ha P P' h)) =
      P'.gibbsMeasure β := by
  obtain ⟨⟨e, he⟩, hH⟩ := hren _ _ (quotientLinkEquiv ha P P' h)
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hw : ∀ U, P'.boltzmannWeight β (e U) = P.boltzmannWeight β U := fun U => by
    rw [he]
    exact boltzmannWeight_reindexFactors ha P P' h hcopy hext hext' β U
  rw [← he] at hH ⊢
  have hN : P'.partitionFunction β = P.partitionFunction β := by
    unfold PeriodSublattice.partitionFunction PeriodSublattice.quotientHaar
    rw [← hH, hemb.integral_map]
    exact integral_congr_ae (ae_of_all _ hw)
  have hD : (P.quotientHaar.withDensity fun U => ENNReal.ofReal (P.boltzmannWeight β U)).map e =
      P'.quotientHaar.withDensity fun U => ENNReal.ofReal (P'.boltzmannWeight β U) := by
    refine Measure.ext fun B hB => ?_
    unfold PeriodSublattice.quotientHaar
    rw [Measure.map_apply e.continuous.measurable hB, withDensity_apply _ hB,
      withDensity_apply _ (e.continuous.measurable hB), ← hH, hemb.restrict_map,
      hemb.lintegral_map]
    exact lintegral_congr fun v => by rw [hw]
  unfold PeriodSublattice.gibbsMeasure
  rw [Measure.map_smul, hD, hN]
theorem dilatedState_liftedGibbsMeasure (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hren : GaugeFieldProduct.ReindexingFactors) (hfin : Finite P.QuotientLink)
    (hfin' : Finite P'.QuotientLink) (hext : P.LiftIsFaithful)
    (hext' : P'.LiftIsFaithful) (β : ℝ) :
    dilatedState ha (P.liftedGibbsMeasure β) = P'.liftedGibbsMeasure β := by
  obtain ⟨⟨e, he⟩, -⟩ := hren _ _ (quotientLinkEquiv ha P P' h)
  have hr : Measurable (PeriodicLattice.reindexFactors (quotientLinkEquiv ha P P' h)) :=
    he ▸ e.continuous.measurable
  rw [dilatedState_eq_map]
  unfold PeriodSublattice.liftedGibbsMeasure
  rw [Measure.map_map (measurable_fieldRescale ha) hext.isEmbedding_lift.continuous.measurable,
    ← gibbsMeasure_map_reindexFactors ha P P' h hcopy hren hfin hfin' hext hext' β,
    Measure.map_map hext'.isEmbedding_lift.continuous.measurable hr]
  congr 1
  funext U
  exact (lift_reindexFactors ha P P' h U).symm
end Quotients
theorem periodSublatticesTransfer (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hren : GaugeFieldProduct.ReindexingFactors)
    (htori : InfiniteLattice.ToriArraysAndTiltedMeasuresFacts) (ha : 0 < a) {β : ℝ}
    (hβ : 0 < β) : PeriodSublatticesTransfer ha β := by
  refine ⟨exists_periodSublattice_iff ha, fun P P' h => ⟨?_, ?_⟩⟩
  · have hmap : P.periods.map
        ((pointAddEquiv ha : LatticePoint a ≃+ LatticePoint 1) : LatticePoint a →+ LatticePoint 1) =
        P'.periods :=
      h.symm
    let E : P.QuotientTorus ≃+ P'.QuotientTorus :=
      QuotientAddGroup.congr P.periods P'.periods (pointAddEquiv ha) hmap
    exact ⟨E, E.bijective, fun x => rfl⟩
  · obtain ⟨hf, he, -⟩ := (htori β hβ).1 a ha P
    obtain ⟨hf', he', -⟩ := (htori β hβ).1 1 one_pos P'
    exact dilatedState_liftedGibbsMeasure ha P P' h hcopy hren hf.finite_quotientLink
      hf'.finite_quotientLink he he' β
theorem scalingToUnitSpacing_holds (hcopy : InfiniteLattice.Dilation.DilatedStateProperties)
    (hforms : InfiniteLattice.GibbsClassEqGibbsStates)
    (hfacts : InfiniteLattice.ElementaryLatticeFacts)
    (htori : InfiniteLattice.ToriArraysAndTiltedMeasuresFacts)
    (hproduct : GaugeFieldProduct.Statement) : ScalingToUnitSpacing := by
  intro a β ha hβ
  have h₁ := (hfacts 1 β one_pos hβ).2.2.2.2.2.2.1
  have h₂ := (hfacts a β ha hβ).2.2.2.2.2.2.1
  exact ⟨latticeStructureTransfers hcopy ha, observablesTransfer hcopy ha h₁ h₂,
    symmetriesTransfer ha, symmetryConjugates ha, mirrorsTransfer ha,
    kernelAndGaugeTransfer hcopy hproduct.2 ha β, gibbsClassesTransfer hcopy hforms ha hβ,
    periodSublatticesTransfer hcopy hproduct.2 htori ha hβ⟩
end YangMills.Construction.UnitSpacing
