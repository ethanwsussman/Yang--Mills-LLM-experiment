import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.MapsThatALatticeIsometryInducesOnATorus
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import YangMills.Construction.ReflectionPositivity.DescentToASplitTorusProof
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace QuotientSymmetries
theorem isOrthogonalPart_orthogonalPart
    (motions : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (g : LatticeSymmetry 1) : g.IsOrthogonalPart g.orthogonalPart := by
  obtain ⟨R, hR, v, h⟩ := motions g.toFun g.preservesDist
  refine Classical.epsilon_spec (p := g.IsOrthogonalPart) ⟨R, hR, fun x => ?_⟩
  have h0 := h 0
  rw [Matrix.mulVec_zero, zero_add] at h0
  rw [h x, h0]
theorem orthogonalPart_shift
    (motions : Tower.OrthogonalMotions.IsometryOfSpaceIsAffine)
    (v : LatticePoint 1) : (shift v).orthogonalPart = 1 := by
  have h := (isOrthogonalPart_orthogonalPart motions (shift v)).2
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  have hx : x + (v : AmbientSpace) = (shift v).orthogonalPart *ᵥ x + (0 + (v : AmbientSpace)) := h x
  rw [zero_add] at hx
  rw [Matrix.toLin'_apply, Matrix.toLin'_one]
  exact (add_right_cancel hx).symm
theorem toFun_bijective_of_isOrthogonalPart {g : LatticeSymmetry 1}
    {R : Matrix (Fin 4) (Fin 4) ℝ} (h : g.IsOrthogonalPart R) : Function.Bijective g.toFun := by
  have h₁ : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 h.1
  have h₂ : R * Rᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 h.1
  refine Function.bijective_iff_has_inverse.2
    ⟨fun y => Rᵀ *ᵥ (y - g.toFun 0), fun x => ?_, fun y => ?_⟩
  · change Rᵀ *ᵥ (g.toFun x - g.toFun 0) = x
    rw [h.2 x, add_sub_cancel_right, Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]
  · change g.toFun (Rᵀ *ᵥ (y - g.toFun 0)) = y
    rw [h.2 (Rᵀ *ᵥ (y - g.toFun 0)), Matrix.mulVec_mulVec, h₂, Matrix.one_mulVec,
      sub_add_cancel]
def inverse (g : LatticeSymmetry 1) (h : Function.Bijective g.toFun) :
    LatticeSymmetry 1 where
  toFun := (Equiv.ofBijective g.toFun h).symm
  preservesDist x y := by
    have e := g.preservesDist ((Equiv.ofBijective g.toFun h).symm x)
      ((Equiv.ofBijective g.toFun h).symm y)
    have ex : g.toFun ((Equiv.ofBijective g.toFun h).symm x) = x :=
      (Equiv.ofBijective g.toFun h).apply_symm_apply x
    have ey : g.toFun ((Equiv.ofBijective g.toFun h).symm y) = y :=
      (Equiv.ofBijective g.toFun h).apply_symm_apply y
    rw [ex, ey] at e
    exact e.symm
  image_eq := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ g.toFun '' (latticeSubgroup 1 : Set AmbientSpace) := by
        rw [g.image_eq]
        exact hx
      obtain ⟨z, hz, rfl⟩ := hx'
      rw [show (Equiv.ofBijective g.toFun h).symm (g.toFun z) = z from
        (Equiv.ofBijective g.toFun h).symm_apply_apply z]
      exact hz
    · intro hy
      exact ⟨g.toFun y, (g.pointMap ⟨y, hy⟩).2, (Equiv.ofBijective g.toFun h).symm_apply_apply y⟩
theorem pointMap_inverse (g : LatticeSymmetry 1) (h : Function.Bijective g.toFun)
    (x : LatticePoint 1) : g.pointMap ((inverse g h).pointMap x) = x :=
  Subtype.ext ((Equiv.ofBijective g.toFun h).apply_symm_apply (x : AmbientSpace))
theorem inverse_pointMap (g : LatticeSymmetry 1) (h : Function.Bijective g.toFun)
    (x : LatticePoint 1) : (inverse g h).pointMap (g.pointMap x) = x :=
  Subtype.ext ((Equiv.ofBijective g.toFun h).symm_apply_apply (x : AmbientSpace))
theorem gaugeField_ext {U V : GaugeField 1} (h : ∀ b, U b = V b) : U = V :=
  Subtype.ext (funext h)
theorem shift_pointMap (v x : LatticePoint 1) : (shift v).pointMap x = x + v :=
  Subtype.ext rfl
theorem shift_pullbackField_shift (w v : LatticePoint 1) (W : GaugeField 1) :
    (shift w).pullbackField ((shift v).pullbackField W) =
      (shift (w + v)).pullbackField W :=
  gaugeField_ext fun b => congrArg W
    (Link.ext (Subtype.ext (add_assoc (b.initial : AmbientSpace) w v))
      (Subtype.ext (add_assoc (b.terminal : AmbientSpace) w v)))
theorem inverse_pullbackField_pullbackField (g : LatticeSymmetry 1)
    (h : Function.Bijective g.toFun) (W : GaugeField 1) :
    (inverse g h).pullbackField (g.pullbackField W) = W :=
  gaugeField_ext fun _ => congrArg W
    (Link.ext (pointMap_inverse g h _) (pointMap_inverse g h _))
theorem pullbackField_inverse_pullbackField (g : LatticeSymmetry 1)
    (h : Function.Bijective g.toFun) (W : GaugeField 1) :
    g.pullbackField ((inverse g h).pullbackField W) = W :=
  gaugeField_ext fun _ => congrArg W
    (Link.ext (inverse_pointMap g h _) (inverse_pointMap g h _))
variable (Γ : PeriodSublattice 1)
def PermutesPeriods (g : LatticeSymmetry 1) : Prop :=
  (∀ γ ∈ Γ.periods, ∃ γ' ∈ Γ.periods, ∀ x : LatticePoint 1, g.pointMap (x + γ) = g.pointMap x + γ') ∧
    ∀ γ' ∈ Γ.periods, ∃ γ ∈ Γ.periods, ∀ x : LatticePoint 1, g.pointMap (x + γ) = g.pointMap x + γ'
variable {Γ}
theorem permutesPeriods_of_orthogonalPartPreserves {g : LatticeSymmetry 1}
    (hl : g.IsOrthogonalPart g.orthogonalPart)
    (h : Γ.OrthogonalPartPreserves g) : PermutesPeriods Γ g := by
  have key : ∀ γ γ' : LatticePoint 1, g.orthogonalPart *ᵥ (γ : AmbientSpace) = γ' →
      ∀ x : LatticePoint 1, g.pointMap (x + γ) = g.pointMap x + γ' := by
    intro γ γ' e x
    apply Subtype.ext
    change g.toFun ((x : AmbientSpace) + γ) = g.toFun x + γ'
    rw [hl.2 ((x : AmbientSpace) + γ), hl.2 x, Matrix.mulVec_add, e]
    abel
  constructor
  · intro γ hγ
    have hm : g.orthogonalPart *ᵥ (γ : AmbientSpace) ∈
        Subtype.val '' (Γ.periods : Set (LatticePoint 1)) := by
      rw [← show _ = _ from h]
      exact ⟨γ, ⟨γ, hγ, rfl⟩, rfl⟩
    obtain ⟨γ', hγ', e⟩ := hm
    exact ⟨γ', hγ', key γ γ' e.symm⟩
  · intro γ' hγ'
    have hm : (γ' : AmbientSpace) ∈
        g.orthogonalPart.mulVec '' (Subtype.val '' (Γ.periods : Set (LatticePoint 1))) := by
      rw [show _ = _ from h]
      exact ⟨γ', hγ', rfl⟩
    obtain ⟨_, ⟨γ, hγ, rfl⟩, e⟩ := hm
    exact ⟨γ, hγ, key γ γ' e⟩
theorem permutesPeriods_shift (v : LatticePoint 1) : PermutesPeriods Γ (shift v) := by
  have key : ∀ (γ x : LatticePoint 1), (shift v).pointMap (x + γ) = (shift v).pointMap x + γ :=
    fun γ x => by
      rw [shift_pointMap, shift_pointMap]
      abel
  exact ⟨fun γ hγ => ⟨γ, hγ, key γ⟩, fun γ hγ => ⟨γ, hγ, key γ⟩⟩
theorem permutesPeriods_inverse {g : LatticeSymmetry 1} (hb : Function.Bijective g.toFun)
    (hk : PermutesPeriods Γ g) : PermutesPeriods Γ (inverse g hb) := by
  have key : ∀ γ γ' : LatticePoint 1, (∀ x : LatticePoint 1, g.pointMap (x + γ) = g.pointMap x + γ') →
      ∀ y : LatticePoint 1, (inverse g hb).pointMap (y + γ') =
        (inverse g hb).pointMap y + γ := by
    intro γ γ' h y
    have e := h ((inverse g hb).pointMap y)
    rw [pointMap_inverse] at e
    rw [← e, inverse_pointMap]
  constructor
  · intro γ' hγ'
    obtain ⟨γ, hγ, h⟩ := hk.2 γ' hγ'
    exact ⟨γ, hγ, key γ γ' h⟩
  · intro γ hγ
    obtain ⟨γ', hγ', h⟩ := hk.1 γ hγ
    exact ⟨γ', hγ', key γ γ' h⟩
theorem quotientMap_eq_iff {x y : LatticePoint 1} :
    Γ.quotientMap x = Γ.quotientMap y ↔ ∃ γ ∈ Γ.periods, y = x + γ := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodDescent.quotientMap_eq_iff <;> assumption
theorem quotientMap_surjective : Function.Surjective Γ.quotientMap :=
  QuotientAddGroup.mk'_surjective Γ.periods
theorem quotientMap_pointMap_eq {g : LatticeSymmetry 1} (hk : PermutesPeriods Γ g)
    {x y : LatticePoint 1} (e : Γ.quotientMap x = Γ.quotientMap y) :
    Γ.quotientMap (g.pointMap x) = Γ.quotientMap (g.pointMap y) := by
  obtain ⟨γ, hγ, rfl⟩ := quotientMap_eq_iff.1 e
  obtain ⟨γ', hγ', h⟩ := hk.1 γ hγ
  exact quotientMap_eq_iff.2 ⟨γ', hγ', h x⟩
theorem bijective_of_isDescendedMap {g : LatticeSymmetry 1} (hb : Function.Bijective g.toFun)
    (hk : PermutesPeriods Γ g) {f : Γ.QuotientTorus → Γ.QuotientTorus}
    (hf : Γ.IsDescendedMap g f) : Function.Bijective f := by
  have hk' := permutesPeriods_inverse hb hk
  constructor
  · intro c d e
    obtain ⟨x, rfl⟩ := quotientMap_surjective c
    obtain ⟨y, rfl⟩ := quotientMap_surjective d
    rw [hf x, hf y] at e
    have e' := quotientMap_pointMap_eq hk' e
    rwa [inverse_pointMap, inverse_pointMap] at e'
  · intro c
    obtain ⟨y, rfl⟩ := quotientMap_surjective c
    exact ⟨Γ.quotientMap ((inverse g hb).pointMap y), by
      rw [hf, pointMap_inverse]⟩
theorem existsUnique_isDescendedMap {g : LatticeSymmetry 1} (hk : PermutesPeriods Γ g) :
    ∃! f : Γ.QuotientTorus → Γ.QuotientTorus, Γ.IsDescendedMap g f := by
  refine ⟨fun c => Γ.quotientMap (g.pointMap (Quotient.out c)), fun x => ?_, fun f hf => ?_⟩
  · exact quotientMap_pointMap_eq hk (QuotientAddGroup.out_eq' (Γ.quotientMap x))
  · funext c
    obtain ⟨x, rfl⟩ := quotientMap_surjective c
    rw [hf x]
    exact (quotientMap_pointMap_eq hk (QuotientAddGroup.out_eq' (Γ.quotientMap x))).symm
theorem pullbackField_mem_invariantFields {g : LatticeSymmetry 1} (hk : PermutesPeriods Γ g)
    {W : GaugeField 1} (hW : W ∈ Γ.invariantFields) :
    g.pullbackField W ∈ Γ.invariantFields := by
  intro γ hγ
  obtain ⟨γ', hγ', h⟩ := hk.1 γ hγ
  refine gaugeField_ext fun b => ?_
  have e : g.linkMap ((shift γ).linkMap b) = (shift γ').linkMap (g.linkMap b) :=
    Link.ext (by
        change g.pointMap ((shift γ).pointMap b.initial) =
          (shift γ').pointMap (g.pointMap b.initial)
        rw [shift_pointMap, shift_pointMap, h])
      (by
        change g.pointMap ((shift γ).pointMap b.terminal) =
          (shift γ').pointMap (g.pointMap b.terminal)
        rw [shift_pointMap, shift_pointMap, h])
  change W (g.linkMap ((shift γ).linkMap b)) = W (g.linkMap b)
  rw [e]
  exact congrFun (congrArg Subtype.val (hW γ' hγ')) (g.linkMap b)
theorem exists_lift_eq_pullbackField (E : Γ.LiftIsFaithful) {g : LatticeSymmetry 1}
    (hk : PermutesPeriods Γ g) (U : Γ.QuotientField) :
    ∃ V, Γ.lift V = g.pullbackField (Γ.lift U) := by
  exact show g.pullbackField (Γ.lift U) ∈ Set.range Γ.lift from by
    rw [E.range_lift]
    exact pullbackField_mem_invariantFields hk (by rw [← E.range_lift]; exact ⟨U, rfl⟩)
theorem exists_isDescendedPullback (E : Γ.LiftIsFaithful)
    (hc : ∀ g : LatticeSymmetry 1, Continuous g.pullbackField) {g : LatticeSymmetry 1}
    (hb : Function.Bijective g.toFun) (hk : PermutesPeriods Γ g) :
    ∃ h : Γ.QuotientField ≃ₜ Γ.QuotientField, Γ.IsDescendedPullback g h := by
  have hk' := permutesPeriods_inverse hb hk
  choose P hP using exists_lift_eq_pullbackField E hk
  choose Q hQ using exists_lift_eq_pullbackField E hk'
  have cont : ∀ (s : LatticeSymmetry 1) (T : Γ.QuotientField → Γ.QuotientField),
      (∀ U, Γ.lift (T U) = s.pullbackField (Γ.lift U)) →
      Continuous T := fun s T hT => by
    refine E.isEmbedding_lift.continuous_iff.2 ?_
    have e : Γ.lift ∘ T = s.pullbackField ∘ Γ.lift := funext hT
    rw [e]
    exact (hc s).comp E.isEmbedding_lift.continuous
  refine ⟨⟨⟨P, Q, fun U => E.isEmbedding_lift.injective ?_,
    fun U => E.isEmbedding_lift.injective ?_⟩,
    cont g P hP, cont _ Q hQ⟩, hP⟩
  · rw [hQ, hP, inverse_pullbackField_pullbackField]
  · rw [hP, hQ, pullbackField_inverse_pullbackField]
theorem isDescendedPullback_descendedPullback (E : Γ.LiftIsFaithful)
    (hc : ∀ g : LatticeSymmetry 1, Continuous g.pullbackField) {g : LatticeSymmetry 1}
    (hb : Function.Bijective g.toFun) (hk : PermutesPeriods Γ g) :
    Γ.IsDescendedPullback g (Γ.descendedPullback g) :=
  Classical.epsilon_spec (exists_isDescendedPullback E hc hb hk)
theorem positiveLink_translate_translate (b : PositiveLink 1) (γ δ : LatticePoint 1) :
    (b.translate γ).translate δ = b.translate (γ + δ) :=
  Subtype.ext (Link.ext (add_assoc _ _ _) (add_assoc _ _ _))
theorem positiveLink_translate_zero (b : PositiveLink 1) : b.translate 0 = b :=
  Subtype.ext (Link.ext (add_zero _) (add_zero _))
theorem linkClass_eq_of_mem {b b' : PositiveLink 1} (h : b' ∈ Γ.linkOrbit b) :
    Γ.linkClass b' = Γ.linkClass b := by
  obtain ⟨γ, hγ, rfl⟩ := h
  refine Subtype.ext (Set.ext fun c => ⟨?_, ?_⟩)
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨γ + δ, add_mem hγ hδ, positiveLink_translate_translate b γ δ⟩
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨-γ + δ, add_mem (neg_mem hγ) hδ, by
      rw [positiveLink_translate_translate, ← add_assoc, add_neg_cancel, zero_add]⟩
theorem exists_linkClass_eq (c : Γ.QuotientLink) : ∃ b, Γ.linkClass b = c := by
  obtain ⟨_, b, rfl⟩ := c
  exact ⟨b, rfl⟩
variable (Γ) in
def shiftLink (v : LatticePoint 1) (c : Γ.QuotientLink) : Γ.QuotientLink :=
  Γ.linkClass ((Γ.linkRep c).translate v)
theorem shiftLink_linkClass (v : LatticePoint 1) (b : PositiveLink 1) :
    shiftLink Γ v (Γ.linkClass b) = Γ.linkClass (b.translate v) := by
  have h : Γ.linkRep (Γ.linkClass b) ∈ Γ.linkOrbit b :=
    (Γ.quotientLink_nonempty (Γ.linkClass b)).some_mem
  obtain ⟨γ, hγ, e⟩ := h
  unfold shiftLink
  rw [e, positiveLink_translate_translate, add_comm, ← positiveLink_translate_translate]
  exact linkClass_eq_of_mem ⟨γ, hγ, rfl⟩
variable (Γ) in
def shiftLinkEquiv (v : LatticePoint 1) : Γ.QuotientLink ≃ Γ.QuotientLink where
  toFun := shiftLink Γ v
  invFun := shiftLink Γ (-v)
  left_inv c := by
    obtain ⟨b, rfl⟩ := exists_linkClass_eq c
    rw [shiftLink_linkClass, shiftLink_linkClass, positiveLink_translate_translate,
      add_neg_cancel, positiveLink_translate_zero]
  right_inv c := by
    obtain ⟨b, rfl⟩ := exists_linkClass_eq c
    rw [shiftLink_linkClass, shiftLink_linkClass, positiveLink_translate_translate,
      neg_add_cancel, positiveLink_translate_zero]
theorem isDescendedPullback_shift_apply {v : LatticePoint 1}
    {h : Γ.QuotientField ≃ₜ Γ.QuotientField}
    (hp : Γ.IsDescendedPullback (shift v) h) (U : Γ.QuotientField)
    (c : Γ.QuotientLink) : h U c = U (shiftLinkEquiv Γ v c) := by
  obtain ⟨b, rfl⟩ := exists_linkClass_eq c
  have e : (shift v).linkMap b.1 = (b.translate v).1 :=
    Link.ext (Subtype.ext rfl) (Subtype.ext rfl)
  calc h U (Γ.linkClass b) = Γ.lift (h U) b.1 :=
        (Γ.lift_apply_positive _ b).symm
    _ = (shift v).pullbackField (Γ.lift U) b.1 := by rw [hp U]
    _ = Γ.lift U (b.translate v).1 := by
        change Γ.lift U ((shift v).linkMap b.1) = _
        rw [e]
    _ = U (Γ.linkClass (b.translate v)) := Γ.lift_apply_positive _ _
    _ = U (shiftLinkEquiv Γ v (Γ.linkClass b)) := by
        rw [show shiftLinkEquiv Γ v (Γ.linkClass b) = shiftLink Γ v (Γ.linkClass b) from rfl,
          shiftLink_linkClass]
def translateFace (p : ElementaryPlaquette 1) (v : LatticePoint 1) : ElementaryPlaquette 1 :=
  ⟨p.corner + v, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem translateFace_translateFace (p : ElementaryPlaquette 1) (γ δ : LatticePoint 1) :
    translateFace (translateFace p γ) δ = translateFace p (γ + δ) :=
  ElementaryPlaquette.ext (add_assoc _ _ _) rfl rfl
theorem translateFace_zero (p : ElementaryPlaquette 1) : translateFace p 0 = p :=
  ElementaryPlaquette.ext (add_zero _) rfl rfl
theorem shift_plaquetteMap
    (inj : Function.Injective
      (ElementaryPlaquette.cornerSet : ElementaryPlaquette 1 → Set (LatticePoint 1)))
    (v : LatticePoint 1) (hc : ∀ p : ElementaryPlaquette 1, ((shift v).plaquetteMap p).cornerSet =
      (shift v).pointMap '' p.cornerSet) (p : ElementaryPlaquette 1) :
    (shift v).plaquetteMap p = translateFace p v := by
  apply inj
  rw [hc]
  simp only [ElementaryPlaquette.cornerSet, translateFace, Set.image_insert_eq,
    Set.image_singleton, shift_pointMap]
  rw [add_right_comm p.corner (axisStep 1 p.lowAxis) v,
    add_right_comm p.corner (axisStep 1 p.highAxis) v,
    add_right_comm (p.corner + axisStep 1 p.lowAxis) (axisStep 1 p.highAxis) v,
    add_right_comm p.corner (axisStep 1 p.lowAxis) v]
theorem faceEnergy_shift_pullbackField (v : LatticePoint 1) (W : GaugeField 1)
    (p : ElementaryPlaquette 1) :
    faceEnergy ((shift v).pullbackField W) p = faceEnergy W (translateFace p v) := by
  have h : ∀ (x : LatticePoint 1) (μ : Fin 4),
      (shift v).pullbackField W (Link.forwardFrom x μ) = W (Link.forwardFrom (x + v) μ) :=
    fun x μ => congrArg W (Link.ext (Subtype.ext rfl)
      (Subtype.ext (add_right_comm (x : AmbientSpace) (axisStep 1 μ) v)))
  have hv : faceHolonomy ((shift v).pullbackField W) p =
      faceHolonomy W (translateFace p v) := by
    simp only [faceHolonomy, h, translateFace]
    rw [add_right_comm p.corner (axisStep 1 p.lowAxis) v,
      add_right_comm p.corner (axisStep 1 p.highAxis) v]
  simp only [faceEnergy, hv]
section Faces
variable (hm : ∀ (v : LatticePoint 1) (p : ElementaryPlaquette 1),
  (shift v).plaquetteMap p = translateFace p v)
include hm
theorem mem_plaquetteOrbit_iff {p q : ElementaryPlaquette 1} :
    q ∈ Γ.plaquetteOrbit p ↔ ∃ γ ∈ Γ.periods, q = translateFace p γ := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, hγ, hm γ p⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, hγ, (hm γ p).symm⟩
theorem faceClass_eq_of_mem {p q : ElementaryPlaquette 1} (h : q ∈ Γ.plaquetteOrbit p) :
    Γ.faceClass q = Γ.faceClass p := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_plaquetteOrbit_iff hm).1 h
  refine Subtype.ext (Set.ext fun c => ⟨fun hc => ?_, fun hc => ?_⟩)
  · obtain ⟨δ, hδ, rfl⟩ := (mem_plaquetteOrbit_iff hm).1 hc
    exact (mem_plaquetteOrbit_iff hm).2
      ⟨γ + δ, add_mem hγ hδ, translateFace_translateFace p γ δ⟩
  · obtain ⟨δ, hδ, rfl⟩ := (mem_plaquetteOrbit_iff hm).1 hc
    exact (mem_plaquetteOrbit_iff hm).2 ⟨-γ + δ, add_mem (neg_mem hγ) hδ, by
      rw [translateFace_translateFace, ← add_assoc, add_neg_cancel, zero_add]⟩
omit hm in
theorem exists_faceClass_eq (c : Γ.QuotientPlaquette) : ∃ p, Γ.faceClass p = c := by
  obtain ⟨_, p, rfl⟩ := c
  exact ⟨p, rfl⟩
variable (Γ) in
def shiftFace (v : LatticePoint 1) (c : Γ.QuotientPlaquette) : Γ.QuotientPlaquette :=
  Γ.faceClass (translateFace (Γ.plaquetteRep c) v)
theorem shiftFace_faceClass (v : LatticePoint 1) (p : ElementaryPlaquette 1) :
    shiftFace Γ v (Γ.faceClass p) = Γ.faceClass (translateFace p v) := by
  have h : Γ.plaquetteRep (Γ.faceClass p) ∈ Γ.plaquetteOrbit p :=
    (Γ.quotientPlaquette_nonempty (Γ.faceClass p)).some_mem
  obtain ⟨γ, hγ, e⟩ := (mem_plaquetteOrbit_iff hm).1 h
  unfold shiftFace
  rw [e, translateFace_translateFace, add_comm, ← translateFace_translateFace]
  exact faceClass_eq_of_mem hm ((mem_plaquetteOrbit_iff hm).2 ⟨γ, hγ, rfl⟩)
variable (Γ) in
def shiftFaceEquiv (v : LatticePoint 1) : Γ.QuotientPlaquette ≃ Γ.QuotientPlaquette where
  toFun := shiftFace Γ v
  invFun := shiftFace Γ (-v)
  left_inv c := by
    obtain ⟨p, rfl⟩ := exists_faceClass_eq c
    rw [shiftFace_faceClass hm, shiftFace_faceClass hm,
      translateFace_translateFace, add_neg_cancel, translateFace_zero]
  right_inv c := by
    obtain ⟨p, rfl⟩ := exists_faceClass_eq c
    rw [shiftFace_faceClass hm, shiftFace_faceClass hm,
      translateFace_translateFace, neg_add_cancel, translateFace_zero]
theorem quotientFaceEnergy_isDescendedPullback (E : Γ.LiftIsFaithful) {v : LatticePoint 1}
    {h : Γ.QuotientField ≃ₜ Γ.QuotientField}
    (hp : Γ.IsDescendedPullback (shift v) h) (U : Γ.QuotientField)
    (c : Γ.QuotientPlaquette) :
    Γ.quotientFaceEnergy (h U) c =
      Γ.quotientFaceEnergy U (shiftFaceEquiv Γ hm v c) := by
  have hq : translateFace (Γ.plaquetteRep c) v ∈
      ((shiftFaceEquiv Γ hm v c : Γ.QuotientPlaquette) : Set (ElementaryPlaquette 1)) :=
    (mem_plaquetteOrbit_iff hm).2 ⟨0, zero_mem _, (translateFace_zero _).symm⟩
  rw [← E.faceEnergy_lift U _ _ hq]
  change faceEnergy (Γ.lift (h U)) (Γ.plaquetteRep c) = _
  rw [hp U, faceEnergy_shift_pullbackField]
theorem finsum_quotientFaceEnergy_isDescendedPullback (E : Γ.LiftIsFaithful)
    {v : LatticePoint 1} {h : Γ.QuotientField ≃ₜ Γ.QuotientField}
    (hp : Γ.IsDescendedPullback (shift v) h) (U : Γ.QuotientField) :
    ∑ᶠ c : Γ.QuotientPlaquette, Γ.quotientFaceEnergy (h U) c =
      ∑ᶠ c : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U c := by
  simp only [quotientFaceEnergy_isDescendedPullback hm E hp U]
  exact finsum_comp_equiv (shiftFaceEquiv Γ hm v)
end Faces
theorem periodize_translate_isDescendedPullback (𝔸 : LocalObservableArray) {v : 𝔸.sublattice}
    {h : Γ.QuotientField ≃ₜ Γ.QuotientField}
    (hp : Γ.IsDescendedPullback (shift (v : LatticePoint 1)) h) (w : 𝔸.sublattice)
    (ι : Fin 𝔸.size) (U : Γ.QuotientField) :
    Γ.periodize (𝔸.translate (w, ι)) (h U) = Γ.periodize (𝔸.translate (w + v, ι)) U := by
  change 𝔸.gen ι ((shift (w : LatticePoint 1)).pullbackField (Γ.lift (h U))) =
    𝔸.gen ι ((shift ((w + v : 𝔸.sublattice) : LatticePoint 1)).pullbackField (Γ.lift U))
  rw [hp U, shift_pullbackField_shift]
  rfl
theorem periodicSum_isDescendedPullback (𝔸 : LocalObservableArray)
    (hterm : ∀ (w w' : 𝔸.sublattice) (ι : Fin 𝔸.size),
      (QuotientAddGroup.mk w : 𝔸.Cosets Γ) = QuotientAddGroup.mk w' →
        Γ.periodize (𝔸.translate (w, ι)) = Γ.periodize (𝔸.translate (w', ι)))
    {v : 𝔸.sublattice} {h : Γ.QuotientField ≃ₜ Γ.QuotientField}
    (hp : Γ.IsDescendedPullback (shift (v : LatticePoint 1)) h) (U : Γ.QuotientField) :
    𝔸.periodicSum Γ (h U) = 𝔸.periodicSum Γ U := by
  let e : 𝔸.Cosets Γ × Fin 𝔸.size ≃ 𝔸.Cosets Γ × Fin 𝔸.size :=
    Equiv.prodCongr (Equiv.addRight (QuotientAddGroup.mk v : 𝔸.Cosets Γ)) (Equiv.refl _)
  let f : 𝔸.Cosets Γ × Fin 𝔸.size → ℝ := fun i =>
    (Γ.periodize (𝔸.translate (𝔸.cosetRep Γ i.1, i.2)) U).re
  refine (finsum_congr fun i => ?_).trans (finsum_comp_equiv e (f := f))
  have hclass : (QuotientAddGroup.mk (𝔸.cosetRep Γ i.1 + v) : 𝔸.Cosets Γ) =
      QuotientAddGroup.mk (𝔸.cosetRep Γ (e i).1) := by
    change (QuotientAddGroup.mk (𝔸.cosetRep Γ i.1) : 𝔸.Cosets Γ) +
        QuotientAddGroup.mk v = QuotientAddGroup.mk (𝔸.cosetRep Γ (e i).1)
    rw [show (QuotientAddGroup.mk (𝔸.cosetRep Γ i.1) : 𝔸.Cosets Γ) = i.1 from
        QuotientAddGroup.out_eq' i.1,
      show (QuotientAddGroup.mk (𝔸.cosetRep Γ (e i).1) : 𝔸.Cosets Γ) = (e i).1 from
        QuotientAddGroup.out_eq' (e i).1]
    rfl
  change (Γ.periodize (𝔸.translate (𝔸.cosetRep Γ i.1, i.2)) (h U)).re =
    (Γ.periodize (𝔸.translate (𝔸.cosetRep Γ (e i).1, i.2)) U).re
  rw [periodize_translate_isDescendedPullback 𝔸 hp, hterm _ _ i.2 hclass]
theorem measurePreserving_withDensity_of_invariant {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (σ : X ≃ᵐ X) (hμ : MeasurePreserving σ μ μ) (ρ : X → ENNReal)
    (hρ : ∀ x, ρ (σ x) = ρ x) :
    MeasurePreserving σ (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨σ.measurable, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply σ.measurable hA, withDensity_apply _ (σ.measurable hA),
    withDensity_apply _ hA, ← hμ.setLIntegral_comp_preimage_emb σ.measurableEmbedding ρ A]
  exact lintegral_congr fun x => (hρ x).symm
theorem measurePreserving_piCongrLeft_haarPi {ι : Type} [Countable ι] (S : ι ≃ ι) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) S.symm)
      (Matrices.ComplexMatrix2.haarPi ι) (Matrices.ComplexMatrix2.haarPi ι) :=
  ⟨(MeasurableEquiv.piCongrLeft
      (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) S.symm).measurable,
    Measure.infinitePi_map_piCongrLeft
      (μ := fun _ : ι => Matrices.ComplexMatrix2.haarProb) S.symm⟩
theorem piCongrLeft_symm_apply {ι : Type} (S : ι ≃ ι)
    (U : ι → Matrices.ComplexMatrix2.specialUnitary) (c : ι) :
    MeasurableEquiv.piCongrLeft (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) S.symm U c =
      U (S c) := by
  have e := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) S.symm U (S c)
  rwa [Equiv.symm_apply_apply] at e
theorem integral_comp_of_piCongrLeft {ι : Type} [Countable ι] (S : ι ≃ ι)
    (h : (ι → Matrices.ComplexMatrix2.specialUnitary) → ι → Matrices.ComplexMatrix2.specialUnitary)
    (hh : ∀ U c, h U c = U (S c))
    (ρ : (ι → Matrices.ComplexMatrix2.specialUnitary) → ENNReal) (hρ : ∀ U, ρ (h U) = ρ U)
    (k : ENNReal) (f : (ι → Matrices.ComplexMatrix2.specialUnitary) → ℂ) :
    ∫ U, f (h U) ∂(k • (Matrices.ComplexMatrix2.haarPi ι).withDensity ρ) =
      ∫ U, f U ∂(k • (Matrices.ComplexMatrix2.haarPi ι).withDensity ρ) := by
  have hσ : ∀ U, MeasurableEquiv.piCongrLeft
      (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) S.symm U = h U :=
    fun U => funext fun c => by rw [piCongrLeft_symm_apply, hh]
  have hd := measurePreserving_withDensity_of_invariant _
    (measurePreserving_piCongrLeft_haarPi S) ρ fun U => by rw [hσ U, hρ U]
  have hμ : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) S.symm)
      (k • (Matrices.ComplexMatrix2.haarPi ι).withDensity ρ)
      (k • (Matrices.ComplexMatrix2.haarPi ι).withDensity ρ) :=
    ⟨(MeasurableEquiv.piCongrLeft
        (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) S.symm).measurable, by
      rw [Measure.map_smul, hd.map_eq]⟩
  simp only [← hσ]
  exact hμ.integral_comp' f
theorem isHomeomorphInvariant_tiltedMeasure (E : Γ.LiftIsFaithful)
    (hm : ∀ (v : LatticePoint 1) (p : ElementaryPlaquette 1),
      (shift v).plaquetteMap p = translateFace p v)
    (𝔸 : LocalObservableArray)
    (hterm : ∀ (w w' : 𝔸.sublattice) (ι : Fin 𝔸.size),
      (QuotientAddGroup.mk w : 𝔸.Cosets Γ) = QuotientAddGroup.mk w' →
        Γ.periodize (𝔸.translate (w, ι)) = Γ.periodize (𝔸.translate (w', ι)))
    (β t : ℝ) {v : 𝔸.sublattice} {h : Γ.QuotientField ≃ₜ Γ.QuotientField}
    (hp : Γ.IsDescendedPullback (shift (v : LatticePoint 1)) h) :
    PeriodSublattice.IsHomeomorphInvariant (𝔸.tiltedMeasure Γ β t) h := by
  have hw : ∀ U, 𝔸.tiltedWeight Γ β t (h U) = 𝔸.tiltedWeight Γ β t U := fun U => by
    rw [LocalObservableArray.tiltedWeight, LocalObservableArray.tiltedWeight,
      periodicSum_isDescendedPullback 𝔸 hterm hp U,
      finsum_quotientFaceEnergy_isDescendedPullback hm E hp U]
  intro f
  exact integral_comp_of_piCongrLeft (shiftLinkEquiv Γ (v : LatticePoint 1)) h
    (isDescendedPullback_shift_apply hp)
    (fun U => ENNReal.ofReal (𝔸.tiltedWeight Γ β t U)) (fun U => by rw [hw U]) _ f
end QuotientSymmetries
open QuotientSymmetries in
theorem latticeSymmetriesDescendToQuotient
    (isometries : Tower.OrthogonalMotions.Classification)
    (space : FieldSpace.SymmetryProperties)
    (facts : ToriArraysAndTiltedMeasuresFacts) :
    LatticeSymmetriesDescendToQuotient := by
  intro β hβ Γ
  have motions := isometries.2.1
  have E : Γ.LiftIsFaithful := ((facts β hβ).1 1 one_pos Γ).2.1
  obtain ⟨-, hact, -, -, -, -, -, -, -, -, -, hinj, hpl⟩ := space 1 one_pos
  have hc : ∀ g : LatticeSymmetry 1, Continuous g.pullbackField :=
    fun g => (hact g g).1.continuous
  have hb : ∀ g : LatticeSymmetry 1, Function.Bijective g.toFun :=
    fun g => toFun_bijective_of_isOrthogonalPart (isOrthogonalPart_orthogonalPart motions g)
  have hm : ∀ (v : LatticePoint 1) (p : ElementaryPlaquette 1),
      (shift v).plaquetteMap p = translateFace p v :=
    fun v p => shift_plaquetteMap hinj v (hpl (shift v)).1 p
  refine ⟨fun g hg => ?_, fun 𝔸 hΓ t v hv => ⟨orthogonalPart_shift motions v, ?_⟩⟩
  · have hk := permutesPeriods_of_orthogonalPartPreserves (isOrthogonalPart_orthogonalPart motions g) hg
    have hu := existsUnique_isDescendedMap hk
    have hf : Γ.IsDescendedMap g (Γ.descendedMap g) :=
      Classical.epsilon_spec hu.exists
    have hP := isDescendedPullback_descendedPullback E hc (hb g) hk
    refine ⟨hu, hf, bijective_of_isDescendedMap (hb g) hk hf, fun U => ?_, hP, fun F _ => ?_⟩
    · exact ⟨Γ.descendedPullback g U, hP U,
        fun V hV => E.isEmbedding_lift.injective (by rw [hV, hP U])⟩
    · funext U
      change F (g.pullbackField (Γ.lift U)) = F (Γ.lift (Γ.descendedPullback g U))
      rw [hP U]
  · have hP := isDescendedPullback_descendedPullback E hc (hb (shift v)) (permutesPeriods_shift v)
    have D := ((facts β hβ).2.1 𝔸 t).2.2 Γ hΓ
    exact isHomeomorphInvariant_tiltedMeasure (v := ⟨v, hv⟩) E hm 𝔸 D.periodize_translate β t hP
end YangMills.Construction.InfiniteLattice
