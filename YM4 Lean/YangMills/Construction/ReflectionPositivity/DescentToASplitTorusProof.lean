import YangMills.Construction.InfiniteLattice.LinearPartAndIdentitiesOfTheReflections
import YangMills.Construction.InfiniteLattice.RulesOfTheActionOfTheLatticeIsometries
import YangMills.Construction.ReflectionPositivity.DescentToASplitTorus
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodDescent
open YangMills.Construction.NormalFamilies
section Plaquettes
variable (hr : SymmetryActionRules.Statement)
include hr
theorem cornerSet_plaquetteMap (r : LatticeSymmetry 1) (p : ElementaryPlaquette 1) :
    (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet :=
  (((hr r r).2.2.2.1 p).1 _).1 rfl
theorem eq_plaquetteMap_of_cornerSet (r : LatticeSymmetry 1) (p q : ElementaryPlaquette 1)
    (h : q.cornerSet = r.pointMap '' p.cornerSet) : q = r.plaquetteMap p :=
  (((hr r r).2.2.2.1 p).1 q).2 h
theorem plaquetteMap_comp_eq_of_pointMap {f g f' g' : LatticeSymmetry 1}
    (e : ∀ x : LatticePoint 1, f.pointMap (g.pointMap x) = f'.pointMap (g'.pointMap x))
    (p : ElementaryPlaquette 1) :
    f.plaquetteMap (g.plaquetteMap p) = f'.plaquetteMap (g'.plaquetteMap p) := by
  refine (eq_plaquetteMap_of_cornerSet hr f _ _ ?_).symm
  rw [cornerSet_plaquetteMap hr, cornerSet_plaquetteMap hr, cornerSet_plaquetteMap hr,
    Set.image_image, Set.image_image]
  exact Set.image_congr fun x _ => (e x).symm
theorem plaquetteMap_plaquetteMap {f g h : LatticeSymmetry 1}
    (e : ∀ x : LatticePoint 1, f.pointMap (g.pointMap x) = h.pointMap x)
    (p : ElementaryPlaquette 1) :
    f.plaquetteMap (g.plaquetteMap p) = h.plaquetteMap p := by
  refine eq_plaquetteMap_of_cornerSet hr h _ _ ?_
  rw [cornerSet_plaquetteMap hr, cornerSet_plaquetteMap hr, Set.image_image]
  exact Set.image_congr fun x _ => e x
theorem shift_zero_plaquetteMap (p : ElementaryPlaquette 1) :
    (shift (0 : LatticePoint 1)).plaquetteMap p = p := by
  refine (eq_plaquetteMap_of_cornerSet hr _ p p ?_).symm
  have h : ∀ x : LatticePoint 1, (shift (0 : LatticePoint 1)).pointMap x = x := fun x =>
    Subtype.ext (add_zero (x : AmbientSpace))
  simp [h]
theorem plaquetteMap_leftInverse {f g : LatticeSymmetry 1}
    (e : ∀ x : LatticePoint 1, f.pointMap (g.pointMap x) = x) (p : ElementaryPlaquette 1) :
    f.plaquetteMap (g.plaquetteMap p) = p := by
  rw [plaquetteMap_plaquetteMap hr (h := shift (0 : LatticePoint 1)) (fun x => by
    rw [e x]
    exact Subtype.ext (add_zero (x : AmbientSpace)).symm) p, shift_zero_plaquetteMap hr]
end Plaquettes
variable (Γ : PeriodSublattice 1)
theorem quotientMap_eq_iff {x y : LatticePoint 1} :
    Γ.quotientMap x = Γ.quotientMap y ↔ ∃ γ ∈ Γ.periods, y = x + γ := by
  constructor
  · intro h
    exact ⟨-x + y, QuotientAddGroup.eq.1 h, (add_neg_cancel_left x y).symm⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact (Γ.quotientMap_add_period x hγ).symm
theorem quotientMap_surjective : Function.Surjective Γ.quotientMap :=
  QuotientAddGroup.mk'_surjective Γ.periods
theorem orientedClass_surjective : Function.Surjective Γ.orientedClass :=
  fun c => ⟨_, Γ.orientedClass_orientedRep c⟩
theorem faceClass_surjective : Function.Surjective Γ.faceClass := by
  rintro ⟨_, p, rfl⟩
  exact ⟨p, rfl⟩
theorem exists_plaquetteRep_eq (p : ElementaryPlaquette 1) :
    ∃ γ ∈ Γ.periods, Γ.plaquetteRep (Γ.faceClass p) =
      (shift γ).plaquetteMap p :=
  (Γ.quotientPlaquette_nonempty (Γ.faceClass p)).some_mem
theorem faceClass_shift (hr : SymmetryActionRules.Statement)
    (p : ElementaryPlaquette 1) {γ : LatticePoint 1} (hγ : γ ∈ Γ.periods) :
    Γ.faceClass ((shift γ).plaquetteMap p) = Γ.faceClass p := by
  refine Subtype.ext (Set.ext fun q => ⟨?_, ?_⟩)
  · rintro ⟨γ', hγ', rfl⟩
    refine ⟨γ' + γ, add_mem hγ' hγ, plaquetteMap_plaquetteMap hr (fun x => ?_) p⟩
    refine Subtype.ext ?_
    change (x : AmbientSpace) + γ + γ' = (x : AmbientSpace) + ((γ' + γ : LatticePoint 1) : AmbientSpace)
    rw [AddSubgroup.coe_add]
    abel
  · rintro ⟨γ', hγ', rfl⟩
    refine ⟨γ' - γ, sub_mem hγ' hγ, (plaquetteMap_plaquetteMap hr (fun x => ?_) p).symm⟩
    refine Subtype.ext ?_
    change (x : AmbientSpace) + γ + ((γ' - γ : LatticePoint 1) : AmbientSpace) = (x : AmbientSpace) + γ'
    rw [AddSubgroup.coe_sub]
    abel
theorem plaquetteVertices_faceClass (hr : SymmetryActionRules.Statement)
    (p : ElementaryPlaquette 1) :
    Γ.plaquetteVertices (Γ.faceClass p) = Γ.quotientMap '' p.cornerSet := by
  obtain ⟨γ, hγ, h⟩ := exists_plaquetteRep_eq Γ p
  rw [PeriodSublattice.plaquetteVertices, h, cornerSet_plaquetteMap hr, Set.image_image]
  exact Set.image_congr fun x _ => Γ.quotientMap_add_period x hγ
def PreservesPeriods (f : AmbientSpace → AmbientSpace) : Prop :=
  ∀ γ ∈ Γ.periods,
    (∃ γ' ∈ Γ.periods, ∀ x : AmbientSpace, f (x + (γ : AmbientSpace)) = f x + (γ' : AmbientSpace)) ∧
      ∃ γ' ∈ Γ.periods, ∀ x : AmbientSpace, f (x + (γ' : AmbientSpace)) = f x + (γ : AmbientSpace)
theorem preservesPeriods_id : PreservesPeriods Γ id :=
  fun γ hγ => ⟨⟨γ, hγ, fun _ => rfl⟩, γ, hγ, fun _ => rfl⟩
theorem preservesPeriods_shift (v : LatticePoint 1) : PreservesPeriods Γ (shift v).toFun :=
  fun γ hγ =>
  ⟨⟨γ, hγ, fun x => add_right_comm x (γ : AmbientSpace) (v : AmbientSpace)⟩, γ, hγ,
    fun x => add_right_comm x (γ : AmbientSpace) (v : AmbientSpace)⟩
variable {Γ}
theorem PreservesPeriods.comp {f g : AmbientSpace → AmbientSpace} (hf : PreservesPeriods Γ f)
    (hg : PreservesPeriods Γ g) : PreservesPeriods Γ (f ∘ g) := by
  intro γ hγ
  constructor
  · obtain ⟨⟨γ₁, hγ₁, h₁⟩, -⟩ := hg γ hγ
    obtain ⟨⟨γ₂, hγ₂, h₂⟩, -⟩ := hf γ₁ hγ₁
    exact ⟨γ₂, hγ₂, fun x => by simp only [Function.comp, h₁, h₂]⟩
  · obtain ⟨-, γ₁, hγ₁, h₁⟩ := hf γ hγ
    obtain ⟨-, γ₂, hγ₂, h₂⟩ := hg γ₁ hγ₁
    exact ⟨γ₂, hγ₂, fun x => by simp only [Function.comp, h₁, h₂]⟩
theorem pointMap_add {R : LatticeSymmetry 1} {γ γ' : LatticePoint 1}
    (h : ∀ x : AmbientSpace, R.toFun (x + (γ : AmbientSpace)) = R.toFun x + (γ' : AmbientSpace))
    (x : LatticePoint 1) : R.pointMap (x + γ) = R.pointMap x + γ' :=
  Subtype.ext (h x)
theorem linkMap_shiftBy {R : LatticeSymmetry 1} {γ γ' : LatticePoint 1}
    (h : ∀ x : AmbientSpace, R.toFun (x + (γ : AmbientSpace)) = R.toFun x + (γ' : AmbientSpace))
    (b : Link 1) : R.linkMap (b.shiftBy γ) = (R.linkMap b).shiftBy γ' :=
  Link.ext (pointMap_add h b.initial) (pointMap_add h b.terminal)
theorem plaquetteMap_shift (hr : SymmetryActionRules.Statement)
    {R : LatticeSymmetry 1} {γ γ' : LatticePoint 1}
    (h : ∀ x : AmbientSpace, R.toFun (x + (γ : AmbientSpace)) = R.toFun x + (γ' : AmbientSpace))
    (p : ElementaryPlaquette 1) :
    R.plaquetteMap ((shift γ).plaquetteMap p) =
      (shift γ').plaquetteMap (R.plaquetteMap p) :=
  plaquetteMap_comp_eq_of_pointMap hr (fun x => pointMap_add h x) p
theorem mapsOrbits (hr : SymmetryActionRules.Statement)
    {R : LatticeSymmetry 1} (hR : PreservesPeriods Γ R.toFun) : Γ.MapsOrbits R where
  points_orbit x := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨γ, hγ, rfl⟩ := (quotientMap_eq_iff Γ).1 (Eq.symm hu)
      obtain ⟨⟨γ', hγ', h⟩, -⟩ := hR γ hγ
      change Γ.quotientMap (R.pointMap (x + γ)) = _
      rw [pointMap_add h]
      exact Γ.quotientMap_add_period _ hγ'
    · intro hy
      obtain ⟨γ, hγ, rfl⟩ := (quotientMap_eq_iff Γ).1 (Eq.symm hy)
      obtain ⟨-, γ', hγ', h⟩ := hR γ hγ
      exact ⟨x + γ', Γ.quotientMap_add_period x hγ', pointMap_add h x⟩
  links_orbit b := by
    ext b'
    constructor
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      obtain ⟨⟨γ', hγ', h⟩, -⟩ := hR γ hγ
      exact ⟨γ', hγ', linkMap_shiftBy h b⟩
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨-, γ', hγ', h⟩ := hR γ hγ
      exact ⟨b.shiftBy γ', ⟨γ', hγ', rfl⟩, linkMap_shiftBy h b⟩
  faces_orbit p := by
    ext q
    constructor
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      obtain ⟨⟨γ', hγ', h⟩, -⟩ := hR γ hγ
      exact ⟨γ', hγ', plaquetteMap_shift hr h p⟩
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨-, γ', hγ', h⟩ := hR γ hγ
      exact ⟨(shift γ').plaquetteMap p, ⟨γ', hγ', rfl⟩, plaquetteMap_shift hr h p⟩
theorem descendPoint_quotientMap {R : LatticeSymmetry 1} (hR : PreservesPeriods Γ R.toFun)
    (x : LatticePoint 1) :
    Γ.descendPoint R (Γ.quotientMap x) = Γ.quotientMap (R.pointMap x) := by
  have hout : Γ.quotientMap x = Γ.quotientMap (Γ.quotientMap x).out :=
    (QuotientAddGroup.out_eq' (Γ.quotientMap x)).symm
  obtain ⟨γ, hγ, h⟩ := (quotientMap_eq_iff Γ).1 hout
  obtain ⟨⟨γ', hγ', h'⟩, -⟩ := hR γ hγ
  rw [PeriodSublattice.descendPoint, h, pointMap_add h']
  exact Γ.quotientMap_add_period _ hγ'
theorem descendOrientedLink_orientedClass {R : LatticeSymmetry 1}
    (hR : PreservesPeriods Γ R.toFun) (b : Link 1) :
    Γ.descendOrientedLink R (Γ.orientedClass b) = Γ.orientedClass (R.linkMap b) := by
  obtain ⟨γ, hγ, h⟩ := Γ.exists_orientedRep_eq b
  obtain ⟨⟨γ', hγ', h'⟩, -⟩ := hR γ hγ
  rw [PeriodSublattice.descendOrientedLink, h, linkMap_shiftBy h']
  exact Γ.orientedClass_shiftBy _ hγ'
theorem descendFace_faceClass (hr : SymmetryActionRules.Statement)
    {R : LatticeSymmetry 1} (hR : PreservesPeriods Γ R.toFun) (p : ElementaryPlaquette 1) :
    Γ.descendFace R (Γ.faceClass p) = Γ.faceClass (R.plaquetteMap p) := by
  obtain ⟨γ, hγ, h⟩ := exists_plaquetteRep_eq Γ p
  obtain ⟨⟨γ', hγ', h'⟩, -⟩ := hR γ hγ
  rw [PeriodSublattice.descendFace, h, plaquetteMap_shift hr h']
  exact faceClass_shift Γ hr _ hγ'
theorem bijective_of_lift {α Q : Type*} {cls : α → Q} (hcls : Function.Surjective cls)
    {f g : α → α} {F : Q → Q} (hF : ∀ a, F (cls a) = cls (f a)) (hfg : ∀ a, f (g a) = a)
    (hinj : ∀ a a', cls (f a) = cls (f a') → cls a = cls a') : Function.Bijective F := by
  refine ⟨fun s s' h => ?_, fun s => ?_⟩
  · obtain ⟨a, rfl⟩ := hcls s
    obtain ⟨a', rfl⟩ := hcls s'
    rw [hF, hF] at h
    exact hinj a a' h
  · obtain ⟨a, rfl⟩ := hcls s
    exact ⟨cls (g a), by rw [hF, hfg]⟩
theorem descendsToQuotient (hr : SymmetryActionRules.Statement)
    {R : LatticeSymmetry 1} (hR : PreservesPeriods Γ R.toFun) : Γ.DescendsToQuotient R := by
  obtain ⟨S, hSR, hRS⟩ := (hr R R).2.2.2.2.2.2.2.1
  have hsr : ∀ x : LatticePoint 1, S.pointMap (R.pointMap x) = x := fun x =>
    Subtype.ext (congrFun hSR (x : AmbientSpace))
  have hrs : ∀ x : LatticePoint 1, R.pointMap (S.pointMap x) = x := fun x =>
    Subtype.ext (congrFun hRS (x : AmbientSpace))
  have hC := mapsOrbits hr hR
  have hsite : Function.Injective R.pointMap := Function.LeftInverse.injective hsr
  have hbond : Function.Injective R.linkMap := Function.LeftInverse.injective
    (g := S.linkMap) fun b => Link.ext (hsr b.initial) (hsr b.terminal)
  have hplaq : Function.Injective R.plaquetteMap := Function.LeftInverse.injective
    (g := S.plaquetteMap) (plaquetteMap_leftInverse hr hsr)
  have hS := descendPoint_quotientMap hR
  have hB := descendOrientedLink_orientedClass hR
  have hP := descendFace_faceClass hr hR
  refine
    { descendPoint_quotientMap := hS
      descendOrientedLink_orientedClass := hB
      descendFace_faceClass := hP
      descendPoint_bijective := ?_
      descendOrientedLink_bijective := ?_
      descendFace_bijective := ?_
      sourcePoint_descend := ?_
      targetPoint_descend := ?_
      plaquetteVertices_descend := ?_ }
  · refine bijective_of_lift (quotientMap_surjective Γ) hS hrs fun x x' h => ?_
    have e : {y | Γ.quotientMap y = Γ.quotientMap x} = {y | Γ.quotientMap y = Γ.quotientMap x'} :=
      hsite.image_injective (by rw [hC.points_orbit x, hC.points_orbit x', h])
    exact (Set.ext_iff.1 e x).1 rfl
  · refine bijective_of_lift (orientedClass_surjective Γ) hB
      (g := S.linkMap) (fun b => Link.ext (hrs b.initial) (hrs b.terminal)) fun b b' h => ?_
    exact Subtype.ext (hbond.image_injective ((hC.links_orbit b).trans
      ((congrArg Subtype.val h).trans (hC.links_orbit b').symm)))
  · refine bijective_of_lift (faceClass_surjective Γ) hP
      (g := S.plaquetteMap) (plaquetteMap_leftInverse hr hrs) fun p p' h => ?_
    exact Subtype.ext (hplaq.image_injective ((hC.faces_orbit p).trans
      ((congrArg Subtype.val h).trans (hC.faces_orbit p').symm)))
  · intro c
    obtain ⟨b, rfl⟩ := orientedClass_surjective Γ c
    rw [hB, Γ.sourcePoint_orientedClass, Γ.sourcePoint_orientedClass, hS]
    rfl
  · intro c
    obtain ⟨b, rfl⟩ := orientedClass_surjective Γ c
    rw [hB, Γ.targetPoint_orientedClass, Γ.targetPoint_orientedClass, hS]
    rfl
  · intro P
    obtain ⟨p, rfl⟩ := faceClass_surjective Γ P
    rw [hP, plaquetteVertices_faceClass Γ hr, plaquetteVertices_faceClass Γ hr,
      cornerSet_plaquetteMap hr, Set.image_image, Set.image_image]
    exact Set.image_congr fun x _ => (hS x).symm
theorem descend_comp (hr : SymmetryActionRules.Statement)
    {R R' R'' : LatticeSymmetry 1} (hR : PreservesPeriods Γ R.toFun)
    (hR' : PreservesPeriods Γ R'.toFun) (h : R''.toFun = R.toFun ∘ R'.toFun) :
    Γ.descendPoint R'' = Γ.descendPoint R ∘ Γ.descendPoint R' ∧
      Γ.descendOrientedLink R'' = Γ.descendOrientedLink R ∘ Γ.descendOrientedLink R' ∧
      Γ.descendFace R'' = Γ.descendFace R ∘ Γ.descendFace R' := by
  have hR'' : PreservesPeriods Γ R''.toFun := h ▸ hR.comp hR'
  have hs : ∀ x : LatticePoint 1, R''.pointMap x = R.pointMap (R'.pointMap x) := fun x =>
    Subtype.ext (congrFun h (x : AmbientSpace))
  refine ⟨funext fun s => ?_, funext fun c => ?_, funext fun P => ?_⟩
  · obtain ⟨x, rfl⟩ := quotientMap_surjective Γ s
    rw [Function.comp, descendPoint_quotientMap hR', descendPoint_quotientMap hR,
      descendPoint_quotientMap hR'', hs]
  · obtain ⟨b, rfl⟩ := orientedClass_surjective Γ c
    rw [Function.comp, descendOrientedLink_orientedClass hR', descendOrientedLink_orientedClass hR,
      descendOrientedLink_orientedClass hR'']
    exact congrArg _ (Link.ext (hs b.initial) (hs b.terminal))
  · obtain ⟨p, rfl⟩ := faceClass_surjective Γ P
    rw [Function.comp, descendFace_faceClass hr hR', descendFace_faceClass hr hR,
      descendFace_faceClass hr hR'', plaquetteMap_plaquetteMap hr (fun x => (hs x).symm)]
theorem sameDescent_of_shift (hr : SymmetryActionRules.Statement)
    {R R' : LatticeSymmetry 1} (hR : PreservesPeriods Γ R.toFun)
    (hR' : PreservesPeriods Γ R'.toFun) {w : LatticePoint 1}
    (hw : w ∈ Γ.periods) (h : ∀ x : AmbientSpace, R'.toFun x = R.toFun x + (w : AmbientSpace)) :
    Γ.SameDescent R' R := by
  have hs : ∀ x : LatticePoint 1, R'.pointMap x = R.pointMap x + w := fun x => Subtype.ext (h x)
  refine ⟨funext fun s => ?_, funext fun c => ?_, funext fun P => ?_⟩
  · obtain ⟨x, rfl⟩ := quotientMap_surjective Γ s
    rw [descendPoint_quotientMap hR', descendPoint_quotientMap hR, hs]
    exact Γ.quotientMap_add_period _ hw
  · obtain ⟨b, rfl⟩ := orientedClass_surjective Γ c
    rw [descendOrientedLink_orientedClass hR', descendOrientedLink_orientedClass hR]
    have e : R'.linkMap b = (R.linkMap b).shiftBy w := Link.ext (hs b.initial) (hs b.terminal)
    rw [e]
    exact Γ.orientedClass_shiftBy _ hw
  · obtain ⟨p, rfl⟩ := faceClass_surjective Γ P
    rw [descendFace_faceClass hr hR', descendFace_faceClass hr hR,
      ← plaquetteMap_plaquetteMap hr (f := shift w) (g := R) (h := R')
        (fun x => (hs x).symm)]
    exact faceClass_shift Γ hr _ hw
section Split
variable {n : AmbientSpace} {z : ℤ} {H : AddSubgroup AmbientSpace}
theorem normalOverNormSq_eq (n : AmbientSpace) :
    ReflectionPositivity.NormalPlanes.normalOverNormSq n = dualVector n := by
  rw [dualVector, normSq_eq_dotProduct]
  rfl
theorem dotProduct_intSMul (n w : AmbientSpace) (k : ℤ) :
    n ⬝ᵥ (k • w) = (k : ℝ) * (n ⬝ᵥ w) := by
  rw [← Int.cast_smul_eq_zsmul ℝ k w, dotProduct_smul, smul_eq_mul]
theorem exists_transverse_decomposition (hH : Γ.IsTransverseComplement n z H) {x : AmbientSpace}
    (hx : x ∈ Γ.toAmbient) :
    ∃ h ∈ H, ∃ k : ℤ, x = h + k • ((2 * (z : ℝ)) • dualVector n) := by
  rw [← hH.sup_eq] at hx
  obtain ⟨h, hh, l, hl, rfl⟩ := AddSubgroup.mem_sup.1 hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hl
  exact ⟨h, hh, k, by rw [normalOverNormSq_eq]⟩
theorem normalPeriod_mem (hH : Γ.IsTransverseComplement n z H) :
    (2 * (z : ℝ)) • dualVector n ∈ Γ.toAmbient := by
  rw [← hH.sup_eq, ← normalOverNormSq_eq n]
  exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)
theorem dotProduct_normalPeriod (hn : n ∈ normalSet) :
    n ⬝ᵥ ((2 * (z : ℝ)) • dualVector n) = 2 * (z : ℝ) := by
  rw [dotProduct_smul, smul_eq_mul, dotProduct_dualVector hn, mul_one]
theorem exists_height_eq (hn : n ∈ normalSet) (hH : Γ.IsTransverseComplement n z H)
    {x : AmbientSpace} (hx : x ∈ Γ.toAmbient) : ∃ k : ℤ, n ⬝ᵥ x = 2 * (z : ℝ) * (k : ℝ) := by
  obtain ⟨h, hh, k, rfl⟩ := exists_transverse_decomposition hH hx
  refine ⟨k, ?_⟩
  have h0 : n ⬝ᵥ h = 0 := hH.height_eq_zero h hh
  rw [dotProduct_add, h0, zero_add, dotProduct_intSMul, dotProduct_normalPeriod hn]
  ring
theorem linearReflect_mem (hn : n ∈ normalSet) (hH : Γ.IsTransverseComplement n z H)
    {x : AmbientSpace} (hx : x ∈ Γ.toAmbient) : linearReflect n x ∈ Γ.toAmbient := by
  obtain ⟨k, hk⟩ := exists_height_eq hn hH hx
  have e : linearReflect n x = x - (2 * k) • ((2 * (z : ℝ)) • dualVector n) := by
    rw [linearReflect_apply, hk, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    congr 2
    push_cast
    ring
  rw [e]
  exact sub_mem hx (zsmul_mem (normalPeriod_mem hH) _)
theorem mem_transverse_iff (hn : n ∈ normalSet) (hz : 2 ≤ z)
    (hH : Γ.IsTransverseComplement n z H) (x : AmbientSpace) :
    x ∈ H ↔ x ∈ Γ.toAmbient ∧ n ⬝ᵥ x = 0 := by
  constructor
  · intro hx
    exact ⟨hH.le_toAmbient hx, hH.height_eq_zero x hx⟩
  · rintro ⟨hx, h0⟩
    obtain ⟨h, hh, k, rfl⟩ := exists_transverse_decomposition hH hx
    have hh0 : n ⬝ᵥ h = 0 := hH.height_eq_zero h hh
    rw [dotProduct_add, hh0, zero_add, dotProduct_intSMul, dotProduct_normalPeriod hn] at h0
    have hz' : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have hk : (k : ℝ) = 0 := by
      rcases mul_eq_zero.1 h0 with h1 | h1
      · exact h1
      · exfalso
        linarith
    have hk' : k = 0 := by exact_mod_cast hk
    subst hk'
    simpa using hh
theorem linearReflect_linearReflect
    (hid : ReflectionLinearPart.Statement) (hn : n ∈ normalSet)
    {c : ℝ} (hc : IsAllowedLevel 1 n c) (x : AmbientSpace) :
    linearReflect n (linearReflect n x) = x := by
  have h0 : IsAllowedLevel 1 n 0 := (hid n hn c c hc hc 0).2.2.2.1
  exact congrFun (hid n hn 0 0 h0 h0 0).2.2.2.2.2.2.2.2.2.1 x
theorem preservesPeriods_reflectAcross (hid : ReflectionLinearPart.Statement)
    (hn : n ∈ normalSet) (hH : Γ.IsTransverseComplement n z H) {c : ℝ}
    (hc : IsAllowedLevel 1 n c) : PreservesPeriods Γ (reflectAcross n c) := by
  have hlin : ∀ (γ : LatticePoint 1) (x : AmbientSpace),
      reflectAcross n c (x + (γ : AmbientSpace)) =
        reflectAcross n c x + linearReflect n (γ : AmbientSpace) :=
    fun γ x => (hid n hn c c hc hc γ).2.2.2.2.2.2.2.1 x
  intro γ hγ
  obtain ⟨γ', hγ', e⟩ := AddSubgroup.mem_map.1
    (linearReflect_mem hn hH (x := (γ : AmbientSpace)) ⟨γ, hγ, rfl⟩)
  have e' : (γ' : AmbientSpace) = linearReflect n (γ : AmbientSpace) := e
  refine ⟨⟨γ', hγ', fun x => by rw [hlin, e']⟩, γ', hγ', fun x => ?_⟩
  rw [hlin, e', linearReflect_linearReflect hid hn hc]
theorem generator_lift (hid : ReflectionLinearPart.Statement)
    (hn : n ∈ normalSet) (hH : Γ.IsTransverseComplement n z H) {f : AmbientSpace → AmbientSpace}
    (hf : IsGenerator n f) :
    (∃ R : LatticeSymmetry 1, R.toFun = f) ∧ PreservesPeriods Γ f := by
  rcases hf with ⟨v, rfl⟩ | ⟨c, hc, rfl⟩
  · exact ⟨⟨_, rfl⟩, preservesPeriods_shift Γ v⟩
  · exact ⟨⟨(⟨n, hn, c, hc⟩ : NormalLevelPair 1).reflectSymmetry, rfl⟩,
      preservesPeriods_reflectAcross hid hn hH hc⟩
theorem classIsometry_lift (hid : ReflectionLinearPart.Statement)
    (hr : SymmetryActionRules.Statement) (hn : n ∈ normalSet)
    (hH : Γ.IsTransverseComplement n z H) {r : AmbientSpace → AmbientSpace}
    (h : IsClassIsometry n r) :
    (∃ R : LatticeSymmetry 1, R.toFun = r) ∧ PreservesPeriods Γ r := by
  obtain ⟨l, hl, rfl⟩ := h
  induction l with
  | nil =>
    exact ⟨⟨shift (0 : LatticePoint 1), funext fun x => by simp [shift]⟩, preservesPeriods_id Γ⟩
  | cons f l ih =>
    obtain ⟨⟨R, hRf⟩, hf⟩ := generator_lift hid hn hH (hl f (by simp))
    obtain ⟨⟨R', hR'⟩, hg⟩ := ih fun g hg => hl g (by simp [hg])
    obtain ⟨S, hS⟩ := (hr R R').2.2.2.2.2.2.2.2.1
    exact ⟨⟨S, by rw [hS, hRf, hR']; rfl⟩, hf.comp hg⟩
end Split
theorem splitTorusDescent (hid : ReflectionLinearPart.Statement)
    (hr : SymmetryActionRules.Statement) :
    SplitTorusDescent := by
  intro Γ n hn z c hc v hs P
  obtain ⟨-, hz, H₀, hH₀⟩ := hs
  obtain ⟨w, hwΓ, hw'⟩ := AddSubgroup.mem_map.1 (normalPeriod_mem hH₀)
  have hw : (w : AmbientSpace) = (2 * (z : ℝ)) • dualVector n := hw'
  have hτ := preservesPeriods_shift Γ v
  have hθ : PreservesPeriods Γ P.reflectSymmetry.toFun :=
    preservesPeriods_reflectAcross hid hn hH₀ hc
  have hfam : ∀ r : AmbientSpace → AmbientSpace, IsClassIsometry n r →
      (∃ R : LatticeSymmetry 1, R.toFun = r) ∧ PreservesPeriods Γ r :=
    fun r h => classIsometry_lift hid hr hn hH₀ h
  have hadm : IsAllowedLevel 1 n (c + (z : ℝ)) := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨k, hk⟩ := hc.1 h
      exact ⟨k + 2 * z, by rw [hk]; push_cast; ring⟩
    · obtain ⟨k, hk⟩ := hc.2 h
      exact ⟨k + z, by rw [hk]; push_cast; ring⟩
  have hθ₂ := preservesPeriods_reflectAcross hid hn hH₀ hadm
  refine ⟨⟨w, hw⟩, dotProduct_normalPeriod hn, ?_, ?_, ?_, ?_, mapsOrbits hr hτ,
    descendsToQuotient hr hτ, mapsOrbits hr hθ, descendsToQuotient hr hθ, ?_, ?_,
    fun r h => (hfam r h).1,
    fun R h => ⟨mapsOrbits hr (hfam _ h).2, descendsToQuotient hr (hfam _ h).2⟩,
    fun R R' R'' h h' e => descend_comp hr (hfam _ h).2 (hfam _ h').2 e,
    ⟨hadm, sameDescent_of_shift hr hθ hθ₂ hwΓ fun x => ?_⟩, ?_, ?_⟩
  · intro γ hγ
    exact exists_height_eq hn hH₀ ⟨γ, hγ, rfl⟩
  · intro x y h
    obtain ⟨γ, hγ, rfl⟩ := (quotientMap_eq_iff Γ).1 h
    obtain ⟨k, hk⟩ := exists_height_eq hn hH₀ (x := (γ : AmbientSpace)) ⟨γ, hγ, rfl⟩
    refine ⟨-k, ?_⟩
    rw [AddSubgroup.coe_add, dotProduct_add, hk]
    push_cast
    ring
  · intro H hH x
    exact mem_transverse_iff hn hz hH x
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact linearReflect_mem hn hH₀ hy
    · intro hx
      exact ⟨_, linearReflect_mem hn hH₀ hx, linearReflect_linearReflect hid hn hc x⟩
  · intro b
    obtain ⟨b₀, rfl⟩ := orientedClass_surjective Γ b
    rw [descendOrientedLink_orientedClass hτ, Γ.orientedIsPositive_orientedClass_iff,
      Γ.orientedIsPositive_orientedClass_iff]
    exact Link.isPositivelyOriented_shiftBy_iff b₀ v
  · intro hv
    refine ⟨funext fun s => ?_, funext fun b => ?_, funext fun p => ?_⟩
    · obtain ⟨x, rfl⟩ := quotientMap_surjective Γ s
      rw [descendPoint_quotientMap hτ]
      exact Γ.quotientMap_add_period x hv
    · obtain ⟨b₀, rfl⟩ := orientedClass_surjective Γ b
      rw [descendOrientedLink_orientedClass hτ]
      exact Γ.orientedClass_shiftBy b₀ hv
    · obtain ⟨p₀, rfl⟩ := faceClass_surjective Γ p
      rw [descendFace_faceClass hr hτ]
      exact faceClass_shift Γ hr p₀ hv
  · change reflectAcross n (c + (z : ℝ)) x = reflectAcross n c x + (w : AmbientSpace)
    rw [hw]
    simp only [reflectAcross]
    module
  · intro x hx
    simp [reflectAcross, hx]
  · intro x hx
    have e : reflectAcross n c (x : AmbientSpace) =
        (x : AmbientSpace) - (2 * (z : ℝ)) • dualVector n := by
      rw [reflectAcross, hx, show 2 * (c + (z : ℝ) - c) = 2 * (z : ℝ) by ring]
    refine ⟨e, ?_⟩
    have e' : P.reflectSymmetry.pointMap x = x + -w :=
      Subtype.ext (e.trans (by rw [← hw, sub_eq_add_neg]; rfl))
    rw [e']
    exact Γ.quotientMap_add_period x (neg_mem hwΓ)
end YangMills.Construction.InfiniteLattice.PeriodDescent
