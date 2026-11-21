import YangMills.Construction.InfiniteLattice.CovarianceOfTheMeasuresOfATorus
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusIsFaithfulProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfTheWilsonMeasureIsInvariantUnderMotionsKeepingThePeriodsProof
import YangMills.Construction.Matrices.HaarExpChartDensity
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice InfiniteLattice.SymmetriesAsMotions Matrices
namespace GibbsAtFixedSpacing
namespace TorusCovariance
variable {a : ℝ}
theorem map_haarPi_perm {ι : Type} [Countable ι] (σ : ι ≃ ι)
    (g : ι → ComplexMatrix2.specialUnitary → ComplexMatrix2.specialUnitary)
    (hg : ∀ i, Measurable (g i))
    (hp : ∀ i (E : Set ComplexMatrix2.specialUnitary), MeasurableSet E →
      ComplexMatrix2.haarProb (g i ⁻¹' E) = ComplexMatrix2.haarProb E) :
    (ComplexMatrix2.haarPi ι).map (fun U c => g c (U (σ c))) = ComplexMatrix2.haarPi ι := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.map_haarPi_perm <;> assumption
def positiveLink (b : Link a) : PositiveLink a :=
  open Classical in
  if h : b.IsPositivelyOriented then ⟨b, h⟩
  else ⟨b.opposite, PeriodSublattice.isPositivelyOriented_opposite_of_not h⟩
theorem positiveLink_of_pos {b : Link a} (h : b.IsPositivelyOriented) : positiveLink b = ⟨b, h⟩ := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.positiveRep_of_pos <;> assumption
theorem positiveLink_val_eq (b : Link a) :
    (positiveLink b).1 = b ∨ (positiveLink b).1 = b.opposite := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.positiveRep_eq_or <;> assumption
theorem positiveLink_opposite (Γ : PeriodSublattice a) (b : Link a) :
    positiveLink b.opposite = positiveLink b := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.positiveRep_opposite <;> assumption
theorem isPositivelyOriented_linkMap_shift (γ : LatticePoint a) (b : Link a) :
    ((shift γ).linkMap b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.isPositivelyOriented_linkMap_shift <;> assumption
theorem positiveLink_shift (γ : LatticePoint a) (b : Link a) :
    positiveLink ((shift γ).linkMap b) = (positiveLink b).translate γ := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.positiveRep_shift <;> assumption
theorem positiveLink_translate_zero (b : PositiveLink a) : b.translate 0 = b :=
  Subtype.ext (Link.ext (add_zero _) (add_zero _))
variable (Γ : PeriodSublattice a)
theorem linkClass_translate (b : PositiveLink a) {γ : LatticePoint a} (hγ : γ ∈ Γ.periods) :
    Γ.linkClass (b.translate γ) = Γ.linkClass b := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.linkClass_translate <;> assumption
def linkRep (c : Γ.QuotientLink) : PositiveLink a := c.2.choose
theorem linkClass_linkRep (c : Γ.QuotientLink) : Γ.linkClass (linkRep Γ c) = c :=
  Subtype.ext c.2.choose_spec
theorem exists_linkRep_eq (b : PositiveLink a) :
    ∃ γ ∈ Γ.periods, linkRep Γ (Γ.linkClass b) = b.translate γ := by
  exact show linkRep Γ (Γ.linkClass b) ∈ Γ.linkOrbit b from by
    have e : Γ.linkOrbit (linkRep Γ (Γ.linkClass b)) = Γ.linkOrbit b :=
      congrArg Subtype.val (linkClass_linkRep Γ (Γ.linkClass b))
    rw [← e]
    exact ⟨0, zero_mem _, (positiveLink_translate_zero _).symm⟩
theorem lift_of_positive (U : Γ.QuotientField) (b : PositiveLink a) :
    Γ.lift U b.1 = U (Γ.linkClass b) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.lift_apply_positive <;> assumption
theorem gaugeField_ext {V W : GaugeField a}
    (h : ∀ b : Link a, b.IsPositivelyOriented → V b = W b) : V = W := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.gaugeField_ext <;> assumption
def orient (b : Link a) : ComplexMatrix2.specialUnitary → ComplexMatrix2.specialUnitary :=
  open Classical in if b.IsPositivelyOriented then id else fun g => g⁻¹
theorem liftValue_eq (U : Γ.QuotientField) (b : Link a) :
    Γ.liftValue U b = orient b (U (Γ.linkClass (positiveLink b))) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.liftValue_eq_orient <;> assumption
theorem measurable_orient (b : Link a) : Measurable (orient b) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.measurable_orient <;> assumption
theorem haarProb_preimage_orient
    (hInv : ∀ E : Set ComplexMatrix2.specialUnitary, MeasurableSet E →
      ComplexMatrix2.haarProb ((fun g => g⁻¹) ⁻¹' E) = ComplexMatrix2.haarProb E) (b : Link a)
    (E : Set ComplexMatrix2.specialUnitary) (hE : MeasurableSet E) :
    ComplexMatrix2.haarProb (orient b ⁻¹' E) = ComplexMatrix2.haarProb E := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.haarProb_preimage_orient <;> assumption
variable (r : LatticeSymmetry a)
def PreservesPeriods : Prop :=
  ∀ γ ∈ Γ.periods, ∃ γ' ∈ Γ.periods, ∀ x : LatticePoint a, r.pointMap (x + γ) = r.pointMap x + γ'
def fieldPullback (U : Γ.QuotientField) : Γ.QuotientField :=
  fun c => Γ.liftValue U (r.linkMap (linkRep Γ c).1)
def linkPermutation (c : Γ.QuotientLink) : Γ.QuotientLink :=
  Γ.linkClass (positiveLink (r.linkMap (linkRep Γ c).1))
variable {Γ r}
theorem linkMap_shift {γ γ' : LatticePoint a}
    (h : ∀ x : LatticePoint a, r.pointMap (x + γ) = r.pointMap x + γ') (b : Link a) :
    r.linkMap ((shift γ).linkMap b) = (shift γ').linkMap (r.linkMap b) :=
  Link.ext (h _) (h _)
theorem linkMap_opposite (b : Link a) : r.linkMap b.opposite = (r.linkMap b).opposite := rfl
theorem fieldPullback_linkClass
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    (hK : PreservesPeriods Γ r) (U : Γ.QuotientField) (b : PositiveLink a) :
    fieldPullback Γ r U (Γ.linkClass b) = Γ.liftValue U (r.linkMap b.1) := by
  obtain ⟨γ, hγ, e⟩ := exists_linkRep_eq Γ b
  obtain ⟨γ', hγ', h⟩ := hK γ hγ
  have hb : (b.translate γ).1 = (shift γ).linkMap b.1 := rfl
  have hpv : Γ.liftValue U ((shift γ').linkMap (r.linkMap b.1)) =
      Γ.liftValue U (r.linkMap b.1) :=
    congrFun (congrArg Subtype.val (hper U γ' hγ')) (r.linkMap b.1)
  simp only [fieldPullback]
  rw [e, hb, linkMap_shift h, hpv]
theorem lift_fieldPullback
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    (hK : PreservesPeriods Γ r) (U : Γ.QuotientField) :
    Γ.lift (fieldPullback Γ r U) = r.pullbackField (Γ.lift U) := by
  refine gaugeField_ext fun b hb => ?_
  have h₁ := lift_of_positive Γ (fieldPullback Γ r U) ⟨b, hb⟩
  have h₂ := fieldPullback_linkClass hper hK U ⟨b, hb⟩
  exact h₁.trans h₂
theorem fieldPullback_eq :
    fieldPullback Γ r = fun U c =>
      orient (r.linkMap (linkRep Γ c).1) (U (linkPermutation Γ r c)) :=
  funext fun U => funext fun c => liftValue_eq Γ U _
theorem linkPermutation_linkClass (hK : PreservesPeriods Γ r) (b : PositiveLink a) :
    linkPermutation Γ r (Γ.linkClass b) = Γ.linkClass (positiveLink (r.linkMap b.1)) := by
  obtain ⟨γ, hγ, e⟩ := exists_linkRep_eq Γ b
  obtain ⟨γ', hγ', h⟩ := hK γ hγ
  have hb : (b.translate γ).1 = (shift γ).linkMap b.1 := rfl
  simp only [linkPermutation]
  rw [e, hb, linkMap_shift h, positiveLink_shift, linkClass_translate Γ _ hγ']
theorem linkMap_linkMap_of_inverse {t : LatticeSymmetry a} (ht : t.IsInverse r) (b : Link a) :
    r.linkMap (t.linkMap b) = b :=
  Link.ext (Subtype.ext (ht.2 _)) (Subtype.ext (ht.2 _))
theorem linkPermutation_surjective (hK : PreservesPeriods Γ r) {t : LatticeSymmetry a}
    (ht : t.IsInverse r) : Function.Surjective (linkPermutation Γ r) := by
  intro c
  have hc := linkClass_linkRep Γ c
  have hpos := (linkRep Γ c).2
  refine ⟨Γ.linkClass (positiveLink (t.linkMap (linkRep Γ c).1)), ?_⟩
  rw [linkPermutation_linkClass hK]
  rcases positiveLink_val_eq (t.linkMap (linkRep Γ c).1) with e | e
  · rw [e, linkMap_linkMap_of_inverse ht, positiveLink_of_pos hpos]
    exact hc
  · rw [e, linkMap_opposite, linkMap_linkMap_of_inverse ht, positiveLink_opposite Γ,
      positiveLink_of_pos hpos]
    exact hc
theorem map_fieldPullback_quotientHaar [Finite Γ.QuotientLink]
    (hInv : ∀ E : Set ComplexMatrix2.specialUnitary, MeasurableSet E →
      ComplexMatrix2.haarProb ((fun g => g⁻¹) ⁻¹' E) = ComplexMatrix2.haarProb E)
    (hK : PreservesPeriods Γ r) {t : LatticeSymmetry a} (ht : t.IsInverse r) :
    Γ.quotientHaar.map (fieldPullback Γ r) = Γ.quotientHaar := by
  have hs := linkPermutation_surjective hK ht
  have hb : Function.Bijective (linkPermutation Γ r) := ⟨Finite.injective_iff_surjective.2 hs, hs⟩
  have h := map_haarPi_perm (Equiv.ofBijective _ hb)
    (fun c => orient (r.linkMap (linkRep Γ c).1))
    (fun _ => measurable_orient _)
    (fun _ E hE => haarProb_preimage_orient hInv _ E hE)
  rw [fieldPullback_eq]
  exact h
theorem measurable_fieldPullback : Measurable (fieldPullback Γ r) := by
  rw [fieldPullback_eq]
  exact measurable_pi_lambda _ fun c =>
    (measurable_orient _).comp (measurable_pi_apply _)
def PlaquetteDeterminedByCorners (a : ℝ) : Prop :=
  ∀ (s : LatticeSymmetry a) (p q : ElementaryPlaquette a),
    q = s.plaquetteMap p ↔ q.cornerSet = s.pointMap '' p.cornerSet
theorem cornerSet_plaquetteMap (hc : PlaquetteDeterminedByCorners a) (s : LatticeSymmetry a)
    (p : ElementaryPlaquette a) : (s.plaquetteMap p).cornerSet = s.pointMap '' p.cornerSet := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.cornerSet_plaquetteMap <;> assumption
theorem shift_plaquetteMap_plaquetteMap (hc : PlaquetteDeterminedByCorners a)
    (γ δ : LatticePoint a) (q : ElementaryPlaquette a) :
    (shift δ).plaquetteMap ((shift γ).plaquetteMap q) = (shift (γ + δ)).plaquetteMap q := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.shift_plaquetteMap_plaquetteMap <;> assumption
theorem shift_zero_plaquetteMap (hc : PlaquetteDeterminedByCorners a)
    (q : ElementaryPlaquette a) : (shift (0 : LatticePoint a)).plaquetteMap q = q := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.shift_zero_plaquetteMap <;> assumption
theorem plaquetteMap_shift (hc : PlaquetteDeterminedByCorners a) {γ γ' : LatticePoint a}
    (h : ∀ x : LatticePoint a, r.pointMap (x + γ) = r.pointMap x + γ') (q : ElementaryPlaquette a) :
    r.plaquetteMap ((shift γ).plaquetteMap q) = (shift γ').plaquetteMap (r.plaquetteMap q) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.plaquetteMap_shift <;> assumption
variable (Γ) in
def orbitClass (q : ElementaryPlaquette a) : Γ.QuotientPlaquette := ⟨Γ.plaquetteOrbit q, q, rfl⟩
theorem plaquetteOrbit_shift (hc : PlaquetteDeterminedByCorners a) {γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) (q : ElementaryPlaquette a) :
    Γ.plaquetteOrbit ((shift γ).plaquetteMap q) = Γ.plaquetteOrbit q := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.plaquetteOrbit_shift <;> assumption
theorem mem_plaquetteOrbit_self (hc : PlaquetteDeterminedByCorners a) (q : ElementaryPlaquette a) :
    q ∈ Γ.plaquetteOrbit q := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.mem_plaquetteOrbit_self <;> assumption
variable (Γ) in
def faceRep (p : Γ.QuotientPlaquette) : ElementaryPlaquette a :=
  (Γ.quotientPlaquette_nonempty p).some
theorem faceRep_mem (p : Γ.QuotientPlaquette) :
    faceRep Γ p ∈ (p : Set (ElementaryPlaquette a)) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.plaquetteRep_mem <;> assumption
theorem eq_orbitClass_of_mem (hc : PlaquetteDeterminedByCorners a) (p : Γ.QuotientPlaquette)
    {q : ElementaryPlaquette a} (hq : q ∈ (p : Set (ElementaryPlaquette a))) :
    orbitClass Γ q = p := by
  obtain ⟨_, q₀, rfl⟩ := p
  obtain ⟨γ, hγ, rfl⟩ := hq
  exact Subtype.ext (plaquetteOrbit_shift hc hγ q₀)
variable (Γ r) in
def facePermutation (p : Γ.QuotientPlaquette) : Γ.QuotientPlaquette :=
  orbitClass Γ (r.plaquetteMap (faceRep Γ p))
theorem facePermutation_orbitClass (hc : PlaquetteDeterminedByCorners a)
    (hK : PreservesPeriods Γ r) (q : ElementaryPlaquette a) :
    facePermutation Γ r (orbitClass Γ q) = orbitClass Γ (r.plaquetteMap q) := by
  obtain ⟨γ, hγ, e⟩ : faceRep Γ (orbitClass Γ q) ∈ Γ.plaquetteOrbit q :=
    faceRep_mem (orbitClass Γ q)
  obtain ⟨γ', hγ', h⟩ := hK γ hγ
  simp only [facePermutation]
  rw [e, plaquetteMap_shift hc h]
  exact Subtype.ext (plaquetteOrbit_shift hc hγ' _)
theorem facePermutation_surjective (hc : PlaquetteDeterminedByCorners a)
    (hK : PreservesPeriods Γ r) {t : LatticeSymmetry a}
    (hright : Function.RightInverse t.plaquetteMap r.plaquetteMap) :
    Function.Surjective (facePermutation Γ r) := by
  intro p
  refine ⟨orbitClass Γ (t.plaquetteMap (faceRep Γ p)), ?_⟩
  rw [facePermutation_orbitClass hc hK, hright]
  exact eq_orbitClass_of_mem hc p (faceRep_mem p)
theorem quotientFaceEnergy_fieldPullback (hc : PlaquetteDeterminedByCorners a)
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    (hwell : ∀ (U : Γ.QuotientField) (p : Γ.QuotientPlaquette),
      ∀ q ∈ (p : Set (ElementaryPlaquette a)), ∀ q' ∈ (p : Set (ElementaryPlaquette a)),
        faceEnergy (Γ.lift U) q = faceEnergy (Γ.lift U) q')
    (hmove : ∀ p : ElementaryPlaquette a,
      r.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (r.plaquetteMap p))
    (hK : PreservesPeriods Γ r) (U : Γ.QuotientField) (p : Γ.QuotientPlaquette) :
    Γ.quotientFaceEnergy (fieldPullback Γ r U) p =
      Γ.quotientFaceEnergy U (facePermutation Γ r p) := by
  have h₁ : Γ.quotientFaceEnergy (fieldPullback Γ r U) p =
      faceEnergy (Γ.lift (fieldPullback Γ r U)) (faceRep Γ p) := rfl
  have h₂ : Γ.quotientFaceEnergy U (facePermutation Γ r p) =
      faceEnergy (Γ.lift U) (faceRep Γ (facePermutation Γ r p)) := rfl
  have h₃ := congrFun (hmove (faceRep Γ p)) (Γ.lift U)
  have h₄ : faceEnergy (r.pullbackField (Γ.lift U)) (faceRep Γ p) =
      faceEnergy (Γ.lift U) (r.plaquetteMap (faceRep Γ p)) := h₃
  rw [h₁, h₂, lift_fieldPullback hper hK, h₄]
  exact hwell U (facePermutation Γ r p) _ (mem_plaquetteOrbit_self hc _) _ (faceRep_mem _)
theorem lift_injective : Function.Injective Γ.lift := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicLift.lift_injective <;> assumption
theorem continuous_orient (b : Link a) : Continuous (orient b) := by
  by_cases h : b.IsPositivelyOriented
  · simpa [orient, h] using continuous_id
  · simpa [orient, h] using (continuous_inv : Continuous fun g : ComplexMatrix2.specialUnitary => g⁻¹)
theorem continuous_fieldPullback : Continuous (fieldPullback Γ r) := by
  rw [fieldPullback_eq]
  exact continuous_pi fun c => (continuous_orient _).comp (continuous_apply _)
theorem preservesPeriods_of_inverse {t : LatticeSymmetry a} (ht : t.IsInverse r)
    (hs : ∀ γ ∈ Γ.periods, ∃ γ' ∈ Γ.periods, ∀ x : LatticePoint a,
      r.pointMap (x + γ') = r.pointMap x + γ) : PreservesPeriods Γ t := by
  intro γ hγ
  obtain ⟨γ', hγ', h⟩ := hs γ hγ
  refine ⟨γ', hγ', fun x => ?_⟩
  have e₁ : r.pointMap (t.pointMap x) = x := Subtype.ext (ht.2 _)
  have e₂ : r.pointMap (t.pointMap x + γ') = x + γ := by rw [h, e₁]
  have e₃ : t.pointMap (r.pointMap (t.pointMap x + γ')) = t.pointMap x + γ' := Subtype.ext (ht.1 _)
  rw [e₂] at e₃
  exact e₃
theorem preservesPeriods_shift (v : LatticePoint a) : PreservesPeriods Γ (shift v) :=
  fun γ hγ => ⟨γ, hγ, fun x =>
    Subtype.ext (add_right_comm (x : AmbientSpace) (γ : AmbientSpace) (v : AmbientSpace))⟩
theorem fieldPullback_fieldPullback
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    {t : LatticeSymmetry a} (hK : PreservesPeriods Γ r) (hK' : PreservesPeriods Γ t)
    (h : Function.LeftInverse t.pullbackField r.pullbackField) (U : Γ.QuotientField) :
    fieldPullback Γ t (fieldPullback Γ r U) = U := by
  refine lift_injective ?_
  rw [lift_fieldPullback hper hK', lift_fieldPullback hper hK]
  exact h _
theorem faceEnergySum_fieldPullback (hb : Function.Bijective (facePermutation Γ r))
    (h : ∀ (U : Γ.QuotientField) (p : Γ.QuotientPlaquette),
      Γ.quotientFaceEnergy (fieldPullback Γ r U) p =
        Γ.quotientFaceEnergy U (facePermutation Γ r p))
    (U : Γ.QuotientField) :
    ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy (fieldPullback Γ r U) p =
      ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p :=
  (finsum_congr (h U)).trans
    (finsum_comp_equiv (f := fun p => Γ.quotientFaceEnergy U p) (Equiv.ofBijective _ hb))
theorem pullbackField_shift_add (v v' : LatticePoint a) (U : GaugeField a) :
    (shift (v + v')).pullbackField U = (shift v).pullbackField ((shift v').pullbackField U) := by
  refine Subtype.ext (funext fun b => congrArg U.1 ?_)
  exact Link.ext (Subtype.ext (add_assoc _ _ _).symm) (Subtype.ext (add_assoc _ _ _).symm)
theorem pointOrbit_eq_of_mem {x y : LatticePoint a} (h : -x + y ∈ Γ.periods) :
    pointOrbit Γ x = pointOrbit Γ y := by
  ext z
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨-(-x + y) + γ, add_mem (neg_mem h) hγ, by abel⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨(-x + y) + γ, add_mem h hγ, by abel⟩
variable (A : SingleGeneratorArray a)
theorem periodize_translate_fieldPullback
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    (v : LatticePoint a) (w : A.sublattice) (U : Γ.QuotientField) :
    Γ.periodize (A.translate w) (fieldPullback Γ (shift v) U) =
      Γ.periodize ((shift ((w : LatticePoint a) + v)).actOn A.gen) U := by
  simp only [PeriodSublattice.periodize, SingleGeneratorArray.translate, LatticeSymmetry.actOn]
  rw [lift_fieldPullback hper (preservesPeriods_shift v), pullbackField_shift_add]
theorem foldedSum_fieldPullback
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    (hdep : ∀ (E : Type) (F : GaugeField a → E) (v w : LatticePoint a),
      pointOrbit Γ v = pointOrbit Γ w →
      Γ.periodize ((shift v).actOn F) = Γ.periodize ((shift w).actOn F))
    (v : A.sublattice) (U : Γ.QuotientField) :
    A.foldedSum Γ (fieldPullback Γ (shift (v : LatticePoint a)) U) = A.foldedSum Γ U := by
  unfold SingleGeneratorArray.foldedSum
  let step : A.QuotientClasses Γ := QuotientAddGroup.mk v
  have key : ∀ c : A.QuotientClasses Γ,
      Γ.periodize (A.translate (A.classRep Γ c))
          (fieldPullback Γ (shift (v : LatticePoint a)) U) =
        Γ.periodize (A.translate (A.classRep Γ (c + step))) U := by
    intro c
    rw [periodize_translate_fieldPullback A hper]
    have hclass : ((A.classRep Γ c + v : A.sublattice) : A.QuotientClasses Γ) =
        ((A.classRep Γ (c + step) : A.sublattice) : A.QuotientClasses Γ) := by
      have e₁ : ((A.classRep Γ c : A.sublattice) : A.QuotientClasses Γ) = c :=
        QuotientAddGroup.out_eq' c
      have e₂ : ((A.classRep Γ (c + step) : A.sublattice) : A.QuotientClasses Γ) = c + step :=
        QuotientAddGroup.out_eq' (c + step)
      rw [e₂, QuotientAddGroup.mk_add, e₁]
    have hmem := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hclass)
    have horbit : pointOrbit Γ ((A.classRep Γ c : LatticePoint a) + v) =
        pointOrbit Γ (A.classRep Γ (c + step) : LatticePoint a) :=
      pointOrbit_eq_of_mem (by simpa using hmem)
    exact congrFun (hdep ℝ A.gen _ _ horbit) U
  rw [finsum_congr key]
  exact finsum_comp_equiv
    (f := fun c => Γ.periodize (A.translate (A.classRep Γ c)) U) (Equiv.addRight step)
theorem continuous_tiltWeight [Finite Γ.QuotientPlaquette] [Finite (A.QuotientClasses Γ)]
    (β t : ℝ)
    (hcont : ∀ F : GaugeField a → ℝ, Continuous F → Continuous (Γ.periodize F))
    (hτ : ∀ v : LatticePoint a, Continuous (shift v).pullbackField)
    (hact : ∀ p : Γ.QuotientPlaquette, Continuous fun U => Γ.quotientFaceEnergy U p) :
    Continuous (A.tiltWeight Γ β t) := by
  haveI := Fintype.ofFinite Γ.QuotientPlaquette
  haveI := Fintype.ofFinite (A.QuotientClasses Γ)
  have hgen : Continuous A.gen := (Complex.continuous_re.comp A.gen_mem.1).congr fun U => Complex.ofReal_re _
  have h : A.tiltWeight Γ β t = fun U => Real.exp (t *
      (∑ c : A.QuotientClasses Γ, Γ.periodize (A.translate (A.classRep Γ c)) U) -
        β * ∑ p, Γ.quotientFaceEnergy U p) :=
    funext fun U => by
      simp only [SingleGeneratorArray.tiltWeight, SingleGeneratorArray.foldedSum]
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  rw [h]
  refine Real.continuous_exp.comp ((continuous_const.mul
    (continuous_finsetSum _ fun c _ => hcont _ (hgen.comp (hτ _)))).sub
    (continuous_const.mul (continuous_finsetSum _ fun p _ => hact p)))
theorem map_withDensity_eq_of_invariant {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {T : X → X} (hT : Measurable T) (hmap : ν.map T = ν) {f : X → ENNReal} (hf : Measurable f)
    (hfT : ∀ x, f (T x) = f x) : (ν.withDensity f).map T = ν.withDensity f := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs,
    ← lintegral_indicator (hT hs), ← lintegral_indicator hs]
  calc ∫⁻ x, (T ⁻¹' s).indicator f x ∂ν
      = ∫⁻ x, s.indicator f (T x) ∂ν := by
        refine lintegral_congr fun x => ?_
        by_cases hx : T x ∈ s
        · simp [Set.indicator, hx, hfT]
        · simp [Set.indicator, hx]
    _ = ∫⁻ x, s.indicator f x ∂(ν.map T) := (lintegral_map (hf.indicator hs) hT).symm
    _ = _ := by rw [hmap]
theorem map_tiltMeasure (h : A.PeriodsWithin Γ) (β t : ℝ)
    {T : Γ.QuotientField → Γ.QuotientField} (hT : Measurable T)
    (hmap : Γ.quotientHaar.map T = Γ.quotientHaar)
    (hw : Measurable (A.tiltWeight Γ β t))
    (hwT : ∀ U, A.tiltWeight Γ β t (T U) = A.tiltWeight Γ β t U) :
    (A.tiltMeasure h β t).map T = A.tiltMeasure h β t := by
  simp only [SingleGeneratorArray.tiltMeasure]
  have hkey : (Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (A.tiltWeight Γ β t U)).map T =
      Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (A.tiltWeight Γ β t U) :=
    map_withDensity_eq_of_invariant hT hmap (ENNReal.measurable_ofReal.comp hw)
      fun U => by simp only [hwT]
  rw [Measure.map_smul, hkey]
theorem integral_liftedTiltMeasure (hm : Measurable Γ.lift)
    (h : A.PeriodsWithin Γ) (β t : ℝ) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    ∫ U, F U ∂(A.liftedTiltMeasure h β t) = ∫ U, Γ.periodize F U ∂(A.tiltMeasure h β t) :=
  integral_map hm.aemeasurable hF.1.aestronglyMeasurable
end TorusCovariance
open TorusCovariance in
theorem torusMeasureCovariance_holds
    (hOrbits : PeriodSublatticeQuotientFacts)
    (hMoves : SymmetriesTransportLinksSupportsAndPlaquettes)
    (hHaar : ComplexMatrix2.HaarExpChartProperties)
    (hAction : InfiniteLattice.SymmetriesAsMotions.Statement)
    (hExtension : InfiniteLattice.PeriodicLiftAndQuotientEnergiesStatement)
    (hWilson : InfiniteLattice.PeriodicGibbsSymmetricUnderPeriodPreservingMotions) :
    TorusMeasureCovariance := by
  intro a β ha hβ A t Γ h
  have : SecondCountableTopology ComplexMatrix2.specialUnitary :=
    have : SecondCountableTopology ComplexMatrix2 :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨⟨-, -, hLinks, hFaces, hQ⟩, ⟨hcont, hper, -⟩, ⟨hdep, -, hcontPer⟩⟩ := hOrbits a ha Γ
  obtain ⟨⟨-, -, hwell, hact⟩, -⟩ := hExtension a ha Γ
  haveI : Finite (A.QuotientClasses Γ) := hQ A.sublattice h
  have hc : PlaquetteDeterminedByCorners a := fun s p q =>
    ((hAction a ha s s).2.2.2.1).1 p q
  have hInv : ∀ E : Set ComplexMatrix2.specialUnitary, MeasurableSet E →
      ComplexMatrix2.haarProb ((fun g => g⁻¹) ⁻¹' E) = ComplexMatrix2.haarProb E := fun E hE => by
    have hm : Measurable fun g : ComplexMatrix2.specialUnitary => g⁻¹ :=
      (continuous_inv : Continuous fun g : ComplexMatrix2.specialUnitary => g⁻¹).measurable
    rw [← Measure.map_apply hm hE, hHaar.2.2.2]
  have hmove : ∀ (s : LatticeSymmetry a) (p : ElementaryPlaquette a),
      s.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (s.plaquetteMap p) :=
    fun s p => ((hMoves a ha).2.2 s).2.2.2.1 p
  refine ⟨fun F hF => integral_liftedTiltMeasure A hcont.measurable h β t hF, ?_, ?_⟩
  · intro r w hL hw
    obtain ⟨hwW, v₀, hv₀⟩ := hL
    have hsite : ∀ (x γ : LatticePoint a),
        (r.pointMap (x + γ) : AmbientSpace) = r.pointMap x + w γ := by
      intro x γ
      change r.toFun ((x : AmbientSpace) + (γ : AmbientSpace)) =
        r.toFun (x : AmbientSpace) + w (γ : AmbientSpace)
      rw [hv₀]
      simp only [latticeMotion, map_add]
      abel
    have hK : PreservesPeriods Γ r := by
      intro γ hγ
      have hmem : w (γ : AmbientSpace) ∈ w '' (Subtype.val '' (Γ.periods : Set (LatticePoint a))) :=
        ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      rw [hw] at hmem
      obtain ⟨γ', hγ', e⟩ := hmem
      refine ⟨γ', hγ', fun x => Subtype.ext ?_⟩
      rw [hsite]
      simp only [AddMemClass.coe_add, e]
    have hs : ∀ γ ∈ Γ.periods, ∃ γ' ∈ Γ.periods, ∀ x : LatticePoint a,
        r.pointMap (x + γ') = r.pointMap x + γ := by
      intro γ hγ
      have hmem : (γ : AmbientSpace) ∈ Subtype.val '' (Γ.periods : Set (LatticePoint a)) :=
        ⟨γ, hγ, rfl⟩
      rw [← hw] at hmem
      obtain ⟨_, ⟨γ', hγ', rfl⟩, e⟩ := hmem
      refine ⟨γ', hγ', fun x => Subtype.ext ?_⟩
      rw [hsite]
      simp only [AddMemClass.coe_add, e]
    obtain ⟨s, hs'⟩ := ((hAction a ha r r).2.1).2
    have hK' : PreservesPeriods Γ s := preservesPeriods_of_inverse hs' hs
    obtain ⟨hleft, hright⟩ := ((hAction a ha r r).2.2.2.2.1).2.2.2 s hs'
    refine ⟨⟨{ toFun := fieldPullback Γ r
               invFun := fieldPullback Γ s
               left_inv := fieldPullback_fieldPullback hper hK hK' hleft
               right_inv := fieldPullback_fieldPullback hper hK' hK hright
               continuous_toFun := continuous_fieldPullback
               continuous_invFun := continuous_fieldPullback }, ?_, ?_⟩, ?_⟩
    · exact ⟨measurable_fieldPullback, map_fieldPullback_quotientHaar hInv hK hs'⟩
    · exact lift_fieldPullback hper hK
    · exact hWilson a β ha hβ Γ r w hwW v₀ (fun x => by rw [hv₀]; rfl) hw
  · intro v hv
    have hK : PreservesPeriods Γ (shift v) := preservesPeriods_shift v
    obtain ⟨s, hs'⟩ := ((hAction a ha (shift v) (shift v)).2.1).2
    have hright := ((((hAction a ha (shift v) (shift v)).2.2.2.1).2.2.1) s hs').2
    have hT := measurable_fieldPullback (Γ := Γ) (r := shift v)
    have hps := facePermutation_surjective (Γ := Γ) hc hK hright
    have hpb : Function.Bijective (facePermutation Γ (shift v)) :=
      ⟨Finite.injective_iff_surjective.2 hps, hps⟩
    have hsum := faceEnergySum_fieldPullback hpb
      (quotientFaceEnergy_fieldPullback hc hper hwell (hmove _) hK)
    have hdesc := foldedSum_fieldPullback A hper hdep ⟨v, hv⟩
    have hw := continuous_tiltWeight A β t (fun F hF => hcontPer ℝ F hF)
      (fun u => ((hAction a ha (shift u) (shift u)).2.2.2.2.1).2.2.1.continuous)
      (fun p => (hact p).1)
    have hwT : ∀ U, A.tiltWeight Γ β t (fieldPullback Γ (shift v) U) = A.tiltWeight Γ β t U :=
      fun U => by
        simp only [SingleGeneratorArray.tiltWeight]
        rw [hsum U, hdesc U]
    have hmap := map_tiltMeasure A h β t hT (map_fieldPullback_quotientHaar hInv hK hs')
      hw.measurable hwT
    intro F hF
    have hO : IsBoundedObservable ((shift v).actOn F) :=
      (((hAction a ha (shift v) (shift v)).2.2.2.2.2.1).2 F F hF hF).1
    rw [integral_liftedTiltMeasure A hcont.measurable h β t hO,
      integral_liftedTiltMeasure A hcont.measurable h β t hF]
    have hper' : ∀ U, Γ.periodize ((shift v).actOn F) U =
        Γ.periodize F (fieldPullback Γ (shift v) U) := fun U => by
      simp only [PeriodSublattice.periodize]
      rw [lift_fieldPullback hper hK]
      rfl
    have hm : Measurable (Γ.periodize F) := hF.1.comp hcont.measurable
    simp only [hper']
    conv_rhs => rw [← hmap]
    exact (integral_map hT.aemeasurable hm.aestronglyMeasurable).symm
end GibbsAtFixedSpacing
end YangMills.Construction
