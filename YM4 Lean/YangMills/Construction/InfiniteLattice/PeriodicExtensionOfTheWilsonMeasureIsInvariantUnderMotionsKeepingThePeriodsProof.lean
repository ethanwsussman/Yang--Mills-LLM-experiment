import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAsMotionsAndTheirAction
import YangMills.Construction.InfiniteLattice.PeriodicExtensionAndPlaquetteActionsOfAPeriodLattice
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfTheWilsonMeasureIsInvariantUnderMotionsKeepingThePeriods
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFinite
import YangMills.Construction.InfiniteLattice.WilsonMeasureOfAPeriodLatticeAndItsExtensionAreStates
import YangMills.Construction.Lattice.HaarAndGaugeInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.Matrices
namespace PeriodicGibbsInvariance
variable {a : ℝ}
theorem map_haarPi_perm {ι : Type} [Countable ι] (σ : ι ≃ ι)
    (g : ι → ComplexMatrix2.specialUnitary → ComplexMatrix2.specialUnitary)
    (hg : ∀ i, Measurable (g i))
    (hp : ∀ i (E : Set ComplexMatrix2.specialUnitary), MeasurableSet E →
      ComplexMatrix2.haarProb (g i ⁻¹' E) = ComplexMatrix2.haarProb E) :
    (ComplexMatrix2.haarPi ι).map (fun U c => g c (U (σ c))) = ComplexMatrix2.haarPi ι := by
  classical
  have hmeas : Measurable (fun (U : ι → ComplexMatrix2.specialUnitary) c => g c (U (σ c))) :=
    measurable_pi_lambda _ fun c => (hg c).comp (measurable_pi_apply _)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : (fun (U : ι → ComplexMatrix2.specialUnitary) c => g c (U (σ c))) ⁻¹' (Set.pi s t) =
      Set.pi (s.map σ.toEmbedding : Finset ι) (fun j => g (σ.symm j) ⁻¹' t (σ.symm j)) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Equiv.coe_toEmbedding]
    constructor
    · rintro h _ ⟨c, hc, rfl⟩
      simpa using h c hc
    · intro h c hc
      simpa using h (σ c) ⟨c, hc, rfl⟩
  rw [hpre]
  unfold ComplexMatrix2.haarPi
  rw [Measure.infinitePi_pi _ fun j _ => hg _ (ht _), Finset.prod_map]
  exact Finset.prod_congr rfl fun c _ => by simp [hp c (t c) (ht c)]
def positiveRep (b : Link a) : PositiveLink a :=
  open Classical in
  if h : b.IsPositivelyOriented then ⟨b, h⟩
  else ⟨b.opposite, PeriodSublattice.isPositivelyOriented_opposite_of_not h⟩
theorem positiveRep_of_pos {b : Link a} (h : b.IsPositivelyOriented) : positiveRep b = ⟨b, h⟩ :=
  dif_pos h
theorem positiveRep_of_not_pos {b : Link a} (h : ¬b.IsPositivelyOriented) :
    positiveRep b = ⟨b.opposite, PeriodSublattice.isPositivelyOriented_opposite_of_not h⟩ :=
  dif_neg h
theorem positiveRep_eq_or (b : Link a) :
    (positiveRep b).1 = b ∨ (positiveRep b).1 = b.opposite := by
  by_cases h : b.IsPositivelyOriented
  · left
    rw [positiveRep_of_pos h]
  · right
    rw [positiveRep_of_not_pos h]
theorem positiveRep_opposite (Γ : PeriodSublattice a) (b : Link a) :
    positiveRep b.opposite = positiveRep b := by
  by_cases h : b.IsPositivelyOriented
  · rw [positiveRep_of_not_pos (Γ.not_isPositivelyOriented_opposite h), positiveRep_of_pos h]
    rfl
  · rw [positiveRep_of_pos (PeriodSublattice.isPositivelyOriented_opposite_of_not h),
      positiveRep_of_not_pos h]
theorem isPositivelyOriented_linkMap_shift (γ : LatticePoint a) (b : Link a) :
    ((shift γ).linkMap b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  have h : ((shift γ).linkMap b).terminal - ((shift γ).linkMap b).initial =
      b.terminal - b.initial :=
    add_sub_add_right_eq_sub b.terminal b.initial γ
  simp only [Link.IsPositivelyOriented, h]
theorem positiveRep_shift (γ : LatticePoint a) (b : Link a) :
    positiveRep ((shift γ).linkMap b) = (positiveRep b).translate γ := by
  by_cases h : b.IsPositivelyOriented
  · rw [positiveRep_of_pos ((isPositivelyOriented_linkMap_shift γ b).2 h),
      positiveRep_of_pos h]
    rfl
  · rw [positiveRep_of_not_pos (mt (isPositivelyOriented_linkMap_shift γ b).1 h),
      positiveRep_of_not_pos h]
    rfl
theorem positiveLink_translate_translate (b : PositiveLink a) (γ δ : LatticePoint a) :
    (b.translate γ).translate δ = b.translate (γ + δ) :=
  Subtype.ext (Link.ext (add_assoc _ _ _) (add_assoc _ _ _))
theorem positiveLink_translate_zero (b : PositiveLink a) : b.translate 0 = b :=
  Subtype.ext (Link.ext (add_zero _) (add_zero _))
variable (Γ : PeriodSublattice a)
theorem linkClass_translate (b : PositiveLink a) {γ : LatticePoint a} (hγ : γ ∈ Γ.periods) :
    Γ.linkClass (b.translate γ) = Γ.linkClass b := by
  refine Subtype.ext (Set.ext fun b' => ⟨?_, ?_⟩)
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨γ + δ, add_mem hγ hδ, positiveLink_translate_translate b γ δ⟩
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨-γ + δ, add_mem (neg_mem hγ) hδ, ?_⟩
    rw [positiveLink_translate_translate, add_neg_cancel_left]
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
theorem lift_apply_positive (U : Γ.QuotientField) (b : PositiveLink a) :
    Γ.lift U b.1 = U (Γ.linkClass b) :=
  dif_pos b.2
theorem gaugeField_ext {V W : GaugeField a}
    (h : ∀ b : Link a, b.IsPositivelyOriented → V b = W b) : V = W := by
  refine Subtype.ext (funext fun b => ?_)
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hr := PeriodSublattice.isPositivelyOriented_opposite_of_not hb
    have e₁ : V.1 b = (V.1 b.opposite)⁻¹ := V.2 b.opposite
    have e₂ : W.1 b = (W.1 b.opposite)⁻¹ := W.2 b.opposite
    have e₃ : V.1 b.opposite = W.1 b.opposite := h _ hr
    rw [e₁, e₂, e₃]
def orient (b : Link a) : ComplexMatrix2.specialUnitary → ComplexMatrix2.specialUnitary :=
  open Classical in if b.IsPositivelyOriented then id else fun g => g⁻¹
theorem liftValue_eq_orient (U : Γ.QuotientField) (b : Link a) :
    Γ.liftValue U b = orient b (U (Γ.linkClass (positiveRep b))) := by
  by_cases h : b.IsPositivelyOriented
  · rw [positiveRep_of_pos h]
    simp [PeriodSublattice.liftValue, orient, h]
  · have hr := PeriodSublattice.isPositivelyOriented_opposite_of_not h
    rw [positiveRep_of_not_pos h]
    simp [PeriodSublattice.liftValue, orient, h, hr]
theorem measurable_orient (b : Link a) : Measurable (orient b) := by
  by_cases h : b.IsPositivelyOriented
  · simpa [orient, h] using measurable_id
  · simpa [orient, h] using
      (continuous_inv : Continuous fun g : ComplexMatrix2.specialUnitary => g⁻¹).measurable
theorem haarProb_preimage_orient
    (hInv : ∀ E : Set ComplexMatrix2.specialUnitary, MeasurableSet E →
      ComplexMatrix2.haarProb ((fun g => g⁻¹) ⁻¹' E) = ComplexMatrix2.haarProb E)
    (b : Link a) (E : Set ComplexMatrix2.specialUnitary) (hE : MeasurableSet E) :
    ComplexMatrix2.haarProb (orient b ⁻¹' E) = ComplexMatrix2.haarProb E := by
  by_cases h : b.IsPositivelyOriented
  · simp [orient, h]
  · simpa [orient, h] using hInv E hE
variable (r : LatticeSymmetry a)
def PreservesPeriods : Prop :=
  ∀ γ ∈ Γ.periods, ∃ γ' ∈ Γ.periods, ∀ x : LatticePoint a, r.pointMap (x + γ) = r.pointMap x + γ'
def quotientPullback (U : Γ.QuotientField) : Γ.QuotientField :=
  fun c => Γ.liftValue U (r.linkMap (linkRep Γ c).1)
def quotientLinkMap (c : Γ.QuotientLink) : Γ.QuotientLink :=
  Γ.linkClass (positiveRep (r.linkMap (linkRep Γ c).1))
variable {Γ r}
theorem linkMap_shift {γ γ' : LatticePoint a}
    (h : ∀ x : LatticePoint a, r.pointMap (x + γ) = r.pointMap x + γ')
    (b : Link a) : r.linkMap ((shift γ).linkMap b) = (shift γ').linkMap (r.linkMap b) :=
  Link.ext (h _) (h _)
theorem linkMap_opposite (b : Link a) : r.linkMap b.opposite = (r.linkMap b).opposite := rfl
theorem quotientPullback_linkClass
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    (hK : PreservesPeriods Γ r) (U : Γ.QuotientField) (b : PositiveLink a) :
    quotientPullback Γ r U (Γ.linkClass b) = Γ.liftValue U (r.linkMap b.1) := by
  obtain ⟨γ, hγ, e⟩ := exists_linkRep_eq Γ b
  obtain ⟨γ', hγ', h⟩ := hK γ hγ
  have hb : (b.translate γ).1 = (shift γ).linkMap b.1 := rfl
  have hpv : Γ.liftValue U ((shift γ').linkMap (r.linkMap b.1)) =
      Γ.liftValue U (r.linkMap b.1) :=
    congrFun (congrArg Subtype.val (hper U γ' hγ')) (r.linkMap b.1)
  simp only [quotientPullback]
  rw [e, hb, linkMap_shift h, hpv]
theorem lift_quotientPullback
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    (hK : PreservesPeriods Γ r) (U : Γ.QuotientField) :
    Γ.lift (quotientPullback Γ r U) = r.pullbackField (Γ.lift U) := by
  refine gaugeField_ext fun b hb => ?_
  have h₁ := lift_apply_positive Γ (quotientPullback Γ r U) ⟨b, hb⟩
  have h₂ := quotientPullback_linkClass hper hK U ⟨b, hb⟩
  exact h₁.trans h₂
theorem quotientPullback_eq :
    quotientPullback Γ r = fun U c =>
      orient (r.linkMap (linkRep Γ c).1) (U (quotientLinkMap Γ r c)) :=
  funext fun U => funext fun c => liftValue_eq_orient Γ U _
theorem quotientLinkMap_linkClass (hK : PreservesPeriods Γ r) (b : PositiveLink a) :
    quotientLinkMap Γ r (Γ.linkClass b) = Γ.linkClass (positiveRep (r.linkMap b.1)) := by
  obtain ⟨γ, hγ, e⟩ := exists_linkRep_eq Γ b
  obtain ⟨γ', hγ', h⟩ := hK γ hγ
  have hb : (b.translate γ).1 = (shift γ).linkMap b.1 := rfl
  simp only [quotientLinkMap]
  rw [e, hb, linkMap_shift h, positiveRep_shift, linkClass_translate Γ _ hγ']
theorem linkMap_linkMap_of_isInverse {t : LatticeSymmetry a} (ht : t.IsInverse r) (b : Link a) :
    r.linkMap (t.linkMap b) = b :=
  Link.ext (Subtype.ext (ht.2 _)) (Subtype.ext (ht.2 _))
theorem quotientLinkMap_surjective (hK : PreservesPeriods Γ r) {t : LatticeSymmetry a}
    (ht : t.IsInverse r) : Function.Surjective (quotientLinkMap Γ r) := by
  intro c
  have hc := linkClass_linkRep Γ c
  have hpos := (linkRep Γ c).2
  refine ⟨Γ.linkClass (positiveRep (t.linkMap (linkRep Γ c).1)), ?_⟩
  rw [quotientLinkMap_linkClass hK]
  rcases positiveRep_eq_or (t.linkMap (linkRep Γ c).1) with e | e
  · rw [e, linkMap_linkMap_of_isInverse ht, positiveRep_of_pos hpos]
    exact hc
  · rw [e, linkMap_opposite, linkMap_linkMap_of_isInverse ht, positiveRep_opposite Γ,
      positiveRep_of_pos hpos]
    exact hc
theorem map_quotientPullback_quotientHaar [Finite Γ.QuotientLink]
    (hInv : ∀ E : Set ComplexMatrix2.specialUnitary, MeasurableSet E →
      ComplexMatrix2.haarProb ((fun g => g⁻¹) ⁻¹' E) = ComplexMatrix2.haarProb E)
    (hK : PreservesPeriods Γ r) {t : LatticeSymmetry a} (ht : t.IsInverse r) :
    Γ.quotientHaar.map (quotientPullback Γ r) = Γ.quotientHaar := by
  have hs := quotientLinkMap_surjective hK ht
  have hb : Function.Bijective (quotientLinkMap Γ r) :=
    ⟨Finite.injective_iff_surjective.2 hs, hs⟩
  have h := map_haarPi_perm (Equiv.ofBijective _ hb)
    (fun c => orient (r.linkMap (linkRep Γ c).1))
    (fun _ => measurable_orient _)
    (fun c E hE => haarProb_preimage_orient hInv _ E hE)
  rw [quotientPullback_eq]
  exact h
theorem measurable_quotientPullback : Measurable (quotientPullback Γ r) := by
  rw [quotientPullback_eq]
  exact measurable_pi_lambda _ fun c =>
    (measurable_orient _).comp (measurable_pi_apply _)
def PlaquettesDeterminedByCorners (a : ℝ) : Prop :=
  ∀ (s : LatticeSymmetry a) (p q : ElementaryPlaquette a),
    q = s.plaquetteMap p ↔ q.cornerSet = s.pointMap '' p.cornerSet
theorem cornerSet_plaquetteMap (hc : PlaquettesDeterminedByCorners a) (s : LatticeSymmetry a)
    (p : ElementaryPlaquette a) : (s.plaquetteMap p).cornerSet = s.pointMap '' p.cornerSet :=
  (hc s p _).1 rfl
theorem shift_plaquetteMap_plaquetteMap (hc : PlaquettesDeterminedByCorners a)
    (γ δ : LatticePoint a) (q : ElementaryPlaquette a) :
    (shift δ).plaquetteMap ((shift γ).plaquetteMap q) =
      (shift (γ + δ)).plaquetteMap q := by
  refine (hc _ _ _).2 ?_
  rw [cornerSet_plaquetteMap hc, cornerSet_plaquetteMap hc, image_image]
  refine image_congr fun x _ => Subtype.ext ?_
  exact add_assoc _ _ _
theorem shift_zero_plaquetteMap (hc : PlaquettesDeterminedByCorners a)
    (q : ElementaryPlaquette a) : (shift (0 : LatticePoint a)).plaquetteMap q = q := by
  refine ((hc _ _ _).2 ?_).symm
  have h : (shift (0 : LatticePoint a)).pointMap = id :=
    funext fun x => Subtype.ext (add_zero _)
  rw [h, image_id]
theorem plaquetteMap_shift (hc : PlaquettesDeterminedByCorners a) {γ γ' : LatticePoint a}
    (h : ∀ x : LatticePoint a, r.pointMap (x + γ) = r.pointMap x + γ')
    (q : ElementaryPlaquette a) :
    r.plaquetteMap ((shift γ).plaquetteMap q) =
      (shift γ').plaquetteMap (r.plaquetteMap q) := by
  refine ((hc _ _ _).2 ?_).symm
  rw [cornerSet_plaquetteMap hc, cornerSet_plaquetteMap hc, cornerSet_plaquetteMap hc,
    image_image, image_image]
  exact image_congr fun x _ => (h x).symm
variable (Γ) in
def plaquetteClass (q : ElementaryPlaquette a) : Γ.QuotientPlaquette :=
  ⟨Γ.plaquetteOrbit q, q, rfl⟩
theorem plaquetteOrbit_shift (hc : PlaquettesDeterminedByCorners a) {γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) (q : ElementaryPlaquette a) :
    Γ.plaquetteOrbit ((shift γ).plaquetteMap q) = Γ.plaquetteOrbit q := by
  refine Set.ext fun q' => ⟨?_, ?_⟩
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨γ + δ, add_mem hγ hδ, shift_plaquetteMap_plaquetteMap hc γ δ q⟩
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨-γ + δ, add_mem (neg_mem hγ) hδ, ?_⟩
    rw [shift_plaquetteMap_plaquetteMap hc, add_neg_cancel_left]
theorem mem_plaquetteOrbit_self (hc : PlaquettesDeterminedByCorners a)
    (q : ElementaryPlaquette a) : q ∈ Γ.plaquetteOrbit q :=
  ⟨0, zero_mem _, (shift_zero_plaquetteMap hc q).symm⟩
variable (Γ) in
def plaquetteRep (p : Γ.QuotientPlaquette) : ElementaryPlaquette a :=
  (Γ.quotientPlaquette_nonempty p).some
theorem plaquetteRep_mem (p : Γ.QuotientPlaquette) :
    plaquetteRep Γ p ∈ (p : Set (ElementaryPlaquette a)) :=
  (Γ.quotientPlaquette_nonempty p).some_mem
theorem eq_plaquetteClass_of_mem (hc : PlaquettesDeterminedByCorners a)
    (p : Γ.QuotientPlaquette) {q : ElementaryPlaquette a}
    (hq : q ∈ (p : Set (ElementaryPlaquette a))) : plaquetteClass Γ q = p := by
  obtain ⟨_, q₀, rfl⟩ := p
  obtain ⟨γ, hγ, rfl⟩ := hq
  exact Subtype.ext (plaquetteOrbit_shift hc hγ q₀)
variable (Γ r) in
def quotientPlaquetteMap (p : Γ.QuotientPlaquette) : Γ.QuotientPlaquette :=
  plaquetteClass Γ (r.plaquetteMap (plaquetteRep Γ p))
theorem quotientPlaquetteMap_plaquetteClass (hc : PlaquettesDeterminedByCorners a)
    (hK : PreservesPeriods Γ r) (q : ElementaryPlaquette a) :
    quotientPlaquetteMap Γ r (plaquetteClass Γ q) = plaquetteClass Γ (r.plaquetteMap q) := by
  obtain ⟨γ, hγ, e⟩ : plaquetteRep Γ (plaquetteClass Γ q) ∈ Γ.plaquetteOrbit q :=
    plaquetteRep_mem (plaquetteClass Γ q)
  obtain ⟨γ', hγ', h⟩ := hK γ hγ
  simp only [quotientPlaquetteMap]
  rw [e, plaquetteMap_shift hc h]
  exact Subtype.ext (plaquetteOrbit_shift hc hγ' _)
theorem quotientPlaquetteMap_surjective (hc : PlaquettesDeterminedByCorners a)
    (hK : PreservesPeriods Γ r) {t : LatticeSymmetry a}
    (hright : Function.RightInverse t.plaquetteMap r.plaquetteMap) :
    Function.Surjective (quotientPlaquetteMap Γ r) := by
  intro p
  refine ⟨plaquetteClass Γ (t.plaquetteMap (plaquetteRep Γ p)), ?_⟩
  rw [quotientPlaquetteMap_plaquetteClass hc hK, hright]
  exact eq_plaquetteClass_of_mem hc p (plaquetteRep_mem p)
theorem quotientFaceEnergy_quotientPullback (hc : PlaquettesDeterminedByCorners a)
    (hper : ∀ (U : Γ.QuotientField), ∀ γ ∈ Γ.periods,
      (shift γ).pullbackField (Γ.lift U) = Γ.lift U)
    (hwell : ∀ (U : Γ.QuotientField) (p : Γ.QuotientPlaquette),
      ∀ q ∈ (p : Set (ElementaryPlaquette a)), ∀ q' ∈ (p : Set (ElementaryPlaquette a)),
        faceEnergy (Γ.lift U) q = faceEnergy (Γ.lift U) q')
    (hmove : ∀ p : ElementaryPlaquette a,
      r.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (r.plaquetteMap p))
    (hK : PreservesPeriods Γ r) (U : Γ.QuotientField) (p : Γ.QuotientPlaquette) :
    Γ.quotientFaceEnergy (quotientPullback Γ r U) p =
      Γ.quotientFaceEnergy U (quotientPlaquetteMap Γ r p) := by
  have h₁ : Γ.quotientFaceEnergy (quotientPullback Γ r U) p =
      faceEnergy (Γ.lift (quotientPullback Γ r U)) (plaquetteRep Γ p) := rfl
  have h₂ : Γ.quotientFaceEnergy U (quotientPlaquetteMap Γ r p) =
      faceEnergy (Γ.lift U) (plaquetteRep Γ (quotientPlaquetteMap Γ r p)) := rfl
  have h₃ := congrFun (hmove (plaquetteRep Γ p)) (Γ.lift U)
  have h₄ : faceEnergy (r.pullbackField (Γ.lift U)) (plaquetteRep Γ p) =
      faceEnergy (Γ.lift U) (r.plaquetteMap (plaquetteRep Γ p)) := h₃
  rw [h₁, h₂, lift_quotientPullback hper hK, h₄]
  exact hwell U (quotientPlaquetteMap Γ r p) _ (mem_plaquetteOrbit_self hc _) _
    (plaquetteRep_mem _)
theorem continuous_boltzmannWeight [Finite Γ.QuotientPlaquette] (β : ℝ)
    (hcont : ∀ p : Γ.QuotientPlaquette, Continuous fun U => Γ.quotientFaceEnergy U p) :
    Continuous (Γ.boltzmannWeight β) := by
  haveI := Fintype.ofFinite Γ.QuotientPlaquette
  have h : Γ.boltzmannWeight β = fun U => Real.exp (-β * ∑ p, Γ.quotientFaceEnergy U p) :=
    funext fun U => by
      simp only [PeriodSublattice.boltzmannWeight]
      rw [finsum_eq_sum_of_fintype]
  rw [h]
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_finsetSum _ fun p _ => hcont p))
theorem boltzmannWeight_quotientPullback (β : ℝ)
    (hb : Function.Bijective (quotientPlaquetteMap Γ r))
    (h : ∀ (U : Γ.QuotientField) (p : Γ.QuotientPlaquette),
      Γ.quotientFaceEnergy (quotientPullback Γ r U) p =
        Γ.quotientFaceEnergy U (quotientPlaquetteMap Γ r p))
    (U : Γ.QuotientField) :
    Γ.boltzmannWeight β (quotientPullback Γ r U) = Γ.boltzmannWeight β U := by
  have hs : ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy (quotientPullback Γ r U) p =
      ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p :=
    (finsum_congr (h U)).trans
      (finsum_comp_equiv (f := fun p => Γ.quotientFaceEnergy U p) (Equiv.ofBijective _ hb))
  simp only [PeriodSublattice.boltzmannWeight]
  rw [hs]
theorem map_gibbsMeasure (β : ℝ) {T : Γ.QuotientField → Γ.QuotientField}
    (hT : Measurable T) (hmap : Γ.quotientHaar.map T = Γ.quotientHaar)
    (hw : Measurable (Γ.boltzmannWeight β))
    (hwT : ∀ U, Γ.boltzmannWeight β (T U) = Γ.boltzmannWeight β U) :
    (Γ.gibbsMeasure β).map T = Γ.gibbsMeasure β := by
  have hd : Measurable fun U => ENNReal.ofReal (Γ.boltzmannWeight β U) :=
    ENNReal.measurable_ofReal.comp hw
  have hkey : (Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (Γ.boltzmannWeight β U)).map T =
      Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (Γ.boltzmannWeight β U) := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs,
      ← lintegral_indicator (hT hs), ← lintegral_indicator hs]
    calc ∫⁻ U, (T ⁻¹' s).indicator (fun U => ENNReal.ofReal (Γ.boltzmannWeight β U)) U
          ∂Γ.quotientHaar
        = ∫⁻ U, s.indicator (fun U => ENNReal.ofReal (Γ.boltzmannWeight β U)) (T U)
            ∂Γ.quotientHaar := by
          refine lintegral_congr fun U => ?_
          by_cases hU : T U ∈ s
          · simp [Set.indicator, hU, hwT]
          · simp [Set.indicator, hU]
      _ = ∫⁻ U, s.indicator (fun U => ENNReal.ofReal (Γ.boltzmannWeight β U)) U
            ∂(Γ.quotientHaar.map T) := (lintegral_map (hd.indicator hs) hT).symm
      _ = _ := by rw [hmap]
  simp only [PeriodSublattice.gibbsMeasure]
  rw [Measure.map_smul, hkey]
end PeriodicGibbsInvariance
open PeriodicGibbsInvariance in
theorem periodicGibbsSymmetricUnderPeriodPreservingMotions_holds
    (hFinite : PeriodQuotientFinite)
    (hExtension : PeriodicLiftAndQuotientEnergiesStatement)
    (hStates : PeriodicGibbsMeasuresAreStates)
    (hAction : SymmetriesAsMotions.Statement)
    (hHaar : PeriodicLattice.HaarAndWilsonInvariance) :
    PeriodicGibbsSymmetricUnderPeriodPreservingMotions := by
  intro a β ha hβ Γ r R hR v hv hΓ
  have : SecondCountableTopology ComplexMatrix2.specialUnitary :=
    have : SecondCountableTopology ComplexMatrix2 :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨-, hLinks, hPlaquettes⟩ := hFinite a ha Γ
  obtain ⟨⟨hper, hcontLift, hwell, hact⟩, -⟩ := hExtension a ha Γ
  obtain ⟨-, -, -, -, hint, -⟩ := hStates a β ha hβ Γ
  have hc : PlaquettesDeterminedByCorners a := fun s p q =>
    ((hAction a ha s s).2.2.2.1).1 p q
  have hK : PreservesPeriods Γ r := by
    intro γ hγ
    have hmem : R (γ : AmbientSpace) ∈ R '' (Subtype.val '' (Γ.periods : Set (LatticePoint a))) :=
      ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    rw [hΓ] at hmem
    obtain ⟨γ', hγ', e⟩ := hmem
    refine ⟨γ', hγ', fun x => Subtype.ext ?_⟩
    change r.toFun ((x : AmbientSpace) + (γ : AmbientSpace)) =
      r.toFun (x : AmbientSpace) + (γ' : AmbientSpace)
    rw [hv, hv, map_add, e]
    abel
  obtain ⟨t, ht⟩ := ((hAction a ha r r).2.1).2
  have hright := ((((hAction a ha r r).2.2.2.1).2.2.1) t ht).2
  have hmove : ∀ p : ElementaryPlaquette a,
      r.actOn (fun U : GaugeField a => faceEnergy U p) =
        fun U : GaugeField a => faceEnergy U (r.plaquetteMap p) :=
    fun p => ((hAction a ha r r).2.2.2.2.2.2.1 p).2
  have hInv : ∀ E : Set ComplexMatrix2.specialUnitary, MeasurableSet E →
      ComplexMatrix2.haarProb ((fun g => g⁻¹) ⁻¹' E) = ComplexMatrix2.haarProb E :=
    fun E hE => (hHaar.2.1 E hE).1
  have hT := measurable_quotientPullback (Γ := Γ) (r := r)
  have hps := quotientPlaquetteMap_surjective (Γ := Γ) hc hK hright
  have hpb : Function.Bijective (quotientPlaquetteMap Γ r) :=
    ⟨Finite.injective_iff_surjective.2 hps, hps⟩
  have hwT := boltzmannWeight_quotientPullback β hpb
    (quotientFaceEnergy_quotientPullback hc hper hwell hmove hK)
  have hw : Measurable (Γ.boltzmannWeight β) :=
    (continuous_boltzmannWeight β fun p => (hact p).1).measurable
  have hmap := map_gibbsMeasure β hT (map_quotientPullback_quotientHaar hInv hK ht) hw hwT
  intro A hA
  have hO : IsBoundedObservable (r.actOn A) :=
    (((hAction a ha r r).2.2.2.2.2.1).2 A A hA hA).1
  rw [hint _ hO, hint A hA]
  have hper' : ∀ U, Γ.periodize (r.actOn A) U = Γ.periodize A (quotientPullback Γ r U) :=
    fun U => by
      simp only [PeriodSublattice.periodize]
      rw [lift_quotientPullback hper hK]
      rfl
  have hm : Measurable (Γ.periodize A) := hA.1.comp hcontLift.measurable
  simp only [hper']
  conv_rhs => rw [← hmap]
  exact (integral_map hT.aemeasurable hm.aestronglyMeasurable).symm
end YangMills.Construction.InfiniteLattice
