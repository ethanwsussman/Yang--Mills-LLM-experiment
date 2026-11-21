import YangMills.Construction.InfiniteLattice.DilationToSpacingOneProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfTheWilsonMeasureIsInvariantUnderMotionsKeepingThePeriodsProof
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.InfiniteLattice.ConfigurationsOfTheTorusLatticeAtPositiveLinks
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.InfiniteLattice.CubicTorusOfACutoffIsAPeriodicExtension
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacing
import YangMills.Construction.InfiniteLattice.ImageOfThePullbackAndLimitsOfThePeriodicExtensions
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndCopies
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CubicTorusAtCutoffLifts
theorem withDensity_map_eq_map_withDensity_comp {α γ : Type*} [MeasurableSpace α]
    [MeasurableSpace γ] (μ : Measure α) {φ : α → γ} (hφ : Measurable φ) {f : γ → ℝ≥0∞}
    (hf : Measurable f) :
    (μ.map φ).withDensity f = (μ.withDensity (f ∘ φ)).map φ := by
  ext E hE
  rw [withDensity_apply _ hE, Measure.map_apply hφ hE, withDensity_apply _ (hφ hE),
    ← lintegral_indicator hE, lintegral_map (hf.indicator hE) hφ, ← lintegral_indicator (hφ hE)]
  rfl
section Orbits
variable {a : ℝ}
def shiftFace (p : ElementaryPlaquette a) (γ : LatticePoint a) : ElementaryPlaquette a :=
  ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem plaquetteMap_shift (ha : 0 < a) (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    (shift γ).plaquetteMap p = shiftFace p γ := by apply _root_.YangMills.Construction.UnitSpacing.plaquetteMap_shift <;> assumption
theorem positiveLink_translate_translate (b : PositiveLink a) (γ δ : LatticePoint a) :
    (b.translate γ).translate δ = b.translate (γ + δ) :=
  Subtype.ext (Link.ext (add_assoc _ _ _) (add_assoc _ _ _))
variable (Γ : PeriodSublattice a)
theorem linkOrbit_eq_of_mem {b b' : PositiveLink a} (h : b' ∈ Γ.linkOrbit b) :
    Γ.linkOrbit b' = Γ.linkOrbit b := by
  obtain ⟨γ, hγ, rfl⟩ := h
  ext c
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨γ + δ, add_mem hγ hδ, positiveLink_translate_translate b γ δ⟩
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨-γ + δ, add_mem (neg_mem hγ) hδ, ?_⟩
    rw [positiveLink_translate_translate, add_neg_cancel_left]
theorem linkRep_mem (c : Γ.QuotientLink) :
    Γ.linkRep c ∈ (c : Set (PositiveLink a)) :=
  (Γ.quotientLink_nonempty c).some_mem
theorem linkClass_linkRep (c : Γ.QuotientLink) : Γ.linkClass (Γ.linkRep c) = c := by
  obtain ⟨_, b, rfl⟩ := c
  exact Subtype.ext (linkOrbit_eq_of_mem Γ (linkRep_mem Γ ⟨_, b, rfl⟩))
def faceRep (q : Γ.QuotientPlaquette) : ElementaryPlaquette a :=
  (Γ.quotientPlaquette_nonempty q).some
theorem faceRep_mem (q : Γ.QuotientPlaquette) :
    faceRep Γ q ∈ (q : Set (ElementaryPlaquette a)) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.plaquetteRep_mem <;> assumption
theorem plaquetteOrbit_eq_of_mem (ha : 0 < a) {p p' : ElementaryPlaquette a}
    (h : p' ∈ Γ.plaquetteOrbit p) :
    Γ.plaquetteOrbit p' = Γ.plaquetteOrbit p := by
  obtain ⟨γ, hγ, rfl⟩ := h
  ext q
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨γ + δ, add_mem hγ hδ, ?_⟩
    simp only [plaquetteMap_shift ha, shiftFace, add_assoc]
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨-γ + δ, add_mem (neg_mem hγ) hδ, ?_⟩
    simp only [plaquetteMap_shift ha, shiftFace]
    exact ElementaryPlaquette.ext (by simp only [add_assoc, add_neg_cancel_left]) rfl rfl
theorem faceClass_faceRep (ha : 0 < a) (q : Γ.QuotientPlaquette) :
    Γ.faceClass (faceRep Γ q) = q := by
  obtain ⟨_, p, rfl⟩ := q
  exact Subtype.ext (plaquetteOrbit_eq_of_mem Γ ha (faceRep_mem Γ ⟨_, p, rfl⟩))
theorem continuous_lift : Continuous Γ.lift := by
  refine Continuous.subtype_mk (continuous_pi fun b => ?_) _
  unfold PeriodSublattice.liftValue
  by_cases h : b.IsPositivelyOriented
  · simp only [dif_pos h]
    exact continuous_apply _
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      exact continuous_inv.comp (continuous_apply _)
    · simp only [dif_neg h, dif_neg h']
      exact continuous_const
end Orbits
section Values
variable {L m : ℕ} {j : ℤ}
theorem gaugeFieldOfPositive_mem (hL : 2 ≤ L) (hj : -(m : ℤ) < j)
    (v : PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) :
    PeriodicLattice.gaugeFieldOfPositive v ∈ PeriodicLattice.compactGaugeFields L m j := by
  classical
  let f : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2.specialUnitary := fun b =>
    if h : b.IsPositivelyOriented then v ⟨b, h⟩
    else if h' : b.opposite.IsPositivelyOriented then (v ⟨b.opposite, h'⟩)⁻¹ else 1
  have hf : ∀ b, (f b : Matrices.ComplexMatrix2) = PeriodicLattice.gaugeFieldOfPositive v b := by
    intro b
    simp only [f, PeriodicLattice.gaugeFieldOfPositive]
    split_ifs
    · rfl
    · exact specialUnitary_coe_inv _
    · rfl
  have hrev : ∀ b, f b.opposite = (f b)⁻¹ := by
    intro b
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with h | h
    · have h₂ : b.opposite.opposite.IsPositivelyOriented := h.1
      simp only [f, dif_pos h.1, dif_neg h.2, dif_pos h₂]
      rfl
    · have h₂ : ¬b.opposite.opposite.IsPositivelyOriented := h.2
      simp only [f, dif_pos h.1, dif_neg h.2, inv_inv]
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rw [← hf]
    exact (f b).2
  · rw [← hf, ← hf, hrev, specialUnitary_coe_inv]
theorem measurable_gaugeFieldOfPositive :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem measurable_boltzmannWeight [Finite (PeriodicLattice.Plaquette L m j)] (β : ℝ) :
    Measurable (PeriodicLattice.boltzmannWeight β :
      (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) → ℝ) := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.boltzmannWeight_measurable <;> assumption
end Values
section Covering
variable {L m : ℕ} {j : ℤ}
def projectPositive (b : PositiveLink (PeriodicLattice.meshSize L j)) :
    PeriodicLattice.PositivelyOrientedBond L m j :=
  ⟨projectLink L m j b.1, by
    obtain ⟨μ, h⟩ := b.2
    refine ⟨μ, ?_⟩
    change projectPoint L m j b.1.terminal - projectPoint L m j b.1.initial = _
    rw [← projectPoint_sub, h, projectPoint_axisStep]⟩
structure CoversPeriodicLattice (Γ : PeriodSublattice (PeriodicLattice.meshSize L j)) : Prop where
  fiber : ∀ x y : LatticePoint (PeriodicLattice.meshSize L j),
    projectPoint L m j x = projectPoint L m j y ↔ x - y ∈ Γ.periods
  forwardFrom_injOn : InjOn
    (fun q : PeriodicLattice.Site L m j × Fin 4 => PeriodicLattice.Bond.forwardFrom q.1 q.2) univ
  positive_surj : ∀ c : PeriodicLattice.PositivelyOrientedBond L m j, ∃ b, projectPositive b = c
  plaquette_surj : Function.Surjective (TorusLifts.projectPlaquette L m j)
  energy : ∀ (U : PeriodicLattice.CompactGaugeField L m j)
    (p : ElementaryPlaquette (PeriodicLattice.meshSize L j)), faceEnergy (liftCompactField U) p =
      PeriodicLattice.plaquetteCost U.1 (TorusLifts.projectPlaquette L m j p)
  compact : ∀ v : PeriodicLattice.PositivelyOrientedBond L m j →
      Matrices.ComplexMatrix2.specialUnitary,
    PeriodicLattice.gaugeFieldOfPositive v ∈ PeriodicLattice.compactGaugeFields L m j
variable {Γ : PeriodSublattice (PeriodicLattice.meshSize L j)}
theorem CoversPeriodicLattice.projectPoint_add (F : CoversPeriodicLattice (m := m) Γ)
    (x : LatticePoint (PeriodicLattice.meshSize L j)) {γ : LatticePoint (PeriodicLattice.meshSize L j)}
    (hγ : γ ∈ Γ.periods) : projectPoint L m j (x + γ) = projectPoint L m j x :=
  (F.fiber _ _).2 (by simpa using hγ)
theorem CoversPeriodicLattice.projectPositive_eq_iff (F : CoversPeriodicLattice (m := m) Γ)
    {b b' : PositiveLink (PeriodicLattice.meshSize L j)} :
    (projectPositive b : PeriodicLattice.PositivelyOrientedBond L m j) = projectPositive b' ↔
      b' ∈ Γ.linkOrbit b := by
  constructor
  · intro h
    obtain ⟨μ, hμ⟩ := b.2
    obtain ⟨μ', hμ'⟩ := b'.2
    have hc : projectLink L m j b.1 = projectLink L m j b'.1 := congrArg Subtype.val h
    have e : ∀ (c : Link (PeriodicLattice.meshSize L j)) (ν : Fin 4),
        c.terminal - c.initial = axisStep _ ν → projectLink L m j c =
          PeriodicLattice.Bond.forwardFrom (projectPoint L m j c.initial) ν := by
      intro c ν hcν
      refine PeriodicLattice.Bond.ext rfl ?_
      change projectPoint L m j c.terminal =
        projectPoint L m j c.initial + PeriodicLattice.unitStep L m j ν
      rw [← projectPoint_axisStep, ← sub_eq_iff_eq_add', ← projectPoint_sub, hcν]
    have hq := F.forwardFrom_injOn (mem_univ (projectPoint L m j b.1.initial, μ))
      (mem_univ (projectPoint L m j b'.1.initial, μ')) (by
        change PeriodicLattice.Bond.forwardFrom _ _ = PeriodicLattice.Bond.forwardFrom _ _
        rw [← e _ _ hμ, ← e _ _ hμ', hc])
    have ht : projectPoint L m j b'.1.initial = projectPoint L m j b.1.initial :=
      (congrArg Prod.fst hq).symm
    have hd : μ = μ' := congrArg Prod.snd hq
    subst hd
    refine ⟨b'.1.initial - b.1.initial, (F.fiber _ _).1 ht, Subtype.ext (Link.ext ?_ ?_)⟩
    · change b'.1.initial = b.1.initial + (b'.1.initial - b.1.initial)
      abel
    · change b'.1.terminal = b.1.terminal + (b'.1.initial - b.1.initial)
      rw [eq_add_of_sub_eq hμ', eq_add_of_sub_eq hμ]
      abel
  · rintro ⟨γ, hγ, rfl⟩
    exact Subtype.ext (PeriodicLattice.Bond.ext (F.projectPoint_add _ hγ).symm
      (F.projectPoint_add _ hγ).symm)
def CoversPeriodicLattice.linkEquiv (F : CoversPeriodicLattice (m := m) Γ) :
    Γ.QuotientLink ≃ PeriodicLattice.PositivelyOrientedBond L m j :=
  Equiv.ofBijective (fun c => projectPositive (Γ.linkRep c)) (by
    constructor
    · intro c c' h
      have ho := linkOrbit_eq_of_mem Γ (F.projectPositive_eq_iff.1 h)
      rw [← linkClass_linkRep Γ c, ← linkClass_linkRep Γ c']
      exact Subtype.ext ho.symm
    · intro l
      obtain ⟨b, rfl⟩ := F.positive_surj l
      exact ⟨Γ.linkClass b,
        (F.projectPositive_eq_iff.2 (linkRep_mem Γ (Γ.linkClass b))).symm⟩)
theorem CoversPeriodicLattice.linkEquiv_linkClass (F : CoversPeriodicLattice (m := m) Γ)
    (b : PositiveLink (PeriodicLattice.meshSize L j)) :
    F.linkEquiv (Γ.linkClass b) = projectPositive b :=
  (F.projectPositive_eq_iff.2 (linkRep_mem Γ (Γ.linkClass b))).symm
theorem CoversPeriodicLattice.projectPlaquette_eq_iff (F : CoversPeriodicLattice (m := m) Γ)
    (ha : 0 < PeriodicLattice.meshSize L j)
    {p p' : ElementaryPlaquette (PeriodicLattice.meshSize L j)} :
    TorusLifts.projectPlaquette L m j p = TorusLifts.projectPlaquette L m j p' ↔
      p' ∈ Γ.plaquetteOrbit p := by
  constructor
  · intro h
    have hb : projectPoint L m j p'.corner = projectPoint L m j p.corner :=
      (congrArg PeriodicLattice.Plaquette.origin h).symm
    refine ⟨p'.corner - p.corner, (F.fiber _ _).1 hb, ?_⟩
    rw [plaquetteMap_shift ha]
    exact ElementaryPlaquette.ext (by simp [shiftFace])
      (congrArg PeriodicLattice.Plaquette.firstAxis h).symm
      (congrArg PeriodicLattice.Plaquette.secondAxis h).symm
  · rintro ⟨γ, hγ, rfl⟩
    rw [plaquetteMap_shift ha]
    simp only [TorusLifts.projectPlaquette, shiftFace, F.projectPoint_add _ hγ]
theorem CoversPeriodicLattice.bijective_projectFaceRep (F : CoversPeriodicLattice (m := m) Γ)
    (ha : 0 < PeriodicLattice.meshSize L j) :
    Function.Bijective fun q : Γ.QuotientPlaquette =>
      TorusLifts.projectPlaquette L m j (faceRep Γ q) := by
  constructor
  · intro q q' h
    have ho := plaquetteOrbit_eq_of_mem Γ ha ((F.projectPlaquette_eq_iff ha).1 h)
    rw [← faceClass_faceRep Γ ha q, ← faceClass_faceRep Γ ha q']
    exact Subtype.ext ho.symm
  · intro P
    obtain ⟨p, rfl⟩ := F.plaquette_surj P
    exact ⟨Γ.faceClass p,
      ((F.projectPlaquette_eq_iff ha).2 (faceRep_mem Γ (Γ.faceClass p))).symm⟩
theorem CoversPeriodicLattice.liftField_eq (F : CoversPeriodicLattice (m := m) Γ)
    (v : PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) :
    liftField L m j (PeriodicLattice.gaugeFieldOfPositive v) =
      Γ.lift fun c => v (F.linkEquiv c) := by
  have key : ∀ b : Link (PeriodicLattice.meshSize L j), b.IsPositivelyOriented →
      liftField L m j (PeriodicLattice.gaugeFieldOfPositive v) b =
        Γ.lift (fun c => v (F.linkEquiv c)) b := by
    intro b h
    refine Subtype.ext ?_
    rw [liftField_apply_of_mem (F.compact v) b]
    have hc : (projectLink L m j b).IsPositivelyOriented := (projectPositive (m := m) ⟨b, h⟩).2
    have e : Γ.lift (fun c => v (F.linkEquiv c)) b = v (projectPositive ⟨b, h⟩) := by
      change Γ.liftValue (fun c => v (F.linkEquiv c)) b = _
      unfold PeriodSublattice.liftValue
      rw [dif_pos h]
      exact congrArg v (F.linkEquiv_linkClass _)
    rw [e]
    unfold PeriodicLattice.gaugeFieldOfPositive
    rw [dif_pos hc]
    rfl
  refine Subtype.ext (funext fun b => ?_)
  by_cases h : b.IsPositivelyOriented
  · exact key b h
  · have hr := PeriodSublattice.isPositivelyOriented_opposite_of_not h
    have e₁ := (liftField L m j (PeriodicLattice.gaugeFieldOfPositive v)).2 b.opposite
    have e₂ := (Γ.lift fun c => v (F.linkEquiv c)).2 b.opposite
    exact e₁.trans ((congrArg _ (key _ hr)).trans e₂.symm)
theorem CoversPeriodicLattice.boltzmannWeight_eq (F : CoversPeriodicLattice (m := m) Γ)
    (ha : 0 < PeriodicLattice.meshSize L j) (β : ℝ)
    (v : PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) :
    PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) =
      Γ.boltzmannWeight β fun c => v (F.linkEquiv c) := by
  unfold PeriodicLattice.boltzmannWeight PeriodSublattice.boltzmannWeight
    PeriodicLattice.wilsonAction
  rw [← finsum_comp (g := fun P => PeriodicLattice.plaquetteCost
    (PeriodicLattice.gaugeFieldOfPositive v) P) _ (F.bijective_projectFaceRep ha)]
  refine congrArg _ (congrArg _ (finsum_congr fun q => ?_))
  have h := F.energy ⟨_, F.compact v⟩ (faceRep Γ q)
  have he : liftCompactField
      (⟨_, F.compact v⟩ : PeriodicLattice.CompactGaugeField L m j) =
      Γ.lift fun c => v (F.linkEquiv c) := F.liftField_eq v
  rw [he] at h
  exact h.symm
end Covering
section Measures
variable {L m K : ℕ} {Γ : PeriodSublattice (PeriodicLattice.meshSize L (K : ℤ))}
theorem CoversPeriodicLattice.liftedWilsonMeasure_eq
    [Finite (PeriodicLattice.Plaquette L m (K : ℤ))]
    (F : CoversPeriodicLattice (m := m) Γ) (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) (β : ℝ) :
    liftedWilsonMeasure L m K β = Γ.liftedGibbsMeasure β := by
  let R : (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) →
      Matrices.ComplexMatrix2.specialUnitary) ≃ᵐ Γ.QuotientField :=
    MeasurableEquiv.piCongrLeft (fun _ : Γ.QuotientLink => Matrices.ComplexMatrix2.specialUnitary)
      F.linkEquiv.symm
  have hRapp : ∀ v c, R v c = v (F.linkEquiv c) := by
    intro v c
    have h := Equiv.piCongrLeft_apply_apply
      (fun _ : Γ.QuotientLink => Matrices.ComplexMatrix2.specialUnitary) F.linkEquiv.symm v
      (F.linkEquiv c)
    simpa [R, MeasurableEquiv.coe_piCongrLeft] using h
  have hRfun : ∀ v, (R v) = fun c => v (F.linkEquiv c) := fun v => funext (hRapp v)
  have hR : (Matrices.ComplexMatrix2.haarPi
      (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ))).map R = Γ.quotientHaar :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun _ : Γ.QuotientLink => Matrices.ComplexMatrix2.haarProb) F.linkEquiv.symm
  have hΦ := measurable_gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))
  have hb := measurable_boltzmannWeight (L := L) (m := m) (j := (K : ℤ)) β
  have hP := measurable_liftField L m (K : ℤ)
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology
      (Matrices.ComplexMatrix2.specialUnitary : Set Matrices.ComplexMatrix2)
  have hE : Measurable Γ.lift := (continuous_lift Γ).measurable
  have hF : ∀ v, liftField L m (K : ℤ) (PeriodicLattice.gaugeFieldOfPositive v) =
      Γ.lift (R v) := fun v => by
    rw [hRfun]
    exact F.liftField_eq v
  have hW : ∀ v, PeriodicLattice.boltzmannWeight β (PeriodicLattice.gaugeFieldOfPositive v) =
      Γ.boltzmannWeight β (R v) := fun v => by
    rw [hRfun]
    exact F.boltzmannWeight_eq ha β v
  have hZ : PeriodicLattice.partitionFunction L m K β = Γ.partitionFunction β := by
    unfold PeriodicLattice.partitionFunction PeriodSublattice.partitionFunction
    rw [PeriodicLattice.productHaarMeasure, integral_map hΦ.aemeasurable hb.aestronglyMeasurable,
      ← hR, integral_map_equiv]
    exact integral_congr_ae (ae_of_all _ hW)
  have hwm : Measurable fun U : Γ.QuotientField => ENNReal.ofReal (Γ.boltzmannWeight β U) := by
    have e : (fun U : Γ.QuotientField => ENNReal.ofReal (Γ.boltzmannWeight β U)) =
        fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β
          (PeriodicLattice.gaugeFieldOfPositive (R.symm U))) := by
      funext U
      rw [hW, R.apply_symm_apply]
    rw [e]
    exact ((hb.comp hΦ).comp R.symm.measurable).ennreal_ofReal
  have hD₁ := withDensity_map_eq_map_withDensity_comp
    (Matrices.ComplexMatrix2.haarPi (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ))) hΦ
    hb.ennreal_ofReal
  have hD₂ := withDensity_map_eq_map_withDensity_comp
    (Matrices.ComplexMatrix2.haarPi (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ)))
    R.measurable hwm
  rw [hR] at hD₂
  have hsame : ((fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U)) ∘
      (PeriodicLattice.gaugeFieldOfPositive :
        (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) →
          Matrices.ComplexMatrix2.specialUnitary) → _)) =
      (fun U : Γ.QuotientField => ENNReal.ofReal (Γ.boltzmannWeight β U)) ∘ R := by
    funext v
    simp only [Function.comp_apply, hW]
  unfold liftedWilsonMeasure PeriodicLattice.wilsonGibbsMeasure PeriodSublattice.liftedGibbsMeasure
    PeriodSublattice.gibbsMeasure
  rw [hZ, Measure.map_smul, Measure.map_smul, PeriodicLattice.productHaarMeasure]
  congr 1
  change Measure.map _ ((Measure.map _ (Matrices.ComplexMatrix2.haarPi _)).withDensity _) =
    Measure.map _ (Γ.quotientHaar.withDensity _)
  rw [hD₁, hD₂, hsame, Measure.map_map hP hΦ, Measure.map_map hE R.measurable]
  congr 1
  funext v
  exact hF v
end Measures
section Cubic
variable (d : Conventions.StandingParameters)
theorem one_lt_L : (1 : ℝ) < d.L := by
  have h13 := d.isAdmissible.2
  exact_mod_cast (by omega : 1 < d.L)
theorem meshSize_pos : 0 < PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ) := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.meshSize_pos <;> assumption
theorem meshSize_le_one : PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ) ≤ 1 := by
  unfold PeriodicLattice.meshSize
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (one_lt_L d).le)
theorem three_le_side : 3 ≤ d.side := by
  have h : (d.L : ℝ) ≤ (d.L : ℝ) ^ (d.m : ℕ) := le_self_pow₀ (one_lt_L d).le d.m.ne_zero
  have h13 : (13 : ℝ) ≤ d.L := by exact_mod_cast d.isAdmissible.2
  have hs : d.side = 2 * (d.L : ℝ) ^ (d.m : ℕ) := rfl
  rw [hs]
  linarith
theorem side_eq_mul_meshSize : d.side = 2 * (d.L : ℝ) ^ ((d.m : ℕ) + (d.K : ℕ)) *
    PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ) :=
  (div_eq_iff (meshSize_pos d).ne').1 (PeriodicLattice.pointsPerAxis_eq d.L d.m d.K)
theorem latticeSubgroup_side_le :
    latticeSubgroup d.side ≤ latticeSubgroup (PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ)) := by
  rintro x ⟨n, hn⟩
  refine ⟨fun μ => n μ * (2 * (d.L : ℤ) ^ ((d.m : ℕ) + (d.K : ℕ))), fun μ => ?_⟩
  rw [hn, side_eq_mul_meshSize]
  push_cast
  ring
def cubicPeriods : PeriodSublattice (PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ)) where
  periods := cubicSublattice _ d.side
  exists_linearIndependent := by
    refine ⟨fun i => ⟨(axisStep d.side i : AmbientSpace),
        latticeSubgroup_side_le d (axisStep d.side i).2⟩,
      fun i => AddSubgroup.mem_addSubgroupOf.2 (axisStep d.side i).2, ?_⟩
    have hs : d.side ≠ 0 := by linarith [three_le_side d]
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    have h := congrFun hg i
    simpa [axisStep, Finset.sum_apply, Pi.single_apply, hs] using h
  le_norm_of_ne_zero := by
    intro γ hγ hne
    obtain ⟨n, hn⟩ := AddSubgroup.mem_addSubgroupOf.1 hγ
    have hex : ∃ μ, n μ ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hne (Subtype.ext (funext fun μ => by simp [hn, hall]))
    obtain ⟨μ, hμ⟩ := hex
    have h1 : (1 : ℝ) ≤ |(n μ : ℝ)| := by exact_mod_cast Int.one_le_abs hμ
    have hs := three_le_side d
    have ha := meshSize_le_one d
    have hpos := meshSize_pos d
    calc minimalPeriodRatio * PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ) ≤ d.side := by
          unfold minimalPeriodRatio
          linarith
      _ ≤ |(n μ : ℝ)| * d.side := by nlinarith
      _ = ‖(γ : AmbientSpace) μ‖ := by
          rw [hn μ, Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith : 0 < d.side)]
      _ ≤ ‖(γ : AmbientSpace)‖ := norm_le_pi_norm _ μ
theorem mem_cubicPeriods_iff (x : LatticePoint (PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ))) :
    x ∈ (cubicPeriods d).periods ↔
      ∃ k : Fin 4 → ℤ, (x : AmbientSpace) = TestFunctions.latticeTranslate d.side k := by
  change x ∈ cubicSublattice _ d.side ↔ _
  unfold cubicSublattice
  rw [AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, funext fun μ => by rw [hn, TestFunctions.latticeTranslate, mul_comm]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, fun μ => by rw [hk, TestFunctions.latticeTranslate, mul_comm]⟩
end Cubic
theorem statement_holds (hCov : LatticeCovering.CoveringStatement)
    (hImage : CutoffLinks.LiftImageAndPeriodizedLimits)
    (hLinks : CutoffLinks.PeriodicFieldsAtPositiveLinks) :
    Statement := by
  intro β hβ d
  let D : ReflectionPositivity.AxisMirror.MirrorData := ⟨d, β, hβ⟩
  let B : CutoffLinks.CutoffData := ⟨d, β, hβ⟩
  obtain ⟨hfib, hbonds, hext, -⟩ := hCov D
  obtain ⟨hfw, -, -, himg, hsurj, -⟩ := hbonds
  have hfinite : Finite (PeriodicLattice.Plaquette d.L d.m ((d.K : ℕ) : ℤ)) := (hLinks B).1.2.2.1
  have hL : 2 ≤ d.L := by
    have h13 := d.isAdmissible.2
    omega
  have hj : -((d.m : ℕ) : ℤ) < ((d.K : ℕ) : ℤ) := by
    have h1 := d.m.pos
    have h2 := d.K.pos
    omega
  have F : CoversPeriodicLattice (m := d.m) (cubicPeriods d) := by
    refine ⟨fun x y => ?_, hfw.injOn, fun c => ?_, hsurj, hext.2.2.1,
      gaugeFieldOfPositive_mem hL hj⟩
    · rw [mem_cubicPeriods_iff, Subtype.ext_iff]
      exact hfib.1 x y
    · have hc : c.1 ∈ PeriodicLattice.forwardBonds d.L d.m ((d.K : ℕ) : ℤ) :=
        PeriodicLattice.mem_positiveBonds_iff.2 c.2
      rw [← himg] at hc
      obtain ⟨b, hb, e⟩ := hc
      exact ⟨⟨b, mem_positiveLinks_iff.1 hb⟩, Subtype.ext e⟩
  obtain ⟨⟨-, hinj, -⟩, -, -, hbij, -⟩ := hImage B
  refine ⟨latticeSubgroup_side_le d, cubicPeriods d, rfl, hinj, ?_,
    F.liftedWilsonMeasure_eq (meshSize_pos d) β⟩
  rw [← image_univ]
  exact hbij.image_eq
end YangMills.Construction.InfiniteLattice.CubicTorusAtCutoffLifts
