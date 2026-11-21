import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.LawInAState.LawsAreInvariantUnderTranslationsProof
import YangMills.Construction.VolumeTransfer.FactsOfLatticeSymmetriesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction.VolumeTransfer
open InfiniteLattice (AmbientSpace refinedLattice refinedSpacing RefinedGaugeField)
open LatticeGeometry (diagSign diagSign_apply diagSign_add diagSign_sub diagSign_mem_latticeSubgroup)
namespace LatticeSymmetries
theorem diagSign_mul (σ τ : Fin 4 → ℤˣ) (x : AmbientSpace) :
    diagSign (σ * τ) x = diagSign σ (diagSign τ x) := by
  funext i
  simp only [diagSign_apply, Pi.mul_apply, Units.val_mul, Int.cast_mul]
  ring
theorem diagSign_one (x : AmbientSpace) : diagSign 1 x = x := by apply _root_.YangMills.Construction.VolumeTransfer.ReflectionTranslations.diagSign_one_apply <;> assumption
theorem diagSign_inv_diagSign (σ : Fin 4 → ℤˣ) (x : AmbientSpace) :
    diagSign σ⁻¹ (diagSign σ x) = x := by
  rw [← diagSign_mul, inv_mul_cancel, diagSign_one]
theorem diagSign_diagSign_inv (σ : Fin 4 → ℤˣ) (x : AmbientSpace) :
    diagSign σ (diagSign σ⁻¹ x) = x := by
  rw [← diagSign_mul, mul_inv_cancel, diagSign_one]
theorem abs_diagSign (σ : Fin 4 → ℤˣ) (v : AmbientSpace) (i : Fin 4) :
    |diagSign σ v i| = |v i| := by
  rw [diagSign_apply]
  rcases Int.units_eq_one_or (σ i) with e | e <;> simp [e]
theorem supNormVec_diagSign (σ : Fin 4 → ℤˣ) (v : AmbientSpace) :
    TorusMetric.supNormVec (diagSign σ v) = TorusMetric.supNormVec v := by
  simp only [TorusMetric.supNormVec, abs_diagSign]
theorem l1NormVec_diagSign (σ : Fin 4 → ℤˣ) (v : AmbientSpace) :
    TorusMetric.l1NormVec (diagSign σ v) = TorusMetric.l1NormVec v := by
  simp only [TorusMetric.l1NormVec, abs_diagSign]
theorem euclidNormVec_diagSign (σ : Fin 4 → ℤˣ) (v : AmbientSpace) :
    TorusMetric.euclidNormVec (diagSign σ v) = TorusMetric.euclidNormVec v := by
  simp only [TorusMetric.euclidNormVec, ← sq_abs (diagSign σ v _), abs_diagSign, sq_abs]
structure ProjFacts {L K : ℕ} (Y : LatticeGeometry L K) : Prop where
  surj : Surjective Y.proj
  ker : ∀ (σ : Fin 4 → ℤˣ) (u : AmbientSpace), Y.proj u = 0 →
    Y.proj (diagSign σ u) = 0
  mem_sites : ∀ y, y ∈ Y.sites ↔ ∃ v ∈ refinedLattice L K, Y.proj v = y
  mapsLinks : ∀ r, Y.IsReflectionTranslation r → Y.MapsLinks r
section Shared
variable {L K : ℕ} {Y : LatticeGeometry L K}
theorem induced_proj {r : Y.Point → Y.Point} {σ : Fin 4 → ℤˣ} {t : AmbientSpace}
    (h : Y.IsInducedBy r fun x => diagSign σ x + t) (x : AmbientSpace) :
    r (Y.proj x) = Y.proj (diagSign σ x + t) :=
  h x
theorem existsUnique_inducedMap (hY : ProjFacts Y) (σ : Fin 4 → ℤˣ) (t : AmbientSpace) :
    ∃! r : Y.Point → Y.Point, Y.IsInducedBy r fun x => diagSign σ x + t := by
  have hwd : ∀ x x', Y.proj x = Y.proj x' →
      Y.proj (diagSign σ x + t) = Y.proj (diagSign σ x' + t) := by
    intro x x' h
    have h0 : Y.proj (x - x') = 0 := by rw [map_sub, h, sub_self]
    have h1 := hY.ker σ _ h0
    rw [diagSign_sub, map_sub, sub_eq_zero] at h1
    rw [map_add, map_add, h1]
  choose sec hsec using hY.surj
  refine ⟨fun y => Y.proj (diagSign σ (sec y) + t), fun x => hwd _ _ (hsec _), ?_⟩
  intro r' hr'
  funext y
  obtain ⟨x, rfl⟩ := hY.surj y
  rw [induced_proj hr' x]
  exact hwd _ _ (hsec _).symm
theorem symmetryInvertible (hY : ProjFacts Y) : SymmetryInvertible Y := by
  intro σ t ht r hr
  obtain ⟨s, hs, -⟩ := existsUnique_inducedMap hY σ⁻¹ (-(diagSign σ⁻¹ t))
  have hs' : Y.IsInducedBy s fun x => diagSign σ⁻¹ x - diagSign σ⁻¹ t := by
    intro x
    beta_reduce
    rw [induced_proj hs x, sub_eq_add_neg]
  have hsproj : ∀ x, s (Y.proj x) =
      Y.proj (diagSign σ⁻¹ x - diagSign σ⁻¹ t) := hs'
  have hleft : LeftInverse s r := by
    intro y
    obtain ⟨x, rfl⟩ := hY.surj y
    rw [induced_proj hr x, hsproj, diagSign_add, diagSign_inv_diagSign, add_sub_cancel_right]
  have hright : RightInverse s r := by
    intro y
    obtain ⟨x, rfl⟩ := hY.surj y
    rw [hsproj, induced_proj hr, diagSign_sub, diagSign_diagSign_inv, diagSign_diagSign_inv,
      sub_add_cancel]
  refine ⟨?_, hY.mapsLinks r ⟨σ, t, ht, hr⟩, ⟨hleft.injective, hright.surjective⟩, s,
    ⟨σ⁻¹, _, neg_mem (diagSign_mem_latticeSubgroup σ⁻¹ ht), hs⟩, hs', hleft, hright⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (hY.mem_sites z).1 hz
    rw [induced_proj hr]
    exact (hY.mem_sites _).2 ⟨_, add_mem (diagSign_mem_latticeSubgroup σ hv) ht, rfl⟩
  · intro hy
    refine ⟨s y, ?_, hright y⟩
    obtain ⟨v, hv, rfl⟩ := (hY.mem_sites y).1 hy
    rw [hsproj]
    exact (hY.mem_sites _).2
      ⟨_, sub_mem (diagSign_mem_latticeSubgroup σ⁻¹ hv) (diagSign_mem_latticeSubgroup σ⁻¹ ht), rfl⟩
theorem symmetryComp (Y : LatticeGeometry L K) : SymmetryComp Y := by
  intro σ τ t ht t' ht' r r' hr hr'
  have h : Y.IsInducedBy (r ∘ r') fun x => diagSign (σ * τ) x + (diagSign σ t' + t) := by
    intro x
    change r (r' (Y.proj x)) = _
    beta_reduce
    rw [induced_proj hr', induced_proj hr, diagSign_add, diagSign_mul, add_assoc]
  exact ⟨⟨σ * τ, _, add_mem (diagSign_mem_latticeSubgroup σ ht') ht, h⟩, h⟩
end Shared
theorem projFacts_euclidean (L K : ℕ) : ProjFacts (LatticeGeometry.euclidean L K) where
  surj y := ⟨y, rfl⟩
  ker σ u h := by
    have hu : u = 0 := h
    subst hu
    change diagSign σ 0 = 0
    funext i
    simp [diagSign_apply]
  mem_sites y := ⟨fun h => ⟨y, h, rfl⟩, fun ⟨v, hv, e⟩ => e ▸ hv⟩
  mapsLinks _ h := LatticeGeometry.IsReflectionTranslation.mapsLinks_euclidean h
theorem sub_of_reflectionTranslation {L K : ℕ} {r : AmbientSpace → AmbientSpace}
    {σ : Fin 4 → ℤˣ} {t : AmbientSpace}
    (h : (LatticeGeometry.euclidean L K).IsInducedBy r fun x => diagSign σ x + t)
    (x y : AmbientSpace) :
    r x - r y = diagSign σ (x - y) := by
  have hx : r x = diagSign σ x + t := h x
  have hy : r y = diagSign σ y + t := h y
  rw [hx, hy, diagSign_sub]
  abel
theorem euclideanSymmetryIsometry (L K : ℕ) : EuclideanSymmetryIsometry L K := by
  rintro r ⟨σ, t, -, hr⟩ x y
  rw [sub_of_reflectionTranslation hr]
  exact ⟨supNormVec_diagSign _ _, l1NormVec_diagSign _ _, euclidNormVec_diagSign _ _⟩
theorem euclideanShiftsAreSymmetries (L K : ℕ) : EuclideanShiftsAreSymmetries L K := by
  intro v
  refine ⟨1, v, v.2, fun x => ?_⟩
  change x + (v : AmbientSpace) = diagSign 1 x + (v : AmbientSpace)
  rw [diagSign_one]
theorem coe_diagSign_eq_zero {S : ℝ} (σ : Fin 4 → ℤˣ) (u : AmbientSpace) (i : Fin 4)
    (h : (u i : AddCircle S) = 0) : ((diagSign σ u i : ℝ) : AddCircle S) = 0 := by
  rw [diagSign_apply]
  rcases Int.units_eq_one_or (σ i) with e | e <;> simp [e, h]
theorem projFacts_periodic (L m K : ℕ) : ProjFacts (LatticeGeometry.periodic L m K) where
  surj := TorusCovering.torusProjHom_surjective _
  ker σ u h := by
    funext i
    exact coe_diagSign_eq_zero σ u i (congrFun h i)
  mem_sites y := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨fun i => (n i : ℝ) * PeriodicLattice.meshSize L (K : ℤ), ⟨n, fun _ => rfl⟩,
        funext fun i => (hn i).symm⟩
    · rintro ⟨v, ⟨n, hn⟩, rfl⟩
      exact ⟨n, fun i => congrArg (fun s : ℝ => (s : AddCircle (PeriodicLattice.torusSide L m))) (hn i)⟩
  mapsLinks _ h := LatticeGeometry.IsReflectionTranslation.mapsLinks_periodic h
theorem diagSign_mem_periodLattice {ℓ : ℝ} (σ : Fin 4 → ℤˣ) {u : AmbientSpace}
    (hu : u ∈ periodLattice ℓ) : diagSign σ u ∈ periodLattice ℓ := by
  obtain ⟨k, hk⟩ := hu
  refine ⟨fun i => ((σ i : ℤˣ) : ℤ) * k i, fun i => ?_⟩
  rw [diagSign_apply, hk i]
  push_cast
  ring
theorem torusInducedMapUnique (L m K : ℕ) : TorusInducedMapUnique L m K := by
  intro σ t _
  refine ⟨existsUnique_inducedMap (projFacts_periodic L m K) σ t, fun x u _ => ?_, ?_⟩
  · rw [diagSign_add]
    abel
  · refine ⟨fun u hu => diagSign_mem_periodLattice σ hu, (diagSign σ).injective.injOn,
      fun y hy => ?_⟩
    exact ⟨diagSign σ⁻¹ y, diagSign_mem_periodLattice σ⁻¹ hy, diagSign_diagSign_inv σ y⟩
theorem preimage_torusProj_diagSign (L m K : ℕ) (σ : Fin 4 → ℤˣ) (v : AmbientSpace) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) ⁻¹'
        {TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (diagSign σ v)} =
      diagSign σ '' (TorusMetric.torusProj (PeriodicLattice.torusSide L m) ⁻¹'
        {TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) v}) := by
  have hk := (projFacts_periodic L m K).ker
  have key : ∀ (δ : Fin 4 → ℤˣ) (w w' : AmbientSpace),
      TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) w =
        TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) w' →
      TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (diagSign δ w) =
        TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (diagSign δ w') := by
    intro δ w w' h
    have h0 : TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (w - w') = 0 := by
      rw [map_sub, h, sub_self]
    have h1 := hk δ _ h0
    rw [diagSign_sub] at h1
    have h2 : TorusCovering.torusProjHom (PeriodicLattice.torusSide L m)
        (diagSign δ w - diagSign δ w') = 0 :=
      h1
    rwa [map_sub, sub_eq_zero] at h2
  ext w
  constructor
  · intro hw
    have hw' : TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) w =
        TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (diagSign σ v) := hw
    refine ⟨diagSign σ⁻¹ w, ?_, diagSign_diagSign_inv σ w⟩
    have := key σ⁻¹ _ _ hw'
    rw [diagSign_inv_diagSign] at this
    exact this
  · rintro ⟨w', hw', rfl⟩
    exact key σ _ _ hw'
theorem torusSymmetryIsometry (L m K : ℕ) : TorusSymmetryIsometry L m K := by
  intro σ t _ r hr x y
  have hY := projFacts_periodic L m K
  obtain ⟨a, rfl⟩ := hY.surj x
  obtain ⟨b, rfl⟩ := hY.surj y
  have hd : r ((LatticeGeometry.periodic L m K).proj a) -
      r ((LatticeGeometry.periodic L m K).proj b) =
        TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (diagSign σ (a - b)) := by
    rw [induced_proj hr, induced_proj hr]
    change TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) _ -
      TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) _ = _
    rw [← map_sub, diagSign_sub, add_sub_add_right_eq_sub]
  have hd' : (LatticeGeometry.periodic L m K).proj a - (LatticeGeometry.periodic L m K).proj b =
      TorusCovering.torusProjHom (PeriodicLattice.torusSide L m) (a - b) := (map_sub _ _ _).symm
  rw [hd, hd']
  have hl := preimage_torusProj_diagSign L m K σ (a - b)
  refine ⟨?_, ?_, ?_, hl⟩
  · simp only [TorusMetric.torusSupNorm, hl, image_image, supNormVec_diagSign]
  · simp only [TorusMetric.torusL1Norm, hl, image_image, l1NormVec_diagSign]
  · simp only [TorusMetric.torusEuclidNorm, hl, image_image, euclidNormVec_diagSign]
theorem torusShiftsAreSymmetries (L m K : ℕ) : TorusShiftsAreSymmetries L m K := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := ((projFacts_periodic L m K).mem_sites w).1 hw
  refine ⟨1, v, hv, fun x => ?_⟩
  change (LatticeGeometry.periodic L m K).proj x + (LatticeGeometry.periodic L m K).proj v =
    (LatticeGeometry.periodic L m K).proj (diagSign 1 x + v)
  rw [diagSign_one, map_add]
section Measures
variable {a : ℝ}
theorem countable_link (a : ℝ) : Countable (InfiniteLattice.Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem borel_linkVariables (ι : Type) [Countable ι] :
    borel (InfiniteLattice.LinkVariables ι) = MeasurableSpace.pi := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.borel_linkVariables <;> assumption
def linkValues (U : InfiniteLattice.GaugeField a) :
    InfiniteLattice.Link a → Matrices.ComplexMatrix2.specialUnitary := U.1
theorem continuous_linkValues :
    Continuous (linkValues : InfiniteLattice.GaugeField a →
      InfiniteLattice.Link a → Matrices.ComplexMatrix2.specialUnitary) :=
  continuous_subtype_val
theorem measurable_linkValues :
    Measurable (linkValues : InfiniteLattice.GaugeField a →
      InfiniteLattice.Link a → Matrices.ComplexMatrix2.specialUnitary) := by
  refine measurable_pi_iff.2 fun e => ?_
  exact ((continuous_apply e).comp continuous_linkValues).measurable
theorem exists_preimage_linkValues {A : Set (InfiniteLattice.GaugeField a)}
    (hA : MeasurableSet A) :
    ∃ B : Set (InfiniteLattice.Link a → Matrices.ComplexMatrix2.specialUnitary),
      MeasurableSet B ∧ linkValues ⁻¹' B = A := by
  have := countable_link a
  have h1 : borel (InfiniteLattice.GaugeField a) =
      MeasurableSpace.comap linkValues MeasurableSpace.pi := by
    rw [← borel_linkVariables (InfiniteLattice.Link a)]
    exact borel_comap
  have hA' : MeasurableSet[borel (InfiniteLattice.GaugeField a)] A := hA
  rw [h1] at hA'
  exact hA'
theorem measure_ext_of_finiteMarginals (ν ν' : Measure (InfiniteLattice.GaugeField a))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ (I : Finset (InfiniteLattice.Link a))
      (B : Set (I → Matrices.ComplexMatrix2.specialUnitary)), MeasurableSet B →
      ν ((fun U (e : I) => linkValues U e.1) ⁻¹' B) =
        ν' ((fun U (e : I) => linkValues U e.1) ⁻¹' B)) :
    ν = ν' := by
  have hval := measurable_linkValues (a := a)
  have : IsProbabilityMeasure (ν.map linkValues) :=
    Measure.isProbabilityMeasure_map hval.aemeasurable
  have : IsProbabilityMeasure (ν'.map linkValues) :=
    Measure.isProbabilityMeasure_map hval.aemeasurable
  have hP : IsProjectiveLimit
      (α := fun _ : InfiniteLattice.Link a => Matrices.ComplexMatrix2.specialUnitary)
      (ν'.map linkValues) (fun I => (ν.map linkValues).map I.restrict) := by
    intro I
    refine Measure.ext fun B hB => ?_
    rw [Measure.map_apply (Finset.measurable_restrict I) hB,
      Measure.map_apply (Finset.measurable_restrict I) hB,
      Measure.map_apply hval (Finset.measurable_restrict I hB),
      Measure.map_apply hval (Finset.measurable_restrict I hB)]
    exact (h I B hB).symm
  have hP' : IsProjectiveLimit
      (α := fun _ : InfiniteLattice.Link a => Matrices.ComplexMatrix2.specialUnitary)
      (ν.map linkValues) (fun I => (ν.map linkValues).map I.restrict) := fun _ => rfl
  have : ∀ I : Finset (InfiniteLattice.Link a),
      IsFiniteMeasure ((ν.map linkValues).map
        (Finset.restrict (π := fun _ => Matrices.ComplexMatrix2.specialUnitary) I)) :=
    fun I => inferInstance
  have heq := hP'.unique hP
  refine Measure.ext fun A hA => ?_
  obtain ⟨B, hB, rfl⟩ := exists_preimage_linkValues hA
  rw [← Measure.map_apply hval hB, ← Measure.map_apply hval hB, heq]
end Measures
theorem measureDeterminedByCylinderFunctions (L K : ℕ) :
    MeasureDeterminedByCylinderFunctions L K := by
  intro ν ν' _ _ h
  refine measure_ext_of_finiteMarginals ν ν' fun I B hB => ?_
  have hlaw : Measurable fun U : RefinedGaugeField L K => fun e : I => linkValues U e.1 :=
    (Finset.measurable_restrict I).comp measurable_linkValues
  have hS := hlaw hB
  set S : Set (RefinedGaugeField L K) := (fun U (e : I) => linkValues U e.1) ⁻¹' B
  have hF : IsBoundedBorelInFinitelyManyLinks (refinedLinkValue L K)
      (S.indicator fun _ => (1 : ℂ)) := by
    refine ⟨(I : Set _), I.finite_toSet, B.indicator fun _ => (1 : ℂ), ?_, ⟨1, fun g => ?_⟩,
      fun U => ?_⟩
    · rw [borel_linkVariables]
      exact measurable_const.indicator hB
    · by_cases hg : g ∈ B <;> simp [Set.indicator, hg]
    · by_cases hU : U ∈ S
      · rw [Set.indicator_of_mem hU, Set.indicator_of_mem]
        exact hU
      · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem]
        exact hU
  have hint := h _ hF
  rw [integral_indicator_const _ hS, integral_indicator_const _ hS] at hint
  have hreal : ν.real S = ν'.real S := by
    simpa using hint
  have := (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν S) (measure_ne_top ν' S)).1 hreal
  exact this
theorem pullback_eq_pullbackField {L K : ℕ} {r : AmbientSpace → AmbientSpace}
    (hr : (LatticeGeometry.euclidean L K).MapsLinks r)
    (s : InfiniteLattice.LatticeSymmetry (refinedSpacing L K)) (hs : s.toFun = r)
    (U : RefinedGaugeField L K) : LatticeGeometry.pullback hr U = s.pullbackField U := by
  subst hs
  refine (LatticeGeometry.euclidean L K).linkValue_injective _ _ fun e => ?_
  rw [LatticeGeometry.linkValue_pullback]
  have he : LatticeGeometry.imageLink hr e = s.linkMap e :=
    (LatticeGeometry.euclidean L K).link_ext _ _ (LatticeGeometry.src_imageLink hr e)
      (LatticeGeometry.tgt_imageLink hr e)
  rw [he]
  rfl
theorem measurable_pullbackField {a : ℝ} (s : InfiniteLattice.LatticeSymmetry a) :
    Measurable s.pullbackField := by apply _root_.YangMills.SharedProofs.p50069 <;> assumption
theorem isBoundedObservable_of_finitelyManyLinks {L K : ℕ} {F : RefinedGaugeField L K → ℂ}
    (hF : IsBoundedBorelInFinitelyManyLinks (refinedLinkValue L K) F) :
    InfiniteLattice.IsBoundedObservable F := by
  obtain ⟨E, hE, Φ, hΦ, ⟨C, hC⟩, hU⟩ := hF
  have : Countable E := hE.countable.to_subtype
  rw [borel_linkVariables] at hΦ
  have hm : Measurable fun U : RefinedGaugeField L K => fun e : E => refinedLinkValue L K U e :=
    measurable_pi_iff.2 fun e => (measurable_pi_apply e.1).comp measurable_linkValues
  refine ⟨?_, C, fun U => ?_⟩
  · have : F = Φ ∘ fun U : RefinedGaugeField L K => fun e : E => refinedLinkValue L K U e :=
      funext hU
    rw [this]
    exact hΦ.comp hm
  · rw [hU]
    exact hC _
theorem invarianceNotionsAgree (L K : ℕ) : InvarianceNotionsAgree L K := by
  intro r hsym
  have hr := LatticeGeometry.IsReflectionTranslation.mapsLinks_euclidean hsym
  have hiso := euclideanSymmetryIsometry L K r hsym
  obtain ⟨σ, t, ht, hind⟩ := id hsym
  have honto : r '' (refinedLattice L K : Set AmbientSpace) = refinedLattice L K :=
    (symmetryInvertible (projFacts_euclidean L K) σ t ht r hind).1
  let s : InfiniteLattice.LatticeSymmetry (refinedSpacing L K) :=
    ⟨r, fun x y => (hiso x y).2.2, honto⟩
  refine ⟨hr, s, rfl, fun ν _ => ⟨fun h A hA => ?_, fun h F hF => ?_⟩⟩
  · have hT := measurable_pullbackField s
    have : IsProbabilityMeasure (ν.map s.pullbackField) :=
      Measure.isProbabilityMeasure_map hT.aemeasurable
    have hmap : ν.map s.pullbackField = ν := by
      refine measureDeterminedByCylinderFunctions L K _ _ fun F hF => ?_
      rw [integral_map hT.aemeasurable
        (isBoundedObservable_of_finitelyManyLinks hF).1.aestronglyMeasurable]
      have := h F hF
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      change F (s.pullbackField U) = F (LatticeGeometry.pullback hr U)
      rw [pullback_eq_pullbackField hr s rfl]
    have := integral_map (μ := ν) hT.aemeasurable (f := A)
      (hA.1.aestronglyMeasurable)
    rw [hmap] at this
    exact this.symm
  · have := h F (isBoundedObservable_of_finitelyManyLinks hF)
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    change F (LatticeGeometry.pullback hr U) = F (s.pullbackField U)
    rw [pullback_eq_pullbackField hr s rfl]
theorem basicProperties : BasicProperties := by
  intro L _ K
  refine ⟨⟨symmetryInvertible (projFacts_euclidean L K), symmetryComp _,
    euclideanSymmetryIsometry L K, euclideanShiftsAreSymmetries L K,
    measureDeterminedByCylinderFunctions L K, invarianceNotionsAgree L K⟩, fun m => ⟨
      torusInducedMapUnique L m K, symmetryInvertible (projFacts_periodic L m K),
      symmetryComp _, torusSymmetryIsometry L m K,
      torusShiftsAreSymmetries L m K⟩⟩
end LatticeSymmetries
end YangMills.Construction.VolumeTransfer
end
