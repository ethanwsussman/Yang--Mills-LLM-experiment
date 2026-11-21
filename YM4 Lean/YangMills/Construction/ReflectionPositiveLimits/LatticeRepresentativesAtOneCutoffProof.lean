import YangMills.Construction.InfiniteLattice.AllLatticeIsometriesAndTheMeanOfThePlaquetteFunctionProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAndTheirActions
import YangMills.Construction.ReflectionPositiveLimits.RepresentativesOfSeparatedTuplesProof
import YangMills.Construction.SpacingIndependentBounds.TheSizesDoNotSeeTheSpacingProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeRepresentatives
open InfiniteLattice (GaugeField IsLocalObservable IsBoundedObservable LatticeSymmetry ElementaryPlaquette
  LatticePoint affineHyperoctahedralMaps latticeMotion scaledCube regionObservables
  boundedRegionObservables faceEnergy regionSigma latticeSubgroup smearedEnergy axisStep shift)
open FieldsAtSpacing (ContainsCorners faceFunction)
open GibbsAtFixedSpacing (BorelProb)
open TestFunctions (euclidDistR4 setDistR4 sharpNormR4)
open TorusMetric (euclidNormVec)
variable {a : ℝ}
structure LatticeFacts (a : ℝ) : Prop where
  compactSpace : CompactSpace (GaugeField a)
  center_injective : Function.Injective (ElementaryPlaquette.center : ElementaryPlaquette a → Space)
  finite_center : ∀ S : Set Space, Bornology.IsBounded S →
    {p : ElementaryPlaquette a | p.center ∈ S}.Finite
  dist_corner : ∀ p : ElementaryPlaquette a, ∀ y ∈ p.cornerSet, ‖(y : Space) - p.center‖ = a / 2
  continuous_energy : ∀ p : ElementaryPlaquette a, Continuous fun U : GaugeField a => faceEnergy U p
  motions_iff : ∀ g : Space → Space, (∃ r : LatticeSymmetry a, r.toFun = g) ↔
    g ∈ affineHyperoctahedralMaps a
  plaquetteMap_bijective : ∀ r : LatticeSymmetry a, Function.Bijective r.plaquetteMap
  center_plaquetteMap : ∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a),
    (r.plaquetteMap p).center = r.toFun p.center
  energy_pullback : ∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a) (U : GaugeField a),
    faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p)
  faceFunction_mem : ∀ (p : ElementaryPlaquette a) (S : Set Space), ContainsCorners S p →
    faceFunction p ∈ boundedRegionObservables a S
theorem latticeFacts_of
    (h₁ : InfiniteLattice.CutoffStructure.FieldSpaceAndSymmetries)
    (h₂ : FieldsAtSpacing.LinkFunctionsStatement) (ha : 0 < a) : LatticeFacts a := by
  obtain ⟨hs, hp, hf, hi, hc, -⟩ := h₁ a ha
  have hr := (h₂ a ha ∅ (empty_subset _)).2.2.2.2.2
  exact
    { compactSpace := hs.2.2.2.2.2.2.1
      center_injective := hp.1
      finite_center := fun S hS => (hp.2.2 S hS).2
      dist_corner := hp.2.1
      continuous_energy := fun p => (hf p).2.2.1
      motions_iff := hi.1
      plaquetteMap_bijective := fun r => (hi.2 r).2.2.2.1
      center_plaquetteMap := fun r => (hi.2 r).2.2.2.2.1
      energy_pullback := hc.1
      faceFunction_mem := fun p S hS => (hr.1 p).2.2 S hS }
theorem finite_center_support (F : LatticeFacts a) {f : ScalarField}
    (hf : Bornology.IsBounded (tsupport f)) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite :=
  (F.finite_center _ hf).subset fun _ hp => subset_tsupport f hp
theorem smearedEnergy_eq_sum (f : ScalarField) (U : GaugeField a) (P : Finset (ElementaryPlaquette a))
    (hP : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P) :
    smearedEnergy f U = ∑ p ∈ P, faceEnergy U p * f p.center := by
  simp only [smearedEnergy, smul_eq_mul]
  refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
  have h : f p.center ≠ 0 := fun h => hp (by simp [h])
  exact hP p h
theorem smearedEnergy_eq_finsetSum (F : LatticeFacts a) {f : ScalarField}
    (hf : Bornology.IsBounded (tsupport f)) :
    (smearedEnergy f : GaugeField a → ℝ) = fun U : GaugeField a =>
      ∑ p ∈ (finite_center_support F hf).toFinset, faceEnergy U p * f p.center :=
  funext fun U => smearedEnergy_eq_sum f U _ fun _ hp => (finite_center_support F hf).mem_toFinset.2 hp
theorem continuous_smearedEnergy (F : LatticeFacts a) {f : ScalarField}
    (hf : Bornology.IsBounded (tsupport f)) :
    Continuous (smearedEnergy f : GaugeField a → ℝ) := by
  rw [smearedEnergy_eq_finsetSum F hf]
  exact continuous_finsetSum _ fun p _ => (F.continuous_energy p).mul continuous_const
theorem measurable_sum_mul_const {Ω ι : Type*} [MeasurableSpace Ω] (P : Finset ι) (w : ι → ℝ)
    (g : ι → Ω → ℝ) (h : ∀ i ∈ P, Measurable (g i)) :
    Measurable fun U => ∑ i ∈ P, g i U * w i :=
  Finset.measurable_fun_sum _ fun i hi => (h i hi).mul_const (w i)
theorem measurable_smearedEnergy (F : LatticeFacts a) {f : ScalarField}
    (hf : Bornology.IsBounded (tsupport f)) (S : Set Space)
    (hS : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → ContainsCorners S p) :
    Measurable[regionSigma S] (smearedEnergy f : GaugeField a → ℝ) := by
  rw [smearedEnergy_eq_finsetSum F hf]
  refine @measurable_sum_mul_const _ _ (regionSigma S) _ (fun p => f p.center)
    (fun p U => faceEnergy U p) fun p hp => ?_
  have h := (F.faceFunction_mem p S (hS p ((finite_center_support F hf).mem_toFinset.1 hp))).2
  have e : (fun U : GaugeField a => faceEnergy U p) = Complex.re ∘ faceFunction p := by
    funext U
    simp [faceFunction]
  rw [e]
  exact Complex.measurable_re.comp h
theorem toComplexObs_mem_of_continuous (F : LatticeFacts a) {g : GaugeField a → ℝ} (hg : Continuous g)
    {S : Set Space} (hS : Measurable[regionSigma S] g) : toComplexObs g ∈ regionObservables a S := by
  have := F.compactSpace
  have hc : Continuous (toComplexObs g) := Complex.continuous_ofReal.comp hg
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨⟨hc.measurable, C, fun U => hC U (mem_univ U)⟩, Complex.measurable_ofReal.comp hS⟩
theorem smearedEnergy_linComb (F : LatticeFacts a) {f f' : ScalarField}
    (hf : Bornology.IsBounded (tsupport f)) (hf' : Bornology.IsBounded (tsupport f')) (α α' : ℝ)
    (U : GaugeField a) :
    smearedEnergy (α • f + α' • f') U = α * smearedEnergy f U + α' * smearedEnergy f' U := by
  classical
  set P := (finite_center_support (a := a) F hf).toFinset ∪
    (finite_center_support (a := a) F hf').toFinset
  have h₁ : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P := fun p hp =>
    Finset.mem_union_left _ ((finite_center_support F hf).mem_toFinset.2 hp)
  have h₂ : ∀ p : ElementaryPlaquette a, f' p.center ≠ 0 → p ∈ P := fun p hp =>
    Finset.mem_union_right _ ((finite_center_support F hf').mem_toFinset.2 hp)
  have h₃ : ∀ p : ElementaryPlaquette a, (α • f + α' • f') p.center ≠ 0 → p ∈ P := by
    intro p hp
    by_contra hn
    have e₁ : f p.center = 0 := by
      by_contra h
      exact hn (h₁ p h)
    have e₂ : f' p.center = 0 := by
      by_contra h
      exact hn (h₂ p h)
    exact hp (by simp [e₁, e₂])
  rw [smearedEnergy_eq_sum _ U P h₃, smearedEnergy_eq_sum _ U P h₁, smearedEnergy_eq_sum _ U P h₂,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem actOn_smearedEnergy (F : LatticeFacts a) (r : LatticeSymmetry a) (f : ScalarField) :
    r.actOn (smearedEnergy f : GaugeField a → ℝ) =
      smearedEnergy (pushFn (latticeSymmetryToEuclid r) f) := by
  funext U
  let e : ElementaryPlaquette a ≃ ElementaryPlaquette a :=
    Equiv.ofBijective r.plaquetteMap (F.plaquetteMap_bijective r)
  change ∑ᶠ p : ElementaryPlaquette a, faceEnergy (r.pullbackField U) p • f p.center =
    ∑ᶠ p : ElementaryPlaquette a, faceEnergy U p •
      pushFn (latticeSymmetryToEuclid r) f p.center
  refine Eq.trans (finsum_congr fun p => ?_) (finsum_comp_equiv e)
  have hb : (e p).center = (latticeSymmetryToEuclid r).toFun p.center :=
    F.center_plaquetteMap r p
  have hm : pushFn (latticeSymmetryToEuclid r) f (e p).center = f p.center := by
    rw [hb]
    simp only [pushFn, Function.comp_apply, EuclidIsometry.symm_toFun]
  rw [hm, F.energy_pullback r p U]
  rfl
def centeredEnergy (ν : Measure (GaugeField a)) (f : ScalarField) (U : GaugeField a) : ℝ :=
  smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν
theorem centeredProduct_eq_prod {L K : ℕ} (ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ)))
    (X : Tuple) : centeredProduct L K ν X = (X.1.map (centeredEnergy ν.1)).prod :=
  rfl
theorem list_map_prod_apply {Ω ι : Type*} (Φ : ι → Ω → ℝ) (l : List ι) (U : Ω) :
    (l.map Φ).prod U = (l.map fun f => Φ f U).prod := by apply _root_.YangMills.Construction.ReflectionPositivity.TupleRepresentatives.list_map_prod_apply <;> assumption
theorem continuous_list_map_prod {Ω ι : Type*} [TopologicalSpace Ω] (Φ : ι → Ω → ℝ) (l : List ι)
    (h : ∀ f ∈ l, Continuous (Φ f)) : Continuous (l.map Φ).prod := by apply _root_.YangMills.Construction.ReflectionPositivity.TupleRepresentatives.continuous_list_map_prod <;> assumption
theorem measurable_list_map_prod {Ω ι : Type*} [MeasurableSpace Ω] (Φ : ι → Ω → ℝ) (l : List ι)
    (h : ∀ f ∈ l, Measurable (Φ f)) : Measurable (l.map Φ).prod := by apply _root_.YangMills.Construction.ReflectionPositivity.TupleRepresentatives.measurable_list_map_prod <;> assumption
theorem isBounded_tsupport_of_mem {X : Tuple} {f : ScalarField} (hf : f ∈ X.1) :
    Bornology.IsBounded (tsupport f) :=
  (X.2.1 f hf).2.1.isBounded
theorem continuous_centeredEnergy (F : LatticeFacts a) (ν : Measure (GaugeField a)) {f : ScalarField}
    (hf : Bornology.IsBounded (tsupport f)) : Continuous (centeredEnergy ν f) :=
  (continuous_smearedEnergy F hf).sub continuous_const
theorem continuous_tuple_prod (F : LatticeFacts a) (ν : Measure (GaugeField a)) (X : Tuple) :
    Continuous (X.1.map (centeredEnergy ν)).prod :=
  continuous_list_map_prod _ _ fun _ hf => continuous_centeredEnergy F ν (isBounded_tsupport_of_mem hf)
theorem measurable_sub_constant {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ} (h : Measurable g)
    (c : ℝ) : Measurable fun U => g U - c :=
  h.sub_const c
theorem toComplexObs_tuple_mem (F : LatticeFacts a) (ν : Measure (GaugeField a)) (X : Tuple)
    (S : Set Space)
    (hS : ∀ f ∈ X.1, ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → ContainsCorners S p) :
    toComplexObs (X.1.map (centeredEnergy ν)).prod ∈ regionObservables a S := by
  refine toComplexObs_mem_of_continuous F (continuous_tuple_prod F ν X) ?_
  exact @measurable_list_map_prod _ _ (regionSigma S) _ _ fun f hf =>
    @measurable_sub_constant _ (regionSigma S) _
      (measurable_smearedEnergy F (isBounded_tsupport_of_mem hf) S (hS f hf)) _
theorem integrable_of_continuous_compact (F : LatticeFacts a) (ν : Measure (GaugeField a))
    [IsFiniteMeasure ν] {g : GaugeField a → ℝ} (hg : Continuous g) : Integrable g ν := by
  have := F.compactSpace
  exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
theorem centeredEnergy_linComb (F : LatticeFacts a) (ν : Measure (GaugeField a)) [IsFiniteMeasure ν]
    {f f' : ScalarField}
    (hf : Bornology.IsBounded (tsupport f)) (hf' : Bornology.IsBounded (tsupport f')) (α α' : ℝ) :
    centeredEnergy ν (α • f + α' • f') = α • centeredEnergy ν f + α' • centeredEnergy ν f' := by
  have hi : ∫ V, smearedEnergy (α • f + α' • f') V ∂ν =
      α * (∫ V, smearedEnergy f V ∂ν) + α' * ∫ V, smearedEnergy f' V ∂ν := by
    simp only [smearedEnergy_linComb F hf hf' α α']
    rw [integral_add
      ((integrable_of_continuous_compact F ν (continuous_smearedEnergy F hf)).const_mul α)
      ((integrable_of_continuous_compact F ν (continuous_smearedEnergy F hf')).const_mul α'),
      integral_const_mul, integral_const_mul]
  funext U
  simp only [centeredEnergy, hi, smearedEnergy_linComb F hf hf' α α' U, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring
theorem actOn_centeredEnergy (F : LatticeFacts a) (ν : Measure (GaugeField a))
    (r : LatticeSymmetry a) (hr : InfiniteLattice.IsSymmetricUnder ν r) {f : ScalarField}
    (hf : Bornology.IsBounded (tsupport f)) :
    r.actOn (centeredEnergy ν f) = centeredEnergy ν (pushFn (latticeSymmetryToEuclid r) f) := by
  have hmove := actOn_smearedEnergy F r f
  have hobs : IsBoundedObservable (toComplexObs (smearedEnergy f : GaugeField a → ℝ)) :=
    (toComplexObs_mem_of_continuous F (continuous_smearedEnergy F hf) (S := univ)
      (measurable_smearedEnergy F hf univ fun p _ y _ => mem_univ _)).1
  have hI : ∫ V, smearedEnergy (pushFn (latticeSymmetryToEuclid r) f) V ∂ν =
      ∫ V, smearedEnergy f V ∂ν := by
    have h := hr _ hobs
    have e : ∀ U, r.actOn (toComplexObs (smearedEnergy f : GaugeField a → ℝ)) U =
        ((smearedEnergy (pushFn (latticeSymmetryToEuclid r) f) U : ℝ) : ℂ) := fun U => by
      rw [← hmove]
      rfl
    have i : ∀ g : GaugeField a → ℝ, ∫ U, ((g U : ℝ) : ℂ) ∂ν = ((∫ U, g U ∂ν : ℝ) : ℂ) :=
      fun g => integral_ofReal
    simp only [e] at h
    simp only [toComplexObs] at h
    rw [i, i] at h
    exact_mod_cast h
  funext U
  change smearedEnergy f (r.pullbackField U) - _ = smearedEnergy _ U - _
  rw [hI, ← hmove]
  rfl
def plaquetteCornersOver (a : ℝ) (T : Set Space) : Set Space :=
  {y | ∃ p : ElementaryPlaquette a, p.center ∈ T ∧ ∃ z ∈ p.cornerSet, y = (z : Space)}
theorem isBounded_plaquetteCornersOver (F : LatticeFacts a) {T : Set Space}
    (hT : Bornology.IsBounded T) : Bornology.IsBounded (plaquetteCornersOver a T) := by
  obtain ⟨R, hR⟩ := hT.subset_closedBall (0 : Space)
  refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := a / 2 + R)).subset ?_
  rintro y ⟨p, hp, z, hz, rfl⟩
  have hb := hR hp
  rw [mem_closedBall_zero_iff] at hb ⊢
  calc ‖(z : Space)‖ = ‖((z : Space) - p.center) + p.center‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖(z : Space) - p.center‖ + ‖p.center‖ := norm_add_le _ _
    _ ≤ a / 2 + R := by
        rw [F.dist_corner p z hz]
        linarith
theorem toComplexObs_mem_plaquetteCornersOver (F : LatticeFacts a) (ν : Measure (GaugeField a))
    (X : Tuple) :
    toComplexObs (X.1.map (centeredEnergy ν)).prod ∈
      regionObservables a (plaquetteCornersOver a (⋃ f ∈ X.1, tsupport f)) :=
  toComplexObs_tuple_mem F ν X _ fun f hf p hp y hy =>
    ⟨p, mem_iUnion₂.2 ⟨f, hf, subset_tsupport f hp⟩, y, hy, rfl⟩
theorem isBounded_iUnion_tsupport (X : Tuple) :
    Bornology.IsBounded (⋃ f ∈ X.1, tsupport f) :=
  (Bornology.isBounded_biUnion (List.finite_toSet X.1)).2 fun _ hf => isBounded_tsupport_of_mem hf
theorem euclidNormVec_single_add_single {μ κ : Fin 4} (h : μ ≠ κ) (t t' : ℝ) :
    euclidNormVec (Pi.single μ t + Pi.single κ t' : Space) = √(t ^ 2 + t' ^ 2) := by
  unfold euclidNormVec
  congr 1
  have e : ∀ ν, (Pi.single μ t + Pi.single κ t' : Space) ν ^ 2 =
      (Pi.single μ (t ^ 2) : Space) ν + (Pi.single κ (t' ^ 2) : Space) ν := by
    intro ν
    by_cases h₁ : ν = μ
    · subst h₁
      simp [h]
    · by_cases h₂ : ν = κ
      · subst h₂
        simp [h₁]
      · simp [h₁, h₂]
  simp only [e, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]
theorem euclidNormVec_corner_sub_center (ha : 0 < a) (p : ElementaryPlaquette a) (y : LatticePoint a)
    (hy : y ∈ p.cornerSet) : euclidNormVec ((y : Space) - p.center) = a / √2 := by
  have hne : p.lowAxis ≠ p.highAxis := ne_of_lt p.lowAxis_lt_highAxis
  have hval : ∀ t t' : ℝ, (t = a / 2 ∨ t = -(a / 2)) → (t' = a / 2 ∨ t' = -(a / 2)) →
      euclidNormVec (Pi.single p.lowAxis t + Pi.single p.highAxis t' : Space) = a / √2 := by
    intro t t' ht ht'
    have e : t ^ 2 + t' ^ 2 = a ^ 2 / 2 := by
      rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl <;> ring
    rw [euclidNormVec_single_add_single hne, e, Real.sqrt_div (sq_nonneg a), Real.sqrt_sq ha.le]
  simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · have e : ((p.corner : LatticePoint a) : Space) - p.center =
        Pi.single p.lowAxis (-(a / 2)) + Pi.single p.highAxis (-(a / 2)) := by
      funext ν
      simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      split_ifs <;> ring
    rw [e]
    exact hval _ _ (Or.inr rfl) (Or.inr rfl)
  · have e : ((p.corner + axisStep a p.lowAxis : LatticePoint a) : Space) - p.center =
        Pi.single p.lowAxis (a / 2) + Pi.single p.highAxis (-(a / 2)) := by
      funext ν
      change (p.corner : Space) ν + (Pi.single p.lowAxis a : Space) ν - p.center ν = _
      simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
      split_ifs <;> ring
    rw [e]
    exact hval _ _ (Or.inl rfl) (Or.inr rfl)
  · have e : ((p.corner + axisStep a p.lowAxis + axisStep a p.highAxis : LatticePoint a) : Space) -
        p.center = Pi.single p.lowAxis (a / 2) + Pi.single p.highAxis (a / 2) := by
      funext ν
      change (p.corner : Space) ν + (Pi.single p.lowAxis a : Space) ν +
        (Pi.single p.highAxis a : Space) ν - p.center ν = _
      simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
      split_ifs <;> ring
    rw [e]
    exact hval _ _ (Or.inl rfl) (Or.inl rfl)
  · have e : ((p.corner + axisStep a p.highAxis : LatticePoint a) : Space) - p.center =
        Pi.single p.lowAxis (-(a / 2)) + Pi.single p.highAxis (a / 2) := by
      funext ν
      change (p.corner : Space) ν + (Pi.single p.highAxis a : Space) ν - p.center ν = _
      simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
      split_ifs <;> ring
    rw [e]
    exact hval _ _ (Or.inr rfl) (Or.inl rfl)
theorem smearedEnergyStructure (F : LatticeFacts a) (ha : 0 < a) : SmearedEnergyStructure a := by
  refine ⟨fun p y hy => ⟨?_, euclidNormVec_corner_sub_center ha p y hy⟩, fun f hf => ?_⟩
  · rw [maxNorm_eq_norm]
    exact F.dist_corner p y hy
  have hb := hf.2
  refine ⟨⟨(F.finite_center _ hb).toFinset, fun p => f p.center,
      fun p hp => (F.finite_center _ hb).mem_toFinset.1 hp, fun U => ?_⟩,
    continuous_smearedEnergy F hb, fun f' α α' hf' => ⟨⟨?_, ?_⟩, ?_⟩, fun S hS => ?_⟩
  · rw [smearedEnergy_eq_sum f U _ fun p hp =>
      (F.finite_center _ hb).mem_toFinset.2 (subset_tsupport f hp)]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  · obtain ⟨C, hC⟩ := hf.1
    obtain ⟨C', hC'⟩ := hf'.1
    refine ⟨|α| * C + |α'| * C', fun x => ?_⟩
    calc ‖(α • f + α' • f') x‖ ≤ ‖α • f x‖ + ‖α' • f' x‖ := norm_add_le _ _
      _ ≤ |α| * C + |α'| * C' := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs α, Real.norm_eq_abs α']
          exact add_le_add (mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hC' x) (abs_nonneg _))
  · exact (hb.union hf'.2).subset (tsupport_linComb_subset α α' f f')
  · funext U
    simp [smearedEnergy_linComb F hb hf'.2 α α' U]
  · exact toComplexObs_mem_of_continuous F (continuous_smearedEnergy F hb)
      (measurable_smearedEnergy F hb S fun p hp y hy => hS p (subset_tsupport f hp) y hy)
def signedPermSymmetry (a : ℝ) (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) : LatticeSymmetry a where
  toFun := permuteAndSign π s
  preservesDist x y := by
    unfold TorusMetric.euclidNormVec
    congr 1
    have h : ∀ μ, (permuteAndSign π s x - permuteAndSign π s y) μ ^ 2 =
        (x - y) (π μ) ^ 2 := by
      intro μ
      change ((s μ : ℤ) • x (π μ) - (s μ : ℤ) • y (π μ)) ^ 2 = (x (π μ) - y (π μ)) ^ 2
      rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_sub, mul_pow, sq ((s μ : ℤ) : ℝ),
        intUnit_cast_mul_self, one_mul]
    simp only [h]
    exact Equiv.sum_comp π fun ν => (x - y) ν ^ 2
  image_eq := by
    ext x
    constructor
    · rintro ⟨y, ⟨n, hn⟩, rfl⟩
      refine ⟨fun μ => (s μ : ℤ) * n (π μ), fun μ => ?_⟩
      change (s μ : ℤ) • y (π μ) = _
      rw [hn, zsmul_eq_mul]
      push_cast
      ring
    · intro hx
      obtain ⟨n, hn⟩ := hx
      refine ⟨(permuteAndSign π s).symm x,
        ⟨fun ν => (s (π.symm ν) : ℤ) * n (π.symm ν), fun ν => ?_⟩, by simp⟩
      change (s (π.symm ν) : ℤ) • x (π.symm ν) = _
      rw [hn, zsmul_eq_mul]
      push_cast
      ring
theorem exists_perm_apply_apply {μ κ μ' κ' : Fin 4} (h : μ ≠ κ) (h' : μ' ≠ κ') :
    ∃ π : Equiv.Perm (Fin 4), π μ' = μ ∧ π κ' = κ := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.exists_perm_of_ne <;> assumption
theorem symmetryCovariance (F : LatticeFacts a)
    (hm : GibbsAtFixedSpacing.SymmetriesTransportPlaquettes a) : SymmetryCovariance a := by
  refine ⟨fun g => ⟨?_, ?_⟩, fun r => ⟨fun p => (hm r).1 p, (hm r).2.1, (hm r).2.2.2.2.1,
    (hm r).2.2.2.1, fun f _ => actOn_smearedEnergy F r f⟩, fun p p' => ?_⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨w, hw, v, h⟩ := (F.motions_iff _).1 ⟨r, rfl⟩
    obtain ⟨π, s, hs⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).1 hw
    refine ⟨Matrix.of fun μ ν => if ν = π μ then ((s μ : ℤ) : ℝ) else 0,
      ⟨π, fun μ => ((s μ : ℤ) : ℝ), fun μ => ?_, fun x μ => ?_⟩, (v : Space), v.2, fun x => ?_⟩
    · rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
    · simp [Matrix.mulVec, dotProduct]
    · rw [h]
      funext μ
      simp [latticeMotion, hs, Matrix.mulVec, dotProduct]
  · rintro ⟨M, ⟨ς, ε, hε, hM⟩, v, hv, hg⟩
    refine ⟨(shift ⟨v, hv⟩).comp (signedPermSymmetry a ς fun μ => if ε μ = 1 then 1 else -1), ?_⟩
    funext x
    rw [hg x]
    change permuteAndSign ς _ x + v = _
    congr 1
    funext μ
    rw [hM x μ]
    rcases hε μ with h | h
    · simp [permuteAndSign, h]
    · have h' : ε μ ≠ 1 := by
        rw [h]
        norm_num
      have e : (if ε μ = 1 then (1 : ℤˣ) else -1) = -1 := if_neg h'
      change ((if ε μ = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) • x (ς μ) = _
      rw [e, h]
      simp
  · obtain ⟨π, h₁, h₂⟩ := exists_perm_apply_apply (ne_of_lt p.lowAxis_lt_highAxis)
      (ne_of_lt p'.lowAxis_lt_highAxis)
    let w₀ : LatticeSymmetry a := signedPermSymmetry a π 1
    let v : LatticePoint a := p'.corner - w₀.pointMap p.corner
    refine ⟨(shift v).comp w₀, F.center_injective ?_⟩
    rw [F.center_plaquetteMap]
    change permuteAndSign π 1 p.center + (v : Space) = p'.center
    funext κ
    have e₁ : (Pi.single p.lowAxis (a / 2) : Space) (π κ) =
        (Pi.single p'.lowAxis (a / 2) : Space) κ := by
      simp only [Pi.single_apply, ← h₁, π.injective.eq_iff]
    have e₂ : (Pi.single p.highAxis (a / 2) : Space) (π κ) =
        (Pi.single p'.highAxis (a / 2) : Space) κ := by
      simp only [Pi.single_apply, ← h₂, π.injective.eq_iff]
    have ev : (v : Space) κ = (p'.corner : Space) κ - (p.corner : Space) (π κ) := by
      change (p'.corner : Space) κ - permuteAndSign π 1 (p.corner : Space) κ = _
      simp [permuteAndSign]
    have ew : permuteAndSign π 1 p.center κ = p.center (π κ) := by
      simp [permuteAndSign]
    rw [Pi.add_apply, ew, ev]
    simp only [ElementaryPlaquette.center, Pi.add_apply, e₁, e₂]
    ring
theorem actOn_tuple_prod (F : LatticeFacts a) (ν : Measure (GaugeField a)) (r : LatticeSymmetry a)
    (hr : InfiniteLattice.IsSymmetricUnder ν r) (X : Tuple) :
    r.actOn ((X.1.map (centeredEnergy ν)).prod : GaugeField a → ℝ) =
      ((push (latticeSymmetryToEuclid r) X).1.map (centeredEnergy ν)).prod := by
  funext U
  change (X.1.map (centeredEnergy ν)).prod (r.pullbackField U) = _
  rw [list_map_prod_apply, list_map_prod_apply]
  simp only [push, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun f hf => ?_)
  exact congrFun (actOn_centeredEnergy F ν r hr (isBounded_tsupport_of_mem hf)) U
theorem disjoint_of_setDistR4_ne_zero {A B : Set Space} (h : setDistR4 A B ≠ 0) :
    Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hA hB
  refine h (le_antisymm ?_ bot_le)
  calc setDistR4 A B ≤ ENNReal.ofReal (euclidNormVec (x - x)) :=
        iInf₂_le_of_le x hA (iInf₂_le x hB)
    _ = 0 := by simp [euclidNormVec]
theorem prod_update_eq_mul_prod_erase {ι Ω : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → Ω)
    [CommMonoid Ω] (i : ι) (x : Ω) :
    ∏ j, Function.update φ i x j = x * ∏ j ∈ Finset.univ.erase i, φ j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
theorem centeredProductCalculus {L : ℕ} {K : ℕ+}
    (ν : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))
    (F : LatticeFacts (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)))
    (hν : ∀ r : LatticeSymmetry (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)),
      InfiniteLattice.IsSymmetricUnder ν.1 r) :
    CenteredProductCalculus L K ν := by
  have : IsProbabilityMeasure ν.1 := ν.2
  refine ⟨fun X => ⟨continuous_tuple_prod F ν.1 X, ?_, ?_⟩, fun X Y h => (h.map _).prod_eq,
    fun k _ A hA => ⟨fun h hh => ⟨fun f hf => ?_, ?_⟩, fun i f f' α α' hf hf' => ⟨?_, ?_, ?_⟩, ?_⟩,
    fun X Y h => ?_, fun r Z => ?_, fun Z U => ?_⟩
  · exact (toComplexObs_mem_plaquetteCornersOver F ν.1 X).1
  · exact ⟨_, isBounded_plaquetteCornersOver F (isBounded_iUnion_tsupport X),
      (toComplexObs_mem_plaquetteCornersOver F ν.1 X).2⟩
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact ⟨(hh i).1, (hh i).2.1, subset_univ _⟩
  · refine List.pairwise_ofFn.2 fun i j hij => ?_
    exact (disjoint_of_setDistR4_ne_zero (hA (ne_of_lt hij))).mono (hh i).2.2 (hh j).2.2
  · exact ContDiff.add (ContDiff.const_smul α hf.1) (ContDiff.const_smul α' hf'.1)
  · exact (hf.2.1.union hf'.2.1).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_linComb_subset α α' f f')
  · exact (tsupport_linComb_subset α α' f f').trans (union_subset hf.2.2 hf'.2.2)
  · intro i h f f' α α' _ hf hf' h₁ h₂ h₃
    classical
    have e : ∀ (g : Fin k → ScalarField) (hg : List.ofFn g ∈ separatedSet),
        centeredProduct L K ν ⟨_, hg⟩ = ∏ j, centeredEnergy ν.1 (g j) := by
      intro g hg
      rw [centeredProduct_eq_prod]
      change ((List.ofFn g).map (centeredEnergy ν.1)).prod = _
      rw [List.map_ofFn, List.prod_ofFn]
      rfl
    have u : ∀ x : ScalarField, (fun j => centeredEnergy ν.1 (Function.update h i x j)) =
        Function.update (fun j => centeredEnergy ν.1 (h j)) i (centeredEnergy ν.1 x) := by
      intro x
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj]
    rw [e _ h₁, e _ h₂, e _ h₃, u, u, u, prod_update_eq_mul_prod_erase,
      prod_update_eq_mul_prod_erase, prod_update_eq_mul_prod_erase,
      centeredEnergy_linComb F ν.1 hf.2.1.isBounded hf'.2.1.isBounded α α']
    funext U
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  · simp [centeredProduct, concat, List.map_append, List.prod_append]
  · induction Z using Finsupp.induction_linear with
    | zero =>
      funext U
      simp [InfiniteLattice.LatticeSymmetry.actOn]
    | add Z W hZ hW =>
      rw [map_add, map_add, map_add, hZ, hW]
      rfl
    | single X z =>
      funext U
      have h := congrFun (actOn_tuple_prod F ν.1 r (hν r) X) U
      simp only [InfiniteLattice.LatticeSymmetry.actOn] at h
      simp only [centeredProductLinear, pushComb, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single, Finsupp.linearCombination_single,
        InfiniteLattice.LatticeSymmetry.actOn, Pi.smul_apply, smul_eq_mul]
      rw [centeredProduct_eq_prod, centeredProduct_eq_prod, h]
  · induction Z using Finsupp.induction_linear with
    | zero => simp [conjComb]
    | add Z W hZ hW =>
      have h : conjComb (Z + W) = conjComb Z + conjComb W := by
        ext Y
        simp [conjComb]
      rw [h, map_add, map_add, Pi.add_apply, Pi.add_apply, map_add, hZ, hW]
    | single X z =>
      simp [conjComb, Finsupp.mapRange_single, centeredProductLinear,
        Finsupp.linearCombination_single]
theorem euclidNormVec_sub_comm (x y : Space) : euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidInner_le_mul (n u : Space) : euclidInner n u ≤ euclidNormVec n * euclidNormVec u :=
  Real.sum_mul_le_sqrt_mul_sqrt _ _ _
theorem centeredProductLocality (s : Conventions.StandingParameters) (K : ℕ+)
    (ν : BorelProb (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)))
    (F : LatticeFacts (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)))
    (ha : 0 < PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) : CenteredProductLocality s K ν := by
  refine ⟨fun ϖ _ d R hd _ X hX hda r hr => ?_, fun n δ hn hδ X hX => ?_⟩
  · have hq : ((r : ℕ) : ℝ) * PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) = ϖ := by
      have hr' : ((r : ℕ) : ℝ) = ϖ / PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) := hr
      rw [hr']
      field_simp
    have hϖ : 0 ≤ ϖ := by
      rw [← hq]
      positivity
    refine ⟨?_, ?_⟩
    · refine toComplexObs_tuple_mem F ν.1 X _ fun f hf p hp y hy => ?_
      rw [InfiniteLattice.mem_centeredCube ha, hq]
      intro μ
      have hb : ‖p.center‖ < ϖ - d / 2 := by
        have h := hX.2 f hf (subset_tsupport f hp)
        simpa [centredCube, maxNorm_eq_norm] using h
      have hn : ‖(y : Space)‖ ≤ ‖(y : Space) - p.center‖ + ‖p.center‖ := by
        calc ‖(y : Space)‖ = ‖((y : Space) - p.center) + p.center‖ := by
              rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      rw [F.dist_corner p y hy] at hn
      have hμ : |(y : Space) μ| ≤ ‖(y : Space)‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (y : Space) μ
      have h := abs_le.1 (hμ.trans (show ‖(y : Space)‖ ≤ ϖ by linarith))
      exact h
    · ext x
      rw [InfiniteLattice.mem_centeredCube ha, hq, mem_ofPred_eq, maxNorm_eq_norm,
        pi_norm_le_iff_of_nonneg hϖ]
      refine forall_congr' fun μ => ?_
      rw [Real.norm_eq_abs, abs_le]
  · refine ⟨plaquetteCornersOver _ (⋃ f ∈ X.1, tsupport f),
      isBounded_plaquetteCornersOver F (isBounded_iUnion_tsupport X), ?_,
      toComplexObs_mem_plaquetteCornersOver F ν.1 X⟩
    rintro y ⟨p, hp, z, hz, rfl⟩
    obtain ⟨f, hf, hb⟩ := mem_iUnion₂.1 hp
    have h₁ : δ ≤ euclidInner n p.center := hX f hf hb
    have h₂ := euclidInner_le_mul n (p.center - (z : Space))
    rw [hn, one_mul, euclidNormVec_sub_comm, euclidNormVec_corner_sub_center ha p z hz] at h₂
    have h₃ : euclidInner n (z : Space) =
        euclidInner n p.center - euclidInner n (p.center - (z : Space)) := by
      simp [euclidInner, mul_sub, Finset.sum_sub_distrib]
    change 0 < euclidInner n (z : Space)
    rw [h₃]
    linarith
theorem norm_le_euclidNormVec (x : Space) : ‖x‖ ≤ euclidNormVec x := by apply _root_.YangMills.SharedProofs.p2512 <;> assumption
theorem euclidNormVec_le_two_mul_norm (x : Space) : euclidNormVec x ≤ 2 * ‖x‖ := by apply _root_.YangMills.SharedProofs.p35791 <;> assumption
theorem exists_pos_le_one_forall {ι : Type*} [Finite ι] (P : ι → ℝ → Prop)
    (hanti : ∀ i x y, 0 < x → x ≤ y → P i y → P i x) (h : ∀ i, ∃ d, 0 < d ∧ P i d) :
    ∃ d, 0 < d ∧ d ≤ 1 ∧ ∀ i, P i d := by
  classical
  haveI := Fintype.ofFinite ι
  choose D hD hP using h
  let S : Finset ℝ := insert 1 (Finset.univ.image D)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  refine ⟨S.min' hS, ?_, Finset.min'_le _ _ (Finset.mem_insert_self _ _), fun i => ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hD i
  · refine hanti i _ _ ?_ (Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ i)))) (hP i)
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hD i
theorem exists_pos_le_euclidNormVec_sub {A B : Set Space} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ d, 0 < d ∧ ∀ y ∈ A, ∀ z ∈ B, d ≤ euclidNormVec (y - z) := by
  obtain ⟨r, hr, hd⟩ := Metric.exists_pos_forall_lt_edist hA hB h
  refine ⟨r, by exact_mod_cast hr, fun y hy z hz => ?_⟩
  have h₁ := hd y hy z hz
  rw [edist_dist, ENNReal.lt_ofReal_iff_toReal_lt ENNReal.coe_ne_top] at h₁
  have h₂ : (r : ℝ) < dist y z := by simpa using h₁
  rw [dist_eq_norm] at h₂
  exact h₂.le.trans (norm_le_euclidNormVec _)
theorem tsupport_pt_eq (s : Conventions.StandingParameters)
    (g : AmbientPoints.Pt s AxisMirror.Ambient.euclidean → ℝ) :
    tsupport g = @tsupport Space ℝ _ _ g := by apply _root_.YangMills.SharedProofs.p14564 <;> assumption
theorem isAdmissibleAt_of (s : Conventions.StandingParameters) {d R : ℝ} (X : Tuple)
    (hb : ∀ i : Fin X.1.length, ∃ x : Space, ∀ y ∈ tsupport (X.1.get i),
      euclidNormVec (y - x) ≤ R)
    (hd : ∀ i i' : Fin X.1.length, i ≠ i' → ∀ y ∈ tsupport (X.1.get i),
      ∀ z ∈ tsupport (X.1.get i'), d ≤ euclidNormVec (y - z)) :
    IsAdmissibleAt s d R X := by
  refine ⟨fun i => ?_, fun i i' h => ?_⟩
  · obtain ⟨x, hx⟩ := hb i
    exact ⟨x, fun y hy => hx y ((tsupport_pt_eq s _).subset hy)⟩
  · exact le_iInf₂ fun y hy => le_iInf₂ fun z hz =>
      ENNReal.ofReal_le_ofReal
        (hd i i' h y ((tsupport_pt_eq s _).subset hy) z ((tsupport_pt_eq s _).subset hz))
theorem of_isAdmissibleAt {s : Conventions.StandingParameters} {d R : ℝ} {X : Tuple}
    (h : IsAdmissibleAt s d R X) :
    (∀ i : Fin X.1.length, ∃ x : Space, ∀ y ∈ tsupport (X.1.get i),
      euclidNormVec (y - x) ≤ R) ∧
    ∀ i i' : Fin X.1.length, i ≠ i' → ∀ y ∈ tsupport (X.1.get i),
      ∀ z ∈ tsupport (X.1.get i'), d ≤ euclidNormVec (y - z) := by
  refine ⟨fun i => ?_, fun i i' hi y hy z hz => ?_⟩
  · obtain ⟨x, hx⟩ := h.1 i
    exact ⟨x, fun y hy => hx ((tsupport_pt_eq s _).symm.subset hy)⟩
  · have h₁ := (h.2 i i' hi).trans (iInf₂_le_of_le y ((tsupport_pt_eq s _).symm.subset hy)
      (iInf₂_le z ((tsupport_pt_eq s _).symm.subset hz)))
    have h₂ : 0 ≤ euclidNormVec (y - z) := Real.sqrt_nonneg _
    exact (ENNReal.ofReal_le_ofReal_iff h₂).1 h₁
theorem sharpNormR4_pushFn (r : EuclidIsometry) (f : ScalarField) (M : ℝ) :
    sharpNormR4 M (pushFn r f) = sharpNormR4 M f := by
  have h₁ : TestFunctions.uniformNorm (pushFn r f) = TestFunctions.uniformNorm f :=
    (r.toPerm.symm.iSup_comp (g := fun x => ‖f x‖))
  have h₂ : TestFunctions.lipConstR4 (pushFn r f) = TestFunctions.lipConstR4 f := by
    unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
    congr 1
    ext C
    refine and_congr_right fun _ => ⟨fun h x y => ?_, fun h x y => ?_⟩
    · have e := h (r.toFun x) (r.toFun y)
      simp only [pushFn, Function.comp_apply, EuclidIsometry.symm_toFun] at e
      rwa [euclidDistR4, r.preserves_dist] at e
    · have e := h (r.symm.toFun x) (r.symm.toFun y)
      rw [euclidDistR4, r.symm.preserves_dist] at e
      exact e
  rw [sharpNormR4, sharpNormR4, h₁, h₂]
theorem isAdmissibleAt_push (s : Conventions.StandingParameters) (r : EuclidIsometry) {d R : ℝ}
    {X : Tuple} (h : IsAdmissibleAt s d R X) :
    IsAdmissibleAt s d R (push r X) := by
  obtain ⟨hb, hs⟩ := of_isAdmissibleAt h
  have e : ∀ i : Fin (push r X).1.length, ∃ i' : Fin X.1.length,
      (push r X).1.get i = pushFn r (X.1.get i') ∧ (i' : ℕ) = i := fun i =>
    ⟨⟨i, by simpa [push] using i.2⟩, List.getElem_map (l := X.1) (f := pushFn r) .., rfl⟩
  refine isAdmissibleAt_of s _ (fun i => ?_) fun i i' hi y hy z hz => ?_
  · obtain ⟨j, hj, -⟩ := e i
    obtain ⟨x, hx⟩ := hb j
    refine ⟨r.toFun x, fun y hy => ?_⟩
    rw [hj, tsupport_pushFn] at hy
    have h₁ := hx _ hy
    rw [← r.preserves_dist, EuclidIsometry.toFun_symm] at h₁
    exact h₁
  · obtain ⟨j, hj, ej⟩ := e i
    obtain ⟨j', hj', ej'⟩ := e i'
    rw [hj, tsupport_pushFn] at hy
    rw [hj', tsupport_pushFn] at hz
    have hne : j ≠ j' := fun h => hi (Fin.ext (by rw [← ej, ← ej', h]))
    have h₁ := hs j j' hne _ hy _ hz
    rw [← r.preserves_dist, EuclidIsometry.toFun_symm, EuclidIsometry.toFun_symm] at h₁
    exact h₁
theorem admissibleClassProperties (s : Conventions.StandingParameters) :
    AdmissibleClassProperties s := by
  refine ⟨fun n X => ?_, fun ϖ _ d R hd _ Y hY f hf => ?_, fun r f _ _ M => sharpNormR4_pushFn r f M,
    fun r d R _ _ X h => isAdmissibleAt_push s r h⟩
  · have hT : Bornology.IsBounded (⋃ b, ⋃ f ∈ (X b).1, tsupport f) :=
      Bornology.isBounded_iUnion.2 fun b => isBounded_iUnion_tsupport (X b)
    obtain ⟨R₀, hR₀⟩ := hT.subset_closedBall (0 : Space)
    obtain ⟨N, hN⟩ := exists_nat_gt R₀
    have hsupp : ∀ b, ∀ f ∈ (X b).1, ∀ x ∈ tsupport f, ‖x‖ < (N : ℝ) := fun b f hf x hx => by
      have h := hR₀ (mem_iUnion.2 ⟨b, mem_iUnion₂.2 ⟨f, hf, hx⟩⟩)
      rw [mem_closedBall_zero_iff] at h
      exact h.trans_lt hN
    obtain ⟨d, hd, hd1, hP⟩ := exists_pos_le_one_forall
      (ι := Σ b : Fin n, Fin (X b).1.length × Fin (X b).1.length)
      (fun c e => c.2.1 ≠ c.2.2 → ∀ y ∈ tsupport ((X c.1).1.get c.2.1),
        ∀ z ∈ tsupport ((X c.1).1.get c.2.2), e ≤ euclidNormVec (y - z))
      (fun c x y _ hxy h hc u hu v hv => hxy.trans (h hc u hu v hv))
      (fun ⟨b, i, j⟩ => by
        by_cases hij : i = j
        · exact ⟨1, one_pos, fun h => absurd hij h⟩
        · have hdis : Disjoint (tsupport ((X b).1.get i)) (tsupport ((X b).1.get j)) := by
            rcases lt_or_gt_of_ne hij with h | h
            · exact List.pairwise_iff_get.1 (X b).2.2 i j h
            · exact (List.pairwise_iff_get.1 (X b).2.2 j i h).symm
          obtain ⟨d, hd, h⟩ := exists_pos_le_euclidNormVec_sub
            ((X b).2.1 _ (List.get_mem _ _)).2.1 (isClosed_tsupport _) hdis
          exact ⟨d, hd, fun _ y hy z hz => h y hy z hz⟩)
    refine ⟨⟨N + 1, Nat.succ_pos N⟩, ?_, d, 2 * ((N : ℝ) + 1), hd, by positivity,
      fun b => ⟨?_, ?_⟩⟩
    · refine ⟨(PeriodicLattice.mem_adicGridPoints_iff _ _).2 ⟨0, (N : ℤ) + 1, ?_⟩, ?_⟩
      · simp [PeriodicLattice.meshSize]
      · change (0 : ℝ) < ((N + 1 : ℕ) : ℝ)
        positivity
    · refine isAdmissibleAt_of s _ (fun i => ⟨0, fun y hy => ?_⟩)
        fun i i' hi y hy z hz => hP ⟨b, i, i'⟩ hi y hy z hz
      have h := hsupp b _ (List.get_mem _ _) y hy
      rw [sub_zero]
      have h₂ := euclidNormVec_le_two_mul_norm y
      linarith
    · intro f hf x hx
      have h := hsupp b f hf x hx
      change maxNorm x < ((N + 1 : ℕ) : ℝ) - d / 2
      rw [maxNorm_eq_norm]
      push_cast
      linarith
  · intro x hx
    have h := hY.2 f hf hx
    change maxNorm x < ϖ - d / 2 at h
    change maxNorm x < ϖ
    linarith
theorem isSymmetricUnder_of_isMotionInvariant {a : ℝ} (F : LatticeFacts a)
    {ν : Measure (GaugeField a)}
    (h : InfiniteLattice.PeriodicGibbsSymmetries.IsMotionInvariant ν)
    (r : LatticeSymmetry a) : InfiniteLattice.IsSymmetricUnder ν r := by
  have hm : r.toFun ∈ InfiniteLattice.latticeMotions a := by
    rw [InfiniteLattice.latticeMotions_eq_latticeMotions]
    exact (F.motions_iff _).1 ⟨r, rfl⟩
  exact h ⟨r.toFun, hm⟩
theorem statement_holds
    (h₁ : InfiniteLattice.CutoffStructure.FieldSpaceAndSymmetries)
    (h₂ : FieldsAtSpacing.LinkFunctionsStatement)
    (h₃ : InfiniteLattice.PeriodicGibbsSymmetries.Statement)
    (h₄ : GibbsAtFixedSpacing.SymmetriesTransportLinksSupportsAndPlaquettes) :
    Statement := by
  intro s K β ν hβ hν
  have hL : (0 : ℝ) < s.L := by
    have : 0 < s.L := by
      have := s.isAdmissible.2
      omega
    exact_mod_cast this
  have ha : 0 < PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) := zpow_pos hL _
  have F : LatticeFacts (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) := latticeFacts_of h₁ h₂ ha
  have hinv := (h₃ _ ha β hβ).1 ν.1 hν
  exact ⟨smearedEnergyStructure F ha, symmetryCovariance F (h₄ _ ha).2.2,
    centeredProductCalculus ν F (isSymmetricUnder_of_isMotionInvariant F hinv.1),
    centeredProductLocality s K ν F ha, admissibleClassProperties s⟩
end YangMills.Construction.ReflectionPositivity.LatticeRepresentatives
