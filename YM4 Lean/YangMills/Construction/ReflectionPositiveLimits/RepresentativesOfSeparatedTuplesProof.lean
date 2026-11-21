import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.SpacePlaquettesFunctionsOfPlaquettesAndLatticeIsometries
import YangMills.Construction.ReflectionPositiveLimits.RepresentativesOfSeparatedTuples
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TupleRepresentatives
open InfiniteLattice (GaugeField LatticeSymmetry ElementaryPlaquette LatticePoint regionObservables
  boundedRegionObservables faceEnergy regionSigma smearedEnergy shift)
open FieldsAtSpacing (ContainsCorners faceFunction)
open GibbsAtFixedSpacing (BorelProb)
variable {a : ℝ}
structure Facts (a : ℝ) : Prop where
  compact : CompactSpace (GaugeField a)
  finite_centers : ∀ S : Set Space, Bornology.IsBounded S →
    {p : ElementaryPlaquette a | p.center ∈ S}.Finite
  dist_corner : ∀ p : ElementaryPlaquette a, ∀ y ∈ p.cornerSet, ‖(y : Space) - p.center‖ = a / 2
  continuous_energy : ∀ p : ElementaryPlaquette a, Continuous fun U : GaugeField a => faceEnergy U p
  bijective_map : ∀ r : LatticeSymmetry a, Function.Bijective r.plaquetteMap
  center_map : ∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a),
    (r.plaquetteMap p).center = r.toFun p.center
  energy_pullback : ∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a) (U : GaugeField a),
    faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p)
  corner_measurable : ∀ (p : ElementaryPlaquette a) (S : Set Space), ContainsCorners S p →
    faceFunction p ∈ boundedRegionObservables a S
theorem facts_of
    (h₁ : InfiniteLattice.CutoffStructure.FieldSpaceAndSymmetries)
    (h₂ : FieldsAtSpacing.LinkFunctionsStatement) (ha : 0 < a) : Facts a := by
  obtain ⟨hs, hp, hf, hi, hc, -⟩ := h₁ a ha
  have hr := (h₂ a ha ∅ (empty_subset _)).2.2.2.2.2
  exact
    { compact := hs.2.2.2.2.2.2.1
      finite_centers := fun S hS => (hp.2.2 S hS).2
      dist_corner := hp.2.1
      continuous_energy := fun p => (hf p).2.2.1
      bijective_map := fun r => (hi.2 r).2.2.2.1
      center_map := fun r => (hi.2 r).2.2.2.2.1
      energy_pullback := hc.1
      corner_measurable := fun p S hS => (hr.1 p).2.2 S hS }
def shiftedSum (c : ℝ) (f : ScalarField) (U : GaugeField a) : ℝ :=
  ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - c)
theorem finite_center_ne_zero (F : Facts a) {f : ScalarField} (hf : IsCompact (tsupport f)) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite :=
  (F.finite_centers _ hf.isBounded).subset fun _ hp => subset_tsupport f hp
theorem shiftedSum_eq_finset_sum (c : ℝ) (f : ScalarField) (U : GaugeField a)
    (P : Finset (ElementaryPlaquette a)) (hP : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P) :
    shiftedSum c f U = ∑ p ∈ P, f p.center * (faceEnergy U p - c) := by
  refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
  have h : f p.center ≠ 0 := fun h => hp (by simp [h])
  exact hP p h
theorem shiftedSum_eq_fun (F : Facts a) (c : ℝ) {f : ScalarField}
    (hf : IsCompact (tsupport f)) :
    (shiftedSum c f : GaugeField a → ℝ) = fun U : GaugeField a =>
      ∑ p ∈ (finite_center_ne_zero F hf).toFinset, f p.center * (faceEnergy U p - c) :=
  funext fun U => shiftedSum_eq_finset_sum c f U _ fun _ hp =>
    (finite_center_ne_zero F hf).mem_toFinset.2 hp
theorem continuous_shiftedSum (F : Facts a) (c : ℝ) {f : ScalarField}
    (hf : IsCompact (tsupport f)) : Continuous (shiftedSum c f : GaugeField a → ℝ) := by
  rw [shiftedSum_eq_fun F c hf]
  exact continuous_finsetSum _ fun p _ =>
    continuous_const.mul ((F.continuous_energy p).sub continuous_const)
theorem measurable_finset_weighted_sum {Ω ι : Type*} [MeasurableSpace Ω] (P : Finset ι)
    (w : ι → ℝ) (g : ι → Ω → ℝ) (c : ℝ) (h : ∀ i ∈ P, Measurable (g i)) :
    Measurable fun U => ∑ i ∈ P, w i * (g i U - c) :=
  Finset.measurable_fun_sum _ fun i hi => ((h i hi).sub_const c).const_mul (w i)
theorem measurable_shiftedSum (F : Facts a) (c : ℝ) {f : ScalarField}
    (hf : IsCompact (tsupport f)) (S : Set Space)
    (hS : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → ContainsCorners S p) :
    Measurable[regionSigma S] (shiftedSum c f : GaugeField a → ℝ) := by
  rw [shiftedSum_eq_fun F c hf]
  refine @measurable_finset_weighted_sum _ _ (regionSigma S) _ (fun p => f p.center)
    (fun p U => faceEnergy U p) c fun p hp => ?_
  have h := (F.corner_measurable p S (hS p ((finite_center_ne_zero F hf).mem_toFinset.1 hp))).2
  have e : (fun U : GaugeField a => faceEnergy U p) = Complex.re ∘ faceFunction p := by
    funext U
    simp [faceFunction]
  rw [e]
  exact Complex.measurable_re.comp h
theorem list_map_prod_apply {Ω ι : Type*} (Φ : ι → Ω → ℝ) (l : List ι) (U : Ω) :
    (l.map Φ).prod U = (l.map fun f => Φ f U).prod := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih]
theorem continuous_list_map_prod {Ω ι : Type*} [TopologicalSpace Ω] (Φ : ι → Ω → ℝ) (l : List ι)
    (h : ∀ f ∈ l, Continuous (Φ f)) : Continuous (l.map Φ).prod := by
  induction l with
  | nil => exact continuous_const
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))
theorem measurable_list_map_prod {Ω ι : Type*} [MeasurableSpace Ω] (Φ : ι → Ω → ℝ) (l : List ι)
    (h : ∀ f ∈ l, Measurable (Φ f)) : Measurable (l.map Φ).prod := by
  induction l with
  | nil => exact measurable_const
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))
theorem isCompact_tsupport_of_mem {X : Tuple} {f : ScalarField} (hf : f ∈ X.1) :
    IsCompact (tsupport f) :=
  (X.2.1 f hf).2.1
theorem continuous_tuple_prod (F : Facts a) (c : ℝ) (X : Tuple) :
    Continuous (X.1.map (shiftedSum c)).prod (X := GaugeField a) :=
  continuous_list_map_prod _ _ fun _ hf => continuous_shiftedSum F c (isCompact_tsupport_of_mem hf)
theorem integrable_of_continuous_fn (F : Facts a) (ν : Measure (GaugeField a))
    [IsFiniteMeasure ν] {g : GaugeField a → ℝ} (hg : Continuous g) : Integrable g ν := by
  have := F.compact
  exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
theorem tuple_prod_mem_regionObservables (F : Facts a) (c : ℝ) (X : Tuple) (S : Set Space)
    (hS : ∀ f ∈ X.1, ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → ContainsCorners S p) :
    (fun U : GaugeField a => (((X.1.map (shiftedSum c)).prod U : ℝ) : ℂ)) ∈
      regionObservables a S := by
  have := F.compact
  have hc : Continuous fun U : GaugeField a => (((X.1.map (shiftedSum c)).prod U : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_tuple_prod F c X)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⟨hc.measurable, C, fun U => hC U (mem_univ U)⟩, ?_⟩
  refine Complex.measurable_ofReal.comp ?_
  exact @measurable_list_map_prod _ _ (regionSigma S) _ _ fun f hf =>
    measurable_shiftedSum F c (isCompact_tsupport_of_mem hf) S (hS f hf)
theorem actOn_shiftedSum (F : Facts a) (c : ℝ) (r : LatticeSymmetry a)
    (f : ScalarField) :
    r.actOn (shiftedSum c f : GaugeField a → ℝ) =
      shiftedSum c (pushFn (latticeSymmetryToEuclid r) f) := by
  funext U
  let e : ElementaryPlaquette a ≃ ElementaryPlaquette a :=
    Equiv.ofBijective r.plaquetteMap (F.bijective_map r)
  change ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy (r.pullbackField U) p - c) =
    ∑ᶠ p : ElementaryPlaquette a, pushFn (latticeSymmetryToEuclid r) f p.center *
      (faceEnergy U p - c)
  refine Eq.trans (finsum_congr fun p => ?_) (finsum_comp_equiv e)
  have hb : (e p).center = (latticeSymmetryToEuclid r).toFun p.center :=
    F.center_map r p
  have hm : pushFn (latticeSymmetryToEuclid r) f (e p).center = f p.center := by
    rw [hb]
    simp only [pushFn, Function.comp_apply, EuclidIsometry.symm_toFun]
  rw [hm, F.energy_pullback r p U]
  rfl
theorem actOn_tuple_prod (F : Facts a) (c : ℝ) (r : LatticeSymmetry a) (X : Tuple) :
    r.actOn ((X.1.map (shiftedSum c)).prod : GaugeField a → ℝ) =
      ((push (latticeSymmetryToEuclid r) X).1.map (shiftedSum c)).prod := by
  funext U
  have h : ∀ g : ScalarField, shiftedSum c g (r.pullbackField U) =
      shiftedSum c (pushFn (latticeSymmetryToEuclid r) g) U :=
    fun g => congrFun (actOn_shiftedSum F c r g) U
  change (X.1.map (shiftedSum c)).prod (r.pullbackField U) = _
  rw [list_map_prod_apply, list_map_prod_apply]
  simp only [push, List.map_map, Function.comp_def, h]
theorem shiftedSum_linear (F : Facts a) (c : ℝ) {f f' : ScalarField}
    (hf : IsCompact (tsupport f)) (hf' : IsCompact (tsupport f')) (α α' : ℝ)
    (U : GaugeField a) :
    shiftedSum c (α • f + α' • f') U =
      α * shiftedSum c f U + α' * shiftedSum c f' U := by
  classical
  set P := (finite_center_ne_zero (a := a) F hf).toFinset ∪
    (finite_center_ne_zero (a := a) F hf').toFinset
  have h₁ : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P := fun p hp =>
    Finset.mem_union_left _ ((finite_center_ne_zero F hf).mem_toFinset.2 hp)
  have h₂ : ∀ p : ElementaryPlaquette a, f' p.center ≠ 0 → p ∈ P := fun p hp =>
    Finset.mem_union_right _ ((finite_center_ne_zero F hf').mem_toFinset.2 hp)
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
  rw [shiftedSum_eq_finset_sum c _ U P h₃, shiftedSum_eq_finset_sum c _ U P h₁,
    shiftedSum_eq_finset_sum c _ U P h₂, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem shiftedSum_of_mean (F : Facts a) (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (c : ℝ) (hc : ∀ p : ElementaryPlaquette a, c = ∫ U, faceEnergy U p ∂ν) {f : ScalarField}
    (hf : IsCompact (tsupport f)) :
    (shiftedSum c f : GaugeField a → ℝ) =
      fun U : GaugeField a => smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν := by
  classical
  set P := (finite_center_ne_zero (a := a) F hf).toFinset
  have hP : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → p ∈ P := fun p hp =>
    (finite_center_ne_zero F hf).mem_toFinset.2 hp
  have hd : ∀ U : GaugeField a, smearedEnergy f U =
      ∑ p ∈ P, faceEnergy U p * f p.center := by
    intro U
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    have h : f p.center ≠ 0 := fun h => hp (by simp [h])
    exact hP p h
  have hi : ∫ V, smearedEnergy f V ∂ν = ∑ p ∈ P, c * f p.center := by
    simp only [hd]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [integral_mul_const, ← hc p]
    · exact fun p _ => (integrable_of_continuous_fn F ν (F.continuous_energy p)).mul_const _
  funext U
  rw [shiftedSum_eq_finset_sum c f U P hP, hi, hd U, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring
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
section Requirements
variable {L : ℕ} (A : LatticeSequence L) (j : ℕ+)
theorem rep_eq (X : Tuple) :
    A.rep j X = (X.1.map (shiftedSum (A.shift j))).prod :=
  rfl
theorem smeared_finite_continuous (F : Facts (A.mesh j)) : A.SmearedFiniteAndContinuous j := by
  intro f hf
  refine ⟨(finite_center_ne_zero F hf.2).subset fun p hp h => hp ?_,
    continuous_shiftedSum F (A.shift j) hf.2⟩
  funext U
  have h' : f p.center = 0 := by simpa using h
  simp [h']
theorem rep_continuous_local (F : Facts (A.mesh j)) :
    A.RepContinuousLocal j := by
  intro X
  have hT : Bornology.IsBounded (⋃ f ∈ {f | f ∈ X.1}, tsupport f) :=
    (Bornology.isBounded_biUnion (List.finite_toSet X.1)).2 fun f hf =>
      (isCompact_tsupport_of_mem hf).isBounded
  obtain ⟨R, hR⟩ := hT.subset_closedBall (0 : Space)
  have hobs := tuple_prod_mem_regionObservables F (A.shift j) X
    (Metric.closedBall 0 (A.mesh j / 2 + R)) (fun f hf p hp y hy => by
      have hb : p.center ∈ Metric.closedBall (0 : Space) R :=
        hR (mem_iUnion₂.2 ⟨f, hf, subset_tsupport f hp⟩)
      rw [mem_closedBall_zero_iff] at hb ⊢
      calc ‖(y : Space)‖ = ‖((y : Space) - p.center) + p.center‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖(y : Space) - p.center‖ + ‖p.center‖ := norm_add_le _ _
        _ ≤ A.mesh j / 2 + R := by
            rw [F.dist_corner p y hy]
            linarith)
  exact ⟨Complex.continuous_ofReal.comp (continuous_tuple_prod F (A.shift j) X), hobs.1, _,
    Metric.isBounded_closedBall, hobs.2⟩
theorem rep_localized (F : Facts (A.mesh j)) :
    A.RepLocalizedNearSupports j := by
  intro X
  refine ⟨fun _ => ?_, fun hT => ?_⟩
  · refine tuple_prod_mem_regionObservables F (A.shift j) X _ fun f hf p hp y hy => ?_
    have hb : p.center ∈ ⋃ f ∈ X.1, tsupport f :=
      mem_iUnion₂.2 ⟨f, hf, subset_tsupport f hp⟩
    change maxNormInfDist _ _ ≤ _
    have hbd : BddBelow ((fun x' => maxNorm ((y : Space) - x')) '' ⋃ f ∈ X.1, tsupport f) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨x', -, rfl⟩
      beta_reduce
      rw [maxNorm_eq_norm]
      exact norm_nonneg _
    have hm : maxNorm ((y : Space) - p.center) ∈
        (fun x' => maxNorm ((y : Space) - x')) '' ⋃ f ∈ X.1, tsupport f :=
      ⟨p.center, hb, rfl⟩
    refine (csInf_le hbd hm).trans_eq ?_
    rw [maxNorm_eq_norm]
    exact F.dist_corner p y hy
  · obtain ⟨l, hl⟩ := X
    cases l with
    | nil => exact ⟨1, fun U => by simp [LatticeSequence.rep]⟩
    | cons f l =>
      have hf0 : ∀ x, f x = 0 := fun x => image_eq_zero_of_notMem_tsupport fun hx => by
        have h : x ∈ ⋃ g ∈ f :: l, tsupport g := mem_iUnion₂.2 ⟨f, by simp, hx⟩
        rw [hT] at h
        exact h
      refine ⟨0, fun U => ?_⟩
      have h : A.smeared j f U = 0 := by simp [LatticeSequence.smeared, hf0]
      simp [LatticeSequence.rep, h]
theorem actOn_rep (F : Facts (A.mesh j)) (r : LatticeSymmetry (A.mesh j))
    (X : Tuple) :
    r.actOn (A.rep j X) =
      A.rep j (push (latticeSymmetryToEuclid r) X) :=
  actOn_tuple_prod F (A.shift j) r X
theorem rep_comm_symmetries (F : Facts (A.mesh j)) :
    A.RepCommutesWithSymmetries j := by
  intro r Z
  induction Z using Finsupp.induction_linear with
  | zero =>
    funext U
    simp [LatticeSymmetry.actOn]
  | add Z W hZ hW =>
    rw [map_add, map_add, map_add, ← hZ, ← hW]
    rfl
  | single X z =>
    funext U
    have h := congrFun (actOn_rep A j F r X) U
    simp only [LatticeSymmetry.actOn] at h
    simp only [LatticeSequence.repComb, pushComb,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      LatticeSymmetry.actOn, Pi.smul_apply, smul_eq_mul, h]
theorem rep_concat : A.RepConcatEqMul j := by
  intro X Y h
  simp [LatticeSequence.rep, concat, List.map_append, List.prod_append]
theorem rep_conj : A.RepConjEqConj j := by
  intro Z
  induction Z using Finsupp.induction_linear with
  | zero =>
    funext U
    simp [conjComb]
  | add Z W hZ hW =>
    have h : conjComb (Z + W) = conjComb Z + conjComb W := by
      ext Y
      simp [conjComb]
    rw [h, map_add, hZ, hW]
    funext U
    simp [map_add]
  | single X z =>
    funext U
    simp [conjComb, Finsupp.mapRange_single, LatticeSequence.repComb,
      Finsupp.linearCombination_single]
theorem mean_perm_invariant : IsPermInvariant (A.mean j) := by
  intro X Y h
  have e : A.rep j X = A.rep j Y := (h.map _).prod_eq
  simp only [LatticeSequence.mean, e]
theorem mean_slot_linear (F : Facts (A.mesh j)) : IsSlotLinear (A.mean j) := by
  intro pre post f f' α α' h h'
  have : IsProbabilityMeasure (A.measure j).1 := (A.measure j).2
  have hf : IsCompact (tsupport f) := (h.1 f (by simp)).2.1
  have hf' : IsCompact (tsupport f') := (h'.1 f' (by simp)).2.1
  have key : ∀ U, A.rep j ⟨pre ++ (α • f + α' • f') :: post, linComb_mem α α' h h'⟩ U =
      α * A.rep j ⟨_, h⟩ U + α' * A.rep j ⟨_, h'⟩ U := by
    intro U
    simp only [rep_eq, List.map_append, List.map_cons, List.prod_append,
      List.prod_cons, Pi.mul_apply, shiftedSum_linear F (A.shift j) hf hf' α α' U]
    ring
  have i₁ : Integrable (A.rep j ⟨_, h⟩) (A.measure j).1 :=
    integrable_of_continuous_fn F _ (continuous_tuple_prod F (A.shift j) ⟨_, h⟩)
  have i₂ : Integrable (A.rep j ⟨_, h'⟩) (A.measure j).1 :=
    integrable_of_continuous_fn F _ (continuous_tuple_prod F (A.shift j) ⟨_, h'⟩)
  calc A.mean j ⟨pre ++ (α • f + α' • f') :: post, linComb_mem α α' h h'⟩
      = ∫ U, (α * A.rep j ⟨_, h⟩ U + α' * A.rep j ⟨_, h'⟩ U)
          ∂(A.measure j).1 := integral_congr_ae (Filter.Eventually.of_forall key)
    _ = (∫ U, α * A.rep j ⟨_, h⟩ U ∂(A.measure j).1) +
          ∫ U, α' * A.rep j ⟨_, h'⟩ U ∂(A.measure j).1 :=
        integral_add (i₁.const_mul α) (i₂.const_mul α')
    _ = α * A.mean j ⟨_, h⟩ + α' * A.mean j ⟨_, h'⟩ :=
        congrArg₂ (· + ·) (integral_const_mul α _) (integral_const_mul α' _)
theorem shift_at_mean (F : Facts (A.mesh j)) :
    A.CenteringAtPlaquetteMean j := by
  intro ν _ hc
  have : IsProbabilityMeasure ν.1 := ν.2
  have hfield : ∀ f : ScalarField, IsCompact (tsupport f) → A.smeared j f =
      fun U => smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν.1 :=
    fun f hf => shiftedSum_of_mean F ν.1 (A.shift j) hc hf
  refine ⟨fun f hf => hfield f hf.2, fun X => ?_⟩
  unfold LatticeSequence.rep centeredProduct
  congr 1
  exact List.map_congr_left fun f hf => hfield f (isCompact_tsupport_of_mem hf)
end Requirements
theorem holds
    (h₁ : InfiniteLattice.CutoffStructure.FieldSpaceAndSymmetries)
    (h₂ : FieldsAtSpacing.LinkFunctionsStatement) : Statement := by
  intro L _ hL A j
  have hL' : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have ha : 0 < A.mesh j := zpow_pos hL' _
  have F : Facts (A.mesh j) := facts_of h₁ h₂ ha
  exact ⟨smeared_finite_continuous A j F, rep_continuous_local A j F, rep_localized A j F,
    rep_comm_symmetries A j F, rep_concat A j, rep_conj A j,
    fun v X => actOn_rep A j F (shift v) X,
    fun P X => actOn_rep A j F P.reflect X,
    fun w hw => by
      obtain ⟨π, s, rfl⟩ := hw
      exact ⟨signedPermSymmetry _ π s, rfl, fun X => actOn_rep A j F _ X⟩,
    mean_perm_invariant A j, mean_slot_linear A j F, shift_at_mean A j F⟩
end YangMills.Construction.ReflectionPositivity.TupleRepresentatives
