import YangMills.Construction.Continuum.ValueOfAFunctionalAtARecentredTuple
import YangMills.Construction.InfiniteLattice.SpacePlaquettesFunctionsOfPlaquettesAndLatticeIsometries
import YangMills.Construction.InfiniteLattice.StatesReflectionPositiveAtEveryLatticeMirror
import YangMills.Construction.ReflectionPositivity.ApproximationCentredAtThePlaquetteMeans
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBounded
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentatives
import YangMills.Construction.ReflectionPositivity.SymmetriesAndMirrorsOfTheLimit
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CentredMeansProof
open YangMills.Construction.InfiniteLattice (GaugeField ElementaryPlaquette AmbientSpace
  refinedSpacing faceEnergy)
open YangMills.Construction.InfiniteLattice.CutoffStructure (PlaquetteGeometry
  FaceEnergyProperties)
open YangMills.Construction.LimitConventions (ApproxTriple)
open YangMills.Construction.ReflectionPositivity.ApproximatingSequences (LatticeApproximation)
open YangMills.Construction.TupleLists (ofList ofList_toList toList
  get_mem_disjointSupportTuples)
open YangMills.Construction.TestSpaces (IsMultilinearSepFunctional SepTupleOfCard c1CompactSupp
  centredPartFunctional componentCumulantOne cumulantOne_eq singletonSepTuple centredTuple
  centringCoeff)
open YangMills.Construction.SeparatedTuples (FormalSpan TupleFunctional RealValued basisVec)
section Expansion
variable {R : Type*} [CommRing R]
theorem list_prod_map_eq_prod_get (h : RealValued → R) (X : List RealValued) :
    (X.map h).prod = ∏ l : Fin X.length, h (X.get l) := by
  induction X with
  | nil => simp
  | cons f X ih =>
    have hs : ∏ l : Fin (f :: X).length, h ((f :: X).get l) =
        h f * ∏ l : Fin X.length, h (X.get l) :=
      Fin.prod_univ_succ fun l : Fin (X.length + 1) => h ((f :: X).get l)
    rw [List.map_cons, List.prod_cons, ih, hs]
theorem list_prod_filter_zipIdx_eq_prod_ite (g : RealValued → R) (A : Finset ℕ)
    (X : List RealValued) (n : ℕ) :
    ((((X.zipIdx n).filter fun p => p.2 ∈ A).map Prod.fst).map g).prod =
      ∏ l : Fin X.length, if (l : ℕ) + n ∈ A then g (X.get l) else 1 := by
  induction X generalizing n with
  | nil => simp
  | cons f X ih =>
    have hs : (∏ l : Fin (f :: X).length, if (l : ℕ) + n ∈ A then g ((f :: X).get l) else 1) =
        (if n ∈ A then g f else 1) *
          ∏ l : Fin X.length, if (l : ℕ) + (n + 1) ∈ A then g (X.get l) else 1 := by
      refine (Fin.prod_univ_succ fun l : Fin (X.length + 1) =>
        if (l : ℕ) + n ∈ A then g ((f :: X).get l) else 1).trans ?_
      simp only [Fin.val_zero, zero_add, Fin.val_succ]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [show (l : ℕ) + 1 + n = (l : ℕ) + (n + 1) by omega]
      rfl
    rw [List.zipIdx_cons, hs, ← ih (n + 1)]
    by_cases hn : n ∈ A
    · simp [hn]
    · simp [hn]
theorem prod_map_sublistOn (g : RealValued → R) (A : Finset ℕ) (X : List RealValued) :
    ((SeparatedTuples.SepTuple.sublistOn X A).map g).prod =
      ∏ l ∈ Finset.univ.filter (fun l : Fin X.length => (l : ℕ) + 1 ∈ A), g (X.get l) := by
  rw [Finset.prod_filter]
  exact list_prod_filter_zipIdx_eq_prod_ite g A X 1
theorem prod_sub_eq_sum_powerset (g c : RealValued → R) (X : List RealValued) :
    (X.map fun f => g f - c f).prod =
      ∑ A ∈ (Finset.Icc 1 X.length).powerset,
        (∏ l ∈ Finset.univ.filter (fun l : Fin X.length => (l : ℕ) + 1 ∉ A), -c (X.get l)) *
          ((SeparatedTuples.SepTuple.sublistOn X A).map g).prod := by
  classical
  have hmem : ∀ (t : Finset (Fin X.length)) (l : Fin X.length),
      (l : ℕ) + 1 ∈ t.image (fun i : Fin X.length => (i : ℕ) + 1) ↔ l ∈ t := by
    intro t l
    simp only [Finset.mem_image, add_left_inj]
    constructor
    · rintro ⟨i, hi, h⟩
      rwa [← Fin.ext h]
    · exact fun h => ⟨l, h, rfl⟩
  rw [list_prod_map_eq_prod_get]
  simp only [sub_eq_add_neg]
  rw [Finset.prod_add]
  refine Finset.sum_nbij' (fun t => t.image fun i : Fin X.length => (i : ℕ) + 1)
    (fun A => Finset.univ.filter fun l : Fin X.length => (l : ℕ) + 1 ∈ A) ?_ ?_ ?_ ?_ ?_
  · intro t _
    refine Finset.mem_powerset.2 fun i hi => ?_
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hi
    have := l.2
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro A _
    exact Finset.mem_powerset.2 (Finset.subset_univ _)
  · intro t _
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
  · intro A hA
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact hl
    · intro hi
      have := Finset.mem_Icc.1 (Finset.mem_powerset.1 hA hi)
      exact ⟨⟨i - 1, by omega⟩, by simpa [show i - 1 + 1 = i by omega] using hi,
        by simp; omega⟩
  · intro t _
    rw [prod_map_sublistOn, mul_comm]
    congr 1
    · refine Finset.prod_congr ?_ fun _ _ => rfl
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem, Finset.mem_sdiff]
    · refine Finset.prod_congr ?_ fun _ _ => rfl
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem, Finset.mem_sdiff]
end Expansion
section Field
variable {a : ℝ}
theorem exists_finset_finsum_eq_sum (hP : PlaquetteGeometry a) {f : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) :
    ∃ S : Finset (ElementaryPlaquette a), ∀ (c : ℝ) (U : GaugeField a),
      ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - c) =
        ∑ p ∈ S, f p.center * (faceEnergy U p - c) := by
  have hfin : {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite :=
    (hP.2.2 _ hf.isCompact.isBounded).2.subset fun _ hp => subset_tsupport f hp
  refine ⟨hfin.toFinset, fun c U => finsum_eq_sum_of_support_subset _ ?_⟩
  intro p hp
  simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
  intro h0
  exact hp (by simp [h0])
theorem integrable_faceEnergy (hF : FaceEnergyProperties a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] (p : ElementaryPlaquette a) :
    Integrable (fun U : GaugeField a => faceEnergy U p) ν := by
  obtain ⟨-, hb, hc, -⟩ := hF p
  refine Integrable.of_bound hc.measurable.aestronglyMeasurable 2
    (Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have := hb U
  exact ⟨by linarith [this.1], this.2⟩
theorem integral_and_shift_of_smeared (hP : PlaquetteGeometry a) (hF : FaceEnergyProperties a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] {o : ℝ}
    (hm : ∀ p : ElementaryPlaquette a, ∫ U, faceEnergy U p ∂ν = o) {f : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) :
    ∃ S : Finset (ElementaryPlaquette a), ∀ c : ℝ,
      ∫ U, (∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - c)) ∂ν =
          ∑ p ∈ S, f p.center * (o - c) ∧
      ∀ U : GaugeField a,
        ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - o) =
          (∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - c)) -
            ∑ p ∈ S, f p.center * (o - c) := by
  obtain ⟨S, hS⟩ := exists_finset_finsum_eq_sum hP hf
  refine ⟨S, fun c => ⟨?_, fun U => ?_⟩⟩
  · simp only [hS c]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [integral_const_mul, integral_sub (integrable_faceEnergy hF ν p)
        (integrable_const c), hm p]
      simp
    · exact fun p _ =>
        ((integrable_faceEnergy hF ν p).sub (integrable_const c)).const_mul _
  · rw [hS o, hS c, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
end Field
section Triple
variable {L : ℕ} (T : ApproxTriple L)
theorem smearedField_eq_finsum (j : ℕ+) (f : AmbientSpace → ℝ)
    (U : GaugeField (refinedSpacing L (T.cutoff j))) :
    LatticeApproximation.smearedField T j f U =
      ∑ᶠ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
        f p.center * (faceEnergy U p - T.offset j) := rfl
theorem integral_smearedField_eq_zero {j : ℕ+}
    (hP : PlaquetteGeometry (refinedSpacing L (T.cutoff j)))
    (hF : FaceEnergyProperties (refinedSpacing L (T.cutoff j)))
    (hm : ∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      ∫ U, faceEnergy U p ∂T.state j = T.offset j)
    {f : AmbientSpace → ℝ} (hf : HasCompactSupport f) :
    ∫ U, LatticeApproximation.smearedField T j f U ∂T.state j = 0 := by
  obtain ⟨S, hS⟩ := integral_and_shift_of_smeared hP hF (T.state j) hm hf
  simp only [smearedField_eq_finsum]
  rw [(hS (T.offset j)).1]
  simp
theorem smearedField_offset_mean {j : ℕ+} (ō : ℕ+ → ℝ)
    (hP : PlaquetteGeometry (refinedSpacing L (T.cutoff j)))
    (hF : FaceEnergyProperties (refinedSpacing L (T.cutoff j)))
    (hm : ∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      ∫ U, faceEnergy U p ∂T.state j = ō j)
    {f : AmbientSpace → ℝ} (hf : HasCompactSupport f)
    (U : GaugeField (refinedSpacing L (T.cutoff j))) :
    LatticeApproximation.smearedField ({ T with offset := ō } : ApproxTriple L) j f U =
      LatticeApproximation.smearedField T j f U -
        ∫ V, LatticeApproximation.smearedField T j f V ∂T.state j := by
  obtain ⟨S, hS⟩ := integral_and_shift_of_smeared hP hF (T.state j) hm hf
  have h1 := (hS (T.offset j)).1
  have h2 := (hS (T.offset j)).2 U
  simp only [smearedField_eq_finsum]
  rw [h1]
  exact h2
theorem tupleRep_offset_mean {j : ℕ+} (ō : ℕ+ → ℝ)
    (hP : PlaquetteGeometry (refinedSpacing L (T.cutoff j)))
    (hF : FaceEnergyProperties (refinedSpacing L (T.cutoff j)))
    (hm : ∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      ∫ U, faceEnergy U p ∂T.state j = ō j)
    (X : SeparatedTuples.SepTuple) (U : GaugeField (refinedSpacing L (T.cutoff j))) :
    ApproxTriple.tupleRep ({ T with offset := ō } : ApproxTriple L) j X U =
      ∑ A ∈ (Finset.Icc 1 X.1.length).powerset,
        (∏ l ∈ Finset.univ.filter (fun l : Fin X.1.length => (l : ℕ) + 1 ∉ A),
          -∫ V, LatticeApproximation.smearedField T j (X.1.get l) V ∂T.state j) *
          ApproxTriple.tupleRep T j (X.subtuple A) U := by
  have h := prod_sub_eq_sum_powerset (fun f => LatticeApproximation.smearedField T j f U)
    (fun f => ∫ V, LatticeApproximation.smearedField T j f V ∂T.state j) X.1
  refine Eq.trans ?_ h
  change (X.1.map fun f => LatticeApproximation.smearedField
    ({ T with offset := ō } : ApproxTriple L) j f U).prod = _
  congr 1
  refine List.map_congr_left fun f hf => ?_
  exact smearedField_offset_mean T ō hP hF hm (X.2.1 f hf).2 U
end Triple
section Forms
theorem ofFn_eq_take_append_cons_drop_of_agree {E : Type*} {n : ℕ} (i : Fin n) (X W : Fin n → E)
    (h : ∀ k, k ≠ i → W k = X k) :
    List.ofFn W = (List.ofFn X).take i ++ W i :: (List.ofFn X).drop (i + 1) := by
  have hset : List.ofFn W = (List.ofFn X).set i (W i) := by
    refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
    have hk : k < n := by simpa using h₁
    by_cases hki : (i : ℕ) = k
    · subst hki
      simp
    · have hne : (⟨k, hk⟩ : Fin n) ≠ i := fun e => hki (by rw [← e])
      simp [List.getElem_set, hki, h _ hne]
  rw [hset, List.set_eq_take_append_cons_drop, if_pos (by simp)]
theorem isMultilinearSepFunctional_of_tupleFunctional (s : TestSpaces.SepTuple → ℝ)
    (F : TupleFunctional) (hF : ∀ X, F X = s (ofList X)) (hm : F.IsEntrywiseLinear) :
    IsMultilinearSepFunctional s := by
  refine ⟨?_, fun n _ i b b' X X' X'' h₁ h₂ h₃ => ?_⟩
  · rw [← TestSpaces.ofList_sepTupleNil, ← hF]
    exact F.map_nil
  · have hv : ∀ Y : SepTupleOfCard n, s ⟨n, Y⟩ = F (toList ⟨n, Y⟩) := fun Y => by
      rw [hF, ofList_toList]
    simp only [hv]
    refine hm ((List.ofFn X.1).take i) ((List.ofFn X.1).drop (i + 1)) (X.1 i) (X'.1 i) b b'
      (toList ⟨n, X⟩) (toList ⟨n, X'⟩) (toList ⟨n, X''⟩)
      (ofFn_eq_take_append_cons_drop_of_agree i X.1 X.1 fun _ _ => rfl)
      (ofFn_eq_take_append_cons_drop_of_agree i X.1 X'.1 fun k hk => (h₁ k hk).symm) ?_
    have := ofFn_eq_take_append_cons_drop_of_agree i X.1 X''.1 h₃
    rw [h₂] at this
    exact this
end Forms
theorem centredPartFunctional_eq_sum (hValue : CentredTupleValue.centredValueFormula)
    (s : TestSpaces.SepTuple → ℝ) (hs : IsMultilinearSepFunctional s) (F : TupleFunctional)
    (hF : ∀ X, F X = s (ofList X)) (X : SeparatedTuples.SepTuple) :
    centredPartFunctional s X =
      ∑ A ∈ (Finset.Icc 1 X.size).powerset,
        (∏ l ∈ Finset.univ.filter (fun l : Fin X.1.length => (l : ℕ) + 1 ∉ A),
          -componentCumulantOne s X l) * s (ofList (X.subtuple A)) := by
  have h := (hValue s hs F hF).1 (basisVec X)
  rw [TestSpaces.centring_basisVec] at h
  simp only [TupleFunctional.spanExtension, SeparatedTuples.linearExtend_basisVec, centredTuple,
    map_sum, map_smul, smul_eq_mul, centringCoeff, hF] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  rfl
theorem centredAtPlaquetteMeans_holds (hValue : CentredTupleValue.centredValueFormula)
    (hFirst : LimitSymmetries.LimitHasSymmetries)
    (hStates : LatticeConventions.ReflectionPositiveStates.Statement)
    (hBounded : ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hCovariant : RepresentativeCovariance.RepresentativesCovariantAndLocal)
    (hPlaquettes : InfiniteLattice.CutoffStructure.FieldSpaceAndSymmetries) :
    CentredAtPlaquetteMeans := by
  intro D T s hbd hrp hlim
  have hL := D.isAdmissible
  have hL0 : (0 : ℝ) < D.L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < D.L)
  have ha : ∀ j : ℕ+, 0 < refinedSpacing D.L (T.cutoff j) := fun j => zpow_pos hL0 _
  have hP : ∀ j : ℕ+, PlaquetteGeometry (refinedSpacing D.L (T.cutoff j)) := fun j =>
    (hPlaquettes _ (ha j)).2.1
  have hFn : ∀ j : ℕ+, FaceEnergyProperties (refinedSpacing D.L (T.cutoff j)) := fun j =>
    (hPlaquettes _ (ha j)).2.2.1
  obtain ⟨hempty, ⟨-, hmul, -⟩, -⟩ := hFirst D T (fun X => s (ofList X)) hbd hrp hlim
  let F : TupleFunctional := ⟨fun X => s (ofList X), hempty⟩
  have hF : ∀ X, F X = s (ofList X) := fun _ => rfl
  have hs : IsMultilinearSepFunctional s :=
    isMultilinearSepFunctional_of_tupleFunctional s F hF hmul
  have hone : ∀ (j : ℕ+) (p p' : ElementaryPlaquette (refinedSpacing D.L (T.cutoff j))),
      ∫ U, faceEnergy U p ∂T.state j = ∫ U, faceEnergy U p' ∂T.state j := fun j =>
    (hStates ⟨refinedSpacing D.L (T.cutoff j), ha j⟩ (T.state j) (hrp j).1 (hrp j).2).1.2
  have hfield : ∀ (f : AmbientSpace → ℝ) (hf : f ∈ c1CompactSupp (Set.univ : Set AmbientSpace)),
      Tendsto (fun j => ∫ U, LatticeApproximation.smearedField T j f U ∂T.state j) atTop
        (𝓝 (s ⟨1, singletonSepTuple f hf⟩)) := by
    intro f hf
    have h : Tendsto (fun j => ∫ U, ApproxTriple.tupleRep T j
        (toList ⟨1, singletonSepTuple f hf⟩) U ∂T.state j) atTop
        (𝓝 (s (ofList (toList ⟨1, singletonSepTuple f hf⟩)))) := hlim _
    rw [ofList_toList] at h
    refine h.congr fun j => integral_congr_ae (Eventually.of_forall fun U => ?_)
    simp [ApproxTriple.tupleRep, LatticeApproximation.latticeProduct, toList, singletonSepTuple]
  refine ⟨hs, ?_, ?_, hfield, ?_⟩
  · have hex : ∀ j : ℕ+, ∃ o : ℝ, ∀ p : ElementaryPlaquette (refinedSpacing D.L (T.cutoff j)),
        ∫ U, faceEnergy U p ∂T.state j = o := by
      intro j
      rcases isEmpty_or_nonempty (ElementaryPlaquette (refinedSpacing D.L (T.cutoff j))) with
        h | ⟨⟨p₀⟩⟩
      · exact ⟨0, fun p => h.elim p⟩
      · exact ⟨_, fun p => hone j p p₀⟩
    choose ō hō using hex
    exact ⟨ō, hō⟩
  · intro ō hō
    have hlimit : ApproxTriple.ConvergesTo ({ T with offset := ō } : ApproxTriple D.L)
        (centredPartFunctional s) := by
      intro X
      have hval : ∀ j : ℕ+, ∫ U, ApproxTriple.tupleRep
            ({ T with offset := ō } : ApproxTriple D.L) j X U ∂T.state j =
          ∑ A ∈ (Finset.Icc 1 X.1.length).powerset,
            (∏ l ∈ Finset.univ.filter (fun l : Fin X.1.length => (l : ℕ) + 1 ∉ A),
              -∫ V, LatticeApproximation.smearedField T j (X.1.get l) V ∂T.state j) *
              ∫ U, ApproxTriple.tupleRep T j (X.subtuple A) U ∂T.state j := by
        intro j
        simp only [tupleRep_offset_mean T ō (hP j) (hFn j) (hō j) X]
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl fun A _ => integral_const_mul _ _
        · intro A _
          refine Integrable.const_mul ?_ _
          obtain ⟨hc, ⟨⟨-, C, hC⟩, -⟩, -⟩ := (hCovariant D.L hL T j).2.2.1 (X.subtuple A)
          refine Integrable.of_bound hc.measurable.aestronglyMeasurable C
            (Eventually.of_forall fun U => ?_)
          simpa using hC U
      change Tendsto (fun j => ∫ U, ApproxTriple.tupleRep
        ({ T with offset := ō } : ApproxTriple D.L) j X U ∂T.state j) atTop
        (𝓝 (centredPartFunctional s X))
      simp only [hval]
      rw [centredPartFunctional_eq_sum hValue s hs F hF X]
      refine tendsto_finsetSum _ fun A _ => Tendsto.mul ?_ (hlim (X.subtuple A))
      refine tendsto_finsetProd _ fun l _ => Tendsto.neg ?_
      have h := hfield (X.1.get l) ((get_mem_disjointSupportTuples X).1 l)
      rw [componentCumulantOne, cumulantOne_eq]
      exact h
    refine ⟨?_, hrp, hlimit⟩
    exact (hBounded.1 D { T with offset := ō } fun X => ⟨_, hlimit X⟩).2
  · intro hm f hf j
    exact integral_smearedField_eq_zero T (hP j) (hFn j) (hm j) hf.2.1
end YangMills.Construction.ReflectionPositivity.CentredMeansProof
end
