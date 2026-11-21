import YangMills.Construction.InfiniteLattice.CalculusOfTheLatticeRepresentatives
import YangMills.Construction.InfiniteLattice.IsometriesAndReflectionsOfTheLatticeOfACutoff
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import YangMills.Construction.InfiniteLattice.WhatAnObservableReads
import YangMills.Construction.ReflectionPositiveLimits.RepresentativesOfSeparatedTuples
import YangMills.Construction.ReflectionsAndOneInsertion.ReflectionsObservablesAndCellDataProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffRepresentative
namespace CentredCalculus
open YangMills.Construction.InfiniteLattice YangMills.Construction.CutoffLattice YangMills.Construction.TupleLists YangMills.Construction.SeparatedTuples
open YangMills.Construction.InfiniteLattice.SmearedEnergyAndSymmetryAction (SmearedEnergyReal)
theorem isBoundedBorelCompactlySupported_of_isC1c {f : RealValued}
    (hf : SeparatedTuples.IsC1c f) : IsBoundedBorelCompactlySupported f := by
  have hc : Continuous f := (show ContDiff ℝ 1 f from hf.1).continuous
  exact ⟨hc.measurable, hc.bounded_above_of_compact_support hf.2, hf.2⟩
section FieldOfAnEntry
variable {a : ℝ}
theorem measurable_smearedEnergy (hE : SmearedEnergyReal a) {g : AmbientSpace → ℝ}
    (hg : IsBoundedBorelCompactlySupported g) :
    Measurable (smearedEnergy g : GaugeField a → ℝ) := by
  obtain ⟨-, -, hobs, -⟩ := hE g hg
  have h := Complex.measurable_re.comp hobs.1
  simpa [Function.comp_def] using h
theorem integrable_smearedEnergy (hE : SmearedEnergyReal a)
    (μ : Measure (GaugeField a)) [IsFiniteMeasure μ] {g : AmbientSpace → ℝ}
    (hg : IsBoundedBorelCompactlySupported g) :
    Integrable (smearedEnergy g : GaugeField a → ℝ) μ := by
  obtain ⟨-, -, hobs, -⟩ := hE g hg
  obtain ⟨C, hC⟩ := hobs.2
  refine Integrable.of_bound (measurable_smearedEnergy hE hg).aestronglyMeasurable C
    (ae_of_all _ fun A => ?_)
  simpa [Complex.norm_real] using hC A
theorem smearedEnergy_linear (hE : SmearedEnergyReal a) {g₁ g₂ : AmbientSpace → ℝ}
    (hg₁ : IsBoundedBorelCompactlySupported g₁) (hg₂ : IsBoundedBorelCompactlySupported g₂)
    (c₁ c₂ : ℝ) (A : GaugeField a) :
    smearedEnergy (c₁ • g₁ + c₂ • g₂) A =
      c₁ * smearedEnergy g₁ A + c₂ * smearedEnergy g₂ A := by
  obtain ⟨h₁, -⟩ := hE g₁ hg₁
  obtain ⟨h₂, -⟩ := hE g₂ hg₂
  have hs₁ : (Function.support fun p : ElementaryPlaquette a =>
      faceEnergy A p • g₁ p.center).Finite :=
    h₁.subset fun p hp h0 => hp (by simp [h0])
  have hs₂ : (Function.support fun p : ElementaryPlaquette a =>
      faceEnergy A p • g₂ p.center).Finite :=
    h₂.subset fun p hp h0 => hp (by simp [h0])
  unfold smearedEnergy
  rw [mul_finsum, mul_finsum, ← finsum_add_distrib]
  · refine finsum_congr fun p => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · exact hs₁.subset fun p hp h0 => hp (by simp only [] at h0 ⊢; rw [h0, mul_zero])
  · exact hs₂.subset fun p hp h0 => hp (by simp only [] at h0 ⊢; rw [h0, mul_zero])
theorem centredSmearedField_linear (hE : SmearedEnergyReal a)
    (μ : Measure (GaugeField a)) [IsFiniteMeasure μ] {g₁ g₂ : AmbientSpace → ℝ}
    (hg₁ : IsBoundedBorelCompactlySupported g₁) (hg₂ : IsBoundedBorelCompactlySupported g₂)
    (c₁ c₂ : ℝ) (A : GaugeField a) :
    centredSmearedField μ (c₁ • g₁ + c₂ • g₂) A =
      c₁ * centredSmearedField μ g₁ A + c₂ * centredSmearedField μ g₂ A := by
  have hi : ∫ B, smearedEnergy (c₁ • g₁ + c₂ • g₂) B ∂μ =
      c₁ * ∫ B, smearedEnergy g₁ B ∂μ + c₂ * ∫ B, smearedEnergy g₂ B ∂μ := by
    simp only [smearedEnergy_linear hE hg₁ hg₂]
    rw [integral_add ((integrable_smearedEnergy hE μ hg₁).const_mul _)
      ((integrable_smearedEnergy hE μ hg₂).const_mul _), integral_const_mul, integral_const_mul]
  unfold centredSmearedField
  rw [hi, smearedEnergy_linear hE hg₁ hg₂]
  ring
end FieldOfAnEntry
section ProductOverEntries
variable {L K : ℕ} (μ : Measure (FieldsAt L K))
theorem centredProduct_ofList (X : SepTuple) (A : FieldsAt L K) :
    centredProduct L K μ (ofList X) A = (X.1.map fun g => centredSmearedField μ g A).prod := by
  simp only [centredProduct, ofList]
  exact Fin.prod_univ_fun_getElem X.1 fun g => centredSmearedField μ g A
theorem centredProductLinear_basisVec (X : SepTuple) :
    centredProductLinear L K μ (basisVec X) =
      fun A => ((centredProduct L K μ (ofList X) A : ℝ) : ℂ) := by
  simp [centredProductLinear, SeparatedTuples.linearExtend_basisVec]
theorem centredProductLinear_basisVec_apply (X : SepTuple) (A : FieldsAt L K) :
    centredProductLinear L K μ (basisVec X) A =
      ((centredProduct L K μ (ofList X) A : ℝ) : ℂ) := by
  rw [centredProductLinear_basisVec]
theorem single_eq_smul_basisVec (X : SepTuple) (c : ℂ) : Finsupp.single X c = c • basisVec X := by
  simp [basisVec]
theorem centredProductLinear_single (X : SepTuple) (c : ℂ) (A : FieldsAt L K) :
    centredProductLinear L K μ (Finsupp.single X c) A =
      c * ((centredProduct L K μ (ofList X) A : ℝ) : ℂ) := by
  rw [single_eq_smul_basisVec, map_smul, centredProductLinear_basisVec]
  rfl
theorem centredProductLinear_apply (Φ : FormalSpan) (A : FieldsAt L K) :
    centredProductLinear L K μ Φ A =
      ∑ X ∈ Φ.support, Φ X * ((centredProduct L K μ (ofList X) A : ℝ) : ℂ) := by
  simp only [centredProductLinear, SeparatedTuples.linearExtend,
    Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
theorem formalSpan_eq_sum (Φ : FormalSpan) : Φ = ∑ X ∈ Φ.support, Φ X • basisVec X := by apply _root_.YangMills.Construction.ReflectionsAndOneInsertion.formalSpan_eq_sum <;> assumption
theorem centredProduct_juxt {X Y : SepTuple} (h : SepTuple.Composable X Y)
    (A : FieldsAt L K) :
    centredProduct L K μ (ofList (SepTuple.juxt X Y)) A =
      centredProduct L K μ (ofList X) A * centredProduct L K μ (ofList Y) A := by
  simp only [centredProduct_ofList, SepTuple.juxt_val h, List.map_append, List.prod_append]
theorem centredProductLinear_singleTuple (g : RealValued) (hg : SeparatedTuples.IsC1c g)
    (A : FieldsAt L K) :
    centredProductLinear L K μ (basisVec (R4TupleForms.singleTuple g hg)) A =
      ((centredSmearedField μ g A : ℝ) : ℂ) := by
  rw [centredProductLinear_basisVec_apply, centredProduct_ofList]
  simp [R4TupleForms.singleTuple]
end ProductOverEntries
section Symmetry
variable {a : ℝ}
theorem invMap_toFun_eq (σ : LatticeSymmetry a) :
    invMap σ.toFun = (ReflectionPositivity.latticeSymmetryToEuclid σ).symm.toFun := by
  funext x
  have h1 : σ.toFun ((ReflectionPositivity.latticeSymmetryToEuclid σ).symm.toFun x) = x :=
    (ReflectionPositivity.latticeSymmetryToEuclid σ).toFun_symm x
  conv_lhs => rw [← h1]
  exact Function.leftInverse_invFun σ.toFun_injective _
theorem isDisjointlySupported_pushList (σ : LatticeSymmetry a) (X : SepTuple) :
    IsDisjointlySupported (pushList σ.toFun X.1) := by
  set e := ReflectionPositivity.latticeSymmetryToEuclid σ with he
  have hts : ∀ g : RealValued, tsupport (g ∘ e.symm.toFun) =
      e.symm.toFun ⁻¹' tsupport g := fun g =>
    ReflectionPositivity.tsupport_pushFn e g
  simp only [pushList, invMap_toFun_eq, ← he]
  refine ⟨fun k hk => ?_, List.pairwise_map.2 (X.2.2.imp fun {g h} hd => ?_)⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hk
    have hc := X.2.1 g hg
    refine ⟨(show ContDiff ℝ 1 g from hc.1).comp e.symm.contDiff_toFun, ?_⟩
    change IsCompact (tsupport (g ∘ e.symm.toFun))
    rw [hts]
    exact e.toHomeo.symm.isCompact_preimage.2 hc.2
  · rw [hts, hts]
    exact hd.preimage _
theorem push_val (σ : LatticeSymmetry a) (X : SepTuple) :
    (push σ.toFun X).1 = X.1.map σ.pushforwardFun := by
  unfold push
  rw [dif_pos (isDisjointlySupported_pushList σ X)]
  rfl
theorem centredSmearedField_pullbackField (hE : SmearedEnergyReal a)
    {μ : Measure (GaugeField a)} (σ : LatticeSymmetry a)
    (hcov : ∀ g : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported g →
      σ.actOn (smearedEnergy g) =
        (smearedEnergy (σ.pushforwardFun g) : GaugeField a → ℝ))
    (hinv : IsSymmetricUnder μ σ) {g : AmbientSpace → ℝ} (hg : IsBoundedBorelCompactlySupported g)
    (A : GaugeField a) :
    centredSmearedField μ g (σ.pullbackField A) =
      centredSmearedField μ (σ.pushforwardFun g) A := by
  have h1 : ∀ B, smearedEnergy g (σ.pullbackField B) =
      smearedEnergy (σ.pushforwardFun g) B := fun B => congrFun (hcov g hg) B
  obtain ⟨-, -, hobs, -⟩ := hE g hg
  have h2 := hinv _ hobs
  have h3 : (fun B => σ.actOn
      (fun W : GaugeField a => ((smearedEnergy g W : ℝ) : ℂ)) B) =
      fun B => ((smearedEnergy (σ.pushforwardFun g) B : ℝ) : ℂ) :=
    funext fun B => congrArg (fun x : ℝ => (x : ℂ)) (h1 B)
  rw [h3, integral_complex_ofReal, integral_complex_ofReal] at h2
  have h4 : ∫ B, smearedEnergy (σ.pushforwardFun g) B ∂μ = ∫ B, smearedEnergy g B ∂μ := by
    exact_mod_cast h2
  unfold centredSmearedField
  rw [h1, h4]
end Symmetry
section UpperHalf
variable {a : ℝ}
theorem regionSigma_le_of_subset {R R' : Set AmbientSpace} (h : R ⊆ R') :
    (regionSigma R : MeasurableSpace (GaugeField a)) ≤ regionSigma R' := by apply _root_.YangMills.Construction.InfiniteLattice.regionSigma_mono <;> assumption
theorem const_mem_localObsAbove (t : halfSpacingTimes a) (c : ℂ) :
    (fun _ : GaugeField a => c) ∈ localObsAbove t :=
  ⟨⟨measurable_const, ‖c‖, fun _ => le_rfl⟩, ∅, Set.empty_subset _, Bornology.isBounded_empty,
    measurable_const⟩
theorem add_mem_localObsAbove {t : halfSpacingTimes a} {F G : GaugeField a → ℂ}
    (hF : F ∈ localObsAbove t) (hG : G ∈ localObsAbove t) :
    F + G ∈ localObsAbove t := by
  obtain ⟨⟨mF, C, hC⟩, R, hR, bR, sF⟩ := hF
  obtain ⟨⟨mG, C', hC'⟩, R', hR', bR', sG⟩ := hG
  have sF' : Measurable[regionSigma (R ∪ R')] F :=
    Measurable.mono sF (regionSigma_le_of_subset Set.subset_union_left) le_rfl
  have sG' : Measurable[regionSigma (R ∪ R')] G :=
    Measurable.mono sG (regionSigma_le_of_subset Set.subset_union_right) le_rfl
  exact ⟨⟨mF.add mG, C + C', fun A => (norm_add_le _ _).trans (add_le_add (hC A) (hC' A))⟩,
    R ∪ R', Set.union_subset hR hR', bR.union bR', sF'.add sG'⟩
theorem mul_mem_localObsAbove {t : halfSpacingTimes a} {F G : GaugeField a → ℂ}
    (hF : F ∈ localObsAbove t) (hG : G ∈ localObsAbove t) :
    F * G ∈ localObsAbove t := by
  obtain ⟨⟨mF, C, hC⟩, R, hR, bR, sF⟩ := hF
  obtain ⟨⟨mG, C', hC'⟩, R', hR', bR', sG⟩ := hG
  have sF' : Measurable[regionSigma (R ∪ R')] F :=
    Measurable.mono sF (regionSigma_le_of_subset Set.subset_union_left) le_rfl
  have sG' : Measurable[regionSigma (R ∪ R')] G :=
    Measurable.mono sG (regionSigma_le_of_subset Set.subset_union_right) le_rfl
  refine ⟨⟨mF.mul mG, C * C', fun A => ?_⟩, R ∪ R', Set.union_subset hR hR', bR.union bR',
    sF'.mul sG'⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC A) (hC' A) (norm_nonneg _) ((norm_nonneg _).trans (hC A))
theorem smul_mem_localObsAbove {t : halfSpacingTimes a} (c : ℂ) {F : GaugeField a → ℂ}
    (hF : F ∈ localObsAbove t) : c • F ∈ localObsAbove t := by
  have h := mul_mem_localObsAbove (const_mem_localObsAbove t c) hF
  exact h
theorem center_sub_half_le_vertex (ha : 0 < a) (p : ElementaryPlaquette a) {y : LatticePoint a}
    (hy : y ∈ p.cornerSet) (τ : Fin 4) : p.center τ - a / 2 ≤ (y : AmbientSpace) τ := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have hstep : ∀ ν, ((axisStep a ν : LatticePoint a) : AmbientSpace) τ = if τ = ν then a else 0 :=
    fun ν => by simp [axisStep, Pi.single_apply]
  have hb : p.center τ = (p.corner : AmbientSpace) τ + (if τ = p.lowAxis then a / 2 else 0) +
      (if τ = p.highAxis then a / 2 else 0) := by
    simp [ElementaryPlaquette.center, Pi.single_apply]
  rw [hb]
  simp only [ElementaryPlaquette.cornerSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  all_goals try simp only [AddSubgroup.coe_add, Pi.add_apply, hstep]
  all_goals
    split_ifs <;>
    first
    | linarith
    | exact absurd (‹τ = p.lowAxis›.symm.trans ‹τ = p.highAxis›) hne
theorem faceEnergy_congr_of_eqOn {A A' : GaugeField a} (p : ElementaryPlaquette a)
    {R : Set AmbientSpace} (hR : ∀ y ∈ p.cornerSet, (y : AmbientSpace) ∈ R)
    (hAA : ∀ ℓ : Link a, ℓ.LiesIn R → A ℓ = A' ℓ) :
    faceEnergy A p = faceEnergy A' p := by
  have v1 : p.corner ∈ p.cornerSet := by simp [ElementaryPlaquette.cornerSet]
  have v2 : p.corner + axisStep a p.lowAxis ∈ p.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have v3 : p.corner + axisStep a p.lowAxis + axisStep a p.highAxis ∈ p.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have v4 : p.corner + axisStep a p.highAxis ∈ p.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have v5 : p.corner + axisStep a p.highAxis + axisStep a p.lowAxis ∈ p.cornerSet := by
    rw [add_right_comm]
    exact v3
  have e1 := hAA (Link.forwardFrom p.corner p.lowAxis) ⟨hR _ v1, hR _ v2⟩
  have e2 := hAA (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis)
    ⟨hR _ v2, hR _ v3⟩
  have e3 := hAA (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)
    ⟨hR _ v4, hR _ v5⟩
  have e4 := hAA (Link.forwardFrom p.corner p.highAxis) ⟨hR _ v1, hR _ v4⟩
  simp only [faceEnergy, faceHolonomy, e1, e2, e3, e4]
end UpperHalf
section ReadoutAbove
variable {L K : ℕ}
theorem smearedEnergy_mem_localObsAbove
    (hread : RegionReadout.TruncationContinuousAndCharacterizes L K)
    (hE : SmearedEnergyReal (CutoffLattice.spacingAt L K)) (ha : 0 < CutoffLattice.spacingAt L K)
    (t : halfSpacingTimes (CutoffLattice.spacingAt L K)) {δ : ℝ}
    (hδ : CutoffLattice.spacingAt L K / 2 < δ)
    {g : AmbientSpace → ℝ} (hg : IsBoundedBorelCompactlySupported g)
    (hsupp : tsupport g ⊆ {x : AmbientSpace | (t : ℝ) + δ ≤ x timeAxis}) :
    (fun A : FieldsAt L K => ((smearedEnergy g A : ℝ) : ℂ)) ∈ localObsAbove t := by
  obtain ⟨h, hs, hobs, -⟩ := hE g hg
  set R : Set AmbientSpace := ⋃ p ∈ h.toFinset, ((↑) '' p.cornerSet : Set AmbientSpace) with hR
  have hfin : R.Finite := by
    refine Set.Finite.biUnion h.toFinset.finite_toSet fun p _ => Set.Finite.image _ ?_
    simp [ElementaryPlaquette.cornerSet]
  have hsub : R ⊆ abovePlane t := by
    intro x hx
    obtain ⟨p, hp, y, hy, rfl⟩ : ∃ p ∈ h.toFinset, ∃ y ∈ p.cornerSet, (y : AmbientSpace) = x := by
      simpa [hR] using hx
    have hp' : g p.center ≠ 0 := by simpa using hp
    have h1 : (t : ℝ) + δ ≤ p.center timeAxis := hsupp (subset_tsupport g hp')
    have h2 := center_sub_half_le_vertex ha p hy timeAxis
    show (t : ℝ) < (y : AmbientSpace) timeAxis
    linarith
  have hmem : ∀ p ∈ h.toFinset, ∀ y ∈ p.cornerSet, (y : AmbientSpace) ∈ R := fun p hp y hy =>
    Set.mem_biUnion (Finset.mem_coe.2 hp) ⟨y, hy, rfl⟩
  have hreads : ∀ A A' : GaugeFieldAtScale L K,
      (∀ ℓ : Link (PeriodicLattice.meshSize L (K : ℤ)), ℓ.LiesIn R → A ℓ = A' ℓ) →
      ((smearedEnergy g A : ℝ) : ℂ) = ((smearedEnergy g A' : ℝ) : ℂ) := by
    intro A A' hAA
    rw [hs A, hs A']
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [faceEnergy_congr_of_eqOn p (hmem p hp) hAA]
  have hin := ((hread R).2 _ hobs).out 0 1
  have hB := hin.2 hreads
  exact ⟨hobs, R, hsub, hfin.isBounded, hB.2⟩
end ReadoutAbove
section Calculus
variable {L K : ℕ}
theorem centredProduct_realSymmetricMultilinear
    (hE : SmearedEnergyReal (CutoffLattice.spacingAt L K))
    (μ : Measure (FieldsAt L K)) [IsProbabilityMeasure μ] :
    CentredProductRealSymmetricMultilinear L K μ := by
  refine ⟨fun X A => ?_, fun X Y h => ?_, fun n X X₁ X₂ i c₁ c₂ hrest hi => ?_⟩
  · rw [centredProductLinear_basisVec]
    exact Complex.ofReal_im _
  · funext A
    rw [centredProduct_ofList, centredProduct_ofList]
    exact (h.map _).prod_eq
  · funext A
    have hmem : ∀ (Y : TestSpaces.SepTupleOfCard n) (j : Fin n),
        IsBoundedBorelCompactlySupported (Y.1 j) :=
      fun Y j => isBoundedBorelCompactlySupported_of_isC1c
        ((isDisjointlySupported_ofFn Y).1 (Y.1 j) ((List.mem_ofFn' _ _).2 ⟨j, rfl⟩))
    show ∏ j, centredSmearedField μ (X.1 j) A =
      c₁ * ∏ j, centredSmearedField μ (X₁.1 j) A + c₂ * ∏ j, centredSmearedField μ (X₂.1 j) A
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j => centredSmearedField μ (X₁.1 j) A)
        (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j => centredSmearedField μ (X₂.1 j) A)
        (Finset.mem_univ i), hi, centredSmearedField_linear hE μ (hmem X₁ i) (hmem X₂ i)]
    have e₁ : ∏ j ∈ Finset.univ.erase i, centredSmearedField μ (X.1 j) A =
        ∏ j ∈ Finset.univ.erase i, centredSmearedField μ (X₁.1 j) A :=
      Finset.prod_congr rfl fun j hj => by rw [(hrest j (Finset.ne_of_mem_erase hj)).1]
    have e₂ : ∏ j ∈ Finset.univ.erase i, centredSmearedField μ (X.1 j) A =
        ∏ j ∈ Finset.univ.erase i, centredSmearedField μ (X₂.1 j) A :=
      Finset.prod_congr rfl fun j hj => by rw [(hrest j (Finset.ne_of_mem_erase hj)).2]
    rw [← e₁, ← e₂]
    ring
theorem conj_centredProductLinear (μ : Measure (FieldsAt L K)) (Φ : FormalSpan)
    (A : FieldsAt L K) :
    conj (centredProductLinear L K μ Φ A) =
      centredProductLinear L K μ (SeparatedTuples.conjugation Φ) A := by
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG =>
    simp only [map_add, Pi.add_apply, hF, hG]
  | single X c =>
    have hc : SeparatedTuples.conjugation (Finsupp.single X c) = Finsupp.single X (conj c) := by
      rw [single_eq_smul_basisVec, map_smulₛₗ, conjugation_basisVec, single_eq_smul_basisVec]
    rw [hc, centredProductLinear_single, centredProductLinear_single, map_mul,
      Complex.conj_ofReal]
theorem centredProductLinear_formalMul (μ : Measure (FieldsAt L K)) {Φ Ψ : FormalSpan}
    (h : R4TupleForms.FormalMulDefined Φ Ψ) :
    centredProductLinear L K μ (formalMul Φ Ψ) =
      centredProductLinear L K μ Φ * centredProductLinear L K μ Ψ := by
  have key : formalMul Φ Ψ = ∑ X ∈ Φ.support, ∑ Y ∈ Ψ.support,
      (Φ X * Ψ Y) • basisVec (SepTuple.juxt X Y) := by
    calc formalMul Φ Ψ =
        formalMul (∑ X ∈ Φ.support, Φ X • basisVec X)
          (∑ Y ∈ Ψ.support, Ψ Y • basisVec Y) := by
          rw [← formalSpan_eq_sum Φ, ← formalSpan_eq_sum Ψ]
      _ = _ := formalMul_sum Φ.support Ψ.support (fun X => Φ X) (fun Y => Ψ Y)
          (fun X => X) (fun Y => Y)
  funext A
  rw [Pi.mul_apply, centredProductLinear_apply μ Φ, centredProductLinear_apply μ Ψ,
    Finset.sum_mul_sum, key, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun X hX => ?_
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [map_smul, Pi.smul_apply, centredProductLinear_basisVec_apply, smul_eq_mul,
    centredProduct_juxt μ (h X hX Y hY)]
  push_cast
  ring
theorem smearedEnergy_zero {a : ℝ} (A : GaugeField a) :
    smearedEnergy (0 : AmbientSpace → ℝ) A = 0 := by
  simp [smearedEnergy]
theorem integral_complexObservable (hE : SmearedEnergyReal (CutoffLattice.spacingAt L K))
    (μ : Measure (FieldsAt L K)) [IsFiniteMeasure μ] {f : ComplexTestFunctions.ComplexValued}
    (hf : ComplexTestFunctions.IsC1cComplex f) :
    ∫ B, ComplexTupleComponents.complexObservable f B ∂μ =
      ((∫ B, smearedEnergy (ComplexTestFunctions.rePart f) B ∂μ : ℝ) : ℂ) +
        Complex.I * ((∫ B, smearedEnergy (ComplexTestFunctions.imPart f) B ∂μ : ℝ) : ℂ) := by
  have h₁ := integrable_smearedEnergy hE μ
    (isBoundedBorelCompactlySupported_of_isC1c (ComplexTupleComponents.rePart_isC1c hf))
  have h₂ := integrable_smearedEnergy hE μ
    (isBoundedBorelCompactlySupported_of_isC1c (ComplexTupleComponents.imPart_isC1c hf))
  unfold ComplexTupleComponents.complexObservable
  rw [integral_add h₁.ofReal (h₂.ofReal.const_mul _), integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal]
theorem centredProductLinear_singleSpan (hE : SmearedEnergyReal (CutoffLattice.spacingAt L K))
    (μ : Measure (FieldsAt L K)) [IsFiniteMeasure μ] (f : ComplexTestFunctions.ComplexValued)
    (hf : ComplexTestFunctions.IsC1cComplex f) (A : FieldsAt L K) :
    centredProductLinear L K μ (ComplexTupleComponents.singleSpan f hf) A =
      ComplexTupleComponents.complexObservable f A -
        ∫ B, ComplexTupleComponents.complexObservable f B ∂μ := by
  rw [integral_complexObservable hE μ hf]
  by_cases h0 : ComplexTestFunctions.imPart f = 0
  · rw [ComplexTupleComponents.singleSpan, if_pos h0, centredProductLinear_singleTuple]
    unfold ComplexTupleComponents.complexObservable centredSmearedField
    simp only [h0, smearedEnergy_zero, integral_zero]
    push_cast
    ring
  · rw [ComplexTupleComponents.singleSpan, if_neg h0, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      centredProductLinear_singleTuple, centredProductLinear_singleTuple, smul_eq_mul]
    unfold ComplexTupleComponents.complexObservable centredSmearedField
    push_cast
    ring
theorem actOn_centredProductLinear (hE : SmearedEnergyReal (CutoffLattice.spacingAt L K))
    (μ : Measure (FieldsAt L K)) (σ : LatticeSymmetry (CutoffLattice.spacingAt L K))
    (hcov : ∀ g : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported g →
      σ.actOn (smearedEnergy g) =
        (smearedEnergy (σ.pushforwardFun g) : GaugeField (CutoffLattice.spacingAt L K) → ℝ))
    (hinv : IsSymmetricUnder μ σ) (Φ : FormalSpan) :
    σ.actOn (centredProductLinear L K μ Φ) =
      centredProductLinear L K μ (pushSpan σ.toFun Φ) := by
  induction Φ using Finsupp.induction_linear with
  | zero =>
    funext A
    simp [LatticeSymmetry.actOn]
  | add F G hF hG =>
    funext A
    have h1 := congrFun hF A
    have h2 := congrFun hG A
    simp only [map_add, Pi.add_apply] at h1 h2 ⊢
    rw [← h1, ← h2]
    rfl
  | single X c =>
    funext A
    have hX : ∀ B, centredProduct L K μ (ofList X) (σ.pullbackField B) =
        centredProduct L K μ (ofList (push σ.toFun X)) B := fun B => by
      rw [centredProduct_ofList, centredProduct_ofList, push_val, List.map_map]
      exact congrArg List.prod (List.map_congr_left fun g hg =>
        centredSmearedField_pullbackField hE σ hcov hinv
          (isBoundedBorelCompactlySupported_of_isC1c (X.2.1 g hg)) B)
    have hpush : pushSpan σ.toFun (Finsupp.single X c) = Finsupp.single (push σ.toFun X) c := by
      rw [single_eq_smul_basisVec, map_smul, pushSpan, linearExtend_basisVec,
        single_eq_smul_basisVec]
    rw [hpush, centredProductLinear_single]
    show centredProductLinear L K μ (Finsupp.single X c) (σ.pullbackField A) = _
    rw [centredProductLinear_single, hX]
theorem centredProductLinear_mem_localObsAbove
    (hread : RegionReadout.TruncationContinuousAndCharacterizes L K)
    (hE : SmearedEnergyReal (CutoffLattice.spacingAt L K)) (ha : 0 < CutoffLattice.spacingAt L K)
    (μ : Measure (FieldsAt L K)) (t : halfSpacingTimes (CutoffLattice.spacingAt L K)) {δ : ℝ}
    (hδ : CutoffLattice.spacingAt L K / 2 < δ) {Φ : FormalSpan}
    (hΦ : Φ ∈ spanIn {x : AmbientSpace | (t : ℝ) + δ ≤ x timeAxis}) :
    centredProductLinear L K μ Φ ∈ localObsAbove t := by
  have hlist : ∀ l : List RealValued, (∀ g ∈ l, IsBoundedBorelCompactlySupported g ∧
      tsupport g ⊆ {x : AmbientSpace | (t : ℝ) + δ ≤ x timeAxis}) →
      (fun A : FieldsAt L K =>
        (((l.map fun g => centredSmearedField μ g A).prod : ℝ) : ℂ)) ∈ localObsAbove t := by
    intro l
    induction l with
    | nil =>
      intro _
      simpa using const_mem_localObsAbove t 1
    | cons g l ih =>
      intro hl
      obtain ⟨hg, hsupp⟩ := hl g (List.mem_cons_self ..)
      have h1 := smearedEnergy_mem_localObsAbove hread hE ha t hδ hg hsupp
      have h2 := add_mem_localObsAbove h1
        (const_mem_localObsAbove t (-((∫ B, smearedEnergy g B ∂μ : ℝ) : ℂ)))
      have h3 := mul_mem_localObsAbove h2 (ih fun k hk => hl k (List.mem_cons_of_mem _ hk))
      convert h3 using 1
      funext A
      simp only [List.map_cons, List.prod_cons, Pi.mul_apply, Pi.add_apply, centredSmearedField]
      push_cast
      ring
  induction hΦ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨⟨X, hX⟩, rfl⟩ := hG
    rw [centredProductLinear_basisVec]
    simp only [centredProduct_ofList]
    exact hlist X.1 fun g hg => ⟨isBoundedBorelCompactlySupported_of_isC1c (X.2.1 g hg), hX g hg⟩
  | zero =>
    rw [map_zero]
    exact const_mem_localObsAbove t 0
  | add F G _ _ hF hG =>
    rw [map_add]
    exact add_mem_localObsAbove hF hG
  | smul c F _ hF =>
    rw [map_smul]
    exact smul_mem_localObsAbove c hF
end Calculus
end CentredCalculus
theorem centredProductCalculus_holds
    (hMoves : GibbsAtFixedSpacing.SymmetriesTransportLinksSupportsAndPlaquettes)
    (hObs : SmearedEnergyAndSymmetryAction.Main)
    (hFacts : CutoffSymmetriesAndTimeReflections)
    (hReads : RegionReadout.Summary) :
    CentredProductCalculus := by
  intro s μ hμ
  have ha : 0 < CutoffLattice.spacingAt s.L s.K := CutoffLattice.spacingAt_pos s.isAdmissible s.K
  have hE := (hObs _ ha).1.2
  have hcov := fun σ : LatticeSymmetry (CutoffLattice.spacingAt s.L s.K) =>
    (hFacts s).1 σ σ
  have hread := (hReads s.L s.K s.isAdmissible s.K.pos).1
  refine ⟨fun σ => ?_, CentredCalculus.centredProduct_realSymmetricMultilinear hE μ,
    ⟨fun Φ Ψ h => CentredCalculus.centredProductLinear_formalMul μ h,
      fun Φ A => CentredCalculus.conj_centredProductLinear μ Φ A,
      fun f hf A => CentredCalculus.centredProductLinear_singleSpan hE μ f hf A⟩,
    fun σ hinv Φ => CentredCalculus.actOn_centredProductLinear hE μ σ
      (hcov σ).2.2.1 hinv Φ,
    fun t δ hδ Φ hΦ => CentredCalculus.centredProductLinear_mem_localObsAbove hread hE ha μ t hδ hΦ⟩
  obtain ⟨-, -, hm⟩ := hMoves _ ha
  obtain ⟨hc, hbij, -, hact, hctr, -⟩ := hm σ
  refine ⟨fun p => (hc p).1, fun ρ hρ => ?_, (hcov σ).2.2.1, (hcov σ).2.2.2⟩
  have hρ' : ρ = σ.plaquetteMap := funext fun p => (hc p).1.unique (hρ p) (hc p).2
  rw [hρ']
  exact ⟨hbij, hctr, hact⟩
end YangMills.Construction.InfiniteLattice.CutoffRepresentative
