import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.ReflectionPositiveLimits.PlateauxOfLimitsOfLatticeStatesProof
import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStatesProof
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMomentsProof
import YangMills.Construction.Cumulants.ReCentringOfAProductOfBoundedRandomVariables
import YangMills.Construction.PassageToTheLimit.WhatPassesToTheLimitProof
import YangMills.Construction.ReflectionPositiveLimits.PeriodicGibbsStatesAndLatticeApproximations
import YangMills.Construction.ReflectionPositiveLimits.TheSizesDoNotSeeTheSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.SpacingFreeSizes
open YangMills.Construction.Cumulants.ProductRecentering (centeredMean realExpect recenteredCumulant
  recenteredCumulant_of_two_le_card)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.InfiniteLattice (LatticeSymmetry scaledCube regionObservables
  periodicGibbsSet smearedEnergy axisStep shift)
open YangMills.Construction.ReflectionPositivity.LatticeRepresentatives (AdmissibleClassProperties
  IsBoundedBoundedSupp CenteredProductLocality CenteredProductCalculus SmearedEnergyStructure
  toComplexObs)
open YangMills.Construction.Probability (IsBoundedRealRV)
open YangMills.Construction.ReflectionPositivity.DirectionPictures (axisReflectionGroup
  scaledCubeReflectionSize)
open YangMills.Construction.SetPartition (Partitions PartitionsFin atLeastTwoPartitions)
open YangMills.Construction.SetPartition.SingletonSplit (singletonFreeProdSumOn)
open YangMills.Construction.TestFunctions (IsLipschitzFor closedBallR4 euclidDistR4 sharpNormR4)
open YangMills.Construction.TorusMetric (euclidNormVec)
private theorem abs_apply_le_euclidNormVec (v : Space) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem norm_le_euclidNormVec (v : Space) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
abbrev _root_.YangMills.SharedProofs.p2512 := @norm_le_euclidNormVec
private theorem euclidNormVec_le_two_norm (v : Space) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
abbrev _root_.YangMills.SharedProofs.p35791 := @euclidNormVec_le_two_norm
private theorem tsupport_pt_eq (s : Conventions.StandingParameters)
    (g : AmbientPoints.Pt s AxisMirror.Ambient.euclidean → ℝ) :
    tsupport g = @tsupport Space ℝ _ _ g := by apply _root_.YangMills.Construction.AmbientPoints.tsupport_eq_of_r4 <;> assumption
abbrev _root_.YangMills.SharedProofs.p14564 := @tsupport_pt_eq
private theorem isLipschitzFor_of_mem {f : ScalarField} (hf : f ∈ c1Compact Set.univ) :
    IsLipschitzFor euclidDistR4 f := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
    (show HasCompactSupport f from hf.2.1) hf.1 (by norm_num)
  refine ⟨C, C.2, fun x y => ?_⟩
  have h := hC.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_euclidNormVec _) C.2)
private theorem isBoundedRealRV_of_mem {a : ℝ} (hW : SmearedEnergyStructure a)
    {f : ScalarField} (hf : f ∈ c1Compact Set.univ) :
    IsBoundedRealRV (smearedEnergy f : InfiniteLattice.GaugeField a → ℝ) := by
  have hb : IsBoundedBoundedSupp f :=
    ⟨HasCompactSupport.exists_bound_of_continuous (show HasCompactSupport f from hf.2.1)
      hf.1.continuous, hf.2.1.isBounded⟩
  obtain ⟨-, hc, -, ho⟩ := hW.2 f hb
  obtain ⟨C, hC⟩ := (ho Set.univ fun _ _ _ _ => Set.mem_univ _).1.2
  refine ⟨hc.measurable, C, fun U => ?_⟩
  have := hC U
  simpa [toComplexObs, Complex.norm_real] using this
variable {L K : ℕ}
private theorem centeredProduct_apply (ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ)))
    (X : Tuple) (U : GaugeFieldsAtLevel L K) :
    centeredProduct L K ν X U = ∏ i : Fin X.1.length,
      (smearedEnergy (X.1.get i) U - ∫ V, smearedEnergy (X.1.get i) V ∂ν.1) := by apply _root_.YangMills.DeltaSharedProofs.p501816 <;> assumption
private abbrev energies {k : ℕ} (f : Fin k → ScalarField) :
    Fin k → GaugeFieldsAtLevel L K → ℝ :=
  fun i => smearedEnergy (f i)
private abbrev energyMeans (ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) {k : ℕ}
    (f : Fin k → ScalarField) : Fin k → ℝ :=
  fun i => realExpectation ν (smearedEnergy (f i))
private theorem parts_eq_empty_of_fin_zero (π : PartitionsFin 0) : π.parts = ∅ := by apply _root_.YangMills.Construction.Cumulants.MomentCumulantFormulas.parts_eq_of_fin_zero <;> assumption
private theorem sum_partCumulant_fin_zero (ρ ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ)))
    (f : Fin 0 → ScalarField) :
    ∑ π : PartitionsFin 0, ∏ J ∈ π.parts, partCumulant ρ ν f J = 1 := by
  have h : ∀ π : PartitionsFin 0, π = ⊥ := fun π =>
    Finpartition.ext (by rw [parts_eq_empty_of_fin_zero, parts_eq_empty_of_fin_zero])
  rw [Fintype.sum_eq_single (⊥ : PartitionsFin 0) fun π hπ => absurd (h π) hπ,
    parts_eq_empty_of_fin_zero]
  simp
private theorem moment_eq_sum_partitions
    (hR : Cumulants.ProductRecentering.ProductRecenteringExpansion)
    (ρ ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) {k : ℕ} (f : Fin k → ScalarField)
    (hb : ∀ i, IsBoundedRealRV (energies (L := L) (K := K) f i)) :
    ((realExpect ρ.1 (fun U => ∏ i, (energies (L := L) (K := K) f i U - energyMeans ν f i)) : ℝ) : ℂ) =
      ∑ π : PartitionsFin k, ∏ J ∈ π.parts, partCumulant ρ ν f J := by
  have : IsProbabilityMeasure ρ.1 := ρ.2
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [sum_partCumulant_fin_zero]
    simp [realExpect]
  · have h := (hR (GaugeFieldsAtLevel L K) ρ.1 k hk (energies f) (energyMeans ν f) hb).1
    exact h.1.trans h.2
private theorem prod_parts_prod_eq {k : ℕ} {A : Finset (Fin k)} (π : Partitions A)
    (w : Fin k → ℝ) : ∏ I ∈ π.parts, ∏ i ∈ I, w i = ∏ i ∈ A, w i := by
  have h := Finset.prod_biUnion (s := π.parts) (t := id) (f := w) π.disjoint
  rw [π.biUnion_parts] at h
  simpa using h.symm
private theorem momentBound_zero (x : ℝ) (y : ℕ → ℝ) : momentBound x y 0 = 1 := by
  have h : ∀ T : Finset (Fin 0), T = ∅ := fun T => Finset.eq_empty_of_isEmpty T
  simp only [momentBound, Finset.univ_unique]
  rw [Finset.sum_singleton]
  simp only [singletonFreeProdSumOn]
  rw [h (Finset.univ \ default), SetPartition.atLeastTwoPartitions_empty]
  rw [h default]
  simp [SetPartition.prod_parts_of_empty]
private theorem moment_abs_le (hR : Cumulants.ProductRecentering.ProductRecenteringExpansion)
    (ρ ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) {k : ℕ} (f : Fin k → ScalarField)
    (hb : ∀ i, IsBoundedRealRV (energies (L := L) (K := K) f i))
    (x : ℝ) (y : ℕ → ℝ) (n : Fin k → ℝ)
    (hδ : ∀ i, |centeredMean ρ.1 (energies (L := L) (K := K) f) (energyMeans ν f) i| ≤ x * n i)
    (hκ : ∀ J : Finset (Fin k), 2 ≤ J.card →
      ‖Cumulants.finsetCumulant ρ.1 (energies (L := L) (K := K) f) J‖ ≤
        y J.card * ∏ i ∈ J, n i) :
    |realExpect ρ.1 (fun U => ∏ i, (energies (L := L) (K := K) f i U - energyMeans ν f i))| ≤
      momentBound x y k * ∏ i, n i := by
  have : IsProbabilityMeasure ρ.1 := ρ.2
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [momentBound_zero]
    simp [realExpect]
  have h := (hR (GaugeFieldsAtLevel L K) ρ.1 k hk (energies f) (energyMeans ν f) hb).1.1
  have hA : ∀ I : Finset (Fin k),
      ‖(∏ i ∈ I, (centeredMean ρ.1 (energies (L := L) (K := K) f) (energyMeans ν f) i : ℂ)) *
        ∑ π ∈ atLeastTwoPartitions (Finset.univ \ I), ∏ J ∈ π.parts,
          recenteredCumulant ρ.1 (energies (L := L) (K := K) f) (energyMeans ν f) J‖ ≤
      (x ^ I.card * singletonFreeProdSumOn y (Finset.univ \ I)) * ∏ i, n i := by
    intro I
    have h₁ : ‖∏ i ∈ I, (centeredMean ρ.1 (energies (L := L) (K := K) f) (energyMeans ν f) i : ℂ)‖ ≤
        x ^ I.card * ∏ i ∈ I, n i := by
      rw [norm_prod]
      refine (Finset.prod_le_prod (g := fun i => x * n i) (fun _ _ => norm_nonneg _)
        fun i _ => ?_).trans_eq ?_
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact hδ i
      · rw [Finset.prod_mul_distrib, Finset.prod_const]
    have h₂ : ‖∑ π ∈ atLeastTwoPartitions (Finset.univ \ I), ∏ J ∈ π.parts,
          recenteredCumulant ρ.1 (energies (L := L) (K := K) f) (energyMeans ν f) J‖ ≤
        singletonFreeProdSumOn y (Finset.univ \ I) * ∏ i ∈ Finset.univ \ I, n i := by
      refine (norm_sum_le _ _).trans ?_
      rw [singletonFreeProdSumOn, Finset.sum_mul]
      refine Finset.sum_le_sum fun π hπ => ?_
      rw [norm_prod]
      refine (Finset.prod_le_prod (g := fun J => y J.card * ∏ i ∈ J, n i)
        (fun _ _ => norm_nonneg _) fun J hJ => ?_).trans_eq ?_
      · have h2 := SetPartition.two_le_card_of_mem_atLeastTwoPartitions hπ hJ
        rw [recenteredCumulant_of_two_le_card _ _ _ h2]
        exact hκ J h2
      · rw [Finset.prod_mul_distrib, prod_parts_prod_eq]
    rw [norm_mul]
    refine (mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)).trans_eq ?_
    rw [← Finset.prod_sdiff (Finset.subset_univ I)]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h, momentBound, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => hA I)
private theorem get_mem_c1Compact (X : Tuple) (i : Fin X.1.length) :
    X.1.get i ∈ c1Compact Set.univ :=
  X.2.1 _ (List.get_mem _ _)
private theorem realExpectation_centeredProduct
    (ρ ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) (X : Tuple) :
    realExpectation ρ (centeredProduct L K ν X) =
      realExpect ρ.1 (fun U => ∏ i, (energies (L := L) (K := K) (fun i => X.1.get i) i U -
        energyMeans ν (fun i => X.1.get i) i)) := by
  have h := funext (centeredProduct_apply ν X)
  rw [realExpectation, h]
  rfl
private theorem momentPartitionExpansion_holds
    (hR : Cumulants.ProductRecentering.ProductRecenteringExpansion)
    (hW : SmearedEnergyStructure (PeriodicLattice.meshSize L (K : ℤ)))
    (ρ ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) (X : Tuple) :
    MomentPartitionExpansion ρ ν X := by
  rw [MomentPartitionExpansion, realExpectation_centeredProduct]
  exact moment_eq_sum_partitions hR ρ ν _ fun i => isBoundedRealRV_of_mem hW (get_mem_c1Compact X i)
private theorem prod_orderEmbOfFin_eq {k : ℕ} (J : Finset (Fin k)) (g : Fin k → ℝ) :
    ∏ a : Fin J.card, g (J.orderEmbOfFin rfl a) = ∏ i ∈ J, g i := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.LimitPassage.prod_comp_orderEmbOfFin <;> assumption
private theorem momentBounded_holds
    (hR : Cumulants.ProductRecentering.ProductRecenteringExpansion)
    (s : Conventions.StandingParameters)
    {K : ℕ} (hW : SmearedEnergyStructure (PeriodicLattice.meshSize s.L (K : ℤ)))
    (ρ ν : BorelProb (PeriodicLattice.meshSize s.L (K : ℤ))) (M d R x : ℝ) (y : ℕ → ℝ)
    (X : Tuple) (hX : IsAdmissibleAt s d R X) (hN : ConstantsBound s ρ ν M d R x y) :
    MomentBounded ρ ν M x y X := by
  have hb : ∀ i, IsBoundedRealRV
      (energies (L := s.L) (K := K) (fun i => X.1.get i) i) :=
    fun i => isBoundedRealRV_of_mem hW (get_mem_c1Compact X i)
  rw [MomentBounded, realExpectation_centeredProduct, ← Fin.prod_univ_fun_getElem]
  refine moment_abs_le hR ρ ν _ hb x y (fun i => sharpNormR4 M (X.1.get i)) (fun i => ?_)
    fun J hJ => ?_
  · obtain ⟨c, hc⟩ := hX.1 i
    exact hN.singleBound (X.1.get i) (isLipschitzFor_of_mem (get_mem_c1Compact X i))
      ⟨c, fun y hy => hc ((tsupport_pt_eq s _).symm.subset hy)⟩
  · have h := hN.cumulantBound J.card hJ (Cumulants.restrictTuple (fun i => X.1.get i) J)
      (fun a => isLipschitzFor_of_mem (get_mem_c1Compact X _))
      ⟨fun a => hX.1 _, fun a a' haa => hX.2 _ _ fun e => haa ((J.orderEmbOfFin rfl).injective e)⟩
    rw [← prod_orderEmbOfFin_eq J fun i => sharpNormR4 M (X.1.get i)]
    exact h
private theorem euclidIsometry_ext {r r' : EuclidIsometry} (h : r.toFun = r'.toFun) : r = r' := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeLimits.euclidIsometry_ext <;> assumption
private theorem maxNorm_reflectionGroupIsometry (γ : reflectionGroup) (x : Space) :
    maxNorm ((reflectionGroupIsometry γ).toFun x) = maxNorm x := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitPlateaux.maxNorm_reflectionGroup_apply <;> assumption
private theorem tsupport_pushFn_subset {r : EuclidIsometry}
    (hr : ∀ x, maxNorm (r.toFun x) = maxNorm x) {f : ScalarField} {c : ℝ}
    (h : tsupport f ⊆ centredCube c) : tsupport (pushFn r f) ⊆ centredCube c := by
  intro x hx
  rw [tsupport_pushFn] at hx
  have e := hr (r.symm.toFun x)
  rw [EuclidIsometry.toFun_symm] at e
  change maxNorm x < c
  rw [e]
  exact h (Set.mem_preimage.1 hx)
private theorem abs_lt_of_mem_centredCube {x : Space} {c : ℝ} (h : x ∈ centredCube c) (μ : Fin 4) :
    |x μ| < c :=
  lt_of_le_of_lt (Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)) h
private theorem mirrorTuple_lt {s : Conventions.StandingParameters} {ϖ d R : ℝ} {X : Tuple}
    (hX : X ∈ admissibleClass s ϖ d R) (μ : Fin 4) (γ : reflectionGroup) :
    ∀ g ∈ (mirrorTuple μ γ X).1, ∀ x ∈ tsupport g, x μ < ϖ - d / 2 := by
  intro g hg x hx
  obtain ⟨g₁, hg₁, rfl⟩ := List.mem_map.1 hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg₁
  have h := tsupport_pushFn_subset (maxNorm_reflectionGroupIsometry _)
    (tsupport_pushFn_subset (maxNorm_reflectionGroupIsometry γ) (hX.2 f hf)) hx
  exact (le_abs_self _).trans_lt (abs_lt_of_mem_centredCube h μ)
private theorem lt_translatedTuple {s : Conventions.StandingParameters} {ϖ d R : ℝ} {X : Tuple}
    (hX : X ∈ admissibleClass s ϖ d R) (μ : Fin 4) (γ : reflectionGroup) :
    ∀ g ∈ (translatedTuple ϖ μ γ X).1, ∀ y ∈ tsupport g, ϖ + d / 2 < y μ := by
  intro g hg y hy
  obtain ⟨g₁, hg₁, rfl⟩ := List.mem_map.1 hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg₁
  rw [tsupport_pushFn] at hy
  have h := tsupport_pushFn_subset (maxNorm_reflectionGroupIsometry γ) (hX.2 f hf)
    (Set.mem_preimage.1 hy)
  rw [EuclidIsometry.symm_translate] at h
  have h₁ := (abs_lt.1 (abs_lt_of_mem_centredCube h μ)).1
  simp [PeriodicLattice.coordVec] at h₁
  linarith
private theorem isAdmissibleAt_iff (s : Conventions.StandingParameters) (d R : ℝ) (X : Tuple) :
    IsAdmissibleAt s d R X ↔
      (∀ f ∈ X.1, ∃ c : Space, tsupport f ⊆ closedBallR4 c R) ∧
        X.1.Pairwise fun f g => ∀ y ∈ tsupport f, ∀ z ∈ tsupport g, d ≤ euclidNormVec (y - z) := by
  constructor
  · intro h
    refine ⟨fun f hf => ?_, List.pairwise_iff_get.2 fun i j hij y hy z hz => ?_⟩
    · obtain ⟨i, rfl⟩ := List.get_of_mem hf
      obtain ⟨x, hx⟩ := h.1 i
      exact ⟨x, fun y hy => hx ((tsupport_pt_eq s _).symm.subset hy)⟩
    · have h₁ := (h.2 i j hij.ne).trans (iInf₂_le_of_le y ((tsupport_pt_eq s _).symm.subset hy)
        (iInf₂_le z ((tsupport_pt_eq s _).symm.subset hz)))
      exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).1 h₁
  · rintro ⟨h₁, h₂⟩
    have hp := List.pairwise_iff_get.1 h₂
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · obtain ⟨c, hc⟩ := h₁ _ (List.get_mem X.1 i)
      exact ⟨c, fun y hy => hc ((tsupport_pt_eq s _).subset hy)⟩
    · refine le_iInf₂ fun y hy => le_iInf₂ fun z hz => ENNReal.ofReal_le_ofReal ?_
      have hy' := (tsupport_pt_eq s _).subset hy
      have hz' := (tsupport_pt_eq s _).subset hz
      rcases lt_or_gt_of_ne hij with h | h
      · exact hp i j h y hy' z hz'
      · exact (hp j i h z hz' y hy').trans_eq (AmbientPoints.euclidNormVec_sub_comm z y)
private theorem concatenable_of_class {s : Conventions.StandingParameters} {ϖ d R : ℝ} {X : Tuple}
    (hd : 0 < d) (hX : X ∈ admissibleClass s ϖ d R) (μ : Fin 4) (γ : reflectionGroup) :
    Concatenable (mirrorTuple μ γ X) (translatedTuple ϖ μ γ X) :=
  fun f hf g hg => Set.disjoint_left.2 fun x hx hx' => by
    have h₁ := mirrorTuple_lt hX μ γ f hf x hx
    have h₂ := lt_translatedTuple hX μ γ g hg x hx'
    linarith
private theorem isAdmissibleAt_concat {s : Conventions.StandingParameters} {ϖ d R : ℝ} {X : Tuple}
    (hd : 0 < d) (hR : 0 < R) (hC : AdmissibleClassProperties s) (hX : X ∈ admissibleClass s ϖ d R)
    (μ : Fin 4) (γ : reflectionGroup)
    (h : Concatenable (mirrorTuple μ γ X) (translatedTuple ϖ μ γ X)) :
    IsAdmissibleAt s d R (concat _ _ h) := by
  have h₁ := (isAdmissibleAt_iff s d R _).1
    (hC.2.2.2 _ d R hd hR _ (hC.2.2.2 (reflectionGroupIsometry γ) d R hd hR X hX.1) :
      IsAdmissibleAt s d R (mirrorTuple μ γ X))
  have h₂ := (isAdmissibleAt_iff s d R _).1
    (hC.2.2.2 _ d R hd hR _ (hC.2.2.2 (reflectionGroupIsometry γ) d R hd hR X hX.1) :
      IsAdmissibleAt s d R (translatedTuple ϖ μ γ X))
  refine (isAdmissibleAt_iff s d R _).2 ⟨fun f hf => ?_, ?_⟩
  · rcases List.mem_append.1 hf with hf | hf
    · exact h₁.1 f hf
    · exact h₂.1 f hf
  · refine List.pairwise_append.2 ⟨h₁.2, h₂.2, fun f hf g hg => ?_⟩
    intro u hu v hv
    have e₁ := mirrorTuple_lt hX μ γ f hf u hu
    have e₂ := lt_translatedTuple hX μ γ g hg v hv
    refine le_trans ?_ (abs_apply_le_euclidNormVec (u - v) μ)
    rw [Pi.sub_apply, abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)
private theorem centeredProductLinear_basisOf (L K : ℕ)
    (ν : BorelProb (PeriodicLattice.meshSize L (K : ℤ))) (X : Tuple) :
    centeredProductLinear L K ν (basisOf X) = toComplexObs (centeredProduct L K ν X) := by
  funext U
  simp [centeredProductLinear, basisOf, toComplexObs]
private theorem actOn_centeredProduct {L : ℕ} {K : ℕ+}
    {ν : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))} (hC : CenteredProductCalculus L K ν)
    (r : LatticeSymmetry (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))) (X : Tuple) :
    r.actOn (toComplexObs (centeredProduct L K ν X)) =
      toComplexObs (centeredProduct L K ν (push (latticeSymmetryToEuclid r) X)) := by
  have h := hC.2.2.2.2.1 r (basisOf X)
  have m : pushComb (latticeSymmetryToEuclid r) (basisOf X) =
      basisOf (push (latticeSymmetryToEuclid r) X) := by
    simp [pushComb, basisOf, Finsupp.mapDomain_single]
  rw [m, centeredProductLinear_basisOf, centeredProductLinear_basisOf] at h
  exact h.symm
private theorem latticeSymmetryToEuclid_coordinateReflect (a : ℝ) (μ : Fin 4) :
    latticeSymmetryToEuclid (LatticeAtSpacing.coordinateReflect a μ) =
      reflectionGroupIsometry (axisReflectionElem μ) := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitPlateaux.latticeSymmetryToEuclid_coordinateReflect <;> assumption
private theorem latticeSymmetryToEuclid_shift {a ϖ : ℝ} {r : ℕ+} (h : (r : ℝ) * a = ϖ) (μ : Fin 4) :
    latticeSymmetryToEuclid (shift ((2 * (r : ℕ)) • axisStep a μ)) =
      EuclidIsometry.translate ((2 * ϖ) • PeriodicLattice.coordVec μ) := by
  refine euclidIsometry_ext ?_
  funext x
  change x + (((2 * (r : ℕ)) • axisStep a μ : InfiniteLattice.LatticePoint a) : Space) =
    x + (2 * ϖ) • PeriodicLattice.coordVec μ
  congr 1
  ext i
  by_cases e : i = μ
  · subst e
    simp [PeriodicLattice.coordVec, axisStep, ← h]
    ring
  · simp [PeriodicLattice.coordVec, axisStep, e]
private theorem actOn_reflect_reflectedObservable {L : ℕ} {K : ℕ+}
    {ν : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))} (hC : CenteredProductCalculus L K ν)
    (μ : Fin 4) (γ : reflectionGroup) (X : Tuple) :
    (LatticeAtSpacing.coordinateReflect _ μ).actOn (reflectedObservable ν γ X) =
      toComplexObs (centeredProduct L K ν (mirrorTuple μ γ X)) := by
  rw [reflectedObservable, actOn_centeredProduct hC, actOn_centeredProduct hC,
    latticeSymmetryToEuclid_coordinateReflect]
  rfl
private theorem actOn_shift_reflectedObservable {L : ℕ} {K : ℕ+}
    {ν : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))} (hC : CenteredProductCalculus L K ν)
    {ϖ : ℝ} {r : ℕ+}
    (h : (r : ℝ) * PeriodicLattice.meshSize L ((K : ℕ) : ℤ) = ϖ) (μ : Fin 4) (γ : reflectionGroup)
    (X : Tuple) :
    (shift ((2 * (r : ℕ)) • axisStep (PeriodicLattice.meshSize L ((K : ℕ) : ℤ)) μ)).actOn
        (reflectedObservable ν γ X) =
      toComplexObs (centeredProduct L K ν (translatedTuple ϖ μ γ X)) := by
  rw [reflectedObservable, actOn_centeredProduct hC, actOn_centeredProduct hC,
    latticeSymmetryToEuclid_shift h]
  rfl
private theorem sizeCorr_eq {L : ℕ} {K : ℕ+}
    {ρ ν : BorelProb (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))} (hC : CenteredProductCalculus L K ν)
    {ϖ : ℝ} {r : ℕ+}
    (hr : (r : ℝ) * PeriodicLattice.meshSize L ((K : ℕ) : ℤ) = ϖ) (μ : Fin 4) (γ : reflectionGroup)
    (X : Tuple) (h : Concatenable (mirrorTuple μ γ X) (translatedTuple ϖ μ γ X)) :
    sizeCorr ρ ν r μ γ X =
      ((realExpectation ρ (centeredProduct L K ν (concat _ _ h)) : ℝ) : ℂ) := by
  rw [sizeCorr, DirectionPictures.reflCorr, actOn_reflect_reflectedObservable hC,
    actOn_shift_reflectedObservable hC hr, hC.2.2.2.1 _ _ h, realExpectation]
  change (∫ U, (starRingEnd ℂ) (toComplexObs (centeredProduct L K ν (mirrorTuple μ γ X)) U) *
    toComplexObs (centeredProduct L K ν (translatedTuple ϖ μ γ X)) U ∂ρ.1) = _
  have e : ∀ U, (starRingEnd ℂ) (toComplexObs (centeredProduct L K ν (mirrorTuple μ γ X)) U) *
      toComplexObs (centeredProduct L K ν (translatedTuple ϖ μ γ X)) U =
      (((centeredProduct L K ν (mirrorTuple μ γ X) *
        centeredProduct L K ν (translatedTuple ϖ μ γ X)) U : ℝ) : ℂ) := fun U => by
    simp [toComplexObs]
  exact (integral_congr_ae (Filter.Eventually.of_forall e)).trans integral_ofReal
private theorem prod_sharpNorm_push (hC : ∀ (r : EuclidIsometry) (f : ScalarField),
      IsLipschitzFor euclidDistR4 f → HasCompactSupport f → ∀ M : ℝ,
        sharpNormR4 M (pushFn r f) = sharpNormR4 M f)
    (M : ℝ) (r : EuclidIsometry) (Z : Tuple) :
    ((push r Z).1.map (sharpNormR4 M)).prod = (Z.1.map (sharpNormR4 M)).prod := by
  change ((Z.1.map (pushFn r)).map (sharpNormR4 M)).prod = _
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun f hf => ?_
  exact hC r f (isLipschitzFor_of_mem (Z.2.1 f hf)) (Z.2.1 f hf).2.1 M
private theorem prod_map_mul_self (l : List ScalarField) (g : ScalarField → ℝ) :
    (l.map g).prod * (l.map g).prod = (l.map fun f => g f ^ 2).prod := by
  induction l with
  | nil => simp
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons, ← ih]
    ring
private theorem prod_sharpNorm_concat (hC : ∀ (r : EuclidIsometry) (f : ScalarField),
      IsLipschitzFor euclidDistR4 f → HasCompactSupport f → ∀ M : ℝ,
        sharpNormR4 M (pushFn r f) = sharpNormR4 M f)
    (M ϖ : ℝ) (μ : Fin 4) (γ : reflectionGroup) (X : Tuple)
    (h : Concatenable (mirrorTuple μ γ X) (translatedTuple ϖ μ γ X)) :
    ((concat _ _ h).1.map (sharpNormR4 M)).prod =
      (X.1.map fun f => sharpNormR4 M f ^ 2).prod := by
  have e₁ : ((mirrorTuple μ γ X).1.map (sharpNormR4 M)).prod =
      (X.1.map (sharpNormR4 M)).prod := by
    rw [mirrorTuple, prod_sharpNorm_push hC, prod_sharpNorm_push hC]
  have e₂ : ((translatedTuple ϖ μ γ X).1.map (sharpNormR4 M)).prod =
      (X.1.map (sharpNormR4 M)).prod := by
    rw [translatedTuple, prod_sharpNorm_push hC, prod_sharpNorm_push hC]
  rw [show (concat _ _ h).1 = (mirrorTuple μ γ X).1 ++ (translatedTuple ϖ μ γ X).1 from rfl,
    List.map_append, List.prod_append, e₁, e₂, prod_map_mul_self]
private theorem sizeIsMoment_holds (s : Conventions.StandingParameters) (K : ℕ+)
    (hCl : AdmissibleClassProperties s)
    (ρ ν : BorelProb (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ))) (hC : CenteredProductCalculus s.L K ν)
    (hO : ∀ (A : InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) → ℂ) (r : ℕ+),
      A ∈ regionObservables _ (scaledCube (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r) →
      ∀ (μ : Fin 4) (γ : axisReflectionGroup),
        ∃ t : ℝ, 0 ≤ t ∧ DirectionPictures.reflCorr ρ μ
            ((axisReflectionGroup.toLatticeSymmetry _ γ).actOn A)
            ((shift ((2 * (r : ℕ)) • axisStep _ μ)).actOn
              ((axisReflectionGroup.toLatticeSymmetry _ γ).actOn A)) =
            (t : ℂ))
    {ϖ d R : ℝ} (hd : 0 < d) (hR : 0 < R) {X : Tuple} (hX : X ∈ admissibleClass s ϖ d R)
    (r : ℕ+) (hr : (r : ℝ) * PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) = ϖ)
    (hA : toComplexObs (centeredProduct s.L K ν X) ∈
      regionObservables (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ))
        (scaledCube (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r))
    (μ : Fin 4) (γ : reflectionGroup) : SizeIsMoment s ρ ν ϖ d R r μ γ X := by
  have h := concatenable_of_class hd hX μ γ
  refine ⟨h, ?_, isAdmissibleAt_concat hd hR hCl hX μ γ h, ?_, sizeCorr_eq hC hr μ γ X h⟩
  · simp [concat, Tuple.len, mirrorTuple, translatedTuple, push]
    omega
  · obtain ⟨t, ht, e⟩ := hO _ r hA μ
      ⟨γ.1, by rw [axisReflectionGroup_eq_reflectionGroup]; exact γ.2⟩
    have e' : sizeCorr ρ ν r μ γ X = (t : ℂ) := e
    rw [e']
    exact_mod_cast ht
theorem sizesIndependentOfSpacing_of_inputs
    (hR : Cumulants.ProductRecentering.ProductRecenteringExpansion)
    (hL : LatticeRepresentatives.Statement)
    (hT : DirectionPictures.singleLatticeInputs)
    (hP : PeriodicGibbs.periodicGibbsTheorem) : SizesIndependentOfSpacing := by
  intro s K β ν ρ hβ hν hρ X
  obtain ⟨hW, -, hC, hLoc, hCl⟩ := hL s K β ν hβ hν
  have ha := meshSize_pos s.isAdmissible ((K : ℕ) : ℤ)
  have hRP := ((hP s.L s.isAdmissible).1 K β hβ ρ hρ).1
  have hD := (hT _ ha ρ hRP).2.2.2.1.2
  have hO : ∀ (A : InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) → ℂ)
      (r : ℕ+), A ∈ regionObservables _ (scaledCube (PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ)) r) →
      ∀ (μ : Fin 4) (γ : axisReflectionGroup),
        ∃ t : ℝ, 0 ≤ t ∧ DirectionPictures.reflCorr ρ μ
            ((axisReflectionGroup.toLatticeSymmetry _ γ).actOn A)
            ((shift ((2 * (r : ℕ)) • axisStep _ μ)).actOn
              ((axisReflectionGroup.toLatticeSymmetry _ γ).actOn A)) =
            (t : ℂ) := fun A r hA μ γ =>
    ⟨_, by positivity, (hD r A hA).2.2.2.2 μ γ⟩
  refine ⟨momentPartitionExpansion_holds hR hW ρ ν X, fun M d R x y _ _ hX hN =>
    momentBounded_holds hR s hW ρ ν M d R x y X hX hN, fun ϖ hϖ d R hd hRpos hX had r hr => ?_⟩
  have hr' : (r : ℝ) * PeriodicLattice.meshSize s.L ((K : ℕ) : ℤ) = ϖ := by
    rw [hr]
    field_simp
  have hc := hLoc.1 ϖ hϖ d R hd hRpos X hX had r hr
  have hsize : ∀ (μ : Fin 4) (γ : reflectionGroup), SizeIsMoment s ρ ν ϖ d R r μ γ X :=
    sizeIsMoment_holds s K hCl ρ ν hC hO hd hRpos hX r hr' hc.1
  refine ⟨hc, hsize, fun M x y hN => ⟨momentBounded_holds hR s hW ρ ν M d R x y X hX.1 hN, ?_, ?_⟩⟩
  · exact (hD r _ hc.1).2.2.2.1
  · obtain ⟨p, hp⟩ := (hD r _ hc.1).2.2.1.1
    obtain ⟨h, hlen, hadm, -, heq⟩ := hsize p.1
      ⟨p.2.1, by rw [← axisReflectionGroup_eq_reflectionGroup]; exact p.2.2⟩
    have e : (scaledCubeReflectionSize ha ρ.1 r
          (toComplexObs (centeredProduct s.L K ν X)) : ℂ) =
        ((realExpectation ρ (centeredProduct s.L K ν (concat _ _ h)) : ℝ) : ℂ) :=
      hp.symm.trans heq
    have e' := Complex.ofReal_injective e
    have hb := momentBounded_holds hR s hW ρ ν M d R x y _ hadm hN
    rw [MomentBounded, hlen] at hb
    rw [prod_sharpNorm_concat hCl.2.2.1] at hb
    exact e'.le.trans ((le_abs_self _).trans hb)
end YangMills.Construction.ReflectionPositivity.SpacingFreeSizes
