import YangMills.Construction.ReflectionsAndOneInsertion.PartitionOfUnityOfMesh
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsUsedOfALimitAlongStates
import YangMills.Construction.SystemsWithFiveBounds.OnePointAtEveryRadius
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds.OnePointDifferenceProof
open TestFunctions
open InfiniteLattice (GaugeField IsBoundedBorelCompactlySupported ElementaryPlaquette AmbientSpace
  periodicGibbsSet faceEnergy smearedEnergy)
open MeshPartition (boxFrom localizedPiece)
open PeriodicGibbsLimits.ObservablesAndMomentsDefined (HasFiniteFaceSum)
theorem isCompact_closedBallR4 (x : AmbientSpace) (r : ℝ) : IsCompact (closedBallR4 x r) := by apply _root_.YangMills.DeltaSharedProofs.p501115 <;> assumption
theorem continuous_of_isLipschitzFor {f : AmbientSpace → ℝ} (h : IsLipschitzFor euclidDistR4 f) :
    Continuous f := by apply _root_.YangMills.SharedProofs.p29528 <;> assumption
theorem isBoundedBorelCompactlySupported_of_tsupport_subset {f : AmbientSpace → ℝ}
    (h : IsLipschitzFor euclidDistR4 f) {x : AmbientSpace}
    {r : ℝ} (hs : tsupport f ⊆ closedBallR4 x r) : IsBoundedBorelCompactlySupported f := by
  have hc := continuous_of_isLipschitzFor h
  have hk : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (isCompact_closedBallR4 x r) (isClosed_tsupport f) hs
  exact ⟨hc.measurable, hk.exists_bound_of_continuous hc, hk⟩
theorem smearedEnergy_eq_sum {a : ℝ} {ι : Type*} (T : Finset ι) {f : AmbientSpace → ℝ}
    {g : ι → AmbientSpace → ℝ} (hf : ∀ x, f x = ∑ i ∈ T, g i x) (U : GaugeField a)
    (hfin : ∀ i ∈ T, HasFiniteFaceSum (g i) U) :
    smearedEnergy f U = ∑ i ∈ T, smearedEnergy (g i) U := by
  simp only [smearedEnergy]
  rw [← finsum_sum_comm T (fun (p : ElementaryPlaquette a) i => faceEnergy U p • g i p.center) hfin]
  refine finsum_congr fun p => ?_
  rw [hf, Finset.smul_sum]
theorem sharpNormR4_le_of_half_mesh {M : ℝ} (hM : 1 ≤ M) {f p : AmbientSpace → ℝ}
    (h₁ : uniformNorm p ≤ uniformNorm f)
    (h₂ : lipConstR4 p ≤ lipConstR4 f + Real.pi / (1 / 2) * uniformNorm f) :
    sharpNormR4 M p ≤ (1 + 80 * Real.pi * M) * sharpNormR4 M f := by
  have hs : uniformNorm f ≤ sharpNormR4 M f := le_max_left _ _
  have hl : 40 * M * lipConstR4 f ≤ sharpNormR4 M f := le_max_right _ _
  have hs0 : 0 ≤ uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
  have hS : 0 ≤ sharpNormR4 M f := hs0.trans hs
  have hc : 0 ≤ 80 * Real.pi * M := by positivity
  refine max_le ?_ ?_
  · nlinarith [mul_nonneg hc hS]
  · have e : 40 * M * (lipConstR4 f + Real.pi / (1 / 2) * uniformNorm f) =
        40 * M * lipConstR4 f + 80 * Real.pi * M * uniformNorm f := by ring
    have h₃ : 40 * M * lipConstR4 p ≤ 40 * M * (lipConstR4 f + Real.pi / (1 / 2) * uniformNorm f) :=
      mul_le_mul_of_nonneg_left h₂ (by positivity)
    have h₄ : 80 * Real.pi * M * uniformNorm f ≤ 80 * Real.pi * M * sharpNormR4 M f :=
      mul_le_mul_of_nonneg_left hs hc
    rw [e] at h₃
    linarith
theorem onePointDifferenceAllRadii_of_smearedObservablesWellDefined
    (hP : MeshPartition.MeshPartitionStatement)
    (hF : SmearedObservablesWellDefined) :
    OnePointDifferenceAllRadii := by
  rintro F N B K β hd ν hν ν' hν' R hR f hf ⟨x, hx⟩
  have hL0 : (0 : ℝ) < F.L := by
    have := F.admissible.2
    exact_mod_cast (by omega : 0 < F.L)
  have ha : 0 < PeriodicLattice.meshSize F.L ((K : ℕ) : ℤ) := by
    unfold PeriodicLattice.meshSize
    exact zpow_pos hL0 _
  have : IsProbabilityMeasure ν := (F.stateSet_subset K β hd hν).1.1
  have : IsProbabilityMeasure ν' := (F.stateSet_subset K β hd hν').1.1
  have hform := (hF _ ha).1
  obtain ⟨-, -, hcut⟩ := hP (1 / 2) (by norm_num)
  have hbox : tsupport f ⊆ boxFrom (fun μ => x μ - R) (fun _ => 2 * R) := fun y hy μ => by
    have h : |(y - x) μ| ≤ TorusMetric.euclidNormVec (y - x) :=
      Real.abs_le_sqrt (Finset.single_le_sum (f := fun ν => (y - x) ν ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ μ))
    have h₂ := abs_le.1 (h.trans (hx hy))
    simp only [Pi.sub_apply] at h₂
    constructor <;> linarith [h₂.1, h₂.2]
  obtain ⟨hfin, hcount, hsum, hpiece⟩ := hcut f _ _ hf (fun _ => by positivity) hbox
  classical
  set T := hfin.toFinset with hT
  have hmem : ∀ α ∈ T, α ∈ CosineSquaredBump.latticeOfSpacing (1 / 2 : ℝ) := fun α hα =>
    (hfin.mem_toFinset.1 hα).1
  have hsumT : f = ∑ α ∈ T, localizedPiece (1 / 2) α f := by
    have e₁ := finsum_subtype_eq_finsum_cond (f := fun α => localizedPiece (1 / 2) α f)
      (fun α => α ∈ CosineSquaredBump.latticeOfSpacing (1 / 2 : ℝ))
    have e₂ : ∑ᶠ (α) (_ : α ∈ CosineSquaredBump.latticeOfSpacing (1 / 2 : ℝ)),
        localizedPiece (1 / 2) α f = ∑ α ∈ T, localizedPiece (1 / 2) α f := by
      refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
      ext α
      simp only [mem_inter_iff, Finset.mem_coe, hT, Set.Finite.mem_toFinset, Function.mem_support,
        mem_ofPred_eq]
      tauto
    exact hsum.trans (e₁.trans e₂)
  have hfT : ∀ y, f y = ∑ α ∈ T, localizedPiece (1 / 2) α f y := fun y => by
    have := congrFun hsumT y
    rwa [Finset.sum_apply] at this
  have hball : ∀ α ∈ T, tsupport (localizedPiece (1 / 2) α f) ⊆ closedBallR4 α 1 := fun α hα => by
    have h := (hpiece α (hmem α hα)).1
    have e : (2 : ℝ) * (1 / 2) = 1 := by norm_num
    rw [e] at h
    exact h.trans inter_subset_right
  have hlip : ∀ α ∈ T, IsLipschitzFor euclidDistR4 (localizedPiece (1 / 2) α f) := fun α hα =>
    (hpiece α (hmem α hα)).2.2.1
  have hbb : ∀ α ∈ T, IsBoundedBorelCompactlySupported (localizedPiece (1 / 2) α f) := fun α hα =>
    isBoundedBorelCompactlySupported_of_tsupport_subset (hlip α hα) (hball α hα)
  have hint : ∀ (μ : Measure (GaugeField (PeriodicLattice.meshSize F.L ((K : ℕ) : ℤ))))
      [IsProbabilityMeasure μ], ∀ α ∈ T,
        Integrable (smearedEnergy (localizedPiece (1 / 2) α f)) μ := by
    intro μ _ α hα
    obtain ⟨-, hr⟩ := hform _ (hbb α hα)
    obtain ⟨C, hC⟩ := hr.bounded
    exact Integrable.of_bound hr.measurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun U => by simpa [Real.norm_eq_abs] using hC U)
  have hexp : ∀ (μ : Measure (GaugeField (PeriodicLattice.meshSize F.L ((K : ℕ) : ℤ))))
      [IsProbabilityMeasure μ], ∫ U, smearedEnergy f U ∂μ =
        ∑ α ∈ T, ∫ U, smearedEnergy (localizedPiece (1 / 2) α f) U ∂μ := by
    intro μ _
    have e : (fun U => smearedEnergy f U) =
        fun U : GaugeField (PeriodicLattice.meshSize F.L ((K : ℕ) : ℤ)) =>
          ∑ α ∈ T, smearedEnergy (localizedPiece (1 / 2) α f) U :=
      funext fun U => smearedEnergy_eq_sum T hfT U fun α hα => (hform _ (hbb α hα)).1 U
    rw [e, integral_finsetSum T fun α hα => hint μ α hα]
  have hcard : (T.card : ℝ) ≤ 256 * (1 + R) ^ 4 := by
    rw [Set.ncard_eq_toFinset_card _ hfin] at hcount
    have h₁ : (T.card : ℝ) ≤ (4 * R + 3) ^ 4 := hcount.trans_eq (by
      rw [Fin.prod_univ_four]
      ring)
    have h₂ : (4 * R + 3) ^ 4 ≤ (4 * (1 + R)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    linarith
  have hC1 : 0 ≤ N.onePointConst 1 := B.admissible_constants.onePointConst_nonneg 1 one_pos
  have hM0 : 0 < F.M := lt_of_lt_of_le one_pos F.one_le_M
  have hS : 0 ≤ sharpNormR4 F.M f :=
    (Real.iSup_nonneg fun _ => norm_nonneg _ : 0 ≤ uniformNorm f).trans (le_max_left _ _)
  have hX : 0 ≤ (1 + 80 * Real.pi * F.M) * sharpNormR4 F.M f := by positivity
  rw [hexp ν, hexp ν', ← Finset.sum_sub_distrib]
  calc |∑ α ∈ T, ((∫ U, smearedEnergy (localizedPiece (1 / 2) α f) U ∂ν) -
          ∫ U, smearedEnergy (localizedPiece (1 / 2) α f) U ∂ν')|
      ≤ ∑ α ∈ T, |(∫ U, smearedEnergy (localizedPiece (1 / 2) α f) U ∂ν) -
          ∫ U, smearedEnergy (localizedPiece (1 / 2) α f) U ∂ν'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _α ∈ T, N.onePointConst 1 * ((1 + 80 * Real.pi * F.M) * sharpNormR4 F.M f) := by
        refine Finset.sum_le_sum fun α hα => ?_
        refine (B.mean_sub_le K β hd ν hν ν' hν' 1 one_pos _ (hlip α hα)
          ⟨α, hball α hα⟩).trans ?_
        obtain ⟨-, h₁, -, h₂, -⟩ := hpiece α (hmem α hα)
        exact mul_le_mul_of_nonneg_left (sharpNormR4_le_of_half_mesh F.one_le_M h₁ h₂) hC1
    _ = (T.card : ℝ) * (N.onePointConst 1 * ((1 + 80 * Real.pi * F.M) * sharpNormR4 F.M f)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (256 * (1 + R) ^ 4) *
          (N.onePointConst 1 * ((1 + 80 * Real.pi * F.M) * sharpNormR4 F.M f)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hC1 hX)
    _ ≤ (256 * (1 + R) ^ 4) *
          ((1 + N.onePointConst 1) * ((1 + 80 * Real.pi * F.M) * sharpNormR4 F.M f)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hX) (by positivity)
    _ = radiusTransferConstant F.M N * (1 + R) ^ 4 * sharpNormR4 F.M f := by
        unfold radiusTransferConstant
        ring
theorem onePointDifferenceAllRadii_holds (hP : MeshPartition.MeshPartitionStatement)
    (hM : PeriodicGibbsLimits.ObservablesAndMomentsDefined.Statement) :
    OnePointDifferenceAllRadii :=
  onePointDifferenceAllRadii_of_smearedObservablesWellDefined hP
    (smearedObservablesWellDefined_of hM)
end YangMills.Construction.SystemsWithFiveBounds.OnePointDifferenceProof
end
