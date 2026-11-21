import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.InfiniteLattice.CentredMomentsAtOneIndexAndTheTwoFormsOfVolumeFirst
import YangMills.Construction.InfiniteLattice.MomentsAndCumulantsUnderTwoMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CutoffLimits.TwoMeasures
open YangMills.Construction.Cumulants (mixedCumulant finsetCumulant finsetMoment)
open YangMills.Construction.InfiniteLattice (centeredMoment ursellFunction compactTestFunctions)
open YangMills.Construction.Probability (IsBoundedRealRV complexExpectation)
open YangMills.Construction.SetPartition (PartitionsFin blockCount singletonFree)
theorem norm_blockMean_le {𝒳 : Type} [MeasurableSpace 𝒳] (ν : Measure 𝒳)
    [IsProbabilityMeasure ν] {n : ℕ} (Y : Fin n → 𝒳 → ℝ) (y : Fin n → ℝ)
    (hY : ∀ i x, |Y i x| ≤ y i) (I : Finset (Fin n)) :
    ‖blockMean ν Y I‖ ≤ ∏ i ∈ I, y i := by
  have hpt : ∀ x, ‖((blockProduct Y I x : ℝ) : ℂ)‖ ≤ ∏ i ∈ I, y i := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, blockProduct, Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hY i x
  have h := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hpt)
  simpa [blockMean, complexExpectation] using h
theorem norm_finset_prod_sub_le {ι : Type*} [DecidableEq ι] (P : Finset ι) (a b : ι → ℂ)
    (w : ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (ha : ∀ I ∈ P, ‖a I‖ ≤ w I) (hb : ∀ I ∈ P, ‖b I‖ ≤ w I)
    (hab : ∀ I ∈ P, ‖a I - b I‖ ≤ ε * w I) :
    ‖∏ I ∈ P, a I - ∏ I ∈ P, b I‖ ≤ (P.card : ℝ) * ε * ∏ I ∈ P, w I := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert I P hI ih =>
    have ha' : ∀ J ∈ P, ‖a J‖ ≤ w J := fun J hJ => ha J (Finset.mem_insert_of_mem hJ)
    have hb' : ∀ J ∈ P, ‖b J‖ ≤ w J := fun J hJ => hb J (Finset.mem_insert_of_mem hJ)
    have hab' : ∀ J ∈ P, ‖a J - b J‖ ≤ ε * w J := fun J hJ => hab J (Finset.mem_insert_of_mem hJ)
    have hrec := ih ha' hb' hab'
    have hA : ‖∏ J ∈ P, a J‖ ≤ ∏ J ∈ P, w J := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) ha'
    have hbI := hb I (Finset.mem_insert_self I P)
    have habI := hab I (Finset.mem_insert_self I P)
    have hwI : 0 ≤ w I := (norm_nonneg _).trans hbI
    rw [Finset.prod_insert hI, Finset.prod_insert hI, Finset.prod_insert hI,
      Finset.card_insert_of_notMem hI]
    have hsplit : a I * ∏ J ∈ P, a J - b I * ∏ J ∈ P, b J =
        (a I - b I) * ∏ J ∈ P, a J + b I * (∏ J ∈ P, a J - ∏ J ∈ P, b J) := by ring
    rw [hsplit]
    calc ‖(a I - b I) * ∏ J ∈ P, a J + b I * (∏ J ∈ P, a J - ∏ J ∈ P, b J)‖
        ≤ ‖a I - b I‖ * ‖∏ J ∈ P, a J‖ + ‖b I‖ * ‖∏ J ∈ P, a J - ∏ J ∈ P, b J‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ (ε * w I) * ∏ J ∈ P, w J + w I * ((P.card : ℝ) * ε * ∏ J ∈ P, w J) := by
          have h₁ : ‖a I - b I‖ * ‖∏ J ∈ P, a J‖ ≤ (ε * w I) * ∏ J ∈ P, w J :=
            mul_le_mul habI hA (norm_nonneg _) (mul_nonneg hε hwI)
          have h₂ : ‖b I‖ * ‖∏ J ∈ P, a J - ∏ J ∈ P, b J‖ ≤
              w I * ((P.card : ℝ) * ε * ∏ J ∈ P, w J) :=
            mul_le_mul hbI hrec (norm_nonneg _) hwI
          exact add_le_add h₁ h₂
      _ = ((P.card + 1 : ℕ) : ℝ) * ε * (w I * ∏ J ∈ P, w J) := by
          push_cast
          ring
theorem finsetMoment_eq_blockMean {𝒳 : Type} [MeasurableSpace 𝒳] (ν : Measure 𝒳) {n : ℕ}
    (Y : Fin n → 𝒳 → ℝ) {I : Finset (Fin n)} (hI : I.Nonempty) :
    finsetMoment ν Y I = blockMean ν Y I := by
  rw [finsetMoment, if_neg hI.ne_empty]
  rfl
theorem mixedCumulant_eq_partition_sum (hRel : Cumulants.CumulantMomentRelations)
    {𝒳 : Type} [MeasurableSpace 𝒳] (ν : Measure 𝒳) [IsProbabilityMeasure ν] {n : ℕ}
    (Y : Fin n → 𝒳 → ℝ) (hn : 1 ≤ n) (hY : ∀ i, IsBoundedRealRV (Y i)) :
    mixedCumulant ν Y =
      ∑ π : PartitionsFin n, (-1 : ℂ) ^ (blockCount π - 1) *
        ((blockCount π - 1).factorial : ℂ) * ∏ I ∈ π.parts, blockMean ν Y I := by
  obtain ⟨-, -, -, -, -, -, h⟩ := hRel 𝒳 ν n Y hY
  rw [h hn]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun I hI =>
    finsetMoment_eq_blockMean ν Y (π.nonempty_of_mem_parts hI)
theorem norm_mixedCumulant_sub_le (hRel : Cumulants.CumulantMomentRelations)
    {𝒳 : Type} [MeasurableSpace 𝒳] (μ ν : Measure 𝒳) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {n : ℕ} (Y : Fin n → 𝒳 → ℝ) (hn : 1 ≤ n)
    (hY : ∀ i, IsBoundedRealRV (Y i)) (y : Fin n → ℝ) (ε : ℝ) (hy : ∀ i, 0 ≤ y i)
    (hε : 0 ≤ ε) (hbd : ∀ i x, |Y i x| ≤ y i)
    (hnear : ∀ I : Finset (Fin n), I.Nonempty →
      ‖blockMean μ Y I - blockMean ν Y I‖ ≤ ε * ∏ i ∈ I, y i) :
    ‖mixedCumulant μ Y - mixedCumulant ν Y‖ ≤
      (partitionFactorialSum n : ℝ) * ε * ∏ i, y i := by
  have hprod : ∀ π : PartitionsFin n, ∏ I ∈ π.parts, ∏ i ∈ I, y i = ∏ i, y i := by
    intro π
    calc ∏ I ∈ π.parts, ∏ i ∈ I, y i = ∏ i ∈ π.parts.biUnion id, y i :=
          (Finset.prod_biUnion π.supIndep.pairwiseDisjoint).symm
      _ = ∏ i, y i := by rw [π.biUnion_parts]
  have hy₀ : 0 ≤ ∏ i, y i := Finset.prod_nonneg fun i _ => hy i
  have hblk : ∀ π : PartitionsFin n,
      ‖∏ I ∈ π.parts, blockMean μ Y I - ∏ I ∈ π.parts, blockMean ν Y I‖ ≤
        (blockCount π : ℝ) * ε * ∏ i, y i := by
    intro π
    have h := norm_finset_prod_sub_le π.parts (blockMean μ Y) (blockMean ν Y)
      (fun I => ∏ i ∈ I, y i) ε hε (fun I _ => norm_blockMean_le μ Y y hbd I)
      (fun I _ => norm_blockMean_le ν Y y hbd I)
      (fun I hI => hnear I (π.nonempty_of_mem_parts hI))
    rwa [hprod π] at h
  rw [mixedCumulant_eq_partition_sum hRel μ Y hn hY, mixedCumulant_eq_partition_sum hRel ν Y hn hY,
    ← Finset.sum_sub_distrib, partitionFactorialSum, Nat.cast_sum, Finset.sum_mul,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  rw [← mul_sub, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  have hfac : ((blockCount π - 1).factorial : ℝ) * (blockCount π : ℝ) ≤
      ((blockCount π).factorial : ℝ) := by
    have : (blockCount π - 1).factorial * blockCount π ≤ (blockCount π).factorial := by
      cases h : blockCount π with
      | zero => simp
      | succ m => simp [Nat.factorial_succ, Nat.mul_comm]
    exact_mod_cast this
  have hεy : 0 ≤ ε * ∏ i, y i := mul_nonneg hε hy₀
  calc ((blockCount π - 1).factorial : ℝ) *
        ‖∏ I ∈ π.parts, blockMean μ Y I - ∏ I ∈ π.parts, blockMean ν Y I‖
      ≤ ((blockCount π - 1).factorial : ℝ) * ((blockCount π : ℝ) * ε * ∏ i, y i) :=
        mul_le_mul_of_nonneg_left (hblk π) (Nat.cast_nonneg _)
    _ = (((blockCount π - 1).factorial : ℝ) * (blockCount π : ℝ)) * (ε * ∏ i, y i) := by
        ring
    _ ≤ ((blockCount π).factorial : ℝ) * (ε * ∏ i, y i) :=
        mul_le_mul_of_nonneg_right hfac hεy
    _ = ((blockCount π).factorial : ℝ) * ε * ∏ i, y i := by ring
theorem isBoundedRealRV_smearedEnergy
    (hVol : CenteredMomentsAndVolumeFirst.Statement)
    (D : Setting) (Λ : FixedSpacing.Setup) (ν : Measure Λ.Fields)
    [IsProbabilityMeasure ν] {n : ℕ} (f : D.SepTuples n) (i : Fin n) :
    IsBoundedRealRV
      (fun U : Λ.Fields => InfiniteLattice.smearedEnergy (f.1 i) U) := by
  have hf : ∀ i, f.1 i ∈ compactTestFunctions := hVol.2.1 D.euclideanParams ⟨n, f.1⟩ f.2
  exact ((hVol.1 Λ ν ν inferInstance inferInstance n f.1 hf).1).1 i
theorem ursellFunction_im_eq_zero (hRel : Cumulants.CumulantMomentRelations)
    (hVol : CenteredMomentsAndVolumeFirst.Statement)
    (D : Setting) (Λ : FixedSpacing.Setup) (ν : Measure Λ.Fields)
    [IsProbabilityMeasure ν] (n : ℕ) (hn : 2 ≤ n) (X : D.SepTuples n) :
    (ursellFunction ν n X.1).im = 0 := by
  have hY := isBoundedRealRV_smearedEnergy hVol D Λ ν X
  have hzero : IsBoundedRealRV (fun _ : Λ.Fields => (0 : ℝ)) :=
    ⟨measurable_const, 0, fun _ => by simp⟩
  obtain ⟨h, -⟩ := hRel Λ.Fields ν n _ hY
  exact (h n _ _ (by omega) hY hzero).1
theorem centeredMoment_eq_centred (hRel : Cumulants.CumulantMomentRelations)
    (hVol : CenteredMomentsAndVolumeFirst.Statement)
    (D : Setting) (Λ : FixedSpacing.Setup) (ν : Measure Λ.Fields)
    [IsProbabilityMeasure ν] (X : D.AllSepTuples) :
    centeredMoment ν X.1.2 = ((centred (ursellFamily D ν) X : ℝ) : ℂ) := by
  obtain ⟨⟨q, f⟩, hX⟩ := X
  have hY := isBoundedRealRV_smearedEnergy hVol D Λ ν (⟨f, hX⟩ : D.SepTuples q)
  obtain ⟨-, -, -, -, -, h, -⟩ := hRel Λ.Fields ν q _ hY
  refine h.trans ?_
  rw [centred, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun π hπ => ?_
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun I hI => ?_
  have h₁ : I.card ≠ 1 := (Finset.mem_filter.mp hπ).2 I hI
  have h₂ : 0 < I.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hI)
  have hI₂ : 2 ≤ I.card := by omega
  have him := ursellFunction_im_eq_zero hRel hVol D Λ ν I.card hI₂
    (AmbientPoints.restrictSeparated (⟨f, hX⟩ : D.SepTuples q) I)
  rw [blockFactor, dif_pos hI₂]
  refine Complex.ext ?_ ?_
  · rfl
  · rw [Complex.ofReal_im]
    exact him
theorem cumulantComparison_holds (hRel : Cumulants.CumulantMomentRelations)
    (hVol : CenteredMomentsAndVolumeFirst.Statement) : CumulantComparison := by
  refine ⟨?_, fun D Λ ν _ => ⟨fun n hn X => ursellFunction_im_eq_zero hRel hVol D Λ ν n hn X,
    fun X => centeredMoment_eq_centred hRel hVol D Λ ν X⟩⟩
  intro 𝒳 _ μ ν _ _ n Y hn hY
  obtain ⟨hLin, -, -, -, hMom, hCen, -⟩ := hRel 𝒳 ν n Y hY
  refine ⟨?_, mixedCumulant_eq_partition_sum hRel ν Y hn hY, ?_, hCen, ?_⟩
  · exact hMom
  · intro k Y' c c' hY'
    exact (hLin n Y Y' hn hY hY').2.2 k c c'
  · intro y ε hy hε hbd hnear
    exact norm_mixedCumulant_sub_le hRel μ ν Y hn hY y ε hy hε hbd hnear
end YangMills.Construction.CutoffLimits.TwoMeasures
end
