import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.BlockItsPathsAndALogarithm
import YangMills.Construction.Lattice.SeriesLogarithmOnTheComplexGroup
import YangMills.Construction.Towers.SecondDifferentialOfAFieldIsLocalWithEntireKernelsProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlockPathsAndLogarithm
open YangMills.Construction.Matrices
open YangMills.Construction.Conventions
theorem complexGaugeGroup_mul_mem {A B : ComplexMatrix2} (hA : A ∈ complexGaugeGroup)
    (hB : B ∈ complexGaugeGroup) : A * B ∈ complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p592 <;> assumption
theorem complexGaugeGroup_inv_mem {A : ComplexMatrix2} (hA : A ∈ complexGaugeGroup) :
    A⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem complexGaugeGroup_inv_inv {A : ComplexMatrix2} (hA : A ∈ complexGaugeGroup) :
    (A⁻¹)⁻¹ = A := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
theorem compactGaugeGroup_inv_mem {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem matExp_I_smul_mem_complexGaugeGroup (hEL : ComplexMatrix2.ExpLogEstimates)
    {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldHessianEntries.matExp_mem_complexGaugeGroup <;> assumption
theorem matExp_I_smul_mem_compactGaugeGroup (hIL : ComplexMatrix2.UnitaryLogarithmProperties)
    {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ compactGaugeGroup :=
  (hIL.1 A hA).2.2.2
theorem operatorNorm_neg_one_sub_one :
    ComplexMatrix2.operatorNorm ((-1 : ComplexMatrix2) - 1) = 2 := by
  have h : (-1 : ComplexMatrix2) - 1 = (-2 : ℂ) • (1 : ComplexMatrix2) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp <;> norm_num
  rw [h]
  change ‖(-2 : ℂ) • (1 : ComplexMatrix2)‖ = 2
  rw [norm_smul, norm_one, mul_one]
  simp
theorem expLogGaugeGroupFacts_holds (hEL : ComplexMatrix2.ExpLogEstimates)
    (hIL : ComplexMatrix2.UnitaryLogarithmProperties) (hSer : LogSeriesInComplexGroupStatement) :
    ExpLogGaugeGroupFacts where
  matExp_mem_complex := fun _ hA => matExp_I_smul_mem_complexGaugeGroup hEL hA
  matExp_mem_compact := fun _ hA => matExp_I_smul_mem_compactGaugeGroup hIL hA
  logSeries_mem := by
    intro X hX hn
    refine ⟨ComplexMatrix2.traceless.smul_mem _ (hSer.1 X hX hn).2, fun hXr => ?_⟩
    obtain ⟨-, -, -, -, -, -, -, hU, -⟩ := hEL
    obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hXr
    obtain ⟨H, -, hlog, -, -, -, hdet⟩ := hU X hu hn
    obtain ⟨-, hH, -, hHl⟩ := hdet hd
    have hne : X ≠ -1 := by
      rintro rfl
      rw [operatorNorm_neg_one_sub_one] at hn
      norm_num at hn
    refine ⟨?_, ⟨hXr, hne⟩, ?_⟩
    · rw [hlog, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
      exact hH
    · rw [hlog, ComplexMatrix2.unitaryLog, hHl]
theorem conjugatedExpMemGaugeGroups_holds (hEL : ComplexMatrix2.ExpLogEstimates)
    (hIL : ComplexMatrix2.UnitaryLogarithmProperties) : ConjugatedExpMemGaugeGroups := by
  refine ⟨fun V hV Vm hVm Vp hVp A hA => ?_, fun V hV Vm hVm Vp hVp A hA => ?_⟩
  · exact complexGaugeGroup_mul_mem (complexGaugeGroup_mul_mem (complexGaugeGroup_mul_mem
      (complexGaugeGroup_mul_mem hVm (matExp_I_smul_mem_complexGaugeGroup hEL hA)) hV)
      (complexGaugeGroup_inv_mem hVp)) (complexGaugeGroup_inv_mem hV)
  · exact mul_mem (mul_mem (mul_mem (mul_mem hVm
      (matExp_I_smul_mem_compactGaugeGroup hIL hA)) hV) (compactGaugeGroup_inv_mem hVp))
      (compactGaugeGroup_inv_mem hV)
variable {L m K i : ℕ}
theorem source_ne_target (hOne : BondOrientationDichotomy)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℤ} (hj : -(m : ℤ) < j) (c : Bond L m j) :
    c.source ≠ c.target := by
  intro h
  have hx := hOne L m hL hm j hj c
  have hr : c.opposite = c := Bond.ext h.symm h
  rw [hr] at hx
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩ <;> exact b a
theorem sublattice_le_and_refinedBlock (hBlk : RefinedBlockCoordinatesHold)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hi : i < K) :
    sublattice L m (levelDepth K (i + 1)) ≤ sublattice L m (levelDepth K i) ∧
      RefinedBlockAroundCentre L m (levelDepth K (i + 1)) (levelDepth K i) 1 := by
  obtain ⟨⟨-, hF, hB, -⟩, -⟩ := (hBlk L K m ⟨rfl, rfl, rfl, hL.1, hL.2, by omega, hm, rfl⟩).2.1
    i (i + 1) (by omega) (by omega)
  have e : i + 1 - i = 1 := by omega
  rw [e] at hB
  exact ⟨hF.2.2.2.1, hB⟩
theorem blockBondContainment_of_endpoint (hBlk : RefinedBlockCoordinatesHold)
    (hOne : BondOrientationDichotomy)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hi : i < K)
    (y : SiteAtLevel L m K (i + 1)) (c : BondAtLevel L m K (i + 1))
    (hc : c.source = y ∨ c.target = y) : BlockBondContainment y c := by
  have hsub : unitBlock y ⊆ bondDoubleBlock c := by
    rcases hc with rfl | rfl
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  obtain ⟨hle, hB⟩ := sublattice_le_and_refinedBlock hBlk hL hm hi
  refine ⟨hsub, fun b hb => ⟨hsub hb.1, hsub hb.2⟩, rfl, fun z hz => ⟨hle z.2, fun hzb => ?_⟩⟩
  have hne := source_ne_target hOne hL hm (j := levelDepth K (i + 1))
    (by simp only [levelDepth]; push_cast; omega) c
  have hmem : (z : FourTorus L m) ∈ refinedBlock 1 y ∩ (sublattice L m (levelDepth K (i + 1)) :
      Set (FourTorus L m)) := ⟨hzb, z.2⟩
  rw [(hB y).2.2.2.2.2.2] at hmem
  have hzy : z = y := Subtype.ext hmem
  rcases hz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hne (h₁.trans (hzy.symm.trans h₂.symm))
  · exact hne (h₂.trans (hzy.trans h₁.symm))
theorem unitBlockPaths_holds (hSch : AveragingSchemeProperties)
    (hBlk : RefinedBlockCoordinatesHold)
    (hOne : BondOrientationDichotomy)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hi : i < K)
    (y : SiteAtLevel L m K (i + 1)) : UnitBlockPaths y := by
  have hpaths : ∀ x ∈ coarseSiteBlock y, BlockPathProperties y x :=
    fun x hx => ((hSch L hL m K i hm hi .centred).1 y x hx).1
  refine
    { center_mem := ((sublattice_le_and_refinedBlock hBlk hL hm hi).2 y).2.2.2.2.1
      endpoints_mem := fun b hb => hb
      xor_oriented := hOne L m hL hm _ (by simp only [levelDepth]; omega)
      exists_oriented_bond := ⟨Bond.forwardFrom y 0, ⟨0, by simp [Bond.forwardFrom]⟩, Or.inl rfl⟩
      oriented_bond := fun c _ hc => blockBondContainment_of_endpoint hBlk hOne hL hm hi y c hc
      comb_defined := fun x hx => (hpaths x hx).comb_in_box
      comb_subset := fun x hx b hb => (hpaths x hx).comb_within.2 b hb
      contour_subset := ?_ }
  rintro x hx _ ⟨σ, rfl⟩ b hb
  exact ((hpaths x hx).contour_within σ).2 b hb
theorem expTwist_of_oriented (a W : BondAtLevel L m K i → ComplexMatrix2)
    {b : BondAtLevel L m K i} (hb : b.IsPositivelyOriented) :
    expTwist a W b = ComplexMatrix2.matExp (Complex.I • a b) * W b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
theorem expTwist_of_not_oriented (a W : BondAtLevel L m K i → ComplexMatrix2)
    {b : BondAtLevel L m K i} (hb : ¬b.IsPositivelyOriented) :
    expTwist a W b = (ComplexMatrix2.matExp (Complex.I • a b.opposite) * W b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
theorem opposite_opposite (b : BondAtLevel L m K i) : b.opposite.opposite = b := rfl
theorem uniqueExpTwistedFieldOnBlock_holds (hEL : ComplexMatrix2.ExpLogEstimates)
    (hOne : BondOrientationDichotomy)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hi : i < K)
    (y : SiteAtLevel L m K (i + 1)) {B₀ E : Set (BondAtLevel L m K i)}
    {W₀ a : BondAtLevel L m K i → ComplexMatrix2} (h₀ : IsGaugeFieldNearBlock y B₀ W₀)
    (ha : IsLieFieldNearBlock y E a) : UniqueExpTwistedFieldOnBlock y W₀ a := by
  have hxor : ∀ b : BondAtLevel L m K i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hOne L m hL hm _ (by simp only [levelDepth]; omega)
  have hrev : ∀ b : BondAtLevel L m K i, ¬b.IsPositivelyOriented →
      b.opposite.IsPositivelyOriented := fun b hb => by
    rcases hxor b with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hb
    · exact h
  have hrev' : ∀ b : BondAtLevel L m K i, b.IsPositivelyOriented →
      ¬b.opposite.IsPositivelyOriented := fun b hb => by
    rcases hxor b with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd hb h
  have hval : ∀ b ∈ (coarseSiteBlockBonds y).bonds, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • a b) * W₀ b ∈ complexGaugeGroup := fun b hb hp =>
    complexGaugeGroup_mul_mem (matExp_I_smul_mem_complexGaugeGroup hEL (ha.2.2 b (ha.2.1 b hb hp)))
      (h₀.2.2.1 b (h₀.2.1 hb))
  have hmem : ∀ b ∈ (coarseSiteBlockBonds y).bonds, expTwist a W₀ b ∈ complexGaugeGroup := by
    intro b hb
    by_cases hp : b.IsPositivelyOriented
    · rw [expTwist_of_oriented a W₀ hp]
      exact hval b hb hp
    · rw [expTwist_of_not_oriented a W₀ hp]
      exact complexGaugeGroup_inv_mem
        (hval _ ((coarseSiteBlockBonds y).opposite_mem b hb) (hrev b hp))
  refine ⟨(coarseSiteBlockBonds y).opposite_mem, ⟨expTwist a W₀, ⟨hmem, ?_⟩, ?_⟩, ?_⟩
  · intro b hb
    by_cases hp : b.IsPositivelyOriented
    · rw [expTwist_of_not_oriented a W₀ (hrev' b hp), opposite_opposite,
        expTwist_of_oriented a W₀ hp]
    · rw [expTwist_of_oriented a W₀ (hrev b hp), expTwist_of_not_oriented a W₀ hp,
        complexGaugeGroup_inv_inv (hval _ ((coarseSiteBlockBonds y).opposite_mem b hb) (hrev b hp))]
  · exact fun b _ hp => expTwist_of_oriented a W₀ hp
  · intro W W' hW hW' b hb
    by_cases hp : b.IsPositivelyOriented
    · rw [hW.2 b hb hp, hW'.2 b hb hp]
    · have hb' := (coarseSiteBlockBonds y).opposite_mem b hb
      have e : W b.opposite = W' b.opposite := by
        rw [hW.2 _ hb' (hrev b hp), hW'.2 _ hb' (hrev b hp)]
      have h₁ := hW.1.2 _ hb'
      have h₂ := hW'.1.2 _ hb'
      rw [opposite_opposite] at h₁ h₂
      rw [h₁, h₂, e]
theorem unitBlockPathsAndLogarithm_holds (hSch : AveragingSchemeProperties)
    (hBlk : RefinedBlockCoordinatesHold)
    (hOne : BondOrientationDichotomy)
    (hEL : ComplexMatrix2.ExpLogEstimates) (hIL : ComplexMatrix2.UnitaryLogarithmProperties)
    (hSer : LogSeriesInComplexGroupStatement) : UnitBlockPathsAndLogarithm :=
  ⟨fun _ hL _ _ _ hm hi y => unitBlockPaths_holds hSch hBlk hOne hL hm hi y,
    expLogGaugeGroupFacts_holds hEL hIL hSer,
    fun _ hL _ _ _ hm hi y _ _ _ _ h₀ ha =>
      uniqueExpTwistedFieldOnBlock_holds hEL hOne hL hm hi y h₀ ha,
    conjugatedExpMemGaugeGroups_holds hEL hIL⟩
end YangMills.Construction.PeriodicLattice.BlockPathsAndLogarithm
