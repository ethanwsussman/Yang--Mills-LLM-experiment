import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSet
import YangMills.Construction.Lattice.AveragingMapIsABorelMap
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.PositiveOneOfABondAndItsReverse
import YangMills.Construction.Lattice.ThreeAveragingCaseSetsAreBorel
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
import Mathlib
open MeasureTheory Set YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace BlockAverageBorel
variable {L m K k : ℕ}
private theorem inv_eq_conjTranspose_of_mem {V : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) : V⁻¹ = V.conjTranspose := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_eq_conjTranspose_of_mem_specialUnitary <;> assumption
private theorem inv_mem_specialUnitary {V : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) : V⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem inv_inv_of_mem {V : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) : V⁻¹⁻¹ = V :=
  Matrix.nonsing_inv_nonsing_inv V (by
    rw [(Matrix.mem_specialUnitaryGroup_iff.1 hV).2]; exact isUnit_one)
abbrev _root_.YangMills.SharedProofs.p318 := @inv_inv_of_mem
private theorem pathHolonomy_mem {j : ℤ} {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (Γ : List (Bond L m j)) :
    pathHolonomy U Γ ∈ ComplexMatrix2.specialUnitary := by
  have hU' : IsGaugeField compactGaugeGroup univ U := hU
  refine Submonoid.list_prod_mem _ fun X hX => ?_
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hX
  exact hU'.1 b (mem_univ b)
abbrev _root_.YangMills.SharedProofs.p3102 := @pathHolonomy_mem
private def IsIMulSkew (M : ComplexMatrix2) : Prop :=
  ∃ Y ∈ ComplexMatrix2.hermitianTraceless, M = Complex.I • Y
private theorem isIMulSkew_zero : IsIMulSkew 0 :=
  ⟨0, ComplexMatrix2.hermitianTraceless.zero_mem, by simp⟩
private theorem isIMulSkew_add (A B : ComplexMatrix2) (hA : IsIMulSkew A) (hB : IsIMulSkew B) :
    IsIMulSkew (A + B) := by
  obtain ⟨Y, hY, rfl⟩ := hA
  obtain ⟨Z, hZ, rfl⟩ := hB
  exact ⟨Y + Z, ComplexMatrix2.hermitianTraceless.add_mem hY hZ, (smul_add _ _ _).symm⟩
private theorem isIMulSkew_real_smul (r : ℝ) {A : ComplexMatrix2} (hA : IsIMulSkew A) :
    IsIMulSkew ((r : ℂ) • A) := by
  obtain ⟨Y, hY, rfl⟩ := hA
  refine ⟨r • Y, ComplexMatrix2.hermitianTraceless.smul_mem r hY, ?_⟩
  ext i j
  simp [mul_left_comm]
private theorem isIMulSkew_sum {ι : Type*} (s : Finset ι) (f : ι → ComplexMatrix2)
    (h : ∀ i ∈ s, IsIMulSkew (f i)) : IsIMulSkew (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsIMulSkew isIMulSkew_add isIMulSkew_zero h
private theorem matExp_mem (hlog : ComplexMatrix2.UnitaryLogarithmProperties) {A : ComplexMatrix2}
    (hA : IsIMulSkew A) : ComplexMatrix2.matExp A ∈ ComplexMatrix2.specialUnitary := by
  obtain ⟨Y, hY, rfl⟩ := hA
  exact (hlog.1 Y hY).2.2.2
private theorem meanContourHolonomy_mem {j j' : ℤ} {U : Bond L m j' → ComplexMatrix2}
    {y : Site L m j} {x : Site L m j'} (h : HasContourMean U y x) :
    meanContourHolonomy U y x ∈ ComplexMatrix2.specialUnitary := by
  obtain ⟨W, hW, _⟩ := h
  exact (Classical.epsilon_spec
    (p := ComplexMatrix2.IsLogMean compactGaugeGroup (contourHolonomies U y x)) ⟨W, hW⟩).1
private theorem blockAverageOnPositive_mem (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hexp : ComplexMatrix2.ExpLogEstimates) (ω : ℝ) {c : BondAtLevel L m K (k + 1)}
    (hcross : AxialPathsSpanDoubleBlock c) {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ gaugeFieldsAtLevel L m K k) :
    blockAverageOnPositive ω U c ∈ ComplexMatrix2.specialUnitary := by
  obtain ⟨-, -, -, -, -, -, -, hunit, -, -⟩ := hexp
  have hT : parallelTransport U c ∈ ComplexMatrix2.specialUnitary := pathHolonomy_mem hU _
  unfold blockAverageOnPositive
  split_ifs with hA hB
  · obtain ⟨-, ht, hh, hnorm⟩ := hA
    unfold regularAverageValue inverseFourthPowerWeight
    refine mul_mem (matExp_mem hlog (isIMulSkew_real_smul _ (finsum_mem_induction IsIMulSkew
      isIMulSkew_zero isIMulSkew_add fun x hx => ?_))) hT
    have hW : crossingDefect U c x ∈ ComplexMatrix2.specialUnitary :=
      mul_mem (mul_mem (mul_mem (meanContourHolonomy_mem (ht x hx)) (pathHolonomy_mem hU _))
        (inv_mem_specialUnitary (meanContourHolonomy_mem (hh _ (hcross.1 x hx).1))))
        (inv_mem_specialUnitary hT)
    have hW' := Matrix.mem_specialUnitaryGroup_iff.1 hW
    obtain ⟨H, -, -, -, -, -, hdet⟩ := hunit _ hW'.1 (hnorm x hx)
    exact (hdet hW'.2).2.2.1
  · unfold logAverageValue inverseFourthPowerWeight
    refine mul_mem (matExp_mem hlog (isIMulSkew_real_smul _ (finsum_mem_induction IsIMulSkew
      isIMulSkew_zero isIMulSkew_add fun x hx => ?_))) hT
    refine isIMulSkew_real_smul _ (isIMulSkew_sum _ _ fun σ _ => ?_)
    refine isIMulSkew_real_smul _ (isIMulSkew_sum _ _ fun σ' _ => ?_)
    have hY : contourCrossingDefect U c x σ σ' ∈ ComplexMatrix2.specialUnitary :=
      mul_mem (mul_mem (mul_mem (pathHolonomy_mem hU _) (pathHolonomy_mem hU _))
        (inv_mem_specialUnitary (pathHolonomy_mem hU _))) (inv_mem_specialUnitary hT)
    exact (hlog.2.2.2.2.1 _ ⟨hY, hB x hx σ σ'⟩).2.2.2
  · exact hT
private theorem blockAverage_of_positive (ω : ℝ) (U : BondAtLevel L m K k → ComplexMatrix2)
    {c : BondAtLevel L m K (k + 1)} (h : c.IsPositivelyOriented) :
    blockAverage ω U c = blockAverageOnPositive ω U c := by
  simp only [blockAverage, if_pos h]
private theorem blockAverage_of_not_positive (ω : ℝ) (U : BondAtLevel L m K k → ComplexMatrix2)
    {c : BondAtLevel L m K (k + 1)} (h : ¬c.IsPositivelyOriented) :
    blockAverage ω U c = (blockAverageOnPositive ω U c.opposite)⁻¹ := by
  simp only [blockAverage, if_neg h]
private theorem opposite_opposite {j : ℤ} (b : Bond L m j) : b.opposite.opposite = b := rfl
private theorem mapsTo_gaugeFieldsAtLevel (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hexp : ComplexMatrix2.ExpLogEstimates) (ω : ℝ)
    (hpos : ∀ c : BondAtLevel L m K (k + 1),
      Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented)
    (hcross : ∀ c : BondAtLevel L m K (k + 1), AxialPathsSpanDoubleBlock c) :
    MapsTo (blockAverageStep (L := L) (m := m) (K := K) ω k) (gaugeFieldsAtLevel L m K k)
      (gaugeFieldsAtLevel L m K (k + 1)) := by
  intro U hU
  have hmem := fun c : BondAtLevel L m K (k + 1) =>
    blockAverageOnPositive_mem hlog hexp ω (hcross c) hU
  have hconf : IsGaugeField compactGaugeGroup univ
      (blockAverageStep (L := L) (m := m) (K := K) ω k U) := by
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · change blockAverage ω U b ∈ ComplexMatrix2.specialUnitary
      rcases hpos b with ⟨hb, -⟩ | ⟨hb, hb'⟩
      · rw [blockAverage_of_positive ω U hb]
        exact hmem b
      · rw [blockAverage_of_not_positive ω U hb']
        exact inv_mem_specialUnitary (hmem _)
    · change blockAverage ω U b.opposite = (blockAverage ω U b)⁻¹
      rcases hpos b with ⟨hb, hb'⟩ | ⟨hb, hb'⟩
      · rw [blockAverage_of_positive ω U hb, blockAverage_of_not_positive ω U hb',
          opposite_opposite]
      · rw [blockAverage_of_positive ω U hb, blockAverage_of_not_positive ω U hb',
          inv_inv_of_mem (hmem _)]
  exact hconf
private theorem measurable_blockAverage_at {ω : ℝ} {c : BondAtLevel L m K (k + 1)}
    (hB : CaseSetsMeasurable ω k c) (hC : BlockAverageContinuousOnCaseSets ω k c) :
    @Measurable (gaugeFieldsAtLevel L m K k) ComplexMatrix2 (borel _) (borel ComplexMatrix2)
      fun U => blockAverage ω U.1 c := by
  let _ : MeasurableSpace (gaugeFieldsAtLevel L m K k) := borel _
  have _ : BorelSpace (gaugeFieldsAtLevel L m K k) := ⟨rfl⟩
  let _ : MeasurableSpace ComplexMatrix2 := borel ComplexMatrix2
  have _ : BorelSpace ComplexMatrix2 := ⟨rfl⟩
  set g : gaugeFieldsAtLevel L m K k → ComplexMatrix2 := fun U => blockAverage ω U.1 c with hg
  set E : BlockAverageCase → Set (gaugeFieldsAtLevel L m K k) :=
    fun κ => (↑) ⁻¹' caseSet ω k c κ with hE
  refine measurable_of_isOpen fun O hO => ?_
  have piece : ∀ κ, MeasurableSet (g ⁻¹' O ∩ E κ) := fun κ => by
    have hcont : ContinuousOn g (E κ) :=
      (hC κ).comp continuous_subtype_val.continuousOn fun U hU => hU
    obtain ⟨u, hu, he⟩ := continuousOn_iff'.1 hcont O hO
    rw [he]
    exact hu.measurableSet.inter (hB κ).2
  have cover : g ⁻¹' O = (g ⁻¹' O ∩ E .logarithmOfMeans) ∪
      (g ⁻¹' O ∩ E .intrinsicLogarithmOfDefects) ∪ (g ⁻¹' O ∩ E .alongBond) := by
    ext U
    have hmem : ∀ κ, U ∈ E κ ↔ blockAverageCase ω U.1 c = κ :=
      fun κ => ⟨And.right, fun h => ⟨U.2, h⟩⟩
    simp only [mem_union, mem_inter_iff, hmem]
    cases blockAverageCase ω U.1 c <;> simp
  rw [cover]
  exact ((piece _).union (piece _)).union (piece _)
theorem blockAverage_isBorelMap (hBorel : CaseSetsMeasurableStatement)
    (hCont : BlockAverageContinuousOnEachCaseSet)
    (hlog : ComplexMatrix2.UnitaryLogarithmProperties) (hexp : ComplexMatrix2.ExpLogEstimates)
    (hreverse : PositiveOrientationOfBondAndOpposite)
    (hblock : DoubleBlockStructure.Statement) :
    BlockAverageIsBorelMap := by
  intro s k hk
  have hpos : ∀ c : BondAtLevel s.L s.m s.K (k + 1),
      Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented :=
    fun c => (hreverse s.L s.m s.K s.isAdmissible s.m.pos s.K.pos k hk c).2.1
  have hcross : ∀ c : BondAtLevel s.L s.m s.K (k + 1), AxialPathsSpanDoubleBlock c :=
    fun c => (hblock s.L s.m s.K k s.isAdmissible s.m.pos hk c).2.2.1
  have hmaps := mapsTo_gaugeFieldsAtLevel hlog hexp (Averaging.smoothingRadius s.L) hpos hcross
  refine ⟨hmaps, ?_⟩
  unfold Kernels.IsBorelMeasurable
  let _ : MeasurableSpace (gaugeFieldsAtLevel s.L s.m s.K k) := borel _
  have _ : BorelSpace (gaugeFieldsAtLevel s.L s.m s.K k) := ⟨rfl⟩
  let _ : MeasurableSpace ComplexMatrix2 := borel ComplexMatrix2
  have _ : BorelSpace ComplexMatrix2 := ⟨rfl⟩
  have _ : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hY : borel (gaugeFieldsAtLevel s.L s.m s.K (k + 1)) = Subtype.instMeasurableSpace :=
    (BorelSpace.measurable_eq
      (α := gaugeFieldsAtLevel s.L s.m s.K (k + 1))).symm
  rw [hY]
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun b => ?_)
  rcases hpos b with ⟨hb, -⟩ | ⟨hb, hb'⟩
  · exact measurable_blockAverage_at (hBorel s k hk b hb) (hCont s k hk b hb)
  · have hm := measurable_blockAverage_at (hBorel s k hk _ hb) (hCont s k hk _ hb)
    have hstar : Measurable fun X : ComplexMatrix2 => X.conjTranspose :=
      (continuous_id.matrix_conjTranspose).measurable
    have heq : (fun U : gaugeFieldsAtLevel s.L s.m s.K k =>
        blockAverageStep (Averaging.smoothingRadius s.L) k U.1 b) =
        fun U => (blockAverage (Averaging.smoothingRadius s.L) U.1 b.opposite).conjTranspose := by
      funext U
      change blockAverage (Averaging.smoothingRadius s.L) U.1 b = _
      rw [blockAverage_of_not_positive _ _ hb', blockAverage_of_positive _ _ hb,
        inv_eq_conjTranspose_of_mem (blockAverageOnPositive_mem hlog hexp _ (hcross _) U.2)]
    exact heq ▸ hstar.comp hm
end BlockAverageBorel
end PeriodicLattice
end YangMills.Construction
end
