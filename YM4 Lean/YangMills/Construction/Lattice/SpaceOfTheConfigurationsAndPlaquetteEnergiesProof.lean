import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquetteProof
import YangMills.Construction.Lattice.CountingSitesBondsPlaquettes
import YangMills.Construction.Lattice.LatticesCubesOfAStandardPartitionAndEnlargements
import YangMills.Construction.Lattice.SpaceOfTheConfigurationsAndPlaquetteEnergies
import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALattice
import YangMills.Construction.SourcesOnAFlow.MeanInAPeriodicExtensionProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.CutoffData.ConfigSpace
instance instSecondCountableComplexMatrix2 : SecondCountableTopology ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
instance instSecondCountableSpecialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary :=
  Topology.IsInducing.subtypeVal.secondCountableTopology
section General
variable {L m : ℕ} {j : ℤ}
theorem opposite_opposite (b : PeriodicLattice.Bond L m j) : b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem inv_eq_star_of_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ = star g := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.inv_eq_star_of_mem_specialUnitary <;> assumption
theorem star_mem_specialUnitary {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    star g ∈ ComplexMatrix2.specialUnitary :=
  ((⟨g, hg⟩ : ComplexMatrix2.specialUnitary)⁻¹).2
theorem gaugeFieldOfPositive_apply_pos
    (v : PeriodicLattice.PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    (b : PeriodicLattice.Bond L m j) (h : b.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = (v ⟨b, h⟩ : ComplexMatrix2) := by
  rw [gaugeFieldOfPositive, dif_pos h]
theorem gaugeFieldOfPositive_apply_opposite
    (v : PeriodicLattice.PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    (b : PeriodicLattice.Bond L m j) (h : ¬ b.IsPositivelyOriented)
    (h' : b.opposite.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = star (v ⟨b.opposite, h'⟩ : ComplexMatrix2) := by
  rw [gaugeFieldOfPositive, dif_neg h, dif_pos h', inv_eq_star_of_mem (v _).2]
theorem gaugeFieldOfPositive_injective :
    Function.Injective (gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → _) := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.injective_gaugeFieldOfPositive <;> assumption
theorem continuous_pathHolonomy (Γ : List (PeriodicLattice.Bond L m j)) :
    Continuous fun U : PeriodicLattice.Bond L m j → ComplexMatrix2 => pathHolonomy U Γ := by apply _root_.YangMills.Construction.PeriodicExtension.continuous_pathHolonomy <;> assumption
theorem pathHolonomy_mem {U : PeriodicLattice.Bond L m j → ComplexMatrix2}
    (hU : ∀ b, U b ∈ ComplexMatrix2.specialUnitary)
    (Γ : List (PeriodicLattice.Bond L m j)) : pathHolonomy U Γ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.PeriodicLattice.CoarsePlaquetteGauge.pathHolonomy_mem <;> assumption
theorem continuous_plaquetteEnergy (p : PeriodicLattice.Plaquette L m j) :
    Continuous fun U : PeriodicLattice.Bond L m j → ComplexMatrix2 => plaquetteEnergy U p := by
  unfold plaquetteEnergy plaquetteHolonomy
  exact continuous_const.sub
    (continuous_const.mul (Continuous.matrix_trace (continuous_pathHolonomy _)))
theorem plaquetteEnergy_eq_real_mem_Icc (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    {U : PeriodicLattice.Bond L m j → ComplexMatrix2}
    (hU : ∀ b, U b ∈ ComplexMatrix2.specialUnitary) (p : PeriodicLattice.Plaquette L m j) :
    ∃ r ∈ Icc (0 : ℝ) 2, plaquetteEnergy U p = (r : ℂ) := by
  obtain ⟨⟨t, ht, he⟩, -⟩ := hlog.2.1 _ (pathHolonomy_mem hU p.boundaryBonds)
  refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
  have h : plaquetteEnergy U p = 1 - ComplexMatrix2.halfTrace (pathHolonomy U p.boundaryBonds) :=
    rfl
  rw [h, he]
  push_cast
  rfl
end General
variable (d : CutoffData)
theorem finite_bond_and_plaquette (h : CubePartitions.CubePartitionFacts) :
    Finite d.Bond ∧ Finite d.Plaquette := by
  have hi : -(((d.m : ℕ)) : ℤ) ≤ (d.cutoff : ℤ) := by
    have := d.m.pos
    omega
  have hc := (h ⟨d.L, d.isAdmissible, 1, d.m⟩ (d.cutoff : ℤ) hi 1 (Or.inl rfl)).1
  exact ⟨hc.2.2.1, hc.2.2.2.1⟩
theorem xor_pos_opposite (h : CovariantAdjoints.CovariantAdjointsStatement)
    (b : d.Bond) : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  have hi : -(((d.m : ℕ)) : ℤ) < (d.cutoff : ℤ) := by
    have := d.m.pos
    omega
  have h₁ := (h d.L d.m 1 0 d.isAdmissible.1 d.isAdmissible.2 d.m.pos
    one_pos (Nat.zero_le _)).1 (d.cutoff : ℤ) hi _ rfl
  exact h₁.1.2.2.1 b
variable {d}
theorem isProbabilityMeasure_gaugeFieldHaar :
    IsProbabilityMeasure (gaugeFieldHaar d.L d.m (d.cutoff : ℤ)) := by
  unfold gaugeFieldHaar ComplexMatrix2.haarPi
  infer_instance
section Bonds
variable (hx : ∀ b : d.Bond, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
include hx
theorem opposite_pos_of_not_pos {b : d.Bond} (h : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  rcases hx b with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · exact absurd h₁ h
  · exact h₁
theorem not_opposite_pos {b : d.Bond} (h : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  rcases hx b with ⟨-, h₁⟩ | ⟨-, h₁⟩
  · exact h₁
  · exact absurd h h₁
theorem gaugeFieldOfPositive_mem (v : d.PosBond → ComplexMatrix2.specialUnitary) :
    gaugeFieldOfPositive v ∈ compactGaugeFields d.L d.m (d.cutoff : ℤ) := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [gaugeFieldOfPositive_apply_pos v b h]
      exact (v _).2
    · rw [gaugeFieldOfPositive_apply_opposite v b h (opposite_pos_of_not_pos hx h)]
      exact star_mem_specialUnitary (v _).2
  · by_cases h : b.IsPositivelyOriented
    · have hr := not_opposite_pos hx h
      have hrr : b.opposite.opposite.IsPositivelyOriented := by rwa [opposite_opposite]
      have e : (⟨b.opposite.opposite, hrr⟩ : d.PosBond) = ⟨b, h⟩ :=
        Subtype.ext (opposite_opposite b)
      rw [gaugeFieldOfPositive_apply_opposite v b.opposite hr hrr, e,
        gaugeFieldOfPositive_apply_pos v b h, inv_eq_star_of_mem (v _).2]
    · have hr := opposite_pos_of_not_pos hx h
      rw [gaugeFieldOfPositive_apply_pos v b.opposite hr,
        gaugeFieldOfPositive_apply_opposite v b h hr,
        inv_eq_star_of_mem (star_mem_specialUnitary (v _).2), star_star]
theorem restrictPositive_bijective : Function.Bijective d.restrictPositive := by
  constructor
  · intro U V h
    apply Subtype.ext
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact congrArg Subtype.val (congrFun h ⟨b, hb⟩)
    · have hr := opposite_pos_of_not_pos hx hb
      have e : U.1 b.opposite = V.1 b.opposite :=
        congrArg Subtype.val (congrFun h ⟨b.opposite, hr⟩)
      have hU := U.2.2 b.opposite (mem_univ _)
      have hV := V.2.2 b.opposite (mem_univ _)
      rw [opposite_opposite] at hU hV
      rw [hU, hV, e]
  · intro v
    refine ⟨⟨gaugeFieldOfPositive v, gaugeFieldOfPositive_mem hx v⟩, ?_⟩
    funext b
    apply Subtype.ext
    exact gaugeFieldOfPositive_apply_pos v b.1 b.2
theorem continuous_gaugeFieldOfPositive :
    Continuous (gaugeFieldOfPositive :
      (d.PosBond → ComplexMatrix2.specialUnitary) → d.Bond → ComplexMatrix2) := by
  refine continuous_pi fun b => ?_
  by_cases h : b.IsPositivelyOriented
  · have e : (fun v : d.PosBond → ComplexMatrix2.specialUnitary => gaugeFieldOfPositive v b) =
        fun v => (v ⟨b, h⟩ : ComplexMatrix2) :=
      funext fun v => gaugeFieldOfPositive_apply_pos v b h
    rw [e]
    exact continuous_subtype_val.comp (continuous_apply _)
  · have hr := opposite_pos_of_not_pos hx h
    have e : (fun v : d.PosBond → ComplexMatrix2.specialUnitary => gaugeFieldOfPositive v b) =
        fun v => star (v ⟨b.opposite, hr⟩ : ComplexMatrix2) :=
      funext fun v => gaugeFieldOfPositive_apply_opposite v b h hr
    rw [e]
    exact Continuous.matrix_conjTranspose (continuous_subtype_val.comp (continuous_apply _))
theorem val_eq_gaugeFieldOfPositive_comp :
    (fun U : d.GaugeField => U.1) = gaugeFieldOfPositive ∘ d.restrictPositive := by
  funext U b
  by_cases h : b.IsPositivelyOriented
  · exact (gaugeFieldOfPositive_apply_pos (d.restrictPositive U) b h).symm
  · have hr := opposite_pos_of_not_pos hx h
    have hU := U.2.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at hU
    rw [Function.comp_apply, gaugeFieldOfPositive_apply_opposite _ b h hr, hU]
    exact inv_eq_star_of_mem (U.2.1 _ (mem_univ _))
theorem continuous_gaugeField_val : Continuous fun U : d.GaugeField => U.1 := by
  rw [val_eq_gaugeFieldOfPositive_comp hx]
  exact (continuous_gaugeFieldOfPositive hx).comp continuous_induced_dom
theorem measurableEmbedding_gaugeFieldOfPositive :
    MeasurableEmbedding
      (gaugeFieldOfPositive :
        (d.PosBond → ComplexMatrix2.specialUnitary) → d.Bond → ComplexMatrix2) :=
  ((continuous_gaugeFieldOfPositive hx).isClosedEmbedding
    gaugeFieldOfPositive_injective).measurableEmbedding
def restrictPositiveHomeomorph : d.GaugeField ≃ₜ (d.PosBond → ComplexMatrix2.specialUnitary) :=
  (Topology.IsEmbedding.toHomeomorphOfSurjective
    ⟨⟨rfl⟩, (restrictPositive_bijective hx).1⟩ (restrictPositive_bijective hx).2)
theorem measurableEmbedding_gaugeField_val :
    MeasurableEmbedding fun U : d.GaugeField => U.1 := by
  rw [val_eq_gaugeFieldOfPositive_comp hx]
  exact (measurableEmbedding_gaugeFieldOfPositive hx).comp
    (restrictPositiveHomeomorph hx).toMeasurableEquiv.measurableEmbedding
theorem isProbabilityMeasure_haar : IsProbabilityMeasure d.haar := by
  have := isProbabilityMeasure_gaugeFieldHaar (d := d)
  exact Measure.isProbabilityMeasure_map
    (measurableEmbedding_gaugeFieldOfPositive hx).measurable.aemeasurable
theorem isProbabilityMeasure_haarOnGaugeFields :
    IsProbabilityMeasure d.haarOnGaugeFields := by
  have := isProbabilityMeasure_gaugeFieldHaar (d := d)
  have hv := measurableEmbedding_gaugeField_val hx
  have hc := measurableEmbedding_gaugeFieldOfPositive hx
  constructor
  rw [haarOnGaugeFields, hv.comap_apply, image_univ]
  show (Measure.map gaugeFieldOfPositive (gaugeFieldHaar d.L d.m (d.cutoff : ℤ))) _ = 1
  rw [Measure.map_apply hc.measurable hv.measurableSet_range]
  have e : gaugeFieldOfPositive ⁻¹' (range fun U : d.GaugeField => U.1) = univ :=
    eq_univ_of_forall fun v => ⟨⟨gaugeFieldOfPositive v, gaugeFieldOfPositive_mem hx v⟩, rfl⟩
  rw [e, measure_univ]
end Bonds
theorem finiteBondsAndCoordinates (hB : Finite d.Bond) (hP : Finite d.Plaquette)
    (hx : ∀ b : d.Bond, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    FiniteBondsAndCoordinates d := by
  refine ⟨inferInstance, ?_, hP, ⟨⟨0, 0, 1, by decide⟩⟩, fun b => ?_,
    restrictPositive_bijective hx⟩
  · exact ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
  · by_cases h : b.IsPositivelyOriented
    · refine Or.inl ⟨h, ?_⟩
      rintro ⟨b', rfl, -⟩
      exact not_opposite_pos hx b'.2 h
    · refine Or.inr ⟨⟨⟨b.opposite, opposite_pos_of_not_pos hx h⟩, opposite_opposite b, ?_⟩, h⟩
      intro y hy
      apply Subtype.ext
      show y.1 = b.opposite
      rw [← hy, opposite_opposite]
theorem topologyAndHaar (hB : Finite d.Bond)
    (hx : ∀ b : d.Bond, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    TopologyAndHaar d := by
  have : Fintype d.PosBond := Fintype.ofFinite _
  have hemb : Topology.IsEmbedding d.restrictPositive :=
    ⟨⟨rfl⟩, (restrictPositive_bijective hx).1⟩
  have : SecondCountableTopology d.GaugeField :=
    hemb.isInducing.secondCountableTopology
  refine ⟨inferInstance, hemb.metrizableSpace, isProbabilityMeasure_haarOnGaugeFields hx,
    isProbabilityMeasure_haar hx, fun b => ?_⟩
  exact ((continuous_apply b).comp (continuous_gaugeField_val hx)).subtype_mk _
theorem weightedEnergyBounds (hP : Finite d.Plaquette)
    (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hx : ∀ b : d.Bond, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (w : d.Plaquette → ℂ) :
    WeightedEnergyBounds d (plaquetteWeightedEnergy w) w := by
  have : Fintype d.Plaquette := Fintype.ofFinite _
  have := isProbabilityMeasure_haarOnGaugeFields hx
  have := isProbabilityMeasure_gaugeFieldHaar (d := d)
  have hsum : ∀ U : d.Bond → ComplexMatrix2,
      plaquetteWeightedEnergy w U = ∑ p, w p * plaquetteEnergy U p :=
    fun U => finsum_eq_sum_of_fintype _
  have hw : ∑ᶠ p : d.Plaquette, ‖w p‖ = ∑ p, ‖w p‖ := finsum_eq_sum_of_fintype _
  have hall : Continuous (plaquetteWeightedEnergy w : (d.Bond → ComplexMatrix2) → ℂ) := by
    rw [show (plaquetteWeightedEnergy w : (d.Bond → ComplexMatrix2) → ℂ) = fun U =>
      ∑ p, w p * plaquetteEnergy U p from funext hsum]
    exact continuous_finset_sum _ fun p _ =>
      continuous_const.mul (continuous_plaquetteEnergy p)
  have hcont : Continuous fun U : d.GaugeField => plaquetteWeightedEnergy w U.1 :=
    hall.comp (continuous_gaugeField_val hx)
  have hmem : ∀ (U : d.GaugeField) (b : d.Bond), U.1 b ∈ ComplexMatrix2.specialUnitary :=
    fun U b => U.2.1 b (mem_univ b)
  have hnorm : ∀ U : d.GaugeField, ‖plaquetteWeightedEnergy w U.1‖ ≤ 2 * ∑ p, ‖w p‖ := by
    intro U
    rw [hsum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    obtain ⟨r, hr, he⟩ := plaquetteEnergy_eq_real_mem_Icc hlog (hmem U) p
    rw [norm_mul, he, Complex.norm_real, Real.norm_of_nonneg hr.1, mul_comm]
    exact mul_le_mul_of_nonneg_right hr.2 (norm_nonneg _)
  have hexp : ∀ U : d.GaugeField,
      ‖Complex.exp (-plaquetteWeightedEnergy w U.1)‖ ≤ Real.exp (2 * ∑ p, ‖w p‖) := by
    intro U
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_neg]
    exact hnorm U
  have hexpc : Continuous fun U : d.GaugeField =>
      Complex.exp (-plaquetteWeightedEnergy w U.1) := hcont.neg.cexp
  have hexpall : Continuous fun U : d.Bond → ComplexMatrix2 =>
      Complex.exp (-plaquetteWeightedEnergy w U) := hall.neg.cexp
  refine ⟨hcont, ?_, ?_, ?_, hexpc, ⟨_, hexp⟩, ?_, ?_⟩
  · intro hre U
    rw [hsum, Complex.im_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    obtain ⟨r, -, he⟩ := plaquetteEnergy_eq_real_mem_Icc hlog (hmem U) p
    rw [he, Complex.mul_im, hre p]
    simp
  · rw [hw]
    exact hnorm
  · rw [hw]
    exact hexp
  · exact Integrable.of_bound hexpc.aestronglyMeasurable _ (Filter.Eventually.of_forall hexp)
  · show Integrable _ (Measure.map gaugeFieldOfPositive _)
    rw [(measurableEmbedding_gaugeFieldOfPositive hx).integrable_map_iff]
    refine Integrable.of_bound
      (hexpall.comp (continuous_gaugeFieldOfPositive hx)).aestronglyMeasurable
      (Real.exp (2 * ∑ p, ‖w p‖)) (Filter.Eventually.of_forall fun v => ?_)
    exact hexp ⟨gaugeFieldOfPositive v, gaugeFieldOfPositive_mem hx v⟩
theorem plaquetteTermBounds (hP : Finite d.Plaquette)
    (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hx : ∀ b : d.Bond, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    PlaquetteTermBounds d := by
  refine ⟨fun p => ⟨(continuous_plaquetteEnergy p).comp (continuous_gaugeField_val hx),
    fun U => ?_⟩,
    fun c => weightedEnergyBounds hP hlog hx c,
    fun c => weightedEnergyBounds hP hlog hx fun p => c p.barycenter⟩
  exact plaquetteEnergy_eq_real_mem_Icc hlog (fun b => U.2.1 b (mem_univ b)) p
theorem basicStructure_holds (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hcounts : CubePartitions.CubePartitionFacts)
    (htranspose : CovariantAdjoints.CovariantAdjointsStatement) : BasicStructure := by
  intro d
  obtain ⟨hB, hP⟩ := finite_bond_and_plaquette d hcounts
  have hx := xor_pos_opposite d htranspose
  exact ⟨finiteBondsAndCoordinates hB hP hx, topologyAndHaar hB hx,
    plaquetteTermBounds hP hlog hx⟩
end PeriodicLattice.CutoffData.ConfigSpace
end YangMills.Construction
