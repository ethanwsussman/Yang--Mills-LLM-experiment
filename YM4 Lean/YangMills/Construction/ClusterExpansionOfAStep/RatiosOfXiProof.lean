import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXi
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.ClusterExpansionOfAStep
open Dobrushin StepGas TorusLumps TorusFields StepSettings
variable {S : StepSetup} {n : ℕ} [NeZero n]
variable (G : GasGround S n)
theorem gasSupport_touches_insert (s : GasSupport S n) (y : TorusSite n) (A : Finset (TorusSite n)) :
    s.Touches (insert y A) ↔ s.Touches A ∨ s.Meets y := by
  unfold GasSupport.Touches GasSupport.Meets
  simp only [Finset.mem_insert]
  constructor
  · rintro (⟨b, hb, h | h⟩ | ⟨z, hz, h | h⟩)
    · exact Or.inr (Or.inl ⟨b, hb, h⟩)
    · exact Or.inl (Or.inl ⟨b, hb, h⟩)
    · exact Or.inr (Or.inr ⟨z, hz, h⟩)
    · exact Or.inl (Or.inr ⟨z, hz, h⟩)
  · rintro ((⟨b, hb, h⟩ | ⟨z, hz, h⟩) | (⟨b, hb, h⟩ | ⟨z, hz, h⟩))
    · exact Or.inl ⟨b, hb, Or.inr h⟩
    · exact Or.inr ⟨z, hz, Or.inr h⟩
    · exact Or.inl ⟨b, hb, Or.inl h⟩
    · exact Or.inr ⟨z, hz, Or.inl h⟩
theorem map_inl_dirac_unit {α : Type} [MeasurableSpace α] :
    Measure.map (Sum.inl : Unit → WithNone α) (Measure.dirac ()) = Measure.dirac (Sum.inl ()) :=
  Measure.map_dirac' measurable_inl ()
theorem measurableSet_vacant {α : Type} [MeasurableSpace α] :
    MeasurableSet ({Sum.inl ()} : Set (WithNone α)) := by
  have hrange : ({Sum.inl ()} : Set (WithNone α)) = Set.range Sum.inl := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro rfl
      exact ⟨(), rfl⟩
    · rintro ⟨u, rfl⟩
      rfl
  rw [hrange]
  exact measurableSet_range_inl
theorem dirac_vacant_restrict {α : Type} [MeasurableSpace α] :
    (Measure.dirac (Sum.inl () : WithNone α)).restrict {Sum.inl ()} = Measure.dirac (Sum.inl ()) := by
  classical
  rw [restrict_dirac' measurableSet_vacant]
  simp
theorem withNoneMeasure_restrict_vacant {α : Type} [MeasurableSpace α] (ν : Measure α) :
    (withNoneMeasure ν).restrict {Sum.inl ()} = Measure.dirac (Sum.inl ()) := by
  unfold withNoneMeasure
  rw [Measure.restrict_add, map_inl_dirac_unit, dirac_vacant_restrict]
  have hzero : (Measure.map Sum.inr ν : Measure (WithNone α)).restrict {Sum.inl ()} = 0 := by
    rw [Measure.restrict_eq_zero, Measure.map_apply measurable_inr measurableSet_vacant]
    have hpre : (Sum.inr : α → WithNone α) ⁻¹' {Sum.inl ()} = ∅ := by
      ext a
      simp
    rw [hpre, measure_empty]
  rw [hzero, add_zero]
theorem noSpinMeets_eq_pi (y : TorusSite n) : G.NoSpinMeets y =
    Set.univ.pi fun i : G.GasSpin => open Classical in if i.1.Meets y then {Sum.inl ()} else Set.univ := by
  classical
  ext ω
  simp only [GasGround.NoSpinMeets, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h i
    split_ifs with hi
    · exact h i hi
    · trivial
  · intro h i hi
    have hval := h i
    rwa [if_pos hi] at hval
theorem measurableSet_noSpinMeets (y : TorusSite n) : MeasurableSet (G.NoSpinMeets y) := by
  classical
  rw [noSpinMeets_eq_pi]
  refine MeasurableSet.univ_pi fun i => ?_
  split_ifs
  · exact measurableSet_vacant
  · exact MeasurableSet.univ
theorem pi_referenceMeasure_insert (A : Finset (TorusSite n)) (y : TorusSite n) :
    Measure.pi (G.referenceMeasure (insert y A)) =
      (Measure.pi (G.referenceMeasure A)).restrict (G.NoSpinMeets y) := by
  classical
  rw [noSpinMeets_eq_pi, Measure.restrict_pi_pi]
  congr 1
  funext i
  unfold GasGround.referenceMeasure GasGround.referenceMeasureOff
  by_cases hm : i.1.Meets y
  · rw [if_pos hm, if_pos ((gasSupport_touches_insert i.1 y A).mpr (Or.inr hm))]
    split_ifs
    · rw [map_inl_dirac_unit, dirac_vacant_restrict]
    · rw [map_inl_dirac_unit, withNoneMeasure_restrict_vacant]
  · rw [if_neg hm, Measure.restrict_univ]
    by_cases ht : i.1.Touches A
    · rw [if_pos ht, if_pos ((gasSupport_touches_insert i.1 y A).mpr (Or.inl ht))]
    · rw [if_neg ht, if_neg (fun h => ((gasSupport_touches_insert i.1 y A).mp h).elim ht hm)]
theorem partitionFunction_insert (A : Finset (TorusSite n)) (y : TorusSite n) :
    G.partitionFunction (insert y A) =
      ∫⁻ ω in G.NoSpinMeets y, G.pairConstraint.weightDensity G.weight ω
        ∂Measure.pi (G.referenceMeasure A) := by
  unfold GasGround.partitionFunction
  rw [pi_referenceMeasure_insert]
theorem pi_dirac_eq_dirac {I : Type} [Fintype I] {X : I → Type} [∀ i, MeasurableSpace (X i)]
    (a : ∀ i, X i) :
    Measure.pi (fun i => Measure.dirac (a i)) = Measure.dirac a := by
  classical
  refine Measure.pi_eq fun B hB => ?_
  have hI : ∀ i, (Measure.dirac (a i)) (B i) = (B i).indicator 1 (a i) := fun i =>
    Measure.dirac_apply' _ (hB i)
  simp_rw [hI]
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hB)]
  by_cases h : a ∈ Set.univ.pi B
  · rw [Set.indicator_of_mem h]
    simp only [Pi.one_apply]
    symm
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Set.indicator_of_mem (h i (Set.mem_univ i))]
    rfl
  · rw [Set.indicator_of_notMem h]
    obtain ⟨i, hi⟩ : ∃ i, a i ∉ B i := by simpa [Set.mem_pi] using h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Set.indicator_of_notMem hi])
section SmallColumns
variable {c : ℝ}
  (hall : ∀ off : G.GasSpin → Prop,
    ∃ h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity c),
      G.HasSmallColumns off c h)
include hall
theorem partitionFunction_pos_ne_top (A : Finset (TorusSite n)) :
    0 < G.partitionFunction A ∧ G.partitionFunction A ≠ ⊤ := by
  obtain ⟨h, hs⟩ := hall (fun j => j.1.Touches A)
  have hp := hs.isProbabilityMeasure.measure_univ
  unfold GasGround.gibbsLawOff PairConstraint.gibbsLaw at hp
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul] at hp
  change (G.partitionFunction A)⁻¹ * G.partitionFunction A = 1 at hp
  constructor
  · refine pos_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at hp
    simp at hp
  · intro h0
    rw [h0] at hp
    simp at hp
theorem coldWeight_pos : 0 < G.coldWeight := by
  obtain ⟨h, -⟩ := hall (fun _ => False)
  exact h.pos_of_admissible _ fun i j _ => Or.inl rfl
theorem xi_pos (A : Finset (TorusSite n)) : 0 < G.xi A := by
  obtain ⟨h1, h2⟩ := partitionFunction_pos_ne_top G hall A
  exact div_pos (ENNReal.toReal_pos h1.ne' h2) (coldWeight_pos G hall)
theorem gibbsLaw_real_noSpinMeets (A : Finset (TorusSite n)) (y : TorusSite n) :
    (G.gibbsLaw A).real (G.NoSpinMeets y) = G.xi (insert y A) / G.xi A := by
  obtain ⟨h1, h2⟩ := partitionFunction_pos_ne_top G hall A
  have hc := coldWeight_pos G hall
  have hz : (G.partitionFunction A).toReal ≠ 0 := (ENNReal.toReal_pos h1.ne' h2).ne'
  have h3 : (G.gibbsLaw A).real (G.NoSpinMeets y) =
      (G.partitionFunction (insert y A)).toReal / (G.partitionFunction A).toReal := by
    rw [measureReal_def]
    unfold GasGround.gibbsLaw GasGround.gibbsLawOff PairConstraint.gibbsLaw
    rw [Measure.smul_apply, withDensity_apply _ (measurableSet_noSpinMeets G y), smul_eq_mul]
    change ((G.partitionFunction A)⁻¹ * ∫⁻ ω in G.NoSpinMeets y,
      G.pairConstraint.weightDensity G.weight ω ∂Measure.pi (G.referenceMeasure A)).toReal = _
    rw [← partitionFunction_insert, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
  rw [h3]
  unfold GasGround.xi
  field_simp
theorem xi_univ : G.xi Finset.univ = 1 := by
  classical
  obtain ⟨h, -⟩ := hall (fun _ => False)
  have hc := coldWeight_pos G hall
  have ht : ∀ i : G.GasSpin, i.1.Touches Finset.univ := by
    intro i
    obtain ⟨z, hz⟩ := i.2.isCluster.1
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨b, hb, -⟩ := Finset.mem_image.mp hz
      exact Or.inl ⟨b, hb, Finset.mem_univ _⟩
    · exact Or.inr ⟨z, hz, Finset.mem_univ _⟩
  have hr : G.referenceMeasure Finset.univ = fun i => Measure.dirac (G.allVacant i) := by
    funext i
    unfold GasGround.referenceMeasure GasGround.referenceMeasureOff
    rw [if_pos (ht i), map_inl_dirac_unit]
    rfl
  have hd : G.pairConstraint.weightDensity G.weight G.allVacant = ENNReal.ofReal G.coldWeight := by
    unfold PairConstraint.weightDensity
    have hadm : G.pairConstraint.IsAdmissible G.allVacant := fun i j _ => Or.inl rfl
    rw [if_pos hadm]
    rfl
  unfold GasGround.xi GasGround.partitionFunction
  rw [hr, pi_dirac_eq_dirac, lintegral_dirac' _ h.measurable_weightDensity, hd,
    ENNReal.toReal_ofReal hc.le]
  exact div_self hc.ne'
theorem xi_insert_ratio_bounds (A : Finset (TorusSite n)) (y : TorusSite n) :
    1 - Real.exp (-(7 * c * S.coupling)) ≤ G.xi (insert y A) / G.xi A ∧
      G.xi (insert y A) / G.xi A ≤ 1 := by
  obtain ⟨h, hs⟩ := hall (fun j => j.1.Touches A)
  haveI := hs.isProbabilityMeasure
  haveI : IsProbabilityMeasure (G.gibbsLaw A) := hs.isProbabilityMeasure
  rw [← gibbsLaw_real_noSpinMeets G hall]
  have hE := measurableSet_noSpinMeets G y
  have hm := hs.abs_integral_le y ((G.NoSpinMeets y)ᶜ.indicator 1) (measurable_one.indicator hE.compl)
    (by
      intro ω
      by_cases hω : ω ∈ (G.NoSpinMeets y)ᶜ
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω])
    (fun ω hω => Set.indicator_of_notMem (by simpa using hω) _)
  have hi : ∫ ω, ((G.NoSpinMeets y)ᶜ.indicator (1 : G.Config → ℝ)) ω
      ∂G.gibbsLawOff (fun j => j.1.Touches A) = 1 - (G.gibbsLaw A).real (G.NoSpinMeets y) := by
    rw [integral_indicator_one hE.compl]
    change (G.gibbsLaw A).real _ = _
    rw [measureReal_compl hE, probReal_univ]
  rw [hi] at hm
  constructor
  · have hup := (abs_le.mp hm).2
    linarith
  · exact measureReal_le_one
end SmallColumns
theorem partitionRatioBounds : PartitionRatioBounds := by
  intro S n _ G c hall
  exact ⟨measurableSet_noSpinMeets G, xi_pos G hall, xi_univ G hall, gibbsLaw_real_noSpinMeets G hall,
    xi_insert_ratio_bounds G hall⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
