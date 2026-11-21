import YangMills.Construction.InfiniteLattice.FunctionsFixedByTheTranslations
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfOneLatticeAndTheirAction
import YangMills.Construction.InfiniteLattice.TopologyAndDensityOnTheConfigurationsOfOneLattice
import YangMills.Construction.Towers.DifferencesAndRestrictionsOfATowerAreMapsOfPeriodicFunctionsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases.ShiftFixedFunctions
variable {a : ℝ}
theorem link_ext_of_endpoints {e e' : Link a} (hs : e.initial = e'.initial)
    (ht : e.terminal = e'.terminal) : e = e' := by apply _root_.YangMills.Construction.Tower.UnitScale.CoboundaryRestrictionPeriodicity.link_ext <;> assumption
theorem pullbackField_shift_add (x y : LatticePoint a) (A : GaugeField a) :
    (shift x).pullbackField ((shift y).pullbackField A) =
      (shift (x + y)).pullbackField A := by
  refine Subtype.ext (funext fun e => ?_)
  have he : (shift y).linkMap ((shift x).linkMap e) =
      (shift (x + y)).linkMap e := by
    refine link_ext_of_endpoints (Subtype.ext ?_) (Subtype.ext ?_)
    · change ((e.initial : AmbientSpace) + x) + y =
        (e.initial : AmbientSpace) + ((x + y : LatticePoint a) : AmbientSpace)
      simp [add_assoc]
    · change ((e.terminal : AmbientSpace) + x) + y =
        (e.terminal : AmbientSpace) + ((x + y : LatticePoint a) : AmbientSpace)
      simp [add_assoc]
  change A ((shift y).linkMap ((shift x).linkMap e)) =
    A ((shift (x + y)).linkMap e)
  rw [he]
theorem pullbackField_shift_zero (A : GaugeField a) :
    (shift (0 : LatticePoint a)).pullbackField A = A := by apply _root_.YangMills.Construction.InfiniteLattice.shift_zero_pullbackField <;> assumption
theorem fixedEverywhere_invariantMeasurable (S : Setup) :
    FixedEverywhereIsInvariantMeasurable S := by
  intro f hf hfix B hB
  refine ⟨hf hB, fun x => ((shift x).actOn_indicator_eq_iff _).mpr ?_⟩
  ext A
  have h : f ((shift x).pullbackField A) = f A := hfix x A
  change f ((shift x).pullbackField A) ∈ B ↔ f A ∈ B
  rw [h]
theorem pullbackField_mem_shiftFixedSet {g : GaugeField a → ℂ} {A : GaugeField a}
    (hA : A ∈ shiftFixedSet g) (y : LatticePoint a) :
    (shift y).pullbackField A ∈ shiftFixedSet g := by
  intro x
  have h₁ : g ((shift (x + y)).pullbackField A) = g A := hA (x + y)
  have h₂ : g ((shift y).pullbackField A) = g A := hA y
  change g ((shift x).pullbackField ((shift y).pullbackField A)) =
    g ((shift y).pullbackField A)
  rw [pullbackField_shift_add, h₁, h₂]
theorem pullbackField_mem_shiftFixedSet_iff {g : GaugeField a → ℂ} (A : GaugeField a)
    (y : LatticePoint a) :
    (shift y).pullbackField A ∈ shiftFixedSet g ↔ A ∈ shiftFixedSet g := by
  refine ⟨fun h => ?_, fun h => pullbackField_mem_shiftFixedSet h y⟩
  have h' := pullbackField_mem_shiftFixedSet h (-y)
  rwa [pullbackField_shift_add, neg_add_cancel, pullbackField_shift_zero] at h'
theorem assertion_holds (hS : LatticeSymmetryAction.SymmetryActionFacts)
    (hT : TopologyDensityHolds) : Assertion := by
  intro S
  refine ⟨fixedEverywhere_invariantMeasurable S, fun μ g hg hae => ?_⟩
  have : Countable (LatticePoint S.mesh) := (hT S).countable_points
  have hmem : ∀ x : LatticePoint S.mesh, (shift x).toFun ∈ latticeMotions S.mesh := fun x => by
    rw [← (hS S).1.1]
    exact ⟨shift x, rfl⟩
  have hpb : ∀ x : LatticePoint S.mesh, Measurable (shift x).pullbackField := fun x =>
    (((hS S).2.1.1 (shift x) (shift x) (hmem x) (hmem x)).1).continuous.measurable
  have hset : MeasurableSet (shiftFixedSet g) := by
    have hEq : shiftFixedSet g =
        ⋂ x : LatticePoint S.mesh, {A | g ((shift x).pullbackField A) = g A} := by
      ext A
      simp only [Set.mem_iInter]
      rfl
    rw [hEq]
    exact MeasurableSet.iInter fun x => measurableSet_eq_fun (hg.comp (hpb x)) hg
  have hall : ∀ᵐ A ∂μ.toMeasure, A ∈ shiftFixedSet g :=
    ae_all_iff.mpr fun x => (ProbMeasure.holdsAS_iff μ _).mp (hae x)
  have hinv : ∀ y : LatticePoint S.mesh, (shift y).pullbackField ⁻¹'
      shiftFixedSet g = shiftFixedSet g := fun y => by
    ext A
    exact pullbackField_mem_shiftFixedSet_iff A y
  refine ⟨⟨hset, fun y => ((shift y).actOn_indicator_eq_iff _).mpr (hinv y)⟩,
    (mem_ae_iff_prob_eq_one hset).mp hall, ?_, ?_⟩
  · refine fixedEverywhere_invariantMeasurable S _ (hg.indicator hset) fun y A => ?_
    change (shiftFixedSet g).indicator g ((shift y).pullbackField A) =
      (shiftFixedSet g).indicator g A
    by_cases hA : A ∈ shiftFixedSet g
    · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (pullbackField_mem_shiftFixedSet hA y)]
      exact (hA y)
    · rw [Set.indicator_of_notMem hA,
        Set.indicator_of_notMem fun h => hA ((pullbackField_mem_shiftFixedSet_iff A y).mp h)]
  · refine (ProbMeasure.holdsAS_iff μ _).mpr ?_
    filter_upwards [hall] with A hA
    exact Set.indicator_of_mem hA g
end YangMills.Construction.LatticePhases.ShiftFixedFunctions
