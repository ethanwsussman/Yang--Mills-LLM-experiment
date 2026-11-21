import YangMills.Construction.InfiniteLattice.WeakLimitPointsAlongSides
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
theorem shift_pullbackField_add (v w : LatticePoint a) (U : GaugeField a) :
    (shift (v + w)).pullbackField U =
      (shift w).pullbackField ((shift v).pullbackField U) := by
  refine Subtype.ext (funext fun b => congrArg U.1 ?_)
  apply Link.ext <;> refine Subtype.ext ?_ <;>
    simp only [LatticeSymmetry.linkMap, LatticeSymmetry.pointMap, shift, AddSubgroup.coe_add] <;>
    abel
theorem shift_zero_pullbackField (U : GaugeField a) :
    (shift (0 : LatticePoint a)).pullbackField U = U := by
  refine Subtype.ext (funext fun b => congrArg U.1 ?_)
  apply Link.ext <;> refine Subtype.ext ?_ <;>
    simp [LatticeSymmetry.linkMap, LatticeSymmetry.pointMap, shift]
theorem shift_actOn_add {E : Type*} (v w : LatticePoint a) (A : GaugeField a → E) :
    (shift (v + w)).actOn A = (shift v).actOn ((shift w).actOn A) :=
  funext fun U => congrArg A (shift_pullbackField_add v w U)
theorem LatticeSymmetry.continuous_pullbackField (s : LatticeSymmetry a) :
    Continuous s.pullbackField := by
  have hval : Continuous fun U : GaugeField a =>
      (U.1 : Link a → Matrices.ComplexMatrix2.specialUnitary) :=
    continuous_subtype_val
  exact Continuous.subtype_mk
    (f := fun U : GaugeField a => fun b => U.1 (s.linkMap b))
    (continuous_pi fun b => (continuous_apply _).comp hval) fun U => (s.pullbackField U).2
theorem IsBoundedObservable.actOn {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (s : LatticeSymmetry a) : IsBoundedObservable (s.actOn A) := by
  obtain ⟨hm, C, hC⟩ := hA
  exact ⟨hm.comp s.continuous_pullbackField.measurable, C, fun U => hC _⟩
def periodSubgroup (ν : Measure (GaugeField a)) : AddSubgroup (LatticePoint a) where
  carrier := {v | IsSymmetricUnder ν (shift v)}
  zero_mem' := fun A _ => by
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    exact congrArg A (shift_zero_pullbackField U)
  add_mem' := fun {v w} hv hw A hA => by
    rw [shift_actOn_add, hv _ (hA.actOn _), hw A hA]
  neg_mem' := fun {v} hv A hA => by
    rw [← hv _ (hA.actOn _), ← shift_actOn_add, add_neg_cancel]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    exact congrArg A (shift_zero_pullbackField U)
theorem mem_weakLimitsAlongSides_iff (L K : ℕ) (β : ℝ)
    (ν : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :
    ν ∈ weakLimitsAlongSides L K β ↔
      IsProbabilityMeasure ν ∧ ∃ n : ℕ → ℕ, (∀ i, 0 < n i) ∧
        Tendsto (fun i => PeriodicLattice.torusSide L (n i)) atTop atTop ∧
        ∀ F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ, Continuous F →
          Tendsto (fun i => ∫ U, F U ∂liftedWilsonMeasure L (n i) K β) atTop
            (𝓝 (∫ U, F U ∂ν)) :=
  Iff.rfl
end InfiniteLattice
end YangMills.Construction
