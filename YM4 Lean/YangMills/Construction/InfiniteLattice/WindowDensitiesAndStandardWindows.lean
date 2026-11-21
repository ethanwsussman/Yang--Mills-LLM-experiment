import YangMills.Construction.InfiniteLattice.WilsonWindows
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
namespace LinkWindow
variable (W : LinkWindow a)
def marginalDensity (ha : 0 < a) (β : ℝ) (ν : Measure (GaugeField a)) (V : W.Assignments) : ℝ :=
  ∫ U, W.densityKernel ha β V U ∂ν
end LinkWindow
def LinkWindow.InjectsIntoTorus {L K : ℕ} (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)))
    (m : ℕ) : Prop :=
  InjOn (projectLink L m (K : ℤ))
    ((W.links : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ∪ W.rim)
theorem latticeSubgroup_supNormVec_le_finite (a r : ℝ) :
    {x : AmbientSpace | x ∈ latticeSubgroup a ∧ TorusMetric.supNormVec x ≤ r}.Finite := by
  by_cases ha : a = 0
  · refine (finite_singleton (0 : AmbientSpace)).subset ?_
    rintro x ⟨⟨n, hn⟩, -⟩
    funext i
    simp [hn i, ha]
  · obtain ⟨N, hN⟩ := exists_nat_ge (r / |a|)
    have hapos : 0 < |a| := abs_pos.mpr ha
    refine ((finite_Icc (fun _ : Fin 4 => -(N : ℤ)) fun _ => (N : ℤ)).image
      fun n i => (n i : ℝ) * a).subset ?_
    rintro x ⟨⟨n, hn⟩, hx⟩
    have hcoord : ∀ i, |n i| ≤ (N : ℤ) := fun i => by
      have hle : |x i| ≤ TorusMetric.supNormVec x :=
        Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)
      have hmul : |(n i : ℝ)| * |a| ≤ r := by
        rw [← abs_mul, ← hn i]
        exact hle.trans hx
      have hreal : |(n i : ℝ)| ≤ N := ((le_div_iff₀ hapos).mpr hmul).trans hN
      exact_mod_cast hreal
    exact ⟨n, ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩,
      funext fun i => (hn i).symm⟩
theorem linksWithin_supNormVec_le_finite (a r : ℝ) :
    (linksWithin {x | TorusMetric.supNormVec x ≤ r} : Set (Link a)).Finite := by
  have hfin := latticeSubgroup_supNormVec_le_finite a r
  refine ((hfin.prod hfin).preimage
    (f := fun e : Link a => ((e.initial : AmbientSpace), (e.terminal : AmbientSpace))) ?_).subset ?_
  · intro e _ f _ h
    have hpair := Prod.ext_iff.mp h
    exact Link.ext (Subtype.ext hpair.1) (Subtype.ext hpair.2)
  · intro e he
    exact ⟨⟨e.initial.2, he.1⟩, ⟨e.terminal.2, he.2⟩⟩
def cutoffWindow (L K : ℕ) : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)) where
  links := ((linksWithin_supNormVec_le_finite (PeriodicLattice.meshSize L (K : ℤ)) (K : ℝ)).subset
    (inter_subset_right
      (s := {e : Link (PeriodicLattice.meshSize L (K : ℤ)) | e.IsPositivelyOriented}))).toFinset
  isPositive _ he := ((Set.Finite.mem_toFinset _).mp he).1
end InfiniteLattice
end YangMills.Construction
