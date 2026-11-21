import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.StateLimits
open InfiniteLattice R4TupleForms
variable {s : Conventions.StandingParameters}
def centeredProduct (K : ℕ) (ν : Measure (GaugeField (PeriodicLattice.meshSize s.L (K : ℤ))))
    (X : FinTuple s) (U : GaugeField (PeriodicLattice.meshSize s.L (K : ℤ))) : ℝ :=
  ∏ i, (smearedEnergy (X.1.2 i) U - ∫ V, smearedEnergy (X.1.2 i) V ∂ν)
theorem centeredProduct_nil (K : ℕ)
    (ν : Measure (GaugeField (PeriodicLattice.meshSize s.L (K : ℤ))))
    (U : GaugeField (PeriodicLattice.meshSize s.L (K : ℤ))) :
    centeredProduct K ν ⟨AmbientPoints.nilTuple s .euclidean,
      AmbientPoints.nilTuple_mem_allSeparatedTuples⟩ U = 1 := by
  have : IsEmpty (Fin (AmbientPoints.nilTuple s .euclidean).1) :=
    inferInstanceAs (IsEmpty (Fin 0))
  exact Fintype.prod_empty _
def pairedValue (K : ℕ → ℕ)
    (ρ ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ)))) (j : ℕ)
    (X : FinTuple s) : ℝ :=
  ∫ U, centeredProduct (K j) (ν j) X U ∂ρ j
def IsPointwiseLimit (K : ℕ → ℕ)
    (ρ ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ))))
    (σ : FinTuple s → ℝ) : Prop :=
  ∀ X, Tendsto (fun j => pairedValue K ρ ν j X) atTop (𝓝 (σ X))
structure IsPeriodicGibbsSeq (K : ℕ → ℕ) (β : ℕ → ℝ)
    (ρ ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize s.L (K j : ℤ)))) : Prop where
  cutoff_tendsto : Tendsto K atTop atTop
  left_mem : ∀ j, ρ j ∈ periodicGibbsSet s.L (K j) (β j)
  right_mem : ∀ j, ν j ∈ periodicGibbsSet s.L (K j) (β j)
end YangMills.Construction.StateLimits
end
