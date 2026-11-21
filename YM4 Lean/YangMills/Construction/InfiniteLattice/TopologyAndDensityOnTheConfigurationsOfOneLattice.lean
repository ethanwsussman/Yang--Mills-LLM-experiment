import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.LatticePhases
def IsUniformlyDenseIn {X : Type*} (A T : Set (X → ℂ)) : Prop :=
  A ⊆ T ∧ ∀ F ∈ T, ∀ ε : ℝ, 0 < ε → ∃ H ∈ A, uniformSup (F - H) < ε
structure TopologyDensity (D : Setup) : Prop where
  compact : CompactSpace (InfiniteLattice.GaugeField D.mesh)
  metrizable : TopologicalSpace.MetrizableSpace (InfiniteLattice.GaugeField D.mesh)
  compact_prob : CompactSpace (ProbMeasure (InfiniteLattice.GaugeField D.mesh))
  metrizable_prob : TopologicalSpace.MetrizableSpace (ProbMeasure (InfiniteLattice.GaugeField D.mesh))
  exists_nonUnitalSubalgebra : ∃ A : NonUnitalSubalgebra ℂ (InfiniteLattice.GaugeField D.mesh → ℂ),
    (A : Set (InfiniteLattice.GaugeField D.mesh → ℂ)) = InfiniteLattice.continuousLocalFunctions D.mesh
  dense_local :
    IsUniformlyDenseIn (InfiniteLattice.continuousLocalFunctions D.mesh) {F | Continuous F}
  countable_dense : ∃ A : Set (InfiniteLattice.GaugeField D.mesh → ℂ),
    A.Countable ∧ IsUniformlyDenseIn A {F | Continuous F}
  countable_dense_local : ∃ A : Set (InfiniteLattice.GaugeField D.mesh → ℂ), A.Countable ∧
    IsUniformlyDenseIn A (InfiniteLattice.continuousLocalFunctions D.mesh) ∧
      IsUniformlyDenseIn A {F | Continuous F}
  dense_Lp1 : ∀ ρ : ProbMeasure (InfiniteLattice.GaugeField D.mesh), Dense {Y : ρ.Lp1 |
    ∃ F : C(InfiniteLattice.GaugeField D.mesh, ℂ),
      (Y : InfiniteLattice.GaugeField D.mesh → ℂ) =ᵐ[ρ.toMeasure] F}
  dense_Lp2 : ∀ ρ : ProbMeasure (InfiniteLattice.GaugeField D.mesh), Dense {Y : ρ.Lp2 |
    ∃ F : C(InfiniteLattice.GaugeField D.mesh, ℂ),
      (Y : InfiniteLattice.GaugeField D.mesh → ℂ) =ᵐ[ρ.toMeasure] F}
  ext_of_dense : ∀ A : Set (InfiniteLattice.GaugeField D.mesh → ℂ),
    IsUniformlyDenseIn A {F | Continuous F} →
    ∀ ρ ρ' : ProbMeasure (InfiniteLattice.GaugeField D.mesh),
      (∀ F ∈ A, ρ.eval F = ρ'.eval F) → ρ = ρ'
  countable_finite_linkSets : {S : Set (InfiniteLattice.Link D.mesh) | S.Finite}.Countable
  countable_points : Countable (InfiniteLattice.LatticePoint D.mesh)
def TopologyDensityHolds : Prop := ∀ D : Setup, TopologyDensity D
end YangMills.Construction.LatticePhases
