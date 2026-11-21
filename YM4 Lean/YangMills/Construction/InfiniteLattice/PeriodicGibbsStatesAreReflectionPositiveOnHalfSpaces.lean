import YangMills.Construction.ChessboardTori.PeriodicGibbsStatesAreInvariantAndReflectionPositive
import YangMills.Construction.InfiniteLattice.StandingConventionsOfMultipleReflections
import YangMills.Construction.InfiniteLattice.TimeReflections
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.MultipleReflections.HalfSpacePositivity
def Statement : Prop :=
  ∀ D : Setup, ∀ μ ∈ D.gibbsStates,
    (∀ v : InfiniteLattice.LatticePoint D.mesh,
      InfiniteLattice.IsSymmetricUnder μ (InfiniteLattice.shift v)) ∧
    (∀ (α : Fin 4) (c : ℝ) (hc : c ∈ InfiniteLattice.halfSpacingTimes D.mesh),
      (∀ A : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable A →
        (InfiniteLattice.IsRegionMeasurable {x : InfiniteLattice.AmbientSpace | c ≤ x α} A ∨
          InfiniteLattice.IsRegionMeasurable {x : InfiniteLattice.AmbientSpace | x α ≤ c} A) →
        0 ≤ ∫ U, (ChessboardTori.axialMirror α c hc).conjReflect A U * A U ∂μ) ∧
      InfiniteLattice.IsReflectionPositiveAt μ (ChessboardTori.axialMirror α c hc)) ∧
    ∀ (α : Fin 4) (c : ℝ) (hc : c ∈ InfiniteLattice.halfSpacingTimes D.mesh),
      InfiniteLattice.IsSymmetricUnder μ (ChessboardTori.axialMirror α c hc).symmetry
end YangMills.Construction.MultipleReflections.HalfSpacePositivity
end
