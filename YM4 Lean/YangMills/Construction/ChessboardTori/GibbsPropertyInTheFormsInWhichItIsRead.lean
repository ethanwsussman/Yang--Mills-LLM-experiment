import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.InfiniteLattice.EquivalentFormsOfTheGibbsProperty
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory
noncomputable section
namespace ChessboardTori
open InfiniteLattice InfiniteLattice.GibbsEquivalences
namespace GibbsForms
def periodicChessboardGibbsMeasures (D : ChessboardSetup) : Set (Measure D.GaugeField) :=
  {ν | IsProbabilityMeasure ν ∧ KernelCondExpInner D.mesh_pos D.β ν ∧
    ∃ H : AddSubgroup (LatticePoint D.mesh), H.FiniteIndex ∧
      ∀ v ∈ H, IsSymmetricUnder ν (InfiniteLattice.shift v)}
def Statement : Prop :=
  ∀ D : ChessboardSetup,
    (∀ ν : Measure D.GaugeField, IsProbabilityMeasure ν →
      List.TFAE [IsGibbs D.β ν, KernelCondExpInner D.mesh_pos D.β ν,
        KernelCondExp D.mesh_pos D.β ν, KernelInvariant D.mesh_pos D.β ν]) ∧
    (∀ ν : Measure D.GaugeField, IsProbabilityMeasure ν → IsGibbs D.β ν →
      ∀ (E : Finset D.Link) (hE : (E : Set D.Link) ⊆ positiveLinkSet D.mesh)
        (A : D.GaugeField → ℂ), IsBoundedObservable A →
        ∫ U, A U ∂ν = ∫ U, specKernel D.mesh_pos D.β E hE A U ∂ν ∧
        ∫ U, specKernel D.mesh_pos D.β E hE A U ∂ν = ∫ ξ, D.wilsonKernelAt E hE A ξ ∂ν) ∧
    D.periodicStates = periodicChessboardGibbsMeasures D ∧
    D.periodicStates = InfiniteLattice.periodicGibbsSet D.L D.K D.β
end GibbsForms
end ChessboardTori
end
end YangMills.Construction
