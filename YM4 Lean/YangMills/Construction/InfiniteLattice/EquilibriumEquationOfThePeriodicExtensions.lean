import YangMills.Construction.InfiniteLattice.LatticeOfACutoffAndTheVariablesOfASetOfBonds
import YangMills.Construction.InfiniteLattice.WindowsKernelOperatorAndDensitiesAtOneSpacing
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace InfiniteLattice.PeriodicExtensions
def LiftedEquilibriumEquation.Statement : Prop :=
  ∀ (d : CutoffLinks.CutoffData) (W : LinkWindow d.spacing) (S : Set (Link d.spacing)),
    S.Finite → S ⊆ CutoffLattice.positiveLinksAt d.L d.K →
    (W.links : Set (Link d.spacing)) ⊆ S → W.rim ⊆ S →
    Set.InjOn (projectLink d.L d.m ((d.K : ℕ) : ℤ)) S →
    ∀ F : GaugeField d.spacing → ℝ, Measurable F → (∃ C : ℝ, ∀ U, |F U| ≤ C) →
      CutoffLattice.DependsOnlyOn F S →
      CutoffLattice.integralAgainst (liftedWilsonMeasure d.L d.m d.K d.coupling)
          (W.realOperator d.spacing_pos d.coupling F) =
        CutoffLattice.integralAgainst (liftedWilsonMeasure d.L d.m d.K d.coupling) F
end InfiniteLattice.PeriodicExtensions
end YangMills.Construction
