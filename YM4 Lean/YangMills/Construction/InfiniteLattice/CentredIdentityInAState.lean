import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CenteredIdentity
def SmearedIsFiniteAndBounded (a : ℝ) (f : AmbientSpace → ℝ) : Prop :=
  {P : ElementaryPlaquette a | f P.center ≠ 0}.Finite ∧
    YangMills.Construction.Probability.IsBoundedRealRV
      (smearedEnergy f : GaugeField a → ℝ)
def TestFunctionsFormSubspaceWithLinearSmearing (a : ℝ) : Prop :=
  ∃ W : Submodule ℝ (AmbientSpace → ℝ), (W : Set (AmbientSpace → ℝ)) = compactTestFunctions ∧
    ∃ T : W →ₗ[ℝ] (GaugeField a → ℝ), ∀ f : W, T f = smearedEnergy (f : AmbientSpace → ℝ)
def UrsellIsRealSymmetricMultilinear {a : ℝ} (μ : Measure (GaugeField a)) (n : ℕ) :
    Prop :=
  ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, f i ∈ compactTestFunctions) →
    (ursellFunction μ n f).im = 0 ∧
    (∀ π : Equiv.Perm (Fin n),
      ursellFunction μ n (fun i => f (π i)) = ursellFunction μ n f) ∧
    (∀ (i : Fin n) (g : AmbientSpace → ℝ), g ∈ compactTestFunctions →
      ursellFunction μ n (Function.update f i (f i + g)) =
        ursellFunction μ n f + ursellFunction μ n (Function.update f i g)) ∧
    (∀ (i : Fin n) (c : ℝ),
      ursellFunction μ n (Function.update f i (c • f i)) =
        (c : ℂ) * ursellFunction μ n f)
def Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (μ : Measure (GaugeField (refinedSpacing s.L s.K))),
    IsProbabilityMeasure μ →
    ((∀ f : AmbientSpace → ℝ, f ∈ compactTestFunctions →
        SmearedIsFiniteAndBounded (refinedSpacing s.L s.K) f) ∧
      TestFunctionsFormSubspaceWithLinearSmearing (refinedSpacing s.L s.K)) ∧
    (∀ n : ℕ, 2 ≤ n → UrsellIsRealSymmetricMultilinear μ n) ∧
    (∀ (q : ℕ) (h : Fin q → AmbientSpace → ℝ), (∀ l, h l ∈ compactTestFunctions) →
      centeredMoment μ h = ursellPartitionSum μ h)
end YangMills.Construction.InfiniteLattice.CenteredIdentity
