import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.BracketAtPeriodicLift
open YangMills.Construction.LocalKernels.Periodisation YangMills.Construction.Tower
def DescendsClaim : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ (j : ℕ) (h : j ≤ k),
      ∀ V ∈ fieldsIn L n k j YangMills.Construction.PeriodicLattice.complexGaugeGroup,
      ∀ J ∈ complexEdgeForms L n k j,
        BracketTermsFormed L n k j V ∧ BracketKernelDescends L n k j h V J
end YangMills.Construction.LocalKernels.BracketAtPeriodicLift
