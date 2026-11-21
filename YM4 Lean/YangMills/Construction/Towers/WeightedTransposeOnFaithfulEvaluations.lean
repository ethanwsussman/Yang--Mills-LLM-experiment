import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (HasFiniteSupport)
open RescaledConditions (TransposeKernelScaling)
namespace FaithfulCoordinates
structure IsFaithfulEvaluation (r : PauliComponentsOfSymmetricKernel) : Prop where
  ofCoeffs_mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  coeffs_linear : ∀ (z : ℂ), ∀ f ∈ r.space.complexSubmodule, ∀ g ∈ r.space.complexSubmodule,
    r.coeffs (z • f + g) = z • r.coeffs f + r.coeffs g
  finitelySupported_iff : ∀ f ∈ r.space.complexSubmodule,
    (r.space.IsFinitelySupported f ↔ HasFiniteSupport (r.coeffs f))
  pair_eq : ∀ g ∈ r.space.complexSubmodule, ∀ f ∈ r.space.complexSubmodule,
    r.space.IsFinitelySupported f →
    r.space.pair g f = ∑ᶠ ι, r.coeffs g ι * r.coeffs f ι
def TransposeScales : Prop :=
  ∀ r r' : PauliComponentsOfSymmetricKernel, IsFaithfulEvaluation r → IsFaithfulEvaluation r' → ∀ a a' : ℝ,
    TransposeKernelScaling r r' a a'
end FaithfulCoordinates
end YangMills.Construction.Tower
end
