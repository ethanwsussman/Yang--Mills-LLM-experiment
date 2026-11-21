import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def GaussianNormaliserPositiveNearOne : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℕ, i + 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L m k (i + 1)) fun W => 0 < gaussianNormaliser L m k i W
end YangMills.Construction.Tower
end
