import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices YangMills.Construction.Conventions
variable {L m K k : ℕ}
def shiftSite (x : SiteAtLevel L m K k) (n : Fin 4 → ℤ) : SiteAtLevel L m K k :=
  x + ∑ ν, n ν • unitStep L m (levelDepth K k) ν
def IsCoarseBondSetup (c : BondAtLevel L m K (k + 1)) (μ : Fin 4) : Prop :=
  IsAdmissibleBlockingFactor L ∧ 0 < K ∧ 0 < m ∧ k < K ∧
    c.target - c.source = unitStep L m (levelDepth K (k + 1)) μ
theorem IsCoarseBondSetup.isPositivelyOriented {c : BondAtLevel L m K (k + 1)} {μ : Fin 4}
    (hc : IsCoarseBondSetup c μ) : c.IsPositivelyOriented :=
  ⟨μ, hc.2.2.2.2⟩
end YangMills.Construction.PeriodicLattice
