import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace
def LinkHasAxis {a : ℝ} (e : InfiniteLattice.Link a) (μ : Fin 4) : Prop :=
  e.terminal - e.initial = InfiniteLattice.axisStep a μ ∨
    e.terminal - e.initial = -InfiniteLattice.axisStep a μ
structure PivotLinkProperties (L : ℕ) {a : ℝ} (a' : ℝ) (c : InfiniteLattice.Link a) : Prop where
  mem_linkCorridor_iff : ∀ e : InfiniteLattice.Link a',
    e ∈ linkCorridor L a' c ↔ e.opposite ∈ linkCorridor L a' c.opposite
  existsUnique_mem_axisPath : ∃! e : InfiniteLattice.Link a',
    e ∈ axisPath (toFiner a' c.initial) (toFiner a' c.terminal) ∧ e ∈ linkCorridor L a' c
  isPivotLink : IsPivotLink L a' c (pivotLink L a' c)
  pivotLink_opposite : pivotLink L a' c.opposite = (pivotLink L a' c).opposite
  linkHasAxis_iff : ∀ μ : Fin 4, LinkHasAxis (pivotLink L a' c) μ ↔ LinkHasAxis c μ
  isPositivelyOriented_iff : (pivotLink L a' c).IsPositivelyOriented ↔ c.IsPositivelyOriented
def PivotLinkOfAnyOrientation : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i : ℕ, i < k →
    ∀ c : Edge L k (i + 1), PivotLinkProperties L (meshAt L k i) c
end Tower.FullSpace
end YangMills.Construction
