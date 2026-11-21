import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AxialGauges
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def BlockContoursAndCombs : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ i : ℕ, i < K → ∀ (z : SiteAtLevel L m K (i + 1)) (x : SiteAtLevel L m K i),
    (x : FourTorus L m) ∈ unitBlock z →
    (∃! n : Fin 4 → ℤ, IsBlockOffset z x n) ∧
    (∀ Γ ∈ contourSet z x,
      IsBondPathFromTo Γ (z.toSublattice (levelDepth K i)) x ∧
      (z : FourTorus L m) ∈ unitBlock z ∧
      (∀ b ∈ Γ, (b.source : FourTorus L m) ∈ unitBlock z ∧
        (b.target : FourTorus L m) ∈ unitBlock z) ∧
      ((x : FourTorus L m) = z → Γ = [])) ∧
    (∃ P : Set (SiteAtLevel L m K i), IsSiteBox (levelDepth K i) P ∧
      z.toSublattice (levelDepth K i) ∈ P ∧ x ∈ P) ∧
    (∃ d : Fin 4 → ℤ, IsChartOffset (z.toSublattice (levelDepth K i)) x d) ∧
    ∃ σ : AxisOrdering z x,
      StrictAnti (fun s => ((σ s : offsetAxes z x) : Fin 4)) ∧
      combToBlockSite z x = orderedContour z x σ
end PeriodicLattice
end YangMills.Construction
