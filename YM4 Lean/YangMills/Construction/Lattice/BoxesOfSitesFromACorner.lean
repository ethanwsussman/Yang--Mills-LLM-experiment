import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def sitesFromCorner (z : Site L m j) (N : Fin 4 → ℤ) : Set (Site L m j) :=
  {x | ∃ t : Fin 4 → ℤ, (∀ μ, 0 ≤ t μ ∧ t μ < N μ) ∧ x = offsetSite z t}
def HasSiteCounts (j : ℤ) (P : Set (Site L m j)) (N : Fin 4 → ℤ) : Prop :=
  ∃ lo hi, HasChartFaces j P lo hi ∧ ∀ μ, hi μ - lo μ = (N μ : ℝ) * meshSize L j
def sitesAsTorusPoints (P : Set (Site L m j)) : Set (FourTorus L m) :=
  (fun x : Site L m j => (x : FourTorus L m)) '' P
def blockCorner {j' : ℤ} (N : ℤ) (y : Site L m j) : Site L m j' :=
  offsetSite (y.toSublattice j') fun _ => -((N - 1) / 2)
def uniformCounts (N : ℤ) : Fin 4 → ℤ := fun _ => N
def doubledCounts (N : ℤ) (μ : Fin 4) : Fin 4 → ℤ := Function.update (uniformCounts N) μ (2 * N)
def plaquetteCounts (N : ℤ) (μ ν : Fin 4) : Fin 4 → ℤ :=
  Function.update (doubledCounts N μ) ν (2 * N)
def CountsBoundedByDoubleBlock (L m K n k' : ℕ) (C : Fin 4 → ℤ) : Prop :=
  (∀ μ, C μ ≤ 2 * (L : ℤ) ^ (k' - n)) ∧ 2 * (L : ℤ) ^ (k' - n) < (L : ℤ) ^ (m + K - n)
def BlocksAreCornerBoxes (L m K n k' : ℕ) : Prop :=
  ∀ y : SiteAtLevel L m K k',
    (refinedBlock (k' - n) y =
        sitesAsTorusPoints (sitesFromCorner (blockCorner (j' := levelDepth K n) ((L : ℤ) ^ (k' - n)) y)
          (uniformCounts ((L : ℤ) ^ (k' - n)))) ∧
      CountsBoundedByDoubleBlock L m K n k' (uniformCounts ((L : ℤ) ^ (k' - n)))) ∧
    (∀ μ : Fin 4,
      refinedBlock (k' - n) (Bond.forwardFrom y μ).source ∪
          refinedBlock (k' - n) (Bond.forwardFrom y μ).target =
          sitesAsTorusPoints (sitesFromCorner
            (blockCorner (j' := levelDepth K n) ((L : ℤ) ^ (k' - n)) y)
            (doubledCounts ((L : ℤ) ^ (k' - n)) μ)) ∧
        CountsBoundedByDoubleBlock L m K n k' (doubledCounts ((L : ℤ) ^ (k' - n)) μ)) ∧
    (∀ p : PlaquetteAtLevel L m K k', p.origin = y →
      (⋃ c ∈ p.vertices, refinedBlock (k' - n) c) =
          sitesAsTorusPoints (sitesFromCorner
            (blockCorner (j' := levelDepth K n) ((L : ℤ) ^ (k' - n)) y)
            (plaquetteCounts ((L : ℤ) ^ (k' - n)) p.firstAxis p.secondAxis)) ∧
        CountsBoundedByDoubleBlock L m K n k'
          (plaquetteCounts ((L : ℤ) ^ (k' - n)) p.firstAxis p.secondAxis))
def CornerBoxProperties : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K → ∀ n : ℕ, n ≤ K →
    (∀ (z : SiteAtLevel L m K n) (N : Fin 4 → ℤ),
      (∀ μ, 1 ≤ N μ ∧ N μ < (L : ℤ) ^ (m + K - n)) →
        IsSiteBox (levelDepth K n) (sitesFromCorner z N) ∧
          HasSiteCounts (levelDepth K n) (sitesFromCorner z N) N) ∧
    ∀ k' : ℕ, n ≤ k' → k' ≤ K → BlocksAreCornerBoxes L m K n k'
end PeriodicLattice
end YangMills.Construction
