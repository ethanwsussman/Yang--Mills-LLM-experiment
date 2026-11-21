import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FullSpace
def projVertex (L n k i : ℕ) (x : FullSpace.Vertex L k i) : Tower.Vertex L n k i :=
  ⟨TorusMetric.torusProj (PeriodicLattice.torusSide L n) (x : InfiniteLattice.AmbientSpace), by
    obtain ⟨_, m, hm⟩ := x
    refine ⟨m, fun μ => ?_⟩
    simp [TorusMetric.torusProj, hm μ, meshSize_levelDepth]⟩
def projEdge (L n k i : ℕ) (e : FullSpace.Edge L k i) : Tower.Edge L n k i :=
  Classical.epsilon fun f =>
    f.source = projVertex L n k i e.initial ∧ f.target = projVertex L n k i e.terminal
def projField (L n k i : ℕ) (S : Set (FullSpace.Edge L k i))
    (U : FullSpace.Edge L k i → Matrices.ComplexMatrix2) :
    Tower.Edge L n k i → Matrices.ComplexMatrix2 :=
  open Classical in
  fun f => if h : ∃ e ∈ S, projEdge L n k i e = f then U h.choose else 1
end FullSpace
def EdgeProjectionProperties : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i ≤ k →
    (∀ e : FullSpace.Edge L k i,
      (FullSpace.projEdge L n k i e).source = FullSpace.projVertex L n k i e.initial ∧
      (FullSpace.projEdge L n k i e).target = FullSpace.projVertex L n k i e.terminal ∧
      (e.IsPositivelyOriented → (FullSpace.projEdge L n k i e).IsPositivelyOriented) ∧
      (FullSpace.projEdge L n k i e).opposite = FullSpace.projEdge L n k i e.opposite) ∧
    ∀ (S : Set (FullSpace.Edge L k i)) (S' : Set (Tower.Edge L n k i)),
      (∀ e ∈ S, e.opposite ∈ S) → BijOn (FullSpace.projEdge L n k i) S S' →
        PeriodicLattice.IsReversalClosed S' ∧
        ∀ U : FullSpace.Edge L k i → Matrices.ComplexMatrix2,
          FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup S U →
            (∀ e ∈ S, FullSpace.projField L n k i S U (FullSpace.projEdge L n k i e) = U e) ∧
            PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup S'
              (FullSpace.projField L n k i S U)
end Tower
end YangMills.Construction
end
