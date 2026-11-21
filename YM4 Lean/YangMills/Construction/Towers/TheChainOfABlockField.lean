import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k : ℕ}
def ChainOverBottom (W : Edge L n k k → Matrices.ComplexMatrix2) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ k), chainBottom W = chosenProlongComp L n k j (descendingChain W hj) ∧
    descendingChain W hj = smoothingIter L n k j (chainBottom W)
def ChainAxialGauge (W : Edge L n k k → Matrices.ComplexMatrix2) : Prop :=
  ∀ (i : ℕ) (hi : i < k), IsAxialGaugeAt L n k i (descendingChain W hi.le)
def ChainScalingCompatible (hL : 0 < L) (W : Edge L n k k → Matrices.ComplexMatrix2) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ k), 1 ≤ j → ∀ (i : ℕ) (hi : i ≤ j),
    descendingChain (scaledTopField hL hj (descendingChain W hj)) hi =
      transportTotal (scaleEdge hL hj i) (descendingChain W (hi.trans hj))
def VerticesInUniqueLayer (L n k : ℕ) : Prop :=
  ∀ x : Vertex L n k 0,
    (x : PeriodicLattice.FourTorus L n) ∉
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k) →
      ∃! i : Fin k,
        (x : PeriodicLattice.FourTorus L n) ∈
            PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i : ℕ)) ∧
          (x : PeriodicLattice.FourTorus L n) ∉
            PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k ((i : ℕ) + 1))
def BlockFieldChainProperties : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k → ∀ hL : 0 < L,
    EventuallyNearIdentity (fieldSpace L n k k)
        (fun W => ChainOverBottom W ∧ ChainAxialGauge W ∧
          ChainScalingCompatible hL W) ∧
      VerticesInUniqueLayer L n k
end YangMills.Construction.Tower
end
