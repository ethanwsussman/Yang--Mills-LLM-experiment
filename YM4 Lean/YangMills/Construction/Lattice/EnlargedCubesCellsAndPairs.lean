import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedSequences
open PeriodicLattice
variable {L m : ℕ} (S : ScaleData)
def widenedCubeClass (Ω : ℕ → Set (FourTorus L m)) (n : ℕ) : Set (Set (FourTorus L m)) :=
  {q | (∃ (z : FourTorus L m) (a : ℝ), 0 < a ∧ q = closedSupCube z a ∧
      S.toUnits L a ≤ 12 * (L : ℝ) ^ S.blockExp * S.levelMesh L n) ∧
    q ⊆ layerSet S Ω n ∪ layerSet S Ω (n + 1) ∧ IsBlockUnion S n q}
def widenedCubes (Ω : ℕ → Set (FourTorus L m)) : Set (LevelCube L m) :=
  {c | c.1 ≤ S.top ∧ c.2 ∈ widenedCubeClass S Ω c.1}
def IsWidenedCell (Ω : ℕ → Set (FourTorus L m)) (rw : ℕ) (F : Set (LevelCube L m)) : Prop :=
  F.Nonempty ∧ F.encard ≤ rw ∧ F ⊆ widenedCubes S Ω ∧
    ∀ c ∈ F, ∀ c' ∈ F, ∃ l : List (LevelCube L m), (∀ x ∈ l, x ∈ F) ∧
      l.IsChain (fun x x' => (x.2 ∩ x'.2).Nonempty) ∧ l.head? = some c ∧ l.getLast? = some c'
end YangMills.Construction.SeparatedSequences
