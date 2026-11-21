import YangMills.Construction.Lattice.MinimalOrbitsOfSetsInForce
import YangMills.Construction.Lattice.StageSequences
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ScaleLabel
variable {L m K m' k : ℕ} {c : ℕ → ℕ}
def stageBackgroundField (ε : ℝ) (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (n : ℕ)
    (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  activeMinimalField ε K k (S.stagedDomain r x Q n) V
def stageGluedBackground (ε : ℝ) (e r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (n : ℕ) (X : Set (FourTorus L m))
    (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  gluedCriticalConfiguration ε K k e k (S.stagedDomain r x Q n) X V
def finalBackground (ε : ℝ) (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  S.stageBackgroundField ε r x Q (Thresholds.delayDepth L r x k) V
end YangMills.Construction.PeriodicLattice.ScaleLabel
