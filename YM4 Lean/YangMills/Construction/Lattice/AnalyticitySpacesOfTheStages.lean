import YangMills.Construction.Lattice.AnalyticityDomains
import YangMills.Construction.Lattice.PreparedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m : ℕ}
namespace AnalyticityConstants
variable (N : AnalyticityConstants)
def nextComplement (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (l : ℕ) : Set (FourTorus L m) :=
  if l < k then complementRegion (coarseCubeIndex K N.cubeExp (l + 1)) (Ω (l + 1)) else univ
def IsStageLocalizationDomain {c : ℕ → ℕ} {K k : ℕ} (r : ℕ) (x : ℕ → ℝ)
    (S : ScaleLabel L m K N.cubeExp c k) (n : ℕ) (X : Set (FourTorus L m)) : Prop :=
  ∃ l, IsLeast {i | (lowerLevel L r x k + n).toNat ≤ i ∧
      X ⊆ N.nextComplement K k S.domainSeq i} l ∧
    (X ∩ S.domainSeq l).Nonempty ∧ X ∈ connectedRegions L m (coarseCubeIndex K N.cubeExp l)
end AnalyticityConstants
end YangMills.Construction.PeriodicLattice
