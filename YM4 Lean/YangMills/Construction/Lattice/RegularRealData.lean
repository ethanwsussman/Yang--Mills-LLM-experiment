import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def HasBlockAverageAt (K q : ℕ) (Γ : ∀ j : ℕ, Set (BondAtLevel L m K j))
    (e : BondAtLevel L m K (q + 1)) : Prop :=
  (bondsInDoubleBlock e : Set (BondAtLevel L m K q)) ⊆ Γ q
def levelMixedField (ω : ℝ) (K q : ℕ) (Γ : ∀ j : ℕ, Set (BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    BondAtLevel L m K (q + 1) → Matrices.ComplexMatrix2 :=
  open Classical in
  fun e => if e ∈ Γ (q + 1) then V (q + 1) e else blockAverageStep ω q (V q) e
def regularRealFields (ω εBar : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (Γ : ∀ j : ℕ, Set (BondAtLevel L m K j)) :
    Set (∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :=
  {V | (∀ j ≤ k, IsGaugeField compactGaugeGroup (Γ j) (V j)) ∧
    (∀ p : PlaquetteAtLevel L m K 0, (∃ e ∈ p.boundaryBonds, e ∈ Γ 0) →
      (∀ e ∈ p.boundaryBonds, e ∈ Γ 0) →
      Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy (V 0) p - 1) < εBar) ∧
    ∀ q < k, ∀ p : PlaquetteAtLevel L m K (q + 1), (∃ e ∈ p.boundaryBonds, e ∈ Γ (q + 1)) →
      (∀ e ∈ p.boundaryBonds, e ∈ Γ (q + 1) ∨ e ∈ bondsInside (Ω q \ Ω (q + 1))) →
      (∀ e ∈ p.boundaryBonds, e ∉ Γ (q + 1) → HasBlockAverageAt K q Γ e) ∧
        Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (levelMixedField ω K q Γ V) p - 1) < εBar}
end PeriodicLattice
end YangMills.Construction
