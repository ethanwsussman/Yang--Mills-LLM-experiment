import YangMills.Construction.Lattice.PropertiesOfTheFourLocalMaps
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences SeparatedRegions Conventions Matrices
namespace SequenceTriples
def IsDoubledLocalMapsConstant (L : ℕ) (c : ℝ) : Prop :=
  1 ≤ c ∧
    ∀ (m : ℕ) (S : ScaleData)
      (_ : ∀ (n : ℕ) (e : BondAtLevel L m S.levels (n + 1)),
        Fintype (PositiveBondsOf (doubleBlockSymmetricSet e)))
      (Ω : ℕ → Set (FourTorus L m)) (g : ℝ) (A : Set (FourTorus L m))
      (U J : FineBond L m S → ComplexMatrix2)
      (j : LeveledBond L m S → ComplexMatrix2) (β : ℝ) (h : FourTorus L m → ℝ) (θ : ℝ),
      IsDoubledMapsHypothesis S Ω g A U J j → 0 < β → β < 1 →
        IsCommutatorTestFunction S Ω h θ →
        DoubledMapsLocal S Ω c β θ A U J j h
def doubledLocalMapsConst (L : ℕ) : ℝ := Classical.epsilon (IsDoubledLocalMapsConstant L)
end SequenceTriples
end YangMills.Construction
end
