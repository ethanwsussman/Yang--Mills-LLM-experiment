import YangMills.Construction.Lattice.EnlargedCubesCellsAndPairs
import YangMills.Construction.SeparatedSequences.SettingOfTheCells
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences
namespace YangMills.Construction.SeparatedSequences.CellSetting
def LatticeFinite (L m : ℕ) (i : ℤ) : Prop :=
  Finite (PeriodicLattice.Site L m i) ∧ Finite (PeriodicLattice.Bond L m i) ∧
    Finite (PeriodicLattice.Plaquette L m i)
def Finiteness.Statement : Prop :=
  (∀ L m K : ℕ, Odd L → 13 ≤ L → 0 < m → 0 < K →
    (∀ i : ℤ, -(m : ℤ) ≤ i → LatticeFinite L m i) ∧
    (∀ n : ℕ, n ≤ K → LatticeFinite L m (levelDepth K n)) ∧
    (∀ i : ℤ, -(m : ℤ) ≤ i → (standardCubePartition L m i).Finite)) ∧
  (∀ (L m : ℕ) (N : CellParameters L) (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)),
    N.IsCellSetting S Ω →
      (widenedCubes S Ω).Finite ∧ {F | IsWidenedCell S Ω N.walkRadius F}.Finite)
end YangMills.Construction.SeparatedSequences.CellSetting
