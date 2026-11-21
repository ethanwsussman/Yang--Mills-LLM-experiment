import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def sideInLevelUnits (L m K j : ℕ) : ℝ := 2 * (L : ℝ) ^ ((m : ℤ) + (K : ℤ) - (j : ℤ))
def halfWidth (L n : ℕ) : ℝ := ((L : ℝ) ^ n - 1) / 2
def IsLevelLift (L m K j : ℕ) (x : FourTorus L m) (w : Fin 4 → ℝ) : Prop :=
  ∃ v : Fin 4 → ℝ, (∀ μ, (v μ : AddCircle (torusSide L m)) = x μ) ∧
    ∀ μ, w μ = toLevelUnits L K j (v μ)
def torusClassOf (L m K j : ℕ) (w : Fin 4 → ℝ) : FourTorus L m :=
  Classical.epsilon fun x => IsLevelLift L m K j x w
def coordVec (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1
def shiftBy (L m K j : ℕ) (x : FourTorus L m) (r : Fin 4 → ℝ) : FourTorus L m :=
  torusClassOf L m K j (Classical.epsilon (IsLevelLift L m K j x) + r)
def supNormVec (r : Fin 4 → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun μ => |r μ|
end PeriodicLattice
end YangMills.Construction
