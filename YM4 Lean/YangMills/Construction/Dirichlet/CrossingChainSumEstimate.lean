import YangMills.Construction.Dirichlet.ShellCrossingChains
import YangMills.Construction.Torus.TorusLengths
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction
namespace Dirichlet
namespace ChainSumEstimate
theorem summable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Summable fun z : ℤ => Real.exp (-a * |(z : ℝ)|) := by
  have h : Summable fun n : ℕ => Real.exp (-a * (n : ℝ)) := by
    have e : (fun n : ℕ => Real.exp (-a * (n : ℝ))) = fun n : ℕ => Real.exp (-a) ^ n := by
      funext n
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [e]
    exact summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using Real.exp_lt_exp.mpr (show -a < 0 by linarith))
  apply Summable.of_nat_of_neg
  · simpa using h
  · simpa using h
section Kernels
variable {X : Type*}
def adjacentIndices (top j : ℕ) : Finset ℕ := ({j + 1, j - 1} : Finset ℕ).filter (· ≤ top)
variable {top : ℕ} {T : ℕ → Finset X} {E : ℕ → X → X → ℝ} {C : ℝ}
end Kernels
section Concrete
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
theorem one_le_blockFactor (hl : Parameters d L aMinus aPlus) : (1 : ℝ) ≤ L := by
  have := hl.three_le_blockFactor
  exact_mod_cast (by omega : 1 ≤ L)
theorem scaleAt_pos (hl : Parameters d L aMinus aPlus) (k : ℕ) : 0 < 𝒮.scaleAt (k : ℤ) := by
  have hL : (0 : ℝ) < L := by linarith [one_le_blockFactor hl]
  exact mul_pos (zpow_pos hL _) 𝒮.isSeparatedChain.scale_pos
open Classical in
def latticeSites (k : ℕ) : Finset (PeriodicTorus d S) :=
  if h : (spacingLattice d S (𝒮.scaleAt (k : ℤ)) : Set (PeriodicTorus d S)).Finite then h.toFinset else ∅
def decayKernel (A : ℝ) (k : ℕ) (a b : PeriodicTorus d S) : ℝ := Real.exp (-A * scaledGap 𝒮 k a b)
end Concrete
end ChainSumEstimate
end Dirichlet
end YangMills.Construction
