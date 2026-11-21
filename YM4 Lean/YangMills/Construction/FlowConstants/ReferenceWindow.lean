import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Parameters.ConstructionParameters
import YangMills.Construction.Thresholds.DegreeFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace FlowConstants
open ParameterChoice
variable (T : DerivedConstants) (c : ChoiceUpToCoupling)
def flowError : ℝ := T.CPrime c.toChoiceUpToRadii * c.γ ^ (c.κ₀ - 8)
def rateSharp : ℝ := oneLoopCoefficient c.L / 2 - flowError T c
def widthSharp : ℝ := T.Cβ c.toChoiceUpToRadii + flowError T c
def passageLevel (g : ℝ) : ℝ := g ^ (-2 : ℤ) + widthSharp T c
def windowLowerEnd (g : ℝ) : ℝ := passageLevel T c g ^ (-(1 / 2) : ℝ)
def firstPassageIndex (x : ℕ → ℝ) (g : ℝ) : ℕ := sInf {k | x k ≤ passageLevel T c g}
def HasFirstPassage (D : ℕ∞) (x : ℕ → ℝ) (g : ℝ) : Prop :=
  ∃ k : ℕ, (k : ℕ∞) ≤ D ∧ x k ≤ passageLevel T c g
def firstPassageWindow (x : ℝ → ℕ → ℝ) (D : ℝ → ℕ∞) (g : ℝ) (K : ℕ) : Set ℝ :=
  {β | passageLevel T c g ≤ β ∧ HasFirstPassage T c (D β) (x β) g ∧
    firstPassageIndex T c (x β) g = K}
def torusExponent (g' : ℝ) : ℕ :=
  11 + Nat.log c.L c.M + Nat.log c.L (Thresholds.blockSize c.L c.r (g' ^ (-2 : ℤ)))
def referenceTorusExponent (g : ℝ) : ℕ := torusExponent c (windowLowerEnd T c g)
def referenceTorusSide (g : ℝ) : ℝ := PeriodicLattice.torusSide c.L (referenceTorusExponent T c g)
def admissibleTorusSides (g : ℝ) : Set ℝ :=
  {ℓ | ℓ ∈ PeriodicLattice.torusSides c.L ∧ referenceTorusSide T c g ≤ ℓ}
variable {T c}
theorem referenceTorusSide_mem_torusSides (g : ℝ) :
    referenceTorusSide T c g ∈ PeriodicLattice.torusSides c.L :=
  ⟨referenceTorusExponent T c g, by unfold referenceTorusExponent torusExponent; omega, rfl⟩
theorem passageLevel_pos {g : ℝ} (hg : 0 < g) (hB : 0 < widthSharp T c) :
    0 < passageLevel T c g := by
  unfold passageLevel
  positivity
theorem zpow_neg_two_rpow_neg_half {g : ℝ} (hg : 0 < g) :
    (g ^ (-2 : ℤ)) ^ (-(1 / 2) : ℝ) = g := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul hg.le]
  norm_num
theorem windowLowerEnd_lt {g : ℝ} (hg : 0 < g) (hB : 0 < widthSharp T c) :
    windowLowerEnd T c g < g := by
  have hz : 0 < g ^ (-2 : ℤ) := by positivity
  have h := (Real.rpow_lt_rpow_iff_of_neg (passageLevel_pos hg hB) hz
    (by norm_num : (-(1 / 2) : ℝ) < 0)).2 (by unfold passageLevel; linarith)
  rwa [zpow_neg_two_rpow_neg_half hg] at h
end FlowConstants
end YangMills.Construction
