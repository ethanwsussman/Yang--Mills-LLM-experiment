import YangMills.Construction.DirichletOperator.ThreeGroupsOfInequalitiesForTheGreenOperator
import YangMills.Construction.Lattice.SiteNearnessRadius
import YangMills.Construction.SeparatedSequences.RateFloorAndSumBoundOfTheConsequences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.InputConstants
def blockPow (L : ℕ) : ℕ :=
  sInf {M : ℕ | (∃ a : ℕ, M = L ^ a) ∧ CombinedConstants.blockLower L ≤ (M : ℝ)}
def gapMultiplier (L : ℕ) : ℕ :=
  sInf {R : ℕ | (∃ a : ℕ, R = L ^ a) ∧ L ≤ R ∧
    max (CombinedConstants.derivedGapLower L)
        (16 * (4 * Real.log (L : ℝ) + Real.log 2) / SeparatedSequences.minimalInputRate L) ≤
      (R : ℝ) * (blockPow L : ℝ)}
def gapLength (L : ℕ) : ℕ := gapMultiplier L * blockPow L
def cappedExp (ε : ℝ) : ℝ := min ε (1 / 2)
def mainBound (L : ℕ) : ℝ :=
  12 * (1 + 16 * Real.exp 2) * Real.exp (2 * Lattice.siteNearnessRadius L) *
    max 1 (max ((L : ℝ) * CombinedConstants.mainConst L) (GreenThreeGroups.secondDiffBound L))
def holderBound (L : ℕ) (β : ℝ) : ℝ := 12 * max 1 (CombinedConstants.holderConst L β)
def gradBound (L : ℕ) (ε : ℝ) : ℝ :=
  24 * max 1 (max (CombinedConstants.gradConst L (cappedExp ε))
    (3 * GreenThreeGroups.pointwiseConst L ε))
def gradHolderBound (L : ℕ) (ε β : ℝ) : ℝ :=
  24 * if β + ε < 1 then
      max 1 (max (CombinedConstants.gradHolderConst L β ε)
        (3 * GreenThreeGroups.holderConst L ε β))
    else max 1 (3 * GreenThreeGroups.holderConst L ε β)
end YangMills.Construction.SeparatedSequences.InputConstants
end
