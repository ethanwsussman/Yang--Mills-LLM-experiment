import YangMills.Construction.WeightedGreen.DecayRateDefs
import YangMills.Construction.WeightedGreen.IntegerExpSums
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedGreen
def sumRate (d L : ℕ) (aLo aHi : ℝ) : ℝ :=
  1 / 4 * expDecayRate d L aLo aHi
def sumBound (d L : ℕ) (aLo aHi : ℝ) : ℝ :=
  blockSumConst d L (sumRate d L aLo aHi)
def cubeOverlap (d : ℕ) : ℕ := 3 * 2 ^ d
def remainderConst (d L : ℕ) (aHi ch C1 : ℝ) : ℝ :=
  (2 * (d : ℝ) * ch * (L : ℝ) ^ 2 + ch * (L : ℝ) ^ 4 + aHi * (d : ℝ) * ch * (L : ℝ) ^ 2) * C1
def crossConst (d L : ℕ) (aHi ch C1 : ℝ) : ℝ :=
  C1 * max
    ((L : ℝ) ^ 2 * (2 * (d : ℝ) * ch ^ 2 * (L : ℝ) ^ 4 + ch * (L : ℝ) ^ 4 +
        aHi * (d : ℝ) * ch * (L : ℝ) ^ 2) + 2 * ch * (L : ℝ) ^ 2)
    ((d : ℝ) * ch * (L : ℝ) ^ 4 + 1)
def gapLowerBound (d L : ℕ) (aLo aHi : ℝ) : ℝ :=
  max ((L : ℝ) * ((L : ℝ) + 9))
    (max (((d : ℝ) + 2) * (expDecayRate d L aLo aHi)⁻¹ * Real.log (L : ℝ))
      (4 * (sumRate d L aLo aHi)⁻¹ *
        (2 * (d : ℝ) * Real.log (intExpSum (1 / 2 * sumRate d L aLo aHi)) +
          1 / 4 * sumRate d L aLo aHi * (d : ℝ) * ((L : ℝ) + 3) +
          Real.log 2 + 1)))
def walkConst (d L : ℕ) (aLo aHi ch C1 : ℝ) : ℝ :=
  (cubeOverlap d : ℝ) * sumBound d L aLo aHi *
    max (remainderConst d L aHi ch C1) (crossConst d L aHi ch C1)
def blockLowerBound (d L : ℕ) (aLo aHi ch C1 : ℝ) : ℝ :=
  max (3 * (L : ℝ) * ((L : ℝ) + 12)) (2 * walkConst d L aLo aHi ch C1)
end WeightedGreen
end YangMills.Construction
