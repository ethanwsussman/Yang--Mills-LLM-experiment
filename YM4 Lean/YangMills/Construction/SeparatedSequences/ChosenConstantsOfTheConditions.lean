import YangMills.Construction.SeparatedSequences.NumbersOfTheConditions
import YangMills.Construction.SeparatedSequences.PropertiesOfTheOperatorsOfASequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses
def operatorConstantsAt (L : ℕ) : OperatorConstants where
  zeroFormRate := SeparatedSequences.CombinedConstants.dirichletDecay L
  avgSqRate := SeparatedSequences.CombinedConstants.expansionDecay L
  cubeRate := SeparatedSequences.CombinedConstants.cubeDecay L
  oneFormRate := SeparatedSequences.CombinedConstants.propagatorDecay L
  coarseRate := SeparatedSequences.CombinedConstants.inverseDecay L
  extRate := SeparatedSequences.CombinedConstants.halfInverseDecay L
  coarseLowerBound := SeparatedSequences.CombinedConstants.compressedCoercivity
  treeLowerBound := SeparatedSequences.CombinedConstants.energyCoercivity
  K := SeparatedSequences.CombinedConstants.mainConst L
  Kα := SeparatedSequences.CombinedConstants.holderConst L
  Kε := SeparatedSequences.CombinedConstants.gradConst L
  Kαε := SeparatedSequences.CombinedConstants.gradHolderConst L
structure ClassData.MeetsSizeLowerBounds (C : ClassData) : Prop where
  blockLower_le : SeparatedSequences.CombinedConstants.blockLower C.L ≤ (C.blockSize : ℝ)
  gapLower_le : SeparatedSequences.CombinedConstants.gapLower C.L ≤ (C.gapSize : ℝ) * (C.blockSize : ℝ)
end YangMills.Construction.SeparatedClasses
end
