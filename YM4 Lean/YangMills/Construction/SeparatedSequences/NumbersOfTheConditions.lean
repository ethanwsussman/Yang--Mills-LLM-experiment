import YangMills.Construction.Lattice.GreenOperatorsOfCubes
import YangMills.Construction.SeparatedSequences.InverseExpansionCutoff
import YangMills.Construction.SeparatedSequences.RatesOfTheInputsAndOfTheExpansion
import YangMills.Construction.SeparatedSequences.SiteSumThresholds
import YangMills.Construction.Weighted.CoverConstant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.CombinedConstants
def dirichletConsts (L : ℕ) : DirichletGreen.GreenConstants :=
  DirichletGreen.FourDimensional.constants L
def dirichletDecay (L : ℕ) : ℝ := (dirichletConsts L).δ₀
def dirichletGapLower (L : ℕ) : ℝ := (dirichletConsts L).rStar
def dirichletBlockLower (L : ℕ) : ℝ := (dirichletConsts L).mStar
def dirichletConst (L : ℕ) : ℝ := (dirichletConsts L).B
def dirichletHolderConst (L : ℕ) (α : ℝ) : ℝ :=
  if α = 0 then
    2 * (L : ℝ) * Real.exp (1 / 2 * dirichletDecay L * 4 * (2 * (L : ℝ) + 1)) * dirichletConst L
  else (dirichletConsts L).Bα α
def coverConstOf (L : ℕ) : ℝ := Weighted.coverConst 4 L
def expansionDecay (L : ℕ) : ℝ := Weighted.expansionDecayRate 4 L
def expansionGapLower (L : ℕ) : ℝ := Weighted.expansionSeparationFloor 4 L
def expansionConst (L : ℕ) : ℝ := Weighted.expansionConstBound 4 L (coverConstOf L)
def expansionBlockLower (L : ℕ) : ℝ :=
  Weighted.expansionBlockSizeFloor 4 L (coverConstOf L)
def cubeDecay (L : ℕ) : ℝ := CubeCovering.cubeDecayRate L
def cubeConsts (L : ℕ) : PeriodicLattice.DecayConstants := CubeCovering.cubeDecayConstants L
def propagatorConsts (L : ℕ) : Propagator.PropagatorConstants :=
  Propagator.SequenceOfRegions.chosenConstants L
def propagatorDecay (L : ℕ) : ℝ := SeparatedSequences.sequencePropagatorRate L
def propagatorConst (L : ℕ) : ℝ := (propagatorConsts L).B
def propagatorBlockLower (L : ℕ) : ℝ := (propagatorConsts L).blockLower
def propagatorGapLower (L : ℕ) : ℝ := (propagatorConsts L).gapLower
def propagatorHolderConst (L : ℕ) (α : ℝ) : ℝ := (propagatorConsts L).Bα α
def propagatorGradConst (L : ℕ) (ε : ℝ) : ℝ := (propagatorConsts L).Bε ε
def propagatorGradHolderConst (L : ℕ) (α ε : ℝ) : ℝ := (propagatorConsts L).Bαε α ε
def inverseDecay (L : ℕ) : ℝ := SeparatedSequences.propagatorInverseRate L
def halfInverseDecay (L : ℕ) : ℝ :=
  SeparatedSequences.halfInverseDecayRate 4 L (propagatorDecay L) (propagatorConst L)
def inverseConst (L : ℕ) : ℝ := SeparatedSequences.inverseKernelConstant 4 L
def fieldConst (L : ℕ) : ℝ :=
  SeparatedSequences.fieldKernelConstant 4 L (propagatorDecay L) (propagatorConst L)
def inverseGapLower (L : ℕ) : ℝ :=
  SeparatedSequences.gapBlockThreshold 4 L (propagatorDecay L) (propagatorConst L)
    (propagatorGapLower L)
def inverseBlockLower (L : ℕ) : ℝ :=
  SeparatedSequences.inverseExpansionBlockCutoff 4 L (propagatorDecay L) (propagatorConst L)
    (propagatorBlockLower L)
def compressedCoercivity : ℝ := SeparatedSequences.compressedGreenLowerBound 4 1
def energyCoercivity : ℝ := 1
def siteSumConst (L : ℕ) (a : ℝ) : ℝ := SeparatedSequences.siteSumMajorant 4 L a
def blockLower (L : ℕ) : ℝ :=
  max (dirichletBlockLower L) (max (expansionBlockLower L) (max (propagatorBlockLower L)
    (max (inverseBlockLower L) ((L : ℝ) ^ 2))))
def gapLower (L : ℕ) : ℝ :=
  max (dirichletGapLower L) (max (expansionGapLower L) (max (propagatorGapLower L)
    (max (inverseGapLower L) (8 * (4 * Real.log (L : ℝ) + 1) / propagatorDecay L))))
def mainConst (L : ℕ) : ℝ :=
  max ((L : ℝ) * Real.exp (1 / 2 * dirichletDecay L * 4) * dirichletConst L)
    (max (expansionConst L)
      (max (cubeConsts L).base
        (max (((L : ℝ) + 2) ^ 4 * (L : ℝ) ^ 2 * Real.exp (2 * propagatorDecay L * 4) *
            propagatorConst L)
          (max (Real.exp (1 / 2 * inverseDecay L * ((L : ℝ) + 1)) * inverseConst L)
            (2 * (L : ℝ) * Real.exp (halfInverseDecay L * 4) *
              Real.exp (1 / 2 * halfInverseDecay L * ((L : ℝ) + 1)) * fieldConst L)))))
def holderFactor (L : ℕ) : ℝ :=
  2 * 4 * (L : ℝ) ^ 2 * (1 + (L : ℝ) ^ 4) * Real.exp (propagatorDecay L * (4 + 1) * (L : ℝ)) *
    inverseConst L * siteSumConst L (1 / 4 * propagatorDecay L)
def holderConst (L : ℕ) (α : ℝ) : ℝ :=
  max (mainConst L)
    (max (dirichletHolderConst L α)
      (max ((cubeConsts L).holder α)
        (max (((L : ℝ) + 2) ^ 4 * Real.exp (propagatorDecay L * 4) * propagatorHolderConst L α)
          (Real.exp (1 / 2 * halfInverseDecay L * ((L : ℝ) + 1)) * holderFactor L *
            propagatorHolderConst L α))))
def gradConst (L : ℕ) (ε : ℝ) : ℝ :=
  max ((cubeConsts L).grad ε) (Real.exp (propagatorDecay L * 4) * propagatorGradConst L ε)
def gradHolderConst (L : ℕ) (α ε : ℝ) : ℝ :=
  max ((cubeConsts L).gradHolder α ε) (propagatorGradHolderConst L α ε)
end YangMills.Construction.SeparatedSequences.CombinedConstants
