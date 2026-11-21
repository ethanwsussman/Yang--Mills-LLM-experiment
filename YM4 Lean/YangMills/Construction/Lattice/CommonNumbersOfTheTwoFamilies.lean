import YangMills.Construction.Lattice.ChainsInTheToolbox
import YangMills.Construction.Lattice.ChainsOfBonds
import YangMills.Construction.Lattice.LinearPartOfOneStepInTheToolbox
import YangMills.Construction.Lattice.OneStepBoundsOfTheGaugeFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
structure PrimaryConstants where
  radius : ℝ
  bondRadius : ℝ
  curvatureBound : ℝ
  boundConstant : ℝ
  growthConstant : ℝ
  growthRadius : ℝ
  curvatureThreshold : ℝ
  remainderConstant : ℝ
  deviationConstant : ℝ
  averageRadius : ℝ
  averageThreshold : ℝ
  averageRemainderConstant : ℝ
  averageDerivativeConstant : ℝ
  accumulatedFactorConstant : ℝ
  angle : ℝ
  recursionConstant : ℝ
  recursionRadius : ℝ
  gaugeThreshold : ℝ
  gaugeRadius : ℝ
  gaugeConstant : ℝ
  holonomyConstant : ℝ
structure AuxiliaryConstants where
  radius : ℝ
  bondRadius : ℝ
  curvatureBound : ℝ
  boundConstant : ℝ
  growthConstant : ℝ
  growthRadius : ℝ
  curvatureThreshold : ℝ
  remainderConstant : ℝ
  deviationConstant : ℝ
  angle : ℝ
  recursionConstant : ℝ
  recursionRadius : ℝ
  holonomyConstant : ℝ
def primaryConstants (L : ℕ) : PrimaryConstants where
  radius := stepRadius L
  bondRadius := stepBondRadius L
  curvatureBound := stepCurvatureBound L
  boundConstant := stepBallConstant L
  growthConstant := curvatureGrowthConst L
  growthRadius := curvatureGrowthRadius L
  curvatureThreshold := smallCurvatureThreshold L
  remainderConstant := stepBondRemainderConst L
  deviationConstant := stepCurvatureDeviationConst L
  averageRadius := straightenedRadius L
  averageThreshold := straightenedCurvatureThreshold L
  averageRemainderConstant := straightenedRemainderConstant L
  averageDerivativeConstant := straightenedDerivConstant L
  accumulatedFactorConstant := accumulatedFactorConstant L
  angle := recursionStepAngle L
  recursionConstant := recursionStepConstant L
  recursionRadius := recursionStepRadius
  gaugeThreshold := orderKCurvatureThreshold L
  gaugeRadius := orderKGaugeRadius L
  gaugeConstant := orderKGaugeConstant L
  holonomyConstant := chainHolonomyConstant L
def auxiliaryConstants (L : ℕ) : AuxiliaryConstants where
  radius := admissibleStepRadius L
  bondRadius := bondFieldRadius L
  curvatureBound := plaquetteSmallness L
  boundConstant := stepBoundConstant L
  growthConstant := plaquetteGrowthConstant L
  growthRadius := plaquetteGrowthRadius L
  curvatureThreshold := smallPlaquetteThreshold L
  remainderConstant := stepRemainderConstant L
  deviationConstant := stepDeviationConstant L
  angle := gaugeAngleThreshold L
  recursionConstant := gaugeStepMultiplier L
  recursionRadius := universalDeviationBound
  holonomyConstant := chainTransportConstant L
namespace SharedConstants
def radius (L : ℕ) : ℝ := min (primaryConstants L).radius (auxiliaryConstants L).radius
def curvatureBound (L : ℕ) : ℝ :=
  min (Averaging.smoothingRadius L / 2)
    (min ((Averaging.SingleStep.loopVariableConstant L)⁻¹ / 2) (radius L / (6 * Real.pi * (L : ℝ))))
def growthConstant (L : ℕ) : ℝ := max (primaryConstants L).growthConstant (auxiliaryConstants L).growthConstant
def growthRadius (L : ℕ) : ℝ := min (primaryConstants L).growthRadius (auxiliaryConstants L).growthRadius
def curvatureThreshold (L : ℕ) : ℝ := min (growthRadius L / 2) ((L : ℝ) ^ 2 / (4 * growthConstant L))
def recursionConstant (L : ℕ) : ℝ :=
  max (primaryConstants L).recursionConstant (auxiliaryConstants L).recursionConstant
def averageThreshold (L : ℕ) : ℝ := min (primaryConstants L).averageThreshold (curvatureThreshold L)
def gaugeThreshold (L : ℕ) : ℝ :=
  min (averageThreshold L) ((L : ℝ) ^ 2 / (4 * recursionConstant L * (2 + 32 * recursionConstant L)))
end SharedConstants
end YangMills.Construction.PeriodicLattice
