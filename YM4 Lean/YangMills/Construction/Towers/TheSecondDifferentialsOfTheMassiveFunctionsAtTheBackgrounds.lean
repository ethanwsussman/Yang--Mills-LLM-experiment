import YangMills.Construction.Towers.TheDilationOfTheMassiveFields
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.BackgroundHessians
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs
open Tower.MassiveOpFunctions.Scaling
open PeriodicOperators.Tempered (EventuallyForSides complexHessian)
open Tower.FullSpace.BackgroundJets
def backgroundModeOnQuotient (L k n : ℕ) (q : Fin 4 → ℂ) (μ : Fin 4) :
    (colourEdges L k 0).QuotMod (2 * L ^ n) → ℂ :=
  descendField (colourEdges L k 0) (2 * L ^ n)
    (blochWave (colourEdges L k 0) q (scaledResponseField L k q μ))
def HessianRelation : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ z : ℝ, 0 < z →
    EventuallyForSides L fun n =>
      ∀ (N : ℕ) (e : Fin N ≃ (colourEdges L k 0).QuotMod (2 * L ^ n)),
        ∀ p ∈ dualLattice (2 * L ^ n), toComplexVec p ∈ momentumPolydisc stripHalfWidth →
          ∀ μ₁ μ₂ : Fin 4,
            logDetSecondDeriv (colourEdges L k 0) (colourVertices L k 0)
                (Tower.MassiveOpFunctions.scaledVertexOpFun L k z) e
                (backgroundModeOnQuotient L k n (toComplexVec p) μ₁)
                (backgroundModeOnQuotient L k n (-toComplexVec p) μ₂) -
              1 / 2 * logDetSecondDeriv (colourEdges L k 0) (colourEdges L k 0)
                (Tower.MassiveOpFunctions.scaledEdgeOpFun L k z) e
                (backgroundModeOnQuotient L k n (toComplexVec p) μ₁)
                (backgroundModeOnQuotient L k n (-toComplexVec p) μ₂) =
            (((Tower.finestMesh L k : ℝ) : ℂ)) ^ 2 *
              ∑ m ∈ Tower.PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
                Tower.MassiveOpFunctions.backgroundCoeff L k (toComplexVec p) μ₁ ρ m *
                  Tower.MassiveOpFunctions.backgroundCoeff L k (-toComplexVec p) μ₂ σ (-m) *
                  complexHessian (Tower.massiveFieldFamily L (Tower.finestMesh L k ^ 2 * z)) (n + k)
                    (PeriodicOperators.Tempered.fourierModeForm L (n + k) 2
                      (Tower.finestMesh L k • shiftedMomentum p m) ρ)
                    (PeriodicOperators.Tempered.fourierModeForm L (n + k) 2
                      (-(Tower.finestMesh L k • shiftedMomentum p m)) σ)
end YangMills.Construction.Tower.MassiveOpFunctions.BackgroundHessians
end
