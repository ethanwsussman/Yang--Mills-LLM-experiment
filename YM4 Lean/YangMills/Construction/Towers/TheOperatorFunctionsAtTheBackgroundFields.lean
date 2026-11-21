import YangMills.Construction.Towers.PropertiesOfTheRescaledLattice
import YangMills.Construction.Towers.TheBackgroundFieldAmongTheTriples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets
open PeriodicOperators
namespace OpFunsAtBackground
open Tower.RescaledConditions (sumDiagScale)
def SaddleRelations : Prop :=
  ∀ (L : ℕ) (hpos : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ε : ℝ, 0 < ε ∧ ∀ a, IsSupBelow (remainderIndex L k) a ε →
      vectorOpFn L k hpos (PeriodicOperators.extendByZero (backgroundIndex L k hpos) a) =
          sumDiagScale ((finestMesh L k : ℂ) ^ 2) (finestMesh L k : ℂ)⁻¹ 1
            (finestMesh L k : ℂ) (rescaledOperators L k (gaugeFieldOfForm L k a)).saddleX ∧
        ghostOpFn L k hpos (PeriodicOperators.extendByZero (backgroundIndex L k hpos) a) =
          sumDiagScale ((finestMesh L k : ℂ) ^ 2) 1 1 ((finestMesh L k : ℂ) ^ 2)
            (rescaledOperators L k (gaugeFieldOfForm L k a)).saddleDelta
end OpFunsAtBackground
end YangMills.Construction.Tower.FullSpace.BackgroundJets
end
