import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
namespace YangMills.Construction.ColdStepAtMirrorFrames
def LimitFormVanishesOnLinearPotentials : Prop :=
  ∀ (P : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f : LocalDensity), P.Admissible →
    ColdExpansion P t x D f →
    ∃ q : BondBilinearForm,
      (∀ b b' X X', Filter.Tendsto
        (fun n => mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X']) Filter.atTop
        (𝓝 (q b b' X X'))) ∧
      ∀ Fm Fm' A A', IsAntisymmetricCurvature Fm → IsAntisymmetricCurvature Fm' → IsLinearPotential Fm A →
        IsLinearPotential Fm' A' → HasSum (fun p : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
          q p.1 p.2 (A p.1) (A' p.2)) 0
end YangMills.Construction.ColdStepAtMirrorFrames
end
