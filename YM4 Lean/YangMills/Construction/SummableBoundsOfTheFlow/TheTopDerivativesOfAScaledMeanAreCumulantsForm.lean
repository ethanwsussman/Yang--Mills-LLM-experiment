import YangMills.Construction.SummableBoundsOfTheFlow.CumulantOfOneMore
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfTheScaledMeans
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaledVariables
variable {F : BlockAverages.BlockFrame}
def derivAlongSubset {k : ℕ} (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (I : Finset (Fin k)) : ℝ :=
  ColdStepAtMirrorFrames.bondDeriv G V (c ∘ I.orderEmbOfFin rfl) (X ∘ I.orderEmbOfFin rfl)
def topDerivCumulantEntries (a ρ lam : ℝ) (f : ColdStepAtMirrorFrames.LocalFamily) (law : StepLaw)
    (Ob : ℝ → ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F) → F.GaugeField F.top → ℝ)
    (l : ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions) (I : Finset (Fin k)) :
    Option (Finset (Fin k)) → ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F) → ℝ
  | none => fun ζ => derivAlongSubset (Ob l ζ) V c X I
  | some J => fun ζ => -derivAlongSubset (fun V' => rescaledLawExponent a ρ lam f l V' law ζ) V c X J
def topDerivsOfScaledMeanAreCumulants : Prop :=
  ForallSmoothObservables fun T _ _ l₁ f law _ _ V Ob k c X =>
    k ≤ 3 → ∀ l : ℝ, 0 < l → l ≤ l₁ →
      ColdStepAtMirrorFrames.bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X =
        ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset, ∑ π : Finpartition (Finset.univ \ I),
          Cumulants.jointCumulant (fun H => rescaledMean T.a T.ρA T.ballRadius T.lam l T.p f law V H)
            (insert none (π.parts.image some)) (topDerivCumulantEntries T.a T.ρA T.lam f law Ob l V c X I)
end YangMills.Construction.ScaledVariables
end
