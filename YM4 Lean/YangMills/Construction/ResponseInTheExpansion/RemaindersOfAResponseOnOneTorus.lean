import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrame
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps BlockAverages ColdStepAtMirrorFrames WeightedResponses
def remainderOnFrame {L t : ℕ} [NeZero L] (P : ColdResponse L t) (F : BlockFrame) (m : ℕ) [NeZero m]
    (h : PlaquetteWeight (fineSide L t m)) : F.Site F.depth → F.GaugeField F.depth → ℝ :=
  fun y W => responseRemainder P m (toTorusSite m y) h (restrictToTorus m W)
def weightedCenteredOnFrame (f : LocalDensity) (F : BlockFrame) (m : ℕ) [NeZero m] (w : F.Site F.depth → ℝ) :
    F.Site F.depth → F.GaugeField F.depth → ℝ :=
  fun y W => w y * centered f m (toTorusSite m y) (restrictToTorus m W)
def ResponseRemaindersOnTorus : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (t : ℕ) (F : BlockFrame) (m : ℕ) [NeZero m] (δ : ℝ),
    (∀ s : ℕ, torusDecayFactor ℓ.side δ s = ℓ.weight s) →
    (∀ i, F.period F.depth i = m) → ℓ.n₀ ≤ m →
    (∀ (K : ResponseParameters) (P : ColdResponse ℓ.side t),
      (∀ (y : TorusSite m) (g : TorusSite m → UnitQuaternion) (W : TorusField m), IsCold ℓ.threshold W →
        ∀ h : PlaquetteWeight (fineSide ℓ.side t m),
        P m y (gaugeTransform g W) h = P m y W h) →
      RemainderBounds ℓ K t P → ∀ h : PlaquetteWeight (fineSide ℓ.side t m),
      IsTorusRemainder ℓ.side ℓ.threshold δ (K.Kc * weightLipschitz ℓ.side t h)
        (K.Kc * weightLipschitz ℓ.side t h / K.η₃) (remainderOnFrame P F m h)) ∧
    ∀ (E E₃ B : ℝ) (f : LocalDensity) (w : F.Site F.depth → ℝ), ColdDensityBounds ℓ E E₃ f → 0 ≤ B →
      (∀ y, |w y| ≤ B) →
      IsTorusRemainder ℓ.side ℓ.threshold δ (B * E) (B * E₃) (weightedCenteredOnFrame f F m w)
end YangMills.Construction.ResponseInTheExpansion
end
