import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ReflectedFieldAgreesOnBox : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (y : F.Cell) (V : F.GaugeField F.top), 2 ≤ m → (∀ i, 2 * m + 2 < F.extent i) →
    AgreeOnBall (finiteCells F) V (finiteCells (reflectedFrame F m)) (reflectedField m y V) y 0 m
end YangMills.Construction.ColdStepAtMirrorFrames
end
