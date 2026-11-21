import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ShiftedFieldGauge
open PeriodicOperators
open BackgroundJets (gaugeFieldOfForm)
def ShiftCommutes : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (k : ℕ) (n : Fin 4 → ℤ)
    (ζ : (remainderIndex L k).Carrier → ℂ) (b : Edge L k 0),
    gaugeFieldOfForm L k (shiftField (remainderIndex L k) n ζ)
      (edgeImage (intShift n) b) = gaugeFieldOfForm L k ζ b
end YangMills.Construction.Tower.FullSpace.ShiftedFieldGauge
end
