import YangMills.Construction.ColdStepAtMirrorFrames.MirrorOfAMovedTopForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
open Classical in
def sourceOffset (m : ℕ) (z : (reflectedFrame F m).Cell) (i : Fin 4) : Fin 4 → ℤ :=
  if IsForwardOriented m z i then fun l => reflectCoord m (z l).valMinAbs
  else fun l => reflectCoord m ((z l).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) l)
def reflectedGauge (m : ℕ) (y : F.Cell) (γ : F.Cell → UnitQuaternion) (z : (reflectedFrame F m).Cell) : UnitQuaternion :=
  γ (y + siteOfCoords F.top fun l => reflectCoord m (z l).valMinAbs)
open Classical in
def ReflectedBondReadsBox : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (z : (reflectedFrame F m).Cell) (i : Fin 4), 0 < m →
    BondWithinRadius m (sourceOffset m z i, i) ∧ ∀ (y : F.Cell) (V : F.GaugeField F.top),
      reflectedField m y V z i = if IsForwardOriented m z i then V (y + siteOfCoords F.top (sourceOffset m z i)) i
        else (V (y + siteOfCoords F.top (sourceOffset m z i)) i)⁻¹
def ReflectedFieldOfGaugedTop : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (y : F.Cell) (V : F.GaugeField F.top) (γ : F.Cell → UnitQuaternion), 0 < m →
    reflectedField m y (gaugeTransform γ V) = gaugeTransform (reflectedGauge m y γ) (reflectedField m y V)
def ReflectedFieldOfTranslatedCentre : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (y h : F.Cell) (V : F.GaugeField F.top),
    reflectedField m (y + h) (translateField h V) = reflectedField m y V
def reflectedFieldReadsBox : Prop :=
  ReflectedBondReadsBox ∧ ReflectedFieldOfGaugedTop ∧ ReflectedFieldOfTranslatedCentre
end ColdStepAtMirrorFrames
end YangMills.Construction
end
