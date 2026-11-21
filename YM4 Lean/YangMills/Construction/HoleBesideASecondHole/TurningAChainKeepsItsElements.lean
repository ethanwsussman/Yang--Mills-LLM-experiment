import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace ChainGauges
open BlockAverages LumpContours
variable {F : BlockFrame}
def pointAtLevel (i : ℕ) (x : F.Site F.depth) : F.Site i :=
  siteOfCoords i fun l => (F.blockSide : ℤ) ^ (F.depth - i) * siteCoords x l
open Classical in
def extendGauge (γ : F.Site F.depth → UnitQuaternion) (i : ℕ) (z : F.Site i) : UnitQuaternion :=
  if h : ∃ x, pointAtLevel i x = z then γ h.choose else 1
def gaugeChain (γ : F.Site F.depth → UnitQuaternion) (U : F.FieldChain) : F.FieldChain := fun i =>
  if i ≤ F.depth then gaugeTransform (extendGauge γ i) (U i) else U i
def GaugeChainPreservesEnergy : Prop :=
  ∀ (F : BlockFrame) (γ : F.Site F.depth → UnitQuaternion) (U : F.FieldChain), 0 < F.blockSide →
    (∀ i, 0 < F.extent i) →
    gaugeChain γ U F.depth = gaugeTransform γ (U F.depth) ∧
    (∀ p, plaquetteDefect (gaugeChain γ U F.depth) p = plaquetteDefect (U F.depth) p) ∧
    ∀ (a : ℝ) (Y : Finset (F.Site F.depth)), cutChainEnergy a F.depth Y (gaugeChain γ U) = cutChainEnergy a F.depth Y U
end ChainGauges
end YangMills.Construction
end
