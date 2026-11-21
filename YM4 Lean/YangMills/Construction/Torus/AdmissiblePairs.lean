import YangMills.Construction.Torus.OperatorsOfTheSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted.SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def IsAdmissiblePair (W : Set D.Space) (E : Set D.Bond) : Prop :=
  B.IsBlockUnion W ∧ TorusData.bondsWithin (D.bareSites W) ⊆ E ∧
    E ⊆ TorusData.bondsMeeting (D.bareSites W)
def bareSpaceOnIncl (W : Set D.Space) : ↥(B.bareSpaceOn W) →ₗ[ℝ] ↥B.bareSpace :=
  Submodule.inclusion inf_le_left
def admissibleForm (W : Set D.Space) (E : Set D.Bond) (f f' : ↥(B.bareSpaceOn W)) : ℝ :=
  D.scale 0 ^ 4 * ∑ᶠ b ∈ E,
      TorusData.bondGrad (f : D.BareSite → ℝ) b * TorusData.bondGrad (f' : D.BareSite → ℝ) b +
    ∑ᶠ y ∈ B.sitesIn W,
      avgWeight D.L (B.level y) * B.siteScale y ^ 2 *
        (B.layerEval (B.avgOp (B.bareSpaceOnIncl W f)) y *
          B.layerEval (B.avgOp (B.bareSpaceOnIncl W f')) y)
def IsAdmissibleFormOp (W : Set D.Space) (E : Set D.Bond)
    (T : Module.End ℝ ↥(B.bareSpaceOn W)) : Prop :=
  (∀ f g : ↥(B.bareSpaceOn W), B.bareInner (T f) g = B.bareInner f (T g)) ∧
    ∀ f g : ↥(B.bareSpaceOn W), B.bareInner f (T g) = B.admissibleForm W E f g
def admissibleOp (W : Set D.Space) (E : Set D.Bond) : Module.End ℝ ↥(B.bareSpaceOn W) :=
  Classical.epsilon (B.IsAdmissibleFormOp W E)
def admissibleGreen (W : Set D.Space) (E : Set D.Bond) :
    Module.End ℝ ↥(B.bareSpaceOn W) :=
  Ring.inverse (B.admissibleOp W E)
def restrictBare (W : Set D.Space) : ↥B.bareSpace →ₗ[ℝ] ↥(B.bareSpaceOn W) where
  toFun f :=
    ⟨(D.bareSites W).indicator (f : D.BareSite → ℝ),
      fun x hx => by simp [indicator, f.2 x hx], fun _ hx => indicator_of_notMem hx _⟩
  map_add' f g := by
    ext x
    by_cases h : x ∈ D.bareSites W <;> simp [h]
  map_smul' c f := by
    ext x
    by_cases h : x ∈ D.bareSites W <;> simp [h]
def restrictLayer (W : Set D.Space) : B.LayerFn →ₗ[ℝ] ↥(B.layerSpaceOn W) where
  toFun w :=
    ⟨{y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}.indicator w,
      fun _ hy =>
        indicator_of_notMem (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}) hy w⟩
  map_add' w w' := by
    ext y
    by_cases h : (y : D.Space) ∈ B.sitesIn W <;> simp [indicator, h]
  map_smul' c w := by
    ext y
    by_cases h : (y : D.Space) ∈ B.sitesIn W <;> simp [indicator, h]
def admissibleAvgGreenSq (W : Set D.Space) (E : Set D.Bond) :
    Module.End ℝ ↥(B.layerSpaceOn W) :=
  B.restrictLayer W ∘ₗ B.avgOp ∘ₗ B.bareSpaceOnIncl W ∘ₗ
    (B.admissibleGreen W E * B.admissibleGreen W E) ∘ₗ B.restrictBare W ∘ₗ
      B.avgOpAdjoint ∘ₗ (B.layerSpaceOn W).subtype
def scaleOnLayerOn (W : Set D.Space) : Module.End ℝ ↥(B.layerSpaceOn W) :=
  B.scaleOnLayer.restrict fun w hw y hy => by
    change B.siteScale y * w y = 0
    rw [hw y hy, mul_zero]
def admissibleScaledGreenSq (W : Set D.Space) (E : Set D.Bond) :
    Module.End ℝ ↥(B.layerSpaceOn W) :=
  Ring.inverse (B.scaleOnLayerOn W) ^ 2 * B.admissibleAvgGreenSq W E *
    Ring.inverse (B.scaleOnLayerOn W) ^ 2
def scaledGreenSq : Module.End ℝ B.LayerFn :=
  Ring.inverse B.scaleOnLayer ^ 2 * B.avgGreenSq * Ring.inverse B.scaleOnLayer ^ 2
def localAdmissibleNorm (u : ↥B.bareSpace) (E : Set D.Bond) (y : D.Space) : ℝ :=
  Real.sqrt
    (TorusData.siteNorm (B.block y) (Ring.inverse B.scaleOnBare u : ↥B.bareSpace) ^ 2 +
      TorusData.bondNorm (E ∩ B.blockBondSet y) (TorusData.bondGrad (u : D.BareSite → ℝ)) ^ 2)
end YangMills.Construction.Weighted.SeparatedChain
end
