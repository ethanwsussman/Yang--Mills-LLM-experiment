import YangMills.Construction.Torus.AdmissiblePairs
import YangMills.Construction.Weighted.LayerOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted.SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def admissibleScaledMatrix (W : Set D.Space) (𝔟 : Set D.Bond) : B.LayerMat :=
  B.matrixOf (B.extendByZeroFromBlocks W (B.admissibleScaledGreenSq W 𝔟))
def blockIndicatorIn (W : Set D.Space) (y : D.Space) : ↥(B.bareSpaceOn W) :=
  ⟨(D.bareSites (B.stage 0) ∩ D.bareSites W).indicator (B.blockIndicator y),
    fun _ hx => indicator_of_notMem (fun h => hx h.1) _,
    fun _ hx => indicator_of_notMem (fun h => hx h.2) _⟩
def AdmissibleScaledMatrixEq (W : Set D.Space) (𝔟 : Set D.Bond) : Prop :=
  ∀ y y' : ↥B.allSites, (y : D.Space) ∈ B.sitesIn W → (y' : D.Space) ∈ B.sitesIn W →
    B.admissibleScaledMatrix W 𝔟 y y' =
      B.siteScale y ^ (-4 : ℤ) * B.siteScale y' ^ (-4 : ℤ) *
        B.bareInner (B.admissibleGreen W 𝔟 (B.blockIndicatorIn W y))
          (B.admissibleGreen W 𝔟 (B.blockIndicatorIn W y'))
end YangMills.Construction.Weighted.SeparatedChain
