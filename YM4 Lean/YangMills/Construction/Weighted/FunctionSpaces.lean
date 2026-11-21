import YangMills.Construction.Weighted.BareLatticeBonds
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Weighted
namespace TorusData
variable (D : TorusData)
def functionsVanishingOff (E : Set D.BareSite) : Submodule ℝ (D.BareSite → ℝ) where
  carrier := {f | ∀ x, x ∉ E → f x = 0}
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]
variable {D}
def bondDiff (f : D.BareSite → ℝ) (b : D.Bond) : ℝ := f b.target - f b.source
def bondGrad (f : D.BareSite → ℝ) (b : D.Bond) : ℝ :=
  (D.scale 0)⁻¹ * bondDiff f b
def siteNorm (E : Set D.BareSite) (f : D.BareSite → ℝ) : ℝ :=
  Real.sqrt (D.scale 0 ^ 4 * ∑ᶠ x ∈ E, f x ^ 2)
def bondNorm (S : Set D.Bond) (A : D.Bond → ℝ) : ℝ :=
  Real.sqrt (D.scale 0 ^ 4 * ∑ᶠ b ∈ S, A b ^ 2)
end TorusData
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def bareSpace : Submodule ℝ (D.BareSite → ℝ) :=
  D.functionsVanishingOff (D.bareSites (B.stage 0))
abbrev LayerFn : Type := ↥B.allSites → ℝ
def bareInner (f g : D.BareSite → ℝ) : ℝ :=
  D.scale 0 ^ 4 * ∑ᶠ x ∈ D.bareSites (B.stage 0), f x * g x
def layerInner (w v : B.LayerFn) : ℝ :=
  ∑ᶠ y : ↥B.allSites, B.siteScale y ^ 4 * (w y * v y)
def bareSpaceNorm (f : D.BareSite → ℝ) : ℝ := Real.sqrt (B.bareInner f f)
def layerSpaceNorm (w : B.LayerFn) : ℝ := Real.sqrt (B.layerInner w w)
def bareSpaceOn (W : Set D.Space) : Submodule ℝ (D.BareSite → ℝ) :=
  B.bareSpace ⊓ D.functionsVanishingOff (D.bareSites W)
def layerSpaceOn (W : Set D.Space) : Submodule ℝ B.LayerFn where
  carrier := {w | ∀ y : ↥B.allSites, (y : D.Space) ∉ B.sitesIn W → w y = 0}
  add_mem' := by
    intro w v hw hv y hy
    simp [hw y hy, hv y hy]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c w hw y hy
    simp [hw y hy]
def scaleOnBare : ↥B.bareSpace →ₗ[ℝ] ↥B.bareSpace where
  toFun f := ⟨fun x => B.bareScale x * (f : D.BareSite → ℝ) x, fun x hx => by
    have h : (f : D.BareSite → ℝ) x = 0 := f.2 x hx
    simp [h]⟩
  map_add' f g := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def scaleOnLayer : B.LayerFn →ₗ[ℝ] B.LayerFn where
  toFun w := fun y => B.siteScale y * w y
  map_add' w v := by
    ext y
    simp [mul_add]
  map_smul' c w := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
end SeparatedChain
end Weighted
end YangMills.Construction
