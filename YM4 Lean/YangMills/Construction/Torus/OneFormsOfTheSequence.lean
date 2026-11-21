import YangMills.Construction.Torus.CoercivityAndWeightedBoundsOfAnAdmissiblePairProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
theorem TorusData.bond_finite (D : TorusData) : Finite D.Bond := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bond_finite <;> assumption
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
abbrev regionSites : Set D.BareSite := D.bareSites (B.stage 0)
abbrev starBonds : Set D.Bond := TorusData.bondsMeeting B.regionSites
abbrev OneForm : Type := ↥B.starBonds → ℝ
def oneFormInner (A A' : B.OneForm) : ℝ :=
  D.scale 0 ^ 4 * ∑ᶠ b : ↥B.starBonds, A b * A' b
def grad : ↥B.bareSpace →ₗ[ℝ] B.OneForm where
  toFun f b := TorusData.bondGrad (f : D.BareSite → ℝ) b
  map_add' f g := by
    funext b
    simp only [TorusData.bondGrad, TorusData.bondDiff, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c f := by
    funext b
    simp only [TorusData.bondGrad, TorusData.bondDiff, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring
def IsGradAdjoint (T : B.OneForm →ₗ[ℝ] ↥B.bareSpace) : Prop :=
  ∀ (f : ↥B.bareSpace) (A : B.OneForm),
    B.oneFormInner (B.grad f) A = B.bareInner f (T A)
def gradAdjoint : B.OneForm →ₗ[ℝ] ↥B.bareSpace :=
  Classical.epsilon B.IsGradAdjoint
open Classical in
def basePoint (b : ↥B.starBonds) : D.BareSite :=
  if (b : D.Bond).source ∈ B.regionSites then (b : D.Bond).source
  else (b : D.Bond).target
def IsAttachedTo (b : ↥B.starBonds) (y : ↥B.allSites) : Prop :=
  B.basePoint b ∈ B.block y
def siteIndicator (x' : ↥B.regionSites) : ↥B.bareSpace :=
  ⟨({(x' : D.BareSite)} : Set D.BareSite).indicator 1, fun x hx =>
    indicator_of_notMem (fun h => hx (by rw [mem_singleton_iff.1 h]; exact x'.2)) _⟩
open Classical in
def bondIndicator (b' : ↥B.starBonds) : B.OneForm := fun b => if b = b' then 1 else 0
def siteKernel (K : Module.End ℝ ↥B.bareSpace) (x : D.BareSite)
    (x' : ↥B.regionSites) : ℝ :=
  (K (B.siteIndicator x') : D.BareSite → ℝ) x
def gradKernel (K : Module.End ℝ ↥B.bareSpace) (b : ↥B.starBonds)
    (x' : ↥B.regionSites) : ℝ :=
  B.grad (K (B.siteIndicator x')) b
def kernelGradAdjoint (K : Module.End ℝ ↥B.bareSpace) (x : D.BareSite)
    (b' : ↥B.starBonds) : ℝ :=
  (K (B.gradAdjoint (B.bondIndicator b')) : D.BareSite → ℝ) x
def gradKernelGradAdjoint (K : Module.End ℝ ↥B.bareSpace) (b b' : ↥B.starBonds) : ℝ :=
  B.grad (K (B.gradAdjoint (B.bondIndicator b'))) b
end SeparatedChain
end YangMills.Construction.Weighted
