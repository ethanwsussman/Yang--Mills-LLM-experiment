import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
namespace NestedRegions
variable {𝒮 : NestedRegions} {E : Type} [SeminormedAddCommGroup E]
def supSite (f : 𝒮.FineSite → E) : ℝ := ⨆ x, ‖f x‖
def supBond (f : 𝒮.FineBond → E) : ℝ := ⨆ b, ‖f b‖
def supTensor {r : ℕ} (J : (Fin r → Fin 4) → 𝒮.FineBond → E) : ℝ := ⨆ ν, supBond (J ν)
def holderSite (α lam : ℝ) (f : 𝒮.FineSite → E) : ℝ :=
  sSup {r | ∃ x x' : 𝒮.FineSite, 0 < siteLOneDist x x' ∧ siteLOneDist x x' ≤ lam ∧
    r = (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖}
def holderBond (α lam : ℝ) (f : 𝒮.FineBond → E) : ℝ :=
  sSup {r | ∃ b b' : 𝒮.FineBond, b.dir = b'.dir ∧
    0 < siteLOneDist b.source b'.source ∧ siteLOneDist b.source b'.source ≤ lam ∧
    r = (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖}
def holderTensor {r : ℕ} (α lam : ℝ) (J : (Fin r → Fin 4) → 𝒮.FineBond → E) : ℝ :=
  ⨆ ν, holderBond α lam (J ν)
def holderBondOne (α : ℝ) (f : 𝒮.FineBond → E) : ℝ := holderBond α 1 f
def holderTensorOne {r : ℕ} (α : ℝ) (J : (Fin r → Fin 4) → 𝒮.FineBond → E) : ℝ :=
  holderTensor α 1 J
def linftyBond (f : 𝒮.FineBond → E) : ℝ := supBond f
def linftyTensor {r : ℕ} (J : (Fin r → Fin 4) → 𝒮.FineBond → E) : ℝ := supTensor J
def ltwoSite (f : 𝒮.FineSite → ℝ) : ℝ := siteNorm f
def ltwoBond (f : 𝒮.FineBond → ℝ) : ℝ := bondL2 f
def ltwoTensor {r : ℕ} (J : 𝒮.Tensor r) : ℝ := tensorL2 J
def cubeHalfSide (o : 𝒮.Point) (lam : ℝ) : Set 𝒮.Point := cubeAt o (2 * lam)
def smulSiteBond {R : Type} [SMul R E] (φ : 𝒮.FineSite → R) (f : 𝒮.FineBond → E) :
    𝒮.FineBond → E :=
  fun b => φ b.source • f b
def smulSiteTensor {R : Type} [SMul R E] {r : ℕ} (φ : 𝒮.FineSite → R)
    (J : (Fin r → Fin 4) → 𝒮.FineBond → E) : (Fin r → Fin 4) → 𝒮.FineBond → E :=
  fun ν => smulSiteBond φ (J ν)
def restrictBonds (X : Set 𝒮.Point) (f : 𝒮.FineBond → E) : 𝒮.FineBond → E :=
  indicator {b | AnchoredIn X b} f
def restrictTensor {r : ℕ} (X : Set 𝒮.Point) (J : (Fin r → Fin 4) → 𝒮.FineBond → E) :
    (Fin r → Fin 4) → 𝒮.FineBond → E :=
  fun ν => restrictBonds X (J ν)
end NestedRegions
end YangMills.Construction.RegionSequence
