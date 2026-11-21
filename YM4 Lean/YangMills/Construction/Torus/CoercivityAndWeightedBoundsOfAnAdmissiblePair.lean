import YangMills.Construction.Torus.AdmissiblePairs
import YangMills.Construction.Weighted.GreenSquareConstants
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def mulOnBare (W : Set D.Space) (g : D.Space → ℝ) :
    Module.End ℝ ↥(B.bareSpaceOn W) where
  toFun u :=
    ⟨fun x => g (x : D.Space) * (u : D.BareSite → ℝ) x,
      fun x hx => by
        have hzero : (u : D.BareSite → ℝ) x = 0 := u.2.1 x hx
        simp [hzero],
      fun x hx => by
        have hzero : (u : D.BareSite → ℝ) x = 0 := u.2.2 x hx
        simp [hzero]⟩
  map_add' u v := by
    ext x
    simp [mul_add]
  map_smul' c u := by
    ext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def conjAdmissibleOp (W : Set D.Space) (b : Set D.Bond) (θ : D.Space → ℝ) :
    Module.End ℝ ↥(B.bareSpaceOn W) :=
  B.mulOnBare W (fun x => Real.exp (θ x)) * B.admissibleOp W b *
    B.mulOnBare W (fun x => Real.exp (-θ x))
def conjAdmissibleGreen (W : Set D.Space) (b : Set D.Bond) (θ : D.Space → ℝ) :
    Module.End ℝ ↥(B.bareSpaceOn W) :=
  B.mulOnBare W (fun x => Real.exp (θ x)) * B.admissibleGreen W b *
    B.mulOnBare W (fun x => Real.exp (-θ x))
def admissibleGreenExt (W : Set D.Space) (b : Set D.Bond) (u : ↥B.bareSpace) :
    ↥B.bareSpace :=
  B.bareSpaceOnIncl W (B.admissibleGreen W b (B.restrictBare W u))
def invScaleNorm (u : ↥B.bareSpace) : ℝ :=
  B.bareSpaceNorm (Ring.inverse B.scaleOnBare u : ↥B.bareSpace)
def scaleNorm (u : ↥B.bareSpace) : ℝ :=
  B.bareSpaceNorm (B.scaleOnBare u : ↥B.bareSpace)
def AdmissibleFormCoercive (W : Set D.Space) (b : Set D.Bond) : Prop :=
  (∀ u : ↥(B.bareSpaceOn W),
      coercivityConst D.L * B.invScaleNorm (B.bareSpaceOnIncl W u) ^ 2 ≤
        B.admissibleForm W b u u) ∧
    (∀ u v : ↥(B.bareSpaceOn W),
      B.bareInner (B.admissibleOp W b u) v = B.bareInner u (B.admissibleOp W b v)) ∧
    ∀ u : ↥(B.bareSpaceOn W), u ≠ 0 → 0 < B.bareInner u (B.admissibleOp W b u)
def IsWeightedLipschitz (θ : D.Space → ℝ) : Prop :=
  ∀ x x' : D.Space, |θ x - θ x'| ≤ greenDecayRate 4 D.L * B.weightedDistance x x'
def ConjAdmissibleBounds (W : Set D.Space) (b : Set D.Bond) (θ : D.Space → ℝ) : Prop :=
  (∀ u : ↥(B.bareSpaceOn W),
      1 / 2 * TorusData.bondNorm b (TorusData.bondGrad (u : D.BareSite → ℝ)) ^ 2 +
          1 / 4 * coercivityConst D.L *
            B.invScaleNorm (B.bareSpaceOnIncl W u) ^ 2 ≤
        B.bareInner u (B.conjAdmissibleOp W b θ u)) ∧
    ∀ u : ↥(B.bareSpaceOn W),
      B.invScaleNorm (B.bareSpaceOnIncl W (B.conjAdmissibleGreen W b θ u)) ≤
          4 / coercivityConst D.L * B.scaleNorm (B.bareSpaceOnIncl W u) ∧
        TorusData.bondNorm b
            (TorusData.bondGrad
              (B.conjAdmissibleGreen W b θ u : D.BareSite → ℝ)) ≤
          Real.sqrt (8 / coercivityConst D.L) * B.scaleNorm (B.bareSpaceOnIncl W u)
def AdmissibleGreenDecay (W : Set D.Space) (b : Set D.Bond) : Prop :=
  ∀ y' ∈ B.sitesIn W, ∀ u : ↥B.bareSpace,
    (∀ x, x ∉ B.block y' → (u : D.BareSite → ℝ) x = 0) → ∀ y'' ∈ B.allSites,
      B.localAdmissibleNorm (B.admissibleGreenExt W b u) b y'' ≤
          weightedBoundConst 4 D.L * B.siteScale y' *
            Real.exp (-(greenDecayRate 4 D.L * B.weightedDistance y'' y')) * B.bareSpaceNorm u ∧
        TorusData.siteNorm (B.block y'') (B.admissibleGreenExt W b u : D.BareSite → ℝ) ≤
          weightedBoundConst 4 D.L * B.siteScale y'' * B.siteScale y' *
            Real.exp (-(greenDecayRate 4 D.L * B.weightedDistance y'' y')) * B.bareSpaceNorm u
end SeparatedChain
def CoercivityWeightedBounds : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D) (W : Set D.Space) (b : Set D.Bond),
    B.IsAdmissiblePair W b →
      B.AdmissibleFormCoercive W b ∧
        (∀ θ : D.Space → ℝ, B.IsWeightedLipschitz θ → B.ConjAdmissibleBounds W b θ) ∧
        B.AdmissibleGreenDecay W b
end YangMills.Construction.Weighted
