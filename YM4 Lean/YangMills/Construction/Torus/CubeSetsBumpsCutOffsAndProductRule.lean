import YangMills.Construction.Torus.CubesPartitionOfUnityAndCutSequencesOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus
def CubeBumpCutoffProperties : Prop :=
  ∀ (C : CubeGaugeSetting) (k : ℕ) (Q : C.data.CubeIndex), Q ∈ C.chain.cubesAt k →
    ScaleData.scaledCube Q 1 =
        ⋃₀ {q ∈ C.data.blockPartition k | IsCubeCorner (C.data.blockLength k) q Q.2} ∧
    (∃ g : ℝ → ℝ,
        (∀ x, ScaleData.bump Q x = g (torusSupNorm (x - Q.2))) ∧
        MapsTo g (Ici 0) (Icc 0 1) ∧
        (∀ r ∈ Ici (0 : ℝ), ∀ r' ∈ Ici (0 : ℝ),
          |g r - g r'| ≤ 6 * (ScaleData.cubeScale Q)⁻¹ * |r - r'|) ∧
        (∀ r ∈ Icc 0 (1 / 2 * ScaleData.cubeScale Q), g r = 1) ∧
        (∀ r ∈ Ici (2 / 3 * ScaleData.cubeScale Q), g r = 0)) ∧
    (∀ x ∈ ScaleData.scaledCube Q (1 / 2), ScaleData.bump Q x = 1) ∧
    (∀ x, ScaleData.bump Q x ≠ 0 → torusSupNorm (x - Q.2) < 2 / 3 * ScaleData.cubeScale Q) ∧
    (∀ x, 0 ≤ ScaleData.cutoffFn Q x ∧ ScaleData.cutoffFn Q x ≤ 1) ∧
    (∀ x ∈ ScaleData.scaledCube Q (4 / 3), ScaleData.cutoffFn Q x = 1) ∧
    (∀ x, 5 / 3 * ScaleData.cubeScale Q ≤ torusSupNorm (x - Q.2) → ScaleData.cutoffFn Q x = 0) ∧
    (∀ x x', |ScaleData.cutoffFn Q x - ScaleData.cutoffFn Q x'| ≤
      3 * (ScaleData.cubeScale Q)⁻¹ * torusSupNorm (x - x')) ∧
    (∀ (f : C.data.SiteField) (A : C.data.BondField),
      C.data.plaquetteCurl (C.data.bondMul f A) =
        C.data.plaquetteMul f (C.data.plaquetteCurl A) + C.data.leibnizTerm f A)
end YangMills.Construction.GeneralTorus
