import YangMills.Construction.PartitionCubes.AveragedBracketMatrix
import YangMills.Construction.PartitionCubes.LapBracketFormulas
import YangMills.Construction.RegionSequence.BlockOperatorNorms
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.PartitionCubes
noncomputable section
namespace YangMills.Construction.LocalTorusBracket
variable {𝒯 : RegionSequence.NestedRegions}
def bracketOp (φ : 𝒯.Point → ℝ) (v : 𝒯.FineBond → ℝ) : 𝒯.FineBond → ℝ :=
  PartitionCubes.lapBracket φ v + PartitionCubes.avgBracket φ v
def IsNearSupport (n : ℕ) (φ : 𝒯.Point → ℝ) (x : 𝒯.Point) : Prop :=
  ∃ z, φ z ≠ 0 ∧ Torus.supNorm (x - z) ≤ 2 * 𝒯.scale (n + 1)
def IsCollar (n : ℕ) (φ : 𝒯.Point → ℝ) (Y Z : Set 𝒯.Point) : Prop :=
  Y ⊆ Z ∧ ∀ x ∈ Y, ∀ z, Torus.supNorm (x - z) ≤ 2 * 𝒯.scale (n + 1) →
    (φ x ≠ 0 ∨ φ z ≠ 0) → z ∈ Z
def lowerOrderConst (𝒯 : RegionSequence.NestedRegions) (n : ℕ) (κ₁ κ₂ : ℝ) : ℝ :=
  κ₂ + 20 * κ₁ * 𝒯.scale (n + 1) * (𝒯.scale n ^ 2)⁻¹
structure BracketDecomposition (n : ℕ) (φ : 𝒯.Point → ℝ) (κ₁ κ₂ : ℝ)
    (w : (𝒯.FineBond → ℝ) →ₗ[ℝ] 𝒯.Tensor 1)
    (u : (𝒯.FineBond → ℝ) →ₗ[ℝ] 𝒯.FineBond → ℝ) : Prop where
  neg_eq_div_add : ∀ A : 𝒯.FineBond → ℝ, -bracketOp φ A = divOne (w A) + u A
  tensor_support : ∀ (A : 𝒯.FineBond → ℝ) (ν : Fin 1 → Fin 4) (c : 𝒯.FineBond), w A ν c ≠ 0 →
    IsNearSupport n φ (c.source : 𝒯.Point)
  rest_support : ∀ (A : 𝒯.FineBond → ℝ) (c : 𝒯.FineBond), u A c ≠ 0 →
    IsNearSupport n φ (c.source : 𝒯.Point)
  tensor_le : ∀ (Y Z : Set 𝒯.Point), IsCollar n φ Y Z → ∀ (p : NormExponent)
    (A : 𝒯.FineBond → ℝ),
    (tensorCutSpace 𝒯 1).pNorm p (restrictTensor Y (w A)) ≤
      8 * κ₁ * (formCutSpace 𝒯).pNorm p (restrictBonds Z A)
  rest_le : ∀ (Y Z : Set 𝒯.Point), IsCollar n φ Y Z → ∀ (p : NormExponent)
    (A : 𝒯.FineBond → ℝ),
    (formCutSpace 𝒯).pNorm p (restrictBonds Y (u A)) ≤
      lowerOrderConst 𝒯 n κ₁ κ₂ * (formCutSpace 𝒯).pNorm p (restrictBonds Z A)
structure BracketProperties (n : ℕ) (φ : 𝒯.Point → ℝ) (κ₁ κ₂ : ℝ) : Prop where
  antisymm : ∀ u v : 𝒯.FineBond → ℝ,
    bondInner (bracketOp φ u) v = -bondInner u (bracketOp φ v)
  support : ∀ (v : 𝒯.FineBond → ℝ) (c : 𝒯.FineBond), bracketOp φ v c ≠ 0 →
    IsNearSupport n φ (c.source : 𝒯.Point)
  norm_le : ∀ (Y Z : Set 𝒯.Point), IsCollar n φ Y Z → ∀ (p : NormExponent)
    (v : 𝒯.FineBond → ℝ),
    (formCutSpace 𝒯).pNorm p (restrictBonds Y (bracketOp φ v)) ≤
      8 * κ₁ * (tensorCutSpace 𝒯 1).pNorm p (restrictTensor Z (nablaOne v)) +
        lowerOrderConst 𝒯 n κ₁ κ₂ * (formCutSpace 𝒯).pNorm p (restrictBonds Z v)
  exists_decomposition : ∃ (w : (𝒯.FineBond → ℝ) →ₗ[ℝ] 𝒯.Tensor 1)
    (u : (𝒯.FineBond → ℝ) →ₗ[ℝ] 𝒯.FineBond → ℝ), BracketDecomposition n φ κ₁ κ₂ w u
end YangMills.Construction.LocalTorusBracket
