import YangMills.Construction.DirichletOperator.BoundsOfTheBracketOnALocalTorus
import YangMills.Construction.RegionSequence.DifferenceAdjointsByParts
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
noncomputable section
namespace LocalTorusBracket
variable {𝒯 : NestedRegions}
theorem finite_fineBond (hT : TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section Norms
variable [Fintype 𝒯.FineBond]
end Norms
section Symmetry
variable [Fintype 𝒯.FineBond]
end Symmetry
section Steps
variable {n : ℕ} {φ : 𝒯.Point → ℝ} {κ : ℝ}
theorem anchoredIn_iff (hloc : IsCubeSetting 𝒯 n) (X : Set 𝒯.Point) (b : 𝒯.FineBond) :
    AnchoredIn X b ↔ (b.source : 𝒯.Point) ∈ X := by
  have h0 : 𝒯.Ω 0 = univ := hloc.full_below 0 (Nat.zero_le n)
  simp [AnchoredIn, anchor, h0]
theorem ξ_le_two_scale (𝒯 : NestedRegions) (n : ℕ) : 𝒯.ξ ≤ 2 * 𝒯.scale (n + 1) := by
  have hL : (1 : ℝ) ≤ 𝒯.L := by
    have := 𝒯.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒯.L)
  have hp : (1 : ℝ) ≤ (𝒯.L : ℝ) ^ (n + 1) := one_le_pow₀ hL
  have hξ := 𝒯.ξ_pos
  simp only [NestedRegions.scale, scaleSpacing, zpow_natCast]
  nlinarith
theorem lOneNorm_unitStep_le (ν : Fin 4) :
    lOneNorm ((unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) ≤ 𝒯.ξ := by
  have hmem : 𝒯.ξ ∈ {r | ∃ v : Fin 4 → ℝ,
      torusProj 4 𝒯.side v = ((unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) ∧
        r = ∑ μ, |v μ|} := by
    refine ⟨Pi.single ν 𝒯.ξ, rfl, ?_⟩
    rw [Finset.sum_eq_single ν (fun μ _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
    simp [abs_of_pos 𝒯.ξ_pos]
  refine csInf_le ⟨0, ?_⟩ hmem
  rintro r ⟨v, -, rfl⟩
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem supNorm_le_of_lOneNorm_le (hLen : LengthAxioms 4 𝒯.side) (n : ℕ) {p : 𝒯.Point}
    (h : lOneNorm p ≤ 𝒯.ξ) : supNorm p ≤ 2 * 𝒯.scale (n + 1) :=
  (hLen.supNorm_le_lOneNorm p).trans (h.trans (ξ_le_two_scale 𝒯 n))
theorem lOneNorm_sub_add_step (hLen : LengthAxioms 4 𝒯.side) (x : 𝒯.FineSite) (ν : Fin 4) :
    lOneNorm ((x : 𝒯.Point) - ((x + unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point)) ≤
      𝒯.ξ := by
  have h : (x : 𝒯.Point) - ((x + unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) =
      -((unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) := by
    rw [AddSubgroup.coe_add]
    abel
  rw [h, hLen.lOneNorm_neg]
  exact lOneNorm_unitStep_le ν
theorem lOneNorm_sub_sub_step (x : 𝒯.FineSite) (ν : Fin 4) :
    lOneNorm ((x : 𝒯.Point) - ((x - unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point)) ≤
      𝒯.ξ := by
  have h : (x : 𝒯.Point) - ((x - unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) =
      ((unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) := by
    rw [AddSubgroup.coe_sub]
    abel
  rw [h]
  exact lOneNorm_unitStep_le ν
theorem eq_zero_of_not_near (hLen : LengthAxioms 4 𝒯.side) {x : 𝒯.FineSite}
    (hN : ¬IsNearSupport n φ (x : 𝒯.Point)) :
    φ (x : 𝒯.Point) = 0 ∧ ∀ ν,
      φ ((x + unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) = 0 ∧
      φ ((x - unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) = 0 := by
  have hz : ∀ x' : 𝒯.Point, supNorm ((x : 𝒯.Point) - x') ≤ 2 * 𝒯.scale (n + 1) →
      φ x' = 0 := fun x' hd => by
    by_contra h
    exact hN ⟨x', h, hd⟩
  refine ⟨hz _ ?_, fun ν => ⟨hz _ (supNorm_le_of_lOneNorm_le hLen n
    (lOneNorm_sub_add_step hLen x ν)),
    hz _ (supNorm_le_of_lOneNorm_le hLen n (lOneNorm_sub_sub_step x ν))⟩⟩
  rw [sub_self, hLen.supNorm_zero]
  exact 𝒯.ξ_pos.le.trans (ξ_le_two_scale 𝒯 n)
theorem IsCollar.mem {Y Z : Set 𝒯.Point} (hH : IsCollar n φ Y Z) {x x' : 𝒯.Point}
    (hx : x ∈ Y) (hd : supNorm (x - x') ≤ 2 * 𝒯.scale (n + 1)) (hne : φ x ≠ φ x') :
    x' ∈ Z := by
  refine hH.2 x hx x' hd ?_
  by_cases h₁ : φ x = 0
  · exact Or.inr fun h₂ => hne (by rw [h₁, h₂])
  · exact Or.inl h₁
end Steps
section Bounds
variable [Fintype 𝒯.FineBond] {n : ℕ} {φ : 𝒯.Point → ℝ} {κ₁ κ₂ : ℝ} {Y Z : Set 𝒯.Point}
omit [Fintype 𝒯.FineBond] in
theorem restrictBonds_of_mem {X : Set 𝒯.Point} {f : 𝒯.FineBond → ℝ} {b : 𝒯.FineBond}
    (h : AnchoredIn X b) : restrictBonds X f b = f b :=
  indicator_of_mem (s := {b | AnchoredIn X b}) h _
end Bounds
end LocalTorusBracket
end
end YangMills.Construction
