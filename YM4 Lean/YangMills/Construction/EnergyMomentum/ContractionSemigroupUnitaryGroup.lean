import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction.EnergyMomentum
abbrev Momentum3 : Type := EuclideanSpace ℝ (Fin 3)
abbrev EnergyMomentumSpace : Type := ℝ≥0 × Momentum3
def spatialDot (y q : Momentum3) : ℝ := ∑ i, y i * q i
def laplaceFourierExp (t : ℝ≥0) (y : Momentum3) (p : EnergyMomentumSpace) : ℂ :=
  Complex.exp (((-(t : ℝ) * (p.1 : ℝ) : ℝ) : ℂ) + Complex.I * ((spatialDot y p.2 : ℝ) : ℂ))
theorem continuous_laplaceFourierExp (t : ℝ≥0) (y : Momentum3) :
    Continuous (laplaceFourierExp t y) := by
  unfold laplaceFourierExp spatialDot
  fun_prop
theorem norm_laplaceFourierExp_le_one (t : ℝ≥0) (y : Momentum3) (p : EnergyMomentumSpace) :
    ‖laplaceFourierExp t y p‖ ≤ 1 := by
  have htp : 0 ≤ (t : ℝ) * (p.1 : ℝ) := mul_nonneg t.2 p.1.2
  simp [laplaceFourierExp, Complex.norm_exp, htp]
def laplaceFourierSpan : Submodule ℂ (EnergyMomentumSpace → ℂ) :=
  Submodule.span ℂ (range fun s : ℝ≥0 × Momentum3 => laplaceFourierExp s.1 s.2)
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
structure IsUnitaryOperator (B : H →L[ℂ] H) : Prop where
  bijective : Function.Bijective B
  norm_map : ∀ ψ, ‖B ψ‖ = ‖ψ‖
theorem isUnitaryOperator_iff_mem_unitary (B : H →L[ℂ] H) :
    IsUnitaryOperator B ↔ B ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff]
  constructor
  · intro hU
    have hl : star B * B = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self B).mp hU.norm_map
    refine ⟨hl, ?_⟩
    ext ψ
    obtain ⟨φ, rfl⟩ := hU.bijective.2 ψ
    have hφ : (star B * B) φ = φ := by rw [hl]; rfl
    change B ((star B * B) φ) = B φ
    rw [hφ]
  · rintro ⟨hl, hr⟩
    have left : ∀ ψ, star B (B ψ) = ψ := fun ψ => by
      change (star B * B) ψ = ψ
      rw [hl]; rfl
    have right : ∀ ψ, B (star B ψ) = ψ := fun ψ => by
      change (B * star B) ψ = ψ
      rw [hr]; rfl
    exact ⟨⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩,
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self B).mpr hl⟩
structure IsContractionSemigroupWithUnitaryGroup (S : ℝ≥0 → H →L[ℂ] H)
    (V : Momentum3 → H →L[ℂ] H) : Prop where
  isSelfAdjoint : ∀ t, IsSelfAdjoint (S t)
  norm_le_one : ∀ t, ‖S t‖ ≤ 1
  semigroup_zero : S 0 = 1
  semigroup_add : ∀ t t', S t * S t' = S (t + t')
  isUnitary : ∀ y, IsUnitaryOperator (V y)
  group_add : ∀ y y', V y * V y' = V (y + y')
  semigroup_mul_group : ∀ t y, S t * V y = V y * S t
  continuous_semigroup : ∀ ψ, Continuous fun t => S t ψ
  continuous_group : ∀ ψ, Continuous fun y => V y ψ
end Operators
end YangMills.Construction.EnergyMomentum
