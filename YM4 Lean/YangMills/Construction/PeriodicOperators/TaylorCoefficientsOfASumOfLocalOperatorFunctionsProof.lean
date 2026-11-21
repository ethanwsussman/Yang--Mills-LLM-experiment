import YangMills.Construction.PeriodicOperators.SumOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfAProductOfLocalOperatorFunctionsProof
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfASumOfLocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CoeffAdditivity
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
theorem expansion_add {l : ℕ} {h h' : Coordinates.ComplexCoordinates l → ℂ}
    {φ φ' : Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ}
    {β β' : Coordinates.ComplexCoordinates l →ₗ[ℂ] Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ}
    (hx : IsSecondOrderExpansion h φ β) (hx' : IsSecondOrderExpansion h' φ' β') :
    IsSecondOrderExpansion (fun z => h z + h' z) (φ + φ') (β + β') := by apply _root_.YangMills.Construction.PeriodicOperators.LeibnizRuleProof.secondOrder_add <;> assumption
theorem entryFun_opFunAdd {F I I' : PeriodicData}
    (T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (a' : I'.Carrier) (a : I.Carrier)
    {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) :
    entryFun (opFunAdd T T') a' a e =
      fun z => entryFun T a' a e z + entryFun T' a' a e z :=
  rfl
theorem claim_holds (hRead : CoeffsOnSuperset.Claim)
    (hNumbers : ParameterIndependence.Claim)
    (hSum : OpFunAdd.LocalClosed) :
    CoeffAdditivity.Claim := by
  intro F I I' hF hI hI' T T' hT hT' u v
  have hS := hSum F I I' hF hI hI' T T' hT hT'
  obtain ⟨ρ₁, R₁, m₁⟩ := hT
  obtain ⟨ρ₂, R₂, m₂⟩ := hT'
  obtain ⟨ρ₃, R₃, m₃⟩ := hS
  set ρ : ℝ := min ρ₁ (min ρ₂ ρ₃) with hρ
  set R : ℝ := max R₁ (max R₂ R₃) with hR
  have hpos : 0 < ρ := lt_min m₁.radius_pos (lt_min m₂.radius_pos m₃.radius_pos)
  have n₁ : IsLocalWith F I I' T ρ R :=
    (hNumbers F I I' hF hI hI' T ρ₁ R₁ ρ₁ R₁ m₁ m₁).1.1 ρ R hpos (min_le_left _ _)
      (le_max_left _ _)
  have n₂ : IsLocalWith F I I' T' ρ R :=
    (hNumbers F I I' hF hI hI' T' ρ₂ R₂ ρ₂ R₂ m₂ m₂).1.1 ρ R hpos
      ((min_le_right _ _).trans (min_le_left _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
  have n₃ : IsLocalWith F I I' (opFunAdd T T') ρ R :=
    (hNumbers F I I' hF hI hI' (opFunAdd T T') ρ₃ R₃ ρ₃ R₃ m₃ m₃).1.1 ρ R hpos
      ((min_le_right _ _).trans (min_le_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
  have key : ∀ (a' : I'.Carrier) (a : I.Carrier),
      coeffOne F I I' (opFunAdd T T') u a' a =
          coeffOne F I I' T u a' a + coeffOne F I I' T' u a' a ∧
        coeffTwo F I I' (opFunAdd T T') u v a' a =
          coeffTwo F I I' T u v a' a + coeffTwo F I I' T' u v a' a := by
    intro a' a
    obtain ⟨l, e, -⟩ := n₃.holo_entry a' a
    obtain ⟨φ, β, hx, hφ, hβ⟩ :=
      hRead F I I' hF hI hI' T ρ R n₁ a' a _ l e subset_rfl
    obtain ⟨φ', β', hx', hφ', hβ'⟩ :=
      hRead F I I' hF hI hI' T' ρ R n₂ a' a _ l e subset_rfl
    have hxs : IsSecondOrderExpansion (entryFun (opFunAdd T T') a' a e) (φ + φ') (β + β') := by
      rw [entryFun_opFunAdd]
      exact expansion_add hx hx'
    have hb := (hNumbers F I I' hF hI hI' (opFunAdd T T') ρ R ρ R n₃ n₃).2.1.1 u v a' a
    constructor
    · have := hb.1.2.2 ρ R n₃ l e (φ + φ') (β + β') hxs
      rw [← this, LinearMap.add_apply, hφ, hφ']
    · have := hb.2.2.2 ρ R n₃ l e (φ + φ') (β + β') hxs
      rw [← this, LinearMap.add_apply, LinearMap.add_apply, hβ, hβ']
  exact ⟨funext fun a' => funext fun a => (key a' a).1,
    funext fun a' => funext fun a => (key a' a).2⟩
end YangMills.Construction.PeriodicOperators.CoeffAdditivity
end
