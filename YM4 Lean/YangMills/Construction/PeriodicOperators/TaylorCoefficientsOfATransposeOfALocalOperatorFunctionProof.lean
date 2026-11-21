import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfATransposeOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsReadOnALargerSetOfIndices
import YangMills.Construction.PeriodicOperators.TransposeOfALocalOperatorFunction
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TransposeTaylor
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
theorem linear_quadratic_coeffs_eq_zero {a b : ℂ}
    (hab : (fun t : ℂ => a * t + b * t ^ 2) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ 3) : a = 0 ∧ b = 0 := by
  obtain ⟨C, hC⟩ := hab.bound
  have hC' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 ∧ ‖a * t + b * t ^ 2‖ ≤ C * ‖t‖ ^ 3 := by
    filter_upwards [hC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    refine ⟨ht0, ?_⟩
    simpa [norm_pow] using ht
  have hid : Tendsto (fun t : ℂ => t) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun t : ℂ => ‖t‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa using hid.norm
  have ha : a = 0 := by
    have h1 : Tendsto (fun t : ℂ => ‖a + b * t‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖a‖) := by
      simpa using ((tendsto_const_nhds (x := a)).add (hid.const_mul b)).norm
    have h2 : Tendsto (fun t : ℂ => C * ‖t‖ ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      simpa using (hnorm.pow 2).const_mul C
    have h3 : ‖a‖ ≤ 0 := by
      refine le_of_tendsto_of_tendsto h1 h2 ?_
      filter_upwards [hC'] with t ht
      obtain ⟨ht0, hle⟩ := ht
      have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
      have e : a * t + b * t ^ 2 = t * (a + b * t) := by ring
      rw [e, norm_mul] at hle
      have hle' : ‖t‖ * ‖a + b * t‖ ≤ ‖t‖ * (C * ‖t‖ ^ 2) := by
        calc ‖t‖ * ‖a + b * t‖ ≤ C * ‖t‖ ^ 3 := hle
          _ = ‖t‖ * (C * ‖t‖ ^ 2) := by ring
      exact le_of_mul_le_mul_left hle' hpos
    exact norm_le_zero_iff.mp h3
  refine ⟨ha, ?_⟩
  have h2 : Tendsto (fun t : ℂ => C * ‖t‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa using hnorm.const_mul C
  have h3 : ‖b‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds h2 ?_
    filter_upwards [hC'] with t ht
    obtain ⟨ht0, hle⟩ := ht
    have hpos : 0 < ‖t‖ ^ 2 := pow_pos (norm_pos_iff.mpr ht0) 2
    rw [ha, zero_mul, zero_add, norm_mul, norm_pow] at hle
    have hle' : ‖t‖ ^ 2 * ‖b‖ ≤ ‖t‖ ^ 2 * (C * ‖t‖) := by
      calc ‖t‖ ^ 2 * ‖b‖ = ‖b‖ * ‖t‖ ^ 2 := mul_comm _ _
        _ ≤ C * ‖t‖ ^ 3 := hle
        _ = ‖t‖ ^ 2 * (C * ‖t‖) := by ring
    exact le_of_mul_le_mul_left hle' hpos
  exact norm_le_zero_iff.mp h3
section QuadraticForms
variable {l : ℕ} {g : Coordinates.ComplexCoordinates l → ℂ}
  {φ φ' : Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ}
  {β β' : Coordinates.ComplexCoordinates l →ₗ[ℂ] Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ}
theorem forms_eq_on_line (hx : IsSecondOrderExpansion g φ β)
    (hx' : IsSecondOrderExpansion g φ' β') (v : Coordinates.ComplexCoordinates l) :
    φ v = φ' v ∧ β v v = β' v v := by
  have hD : (fun z : Coordinates.ComplexCoordinates l =>
      (φ z - φ' z) + (1 / 2 : ℂ) * (β z z - β' z z))
      =O[𝓝 0] fun z : Coordinates.ComplexCoordinates l => ‖z‖ ^ 3 :=
    (hx'.2.sub hx.2).congr_left fun z => by ring
  have hline : Tendsto (fun t : ℂ => t • v) (𝓝 0)
      (𝓝 (0 : Coordinates.ComplexCoordinates l)) := by
    have hc : Continuous fun t : ℂ => t • v := by fun_prop
    simpa using hc.tendsto 0
  have hcomp := hD.comp_tendsto hline
  have hbound : (fun t : ℂ => ‖t • v‖ ^ 3) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ 3 := by
    refine IsBigO.of_bound (‖v‖ ^ 3) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), norm_smul, mul_pow]
    exact le_of_eq (by ring)
  have hpoly : (fun t : ℂ => (φ v - φ' v) * t + ((1 / 2 : ℂ) * (β v v - β' v v)) * t ^ 2)
      =O[𝓝 0] fun t : ℂ => ‖t‖ ^ 3 := by
    refine (hcomp.trans hbound).congr_left fun t => ?_
    simp only [Function.comp, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  obtain ⟨h1, h2⟩ := linear_quadratic_coeffs_eq_zero hpoly
  refine ⟨sub_eq_zero.mp h1, sub_eq_zero.mp ?_⟩
  simpa using h2
theorem forms_eq (hx : IsSecondOrderExpansion g φ β)
    (hx' : IsSecondOrderExpansion g φ' β') : φ = φ' ∧ β = β' := by
  refine ⟨LinearMap.ext fun v => (forms_eq_on_line hx hx' v).1, ?_⟩
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  have hvw := (forms_eq_on_line hx hx' (v + w)).2
  have hv := (forms_eq_on_line hx hx' v).2
  have hw := (forms_eq_on_line hx hx' w).2
  simp only [map_add, LinearMap.add_apply] at hvw
  have hs := hx.1 w v
  have hs' := hx'.1 w v
  linear_combination (1 / 2 : ℂ) * hvw - (1 / 2 : ℂ) * hv - (1 / 2 : ℂ) * hw
    - (1 / 2 : ℂ) * hs + (1 / 2 : ℂ) * hs'
theorem secondOrderExpansion_const_mul (c : ℂ) (hx : IsSecondOrderExpansion g φ β) :
    IsSecondOrderExpansion (fun z => c * g z) (c • φ) (c • β) := by
  refine ⟨fun z z' => ?_, (hx.2.const_mul_left c).congr_left fun z => ?_⟩
  · simp only [LinearMap.smul_apply]
    rw [hx.1 z z']
  · simp only [LinearMap.smul_apply, smul_eq_mul]
    ring
end QuadraticForms
theorem claim_holds (h₁ : CoeffsOnSuperset.Claim)
    (h₂ : OpFunTransposeLocal.Claim)
    (h₃ : CovariantFiniteRange.Claim) : Claim := by
  intro F I I' hF hI hI' T hT ζ ζ'
  obtain ⟨ρ', R', hm'⟩ := h₂ F I I' hF hI hI' T hT
  obtain ⟨ρ, R, hm⟩ := hT
  have key : ∀ (a : I.Carrier) (b : I'.Carrier),
      coeffOne F I' I (opFunTranspose T) ζ a b =
          ((I'.weightOf b / I.weightOf a : ℝ) : ℂ) * coeffOne F I I' T ζ b a ∧
        coeffTwo F I' I (opFunTranspose T) ζ ζ' a b =
          ((I'.weightOf b / I.weightOf a : ℝ) : ℂ) * coeffTwo F I I' T ζ ζ' b a := by
    intro a b
    let A : Set F.Carrier :=
      nearIndices F (I.pos a) R' ∪ nearIndices F (I'.pos b) R
    have hA : A.Finite := ((h₃.1 F hF).1 _ _).union ((h₃.1 F hF).1 _ _)
    have := hA.to_subtype
    obtain ⟨l, ⟨e⟩⟩ := Finite.exists_equiv_fin A
    obtain ⟨φ, β, hx, hφ, hβ⟩ :=
      h₁ F I I' hF hI hI' T ρ R hm b a A l e.symm subset_union_right
    obtain ⟨φ', β', hx', hφ', hβ'⟩ :=
      h₁ F I' I hF hI' hI (opFunTranspose T) ρ' R' hm' a b A l e.symm subset_union_left
    have hc : IsSecondOrderExpansion (entryFun (opFunTranspose T) a b e.symm)
        (((I'.weightOf b / I.weightOf a : ℝ) : ℂ) • φ)
        (((I'.weightOf b / I.weightOf a : ℝ) : ℂ) • β) :=
      secondOrderExpansion_const_mul _ hx
    obtain ⟨e₁, e₂⟩ := forms_eq hx' hc
    constructor
    · rw [← hφ', ← hφ, e₁]
      rfl
    · rw [← hβ', ← hβ, e₂]
      rfl
  constructor
  · funext a b
    exact (key a b).1
  · funext a b
    exact (key a b).2
end YangMills.Construction.PeriodicOperators.TransposeTaylor
end
