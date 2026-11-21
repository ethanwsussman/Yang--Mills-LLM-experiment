import YangMills.Construction.Analysis.QuadraticTaylorUniqueness
import YangMills.Construction.PeriodicOperators.CoefficientsHaveSupportOfEntries
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfALocalOperatorFunctionProof
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsReadOnALargerSetOfIndices
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
namespace CoeffLocality
section Values
variable {F : PeriodicData} {S : Set F.Carrier} {l : ℕ}
theorem fieldExtend_apply (e : Fin l ≃ S) (z : Coordinates.ComplexCoordinates l) (j : Fin l) :
    fieldExtend e z ((e j : S) : F.Carrier) = z j := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.fieldExtend_apply <;> assumption
theorem fieldExtend_of_not_mem (e : Fin l ≃ S) (z : Coordinates.ComplexCoordinates l)
    {x : F.Carrier} (hx : x ∉ S) : fieldExtend e z x = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.fieldExtend_of_notMem <;> assumption
theorem isSupBelow_fieldExtend (e : Fin l ≃ S) {z : Coordinates.ComplexCoordinates l} {r : ℝ}
    (hz : ‖z‖ < r) : IsSupBelow F (fieldExtend e z) r := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.isSupBelow_fieldExtend <;> assumption
open Classical in
def keepOn (e : Fin l ≃ S) (A : Set F.Carrier) :
    Coordinates.ComplexCoordinates l →ₗ[ℂ] Coordinates.ComplexCoordinates l where
  toFun z j := if ((e j : S) : F.Carrier) ∈ A then z j else 0
  map_add' z w := by
    funext j
    by_cases h : ((e j : S) : F.Carrier) ∈ A <;> simp [h]
  map_smul' c z := by
    funext j
    by_cases h : ((e j : S) : F.Carrier) ∈ A <;> simp [h]
theorem keepOn_apply_of_mem (e : Fin l ≃ S) (A : Set F.Carrier)
    (z : Coordinates.ComplexCoordinates l) {j : Fin l}
    (h : ((e j : S) : F.Carrier) ∈ A) : keepOn e A z j = z j :=
  if_pos h
theorem keepOn_apply_of_not_mem (e : Fin l ≃ S) (A : Set F.Carrier)
    (z : Coordinates.ComplexCoordinates l) {j : Fin l}
    (h : ((e j : S) : F.Carrier) ∉ A) : keepOn e A z j = 0 :=
  if_neg h
theorem norm_keepOn_le (e : Fin l ≃ S) (A : Set F.Carrier) (z : Coordinates.ComplexCoordinates l) :
    ‖keepOn e A z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j => ?_
  by_cases h : ((e j : S) : F.Carrier) ∈ A
  · rw [keepOn_apply_of_mem e A z h]
    exact norm_le_pi_norm z j
  · rw [keepOn_apply_of_not_mem e A z h, norm_zero]
    exact norm_nonneg z
theorem fieldExtend_keepOn_eqOn (e : Fin l ≃ S) (A : Set F.Carrier)
    (z : Coordinates.ComplexCoordinates l) :
    EqOn (fieldExtend e z) (fieldExtend e (keepOn e A z)) A := by
  intro x hx
  by_cases hS : x ∈ S
  · obtain ⟨j, hj⟩ := e.surjective ⟨x, hS⟩
    have hj' : ((e j : S) : F.Carrier) = x := congrArg Subtype.val hj
    subst hj'
    rw [fieldExtend_apply, fieldExtend_apply, keepOn_apply_of_mem e A z hx]
  · rw [fieldExtend_of_not_mem e _ hS, fieldExtend_of_not_mem e _ hS]
theorem keepOn_fieldValues (e : Fin l ≃ S) {A : Set F.Carrier} {u v : F.Carrier → ℂ}
    (h : EqOn u v A) : keepOn e A (fieldValues e u) = keepOn e A (fieldValues e v) := by
  funext j
  by_cases hj : ((e j : S) : F.Carrier) ∈ A
  · rw [keepOn_apply_of_mem e A _ hj, keepOn_apply_of_mem e A _ hj]
    exact h hj
  · rw [keepOn_apply_of_not_mem e A _ hj, keepOn_apply_of_not_mem e A _ hj]
theorem fieldValues_smul (e : Fin l ≃ S) (c : ℂ) (u : F.Carrier → ℂ) :
    fieldValues e (c • u) = c • fieldValues e u :=
  rfl
end Values
section Expansions
variable {l : ℕ} {g g' : Coordinates.ComplexCoordinates l → ℂ}
  {φ φ' : Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ}
  {β β' : Coordinates.ComplexCoordinates l →ₗ[ℂ] Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ}
theorem forms_eq_of_eventuallyEq (hU : Taylor.QuadraticTaylorUniqueness) (hg : g =ᶠ[𝓝 0] g')
    (hx : IsSecondOrderExpansion g φ β) (hx' : IsSecondOrderExpansion g' φ' β') :
    φ = φ' ∧ β = β' := by
  have h0 : g 0 = g' 0 := hg.self_of_nhds
  have hO : (fun z : Coordinates.ComplexCoordinates l =>
      (φ - φ') z + ((1 / 2 : ℂ) • (β - β')) z z) =O[𝓝 0] fun z => ‖z‖ ^ 3 := by
    refine (hx'.2.sub hx.2).congr' ?_ EventuallyEq.rfl
    filter_upwards [hg] with z hz
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hz, h0]
    ring
  obtain ⟨hφ, hβ⟩ := hU (Coordinates.ComplexCoordinates l) (φ - φ') ((1 / 2 : ℂ) • (β - β')) hO
  have hd : ∀ z, β z z = β' z z := fun z => by
    have h := hβ z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
    have h' : β z z - β' z z = 0 := by
      rcases mul_eq_zero.1 h with h | h
      · norm_num at h
      · exact h
    exact sub_eq_zero.1 h'
  refine ⟨sub_eq_zero.1 hφ, LinearMap.ext fun z => LinearMap.ext fun w => ?_⟩
  have h := hd (z + w)
  simp only [map_add, LinearMap.add_apply] at h
  have hs : β w z = β z w := hx.1 w z
  have hs' : β' w z = β' z w := hx'.1 w z
  rw [hd z, hd w, hs, hs'] at h
  have h2 : (2 : ℂ) * β z w = 2 * β' z w := by linear_combination h
  exact mul_left_cancel₀ two_ne_zero h2
theorem expansion_comp_linear (hx : IsSecondOrderExpansion g φ β)
    (L : Coordinates.ComplexCoordinates l →ₗ[ℂ] Coordinates.ComplexCoordinates l)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    IsSecondOrderExpansion (fun z => g (L z)) (φ ∘ₗ L) (β.compl₁₂ L L) := by
  refine ⟨fun z z' => by simpa using hx.1 (L z) (L z'), ?_⟩
  have ht : Tendsto L (𝓝 0) (𝓝 0) := by
    have h := (LinearMap.continuous_of_finiteDimensional L).tendsto 0
    simpa using h
  have h1 : (fun z : Coordinates.ComplexCoordinates l =>
      g (L z) - (g 0 + φ (L z) + (1 / 2 : ℂ) * β (L z) (L z)))
      =O[𝓝 0] fun z => ‖L z‖ ^ 3 := hx.2.comp_tendsto ht
  have h2 : (fun z : Coordinates.ComplexCoordinates l => ‖L z‖ ^ 3) =O[𝓝 0] fun z => ‖z‖ ^ 3 :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [one_mul, norm_pow, norm_pow, norm_norm, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hL z) 3)
  refine (h1.trans h2).congr' ?_ EventuallyEq.rfl
  refine Eventually.of_forall fun z => ?_
  simp
theorem expansion_const_zero :
    IsSecondOrderExpansion (fun _ : Coordinates.ComplexCoordinates l => (0 : ℂ)) 0 0 := by apply _root_.YangMills.Construction.PeriodicOperators.LocalOpFunTaylor.isSecondOrderExpansion_zero <;> assumption
end Expansions
theorem claim_holds (hL : CoeffsOnSuperset.Claim)
    (hU : Taylor.QuadraticTaylorUniqueness) : CoeffLocality.Claim := by
  intro F I I' hF hI hI' T hloc a' a
  obtain ⟨ρ, R, hT⟩ := hloc
  obtain ⟨l, e, -, -, -⟩ := hT.holo_entry a' a
  obtain ⟨φ, β, hx, h1, h2⟩ := hL F I I' hF hI hI' T ρ R hT a' a _ l e subset_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r A hr hread
    have hev : entryFun T a' a e =ᶠ[𝓝 0] fun z => entryFun T a' a e (keepOn e A z) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Coordinates.ComplexCoordinates l) hr] with z hz
      have hz' : ‖z‖ < r := by simpa using hz
      exact hread _ _ (isSupBelow_fieldExtend e hz')
        (isSupBelow_fieldExtend e (lt_of_le_of_lt (norm_keepOn_le e A z) hz'))
        (fieldExtend_keepOn_eqOn e A z)
    obtain ⟨hφ, hβ⟩ :=
      forms_eq_of_eventuallyEq hU hev hx (expansion_comp_linear hx (keepOn e A) (norm_keepOn_le e A))
    have hφ' : ∀ z, φ z = φ (keepOn e A z) := fun z => LinearMap.congr_fun hφ z
    have hβ' : ∀ z w, β z w = β (keepOn e A z) (keepOn e A w) := fun z w =>
      (LinearMap.congr_fun (LinearMap.congr_fun hβ z) w).trans (LinearMap.compl₁₂_apply _ _ _ _ _)
    refine ⟨fun u v h => ?_, fun u₁ u₂ v₁ v₂ h h' => ?_⟩
    · rw [← h1, ← h1, hφ', hφ' (fieldValues e v), keepOn_fieldValues e h]
    · rw [← h2, ← h2, hβ', hβ' (fieldValues e v₁), keepOn_fieldValues e h, keepOn_fieldValues e h']
  · intro r hr hzero u v
    have hev : entryFun T a' a e =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Coordinates.ComplexCoordinates l) hr] with z hz
      exact hzero _ (isSupBelow_fieldExtend e (by simpa using hz))
    obtain ⟨hφ, hβ⟩ := forms_eq_of_eventuallyEq hU hev hx expansion_const_zero
    rw [← h1, ← h2, hφ, hβ]
    simp
  · intro c u
    rw [← h1, ← h1, fieldValues_smul, map_smul, smul_eq_mul]
  · intro c c' u v
    rw [← h2, ← h2, fieldValues_smul, fieldValues_smul, map_smul, map_smul, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring
end CoeffLocality
end YangMills.Construction.PeriodicOperators
end
