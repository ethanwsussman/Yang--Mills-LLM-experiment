import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunctionProof
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsReadOnALargerSetOfIndices
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
namespace CoeffsOnSuperset
section Restriction
variable {F : PeriodicData}
theorem fieldExtend_apply {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) (z : ComplexCoordinates l)
    (j : Fin l) : fieldExtend e z ((e j : S) : F.Carrier) = z j := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.fieldExtend_apply <;> assumption
theorem isSupBelow_fieldExtend {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S)
    {z : ComplexCoordinates l} {ρ : ℝ} (hz : ‖z‖ < ρ) : IsSupBelow F (fieldExtend e z) ρ := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.isSupBelow_fieldExtend <;> assumption
def coordRestrict {S S' : Set F.Carrier} {l l' : ℕ} (hS : S ⊆ S') (e : Fin l ≃ S)
    (e' : Fin l' ≃ S') : ComplexCoordinates l' →ₗ[ℂ] ComplexCoordinates l :=
  LinearMap.funLeft ℂ ℂ fun j => e'.symm ⟨e j, hS (e j).2⟩
variable {S S' : Set F.Carrier} {l l' : ℕ} (hS : S ⊆ S') (e : Fin l ≃ S) (e' : Fin l' ≃ S')
theorem coordRestrict_apply (z : ComplexCoordinates l') (j : Fin l) :
    coordRestrict hS e e' z j = z (e'.symm ⟨e j, hS (e j).2⟩) :=
  rfl
theorem coordRestrict_fieldValues (ζ : F.Carrier → ℂ) :
    coordRestrict hS e e' (fieldValues e' ζ) = fieldValues e ζ := by
  funext j
  rw [coordRestrict_apply]
  show ζ ((e' (e'.symm ⟨e j, hS (e j).2⟩) : S') : F.Carrier) = ζ (e j)
  rw [Equiv.apply_symm_apply]
theorem norm_coordRestrict_le (z : ComplexCoordinates l') : ‖coordRestrict hS e e' z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun _ => norm_le_pi_norm z _
theorem fieldExtend_coordRestrict (z : ComplexCoordinates l') {κ : F.Carrier} (hκ : κ ∈ S) :
    fieldExtend e (coordRestrict hS e e' z) κ = fieldExtend e' z κ := by
  obtain ⟨j, hj⟩ := e.surjective ⟨κ, hκ⟩
  have hj' : ((e j : S) : F.Carrier) = κ := congrArg Subtype.val hj
  subst hj'
  rw [fieldExtend_apply, coordRestrict_apply]
  have hval := fieldExtend_apply e' z (e'.symm ⟨e j, hS (e j).2⟩)
  rw [Equiv.apply_symm_apply] at hval
  exact hval.symm
end Restriction
section Expansions
variable {l m : ℕ} {f g : ComplexCoordinates l → ℂ} {φ : ComplexCoordinates l →ₗ[ℂ] ℂ}
  {β : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ}
theorem secondOrder_congr (hfg : f =ᶠ[𝓝 0] g) (hx : IsSecondOrderExpansion f φ β) :
    IsSecondOrderExpansion g φ β := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.secondOrder_congr <;> assumption
theorem secondOrder_comp (hx : IsSecondOrderExpansion f φ β)
    (A : ComplexCoordinates m →ₗ[ℂ] ComplexCoordinates l) (hA : ∀ z, ‖A z‖ ≤ ‖z‖) :
    IsSecondOrderExpansion (fun z => f (A z)) (φ ∘ₗ A) (β.compl₁₂ A A) := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.secondOrder_comp <;> assumption
end Expansions
section Entries
variable {F I I' : PeriodicData} {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
theorem entry_eq_of_eqOn_near (hT : IsLocalWith F I I' T ρ R) (ι' : I'.Carrier) (ι : I.Carrier)
    {ζ₁ ζ₂ : F.Carrier → ℂ} (h₁ : IsSupBelow F ζ₁ ρ) (h₂ : IsSupBelow F ζ₂ ρ)
    (hag : ∀ κ ∈ nearIndices F (I'.pos ι') R, ζ₁ κ = ζ₂ κ) :
    T ζ₁ ι' ι = T ζ₂ ι' ι := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.entry_eq_of_eqOn <;> assumption
theorem entryFun_eventuallyEq (hρ : 0 < ρ) {ι' : I'.Carrier} {ι : I.Carrier} {S : Set F.Carrier}
    {l : ℕ} (e : Fin l ≃ S) {h : ComplexCoordinates l → ℂ}
    (hh : ∀ ζ, IsSupBelow F ζ ρ → T ζ ι' ι = h (fieldValues e ζ)) :
    entryFun T ι' ι e =ᶠ[𝓝 0] h := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.entryFun_eventuallyEq <;> assumption
theorem secondOrder_entryFun_superset (hT : IsLocalWith F I I' T ρ R)
    {ι' : I'.Carrier} {ι : I.Carrier} {A : Set F.Carrier} {l l' : ℕ}
    (hA : nearIndices F (I'.pos ι') R ⊆ A)
    (e : Fin l ≃ nearIndices F (I'.pos ι') R) (e' : Fin l' ≃ A)
    {φ : ComplexCoordinates l →ₗ[ℂ] ℂ}
    {β : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ}
    (hx : IsSecondOrderExpansion (entryFun T ι' ι e) φ β) :
    IsSecondOrderExpansion (entryFun T ι' ι e') (φ ∘ₗ coordRestrict hA e e')
      (β.compl₁₂ (coordRestrict hA e e') (coordRestrict hA e e')) := by
  refine secondOrder_congr ?_ (secondOrder_comp hx _ (norm_coordRestrict_le hA e e'))
  filter_upwards [Metric.ball_mem_nhds (0 : ComplexCoordinates l') hT.radius_pos] with z hz
  have hz' : ‖z‖ < ρ := by simpa using hz
  exact entry_eq_of_eqOn_near hT ι' ι
    (isSupBelow_fieldExtend e ((norm_coordRestrict_le hA e e' z).trans_lt hz'))
    (isSupBelow_fieldExtend e' hz') fun κ hκ => fieldExtend_coordRestrict hA e e' z hκ
end Entries
theorem claim_holds (hTaylor : YangMills.Construction.Coordinates.QuadraticTaylor.UniqueExpansion)
    (hNumbers : ParameterIndependence.Claim) : Claim := by
  intro F I I' hF hI hI' T ρ R hT ι' ι A l e hA
  obtain ⟨l₀, e₀, h, hol, hh⟩ := hT.holo_entry ι' ι
  obtain ⟨p, hp, -⟩ := hTaylor l₀ ρ hT.radius_pos h hol
  have x₀ : IsSecondOrderExpansion (entryFun T ι' ι e₀) p.1 p.2 :=
    secondOrder_congr (entryFun_eventuallyEq hT.radius_pos e₀ hh).symm hp
  have hN := ((hNumbers F I I' hF hI hI' T ρ R ρ R hT hT).2.1.1)
  refine ⟨p.1 ∘ₗ coordRestrict hA e₀ e,
    p.2.compl₁₂ (coordRestrict hA e₀ e) (coordRestrict hA e₀ e),
    secondOrder_entryFun_superset hT hA e₀ e x₀, fun ζ => ?_, fun ζ ζ' => ?_⟩
  · have hAt := (hN ζ ζ ι' ι).1.2.2 ρ R hT l₀ e₀ p.1 p.2 x₀
    simpa [coordRestrict_fieldValues] using hAt
  · have hAt := (hN ζ ζ' ι' ι).2.2.2 ρ R hT l₀ e₀ p.1 p.2 x₀
    simpa [coordRestrict_fieldValues] using hAt
end CoeffsOnSuperset
end YangMills.Construction.PeriodicOperators
end
