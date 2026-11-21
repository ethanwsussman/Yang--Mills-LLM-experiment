import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunctionProof
import YangMills.Construction.PeriodicOperators.OperatorFunctionsThatAgreeOnSmallFields
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
namespace LocalAgreement
section Fields
variable {F : PeriodicData}
theorem isSupBelow_mono {ζ : F.Carrier → ℂ} {r s : ℝ} (h : IsSupBelow F ζ r) (hrs : r ≤ s) :
    IsSupBelow F ζ s :=
  let ⟨t, ht, hb⟩ := h
  ⟨t, ht.trans_le hrs, hb⟩
theorem isSupBelow_shiftField (n : Fin 4 → ℤ) {ζ : F.Carrier → ℂ} {r : ℝ}
    (h : IsSupBelow F ζ r) : IsSupBelow F (shiftField F n ζ) r :=
  let ⟨t, ht, hb⟩ := h
  ⟨t, ht, fun _ => hb _⟩
theorem norm_fieldExtend_le {A : Set F.Carrier} {l : ℕ} (e : Fin l ≃ A)
    (z : Coordinates.ComplexCoordinates l) (κ : F.Carrier) : ‖fieldExtend e z κ‖ ≤ ‖z‖ := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.norm_fieldExtend_le <;> assumption
end Fields
theorem isOpen_openPolydisk_zero (l : ℕ) (r : ℝ) :
    IsOpen (openPolydisk (0 : Coordinates.ComplexCoordinates l) r) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
theorem openPolydisk_zero_mono (l : ℕ) {r s : ℝ} (hrs : r ≤ s) :
    openPolydisk (0 : Coordinates.ComplexCoordinates l) r ⊆
      openPolydisk (0 : Coordinates.ComplexCoordinates l) s := by
  intro z hz
  simp only [openPolydisk, mem_ofPred_eq] at hz ⊢
  exact fun j => (hz j).trans_le hrs
theorem isSecondOrderExpansion_congr {l : ℕ} {g g' : Coordinates.ComplexCoordinates l → ℂ}
    {φ : Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ}
    {β : Coordinates.ComplexCoordinates l →ₗ[ℂ] Coordinates.ComplexCoordinates l →ₗ[ℂ] ℂ}
    (hg : g =ᶠ[𝓝 0] g') (hx : IsSecondOrderExpansion g φ β) : IsSecondOrderExpansion g' φ β := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.secondOrder_congr <;> assumption
section Agreement
variable {F I I' : PeriodicData} {T S : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ₀ : ℝ}
theorem isLocalWith_of_agree (hρ₀ : 0 < ρ₀) (hag : ∀ ζ, IsSupBelow F ζ ρ₀ → S ζ = T ζ) {ρ R : ℝ}
    (hT : IsLocalWith F I I' T ρ R) : IsLocalWith F I I' S (min ρ ρ₀) R where
  radius_pos := lt_min hT.radius_pos hρ₀
  vanish_far ζ hζ ι' ι h := by
    rw [hag ζ (isSupBelow_mono hζ (min_le_right _ _))]
    exact hT.vanish_far ζ (isSupBelow_mono hζ (min_le_left _ _)) ι' ι h
  holo_entry ι' ι := by
    obtain ⟨l, e, h, hh, hv⟩ := hT.holo_entry ι' ι
    have hs := openPolydisk_zero_mono l (min_le_left ρ ρ₀)
    refine ⟨l, e, h, ⟨isOpen_openPolydisk_zero l _, hh.2.1.mono hs,
      fun a ha j => hh.2.2 a (hs ha) j⟩, fun ζ hζ => ?_⟩
    rw [hag ζ (isSupBelow_mono hζ (min_le_right _ _))]
    exact hv ζ (isSupBelow_mono hζ (min_le_left _ _))
  shift_covariant ζ hζ n ι' ι := by
    have h₀ := isSupBelow_mono hζ (min_le_right _ _)
    rw [hag _ (isSupBelow_shiftField n h₀), hag ζ h₀]
    exact hT.shift_covariant ζ (isSupBelow_mono hζ (min_le_left _ _)) n ι' ι
theorem entryFun_eventuallyEq (hρ₀ : 0 < ρ₀) (hag : ∀ ζ, IsSupBelow F ζ ρ₀ → S ζ = T ζ)
    (ι' : I'.Carrier) (ι : I.Carrier) {A : Set F.Carrier} {l : ℕ} (e : Fin l ≃ A) :
    entryFun T ι' ι e =ᶠ[𝓝 0] entryFun S ι' ι e := by
  filter_upwards [Metric.ball_mem_nhds (0 : Coordinates.ComplexCoordinates l) hρ₀] with z hz
  have hz' : ‖z‖ < ρ₀ := by simpa using hz
  have hb : IsSupBelow F (fieldExtend e z) ρ₀ := ⟨‖z‖, hz', norm_fieldExtend_le e z⟩
  simp only [entryFun, hag _ hb]
theorem isLinearCoeff_of_agree (hρ₀ : 0 < ρ₀) (hag : ∀ ζ, IsSupBelow F ζ ρ₀ → S ζ = T ζ)
    {ζ : F.Carrier → ℂ} {ι' : I'.Carrier} {ι : I.Carrier} {t : ℂ}
    (h : IsLinearCoeff F I I' T ζ ι' ι t) : IsLinearCoeff F I I' S ζ ι' ι t :=
  fun _ R hS l e φ β hx =>
    h _ R (isLocalWith_of_agree hρ₀ (fun ζ hζ => (hag ζ hζ).symm) hS) l e φ β
      (isSecondOrderExpansion_congr ((entryFun_eventuallyEq hρ₀ hag ι' ι e).symm) hx)
theorem isBilinearCoeff_of_agree (hρ₀ : 0 < ρ₀) (hag : ∀ ζ, IsSupBelow F ζ ρ₀ → S ζ = T ζ)
    {ζ ζ' : F.Carrier → ℂ} {ι' : I'.Carrier} {ι : I.Carrier} {t : ℂ}
    (h : IsBilinearCoeff F I I' T ζ ζ' ι' ι t) :
    IsBilinearCoeff F I I' S ζ ζ' ι' ι t :=
  fun _ R hS l e φ β hx =>
    h _ R (isLocalWith_of_agree hρ₀ (fun ζ hζ => (hag ζ hζ).symm) hS) l e φ β
      (isSecondOrderExpansion_congr ((entryFun_eventuallyEq hρ₀ hag ι' ι e).symm) hx)
theorem coeffOne_eq (hρ₀ : 0 < ρ₀) (hag : ∀ ζ, IsSupBelow F ζ ρ₀ → S ζ = T ζ) :
    coeffOne F I I' S = coeffOne F I I' T := by
  funext ζ ι' ι
  have hp : IsLinearCoeff F I I' S ζ ι' ι = IsLinearCoeff F I I' T ζ ι' ι :=
    funext fun t => propext
      ⟨isLinearCoeff_of_agree hρ₀ fun ζ hζ => (hag ζ hζ).symm, isLinearCoeff_of_agree hρ₀ hag⟩
  simp only [coeffOne, hp]
theorem coeffTwo_eq (hρ₀ : 0 < ρ₀) (hag : ∀ ζ, IsSupBelow F ζ ρ₀ → S ζ = T ζ) :
    coeffTwo F I I' S = coeffTwo F I I' T := by
  funext ζ ζ' ι' ι
  have hp : IsBilinearCoeff F I I' S ζ ζ' ι' ι = IsBilinearCoeff F I I' T ζ ζ' ι' ι :=
    funext fun t => propext
      ⟨isBilinearCoeff_of_agree hρ₀ fun ζ hζ => (hag ζ hζ).symm, isBilinearCoeff_of_agree hρ₀ hag⟩
  simp only [coeffTwo, hp]
end Agreement
theorem claim_holds : Claim := by
  rintro F I I' - - - T S ⟨ρ, R, hT⟩ ⟨ρ₀, hρ₀, hag⟩
  refine ⟨⟨_, R, isLocalWith_of_agree hρ₀ hag hT⟩, fun p εPlus εMinus => ?_⟩
  have h0 : coeffZero F I I' S = coeffZero F I I' T :=
    hag 0 ⟨0, hρ₀, fun κ => by simp⟩
  have h1 := coeffOne_eq (I := I) (I' := I') hρ₀ hag
  have h2 := coeffTwo_eq (I := I) (I' := I') hρ₀ hag
  have hj : IsActionTriple F I I' S p εPlus εMinus = IsActionTriple F I I' T p εPlus εMinus :=
    funext fun A => propext (by simp only [IsActionTriple, h1, h2])
  simp only [jetAlong, h0, hj]
end LocalAgreement
end YangMills.Construction.PeriodicOperators
end
