import YangMills.Construction.SpectralTheory.MatrixMeasuresAndCommutation
import Mathlib
set_option autoImplicit false
open Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.WholeSpaceSpectral
open BorelSpectral (BorelSubsets SpectralMeasure)
abbrev SpectralMeasureOnSpace (n : ℕ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : Type _ :=
  SpectralMeasure (univ : Set (Fin n → ℝ)) K
variable {n m : ℕ}
def restrictToUniv (S : BorelSubsets (Fin n → ℝ)) : BorelSubsets (univ : Set (Fin n → ℝ)) :=
  ⟨Subtype.val ⁻¹' S.1, measurable_subtype_coe S.2⟩
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def opAt (E : SpectralMeasureOnSpace n K) (S : BorelSubsets (Fin n → ℝ)) : K →L[ℂ] K :=
  E (restrictToUniv S)
def diagSetFn (E : SpectralMeasureOnSpace n K) (v : K) (S : BorelSubsets (Fin n → ℝ)) : ℂ :=
  E.matrixCoeff v v (restrictToUniv S)
theorem diagSetFn_apply (E : SpectralMeasureOnSpace n K) (v : K) (S : BorelSubsets (Fin n → ℝ)) :
    diagSetFn E v S = ⟪v, opAt E S v⟫_ℂ :=
  rfl
def IsSupportedOn (E : SpectralMeasureOnSpace n K) (C : BorelSubsets (Fin n → ℝ)) : Prop :=
  E.IsCarriedBy (restrictToUniv C)
theorem isSupportedOn_iff (E : SpectralMeasureOnSpace n K) (C : BorelSubsets (Fin n → ℝ)) :
    IsSupportedOn E C ↔ opAt E ⟨univ \ C.1, MeasurableSet.univ.diff C.2⟩ = 0 := by
  have h : (⟨(restrictToUniv C).1ᶜ, (restrictToUniv C).2.compl⟩ :
      BorelSubsets (univ : Set (Fin n → ℝ))) =
      restrictToUniv ⟨univ \ C.1, MeasurableSet.univ.diff C.2⟩ :=
    Subtype.ext (by ext y; simp [restrictToUniv])
  unfold IsSupportedOn SpectralMeasure.IsCarriedBy opAt
  rw [h]
def mapBy (E : SpectralMeasureOnSpace n K) (hm : 1 ≤ m) (f : (Fin n → ℝ) → (Fin m → ℝ))
    (hf : Measurable f) : SpectralMeasureOnSpace m K :=
  E.pushforward hm MeasurableSet.univ (fun y => ⟨f y.1, mem_univ _⟩)
    ((hf.comp measurable_subtype_coe).subtype_mk)
end YangMills.Construction.WholeSpaceSpectral
