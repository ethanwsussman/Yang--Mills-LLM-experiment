import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.SpectralCalculus
variable {V : Type} [AddCommGroup V] [Module ℂ V]
structure PosFormBasics (b : V → V → ℂ) : Prop where
  norm_le_mul : ∀ f h, ‖b f h‖ ≤ formSeminorm b f * formSeminorm b h
  formSeminorm_add_le : ∀ f h, formSeminorm b (f + h) ≤ formSeminorm b f + formSeminorm b h
  exists_submodule_null : ∃ N : Submodule ℂ V, ∀ f, f ∈ N ↔ IsNullForForm b f
  add_null : ∀ f h f₀ h₀, IsNullForForm b f₀ → IsNullForForm b h₀ →
    b (f + f₀) (h + h₀) = b f h
  polarization : ∀ f h, 4 * b f h =
    ∑ l ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ), l * (formSeminorm b (l • f + h) : ℂ) ^ 2
structure SeparatedCompletionBasics (b : V → V → ℂ) : Prop where
  isFormCauchy_add_smul : ∀ (f h : ℕ → V) (a : ℂ), IsFormCauchy b f →
    IsFormCauchy b h → IsFormCauchy b fun j => f j + a • h j
  formEquivalent_add_smul : ∀ (f f' h h' : ℕ → V) (a : ℂ), IsFormCauchy b f →
    IsFormCauchy b f' → IsFormCauchy b h → IsFormCauchy b h' →
    FormEquivalent b f f' → FormEquivalent b h h' →
    FormEquivalent b (fun j => f j + a • h j) (fun j => f' j + a • h' j)
  exists_tendsto_form : ∀ f h : ℕ → V, IsFormCauchy b f → IsFormCauchy b h →
    ∃ z : ℂ, Tendsto (fun j => b (f j) (h j)) atTop (𝓝 z)
  limit_eq_of_formEquivalent : ∀ (f f' h h' : ℕ → V) (z z' : ℂ), IsFormCauchy b f →
    IsFormCauchy b f' → IsFormCauchy b h → IsFormCauchy b h' →
    FormEquivalent b f f' → FormEquivalent b h h' →
    Tendsto (fun j => b (f j) (h j)) atTop (𝓝 z) →
    Tendsto (fun j => b (f' j) (h' j)) atTop (𝓝 z') → z = z'
  seqClass_add_smul : ∀ (f h : ℕ → V) (a : ℂ) (hf : IsFormCauchy (posHermitianPart b) f)
    (hh : IsFormCauchy (posHermitianPart b) h)
    (hs : IsFormCauchy (posHermitianPart b) fun j => f j + a • h j),
    seqClass b (fun j => f j + a • h j) hs =
      seqClass b f hf + a • seqClass b h hh
  tendsto_inner_seqClass : ∀ (f h : ℕ → V) (hf : IsFormCauchy (posHermitianPart b) f)
    (hh : IsFormCauchy (posHermitianPart b) h),
    Tendsto (fun j => b (f j) (h j)) atTop
      (𝓝 (inner ℂ (seqClass b f hf) (seqClass b h hh)))
  isCompleteForm :
    IsCompleteForm fun u v : SeparatedCompletion b => inner ℂ u v
  isLinearMap_constClass : IsLinearMap ℂ (constClass b)
  inner_constClass : ∀ f h, inner ℂ (constClass b f) (constClass b h) = b f h
  constClass_eq_constClass_iff : ∀ f h, constClass b f = constClass b h ↔ IsNullForForm b (f - h)
  isSeqDense_range_constClass : IsSeqDense (Set.range (constClass b))
def IsCompletionExtension (b : V → V → ℂ) (A : V →ₗ[ℂ] V)
    (T : SeparatedCompletion b →L[ℂ] SeparatedCompletion b) : Prop :=
  ∀ f, T (constClass b f) = constClass b (A f)
def IsFormBoundedBy (b : V → V → ℂ) (A : V →ₗ[ℂ] V) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ f, formSeminorm b (A f) ≤ C * formSeminorm b f
structure CompletionExtensionBasics (b : V → V → ℂ) (A : V →ₗ[ℂ] V) (C : ℝ) : Prop where
  constClass_map_eq : ∀ f h, constClass b f = constClass b h →
    constClass b (A f) = constClass b (A h)
  existsUnique_extension :
    ∃! T : SeparatedCompletion b →L[ℂ] SeparatedCompletion b, IsCompletionExtension b A T
  norm_le : ∀ T, IsCompletionExtension b A T → ‖T‖ ≤ C
  extension_comp : ∀ (A' : V →ₗ[ℂ] V) (C' : ℝ), IsFormBoundedBy b A' C' → ∀ T T' S,
    IsCompletionExtension b A T → IsCompletionExtension b A' T' →
    IsCompletionExtension b (A ∘ₗ A') S → S = T * T'
  extension_adjoint : ∀ (A' : V →ₗ[ℂ] V) (C' : ℝ), IsFormBoundedBy b A' C' → ∀ T T',
    IsCompletionExtension b A T → IsCompletionExtension b A' T' →
    (∀ f h, b (A f) h = b f (A' h)) →
    ∀ u v, inner ℂ (T u) v = inner ℂ u (T' v)
  extension_isometry : (∀ f, formSeminorm b (A f) = formSeminorm b f) → ∀ T,
    IsCompletionExtension b A T → ∀ v, ‖T v‖ = ‖v‖
structure InnerContinuousDenseExt (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Prop where
  tendsto_inner : ∀ (u v : ℕ → H) (x y : H), Tendsto u atTop (𝓝 x) → Tendsto v atTop (𝓝 y) →
    Tendsto (fun j => inner ℂ (u j) (v j)) atTop (𝓝 (inner ℂ x y))
  eq_of_eqOn_dense : ∀ (S : Set H) (B B' : H →L[ℂ] H), IsSeqDense S →
    (∀ s ∈ S, B s = B' s) → B = B'
def FormCompletionAndBoundedExtension : Prop :=
  (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (b : V → V → ℂ), IsPosHermitianForm b →
    PosFormBasics b ∧ SeparatedCompletionBasics b ∧
      ∀ (A : V →ₗ[ℂ] V) (C : ℝ), IsFormBoundedBy b A C → CompletionExtensionBasics b A C) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    InnerContinuousDenseExt H
end YangMills.Construction.SpectralCalculus
