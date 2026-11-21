import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace
open YangMills.Construction.SmoothMaps
variable {n : ℕ}
def complexPart (e : Fin 2) (z : ℂ) : ℂ := if e = 0 then (z.re : ℂ) else (z.im : ℂ)
def fnComplexPart (e : Fin 2) (φ : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ := complexPart e ∘ φ
def tupleComplexParts (ε : Fin n → Fin 2) (φ : FnTuple n) : FnTuple n :=
  fun i => fnComplexPart (ε i) (φ i)
theorem complexPart_zero (e : Fin 2) : complexPart e 0 = 0 := by
  unfold complexPart
  split_ifs <;> simp
theorem contDiff_complexPart (e : Fin 2) : ContDiff ℝ ∞ (complexPart e) := by
  unfold complexPart
  split_ifs
  · exact Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
  · exact Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff
theorem tsupport_fnComplexPart_subset (e : Fin 2) (φ : (Fin 4 → ℝ) → ℂ) :
    tsupport (fnComplexPart e φ) ⊆ tsupport φ :=
  tsupport_comp_subset (complexPart_zero e) φ
theorem tupleComplexParts_mem (ε : Fin n → Fin 2) (φ : smoothComplexTupleSet n) :
    tupleComplexParts ε φ.1 ∈ smoothRealTupleSet n := by
  obtain ⟨φ, hφ, hdisj⟩ := φ
  have hsmooth : SmoothEntries (tupleComplexParts ε φ) := fun i =>
    (contDiff_complexPart (ε i)).comp (hφ i).1
  refine ⟨⟨fun i => ⟨?_, ?_, ?_, subset_univ _⟩, ?_⟩, hsmooth⟩
  · intro y
    simp only [tupleComplexParts, fnComplexPart, complexPart, Function.comp_apply]
    split_ifs <;> simp
  · exact (hsmooth i).of_le (by exact_mod_cast le_top)
  · exact (hφ i).2.comp_left (complexPart_zero (ε i))
  · intro i i' hne
    exact (hdisj i i' hne).mono (tsupport_fnComplexPart_subset _ _)
      (tsupport_fnComplexPart_subset _ _)
def complexify (T : smoothRealTupleSet n → ℝ) (φ : smoothComplexTupleSet n) : ℂ :=
  ∑ ε : Fin n → Fin 2,
    Complex.I ^ (∑ i, (ε i : ℕ)) * (T ⟨tupleComplexParts ε φ.1, tupleComplexParts_mem ε φ⟩ : ℂ)
end YangMills.Construction.ConfigSpace
