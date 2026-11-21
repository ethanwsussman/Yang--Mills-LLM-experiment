import YangMills.Construction.TwoPoints.SignsOfTheContinuumFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace TwoPoints
open InfiniteLattice (AmbientSpace)
abbrev compactC1Complex : Submodule ℂ (AmbientSpace → ℂ) := cc1In univ
abbrev compactC1Real : Submodule ℝ (AmbientSpace → ℂ) := realValuedPart compactC1Complex
def DisjointSupports (f h : AmbientSpace → ℂ) : Prop := Disjoint (tsupport f) (tsupport h)
def IsDisjointForm (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  (∀ f ∈ compactC1Real, ∀ h ∈ compactC1Real, DisjointSupports f h → S f h = S h f) ∧
    ∀ (a₁ a₂ : ℝ), ∀ f₁ ∈ compactC1Real, ∀ f₂ ∈ compactC1Real, ∀ h ∈ compactC1Real,
      DisjointSupports f₁ h → DisjointSupports f₂ h →
        S (a₁ • f₁ + a₂ • f₂) h = a₁ * S f₁ h + a₂ * S f₂ h
def realPartFun (f : AmbientSpace → ℂ) : AmbientSpace → ℂ := fun x => ((f x).re : ℂ)
def imagPartFun (f : AmbientSpace → ℂ) : AmbientSpace → ℂ := fun x => ((f x).im : ℂ)
def complexifyForm (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (f h : AmbientSpace → ℂ) : ℂ :=
  ((S (realPartFun f) (realPartFun h) - S (imagPartFun f) (imagPartFun h) : ℝ) : ℂ) +
    Complex.I * ((S (realPartFun f) (imagPartFun h) +
      S (imagPartFun f) (realPartFun h) : ℝ) : ℂ)
theorem realPartFun_add_I_smul {u v : AmbientSpace → ℂ} (hu : ∀ x, (u x).im = 0)
    (hv : ∀ x, (v x).im = 0) : realPartFun (u + Complex.I • v) = u := by
  funext x
  apply Complex.ext <;> simp [realPartFun, hu x, hv x]
theorem imagPartFun_add_I_smul {u v : AmbientSpace → ℂ} (hu : ∀ x, (u x).im = 0)
    (hv : ∀ x, (v x).im = 0) : imagPartFun (u + Complex.I • v) = v := by
  funext x
  apply Complex.ext <;> simp [imagPartFun, hu x, hv x]
theorem disjointSupports_zero_left (h : AmbientSpace → ℂ) : DisjointSupports 0 h := by
  simp [DisjointSupports, tsupport]
theorem IsDisjointForm.apply_zero_left {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hS : IsDisjointForm S) {h : AmbientSpace → ℂ} (hh : h ∈ compactC1Real) : S 0 h = 0 := by
  have key := hS.2 0 0 0 compactC1Real.zero_mem 0 compactC1Real.zero_mem h hh
    (disjointSupports_zero_left h) (disjointSupports_zero_left h)
  simpa using key
theorem IsDisjointForm.apply_zero_right {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hS : IsDisjointForm S) {f : AmbientSpace → ℂ} (hf : f ∈ compactC1Real) : S f 0 = 0 := by
  rw [← hS.1 0 compactC1Real.zero_mem f hf (disjointSupports_zero_left f)]
  exact hS.apply_zero_left hf
theorem realPartFun_of_mem_compactC1Real {f : AmbientSpace → ℂ} (hf : f ∈ compactC1Real) :
    realPartFun f = f := by
  funext x
  apply Complex.ext
  · simp [realPartFun]
  · simpa [realPartFun] using (hf.2 x).symm
theorem imagPartFun_of_mem_compactC1Real {f : AmbientSpace → ℂ} (hf : f ∈ compactC1Real) :
    imagPartFun f = 0 := by
  funext x
  simp [imagPartFun, hf.2 x]
theorem IsDisjointForm.complexifyForm_of_mem_compactC1Real
    {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} (hS : IsDisjointForm S)
    {f h : AmbientSpace → ℂ} (hf : f ∈ compactC1Real) (hh : h ∈ compactC1Real) :
    complexifyForm S f h = (S f h : ℂ) := by
  simp [complexifyForm, realPartFun_of_mem_compactC1Real hf, realPartFun_of_mem_compactC1Real hh,
    imagPartFun_of_mem_compactC1Real hf, imagPartFun_of_mem_compactC1Real hh,
    hS.apply_zero_left hh, hS.apply_zero_right hf, hS.apply_zero_left compactC1Real.zero_mem]
end TwoPoints
end YangMills.Construction
end
