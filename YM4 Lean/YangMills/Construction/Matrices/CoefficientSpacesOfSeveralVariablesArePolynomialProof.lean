import YangMills.Construction.Matrices.ClassicalHarmonicAnalysisOnG
import YangMills.Construction.Matrices.CoefficientSpacesOfSeveralVariablesArePolynomial
import YangMills.Construction.Matrices.PeterWeylFunctionsOfSeveralVariablesAndKernelsForm
import YangMills.Construction.Matrices.PolynomialsAreSpannedByThePeterWeylFunctionsForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics.SeveralVariables
open MeasureTheory Matrices.ComplexMatrix2 HilbertSpaceBasics
section
variable {J : Type} [Finite J]
theorem star_mem_coeffSpan (h : HarmonicAnalysisFacts) (t : HalfNatural)
    {x : C(specialUnitary, ℂ)} (hx : x ∈ coeffSpan t) : star x ∈ coeffSpan t := by
  obtain ⟨g, hg, e⟩ := (h t t).2.1.star_mem x hx
  have hg' : g = star x := ContinuousMap.ext e
  rwa [← hg']
theorem star_coordProduct (φ : J → C(specialUnitary, ℂ)) :
    star (coordProduct φ) = coordProduct fun j => star (φ j) := by
  let _ : Fintype J := Fintype.ofFinite J
  ext u
  change star (∏ᶠ j, φ j (u j)) = ∏ᶠ j, star (φ j (u j))
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← starRingEnd_apply, map_prod]
  rfl
theorem star_mem_prodCoeffSpan (h : HarmonicAnalysisFacts)
    (s : J → HalfNatural) {F : C(J → specialUnitary, ℂ)} (hF : F ∈ prodCoeffSpan s) :
    star F ∈ prodCoeffSpan s := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    rw [star_coordProduct]
    exact Submodule.subset_span ⟨_, fun j => star_mem_coeffSpan h _ (hφ j), rfl⟩
  | zero =>
    rw [star_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [star_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [star_smul]
    exact Submodule.smul_mem _ _ hx
variable (J) in
theorem truncatedCoeffSpan_eq_iSup (κ : HalfNatural) :
    truncatedCoeffSpan J κ =
      ⨆ s : {s : J → HalfNatural // s ∈ boundedWeights J κ}, prodCoeffSpan s.1 := by
  rw [truncatedCoeffSpan, iSup_subtype']
end
section
variable {J : Type} [Finite J] [Nonempty J]
theorem prodCoeffSpan_eq_span (P : PeterWeylOrthonormalAndKernel)
    (s : J → HalfNatural) :
    prodCoeffSpan s =
      Submodule.span ℂ (peterWeylFn '' {α : PeterWeylIndex J | spins α = s}) :=
  (P J s).2.2.1.symm
theorem finiteDimensional_prodCoeffSpan
    (P : PeterWeylOrthonormalAndKernel) (s : J → HalfNatural) :
    FiniteDimensional ℂ (prodCoeffSpan s) := by
  rw [prodCoeffSpan_eq_span P s]
  exact FiniteDimensional.span_of_finite ℂ ((finite_indicesWithSpins s).image _)
theorem prodCoeffSpan_le_span (P : PeterWeylOrthonormalAndKernel)
    (s : J → HalfNatural) :
    prodCoeffSpan s ≤
      Submodule.span ℂ (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ))) := by
  rw [prodCoeffSpan_eq_span P s]
  exact Submodule.span_mono (Set.image_subset_range _ _)
theorem isStarClosedPolySpan_prodCoeffSpan (h : HarmonicAnalysisFacts)
    (P : PeterWeylOrthonormalAndKernel)
    (S : PolynomialIffInPeterWeylSpan) (s : J → HalfNatural) :
    IsStarClosedPolySpan (prodCoeffSpan s) :=
  ⟨finiteDimensional_prodCoeffSpan P s,
    fun F hF => (S J F).mpr ⟨F, prodCoeffSpan_le_span P s hF, fun _ => rfl⟩,
    fun _ hF => star_mem_prodCoeffSpan h s hF⟩
theorem isStarClosedPolySpan_truncatedCoeffSpan (h : HarmonicAnalysisFacts)
    (P : PeterWeylOrthonormalAndKernel)
    (S : PolynomialIffInPeterWeylSpan) (κ : HalfNatural) :
    IsStarClosedPolySpan (truncatedCoeffSpan J κ) := by
  rw [truncatedCoeffSpan_eq_iSup]
  refine ⟨?_, fun F hF => ?_, fun F hF => ?_⟩
  · have : ∀ s : {s : J → HalfNatural // s ∈ boundedWeights J κ},
        FiniteDimensional ℂ (prodCoeffSpan s.1) :=
      fun s => finiteDimensional_prodCoeffSpan P s.1
    exact Submodule.finiteDimensional_iSup _
  · have hle : (⨆ s : {s : J → HalfNatural // s ∈ boundedWeights J κ},
        prodCoeffSpan s.1) ≤
        Submodule.span ℂ (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ))) :=
      iSup_le fun s => prodCoeffSpan_le_span P s.1
    exact (S J F).mpr ⟨F, hle hF, fun _ => rfl⟩
  · refine Submodule.iSup_induction _
      (motive := fun x => star x ∈
        ⨆ s : {s : J → HalfNatural // s ∈ boundedWeights J κ}, prodCoeffSpan s.1)
      hF (fun s x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · exact Submodule.mem_iSup_of_mem s (star_mem_prodCoeffSpan h s.1 hx)
    · rw [star_add]
      exact Submodule.add_mem _ hx hy
end
theorem coeffSpansArePolynomial_of (h : HarmonicAnalysisFacts)
    (P : PeterWeylOrthonormalAndKernel)
    (S : PolynomialIffInPeterWeylSpan) : CoeffSpansArePolynomial := by
  intro J _ _ s κ
  exact ⟨isStarClosedPolySpan_truncatedCoeffSpan h P S κ,
    isStarClosedPolySpan_prodCoeffSpan h P S s⟩
end YangMills.Construction.SpinHarmonics.SeveralVariables
end
