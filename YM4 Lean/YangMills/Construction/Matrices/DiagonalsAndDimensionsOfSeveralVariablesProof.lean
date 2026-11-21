import YangMills.Construction.Matrices.ClassicalHarmonicAnalysisOnG
import YangMills.Construction.Matrices.DiagonalsAndDimensionsOfSeveralVariables
import YangMills.Construction.Matrices.PeterWeylFunctionsOfSeveralVariablesAndKernelsForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open HilbertSpaceBasics Matrices.ComplexMatrix2
namespace SpinHarmonics.SeveralVariables.KernelDiagonals
variable {J : Type} [Finite J]
theorem mem_indicesWithSpins_iff {l : J → HalfNatural} {α : PeterWeylIndex J} :
    α ∈ indicesWithSpins l ↔ spins α = l :=
  Set.Finite.mem_toFinset _
theorem isotypicKernel_diag (hC : HarmonicAnalysisFacts) (l : J → HalfNatural)
    (u : J → Matrices.ComplexMatrix2.specialUnitary) :
    isotypicKernel l u u = ((∏ᶠ b, (2 * (l b).toReal + 1) ^ 2 : ℝ) : ℂ) := by
  let _ : Fintype J := Fintype.ofFinite J
  simp only [isotypicKernel, finprod_eq_prod_of_fintype]
  push_cast
  refine Finset.prod_congr rfl fun b _ => ?_
  have hone := (hC (l b) (l b)).2.2.1.apply_one
  rw [mul_inv_cancel, hone]
  push_cast
  ring
theorem card_indicesWithSpins (l : J → HalfNatural) :
    ((indicesWithSpins l).card : ℝ) = ∏ᶠ b, (2 * (l b).toReal + 1) ^ 2 := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  let f : (∀ b, Fin ((l b).doubled + 1) × Fin ((l b).doubled + 1)) → PeterWeylIndex J :=
    fun x b => ⟨l b, (x b).1, (x b).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    funext b
    have hb := congrFun hxy b
    simp only [f, PeterWeylLabel.mk.injEq, heq_eq_eq, true_and] at hb
    exact Prod.ext hb.1 hb.2
  have himg : indicesWithSpins l = Finset.univ.image f := by
    ext α
    rw [mem_indicesWithSpins_iff, Finset.mem_image]
    constructor
    · rintro rfl
      exact ⟨fun b => ((α b).rowIdx, (α b).colIdx), Finset.mem_univ _, rfl⟩
    · rintro ⟨x, -, rfl⟩
      rfl
  rw [himg, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_pi,
    finprod_eq_prod_of_fintype]
  push_cast
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [Fintype.card_prod, Fintype.card_fin, HalfNatural.toReal]
  push_cast
  ring
theorem linearIndependent_peterWeylFn
    (hO : Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J)) :
    LinearIndependent ℂ (peterWeylFn : PeterWeylIndex J → C(J → Matrices.ComplexMatrix2.specialUnitary, ℂ)) := by
  have hcomp : LinearIndependent ℂ
      ((ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ).toLinearMap ∘
        (peterWeylFn : PeterWeylIndex J → C(J → Matrices.ComplexMatrix2.specialUnitary, ℂ))) := hO.linearIndependent
  exact LinearIndependent.of_comp _ hcomp
theorem finrank_span_peterWeylFn_image
    (hO : Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J))
    (s : Finset (PeterWeylIndex J)) :
    Module.finrank ℂ (Submodule.span ℂ
      ((peterWeylFn : PeterWeylIndex J → C(J → Matrices.ComplexMatrix2.specialUnitary, ℂ)) '' (s : Set (PeterWeylIndex J)))) = s.card := by
  have hli : LinearIndependent ℂ (fun α : s => (peterWeylFn α.1 : C(J → Matrices.ComplexMatrix2.specialUnitary, ℂ))) :=
    (linearIndependent_peterWeylFn hO).comp _ Subtype.val_injective
  have hrange : Set.range (fun α : s => (peterWeylFn α.1 : C(J → Matrices.ComplexMatrix2.specialUnitary, ℂ))) =
      (peterWeylFn : PeterWeylIndex J → C(J → Matrices.ComplexMatrix2.specialUnitary, ℂ)) '' (s : Set (PeterWeylIndex J)) := by
    ext F
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨α.1, α.2, rfl⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨⟨α, hα⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]
theorem filter_boundedIndices_spins {κ : HalfNatural} {l : J → HalfNatural} (hl : l ∈ boundedWeights J κ) :
    open Classical in
    (boundedIndices J κ).filter (fun α => spins α = l) = indicesWithSpins l := by
  classical
  ext α
  rw [Finset.mem_filter, mem_indicesWithSpins_iff, mem_boundedIndices]
  refine ⟨fun h => h.2, fun h => ⟨fun b => ?_, h⟩⟩
  have hb : (α b).spin = l b := congrFun h b
  rw [hb]
  exact mem_boundedWeights.mp hl b
theorem spins_mem_boundedWeights {κ : HalfNatural} {α : PeterWeylIndex J} (hα : α ∈ boundedIndices J κ) :
    spins α ∈ boundedWeights J κ :=
  mem_boundedWeights.mpr (mem_boundedIndices.mp hα)
theorem sum_boundedIndices_eq_sum_fibers (κ : HalfNatural) (g : PeterWeylIndex J → ℝ) :
    ∑ α ∈ boundedIndices J κ, g α =
      ∑ l ∈ boundedWeights J κ, ∑ α ∈ indicesWithSpins l, g α := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun α hα => spins_mem_boundedWeights hα)]
  exact Finset.sum_congr rfl fun l hl => by rw [filter_boundedIndices_spins hl]
theorem truncatedCoeffSpan_eq_span
    (hSpan : ∀ l : J → HalfNatural, Submodule.span ℂ (peterWeylFn '' {α : PeterWeylIndex J | spins α = l}) =
      prodCoeffSpan l) (κ : HalfNatural) :
    truncatedCoeffSpan J κ = Submodule.span ℂ
      ((peterWeylFn : PeterWeylIndex J → C(J → Matrices.ComplexMatrix2.specialUnitary, ℂ)) ''
        (boundedIndices J κ : Set (PeterWeylIndex J))) := by
  refine le_antisymm (iSup₂_le fun l hl => ?_) (Submodule.span_le.mpr ?_)
  · rw [← hSpan l]
    refine Submodule.span_mono (Set.image_mono fun α hα => ?_)
    have hα' : spins α = l := hα
    have hfil := filter_boundedIndices_spins hl
    classical
    have hmem : α ∈ indicesWithSpins l := mem_indicesWithSpins_iff.mpr hα'
    rw [← hfil] at hmem
    exact (Finset.mem_filter.mp hmem).1
  · rintro _ ⟨α, hα, rfl⟩
    have hin : peterWeylFn α ∈ prodCoeffSpan (spins α) := by
      rw [← hSpan]
      exact Submodule.subset_span ⟨α, rfl, rfl⟩
    exact (le_iSup₂_of_le (f := fun l (_ : l ∈ boundedWeights J κ) =>
      prodCoeffSpan l) (spins α) (spins_mem_boundedWeights hα) le_rfl) hin
theorem sum_norm_sq_peterWeylFn (hC : HarmonicAnalysisFacts) (l : J → HalfNatural)
    (hK : ∀ u v : J → Matrices.ComplexMatrix2.specialUnitary, isotypicKernel l u v =
      ∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α v))
    (u : J → Matrices.ComplexMatrix2.specialUnitary) :
    ∑ α ∈ indicesWithSpins l, ‖peterWeylFn α u‖ ^ 2 =
      ∏ᶠ b, (2 * (l b).toReal + 1) ^ 2 := by
  have hd := hK u u
  rw [isotypicKernel_diag hC] at hd
  have hsum : (∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α u)) =
      ((∑ α ∈ indicesWithSpins l, ‖peterWeylFn α u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  rw [hsum] at hd
  exact (Complex.ofReal_injective hd).symm
theorem kernelDiagonalsAreDims_holds (hC : HarmonicAnalysisFacts)
    (hPW : PeterWeylOrthonormalAndKernel) : KernelDiagonalsAreDims := by
  intro J _ _ l κ
  have hO : Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J) := (hPW J l).1
  have hSpan : ∀ l : J → HalfNatural, Submodule.span ℂ
      (peterWeylFn '' {α : PeterWeylIndex J | spins α = l}) = prodCoeffSpan l :=
    fun l => (hPW J l).2.2.1
  have hK : ∀ (l : J → HalfNatural) (u v : J → Matrices.ComplexMatrix2.specialUnitary), isotypicKernel l u v =
      ∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α v) :=
    fun l => (hPW J l).2.2.2.1
  refine ⟨fun u => ⟨?_, ?_, isotypicKernel_diag hC l u⟩, ?_, ?_⟩
  · simp only [truncatedDim, truncationKernel]
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [isotypicKernel_diag hC]
  · rw [sum_boundedIndices_eq_sum_fibers]
    exact Finset.sum_congr rfl fun m _ => (sum_norm_sq_peterWeylFn hC m (hK m) u).symm
  · rw [truncatedCoeffSpan_eq_span hSpan, finrank_span_peterWeylFn_image hO]
    have hc := sum_boundedIndices_eq_sum_fibers (J := J) κ fun _ => (1 : ℝ)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
    rw [hc]
    exact Finset.sum_congr rfl fun m _ => (card_indicesWithSpins m).symm
  · have hs : prodCoeffSpan l = Submodule.span ℂ
        ((peterWeylFn : PeterWeylIndex J → C(J → Matrices.ComplexMatrix2.specialUnitary, ℂ)) ''
          (indicesWithSpins l : Set (PeterWeylIndex J))) := by
      rw [← hSpan l]
      congr 2
      ext α
      simp [mem_indicesWithSpins_iff]
    rw [hs, finrank_span_peterWeylFn_image hO]
    exact (card_indicesWithSpins l).symm
end SpinHarmonics.SeveralVariables.KernelDiagonals
end YangMills.Construction
end
