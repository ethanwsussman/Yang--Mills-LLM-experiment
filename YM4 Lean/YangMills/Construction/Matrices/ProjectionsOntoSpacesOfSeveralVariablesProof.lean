import YangMills.Construction.Matrices.PeterWeylFunctionsOfSeveralVariablesAndKernelsForm
import YangMills.Construction.Matrices.ProjectionsOntoSpacesOfSeveralVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.ComplexMatrix2 HilbertSpaceBasics Schatten
namespace SpinHarmonics.ProjectionFormulas
open SeveralVariables
section Hilbert
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def rankOneSum (v : ι → H) (s : Finset ι) : H →L[ℂ] H :=
  ∑ i ∈ s, (innerSL ℂ (v i)).smulRight (v i)
theorem rankOneSum_apply (v : ι → H) (s : Finset ι) (x : H) :
    rankOneSum v s x = ∑ i ∈ s, (inner ℂ (v i) x : ℂ) • v i := by
  simp [rankOneSum]
theorem rankOneSum_apply_of_mem {v : ι → H} (hv : Orthonormal ℂ v) {s : Finset ι} {j : ι}
    (hj : j ∈ s) : rankOneSum v s (v j) = v j := by
  classical
  rw [rankOneSum_apply, Finset.sum_eq_single j]
  · have h := (orthonormal_iff_ite.mp hv) j j
    rw [if_pos rfl] at h
    rw [h, one_smul]
  · intro i _ hij
    rw [hv.2 hij, zero_smul]
  · intro h
    exact absurd hj h
theorem rankOneSum_apply_of_mem_span {v : ι → H} (hv : Orthonormal ℂ v) {s : Finset ι} {x : H}
    (hx : x ∈ Submodule.span ℂ (v '' (s : Set ι))) : rankOneSum v s x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact rankOneSum_apply_of_mem hv hj
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]
theorem rankOneSum_mem_span (v : ι → H) (s : Finset ι) (x : H) :
    rankOneSum v s x ∈ Submodule.span ℂ (v '' (s : Set ι)) := by
  rw [rankOneSum_apply]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
theorem inner_rankOneSum_left (v : ι → H) (s : Finset ι) (x y : H) :
    (inner ℂ (rankOneSum v s x) y : ℂ) = inner ℂ x (rankOneSum v s y) := by
  rw [rankOneSum_apply, rankOneSum_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
variable [CompleteSpace H]
theorem rankOneSum_isOrthProjOnto {v : ι → H} (hv : Orthonormal ℂ v)
    (s : Finset ι) :
    IsOrthProjOnto (rankOneSum v s)
      (Submodule.span ℂ (v '' (s : Set ι)) : Set H) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (inner_rankOneSum_left v s)
  · ext1 x
    exact (rankOneSum_apply_of_mem_span hv (rankOneSum_mem_span v s x)).symm
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact rankOneSum_mem_span v s y
    · intro hx
      exact ⟨x, rankOneSum_apply_of_mem_span hv hx⟩
end Hilbert
variable {J : Type} [Finite J]
theorem peterWeylVec_ae_eq (α : PeterWeylIndex J) :
    (peterWeylVec α : (J → specialUnitary) → ℂ) =ᵐ[haarPi J] peterWeylFn α :=
  ContinuousMap.coeFn_toLp (haarPi J) (peterWeylFn α)
theorem inner_peterWeylVec (α : PeterWeylIndex J) (F : HaarL2 J) :
    (inner ℂ (peterWeylVec α) F : ℂ) =
      ∫ u, star (peterWeylFn α u) * F u ∂haarPi J := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [peterWeylVec_ae_eq α] with u hu
  rw [hu, RCLike.inner_apply, mul_comm]
  rfl
theorem integrable_star_peterWeylFn_mul (α : PeterWeylIndex J) (F : HaarL2 J) :
    Integrable (fun u => star (peterWeylFn α u) * F u) (haarPi J) := by
  refine (L2.integrable_inner (𝕜 := ℂ) (peterWeylVec α) F).congr ?_
  filter_upwards [peterWeylVec_ae_eq α] with u hu
  rw [hu, RCLike.inner_apply, mul_comm]
  rfl
theorem sum_smul_peterWeylVec_ae_eq (s : Finset (PeterWeylIndex J)) (c : PeterWeylIndex J → ℂ) :
    (⇑(∑ α ∈ s, c α • peterWeylVec α : HaarL2 J) : (J → specialUnitary) → ℂ)
      =ᵐ[haarPi J] fun u => ∑ α ∈ s, c α * peterWeylFn α u := by
  have h : (∑ α ∈ s, c α • peterWeylVec α : HaarL2 J) =
      ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ (∑ α ∈ s, c α • peterWeylFn α) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_smul]
    rfl
  rw [h]
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarPi J)
    (∑ α ∈ s, c α • peterWeylFn α : C(J → specialUnitary, ℂ))] with u hu
  rw [hu, ContinuousMap.sum_apply]
  rfl
theorem hasKernel_rankOneSum (l : J → HalfNatural)
    (hk : ∀ u u' : J → specialUnitary, isotypicKernel l u u' =
      ∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α u')) :
    HasKernel (haarPi J) (fun p => isotypicKernel l p.1 p.2)
      (rankOneSum peterWeylVec (indicesWithSpins l)) := by
  intro F
  rw [rankOneSum_apply]
  refine (sum_smul_peterWeylVec_ae_eq _ _).trans (Filter.Eventually.of_forall fun u => ?_)
  have e : ∀ u', isotypicKernel l u u' * F u' =
      ∑ α ∈ indicesWithSpins l,
        peterWeylFn α u * (star (peterWeylFn α u') * F u') := by
    intro u'
    rw [hk, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => mul_assoc _ _ _
  change _ = ∫ u', isotypicKernel l u u' * F u' ∂haarPi J
  simp only [e]
  rw [integral_finsetSum _ fun α _ => (integrable_star_peterWeylFn_mul α F).const_mul _]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_const_mul, inner_peterWeylVec, mul_comm]
theorem isotypicProj_eq_rankOneSum (l : J → HalfNatural)
    (hk : ∀ u u' : J → specialUnitary, isotypicKernel l u u' =
      ∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α u')) :
    isotypicProj l = rankOneSum peterWeylVec (indicesWithSpins l) := by
  have hQ := hasKernel_rankOneSum l hk
  have hs : HasKernel (haarPi J) (fun p => isotypicKernel l p.1 p.2)
      (isotypicProj l) := Classical.epsilon_spec (p := HasKernel (haarPi J)
        (fun p => isotypicKernel l p.1 p.2)) ⟨_, hQ⟩
  ext1 F
  exact Lp.ext ((hs F).trans (hQ F).symm)
theorem mem_indicesWithSpins {l : J → HalfNatural} {α : PeterWeylIndex J} :
    α ∈ indicesWithSpins l ↔ spins α = l :=
  Set.Finite.mem_toFinset _
theorem truncationProj_eq_rankOneSum (ϰ : HalfNatural)
    (h : ∀ l : J → HalfNatural, isotypicProj l =
      rankOneSum peterWeylVec (indicesWithSpins l)) :
    truncationProj J ϰ = rankOneSum peterWeylVec (boundedIndices J ϰ) := by
  classical
  have hmaps : ∀ α ∈ boundedIndices J ϰ, spins α ∈ boundedWeights J ϰ := fun α hα =>
    mem_boundedWeights.mpr (mem_boundedIndices.mp hα)
  rw [rankOneSum, ← Finset.sum_fiberwise_of_maps_to hmaps, truncationProj]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [h l, rankOneSum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext α
  rw [Finset.mem_filter, mem_indicesWithSpins]
  constructor
  · rintro rfl
    exact ⟨mem_boundedIndices.mpr (mem_boundedWeights.mp hl), rfl⟩
  · exact fun h => h.2
theorem prodCoeffSpanL2_eq_span (l : J → HalfNatural)
    (hs : Submodule.span ℂ (peterWeylFn '' {α : PeterWeylIndex J | spins α = l}) =
      prodCoeffSpan l) :
    prodCoeffSpanL2 l = Submodule.span ℂ
      (peterWeylVec '' (indicesWithSpins l : Set (PeterWeylIndex J))) := by
  rw [prodCoeffSpanL2, ← hs, Submodule.map_span, Set.image_image]
  congr 1
  ext F
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, mem_indicesWithSpins.mpr hα, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, mem_indicesWithSpins.mp hα, rfl⟩
theorem truncatedCoeffSpanL2_eq_span (ϰ : HalfNatural)
    (hs : ∀ l : J → HalfNatural, prodCoeffSpanL2 l = Submodule.span ℂ
      (peterWeylVec '' (indicesWithSpins l : Set (PeterWeylIndex J)))) :
    truncatedCoeffSpanL2 J ϰ = Submodule.span ℂ
      (peterWeylVec '' (boundedIndices J ϰ : Set (PeterWeylIndex J))) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.map_le_iff_le_comap.mpr (iSup₂_le fun l hl => ?_)
    refine Submodule.map_le_iff_le_comap.mp ?_
    change prodCoeffSpanL2 l ≤ _
    rw [hs l]
    refine Submodule.span_mono (Set.image_mono fun α hα => ?_)
    have hw := mem_indicesWithSpins.mp hα
    refine mem_boundedIndices.mpr fun b => ?_
    have hb : (α b).spin = l b := congrFun hw b
    rw [hb]
    exact mem_boundedWeights.mp hl b
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨α, hα, rfl⟩
    have hl : spins α ∈ boundedWeights J ϰ :=
      mem_boundedWeights.mpr (mem_boundedIndices.mp hα)
    have hmem : peterWeylVec α ∈ prodCoeffSpanL2 (spins α) := by
      rw [hs]
      exact Submodule.subset_span ⟨α, mem_indicesWithSpins.mpr rfl, rfl⟩
    have hle : prodCoeffSpan (spins α) ≤ truncatedCoeffSpan J ϰ :=
      le_iSup₂_of_le (spins α) hl le_rfl
    exact Submodule.map_mono hle hmem
theorem isotypicProjProperties_of_peterWeyl (hPW : PeterWeylOrthonormalAndKernel) :
    IsotypicProjProperties := by
  intro J _ _ l ϰ
  have hOrtho : Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J) :=
    (hPW J l).1
  have hProj : ∀ l : J → HalfNatural, isotypicProj l =
      rankOneSum peterWeylVec (indicesWithSpins l) := fun l =>
    isotypicProj_eq_rankOneSum l (hPW J l).2.2.2.1
  have hSpace : ∀ l : J → HalfNatural, prodCoeffSpanL2 l = Submodule.span ℂ
      (peterWeylVec '' (indicesWithSpins l : Set (PeterWeylIndex J))) := fun l =>
    prodCoeffSpanL2_eq_span l (hPW J l).2.2.1
  refine ⟨fun F => ?_, ?_, ?_, ?_⟩
  · rw [hProj, rankOneSum_apply]
  · rw [hProj, hSpace]
    exact rankOneSum_isOrthProjOnto hOrtho _
  · rw [truncationProj_eq_rankOneSum ϰ hProj, truncatedCoeffSpanL2_eq_span ϰ hSpace]
    exact rankOneSum_isOrthProjOnto hOrtho _
  · intro l₁ l₂ hne
    rw [hSpace, hSpace, Submodule.isOrtho_span]
    rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    refine hOrtho.2 fun hαβ => hne ?_
    rw [← mem_indicesWithSpins.mp hα, ← mem_indicesWithSpins.mp hβ, hαβ]
end SpinHarmonics.ProjectionFormulas
end YangMills.Construction
end
