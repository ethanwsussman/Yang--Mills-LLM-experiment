module

public import NoContact.Space
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NoContact

/-- Fields essentially supported in a compact subset of `s`. -/
def compactSubmodule (s : Set X) : Submodule ℂ L2 where
  carrier := {f | ∃ K, IsCompact K ∧ K ⊆ s ∧ Supported K f}
  zero_mem' := ⟨∅, isCompact_empty, empty_subset s, supported_zero ∅⟩
  add_mem' := by
    rintro f g ⟨K, hK, hKs, hf⟩ ⟨L, hL, hLs, hg⟩
    exact ⟨K ∪ L, hK.union hL, union_subset hKs hLs,
      (hf.mono subset_union_left).add (hg.mono subset_union_right)⟩
  smul_mem' := by
    rintro c f ⟨K, hK, hKs, hf⟩
    exact ⟨K, hK, hKs, hf.smul c⟩

/-- The constant field `c` on a compact set `K`, extended by zero. -/
def compactIndicator (K : Set X) (hK : IsCompact K) (c : E) : L2 :=
  indicatorConstLp 2 hK.measurableSet hK.measure_ne_top c

/-- A compact indicator is supported in its defining set. -/
theorem compactIndicator_supported (K : Set X) (hK : IsCompact K) (c : E) :
    Supported K (compactIndicator K hK c) := indicatorConstLp_coeFn_notMem

/-- A compact indicator agrees almost everywhere with its pointwise formula. -/
theorem compactIndicator_ae (K : Set X) (hK : IsCompact K) (c : E) :
    compactIndicator K hK c =ᵐ[volume] K.indicator (fun _ => c) :=
  indicatorConstLp_coeFn

/-- Approximate a finite-measure indicator by indicators of compact subsets. -/
theorem indicator_mem_closure_compactIndicators {s : Set X} (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (c : E) :
    indicatorConstLp 2 hs hμs c ∈ closure
      {f : L2 | ∃ K, ∃ hK : IsCompact K, K ⊆ s ∧ f = compactIndicator K hK c} := by
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨η, hη, hηδ⟩ := exists_eLpNorm_indicator_le
    (μ := (volume : Measure X)) (p := 2) (by norm_num) c hδ.ne'
  obtain ⟨K, hKs, hK, hsmall⟩ := hs.exists_isCompact_sdiff_lt hμs
    (show (η : ℝ≥0∞) ≠ 0 by exact_mod_cast hη.ne')
  refine ⟨compactIndicator K hK c, ⟨K, hK, hKs, rfl⟩, ?_⟩
  calc
    edist (indicatorConstLp 2 hs hμs c) (compactIndicator K hK c)
        = eLpNorm ((s \ K).indicator (fun _ => c)) 2 volume := by
          rw [compactIndicator, indicatorConstLp, indicatorConstLp, Lp.edist_toLp_toLp]
          rw [← Set.indicator_sdiff hKs]
    _ ≤ δ := hηδ _ hsmall.le (hs.diff hK.measurableSet).nullMeasurableSet
    _ < ε := hδε

/-- Cutting an indicator intersects its defining set with the cut set. -/
theorem cut_indicator {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμt : volume t ≠ ∞) (c : E) :
    cut s hs (indicatorConstLp 2 ht hμt c) =
      indicatorConstLp 2 (hs.inter ht) (measure_ne_top_of_subset inter_subset_right hμt) c := by
  apply Lp.ext
  filter_upwards [cut_ae s hs (indicatorConstLp 2 ht hμt c),
    indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hμt) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hs.inter ht)
      (hμs := measure_ne_top_of_subset inter_subset_right hμt) (c := c)] with x h₁ h₂ h₃
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp_all

/-- A closed complex subspace containing compact constant fields in `s`
contains every field essentially supported in `s`. The proof combines inner
regularity with `Lp.induction`. -/
theorem supported_mem_of_compactIndicators (s : Set X) (hs : MeasurableSet s)
    (P : Submodule ℂ L2) (hP : IsClosed (P : Set L2))
    (hcompact : ∀ K, ∀ hK : IsCompact K, K ⊆ s → ∀ c, compactIndicator K hK c ∈ P)
    {f : L2} (hf : Supported s f) : f ∈ P := by
  have hcut : ∀ g : L2, cut s hs g ∈ P := by
    refine Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (fun g : L2 => cut s hs g ∈ P) ?_ ?_ ?_
    · intro c t ht hμt
      rw [Lp.simpleFunc.coe_indicatorConst, cut_indicator]
      apply closure_minimal (t := (P : Set L2)) ?_ hP
        (indicator_mem_closure_compactIndicators (hs.inter ht)
          (measure_ne_top_of_subset inter_subset_right hμt.ne) c)
      rintro g ⟨K, hK, hKt, rfl⟩
      exact hcompact K hK (hKt.trans inter_subset_left) c
    · intro g h hg hh _ hgP hhP
      simpa [cut_add] using P.add_mem hgP hhP
    · exact hP.preimage (cutCLM s hs).continuous
  simpa [cut_eq_self hs hf] using hcut f

/-- Compactly supported fields are dense among fields supported in a measurable set. -/
theorem supported_mem_closure_compact {s : Set X} (hs : MeasurableSet s)
    {f : L2} (hf : Supported s f) : f ∈ closure (compactSubmodule s : Set L2) := by
  apply supported_mem_of_compactIndicators s hs (compactSubmodule s).topologicalClosure
    (compactSubmodule s).isClosed_topologicalClosure ?_ hf
  intro K hK hKs c
  exact (compactSubmodule s).le_topologicalClosure
    ⟨K, hK, hKs, compactIndicator_supported K hK c⟩

/-- A continuous function vanishing on compactly supported tuples vanishes on their closure. -/
theorem continuous_zero_of_compact {ι : Type*} (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (F : (ι → L2) → ℂ) (hF : Continuous F)
    (hzero : ∀ f, (∀ i, f i ∈ compactSubmodule (s i)) → F f = 0)
    (f : ι → L2) (hf : ∀ i, Supported (s i) (f i)) : F f = 0 := by
  have hmem : f ∈ closure (Set.pi univ fun i => (compactSubmodule (s i) : Set L2)) := by
    rw [closure_pi_set]
    intro i _
    exact supported_mem_closure_compact (hs i) (hf i)
  have hsub : Set.pi univ (fun i => (compactSubmodule (s i) : Set L2)) ⊆ {g | F g = 0} := by
    intro g hg
    exact hzero g (fun i => hg i (mem_univ i))
  exact closure_minimal hsub (isClosed_eq hF continuous_const) hmem

end NoContact
