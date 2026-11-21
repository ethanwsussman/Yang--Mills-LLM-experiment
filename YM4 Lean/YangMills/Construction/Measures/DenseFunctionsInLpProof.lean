import YangMills.Construction.Measures.DenseFunctionsInLp
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.Measures.DenseInLp
variable {Y : Type} [MeasurableSpace Y] {m : Measure Y} [IsFiniteMeasure m]
theorem tendsto_toLp_of_uniformBound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {u : ℕ → Y → ℂ}
    {g : Y → ℂ} (hu : ∀ n, MemLp (u n) p m) (hg : MemLp g p m) {C : ℝ≥0}
    (hC : ∀ n y, ‖u n y‖ ≤ C) (hlim : ∀ y, Tendsto (fun n => u n y) atTop (𝓝 (g y))) :
    Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hg.toLp g)) := by
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu g hg).2 ?_
  refine tendsto_Lp_finite_of_tendsto_ae Fact.out hp (fun n => (hu n).1) hg ?_ (ae_of_all _ hlim)
  refine unifIntegrable_of Fact.out hp (fun n => (hu n).1) fun ε hε => ⟨C + 1, fun n => ?_⟩
  have hvoid : {x | C + 1 ≤ ‖u n x‖₊} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    have hle : ‖u n x‖₊ ≤ C := by exact_mod_cast hC n x
    exact lt_of_le_of_lt hle (lt_add_one C)
  rw [hvoid]
  simp
def lpClasses (p : ℝ≥0∞) (m : Measure Y) [Fact (1 ≤ p)] (A : Submodule ℂ (Y → ℂ)) :
    Submodule ℂ (Lp ℂ p m) where
  carrier := {g | ∃ f ∈ A, ∃ hf : MemLp f p m, hf.toLp f = g}
  add_mem' := by
    rintro _ _ ⟨f, hf, hf', rfl⟩ ⟨g, hg, hg', rfl⟩
    exact ⟨f + g, A.add_mem hf hg, hf'.add hg', MemLp.toLp_add _ _⟩
  zero_mem' := ⟨0, A.zero_mem, MemLp.zero, MemLp.toLp_zero _⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, hf', rfl⟩
    exact ⟨c • f, A.smul_mem c hf, hf'.const_smul c, MemLp.toLp_const_smul _ _⟩
theorem approximatesLp_of_generating (A : Submodule ℂ (Y → ℂ)) (Q₀ : Set (Set Y))
    (hA : ∀ f ∈ A, Measurable f ∧ ∃ c : ℝ, ∀ y, ‖f y‖ ≤ c)
    (hinter : ∀ Q ∈ Q₀, ∀ Q' ∈ Q₀, Q ∩ Q' ∈ Q₀) (huniv : Set.univ ∈ Q₀)
    (hgen : ‹MeasurableSpace Y› = MeasurableSpace.generateFrom Q₀)
    (happ : ∀ Q ∈ Q₀, ∃ f : ℕ → Y → ℂ, (∀ k, 1 ≤ k → f k ∈ A ∧ ∀ y, ‖f k y‖ ≤ 1) ∧
      ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (Q.indicator 1 y))) :
    ApproximatesLp m (A : Set (Y → ℂ)) := by
  intro p hp J ε hε
  have hp1 : 1 ≤ p := by
    rcases hp with rfl | rfl
    · exact le_rfl
    · norm_num
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have hptop : p ≠ ∞ := by
    rcases hp with rfl | rfl <;> simp
  have memLp_of_mem : ∀ f ∈ A, MemLp f p m := fun f hf => by
    obtain ⟨hfm, c, hc⟩ := hA f hf
    exact MemLp.of_bound hfm.aestronglyMeasurable c (ae_of_all _ hc)
  let cl : Submodule ℂ (Lp ℂ p m) := (lpClasses p m A).topologicalClosure
  have hclosed : IsClosed (cl : Set (Lp ℂ p m)) := Submodule.isClosed_topologicalClosure _
  have hcongr : ∀ (S T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T), S = T →
      indicatorConstLp p hS (measure_ne_top m S) (1 : ℂ) ∈ cl →
      indicatorConstLp p hT (measure_ne_top m T) (1 : ℂ) ∈ cl := by
    rintro S _ hS hT rfl h
    exact h
  have hempty : indicatorConstLp p (MeasurableSet.empty) (measure_ne_top m ∅) (1 : ℂ) ∈ cl := by
    rw [indicatorConstLp_empty]
    exact cl.zero_mem
  have hbasic : ∀ Q ∈ Q₀, ∀ hQ : MeasurableSet Q,
      indicatorConstLp p hQ (measure_ne_top m Q) (1 : ℂ) ∈ cl := by
    intro Q hQ hQm
    obtain ⟨f, hf, hlim⟩ := happ Q hQ
    have hmem : ∀ n, MemLp (f (n + 1)) p m := fun n =>
      memLp_of_mem _ (hf (n + 1) (Nat.le_add_left 1 n)).1
    have ht := tendsto_toLp_of_uniformBound (C := 1) hptop hmem
      (memLp_indicator_const p hQm (1 : ℂ) (Or.inr (measure_ne_top m Q)))
      (fun n y => by simpa using (hf (n + 1) (Nat.le_add_left 1 n)).2 y)
      (fun y => (hlim y).comp (tendsto_add_atTop_nat 1))
    exact hclosed.mem_of_tendsto ht (Eventually.of_forall fun n =>
      Submodule.le_topologicalClosure _
        ⟨f (n + 1), (hf (n + 1) (Nat.le_add_left 1 n)).1, hmem n, rfl⟩)
  have hind : ∀ (D : Set Y) (hD : MeasurableSet D),
      indicatorConstLp p hD (measure_ne_top m D) (1 : ℂ) ∈ cl := by
    refine MeasurableSpace.induction_on_inter
      (C := fun D hD => indicatorConstLp p hD (measure_ne_top m D) (1 : ℂ) ∈ cl)
      hgen (fun S hS T hT _ => hinter S hS T hT) hempty
      (fun t ht => hbasic t ht _) ?_ ?_
    · intro t htm ih
      have h := hcongr univ (t ∪ tᶜ) MeasurableSet.univ (htm.union htm.compl)
        (union_compl_self t).symm (hbasic univ huniv _)
      rw [indicatorConstLp_disjoint_union htm htm.compl (measure_ne_top m _) (measure_ne_top m _)
        disjoint_compl_right (1 : ℂ)] at h
      have h2 := cl.sub_mem h ih
      rwa [add_sub_cancel_left] at h2
    · intro f hdis hfm ih
      have hbi : ∀ n, MeasurableSet (⋃ i ∈ Finset.range n, f i) := fun n =>
        Finset.measurableSet_biUnion _ fun i _ => hfm i
      have hfin : ∀ n, indicatorConstLp p (hbi n) (measure_ne_top m _) (1 : ℂ) ∈ cl := by
        intro n
        induction n with
        | zero => exact hcongr ∅ _ MeasurableSet.empty (hbi 0) (by simp) hempty
        | succ n ih2 =>
          have hdisj : Disjoint (⋃ i ∈ Finset.range n, f i) (f n) := by
            rw [Set.disjoint_iUnion₂_left]
            intro i hi
            exact hdis (Nat.ne_of_lt (Finset.mem_range.1 hi))
          have h := cl.add_mem ih2 (ih n)
          rw [← indicatorConstLp_disjoint_union (hbi n) (hfm n) (measure_ne_top m _)
            (measure_ne_top m _) hdisj (1 : ℂ)] at h
          exact hcongr _ _ _ _
            (by rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]) h
      have hU : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hfm
      have hmem : ∀ n, MemLp ((⋃ i ∈ Finset.range n, f i).indicator fun _ => (1 : ℂ)) p m :=
        fun n => memLp_indicator_const p (hbi n) (1 : ℂ) (Or.inr (measure_ne_top m _))
      have ht := tendsto_toLp_of_uniformBound (C := 1) hptop hmem
        (memLp_indicator_const p hU (1 : ℂ) (Or.inr (measure_ne_top m _)))
        (fun n y => (norm_indicator_le_norm_self _ _).trans (by simp))
        (fun y => by
          by_cases hy : y ∈ ⋃ i, f i
          · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
            rw [indicator_of_mem hy]
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [eventually_gt_atTop i] with n hn
            rw [indicator_of_mem]
            exact mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hn, hi⟩
          · rw [indicator_of_notMem hy]
            refine tendsto_const_nhds.congr fun n => ?_
            rw [indicator_of_notMem]
            intro h
            obtain ⟨i, _, hi⟩ := mem_iUnion₂.1 h
            exact hy (mem_iUnion.2 ⟨i, hi⟩))
      exact hclosed.mem_of_tendsto ht (Eventually.of_forall hfin)
  have hdense : ∀ g : Lp ℂ p m, g ∈ cl := by
    refine Lp.induction hptop (fun g => g ∈ cl) ?_ ?_ hclosed
    · intro c D hD hμ
      rw [Lp.simpleFunc.coe_indicatorConst]
      have hsm : indicatorConstLp p hD hμ.ne c = c • indicatorConstLp p hD hμ.ne (1 : ℂ) := by
        rw [indicatorConstLp, indicatorConstLp, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (ae_of_all _ fun y => by by_cases h : y ∈ D <;> simp [h])
      rw [hsm]
      exact cl.smul_mem c (hind D hD)
    · intro f g hf hg _ h1 h2
      exact cl.add_mem h1 h2
  have hJ : J ∈ closure ((lpClasses p m A : Submodule ℂ (Lp ℂ p m)) : Set (Lp ℂ p m)) := hdense J
  obtain ⟨g, ⟨f, hf, hf', rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hJ ε hε
  exact ⟨f, hf, hf', by rw [← dist_eq_norm]; exact hd.le⟩
def continuousSubmodule (Y : Type) [TopologicalSpace Y] : Submodule ℂ (Y → ℂ) where
  carrier := {f | Continuous f}
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := continuous_const
  smul_mem' := fun c _ hf => hf.const_smul c
theorem approximatesLp_continuous [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [BorelSpace Y] :
    ApproximatesLp m {f : Y → ℂ | Continuous f} := by
  refine approximatesLp_of_generating (continuousSubmodule Y) {F | IsClosed F}
    (fun f hf => ⟨Continuous.measurable hf, ?_⟩) (fun Q hQ Q' hQ' => IsClosed.inter hQ hQ')
    isClosed_univ ?_ ?_
  · obtain ⟨c, hc⟩ := isCompact_univ.exists_bound_of_continuousOn (Continuous.continuousOn hf)
    exact ⟨c, fun y => hc y (mem_univ y)⟩
  · rw [← borel_eq_generateFrom_isClosed]
    exact BorelSpace.measurable_eq
  · intro F hF
    have hφ : Continuous fun x : ℝ≥0 => ((x : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp NNReal.continuous_coe
    refine ⟨fun k y => (((IsClosed.apprSeq hF k y : ℝ≥0) : ℝ) : ℂ), fun k _ => ⟨?_, fun y => ?_⟩,
      fun y => ?_⟩
    · exact hφ.comp (IsClosed.apprSeq hF k).continuous
    · rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF k y
    · have ht := tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hF) y
      have hv : (((F.indicator (fun _ => (1 : ℝ≥0)) y : ℝ≥0) : ℝ) : ℂ) = F.indicator 1 y := by
        by_cases h : y ∈ F <;> simp [h]
      rw [← hv]
      exact (hφ.tendsto _).comp ht
theorem boundedConvergence_dense_holds : boundedConvergence_dense := by
  intro Y _ _ _ _ _ m hm
  have := hm
  exact ⟨fun A Q₀ hA _ hinter huniv hgen happ =>
    approximatesLp_of_generating A Q₀ hA hinter huniv
      ((BorelSpace.measurable_eq).trans hgen.symm) happ, approximatesLp_continuous⟩
end YangMills.Construction.Measures.DenseInLp
