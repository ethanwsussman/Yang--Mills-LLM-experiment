import YangMills.Construction.Continuum.TraceOfARingOfPropagators
import YangMills.Construction.LinearAlgebra.FreeCurvaturePropagatorIsSymmetricEvenAndContinuous
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Tuples FreeRingKernels PeriodicLattice Exterior TorusMetric TestFunctions
namespace PropagatorRings
variable {n : ℕ}
theorem bivectorTrace_prod_rotate_one (l : List (Module.End ℝ Bivector)) :
    bivectorTrace (l.rotate 1).prod = bivectorTrace l.prod := by
  cases l with
  | nil => simp
  | cons a t =>
    have hrot : ((a :: t).rotate 1).prod = t.prod * a := by
      simp [List.rotate_cons_succ]
    rw [hrot, List.prod_cons, bivectorTrace_eq_trace, bivectorTrace_eq_trace]
    exact LinearMap.trace_mul_comm ℝ t.prod a
theorem list_ofFn_comp_finRotate {M : Type*} (B : Fin n → M) :
    List.ofFn (fun i => B (finRotate n i)) = (List.ofFn B).rotate 1 := by
  cases n with
  | zero => simp
  | succ k =>
    apply List.ext_getElem (by simp)
    intro i hi₁ hi₂
    simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
    congr 1
    apply Fin.ext
    rw [finRotate_apply]
    simp [Fin.val_add]
theorem list_ofFn_comp_rev {M : Type*} (B : Fin n → M) :
    List.ofFn (fun i => B (Fin.rev i)) = (List.ofFn B).reverse := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hin : i < n := by simpa using hi₁
  simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev]
  omega
theorem inner_list_prod_eq_of_selfAdjoint (l : List (Module.End ℝ Bivector))
    (hl : ∀ a ∈ l, IsSelfAdjointMap a) (u v : Bivector) :
    inner ℝ u (l.prod v) = inner ℝ (l.reverse.prod u) v := by
  induction l generalizing u with
  | nil => simp
  | cons a t ih =>
    have ht := ih (fun b hb => hl b (List.mem_cons_of_mem a hb)) (a u)
    have ha := hl a List.mem_cons_self u (t.prod v)
    simp only [List.prod_cons, List.reverse_cons, List.prod_append, List.prod_nil, mul_one,
      Module.End.mul_apply]
    rw [ha, ht]
theorem bivectorTrace_prod_reverse (l : List (Module.End ℝ Bivector))
    (hl : ∀ a ∈ l, IsSelfAdjointMap a) :
    bivectorTrace l.reverse.prod = bivectorTrace l.prod := by
  unfold bivectorTrace bivectorMatrixEntry
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [inner_list_prod_eq_of_selfAdjoint l hl, real_inner_comm]
theorem finRotate_rev_finRotate_eq (i : Fin n) :
    finRotate n (Fin.rev (finRotate n i)) = Fin.rev i := by apply _root_.YangMills.SharedProofs.p38097 <;> assumption
def ringFactor (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ) (i : Fin n) :
    Module.End ℝ Bivector :=
  freeCurvaturePropagator (x (σ i) - x (σ (finRotate n i)))
theorem cyclicPropagatorProduct_eq_prod (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ) :
    cyclicPropagatorProduct σ x = (List.ofFn (ringFactor σ x)).prod := rfl
theorem cyclicTrace_rotateBy_one (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ) :
    cyclicTrace (rotateBy 1 σ) x = cyclicTrace σ x := by
  have hl : List.ofFn (ringFactor (rotateBy 1 σ) x) = (List.ofFn (ringFactor σ x)).rotate 1 := by
    rw [← list_ofFn_comp_finRotate]
    rfl
  unfold cyclicTrace
  rw [cyclicPropagatorProduct_eq_prod, cyclicPropagatorProduct_eq_prod, hl,
    bivectorTrace_prod_rotate_one]
theorem cyclicTrace_rotateBy (t : ℤ) (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ) :
    cyclicTrace (rotateBy t σ) x = cyclicTrace σ x := by
  induction t using Int.induction_on with
  | zero => rw [rotateBy_zero]
  | succ k ih =>
    have hk := cyclicTrace_rotateBy_one (rotateBy (k : ℤ) σ) x
    rw [rotateBy_rotateBy] at hk
    rw [hk, ih]
  | pred k ih =>
    have hk := cyclicTrace_rotateBy_one (rotateBy (-(k : ℤ) - 1) σ) x
    rw [rotateBy_rotateBy, sub_add_cancel] at hk
    rw [← hk, ih]
theorem cyclicTrace_reversed (hK : FreeCurvaturePropagatorSymmEvenContinuous)
    (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ)
    (hx : ∀ i, x (σ i) ≠ x (σ (finRotate n i))) :
    cyclicTrace (reversed σ) x = cyclicTrace σ x := by
  have hne : ∀ i, x (σ i) - x (σ (finRotate n i)) ≠ 0 := fun i => sub_ne_zero.2 (hx i)
  have hfac : ringFactor (reversed σ) x = fun i => ringFactor σ x (Fin.rev (finRotate n i)) := by
    funext i
    simp only [ringFactor, reversed, finRotate_rev_finRotate_eq]
    rw [← neg_sub, hK.2.1 _ (by
      have hr := hne (Fin.rev (finRotate n i))
      rwa [finRotate_rev_finRotate_eq] at hr)]
  have hl : List.ofFn (ringFactor (reversed σ) x) =
      (List.ofFn (ringFactor σ x)).reverse.rotate 1 := by
    rw [hfac, ← list_ofFn_comp_rev, ← list_ofFn_comp_finRotate]
  have hsym : ∀ a ∈ List.ofFn (ringFactor σ x), IsSelfAdjointMap a := by
    intro a ha
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact hK.1 _ (hne i)
  unfold cyclicTrace
  rw [cyclicPropagatorProduct_eq_prod, cyclicPropagatorProduct_eq_prod, hl,
    bivectorTrace_prod_rotate_one, bivectorTrace_prod_reverse _ hsym]
theorem cyclicTraceRingInvariant_of (hK : FreeCurvaturePropagatorSymmEvenContinuous)
    (σ : Fin n → Fin n) : CyclicTraceRingInvariant σ := by
  intro x hx
  have hrev := cyclicTrace_reversed hK σ x hx
  refine ⟨cyclicTrace_rotateBy_one σ x, hrev, ?_⟩
  intro τ hτ
  rw [ringClass_eq_union] at hτ
  rcases hτ with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact cyclicTrace_rotateBy t σ x
  · exact (cyclicTrace_rotateBy t _ x).trans hrev
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem eq_zero_of_euclidNormVec_eq_zero {v : Fin 4 → ℝ} (hv : euclidNormVec v = 0) : v = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.eq_zero_of_euclidNormVec_eq_zero <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem setDistR4_pos_of_disjoint {A B : Set (Fin 4 → ℝ)} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) : 0 < setDistR4 A B := by
  have hd : ∃ d : ℝ, 0 < d ∧ ∀ a ∈ A, ∀ b ∈ B, d ≤ euclidNormVec (a - b) := by
    by_cases hne : (A ×ˢ B).Nonempty
    · have hc : ContinuousOn (fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) => euclidNormVec (z.1 - z.2))
          (A ×ˢ B) :=
        (continuous_euclidNormVec.comp (continuous_fst.sub continuous_snd)).continuousOn
      obtain ⟨z, hz, hmin⟩ := (hA.prod hB).exists_isMinOn hne hc
      refine ⟨euclidNormVec (z.1 - z.2), ?_, fun a ha b hb => hmin (Set.mk_mem_prod ha hb)⟩
      refine lt_of_le_of_ne (euclidNormVec_nonneg _) fun h0 => ?_
      have hz12 : z.1 = z.2 := sub_eq_zero.1 (eq_zero_of_euclidNormVec_eq_zero h0.symm)
      exact Set.disjoint_left.1 hAB hz.1 (hz12 ▸ hz.2)
    · refine ⟨1, one_pos, fun a ha b hb => absurd ⟨(a, b), Set.mk_mem_prod ha hb⟩ hne⟩
  obtain ⟨d, hd, hle⟩ := hd
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hd) ?_
  unfold setDistR4
  exact le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (hle a ha b hb)
theorem continuous_cyclicTrace_restrict (hK : FreeCurvaturePropagatorSymmEvenContinuous)
    (σ : Fin n → Fin n) (S : Set (Fin n → Fin 4 → ℝ))
    (hS : ∀ x ∈ S, ∀ i, x (σ i) ≠ x (σ (finRotate n i))) :
    Continuous fun x : S => cyclicTrace σ x := by
  classical
  let toMat := LinearMap.toMatrixAlgEquiv (R := ℝ) axisBivectorBasis.toBasis
  have hentry : ∀ (T : Module.End ℝ Bivector) (P Q : AxisPlane),
      toMat T P Q = bivectorMatrixEntry T P Q := by
    intro T P Q
    simp [toMat, bivectorMatrixEntry, LinearMap.toMatrixAlgEquiv_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  have hfac : ∀ i, Continuous fun x : S => toMat (ringFactor σ x i) := by
    intro i
    refine continuous_matrix fun P Q => ?_
    simp only [hentry, ringFactor]
    have hv : Continuous fun x : S => (x : Fin n → Fin 4 → ℝ) (σ i) -
        (x : Fin n → Fin 4 → ℝ) (σ (finRotate n i)) :=
      ((continuous_apply _).comp continuous_subtype_val).sub
        ((continuous_apply _).comp continuous_subtype_val)
    exact (hK.2.2 P Q).comp_continuous hv fun x => sub_ne_zero.2 (hS x x.2 i)
  have hprod : Continuous fun x : S => toMat (cyclicPropagatorProduct σ x) := by
    have hl : ∀ x : S, toMat (cyclicPropagatorProduct σ x) =
        ((List.finRange n).map fun i => toMat (ringFactor σ x i)).prod := by
      intro x
      rw [cyclicPropagatorProduct_eq_prod, map_list_prod, List.ofFn_eq_map, List.map_map]
      rfl
    simp only [hl]
    exact continuous_list_prod _ fun i _ => hfac i
  have htr : ∀ x : S, cyclicTrace σ x = ∑ P, toMat (cyclicPropagatorProduct σ x) P P := by
    intro x
    simp only [cyclicTrace, bivectorTrace, hentry]
  simp only [htr]
  refine continuous_finsetSum _ fun P _ => ?_
  exact (continuous_apply P).comp ((continuous_apply P).comp hprod)
theorem cyclicIntegralAbsConv_of (hK : FreeCurvaturePropagatorSymmEvenContinuous) (hn : 2 ≤ n)
    (σ : Fin n → Fin n) (hσ : IsBijectiveTuple σ) (f : Fin n → (Fin 4 → ℝ) → ℝ)
    (hf : IsAdmissibleTestFamily f) : CyclicIntegralAbsConv σ f := by
  obtain ⟨hmeas, hbd, hcpt, hdisj⟩ := hf
  have hS : IsCompact (supportBox f) := isCompact_univ_pi fun j => hcpt j
  have hrot : ∀ i : Fin n, σ i ≠ σ (finRotate n i) := by
    intro i e
    have hi := hσ.1 e
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [finRotate_apply] at hi
    have h10 : (1 : Fin (k + 2)) = 0 :=
      add_left_cancel (a := i) (by rw [add_zero]; exact hi.symm)
    exact one_ne_zero h10
  have hnb : ∀ x ∈ supportBox f, ∀ i, x (σ i) ≠ x (σ (finRotate n i)) := by
    intro x hx i e
    have hx₁ := hx (σ i) (Set.mem_univ _)
    have hx₂ := hx (σ (finRotate n i)) (Set.mem_univ _)
    exact Set.disjoint_left.1 (hdisj (hrot i)) hx₁ (e ▸ hx₂)
  have hcont := continuous_cyclicTrace_restrict hK σ _ hnb
  have hcontOn : ContinuousOn (cyclicTrace σ) (supportBox f) :=
    continuousOn_iff_continuous_domRestrict.2 hcont
  obtain ⟨C₁, hC₁⟩ := hS.exists_bound_of_continuousOn hcontOn
  choose C hC using hbd
  have hbound : ∀ x ∈ supportBox f, |cyclicIntegrand σ f x| ≤ (∏ j, C j) * C₁ := by
    intro x hx
    have hC0 : ∀ j, 0 ≤ C j := fun j => (abs_nonneg _).trans (hC j 0)
    have hb₁ : |∏ j, f j (x j)| ≤ ∏ j, C j := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => hC j _
    have hb₂ : |cyclicTrace σ x| ≤ C₁ := by simpa using hC₁ x hx
    rw [cyclicIntegrand, abs_mul]
    exact mul_le_mul hb₁ hb₂ (abs_nonneg _) (Finset.prod_nonneg fun j _ => hC0 j)
  have hsub : Measurable fun x : supportBox f => cyclicIntegrand σ f x := by
    refine Measurable.mul ?_ hcont.measurable
    refine Finset.measurable_prod _ fun j _ => ?_
    exact (hmeas j).comp ((measurable_pi_apply j).comp measurable_subtype_coe)
  have hSm : MeasurableSet (supportBox f) := hS.isClosed.measurableSet
  refine ⟨fun i j hij => setDistR4_pos_of_disjoint (hcpt i) (hcpt j) (hdisj hij), hS,
    ⟨_, hbound⟩, hsub, ?_⟩
  have hind : Measurable ((supportBox f).indicator (cyclicIntegrand σ f)) := by
    refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
    · have hr : (supportBox f).domRestrict ((supportBox f).indicator (cyclicIntegrand σ f)) =
          fun x : supportBox f => cyclicIntegrand σ f x := by
        funext x
        simp [Set.domRestrict, x.2]
      rw [hr]
      exact hsub
    · have hr : (supportBox f)ᶜ.domRestrict
          ((supportBox f).indicator (cyclicIntegrand σ f)) = fun _ => 0 := by
        funext x
        simpa [Set.domRestrict] using Set.indicator_of_notMem x.2 _
      rw [hr]
      exact measurable_const
  have hon : IntegrableOn ((supportBox f).indicator (cyclicIntegrand σ f))
      (supportBox f) volume := by
    refine Measure.integrableOn_of_bounded (M := (∏ j, C j) * C₁) hS.measure_lt_top.ne
      hind.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.indicator_of_mem hx]
    exact hbound x hx
  have hint := (integrable_indicator_iff hSm).2 hon
  rwa [Set.indicator_indicator, Set.inter_self] at hint
theorem cyclicTraceProperties_holds (hK : FreeCurvaturePropagatorSymmEvenContinuous) :
    CyclicTraceProperties :=
  fun _ hn σ hσ => ⟨cyclicTraceRingInvariant_of hK σ,
    fun f hf => cyclicIntegralAbsConv_of hK hn σ hσ f hf⟩
end PropagatorRings
end YangMills.Construction
end
