import YangMills.Construction.ClusterExpansionOfAStep.StatesOfGivenShapes
import YangMills.Construction.ClusterExpansionOfAStep.BasesOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.CaseFunctionIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.CasesOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.InnerIntegralOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.ProductOverAPartition
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps StepGas StepSettings StepCosts RenormalizationStepParameters SpinFamilies FamilyZones TopLevelSites ProductMeasure
namespace FamilyCaseSum
section Products
variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
theorem lintegral_pi_prod_apply_eq_prod (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, X i → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) : ∫⁻ x, ∏ i, g i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, g i y ∂μ i := by
  classical
  by_cases hne : Nonempty (∀ i, X i)
  · obtain ⟨x₀⟩ := hne
    have hm : Measurable fun x : ∀ i, X i => ∏ i, g i (x i) :=
      Finset.measurable_prod _ fun i _ => (hg i).comp (measurable_pi_apply i)
    have key : ∀ (s : Finset I) (x : ∀ i, X i),
        (∫⋯∫⁻_s, (fun x : ∀ i, X i => ∏ i, g i (x i)) ∂μ) x =
          (∏ i ∈ s, ∫⁻ y, g i y ∂μ i) * ∏ i ∈ Finset.univ \ s, g i (x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro x
        simp [lmarginal_empty]
      | insert i s hi ih =>
        intro x
        rw [lmarginal_insert _ hm hi]
        simp only [ih]
        have e : ∀ xi : X i, ∏ j ∈ Finset.univ \ s, g j (Function.update x i xi j) =
            g i xi * ∏ j ∈ Finset.univ \ insert i s, g j (x j) := by
          intro xi
          have hmem : i ∈ Finset.univ \ s := by simp [hi]
          rw [← Finset.mul_prod_erase _ _ hmem]
          simp only [Function.update_self]
          congr 1
          have : (Finset.univ \ s).erase i = Finset.univ \ insert i s := by
            ext j
            simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
          rw [this]
          refine Finset.prod_congr rfl fun j hj => ?_
          have : j ≠ i := by
            intro e
            subst e
            simp at hj
          rw [Function.update_of_ne this]
        simp only [e]
        rw [Finset.prod_insert hi, lintegral_const_mul _ ((hg i).mul_const _), lintegral_mul_const _ (hg i)]
        ring
    rw [lintegral_eq_lmarginal_univ x₀, key]
    simp
  · obtain ⟨i, hi⟩ : ∃ i, IsEmpty (X i) := by
      by_contra h
      push Not at h
      exact hne (Classical.nonempty_pi.mpr h)
    have : IsEmpty (∀ i, X i) := not_nonempty_iff.mp hne
    rw [Measure.eq_zero_of_isEmpty (Measure.pi μ), lintegral_zero_measure]
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Measure.eq_zero_of_isEmpty (μ i), lintegral_zero_measure]
theorem pi_withDensity_eq (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, X i → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) [∀ i, SigmaFinite ((μ i).withDensity (g i))] :
    Measure.pi (fun i => (μ i).withDensity (g i)) =
      (Measure.pi μ).withDensity fun x => ∏ i, g i (x i) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have e : (Set.univ.pi s).indicator (fun x : ∀ i, X i => ∏ i, g i (x i)) =
      fun x => ∏ i, (s i).indicator (g i) (x i) := by
    funext x
    by_cases h : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem h]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (h i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem h]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at h
      obtain ⟨i, hi⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [e, lintegral_pi_prod_apply_eq_prod μ _ fun i => (hg i).indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]
theorem lintegral_pi_prodMeasure (μ : ∀ i, Measure (X i)) (ν : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] (f : (∀ i, X i × Y i) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ c, f c ∂Measure.pi (fun i => (μ i).prod (ν i)) =
      ∫⁻ x, ∫⁻ y, f (fun i => (x i, y i)) ∂Measure.pi ν ∂Measure.pi μ := by
  classical
  set t : (∀ i, X i) × (∀ i, Y i) → ∀ i, X i × Y i := fun p i => (p.1 i, p.2 i) with ht
  have hm : Measurable t := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
  have hmap : Measure.pi (fun i => (μ i).prod (ν i)) = ((Measure.pi μ).prod (Measure.pi ν)).map t := by
    refine Measure.pi_eq_generateFrom (fun i => generateFrom_prod) (fun i => isPiSystem_prod)
      (fun i => (μ i).toFiniteSpanningSetsIn.prod (ν i).toFiniteSpanningSetsIn) ?_
    intro s hs
    choose A hA B hB e using hs
    have hbox : MeasurableSet (Set.univ.pi s) := by
      refine MeasurableSet.univ_pi fun i => ?_
      rw [← e i]
      exact (hA i).prod (hB i)
    rw [Measure.map_apply hm hbox]
    have hpre : t ⁻¹' Set.univ.pi s = (Set.univ.pi A) ×ˢ (Set.univ.pi B) := by
      ext ⟨x, y⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, ht, ← e,
        forall_and]
    rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← e i, Measure.prod_prod]
  rw [hmap, lintegral_map hf hm]
  exact lintegral_prod _ (hf.comp hm).aemeasurable
theorem lintegral_pi_count_eq_sum [Fintype (∀ i, X i)] [∀ i, Countable (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (f : (∀ i, X i) → ℝ≥0∞) :
    ∫⁻ o, f o ∂Measure.pi (fun i => (Measure.count : Measure (X i))) = ∑ o, f o := by
  classical
  rw [lintegral_fintype]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Measure.pi_singleton]
  simp
theorem lintegral_pi_prod_prod_count {Z : I → Type} [∀ i, MeasurableSpace (Z i)] [Fintype (∀ i, Z i)] [∀ i, Countable (Z i)]
    [∀ i, MeasurableSingletonClass (Z i)] (μ : ∀ i, Measure (X i)) (ν : ∀ i, Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] (E : (∀ i, X i × Y i × Z i) → ℝ≥0∞) (hE : Measurable E) :
    ∫⁻ c, E c ∂Measure.pi (fun i => (μ i).prod ((ν i).prod (Measure.count : Measure (Z i)))) =
      ∑ o : ∀ i, Z i, ∫⁻ a : ∀ i, X i, ∫⁻ l : ∀ i, Y i, E (fun i => (a i, l i, o i)) ∂Measure.pi ν ∂Measure.pi μ := by
  rw [lintegral_pi_prodMeasure _ _ E hE]
  have step : ∀ a : ∀ i, X i,
      ∫⁻ y, E (fun i => (a i, y i)) ∂Measure.pi (fun i => (ν i).prod (Measure.count : Measure (Z i))) =
        ∑ o : ∀ i, Z i, ∫⁻ l : ∀ i, Y i, E (fun i => (a i, l i, o i)) ∂Measure.pi ν := by
    intro a
    have hm : Measurable fun y : ∀ i, Y i × Z i => E fun i => (a i, y i) :=
      hE.comp (measurable_pi_lambda _ fun i => measurable_const.prodMk (measurable_pi_apply i))
    rw [lintegral_pi_prodMeasure _ _ _ hm]
    simp only [lintegral_pi_count_eq_sum]
    rw [lintegral_finsetSum]
    intro o _
    exact hE.comp (measurable_pi_lambda _ fun i => measurable_const.prodMk
      ((measurable_pi_apply i).prodMk measurable_const))
  simp only [step]
  rw [lintegral_finsetSum]
  intro o _
  refine Measurable.lintegral_prod_right' (f := fun p : (∀ i, X i) × (∀ i, Y i) =>
    E fun i => (p.1 i, p.2 i, o i)) (hE.comp (measurable_pi_lambda _ fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_const)))
end Products
section Parts
variable {B I : Type} [Fintype B] [Fintype I] {T : I → Type} [∀ i, Fintype (T i)] {X : Type} [MeasurableSpace X]
def IsDisjointEmbedding (ι : ∀ i, T i → B) : Prop := Function.Injective fun p : Σ i, T i => ι p.1 p.2
open Classical in
def disjointEmbeddingEquiv (ι : ∀ i, T i → B) (h : IsDisjointEmbedding ι) :
    (Σ i, T i) ⊕ {β : B // ¬ ∃ p : Σ i, T i, ι p.1 p.2 = β} ≃ B :=
  Equiv.ofBijective (Sum.elim (fun p => ι p.1 p.2) Subtype.val) (by
    constructor
    · rintro (p | q) (p' | q') e
      · exact congrArg Sum.inl (h e)
      · exact absurd ⟨p, e⟩ q'.2
      · exact absurd ⟨p', e.symm⟩ q.2
      · exact congrArg Sum.inr (Subtype.ext e)
    · intro β
      by_cases hb : ∃ p : Σ i, T i, ι p.1 p.2 = β
      · obtain ⟨p, rfl⟩ := hb
        exact ⟨Sum.inl p, rfl⟩
      · exact ⟨Sum.inr ⟨β, hb⟩, rfl⟩)
open Classical in
def insertValues (ι : ∀ i, T i → B) (a : ∀ i, T i → X) (w : B → X) : B → X := fun β =>
  if h : ∃ p : Σ i, T i, ι p.1 p.2 = β then a h.choose.1 h.choose.2 else w β
theorem insertValues_apply_embed {ι : ∀ i, T i → B} (h : IsDisjointEmbedding ι) (a : ∀ i, T i → X) (w : B → X) (i : I) (t : T i) :
    insertValues ι a w (ι i t) = a i t := by
  classical
  have hx : ∃ p : Σ i, T i, ι p.1 p.2 = ι i t := ⟨⟨i, t⟩, rfl⟩
  unfold insertValues
  rw [dif_pos hx]
  have : hx.choose = ⟨i, t⟩ := h hx.choose_spec
  rw [this]
theorem insertValues_apply_of_not_mem {ι : ∀ i, T i → B} (a : ∀ i, T i → X) (w : B → X) {β : B}
    (h : ¬ ∃ p : Σ i, T i, ι p.1 p.2 = β) : insertValues ι a w β = w β := by
  classical
  unfold insertValues
  rw [dif_neg h]
theorem glueParts_eq_insertValues {ι : ∀ i, T i → B} (h : IsDisjointEmbedding ι)
    (a : ∀ i, T i → X) (w : B → X) :
    glueParts (disjointEmbeddingEquiv ι h) a (fun q => w q.1) = insertValues ι a w := by
  classical
  funext β
  by_cases hb : ∃ p : Σ i, T i, ι p.1 p.2 = β
  · obtain ⟨⟨i, t⟩, rfl⟩ := hb
    rw [insertValues_apply_embed h]
    have : (disjointEmbeddingEquiv ι h).symm (ι i t) = Sum.inl ⟨i, t⟩ :=
      (Equiv.symm_apply_eq _).mpr rfl
    unfold glueParts
    rw [this]
  · rw [insertValues_apply_of_not_mem a w hb]
    have : (disjointEmbeddingEquiv ι h).symm β = Sum.inr ⟨β, hb⟩ := (Equiv.symm_apply_eq _).mpr rfl
    unfold glueParts
    rw [this]
theorem measurable_glueParts {Q : Type} (e : (Σ i, T i) ⊕ Q ≃ B) :
    Measurable fun p : (∀ i, T i → X) × (Q → X) => glueParts e p.1 p.2 := by
  refine measurable_pi_lambda _ fun b => ?_
  unfold glueParts
  rcases hb : e.symm b with p | u
  · simp only
    exact (measurable_pi_apply p.2).comp ((measurable_pi_apply p.1).comp measurable_fst)
  · simp only
    exact (measurable_pi_apply u).comp measurable_snd
theorem measurable_insertValues {ι : ∀ i, T i → B} :
    Measurable fun p : (∀ i, T i → X) × (B → X) => insertValues ι p.1 p.2 := by
  classical
  refine measurable_pi_lambda _ fun β => ?_
  unfold insertValues
  by_cases h : ∃ p : Σ i, T i, ι p.1 p.2 = β
  · simp only [dif_pos h]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst)
  · simp only [dif_neg h]
    exact (measurable_pi_apply _).comp measurable_snd
open Classical in
theorem lintegral_pi_eq_lintegral_insertValues (hp : LintegralPiPartitionStatement) {ι : ∀ i, T i → B} (h : IsDisjointEmbedding ι) (μ : Measure X)
    [IsProbabilityMeasure μ] (f : (B → X) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ w, f w ∂Measure.pi (fun _ : B => μ) =
      ∫⁻ a, ∫⁻ w, f (insertValues ι a w) ∂Measure.pi (fun _ : B => μ)
        ∂Measure.pi (fun i : I => Measure.pi fun _ : T i => μ) := by
  rw [hp B I _ X T μ (disjointEmbeddingEquiv ι h) f hf]
  refine lintegral_congr fun a => ?_
  have hm : Measurable fun r : {β : B // ¬ ∃ p : Σ i, T i, ι p.1 p.2 = β} → X => glueParts (disjointEmbeddingEquiv ι h) a r :=
    (measurable_glueParts (disjointEmbeddingEquiv ι h)).comp (measurable_const.prodMk measurable_id)
  have hres : Measurable fun w : B → X => fun q : {β : B // ¬ ∃ p : Σ i, T i, ι p.1 p.2 = β} => w q.1 :=
    measurable_pi_lambda _ fun q => measurable_pi_apply _
  have e1 : ∀ w, f (insertValues ι a w) = f (glueParts (disjointEmbeddingEquiv ι h) a fun q => w q.1) := fun w => by
    rw [glueParts_eq_insertValues h]
  simp only [e1]
  rw [hp B I _ X T μ (disjointEmbeddingEquiv ι h) (fun w => f (glueParts (disjointEmbeddingEquiv ι h) a fun q => w q.1))
    ((hf.comp hm).comp hres)]
  have e2 : ∀ (c : ∀ i, T i → X) (r : {β : B // ¬ ∃ p : Σ i, T i, ι p.1 p.2 = β} → X),
      (fun q : {β : B // ¬ ∃ p : Σ i, T i, ι p.1 p.2 = β} => glueParts (disjointEmbeddingEquiv ι h) c r q.1) = r := by
    intro c r
    funext q
    have : (disjointEmbeddingEquiv ι h).symm q.1 = Sum.inr q := (Equiv.symm_apply_eq _).mpr rfl
    unfold glueParts
    rw [this]
  simp only [e2]
  rw [lintegral_const, measure_univ, mul_one]
def coverGlue (ι : ∀ i, T i → B) (hc : ∀ β, ∃ p : Σ i, T i, ι p.1 p.2 = β) (l : ∀ i, T i → X) : B → X :=
  fun β => l (hc β).choose.1 (hc β).choose.2
theorem coverGlue_apply_embed {ι : ∀ i, T i → B} (h : IsDisjointEmbedding ι) (hc : ∀ β, ∃ p : Σ i, T i, ι p.1 p.2 = β)
    (l : ∀ i, T i → X) (i : I) (t : T i) : coverGlue ι hc l (ι i t) = l i t := by
  unfold coverGlue
  have : (hc (ι i t)).choose = ⟨i, t⟩ := h (hc (ι i t)).choose_spec
  rw [this]
theorem measurable_coverGlue (ι : ∀ i, T i → B) (hc : ∀ β, ∃ p : Σ i, T i, ι p.1 p.2 = β) :
    Measurable (coverGlue (X := X) ι hc) :=
  measurable_pi_lambda _ fun β => (measurable_pi_apply _).comp (measurable_pi_apply _)
open Classical in
theorem lintegral_pi_eq_lintegral_coverGlue (hp : LintegralPiPartitionStatement) {ι : ∀ i, T i → B} (h : IsDisjointEmbedding ι)
    (hc : ∀ β, ∃ p : Σ i, T i, ι p.1 p.2 = β) (μ : Measure X) [SigmaFinite μ] (f : (B → X) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ w, f w ∂Measure.pi (fun _ : B => μ) =
      ∫⁻ l, f (coverGlue ι hc l) ∂Measure.pi (fun i : I => Measure.pi fun _ : T i => μ) := by
  rw [hp B I _ X T μ (disjointEmbeddingEquiv ι h) f hf]
  refine lintegral_congr fun l => ?_
  have hQ : IsEmpty {β : B // ¬ ∃ p : Σ i, T i, ι p.1 p.2 = β} := ⟨fun q => q.2 (hc q.1)⟩
  have e : ∀ r, glueParts (disjointEmbeddingEquiv ι h) l r = coverGlue ι hc l := by
    intro r
    funext β
    obtain ⟨⟨i, t⟩, rfl⟩ := hc β
    rw [coverGlue_apply_embed h]
    have : (disjointEmbeddingEquiv ι h).symm (ι i t) = Sum.inl ⟨i, t⟩ := (Equiv.symm_apply_eq _).mpr rfl
    unfold glueParts
    rw [this]
  simp only [e]
  rw [lintegral_const, Measure.pi_of_empty]
  simp
end Parts
section States
variable {I : Type} [Fintype I] {X : I → Type} [∀ i, MeasurableSpace (X i)]
open Classical in
theorem lintegral_pi_withDensity_subtype (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (P : ∀ i, X i → Prop)
    (hP : ∀ i, MeasurableSet {x | P i x}) (fac : ∀ i, X i → ℝ≥0∞) (hfac : ∀ i, Measurable (fac i))
    [∀ i, SigmaFinite ((m i).comap (Subtype.val : {x // P i x} → X i))]
    [∀ i, SigmaFinite (((m i).comap (Subtype.val : {x // P i x} → X i)).withDensity fun s => fac i s.1)]
    (h : (∀ i, {x // P i x}) → ℝ≥0∞) (hh : Measurable h) (E : (∀ i, X i) → ℝ≥0∞)
    (hE : ∀ c, E c = if hc : ∀ i, P i (c i) then (∏ i, fac i (c i)) * h (fun i => ⟨c i, hc i⟩) else 0) :
    Measurable E ∧
      ∫⁻ τ, h τ ∂Measure.pi (fun i => ((m i).comap (Subtype.val : {x // P i x} → X i)).withDensity fun s => fac i s.1) =
        ∫⁻ c, E c ∂Measure.pi m := by
  set box : Set (∀ i, X i) := Set.univ.pi fun i => {x | P i x} with hbox
  have hb : MeasurableSet box := MeasurableSet.univ_pi hP
  have mem : ∀ c, c ∈ box ↔ ∀ i, P i (c i) := fun c => by simp [hbox, Set.mem_pi]
  set lift : box → ∀ i, {x // P i x} := fun c i => ⟨c.1 i, (mem c.1).mp c.2 i⟩ with hlift
  have hl : Measurable lift := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_subtype_coe).subtype_mk
  have hprod : Measurable fun c : ∀ i, X i => ∏ i, fac i (c i) :=
    Finset.measurable_prod _ fun i _ => (hfac i).comp (measurable_pi_apply i)
  have hEm : Measurable E := by
    have e : E = fun c => if hc : c ∈ box then (∏ i, fac i (c i)) * h (lift ⟨c, hc⟩) else 0 := by
      funext c
      rw [hE]
      by_cases hc : ∀ i, P i (c i)
      · rw [dif_pos hc, dif_pos ((mem c).mpr hc)]
      · rw [dif_neg hc, dif_neg fun x => hc ((mem c).mp x)]
    rw [e]
    exact Measurable.dite (f := fun c : box => (∏ i, fac i (c.1 i)) * h (lift c))
      (g := fun _ => 0) ((hprod.comp measurable_subtype_coe).mul (hh.comp hl)) measurable_const hb
  refine ⟨hEm, ?_⟩
  have hv : Measurable fun τ : ∀ i, {x // P i x} => fun i => (τ i).1 :=
    measurable_pi_lambda _ fun i => measurable_subtype_coe.comp (measurable_pi_apply i)
  rw [pi_withDensity_eq _ (fun i (s : {x // P i x}) => fac i s.1)
    fun i => (hfac i).comp measurable_subtype_coe]
  have hw : Measurable fun x : ∀ i, {x // P i x} => ∏ i, fac i (x i).1 :=
    Finset.measurable_prod _ fun i _ => ((hfac i).comp measurable_subtype_coe).comp (measurable_pi_apply i)
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hh]
  have hmap : (Measure.pi fun i => (m i).comap (Subtype.val : {x // P i x} → X i)).map
      (fun τ i => (τ i).1) = (Measure.pi m).restrict box := by
    have hres : ∀ i, ((m i).comap (Subtype.val : {x // P i x} → X i)).map Subtype.val = (m i).restrict {x | P i x} :=
      fun i => map_comap_subtype_coe (hP i) (m i)
    have hsf : ∀ i, SigmaFinite (((m i).comap (Subtype.val : {x // P i x} → X i)).map Subtype.val) := fun i => by
      rw [hres i]
      infer_instance
    rw [Measure.pi_map_pi (fun i => measurable_subtype_coe.aemeasurable), hbox, Measure.restrict_pi_pi]
    congr 1
    funext i
    exact hres i
  have e2 : ∀ τ : ∀ i, {x // P i x}, ((∏ i, fac i (τ i).1) * h τ) = E fun i => (τ i).1 := by
    intro τ
    rw [hE, dif_pos fun i => (τ i).2]
  simp only [Pi.mul_apply, e2]
  rw [← lintegral_map hEm hv, hmap, ← lintegral_indicator hb]
  refine lintegral_congr fun c => ?_
  by_cases hc : c ∈ box
  · rw [Set.indicator_of_mem hc]
  · rw [Set.indicator_of_notMem hc, hE, dif_neg fun x => hc ((mem c).mpr x)]
end States
section Sum
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {Γ : Finset G.GasSpin}
abbrev bondCurry (m : ℕ) : (TorusBond m → UnitQuaternion) ≃ᵐ TorusField m := MeasurableEquiv.curry (TorusSite m) (Fin 4) UnitQuaternion
theorem measurePreserving_bondCurry_symm (m : ℕ) [NeZero m] :
    MeasurePreserving (bondCurry m).symm (fieldHaar m) (Measure.pi fun _ : TorusBond m => haarUnit) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurePreserving_uncurry_fieldHaar <;> assumption
def insertLinks {I : Type} [Fintype I] {T : I → Type} [∀ i, Fintype (T i)] {m : ℕ} [NeZero m] (ι : ∀ i, T i → TorusBond m) (a : ∀ i, T i → UnitQuaternion) (W : TorusField m) :
    TorusField m := bondCurry m (insertValues ι a ((bondCurry m).symm W))
theorem measurable_insertLinks {I : Type} [Fintype I] {T : I → Type} [∀ i, Fintype (T i)] {m : ℕ} [NeZero m] (ι : ∀ i, T i → TorusBond m) :
    Measurable fun p : (∀ i, T i → UnitQuaternion) × TorusField m => insertLinks ι p.1 p.2 := by
  unfold insertLinks
  exact (bondCurry m).measurable.comp (measurable_insertValues.comp
    (measurable_fst.prodMk ((bondCurry m).symm.measurable.comp measurable_snd)))
open Classical in
theorem lintegral_fieldHaar_insertLinks (hp : LintegralPiPartitionStatement) {I : Type} [Fintype I] {T : I → Type}
    [∀ i, Fintype (T i)] {m : ℕ} [NeZero m] {ι : ∀ i, T i → TorusBond m} (h : IsDisjointEmbedding ι) (g : TorusField m → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ W, g W ∂fieldHaar m = ∫⁻ a, ∫⁻ W, g (insertLinks ι a W) ∂fieldHaar m
      ∂Measure.pi (fun i : I => Measure.pi fun _ : T i => haarUnit) := by
  have pres := measurePreserving_bondCurry_symm m
  have e1 : ∀ f : (TorusBond m → UnitQuaternion) → ℝ≥0∞, Measurable f →
      ∫⁻ W, f ((bondCurry m).symm W) ∂fieldHaar m = ∫⁻ w, f w ∂Measure.pi (fun _ : TorusBond m => haarUnit) :=
    fun f hf => pres.lintegral_comp hf
  have e2 : ∫⁻ W, g W ∂fieldHaar m = ∫⁻ w, g (bondCurry m w) ∂Measure.pi (fun _ : TorusBond m => haarUnit) := by
    have := e1 (fun w => g (bondCurry m w)) (hg.comp (bondCurry m).measurable)
    simpa only [MeasurableEquiv.apply_symm_apply] using this
  rw [e2, lintegral_pi_eq_lintegral_insertValues hp h haarUnit (fun w => g (bondCurry m w)) (hg.comp (bondCurry m).measurable)]
  refine lintegral_congr fun a => ?_
  have hm : Measurable fun w : TorusBond m → UnitQuaternion => g (bondCurry m (insertValues ι a w)) :=
    (hg.comp (bondCurry m).measurable).comp (measurable_insertValues.comp (measurable_const.prodMk measurable_id))
  exact (e1 (fun w => g (bondCurry m (insertValues ι a w))) hm).symm
open Classical in
theorem lintegral_fieldHaar_pi_family (hp : LintegralPiPartitionStatement) {m : ℕ} [NeZero m] {I : Type} [Fintype I]
    {T₁ T₂ : I → Type} [∀ i, Fintype (T₁ i)] [∀ i, Fintype (T₂ i)] {B₂ : Type} [Fintype B₂] {Ω : Type}
    [MeasurableSpace Ω] {ι₁ : ∀ i, T₁ i → TorusBond m} (h₁ : IsDisjointEmbedding ι₁) {ι₂ : ∀ i, T₂ i → B₂} (h₂ : IsDisjointEmbedding ι₂)
    (hc : ∀ β, ∃ p : Σ i, T₂ i, ι₂ p.1 p.2 = β) (μ : Measure Ω) [SigmaFinite μ]
    (cf : TorusField m → (B₂ → Ω) → ℝ≥0∞) (hcf : Measurable fun p : TorusField m × (B₂ → Ω) => cf p.1 p.2)
    (E : (∀ i, T₁ i → UnitQuaternion) → (∀ i, T₂ i → Ω) → ℝ≥0∞)
    (hE : Measurable fun p : (∀ i, T₁ i → UnitQuaternion) × (∀ i, T₂ i → Ω) => E p.1 p.2) (K : ℝ≥0∞)
    (hin : ∀ a l, ∫⁻ W, cf (insertLinks ι₁ a W) (coverGlue ι₂ hc l) ∂fieldHaar m = K * E a l) :
    ∫⁻ W, ∫⁻ ν, cf W ν ∂(Measure.pi fun _ : B₂ => μ) ∂fieldHaar m =
      K * ∫⁻ a, ∫⁻ l, E a l ∂Measure.pi (fun i : I => Measure.pi fun _ : T₂ i => μ)
        ∂Measure.pi (fun i : I => Measure.pi fun _ : T₁ i => haarUnit) := by
  have hglm : Measurable (coverGlue (X := Ω) ι₂ hc) := measurable_coverGlue _ hc
  have A1 : ∀ W, ∫⁻ ν, cf W ν ∂(Measure.pi fun _ : B₂ => μ) =
      ∫⁻ l, cf W (coverGlue ι₂ hc l) ∂Measure.pi (fun i : I => Measure.pi fun _ : T₂ i => μ) := fun W =>
    lintegral_pi_eq_lintegral_coverGlue hp h₂ hc μ (fun ν => cf W ν) (hcf.comp (measurable_const.prodMk measurable_id))
  simp only [A1]
  have hjoint : Measurable fun p : TorusField m × (∀ i, T₂ i → Ω) => cf p.1 (coverGlue ι₂ hc p.2) :=
    hcf.comp (measurable_fst.prodMk (hglm.comp measurable_snd))
  rw [lintegral_fieldHaar_insertLinks hp h₁ _ hjoint.lintegral_prod_right']
  have hswap : ∀ a : ∀ i, T₁ i → UnitQuaternion,
      ∫⁻ W, ∫⁻ l, cf (insertLinks ι₁ a W) (coverGlue ι₂ hc l)
          ∂Measure.pi (fun i : I => Measure.pi fun _ : T₂ i => μ) ∂fieldHaar m =
        ∫⁻ l, K * E a l ∂Measure.pi (fun i : I => Measure.pi fun _ : T₂ i => μ) := by
    intro a
    rw [lintegral_lintegral_swap]
    · exact lintegral_congr fun l => hin a l
    · exact (hcf.comp (((measurable_insertLinks _).comp (measurable_const.prodMk measurable_fst)).prodMk
        (hglm.comp measurable_snd))).aemeasurable
  simp only [hswap]
  have hl : ∀ a : ∀ i, T₁ i → UnitQuaternion, Measurable fun l : ∀ i, T₂ i → Ω => E a l :=
    fun a => hE.comp (measurable_const.prodMk measurable_id)
  have e3 : ∀ a, ∫⁻ l, K * E a l ∂Measure.pi (fun i : I => Measure.pi fun _ : T₂ i => μ) =
      K * ∫⁻ l, E a l ∂Measure.pi (fun i : I => Measure.pi fun _ : T₂ i => μ) :=
    fun a => lintegral_const_mul K (hl a)
  simp only [e3]
  rw [lintegral_const_mul K hE.lintegral_prod_right']
theorem measurable_valuesOn (Γ : Finset G.GasSpin) :
    Measurable (valuesOn (S := fun i : G.GasSpin => G.SpinState i) Γ) := by
  classical
  refine measurable_pi_lambda _ fun i => ?_
  unfold valuesOn
  by_cases h : i ∈ Γ
  · simp only [dif_pos h]
    exact measurable_inr.comp (measurable_pi_apply _)
  · simp only [dif_neg h]
    exact measurable_const
def familyStateOf {Γ : Finset G.GasSpin} (a : ∀ i : Γ, i.1.1.coreBonds → UnitQuaternion) (l : ∀ i : Γ, i.1.1.2 → R.labels.Ω)
    (o : ∀ i : Γ, i.1.1.core → BlockOffset R.params.side) : FamilyState G Γ := fun i => (a i, l i, o i)
theorem measurable_familyStateOf (o : ∀ i : Γ, i.1.1.core → BlockOffset R.params.side) :
    Measurable fun p : (∀ i : Γ, i.1.1.coreBonds → UnitQuaternion) × (∀ i : Γ, i.1.1.2 → R.labels.Ω) => familyStateOf (G := G) p.1 p.2 o :=
  measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
    (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_const)
open Classical in
theorem sum_caseIntegral_eq_lintegral_gas (hp : LintegralPiPartitionStatement) (F : CaseFunctional R n) (K : ℝ≥0∞)
    (hr : R.params.side ≤ 2 * R.range) (hΓ : G.IsPairwiseFarApart Γ) (hM : Measurable (G.gasIntegrand F))
    (hcf : ∀ b, Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled (G.familySites Γ) → R.labels.Ω) =>
      G.caseIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) b p.1 p.2)
    (hall : ∀ i : G.GasSpin, MeasurableSet {s : SupportState i.1 | G.IsAllowed i.1 s} ∧
      Measurable fun v : G.SpinState i => G.activity i.1 v.1)
    (hbases : ∀ (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω),
      G.caseIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) b W ν ≠ 0 → ∃ o, b = G.basesOfOffsets Γ o)
    (hinj : Function.Injective (G.basesOfOffsets Γ))
    (hparts₁ : IsDisjointEmbedding fun (i : Γ) (t : i.1.1.coreBonds) => (t.1 : TorusBond (n * R.params.side)))
    (hmem : ∀ (i : Γ) (t : i.1.1.2), t.1 ∈ G.state.unlabelled (G.familySites Γ))
    (hparts₂ : IsDisjointEmbedding fun (i : Γ) (t : i.1.1.2) => (⟨t.1, hmem i t⟩ : G.state.unlabelled (G.familySites Γ)))
    (hcover : ∀ z : G.state.unlabelled (G.familySites Γ), ∃ p : Σ i : Γ, i.1.1.2, (⟨p.2.1, hmem p.1 p.2⟩ : G.state.unlabelled (G.familySites Γ)) = z)
    (hover : ∀ (c : FamilyState G Γ) (W : TorusField (n * R.params.side)), G.overwriteField c W =
      insertLinks (fun (i : Γ) (t : i.1.1.coreBonds) => (t.1 : TorusBond (n * R.params.side))) (fun i => (c i).1) W)
    (hinner : ∀ (c : FamilyState G Γ) (ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω),
      (∀ (i : Γ) (z : TorusSite (n * R.params.side)) (hz : z ∈ i.1.1.2) (hr : z ∈ G.state.unlabelled (G.familySites Γ)),
          ν ⟨z, hr⟩ = (c i).2.1 ⟨z, hz⟩) →
      ∫⁻ W, G.caseIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.familySetting c).bases (G.overwriteField c W) ν
          ∂fieldHaar (n * R.params.side) =
        K * ((∏ i : Γ, G.allowedActivity i.1 (c i)) * (G.familySetting c).settingIntegral F (G.familyBadBonds Γ))) :
    ∑ b : BaseChoice R.params.side n, G.caseIntegral F (G.familyBadBonds Γ) (G.familySites Γ) b =
      K * ∫⁻ τ, G.gasIntegrand F (valuesOn Γ τ) ∂Measure.pi (fun i : Γ => G.spinStateMeasure i) := by
  set E : FamilyState G Γ → ℝ≥0∞ := fun c =>
    (∏ i : Γ, G.allowedActivity i.1 (c i)) * (G.familySetting c).settingIntegral F (G.familyBadBonds Γ) with hE
  have hfac : ∀ i : G.GasSpin, Measurable (G.allowedActivity i) := by
    intro i
    have e : G.allowedActivity i = fun s => if hs : s ∈ {s | G.IsAllowed i.1 s} then
        ENNReal.ofReal (G.activity i.1 (⟨s, hs⟩ : G.SpinState i).1) else 0 := by
      funext s
      unfold GasGround.allowedActivity
      by_cases h : G.IsAllowed i.1 s
      · rw [if_pos h, dif_pos (show s ∈ {s | G.IsAllowed i.1 s} from h)]
      · rw [if_neg h, dif_neg (show s ∉ {s | G.IsAllowed i.1 s} from h)]
    rw [e]
    exact Measurable.dite (f := fun v : {s | G.IsAllowed i.1 s} => ENNReal.ofReal (G.activity i.1 v.1))
      (g := fun _ => 0) (ENNReal.measurable_ofReal.comp (hall i).2) measurable_const (hall i).1
  have hden : ∀ i : G.GasSpin, (fun s : G.SpinState i => G.allowedActivity i s.1) =
      fun s => ENNReal.ofReal (G.activity i.1 s.1) := by
    intro i
    funext s
    unfold GasGround.allowedActivity
    rw [if_pos s.2]
  have s1 : ∀ i : Γ, SigmaFinite ((supportStateMeasure i.1.1).comap (Subtype.val : {x // G.IsAllowed i.1.1 x} → _)) :=
    fun i => sigmaFinite_comap_subtype_val _ _
  have hst : ∀ i : Γ, ((supportStateMeasure i.1.1).comap (Subtype.val : {x // G.IsAllowed i.1.1 x} → _)).withDensity
      (fun s => G.allowedActivity i.1 s.1) = G.spinStateMeasure i.1 := by
    intro i
    unfold GasGround.spinStateMeasure
    rw [show (fun s : {x // G.IsAllowed i.1.1 x} => G.allowedActivity i.1 s.1) = _ from hden i.1]
  have s2 : ∀ i : Γ, SigmaFinite (((supportStateMeasure i.1.1).comap (Subtype.val : {x // G.IsAllowed i.1.1 x} → _)).withDensity
      fun s => G.allowedActivity i.1 s.1) := fun i => by
    rw [hst i]
    infer_instance
  obtain ⟨hEm, hgas⟩ := lintegral_pi_withDensity_subtype (fun i : Γ => supportStateMeasure i.1.1) (fun i c => G.IsAllowed i.1.1 c)
    (fun i => (hall i.1).1) (fun i s => G.allowedActivity i.1 s)
    (fun i => hfac i.1)
    (fun τ : ∀ i : Γ, G.SpinState i.1 => G.gasIntegrand F (valuesOn Γ τ))
    (hM.comp (measurable_valuesOn Γ)) E (by
      intro c
      by_cases hc : ∀ i : Γ, G.IsAllowed i.1.1 (c i)
      · rw [dif_pos hc, hE]
        simp only
        rw [gasIntegrand_valuesOn hΓ]
      · rw [dif_neg hc, hE]
        simp only
        push Not at hc
        obtain ⟨i, hi⟩ := hc
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by
          unfold GasGround.allowedActivity
          rw [if_neg hi]), zero_mul])
  have hgas' : ∫⁻ τ, G.gasIntegrand F (valuesOn Γ τ) ∂Measure.pi (fun i : Γ => G.spinStateMeasure i) =
      ∫⁻ c, E c ∂Measure.pi (fun i : Γ => supportStateMeasure i.1.1) := by
    rw [← hgas]
    congr 2
    funext i
    exact (hst i).symm
  have hsplit : ∫⁻ c, E c ∂Measure.pi (fun i : Γ => supportStateMeasure i.1.1) =
      ∑ o : ∀ i : Γ, i.1.1.core → BlockOffset R.params.side,
        ∫⁻ a : ∀ i : Γ, i.1.1.coreBonds → UnitQuaternion, ∫⁻ l : ∀ i : Γ, i.1.1.2 → R.labels.Ω, E (familyStateOf a l o)
          ∂Measure.pi (fun i : Γ => Measure.pi fun _ : i.1.1.2 => R.labels.μ)
          ∂Measure.pi (fun i : Γ => Measure.pi fun _ : i.1.1.coreBonds => haarUnit) := by
    exact lintegral_pi_prod_prod_count (fun i : Γ => Measure.pi fun _ : i.1.1.coreBonds => haarUnit)
      (fun i : Γ => Measure.pi fun _ : i.1.1.2 => R.labels.μ) E hEm
  rw [hgas', hsplit, Finset.mul_sum]
  symm
  refine Finset.sum_of_injOn (G.basesOfOffsets Γ) hinj.injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_ ?_
  · intro b _ hb
    unfold GasGround.caseIntegral
    have : ∀ W (ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω),
        G.caseIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) b W ν = 0 := by
      intro W ν
      by_contra h0
      obtain ⟨o, ho⟩ := hbases b W ν h0
      exact hb ⟨o, Finset.mem_coe.mpr (Finset.mem_univ _), ho.symm⟩
    simp [this]
  · intro o _
    unfold GasGround.caseIntegral
    have hsep := fun c => coresDisjoint_familyData hΓ hr (G := G) c
    have hEo : Measurable fun p : (∀ i : Γ, i.1.1.coreBonds → UnitQuaternion) × (∀ i : Γ, i.1.1.2 → R.labels.Ω) =>
        E (familyStateOf p.1 p.2 o) := hEm.comp (measurable_familyStateOf o)
    refine (lintegral_fieldHaar_pi_family hp hparts₁ hparts₂ hcover R.labels.μ
      (G.caseIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.basesOfOffsets Γ o)) (hcf _)
      (fun a l => E (familyStateOf a l o)) hEo K ?_).symm
    intro a l
    have h1 := hinner (familyStateOf a l o) (coverGlue _ hcover l) (fun i z hz hr' =>
      coverGlue_apply_embed hparts₂ hcover l i ⟨z, hz⟩)
    rw [bases_familySetting (hsep _)] at h1
    simp only [hover] at h1
    exact h1
end Sum
section Facts
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {Γ : Finset G.GasSpin}
theorem isDisjointEmbedding_coreBonds (hΓ : G.IsPairwiseFarApart Γ) (hr : R.params.side ≤ 2 * R.range) :
    IsDisjointEmbedding fun (i : Γ) (t : i.1.1.coreBonds) => (t.1 : TorusBond (n * R.params.side)) := by
  rintro ⟨i, t⟩ ⟨j, u⟩ e
  have e' : t.1 = u.1 := e
  by_cases hij : i = j
  · subst hij
    have : t = u := Subtype.ext e'
    rw [this]
  · exact ((hΓ i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h)).false_of_mem_cores hr (GasSupport.parentBlock_mem_core_of_mem_coreBonds t.2)
      (e' ▸ GasSupport.parentBlock_mem_core_of_mem_coreBonds u.2)).elim
theorem mem_unlabelled_of_mem_sites (i : Γ) (t : i.1.1.2) : t.1 ∈ G.state.unlabelled (G.familySites Γ) := by
  classical
  unfold CoarseState.unlabelled GasGround.familySites
  exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i.1, i.2, t.2⟩),
    labelAt_eq_inl_of_not_mem_recordedSites (not_mem_recordedSites_of_mem_sites i.1 t.2)⟩
theorem isDisjointEmbedding_sites (hΓ : G.IsPairwiseFarApart Γ) :
    IsDisjointEmbedding fun (i : Γ) (t : i.1.1.2) => (⟨t.1, mem_unlabelled_of_mem_sites i t⟩ : G.state.unlabelled (G.familySites Γ)) := by
  classical
  rintro ⟨i, t⟩ ⟨j, u⟩ e
  have e' : t.1 = u.1 := congrArg Subtype.val e
  by_cases hij : i = j
  · subst hij
    have : t = u := Subtype.ext e'
    rw [this]
  · have h1 := hΓ i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) t.1 (Finset.mem_union_right _ t.2) u.1
      (Finset.mem_union_right _ u.2)
    rw [e', supDist_self] at h1
    omega
theorem exists_sites_eq (z : G.state.unlabelled (G.familySites Γ)) :
    ∃ p : Σ i : Γ, i.1.1.2, (⟨p.2.1, mem_unlabelled_of_mem_sites p.1 p.2⟩ : G.state.unlabelled (G.familySites Γ)) = z := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp z.2
  unfold GasGround.familySites at h1
  rcases Finset.mem_union.mp h1 with h | h
  · have := (Finset.mem_filter.mp h).2
    rw [h2] at this
    simp at this
  · obtain ⟨i, hi, hz⟩ := Finset.mem_biUnion.mp h
    exact ⟨⟨⟨i, hi⟩, ⟨z.1, hz⟩⟩, rfl⟩
theorem overwriteField_eq_insertLinks (hΓ : G.IsPairwiseFarApart Γ) (hr : R.params.side ≤ 2 * R.range) (c : FamilyState G Γ) (W : TorusField (n * R.params.side)) :
    G.overwriteField c W = insertLinks (fun (i : Γ) (t : i.1.1.coreBonds) => (t.1 : TorusBond (n * R.params.side))) (fun i => (c i).1) W := by
  classical
  funext x k
  show _ = insertValues (fun (i : Γ) (t : i.1.1.coreBonds) => (t.1 : TorusBond (n * R.params.side))) (fun i => (c i).1)
    ((bondCurry _).symm W) (x, k)
  by_cases h : ∃ i : Γ, (x, k) ∈ i.1.1.coreBonds
  · obtain ⟨i, hi⟩ := h
    have e1 := insertValues_apply_embed (isDisjointEmbedding_coreBonds hΓ hr) (fun i => (c i).1) ((bondCurry _).symm W) i ⟨(x, k), hi⟩
    have e2 := fieldAt_familyData (coresDisjoint_familyData hΓ hr c) i hi
    rw [show insertValues (fun (i : Γ) (t : i.1.1.coreBonds) => (t.1 : TorusBond (n * R.params.side))) (fun i => (c i).1)
      ((bondCurry _).symm W) (x, k) = (c i).1 ⟨(x, k), hi⟩ from e1]
    unfold GasGround.overwriteField
    rw [e2]
  · unfold GasGround.overwriteField
    rw [fieldAt_familyData_of_forall_not_mem c fun i hi => h ⟨i, hi⟩, insertValues_apply_of_not_mem]
    · rfl
    · rintro ⟨⟨i, t⟩, e⟩
      exact h ⟨i, e ▸ t.2⟩
theorem basesOfOffsets_apply_cell (hΓ : G.IsPairwiseFarApart Γ) (hr : R.params.side ≤ 2 * R.range) (o : ∀ i : Γ, i.1.1.core → BlockOffset R.params.side)
    (i : Γ) (e : (stepBlockFrame R.params.side n).Cell) (hy : cellBlock R.params.side n e ∈ i.1.1.core) :
    G.basesOfOffsets Γ o e = frameBlockSite R.params.side n (cellBlock R.params.side n e) (o i ⟨_, hy⟩) := by
  classical
  have hex : ∃ i : Γ, cellBlock R.params.side n e ∈ i.1.1.core := ⟨i, hy⟩
  unfold GasGround.basesOfOffsets
  rw [dif_pos hex]
  have hch : hex.choose = i := by
    by_contra hne
    have hij : hex.choose.1 ≠ i.1 := fun e => hne (Subtype.ext e)
    exact (hΓ _ hex.choose.2 _ i.2 hij).false_of_mem_cores hr hex.choose_spec hy
  have key : ∀ (j : Γ) (hj : cellBlock R.params.side n e ∈ j.1.1.core), j = i → o j ⟨_, hj⟩ = o i ⟨_, hy⟩ := by
    rintro j hj rfl
    rfl
  rw [key _ hex.choose_spec hch]
theorem basesOfOffsets_apply_torusSiteInFrame (hΓ : G.IsPairwiseFarApart Γ) (hr : R.params.side ≤ 2 * R.range) (o : ∀ i : Γ, i.1.1.core → BlockOffset R.params.side)
    (i : Γ) {y : TorusSite n} (hy : y ∈ i.1.1.core) :
    G.basesOfOffsets Γ o (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = frameBlockSite R.params.side n y (o i ⟨y, hy⟩) := by
  have hp : ∀ k, (stepBlockFrame R.params.side n).period 1 k = n := fun k => by simp [stepBlockFrame, BlockFrame.period, BlockFrame.top]
  have e : cellBlock R.params.side n (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = y := toTorusSite_torusSiteInFrame hp y
  have key : ∀ (z : TorusSite n) (hz : z ∈ i.1.1.core), z = y →
      frameBlockSite R.params.side n z (o i ⟨z, hz⟩) = frameBlockSite R.params.side n y (o i ⟨y, hy⟩) := by
    rintro z hz rfl
    rfl
  exact (basesOfOffsets_apply_cell hΓ hr o i (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) (e.symm ▸ hy)).trans (key _ _ e)
theorem basesOfOffsets_injective (hΓ : G.IsPairwiseFarApart Γ) (hr : R.params.side ≤ 2 * R.range) : Function.Injective (G.basesOfOffsets Γ) := by
  intro o o' e
  funext i y
  have h1 := congrFun e (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y.1)
  rw [basesOfOffsets_apply_torusSiteInFrame hΓ hr o i y.2, basesOfOffsets_apply_torusSiteInFrame hΓ hr o' i y.2] at h1
  exact frameBlockSite_injective _ h1
end Facts
end FamilyCaseSum
open FamilyCaseSum in
theorem familyCaseSumEqIntegral_holds (hp : LintegralPiPartitionStatement) (hi : FamilyInnerLintegral)
    (hb : CaseIntegrandMeasurable) (hB : NonzeroCaseBasesAreGroundOffsets) (hf1 : CouplingFloorExists) :
    FamilyCaseSumEqIntegral := by
  classical
  intro T hT
  obtain ⟨y₁, hi⟩ := hi T hT
  obtain ⟨y₂, hb⟩ := hb T hT
  obtain ⟨y₃, hB⟩ := hB T hT
  obtain ⟨y₄, hf1⟩ := hf1 1 T.side T.rt one_pos
  refine ⟨max y₁ (max y₂ (max y₃ y₄)), fun y hy R hR hx' n _ G hG F hF hM Γ hΓ => ?_⟩
  have b₁ : y₁ ≤ y := (le_max_left _ _).trans hy
  have b₂ : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have b₃ : y₃ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have b₄ : y₄ ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hr : R.params.side ≤ 2 * R.range := by
    have := (hf1 R.coupling (b₄.trans hR.le_coupling)).1
    have e : R.range = clusterRange R.coupling := rfl
    omega
  obtain ⟨c1, -, c2⟩ := hb y b₂ R hR hx' n G hG
  refine sum_caseIntegral_eq_lintegral_gas hp F _ hr hΓ hM (fun b => c1 F hF _ _ b) c2
    (fun b W ν h0 => hB y b₃ R hR hx' n G hG F Γ hΓ b W ν h0) (basesOfOffsets_injective hΓ hr) (isDisjointEmbedding_coreBonds hΓ hr)
    mem_unlabelled_of_mem_sites (isDisjointEmbedding_sites hΓ) exists_sites_eq (overwriteField_eq_insertLinks hΓ hr)
    (fun c ν hν => hi y b₁ R hR hx' n G hG F hF Γ hΓ c ν hν)
end YangMills.Construction.ClusterExpansionOfAStep
end
