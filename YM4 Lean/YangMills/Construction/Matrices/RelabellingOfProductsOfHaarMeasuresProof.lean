import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfGProof
import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.Matrices.RelabellingOfProductsOfHaarMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.HaarRelabel
private lemma haarPi_isProbabilityMeasure (ι : Type) [Countable ι] :
    IsProbabilityMeasure (haarPi ι) := by apply _root_.YangMills.Construction.SpinHarmonics.FieldCalculus.isProbabilityMeasure_haarPi <;> assumption
private lemma haarPi_pi_univ (ι : Type) [Fintype ι] (w : ι → Set specialUnitary)
    (hw : ∀ i, MeasurableSet (w i)) :
    haarPi ι (Set.pi Set.univ w) = ∏ i, haarProb (w i) := by
  have h := Measure.infinitePi_pi (μ := fun _ : ι => haarProb) (s := Finset.univ) (t := w)
    (fun i _ => hw i)
  simpa [haarPi] using h
private def sumCoord {B S : Type}
    (x : (B → specialUnitary) × (B → specialUnitary) × (S → specialUnitary)) :
    B ⊕ B ⊕ S → specialUnitary :=
  Sum.elim x.1 (Sum.elim x.2.1 x.2.2)
private lemma measurable_sumCoord {B S : Type} (i : B ⊕ B ⊕ S) :
    Measurable fun x : (B → specialUnitary) × (B → specialUnitary) × (S → specialUnitary) =>
      sumCoord x i := by
  rcases i with b | b | c
  · exact (measurable_pi_apply b).comp measurable_fst
  · exact (measurable_pi_apply b).comp (measurable_fst.comp measurable_snd)
  · exact (measurable_pi_apply c).comp (measurable_snd.comp measurable_snd)
theorem statement_of_haarExpChart (hHaar : HaarExpChartProperties) : Statement := by
  intro P B S _ _ _ e s
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype S := Fintype.ofFinite S
  have := haarPi_isProbabilityMeasure B
  have := haarPi_isProbabilityMeasure S
  have hInvMap : Measure.map (fun g : specialUnitary => g⁻¹) haarProb = haarProb := hHaar.2.2.2
  have hInv : Measurable fun g : specialUnitary => g⁻¹ := continuous_inv.measurable
  have hMeas : Measurable (relabel e s) := by
    refine measurable_pi_lambda _ fun p => ?_
    have hc := measurable_sumCoord (B := B) (S := S) (e p)
    cases hs : s p
    · have hf : (fun x => relabel e s x p) = fun x => sumCoord x (e p) := by
        funext x
        simp [relabel, hs, sumCoord]
      rw [hf]
      exact hc
    · have hf : (fun x => relabel e s x p) = fun x => (sumCoord x (e p))⁻¹ := by
        funext x
        simp [relabel, hs, sumCoord]
      rw [hf]
      exact hInv.comp hc
  refine ⟨hMeas, ?_⟩
  refine Measure.eq_infinitePi (μ := fun _ : P => haarProb) ?_
  intro F t ht
  let v : P → Set specialUnitary := fun p =>
    if p ∈ F then (if s p = true then (fun g : specialUnitary => g⁻¹) ⁻¹' t p else t p)
    else Set.univ
  have hv : ∀ p, MeasurableSet (v p) := by
    intro p
    by_cases hp : p ∈ F
    · by_cases hs : s p = true
      · simpa [v, hp, hs] using hInv (ht p)
      · simpa [v, hp, hs] using ht p
    · simp [v, hp]
  have hvMass : ∀ p, haarProb (v p) = if p ∈ F then haarProb (t p) else 1 := by
    intro p
    by_cases hp : p ∈ F
    · by_cases hs : s p = true
      · have h := Measure.map_apply (μ := haarProb) hInv (ht p)
        rw [hInvMap] at h
        simpa [v, hp, hs] using h.symm
      · simp [v, hp, hs]
    · simp [v, hp]
  let w : B ⊕ B ⊕ S → Set specialUnitary := fun i => v (e.symm i)
  have hw : ∀ i, MeasurableSet (w i) := fun i => hv _
  have hwe : ∀ p, w (e p) = v p := fun p => by simp [w]
  have hPre : relabel e s ⁻¹' Set.pi F t =
      Set.pi Set.univ (fun b => w (Sum.inl b)) ×ˢ
        (Set.pi Set.univ (fun b => w (Sum.inr (Sum.inl b))) ×ˢ
          Set.pi Set.univ (fun c => w (Sum.inr (Sum.inr c)))) := by
    ext x
    have hAll : (∀ i, sumCoord x i ∈ w i) ↔ x ∈ relabel e s ⁻¹' Set.pi F t := by
      constructor
      · intro h p hpF
        have hp : p ∈ F := Finset.mem_coe.mp hpF
        have h' := h (e p)
        rw [hwe] at h'
        by_cases hs : s p = true
        · simpa [v, hp, hs, relabel, sumCoord] using h'
        · simpa [v, hp, hs, relabel, sumCoord] using h'
      · intro h i
        obtain ⟨p, rfl⟩ := e.surjective i
        rw [hwe]
        by_cases hp : p ∈ F
        · have h' := h p hp
          by_cases hs : s p = true
          · simpa [v, hp, hs, relabel, sumCoord] using h'
          · simpa [v, hp, hs, relabel, sumCoord] using h'
        · simp [v, hp]
    rw [← hAll]
    simp [Sum.forall, sumCoord, Set.mem_prod, Set.mem_pi]
  have hBox : MeasurableSet (Set.pi (F : Set P) t) :=
    MeasurableSet.pi F.countable_toSet fun i _ => ht i
  rw [Measure.map_apply hMeas hBox, hPre, Measure.prod_prod, Measure.prod_prod,
    haarPi_pi_univ B _ (fun b => hw _), haarPi_pi_univ B _ (fun b => hw _),
    haarPi_pi_univ S _ (fun c => hw _)]
  have hSplit : (∏ i, haarProb (w i)) = (∏ b, haarProb (w (Sum.inl b))) *
      ((∏ b, haarProb (w (Sum.inr (Sum.inl b)))) * ∏ c, haarProb (w (Sum.inr (Sum.inr c)))) := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  rw [← hSplit, Fintype.prod_equiv e.symm (fun i => haarProb (w i)) (fun p => haarProb (v p))
    (fun i => rfl)]
  simp only [hvMass]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
end YangMills.Construction.Matrices.ComplexMatrix2.HaarRelabel
end
