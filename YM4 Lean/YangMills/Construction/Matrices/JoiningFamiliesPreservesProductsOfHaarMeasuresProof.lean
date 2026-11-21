import YangMills.Construction.ReflectionPositivity.IntegralOverVariablesOfATorusProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.ComplexMatrix2
namespace SpinHarmonics.GlueMeasure
private lemma haarPi_pi_univ (ι : Type) [Fintype ι] (s : ι → Set specialUnitary)
    (hs : ∀ i, MeasurableSet (s i)) :
    haarPi ι (Set.pi Set.univ s) = ∏ i, haarProb (s i) := by
  have h := Measure.infinitePi_pi (μ := fun _ : ι => haarProb) (s := Finset.univ) (t := s)
    (fun i _ => hs i)
  simpa [haarPi] using h
private lemma measurable_glue {J : Type} (B : Set J) :
    Measurable fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2 := by apply _root_.YangMills.SharedProofs.p39109 <;> assumption
theorem glueMeasurePreserving_holds : GlueMeasurePreserving := by
  intro J _ B
  classical
  let _ : Fintype J := Fintype.ofFinite J
  have hmeas := measurable_glue B
  refine ⟨hmeas, ?_⟩
  refine Measure.eq_infinitePi (μ := fun _ : J => haarProb) ?_
  intro F t ht
  let v : J → Set specialUnitary := fun j => if j ∈ F then t j else Set.univ
  have hv : ∀ j, MeasurableSet (v j) := by
    intro j
    by_cases hj : j ∈ F
    · simpa [v, hj] using ht j
    · simp [v, hj]
  have hpre : (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2) ⁻¹'
        Set.pi (F : Set J) t =
      Set.pi Set.univ (fun b : ↥B => v b) ×ˢ Set.pi Set.univ (fun c : ↥Bᶜ => v c) := by
    ext p
    have hco : ∀ j, glue B p.1 p.2 j ∈ v j ↔ (j ∈ F → glue B p.1 p.2 j ∈ t j) := by
      intro j
      by_cases hj : j ∈ F <;> simp [v, hj]
    constructor
    · intro h
      refine ⟨fun b _ => ?_, fun c _ => ?_⟩
      · have h' := (hco b).2 fun hb => h b (Finset.mem_coe.mpr hb)
        rwa [glue_of_mem B p.1 p.2 b] at h'
      · have h' := (hco c).2 fun hc => h c (Finset.mem_coe.mpr hc)
        rwa [glue_of_notMem B p.1 p.2 c] at h'
    · rintro ⟨h₁, h₂⟩ j hj
      refine (hco j).1 ?_ (Finset.mem_coe.mp hj)
      by_cases hB : j ∈ B
      · have h' := h₁ ⟨j, hB⟩ (Set.mem_univ _)
        rwa [← glue_of_mem B p.1 p.2 ⟨j, hB⟩] at h'
      · have h' := h₂ ⟨j, hB⟩ (Set.mem_univ _)
        rwa [← glue_of_notMem B p.1 p.2 ⟨j, hB⟩] at h'
  have hbox : MeasurableSet (Set.pi (F : Set J) t) :=
    MeasurableSet.pi F.countable_toSet fun i _ => ht i
  rw [Measure.map_apply hmeas hbox, hpre, Measure.prod_prod,
    haarPi_pi_univ ↥B _ (fun b => hv b), haarPi_pi_univ ↥Bᶜ _ (fun c => hv c)]
  have hsplit : (∏ b : ↥B, haarProb (v b)) * ∏ c : ↥Bᶜ, haarProb (v c) = ∏ j, haarProb (v j) :=
    Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ B) fun j => haarProb (v j)
  have hvmass : ∀ j, haarProb (v j) = if j ∈ F then haarProb (t j) else 1 := by
    intro j
    by_cases hj : j ∈ F <;> simp [v, hj]
  rw [hsplit]
  simp only [hvmass]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
end SpinHarmonics.GlueMeasure
end YangMills.Construction
end
