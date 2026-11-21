import YangMills.Construction.LawInAState.MarksOnTheBoxProof
import YangMills.Construction.LawOnABoxOfTheFlow.PlaquettesAreSmall
open MeasureTheory Finset
open YangMills.Construction.TorusFields

namespace YangMills.ReferenceCalibration

/-- A sitewise hull estimate and the one-plaquette energy tail control the whole
reference torus. The only volume loss here is the number of sites. -/
theorem bad_reference_torus_measure
    {n : ℕ} [NeZero n] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → TorusField n) (Y : Ω → Finset (TorusSite n)) (t H P : ℝ)
    (ht : 0 ≤ t) (hP : 0 ≤ P)
    (hh : ∀ z, μ.real {u | z ∈ Y u} ≤ H)
    (hp : ∀ p ∈ plaquettesIn (univ : Finset (TorusSite n)),
      μ.real {u | t ^ 2 / 2 < plaquetteEnergy (W u) p.1 p.2.1 p.2.2} ≤ P) :
    μ.real {u | Y u ≠ ∅ ∨ ∃ z i j, t < curvature (W u) z i j}
      ≤ (n : ℝ) ^ 4 * (H + 16 * P) := by
  classical
  let E (p : TorusPlaquette n) := {u | t < curvature (W u) p.1 p.2.1 p.2.2}
  let faces := plaquettesIn (univ : Finset (TorusSite n))
  have face_mem (z : TorusSite n) {i j : Fin 4} (hij : i < j) :
      (z,i,j) ∈ faces := by simp [faces, plaquettesIn, hij]
  have oriented (u) (z : TorusSite n) (i j : Fin 4) (hij : t < curvature (W u) z i j) :
      ∃ p ∈ faces, u ∈ E p := by
    rcases lt_trichotomy i j with h | rfl | h
    · exact ⟨(z,i,j), face_mem z h, hij⟩
    · have hz : curvature (W u) z i i = 0 := by
        simp [curvature, holonomy, mul_assoc]
      linarith
    · exact ⟨(z,j,i), face_mem z h, by
        change t < curvature (W u) z j i
        rw [YangMills.SharedProofs.p108355 (W u) z i j]
        exact hij⟩
  have cover : {u | Y u ≠ ∅ ∨ ∃ z i j, t < curvature (W u) z i j} ⊆
      (⋃ z, {u | z ∈ Y u}) ∪ ⋃ p ∈ faces, E p := by
    intro u h
    rcases h with h | ⟨z,i,j,h⟩
    · obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.2 h
      exact Or.inl (Set.mem_iUnion.2 ⟨z,hz⟩)
    · obtain ⟨p, hp', hu⟩ := oriented u z i j h
      exact Or.inr (Set.mem_iUnion.2 ⟨p,Set.mem_iUnion.2 ⟨hp',hu⟩⟩)
  have henergy (p) (hpf : p ∈ faces) : μ.real (E p) ≤ P := by
    refine (measureReal_mono (μ := μ) (s₂ := {u | t ^ 2 / 2 < plaquetteEnergy (W u) p.1 p.2.1 p.2.2}) ?_ (measure_ne_top _ _)).trans (hp p hpf)
    intro u hu
    change t < curvature (W u) p.1 p.2.1 p.2.2 at hu
    change t ^ 2 / 2 < plaquetteEnergy (W u) p.1 p.2.1 p.2.2
    rw [plaquetteEnergy_eq_curvature_sq]
    nlinarith
  have hcard : (Fintype.card (TorusSite n) : ℝ) = (n : ℝ) ^ 4 := by
    simp [TorusSite, Fintype.card_pi]
  have hfaces : (faces.card : ℝ) ≤ (n : ℝ) ^ 4 * 16 := by
    have h := faces.card_le_univ
    have he : (Fintype.card (TorusPlaquette n) : ℝ) = (n : ℝ) ^ 4 * 16 := by
      simp [TorusPlaquette, Fintype.card_prod]
    rw [← he]
    exact_mod_cast h
  calc μ.real _ ≤ μ.real ((⋃ z, {u | z ∈ Y u}) ∪ ⋃ p ∈ faces, E p) := measureReal_mono cover
    _ ≤ μ.real (⋃ z, {u | z ∈ Y u}) + μ.real (⋃ p ∈ faces, E p) := measureReal_union_le _ _
    _ ≤ (∑ z, μ.real {u | z ∈ Y u}) + ∑ p ∈ faces, μ.real (E p) :=
      add_le_add (measureReal_iUnion_fintype_le _) (measureReal_biUnion_finset_le _ _)
    _ ≤ (∑ _ : TorusSite n, H) + ∑ _ ∈ faces, P :=
      add_le_add (sum_le_sum fun z _ => hh z) (sum_le_sum henergy)
    _ ≤ (n : ℝ) ^ 4 * (H + 16 * P) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, hcard]
      nlinarith [mul_le_mul_of_nonneg_right hfaces hP]

end YangMills.ReferenceCalibration
