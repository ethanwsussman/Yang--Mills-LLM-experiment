import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.CoercivityOfTheChain
import YangMills.Construction.HoleBesideASecondHole.CurvatureBelowTheElementsAtItsCorners
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CornerCounting
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.LumpContours.BlockLevels
variable {F : BlockFrame}
def plaquettePlanes : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun d => d.1 < d.2
theorem card_plaquettePlanes : (plaquettePlanes).card = 6 := by decide
def plaquettesWithCorner {j : ℕ} (y : F.Site j) : Finset (F.Site j × Fin 4 × Fin 4) :=
  ((Finset.univ : Finset (Bool × Bool)) ×ˢ plaquettePlanes).image fun e =>
    (y - (if e.1.1 then unitStep j e.2.1 else 0) - (if e.1.2 then unitStep j e.2.2 else 0), e.2.1, e.2.2)
theorem card_plaquettesWithCorner_le {j : ℕ} (y : F.Site j) : (plaquettesWithCorner y).card ≤ 24 := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, card_plaquettePlanes]
  simp
theorem mem_plaquettesWithCorner {j : ℕ} {y : F.Site j} {p : F.Site j × Fin 4 × Fin 4} (hlt : p.2.1 < p.2.2)
    (hy : y ∈ plaquetteCorners p) : p ∈ plaquettesWithCorner y := by
  obtain ⟨x, μ, ν⟩ := p
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hy
  refine Finset.mem_image.2 ?_
  rcases hy with rfl | rfl | rfl | rfl
  · exact ⟨((false, false), (μ, ν)), by simp [plaquettePlanes, hlt], by simp <;> abel⟩
  · exact ⟨((true, false), (μ, ν)), by simp [plaquettePlanes, hlt], by simp <;> abel⟩
  · exact ⟨((false, true), (μ, ν)), by simp [plaquettePlanes, hlt], by simp <;> abel⟩
  · exact ⟨((true, true), (μ, ν)), by simp [plaquettePlanes, hlt], by simp <;> abel⟩
theorem card_filter_mem_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (hL : Odd F.blockSide) {B : Type}
    [DecidableEq B] (P : Finset (F.Site j × Fin 4 × Fin 4)) (hP : ∀ p ∈ P, p.2.1 < p.2.2)
    (E : F.Site j × Fin 4 × Fin 4 → Finset B) (site : B → F.Site i)
    (hE : ∀ p x, x ∈ E p → site x ∈ cutBelow i (plaquetteCorners p)) (x : B) :
    (P.filter fun p => x ∈ E p).card ≤ 24 := by
  classical
  by_cases hne : (P.filter fun p => x ∈ E p).Nonempty
  · obtain ⟨p0, hp0⟩ := hne
    obtain ⟨y, -, hy⟩ := Finset.mem_biUnion.1 (hE p0 x (Finset.mem_filter.1 hp0).2)
    refine (Finset.card_le_card ?_).trans (card_plaquettesWithCorner_le y)
    intro p hp
    obtain ⟨hpP, hpx⟩ := Finset.mem_filter.1 hp
    obtain ⟨y', hy', hu⟩ := Finset.mem_biUnion.1 (hE p x hpx)
    have : y = y' := eq_of_mem_sitesBelow_of_mem_sitesBelow hij hj hL hy hu
    subst this
    exact mem_plaquettesWithCorner (hP p hpP) hy'
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
    simp
theorem sum_cutChainEnergy_corners_le {a : ℝ} (ha : 0 ≤ a) {j : ℕ} (hj : j ≤ F.top) (hL : Odd F.blockSide)
    (X : Finset (F.Site j)) (P : Finset (F.Site j × Fin 4 × Fin 4)) (U : F.FieldChain)
    (hP : P ⊆ cutPlaquettes X) :
    ∑ p ∈ P, cutChainEnergy a j (plaquetteCorners p) U ≤ 24 * cutChainEnergy a j X U := by
  classical
  have hlt : ∀ p ∈ P, p.2.1 < p.2.2 := fun p hp => by
    have := hP hp
    simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at this
    exact this.2.1
  have hsub : ∀ p ∈ P, plaquetteCorners p ⊆ X := fun p hp => by
    have := hP hp
    simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at this
    exact this.2.2
  have h0 := sum_sum_le_mul_sum_of_card_le P (fun p => cutPlaquettes (cutBelow 0 (plaquetteCorners p)))
    (cutPlaquettes (cutBelow 0 X)) (plaquetteEnergy (U 0)) (plaquetteEnergy_nonneg _) 24
    (fun p hp => cutPlaquettes_mono (cutBelow_mono 0 (hsub p hp)))
    (fun q _ => card_filter_mem_le (Nat.zero_le j) hj hL P hlt _ (fun q => q.1) (fun p q hq => by
      simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hq
      exact hq.1) q)
  have h1 : ∀ i ∈ Finset.range j, ∑ p ∈ P, ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)),
      blockFit (U i) (U (i + 1)) c ≤
      24 * ∑ c ∈ cutBonds (cutBelow (i + 1) X), blockFit (U i) (U (i + 1)) c := fun i hi => by
    have hij : i + 1 ≤ j := Finset.mem_range.1 hi
    have := sum_sum_le_mul_sum_of_card_le P (fun p => cutBonds (cutBelow (i + 1) (plaquetteCorners p)))
      (cutBonds (cutBelow (i + 1) X)) (blockFit (U i) (U (i + 1))) (blockFit_nonneg _ _) 24
      (fun p hp => cutBonds_mono (cutBelow_mono (i + 1) (hsub p hp)))
      (fun q _ => card_filter_mem_le hij hj hL P hlt _ (fun q => q.1) (fun p q hq => by
        simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hq
        exact hq.1) q)
    simpa using this
  simp only [cutChainEnergy, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ p ∈ P, ∑ i ∈ Finset.range j, ∑ c ∈ cutBonds (cutBelow (i + 1) (plaquetteCorners p)),
      blockFit (U i) (U (i + 1)) c ≤
      24 * ∑ i ∈ Finset.range j, ∑ c ∈ cutBonds (cutBelow (i + 1) X), blockFit (U i) (U (i + 1)) c := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum h1
  have h3 := mul_le_mul_of_nonneg_left h2 ha
  have h0' : ∑ p ∈ P, ∑ q ∈ cutPlaquettes (cutBelow 0 (plaquetteCorners p)), plaquetteEnergy (U 0) q ≤
      24 * ∑ q ∈ cutPlaquettes (cutBelow 0 X), plaquetteEnergy (U 0) q := by simpa using h0
  nlinarith
theorem cornerDefectBound_of_chainCoercivity (hK : ChainCoercivity) : CornerDefectBound := by
  obtain ⟨cK, hc0, hc1, L₀, hK⟩ := hK
  refine ⟨cK, hc0, hc1, L₀, fun a L ha hL hL₀ F hF hamb j hj => ?_⟩
  have hoddF : Odd F.blockSide := hF ▸ hL
  have one : ∀ (p : F.Site j × Fin 4 × Fin 4) (U : F.FieldChain), p.2.1 < p.2.2 →
      cutChainEnergy a j (plaquetteCorners p) U < cK * (L : ℝ) ^ (-4 : ℤ) →
      plaquetteDefect (U j) p ^ 2 ≤ cutChainEnergy a j (plaquetteCorners p) U / cK := by
    intro p U hlt hE
    have h := (hK a L ha hL hL₀ F hF hamb j hj).1 p U hlt
    rw [le_div_iff₀ hc0]
    rcases min_cases (plaquetteDefect (U j) p ^ 2) ((L : ℝ) ^ (-4 : ℤ)) with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e] at h
      linarith
    · rw [e] at h
      linarith
  refine ⟨one, fun X P U hP => sum_cutChainEnergy_corners_le (by linarith) hj hoddF X P U hP,
    fun X P U hP hsm => ?_⟩
  have hsum : ∑ p ∈ P, plaquetteDefect (U j) p ^ 2 ≤
      ∑ p ∈ P, cutChainEnergy a j (plaquetteCorners p) U / cK := by
    refine Finset.sum_le_sum fun p hp => one p U ?_ (hsm p hp)
    have := hP hp
    simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at this
    exact this.2.1
  refine hsum.trans ?_
  rw [← Finset.sum_div, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (sum_cutChainEnergy_corners_le (by linarith) hj hoddF X P U hP) hc0.le
end YangMills.Construction.CornerCounting
end
