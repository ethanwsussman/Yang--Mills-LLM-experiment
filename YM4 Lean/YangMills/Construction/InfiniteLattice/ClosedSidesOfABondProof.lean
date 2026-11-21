import YangMills.Construction.InfiniteLattice.ClosedSidesOfABond
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.LatticeConventions.LinkHalfSpaces
open YangMills.Construction.InfiniteLattice (Link GaugeField IsBoundedObservable LatticePoint
  localRegionObservables boundedRegionObservables linksWithin regionSigma)
theorem hyperplane_mem_carrier_iff (Q : NormalHyperplane) (x : Point) :
    x ∈ Q.carrier ↔ x ∈ Q.upperHalfSpace ∧ x ∈ Q.lowerHalfSpace := by
  constructor
  · intro hx
    have hx' : euclidDot Q.normal x = Q.level := hx
    exact ⟨hx'.ge, hx'.le⟩
  · rintro ⟨hu, hl⟩
    show euclidDot Q.normal x = Q.level
    exact le_antisymm hl hu
theorem euclidDot_basisVector (μ : Direction) (x : Point) : euclidDot (basisVector μ) x = x μ := by
  simp [euclidDot, basisVector, Pi.single_apply]
theorem exists_coord_eq_mul {a : ℝ} (x : LatticePoint a) (μ : Direction) :
    ∃ k : ℤ, (x : Point) μ = (k : ℝ) * a := by
  obtain ⟨k, hk⟩ := x.2
  exact ⟨k μ, hk μ⟩
theorem coord_ne_half_odd (a : Spacing) (x : LatticePoint (a : ℝ)) (μ : Direction) (q : ℤ) :
    (x : Point) μ ≠ (q : ℝ) * (a : ℝ) + (a : ℝ) / 2 := by
  obtain ⟨k, hk⟩ := exists_coord_eq_mul x μ
  intro hx
  rw [hk] at hx
  have ha : (a : ℝ) ≠ 0 := a.2.ne'
  have h₁ : ((2 * k : ℤ) : ℝ) * (a : ℝ) = ((2 * q + 1 : ℤ) : ℝ) * (a : ℝ) := by
    push_cast
    linarith
  have h₂ : (2 * k : ℤ) = 2 * q + 1 := by
    exact_mod_cast mul_right_cancel₀ ha h₁
  omega
theorem neg_half_le_coord_iff (a : Spacing) (x : LatticePoint (a : ℝ)) (μ : Direction) :
    -((a : ℝ) / 2) ≤ (x : Point) μ ↔ 0 ≤ (x : Point) μ := by
  have ha : 0 < (a : ℝ) := a.2
  obtain ⟨k, hk⟩ := exists_coord_eq_mul x μ
  constructor
  · intro hx
    rw [hk] at hx ⊢
    by_contra hc
    have hk' : k < 0 := by
      by_contra hp
      exact hc (mul_nonneg (by exact_mod_cast not_lt.mp hp) ha.le)
    have h₁ : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    nlinarith
  · intro hx
    linarith
theorem linkInBothHalvesIffInPlane_holds (a : Spacing) (Q : NormalHyperplane) :
    LinkInBothHalvesIffInPlane a Q := by
  intro b
  constructor
  · rintro ⟨hi, ht⟩
    have hi' := (hyperplane_mem_carrier_iff Q _).mp hi
    have ht' := (hyperplane_mem_carrier_iff Q _).mp ht
    exact ⟨⟨hi'.1, ht'.1⟩, ⟨hi'.2, ht'.2⟩⟩
  · rintro ⟨⟨hi, ht⟩, ⟨hi', ht'⟩⟩
    exact ⟨(hyperplane_mem_carrier_iff Q _).mpr ⟨hi, hi'⟩, (hyperplane_mem_carrier_iff Q _).mpr ⟨ht, ht'⟩⟩
theorem mem_upperHalfSpace_axial (μ : Direction) (c : ℝ) (x : Point) :
    x ∈ (NormalHyperplane.axial μ c).upperHalfSpace ↔ c ≤ x μ := by
  show c ≤ euclidDot (basisVector μ) x ↔ _
  rw [euclidDot_basisVector]
theorem mem_lowerHalfSpace_axial (μ : Direction) (c : ℝ) (x : Point) :
    x ∈ (NormalHyperplane.axial μ c).lowerHalfSpace ↔ x μ ≤ c := by
  show euclidDot (basisVector μ) x ≤ c ↔ _
  rw [euclidDot_basisVector]
theorem crossingLinksInNeitherHalf_holds (a : Spacing) (μ : Direction) (c : ℝ) :
    CrossingLinksInNeitherHalf a μ c := by
  intro b hb
  constructor
  · rintro ⟨hi, ht⟩
    rw [mem_upperHalfSpace_axial] at hi ht
    rcases hb with ⟨hlt, _⟩ | ⟨hlt, _⟩
    · exact absurd hi (not_le.mpr hlt)
    · exact absurd ht (not_le.mpr hlt)
  · rintro ⟨hi, ht⟩
    rw [mem_lowerHalfSpace_axial] at hi ht
    rcases hb with ⟨_, hlt⟩ | ⟨_, hlt⟩
    · exact absurd ht (not_le.mpr hlt)
    · exact absurd hi (not_le.mpr hlt)
theorem noPointOnPlane_holds (a : Spacing) (μ : Direction) (c : ℝ)
    (hm : (NormalHyperplane.axial μ c).IsEdgeMirror (a : ℝ)) :
    NoPointOnPlane a μ c := by
  obtain ⟨_, _, q, hq⟩ := hm
  intro x hx
  have hx' : euclidDot (basisVector μ) (x : Point) = c := hx
  rw [euclidDot_basisVector] at hx'
  have hq' : c = (q : ℝ) * (a : ℝ) + (a : ℝ) / 2 := hq
  exact coord_ne_half_odd a x μ q (hx'.trans hq')
theorem halfSpaceLocalObservablesEq_holds (a : Spacing) (μ : Direction) :
    HalfSpaceLocalObservablesEq a μ := by
  have hl : ∀ R : Set Point,
      (linksWithin ({x : Point | -((a : ℝ) / 2) ≤ x μ} ∩ R) : Set (Link (a : ℝ))) =
        linksWithin ({x : Point | 0 ≤ x μ} ∩ R) := by
    intro R
    ext b
    simp only [linksWithin, Set.mem_ofPred_eq, Set.mem_inter_iff, neg_half_le_coord_iff]
  have ho : ∀ R : Set Point,
      boundedRegionObservables (a : ℝ) ({x : Point | -((a : ℝ) / 2) ≤ x μ} ∩ R) =
        boundedRegionObservables (a : ℝ) ({x : Point | 0 ≤ x μ} ∩ R) := by
    intro R
    have hs : (regionSigma ({x : Point | -((a : ℝ) / 2) ≤ x μ} ∩ R) :
        MeasurableSpace (GaugeField (a : ℝ))) = regionSigma ({x : Point | 0 ≤ x μ} ∩ R) := by
      simp only [regionSigma, hl R]
    ext F
    show IsBoundedObservable F ∧ Measurable[regionSigma _] F ↔
      IsBoundedObservable F ∧ Measurable[regionSigma _] F
    rw [hs]
  simp only [HalfSpaceLocalObservablesEq, localRegionObservables, ho]
theorem statement_holds : Statement := by
  intro a
  exact ⟨fun Q _ => linkInBothHalvesIffInPlane_holds a Q,
    fun μ c hm => ⟨crossingLinksInNeitherHalf_holds a μ c, noPointOnPlane_holds a μ c hm⟩,
    fun μ => halfSpaceLocalObservablesEq_holds a μ⟩
end YangMills.Construction.LatticeConventions.LinkHalfSpaces
