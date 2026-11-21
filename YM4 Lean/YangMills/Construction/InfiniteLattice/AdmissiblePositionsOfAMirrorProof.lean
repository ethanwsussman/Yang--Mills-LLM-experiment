import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrorsProof
import YangMills.Construction.InfiniteLattice.AdmissiblePositionsOfAMirror
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivityProof
import YangMills.Construction.InfiniteLattice.ReflectionsAndLatticeMirrorsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.MirrorReflection
open InfiniteLattice (latticeSubgroup)
open LatticeConventions (Direction NormalHyperplane IsAxialNormal IsFaceDiagonalNormal Point
  euclidDot euclidNorm euclidNorm_sq_eq_dotProduct basisVector)
theorem euclidDot_add_right (n x y : Point) : euclidDot n (x + y) = euclidDot n x + euclidDot n y := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.euclidDot_add <;> assumption
theorem euclidDot_sub_right (n x y : Point) : euclidDot n (x - y) = euclidDot n x - euclidDot n y := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_sub_right <;> assumption
theorem euclidDot_smul_right (t : ℝ) (n x : Point) : euclidDot n (t • x) = t * euclidDot n x := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_smul_right <;> assumption
theorem basisVector_apply_self (i : Direction) : basisVector i i = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_self <;> assumption
theorem basisVector_apply_of_ne {i j : Direction} (h : j ≠ i) : basisVector i j = 0 := by
  simp [basisVector, h]
theorem euclidDot_self_of_axial {n : Point} (h : IsAxialNormal n) : euclidDot n n = 1 := by apply _root_.YangMills.Construction.LatticeConventions.LatticeMirrorsAndReflectionPositivity.euclidDot_self_of_axial <;> assumption
theorem euclidDot_self_of_faceDiagonal {n : Point} (h : IsFaceDiagonalNormal n) :
    euclidDot n n = 2 := by apply _root_.YangMills.Construction.LatticeConventions.LatticeMirrorsAndReflectionPositivity.euclidDot_self_of_faceDiagonal <;> assumption
theorem normal_dot_self_ne_zero (H : NormalHyperplane) : euclidDot H.normal H.normal ≠ 0 := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_normal_self_ne_zero <;> assumption
theorem reflect_eq (H : NormalHyperplane) (x : Point) :
    H.reflect x =
      x - (2 * (euclidDot H.normal x - H.level) / euclidDot H.normal H.normal) • H.normal := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReflections.reflect_apply <;> assumption
theorem signedHeight_reflect (H : NormalHyperplane) (x : Point) :
    euclidDot H.normal (H.reflect x) - H.level = -(euclidDot H.normal x - H.level) := by
  have hN := normal_dot_self_ne_zero H
  rw [reflect_eq, euclidDot_sub_right, euclidDot_smul_right]
  field_simp
  ring
theorem reflect_reflect (H : NormalHyperplane) (x : Point) :
    H.reflect (H.reflect x) = x := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReflections.reflect_reflect <;> assumption
theorem euclidNorm_reflect_sub (H : NormalHyperplane) (x y : Point) :
    euclidNorm (H.reflect x - H.reflect y) = euclidNorm (x - y) := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReflections.euclidNorm_reflect_sub <;> assumption
theorem reflect_add_smul_normal (H : NormalHyperplane) (x : Point) (s : ℝ) :
    H.reflect (x + s • H.normal) = H.reflect x - s • H.normal := by
  have hN := normal_dot_self_ne_zero H
  rw [reflect_eq, reflect_eq, euclidDot_add_right, euclidDot_smul_right]
  have : 2 * (euclidDot H.normal x + s * euclidDot H.normal H.normal - H.level) /
      euclidDot H.normal H.normal =
      2 * (euclidDot H.normal x - H.level) / euclidDot H.normal H.normal + 2 * s := by
    field_simp
    ring
  have h₂ : (2 * s) • H.normal = s • H.normal + s • H.normal := by rw [two_mul, add_smul]
  rw [this, add_smul, h₂]
  abel
theorem image_eq_of_self_inverse {f : Point → Point} (hf : ∀ x, f (f x) = x) {A B : Set Point}
    (hAB : ∀ x ∈ A, f x ∈ B) (hBA : ∀ x ∈ B, f x ∈ A) : f '' A = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hAB x hx
  · exact fun hy => ⟨f y, hBA y hy, hf y⟩
theorem reflect_mem_lowerHalfSpace (H : NormalHyperplane) {x : Point}
    (hx : x ∈ H.upperHalfSpace) : H.reflect x ∈ H.lowerHalfSpace := by
  have h := signedHeight_reflect H x
  have hx' : H.level ≤ euclidDot H.normal x := hx
  change euclidDot H.normal (H.reflect x) ≤ H.level
  linarith
theorem reflect_mem_upperHalfSpace (H : NormalHyperplane) {x : Point}
    (hx : x ∈ H.lowerHalfSpace) : H.reflect x ∈ H.upperHalfSpace := by
  have h := signedHeight_reflect H x
  have hx' : euclidDot H.normal x ≤ H.level := hx
  change H.level ≤ euclidDot H.normal (H.reflect x)
  linarith
theorem reflect_mem_latticeSubgroup (H : NormalHyperplane) {a : ℝ} (m : Fin 4 → ℤ)
    (hm : ∀ j, H.normal j = (m j : ℝ)) (e d : ℤ)
    (he : 2 / euclidDot H.normal H.normal = (e : ℝ))
    (hd : 2 * H.level / euclidDot H.normal H.normal = (d : ℝ) * a) {x : Point}
    (hx : x ∈ latticeSubgroup a) : H.reflect x ∈ latticeSubgroup a := by
  obtain ⟨k, hk⟩ := hx
  have hdot : euclidDot H.normal x = ((∑ j, m j * k j : ℤ) : ℝ) * a := by
    simp only [euclidDot, hm, hk]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨fun j => k j - (e * (∑ j, m j * k j) - d) * m j, fun j => ?_⟩
  have hcoef : 2 * (euclidDot H.normal x - H.level) / euclidDot H.normal H.normal =
      ((e : ℝ) * ((∑ j, m j * k j : ℤ) : ℝ) - (d : ℝ)) * a := by
    rw [mul_sub, sub_div, hd, ← he, hdot]
    ring
  rw [reflect_eq, hcoef]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hk, hm]
  push_cast
  ring
theorem reflect_zero (H : NormalHyperplane) :
    H.reflect 0 = (2 * H.level / euclidDot H.normal H.normal) • H.normal := by
  have h0 : euclidDot H.normal 0 = 0 := by simp [euclidDot]
  rw [reflect_eq, h0, zero_sub, zero_sub, mul_neg, neg_div, neg_smul, neg_neg]
theorem reflect_image_latticeSubgroup (H : NormalHyperplane) {a : ℝ}
    (h : ∀ x ∈ (latticeSubgroup a : Set Point), H.reflect x ∈ (latticeSubgroup a : Set Point)) :
    H.reflect '' (latticeSubgroup a : Set Point) = (latticeSubgroup a : Set Point) :=
  image_eq_of_self_inverse (reflect_reflect H) h h
theorem reflect_zero_mem_of_image_eq (H : NormalHyperplane) {a : ℝ}
    (h : H.reflect '' (latticeSubgroup a : Set Point) = (latticeSubgroup a : Set Point)) :
    (2 * H.level / euclidDot H.normal H.normal) • H.normal ∈ latticeSubgroup a := by
  rw [← reflect_zero]
  have h0 : H.reflect 0 ∈ H.reflect '' (latticeSubgroup a : Set Point) :=
    ⟨0, (latticeSubgroup a).zero_mem, rfl⟩
  rw [h] at h0
  exact h0
theorem image_eq_iff_of_axial (H : NormalHyperplane) {a : ℝ} (hn : IsAxialNormal H.normal) :
    H.reflect '' (latticeSubgroup a : Set Point) = (latticeSubgroup a : Set Point) ↔
      ∃ q : ℤ, H.level = (q : ℝ) * (a / 2) := by
  have hN := euclidDot_self_of_axial hn
  obtain ⟨i, hi⟩ := id hn
  constructor
  · intro h
    obtain ⟨k, hk⟩ := reflect_zero_mem_of_image_eq H h
    refine ⟨k i, ?_⟩
    have hone : H.normal i = 1 := by rw [hi, basisVector_apply_self]
    have := hk i
    rw [Pi.smul_apply, smul_eq_mul, hN, hone] at this
    linarith
  · rintro ⟨q, hq⟩
    refine reflect_image_latticeSubgroup H fun x hx => ?_
    refine reflect_mem_latticeSubgroup H (fun j => if j = i then 1 else 0) (fun j => ?_) 2 q ?_ ?_ hx
    · rw [hi]
      by_cases h : j = i
      · simp [h, basisVector_apply_self]
      · simp [h, basisVector_apply_of_ne h]
    · rw [hN]; norm_num
    · rw [hN, hq]; ring
theorem image_eq_iff_of_faceDiagonal (H : NormalHyperplane) {a : ℝ}
    (hn : IsFaceDiagonalNormal H.normal) :
    H.reflect '' (latticeSubgroup a : Set Point) = (latticeSubgroup a : Set Point) ↔
      ∃ q : ℤ, H.level = (q : ℝ) * a := by
  have hN := euclidDot_self_of_faceDiagonal hn
  obtain ⟨i, j, hij, hform⟩ := id hn
  have hone : H.normal i = 1 := by
    rcases hform with h | h <;> rw [h]
    · simp [basisVector_apply_self, basisVector_apply_of_ne hij]
    · simp [basisVector_apply_self, basisVector_apply_of_ne hij]
  have hint : ∃ m : Fin 4 → ℤ, ∀ l, H.normal l = (m l : ℝ) := by
    rcases hform with h | h
    · refine ⟨fun l => (if l = i then 1 else 0) + (if l = j then 1 else 0), fun l => ?_⟩
      rw [h]
      simp only [Pi.add_apply, basisVector, Pi.single_apply]
      push_cast
      rfl
    · refine ⟨fun l => (if l = i then 1 else 0) - (if l = j then 1 else 0), fun l => ?_⟩
      rw [h]
      simp only [Pi.sub_apply, basisVector, Pi.single_apply]
      push_cast
      rfl
  constructor
  · intro h
    obtain ⟨k, hk⟩ := reflect_zero_mem_of_image_eq H h
    refine ⟨k i, ?_⟩
    have := hk i
    rw [Pi.smul_apply, smul_eq_mul, hN, hone] at this
    linarith
  · rintro ⟨q, hq⟩
    obtain ⟨m, hm⟩ := hint
    refine reflect_image_latticeSubgroup H fun x hx => ?_
    refine reflect_mem_latticeSubgroup H m hm 1 q ?_ ?_ hx
    · rw [hN]; norm_num
    · rw [hN, hq]; ring
theorem mirrorPositionsAndReflectionRules_holds : MirrorPositionsAndReflectionRules := by
  intro a _ H
  refine ⟨image_eq_iff_of_axial H, image_eq_iff_of_faceDiagonal H, euclidNorm_reflect_sub H,
    funext (reflect_reflect H), signedHeight_reflect H, ?_, ?_, reflect_add_smul_normal H⟩
  · exact image_eq_of_self_inverse (reflect_reflect H) (fun x => reflect_mem_lowerHalfSpace H)
      (fun x => reflect_mem_upperHalfSpace H)
  · exact image_eq_of_self_inverse (reflect_reflect H) (fun x => reflect_mem_upperHalfSpace H)
      (fun x => reflect_mem_lowerHalfSpace H)
end YangMills.Construction.GibbsAtFixedSpacing.MirrorReflection
end
