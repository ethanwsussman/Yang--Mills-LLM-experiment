import YangMills.Construction.ColdChainAtEveryLevel.ComplexChain
import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAnIsometryProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ComplexContours
open BlockAverages ComplexifiedQuaternions LatticePaths LatticeFractionalIntegration
variable {F : BlockFrame}
theorem ofUnit_inv_mul_cancel_left (g : UnitQuaternion) (e : ComplexQuat) : ofUnit g⁻¹ * (ofUnit g * e) = e := by
  rw [← mul_assoc, ofUnit_inv_mul, one_mul]
theorem ofUnit_mul_inv_cancel_left (g : UnitQuaternion) (e : ComplexQuat) : ofUnit g * (ofUnit g⁻¹ * e) = e := by
  rw [← mul_assoc, ofUnit_mul_inv, one_mul]
theorem ofUnit_injective : Function.Injective ofUnit := by
  intro g h e
  have h1 : ofQuat ((g : ℍ[ℝ]) - h) = 0 := by
    have h2 : ofQuat ((g : ℍ[ℝ]) - h) = ofQuat (g : ℍ[ℝ]) - ofQuat (h : ℍ[ℝ]) := by
      have := ofQuat_add ((g : ℍ[ℝ]) - h) (h : ℍ[ℝ])
      rw [sub_add_cancel] at this
      rw [this, add_sub_cancel_right]
    rw [h2]
    exact sub_eq_zero.2 e
  have h3 := norm_ofQuat ((g : ℍ[ℝ]) - h)
  rw [h1, norm_zero] at h3
  exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h3.symm))
theorem conjByUnit_one (g : UnitQuaternion) : conjByUnit g 1 = 1 := by
  rw [conjByUnit, mul_one, ofUnit_mul_inv]
theorem conjByUnit_sub (g : UnitQuaternion) (a b : ComplexQuat) :
    conjByUnit g (a - b) = conjByUnit g a - conjByUnit g b := by
  simp only [conjByUnit, mul_sub, sub_mul]
theorem conjByUnit_add (g : UnitQuaternion) (a b : ComplexQuat) :
    conjByUnit g (a + b) = conjByUnit g a + conjByUnit g b := by
  simp only [conjByUnit, mul_add, add_mul]
theorem conjByUnit_conjByUnit (g h : UnitQuaternion) (e : ComplexQuat) :
    conjByUnit g (conjByUnit h e) = conjByUnit (g * h) e := by
  simp only [conjByUnit, mul_inv_rev, ofUnit_mul, mul_assoc]
theorem conjByUnit_smul (g : UnitQuaternion) (z : ℂ) (e : ComplexQuat) :
    conjByUnit g (z • e) = z • conjByUnit g e := by
  simp only [conjByUnit, mul_smul_comm, smul_mul_assoc]
theorem conjByUnit_sum {ι : Type} (g : UnitQuaternion) (s : Finset ι) (f : ι → ComplexQuat) :
    conjByUnit g (∑ i ∈ s, f i) = ∑ i ∈ s, conjByUnit g (f i) := by
  simp only [conjByUnit, Finset.mul_sum, Finset.sum_mul]
theorem conjByUnit_one_left (e : ComplexQuat) : conjByUnit 1 e = e := by
  simp [conjByUnit, ofUnit_one]
theorem det_conjByUnit (g : UnitQuaternion) (e : ComplexQuat) : (conjByUnit g e).det = e.det := by
  rw [conjByUnit, Matrix.det_mul, Matrix.det_mul, det_ofUnit, det_ofUnit]
  simp
theorem trace_conjByUnit (g : UnitQuaternion) (e : ComplexQuat) : (conjByUnit g e).trace = e.trace := by
  rw [conjByUnit, Matrix.trace_mul_comm, ← mul_assoc, ofUnit_inv_mul, one_mul]
theorem adjugate_one_complexQuat : Matrix.adjugate (1 : ComplexQuat) = 1 := Matrix.adjugate_one
theorem det_adjugate_complexQuat (a : ComplexQuat) : (Matrix.adjugate a).det = a.det := by
  simp [Matrix.adjugate_fin_two, Matrix.det_fin_two]
  ring
theorem adjugate_purePart (a : ComplexQuat) : Matrix.adjugate (purePart a) = - purePart a := by
  rw [purePart, adjugate_map_smul, adjugate_map_sub, adjugate_adjugate_eq_self, ← smul_neg, neg_sub]
section Products
theorem norm_mul_sub_one_le_complexQuat (a b : ComplexQuat) :
    ‖a * b - 1‖ ≤ (1 + ‖a - 1‖) * (1 + ‖b - 1‖) - 1 := by
  have h : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [h]
  have h1 := norm_add_le ((a - 1) + (b - 1)) ((a - 1) * (b - 1))
  have h2 := norm_add_le (a - 1) (b - 1)
  have h3 := norm_mul_le (a - 1) (b - 1)
  nlinarith
theorem one_add_pow_sub_one_le_two_mul {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (hm : 2 * (m : ℝ) * t ≤ 1) :
    (1 + t) ^ m - 1 ≤ 2 * (m : ℝ) * t := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : 2 * (m : ℝ) * t ≤ 1 := by
      push_cast at hm
      nlinarith
    have h := ih hm'
    have h2 : (1 + t) ^ (m + 1) = (1 + t) ^ m * (1 + t) := pow_succ _ _
    rw [h2]
    push_cast
    have h3 : (1 + t) ^ m ≤ 1 + 2 * (m : ℝ) * t := by linarith
    have h4 : (1 + t) ^ m * (1 + t) ≤ (1 + 2 * (m : ℝ) * t) * (1 + t) :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    nlinarith
end Products
section Paths
variable {j : ℕ}
def linkDeviation (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) (i : Fin 4) : ComplexQuat :=
  X x i * ofUnit (R x i)⁻¹ - 1
theorem field_eq_one_add_linkDeviation_mul (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) (i : Fin 4) :
    X x i = (1 + linkDeviation X R x i) * ofUnit (R x i) := by
  rw [linkDeviation, add_sub_cancel, mul_assoc, ofUnit_inv_mul, mul_one]
def crossedBond (x : F.Site j) (st : PathStep) : F.Site j := if st.2 then x else x - unitStep j st.1
def StepNearReal (X : F.ComplexField j) (R : F.GaugeField j) (t : ℝ) (x : F.Site j) (st : PathStep) : Prop :=
  ‖linkDeviation X R (crossedBond x st) st.1‖ ≤ t ∧ (X (crossedBond x st) st.1).det = 1
def PathNearReal (X : F.ComplexField j) (R : F.GaugeField j) (t : ℝ) : F.Site j → List PathStep → Prop
  | _, [] => True
  | x, st :: r => StepNearReal X R t x st ∧ PathNearReal X R t (x + stepDisplacement j st) r
def relativeHolonomy (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) (l : List PathStep) : ComplexQuat :=
  complexPathHolonomy X x l * ofUnit (pathHolonomy R x l)⁻¹
def relativeLinkValue (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) (st : PathStep) : ComplexQuat :=
  complexLinkValue X x st * ofUnit (linkValue R x st)⁻¹
theorem relativeHolonomy_nil (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) :
    relativeHolonomy X R x [] = 1 := by
  simp [relativeHolonomy, complexPathHolonomy, pathHolonomy, ofUnit_one]
theorem relativeHolonomy_cons (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) (st : PathStep)
    (r : List PathStep) :
    relativeHolonomy X R x (st :: r) =
      relativeLinkValue X R x st * conjByUnit (linkValue R x st) (relativeHolonomy X R (x + stepDisplacement j st) r) := by
  simp only [relativeHolonomy, relativeLinkValue, complexPathHolonomy, pathHolonomy, conjByUnit, mul_inv_rev,
    ofUnit_mul, mul_assoc, ofUnit_inv_mul_cancel_left]
theorem relativeLinkValue_of_forward (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) {st : PathStep}
    (h : st.2 = true) : relativeLinkValue X R x st = 1 + linkDeviation X R x st.1 := by
  simp [relativeLinkValue, complexLinkValue, linkValue, h, linkDeviation]
theorem relativeLinkValue_of_backward (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) {st : PathStep}
    (h : st.2 = false) :
    relativeLinkValue X R x st = 1 + conjByUnit (R (x - unitStep j st.1) st.1)⁻¹
      (Matrix.adjugate (linkDeviation X R (x - unitStep j st.1) st.1)) := by
  have e : X (x - unitStep j st.1) st.1 =
      (1 + linkDeviation X R (x - unitStep j st.1) st.1) * ofUnit (R (x - unitStep j st.1) st.1) :=
    field_eq_one_add_linkDeviation_mul X R _ _
  simp only [relativeLinkValue, complexLinkValue, linkValue, h, Bool.false_eq_true, if_false, inv_inv]
  rw [e, Matrix.adjugate_mul_distrib, adjugate_map_add, adjugate_one_complexQuat, ← ofUnit_inv, conjByUnit]
  simp only [inv_inv, mul_add, add_mul, mul_one, mul_assoc, ofUnit_inv_mul]
theorem norm_relativeLinkValue_sub_one_le {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} {x : F.Site j}
    {st : PathStep} (h : StepNearReal X R t x st) : ‖relativeLinkValue X R x st - 1‖ ≤ t := by
  rcases hs : st.2 with _ | _
  · have h1 := h.1
    simp only [crossedBond, hs, Bool.false_eq_true, if_false] at h1
    rw [relativeLinkValue_of_backward X R x hs, add_sub_cancel_left, norm_conjByUnit, norm_adjugate]
    exact h1
  · have h1 := h.1
    simp only [crossedBond, hs, if_true] at h1
    rw [relativeLinkValue_of_forward X R x hs, add_sub_cancel_left]
    exact h1
theorem det_relativeLinkValue {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} {x : F.Site j} {st : PathStep}
    (h : StepNearReal X R t x st) : (relativeLinkValue X R x st).det = 1 := by
  have h1 := h.2
  rcases hs : st.2 with _ | _
  · simp only [crossedBond, hs, Bool.false_eq_true, if_false] at h1
    simp only [relativeLinkValue, complexLinkValue, hs, Bool.false_eq_true, if_false, Matrix.det_mul, det_ofUnit,
      mul_one, det_adjugate_complexQuat, h1]
  · simp only [crossedBond, hs, if_true] at h1
    simp only [relativeLinkValue, complexLinkValue, hs, if_true, Matrix.det_mul, det_ofUnit, mul_one, h1]
theorem det_relativeHolonomy {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} {x : F.Site j}
    {l : List PathStep} (h : PathNearReal X R t x l) : (relativeHolonomy X R x l).det = 1 := by
  induction l generalizing x with
  | nil => simp [relativeHolonomy_nil]
  | cons st r ih =>
    rw [relativeHolonomy_cons, Matrix.det_mul, det_relativeLinkValue h.1, det_conjByUnit, ih h.2, one_mul]
theorem norm_relativeHolonomy_sub_one_le {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} (ht : 0 ≤ t)
    {x : F.Site j} {l : List PathStep} (h : PathNearReal X R t x l) :
    ‖relativeHolonomy X R x l - 1‖ ≤ (1 + t) ^ l.length - 1 := by
  induction l generalizing x with
  | nil => simp [relativeHolonomy_nil]
  | cons st r ih =>
    rw [relativeHolonomy_cons]
    have h1 := norm_relativeLinkValue_sub_one_le h.1
    have h2 := ih h.2
    have h3 : conjByUnit (linkValue R x st) (relativeHolonomy X R (x + stepDisplacement j st) r) - 1 =
        conjByUnit (linkValue R x st) (relativeHolonomy X R (x + stepDisplacement j st) r - 1) := by
      rw [conjByUnit_sub, conjByUnit_one]
    have h4 := norm_mul_sub_one_le_complexQuat (relativeLinkValue X R x st)
      (conjByUnit (linkValue R x st) (relativeHolonomy X R (x + stepDisplacement j st) r))
    rw [h3, norm_conjByUnit] at h4
    refine h4.trans ?_
    rw [List.length_cons, pow_succ]
    have h6 : 1 + ‖relativeHolonomy X R (x + stepDisplacement j st) r - 1‖ ≤ (1 + t) ^ r.length := by linarith
    have h7 := mul_le_mul (by linarith : 1 + ‖relativeLinkValue X R x st - 1‖ ≤ 1 + t) h6 (by positivity)
      (by linarith)
    nlinarith
end Paths
section Holonomies
variable {j : ℕ}
theorem siteOfCoords_flatStep (st : PathStep) :
    siteOfCoords (F := F) j (FlatPairing.stepDisplacement st) = stepDisplacement j st := by apply _root_.YangMills.Construction.ReferenceBounds.siteOfCoords_stepDisplacement <;> assumption
theorem add_stepDisplacement_add_siteOfCoords (x : F.Site j) (st : PathStep) (r : List PathStep) :
    x + stepDisplacement j st + siteOfCoords j (endpoint 0 r) = x + siteOfCoords j (endpoint 0 (st :: r)) := by apply _root_.YangMills.Construction.BlockAverages.ContourMean.add_stepDisplacement_add_siteOfCoords <;> assumption
theorem complexPathHolonomy_append (X : F.ComplexField j) (x : F.Site j) (l l' : List PathStep) :
    complexPathHolonomy X x (l ++ l') =
      complexPathHolonomy X x l * complexPathHolonomy X (x + siteOfCoords j (endpoint 0 l)) l' := by
  induction l generalizing x with
  | nil => simp [complexPathHolonomy, endpoint, siteOfCoords_zero]
  | cons st r ih =>
    simp only [List.cons_append, complexPathHolonomy]
    rw [ih, add_stepDisplacement_add_siteOfCoords, mul_assoc]
theorem pathHolonomy_append (X : F.GaugeField j) (x : F.Site j) (l l' : List PathStep) :
    pathHolonomy X x (l ++ l') = pathHolonomy X x l * pathHolonomy X (x + siteOfCoords j (endpoint 0 l)) l' := by
  apply ofUnit_injective
  rw [ofUnit_mul, ← complexPathHolonomy_complexify, ← complexPathHolonomy_complexify,
    ← complexPathHolonomy_complexify, complexPathHolonomy_append]
theorem endpoint_zero_reversePath (l : List PathStep) : endpoint 0 (reversePath l) = - endpoint 0 l := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.endpoint_zero_reversePath <;> assumption
theorem complexLinkValue_reverse (X : F.ComplexField j) (x : F.Site j) (st : PathStep) :
    complexLinkValue X (x + stepDisplacement j st) (st.1, !st.2) = Matrix.adjugate (complexLinkValue X x st) := by
  rcases hs : st.2 with _ | _
  · simp [complexLinkValue, stepDisplacement, hs, adjugate_adjugate_eq_self, sub_eq_add_neg]
  · simp [complexLinkValue, stepDisplacement, hs]
theorem complexPathHolonomy_reversePath (X : F.ComplexField j) (x : F.Site j) (l : List PathStep) :
    complexPathHolonomy X (x + siteOfCoords j (endpoint 0 l)) (reversePath l) =
      Matrix.adjugate (complexPathHolonomy X x l) := by
  induction l generalizing x with
  | nil => simp [complexPathHolonomy, endpoint, siteOfCoords_zero, reversePath]
  | cons st r ih =>
    have hr : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e1 : x + siteOfCoords j (endpoint 0 (st :: r)) + siteOfCoords j (endpoint 0 (reversePath r)) =
        x + stepDisplacement j st := by
      rw [endpoint_zero_reversePath, ← add_stepDisplacement_add_siteOfCoords, siteOfCoords_neg]
      abel
    rw [hr, complexPathHolonomy_append, e1, ← add_stepDisplacement_add_siteOfCoords, ih]
    simp only [complexPathHolonomy, mul_one, complexLinkValue_reverse, Matrix.adjugate_mul_distrib]
def straightLineSum (X : F.ComplexField j) (R : F.GaugeField j) (x : F.Site j) (i : Fin 4) (r : ℕ) :
    ComplexQuat :=
  ∑ q ∈ Finset.range r, conjByUnit (pathHolonomy R x (List.replicate q (i, true)))
    (linkDeviation X R (x + (q : ℤ) • unitStep j i) i)
theorem norm_relativeHolonomy_straight_sub_le {X : F.ComplexField j} {R : F.GaugeField j} {t : ℝ} (ht : 0 ≤ t)
    (i : Fin 4) (r : ℕ) (x : F.Site j) (hp : PathNearReal X R t x (List.replicate r (i, true)))
    (hr : 2 * (r : ℝ) * t ≤ 1) :
    ‖relativeHolonomy X R x (List.replicate r (i, true)) - 1 - straightLineSum X R x i r‖ ≤
      (r : ℝ) ^ 2 * t ^ 2 := by
  induction r generalizing x with
  | zero => simp [relativeHolonomy_nil, straightLineSum]
  | succ r ih =>
    have hr' : 2 * (r : ℝ) * t ≤ 1 := by
      push_cast at hr
      nlinarith
    rw [List.replicate_succ] at hp
    have hstep := hp.1
    have hrest := hp.2
    have hg : ‖linkDeviation X R x i‖ ≤ t := by simpa [crossedBond] using hstep.1
    set e : F.Site j := stepDisplacement j (i, true) with he
    have he' : e = unitStep j i := by simp [he, stepDisplacement]
    have h1 := ih (x + e) hrest hr'
    have h2 := norm_relativeHolonomy_sub_one_le ht hrest
    rw [List.length_replicate] at h2
    have h3 := one_add_pow_sub_one_le_two_mul ht r hr'
    set Y' := relativeHolonomy X R (x + e) (List.replicate r (i, true)) with hY
    set s : UnitQuaternion := linkValue R x (i, true) with hs
    have hsum : straightLineSum X R x i (r + 1) =
        linkDeviation X R x i + conjByUnit s (straightLineSum X R (x + e) i r) := by
      simp only [straightLineSum]
      rw [Finset.sum_range_succ', conjByUnit_sum, add_comm]
      congr 1
      · simp [pathHolonomy, conjByUnit_one_left]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [conjByUnit_conjByUnit]
        have e2 : s * pathHolonomy R (x + e) (List.replicate q (i, true)) =
            pathHolonomy R x (List.replicate (q + 1) (i, true)) := by
          rw [List.replicate_succ]
          rfl
        have e3 : x + e + (q : ℤ) • unitStep j i = x + ((q + 1 : ℕ) : ℤ) • unitStep j i := by
          rw [he', add_assoc]
          congr 1
          push_cast
          rw [add_smul, one_smul]
          abel
        rw [e2, e3]
    have hcy : relativeHolonomy X R x (List.replicate (r + 1) (i, true)) =
        (1 + linkDeviation X R x i) * conjByUnit s Y' := by
      rw [List.replicate_succ, relativeHolonomy_cons, relativeLinkValue_of_forward X R x rfl]
    have hid : relativeHolonomy X R x (List.replicate (r + 1) (i, true)) - 1 - straightLineSum X R x i (r + 1) =
        conjByUnit s (Y' - 1 - straightLineSum X R (x + e) i r) + linkDeviation X R x i * conjByUnit s (Y' - 1) := by
      rw [hcy, hsum, conjByUnit_sub, conjByUnit_sub, conjByUnit_one]
      noncomm_ring
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    rw [norm_conjByUnit]
    have h4 := norm_mul_le (linkDeviation X R x i) (conjByUnit s (Y' - 1))
    rw [norm_conjByUnit] at h4
    have h5 : ‖linkDeviation X R x i‖ * ‖Y' - 1‖ ≤ t * (2 * r * t) :=
      mul_le_mul hg (h2.trans h3) (norm_nonneg _) ht
    push_cast
    nlinarith [sq_nonneg t]
end Holonomies
section Means
variable {E : Type} [AddCommMonoid E] [Module ℂ E]
def blockContourMean (F : BlockFrame) (f : Lattice4 → Equiv.Perm (Fin 4) → E) : E :=
  contourWeight F • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), f h π
theorem blockContourMean_add (f g : Lattice4 → Equiv.Perm (Fin 4) → E) :
    blockContourMean F (fun h π => f h π + g h π) = blockContourMean F f + blockContourMean F g := by
  simp only [blockContourMean, Finset.sum_add_distrib, smul_add]
theorem map_blockContourMean {E' : Type} [AddCommMonoid E'] [Module ℂ E'] (φ : E →ₗ[ℂ] E')
    (f : Lattice4 → Equiv.Perm (Fin 4) → E) :
    φ (blockContourMean F f) = blockContourMean F (fun h π => φ (f h π)) := by
  simp only [blockContourMean, map_smul, map_sum]
theorem contourWeight_mul_card (hodd : Odd F.blockSide) :
    contourWeight F * (((centredCube F.blockSide).card * 24 : ℕ) : ℂ) = 1 := by
  have hL : (F.blockSide : ℝ) ≠ 0 := by
    have := hodd.pos
    positivity
  rw [card_centredCube hodd, contourWeight]
  have : ((1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ) : ℂ) * (((F.blockSide ^ 4 * 24 : ℕ) : ℂ)) =
      (((1 / (24 * (F.blockSide : ℝ) ^ 4)) * ((F.blockSide ^ 4 * 24 : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this]
  have h2 : (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ((F.blockSide ^ 4 * 24 : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [h2]
  simp
theorem card_perm_fin_four : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  rfl
theorem blockContourMean_const (hodd : Odd F.blockSide) (e : E) : blockContourMean F (fun _ _ => e) = e := by
  simp only [blockContourMean, Finset.sum_const, Finset.card_univ, card_perm_fin_four]
  rw [← mul_nsmul', ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have := contourWeight_mul_card hodd
  rw [this, one_smul]
end Means
section NormMeans
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem blockContourMean_sub (f g : Lattice4 → Equiv.Perm (Fin 4) → E) :
    blockContourMean F (fun h π => f h π - g h π) = blockContourMean F f - blockContourMean F g := by
  simp only [blockContourMean, Finset.sum_sub_distrib, smul_sub]
theorem norm_blockContourMean_le (hodd : Odd F.blockSide) {f : Lattice4 → Equiv.Perm (Fin 4) → E} {b : ℝ}
    (hf : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖f h π‖ ≤ b) : ‖blockContourMean F f‖ ≤ b := by
  have hw : ‖contourWeight F‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
    rw [contourWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hL : (F.blockSide : ℝ) ≠ 0 := by
    have := hodd.pos
    positivity
  rw [blockContourMean, norm_smul, hw]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), f h π‖ ≤
      ((centredCube F.blockSide).card * 24 : ℝ) * b := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4), f h π‖ ≤ 24 * b := fun h hh => by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ b fun π _ => hf h hh π).trans ?_
      simp [Finset.card_univ, card_perm_fin_four]
    refine (Finset.sum_le_card_nsmul _ _ (24 * b) this).trans ?_
    simp
    linarith
  rw [card_centredCube hodd] at h1
  have h2 : 1 / (24 * (F.blockSide : ℝ) ^ 4) * (((F.blockSide ^ 4 : ℕ) : ℝ) * 24 * b) = b := by
    push_cast
    field_simp
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), f h π‖
      ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * (((F.blockSide ^ 4 : ℕ) : ℝ) * 24 * b) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = b := h2
end NormMeans
section Contours
variable {j : ℕ}
def transportedAverage (R : F.GaugeField j) (f : F.Site j → Fin 4 → ComplexQuat) (c : F.Site (j + 1) × Fin 4) :
    ComplexQuat :=
  blockContourMean F fun h π => ∑ r ∈ Finset.range F.blockSide,
    conjByUnit (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
      (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)
theorem complexPathHolonomy_bondContour (hj : j + 1 ≤ F.top) (X : F.ComplexField j) (c : F.Site (j + 1) × Fin 4)
    (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    complexPathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) =
      complexPathHolonomy X (refineSite c.1) (axisPath h π) *
        complexPathHolonomy X (refineSite c.1 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true)) *
        Matrix.adjugate (complexPathHolonomy X (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π)) := by
  have hend := (axisPath_spec h π).2
  have e1 : refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h =
      refineSite c.1 + siteOfCoords j (endpoint 0 (axisPath h π ++ List.replicate F.blockSide (c.2, true))) := by
    rw [endpoint_append, hend, endpoint_replicate, unitStep_eq, refineSite_add j hj, siteOfCoords_add]
    have : (fun i => (F.blockSide : ℤ) * basisVector c.2 i) =
        (F.blockSide : ℤ) • FlatPairing.stepDisplacement (c.2, true) := by
      funext i
      simp [FlatPairing.stepDisplacement]
    rw [this]
    abel
  have h2 := complexPathHolonomy_reversePath X (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π)
  rw [hend, e1] at h2
  unfold bondContour
  rw [complexPathHolonomy_append, h2, complexPathHolonomy_append, hend]
theorem complexPathHolonomy_bondContour_mul_inv (hj : j + 1 ≤ F.top) (X : F.ComplexField j) (R : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) (h : Lattice4) (π : Equiv.Perm (Fin 4)) (w : UnitQuaternion) :
    complexPathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) * ofUnit w⁻¹ =
      relativeHolonomy X R (refineSite c.1) (axisPath h π) *
        conjByUnit (pathHolonomy R (refineSite c.1) (axisPath h π))
          (relativeHolonomy X R (refineSite c.1 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true))) *
        ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) * w⁻¹) *
        conjByUnit w (Matrix.adjugate
          (relativeHolonomy X R (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π))) := by
  have hR := complexPathHolonomy_bondContour hj (complexifyField R) c h π
  simp only [complexPathHolonomy_complexify, ← ofUnit_inv] at hR
  rw [complexPathHolonomy_bondContour hj X c h π, ofUnit_mul, hR]
  simp only [relativeHolonomy, conjByUnit, Matrix.adjugate_mul_distrib, ← ofUnit_inv, inv_inv, mul_assoc,
    ofUnit_inv_mul_cancel_left, ofUnit_mul_inv_cancel_left]
theorem ofQuat_mul_ofUnit_polarUnit_inv (q : ℍ[ℝ]) :
    ofQuat q * ofUnit (polarUnit q)⁻¹ = ((‖q‖ : ℝ) : ℂ) • (1 : ComplexQuat) := by
  by_cases h : q = 0
  · simp [h, ofQuat_zero]
  · have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 h
    have e : ofQuat q = ((‖q‖ : ℝ) : ℂ) • ofUnit (polarUnit q) := by
      have e1 : ((polarUnit q : UnitQuaternion) : ℍ[ℝ]) = ‖q‖⁻¹ • q := by
        simp [polarUnit, h]
      rw [ofUnit, e1, ofQuat_smul, smul_smul]
      have : ((‖q‖ : ℝ) : ℂ) * ((‖q‖⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hn]
        simp
      rw [this, one_smul]
    rw [e, smul_mul_assoc, ofUnit_mul_inv]
theorem length_axisPath_le (L : ℕ) (h : Lattice4) (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).length ≤ 2 * L := by
  rw [length_axisPath]
  have hb : ∀ i, (h i).natAbs ≤ L / 2 := fun i => by
    have := (mem_centredCube_iff L h).1 hh i
    omega
  have h0 := hb (π 0)
  have h1 := hb (π 1)
  have h2 := hb (π 2)
  have h3 := hb (π 3)
  omega
structure ContoursNearReal (X : F.ComplexField j) (R : F.GaugeField j) (t σ : ℝ) (c : F.Site (j + 1) × Fin 4) :
    Prop where
  nearLegs : ∀ h ∈ centredCube F.blockSide, ∀ π, PathNearReal X R t (refineSite c.1) (axisPath h π)
  nearLine : ∀ h ∈ centredCube F.blockSide,
    PathNearReal X R t (refineSite c.1 + siteOfCoords j h) (List.replicate F.blockSide (c.2, true))
  nearFarLegs : ∀ h ∈ centredCube F.blockSide, ∀ π,
    PathNearReal X R t (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π)
  realNearAverage : ∀ h ∈ centredCube F.blockSide, ∀ π,
    ‖ofUnit (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
      (polarUnit (contourAverage R c))⁻¹) - 1‖ ≤ σ
theorem norm_four_factor_sub_le (A B η D : ComplexQuat) {τ e : ℝ} (hτ : τ ≤ 1) (hA : ‖A‖ ≤ τ) (hB : ‖B‖ ≤ τ)
    (he : ‖η‖ ≤ e) (hD : ‖D‖ ≤ τ) :
    ‖(1 + A) * (1 + B) * (1 + η) * (1 + D) - (1 + η + A + B + D)‖ ≤ 4 * τ ^ 2 + 7 * e * τ := by
  have hτ0 : 0 ≤ τ := (norm_nonneg A).trans hA
  have he0 : 0 ≤ e := (norm_nonneg η).trans he
  have hid : (1 + A) * (1 + B) * (1 + η) * (1 + D) - (1 + η + A + B + D) =
      A * B + (A + B + A * B) * D + η * D + (A + B + A * B) * η * (1 + D) := by noncomm_ring
  rw [hid]
  have hAB : ‖A * B‖ ≤ τ ^ 2 := by
    refine (norm_mul_le _ _).trans ?_
    nlinarith [norm_nonneg A, norm_nonneg B]
  have hP : ‖A + B + A * B‖ ≤ 3 * τ := by
    have h1 := norm_add_le (A + B) (A * B)
    have h2 := norm_add_le A B
    nlinarith
  have h1 : ‖(A + B + A * B) * D‖ ≤ 3 * τ * τ :=
    (norm_mul_le _ _).trans (mul_le_mul hP hD (norm_nonneg _) (by linarith))
  have h2 : ‖η * D‖ ≤ e * τ := (norm_mul_le _ _).trans (mul_le_mul he hD (norm_nonneg _) he0)
  have h3 : ‖1 + D‖ ≤ 2 := by
    have := norm_add_le (1 : ComplexQuat) D
    rw [CStarRing.norm_one] at this
    linarith
  have h4 : ‖(A + B + A * B) * η * (1 + D)‖ ≤ 3 * τ * e * 2 := by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ h3 (norm_nonneg _) (by positivity))
    exact (norm_mul_le _ _).trans (mul_le_mul hP he (norm_nonneg _) (by linarith))
  have h5 := norm_add_le (A * B + (A + B + A * B) * D + η * D) ((A + B + A * B) * η * (1 + D))
  have h6 := norm_add_le (A * B + (A + B + A * B) * D) (η * D)
  have h7 := norm_add_le (A * B) ((A + B + A * B) * D)
  nlinarith
theorem eq_smul_one_add_purePart (a : ComplexQuat) : a = (a.trace / 2) • (1 : ComplexQuat) + purePart a := by
  rw [purePart_eq_sub_half_trace]
  abel
theorem adjugate_eq_smul_one_sub_purePart (a : ComplexQuat) :
    Matrix.adjugate a = (a.trace / 2) • (1 : ComplexQuat) - purePart a := by
  have h := congrArg Matrix.adjugate (eq_smul_one_add_purePart a)
  rw [adjugate_map_add, adjugate_map_smul, adjugate_one_complexQuat, adjugate_purePart] at h
  rw [h, sub_eq_add_neg]
theorem norm_sandwich_sub_le (a a' Q W : ComplexQuat) (w : UnitQuaternion) {r τ σ ω : ℝ} (hτ : τ ≤ 1 / 32)
    (ha : ‖a‖ ≤ τ) (ha' : ‖a'‖ ≤ τ) (hQ : ‖Q‖ ≤ τ) (hta : ‖a.trace‖ ≤ τ ^ 2) (hta' : ‖a'.trace‖ ≤ τ ^ 2)
    (hr0 : 0 ≤ r) (hr : |r - 1| ≤ σ) (hσ : σ ≤ 1) (hW : ‖W‖ ≤ ω) (hωτ : ω ≤ τ) :
    ‖Matrix.adjugate (unitPart (1 + a)) *
        (((r : ℝ) : ℂ) • (1 : ComplexQuat) + a + Q + conjByUnit w (Matrix.adjugate a') + W) *
        conjByUnit w (unitPart (1 + a')) - ((r : ℝ) : ℂ) • (1 : ComplexQuat) - Q‖ ≤
      200 * τ ^ 2 + 2 * σ * τ + ω := by
  have hτ0 : 0 ≤ τ := (norm_nonneg a).trans ha
  have hτ8 : τ ≤ 1 / 8 := by linarith
  have hσ0 : 0 ≤ σ := (abs_nonneg _).trans hr
  have hr2 : r ≤ 2 := by
    have := (abs_le.1 hr).2
    linarith
  set p := purePart a with hp
  set p0 := purePart a' with hp0
  set ε := unitPart (1 + a) - 1 - p with hε
  set ε0 := unitPart (1 + a') - 1 - p0 with hε0
  have h1 : ‖ε‖ ≤ 32 * τ ^ 2 := (norm_unitPart_one_add_sub_le (ha.trans hτ8)).trans (by gcongr)
  have h2 : ‖ε0‖ ≤ 32 * τ ^ 2 := (norm_unitPart_one_add_sub_le (ha'.trans hτ8)).trans (by gcongr)
  have hpn : ‖p‖ ≤ τ := (norm_purePart_le a).trans ha
  have hp0n : ‖p0‖ ≤ τ := (norm_purePart_le a').trans ha'
  set u := - p + Matrix.adjugate ε with hu
  set v := conjByUnit w p0 + conjByUnit w ε0 with hv
  have hk : Matrix.adjugate (unitPart (1 + a)) = 1 + u := by
    have : unitPart (1 + a) = 1 + p + ε := by
      rw [hε]
      abel
    rw [this, adjugate_map_add, adjugate_map_add, adjugate_one_complexQuat, adjugate_purePart, hu]
    abel
  have hk' : conjByUnit w (unitPart (1 + a')) = 1 + v := by
    have : unitPart (1 + a') = 1 + p0 + ε0 := by
      rw [hε0]
      abel
    rw [this, conjByUnit_add, conjByUnit_add, conjByUnit_one, hv]
    abel
  have hun : ‖u‖ ≤ 2 * τ := by
    have := norm_add_le (-p) (Matrix.adjugate ε)
    rw [norm_neg, norm_adjugate] at this
    nlinarith
  have hvn : ‖v‖ ≤ 2 * τ := by
    have := norm_add_le (conjByUnit w p0) (conjByUnit w ε0)
    rw [norm_conjByUnit, norm_conjByUnit] at this
    nlinarith
  set α : ℂ := a.trace / 2 + a'.trace / 2 with hα
  have hαn : ‖α‖ ≤ τ ^ 2 := by
    have := norm_add_le (a.trace / 2) (a'.trace / 2)
    simp only [norm_div, Complex.norm_ofNat] at this
    linarith
  set p1 := conjByUnit w p0 with hp1
  set G := α • (1 : ComplexQuat) + p + Q - p1 + W with hG
  have hM : ((r : ℝ) : ℂ) • (1 : ComplexQuat) + a + Q + conjByUnit w (Matrix.adjugate a') + W =
      ((r : ℝ) : ℂ) • (1 : ComplexQuat) + G := by
    have e1 : conjByUnit w (Matrix.adjugate a') = (a'.trace / 2) • (1 : ComplexQuat) - p1 := by
      rw [adjugate_eq_smul_one_sub_purePart, conjByUnit_sub, conjByUnit_smul, conjByUnit_one]
    rw [e1, hG, hα]
    nth_rewrite 1 [eq_smul_one_add_purePart a]
    module
  have hp1n : ‖p1‖ ≤ τ := by rw [hp1, norm_conjByUnit]; exact hp0n
  have hGn : ‖G‖ ≤ 5 * τ := by
    have h3 := norm_add_le (α • (1 : ComplexQuat) + p + Q - p1) W
    have h4 := norm_sub_le (α • (1 : ComplexQuat) + p + Q) p1
    have h5 := norm_add_le (α • (1 : ComplexQuat) + p) Q
    have h6 := norm_add_le (α • (1 : ComplexQuat)) p
    have h7 : ‖α • (1 : ComplexQuat)‖ = ‖α‖ := by rw [norm_smul, CStarRing.norm_one, mul_one]
    nlinarith
  set ρ : ComplexQuat := ((r : ℝ) : ℂ) • (1 : ComplexQuat) with hρ
  have hid : (1 + u) * (ρ + G) * (1 + v) - ρ - Q =
      (G - Q + u * ρ + ρ * v) + (u * G + G * v + u * ρ * v + u * G * v) := by noncomm_ring
  have hlin : G - Q + u * ρ + ρ * v =
      α • (1 : ComplexQuat) + (1 - ((r : ℝ) : ℂ)) • (p - p1) + W +
        ((r : ℝ) : ℂ) • (Matrix.adjugate ε + conjByUnit w ε0) := by
    have e1 : u * ρ = ((r : ℝ) : ℂ) • u := by rw [hρ, mul_smul_comm, mul_one]
    have e2 : ρ * v = ((r : ℝ) : ℂ) • v := by rw [hρ, smul_mul_assoc, one_mul]
    rw [e1, e2, hG, hu, hv]
    module
  rw [hM, hk, hk', hid, hlin]
  have hrn : ‖((r : ℝ) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr2
  have h1r : ‖(1 - ((r : ℝ) : ℂ))‖ ≤ σ := by
    have : (1 - ((r : ℝ) : ℂ)) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hr
  have hρn : ‖ρ‖ ≤ 2 := by
    rw [hρ, norm_smul, CStarRing.norm_one, mul_one]
    exact hrn
  have n1 : ‖α • (1 : ComplexQuat)‖ ≤ τ ^ 2 := by rw [norm_smul, CStarRing.norm_one, mul_one]; exact hαn
  have n2 : ‖(1 - ((r : ℝ) : ℂ)) • (p - p1)‖ ≤ σ * (2 * τ) := by
    rw [norm_smul]
    have := norm_sub_le p p1
    exact mul_le_mul h1r (by linarith) (norm_nonneg _) hσ0
  have n3 : ‖((r : ℝ) : ℂ) • (Matrix.adjugate ε + conjByUnit w ε0)‖ ≤ 2 * (64 * τ ^ 2) := by
    rw [norm_smul]
    have := norm_add_le (Matrix.adjugate ε) (conjByUnit w ε0)
    rw [norm_adjugate, norm_conjByUnit] at this
    exact mul_le_mul hrn (by linarith) (norm_nonneg _) (by norm_num)
  have n4 : ‖u * G‖ ≤ 2 * τ * (5 * τ) :=
    (norm_mul_le _ _).trans (mul_le_mul hun hGn (norm_nonneg _) (by linarith))
  have n5 : ‖G * v‖ ≤ 5 * τ * (2 * τ) :=
    (norm_mul_le _ _).trans (mul_le_mul hGn hvn (norm_nonneg _) (by linarith))
  have n6 : ‖u * ρ * v‖ ≤ 2 * τ * 2 * (2 * τ) := by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ hvn (norm_nonneg _) (by linarith))
    exact (norm_mul_le _ _).trans (mul_le_mul hun hρn (norm_nonneg _) (by linarith))
  have n7 : ‖u * G * v‖ ≤ 2 * τ * (5 * τ) * (2 * τ) := by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ hvn (norm_nonneg _) (by positivity))
    exact (norm_mul_le _ _).trans (mul_le_mul hun hGn (norm_nonneg _) (by linarith))
  have n8 : 2 * τ * (5 * τ) * (2 * τ) ≤ 2 * τ ^ 2 := by nlinarith [sq_nonneg τ]
  have m1 := norm_add_le (α • (1 : ComplexQuat) + (1 - ((r : ℝ) : ℂ)) • (p - p1) + W +
        ((r : ℝ) : ℂ) • (Matrix.adjugate ε + conjByUnit w ε0)) (u * G + G * v + u * ρ * v + u * G * v)
  have m2 := norm_add_le (α • (1 : ComplexQuat) + (1 - ((r : ℝ) : ℂ)) • (p - p1) + W)
    (((r : ℝ) : ℂ) • (Matrix.adjugate ε + conjByUnit w ε0))
  have m3 := norm_add_le (α • (1 : ComplexQuat) + (1 - ((r : ℝ) : ℂ)) • (p - p1)) W
  have m4 := norm_add_le (α • (1 : ComplexQuat)) ((1 - ((r : ℝ) : ℂ)) • (p - p1))
  have m5 := norm_add_le (u * G + G * v + u * ρ * v) (u * G * v)
  have m6 := norm_add_le (u * G + G * v) (u * ρ * v)
  have m7 := norm_add_le (u * G) (G * v)
  nlinarith
end Contours
end YangMills.Construction.ComplexContours
end
