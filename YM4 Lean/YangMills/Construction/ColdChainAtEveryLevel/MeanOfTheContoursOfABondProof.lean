import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.ColdChainAtEveryLevel.MeanOfTheContoursOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
namespace ContourMean
open LatticePaths FlatPairing LatticeFractionalIntegration
variable {F : BlockFrame}
section Units
theorem coe_unitQuaternion_mul (a b : UnitQuaternion) :
    ((a * b : UnitQuaternion) : ℍ[ℝ]) = (a : ℍ[ℝ]) * (b : ℍ[ℝ]) := rfl
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem adjointAction_mul (a b : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (a * b) w = adjointAction a (adjointAction b w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (x y : ℍ[ℝ]) :
    adjointAction g (x - y) = adjointAction g x - adjointAction g y := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_sum {ι : Type*} (g : UnitQuaternion) (s : Finset ι) (f : ι → ℍ[ℝ]) :
    adjointAction g (∑ i ∈ s, f i) = ∑ i ∈ s, adjointAction g (f i) := by
  simp only [adjointAction, Finset.mul_sum, Finset.sum_mul]
theorem coe_conj_eq_adjointAction (a b : UnitQuaternion) :
    ((a * b * a⁻¹ : UnitQuaternion) : ℍ[ℝ]) = adjointAction a (b : ℍ[ℝ]) := rfl
theorem pureComponent_adjointAction (g : UnitQuaternion) (q : ℍ[ℝ]) :
    pureComponent (adjointAction g q) = adjointAction g (pureComponent q) := by apply _root_.YangMills.Construction.BlockLines.pureComponent_adjointAction <;> assumption
theorem norm_pureComponent_coe_le (g : UnitQuaternion) :
    ‖pureComponent (g : ℍ[ℝ])‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockLines.norm_pureComponent_coe_le <;> assumption
theorem norm_pureComponent_mul_sub_le (g w : UnitQuaternion) :
    ‖pureComponent ((g * w : UnitQuaternion) : ℍ[ℝ]) - pureComponent (g : ℍ[ℝ]) -
        pureComponent (w : ℍ[ℝ])‖ ≤
      ‖(g : ℍ[ℝ]) - 1‖ * ‖(w : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockLines.norm_pureComponent_mul_sub_le <;> assumption
theorem norm_four_product_sub_le (a b c d : UnitQuaternion) :
    ‖((a * b * c * d : UnitQuaternion) : ℍ[ℝ]) - 1 - ((a : ℍ[ℝ]) - 1) - ((b : ℍ[ℝ]) - 1) -
        ((c : ℍ[ℝ]) - 1) - ((d : ℍ[ℝ]) - 1)‖ ≤
      ‖(a : ℍ[ℝ]) - 1‖ * (‖(b : ℍ[ℝ]) - 1‖ + ‖(c : ℍ[ℝ]) - 1‖ + ‖(d : ℍ[ℝ]) - 1‖) +
        ‖(b : ℍ[ℝ]) - 1‖ * (‖(c : ℍ[ℝ]) - 1‖ + ‖(d : ℍ[ℝ]) - 1‖) +
        ‖(c : ℍ[ℝ]) - 1‖ * ‖(d : ℍ[ℝ]) - 1‖ := by
  have e : ((a * b * c * d : UnitQuaternion) : ℍ[ℝ]) - 1 - ((a : ℍ[ℝ]) - 1) - ((b : ℍ[ℝ]) - 1) -
      ((c : ℍ[ℝ]) - 1) - ((d : ℍ[ℝ]) - 1) =
      ((a : ℍ[ℝ]) - 1) * (((b * c * d : UnitQuaternion) : ℍ[ℝ]) - 1) +
        ((b : ℍ[ℝ]) - 1) * (((c * d : UnitQuaternion) : ℍ[ℝ]) - 1) +
        ((c : ℍ[ℝ]) - 1) * ((d : ℍ[ℝ]) - 1) := by
    simp only [coe_unitQuaternion_mul]
    noncomm_ring
  rw [e]
  have h1 := norm_coe_mul_sub_one_le (b * c) d
  have h2 := norm_coe_mul_sub_one_le b c
  have h3 := norm_coe_mul_sub_one_le c d
  have n1 : ‖((a : ℍ[ℝ]) - 1) * (((b * c * d : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤
      ‖(a : ℍ[ℝ]) - 1‖ * (‖(b : ℍ[ℝ]) - 1‖ + ‖(c : ℍ[ℝ]) - 1‖ + ‖(d : ℍ[ℝ]) - 1‖) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _))
  have n2 : ‖((b : ℍ[ℝ]) - 1) * (((c * d : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤
      ‖(b : ℍ[ℝ]) - 1‖ * (‖(c : ℍ[ℝ]) - 1‖ + ‖(d : ℍ[ℝ]) - 1‖) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
  have n3 := norm_mul_le ((c : ℍ[ℝ]) - 1) ((d : ℍ[ℝ]) - 1)
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add n1 n2)) n3)
theorem polarUnit_coe (g : UnitQuaternion) : polarUnit (g : ℍ[ℝ]) = g := by apply _root_.YangMills.Construction.BlockLines.polarUnit_coe <;> assumption
end Units
section Paths
def linkGap {j : ℕ} (X R : F.GaugeField j) (x : F.Site j) (st : PathStep) : UnitQuaternion :=
  linkValue X x st * (linkValue R x st)⁻¹
def relativeHolonomy {j : ℕ} (X R : F.GaugeField j) (x : F.Site j) (l : List PathStep) : UnitQuaternion :=
  pathHolonomy X x l * (pathHolonomy R x l)⁻¹
theorem relativeHolonomy_nil {j : ℕ} (X R : F.GaugeField j) (x : F.Site j) :
    relativeHolonomy X R x [] = 1 := by
  simp [relativeHolonomy, pathHolonomy]
theorem relativeHolonomy_cons {j : ℕ} (X R : F.GaugeField j) (x : F.Site j) (st : PathStep)
    (l : List PathStep) :
    relativeHolonomy X R x (st :: l) = linkGap X R x st *
      (linkValue R x st * relativeHolonomy X R (x + BlockAverages.stepDisplacement j st) l *
        (linkValue R x st)⁻¹) := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.pathDiscrepancy_cons <;> assumption
theorem stepDisplacement_eq_siteOfCoords (j : ℕ) (st : PathStep) :
    BlockAverages.stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem linkGap_forward {j : ℕ} (X R : F.GaugeField j) (x : F.Site j) (k : Fin 4) :
    linkGap X R x (k, true) = X x k * (R x k)⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.linkDiscrepancy_forward <;> assumption
theorem norm_relativeHolonomy_sub_one_le {j : ℕ} (X R : F.GaugeField j) (x₀ : F.Site j)
    (p : Lattice4 → Prop) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : ∀ u st, p u → p (u + FlatPairing.stepDisplacement st) →
      ‖((linkGap X R (x₀ + siteOfCoords j u) st : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t) :
    ∀ (l : List PathStep) (u : Lattice4), AllAlong p u l →
      ‖((relativeHolonomy X R (x₀ + siteOfCoords j u) l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * t := by apply _root_.YangMills.Construction.BondHull.distFromOne_pathRatio_le <;> assumption
theorem add_stepDisplacement_add_siteOfCoords {j : ℕ} (x : F.Site j) (st : PathStep) (l : List PathStep) :
    x + BlockAverages.stepDisplacement j st + siteOfCoords j (endpoint 0 l) =
      x + siteOfCoords j (endpoint 0 (st :: l)) := by
  show _ = x + siteOfCoords j (endpoint (0 + FlatPairing.stepDisplacement st) l)
  rw [stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add, zero_add]
  congr 2
  have := endpoint_add 0 (FlatPairing.stepDisplacement st) l
  rw [zero_add] at this
  rw [this, add_comm]
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) (x : F.Site j) :
    pathHolonomy X x (l ++ l') =
      pathHolonomy X x l * pathHolonomy X (x + siteOfCoords j (endpoint 0 l)) l' := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, endpoint, siteOfCoords_zero]
  | cons st r ih =>
    simp only [List.cons_append, pathHolonomy]
    rw [ih, add_stepDisplacement_add_siteOfCoords, mul_assoc]
theorem linkValue_flip {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + BlockAverages.stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) (x : F.Site j) :
    pathHolonomy X (x + siteOfCoords j (endpoint 0 l)) (reversePath l) = (pathHolonomy X x l)⁻¹ := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, endpoint, siteOfCoords_zero, reversePath]
  | cons st r ih =>
    rw [reversePath_cons, ← add_stepDisplacement_add_siteOfCoords, pathHolonomy_append, ih]
    have e : x + BlockAverages.stepDisplacement j st + siteOfCoords j (endpoint 0 r) +
        siteOfCoords j (endpoint 0 (reversePath r)) = x + BlockAverages.stepDisplacement j st := by
      rw [add_assoc, ← siteOfCoords_add]
      have h1 := endpoint_reversePath 0 r
      have h2 := endpoint_add 0 (endpoint 0 r) (reversePath r)
      rw [zero_add] at h2
      rw [h2] at h1
      rw [add_comm (endpoint 0 r), h1, siteOfCoords_zero, add_zero]
    rw [e]
    simp only [pathHolonomy, linkValue_flip, mul_one, mul_inv_rev]
theorem straightLine_estimate {j : ℕ} (X R : F.GaugeField j) (i : Fin 4) (t : ℝ) (ht0 : 0 ≤ t) (n : ℕ)
    (x : F.Site j)
    (ht : ∀ r : ℕ, r < n →
      ‖((X (x + (r : ℤ) • unitStep j i) i * (R (x + (r : ℤ) • unitStep j i) i)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ t) :
    ‖((relativeHolonomy X R x (List.replicate n (i, true)) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ n * t ∧
    ‖pureComponent ((relativeHolonomy X R x (List.replicate n (i, true)) : UnitQuaternion) : ℍ[ℝ]) -
        ∑ r ∈ Finset.range n, adjointAction (pathHolonomy R x (List.replicate r (i, true)))
          (pureGap X R (x + (r : ℤ) • unitStep j i) i)‖ ≤ (n : ℝ) ^ 2 * t ^ 2 := by
  induction n generalizing x with
  | zero => simp [relativeHolonomy_nil, pureComponent_one]
  | succ n ih =>
    have hx' : ∀ r : ℕ, x + unitStep j i + (r : ℤ) • unitStep j i =
        x + ((r + 1 : ℕ) : ℤ) • unitStep j i := by
      intro r
      push_cast
      rw [add_smul, one_smul]
      abel
    obtain ⟨i1, i2⟩ := ih (x + unitStep j i) (fun r hr => by
      rw [hx']
      exact ht (r + 1) (by omega))
    have hst : BlockAverages.stepDisplacement j (i, true) = unitStep (F := F) j i := by
      simp [BlockAverages.stepDisplacement]
    have hsv : linkValue R x (i, true) = R x i := by simp [linkValue]
    set G' := relativeHolonomy X R (x + unitStep j i) (List.replicate n (i, true)) with hG'
    set g := X x i * (R x i)⁻¹ with hg
    set w := R x i * G' * (R x i)⁻¹ with hw
    have hcons : relativeHolonomy X R x (List.replicate (n + 1) (i, true)) = g * w := by
      rw [List.replicate_succ, relativeHolonomy_cons, linkGap_forward, hst, hsv]
    have hg1 : ‖(g : ℍ[ℝ]) - 1‖ ≤ t := by
      have h0 := ht 0 (by omega)
      rw [Nat.cast_zero, zero_smul, add_zero] at h0
      exact h0
    have hw1 : ‖(w : ℍ[ℝ]) - 1‖ ≤ n * t := by
      rw [hw, norm_coe_conj_sub_one]
      exact i1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    rw [hcons]
    refine ⟨?_, ?_⟩
    · have := norm_coe_mul_sub_one_le g w
      have hc : ((n + 1 : ℕ) : ℝ) * t = n * t + t := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      rw [hc]
      linarith
    · have hpw : pureComponent (w : ℍ[ℝ]) = adjointAction (R x i) (pureComponent (G' : ℍ[ℝ])) := by
        rw [← pureComponent_adjointAction]
        rfl
      have hsum : ∑ r ∈ Finset.range (n + 1), adjointAction (pathHolonomy R x (List.replicate r (i, true)))
            (pureGap X R (x + (r : ℤ) • unitStep j i) i) =
          adjointAction (R x i) (∑ r ∈ Finset.range n,
            adjointAction (pathHolonomy R (x + unitStep j i) (List.replicate r (i, true)))
            (pureGap X R (x + unitStep j i + (r : ℤ) • unitStep j i) i)) + pureComponent (g : ℍ[ℝ]) := by
        rw [Finset.sum_range_succ', adjointAction_sum]
        congr 1
        · refine Finset.sum_congr rfl fun r _ => ?_
          rw [← adjointAction_mul, hx', List.replicate_succ]
          simp only [pathHolonomy, hsv, hst]
        · simp [pathHolonomy, adjointAction, pureGap, hg]
      rw [hsum]
      have e : pureComponent ((g * w : UnitQuaternion) : ℍ[ℝ]) - (adjointAction (R x i) (∑ r ∈ Finset.range n,
            adjointAction (pathHolonomy R (x + unitStep j i) (List.replicate r (i, true)))
            (pureGap X R (x + unitStep j i + (r : ℤ) • unitStep j i) i)) + pureComponent (g : ℍ[ℝ])) =
          (pureComponent ((g * w : UnitQuaternion) : ℍ[ℝ]) - pureComponent (g : ℍ[ℝ]) -
              pureComponent (w : ℍ[ℝ])) +
            adjointAction (R x i) (pureComponent (G' : ℍ[ℝ]) - ∑ r ∈ Finset.range n,
              adjointAction (pathHolonomy R (x + unitStep j i) (List.replicate r (i, true)))
              (pureGap X R (x + unitStep j i + (r : ℤ) • unitStep j i) i)) := by
        rw [adjointAction_sub, ← hpw]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_adjointAction]
      have h1 := norm_pureComponent_mul_sub_le g w
      have h2 : ‖(g : ℍ[ℝ]) - 1‖ * ‖(w : ℍ[ℝ]) - 1‖ ≤ t * (n * t) :=
        mul_le_mul hg1 hw1 (norm_nonneg _) ht0
      have hc : ((n + 1 : ℕ) : ℝ) ^ 2 * t ^ 2 = (n : ℝ) ^ 2 * t ^ 2 + (2 * (n * (t * t)) + t * t) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      rw [hc]
      nlinarith [mul_nonneg hn0 (mul_nonneg ht0 ht0), mul_nonneg ht0 ht0]
theorem pathHolonomy_bondContour {j : ℕ} (hj : j + 1 ≤ F.top) (Y : F.GaugeField j) (y : F.Site (j + 1))
    (i : Fin 4) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy Y (refineSite y) (bondContour F.blockSide h π i) =
      pathHolonomy Y (refineSite y) (axisPath h π) *
        pathHolonomy Y (refineSite y + siteOfCoords j h) (List.replicate F.blockSide (i, true)) *
        (pathHolonomy Y (refineSite (y + unitStep (j + 1) i)) (axisPath h π))⁻¹ := by
  have hend := (axisPath_spec h π).2
  have e1 : FlatPairing.stepDisplacement (i, true) = basisVector i := by
    simp [FlatPairing.stepDisplacement]
  have e2 : refineSite y + siteOfCoords j (endpoint 0 (axisPath h π ++ List.replicate F.blockSide (i, true))) =
      refineSite (y + unitStep (j + 1) i) + siteOfCoords j (endpoint 0 (axisPath h π)) := by
    rw [endpoint_append, hend, endpoint_replicate, e1, unitStep_eq, refineSite_add j hj, add_assoc,
      ← siteOfCoords_add]
    congr 2
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold bondContour
  rw [pathHolonomy_append, pathHolonomy_append, hend, e2, pathHolonomy_reversePath]
end Paths
section Means
def blockMean (L : ℕ) (φ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) : ℍ[ℝ] :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), φ h π
theorem sum_centredCube_perm_const {L : ℕ} (hL : Odd L) (B : ℝ) :
    ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), B = 24 * (L : ℝ) ^ 4 * B := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    card_centredCube hL]
  simp [Nat.factorial]
  ring
theorem cast_pos_of_odd {L : ℕ} (hL : Odd L) : (0 : ℝ) < L := by exact_mod_cast hL.pos
theorem norm_blockMean_le {L : ℕ} (hL : Odd L) (φ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) (B : ℝ)
    (hb : ∀ h ∈ centredCube L, ∀ π, ‖φ h π‖ ≤ B) : ‖blockMean L φ‖ ≤ B := by
  have hp := cast_pos_of_odd hL
  unfold blockMean
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), φ h π‖ ≤
      ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), B := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => hb h hh π)
  rw [sum_centredCube_perm_const hL] at h1
  calc 1 / (24 * (L : ℝ) ^ 4) * _ ≤ 1 / (24 * (L : ℝ) ^ 4) * (24 * (L : ℝ) ^ 4 * B) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B := by field_simp
theorem blockMean_one {L : ℕ} (hL : Odd L) : blockMean L (fun _ _ => (1 : ℍ[ℝ])) = 1 := by
  have hp := cast_pos_of_odd hL
  unfold blockMean
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    card_centredCube hL]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  have : 1 / (24 * (L : ℝ) ^ 4) * ((L ^ 4 : ℕ) : ℝ) * (((Nat.factorial 4 : ℕ)) : ℝ) = 1 := by
    simp only [Nat.factorial]
    push_cast
    field_simp
    try norm_num
  rw [this, one_smul]
theorem blockMean_sub (L : ℕ) (φ ψ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    blockMean L (fun h π => φ h π - ψ h π) = blockMean L φ - blockMean L ψ := by
  simp only [blockMean, Finset.sum_sub_distrib, smul_sub]
theorem blockMean_add (L : ℕ) (φ ψ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    blockMean L (fun h π => φ h π + ψ h π) = blockMean L φ + blockMean L ψ := by
  simp only [blockMean, Finset.sum_add_distrib, smul_add]
theorem pureComponent_blockMean (L : ℕ) (φ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    pureComponent (blockMean L φ) = blockMean L (fun h π => pureComponent (φ h π)) := by
  unfold blockMean
  rw [pureComponent_smul, pureComponent_sum]
  simp only [pureComponent_sum]
theorem mul_blockMean_mul (L : ℕ) (a b : ℍ[ℝ]) (φ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    a * blockMean L φ * b = blockMean L (fun h π => a * φ h π * b) := by
  unfold blockMean
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
theorem star_blockMean (L : ℕ) (φ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    star (blockMean L φ) = blockMean L (fun h π => star (φ h π)) := by
  unfold blockMean
  rw [quaternion_star_real_smul, star_sum]
  simp only [star_sum]
theorem adjointAction_blockMean (L : ℕ) (g : UnitQuaternion) (φ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) :
    adjointAction g (blockMean L φ) = blockMean L (fun h π => adjointAction g (φ h π)) := by
  simp only [adjointAction, mul_blockMean_mul]
theorem relativePathAverage_eq {j : ℕ} (X R : F.GaugeField j) (y : F.Site (j + 1)) :
    relativePathAverage X R y = blockMean F.blockSide
      (fun h π => ((relativeHolonomy X R (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ])) := rfl
theorem contourAverage_eq {j : ℕ} (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    contourAverage X c = blockMean F.blockSide (fun h π =>
      ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) := rfl
theorem coe_polarUnit_inv_mul {q : ℍ[ℝ]} (h : q ≠ 0) :
    (((polarUnit q)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * q = ((‖q‖ : ℝ) : ℍ[ℝ]) := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 h
  rw [coe_unitQuaternion_inv, coe_polarUnit h, quaternion_star_real_smul, Algebra.smul_mul_assoc,
    Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self]
  ext <;> simp
  field_simp
theorem mul_coe_polarUnit_inv {q : ℍ[ℝ]} (h : q ≠ 0) :
    q * (((polarUnit q)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = ((‖q‖ : ℝ) : ℍ[ℝ]) := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 h
  rw [coe_unitQuaternion_inv, coe_polarUnit h, quaternion_star_real_smul, Algebra.mul_smul_comm,
    Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self]
  ext <;> simp
  field_simp
end Means
section Main
variable {j : ℕ}
theorem norm_linkGap_sub_one_le (X R : F.GaugeField j) (x₀ : F.Site j) (H : Set Lattice4) (t : ℝ)
    (hcl : ∀ a ∈ H, ∀ k, a + basisVector k ∈ H →
      ‖((X (x₀ + siteOfCoords j a) k * (R (x₀ + siteOfCoords j a) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t)
    (u : Lattice4) (st : PathStep) (hu : u ∈ H) (hv : u + FlatPairing.stepDisplacement st ∈ H) :
    ‖((linkGap X R (x₀ + siteOfCoords j u) st : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.normSubOne_linkDiscrepancy_le <;> assumption
theorem length_axisPath_le {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) :
    ((axisPath h π).length : ℝ) ≤ 2 * L := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.length_axisPath_le <;> assumption
theorem mem_twoBlockHull_of_between_shift {L : ℕ} {h v : Lattice4} {i : Fin 4} (hh : h ∈ centredCube L)
    (hL : 1 ≤ L) (hv : BetweenOrigin h (v - (L : ℤ) • basisVector i)) : v ∈ twoBlockHull L i := by
  intro μ
  have h1 := ((mem_centredCube_iff L h).1 hh) μ
  have h2 := hv μ
  have hk : (0 : ℤ) ≤ ((L : ℤ) - 1) / 2 := by omega
  have a1 : min 0 (h μ) ≥ -(((L : ℤ) - 1) / 2) := le_min (by omega) h1.1
  have a2 : max 0 (h μ) ≤ ((L : ℤ) - 1) / 2 := max_le hk h1.2
  by_cases hμ : μ = i
  · subst hμ
    simp only [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one,
      if_true] at h2 ⊢
    constructor <;> omega
  · simp only [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hμ, smul_eq_mul, mul_zero,
      sub_zero, if_neg hμ] at h2 ⊢
    constructor <;> omega
theorem polarUnit_near_one {q : ℍ[ℝ]} {e : ℝ} (h : ‖q - 1‖ ≤ e) (he : e ≤ 1 / 4) :
    q ≠ 0 ∧ ‖((polarUnit q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * e := by apply _root_.YangMills.Construction.BondHull.polarUnit_near_one <;> assumption
theorem norm_line_link_gap_le (X R : F.GaugeField j) (b : F.Site (j + 1) × Fin 4) (t : ℝ)
    (hodd : Odd F.blockSide) (ht0 : 0 ≤ t)
    (hcl : ∀ a ∈ twoBlockHull F.blockSide b.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide b.2 →
      ‖((X (refineSite b.1 + siteOfCoords j a) k * (R (refineSite b.1 + siteOfCoords j a) k)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t)
    (h : Lattice4) (hh : h ∈ centredCube F.blockSide) (r : ℕ) (hr : r < F.blockSide) :
    ‖((X (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2 *
      (R (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ t := by
  have e : refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2 =
      refineSite b.1 + siteOfCoords j (h + (r : ℤ) • basisVector b.2) := by
    rw [add_assoc, siteOfCoords_add]
    congr 2
    funext l
    simp [unitStep, siteOfCoords, basisVector, Pi.single_apply]
  rw [e]
  have hc := (mem_centredCube_iff F.blockSide h).1 hh
  refine hcl _ ?_ b.2 ?_
  · intro μ
    have h1 := hc μ
    by_cases hμ : μ = b.2
    · subst hμ
      simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one,
        if_true]
      constructor <;> omega
    · simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hμ, smul_eq_mul, mul_zero,
        add_zero, if_neg hμ]
      constructor <;> omega
  · intro μ
    have h1 := hc μ
    by_cases hμ : μ = b.2
    · subst hμ
      simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one,
        if_true]
      constructor <;> omega
    · simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hμ, smul_eq_mul, mul_zero,
        add_zero, if_neg hμ]
      constructor <;> omega
theorem parallelAverage_eq (R : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ]) (b : F.Site (j + 1) × Fin 4) :
    parallelAverage R f b = blockMean F.blockSide (fun h π =>
      adjointAction (pathHolonomy R (refineSite b.1) (axisPath h π))
      (∑ r ∈ Finset.range F.blockSide,
        adjointAction (pathHolonomy R (refineSite b.1 + siteOfCoords j h) (List.replicate r (b.2, true)))
        (f (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2))) := by
  unfold parallelAverage blockMean
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
  beta_reduce
  rw [adjointAction_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pathHolonomy_append, adjointAction_mul, (axisPath_spec h π).2]
theorem real_tail_bound {p q P τ ε : ℝ} (hp0 : 0 ≤ p) (hPn : 41 / 50 ≤ P)
    (hpure : p ≤ q + 81 * (τ * (τ + ε))) (hτε : 0 ≤ τ * (τ + ε)) :
    2 * p ≤ (4 * q + 500 * τ * (τ + ε)) * P := by
  have h4 : 2 * p ≤ (4 * p) * P := by nlinarith
  have h5 : 4 * p ≤ 4 * q + 500 * τ * (τ + ε) := by nlinarith
  have h6 : (4 * p) * P ≤ (4 * q + 500 * τ * (τ + ε)) * P :=
    mul_le_mul_of_nonneg_right h5 (by linarith)
  linarith
theorem contourAverage_estimate (X R : F.GaugeField j) (b : F.Site (j + 1) × Fin 4) (t ε : ℝ)
    (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hτ : (F.blockSide : ℝ) * t ≤ 1 / 100) (hε : ε ≤ 1 / 100)
    (hcl : ∀ a ∈ twoBlockHull F.blockSide b.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide b.2 →
      ‖((X (refineSite b.1 + siteOfCoords j a) k * (R (refineSite b.1 + siteOfCoords j a) k)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t)
    (hsp : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) *
        (polarUnit (contourAverage R b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) :
    ‖parallelAverage R (pureGap X R) b‖ ≤ (F.blockSide : ℝ) * t ∧
      ‖pureComponent ((relativeContourMean X R b : UnitQuaternion) : ℍ[ℝ]) -
          parallelAverage R (pureGap X R) b‖ ≤
        500 * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε) ∧
      ‖((relativeContourMean X R b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        4 * ‖parallelAverage R (pureGap X R) b‖ +
          500 * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε) := by
  have hL1 : 1 ≤ F.blockSide := hodd.pos
  have hLr : (0 : ℝ) < F.blockSide := cast_pos_of_odd hodd
  set τ : ℝ := (F.blockSide : ℝ) * t with hτdef
  have hτ0 : 0 ≤ τ := mul_nonneg hLr.le ht0
  set y' : F.Site (j + 1) := b.1 + unitStep (j + 1) b.2 with hy'
  set ub : UnitQuaternion := polarUnit (contourAverage R b) with hub
  have hdown : refineSite y' = refineSite b.1 + siteOfCoords j ((F.blockSide : ℤ) • basisVector b.2) := by
    rw [hy', unitStep_eq, refineSite_add j hj]
    congr 2
  have hleg : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((relativeHolonomy X R (refineSite b.1) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * τ := by
    intro h hh π
    have := norm_relativeHolonomy_sub_one_le X R (refineSite b.1)
      (fun v => v ∈ twoBlockHull F.blockSide b.2) t ht0
      (fun u st hu hv => norm_linkGap_sub_one_le X R _ _ t hcl u st hu hv) (axisPath h π) 0
      (allAlong_mono (fun v hv => mem_twoBlockHull_of_between hh hv hL1) (axisPath_spec h π).1)
    rw [siteOfCoords_zero, add_zero] at this
    refine this.trans ?_
    have h2 := length_axisPath_le hh π
    calc ((axisPath h π).length : ℝ) * t ≤ (2 * F.blockSide) * t := mul_le_mul_of_nonneg_right h2 ht0
      _ = 2 * τ := by rw [hτdef]; ring
  have hleg' : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((relativeHolonomy X R (refineSite y') (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * τ := by
    intro h hh π
    have hp := allAlong_add (w := (F.blockSide : ℤ) • basisVector b.2) (axisPath_spec h π).1
    rw [zero_add] at hp
    have := norm_relativeHolonomy_sub_one_le X R (refineSite b.1)
      (fun v => v ∈ twoBlockHull F.blockSide b.2) t ht0
      (fun u st hu hv => norm_linkGap_sub_one_le X R _ _ t hcl u st hu hv) (axisPath h π)
      ((F.blockSide : ℤ) • basisVector b.2)
      (allAlong_mono (fun v hv => mem_twoBlockHull_of_between_shift hh hL1 hv) hp)
    rw [← hdown] at this
    refine this.trans ?_
    have h2 := length_axisPath_le hh π
    calc ((axisPath h π).length : ℝ) * t ≤ (2 * F.blockSide) * t := mul_le_mul_of_nonneg_right h2 ht0
      _ = 2 * τ := by rw [hτdef]; ring
  have hmean1 : ∀ y : F.Site (j + 1), (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((relativeHolonomy X R (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * τ) →
      ‖relativePathAverage X R y - 1‖ ≤ 2 * τ := by
    intro y hy
    rw [relativePathAverage_eq, ← blockMean_one hodd, ← blockMean_sub]
    exact norm_blockMean_le hodd _ _ hy
  have hlink : ∀ y : F.Site (j + 1), (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((relativeHolonomy X R (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * τ) →
      relativePathAverage X R y ≠ 0 ∧ ‖((balancingGauge X R y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 6 * τ := by
    intro y hy
    obtain ⟨h0, h1⟩ := polarUnit_near_one (hmean1 y hy) (by linarith)
    refine ⟨h0, ?_⟩
    unfold balancingGauge
    rw [norm_coe_inv_sub_one]
    linarith
  obtain ⟨hl0, hk⟩ := hlink b.1 hleg
  obtain ⟨hl0', hk'⟩ := hlink y' hleg'
  set k : UnitQuaternion := balancingGauge X R b.1 with hkdef
  set k' : UnitQuaternion := balancingGauge X R y' with hkdef'
  set A : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π =>
    k * relativeHolonomy X R (refineSite b.1) (axisPath h π) with hA
  set E : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π =>
    pathHolonomy R (refineSite b.1) (axisPath h π) *
    relativeHolonomy X R (refineSite b.1 + siteOfCoords j h) (List.replicate F.blockSide (b.2, true)) *
    (pathHolonomy R (refineSite b.1) (axisPath h π))⁻¹ with hE
  set Hh : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π =>
    pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) * ub⁻¹ with hH
  set B : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion := fun h π =>
    ub * (k' * relativeHolonomy X R (refineSite y') (axisPath h π))⁻¹ * ub⁻¹ with hB
  have hAb : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((A h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 8 * τ := by
    intro h hh π
    have := norm_coe_mul_sub_one_le k (relativeHolonomy X R (refineSite b.1) (axisPath h π))
    have h2 := hleg h hh π
    simp only [hA]
    linarith
  have hBb : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((B h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 8 * τ := by
    intro h hh π
    simp only [hB]
    rw [norm_coe_conj_sub_one, norm_coe_inv_sub_one]
    have := norm_coe_mul_sub_one_le k' (relativeHolonomy X R (refineSite y') (axisPath h π))
    have h2 := hleg' h hh π
    linarith
  have hLine : ∀ h ∈ centredCube F.blockSide,
      ‖((relativeHolonomy X R (refineSite b.1 + siteOfCoords j h) (List.replicate F.blockSide (b.2, true)) :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ τ ∧
      ‖pureComponent ((relativeHolonomy X R (refineSite b.1 + siteOfCoords j h)
          (List.replicate F.blockSide (b.2, true)) : UnitQuaternion) : ℍ[ℝ]) -
        ∑ r ∈ Finset.range F.blockSide,
          adjointAction (pathHolonomy R (refineSite b.1 + siteOfCoords j h) (List.replicate r (b.2, true)))
          (pureGap X R (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)‖ ≤ τ ^ 2 := by
    intro h hh
    obtain ⟨l1, l2⟩ := straightLine_estimate X R b.2 t ht0 F.blockSide (refineSite b.1 + siteOfCoords j h)
      (fun r hr => norm_line_link_gap_le X R b t hodd ht0 hcl h hh r hr)
    refine ⟨l1, l2.trans (le_of_eq ?_)⟩
    rw [hτdef]
    ring
  have hEb : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((E h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ τ := by
    intro h hh π
    simp only [hE]
    rw [norm_coe_conj_sub_one]
    exact (hLine h hh).1
  have hHb : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((Hh h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε := hsp
  set P : ℍ[ℝ] := gaugedContourAverage X (balancingGauge X R) b * ((ub⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hP
  have hPm : P = blockMean F.blockSide
      (fun h π => ((A h π * E h π * Hh h π * B h π : UnitQuaternion) : ℍ[ℝ])) := by
    rw [hP]
    unfold gaugedContourAverage
    rw [contourAverage_eq, mul_blockMean_mul]
    have := mul_blockMean_mul F.blockSide 1 ((ub⁻¹ : UnitQuaternion) : ℍ[ℝ]) (fun h π => (k : ℍ[ℝ]) *
      ((pathHolonomy X (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]) *
        ((k'⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    rw [one_mul] at this
    rw [this]
    unfold blockMean
    congr 1
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
    beta_reduce
    rw [one_mul, ← coe_unitQuaternion_mul, ← coe_unitQuaternion_mul, ← coe_unitQuaternion_mul]
    congr 1
    simp only [hA, hE, hH, hB, relativeHolonomy]
    have e1 := pathHolonomy_bondContour hj X b.1 b.2 h π
    have e2 := pathHolonomy_bondContour hj R b.1 b.2 h π
    rw [← hy'] at e1 e2
    rw [e1, e2]
    group
  have hpA : pureComponent (blockMean F.blockSide (fun h π => ((A h π : UnitQuaternion) : ℍ[ℝ]))) = 0 := by
    have e : blockMean F.blockSide (fun h π => ((A h π : UnitQuaternion) : ℍ[ℝ])) =
        ((‖relativePathAverage X R b.1‖ : ℝ) : ℍ[ℝ]) := by
      rw [← coe_polarUnit_inv_mul hl0, relativePathAverage_eq]
      have := mul_blockMean_mul F.blockSide (((polarUnit (blockMean F.blockSide fun h π =>
        ((relativeHolonomy X R (refineSite b.1) (axisPath h π) : UnitQuaternion) : ℍ[ℝ])))⁻¹ :
          UnitQuaternion) : ℍ[ℝ]) 1 (fun h π =>
        ((relativeHolonomy X R (refineSite b.1) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]))
      rw [mul_one] at this
      rw [this]
      simp only [mul_one]
      rfl
    rw [e, pureComponent_coe]
  have hpB : pureComponent (blockMean F.blockSide (fun h π => ((B h π : UnitQuaternion) : ℍ[ℝ]))) = 0 := by
    have e0 : blockMean F.blockSide (fun h π =>
        ((k' * relativeHolonomy X R (refineSite y') (axisPath h π) : UnitQuaternion) : ℍ[ℝ])) =
        ((‖relativePathAverage X R y'‖ : ℝ) : ℍ[ℝ]) := by
      rw [← coe_polarUnit_inv_mul hl0', relativePathAverage_eq]
      have := mul_blockMean_mul F.blockSide (((polarUnit (blockMean F.blockSide fun h π =>
        ((relativeHolonomy X R (refineSite y') (axisPath h π) : UnitQuaternion) : ℍ[ℝ])))⁻¹ :
          UnitQuaternion) : ℍ[ℝ]) 1 (fun h π =>
        ((relativeHolonomy X R (refineSite y') (axisPath h π) : UnitQuaternion) : ℍ[ℝ]))
      rw [mul_one] at this
      rw [this]
      simp only [mul_one]
      rfl
    have e : blockMean F.blockSide (fun h π => ((B h π : UnitQuaternion) : ℍ[ℝ])) =
        adjointAction ub (star (blockMean F.blockSide (fun h π =>
        ((k' * relativeHolonomy X R (refineSite y') (axisPath h π) : UnitQuaternion) : ℍ[ℝ])))) := by
      rw [star_blockMean, adjointAction_blockMean]
      rfl
    rw [e, pureComponent_adjointAction, pureComponent_star, e0, pureComponent_coe, neg_zero]
    simp [adjointAction]
  have hpH : pureComponent (blockMean F.blockSide (fun h π => ((Hh h π : UnitQuaternion) : ℍ[ℝ]))) = 0 := by
    have e : blockMean F.blockSide (fun h π => ((Hh h π : UnitQuaternion) : ℍ[ℝ])) =
        contourAverage R b * ((ub⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [contourAverage_eq]
      have := mul_blockMean_mul F.blockSide 1 ((ub⁻¹ : UnitQuaternion) : ℍ[ℝ]) (fun h π =>
        ((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) : UnitQuaternion) : ℍ[ℝ]))
      rw [one_mul] at this
      rw [this]
      simp only [one_mul]
      rfl
    rw [e]
    by_cases hq : contourAverage R b = 0
    · rw [hq, zero_mul]
      simp [pureComponent]
    · rw [hub, mul_coe_polarUnit_inv hq, pureComponent_coe]
  set Rem : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    ((A h π * E h π * Hh h π * B h π : UnitQuaternion) : ℍ[ℝ]) - 1 - (((A h π : UnitQuaternion) : ℍ[ℝ]) - 1) -
      (((E h π : UnitQuaternion) : ℍ[ℝ]) - 1) - (((Hh h π : UnitQuaternion) : ℍ[ℝ]) - 1) -
      (((B h π : UnitQuaternion) : ℍ[ℝ]) - 1) with hRem
  have hRemb : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖pureComponent (Rem h π)‖ ≤ 80 * τ * (τ + ε) := by
    intro h hh π
    refine (norm_pureComponent_le _).trans ((norm_four_product_sub_le _ _ _ _).trans ?_)
    have a := hAb h hh π
    have e := hEb h hh π
    have c := hHb h hh π
    have d := hBb h hh π
    have e0 := norm_nonneg (((E h π : UnitQuaternion) : ℍ[ℝ]) - 1)
    have d0 := norm_nonneg (((B h π : UnitQuaternion) : ℍ[ℝ]) - 1)
    have t1 : ‖((A h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ * (‖((E h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        ‖((Hh h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ + ‖((B h π : UnitQuaternion) : ℍ[ℝ]) - 1‖) ≤
        8 * τ * (τ + ε + 8 * τ) :=
      mul_le_mul a (by linarith) (by positivity) (by positivity)
    have t2 : ‖((E h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ * (‖((Hh h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        ‖((B h π : UnitQuaternion) : ℍ[ℝ]) - 1‖) ≤
        τ * (ε + 8 * τ) := mul_le_mul e (by linarith) (by positivity) hτ0
    have t3 : ‖((Hh h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖((B h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        ε * (8 * τ) :=
      mul_le_mul c d d0 hε0
    nlinarith [mul_nonneg hτ0 hε0, mul_nonneg hτ0 hτ0]
  have hdecomp : ∀ h π, pureComponent ((A h π * E h π * Hh h π * B h π : UnitQuaternion) : ℍ[ℝ]) =
      pureComponent ((A h π : UnitQuaternion) : ℍ[ℝ]) + pureComponent ((E h π : UnitQuaternion) : ℍ[ℝ]) +
        pureComponent ((Hh h π : UnitQuaternion) : ℍ[ℝ]) +
        pureComponent ((B h π : UnitQuaternion) : ℍ[ℝ]) + pureComponent (Rem h π) := by
    intro h π
    have e : ((A h π * E h π * Hh h π * B h π : UnitQuaternion) : ℍ[ℝ]) =
        Rem h π + 1 + (((A h π : UnitQuaternion) : ℍ[ℝ]) - 1) +
        (((E h π : UnitQuaternion) : ℍ[ℝ]) - 1) + (((Hh h π : UnitQuaternion) : ℍ[ℝ]) - 1) +
        (((B h π : UnitQuaternion) : ℍ[ℝ]) - 1) := by
      simp only [hRem]
      abel
    rw [e]
    simp only [pureComponent_add, pureComponent_sub, pureComponent_one, sub_zero, add_zero]
    abel
  have mA : blockMean F.blockSide (fun h π => pureComponent ((A h π : UnitQuaternion) : ℍ[ℝ])) = 0 := by
    rw [← pureComponent_blockMean]
    exact hpA
  have mB : blockMean F.blockSide (fun h π => pureComponent ((B h π : UnitQuaternion) : ℍ[ℝ])) = 0 := by
    rw [← pureComponent_blockMean]
    exact hpB
  have mH : blockMean F.blockSide (fun h π => pureComponent ((Hh h π : UnitQuaternion) : ℍ[ℝ])) = 0 := by
    rw [← pureComponent_blockMean]
    exact hpH
  have hpP : pureComponent P =
      blockMean F.blockSide (fun h π => pureComponent ((E h π : UnitQuaternion) : ℍ[ℝ])) +
      blockMean F.blockSide (fun h π => pureComponent (Rem h π)) := by
    rw [hPm, pureComponent_blockMean]
    simp only [hdecomp, blockMean_add, mA, mB, mH, zero_add, add_zero]
  set Qf : ℍ[ℝ] := parallelAverage R (pureGap X R) b with hQf
  have hEQ : ‖blockMean F.blockSide (fun h π => pureComponent ((E h π : UnitQuaternion) : ℍ[ℝ])) - Qf‖ ≤
      τ ^ 2 := by
    rw [hQf, parallelAverage_eq, ← blockMean_sub]
    refine norm_blockMean_le hodd _ _ fun h hh π => ?_
    simp only [hE]
    rw [coe_conj_eq_adjointAction, pureComponent_adjointAction, ← adjointAction_sub, norm_adjointAction]
    exact (hLine h hh).2
  have hRm : ‖blockMean F.blockSide (fun h π => pureComponent (Rem h π))‖ ≤ 80 * τ * (τ + ε) :=
    norm_blockMean_le hodd _ _ hRemb
  have hτε : 0 ≤ τ * (τ + ε) := mul_nonneg hτ0 (by linarith)
  have hD : ‖pureComponent P - Qf‖ ≤ 81 * (τ * (τ + ε)) := by
    have e : pureComponent P - Qf =
        (blockMean F.blockSide (fun h π => pureComponent ((E h π : UnitQuaternion) : ℍ[ℝ])) - Qf) +
        blockMean F.blockSide (fun h π => pureComponent (Rem h π)) := by
      rw [hpP]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith [mul_nonneg hτ0 hε0]
  have hP1 : ‖P - 1‖ ≤ 17 * τ + ε := by
    rw [hPm, ← blockMean_one hodd, ← blockMean_sub]
    refine norm_blockMean_le hodd _ _ fun h hh π => ?_
    have a := hAb h hh π
    have e := hEb h hh π
    have c := hHb h hh π
    have d := hBb h hh π
    have n1 := norm_coe_mul_sub_one_le (A h π * E h π * Hh h π) (B h π)
    have n2 := norm_coe_mul_sub_one_le (A h π * E h π) (Hh h π)
    have n3 := norm_coe_mul_sub_one_le (A h π) (E h π)
    linarith
  have hQb : ‖Qf‖ ≤ τ := by
    rw [hQf, parallelAverage_eq]
    refine norm_blockMean_le hodd _ _ fun h hh π => ?_
    rw [norm_adjointAction]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ r ∈ Finset.range F.blockSide,
        ‖adjointAction (pathHolonomy R (refineSite b.1 + siteOfCoords j h) (List.replicate r (b.2, true)))
        (pureGap X R (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)‖ ≤ t := by
      intro r hr
      rw [norm_adjointAction]
      exact (norm_pureComponent_coe_le _).trans
        (norm_line_link_gap_le X R b t hodd ht0 hcl h hh r (Finset.mem_range.1 hr))
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    simp [hτdef]
  have hPn : 41 / 50 ≤ ‖P‖ := by
    have := norm_sub_norm_le (1 : ℍ[ℝ]) P
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hPn
    linarith
  have hre : 0 ≤ P.re := by
    have h2 := quaternion_re_le_norm (1 - P)
    have h3 : (1 - P).re = 1 - P.re := by simp
    rw [h3, norm_sub_rev] at h2
    linarith
  have hm : gaugedContourAverage X (balancingGauge X R) b ≠ 0 := by
    intro h0
    exact hP0 (by rw [hP, h0, zero_mul])
  have hmean : relativeContourMean X R b = polarUnit P := by
    unfold relativeContourMean
    rw [hP, polarUnit_mul hm (coe_unitQuaternion_ne_zero _), polarUnit_coe]
  have hpure : ‖pureComponent P‖ ≤ ‖Qf‖ + 81 * (τ * (τ + ε)) := by
    have := norm_sub_norm_le (pureComponent P) Qf
    linarith
  rw [hmean]
  refine ⟨hQb, ?_, ?_⟩
  · rw [pureComponent_polarUnit hP0]
    have hinv : |‖P‖⁻¹ - 1| ≤ 2 * (17 * τ + ε) := by
      have h1 : ‖P‖⁻¹ - 1 = (1 - ‖P‖) / ‖P‖ := by
        field_simp
      have h2 : |1 - ‖P‖| ≤ ‖P - 1‖ := by
        have := abs_norm_sub_norm_le (1 : ℍ[ℝ]) P
        rw [norm_one, norm_sub_rev] at this
        exact this
      rw [h1, abs_div, abs_of_pos (by linarith : 0 < ‖P‖), div_le_iff₀ (by linarith)]
      have h3 : 0 ≤ 17 * τ + ε := by positivity
      nlinarith
    have e : ‖P‖⁻¹ • pureComponent P - Qf = (‖P‖⁻¹ - 1) • pureComponent P + (pureComponent P - Qf) := by
      rw [sub_smul, one_smul]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have hp3 : ‖pureComponent P‖ ≤ 3 * τ := by
      have : τ * (τ + ε) ≤ τ * (1 / 50) := mul_le_mul_of_nonneg_left (by linarith) hτ0
      linarith
    have hprod : |‖P‖⁻¹ - 1| * ‖pureComponent P‖ ≤ (2 * (17 * τ + ε)) * (3 * τ) :=
      mul_le_mul hinv hp3 (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg hτ0 hε0, mul_nonneg hτ0 hτ0]
  · refine (norm_polarUnit_sub_one_le hre hP0).trans ?_
    rw [div_le_iff₀ (by linarith)]
    exact real_tail_bound (norm_nonneg _) hPn hpure hτε
end Main
end ContourMean
theorem contourMeanFirstOrder : contourMeanFirstOrderStatement := by
  refine ⟨500, 1 / 100, by norm_num, by norm_num, ?_⟩
  intro F j X R b t ε hodd hj ht0 hε0 hτ hε hcl hsp
  exact ContourMean.contourAverage_estimate X R b t ε hodd hj ht0 hε0 hτ hε hcl hsp
end BlockAverages
end YangMills.Construction
end
