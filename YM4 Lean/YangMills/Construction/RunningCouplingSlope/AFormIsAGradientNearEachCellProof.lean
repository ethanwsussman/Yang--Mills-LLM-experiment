import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import YangMills.Construction.Towers.DataOfAChangeOfTheGaugeFixingAtAChainProof
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.RunningCouplingSlope.AFormIsAGradientNearEachCell
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.Towers.MapsOfTheResponseAndTheirTransposes
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.LocalGradient
open Tower
open Matrices
section Signed
variable {V : Type*} [AddCommGroup V]
private def signedTerm (m : ℤ) (i : ℕ) : ℤ := if 0 ≤ m then (i : ℤ) else -1 - (i : ℤ)
private def signedRangeSum (f : ℤ → V) (m : ℤ) : V :=
  (if 0 ≤ m then (1 : ℤ) else -1) • ∑ i ∈ Finset.range m.natAbs, f (signedTerm m i)
private theorem signedRangeSum_natCast (f : ℤ → V) (t : ℕ) :
    signedRangeSum f (t : ℤ) = ∑ i ∈ Finset.range t, f (i : ℤ) := by
  simp [signedRangeSum, signedTerm]
private theorem signedRangeSum_neg (f : ℤ → V) (t : ℕ) :
    signedRangeSum f (-(t : ℤ)) = -∑ i ∈ Finset.range t, f (-1 - (i : ℤ)) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [signedRangeSum]
  · have h : t ≠ 0 := ht.ne'
    simp [signedRangeSum, signedTerm, h]
private theorem signedRangeSum_succ (f : ℤ → V) (m : ℤ) :
    signedRangeSum f (m + 1) = signedRangeSum f m + f m := by
  rcases le_or_gt 0 m with h | h
  · lift m to ℕ using h
    have e : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [e, signedRangeSum_natCast, signedRangeSum_natCast, Finset.sum_range_succ]
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = -((t + 1 : ℕ) : ℤ) := ⟨(-m - 1).toNat, by omega⟩
    have e : -((t + 1 : ℕ) : ℤ) + 1 = -(t : ℤ) := by push_cast; ring
    rw [e, signedRangeSum_neg, signedRangeSum_neg, Finset.sum_range_succ]
    have e2 : (-1 - (t : ℤ)) = -((t + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e2]
    abel
private theorem signedRangeSum_zero (f : ℤ → V) : signedRangeSum f 0 = 0 := by
  simp [signedRangeSum]
private theorem signedRangeSum_add (f g : ℤ → V) (m : ℤ) :
    signedRangeSum (fun i => f i + g i) m = signedRangeSum f m + signedRangeSum g m := by
  simp only [signedRangeSum, Finset.sum_add_distrib, smul_add]
private theorem signedRangeSum_telescope (g : ℤ → V) (m : ℤ) :
    signedRangeSum (fun i => g (i + 1) - g i) m = g m - g 0 := by
  induction m using Int.induction_on with
  | zero => simp [signedRangeSum_zero]
  | succ t ih =>
    rw [signedRangeSum_succ, ih]
    abel
  | pred t ih =>
    have h := signedRangeSum_succ (fun i => g (i + 1) - g i) (-(t : ℤ) - 1)
    have e : -(t : ℤ) - 1 + 1 = -(t : ℤ) := by ring
    rw [e, ih] at h
    have h2 : signedRangeSum (fun i => g (i + 1) - g i) (-(t : ℤ) - 1) =
        g (-(t : ℤ)) - g 0 - (g (-(t : ℤ)) - g (-(t : ℤ) - 1)) := by
      rw [h]
      abel
    rw [h2]
    abel
end Signed
section Axial
variable {V : Type*} [AddCommGroup V]
private def axisVec (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
private def lowerCoords (ν : Fin 4) (w : Fin 4 → ℤ) : Fin 4 → ℤ := fun ρ => if ρ < ν then w ρ else 0
private def throughCoords (ν : Fin 4) (w : Fin 4 → ℤ) : Fin 4 → ℤ := fun ρ => if ρ ≤ ν then w ρ else 0
private def axisLineSum (T : (Fin 4 → ℤ) → Fin 4 → V) (ν : Fin 4) (w : Fin 4 → ℤ) : V :=
  signedRangeSum (fun i => T (lowerCoords ν w + i • axisVec ν) ν) (w ν)
private def stairSum (T : (Fin 4 → ℤ) → Fin 4 → V) (w : Fin 4 → ℤ) : V :=
  ∑ ν, axisLineSum T ν w
private def discreteCurl (T : (Fin 4 → ℤ) → Fin 4 → V) (v : Fin 4 → ℤ) (μ ν : Fin 4) : V :=
  T v μ + T (v + axisVec μ) ν - T (v + axisVec ν) μ - T v ν
private theorem throughCoords_eq (ν : Fin 4) (w : Fin 4 → ℤ) :
    lowerCoords ν w + w ν • axisVec ν = throughCoords ν w := by
  funext ρ
  simp only [lowerCoords, throughCoords, axisVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : ρ = ν
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h]
    rcases lt_or_gt_of_ne h with h' | h'
    · simp [h', h'.le]
    · simp [not_lt.2 h'.le, not_le.2 h']
private theorem axisLineSum_of_lt (T : (Fin 4 → ℤ) → Fin 4 → V) {ν μ : Fin 4} (h : ν < μ)
    (w : Fin 4 → ℤ) : axisLineSum T ν (w + axisVec μ) = axisLineSum T ν w := by
  have e1 : lowerCoords ν (w + axisVec μ) = lowerCoords ν w := by
    funext ρ
    simp only [lowerCoords, Pi.add_apply, axisVec]
    by_cases hρ : ρ < ν
    · have : ρ ≠ μ := (hρ.trans h).ne
      simp [hρ, Pi.single_eq_of_ne this]
    · simp [hρ]
  have e2 : (w + axisVec μ) ν = w ν := by
    simp [axisVec, Pi.single_eq_of_ne h.ne]
  simp only [axisLineSum, e1, e2]
private theorem axisLineSum_self (T : (Fin 4 → ℤ) → Fin 4 → V) (μ : Fin 4) (w : Fin 4 → ℤ) :
    axisLineSum T μ (w + axisVec μ) = axisLineSum T μ w + T (throughCoords μ w) μ := by
  have e1 : lowerCoords μ (w + axisVec μ) = lowerCoords μ w := by
    funext ρ
    simp only [lowerCoords, Pi.add_apply, axisVec]
    by_cases hρ : ρ < μ
    · simp [hρ, Pi.single_eq_of_ne hρ.ne]
    · simp [hρ]
  have e2 : (w + axisVec μ) μ = w μ + 1 := by simp [axisVec]
  simp only [axisLineSum, e1, e2]
  rw [signedRangeSum_succ, throughCoords_eq]
private theorem axisLineSum_of_gt (T : (Fin 4 → ℤ) → Fin 4 → V) {μ ν : Fin 4} (h : μ < ν)
    (w : Fin 4 → ℤ) :
    axisLineSum T ν (w + axisVec μ) = axisLineSum T ν w +
      signedRangeSum (fun i => discreteCurl T (lowerCoords ν w + i • axisVec ν) μ ν) (w ν) +
        T (throughCoords ν w) μ - T (lowerCoords ν w) μ := by
  have e1 : lowerCoords ν (w + axisVec μ) = lowerCoords ν w + axisVec μ := by
    funext ρ
    simp only [lowerCoords, Pi.add_apply, axisVec]
    by_cases hρ : ρ < ν
    · simp [hρ]
    · have : ρ ≠ μ := fun e => hρ (e ▸ h)
      simp [hρ, Pi.single_eq_of_ne this]
  have e2 : (w + axisVec μ) ν = w ν := by
    simp [axisVec, Pi.single_eq_of_ne h.ne']
  set g : ℤ → V := fun i => T (lowerCoords ν w + i • axisVec ν) μ with hg
  have e3 : ∀ i : ℤ, T (lowerCoords ν w + axisVec μ + i • axisVec ν) ν =
      T (lowerCoords ν w + i • axisVec ν) ν + discreteCurl T (lowerCoords ν w + i • axisVec ν) μ ν +
        (g (i + 1) - g i) := by
    intro i
    have a1 : lowerCoords ν w + axisVec μ + i • axisVec ν =
        lowerCoords ν w + i • axisVec ν + axisVec μ := by
      abel
    have a2 : lowerCoords ν w + (i + 1) • axisVec ν =
        lowerCoords ν w + i • axisVec ν + axisVec ν := by
      rw [add_smul, one_smul]
      abel
    simp only [discreteCurl, hg, a1, a2]
    abel
  simp only [axisLineSum, e1, e2, e3]
  rw [signedRangeSum_add, signedRangeSum_add, signedRangeSum_telescope]
  have e4 : g (w ν) = T (throughCoords ν w) μ := by simp only [hg, throughCoords_eq]
  have e5 : g 0 = T (lowerCoords ν w) μ := by simp [hg]
  rw [e4, e5]
  abel
private theorem throughCoords_eq_lowerCoords_succ :
    (throughCoords 0 = lowerCoords 1) ∧ (throughCoords 1 = lowerCoords 2) ∧
      (throughCoords 2 = lowerCoords 3) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · funext w ρ
    fin_cases ρ <;> simp [throughCoords, lowerCoords]
private theorem throughCoords_last (w : Fin 4 → ℤ) : throughCoords 3 w = w := by
  funext ρ
  have : ρ ≤ 3 := Fin.le_last ρ
  simp [throughCoords, this]
private theorem stairSum_step (T : (Fin 4 → ℤ) → Fin 4 → V) (w : Fin 4 → ℤ) (μ : Fin 4) :
    stairSum T (w + axisVec μ) - stairSum T w = T w μ +
      ∑ ν ∈ Finset.Ioi μ,
        signedRangeSum (fun i => discreteCurl T (lowerCoords ν w + i • axisVec ν) μ ν) (w ν) := by
  obtain ⟨u0, u1, u2⟩ := throughCoords_eq_lowerCoords_succ
  have u3 := throughCoords_last w
  have l01 : (0 : Fin 4) < 1 := by decide
  have l02 : (0 : Fin 4) < 2 := by decide
  have l03 : (0 : Fin 4) < 3 := by decide
  have l12 : (1 : Fin 4) < 2 := by decide
  have l13 : (1 : Fin 4) < 3 := by decide
  have l23 : (2 : Fin 4) < 3 := by decide
  simp only [stairSum, Fin.sum_univ_four]
  fin_cases μ
  · have i0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
    simp only [Fin.zero_eta, i0]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [axisLineSum_self T 0 w, axisLineSum_of_gt T l01 w, axisLineSum_of_gt T l02 w,
      axisLineSum_of_gt T l03 w, u3]
    simp only [u0, u1, u2]
    abel
  · have i1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
    simp only [Fin.mk_one, i1]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [axisLineSum_of_lt T l01 w, axisLineSum_self T 1 w, axisLineSum_of_gt T l12 w,
      axisLineSum_of_gt T l13 w, u3]
    simp only [u1, u2]
    abel
  · have i2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
    simp only [Fin.reduceFinMk, i2, Finset.sum_singleton]
    rw [axisLineSum_of_lt T l02 w, axisLineSum_of_lt T l12 w, axisLineSum_self T 2 w,
      axisLineSum_of_gt T l23 w, u3]
    simp only [u2]
    abel
  · have i3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
    simp only [Fin.reduceFinMk, i3, Finset.sum_empty]
    rw [axisLineSum_of_lt T l03 w, axisLineSum_of_lt T l13 w, axisLineSum_of_lt T l23 w,
      axisLineSum_self T 3 w, u3]
    abel
end Axial
section Squares
private def halfTraceSq (X : ComplexMatrix2) : ℝ := (ComplexMatrix2.halfTrace (X * X)).re
private def halfFrobSq (X : ComplexMatrix2) : ℝ :=
  (‖X 0 0‖ ^ 2 + ‖X 0 1‖ ^ 2 + ‖X 1 0‖ ^ 2 + ‖X 1 1‖ ^ 2) / 2
private theorem halfTraceSq_eq_halfFrobSq {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : halfTraceSq X = halfFrobSq X := by
  obtain ⟨hH, -⟩ := hX
  have e00 : X 0 0 = star (X 0 0) := congrFun (congrFun hH 0) 0
  have e11 : X 1 1 = star (X 1 1) := congrFun (congrFun hH 1) 1
  have e10 : X 1 0 = star (X 0 1) := congrFun (congrFun hH 1) 0
  have i0 : (X 0 0).im = 0 := by
    have := congrArg Complex.im e00
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have i1 : (X 1 1).im = 0 := by
    have := congrArg Complex.im e11
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have r1 : (X 1 0).re = (X 0 1).re := by
    have := congrArg Complex.re e10
    simpa using this
  have m1 : (X 1 0).im = -(X 0 1).im := by
    have := congrArg Complex.im e10
    simpa using this
  simp only [halfTraceSq, halfFrobSq, ComplexMatrix2.halfTrace, Complex.sq_norm,
    Complex.normSq_apply]
  simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im, i0, i1, r1, m1]
  ring
private theorem norm_finsetSum_sq_le {ι : Type*} (T : Finset ι) (a : ι → ℂ) :
    ‖∑ i ∈ T, a i‖ ^ 2 ≤ T.card * ∑ i ∈ T, ‖a i‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq
private theorem halfTraceSq_sum_le {ι : Type*} (T : Finset ι) (f : ι → ComplexMatrix2)
    (hf : ∀ i ∈ T, f i ∈ ComplexMatrix2.hermitianTraceless) :
    halfTraceSq (∑ i ∈ T, f i) ≤ T.card * ∑ i ∈ T, halfTraceSq (f i) := by
  rw [halfTraceSq_eq_halfFrobSq (Submodule.sum_mem _ hf),
    Finset.sum_congr rfl fun i hi => halfTraceSq_eq_halfFrobSq (hf i hi)]
  simp only [halfFrobSq, Matrix.sum_apply]
  have h1 := norm_finsetSum_sq_le T fun i => f i 0 0
  have h2 := norm_finsetSum_sq_le T fun i => f i 0 1
  have h3 := norm_finsetSum_sq_le T fun i => f i 1 0
  have h4 := norm_finsetSum_sq_le T fun i => f i 1 1
  have e : ∑ i ∈ T, (‖f i 0 0‖ ^ 2 + ‖f i 0 1‖ ^ 2 + ‖f i 1 0‖ ^ 2 + ‖f i 1 1‖ ^ 2) / 2 =
      (∑ i ∈ T, ‖f i 0 0‖ ^ 2 + ∑ i ∈ T, ‖f i 0 1‖ ^ 2 + ∑ i ∈ T, ‖f i 1 0‖ ^ 2 +
        ∑ i ∈ T, ‖f i 1 1‖ ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [e]
  linarith
private theorem halfTraceSq_nonneg {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : 0 ≤ halfTraceSq X := by apply _root_.YangMills.DeltaSharedProofs.p2944 <;> assumption
private theorem halfTraceSq_neg (X : ComplexMatrix2) : halfTraceSq (-X) = halfTraceSq X := by
  simp [halfTraceSq]
private theorem halfTraceSq_sub_sub_le {x y w : ComplexMatrix2}
    (hx : x ∈ ComplexMatrix2.hermitianTraceless) (hy : y ∈ ComplexMatrix2.hermitianTraceless)
    (hw : w ∈ ComplexMatrix2.hermitianTraceless) :
    halfTraceSq (x - (y - w)) ≤ 3 * (halfTraceSq x + halfTraceSq y + halfTraceSq w) := by
  have h := halfTraceSq_sum_le (Finset.univ : Finset (Fin 3)) ![x, -y, w] (by
    intro i _
    fin_cases i
    · exact hx
    · exact ComplexMatrix2.hermitianTraceless.neg_mem hy
    · exact hw)
  simp only [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, halfTraceSq_neg] at h
  have e : x - (y - w) = x + -y + w := by abel
  rw [e]
  push_cast at h
  exact h
private theorem signedRangeSum_mem (f : ℤ → ComplexMatrix2)
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) (m : ℤ) :
    signedRangeSum f m ∈ ComplexMatrix2.hermitianTraceless := by
  simp only [signedRangeSum]
  split_ifs
  · simpa using Submodule.sum_mem _ fun i _ => hf _
  · simpa using ComplexMatrix2.hermitianTraceless.neg_mem (Submodule.sum_mem _ fun i _ => hf _)
private theorem halfTraceSq_signedRangeSum (f : ℤ → ComplexMatrix2)
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) (m : ℤ) :
    halfTraceSq (signedRangeSum f m) ≤
      m.natAbs * ∑ i ∈ Finset.range m.natAbs, halfTraceSq (f (signedTerm m i)) := by
  have h := halfTraceSq_sum_le (Finset.range m.natAbs) (fun i => f (signedTerm m i))
    fun i _ => hf _
  rw [Finset.card_range] at h
  simp only [signedRangeSum]
  split_ifs
  · simpa using h
  · simpa [halfTraceSq_neg] using h
end Squares
section Coordinates
variable {L n k : ℕ}
private def ofCoords (w : Fin 4 → ℤ) : Vertex L n k 0 :=
  ∑ μ, w μ • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ
private theorem ofCoords_add (w w' : Fin 4 → ℤ) :
    ofCoords (L := L) (n := n) (k := k) (w + w') = ofCoords w + ofCoords w' := by
  simp [ofCoords, add_smul, Finset.sum_add_distrib]
private theorem ofCoords_axisVec (μ : Fin 4) :
    ofCoords (L := L) (n := n) (k := k) (axisVec μ) =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ := by
  simp [ofCoords, axisVec, Pi.single_apply, ite_smul]
private def halfWidth (L n k : ℕ) : ℕ :=
  PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k 0)
private def coordBox (H : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ioc (-(H : ℤ)) (H : ℤ)
private theorem mem_coordBox {H : ℕ} {w : Fin 4 → ℤ} :
    w ∈ coordBox H ↔ ∀ μ, -(H : ℤ) < w μ ∧ w μ ≤ H := by
  simp [coordBox, Fintype.mem_piFinset, Finset.mem_Ioc]
private theorem sublatticeCoordinates_fine (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k 0) :=
  (hc L n hL.1 hL.2 hn).1 _ (by simp only [PeriodicLattice.levelDepth]; omega)
private theorem exists_coords (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (d : Vertex L n k 0) :
    ∃ w ∈ coordBox (halfWidth L n k), d = ofCoords w := by
  obtain ⟨-, c2, -, c4, c5, -⟩ := sublatticeCoordinates_fine (k := k) hc hL hn
  obtain ⟨m, hm⟩ := c4 0 d
  set H : ℤ := (halfWidth L n k : ℤ) with hH
  have hN : (((2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k 0) : ℕ)) : ℤ) =
      2 * H := by
    simp [hH, halfWidth]
  have hH0 : 0 < H := by
    have : (0 : ℤ) <
        ((2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k 0) : ℕ) : ℤ) := by
      exact_mod_cast c2
    omega
  refine ⟨fun μ => (m μ + H - 1) % (2 * H) - H + 1, mem_coordBox.2 fun μ => ?_, ?_⟩
  · have h1 := Int.emod_nonneg (m μ + H - 1) (show 2 * H ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos (m μ + H - 1) (show 0 < 2 * H by omega)
    constructor <;> omega
  · have e := (c5 0 (fun μ => (m μ + H - 1) % (2 * H) - H + 1) m).2 fun μ => by
      rw [hN]
      refine (Int.modEq_iff_dvd).2 ⟨(m μ + H - 1) / (2 * H), ?_⟩
      have := Int.emod_add_mul_ediv (m μ + H - 1) (2 * H)
      linarith
    rw [hm, ← e]
    simp [PeriodicLattice.offsetSite, ofCoords]
private theorem coords_unique (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {w w' : Fin 4 → ℤ}
    (hw : w ∈ coordBox (halfWidth L n k)) (hw' : w' ∈ coordBox (halfWidth L n k))
    (h : ofCoords (L := L) (n := n) (k := k) w = ofCoords w') : w = w' := by
  obtain ⟨-, -, -, -, c5, -⟩ := sublatticeCoordinates_fine (k := k) hc hL hn
  have e := (c5 0 w w').1 (by simpa [PeriodicLattice.offsetSite, ofCoords] using h)
  funext μ
  have b := mem_coordBox.1 hw μ
  have b' := mem_coordBox.1 hw' μ
  have hN : (((2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k 0) : ℕ)) : ℤ) =
      2 * (halfWidth L n k : ℤ) := by
    simp [halfWidth]
  have hd := Int.modEq_iff_dvd.1 (show w μ ≡ w' μ [ZMOD _] from e μ)
  rw [hN] at hd
  have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  omega
private def coordsOf (d : Vertex L n k 0) : Fin 4 → ℤ :=
  Classical.epsilon fun w => w ∈ coordBox (halfWidth L n k) ∧ d = ofCoords w
private theorem coordsOf_spec (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (d : Vertex L n k 0) :
    coordsOf d ∈ coordBox (halfWidth L n k) ∧ d = ofCoords (coordsOf d) := by
  obtain ⟨w, hw, e⟩ := exists_coords (k := k) hc hL hn d
  exact Classical.epsilon_spec
    (p := fun w => w ∈ coordBox (halfWidth L n k) ∧ d = ofCoords w) ⟨w, hw, e⟩
private theorem coordsOf_ofCoords (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {w : Fin 4 → ℤ}
    (hw : w ∈ coordBox (halfWidth L n k)) :
    coordsOf (ofCoords (L := L) (n := n) (k := k) w) = w := by
  obtain ⟨h1, h2⟩ := coordsOf_spec (k := k) hc hL hn (ofCoords w)
  exact coords_unique hc hL hn h1 hw h2.symm
end Coordinates
section Cells
variable {L n k : ℕ}
open TorusMetric
private theorem meshSize_top (L k : ℕ) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private def fineVertex (y : Vertex L n k k) : Vertex L n k 0 :=
  y.toSublattice (PeriodicLattice.levelDepth k 0)
private theorem coe_fineVertex (hL : 0 < L) (y : Vertex L n k k) :
    ((fineVertex y : Vertex L n k 0) : PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.Construction.Tower.TransferAlongChain.coe_toSublattice_levelDepth <;> assumption
private theorem fineVertex_injective (hL : 0 < L) :
    Function.Injective (fineVertex (L := L) (n := n) (k := k)) := fun y y' h =>
  Subtype.ext (by rw [← coe_fineVertex hL y, ← coe_fineVertex hL y', h])
private theorem norm_sub_fineVertexCell_le (hcell : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (x : Vertex L n k 0) (μ : Fin 4) :
    ‖((x : PeriodicLattice.FourTorus L n) -
      (fineVertexCell (L := L) (n := n) (k := k) x : PeriodicLattice.FourTorus L n)) μ‖ ≤
        1 / 2 := by
  have h := ((hcell L hL n k).2.2.1 x).1
  change torusSupNorm _ ≤ _ at h
  rw [SeparatedSequence.torusSupNorm_le_iff, meshSize_top] at h
  exact h μ
private theorem coe_ofCoords (w : Fin 4 → ℤ) (μ : Fin 4) :
    ((ofCoords (L := L) (n := n) (k := k) w : Vertex L n k 0) :
      PeriodicLattice.FourTorus L n) μ =
      (((w μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L n)) := by
  have e : ∀ ν, ((w ν • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν :
      Vertex L n k 0) : PeriodicLattice.FourTorus L n) μ =
      if ν = μ then (((w μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L n)) else 0 := by
    intro ν
    by_cases h : ν = μ
    · subst h
      simp only [AddSubgroup.coe_zsmul, Pi.smul_apply, PeriodicLattice.unitStep,
        PeriodicLattice.pointOnAxis, Pi.single_eq_same, if_true]
      rw [← zsmul_eq_mul, ← QuotientAddGroup.mk_zsmul]
    · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, h]
  simp only [ofCoords, AddSubgroup.val_finsetSum, Finset.sum_apply, e]
  simp
private theorem norm_coe_ofCoords {ℓ : ℝ}
    (hℓ : ℓ = PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0))
    (hℓ0 : 0 < ℓ) (hside : PeriodicLattice.torusSide L n = 2 * (halfWidth L n k : ℝ) * ℓ)
    {w : Fin 4 → ℤ} (hw : w ∈ coordBox (halfWidth L n k)) (μ : Fin 4) :
    ‖((ofCoords (L := L) (n := n) (k := k) w : Vertex L n k 0) :
      PeriodicLattice.FourTorus L n) μ‖ = ℓ * |(w μ : ℝ)| := by
  have hs : 0 < PeriodicLattice.torusSide L n := by
    rcases Nat.eq_zero_or_pos (halfWidth L n k) with h0 | h0
    · have := mem_coordBox.1 hw μ
      omega
    · rw [hside]
      have : (0 : ℝ) < (halfWidth L n k : ℝ) := by exact_mod_cast h0
      positivity
  rw [coe_ofCoords, ← hℓ, (AddCircle.norm_coe_eq_abs_iff _ hs.ne').2, abs_mul, abs_of_pos hℓ0,
    mul_comm]
  · rw [abs_mul, abs_of_pos hℓ0, abs_of_pos hs, hside]
    have b := mem_coordBox.1 hw μ
    have h1 : |(w μ : ℝ)| ≤ (halfWidth L n k : ℝ) := by
      rw [abs_le]
      constructor
      · have : -(halfWidth L n k : ℤ) ≤ w μ := b.1.le
        exact_mod_cast this
      · exact_mod_cast b.2
    nlinarith [mul_le_mul_of_nonneg_right h1 hℓ0.le]
private theorem cellDist_ge (hcell : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {ℓ : ℝ}
    (hℓ : ℓ = PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0)) (hℓ0 : 0 < ℓ)
    (hside : PeriodicLattice.torusSide L n = 2 * (halfWidth L n k : ℝ) * ℓ)
    {w : Fin 4 → ℤ} (hw : w ∈ coordBox (halfWidth L n k)) (y : Vertex L n k k) :
    ℓ * (∑ μ, |(w μ : ℝ)|) / 4 - 1 / 2 ≤
      cellDist (fineVertexCell (fineVertex y + ofCoords w)) y := by
  have hL0 : 0 < L := by have := hL.2; omega
  set x : Vertex L n k 0 := fineVertex y + ofCoords w with hx
  set c := fineVertexCell (L := L) (n := n) (k := k) x with hc
  have key : ∀ μ, ℓ * |(w μ : ℝ)| ≤ 1 / 2 + cellDist c y := by
    intro μ
    have h1 := norm_sub_fineVertexCell_le (k := k) hcell hL x μ
    have h2 : ‖((c : PeriodicLattice.FourTorus L n) - y) μ‖ ≤ cellDist c y := by
      unfold cellDist
      rw [AmbientPoints.torusEuclidNorm_eq_sqrt, ← abs_of_nonneg (norm_nonneg _)]
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum
        (f := fun i => ‖((c : PeriodicLattice.FourTorus L n) - y) i‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ μ)
    have e : ((ofCoords (L := L) (n := n) (k := k) w : Vertex L n k 0) :
        PeriodicLattice.FourTorus L n) μ =
        ((x : PeriodicLattice.FourTorus L n) - c) μ + ((c : PeriodicLattice.FourTorus L n) - y) μ := by
      have : (x : PeriodicLattice.FourTorus L n) = y + (ofCoords w : Vertex L n k 0) := by
        rw [hx, AddSubgroup.coe_add, coe_fineVertex hL0]
      simp only [Pi.sub_apply, this, Pi.add_apply]
      abel
    rw [← norm_coe_ofCoords hℓ hℓ0 hside hw μ, e]
    exact (norm_add_le _ _).trans (by linarith)
  have := key 0
  have := key 1
  have := key 2
  have := key 3
  rw [Fin.sum_univ_four]
  nlinarith
end Cells
section Lift
variable {L n k : ℕ}
open PeriodicLattice (Bond.forwardFrom)
private def liftedForm (A : Edge L n k 0 → ComplexMatrix2) (x₀ : Vertex L n k 0) :
    (Fin 4 → ℤ) → Fin 4 → ComplexMatrix2 :=
  fun w μ => A (PeriodicLattice.Bond.forwardFrom (x₀ + ofCoords w) μ)
private theorem forwardFrom_isPositivelyOriented (x : Vertex L n k 0) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
private theorem form_forwardFrom_mem (A : edgeFormSpace L n k 0) (x : Vertex L n k 0) (μ : Fin 4) :
    (A : Edge L n k 0 → ComplexMatrix2) (PeriodicLattice.Bond.forwardFrom x μ) ∈
      ComplexMatrix2.hermitianTraceless :=
  A.2.1 _ (forwardFrom_isPositivelyOriented x μ)
private theorem liftedForm_mem (A : edgeFormSpace L n k 0) (x₀ : Vertex L n k 0)
    (w : Fin 4 → ℤ) (μ : Fin 4) :
    liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀ w μ ∈ ComplexMatrix2.hermitianTraceless :=
  form_forwardFrom_mem A _ μ
private theorem discreteCurl_liftedForm (A : Edge L n k 0 → ComplexMatrix2) (x₀ : Vertex L n k 0)
    (v : Fin 4 → ℤ) {μ ν : Fin 4} (h : μ < ν) :
    discreteCurl (liftedForm A x₀) v μ ν = edgeCoboundary A ⟨x₀ + ofCoords v, μ, ν, h⟩ := by
  simp only [discreteCurl, liftedForm, edgeCoboundary, ofCoords_add, ofCoords_axisVec, add_assoc]
private theorem edgeCoboundary_mem (A : edgeFormSpace L n k 0) (p : Face L n k 0) :
    edgeCoboundary (A : Edge L n k 0 → ComplexMatrix2) p ∈ ComplexMatrix2.hermitianTraceless :=
  ComplexMatrix2.hermitianTraceless.sub_mem
    (ComplexMatrix2.hermitianTraceless.sub_mem
      (ComplexMatrix2.hermitianTraceless.add_mem (form_forwardFrom_mem A _ _)
        (form_forwardFrom_mem A _ _))
      (form_forwardFrom_mem A _ _)) (form_forwardFrom_mem A _ _)
private theorem discreteCurl_mem (A : edgeFormSpace L n k 0) (x₀ : Vertex L n k 0)
    (v : Fin 4 → ℤ) {μ ν : Fin 4} (h : μ < ν) :
    discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀) v μ ν ∈
      ComplexMatrix2.hermitianTraceless := by
  rw [discreteCurl_liftedForm _ _ _ h]
  exact edgeCoboundary_mem A _
private def stairPotential (A : Edge L n k 0 → ComplexMatrix2) (x₀ : Vertex L n k 0) :
    Vertex L n k 0 → ComplexMatrix2 :=
  fun x => stairSum (liftedForm A x₀) (coordsOf (x - x₀))
private theorem axisLineSum_mem (A : edgeFormSpace L n k 0) (x₀ : Vertex L n k 0) (ν : Fin 4)
    (w : Fin 4 → ℤ) :
    axisLineSum (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀) ν w ∈
      ComplexMatrix2.hermitianTraceless :=
  signedRangeSum_mem _ (fun _ => liftedForm_mem A x₀ _ ν) _
private theorem stairSum_mem (A : edgeFormSpace L n k 0) (x₀ : Vertex L n k 0) (w : Fin 4 → ℤ) :
    stairSum (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀) w ∈
      ComplexMatrix2.hermitianTraceless :=
  Submodule.sum_mem _ fun ν _ => axisLineSum_mem A x₀ ν w
private theorem stairPotential_mem (A : edgeFormSpace L n k 0) (x₀ x : Vertex L n k 0) :
    stairPotential (A : Edge L n k 0 → ComplexMatrix2) x₀ x ∈ ComplexMatrix2.hermitianTraceless :=
  stairSum_mem A x₀ _
private theorem stairPotential_add_ofCoords (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (A : Edge L n k 0 → ComplexMatrix2)
    (x₀ : Vertex L n k 0) {w : Fin 4 → ℤ} (hw : w ∈ coordBox (halfWidth L n k)) :
    stairPotential A x₀ (x₀ + ofCoords w) = stairSum (liftedForm A x₀) w := by
  simp only [stairPotential, add_sub_cancel_left]
  rw [coordsOf_ofCoords hc hL hn hw]
private theorem form_sub_vertexCoboundary_eq (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (A : Edge L n k 0 → ComplexMatrix2)
    (x₀ : Vertex L n k 0) {w : Fin 4 → ℤ} {μ : Fin 4} (hw : w ∈ coordBox (halfWidth L n k))
    (hw' : w + axisVec μ ∈ coordBox (halfWidth L n k)) :
    A (PeriodicLattice.Bond.forwardFrom (x₀ + ofCoords w) μ) -
        vertexCoboundary (stairPotential A x₀)
          (PeriodicLattice.Bond.forwardFrom (x₀ + ofCoords w) μ) =
      -∑ ν ∈ Finset.Ioi μ,
        signedRangeSum
          (fun i => discreteCurl (liftedForm A x₀) (lowerCoords ν w + i • axisVec ν) μ ν) (w ν) := by
  have e : (PeriodicLattice.Bond.forwardFrom (x₀ + ofCoords w) μ).target =
      x₀ + ofCoords (w + axisVec μ) := by
    simp [PeriodicLattice.Bond.forwardFrom, ofCoords_add, ofCoords_axisVec, add_assoc]
  have e' : (PeriodicLattice.Bond.forwardFrom (x₀ + ofCoords w) μ).source = x₀ + ofCoords w := rfl
  simp only [vertexCoboundary]
  rw [e, e', stairPotential_add_ofCoords hc hL hn A x₀ hw,
    stairPotential_add_ofCoords hc hL hn A x₀ hw', stairSum_step]
  change liftedForm A x₀ w μ - _ = _
  abel
private theorem halfTraceSq_remainder_le (A : edgeFormSpace L n k 0) (w : Fin 4 → ℤ)
    (x₀ : Vertex L n k 0) (μ : Fin 4) :
    halfTraceSq (-∑ ν ∈ Finset.Ioi μ, signedRangeSum
        (fun i => discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀)
          (lowerCoords ν w + i • axisVec ν) μ ν)
        (w ν)) ≤
      4 * ∑ ν ∈ Finset.Ioi μ, ((w ν).natAbs : ℝ) * ∑ i ∈ Finset.range (w ν).natAbs,
        halfTraceSq (discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀)
          (lowerCoords ν w + signedTerm (w ν) i • axisVec ν) μ ν) := by
  rw [halfTraceSq_neg]
  have hmem : ∀ ν ∈ Finset.Ioi μ, ∀ i : ℤ,
      discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀)
        (lowerCoords ν w + i • axisVec ν) μ ν ∈ ComplexMatrix2.hermitianTraceless :=
    fun ν hν i => discreteCurl_mem A x₀ _ (Finset.mem_Ioi.1 hν)
  have h1 := halfTraceSq_sum_le (Finset.Ioi μ) (fun ν => signedRangeSum
    (fun i => discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀)
      (lowerCoords ν w + i • axisVec ν) μ ν) (w ν))
    fun ν hν => signedRangeSum_mem _ (hmem ν hν) _
  have hcard : ((Finset.Ioi μ).card : ℝ) ≤ 4 := by
    have := Finset.card_le_univ (Finset.Ioi μ)
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hnn : ∀ ν ∈ Finset.Ioi μ, 0 ≤ halfTraceSq (signedRangeSum
      (fun i => discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀)
        (lowerCoords ν w + i • axisVec ν) μ ν)
      (w ν)) := fun ν hν => halfTraceSq_nonneg (signedRangeSum_mem _ (hmem ν hν) _)
  refine h1.trans ?_
  calc _ ≤ 4 * ∑ ν ∈ Finset.Ioi μ, halfTraceSq (signedRangeSum
        (fun i => discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀)
          (lowerCoords ν w + i • axisVec ν) μ ν)
        (w ν)) := mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg hnn)
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ν hν => ?_) (by norm_num)
      exact halfTraceSq_signedRangeSum _ (hmem ν hν) _
end Lift
section Box
private theorem summable_exp_neg_mul_abs {r : ℝ} (hr : 0 < r) :
    Summable fun t : ℤ => Real.exp (-(r * |(t : ℝ)|)) := by apply _root_.YangMills.SharedProofs.p3695 <;> assumption
private theorem exists_coordBox_sum_exp_le {r : ℝ} (hr : 0 < r) : ∃ D : ℝ, 0 ≤ D ∧ ∀ H : ℕ,
    ∑ w ∈ coordBox H, Real.exp (-(r * ∑ μ, |(w μ : ℝ)|)) ≤ D := by
  set g : ℤ → ℝ := fun t => Real.exp (-(r * |(t : ℝ)|)) with hg
  have hg0 : ∀ t, 0 ≤ g t := fun t => (Real.exp_pos _).le
  have hs : Summable g := summable_exp_neg_mul_abs hr
  refine ⟨(∑' t, g t) ^ 4, pow_nonneg (tsum_nonneg hg0) 4, fun H => ?_⟩
  have e : ∀ w : Fin 4 → ℤ, Real.exp (-(r * ∑ μ, |(w μ : ℝ)|)) = ∏ μ, g (w μ) := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp only [e, coordBox]
  rw [← Finset.prod_univ_sum]
  have h1 : ∀ μ ∈ (Finset.univ : Finset (Fin 4)),
      ∑ t ∈ Finset.Ioc (-(H : ℤ)) (H : ℤ), g t ≤ ∑' t, g t :=
    fun _ _ => hs.sum_le_tsum _ fun t _ => hg0 t
  calc _ ≤ ∏ _μ : Fin 4, ∑' t, g t :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun t _ => hg0 t) h1
    _ = _ := by simp
private theorem card_coordBox (H : ℕ) : (coordBox H).card = (2 * H) ^ 4 := by
  simp only [coordBox, Fintype.card_piFinset, Int.card_Ioc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega
private theorem sq_mul_exp_neg_le {κ x : ℝ} (hκ : 0 < κ) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-(κ * x)) ≤ 8 / κ ^ 2 * Real.exp (-(κ / 2 * x)) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (x := κ / 2 * x) (by positivity)
  have h2 : (κ / 2 * x) ^ 2 / 2 ≤ Real.exp (κ / 2 * x) := by nlinarith [mul_nonneg hκ.le hx]
  have h3 : x ^ 2 ≤ 8 / κ ^ 2 * Real.exp (κ / 2 * x) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have e2 : Real.exp (-(κ / 2 * x)) = Real.exp (κ / 2 * x) * Real.exp (-(κ * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
end Box
section Sums
variable {L n k : ℕ}
private theorem sum_halfTraceSq_discreteCurl_le [Fintype (Vertex L n k k)] [Fintype (Face L n k 0)]
    (hL0 : 0 < L) (A : edgeFormSpace L n k 0) (v : Fin 4 → ℤ) {μ ν : Fin 4} (h : μ < ν) :
    ∑ y : Vertex L n k k,
        halfTraceSq (discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) (fineVertex y))
          v μ ν) ≤
      ∑ p : Face L n k 0, halfTraceSq (edgeCoboundary (A : Edge L n k 0 → ComplexMatrix2) p) := by
  classical
  set g : Vertex L n k k → Face L n k 0 := fun y => ⟨fineVertex y + ofCoords v, μ, ν, h⟩ with hg
  have hinj : Function.Injective g := by
    intro y y' e
    have := congrArg PeriodicLattice.Plaquette.origin e
    exact fineVertex_injective hL0 (add_right_cancel this)
  calc _ = ∑ y, halfTraceSq (edgeCoboundary (A : Edge L n k 0 → ComplexMatrix2) (g y)) :=
        Finset.sum_congr rfl fun y _ => by rw [discreteCurl_liftedForm _ _ _ h]
    _ = ∑ p ∈ Finset.univ.image g,
          halfTraceSq (edgeCoboundary (A : Edge L n k 0 → ComplexMatrix2) p) :=
        (Finset.sum_image
          (f := fun p => halfTraceSq (edgeCoboundary (A : Edge L n k 0 → ComplexMatrix2) p))
          fun a _ b _ e => hinj e).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun p _ _ => halfTraceSq_nonneg (edgeCoboundary_mem A p)
private theorem halfTraceSq_form_le [Fintype (PositiveEdge L n k 0)] (A : edgeFormSpace L n k 0)
    (x : Vertex L n k 0) (μ : Fin 4) :
    halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) (PeriodicLattice.Bond.forwardFrom x μ)) ≤
      ∑ b : PositiveEdge L n k 0, halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) b.1) := by
  set b₀ : PositiveEdge L n k 0 :=
    ⟨PeriodicLattice.Bond.forwardFrom x μ, forwardFrom_isPositivelyOriented x μ⟩ with hb₀
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b : PositiveEdge L n k 0 => halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) b.1))
    (fun b _ => halfTraceSq_nonneg (A.2.1 _ b.2)) (Finset.mem_univ b₀)
  exact h
private theorem halfTraceSq_stairSum_le [Fintype (PositiveEdge L n k 0)] (A : edgeFormSpace L n k 0)
    (x₀ : Vertex L n k 0) {w : Fin 4 → ℤ} (hw : w ∈ coordBox (halfWidth L n k)) :
    halfTraceSq (stairSum (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀) w) ≤
      16 * (halfWidth L n k : ℝ) ^ 2 *
        ∑ b : PositiveEdge L n k 0, halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) b.1) := by
  set S := ∑ b : PositiveEdge L n k 0, halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) b.1)
    with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => halfTraceSq_nonneg (A.2.1 _ b.2)
  have hline : ∀ ν, halfTraceSq (axisLineSum (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀) ν w) ≤
      (halfWidth L n k : ℝ) ^ 2 * S := by
    intro ν
    have hb : ((w ν).natAbs : ℝ) ≤ (halfWidth L n k : ℝ) := by
      have b := mem_coordBox.1 hw ν
      have : (w ν).natAbs ≤ halfWidth L n k := by omega
      exact_mod_cast this
    refine (halfTraceSq_signedRangeSum _ (fun _ => liftedForm_mem A x₀ _ ν) _).trans ?_
    have h1 : ∑ i ∈ Finset.range (w ν).natAbs,
        halfTraceSq (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀
          (lowerCoords ν w + signedTerm (w ν) i • axisVec ν) ν) ≤ ((w ν).natAbs : ℝ) * S := by
      refine (Finset.sum_le_card_nsmul _ _ S fun i _ => halfTraceSq_form_le A _ ν).trans ?_
      simp
    calc _ ≤ ((w ν).natAbs : ℝ) * (((w ν).natAbs : ℝ) * S) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ ≤ (halfWidth L n k : ℝ) * ((halfWidth L n k : ℝ) * S) := by gcongr
      _ = _ := by ring
  have h2 := halfTraceSq_sum_le (Finset.univ : Finset (Fin 4))
    (fun ν => axisLineSum (liftedForm (A : Edge L n k 0 → ComplexMatrix2) x₀) ν w)
    fun ν _ => axisLineSum_mem A x₀ ν w
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  refine h2.trans ?_
  rw [Fin.sum_univ_four]
  have := hline 0
  have := hline 1
  have := hline 2
  have := hline 3
  push_cast
  linarith
private theorem halfTraceSq_form_sub_vertexCoboundary_le [Fintype (PositiveEdge L n k 0)]
    (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (A : edgeFormSpace L n k 0)
    (x₀ x : Vertex L n k 0) (μ : Fin 4) :
    halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) (PeriodicLattice.Bond.forwardFrom x μ) -
        vertexCoboundary (stairPotential (A : Edge L n k 0 → ComplexMatrix2) x₀)
          (PeriodicLattice.Bond.forwardFrom x μ)) ≤
      3 * (1 + 32 * (halfWidth L n k : ℝ) ^ 2) *
        ∑ b : PositiveEdge L n k 0, halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) b.1) := by
  simp only [vertexCoboundary]
  refine (halfTraceSq_sub_sub_le (form_forwardFrom_mem A _ _) (stairPotential_mem A x₀ _)
    (stairPotential_mem A x₀ _)).trans ?_
  have h1 := halfTraceSq_form_le A x μ
  have h2 := halfTraceSq_stairSum_le A x₀ (coordsOf_spec (k := k) hc hL hn
    ((PeriodicLattice.Bond.forwardFrom x μ).target - x₀)).1
  have h3 := halfTraceSq_stairSum_le A x₀ (coordsOf_spec (k := k) hc hL hn
    ((PeriodicLattice.Bond.forwardFrom x μ).source - x₀)).1
  simp only [stairPotential]
  nlinarith
private theorem sum_positiveEdge_le [Fintype (PositiveEdge L n k 0)]
    (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (x₀ : Vertex L n k 0)
    (f : PositiveEdge L n k 0 → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b, f b ≤ ∑ w ∈ coordBox (halfWidth L n k), ∑ μ : Fin 4,
      f ⟨PeriodicLattice.Bond.forwardFrom (x₀ + ofCoords w) μ,
        forwardFrom_isPositivelyOriented _ _⟩ := by
  classical
  have hdir : ∀ b : PositiveEdge L n k 0, ∃ μ : Fin 4,
      b.1.target - b.1.source = PeriodicLattice.unitStep L n _ μ := fun b => b.2
  choose dir hdir using hdir
  set ψ : PositiveEdge L n k 0 → (Fin 4 → ℤ) × Fin 4 :=
    fun b => (coordsOf (b.1.source - x₀), dir b) with hψ
  set F : (Fin 4 → ℤ) × Fin 4 → ℝ := fun p =>
    f ⟨PeriodicLattice.Bond.forwardFrom (x₀ + ofCoords p.1) p.2,
      forwardFrom_isPositivelyOriented _ _⟩ with hF
  have hrec : ∀ b, (⟨PeriodicLattice.Bond.forwardFrom (x₀ + ofCoords (ψ b).1) (ψ b).2,
      forwardFrom_isPositivelyOriented _ _⟩ : PositiveEdge L n k 0) = b := by
    intro b
    have ht : x₀ + ofCoords (coordsOf (b.1.source - x₀)) = b.1.source := by
      rw [← (coordsOf_spec (k := k) hc hL hn (b.1.source - x₀)).2]
      abel
    apply Subtype.ext
    apply PeriodicLattice.Bond.ext
    · exact ht
    · change x₀ + ofCoords (coordsOf (b.1.source - x₀)) + PeriodicLattice.unitStep L n _ (dir b) =
        b.1.target
      rw [ht, ← hdir b]
      abel
  have hinj : Function.Injective ψ := by
    intro b b' e
    rw [← hrec b, ← hrec b']
    simp only [e]
  calc ∑ b, f b = ∑ b, F (ψ b) := Finset.sum_congr rfl fun b _ => by
        simp only [hF]
        rw [hrec b]
    _ = ∑ p ∈ Finset.univ.image ψ, F p := (Finset.sum_image fun a _ b _ e => hinj e).symm
    _ ≤ ∑ p ∈ coordBox (halfWidth L n k) ×ˢ (Finset.univ : Finset (Fin 4)), F p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hf _
        intro p hp
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp
        exact Finset.mem_product.2 ⟨(coordsOf_spec (k := k) hc hL hn _).1, Finset.mem_univ _⟩
    _ = _ := Finset.sum_product _ _ _
private theorem card_coarseVertex_le [Fintype (Vertex L n k k)]
    (hc : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    Fintype.card (Vertex L n k k) ≤ (2 * halfWidth L n k) ^ 4 := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hinj : Function.Injective fun y : Vertex L n k k =>
      (⟨coordsOf (fineVertex y), (coordsOf_spec (k := k) hc hL hn _).1⟩ :
        coordBox (halfWidth L n k)) := by
    intro y y' e
    have e' : coordsOf (fineVertex (L := L) (n := n) (k := k) y) = coordsOf (fineVertex y') :=
      congrArg Subtype.val e
    apply fineVertex_injective hL0
    rw [(coordsOf_spec (k := k) hc hL hn (fineVertex y)).2,
      (coordsOf_spec (k := k) hc hL hn (fineVertex y')).2, e']
  have := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_coe, card_coordBox] at this
end Sums
private theorem traceFinsumPairing_self_re {ι : Type*} [Fintype ι] (f : ι → ComplexMatrix2) :
    (traceFinsumPairing f f).re = ∑ i, halfTraceSq (f i) := by
  simp only [traceFinsumPairing, halfTraceSq, finsum_eq_sum_of_fintype, Complex.re_sum]
private theorem sum_sum_split (T : Finset (Fin 4 → ℤ)) (a b : (Fin 4 → ℤ) → ℝ) (c X : ℝ) :
    ∑ w ∈ T, ∑ _μ : Fin 4, (a w * (4 * b w ^ 2 * c) + X) =
      16 * (∑ w ∈ T, a w * b w ^ 2) * c + 4 * (T.card : ℝ) * X := by
  have h : ∀ w, ∑ _μ : Fin 4, (a w * (4 * b w ^ 2 * c) + X) =
      16 * c * (a w * b w ^ 2) + 4 * X := by
    intro w
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
  ring
private theorem far_edge_constant_le {θ s P H : ℝ} (hθ : 0 < θ) (hs : 1 ≤ s) (hP : 1 ≤ P)
    (hH : H = P * s) :
    4 * (2 * H) ^ 4 * ((2 * H) ^ 4 * (3 * (1 + 32 * H ^ 2))) *
        (Real.exp (θ / 2) * Real.exp (-(θ * s / 4))) ≤
      (4 * 2 ^ 8 * 3 * 33 * P ^ 10 * ((Nat.factorial 10 : ℝ) * (8 / θ) ^ 10) *
          Real.exp (θ / 2)) *
        Real.exp (-(θ / 16 * (2 * s))) := by
  have hH1 : 1 ≤ H := by rw [hH]; nlinarith
  have h1 : 1 + 32 * H ^ 2 ≤ 33 * H ^ 2 := by nlinarith
  have hx : 0 ≤ θ * s / 8 := by positivity
  have h2 := Real.pow_div_factorial_le_exp (θ * s / 8) hx 10
  have hf : (0 : ℝ) < Nat.factorial 10 := by positivity
  have h3 : s ^ 10 ≤ (Nat.factorial 10 : ℝ) * (8 / θ) ^ 10 * Real.exp (θ * s / 8) := by
    rw [div_le_iff₀ hf] at h2
    have e : (8 / θ) ^ 10 * (θ * s / 8) ^ 10 = s ^ 10 := by
      rw [← mul_pow]
      congr 1
      field_simp
    have h8 : (0 : ℝ) ≤ (8 / θ) ^ 10 := by positivity
    have := mul_le_mul_of_nonneg_left h2 h8
    rw [e] at this
    calc s ^ 10 ≤ _ := this
      _ = _ := by ring
  have h4 : 4 * (2 * H) ^ 4 * ((2 * H) ^ 4 * (3 * (1 + 32 * H ^ 2))) ≤
      4 * 2 ^ 8 * 3 * 33 * P ^ 10 * s ^ 10 := by
    have e : 4 * 2 ^ 8 * 3 * 33 * P ^ 10 * s ^ 10 =
        4 * (2 * H) ^ 4 * ((2 * H) ^ 4 * (3 * (33 * H ^ 2))) := by
      rw [hH]
      ring
    rw [e]
    gcongr
  have hE : 0 ≤ Real.exp (θ / 2) * Real.exp (-(θ * s / 4)) := by positivity
  calc _ ≤ 4 * 2 ^ 8 * 3 * 33 * P ^ 10 * s ^ 10 *
        (Real.exp (θ / 2) * Real.exp (-(θ * s / 4))) := mul_le_mul_of_nonneg_right h4 hE
    _ ≤ 4 * 2 ^ 8 * 3 * 33 * P ^ 10 *
        ((Nat.factorial 10 : ℝ) * (8 / θ) ^ 10 * Real.exp (θ * s / 8)) *
        (Real.exp (θ / 2) * Real.exp (-(θ * s / 4))) := by
      gcongr
    _ = _ := by
      have e : Real.exp (-(θ / 16 * (2 * s))) =
          Real.exp (θ * s / 8) * Real.exp (-(θ * s / 4)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      ring
theorem formIsLocallyAGradient_of (hc : PeriodicLattice.CoordinateDescription)
    (hcell : NeighbouringFineVertexCells)
    (hm : ResponseMaps.ResponseMapsHold) :
    FormIsLocallyAGradient := by
  intro L hL k hk θ hθ
  have hL0 : 0 < L := by have := hL.2; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL0
  set ℓ := PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) with hℓ
  have hℓ0 : 0 < ℓ := by
    simp only [hℓ, PeriodicLattice.meshSize]
    exact zpow_pos (by linarith) _
  set κ := θ * ℓ / 4 with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨D, hD0, hD⟩ := exists_coordBox_sum_exp_le (r := κ / 2) (by positivity)
  set P : ℝ := (L : ℝ) ^ k with hP
  have hP1 : 1 ≤ P := one_le_pow₀ hL1
  set C₁ : ℝ := 16 * (Real.exp (θ / 2) * (8 / κ ^ 2 * D)) with hC₁
  set C₂ : ℝ := 4 * 2 ^ 8 * 3 * 33 * P ^ 10 * ((Nat.factorial 10 : ℝ) * (8 / θ) ^ 10) *
    Real.exp (θ / 2) with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + C₂, θ / 16, by positivity, by positivity, fun n hn A => ?_⟩
  set H : ℕ := halfWidth L n k with hH
  set s : ℝ := (L : ℝ) ^ n with hs
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hHr : (H : ℝ) = P * s := by
    have : H = L ^ (k + n) := by
      simp only [hH, halfWidth, PeriodicLattice.halfPeriod, PeriodicLattice.levelDepth]
      congr 1
      omega
    rw [this]
    push_cast
    rw [pow_add]
  have hside : PeriodicLattice.torusSide L n = 2 * (H : ℝ) * ℓ := by
    have c1 := (sublatticeCoordinates_fine (k := k) hc hL hn).1
    rw [div_eq_iff hℓ0.ne'] at c1
    rw [c1]
    simp [hH, halfWidth, hℓ]
  have hHℓ : (H : ℝ) * ℓ = s := by
    have : PeriodicLattice.torusSide L n = 2 * s := rfl
    linarith
  have hfs : Finite (Vertex L n k 0) :=
    Finite.of_surjective (fun w : coordBox H => ofCoords (L := L) (n := n) (k := k) w.1)
      fun d => by
        obtain ⟨w, hw, e⟩ := exists_coords (k := k) hc hL hn d
        exact ⟨⟨w, hw⟩, e.symm⟩
  have hfy : Finite (Vertex L n k k) := Finite.of_injective _ (fineVertex_injective hL0)
  have hfb : Finite (Edge L n k 0) :=
    Finite.of_injective (fun b : Edge L n k 0 => (b.source, b.target)) fun b b' e =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hfp : Finite (Face L n k 0) :=
    Finite.of_injective (fun p : Face L n k 0 => (p.origin, p.firstAxis, p.secondAxis))
      fun p p' e => by
        simp only [Prod.mk.injEq] at e
        exact PeriodicLattice.Plaquette.ext e.1 e.2.1 e.2.2
  letI : Fintype (Vertex L n k k) := Fintype.ofFinite _
  letI : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  letI : Fintype (Face L n k 0) := Fintype.ofFinite _
  set Curv : ℝ := ∑ p : Face L n k 0,
    halfTraceSq (edgeCoboundary (A : Edge L n k 0 → ComplexMatrix2) p) with hCurv
  set Asq : ℝ := ∑ b : PositiveEdge L n k 0,
    halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) b.1) with hAsq
  have hCurv0 : 0 ≤ Curv := Finset.sum_nonneg fun p _ => halfTraceSq_nonneg (edgeCoboundary_mem A p)
  have hAsq0 : 0 ≤ Asq := Finset.sum_nonneg fun b _ => halfTraceSq_nonneg (A.2.1 _ b.2)
  have eCurv : backgroundCurvatureNormSq A = Curv := by
    simp only [backgroundCurvatureNormSq]
    rw [(hm L hL k n hk hn).coboundary_eq, traceFinsumPairing_self_re]
  have eAsq : (edgeFormPairing (A : Edge L n k 0 → ComplexMatrix2)
      (A : Edge L n k 0 → ComplexMatrix2)).re = Asq := by
    simp only [edgeFormPairing]
    rw [traceFinsumPairing_self_re]
    rfl
  refine ⟨fun y => ⟨stairPotential (A : Edge L n k 0 → ComplexMatrix2) (fineVertex y),
    Submodule.mem_pi.2 fun x _ => stairPotential_mem A _ x⟩, ?_⟩
  rw [eCurv, eAsq]
  simp only [finsum_eq_sum_of_fintype]
  set S : (Fin 4 → ℤ) → ℝ := fun w => ∑ μ, |(w μ : ℝ)| with hS
  have hS0 : ∀ w, 0 ≤ S w := fun w => Finset.sum_nonneg fun μ _ => abs_nonneg _
  set E : (Fin 4 → ℤ) → ℝ := fun w => Real.exp (θ / 2) * Real.exp (-(κ * S w)) with hE
  have hE0 : ∀ w, 0 ≤ E w := fun w => by positivity
  set g : Vertex L n k k → (Fin 4 → ℤ) → Fin 4 → ℝ := fun y w μ =>
    halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2)
        (PeriodicLattice.Bond.forwardFrom (fineVertex y + ofCoords w) μ) -
      vertexCoboundary (stairPotential (A : Edge L n k 0 → ComplexMatrix2) (fineVertex y))
        (PeriodicLattice.Bond.forwardFrom (fineVertex y + ofCoords w) μ)) with hg
  have hg0 : ∀ y w μ, 0 ≤ g y w μ := fun y w μ => halfTraceSq_nonneg
    (ComplexMatrix2.hermitianTraceless.sub_mem (form_forwardFrom_mem A _ _)
      (ComplexMatrix2.hermitianTraceless.sub_mem (stairPotential_mem A _ _)
        (stairPotential_mem A _ _)))
  have step2 : ∀ y : Vertex L n k k, ∑ b : PositiveEdge L n k 0,
      Real.exp (-(θ * cellDist (fineVertexCell b.1.source) y)) *
        halfTraceSq ((A : Edge L n k 0 → ComplexMatrix2) b.1 -
          vertexCoboundary (stairPotential (A : Edge L n k 0 → ComplexMatrix2) (fineVertex y))
            b.1) ≤
      ∑ w ∈ coordBox H, ∑ μ : Fin 4, E w * g y w μ := by
    intro y
    refine (sum_positiveEdge_le hc hL hn (fineVertex y) _ fun b =>
      mul_nonneg (Real.exp_pos _).le
        (halfTraceSq_nonneg (ComplexMatrix2.hermitianTraceless.sub_mem (A.2.1 _ b.2)
          (ComplexMatrix2.hermitianTraceless.sub_mem (stairPotential_mem A _ _)
            (stairPotential_mem A _ _))))).trans ?_
    refine Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun μ _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (hg0 y w μ)
    have hf := cellDist_ge hcell hL hℓ hℓ0 hside hw y
    rw [hE]
    simp only
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h2 := mul_le_mul_of_nonneg_left hf hθ.le
    change -(θ * cellDist (fineVertexCell (fineVertex y + ofCoords w)) y) ≤
      θ / 2 + -(κ * S w)
    have e : θ * (ℓ * S w / 4 - 1 / 2) = κ * S w - θ / 2 := by
      rw [hκ]
      ring
    rw [e] at h2
    linarith
  set B : ℝ := 3 * (1 + 32 * (H : ℝ) ^ 2) * Asq with hB
  set Nc : ℝ := (Fintype.card (Vertex L n k k) : ℝ) with hNc
  set X : ℝ := Real.exp (θ / 2) * Real.exp (-(κ * H)) * (Nc * B) with hX
  have hX0 : 0 ≤ X := by positivity
  have step4 : ∀ w ∈ coordBox H, ∀ μ : Fin 4,
      E w * ∑ y, g y w μ ≤ E w * (4 * S w ^ 2 * Curv) + X := by
    intro w hw μ
    by_cases hμ : w μ < (H : ℤ)
    · have hw' : w + axisVec μ ∈ coordBox H := by
        refine mem_coordBox.2 fun ρ => ?_
        have b := mem_coordBox.1 hw ρ
        by_cases h : ρ = μ
        · subst h
          simp only [Pi.add_apply, axisVec, Pi.single_eq_same]
          omega
        · simp only [Pi.add_apply, axisVec, Pi.single_eq_of_ne h, add_zero]
          exact b
      have h1 : ∀ y, g y w μ ≤ 4 * ∑ ν ∈ Finset.Ioi μ, ((w ν).natAbs : ℝ) *
          ∑ i ∈ Finset.range (w ν).natAbs,
            halfTraceSq (discreteCurl (liftedForm (A : Edge L n k 0 → ComplexMatrix2) (fineVertex y))
              (lowerCoords ν w + signedTerm (w ν) i • axisVec ν) μ ν) := by
        intro y
        simp only [hg]
        rw [form_sub_vertexCoboundary_eq hc hL hn _ _ hw hw']
        exact halfTraceSq_remainder_le A w _ μ
      have h2 : ∑ y, g y w μ ≤ 4 * ∑ ν ∈ Finset.Ioi μ, ((w ν).natAbs : ℝ) *
          (((w ν).natAbs : ℝ) * Curv) := by
        refine (Finset.sum_le_sum fun y _ => h1 y).trans ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ν hν => ?_) (by norm_num)
        rw [← Finset.mul_sum, Finset.sum_comm]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine (Finset.sum_le_card_nsmul _ _ Curv fun i _ =>
          sum_halfTraceSq_discreteCurl_le hL0 A _ (Finset.mem_Ioi.1 hν)).trans ?_
        simp
      have h3 : ∑ ν ∈ Finset.Ioi μ, ((w ν).natAbs : ℝ) * (((w ν).natAbs : ℝ) * Curv) ≤
          S w ^ 2 * Curv := by
        have ha : ∀ ν, ((w ν).natAbs : ℝ) = |(w ν : ℝ)| := fun ν => by
          rw [Nat.cast_natAbs, Int.cast_abs]
        have hle : ∀ ν, |(w ν : ℝ)| ≤ S w := fun ν =>
          Finset.single_le_sum (f := fun μ => |(w μ : ℝ)|) (fun μ _ => abs_nonneg _)
            (Finset.mem_univ ν)
        calc _ ≤ ∑ ν ∈ Finset.Ioi μ, |(w ν : ℝ)| * (S w * Curv) := by
              refine Finset.sum_le_sum fun ν _ => ?_
              rw [ha ν]
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_right (hle ν) hCurv0
          _ = (∑ ν ∈ Finset.Ioi μ, |(w ν : ℝ)|) * (S w * Curv) := (Finset.sum_mul _ _ _).symm
          _ ≤ S w * (S w * Curv) := by
              refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (hS0 w) hCurv0)
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                fun μ _ _ => abs_nonneg _
          _ = _ := by ring
      have h4 : ∑ y, g y w μ ≤ 4 * S w ^ 2 * Curv := by
        refine h2.trans ?_
        nlinarith
      have := mul_le_mul_of_nonneg_left h4 (hE0 w)
      linarith
    · have hwμ : w μ = (H : ℤ) := le_antisymm (mem_coordBox.1 hw μ).2 (not_lt.1 hμ)
      have hSH : (H : ℝ) ≤ S w := by
        have h := Finset.single_le_sum (f := fun μ => |(w μ : ℝ)|) (fun μ _ => abs_nonneg _)
          (Finset.mem_univ μ)
        have e : |(w μ : ℝ)| = (H : ℝ) := by
          rw [hwμ]
          simp
        simpa [hS, e] using h
      have h1 : ∑ y : Vertex L n k k, g y w μ ≤ Nc * B := by
        refine (Finset.sum_le_card_nsmul _ _ B fun y _ =>
          halfTraceSq_form_sub_vertexCoboundary_le hc hL hn A _ _ μ).trans ?_
        simp [hNc]
      have h2 : E w ≤ Real.exp (θ / 2) * Real.exp (-(κ * H)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        have := mul_le_mul_of_nonneg_left hSH hκ0.le
        linarith
      have h3 : E w * ∑ y, g y w μ ≤ X := by
        refine (mul_le_mul h2 h1 (Finset.sum_nonneg fun y _ => hg0 y w μ) (by positivity))
      have h4 : 0 ≤ E w * (4 * S w ^ 2 * Curv) := mul_nonneg (hE0 w) (by positivity)
      linarith
  have hsumE : ∑ w ∈ coordBox H, E w * S w ^ 2 ≤ Real.exp (θ / 2) * (8 / κ ^ 2 * D) := by
    have h1 : ∀ w ∈ coordBox H, E w * S w ^ 2 ≤
        Real.exp (θ / 2) * (8 / κ ^ 2 * Real.exp (-(κ / 2 * S w))) := by
      intro w _
      have := sq_mul_exp_neg_le hκ0 (hS0 w)
      calc E w * S w ^ 2 = Real.exp (θ / 2) * (S w ^ 2 * Real.exp (-(κ * S w))) := by
            simp only [hE]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_left (hD H) (by positivity)
  have hNc2 : Nc ≤ (2 * (H : ℝ)) ^ 4 := by
    have := card_coarseVertex_le (k := k) (n := n) (L := L) hc hL hn
    rw [hNc]
    exact_mod_cast this
  have hκH : κ * H = θ * s / 4 := by
    rw [hκ, ← hHℓ]
    ring
  have hfar : 4 * (2 * (H : ℝ)) ^ 4 * X ≤ C₂ * Real.exp (-(θ / 16 * (2 * s))) * Asq := by
    have hfin := far_edge_constant_le (H := (H : ℝ)) hθ hs1 hP1 hHr
    have hAmul := mul_le_mul_of_nonneg_right hfin hAsq0
    refine le_trans ?_ hAmul
    rw [hX, hB, hκH]
    have hNB : Nc * (3 * (1 + 32 * (H : ℝ) ^ 2) * Asq) ≤
        (2 * (H : ℝ)) ^ 4 * (3 * (1 + 32 * (H : ℝ) ^ 2)) * Asq := by
      have : 0 ≤ 3 * (1 + 32 * (H : ℝ) ^ 2) * Asq := by positivity
      calc _ ≤ (2 * (H : ℝ)) ^ 4 * (3 * (1 + 32 * (H : ℝ) ^ 2) * Asq) :=
            mul_le_mul_of_nonneg_right hNc2 this
        _ = _ := by ring
    have hpos : 0 ≤ 4 * (2 * (H : ℝ)) ^ 4 *
        (Real.exp (θ / 2) * Real.exp (-(θ * s / 4))) := by positivity
    calc _ = 4 * (2 * (H : ℝ)) ^ 4 * (Real.exp (θ / 2) * Real.exp (-(θ * s / 4))) *
          (Nc * (3 * (1 + 32 * (H : ℝ) ^ 2) * Asq)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNB hpos
      _ = _ := by ring
  calc ∑ y : Vertex L n k k, ∑ b : PositiveEdge L n k 0,
        Real.exp (-(θ * cellDist (fineVertexCell b.1.source) y)) *
          (ComplexMatrix2.halfTrace (((A : Edge L n k 0 → ComplexMatrix2) b.1 -
              vertexCoboundary (stairPotential (A : Edge L n k 0 → ComplexMatrix2) (fineVertex y))
                b.1) *
            ((A : Edge L n k 0 → ComplexMatrix2) b.1 -
              vertexCoboundary (stairPotential (A : Edge L n k 0 → ComplexMatrix2) (fineVertex y))
                b.1))).re
      ≤ ∑ y : Vertex L n k k, ∑ w ∈ coordBox H, ∑ μ : Fin 4, E w * g y w μ :=
        Finset.sum_le_sum fun y _ => step2 y
    _ = ∑ w ∈ coordBox H, ∑ μ : Fin 4, E w * ∑ y, g y w μ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ w ∈ coordBox H, ∑ μ : Fin 4, (E w * (4 * S w ^ 2 * Curv) + X) :=
        Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun μ _ => step4 w hw μ
    _ = 16 * (∑ w ∈ coordBox H, E w * S w ^ 2) * Curv + 4 * (2 * (H : ℝ)) ^ 4 * X := by
        rw [sum_sum_split, card_coordBox]
        push_cast
        ring
    _ ≤ C₁ * Curv + C₂ * Real.exp (-(θ / 16 * (2 * s))) * Asq := by
        refine add_le_add ?_ hfar
        refine mul_le_mul_of_nonneg_right ?_ hCurv0
        rw [hC₁]
        linarith
    _ ≤ (C₁ + C₂) * (Curv + Real.exp (-(θ / 16 * (2 * s))) * Asq) := by
        have h1 : 0 ≤ Real.exp (-(θ / 16 * (2 * s))) * Asq := by positivity
        nlinarith [mul_nonneg hC₁0 h1, mul_nonneg hC₂0 hCurv0]
end YangMills.Construction.RunningCouplingSlope.LocalGradient
end
