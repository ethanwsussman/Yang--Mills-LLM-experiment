import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOneProof
import YangMills.Construction.RunningCouplingSlope.ContoursAboveGivenFrames
import YangMills.Construction.RunningCouplingSlope.ContoursAtTheLeastFieldHaveKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology Nat
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates Interpolation
namespace Interpolation
namespace LogContourDerivSteps
variable {F : BlockFrame}
private abbrev topSmoothness : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
private theorem natCast_le_topSmoothness (j : ℕ) : (j : WithTop ℕ∞) ≤ topSmoothness := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NormNearOne.natCast_le_smoothTop <;> assumption
private def HolonomyDerivBounds (B : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ (F : BlockFrame) (lev : ℕ) (W : F.GaugeField lev) (x : F.Site lev) (l : List PathStep) (k : ℕ)
    (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (perturbedHolonomy W x l c X) ∧
    ((∀ i, ‖X i‖ ≤ 1) → ∀ j, ‖iteratedFDeriv ℝ j (perturbedHolonomy W x l c X) 0‖ ≤ B k l.length j) ∧
    ∀ i, c i ∉ pathPositiveBonds x l → ∀ (τ : Fin k → ℝ) (s : ℝ),
      perturbedHolonomy W x l c X (Function.update τ i s) = perturbedHolonomy W x l c X τ
private def averageAlong {k : ℕ} (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4)
    (b : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : ℍ[ℝ] :=
  contourAverage (leftTranslate (bondSpread b X τ) W) c₀
private def normSqAlong {k : ℕ} (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4)
    (b : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : ℝ :=
  inner ℝ (averageAlong W c₀ b X τ) (averageAlong W c₀ b X τ)
private def halfLog (y : ℝ) : ℝ := 1 / 2 * Real.log y
private theorem log_norm_eq_halfLog (q : ℍ[ℝ]) : Real.log ‖q‖ = halfLog (inner ℝ q q) := by
  rw [real_inner_self_eq_norm_sq, halfLog, Real.log_pow]
  push_cast
  ring
private def averageBound (B : ℕ → ℕ → ℕ → ℝ) (L k j : ℕ) : ℝ :=
  ‖(1 / (24 * (L : ℝ) ^ 4) : ℝ)‖ * ∑ i : Fin 4, ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
    B k (bondContour L h π i).length j
private theorem averageBound_nonneg {B : ℕ → ℕ → ℕ → ℝ} (hB0 : ∀ k n j, 0 ≤ B k n j) (L k j : ℕ) :
    0 ≤ averageBound B L k j :=
  mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => hB0 _ _ _)
private def normSqBound (B : ℕ → ℕ → ℕ → ℝ) (L k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * averageBound B L k i * averageBound B L k (n - i)
private theorem normSqBound_nonneg {B : ℕ → ℕ → ℕ → ℝ} (hB0 : ∀ k n j, 0 ≤ B k n j) (L k n : ℕ) :
    0 ≤ normSqBound B L k n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (averageBound_nonneg hB0 _ _ _))
    (averageBound_nonneg hB0 _ _ _)
private theorem norm_iteratedFDeriv_sum_le {k : ℕ} {ι : Type} (S : Finset ι) (f : ι → (Fin k → ℝ) → ℍ[ℝ])
    (hf : ∀ q ∈ S, ContDiff ℝ topSmoothness (f q)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun τ => ∑ q ∈ S, f q τ) 0‖ ≤ ∑ q ∈ S, ‖iteratedFDeriv ℝ j (f q) 0‖ := by apply _root_.YangMills.DeltaSharedProofs.p501344 <;> assumption
private theorem averageAlong_eq {k : ℕ} (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4)
    (b : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    averageAlong W c₀ b X = (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ) • fun τ => ∑ h ∈ centredCube F.blockSide,
      ∑ π : Equiv.Perm (Fin 4), perturbedHolonomy W (refineSite c₀.1) (bondContour F.blockSide h π c₀.2) b X τ := rfl
private theorem contDiff_holonomySum {B : ℕ → ℕ → ℕ → ℝ} (hB : HolonomyDerivBounds B) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ContDiff ℝ topSmoothness (fun τ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      perturbedHolonomy W (refineSite c₀.1) (bondContour F.blockSide h π c₀.2) b X τ) :=
  ContDiff.sum fun _ _ => ContDiff.sum fun _ _ => (hB F F.depth W _ _ k b X).1
private theorem contDiff_averageAlong {B : ℕ → ℕ → ℕ → ℝ} (hB : HolonomyDerivBounds B) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ContDiff ℝ topSmoothness (averageAlong W c₀ b X) := by
  rw [averageAlong_eq]
  exact (contDiff_holonomySum hB W c₀ b X).const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ)
private theorem norm_iteratedFDeriv_averageAlong_le {B : ℕ → ℕ → ℕ → ℝ} (hB0 : ∀ k n j, 0 ≤ B k n j)
    (hB : HolonomyDerivBounds B) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : ∀ i, ‖X i‖ ≤ 1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (averageAlong W c₀ b X) 0‖ ≤ averageBound B F.blockSide k j := by
  rw [averageAlong_eq, iteratedFDeriv_const_smul_apply
    (((contDiff_holonomySum hB W c₀ b X).of_le (natCast_le_topSmoothness j)).contDiffAt), norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := norm_iteratedFDeriv_sum_le (centredCube F.blockSide) (fun h τ => ∑ π : Equiv.Perm (Fin 4),
    perturbedHolonomy W (refineSite c₀.1) (bondContour F.blockSide h π c₀.2) b X τ)
    (fun h _ => ContDiff.sum fun π _ => (hB F F.depth W _ _ k b X).1) j
  refine h1.trans ?_
  have h2 : ∀ h ∈ centredCube F.blockSide, ‖iteratedFDeriv ℝ j (fun τ => ∑ π : Equiv.Perm (Fin 4),
      perturbedHolonomy W (refineSite c₀.1) (bondContour F.blockSide h π c₀.2) b X τ) 0‖ ≤
      ∑ π : Equiv.Perm (Fin 4), B k (bondContour F.blockSide h π c₀.2).length j := fun h _ =>
    (norm_iteratedFDeriv_sum_le Finset.univ (fun π τ =>
      perturbedHolonomy W (refineSite c₀.1) (bondContour F.blockSide h π c₀.2) b X τ)
      (fun π _ => (hB F F.depth W _ _ k b X).1) j).trans
      (Finset.sum_le_sum fun π _ => (hB F F.depth W _ _ k b X).2.1 hX j)
  refine (Finset.sum_le_sum h2).trans ?_
  exact Finset.single_le_sum (f := fun i : Fin 4 => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    B k (bondContour F.blockSide h π i).length j)
    (fun i _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hB0 _ _ _)
    (Finset.mem_univ c₀.2)
private theorem contDiff_normSqAlong {B : ℕ → ℕ → ℕ → ℝ} (hB : HolonomyDerivBounds B) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ContDiff ℝ topSmoothness (normSqAlong W c₀ b X) :=
  (contDiff_averageAlong hB W c₀ b X).inner ℝ (contDiff_averageAlong hB W c₀ b X)
private theorem norm_iteratedFDeriv_normSqAlong_le {B : ℕ → ℕ → ℕ → ℝ} (hB0 : ∀ k n j, 0 ≤ B k n j)
    (hB : HolonomyDerivBounds B) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : ∀ i, ‖X i‖ ≤ 1) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (normSqAlong W c₀ b X) 0‖ ≤ normSqBound B F.blockSide k n := by
  have h := (innerSL ℝ (E := ℍ[ℝ])).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (contDiff_averageAlong hB W c₀ b X) (contDiff_averageAlong hB W c₀ b X) (0 : Fin k → ℝ)
    (natCast_le_topSmoothness n) (norm_innerSL_le ℝ)
  have e : (fun y => innerSL ℝ (averageAlong W c₀ b X y) (averageAlong W c₀ b X y)) = normSqAlong W c₀ b X := by
    funext y
    rfl
  rw [e] at h
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 := norm_iteratedFDeriv_averageAlong_le hB0 hB W c₀ b X hX i
  have h2 := norm_iteratedFDeriv_averageAlong_le hB0 hB W c₀ b X hX (n - i)
  have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
    (mul_nonneg hc (averageBound_nonneg hB0 _ _ _))
private theorem contDiffOn_halfLog : ContDiffOn ℝ topSmoothness halfLog (Set.Ioi 0) := by
  have h : ContDiffOn ℝ topSmoothness Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono fun y hy => (ne_of_gt (Set.mem_Ioi.1 hy))
  exact contDiffOn_const.mul h
private theorem exists_halfLog_deriv_bound (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, i ≤ n → ∀ y ∈ Set.Icc (1 / 4 : ℝ) 1,
    ‖iteratedFDerivWithin ℝ i halfLog (Set.Ioi 0) y‖ ≤ C := by
  have hone : ∀ i : ℕ, ∃ C : ℝ, ∀ y ∈ Set.Icc (1 / 4 : ℝ) 1,
      ‖iteratedFDerivWithin ℝ i halfLog (Set.Ioi 0) y‖ ≤ C := by
    intro i
    have hc : ContinuousOn (iteratedFDerivWithin ℝ i halfLog (Set.Ioi 0)) (Set.Ioi 0) :=
      contDiffOn_halfLog.continuousOn_iteratedFDerivWithin (natCast_le_topSmoothness i) (uniqueDiffOn_Ioi 0)
    have hsub : Set.Icc (1 / 4 : ℝ) 1 ⊆ Set.Ioi 0 := fun y hy =>
      Set.mem_Ioi.2 (lt_of_lt_of_le (by norm_num) hy.1)
    exact isCompact_Icc.exists_bound_of_continuousOn (hc.mono hsub)
  choose C hC using hone
  refine ⟨∑ i ∈ Finset.range (n + 1), |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro i hi y hy
  refine ((hC i y hy).trans (le_abs_self _)).trans ?_
  exact Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))
private def logNormBound (B : ℕ → ℕ → ℕ → ℝ) (Cl : ℕ → ℝ) (L k n : ℕ) : ℝ :=
  (n ! : ℝ) * Cl n * (1 + ∑ i ∈ Finset.range (n + 1), normSqBound B L k i) ^ n
private theorem log_norm_average_eq {k : ℕ} (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4)
    (b : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    (fun τ => Real.log ‖contourAverage (leftTranslate (bondSpread b X τ) W) c₀‖) =
      halfLog ∘ normSqAlong W c₀ b X := by
  funext τ
  exact log_norm_eq_halfLog _
private theorem averageAlong_zero {k : ℕ} (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4)
    (b : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    averageAlong W c₀ b X 0 = contourAverage W c₀ := by
  have e : leftTranslate (bondSpread b X 0) W = W := by
    funext y i
    simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, expUnit]
  simp only [averageAlong, e]
private theorem normSqAlong_zero {k : ℕ} (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4)
    (b : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    normSqAlong W c₀ b X 0 = ‖contourAverage W c₀‖ ^ 2 := by
  simp only [normSqAlong, averageAlong_zero, real_inner_self_eq_norm_sq]
private theorem contDiffAt_log_norm_average {B : ℕ → ℕ → ℕ → ℝ} (hB : HolonomyDerivBounds B) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) (h0 : contourAverage W c₀ ≠ 0) (N : ℕ) :
    ContDiffAt ℝ N (fun τ => Real.log ‖contourAverage (leftTranslate (bondSpread b X τ) W) c₀‖) 0 := by
  rw [log_norm_average_eq]
  have hpos : 0 < normSqAlong W c₀ b X 0 := by
    rw [normSqAlong_zero]
    have := norm_pos_iff.2 h0
    positivity
  have h1 : ContDiffAt ℝ N halfLog (normSqAlong W c₀ b X 0) :=
    ((contDiffOn_halfLog.contDiffAt (Ioi_mem_nhds hpos))).of_le (natCast_le_topSmoothness N)
  exact h1.comp _ (((contDiff_normSqAlong hB W c₀ b X).of_le (natCast_le_topSmoothness N)).contDiffAt)
private theorem norm_iteratedFDeriv_log_le {B : ℕ → ℕ → ℕ → ℝ} (hB0 : ∀ k n j, 0 ≤ B k n j)
    (hB : HolonomyDerivBounds B)
    {Cl : ℕ → ℝ} (hCl : ∀ n i, i ≤ n → ∀ y ∈ Set.Icc (1 / 4 : ℝ) 1,
      ‖iteratedFDerivWithin ℝ i halfLog (Set.Ioi 0) y‖ ≤ Cl n) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : ∀ i, ‖X i‖ ≤ 1) (h1 : 1 / 2 ≤ ‖contourAverage W c₀‖)
    (h2 : ‖contourAverage W c₀‖ ≤ 1) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun τ => Real.log ‖contourAverage (leftTranslate (bondSpread b X τ) W) c₀‖) 0‖ ≤
      logNormBound B Cl F.blockSide k n := by
  rw [log_norm_average_eq]
  set N := normSqAlong W c₀ b X with hN
  have hNs := contDiff_normSqAlong hB W c₀ b X
  set U : Set (Fin k → ℝ) := N ⁻¹' Set.Ioi 0 with hU
  have hUo : IsOpen U := isOpen_Ioi.preimage hNs.continuous
  have hN0 : N 0 ∈ Set.Icc (1 / 4 : ℝ) 1 := by
    rw [hN, normSqAlong_zero]
    constructor <;> nlinarith [norm_nonneg (contourAverage W c₀)]
  have h0U : (0 : Fin k → ℝ) ∈ U := lt_of_lt_of_le (by norm_num) hN0.1
  set D : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), normSqBound B F.blockSide k i with hD
  have hs0 : ∀ i, 0 ≤ normSqBound B F.blockSide k i := fun i => normSqBound_nonneg hB0 _ _ _
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ∑ i ∈ Finset.range (n + 1), normSqBound B F.blockSide k i :=
      Finset.sum_nonneg fun i _ => hs0 i
    linarith
  have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := halfLog) (f := N) (n := n) (s := U)
    (t := Set.Ioi 0) (x := 0) (N := topSmoothness) (C := Cl n) (D := D) contDiffOn_halfLog hNs.contDiffOn
    (natCast_le_topSmoothness n)
    (uniqueDiffOn_Ioi 0) hUo.uniqueDiffOn (fun τ hτ => hτ) h0U
    (fun i hi => hCl n i hi _ hN0)
    (fun i hi hin => by
      rw [iteratedFDerivWithin_of_isOpen i hUo h0U]
      refine (norm_iteratedFDeriv_normSqAlong_le hB0 hB W c₀ b X hX i).trans ?_
      have h3 : normSqBound B F.blockSide k i ≤ ∑ i ∈ Finset.range (n + 1), normSqBound B F.blockSide k i :=
        Finset.single_le_sum (f := fun i => normSqBound B F.blockSide k i) (fun i _ => hs0 i)
          (Finset.mem_range.2 (by omega))
      have h4 : D ≤ D ^ i := le_self_pow₀ hD1 (by omega)
      linarith)
  rw [iteratedFDerivWithin_of_isOpen n hUo h0U] at hcomp
  exact hcomp
open Classical in
private def contourBondSet (c₀ : F.Site F.top × Fin 4) : Finset (F.Site F.depth × Fin 4) :=
  (centredCube F.blockSide).biUnion fun h => Finset.univ.biUnion fun π : Equiv.Perm (Fin 4) =>
    (pathPositiveBonds (refineSite c₀.1) (bondContour F.blockSide h π c₀.2)).toFinset
private theorem averageAlong_update {B : ℕ → ℕ → ℕ → ℝ} (hB : HolonomyDerivBounds B) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) (l : Fin k)
    (hl : b l ∉ contourBondSet c₀) (τ : Fin k → ℝ) (s : ℝ) :
    averageAlong W c₀ b X (Function.update τ l s) = averageAlong W c₀ b X τ := by
  classical
  rw [averageAlong_eq]
  simp only [Pi.smul_apply]
  congr 1
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  refine (hB F F.depth W _ _ k b X).2.2 l (fun hm => hl ?_) τ s
  exact Finset.mem_biUnion.2 ⟨h, hh, Finset.mem_biUnion.2 ⟨π, Finset.mem_univ _, List.mem_toFinset.2 hm⟩⟩
private def zeroCoord {k : ℕ} (l : Fin k) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => if i = l then 0 else (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)
private theorem zeroCoord_apply {k : ℕ} (l : Fin k) (τ : Fin k → ℝ) :
    zeroCoord l τ = Function.update τ l 0 := by
  funext i
  by_cases h : i = l
  · subst h
    simp [zeroCoord]
  · simp [zeroCoord, h]
private theorem iteratedFDeriv_log_eq_zero_of_not_mem {B : ℕ → ℕ → ℕ → ℝ} (hB : HolonomyDerivBounds B) {k : ℕ}
    (W : F.GaugeField F.depth) (c₀ : F.Site F.top × Fin 4) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) (l : Fin k)
    (hl : b l ∉ contourBondSet c₀) (h0 : contourAverage W c₀ ≠ 0) :
    iteratedFDeriv ℝ k (fun τ => Real.log ‖contourAverage (leftTranslate (bondSpread b X τ) W) c₀‖) 0
      (fun i => Pi.single i 1) = 0 := by
  rw [log_norm_average_eq]
  set N := normSqAlong W c₀ b X with hN
  have hNs := contDiff_normSqAlong hB W c₀ b X
  set U : Set (Fin k → ℝ) := N ⁻¹' Set.Ioi 0 with hU
  have hUo : IsOpen U := isOpen_Ioi.preimage hNs.continuous
  have h0U : (0 : Fin k → ℝ) ∈ U := by
    show 0 < N 0
    rw [hN, normSqAlong_zero]
    have := norm_pos_iff.2 h0
    positivity
  have hNP : ∀ τ, N (zeroCoord l τ) = N τ := fun τ => by
    rw [zeroCoord_apply]
    simp only [hN, normSqAlong, averageAlong_update hB W c₀ b X l hl]
  have hf : ContDiffOn ℝ topSmoothness (halfLog ∘ N) U :=
    contDiffOn_halfLog.comp hNs.contDiffOn fun τ hτ => hτ
  have hpre : zeroCoord l ⁻¹' U = U := by
    ext τ
    simp only [hU, Set.mem_preimage, hNP]
  have hcomp : (halfLog ∘ N) ∘ zeroCoord l = halfLog ∘ N := by
    funext τ
    simp only [Function.comp, hNP]
  have h1 := (zeroCoord l).iteratedFDerivWithin_comp_right hf hUo.uniqueDiffOn
    (by rw [hpre]; exact hUo.uniqueDiffOn) (x := 0) (by simpa using h0U) (i := k) (natCast_le_topSmoothness k)
  rw [hcomp, hpre, map_zero, iteratedFDerivWithin_of_isOpen k hUo h0U] at h1
  rw [h1, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ContinuousMultilinearMap.map_coord_zero _ l ?_
  rw [zeroCoord_apply]
  funext i
  by_cases h : i = l
  · subst h
    simp
  · simp [h]
private theorem prod_le_exp_sup {p : ℕ} (c : OrderedFinpartition p) (hp : 1 ≤ p) {Mm : Fin c.length → ℝ}
    (hM : ∀ m, 0 ≤ Mm m) {r : ℝ} (hr : 0 ≤ r) (d : Fin p → ℕ) (a : Fin c.length → ℝ) (ha0 : ∀ m, 0 ≤ a m)
    (ha : ∀ (m : Fin c.length) (q : Fin (c.partSize m)), a m ≤ Mm m * Real.exp (-(r * d (c.emb m q)))) :
    ∏ m, a m ≤ (∏ m, Mm m) * Real.exp (-(r * ((Finset.univ.sup d : ℕ) : ℝ))) := by apply _root_.YangMills.SharedProofs.p56725 <;> assumption
private theorem sum_slots_le {i : ℕ} {A : Fin i → F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (S T : Finset (F.Site F.depth × Fin 4))
    {Bi Q : ℝ} (hBi : 0 ≤ Bi) (hQ : 0 ≤ Q)
    (hprod : ∀ b : Fin i → F.Site F.depth × Fin 4, (∀ m, b m ∈ S) → ∏ m, ‖A m (b m).1 (b m).2‖ ≤ Q) :
    ∑ b ∈ Fintype.piFinset (fun _ : Fin i => T), (open Classical in if ∀ m, b m ∈ S then Bi else 0) *
      ∏ m, ‖A m (b m).1 (b m).2‖ ≤ (S.card : ℝ) ^ i * (Bi * Q) := by apply _root_.YangMills.SharedProofs.p93245 <;> assumption
private theorem length_pathPositiveBonds {j : ℕ} (l : List PathStep) (x : F.Site j) :
    (pathPositiveBonds x l).length = l.length := by apply _root_.YangMills.SharedProofs.p1818 <;> assumption
private theorem siteSupDist_path_le (hdist : SupDistCellComparison) {j : ℕ} (l : List PathStep) (x : F.Site j)
    (b : F.Site j × Fin 4) (h : b ∈ pathPositiveBonds x l) : siteSupDist x b.1 ≤ l.length := by apply _root_.YangMills.SharedProofs.p17230 <;> assumption
private def contourStepCount (L : ℕ) : ℕ :=
  ∑ i : Fin 4, ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), (bondContour L h π i).length
private theorem length_bondContour_le {L : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (bondContour L h π i).length ≤ contourStepCount L := by apply _root_.YangMills.DeltaSharedProofs.p501988 <;> assumption
private theorem card_contourBondSet_le (c₀ : F.Site F.top × Fin 4) :
    (contourBondSet c₀).card ≤ contourStepCount F.blockSide := by
  classical
  have h1 : (contourBondSet c₀).card ≤ ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (bondContour F.blockSide h π c₀.2).length := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun h _ => ?_)
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun π _ => ?_)
    exact (List.toFinset_card_le _).trans (length_pathPositiveBonds _ _).le
  exact h1.trans (Finset.single_le_sum (f := fun i : Fin 4 => ∑ h ∈ centredCube F.blockSide,
    ∑ π : Equiv.Perm (Fin 4), (bondContour F.blockSide h π i).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ c₀.2))
private theorem cellSupDist_contour_le (hdist : SupDistCellComparison) (hL : 0 < F.blockSide)
    (hodd : Odd F.blockSide) (hpos : ∀ i, 0 < F.extent i)
    (hls : ∀ x y : F.Site F.depth, F.blockSide * cellSupDist (enclosingCell x) (enclosingCell y) ≤
      siteSupDist x y + F.blockSide)
    (hcs : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (c₀ : F.Site F.top × Fin 4) (b : F.Site F.depth × Fin 4) (hb : b ∈ contourBondSet c₀) :
    cellSupDist c₀.1 (enclosingCell b.1) ≤ contourStepCount F.blockSide + 1 := by
  classical
  obtain ⟨h, hh, hb⟩ := Finset.mem_biUnion.1 hb
  obtain ⟨π, -, hb⟩ := Finset.mem_biUnion.1 hb
  have h1 := siteSupDist_path_le hdist _ _ b (List.mem_toFinset.1 hb)
  have h2 := length_bondContour_le hh π c₀.2 (L := F.blockSide)
  have h3 := hls b.1 (refineSite c₀.1)
  rw [(hdist.2.2 F hodd hpos).2.2 c₀.1, (hdist.1 F F.depth b.1 (refineSite c₀.1) b.1).2.1] at h3
  rw [hcs]
  by_contra hlt
  push Not at hlt
  have h4 : F.blockSide * (contourStepCount F.blockSide + 2) ≤
      F.blockSide * cellSupDist (enclosingCell b.1) c₀.1 :=
    Nat.mul_le_mul_left _ hlt
  nlinarith
private def perturbationList {l j : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) : Fin (l + j) → Perturbation F :=
  Fin.addCases (fun i => Perturbation.bulk (b i) (u i)) (fun i => Perturbation.top (c i) (X i))
private theorem displacedPoint_eq {l j : ℕ} (η : StepVariable (finiteCells F))
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) (τ : Fin (l + j) → ℝ) :
    displacedPoint η b u (fun i => τ (Fin.castAdd j i)) = perturbedVariable η (perturbationList b u c X) τ := by
  classical
  simp only [displacedPoint, perturbedVariable, Fin.sum_univ_add, perturbationList, Fin.addCases_left,
    Fin.addCases_right, Perturbation.variableDirection, smul_zero, Finset.sum_const_zero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.single_smul]
private theorem leftTranslate_eq_perturbedTop {l j : ℕ} (V : F.GaugeField F.top)
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) (τ : Fin (l + j) → ℝ) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X fun i => τ (Fin.natAdd l i)) V =
      perturbedTop V (perturbationList b u c X) τ := by
  classical
  have e : ColdStepAtMirrorFrames.bondSpread c X (fun i => τ (Fin.natAdd l i)) =
      ColdStepAtMirrorFrames.bondSpread (fun l' => (perturbationList b u c X l').topBond)
        (fun l' => (perturbationList b u c X l').topDirection) τ := by
    funext y i
    simp [ColdStepAtMirrorFrames.bondSpread, Fin.sum_univ_add, perturbationList, Perturbation.topBond, Perturbation.topDirection]
  rw [perturbedTop, e]
private theorem jointDisplacement_eq {l j : ℕ} {E : Type}
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → E)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top)
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) :
    jointDisplacement G η V b u c X = fun τ =>
      G (perturbedVariable η (perturbationList b u c X) τ) (perturbedTop V (perturbationList b u c X) τ) := by
  funext τ
  simp only [jointDisplacement]
  rw [displacedPoint_eq η b u c X τ, leftTranslate_eq_perturbedTop V b u c X τ]
private theorem decayWeight_le_exp (w : Perturbation F) (r : ℝ) (x : F.Site F.depth) (i : Fin 4) :
    w.decayWeight r x i ≤ Real.exp (-(r * cellSupDist (enclosingCell x) w.cell)) := by apply _root_.YangMills.SharedProofs.p17086 <;> assumption
private theorem abs_apply_basis_le {i : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin i → ℝ) ℝ) :
    |D fun l => Pi.single l 1| ≤ ‖D‖ := by apply _root_.YangMills.SharedProofs.p22295 <;> assumption
private def partitionBound (B : ℕ → ℕ → ℕ → ℝ) (Cl : ℕ → ℝ) (L : ℕ) (M : ℕ → ℝ) (E : ℝ) (N p : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition p, (N : ℝ) ^ c.length *
    (logNormBound B Cl L c.length c.length * ∏ m, (M (c.partSize m) * E))
private theorem logNormBound_nonneg {B : ℕ → ℕ → ℕ → ℝ} (hB0 : ∀ k n j, 0 ≤ B k n j) {Cl : ℕ → ℝ}
    (hCl0 : ∀ n, 0 ≤ Cl n) (L k n : ℕ) : 0 ≤ logNormBound B Cl L k n := by
  have h : 0 ≤ ∑ i ∈ Finset.range (n + 1), normSqBound B L k i :=
    Finset.sum_nonneg fun i _ => normSqBound_nonneg hB0 _ _ _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCl0 n)) (pow_nonneg (by linarith) _)
private theorem partitionBound_nonneg {B : ℕ → ℕ → ℕ → ℝ} (hB0 : ∀ k n j, 0 ≤ B k n j) {Cl : ℕ → ℝ}
    (hCl0 : ∀ n, 0 ≤ Cl n) (L : ℕ) {M : ℕ → ℝ} (hM : ∀ q, 0 ≤ M q) {E : ℝ} (hE : 0 ≤ E) (N p : ℕ) :
    0 ≤ partitionBound B Cl L M E N p :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (mul_nonneg (logNormBound_nonneg hB0 hCl0 _ _ _)
      (Finset.prod_nonneg fun _ _ => mul_nonneg (hM _) hE))
private theorem log_norm_average_along_motion {B : ℕ → ℕ → ℕ → ℝ} (hB0 : ∀ k n j, 0 ≤ B k n j)
    (hB : HolonomyDerivBounds B)
    {Cl : ℕ → ℝ} (hCl0 : ∀ n, 0 ≤ Cl n) (hCl : ∀ n i, i ≤ n → ∀ y ∈ Set.Icc (1 / 4 : ℝ) 1,
      ‖iteratedFDerivWithin ℝ i halfLog (Set.Ioi 0) y‖ ≤ Cl n)
    (hexp : expansionAlongMotionStatement) {r : ℝ} (hr : 0 ≤ r) {M : ℕ → ℝ} (hM : ∀ q, 0 ≤ M q)
    {R p : ℕ} (hp : 1 ≤ p) {W₀ : F.GaugeField F.depth} (c₀ : F.Site F.top × Fin 4) (w : Fin p → Perturbation F)
    {α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions} (hper : ∀ i, F.period F.depth i ≠ 0)
    (hT : ∀ b, b ∈ fineBonds F) (h1 : 1 / 2 ≤ ‖contourAverage W₀ c₀‖) (h2 : ‖contourAverage W₀ c₀‖ ≤ 1)
    (hα0 : ∀ x i, α 0 x i = 0) (hαs : ∀ x i, ContDiffAt ℝ p (fun τ => α τ x i) 0)
    (hαp : ∀ (q : ℕ) (e : Fin q → Fin p) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ p →
      ‖motionComponent α e x i‖ ≤ M q * (w (e l)).decayWeight r x i)
    (hnear : ∀ b ∈ contourBondSet c₀, cellSupDist c₀.1 (enclosingCell b.1) ≤ R)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) :
    ContDiffAt ℝ p (fun τ => Real.log ‖contourAverage (leftTranslate (α τ) W₀) c₀‖) 0 ∧
    |iteratedFDeriv ℝ p (fun τ => Real.log ‖contourAverage (leftTranslate (α τ) W₀) c₀‖) 0
      (fun l => Pi.single l 1)| ≤
      partitionBound B Cl F.blockSide M (Real.exp (r * R)) (contourStepCount F.blockSide) p *
        Real.exp (-(r * ((Finset.univ.sup fun l => cellSupDist c₀.1 (w l).cell : ℕ) : ℝ))) := by
  classical
  have h0 : contourAverage W₀ c₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    norm_num at h1
  set G : F.GaugeField F.depth → ℝ := fun W => Real.log ‖contourAverage W c₀‖ with hG
  set d : Fin p → ℕ := fun l => cellSupDist c₀.1 (w l).cell with hd
  set E : ℝ := Real.exp (r * R) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hGs : ∀ (N q : ℕ) (c : Fin q → F.Site F.depth × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ N (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c X τ) W₀)) 0 :=
    fun N q c X => contDiffAt_log_norm_average hB W₀ c₀ c X h0 N
  obtain ⟨hsm, hex⟩ := hexp.1 F F.depth p G W₀ α hper (hGs p) hαs hα0
  refine ⟨hsm, ?_⟩
  rw [hex]
  have hterm : ∀ c : OrderedFinpartition p,
      |mixedDerivAlong G W₀ fun m => motionComponent α (c.emb m)| ≤
        (contourStepCount F.blockSide : ℝ) ^ c.length *
          (logNormBound B Cl F.blockSide c.length c.length * ∏ m, (M (c.partSize m) * E)) *
          Real.exp (-(r * ((Finset.univ.sup d : ℕ) : ℝ))) := by
    intro c
    set i := c.length with hi
    set Bi := logNormBound B Cl F.blockSide i i with hBi
    have hBi0 : 0 ≤ Bi := logNormBound_nonneg hB0 hCl0 _ _ _
    have hs := hexp.2 F F.depth i G W₀ (fun m => motionComponent α (c.emb m)) (fineBonds F)
      (fun b => if ∀ m, b m ∈ contourBondSet c₀ then Bi else 0) hper hT (hGs i) (fun b X hX => by
        by_cases hb : ∀ m, b m ∈ contourBondSet c₀
        · rw [if_pos hb]
          exact (abs_apply_basis_le _).trans
            (norm_iteratedFDeriv_log_le hB0 hB hCl W₀ c₀ b X (fun l => (hX l).le) h1 h2 i)
        · rw [if_neg hb]
          push Not at hb
          obtain ⟨l, hl⟩ := hb
          have := iteratedFDeriv_log_eq_zero_of_not_mem hB W₀ c₀ b X l hl h0
          simp only [bondDeriv, hG, this, abs_zero, le_refl])
    have hQ0 : 0 ≤ (∏ m, (M (c.partSize m) * E)) * Real.exp (-(r * ((Finset.univ.sup d : ℕ) : ℝ))) :=
      mul_nonneg (Finset.prod_nonneg fun m _ => mul_nonneg (hM _) hE0) (Real.exp_pos _).le
    have hsum := sum_slots_le (A := fun m => motionComponent α (c.emb m)) (contourBondSet c₀) (fineBonds F)
      hBi0 hQ0
      (fun b hb => prod_le_exp_sup c hp (fun m => mul_nonneg (hM _) hE0) hr d _ (fun m => norm_nonneg _)
        (fun m q => by
          have hw := hαp (c.partSize m) (c.emb m) (b m).1 (b m).2 q (c.partSize_le m)
          refine hw.trans ?_
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (hM _)
          refine (decayWeight_le_exp _ r _ _).trans ?_
          rw [hE, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have h3 := htri c₀.1 (enclosingCell (b m).1) (w (c.emb m q)).cell
          have h4 := hnear (b m) (hb m)
          have h5 : (d (c.emb m q) : ℝ) ≤ R + cellSupDist (enclosingCell (b m).1) (w (c.emb m q)).cell := by
            have : d (c.emb m q) ≤ R + cellSupDist (enclosingCell (b m).1) (w (c.emb m q)).cell := by
              simp only [hd]
              omega
            exact_mod_cast this
          nlinarith [mul_le_mul_of_nonneg_left h5 hr]))
    refine hs.trans (hsum.trans ?_)
    have hcard : ((contourBondSet c₀).card : ℝ) ^ i ≤ (contourStepCount F.blockSide : ℝ) ^ i :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast card_contourBondSet_le c₀) _
    calc ((contourBondSet c₀).card : ℝ) ^ i * (Bi * ((∏ m, (M (c.partSize m) * E)) *
            Real.exp (-(r * ((Finset.univ.sup d : ℕ) : ℝ))))) ≤
          (contourStepCount F.blockSide : ℝ) ^ i * (Bi * ((∏ m, (M (c.partSize m) * E)) *
            Real.exp (-(r * ((Finset.univ.sup d : ℕ) : ℝ))))) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hBi0 hQ0)
      _ = _ := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c _ => hterm c).trans ?_)
  rw [← Finset.sum_mul]
  exact le_rfl
private theorem half_le_norm_contourAverage (hcon : ChartedFieldContourBound) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsm : 5 * (F.blockSide : ℝ) * ε ≤ 1 / 2) (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ ε)
    (c : F.Site F.top × Fin 4) : 1 / 2 ≤ ‖contourAverage (chartedField w V) c‖ := by apply _root_.YangMills.SharedProofs.p7212 <;> assumption
end LogContourDerivSteps
open LogContourDerivSteps in
theorem logContourDerivBounds_holds (hH : HolonomyDerivativeBounds)
    (hmot : motionAboveFrameStatement)
    (hexp : expansionAlongMotionStatement) (hcon : ChartedFieldContourBound)
    (hgeo : CubicTorusCellGeometry) (hcov : BlocksCoverLowerLevel)
    (hdist : SupDistCellComparison) :
    logContourDerivBounds := by
  classical
  obtain ⟨B, hB0, hB⟩ := hH
  have hB' : HolonomyDerivBounds B := hB
  choose Cl hCl0 hCl using exists_halfLog_deriv_bound
  have hCl' : ∀ n i, i ≤ n → ∀ y ∈ Set.Icc (1 / 4 : ℝ) 1,
      ‖iteratedFDerivWithin ℝ i halfLog (Set.Ioi 0) y‖ ≤ Cl n := hCl
  intro K r κ L hK hκ0 hκ hodd
  have hr : 0 ≤ r := by
    have : (0 : ℝ) ≤ 2 ^ 9 * κ := by positivity
    linarith
  let Mof : ℕ → ℕ → ℝ := fun n => (hmot n K hK).choose
  have hMof := fun n : ℕ => (hmot n K hK).choose_spec
  let D : ℕ → ℕ → ℝ := fun l j =>
    partitionBound B Cl L (Mof (l + j)) (Real.exp (r * ((contourStepCount L + 1 : ℕ) : ℝ)))
      (contourStepCount L) (l + j) + 1
  refine ⟨D, fun l j => ?_, ?_⟩
  · have := partitionBound_nonneg hB0 hCl0 L (hMof (l + j)).1
      (Real.exp_pos (r * ((contourStepCount L + 1 : ℕ) : ℝ))).le (contourStepCount L) (l + j)
    simp only [D]
    linarith
  intro F s a ρA ε m V η hFL hcub hε0 hsmall hsize han hdecay c₀ l j b u c X hlj hu hX
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hL0 : 0 < F.blockSide := hoddF.pos
  have hLR : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL0
  obtain ⟨n, hn64, hside⟩ := id hcub
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hper : ∀ i, F.period F.depth i ≠ 0 := fun i => by
    simp only [BlockFrame.period]
    exact mul_ne_zero (hpos i).ne' (pow_ne_zero _ hL0.ne')
  have hall := hcov F hoddF hpos
  have hbond : ∀ b : F.Site F.depth × Fin 4, b ∈ fineBonds F := fun b => by
    simp [fineBonds, hall]
  have hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
    simp [chordBonds, innerBonds, hall, hd]
  have hLeq : (F.blockSide : ℝ) = L := by exact_mod_cast hFL
  have hε10 : ε * (10 * (F.blockSide : ℝ)) ≤ 1 := by
    rw [hLeq]
    exact hsmall
  have hε1 : ε ≤ 1 := by nlinarith
  set p := l + j with hp
  set w : Fin p → Perturbation F := perturbationList b u c X with hw
  have hunit : ∀ l', (w l').IsUnit := by
    intro l'
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l'
    · simpa [hw, perturbationList, Perturbation.IsUnit] using hu i
    · simpa [hw, perturbationList, Perturbation.IsUnit] using hX i
  obtain ⟨α, hα0, hαs, -, hαe, hαp, -⟩ := (hMof p).2 F s a ρA r m p V η w hper
    hr hchart (fun y i h => (hsize (y, i) (hchart _ h)).trans hε1) han hdecay hunit
  set W₀ := interpolatedField s a ρA m V η with hW₀
  have hlow : 1 / 2 ≤ ‖contourAverage W₀ c₀‖ :=
    half_le_norm_contourAverage hcon hoddF hs2 (interpolatedCoords s a ρA m V η) V hε0 (by nlinarith)
      (fun d hd => hsize d hd) c₀
  have hup : ‖contourAverage W₀ c₀‖ ≤ 1 := norm_contourAverage_le_one hoddF W₀ c₀
  obtain ⟨-, -, hcs, htri, hls⟩ := hgeo.1 F hoddF hcub
  have hnear : ∀ d ∈ contourBondSet c₀, cellSupDist c₀.1 (enclosingCell d.1) ≤ contourStepCount L + 1 :=
    fun d hd => by
      have := cellSupDist_contour_le hdist hL0 hoddF hpos hls hcs c₀ d hd
      rwa [hFL] at this
  have hp1 : 1 ≤ p := hlj
  obtain ⟨hsm, hbd⟩ := log_norm_average_along_motion hB0 hB' hCl0 hCl' hexp hr (hMof p).1 hp1 c₀ w hper
    hbond hlow hup hα0 hαs (fun q e y i l' hq => hαp q e y i l' hq) hnear htri
  set G' : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun ζ V' => Real.log ‖contourAverage (interpolatedField s a ρA m V' ζ) c₀‖ with hG'
  have hev : jointDisplacement G' η V b u c X =ᶠ[𝓝 0]
      fun τ => Real.log ‖contourAverage (leftTranslate (α τ) W₀) c₀‖ := by
    rw [jointDisplacement_eq]
    exact hαe.mono fun τ h => by
      simp only [hG']
      rw [h]
  refine ⟨hsm.congr_of_eventuallyEq hev, ?_⟩
  show |iteratedFDeriv ℝ p (jointDisplacement G' η V b u c X) 0 (fun i => Pi.single i 1)| ≤ _
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev p).eq_of_nhds]
  rw [hFL] at hbd
  refine hbd.trans ?_
  set Dm : ℕ := Finset.univ.sup fun l' => cellSupDist c₀.1 (w l').cell with hDm
  have hmem : ∀ l', cellSupDist c₀.1 (w l').cell ≤ Dm := fun l' =>
    Finset.le_sup (f := fun l' => cellSupDist c₀.1 (w l').cell) (Finset.mem_univ l')
  have hin : ∀ v ∈ ({c₀.1} ∪ chordBondCells b ∪ topBondCells c : Finset F.Cell), cellSupDist c₀.1 v ≤ Dm := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · rcases Finset.mem_union.1 hv with hv | hv
      · rw [Finset.mem_singleton.1 hv]
        simp [cellSupDist]
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
        have := hmem (Fin.castAdd j i)
        simpa [hw, perturbationList, Perturbation.cell] using this
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      have := hmem (Fin.natAdd l i)
      simpa [hw, perturbationList, Perturbation.cell] using this
  have hspan : cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c) ≤ 2 * Dm := by
    refine Finset.sup_le fun v hv => Finset.sup_le fun v' hv' => ?_
    have h1 := htri v c₀.1 v'
    rw [hcs v c₀.1] at h1
    have h2 := hin v hv
    have h3 := hin v' hv'
    omega
  have hspanR : (cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c) : ℝ) ≤ 2 * Dm := by
    exact_mod_cast hspan
  have hexpo : -(r * (Dm : ℝ)) ≤
      -(2 ^ 8 * κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c)) := by
    have h1 : 2 ^ 8 * κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c) ≤
        2 ^ 8 * κ * (2 * Dm) := mul_le_mul_of_nonneg_left hspanR (by positivity)
    have h2 : 2 ^ 9 * κ * (Dm : ℝ) ≤ r * Dm := mul_le_mul_of_nonneg_right hκ (Nat.cast_nonneg _)
    linarith
  have hnum := partitionBound_nonneg hB0 hCl0 L (hMof p).1
    (Real.exp_pos (r * ((contourStepCount L + 1 : ℕ) : ℝ))).le (contourStepCount L) p
  have hD1 : D l j = partitionBound B Cl L (Mof p)
      (Real.exp (r * ((contourStepCount L + 1 : ℕ) : ℝ))) (contourStepCount L) p + 1 := rfl
  rw [hD1]
  calc _ ≤ partitionBound B Cl L (Mof p)
        (Real.exp (r * ((contourStepCount L + 1 : ℕ) : ℝ))) (contourStepCount L) p *
        Real.exp (-(2 ^ 8 * κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexpo) hnum
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
end Interpolation
end YangMills.Construction
end
