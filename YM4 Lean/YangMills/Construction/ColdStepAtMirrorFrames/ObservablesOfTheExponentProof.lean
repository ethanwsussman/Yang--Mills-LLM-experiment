import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.ColdStepAtMirrorFrames.ObservablesOfTheExponent
import YangMills.Construction.SummableBoundsOfTheFlow.PartsOfAnExponentHaveTheirSizesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages Topology
namespace ExponentObservables
variable {F : BlockFrame}
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem chordBondDist_isPseudoMetric : IsPseudoMetricOnBonds (chordBondDist F) where
  self b := by simp [chordBondDist, cellSupDist_self]
  symm b b' := by simp only [chordBondDist]; rw [cellSupDist_comm]
  triangle b b' b'' := by
    simp only [chordBondDist]
    exact_mod_cast cellSupDist_triangle _ _ _
theorem cellSupDist_le_bondSpan (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (l : Fin k) :
    cellSupDist Y (c l).1 ≤ bondSpan Y c :=
  le_max_of_le_left (Finset.le_sup (f := fun l : Fin k => siteSupDist Y (c l).1) (Finset.mem_univ l))
theorem cellSupDist_pair_le_bondSpan (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (l l' : Fin k) :
    cellSupDist (c l).1 (c l').1 ≤ bondSpan Y c := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.cellSupDist_pair_le_bondSpan <;> assumption
theorem bondSpan_le_of {Y : F.Cell} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {n : ℕ}
    (h1 : ∀ l, cellSupDist Y (c l).1 ≤ n) (h2 : ∀ l l', cellSupDist (c l).1 (c l').1 ≤ n) : bondSpan Y c ≤ n :=
  max_le (Finset.sup_le fun l _ => h1 l) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => h2 l l')
theorem bondSpan_le_bondSpanWithCell (Y z : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ bondSpanWithCell Y z c := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.bondSpan_le_bondSpanWithCell <;> assumption
theorem cellSupDist_le_bondSpanWithCell (Y z : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) :
    cellSupDist Y z ≤ bondSpanWithCell Y z c := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.cellSupDist_le_bondSpanWithCell <;> assumption
theorem cellSupDist_pair_le_bondSpanWithCell (Y z : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (l : Fin k) :
    cellSupDist z (c l).1 ≤ bondSpanWithCell Y z c := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.cellSupDist_pair_le_bondSpanWithCell <;> assumption
theorem bondSpan_at_le (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (l : Fin k) :
    bondSpan (c l).1 c ≤ bondSpan Y c :=
  bondSpan_le_of (fun l' => cellSupDist_pair_le_bondSpan Y c l l') (fun l' l'' => cellSupDist_pair_le_bondSpan Y c l' l'')
section QuadraticBounds
variable {ι : Type} [Fintype ι] {ρ x W₀ : ℝ}
theorem quadBound_mono {B B' a a' : ℝ} {H : BondField ι → ℝ} (hx : 0 ≤ x) (hB : B ≤ B') (ha : a ≤ a')
    (h : IsQuadraticallyBoundedOnBalls ρ x W₀ B a H) : IsQuadraticallyBoundedOnBalls ρ x W₀ B' a' H := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.quadBound_mono <;> assumption
theorem quadBound_of_abs_le {B a : ℝ} {H H' : BondField ι → ℝ}
    (hle : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H' η| ≤ |H η|)
    (h : IsQuadraticallyBoundedOnBalls ρ x W₀ B a H) : IsQuadraticallyBoundedOnBalls ρ x W₀ B a H' := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.quadBound_of_abs_le <;> assumption
theorem quadBound_sum {α : Type} (S : Finset α) {B : ℝ} (a : α → ℝ) (H : α → BondField ι → ℝ) (hB : 0 ≤ B)
    (hW₀ : 0 ≤ W₀) (h : ∀ i ∈ S, IsQuadraticallyBoundedOnBalls ρ x W₀ B (a i) (H i)) :
    IsQuadraticallyBoundedOnBalls ρ x W₀ B (∑ i ∈ S, a i) (fun η => ∑ i ∈ S, H i η) := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.quadBound_sum <;> assumption
theorem quadBound_scale {B a S : ℝ} {H : BondField ι → ℝ} (hS : 0 < S)
    (h : IsQuadraticallyBoundedOnBalls ρ x W₀ B (S * a) H) : IsQuadraticallyBoundedOnBalls ρ x W₀ (S * B) a H := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.quadBound_scale <;> assumption
end QuadraticBounds
section CellBounds
variable {ρ x κ : ℝ}
abbrev openBalls (F : BlockFrame) (ρ : ℝ) : Set (StepVariable (finiteCells F)) := {η | ∀ b, ‖η b‖ < ρ}
theorem isOpen_openBalls (ρ : ℝ) : IsOpen (openBalls F ρ) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.isOpen_bondBall <;> assumption
structure CellBound (ρ x κ C : ℝ) (Y : F.Cell) (n : ℕ) (nb : ↥(chordBonds (finiteCells F)) → ℕ)
    (H : StepVariable (finiteCells F) → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 1 H (openBalls F ρ)
  abs_le : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
    |H η| ≤ C * (x * localSqNorm κ Y η + 1) * Real.exp (-(2 ^ 6 * κ * n))
  partial_le : ∀ (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))), (∀ b, ‖η b‖ < ρ) →
    bondGradNorm H b η ≤ C * (x * Real.sqrt (localSqNorm κ Y η) + 1) * Real.exp (-(2 ^ 6 * κ * nb b))
theorem localSqNorm_nonneg (Y : F.Cell) (η : StepVariable (finiteCells F)) :
    0 ≤ localSqNorm κ Y η :=
  Finset.sum_nonneg fun b _ => by positivity
theorem bondGradNorm_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] (f : BondField ι → ℝ) (b : ι)
    (η : BondField ι) : 0 ≤ bondGradNorm f b η := norm_nonneg _
def CellWeightSumLE (F : BlockFrame) (κ W₀ : ℝ) : Prop :=
  ∀ Y : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
    Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ W₀
theorem quadBound_of_value {W₀ C : ℝ} {Y : F.Cell} {n : ℕ} {H : StepVariable (finiteCells F) → ℝ}
    (hW : CellWeightSumLE F κ W₀) (hC : 0 ≤ C)
    (hv : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      |H η| ≤ C * (x * localSqNorm κ Y η + 1) * Real.exp (-(2 ^ 6 * κ * n))) :
    IsQuadraticallyBoundedOnBalls ρ x W₀ C (Real.exp (-(2 ^ 6 * κ * n))) H := by
  set A := Real.exp (-(2 ^ 6 * κ * n)) with hA
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  refine ⟨fun b => A * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)), A, hA0, le_rfl,
    fun b => by positivity, ?_, fun η hη => ?_⟩
  · rw [← Finset.mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hW Y) hA0
  · have e : x * ∑ b : ↥(chordBonds (finiteCells F)),
          A * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖η b‖ ^ 2 + A =
        (x * localSqNorm κ Y η + 1) * A := by
      have : ∑ b : ↥(chordBonds (finiteCells F)),
            A * Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖η b‖ ^ 2 =
          A * localSqNorm κ Y η := by
        unfold localSqNorm
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [this]
      ring
    rw [e, ← mul_assoc]
    exact hv η hη
private theorem mul_sqrt_add_one_le {x s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) :
    x * Real.sqrt s + 1 ≤ Real.sqrt x * 2 * (x * s + 1) := by apply _root_.YangMills.SharedProofs.p56556 <;> assumption
theorem quadBound_of_gradient {W₀ C : ℝ} {Y : F.Cell} {n : ℕ} {G : StepVariable (finiteCells F) → ℝ}
    (hW : CellWeightSumLE F κ W₀) (hC : 0 ≤ C) (hx : 1 ≤ x) (hG0 : ∀ η, 0 ≤ G η)
    (hv : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      G η ≤ C * (x * Real.sqrt (localSqNorm κ Y η) + 1) * Real.exp (-(2 ^ 6 * κ * n))) :
    IsQuadraticallyBoundedOnBalls ρ x W₀ (Real.sqrt x * (2 * C)) (Real.exp (-(2 ^ 6 * κ * n))) G := by
  refine quadBound_of_value (Y := Y) hW (by positivity) fun η hη => ?_
  rw [abs_of_nonneg (hG0 η)]
  refine (hv η hη).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have := mul_sqrt_add_one_le hx (localSqNorm_nonneg (κ := κ) Y η)
  calc C * (x * Real.sqrt (localSqNorm κ Y η) + 1)
      ≤ C * (Real.sqrt x * 2 * (x * localSqNorm κ Y η + 1)) := mul_le_mul_of_nonneg_left this hC
    _ = Real.sqrt x * (2 * C) * (x * localSqNorm κ Y η + 1) := by ring
theorem cellBound_bondDeriv_cellExponent {a ρA C : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hDer : Calculus.IteratedFDerivParamDiff)
    (hE : CellExponentBounds false a ρA ρ x κ C m V) (hC : 0 ≤ C) (hκ : 0 ≤ κ) (Y : F.Cell) {k : ℕ}
    (hk : k ≤ 3) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (hs4 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        cellExponent false a ρA x m Y (leftTranslate (bondSpread c X q.1) V) q.2) (0, η)) (hx : 0 ≤ x) :
    CellBound ρ x κ C Y (bondSpan Y c) (fun b => bondSpanWithCell Y (enclosingCell b.1.1) c)
      (fun η => bondDeriv (fun V' => cellExponent false a ρA x m Y V' η) V c X) := by
  set G : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun q =>
    cellExponent false a ρA x m Y (leftTranslate (bondSpread c X q.1) V) q.2 with hG
  have hdk : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
      ContDiffAt ℝ 1 (fun ζ => iteratedFDeriv ℝ k (fun s => G (s, ζ)) 0 (fun l => Pi.single l 1)) η ∧
      ∀ e : StepVariable (finiteCells F),
        fderiv ℝ (fun ζ => iteratedFDeriv ℝ k (fun s => G (s, ζ)) 0 (fun l => Pi.single l 1)) η e =
          iteratedFDeriv ℝ k (fun s => fderiv ℝ (fun ζ => G (s, ζ)) η e) 0 (fun l => Pi.single l 1) :=
    fun η hη => hDer (Fin k → ℝ) (StepVariable (finiteCells F)) k G η (fun l => Pi.single l 1)
      ((hs4 η fun b => (hη b).le).of_le (by norm_cast; omega))
  refine ⟨fun η hη => (hdk η hη).1.contDiffWithinAt, fun η hη => ?_, fun η b hη => ?_⟩
  · exact hE.deriv_top Y η k c X hη hk hX
  · set B := C * (x * Real.sqrt (localSqNorm κ Y η) + 1) *
      Real.exp (-(2 ^ 6 * κ * bondSpanWithCell Y (enclosingCell b.1.1) c)) with hB
    have hB0 : 0 ≤ B := by
      have := Real.sqrt_nonneg (localSqNorm κ Y η)
      positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun e => ?_
    rw [ContinuousLinearMap.comp_apply]
    by_cases he : e = 0
    · simp [he]
    have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
    set e' : BondVector := ‖e‖⁻¹ • e with he'
    have hunit : ‖e'‖ = 1 := by
      rw [he', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    have hsc : ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b e =
        ‖e‖ • bondVariation b e' := by
      have h0 : ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b e =
          Pi.single b e := rfl
      rw [h0, bondVariation, he', ← Pi.single_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
    have hslope := hE.deriv_top_partial Y η b e' k c X hη hk hX hunit
    have hval : fderiv ℝ (fun ζ => bondDeriv (fun V' => cellExponent false a ρA x m Y V' ζ) V c X) η
          (bondVariation b e') =
        bondDeriv (fun V' => bondPartialDeriv (cellExponent false a ρA x m Y V') b η e') V c X :=
      (hdk η hη).2 (bondVariation b e')
    rw [hsc, map_smul, hval, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right hslope (norm_nonneg e)
theorem CellBound.mono {C C' : ℝ} {Y : F.Cell} {n : ℕ} {nb : ↥(chordBonds (finiteCells F)) → ℕ}
    {H : StepVariable (finiteCells F) → ℝ} (hx : 0 ≤ x) (hC : C ≤ C') (h : CellBound ρ x κ C Y n nb H) :
    CellBound ρ x κ C' Y n nb H := by
  refine ⟨h.contDiffOn, fun η hη => (h.abs_le η hη).trans ?_, fun η b hη => (h.partial_le η b hη).trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hC
      (add_nonneg (mul_nonneg hx (localSqNorm_nonneg Y η)) zero_le_one)
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hC
      (add_nonneg (mul_nonneg hx (Real.sqrt_nonneg _)) zero_le_one)
theorem CellBound.congr {C : ℝ} {Y : F.Cell} {n : ℕ} {nb : ↥(chordBonds (finiteCells F)) → ℕ}
    {H H' : StepVariable (finiteCells F) → ℝ} (h : CellBound ρ x κ C Y n nb H)
    (he : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → H' η = H η) :
    CellBound ρ x κ C Y n nb H' := by
  refine ⟨h.contDiffOn.congr fun η hη => he η hη, fun η hη => ?_, fun η b hη => ?_⟩
  · rw [he η hη]
    exact h.abs_le η hη
  · have hev : H' =ᶠ[𝓝 η] H := by
      filter_upwards [(isOpen_openBalls ρ).mem_nhds (show η ∈ openBalls F ρ from hη)] with ζ hζ using he ζ hζ
    have : bondGradNorm H' b η = bondGradNorm H b η := by
      unfold bondGradNorm
      rw [hev.fderiv_eq]
    rw [this]
    exact h.partial_le η b hη
theorem cellQuadratic_fderiv (lam : ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (e : BondVector) :
    DifferentiableAt ℝ (cellQuadratic (F := F) lam x Y) η ∧
    fderiv ℝ (cellQuadratic (F := F) lam x Y) η (Pi.single b e) =
      if enclosingCell b.1.1 = Y then x * lam / 2 * (2 * inner ℝ (η b) e) else 0 := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.cellQuadratic_fderiv <;> assumption
theorem cellQuadratic_contDiff (lam : ℝ) (Y : F.Cell) : ContDiff ℝ 4 (cellQuadratic (F := F) lam x Y) := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.cellQuadratic_contDiff <;> assumption
theorem sq_norm_le_localSqNorm (Y : F.Cell) (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
    (h : enclosingCell b.1.1 = Y) : ‖η b‖ ^ 2 ≤ localSqNorm κ Y η := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.sq_norm_le_localSqNorm <;> assumption
theorem abs_cellQuadratic_le {lam : ℝ} (hlam : 0 ≤ lam) (hx : 0 ≤ x) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) :
    |cellQuadratic lam x Y η| ≤ lam * (x * localSqNorm κ Y η + 1) := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.abs_cellQuadratic_le <;> assumption
theorem cellBound_sub_cellQuadratic {C lam : ℝ} {n : ℕ} (hn : n = 0) {nb : ↥(chordBonds (finiteCells F)) → ℕ}
    {Y : F.Cell} {H : StepVariable (finiteCells F) → ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hnb : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → nb b = 0)
    (h : CellBound ρ x κ C Y n nb H) :
    CellBound ρ x κ (C + lam) Y n nb (fun η => H η - cellQuadratic lam x Y η) := by
  subst hn
  have hsm : ContDiffOn ℝ 1 (fun η => H η - cellQuadratic lam x Y η) (openBalls F ρ) :=
    h.contDiffOn.sub ((cellQuadratic_contDiff lam Y).of_le (by norm_num)).contDiffOn
  refine ⟨hsm, fun η hη => ?_, fun η b hη => ?_⟩
  · have h1 := h.abs_le η hη
    have h2 := abs_cellQuadratic_le (κ := κ) hlam hx Y η
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1 ⊢
    calc |H η - cellQuadratic lam x Y η| ≤ |H η| + |cellQuadratic lam x Y η| := abs_sub _ _
      _ ≤ C * (x * localSqNorm κ Y η + 1) + lam * (x * localSqNorm κ Y η + 1) := add_le_add h1 h2
      _ = (C + lam) * (x * localSqNorm κ Y η + 1) := by ring
  · have hdH : DifferentiableAt ℝ H η :=
      (h.contDiffOn.contDiffAt ((isOpen_openBalls ρ).mem_nhds (show η ∈ openBalls F ρ from hη))).differentiableAt
        (by simp)
    have hdq := (cellQuadratic_fderiv (x := x) lam Y η b 0).1
    have hf : fderiv ℝ (fun η => H η - cellQuadratic lam x Y η) η =
        fderiv ℝ H η - fderiv ℝ (cellQuadratic lam x Y) η :=
      fderiv_fun_sub hdH hdq
    have hbd : 0 ≤ (C + lam) * (x * Real.sqrt (localSqNorm κ Y η) + 1) * Real.exp (-(2 ^ 6 * κ * nb b)) := by
      positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hbd fun e => ?_
    rw [ContinuousLinearMap.comp_apply, hf, ContinuousLinearMap.sub_apply]
    have h0 : ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b e =
        Pi.single b e := rfl
    have hH1 : ‖fderiv ℝ H η (Pi.single b e)‖ ≤ bondGradNorm H b η * ‖e‖ :=
      ((fderiv ℝ H η).comp
        (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b)).le_opNorm e
    have hH2 := h.partial_le η b hη
    have hq : ‖fderiv ℝ (cellQuadratic lam x Y) η (Pi.single b e)‖ ≤
        lam * (x * Real.sqrt (localSqNorm κ Y η) + 1) * Real.exp (-(2 ^ 6 * κ * nb b)) * ‖e‖ := by
      rw [(cellQuadratic_fderiv (x := x) lam Y η b e).2]
      split_ifs with hb
      · rw [hnb b hb]
        simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
        have hin : |inner ℝ (η b) e| ≤ ‖η b‖ * ‖e‖ := abs_real_inner_le_norm _ _
        have hsq : ‖η b‖ ≤ Real.sqrt (localSqNorm κ Y η) :=
          Real.le_sqrt_of_sq_le (sq_norm_le_localSqNorm Y η b hb)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x * lam / 2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have h3 : x * lam / 2 * (2 * |inner ℝ (η b) e|) ≤
            x * lam / 2 * (2 * (Real.sqrt (localSqNorm κ Y η) * ‖e‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hin.trans (mul_le_mul_of_nonneg_right hsq (norm_nonneg e))
        refine h3.trans ?_
        have : 0 ≤ lam * ‖e‖ := by positivity
        nlinarith
      · simp only [norm_zero]
        positivity
    rw [h0]
    calc ‖fderiv ℝ H η (Pi.single b e) - fderiv ℝ (cellQuadratic lam x Y) η (Pi.single b e)‖
        ≤ ‖fderiv ℝ H η (Pi.single b e)‖ + ‖fderiv ℝ (cellQuadratic lam x Y) η (Pi.single b e)‖ :=
          norm_sub_le _ _
      _ ≤ C * (x * Real.sqrt (localSqNorm κ Y η) + 1) * Real.exp (-(2 ^ 6 * κ * nb b)) * ‖e‖ +
          lam * (x * Real.sqrt (localSqNorm κ Y η) + 1) * Real.exp (-(2 ^ 6 * κ * nb b)) * ‖e‖ :=
        add_le_add (hH1.trans (mul_le_mul_of_nonneg_right hH2 (norm_nonneg e))) hq
      _ = (C + lam) * (x * Real.sqrt (localSqNorm κ Y η) + 1) * Real.exp (-(2 ^ 6 * κ * nb b)) * ‖e‖ := by
          ring
theorem bondDeriv_zero {j : ℕ} (g : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv g W c X = g W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem bondDeriv_sub_const {j k : ℕ} (hk : k ≠ 0) (g : F.GaugeField j → ℝ) (r : ℝ) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hg : ContDiffAt ℝ k (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun V' => g V' - r) W c X = bondDeriv g W c X := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.bondDeriv_sub_const <;> assumption
theorem bondGradNorm_const_mul_sum_le {α ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset α)
    (f : α → BondField ι → ℝ) {v : ℝ}
    (hv : |v| ≤ 1) {η : BondField ι} (hd : ∀ i ∈ S, DifferentiableAt ℝ (f i) η) (b : ι) :
    bondGradNorm (fun η => v * ∑ i ∈ S, f i η) b η ≤ ∑ i ∈ S, bondGradNorm (f i) b η := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.bondGradNorm_const_mul_sum_le <;> assumption
theorem exp_decay_le_two {κ : ℝ} (hκ : 0 < κ) {n S d : ℕ} (h1 : n ≤ S) (h2 : d ≤ S) :
    Real.exp (-(2 ^ 6 * κ * S)) ≤ Real.exp (-(2 ^ 5 * κ * n)) * Real.exp (-(2 * κ * d)) := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.exp_decay_split_two <;> assumption
theorem exp_decay_le_split {κ : ℝ} (hκ : 0 < κ) {D S d : ℕ} (h1 : D ≤ S) (h2 : d ≤ S) :
    Real.exp (-(2 ^ 6 * κ * S)) ≤ Real.exp (-(2 ^ 4 * κ * D)) * Real.exp (-(2 ^ 5 * κ * d)) := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.exp_decay_split_span <;> assumption
theorem exp_decay_le_three {κ : ℝ} (hκ : 0 < κ) {D S d e : ℕ} (h1 : D ≤ S) (h2 : d ≤ S) (h3 : e ≤ S) :
    Real.exp (-(2 ^ 6 * κ * S)) ≤
      Real.exp (-(2 ^ 4 * κ * D)) * Real.exp (-(2 * κ * e)) * Real.exp (-(2 ^ 5 * κ * d)) := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.exp_decay_split_three <;> assumption
theorem exp_decay_le_half_rate {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    Real.exp (-(2 ^ 6 * κ * n)) ≤ Real.exp (-(2 ^ 5 * κ * n)) := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.exp_decay_mono_rate <;> assumption
theorem cellBound_cellObservable {a ρA C lam : ℝ} {m : ℕ} {V : F.GaugeField F.top} {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (Y : F.Cell) (hx0 : 0 < x)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hb : CellBound ρ x κ C Y (bondSpan Y c) (fun b => bondSpanWithCell Y (enclosingCell b.1.1) c)
      (fun η => bondDeriv (fun V' => cellExponent false a ρA x m Y V' η) V c X))
    (hs4 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        cellExponent false a ρA x m Y (leftTranslate (bondSpread c X q.1) V) q.2) (0, η)) (hk : k ≤ 3) :
    CellBound ρ x κ (C + lam) Y (bondSpan Y c) (fun b => bondSpanWithCell Y (enclosingCell b.1.1) c)
      (cellObservable a ρA lam x m Y V c X) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hnb : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y →
        bondSpanWithCell Y (enclosingCell b.1.1) c = 0 := by
      intro b hb'
      rw [hb']
      apply Nat.le_zero.mp
      refine bondSpan_le_of (fun l => ?_) (fun l l' => ?_)
      · have : l = 0 := Fin.fin_one_eq_zero l
        subst this
        simp [cellSupDist_self]
      · have h1 : l = 0 := Fin.fin_one_eq_zero l
        have h2 : l' = 0 := Fin.fin_one_eq_zero l'
        subst h1 h2
        simp [cellSupDist_self]
    have h0 := cellBound_sub_cellQuadratic (lam := lam) (by simp [bondSpan]) hx0.le hC hlam hnb hb
    refine h0.congr fun η _ => ?_
    unfold cellObservable
    rw [bondDeriv_zero, bondDeriv_zero]
  · refine (hb.mono hx0.le (by linarith)).congr fun η hη => ?_
    unfold cellObservable
    refine bondDeriv_sub_const (by omega) _ _ V c X ?_
    have h4 := hs4 η fun b => (hη b).le
    have hp : ContDiffAt ℝ 4 (fun s : Fin k → ℝ => (s, η)) 0 := contDiffAt_id.prodMk contDiffAt_const
    have h5 := ContDiffAt.comp (0 : Fin k → ℝ) h4 hp
    exact h5.of_le (by norm_cast; omega)
theorem quadBound_exponentObservable {a ρA C W₀ S B v : ℝ} {m : ℕ} {V : F.GaugeField F.top} {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : Fin k) (hκ : 0 < κ) (hx0 : 0 < x)
    (hC : 0 ≤ C) (hW₀0 : 0 ≤ W₀) (hS0 : 0 < S) (hB : (1 + S) * C ≤ B) (hv : |v| ≤ 1)
    (hWB : CellWeightSumLE F κ W₀)
    (hS : ∀ z : F.Cell, ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 5 * κ * siteSupDist z Y')) ≤ S)
    (hb : ∀ Y' : F.Cell, CellBound ρ x κ C Y' (bondSpan Y' c) (fun b => bondSpanWithCell Y' (enclosingCell b.1.1) c)
      (fun η => bondDeriv (fun V' => cellExponent false a ρA x m Y' V' η) V c X)) :
    IsQuadraticallyBoundedOnBalls ρ x W₀ B (Real.exp (-(2 ^ 4 * κ * bondSpan (c l).1 c)))
      (fun η => v * exponentObservable a ρA x m V c X η) := by
  set z := (c l).1 with hz
  set h₂ := Real.exp (-(2 ^ 4 * κ * bondSpan z c)) with hh₂
  have hh₂0 : 0 ≤ h₂ := (Real.exp_pos _).le
  have hS1 : (0 : ℝ) < 1 + S := by linarith
  have h1 := quadBound_sum (ρ := ρ) (x := x) (W₀ := W₀) (finiteCells F) (B := C)
    (fun Y' => Real.exp (-(2 ^ 6 * κ * bondSpan Y' c)))
    (fun Y' η => bondDeriv (fun V' => cellExponent false a ρA x m Y' V' η) V c X) hC hW₀0
    (fun Y' _ => quadBound_of_value hWB hC (hb Y').abs_le)
  have h2 : ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 6 * κ * bondSpan Y' c)) ≤ (1 + S) * h₂ := by
    calc ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 6 * κ * bondSpan Y' c))
        ≤ ∑ Y' ∈ finiteCells F, h₂ * Real.exp (-(2 ^ 5 * κ * siteSupDist z Y')) := by
          refine Finset.sum_le_sum fun Y' _ => ?_
          have d1 : siteSupDist z Y' ≤ bondSpan Y' c := by
            have := cellSupDist_le_bondSpan Y' c l
            rw [cellSupDist_comm] at this
            exact this
          exact exp_decay_le_split hκ (bondSpan_at_le Y' c l) d1
      _ = h₂ * ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 5 * κ * siteSupDist z Y')) := by
          rw [Finset.mul_sum]
      _ ≤ h₂ * S := mul_le_mul_of_nonneg_left (hS z) hh₂0
      _ ≤ (1 + S) * h₂ := by nlinarith
  have h3 := quadBound_scale hS1 (quadBound_mono hx0.le le_rfl h2 h1)
  refine quadBound_mono hx0.le hB le_rfl (quadBound_of_abs_le (fun η _ => ?_) h3)
  show |v * exponentObservable a ρA x m V c X η| ≤ |exponentObservable a ρA x m V c X η|
  rw [abs_mul]
  calc |v| * |exponentObservable a ρA x m V c X η| ≤ 1 * |exponentObservable a ρA x m V c X η| :=
        mul_le_mul_of_nonneg_right hv (abs_nonneg _)
    _ = _ := one_mul _
theorem quadBound_bondGradNorm_exponentObservable {a ρA C W₀ S B v : ℝ} {m : ℕ} {V : F.GaugeField F.top} {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : Fin k) (hκ : 0 < κ) (hx : 1 ≤ x)
    (hC : 0 ≤ C) (hW₀0 : 0 ≤ W₀) (hS0 : 0 < S) (hB : (1 + S) * (2 * C) ≤ B) (hv : |v| ≤ 1)
    (hWB : CellWeightSumLE F κ W₀)
    (hS : ∀ z : F.Cell, ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 5 * κ * siteSupDist z Y')) ≤ S)
    (hb : ∀ Y' : F.Cell, CellBound ρ x κ C Y' (bondSpan Y' c) (fun b => bondSpanWithCell Y' (enclosingCell b.1.1) c)
      (fun η => bondDeriv (fun V' => cellExponent false a ρA x m Y' V' η) V c X))
    (b : ↥(chordBonds (finiteCells F))) :
    IsQuadraticallyBoundedOnBalls ρ x W₀ (Real.sqrt x * B)
      (Real.exp (-(2 ^ 4 * κ * bondSpan (c l).1 c)) *
        Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) (c l).1 : ℝ))))
      (bondGradNorm (fun η => v * exponentObservable a ρA x m V c X η) b) := by
  have hx0 : 0 < x := by linarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  set z := (c l).1 with hz
  set h₂ := Real.exp (-(2 ^ 4 * κ * bondSpan z c)) with hh₂
  have hS1 : (0 : ℝ) < 1 + S := by linarith
  set e₂ := Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) with he₂
  have h1 := quadBound_sum (ρ := ρ) (x := x) (W₀ := W₀) (finiteCells F) (B := Real.sqrt x * (2 * C))
    (fun Y' => Real.exp (-(2 ^ 6 * κ * bondSpanWithCell Y' (enclosingCell b.1.1) c)))
    (fun Y' η => bondGradNorm (fun η => bondDeriv (fun V' => cellExponent false a ρA x m Y' V' η) V c X) b η)
    (by positivity) hW₀0
    (fun Y' _ => quadBound_of_gradient (Y := Y') hWB hC hx (fun η => bondGradNorm_nonneg _ b η)
      (fun η hη => (hb Y').partial_le η b hη))
  have h2 : ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 6 * κ * bondSpanWithCell Y' (enclosingCell b.1.1) c)) ≤
      (1 + S) * (h₂ * e₂) := by
    have hhe : 0 ≤ h₂ * e₂ := by positivity
    calc ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 6 * κ * bondSpanWithCell Y' (enclosingCell b.1.1) c))
        ≤ ∑ Y' ∈ finiteCells F, h₂ * e₂ * Real.exp (-(2 ^ 5 * κ * siteSupDist z Y')) := by
          refine Finset.sum_le_sum fun Y' _ => ?_
          have d1 : siteSupDist z Y' ≤ bondSpanWithCell Y' (enclosingCell b.1.1) c := by
            have := cellSupDist_le_bondSpan Y' c l
            rw [cellSupDist_comm] at this
            exact this.trans (bondSpan_le_bondSpanWithCell _ _ c)
          have d2 : cellSupDist (enclosingCell b.1.1) z ≤ bondSpanWithCell Y' (enclosingCell b.1.1) c :=
            cellSupDist_pair_le_bondSpanWithCell Y' _ c l
          exact exp_decay_le_three hκ ((bondSpan_at_le Y' c l).trans (bondSpan_le_bondSpanWithCell _ _ c)) d1 d2
      _ = h₂ * e₂ * ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 5 * κ * siteSupDist z Y')) := by
          rw [Finset.mul_sum]
      _ ≤ h₂ * e₂ * S := mul_le_mul_of_nonneg_left (hS z) hhe
      _ ≤ (1 + S) * (h₂ * e₂) := by nlinarith
  have h3 := quadBound_scale hS1 (quadBound_mono hx0.le le_rfl h2 h1)
  refine quadBound_mono hx0.le ?_ le_rfl (quadBound_of_abs_le (fun η hη => ?_) h3)
  · calc (1 + S) * (Real.sqrt x * (2 * C)) = Real.sqrt x * ((1 + S) * (2 * C)) := by ring
      _ ≤ Real.sqrt x * B := mul_le_mul_of_nonneg_left hB hsx
  · have hle := bondGradNorm_const_mul_sum_le (finiteCells F)
      (fun Y' η => bondDeriv (fun V' => cellExponent false a ρA x m Y' V' η) V c X) hv
      (fun Y' _ => ((hb Y').contDiffOn.contDiffAt
        ((isOpen_openBalls ρ).mem_nhds (show η ∈ openBalls F ρ from hη))).differentiableAt (by simp)) b
    rw [abs_of_nonneg (bondGradNorm_nonneg _ b η)]
    have hsum0 : 0 ≤ ∑ Y' ∈ finiteCells F,
        bondGradNorm (fun η => bondDeriv (fun V' => cellExponent false a ρA x m Y' V' η) V c X) b η :=
      Finset.sum_nonneg fun Y' _ => bondGradNorm_nonneg _ b η
    rw [abs_of_nonneg hsum0]
    exact hle
end CellBounds
end ExponentObservables
theorem ExponentObservables.cellBonds_card_le (hFew : Estimates.cellBondsCardStatement) (F : BlockFrame)
    (hL : Odd F.blockSide) (hside : ∀ i, 2 ≤ F.extent i) (z : F.Cell) :
    (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      4 * F.blockSide ^ 4 :=
  hFew F hL hside z
open ExponentObservables in
theorem ExponentObservables.exponentObservableBounds_holds (hDer : Calculus.IteratedFDerivParamDiff)
    (hSize : LocalSizeOfQuadraticBounds) (hMom : momentBoundOfQuadraticBound)
    (hDecay : _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpDecaySumBounded) (hWt : CellCounting.ExpDecaySumBounded)
    (hFew : Estimates.cellBondsCardStatement) : ExponentObservableBounds := by
  intro L κ lam C hL hκ hlam hC
  obtain ⟨W₀, hW₀0, hW₀⟩ := hWt (4 * L ^ 4) (2 ^ 6 * κ) (by positivity)
  obtain ⟨W, hW0, hW⟩ := hWt (4 * L ^ 4) (2 * κ) (by positivity)
  obtain ⟨S, hS0, hS⟩ := hDecay (2 ^ 5 * κ) (by positivity)
  have hC₁0 : 0 ≤ C + lam := by positivity
  have hB0 : 0 ≤ (1 + S) * (2 * (C + lam)) := by positivity
  have hnum : ∀ q, 0 ≤ lpMomentConstant lam W₀ W q := fun q => by
    have : 0 ≤ ∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W) := Finset.prod_nonneg fun k _ => by positivity
    unfold lpMomentConstant
    positivity
  refine ⟨fun q => lpMomentConstant lam W₀ W q * ((1 + S) * (2 * (C + lam))),
    fun q => mul_nonneg (hnum q) hB0, ?_⟩
  intro F a ρA ρ x m p V Ψ K Y hFL hside hρ hx hcut hE hs4 hconv hslope k c X hk hX
  have hx0 : 0 < x := by linarith
  have hfew : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤ 4 * L ^ 4 := by
    intro z
    subst hFL
    exact ExponentObservables.cellBonds_card_le hFew F hL hside z
  have hWB : CellWeightSumLE F κ W₀ := by
    have key := hW₀ F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1)
    have k2 := key hfew
    exact fun Y' => k2 Y'
  have hsum2 : ∀ b₀ : ↥(chordBonds (finiteCells F)),
      ∑ b, Real.exp (-(2 * κ * chordBondDist F b b₀)) ≤ W := by
    have key := hW F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1)
    have k2 := key hfew
    exact fun b₀ => k2 (enclosingCell b₀.1.1)
  have hb : ∀ Y' : F.Cell, CellBound ρ x κ C Y' (bondSpan Y' c)
      (fun b => bondSpanWithCell Y' (enclosingCell b.1.1) c)
      (fun η => bondDeriv (fun V' => cellExponent false a ρA x m Y' V' η) V c X) := fun Y' =>
    cellBound_bondDeriv_cellExponent hDer hE hC hκ.le Y' hk c X hX (fun η hη => hs4 Y' k c X η hη) hx0.le
  have hH := cellBound_cellObservable (lam := lam) c X Y hx0 hC hlam.le (hb Y)
    (fun η hη => hs4 Y k c X η hη) hk
  have hC₁B : C + lam ≤ (1 + S) * (2 * (C + lam)) := by nlinarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hIsB : IsQuadraticallyBoundedOnBalls ρ x W₀ ((1 + S) * (2 * (C + lam)))
      (Real.exp (-(2 ^ 5 * κ * bondSpan Y c)))
      (cellObservable a ρA lam x m Y V c X) :=
    quadBound_mono hx0.le hC₁B (exp_decay_le_half_rate hκ _) (quadBound_of_value hWB hC₁0 hH.abs_le)
  have hIsG : ∀ b : ↥(chordBonds (finiteCells F)),
      IsQuadraticallyBoundedOnBalls ρ x W₀ (Real.sqrt x * ((1 + S) * (2 * (C + lam))))
        (Real.exp (-(2 ^ 5 * κ * bondSpan Y c)) *
          Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))))
        (bondGradNorm (cellObservable a ρA lam x m Y V c X) b) := by
    intro b
    have h1 := quadBound_of_gradient (Y := Y) (n := bondSpanWithCell Y (enclosingCell b.1.1) c) hWB hC₁0 hx
      (fun η => bondGradNorm_nonneg _ b η) (fun η hη => hH.partial_le η b hη)
    refine quadBound_mono hx0.le ?_ ?_ h1
    · exact mul_le_mul_of_nonneg_left (by nlinarith) hsx
    · have := cellSupDist_le_bondSpanWithCell Y (enclosingCell b.1.1) c
      rw [cellSupDist_comm] at this
      exact exp_decay_le_two hκ (bondSpan_le_bondSpanWithCell Y _ c) this
  have hdist := chordBondDist_isPseudoMetric (F := F)
  have hSz := hSize _ ρ x lam κ W W₀ (chordBondDist F) Ψ K p hρ hx0 hlam hκ.le hW0 hW₀0 hcut hdist hconv hsum2
    hslope
  refine ⟨hH.contDiffOn, ContDiffOn.sum fun Y' _ => (hb Y').contDiffOn, ?_, ?_, ?_⟩
  · obtain ⟨w, A, hA, hAa, hw, hSw, hbd⟩ := hIsB
    have h1 := hMom _ ρ x lam κ W W₀ (chordBondDist F) Ψ K p hρ hx0 hlam hκ.le hW0 hW₀0 hcut hdist hconv hsum2
      hslope (cellObservable a ρA lam x m Y V c X) _ A w 1 le_rfl hB0 hA hw hSw hH.contDiffOn.continuousOn hbd
    refine ⟨h1.1, h1.2.trans ?_⟩
    apply pow_le_pow_left₀ (mul_nonneg (hnum 1) (mul_nonneg hB0 hA))
    beta_reduce
    rw [mul_assoc (lpMomentConstant lam W₀ W 1)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAa hB0) (hnum 1)
  · exact hSz _ _ _ _ hB0 (Real.exp_pos _).le hH.contDiffOn hIsB hIsG
  · intro v l hv0 hv1
    have hv : |v| ≤ 1 := by rw [abs_of_nonneg hv0]; exact hv1
    have hsm : ContDiffOn ℝ 1 (fun η => v * exponentObservable a ρA x m V c X η) (openBalls F ρ) :=
      contDiffOn_const.mul (ContDiffOn.sum fun Y' _ => (hb Y').contDiffOn)
    have hSall : ∀ z : F.Cell, ∑ Y' ∈ finiteCells F, Real.exp (-(2 ^ 5 * κ * siteSupDist z Y')) ≤ S :=
      fun z => hS F F.top z (finiteCells F)
    have hBC : (1 + S) * C ≤ (1 + S) * (2 * (C + lam)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hBC2 : (1 + S) * (2 * C) ≤ (1 + S) * (2 * (C + lam)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    exact hSz _ _ _ _ hB0 (Real.exp_pos _).le hsm
      (quadBound_exponentObservable c X l hκ hx0 hC hW₀0 hS0 hBC hv hWB hSall hb)
      (fun b => quadBound_bondGradNorm_exponentObservable c X l hκ hx hC hW₀0 hS0 hBC2 hv hWB hSall hb b)
end YangMills.Construction.ColdStepAtMirrorFrames
end
