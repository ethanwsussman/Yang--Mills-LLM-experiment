import YangMills.Construction.ColdStepAtMirrorFrames.FramesOnTheParameters
import YangMills.Construction.ColdStepAtMirrorFrames.HaarExcessNearZero
import YangMills.Construction.ColdStepAtMirrorFrames.PartsOfTheExponent
import Mathlib
import YangMills.Construction.HoleBesideASecondHole.CellsLeftOffTheSpotsProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
set_option autoImplicit false

noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def HaarComponentsClose (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (F F' : BlockFrame) (U : F.GaugeField F.top) (U' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (star : Bool), AgreeingTopPair P t x U U' Y Y' r →
    NearCellsClose P.ballRadius x P.κ ((P.Ct / 4) * Real.exp (-(2 * P.κ * r))) Y Y' r
      (fun Z η => haarComponent star P.a P.chainParams.ρA (frameRadius x) Z U η)
      (fun Z η => haarComponent star P.a P.chainParams.ρA (frameRadius x) Z U' η)
def HaarComponentsCloseEventually : Prop := EventuallyInParameters HaarComponentsClose
end YangMills.Construction.ColdStepAtMirrorFrames
end

noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace HaarComponentSteps
variable {F F' : BlockFrame}
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem haarLogRatio_lipschitz {K : ℝ} (hK : 0 < K)
    (hD : ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 → ContDiffAt ℝ 3 haarLogRatio v ∧
      ∀ w : imaginaryQuaternions, |fderiv ℝ haarLogRatio v w| ≤ K * ‖w‖)
    {u v : imaginaryQuaternions} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |haarLogRatio u - haarLogRatio v| ≤ K * ‖u - v‖ := by
  have hball : ∀ {z : imaginaryQuaternions}, z ∈ Metric.closedBall (0 : imaginaryQuaternions) 1 → ‖z‖ ≤ 1 :=
    fun hz => by
    simpa using hz
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (s := Metric.closedBall (0 : imaginaryQuaternions) 1)
    (f := haarLogRatio) (C := K) (x := v) (y := u)
    (fun z hz => ((hD z (hball hz)).1.differentiableAt (by norm_num)))
    (fun z hz => ContinuousLinearMap.opNorm_le_bound _ hK.le fun w => by
      simpa [Real.norm_eq_abs] using (hD z (hball hz)).2 w)
    (convex_closedBall _ _) (by simpa using hv) (by simpa using hu)
  simpa [Real.norm_eq_abs] using hmv
private theorem mem_centredCube_odd (R : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube (2 * R + 1) ↔ ∀ i, |h i| ≤ (R : ℤ) := by apply _root_.YangMills.Construction.HoleSavings.mem_centredCube_odd <;> assumption
private theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
private theorem siteOfCoords_injective {n : ℕ} (hext : ∀ i, F.extent i = n) {Y : F.Cell} {c c' : Fin 4 → ℤ}
    (h : ∀ i, 2 * |c i - c' i| < n) (heq : Y + siteOfCoords F.top c = Y + siteOfCoords F.top c') :
    c = c' := by
  funext i
  have h1 := congrFun (add_left_cancel heq) i
  simp only [siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_top, hext] at h1
  have h2 : c' i - c i = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd h1
    have := h i
    rw [abs_sub_comm] at this
    have := abs_nonneg (c' i - c i)
    omega
  omega
abbrev _root_.YangMills.SharedProofs.p11813 := @siteOfCoords_injective
private theorem cellSupDist_le {n M : ℕ} (hext : ∀ i, F.extent i = n) (hn : 2 * M + 2 < n) (Y : F.Cell)
    (h : Fin 4 → ℤ) (hh : ∀ i, |h i| ≤ (M : ℤ)) : cellSupDist Y (Y + siteOfCoords F.top h) ≤ M := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have hdiff : Y i - (Y + siteOfCoords F.top h : F.Cell) i = ((- h i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  have hne : NeZero (F.period F.top i) := ⟨by rw [period_top, hext]; omega⟩
  have hv : (((- h i : ℤ) : ZMod (F.period F.top i))).valMinAbs = - h i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    rw [period_top, hext]
    have h1 := abs_le.mp (hh i)
    constructor <;> omega
  show ((Y i - (Y + siteOfCoords F.top h : F.Cell) i).valMinAbs).natAbs ≤ M
  rw [hdiff, hv, Int.natAbs_neg]
  have h1 := hh i
  rw [Int.abs_eq_natAbs] at h1
  exact_mod_cast h1
private theorem zeroExtensionL_apply {ι Λ : Type} [Fintype ι] [Fintype Λ] [DecidableEq ι] (e : Λ → ι)
    (he : Function.Injective e) (ζ : BondField Λ) (q : Λ) : zeroExtensionL e ζ (e q) = ζ q := by
  have h : ∃ l, e l = e q := ⟨q, rfl⟩
  have h2 : h.choose = q := he h.choose_spec
  simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_pos h]
  simp [h2]
private theorem haarComponent_eq_sum {Λ : Type} [Fintype Λ] [DecidableEq ↥(chordBonds (finiteCells F))]
    (star : Bool) (a ρA : ℝ) (m : ℕ) (Z : F.Cell) (V : F.GaugeField F.top)
    (e : Λ → ↥(chordBonds (finiteCells F))) (he : Function.Injective e) (P : Λ → Prop) [DecidablePred P]
    (hoff : ∀ b, b ∉ Set.range e → enclosingCell b.1.1 ≠ Z) (hP : ∀ q, enclosingCell (e q).1.1 = Z ↔ P q)
    (ζ : BondField Λ) :
    haarComponent star a ρA m Z V (zeroExtensionL e ζ) =
      ∑ q, if P q then haarLogRatio (stepFrame star a ρA m (e q).1 V + toImaginary (ζ q)) else 0 := by
  classical
  unfold haarComponent
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) (fun b _ hb => ?_),
    Finset.sum_image (fun x _ y _ h => he h)]
  · refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : P q
    · rw [if_pos ((hP q).2 hq), if_pos hq]
      congr 1
      show stepFrame star a ρA m (e q).1 V + stepCoordinates (zeroExtensionL e ζ) (e q).1.1 (e q).1.2 = _
      congr 1
      unfold stepCoordinates
      rw [dif_pos (e q).2]
      show toImaginary (zeroExtensionL e ζ (e q)) = _
      rw [zeroExtensionL_apply e he]
    · rw [if_neg (fun h => hq ((hP q).1 h)), if_neg hq]
  · refine if_neg (hoff b fun ⟨q, hq⟩ => hb ?_)
    exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩
private theorem enclosingCell_fineBondAt (hS : SiteDecomposition) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) {h o : Fin 4 → ℤ} (i : Fin 4) (ho : o ∈ centredCube F.blockSide) :
    enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h :=
  ((hS F hodd hs).1 _ o ho).1
private theorem enclosingCell_fineBondAt_iff {n r : ℕ} (hS : SiteDecomposition) (hodd : Odd F.blockSide)
    (hext : ∀ i, F.extent i = n) (hn : 2 * r + 2 < n) (Y : F.Cell) {q c o : Fin 4 → ℤ} (i : Fin 4)
    (ho : o ∈ centredCube F.blockSide)
    (hq : ∀ l, |q l| ≤ ((r / 2 : ℕ) : ℤ)) (hc : ∀ l, |c l| ≤ ((r / 8 : ℕ) : ℤ)) :
    enclosingCell (fineBondAt Y q o i).1 = Y + siteOfCoords F.top c ↔ q = c := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hext]; omega
  rw [enclosingCell_fineBondAt hS hodd hs Y i ho]
  constructor
  · refine siteOfCoords_injective hext fun l => ?_
    have h1 := abs_sub (q l) (c l)
    have h2 := hq l
    have h3 := hc l
    omega
  · rintro rfl
    rfl
private theorem enclosingCell_ne_of_far {n r : ℕ} (hext : ∀ i, F.extent i = n) (hn : 2 * r + 2 < n)
    (hr : 1 ≤ r) (Y : F.Cell)
    {c : Fin 4 → ℤ} (hc : ∀ l, |c l| ≤ ((r / 8 : ℕ) : ℤ)) (b : ↥(chordBonds (finiteCells F)))
    (hfar : (r : ℝ) / 2 ≤ cellDistReal F Y (chordBondCell F b)) :
    enclosingCell b.1.1 ≠ Y + siteOfCoords F.top c := by
  intro h
  have h1 : cellSupDist Y (Y + siteOfCoords F.top c) ≤ r / 8 := cellSupDist_le hext (by omega) Y c hc
  have h2 : cellSupDist Y (chordBondCell F b) ≤ r / 8 := by
    unfold chordBondCell
    rw [h]
    exact h1
  have h3 : (8 * cellSupDist Y (chordBondCell F b) : ℕ) ≤ r := by omega
  have h4 : (8 : ℝ) * (cellSupDist Y (chordBondCell F b) : ℝ) ≤ r := by exact_mod_cast h3
  have h5 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold cellDistReal at hfar
  linarith
private theorem fineBond_within_radius {n r : ℕ} (hS : SiteDecomposition) (hodd : Odd F.blockSide)
    (hext : ∀ i, F.extent i = n)
    (hn : 2 * r + 2 < n) (hr : 1 ≤ r) (Y : F.Cell) {c o : Fin 4 → ℤ} {i : Fin 4}
    (ho : o ∈ centredCube F.blockSide)
    (hc : ∀ l, |c l| ≤ ((r / 8 : ℕ) : ℤ)) (hb : fineBondAt Y c o i ∈ chordBonds (finiteCells F)) :
    IsFineBondWithinRadius Y r c o i ∧ cellSupDist Y (enclosingCell (fineBondAt Y c o i).1) ≤ r / 8 := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hext]; omega
  have hcell := enclosingCell_fineBondAt (h := c) hS hodd hs Y i ho
  have hd : cellSupDist Y (Y + siteOfCoords F.top c) ≤ r / 8 := cellSupDist_le hext (by omega) Y c hc
  refine ⟨⟨ho, hb, fun l => (hc l).trans (by exact_mod_cast (Nat.div_le_self r 8)), ?_, ?_⟩, ?_⟩
  · rw [hcell]
    omega
  · rcases ((hS F hodd hs).2.2.2 (fineBondAt Y c o i).1 i) with hend | hend
    · rw [hend, hcell]
      omega
    · have hadd : (Y + siteOfCoords F.top c + unitStep F.top i : F.Cell) =
          Y + siteOfCoords F.top (c + Pi.single i 1) := by
        funext l
        simp [siteOfCoords, unitStep, add_assoc]
      rw [hend, hcell, hadd]
      have h5 : ∀ l, |(c + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ ((r / 8 + 1 : ℕ) : ℤ) := by
        intro l
        have a1 : |(c + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤
            |c l| + |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| :=
          abs_add_le _ _
        have a2 : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
          by_cases hli : l = i
          · subst hli
            simp
          · simp [hli]
        have a3 := hc l
        push_cast at a3 ⊢
        linarith
      have := cellSupDist_le hext (by omega) Y _ h5
      omega
  · rw [hcell]
    exact hd
private def HaarDecayCondition (K : ℝ) (T : StepParameters) : Prop :=
  1 ≤ T.blockIndex ∧ ∀ r : ℕ, T.blockIndex ≤ r →
    4 * ((((centredCube T.L).card * 4 : ℕ) : ℝ) * K) * Real.exp (-(T.chainParams.δ₂ / 4 * (7 / 8 * r))) ≤
      Real.exp (-(2 * T.κ * r))
private theorem haarDecayCondition_eventually (K : ℝ) : EventuallyInParameters (HaarDecayCondition K) := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ⟨0, fun Ct _ => ?_⟩⟩
  obtain ⟨⟨_, _, _, hδ, _⟩, _⟩ := hc.classical
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * ((((centredCube L).card * 4 : ℕ) : ℝ) * K) / (c.δ₂ * (3 / 16)))
  refine ⟨c.δ₂ / 64, by positivity, fun κ hκ hκ' => ⟨1, one_pos, fun η₃ _ _ _ => ⟨N + 1, fun m hm =>
    ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨by show 1 ≤ m; omega, fun r hr => ?_⟩
  have hr' : N + 1 ≤ r := hm.trans hr
  show 4 * ((((centredCube L).card * 4 : ℕ) : ℝ) * K) * Real.exp (-(c.δ₂ / 4 * (7 / 8 * r))) ≤
    Real.exp (-(2 * κ * r))
  have hNr : (N : ℝ) ≤ r := by exact_mod_cast (by omega : N ≤ r)
  have hpos : 0 < c.δ₂ * (3 / 16) := by positivity
  have hK : 4 * ((((centredCube L).card * 4 : ℕ) : ℝ) * K) ≤ c.δ₂ * (3 / 16) * r := by
    have := (div_lt_iff₀ hpos).1 hN
    nlinarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hexp : 4 * ((((centredCube L).card * 4 : ℕ) : ℝ) * K) ≤
      Real.exp (c.δ₂ / 4 * (7 / 8 * r) - 2 * κ * r) := by
    have h1 : c.δ₂ * (3 / 16) * r ≤ c.δ₂ / 4 * (7 / 8 * r) - 2 * κ * r := by nlinarith
    have h2 := Real.add_one_le_exp (c.δ₂ / 4 * (7 / 8 * r) - 2 * κ * r)
    linarith
  calc 4 * ((((centredCube L).card * 4 : ℕ) : ℝ) * K) * Real.exp (-(c.δ₂ / 4 * (7 / 8 * r)))
      ≤ Real.exp (c.δ₂ / 4 * (7 / 8 * r) - 2 * κ * r) * Real.exp (-(c.δ₂ / 4 * (7 / 8 * r))) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = Real.exp (-(2 * κ * r)) := by
        rw [← Real.exp_add]
        congr 1
        ring
set_option maxHeartbeats 1600000 in
private theorem haarComponentsClose_of {K : ℝ} (hK : 0 < K)
    (hD : ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 → ContDiffAt ℝ 3 haarLogRatio v ∧
      ∀ w : imaginaryQuaternions, |fderiv ℝ haarLogRatio v w| ≤ K * ‖w‖)
    (hC : commonBondsOfTwoTori) (hS : SiteDecomposition) (T : StepParameters) (hd : T.IsOrdered)
    (hf : FrameBoundsForParameters T) (hfl : HaarDecayCondition K T) : HaarComponentsClose T := by
  obtain ⟨Cf, C, _, hC1, _, hCCt, _, h64, _, hσ1, _, _, _, hy1, _, hall⟩ := hf
  obtain ⟨⟨_, hρ1, _, hδ, _⟩, _⟩ := hd.chain_admissible.classical
  intro t x F F' V V' Y Y' r star hT c ζ hζ
  obtain ⟨hL, _, n, hext, hn⟩ := hT.top
  obtain ⟨hL', _, n', hext', hn'⟩ := hT.top'
  have hr : 1 ≤ r := hfl.1.trans hT.radius_le
  have hx : 1 ≤ x := hy1.trans hT.coupling_le
  have hodd : Odd F.blockSide := hL ▸ hd.odd_L
  have hodd' : Odd F'.blockSide := hL' ▸ hd.odd_L
  have hn2 : 2 * r + 2 < n := by
    rcases hT.agree.1 0 with h | h <;> rw [hext] at h <;> omega
  have hn2' : 2 * r + 2 < n' := by
    rcases hT.agree.2.1 0 with h | h <;> rw [hext'] at h <;> omega
  have hcom : HasCommonBonds Y Y' r := (hC T.L hd.odd_L).2 F F' Y Y' r n n' hL hL' hext hext' hn2 hn2'
  obtain ⟨_, hsm, _, hloc⟩ := hall t x F V hT.coupling_le hT.top hT.small
  obtain ⟨_, hsm', _, _⟩ := hall t x F' V' hT.coupling_le hT.top' hT.small'
  have hlocal := (hloc F' V' Y Y' r hT.top' hT.small' hT.agree).1 star
  have hc : ∀ l, |c.1 l| ≤ ((r / 8 : ℕ) : ℤ) := (mem_centredCube_odd _ _).1 c.2
  have hmem : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)), (∀ l, |q.1.1 l| ≤ ((r / 2 : ℕ) : ℤ)) ∧
      q.1.2.1 ∈ centredCube F.blockSide ∧ q.1.2.1 ∈ centredCube F'.blockSide := by
    intro q
    have h1 := (Finset.mem_filter.mp q.2).1
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at h1
    exact ⟨(mem_centredCube_odd _ _).1 h1.1, h1.2, by rw [hL', ← hL]; exact h1.2⟩
  have e1 := haarComponent_eq_sum star T.a T.chainParams.ρA (frameRadius x) (offsetCell Y (r / 8) c) V
    (commonBondLeft Y Y' (r / 2)) hcom.injective_left (fun q => q.1.1 = c.1)
    (fun b hb => enclosingCell_ne_of_far hext hn2 hr Y hc b (hcom.far_of_not_common b hb))
    (fun q => enclosingCell_fineBondAt_iff hS hodd hext hn2 Y _ (hmem q).2.1 (hmem q).1 hc) ζ
  have e2 := haarComponent_eq_sum star T.a T.chainParams.ρA (frameRadius x) (offsetCell Y' (r / 8) c) V'
    (commonBondRight Y Y' (r / 2)) hcom.injective_right (fun q => q.1.1 = c.1)
    (fun b hb => enclosingCell_ne_of_far hext' hn2' hr Y' hc b (hcom.far_of_not_common' b hb))
    (fun q => enclosingCell_fineBondAt_iff hS hodd' hext' hn2' Y' _ (hmem q).2.2 (hmem q).1 hc) ζ
  set E : ℝ := Real.exp (-(T.chainParams.δ₂ / 4 * (7 / 8 * r))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hσ0 : 0 < T.σ := hd.σ_pos
  have hC0 : 0 < C := by linarith
  have hterm : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)), q.1.1 = c.1 →
      |haarLogRatio (stepFrame star T.a T.chainParams.ρA (frameRadius x) (commonBondLeft Y Y' (r / 2) q).1 V +
          toImaginary (ζ q)) -
        haarLogRatio (stepFrame star T.a T.chainParams.ρA (frameRadius x) (commonBondRight Y Y' (r / 2) q).1 V' +
          toImaginary (ζ q))| ≤
      K * (C * T.σ * E) := by
    intro q hq
    have hcq : ∀ l, |q.1.1 l| ≤ ((r / 8 : ℕ) : ℤ) := fun l => by rw [hq]; exact hc l
    obtain ⟨hbox, hdist⟩ := fineBond_within_radius hS hodd hext hn2 hr Y (hmem q).2.1 hcq
      (commonBondLeft Y Y' (r / 2) q).2
    have hv := hlocal.value _ _ _ hbox
    have hζq : ‖ζ q‖ ≤ T.σ / 64 := (hζ q).le
    have hu : ‖stepFrame star T.a T.chainParams.ρA (frameRadius x) (commonBondLeft Y Y' (r / 2) q).1 V +
        toImaginary (ζ q)‖ ≤ 1 := by
      have h1 := (hsm star).norm_add_le _ (commonBondLeft Y Y' (r / 2) q).2
      have h2 := norm_add_le
        (stepFrame star T.a T.chainParams.ρA (frameRadius x) (commonBondLeft Y Y' (r / 2) q).1 V)
        (toImaginary (ζ q))
      rw [norm_toImaginary] at h2
      linarith
    have hu' : ‖stepFrame star T.a T.chainParams.ρA (frameRadius x) (commonBondRight Y Y' (r / 2) q).1 V' +
        toImaginary (ζ q)‖ ≤ 1 := by
      have h1 := (hsm' star).norm_add_le _ (commonBondRight Y Y' (r / 2) q).2
      have h2 := norm_add_le
        (stepFrame star T.a T.chainParams.ρA (frameRadius x) (commonBondRight Y Y' (r / 2) q).1 V')
        (toImaginary (ζ q))
      rw [norm_toImaginary] at h2
      linarith
    refine (haarLogRatio_lipschitz hK hD hu hu').trans (mul_le_mul_of_nonneg_left ?_ hK.le)
    rw [add_sub_add_right_eq_sub]
    refine le_trans hv (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
    have h3 : (8 * cellSupDist Y (enclosingCell (fineBondAt Y q.1.1 q.1.2.1 q.1.2.2).1) : ℕ) ≤ r := by omega
    have h4 : (8 : ℝ) * (cellSupDist Y (enclosingCell (fineBondAt Y q.1.1 q.1.2.1 q.1.2.2).1) : ℝ) ≤ r := by
      exact_mod_cast h3
    nlinarith
  have hcard : (Finset.univ.filter fun q : ↥(commonBondOffsets Y Y' (r / 2)) => q.1.1 = c.1).card ≤
      (centredCube T.L).card * 4 := by
    have h1 : (Finset.univ.filter fun q : ↥(commonBondOffsets Y Y' (r / 2)) => q.1.1 = c.1).card ≤
        (centredCube T.L ×ˢ (Finset.univ : Finset (Fin 4))).card := by
      refine Finset.card_le_card_of_injOn (fun q => (q.1.2.1, q.1.2.2)) (fun q _ => ?_)
        (fun q hq q' hq' heq => ?_)
      · have := (hmem q).2.1
        rw [hL] at this
        simpa using this
      · have a1 : q.1.1 = c.1 := (Finset.mem_filter.mp hq).2
        have a2 : q'.1.1 = c.1 := (Finset.mem_filter.mp hq').2
        exact Subtype.ext (Prod.ext (a1.trans a2.symm) (by simpa using heq))
    simpa [Finset.card_product] using h1
  have hsum : |(∑ q : ↥(commonBondOffsets Y Y' (r / 2)), if q.1.1 = c.1 then
        haarLogRatio (stepFrame star T.a T.chainParams.ρA (frameRadius x) (commonBondLeft Y Y' (r / 2) q).1 V +
          toImaginary (ζ q)) else 0) -
      ∑ q : ↥(commonBondOffsets Y Y' (r / 2)), if q.1.1 = c.1 then
        haarLogRatio (stepFrame star T.a T.chainParams.ρA (frameRadius x) (commonBondRight Y Y' (r / 2) q).1 V' +
          toImaginary (ζ q)) else 0| ≤
      (((centredCube T.L).card * 4 : ℕ) : ℝ) * (K * (C * T.σ * E)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hε : 0 ≤ K * (C * T.σ * E) := by positivity
    calc _ ≤ ∑ q : ↥(commonBondOffsets Y Y' (r / 2)), if q.1.1 = c.1 then K * (C * T.σ * E) else 0 := by
          refine Finset.sum_le_sum fun q _ => ?_
          by_cases hq : q.1.1 = c.1
          · simp only [if_pos hq]
            exact hterm q hq
          · simp [if_neg hq]
      _ = ((Finset.univ.filter fun q : ↥(commonBondOffsets Y Y' (r / 2)) => q.1.1 = c.1).card : ℝ) *
            (K * (C * T.σ * E)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hε
  show |haarComponent star T.a T.chainParams.ρA (frameRadius x) (offsetCell Y (r / 8) c) V
        (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) -
      haarComponent star T.a T.chainParams.ρA (frameRadius x) (offsetCell Y' (r / 8) c) V'
        (zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ)| ≤ _
  rw [e1, e2]
  refine hsum.trans ?_
  have hB := hfl.2 r hT.radius_le
  have hsq : 0 ≤ weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F) (offsetCell Y (r / 8) c)
      (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hCs : C * T.σ ≤ T.Ct := by nlinarith
  have hX : 0 < Real.exp (-(2 * T.κ * r)) := Real.exp_pos _
  have hCt : 0 < T.Ct := by linarith
  calc (((centredCube T.L).card * 4 : ℕ) : ℝ) * (K * (C * T.σ * E))
      = (C * T.σ / 4) * (4 * ((((centredCube T.L).card * 4 : ℕ) : ℝ) * K) * E) := by ring
    _ ≤ (C * T.σ / 4) * Real.exp (-(2 * T.κ * r)) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ (T.Ct / 4) * Real.exp (-(2 * T.κ * r)) := mul_le_mul_of_nonneg_right (by linarith) hX.le
    _ ≤ (T.Ct / 4) * Real.exp (-(2 * T.κ * r)) * (x * weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F)
          (offsetCell Y (r / 8) c) (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) + 1) :=
        le_mul_of_one_le_right (by positivity) (by nlinarith)
end HaarComponentSteps
theorem haarComponentsCloseEventually_holds (hF : FrameBoundsEventually) (hH : HaarLogRatioNearZero)
    (hC : commonBondsOfTwoTori) (hS : SiteDecomposition) (hJ : EventuallyInParametersCombines) :
    HaarComponentsCloseEventually := by
  obtain ⟨K, hK, hH⟩ := hH
  refine hJ.2 _ _ (fun T hd h => HaarComponentSteps.haarComponentsClose_of hK (fun v hv => ?_) hC hS T hd h.1 h.2)
    (hJ.1 _ _ hF (HaarComponentSteps.haarDecayCondition_eventually K))
  exact ⟨(hH v hv).1, (hH v hv).2.1⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
