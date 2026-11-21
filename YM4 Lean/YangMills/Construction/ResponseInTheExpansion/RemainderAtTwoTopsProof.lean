import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTermsOfTheExponentProof
import YangMills.Construction.ResponseInTheExpansion.DerivativesAboveOnTheBalls
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfARemainderAboveTheFrame
import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrame
import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import Mathlib
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.BondsNearACellPairByOffsets
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames
def LiftedExpansionTwoFieldsAt (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V V' : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell) (q : ℕ) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)),
    T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
    IsSmallCurvature (5 / 4 * T.σ) V' → 0 < e →
    IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r → AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q →
    T.blockIndex ≤ q → enclosingCell y = Y → (∀ b, ‖η b‖ ≤ T.ballRadius) →
    |(coldHalfLawAt T x f).liftedExpansion r y η V - (coldHalfLawAt T x f).liftedExpansion r y η V'| ≤
      C * (e / T.η₃) * Real.exp (-(4 * T.κ * q))
def liftedExpansionTwoFieldsStatement : Prop :=
  ∃ C : StepParameters → ℝ, (∀ T, 0 ≤ C T) ∧
    EventuallyInParameters fun T => LiftedExpansionTwoFieldsAt T (C (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison WeightedResponses
namespace ResponseInTheExpansion
namespace TwoFieldsLemmas
variable {F : BlockFrame}
structure FarBounds (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  L_ge : 2 ^ 15 ≤ T.L
  Ct_ge : 1 ≤ T.Ct
  κ_le : 2 ^ 5 * T.κ ≤ T.chainParams.δ₂
  δ₂_pos : 0 < T.chainParams.δ₂
  blockIndex_ge : 16 ≤ T.blockIndex
  far : ∀ q : ℕ, T.blockIndex ≤ q → 64 * T.Ct * Real.exp (-(T.chainParams.δ₂ / 8 * q)) ≤ 1
  n₀_ge : 64 ≤ T.n₀
theorem exists_nat_mul_exp_neg_le_one (A d : ℝ) (hd : 0 < d) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → A * Real.exp (-(d * q)) ≤ 1 := by
  have t : Filter.Tendsto (fun q : ℕ => |A| * Real.exp (-(d * q))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun q : ℕ => d * (q : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hd tendsto_natCast_atTop_atTop
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa using h2.const_mul |A|
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (t.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨N, fun q hq => ?_⟩
  have h := hN q hq
  have h2 : A * Real.exp (-(d * q)) ≤ |A| * Real.exp (-(d * q)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
  exact h2.trans h.le
theorem eventuallyInParameters_farBounds : EventuallyInParameters FarBounds := by
  intro a ha
  refine ⟨2 ^ 15, fun L hodd hL c hc => ?_⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨1, fun Ct hCt => ⟨c.δ₂ / 2 ^ 5, by positivity, fun κ hκ hκ₀ => ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩⟩⟩
  obtain ⟨N, hN⟩ := exists_nat_mul_exp_neg_le_one (64 * Ct) (c.δ₂ / 8) (by positivity)
  refine ⟨max 16 N, fun nss hn => ⟨1, one_pos, fun σ hσ _ p _ => ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn₀ =>
    ⟨0, fun CE _ => ⟨0, fun y _ => ?_⟩⟩⟩⟩⟩⟩
  refine ⟨hL, hCt, ?_, hδ, le_of_max_le_left hn, fun q hq => hN q ((le_of_max_le_right hn).trans hq), hn₀⟩
  show 2 ^ 5 * κ ≤ c.δ₂
  have : κ ≤ c.δ₂ / 2 ^ 5 := hκ₀
  nlinarith
theorem toImaginary_imaginaryCoords (w : imaginaryQuaternions) : toImaginary (_root_.YangMills.Construction.Interpolation.imaginaryCoords w) = w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_imaginaryCoords <;> assumption
theorem norm_imaginaryCoords (w : imaginaryQuaternions) : ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords w‖ = ‖w‖ := by exact _root_.YangMills.SharedProofs.p6124 w
theorem toImaginary_add (v w : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (v + w) = toImaginary v + toImaginary w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
theorem bondDeriv_zero {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem siteSupDist_add_siteOfCoords_le (hc : IsLargeCubicTorus F) (hL : 0 < F.blockSide) (y : F.Site F.depth)
    (o : Fin 4 → ℤ) (r : ℕ) (ho : WithinRadius r o) :
    siteSupDist (y + siteOfCoords F.depth o) y ≤ r := by
  obtain ⟨n, hn, hs⟩ := hc
  refine Finset.sup_le fun l _ => ?_
  have hp : F.period F.depth l = F.extent l * F.blockSide := BlockOffsets.period_depth l
  have hp2 : 0 < F.period F.depth l := by
    rw [hp, hs l]
    have : 0 < n := by omega
    positivity
  have : NeZero (F.period F.depth l) := ⟨by omega⟩
  have e : ((y + siteOfCoords F.depth o : F.Site F.depth)) l - y l = ((o l : ℤ) : ZMod (F.period F.depth l)) := by
    simp [siteOfCoords]
  show (((y + siteOfCoords F.depth o : F.Site F.depth)) l - y l).valMinAbs.natAbs ≤ r
  rw [e]
  have h1 := ZMod.natAbs_min_of_le_div_two (F.period F.depth l)
    (((o l : ℤ) : ZMod (F.period F.depth l))).valMinAbs (o l)
    (by rw [ZMod.coe_valMinAbs]) (ZMod.natAbs_valMinAbs_le _)
  have h2 := abs_le.mp (ho l)
  omega
theorem sum_chordBonds_le_sum_fineBonds (g : F.Site F.depth × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ b : ↥(chordBonds (finiteCells F)), g b.1 ≤ ∑ b ∈ fineBonds F, g b := by
  classical
  rw [Finset.sum_coe_sort (chordBonds (finiteCells F)) g]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun b _ _ => hg b
  have h1 := (Finset.mem_filter.1 hb).1
  have h2 := (Finset.mem_filter.1 h1).1
  exact Finset.mem_product.2 ⟨(Finset.mem_product.1 h2).1, Finset.mem_univ _⟩
theorem cellSupDist_le_cellSetDiameter (y : F.Site F.depth) (b : ↥(chordBonds (finiteCells F))) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) :
    cellSupDist (enclosingCell b.1.1) (enclosingCell y) ≤
      cellSetDiameter (insert (enclosingCell y) (chordBondCells ![b] ∪ topBondCells c)) := by
  classical
  set P := insert (enclosingCell y) (chordBondCells ![b] ∪ topBondCells c) with hP
  have h1 : enclosingCell b.1.1 ∈ P := by
    refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
    exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩
  have h2 : enclosingCell y ∈ P := Finset.mem_insert_self _ _
  exact le_trans (Finset.le_sup (f := fun v => cellSupDist (enclosingCell b.1.1) v) h2)
    (Finset.le_sup (f := fun u => P.sup fun v => cellSupDist u v) h1)
theorem exp_le_torusDecayFactor (L : ℕ) (δ x : ℝ) : Real.exp (δ * x) ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SeriesExpansionTerms.exp_le_torusDecayFactor <;> assumption
theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem abs_sub_le_of_four_steps {A B C D E S m P M : ℝ} (h1 : |B - A| ≤ S) (h2 : |C - B| ≤ S)
    (h3 : |C - D| ≤ m) (h4 : |E - D| ≤ S) (hS : S ≤ P) (hm : m ≤ M) : |A - E| ≤ 3 * P + M := by
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have a3 := abs_le.1 h3
  have a4 := abs_le.1 h4
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
theorem exists_offset_of_cell (hp : ∀ i, F.period F.top i ≠ 0) (Y z : F.Cell) :
    ∃ o : Fin 4 → ℤ, Y + siteOfCoords F.top o = z ∧ WithinRadius (cellSupDist z Y) o := by
  refine ⟨fun i => ((z - Y) i).valMinAbs, ?_, fun i => ?_⟩
  · funext i
    have : NeZero (F.period F.top i) := ⟨hp i⟩
    show Y i + ((((z - Y) i).valMinAbs : ℤ) : ZMod (F.period F.top i)) = z i
    rw [ZMod.coe_valMinAbs]
    simp
  · have h1 : (((z - Y) i).valMinAbs).natAbs ≤ cellSupDist z Y :=
      Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
end TwoFieldsLemmas
open TwoFieldsLemmas in
set_option maxHeartbeats 1000000 in
theorem liftedExpansionTwoFieldsStatement_holds (hRow : remainderExpansionAboveFramesStatement)
    (hD : mixedDerivativesOnBallsStatement) (hFB : interpolatedFramesStatement)
    (hPair : bondsNearCellsPairStatement) (hG : CubicTorusCellGeometry)
    (hCov : BlocksCoverLowerLevel) (hJ : EventuallyInParametersCombines) : liftedExpansionTwoFieldsStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cr, hCr, hExpansionT⟩ := hRow
  obtain ⟨Cq, Cz, Crm, hP⟩ := hFB
  obtain ⟨hg1, hg2⟩ := hG
  choose! Wc hWc0 hWc using hg2
  refine ⟨fun U => |3 * U.Ct * U.σ * (Cr U * (Wc (2 ^ 7 * U.κ) * (U.L : ℝ) ^ 4))| + 1, fun U => by positivity, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ hExpansionT eventuallyInParameters_farBounds))
  rintro T hDr ⟨hPT, hRT, hB⟩ t x e f F V V' r Y q y η hx hF hV hV' he hr hag hq hy hη
  obtain ⟨hLF, -, n, hside, hn⟩ := id hF
  have hodd : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hn64 : 64 ≤ n := hB.n₀_ge.trans hn
  have hcub : IsLargeCubicTorus F := ⟨n, hn64, hside⟩
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hLpos : 0 < F.blockSide := hodd.pos
  have hcover := hCov F hodd hpos
  have hch : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d ht => by
    simp only [chordBonds, innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨hcover _, hcover _⟩, ht⟩
  have hfb := hPT t x hx
  have hone := hfb.one_torus F V 1 hF hV zero_le_one le_rfl
  have hone' := hfb.one_torus F V' 1 hF hV' zero_le_one le_rfl
  have htwo := (hfb.two_tori F F V V' Y Y q 1 hF hF hV hV' hag zero_le_one le_rfl).1
  have hs := hRT t x e f F V r hx hF hV he hr.decaying
  have hs' := hRT t x e f F V' r hx hF hV' he hr.decaying
  set Cb := Cr (parametersBeforeSide T) with hCb
  have hCb0 : 0 < Cb := hCr _
  have hσ := hDr.σ_pos
  have hκ := hDr.κ_pos
  have hη₃ := hDr.η₃_pos
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hq16 : 16 ≤ q := hB.blockIndex_ge.trans hq
  obtain ⟨hgs, hgt, hgc, hgtri, hcell⟩ := hg1 F hodd hcub
  set m := frameRadius x with hm
  set a := T.a with ha
  set ρA := T.chainParams.ρA with hρA
  let w : ↥(chordBonds (finiteCells F)) → imaginaryQuaternions := fun b => interpolatedFrame 1 a ρA m b.1 V
  let w' : ↥(chordBonds (finiteCells F)) → imaginaryQuaternions := fun b => interpolatedFrame 1 a ρA m b.1 V'
  set μ : ℝ := T.Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 8 * q)) with hμ
  have hCt0 : 0 < T.Ct := lt_of_lt_of_le one_pos hB.Ct_ge
  have hμ0 : 0 ≤ μ := by positivity
  have hμρ : μ ≤ T.ballRadius := by
    have h1 := hB.far q hq
    show T.Ct * T.σ * Real.exp (-(T.chainParams.δ₂ / 8 * q)) ≤ T.σ / 64
    nlinarith
  have hnear : ∀ b ∈ bondsNearCell Y q, ‖w' b - w b‖ ≤ μ := by
    intro b hb
    have hsq : ∀ i, 2 * q + 2 < F.extent i := fun i => (hag.1 i).resolve_left (hpos i).ne'
    obtain ⟨ι, _, _, j, j', hp⟩ := hPair F F Y Y q hodd rfl hsq hsq
    obtain ⟨i, hi⟩ := (hp.isBoxPairing.mem_left_iff b).1 hb
    obtain ⟨h, o, k, hh, ho, h1, -⟩ := hp.short_offsets i
    rw [hi] at h1
    have hbd : 2 * cellSupDist (enclosingCell b.1.1) Y ≤ q := (Finset.mem_filter.1 hb).2
    have hbox : IsFineBondWithinRadius Y q h o k := by
      refine ⟨ho, ?_, fun l => ?_, ?_, ?_⟩
      · rw [← h1]
        exact b.2
      · have := hh l
        rw [abs_le]
        have h2 := abs_le.1 (le_refl |h l|)
        omega
      · rw [← h1, hgc]
        omega
      · rw [← h1]
        have hu : WithinRadius 1 (Pi.single k 1 : Fin 4 → ℤ) := fun l => by
          by_cases hl : l = k
          · subst hl
            simp
          · simp [Pi.single_eq_of_ne hl]
        have h2 := siteSupDist_add_siteOfCoords_le hcub hLpos b.1.1 (Pi.single k 1) 1 hu
        have h3 := hcell (b.1.1 + unitStep F.depth k) b.1.1
        have h4 : siteSupDist (b.1.1 + unitStep F.depth k) b.1.1 ≤ 1 := h2
        have hL3 : 3 ≤ F.blockSide := by
          rw [hLF]
          have := hB.L_ge
          omega
        have h5 : cellSupDist (enclosingCell (b.1.1 + unitStep F.depth k)) (enclosingCell b.1.1) ≤ 1 := by
          by_contra hc
          have : 2 ≤ cellSupDist (enclosingCell (b.1.1 + unitStep F.depth k)) (enclosingCell b.1.1) := by omega
          nlinarith
        have h6 := hgtri Y (enclosingCell b.1.1) (enclosingCell (b.1.1 + unitStep F.depth k))
        have h7 := hgc Y (enclosingCell b.1.1)
        have h8 := hgc (enclosingCell b.1.1) (enclosingCell (b.1.1 + unitStep F.depth k))
        omega
    have hv := htwo.norm_sub_le h o k hbox
    rw [← h1] at hv
    rw [norm_sub_rev]
    refine hv.trans ?_
    rw [hgc Y]
    have hd2 : (2 : ℝ) * cellSupDist (enclosingCell b.1.1) Y ≤ q := by exact_mod_cast hbd
    have hδ₂ := hB.δ₂_pos
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    nlinarith
  set ε : ℝ := μ / T.ballRadius with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := (div_le_one hρ).2 hμρ
  have hερ : ε * T.ballRadius = μ := by
    rw [hε]
    field_simp
  set ηs : StepVariable (finiteCells F) := (1 - ε) • η with hηs
  set δv : StepVariable (finiteCells F) := fun b =>
    if b ∈ bondsNearCell Y q then _root_.YangMills.Construction.Interpolation.imaginaryCoords (w' b - w b) else 0 with hδv
  set ηx : StepVariable (finiteCells F) := ηs + δv with hηx
  have hsmall : ∀ b, ‖ηs b‖ ≤ (1 - ε) * T.ballRadius := fun b => by
    rw [hηs, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left (hη b) (by linarith)
  have hδn : ∀ b, ‖δv b‖ ≤ μ := fun b => by
    simp only [hδv]
    split_ifs with hb
    · rw [norm_imaginaryCoords]
      exact hnear b hb
    · simpa using hμ0
  have hs1 : ∀ b, ‖ηs b‖ ≤ T.ballRadius := fun b => (hsmall b).trans (by nlinarith)
  have hsx : ∀ b, ‖ηx b‖ ≤ T.ballRadius := fun b => by
    calc ‖ηx b‖ ≤ ‖ηs b‖ + ‖δv b‖ := norm_add_le _ _
      _ ≤ (1 - ε) * T.ballRadius + μ := add_le_add (hsmall b) (hδn b)
      _ = T.ballRadius := by rw [← hερ]; ring
  set Q := coldHalfLawAt T x f with hQ
  have hX0 : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  set D : ↥(chordBonds (finiteCells F)) → ℝ := fun b =>
    Cb * e * Real.exp (-(2 ^ 7 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) with hD'
  have hDb0 : ∀ b, 0 ≤ D b := fun b => by positivity
  have slopeD : ∀ (U : F.GaugeField F.top),
      HasMixedDerivBounds T.ballRadius T.κ Cb e (e / T.η₃) (Q.liftedExpansion r) U →
      ∀ ξ : StepVariable (finiteCells F), (∀ b, ‖ξ b‖ ≤ T.ballRadius) → ∀ (b : ↥(chordBonds (finiteCells F)))
        (u : EuclideanSpace ℝ (Fin 3)), ‖u‖ = 1 →
        |jointMixedDeriv (Q.liftedExpansion r y) ξ U ![b] ![u] (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
          (Fin.elim0 : Fin 0 → imaginaryQuaternions)| ≤ D b := by
    intro U hU ξ hξ b u hu
    refine (hU.deriv_one y ξ b u 0 Fin.elim0 Fin.elim0 hξ hu (Nat.zero_le _) hX0).trans ?_
    simp only [hD']
    have hsp := cellSupDist_le_cellSetDiameter y b (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    rw [hy] at hsp
    have hsp' : (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤
        (cellSetDiameter (insert Y (chordBondCells ![b] ∪
          topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) : ℝ) := by
      exact_mod_cast hsp
    rw [hy]
    simp only [show ((0 : ℕ) = 2) = False from by simp, if_false]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have : 0 < (2 : ℝ) ^ 7 * T.κ := by positivity
    nlinarith
  have lip : ∀ (U : F.GaugeField F.top),
      HasMixedDerivBounds T.ballRadius T.κ Cb e (e / T.η₃) (Q.liftedExpansion r) U →
      ∀ ζ ζ' : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ T.ballRadius) → (∀ b, ‖ζ' b‖ ≤ T.ballRadius) →
      (∀ b, ‖ζ' b - ζ b‖ ≤ μ) →
      |Q.liftedExpansion r y ζ' U - Q.liftedExpansion r y ζ U| ≤ μ * ∑ b, D b := by
    intro U hU ζ ζ' hζ hζ' hd
    have hRd := (hD F T.ballRadius U).2 (Q.liftedExpansion r y) (hU.smooth y)
    have h1 := hRd.abs_sub_le (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) D ζ ζ' (Nat.zero_le _) (slopeD U hU) hζ hζ'
    rw [hRd.fieldDeriv_zero _ _ rfl] at h1
    refine h1.trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hd b) (hDb0 b)
  have hSD : ∑ b, D b ≤ Cb * e * (Wc (2 ^ 7 * T.κ) * (T.L : ℝ) ^ 4) := by
    simp only [hD']
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := sum_chordBonds_le_sum_fineBonds (F := F)
      (fun b => Real.exp (-(2 ^ 7 * T.κ * (cellSupDist (enclosingCell b.1) Y : ℝ)))) fun _ => (Real.exp_pos _).le
    refine h1.trans ?_
    have h2 := hWc (2 ^ 7 * T.κ) (by positivity) F hodd hcub Y
    rw [hLF] at h2
    exact h2
  have hd1 : ∀ b, ‖ηs b - η b‖ ≤ μ := fun b => by
    have e1 : ηs b - η b = (-ε) • η b := by
      rw [hηs, Pi.smul_apply]
      module
    rw [e1, norm_smul, norm_neg, Real.norm_of_nonneg hε0, ← hερ]
    exact mul_le_mul_of_nonneg_left (hη b) hε0
  have hd2 : ∀ b, ‖ηx b - ηs b‖ ≤ μ := fun b => by
    have e1 : ηx b - ηs b = δv b := by
      rw [hηx, Pi.add_apply]
      abel
    rw [e1]
    exact hδn b
  have hd3 : ∀ b, ‖η b - ηs b‖ ≤ μ := fun b => by
    rw [norm_sub_rev]
    exact hd1 b
  have l1 := lip V hs η ηs hη hs1 hd1
  have l2 := lip V hs ηs ηx hs1 hsx hd2
  have l3 := lip V' hs' ηs η hs1 hη hd3
  set R₁ : ℕ := q / 4 with hR₁
  set R : ℕ := T.L * (R₁ - 1) with hR
  have hR₁4 : 4 ≤ R₁ := by omega
  have hper : ∀ i, 2 * R + 2 < F.period F.depth i := fun i => by
    rw [BlockOffsets.period_depth, hLF, hR]
    have hsq := (hag.1 i).resolve_left (hpos i).ne'
    have hLp : 3 ≤ T.L := by
      have := hB.L_ge
      omega
    have h1 : 2 * (R₁ - 1) + 2 ≤ F.extent i := by omega
    calc 2 * (T.L * (R₁ - 1)) + 2 < (2 * (R₁ - 1) + 2) * T.L := by nlinarith
      _ ≤ F.extent i * T.L := Nat.mul_le_mul_right _ h1
  have hcoord : ∀ (x₀ : F.Site F.depth) (i : Fin 4), ¬ IsAxialTreeBond (x₀, i) →
      2 * cellSupDist (enclosingCell x₀) Y ≤ q →
      interpolatedCoords 1 a ρA m V ηx x₀ i = interpolatedCoords 1 a ρA m V' ηs x₀ i := by
    intro x₀ i hnt hd
    have hm' := hch _ hnt
    have hnb : (⟨(x₀, i), hm'⟩ : ↥(chordBonds (finiteCells F))) ∈ bondsNearCell Y q :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩
    simp only [interpolatedCoords, stepCoordinates, dif_pos hm']
    have e1 : ηx ⟨(x₀, i), hm'⟩ =
        ηs ⟨(x₀, i), hm'⟩ + _root_.YangMills.Construction.Interpolation.imaginaryCoords (w' ⟨(x₀, i), hm'⟩ - w ⟨(x₀, i), hm'⟩) := by
      simp only [hηx, Pi.add_apply, hδv, if_pos hnb]
    rw [e1, toImaginary_add, toImaginary_imaginaryCoords]
    show interpolatedFrame 1 a ρA m (x₀, i) V + (toImaginary (ηs ⟨(x₀, i), hm'⟩) +
      (interpolatedFrame 1 a ρA m (x₀, i) V' - interpolatedFrame 1 a ρA m (x₀, i) V)) = _
    abel
  have hperN : ∀ i, F.period F.top i ≠ 0 := fun i => by
    rw [BlockOffsets.period_top]
    exact (hpos i).ne'
  have hag' : AgreeOnBox (interpolatedField 1 a ρA m V ηx) (interpolatedField 1 a ρA m V' ηs) y y R := by
    refine ⟨hper, hper, fun b hb => ?_⟩
    set x₀ := y + siteOfCoords F.depth b.1 with hx₀
    set i := b.2 with hi
    have h1 := hcell x₀ y
    have h2 : siteSupDist x₀ y ≤ R := siteSupDist_add_siteOfCoords_le hcub hLpos y b.1 R hb.1
    rw [hy, hLF] at h1
    have h3 : cellSupDist (enclosingCell x₀) Y ≤ R₁ := by
      have hLp : 0 < T.L := hLF ▸ hLpos
      have h4 : T.L * cellSupDist (enclosingCell x₀) Y ≤ T.L * R₁ := by
        refine h1.trans ((Nat.add_le_add_right h2 _).trans (le_of_eq ?_))
        rw [hR, ← Nat.mul_succ]
        congr 1
        omega
      exact Nat.le_of_mul_le_mul_left h4 hLp
    have hq2 : 2 * cellSupDist (enclosingCell x₀) Y ≤ q := by omega
    simp only [interpolatedField, chartedField]
    by_cases hc : IsCrossingBond (x₀, i)
    · rw [if_pos hc, if_pos hc, hcoord x₀ i (fun ht => ht.1 hc) hq2]
      obtain ⟨o, ho, hbox⟩ := exists_offset_of_cell hperN Y (enclosingCell x₀)
      have hb' : BondWithinRadius q (o, i) := by
        refine ⟨fun l => ?_, fun l => ?_⟩
        · have := abs_le.1 (hbox l)
          show |o l| ≤ _
          rw [abs_le]
          omega
        · have h5 := abs_le.1 (hbox l)
          have h6 : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
            by_cases hl : l = i
            · subst hl
              simp
            · simp [Pi.single_eq_of_ne hl]
          have h7 := abs_le.1 h6
          show |o l + (Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ _
          rw [abs_le]
          omega
      have hv := hag.2.2.2 (o, i) hb'
      simp only [ho] at hv
      rw [hv]
    · rw [if_neg hc, if_neg hc]
      by_cases ht : IsAxialTreeBond (x₀, i)
      · rw [if_pos ht, if_pos ht]
      · rw [if_neg ht, if_neg ht, hcoord x₀ i ht hq2]
  have hcoldx : IsSmallCurvature T.σ (interpolatedField 1 a ρA m V ηx) := fun p hp =>
    (hone.small.small_curvature_nearby ηx hsx p hp).trans (by linarith)
  have hcoldp : IsSmallCurvature T.σ (interpolatedField 1 a ρA m V' ηs) := fun p hp =>
    (hone'.small.small_curvature_nearby ηs hs1 p hp).trans (by linarith)
  have hmid : |Q.liftedExpansion r y ηx V - Q.liftedExpansion r y ηs V'| ≤ e / torusDecayFactor T.L T.decayRate R := by
    have h1 := hr.agreement y _ _ R 0 Fin.elim0 Fin.elim0 hcoldx hcoldp hag' (Nat.zero_le _) (fun l => l.elim0) hX0
    rw [bondDeriv_zero, bondDeriv_zero] at h1
    simp only [remainderHat, sub_sub_sub_cancel_right] at h1
    exact h1
  have hdec : e / torusDecayFactor T.L T.decayRate R ≤ e * Real.exp (-(4 * T.κ * q)) := by
    rw [div_le_iff₀ (torusDecayFactor_pos _ _ _)]
    have h1 := exp_le_torusDecayFactor T.L T.decayRate R
    have hLr : (2 : ℝ) ^ 15 ≤ T.L := by exact_mod_cast hB.L_ge
    have hRr : (4 * T.κ * q) ≤ T.decayRate * R := by
      have hu : (q : ℝ) ≤ 4 * (R₁ : ℝ) + 3 := by
        have : q ≤ 4 * R₁ + 3 := by omega
        exact_mod_cast this
      have hq16' : (16 : ℝ) ≤ q := by exact_mod_cast hq16
      have hc : ((R₁ - 1 : ℕ) : ℝ) = (R₁ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      have hRc : (R : ℝ) = (T.L : ℝ) * ((R₁ : ℝ) - 1) := by
        rw [hR, Nat.cast_mul, hc]
      rw [hRc]
      show 4 * T.κ * q ≤ T.κ / 2 ^ 10 * ((T.L : ℝ) * ((R₁ : ℝ) - 1))
      have h2 : (q : ℝ) / 8 ≤ (R₁ : ℝ) - 1 := by linarith
      have h3 : (2 : ℝ) ^ 15 * ((q : ℝ) / 8) ≤ (T.L : ℝ) * ((R₁ : ℝ) - 1) :=
        mul_le_mul hLr h2 (by positivity) (by positivity)
      have h4 : T.κ / 2 ^ 10 * ((2 : ℝ) ^ 15 * ((q : ℝ) / 8)) ≤
          T.κ / 2 ^ 10 * ((T.L : ℝ) * ((R₁ : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      refine le_trans (le_of_eq ?_) h4
      ring
    have h5 : 1 ≤ Real.exp (-(4 * T.κ * q)) * torusDecayFactor T.L T.decayRate R := by
      have h6 : Real.exp (-(4 * T.κ * q)) * Real.exp (T.decayRate * R) ≤
          Real.exp (-(4 * T.κ * q)) * torusDecayFactor T.L T.decayRate R :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      refine le_trans ?_ h6
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc e = e * 1 := (mul_one e).symm
      _ ≤ e * (Real.exp (-(4 * T.κ * q)) * torusDecayFactor T.L T.decayRate R) :=
        mul_le_mul_of_nonneg_left h5 he.le
      _ = _ := by ring
  have hμe : μ ≤ T.Ct * T.σ * Real.exp (-(4 * T.κ * q)) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have h1 := hB.κ_le
    nlinarith
  set W₄ : ℝ := Wc (2 ^ 7 * T.κ) * (T.L : ℝ) ^ 4 with hW₄
  have hee : e ≤ e / T.η₃ := by
    rw [le_div_iff₀ hη₃]
    nlinarith [hDr.η₃_le_one]
  have hE := Real.exp_pos (-(4 * T.κ * q))
  set E₄ := Real.exp (-(4 * T.κ * q)) with hE₄
  have hsum : μ * ∑ b, D b ≤ (T.Ct * T.σ * E₄) * (Cb * e * W₄) :=
    mul_le_mul hμe hSD (Finset.sum_nonneg fun b _ => hDb0 b) (by positivity)
  have htri : |Q.liftedExpansion r y η V - Q.liftedExpansion r y η V'| ≤ (3 * T.Ct * T.σ * (Cb * W₄) + 1) * e * E₄ := by
    have a5 : (3 * T.Ct * T.σ * (Cb * W₄) + 1) * e * E₄ =
        3 * ((T.Ct * T.σ * E₄) * (Cb * e * W₄)) + e * E₄ := by ring
    rw [a5]
    exact abs_sub_le_of_four_steps l1 l2 hmid l3 hsum (hdec)
  refine htri.trans ?_
  have hC1 : 3 * T.Ct * T.σ * (Cb * W₄) + 1 ≤
      |3 * (parametersBeforeSide T).Ct * (parametersBeforeSide T).σ * (Cb * (Wc (2 ^ 7 * (parametersBeforeSide T).κ) *
        ((parametersBeforeSide T).L : ℝ) ^ 4))| + 1 := by
    have := le_abs_self (3 * T.Ct * T.σ * (Cb * W₄))
    show _ ≤ |3 * T.Ct * T.σ * (Cb * W₄)| + 1
    linarith
  calc (3 * T.Ct * T.σ * (Cb * W₄) + 1) * e * E₄ ≤
      (|3 * (parametersBeforeSide T).Ct * (parametersBeforeSide T).σ * (Cb * (Wc (2 ^ 7 * (parametersBeforeSide T).κ) *
        ((parametersBeforeSide T).L : ℝ) ^ 4))| + 1) * (e / T.η₃) * E₄ := by
        refine mul_le_mul_of_nonneg_right ?_ hE.le
        exact mul_le_mul hC1 hee he.le (by positivity)
    _ = _ := rfl
end ResponseInTheExpansion
end YangMills.Construction
end
