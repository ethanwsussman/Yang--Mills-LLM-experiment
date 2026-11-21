import YangMills.Construction.ClusterExpansionOfAStep.ChartCoordinateIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.FrameIsContinuousWhereItIsRead
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours GaugeFixing ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps StepCosts
namespace StepFrames
def imaginaryBasis (e : Fin 3) : imaginaryQuaternions :=
  ⟨![(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] e, by fin_cases e <;> rfl⟩
def imaginaryCoord (e : Fin 3) (w : imaginaryQuaternions) : ℝ :=
  ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] e
theorem sum_imaginaryCoord_smul (w : imaginaryQuaternions) :
    ∑ e, imaginaryCoord e w • imaginaryBasis e = w := by
  apply Subtype.ext
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  ext
  · simp only [Fin.sum_univ_three, imaginaryCoord, imaginaryBasis, hw]
    simp
    change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = 0
    ring
  · simp only [Fin.sum_univ_three, imaginaryCoord, imaginaryBasis]
    simp
    change (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    ring
  · simp only [Fin.sum_univ_three, imaginaryCoord, imaginaryBasis]
    simp
    change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    ring
  · simp only [Fin.sum_univ_three, imaginaryCoord, imaginaryBasis]
    simp
    change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    ring
theorem abs_imaginaryCoord_le (e : Fin 3) (w : imaginaryQuaternions) :
    |imaginaryCoord e w| ≤ ‖(w : ℍ[ℝ])‖ := by
  have h : ‖(w : ℍ[ℝ])‖ ^ 2 = (w : ℍ[ℝ]).re ^ 2 + (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
  fin_cases e <;> simp [imaginaryCoord] <;>
    nlinarith [sq_nonneg (w : ℍ[ℝ]).re, sq_nonneg (w : ℍ[ℝ]).imI, sq_nonneg (w : ℍ[ℝ]).imJ, sq_nonneg (w : ℍ[ℝ]).imK]
variable {F : BlockFrame}
theorem continuousAt_of_isBondAnalyticAt [Finite F.Cell] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : F.GaugeField F.top → E} {V : F.GaugeField F.top} (hG : IsBondAnalyticAt G V) : ContinuousAt G V := by
  classical
  have : Fintype F.Cell := Fintype.ofFinite _
  obtain ⟨N, ⟨e⟩⟩ : ∃ N : ℕ, Nonempty (Fin N ≃ (F.Cell × Fin 4) × Fin 3) :=
    ⟨_, ⟨(Fintype.equivFin _).symm⟩⟩
  let c : Fin N → F.Site F.top × Fin 4 := fun l => (e l).1
  let X : Fin N → imaginaryQuaternions := fun l => imaginaryBasis (e l).2
  let wv : F.GaugeField F.top → F.Cell × Fin 4 → imaginaryQuaternions :=
    fun V' b => minimalLog (V' b.1 b.2 * (V b.1 b.2)⁻¹)
  let sg : F.GaugeField F.top → Fin N → ℝ := fun V' l => imaginaryCoord (e l).2 (wv V' (e l).1)
  have hspread : ∀ V' y i, BlockAverages.bondSpread c X (sg V') y i = wv V' (y, i) := by
    intro V' y i
    unfold BlockAverages.bondSpread
    have e1 : (∑ l, if c l = (y, i) then sg V' l • X l else 0) =
        ∑ p : (F.Cell × Fin 4) × Fin 3, if p.1 = (y, i) then imaginaryCoord p.2 (wv V' p.1) • imaginaryBasis p.2 else 0 :=
      Equiv.sum_comp e fun p : (F.Cell × Fin 4) × Fin 3 =>
        if p.1 = (y, i) then imaginaryCoord p.2 (wv V' p.1) • imaginaryBasis p.2 else 0
    rw [e1, Fintype.sum_prod_type, Finset.sum_eq_single (y, i)]
    · simp only [if_true]
      exact sum_imaginaryCoord_smul _
    · intro b _ hb
      simp [hb]
    · simp
  have hturn : ∀ V', rotatedField (BlockAverages.bondSpread c X (sg V')) V = V' := by
    intro V'
    funext y i
    unfold rotatedField
    rw [hspread]
    show expUnit (minimalLog (V' y i * (V y i)⁻¹)) * V y i = V' y i
    rw [GaugeFixing.expUnit_minimalLog]
    simp
  have hcomp : G = fun V' => (fun σ : Fin N → ℝ => G (rotatedField (BlockAverages.bondSpread c X σ) V)) (sg V') := by
    funext V'
    show G V' = G (rotatedField (BlockAverages.bondSpread c X (sg V')) V)
    rw [hturn]
  have hsg0 : sg V = 0 := by
    funext l
    show imaginaryCoord (e l).2 (minimalLog (V (e l).1.1 (e l).1.2 * (V (e l).1.1 (e l).1.2)⁻¹)) = 0
    have h0 : minimalLog (V (e l).1.1 (e l).1.2 * (V (e l).1.1 (e l).1.2)⁻¹) = 0 := by
      rw [mul_inv_cancel]
      have h1 : (1 : UnitQuaternion) = expUnit 0 := by
        apply Subtype.ext
        show (1 : ℍ[ℝ]) = NormedSpace.exp ((0 : imaginaryQuaternions) : ℍ[ℝ])
        simp [NormedSpace.exp_zero]
      rw [h1]
      exact GaugeFixing.minimalLog_expUnit 0 (by simpa using Real.pi_pos)
    rw [h0]
    have hz : ∀ e' : Fin 3, imaginaryCoord e' (0 : imaginaryQuaternions) = 0 := by
      intro e'
      fin_cases e' <;> simp [imaginaryCoord]
    exact hz _
  have hsgc : ContinuousAt sg V := by
    refine continuousAt_pi.mpr fun l => ?_
    have hc0 : Continuous fun V' : F.GaugeField F.top => V' (e l).1.1 (e l).1.2 :=
      (continuous_apply (e l).1.2).comp (continuous_apply (e l).1.1)
    have hg : ContinuousAt (fun V' : F.GaugeField F.top => V' (e l).1.1 (e l).1.2 * (V (e l).1.1 (e l).1.2)⁻¹) V :=
      (hc0.mul continuous_const).continuousAt
    have htend : Filter.Tendsto (fun V' : F.GaugeField F.top =>
        ‖((V' (e l).1.1 (e l).1.2 * (V (e l).1.1 (e l).1.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖) (nhds V) (nhds 0) := by
      have h1 : ContinuousAt (fun V' : F.GaugeField F.top =>
          ‖((V' (e l).1.1 (e l).1.2 * (V (e l).1.1 (e l).1.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖) V :=
        ((continuous_subtype_val.continuousAt.comp hg).sub continuousAt_const).norm
      have h2 := h1.tendsto
      simpa using h2
    have hb : ∀ V' : F.GaugeField F.top, |sg V' l| ≤
        2 * ‖((V' (e l).1.1 (e l).1.2 * (V (e l).1.1 (e l).1.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := fun V' =>
      (abs_imaginaryCoord_le _ _).trans (GaugeFixing.norm_minimalLog_le _)
    have ht : Filter.Tendsto (fun V' => sg V' l) (nhds V) (nhds 0) := by
      refine squeeze_zero_norm (fun V' => ?_) (by simpa using htend.const_mul 2)
      exact hb V'
    show Filter.Tendsto (fun V' => sg V' l) (nhds V) (nhds (sg V l))
    rw [hsg0]
    exact ht
  have hH := (hG N c X).continuousAt
  rw [hcomp]
  exact ContinuousAt.comp_of_eq (by rw [hsg0]; exact hH) hsgc rfl |>.congr (Filter.Eventually.of_forall fun _ => rfl)
theorem continuous_readAtLevel {m : ℕ} (j : ℕ) : Continuous (readAtLevel (n := m) F j) := by apply _root_.YangMills.Construction.StepCosts.continuous_readAtLevel <;> assumption
theorem continuous_reflectedField (m : ℕ) (y : F.Cell) :
    Continuous fun V : F.GaugeField F.top => reflectedField m y V := by
  refine continuous_pi fun z => continuous_pi fun i => ?_
  unfold reflectedField
  simp only
  split_ifs
  · fun_prop
  · have h : Continuous fun V : F.GaugeField F.top => V (y + siteOfCoords F.top fun l =>
        reflectCoord m ((z l).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) l)) i := by fun_prop
    exact h.inv
open Classical in
theorem mem_chordBonds_finiteCells (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (b : F.Site F.depth × Fin 4) (hb : ¬ IsAxialTreeBond b) : b ∈ chordBonds (finiteCells F) := by
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hall : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth := by
    intro x
    obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
    refine Finset.mem_biUnion.mpr ⟨z, mem_finiteCells hpos z, Finset.mem_image.mpr ⟨h, ?_, rfl⟩⟩
    simpa [BlockFrame.top] using hh
  unfold chordBonds innerBonds
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hall _, Finset.mem_univ _⟩, hall _⟩, hb⟩
theorem continuousOn_frameCoord_of_cold_holds : continuousOn_frameCoord_of_cold := by
  intro ℓ δ lam ρA σA cg N hfit hch hσ t m n _ hm hn64 b hb
  obtain ⟨_, _, _, _, _, _, _, _, hbody⟩ := hch
  have hσpos := hfit.σ_pos
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  have hne0 : NeZero (n * ℓ.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  have : NeZero (n * (torusFrame ℓ.side t n).blockSide) := hne0
  have : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := hne0
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hodd : Odd (torusFrame ℓ.side t n).blockSide := hfit.L_odd
  have hs2 : ∀ i, 2 ≤ (torusFrame ℓ.side t n).extent i := fun i => by rw [hn]; omega
  have h2 : 2 ≤ n := by omega
  have hnt : ¬ IsAxialTreeBond (F := torusFrame ℓ.side t n)
      (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2) := by
    intro ht
    have h0 : ¬ IsAxialTreeBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2) := by
      classical
      exact (Finset.mem_filter.mp hb).2
    apply h0
    have e1 := (isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame ℓ.side t n) hn hodd h2 b.1 b.2).mp ht
    exact (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hfit.L_odd h2 b.1 b.2).mpr e1
  have hcell : enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) =
      torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1) :=
    enclosingCell_torusSiteInFrame hn b.1
  have hamb : IsAdmissibleAmbient (torusFrame ℓ.side t n) := Or.inr fun i => by rw [hn]; omega
  constructor
  · intro hbig
    have hsides : ∀ i, 4 * m + 5 < (torusFrame ℓ.side t n).extent i := fun i => by rw [hn]; exact hbig
    set F' := reflectedFrame (torusFrame ℓ.side t n) m with hF'
    have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by
      change 2 ≤ 4 * m
      omega
    have hodd' : Odd F'.blockSide := hfit.L_odd
    have hamb' : IsAdmissibleAmbient F' := Or.inr fun i => by
      change 64 ≤ 4 * m
      omega
    have hpos' : ∀ i, 0 < F'.extent i := fun i => by have := hs' i; omega
    have hreg' := isOrthantRegular_finiteCells (F := F') hpos' 2047
    have : Finite F'.Cell := finite_cell hpos'
    set bb := (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2) with hbb
    have hfr : ∀ V : TorusField n, frameCoord ℓ ρA t m V b = minimizingBondCoordinate ℓ.coupling ρA (finiteCells F')
        (reflectedBond (F := torusFrame ℓ.side t n) m bb)
        (reflectedField m (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) := by
      intro V
      unfold frameCoord bondFrameCoord
      rw [if_pos hsides]
      unfold reflectedBondCoord
      simp only
      rw [hcell]
    have hmb : reflectedBond (F := torusFrame ℓ.side t n) m bb ∈ chordBonds (finiteCells F') := by
      refine mem_chordBonds_finiteCells hodd' hs' _ fun ht => hnt ?_
      obtain ⟨hc', he⟩ := centre_cellOffset hodd hs2 bb.1
      have e1 : IsAxialTreeBond (F := torusFrame ℓ.side t n) bb ↔ IsTreeOffset ℓ.side (cellOffset bb.1, bb.2) := by
        have := isAxialTreeBond_iff hodd hs2 (enclosingCell bb.1) (cellOffset bb.1) hc' bb.2
        rwa [he] at this
      have e2 : IsAxialTreeBond (F := F') (reflectedBond (F := torusFrame ℓ.side t n) m bb) ↔
          IsTreeOffset ℓ.side (cellOffset bb.1, bb.2) := by
        have := isAxialTreeBond_iff hodd' hs' (0 : F'.Cell) (cellOffset bb.1) hc' bb.2
        have e3 : (cellCentre F'.depth (0 : F'.Cell) + siteOfCoords F'.depth (cellOffset bb.1) : F'.Site F'.depth) =
            (reflectedBond (F := torusFrame ℓ.side t n) m bb).1 := by
          have e4 : (cellCentre F'.depth (0 : F'.Cell) : F'.Site F'.depth) = 0 := by
            funext i
            simp [cellCentre, siteOfCoords, siteCoords]
          rw [e4, zero_add]
          rfl
        rwa [e3] at this
      exact e1.mpr (e2.mp ht)
    intro V hV
    have hcold := isCold_reflectedField (F := torusFrame ℓ.side t n) hn (m := m) (by omega) hσpos V (parentBlock ℓ.side b.1) hV
    obtain ⟨_, _, _, hA, _⟩ := hbody F' 2047 _ rfl hamb' (by norm_num) hreg' ℓ.threshold _ hσpos hσ hcold
    have hG := continuousAt_of_isBondAnalyticAt ((hA _ hmb).1)
    have hc : Continuous fun V : TorusField n => reflectedField m
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) :=
      (continuous_reflectedField m _).comp (continuous_readAtLevel _)
    have hfull : ContinuousAt (fun V : TorusField n => frameCoord ℓ ρA t m V b) V := by
      have e : (fun V : TorusField n => frameCoord ℓ ρA t m V b) = fun V =>
          minimizingBondCoordinate ℓ.coupling ρA (finiteCells F')
          (reflectedBond (F := torusFrame ℓ.side t n) m bb)
          (reflectedField m (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
            (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) := funext hfr
      rw [e]
      exact ContinuousAt.comp (f := fun V : TorusField n => reflectedField m
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) hG hc.continuousAt
    exact (continuous_subtype_val.continuousAt.comp hfull).continuousWithinAt
  · intro hsmall
    have hpos : ∀ i, 0 < (torusFrame ℓ.side t n).extent i := fun i => by have := hs2 i; omega
    have hreg := isOrthantRegular_finiteCells (F := torusFrame ℓ.side t n) hpos 2047
    have : Finite (torusFrame ℓ.side t n).Cell := finite_cell hpos
    set bb := (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2) with hbb
    have hfr : ∀ V : TorusField n, frameCoord ℓ ρA t m V b =
        minimizingBondCoordinate ℓ.coupling ρA (finiteCells (torusFrame ℓ.side t n)) bb
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := by
      intro V
      unfold frameCoord bondFrameCoord
      rw [if_neg (fun h => hsmall (h 0))]
    have hmb : bb ∈ chordBonds (finiteCells (torusFrame ℓ.side t n)) := mem_chordBonds_finiteCells hodd hs2 _ hnt
    intro V hV
    have hcold : IsCold (finiteCells (torusFrame ℓ.side t n)) (torusFrame ℓ.side t n).top ℓ.threshold
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := isCold_readAtLevel hn hV
    obtain ⟨_, _, _, hA, _⟩ := hbody (torusFrame ℓ.side t n) 2047 _ rfl hamb (by norm_num) hreg ℓ.threshold _ hσpos hσ hcold
    have hG := continuousAt_of_isBondAnalyticAt ((hA _ hmb).1)
    have hfull : ContinuousAt (fun V : TorusField n => frameCoord ℓ ρA t m V b) V := by
      have e : (fun V : TorusField n => frameCoord ℓ ρA t m V b) = fun V =>
          minimizingBondCoordinate ℓ.coupling ρA (finiteCells (torusFrame ℓ.side t n)) bb
            (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := funext hfr
      rw [e]
      exact ContinuousAt.comp (f := fun V : TorusField n => readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) hG
        (continuous_readAtLevel _).continuousAt
    exact (continuous_subtype_val.continuousAt.comp hfull).continuousWithinAt
end StepFrames
end YangMills.Construction
end
