import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ResponseInTheExpansion.ChartsOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ChartResponse
variable {F F' : BlockFrame}
open BlockOffsets

private abbrev LatticeOffset : Type := Fin 4 → ℤ
private def siteNear (Y : F.Cell) (p : LatticeOffset) : F.Site F.depth :=
  cellCentre F.depth Y + siteOfCoords F.depth p
private def NearBox (L r : ℕ) (p : LatticeOffset) : Prop := ∀ i, |p i| ≤ (L : ℤ) * r + halfSide L
private theorem cast_eq_two_mul_halfSide_add_one {L : ℕ} (hL : Odd L) : (L : ℤ) = 2 * halfSide L + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.cast_eq_two_mul_halfSide_add_one <;> assumption
private theorem exists_block_decomposition {L : ℕ} (hL : Odd L) (p : LatticeOffset) :
    ∃ g q : LatticeOffset, q ∈ centredCube L ∧ ∀ i, p i = (L : ℤ) * g i + q i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.exists_block_decomposition <;> assumption
private theorem mem_sitesOfCells_finiteCells (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) : x ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.mem_sitesOfCells_finiteCells <;> assumption
private theorem fineBondAt_mem_chordBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (g q : LatticeOffset) (j : Fin 4) (ht : ¬ IsAxialTreeBond (fineBondAt Y g q j)) :
    fineBondAt Y g q j ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.fineBondAt_mem_chordBonds <;> assumption
private theorem withinRadius_add_single {L r : ℕ} (hL : Odd L) {p g q : LatticeOffset} {j : Fin 4}
    (hp : ∀ i, p i = (L : ℤ) * g i + q i) (hq : q ∈ centredCube L) (hg : WithinRadius r g)
    (hp' : NearBox L r (p + Pi.single j 1)) (hqj : q j = halfSide L) :
    WithinRadius r (g + Pi.single j 1) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.withinRadius_add_single <;> assumption
private theorem chartedField_agree {L r : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius r b →
      V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y g q j).1 j = w' (fineBondAt Y' g q j).1 j)
    (p : LatticeOffset) (j : Fin 4) (hp : NearBox L r p) (hp' : NearBox L r (p + Pi.single j 1)) :
    chartedField w V (siteNear Y p) j = chartedField w' V' (siteNear Y' p) j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.chartedField_eq <;> assumption
private theorem refineSite_eq_cellCentre (Y : F.Cell) : _root_.YangMills.Construction.BlockAverages.refineSite Y = cellCentre F.depth Y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
private theorem contourAverage_agree {L : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    {Y : F.Cell} {Y' : F'.Cell} {X : F.GaugeField F.depth} {X' : F'.GaugeField F'.depth}
    (g : LatticeOffset) (d : Fin 4)
    (h : ∀ v k, (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      (v + LatticeFractionalIntegration.basisVector k - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      X (siteNear Y v) k = X' (siteNear Y' v) k) :
    _root_.YangMills.Construction.BlockAverages.contourAverage X ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
      _root_.YangMills.Construction.BlockAverages.contourAverage X' ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.contourAverage_eq_of_agree <;> assumption
private theorem nearBox_of_mem_twoBlockHull {L r : ℕ} (hL : Odd L) {g v : LatticeOffset} {d : Fin 4}
    (hg : WithinRadius r g) (hg' : WithinRadius r (g + Pi.single d 1))
    (hv : (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d) :
    NearBox L r v := by exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.nearBox_of_mem_twoBlockHull hL hg hg' hv
private theorem bondDeriv_fin_zero {G : F.GaugeField F.depth → ℝ} (W : F.GaugeField F.depth)
    (c : Fin 0 → F.Site F.depth × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.bondDeriv_zero_order <;> assumption
theorem sharesAndContoursAgreeOnTwoTori_of_coldEstimates (hch : ColdEstimatesAtEveryDepth) :
    SharesAndContoursAgreeOnTwoTori := by
  classical
  intro a L c ha hodd hL40 hc
  obtain ⟨N, hN0, hNc⟩ := hch a L c ha hodd hL40 hc
  have hσA : 0 < c.σA := hc.positivity.2.2.2.1
  obtain ⟨D, hD⟩ : ∃ D, D = c.σA ^ 2 * N 0 := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    have := hN0 0
    rw [hD]
    positivity
  refine ⟨D, hD0, ?_⟩
  intro F F' w w' V V' Y Y' r hr hT hT' ht hsm hsm' hag hww
  have hT0 := hT
  have hT0' := hT'
  obtain ⟨hF, n, hn, hside⟩ := hT
  obtain ⟨hF', n', hn', hside'⟩ := hT'
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hside']; omega
  obtain ⟨sd0, sd0', -, hV⟩ := hag
  have sd : ∀ i, 2 * r + 2 < F.extent i := fun i => by
    rcases sd0 i with h0 | h0
    · have := hs i
      omega
    · exact h0
  have sd' : ∀ i, 2 * r + 2 < F'.extent i := fun i => by
    rcases sd0' i with h0 | h0
    · have := hs' i
      omega
    · exact h0
  have hLpos : 0 < L := hodd.pos
  have hper : ∀ {G : BlockFrame}, G.blockSide = L → (∀ i, 2 * r + 2 < G.extent i) →
      ∀ i, 2 * r + 2 < G.period G.depth i := by
    intro G hG hg i
    rw [period_depth, hG]
    have := hg i
    nlinarith
  have hnear : ∀ (o : LatticeOffset) (u : LatticeOffset), o ∈ centredCube L → WithinRadius r u →
      NearBox L r (o + u) := by
    intro o u ho hu i
    have h1 := (mem_centredCube_iff o).1 ho i
    have h2 := abs_le.1 (hu i)
    have h3 : (r : ℤ) ≤ (L : ℤ) * r := by
      have : (1 : ℤ) ≤ L := by exact_mod_cast hLpos
      nlinarith
    simp only [Pi.add_apply]
    rw [abs_le]
    constructor <;> omega
  refine ⟨fun o ho => ?_, fun g d hg hg' => ?_⟩
  · have hag2 : AgreeOnBox (chartedField w V) (chartedField w' V') (siteNear Y o) (siteNear Y' o) r := by
      refine ⟨hper hF sd, hper hF' sd', fun b hb => ?_⟩
      have hsite : ∀ {G : BlockFrame} (Z : G.Cell),
          siteNear Z o + siteOfCoords G.depth b.1 = siteNear Z (o + b.1) := by
        intro G Z
        unfold siteNear
        rw [add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
      rw [hsite, hsite]
      refine chartedField_agree hF hF' hodd hs hs' hV hww (o + b.1) b.2 (hnear o b.1 ho hb.1) ?_
      rw [add_assoc]
      exact hnear o _ ho hb.2
    have hcmp := hNc.2 F F' c.σA _ _ _ _ r hT0 hT0' ht hσA le_rfl hsm.small_curvature
      hsm'.small_curvature hag2
    have h1 := hcmp.siteShare_deriv_close 0 Fin.elim0 Fin.elim0 (fun l => l.elim0) (fun l => l.elim0)
    rw [bondDeriv_fin_zero, bondDeriv_fin_zero] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hD]
    simp [derivativeScale]
  · exact contourAverage_agree hF hF' hodd (Y := Y) (Y' := Y') (X := chartedField w V)
      (X' := chartedField w' V') g d
      (fun v k h1 h2 => chartedField_agree hF hF' hodd hs hs' hV hww v k
        (nearBox_of_mem_twoBlockHull hodd hg hg' h1) (nearBox_of_mem_twoBlockHull hodd hg hg' h2))
end ChartResponse
end YangMills.Construction
end
