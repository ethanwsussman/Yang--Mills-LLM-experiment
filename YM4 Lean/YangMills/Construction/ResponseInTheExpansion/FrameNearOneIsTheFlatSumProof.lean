import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalarProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorAgreesOnItsBox
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorReadsItsBox
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.ResponseInTheExpansion.FlatSumsOnTwoTori
import YangMills.Construction.ResponseInTheExpansion.FrameNearOneIsTheFlatSum
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets YangMills.Construction.ColdStepAtMirrorFrames.SmallUnits
namespace NearFlat
variable {F : BlockFrame}
private theorem isSmallCurvature_leftTranslate_uniformField {j : ℕ} (v : F.Site j → Fin 4 → imaginaryQuaternions)
    {s ε : ℝ} (hε : ∀ x i, ‖v x i‖ ≤ ε)
    (hs : 4 * ε < s) : IsSmallCurvature s (leftTranslate v (ColdStepAtMirrorFrames.uniformField F j)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.isSmallCurvature_leftTranslate_uniform <;> assumption
open Classical in
private def foldedLinkForm (R : ℕ) (Y : F.Cell) (B : F.Cell → Fin 4 → imaginaryQuaternions)
    (z : (reflectedFrame F R).Cell) (l : Fin 4) : imaginaryQuaternions :=
  if IsForwardOriented R z l then B (Y + siteOfCoords F.top (sourceOffset (F := F) R z l)) l
  else - B (Y + siteOfCoords F.top (sourceOffset (F := F) R z l)) l
private theorem norm_foldedLinkForm_le {R : ℕ} {Y : F.Cell} {B : F.Cell → Fin 4 → imaginaryQuaternions} {s : ℝ}
    (hB : ∀ z l, ‖B z l‖ ≤ s)
    (z : (reflectedFrame F R).Cell) (l : Fin 4) : ‖foldedLinkForm R Y B z l‖ ≤ s := by
  classical
  unfold foldedLinkForm
  split_ifs
  · exact hB _ _
  · rw [norm_neg]
    exact hB _ _
private theorem isForwardOriented_of_bondWithinRadius {R : ℕ} (hR : 1 ≤ R) {h : Fin 4 → ℤ} {l : Fin 4}
    (hb : BondWithinRadius R (h, l)) :
    IsForwardOriented R (0 + siteOfCoords (reflectedFrame F R).top h : (reflectedFrame F R).Cell) l ∧
      sourceOffset (F := F) R (0 + siteOfCoords (reflectedFrame F R).top h : (reflectedFrame F R).Cell) l = h := by
  classical
  have hp : ∀ m, (reflectedFrame F R).period (reflectedFrame F R).top m = 4 * R :=
    fun m => TopLevelSites.period_top m
  have hval : ∀ m, ((0 + siteOfCoords (reflectedFrame F R).top h : (reflectedFrame F R).Cell) m).valMinAbs = h m := by
    intro m
    have hne : NeZero ((reflectedFrame F R).period (reflectedFrame F R).top m) := ⟨by rw [hp]; omega⟩
    rw [zero_add]
    change (((h m : ℤ) : ZMod ((reflectedFrame F R).period (reflectedFrame F R).top m))).valMinAbs = h m
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    rw [hp]
    have h1 : |h m| ≤ (R : ℤ) := hb.1 m
    have h1' := abs_le.mp h1
    push_cast
    constructor <;> omega
  have hfold : ∀ {e : ℤ}, |e| ≤ (R : ℤ) → reflectCoord R e = e := fun he => by
    unfold reflectCoord
    rw [if_pos he]
  have hfwd : IsForwardOriented R (0 + siteOfCoords (reflectedFrame F R).top h : (reflectedFrame F R).Cell) l := by
    unfold IsForwardOriented
    rw [hval l, hfold (hb.1 l)]
    have h2 := hb.2 l
    simp only [Pi.add_apply, Pi.single_eq_same] at h2
    exact hfold h2
  refine ⟨hfwd, ?_⟩
  unfold sourceOffset
  rw [if_pos hfwd]
  funext m
  rw [hval m, hfold (hb.1 m)]
private theorem foldedLinkForm_of_bondWithinRadius {R : ℕ} (hR : 1 ≤ R) {Y : F.Cell}
    {B : F.Cell → Fin 4 → imaginaryQuaternions} {h : Fin 4 → ℤ} {l : Fin 4}
    (hb : BondWithinRadius R (h, l)) :
    B (Y + siteOfCoords F.top h) l =
      foldedLinkForm R Y B (0 + siteOfCoords (reflectedFrame F R).top h : (reflectedFrame F R).Cell) l := by
  classical
  obtain ⟨h1, h2⟩ := isForwardOriented_of_bondWithinRadius (F := F) hR hb
  unfold foldedLinkForm
  rw [if_pos h1, h2]
private theorem gaugeTransform_reflectedField_eq (hrd : reflectedFieldReadsBox) {R : ℕ} (hR : 0 < R) {Y : F.Cell}
    {V : F.GaugeField F.top} {γ : F.Cell → UnitQuaternion} {B : F.Cell → Fin 4 → imaginaryQuaternions}
    (hlog : ∀ (h : Fin 4 → ℤ) (l : Fin 4), BondWithinRadius R (h, l) →
      gaugeTransform γ V (Y + siteOfCoords F.top h) l = expUnit (B (Y + siteOfCoords F.top h) l)) :
    gaugeTransform (reflectedGauge R Y γ) (reflectedField R Y V) =
      leftTranslate (foldedLinkForm R Y B)
        (ColdStepAtMirrorFrames.uniformField (reflectedFrame F R) (reflectedFrame F R).top) := by
  classical
  rw [← hrd.2.1 F R Y V γ hR]
  funext z l
  obtain ⟨hbox, hread⟩ := hrd.1 F R z l hR
  rw [hread Y (gaugeTransform γ V)]
  simp only [leftTranslate, ColdStepAtMirrorFrames.uniformField, mul_one]
  unfold foldedLinkForm
  rw [hlog _ _ hbox]
  split_ifs
  · rfl
  · rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallUnits.expUnit_neg]
section Chain
variable {a : ℝ} {L : ℕ} {c : ColdChainParameters}
private theorem minimizingChart_of_smallCurvature (hL : Odd L) (hc : c.Admissible a L) (hF : IsBlockTorus L F)
    {V : F.GaugeField F.top} (hV : IsSmallCurvature c.σA V) :
    IsMinimizingChart a (finiteCells F) V c.ρA (minimizingCoordinates a (finiteCells F) V c.ρA) ∧
      ∀ w, IsMinimizingChart a (finiteCells F) V c.ρA w → w = minimizingCoordinates a (finiteCells F) V c.ρA := by
  classical
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hρ := hc.classical.1
  have hπ : c.ρA < Real.pi := by linarith [Real.pi_gt_three, hρ.2.1]
  have hOdd : Odd F.blockSide := by rw [hF.1]; exact hL
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hC := hc.estimates F c.σA V hF hσ le_rfl hV
  obtain ⟨w, hw, -, hu⟩ := hC.minimizer
  have hwρ : IsMinimizingChart a (finiteCells F) V c.ρA w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hex : ∃ w, IsMinimizingChart a (finiteCells F) V c.ρA w := ⟨w, hwρ⟩
  have hl : minimizingCoordinates a (finiteCells F) V c.ρA = w := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact TopLevelSites.minimizingChart_unique hOdd hs hπ hex.choose_spec hwρ hu
  rw [hl]
  exact ⟨hwρ, fun w' hw' => TopLevelSites.minimizingChart_unique hOdd hs hπ hw' hwρ hu⟩
private theorem minimizingBondCoordinate_gaugeTransform (hT : MinimalActionGaugeCovariance) (hL : Odd L)
    (hc : c.Admissible a L)
    (hF : IsBlockTorus L F) {V : F.GaugeField F.top} (γ : F.Cell → UnitQuaternion) (hV : IsSmallCurvature c.σA V)
    (hV' : IsSmallCurvature c.σA (gaugeTransform γ V)) (b : F.Site F.depth × Fin 4) :
    minimizingBondCoordinate a c.ρA (finiteCells F) b (gaugeTransform γ V) =
      adjointMap (γ (enclosingCell b.1)) (minimizingBondCoordinate a c.ρA (finiteCells F) b V) := by
  have hOdd : Odd F.blockSide := by rw [hF.1]; exact hL
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have h1 := (minimizingChart_of_smallCurvature hL hc hF hV).1
  have h2 := (minimizingChart_of_smallCurvature hL hc hF hV').2 _ (hT.2 F a c.ρA V _ γ hOdd hs h1)
  unfold minimizingBondCoordinate
  exact (congrFun (congrFun h2 b.1) b.2).symm
end Chain
end NearFlat
set_option maxHeartbeats 2000000 in
open NearFlat in
theorem reflectedCoordNearFlatLinearPart_holds (hTy : smallFormCoordinateStatement) (hCm : FlatLinearPartLocality)
    (hT : MinimalActionGaugeCovariance) (hrd : reflectedFieldReadsBox) (hag : ReflectedFieldAgreesOnBox)
    (hCU : chartEquivarianceStatement) : ReflectedCoordNearFlatLinearPart := by
  intro a L c hL hc
  obtain ⟨K, s₀, hK, hs₀, hTay⟩ := hTy a L c hL hc
  obtain ⟨C₂, r₂, hC₂, hr₂, hCmp⟩ := hCm a L c hL hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hN0 : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  refine ⟨c.N 0 * c.σA + K + C₂ * min s₀ (c.σA / 16), min c.δ₁ r₂, min s₀ (c.σA / 16), by positivity,
    lt_min hδ hr₂, lt_min hs₀ (by positivity), ?_⟩
  intro F Y R m o i V γ B X s hF hbig hR hRm ho hb hX hs0 hs1 hcm hcR hB hlog
  classical
  obtain ⟨n, hn, hside⟩ := hF.2
  have hnF : ∀ l, F.extent l = n := hside
  have hs2 : ∀ l, 2 ≤ F.extent l := fun l => by rw [hside l]; omega
  have hOdd : Odd F.blockSide := by rw [hF.1]; exact hL
  have ho' : o ∈ centredCube F.blockSide := by rw [hF.1]; exact ho
  set M₀ := reflectedFrame F m with hM₀
  set M := reflectedFrame F R with hM
  have hFM₀ : IsBlockTorus L M₀ := ⟨hF.1, 4 * m, by omega, fun _ => rfl⟩
  have hFM : IsBlockTorus L M := ⟨hF.1, 4 * R, by omega, fun _ => rfl⟩
  have hsM₀ : ∀ l, 2 ≤ M₀.extent l := fun l => by change 2 ≤ 4 * m; omega
  have hsM : ∀ l, 2 ≤ M.extent l := fun l => by change 2 ≤ 4 * R; omega
  have hpM₀ : ∀ l, 0 < M₀.extent l := fun l => by have := hsM₀ l; omega
  have hpM : ∀ l, 0 < M.extent l := fun l => by have := hsM l; omega
  have hz : ∀ {G : BlockFrame}, (siteOfCoords G.top (0 : Fin 4 → ℤ) : G.Cell) = 0 := fun {G} => by
    funext l
    simp [siteOfCoords]
  have hlow : ∀ {G : BlockFrame} (z : G.Cell),
      fineBondAt z 0 o i = ((cellCentre G.depth z + siteOfCoords G.depth o : G.Site G.depth), i) := fun {G} z => by
    unfold fineBondAt
    simp only [hz, add_zero]
  have hcell : enclosingCell (fineBondAt Y 0 o i).1 = Y := by
    rw [hlow]
    exact TopLevelSites.enclosingCell_centre_add hOdd hs2 Y o ho'
  have hoff : cellOffset (fineBondAt Y 0 o i).1 = o := by
    rw [hlow]
    exact TopLevelSites.cellOffset_centre_add hOdd hs2 Y o ho'
  have hneM₀ : ∀ l, NeZero (M₀.period M₀.top l) :=
    fun l => ⟨by rw [TopLevelSites.period_top]; exact (hpM₀ l).ne'⟩
  have hneM : ∀ l, NeZero (M.period M.top l) :=
    fun l => ⟨by rw [TopLevelSites.period_top]; exact (hpM l).ne'⟩
  have hmir : reflectedBondCoord a c.ρA m (fineBondAt Y 0 o i) V =
      minimizingBondCoordinate a c.ρA (finiteCells M₀) (fineBondAt (0 : M₀.Cell) 0 o i) (reflectedField m Y V) := by
    unfold reflectedBondCoord reflectedBond
    rw [hcell, hoff, TopLevelSites.fineBondAt_zero hneM₀]
    rfl
  have hmirR : reflectedBondCoord a c.ρA R (fineBondAt Y 0 o i) V =
      minimizingBondCoordinate a c.ρA (finiteCells M) (fineBondAt (0 : M.Cell) 0 o i) (reflectedField R Y V) := by
    unfold reflectedBondCoord reflectedBond
    rw [hcell, hoff, TopLevelSites.fineBondAt_zero hneM]
    rfl
  set b := fineBondAt Y 0 o i with hbdef
  set b₀ := fineBondAt (0 : M₀.Cell) 0 o i with hb₀
  set b₁ := fineBondAt (0 : M.Cell) 0 o i with hb₁
  have hntree : ¬ IsAxialTreeBond b := (Finset.mem_filter.mp hb).2
  have hisoff : ¬ TopLevelSites.IsTreeOffset F.blockSide (o, i) := fun h =>
    hntree (by rw [hbdef, hlow]; exact (TopLevelSites.isAxialTreeBond_iff hOdd hs2 Y o ho' i).2 h)
  have hcM₀ : b₀ ∈ chordBonds (finiteCells M₀) := (hCU M₀ a hOdd hsM₀).mem_chordBonds_of_not_tree b₀ (fun h => hisoff
    ((TopLevelSites.isAxialTreeBond_iff (F := M₀) hOdd hsM₀ 0 o ho' i).1 (by rwa [hb₀, hlow] at h)))
  have hcM : b₁ ∈ chordBonds (finiteCells M) := (hCU M a hOdd hsM).mem_chordBonds_of_not_tree b₁ (fun h => hisoff
    ((TopLevelSites.isAxialTreeBond_iff (F := M) hOdd hsM 0 o ho' i).1 (by rwa [hb₁, hlow] at h)))
  have hcell₀ : enclosingCell b₀.1 = 0 := by
    rw [hb₀, hlow]
    exact TopLevelSites.enclosingCell_centre_add (F := M₀) hOdd hsM₀ 0 o ho'
  have hcell₁ : enclosingCell b₁.1 = 0 := by
    rw [hb₁, hlow]
    exact TopLevelSites.enclosingCell_centre_add (F := M) hOdd hsM 0 o ho'
  have hagree : AgreeOnBall (finiteCells M₀) (reflectedField m Y V) (finiteCells M) (reflectedField R Y V) 0 0 R := by
    refine ⟨fun l => Or.inr ?_, fun l => Or.inr ?_,
      fun _ _ => ⟨fun _ => TopLevelSites.mem_finiteCells hpM _, fun _ => TopLevelSites.mem_finiteCells hpM₀ _⟩,
      fun q hq => ?_⟩
    · change 2 * R + 2 < 4 * m
      omega
    · change 2 * R + 2 < 4 * R
      omega
    · have hRm' : (R : ℤ) ≤ m := by exact_mod_cast hRm
      have hq' : BondWithinRadius m q := ⟨fun l => (hq.1 l).trans hRm', fun l => (hq.2 l).trans hRm'⟩
      have e1 := (hag F m Y V (by omega) (fun l => by have := hbig l; omega)).2.2.2 q hq'
      have e2 := (hag F R Y V (by omega) (fun l => by have := hbig l; omega)).2.2.2 q hq
      exact e1.symm.trans e2
  have hnext : cellSupDist (0 : M₀.Cell) (enclosingCell (b₀.1 + unitStep M₀.depth i)) ≤ R := by
    have h1 := TopLevelSites.cellSupDist_enclosingCell_step_le (F := M₀) hOdd hsM₀ b₀.1 i
    rw [hcell₀] at h1
    omega
  have hin0 : BlockAverages.WithinRadius R (0 : Fin 4 → ℤ) := fun l => by simp
  have hcl := hc.estimates M₀ c.σA _ hFM₀ hσ le_rfl hcm
  have hloc := (hcl.locality M _ 0 0 R rfl rfl hFM.2 hcR hagree).2.1
  have h1 := (hloc 0 o i ho' hcM₀ hin0 hnext).1
  rw [← hb₀, ← hb₁, hcell₀, TopLevelSites.cellSupDist_self] at h1
  have hgt := gaugeTransform_reflectedField_eq (B := B) hrd (R := R) (by omega) hlog
  have hs4 : s ≤ c.σA / 16 := hs1.trans (min_le_right _ _)
  have hcD : IsSmallCurvature c.σA (leftTranslate (foldedLinkForm R Y B)
      (ColdStepAtMirrorFrames.uniformField (reflectedFrame F R) (reflectedFrame F R).top)) :=
    isSmallCurvature_leftTranslate_uniformField _ (ε := s) (norm_foldedLinkForm_le hB) (by linarith)
  have hco := minimizingBondCoordinate_gaugeTransform hT hL hc hFM (reflectedGauge R Y γ) hcR
    (by rw [hgt]; exact hcD) b₁
  have hΓ : reflectedGauge R Y γ (enclosingCell b₁.1) = γ Y := by
    rw [hcell₁]
    unfold reflectedGauge
    have e : (fun l => reflectCoord R (((0 : M.Cell) l).valMinAbs)) = (0 : Fin 4 → ℤ) := by
      funext l
      have := hneM l
      simp [reflectCoord]
    have e' := hz (G := F)
    change γ (Y + siteOfCoords F.top (fun l => reflectCoord R (((0 : M.Cell) l).valMinAbs))) = γ Y
    rw [e, e', add_zero]
  rw [hgt, hΓ] at hco
  have hTay' := hTay M b₁ (foldedLinkForm R Y B) X s hFM hcM hX hs0 (hs1.trans (min_le_left _ _))
    (norm_foldedLinkForm_le hB)
  have hCmp' := hCmp F M Y 0 R o i B (foldedLinkForm R Y B) X s hF hFM rfl
    (fun l => by have := hbig l; omega) (fun l => by change 2 * R + 2 < 4 * R; omega) (by omega) ho hb hcM hX hs0 hB
    (norm_foldedLinkForm_le hB) (fun h l hq => foldedLinkForm_of_bondWithinRadius (by omega) hq)
  rw [← hbdef, ← hb₁] at hCmp'
  have hw : torusCoordinate a c.ρA b₁ (leftTranslate (foldedLinkForm R Y B) (ColdStepAtMirrorFrames.uniformField M M.top)) =
      adjointMap (γ Y) (minimizingBondCoordinate a c.ρA (finiteCells M) b₁ (reflectedField R Y V)) := hco
  rw [show (flatTopField (F := M)) = ColdStepAtMirrorFrames.uniformField M M.top from rfl, hw] at hTay'
  rw [hmir]
  set u₀ := minimizingBondCoordinate a c.ρA (finiteCells M₀) b₀ (reflectedField m Y V) with hu₀
  set u₁ := minimizingBondCoordinate a c.ρA (finiteCells M) b₁ (reflectedField R Y V) with hu₁
  set fT := flatLinearPart a c.ρA X b B with hfT
  set fM := flatLinearPart a c.ρA X b₁ (foldedLinkForm R Y B) with hfM
  have hAd : ∀ v : imaginaryQuaternions, ‖adjointMap (γ Y) v‖ = ‖v‖ := fun v => by
    change ‖(γ Y : ℍ[ℝ]) * (v : ℍ[ℝ]) * ((γ Y)⁻¹ : UnitQuaternion)‖ = ‖(v : ℍ[ℝ])‖
    rw [norm_mul, norm_mul, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, one_mul, mul_one]
  have e : adjointMap (γ Y) u₀ - fT =
      adjointMap (γ Y) (u₀ - u₁) + (adjointMap (γ Y) u₁ - fM) + (fM - fT) := by
    rw [map_sub]
    abel
  change ‖adjointMap (γ Y) u₀ - fT‖ ≤ _
  rw [e]
  have n1 : ‖adjointMap (γ Y) (u₀ - u₁)‖ ≤ c.N 0 * c.σA * Real.exp (-c.δ₁ * ((R : ℝ) - ((0 : ℕ) : ℝ))) := by
    rw [hAd]
    exact h1
  have n2 : ‖adjointMap (γ Y) u₁ - fM‖ ≤ K * s ^ 2 := hTay'
  have n3 : ‖fM - fT‖ ≤ C₂ * s * Real.exp (-(r₂ * (R : ℝ))) := by
    rw [norm_sub_rev]
    rw [← Submodule.coe_sub] at hCmp'
    exact hCmp'
  set r := min c.δ₁ r₂ with hr
  set s₁ := min s₀ (c.σA / 16) with hs₁
  have hRr : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hE1 : Real.exp (-c.δ₁ * ((R : ℝ) - ((0 : ℕ) : ℝ))) ≤ Real.exp (-(r * (R : ℝ))) := by
    rw [Real.exp_le_exp]
    have : r ≤ c.δ₁ := min_le_left _ _
    push_cast
    nlinarith
  have hE2 : Real.exp (-(r₂ * (R : ℝ))) ≤ Real.exp (-(r * (R : ℝ))) := by
    rw [Real.exp_le_exp]
    have : r ≤ r₂ := min_le_right _ _
    nlinarith
  set E := Real.exp (-(r * (R : ℝ))) with hE
  have hEp : 0 < E := Real.exp_pos _
  have hs₁p : 0 < s₁ := lt_min hs₀ (by positivity)
  have m1 : c.N 0 * c.σA * Real.exp (-c.δ₁ * ((R : ℝ) - ((0 : ℕ) : ℝ))) ≤ c.N 0 * c.σA * E :=
    mul_le_mul_of_nonneg_left hE1 (by positivity)
  have m2 : C₂ * s * Real.exp (-(r₂ * (R : ℝ))) ≤ C₂ * s₁ * E :=
    mul_le_mul (mul_le_mul_of_nonneg_left hs1 hC₂) hE2 (Real.exp_pos _).le (by positivity)
  have hsq : 0 ≤ s ^ 2 := by positivity
  have h3 := norm_add₃_le (a := adjointMap (γ Y) (u₀ - u₁)) (b := adjointMap (γ Y) u₁ - fM) (c := fM - fT)
  have hA : 0 ≤ c.N 0 * c.σA := by positivity
  have hB' : 0 ≤ C₂ * s₁ := by positivity
  calc _ ≤ _ := h3
    _ ≤ c.N 0 * c.σA * E + K * s ^ 2 + C₂ * s₁ * E := by linarith
    _ ≤ (c.N 0 * c.σA + K + C₂ * s₁) * (s ^ 2 + E) := by
      have p1 := mul_nonneg hA hsq
      have p2 := mul_nonneg hK hEp.le
      have p3 := mul_nonneg hB' hsq
      nlinarith
end YangMills.Construction.WeightedResponses
end
