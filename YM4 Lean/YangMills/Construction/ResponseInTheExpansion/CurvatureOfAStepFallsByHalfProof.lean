import YangMills.Construction.ClusterExpansionOfAStep.ChartOnTheTorus
import YangMills.Construction.ClusterExpansionOfAStep.FlowWhereTheExpansionReturns
import YangMills.Construction.ClusterExpansionOfAStep.MovesAlongLinearDirections
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsAboveABox
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfAStepFallsByHalf
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps TorusCharts TopLevelSites BlockAverages StepCosts StepMarks TorusMirror StepSettings
  RenormalizationStepParameters ColdStepAtMirrorFrames LumpContours ColdChain
namespace CurvatureHalves
private theorem curvature_le_add_four_bonds {N N' : ℕ} (A : TorusField N) (B : TorusField N') (x : TorusSite N)
    (x' : TorusSite N') (μ ν : Fin 4) :
    curvature A x μ ν ≤ curvature B x' μ ν + (‖(A x μ : ℍ[ℝ]) - B x' μ‖ +
      ‖(A (x + TorusFields.unitStep N μ) ν : ℍ[ℝ]) - B (x' + TorusFields.unitStep N' μ) ν‖ +
      ‖(A (x + TorusFields.unitStep N ν) μ : ℍ[ℝ]) - B (x' + TorusFields.unitStep N' ν) μ‖ +
      ‖(A x ν : ℍ[ℝ]) - B x' ν‖) := by
  unfold curvature holonomy
  set a₁ := A (x + TorusFields.unitStep N μ) ν
  set a₂ := A (x + TorusFields.unitStep N ν) μ
  set b₁ := B (x' + TorusFields.unitStep N' μ) ν
  set b₂ := B (x' + TorusFields.unitStep N' ν) μ
  set P : UnitQuaternion := A x μ * a₁ * a₂⁻¹ * (A x ν)⁻¹
  set Q : UnitQuaternion := B x' μ * b₁ * b₂⁻¹ * (B x' ν)⁻¹
  have h1 : ‖(P : ℍ[ℝ]) - Q‖ ≤ ‖(A x μ : ℍ[ℝ]) - B x' μ‖ + ‖(a₁ : ℍ[ℝ]) - b₁‖ + ‖(a₂ : ℍ[ℝ]) - b₂‖ +
      ‖(A x ν : ℍ[ℝ]) - B x' ν‖ := by
    have a1 := TopLevelSites.norm_mul_sub_mul_le (A x μ * a₁ * a₂⁻¹) (B x' μ * b₁ * b₂⁻¹) (A x ν)⁻¹ (B x' ν)⁻¹
    have a2 := TopLevelSites.norm_mul_sub_mul_le (A x μ * a₁) (B x' μ * b₁) a₂⁻¹ b₂⁻¹
    have a3 := TopLevelSites.norm_mul_sub_mul_le (A x μ) (B x' μ) a₁ b₁
    rw [TopLevelSites.norm_inv_sub_inv] at a1 a2
    linarith
  have h2 : ‖(P : ℍ[ℝ]) - 1‖ ≤ ‖(Q : ℍ[ℝ]) - 1‖ + ‖(P : ℍ[ℝ]) - Q‖ := by
    have : (P : ℍ[ℝ]) - 1 = ((Q : ℍ[ℝ]) - 1) + ((P : ℍ[ℝ]) - Q) := by abel
    rw [this]
    exact norm_add_le _ _
  linarith
private theorem offsetFromCentre_cast {L : ℕ} (hL : 0 < L) (hodd : Odd L) (N : ℕ) (u : ℤ) :
    offsetFromCentre L (((u : ZMod (N * L))).cast : ℤ) = offsetFromCentre L u := by
  have hc : (((u : ZMod (N * L))).cast : ℤ) = u % ((N * L : ℕ) : ℤ) := ZMod.coe_intCast _
  rw [hc, Int.emod_def, sub_eq_add_neg]
  refine offsetFromCentre_add_dvd hL hodd _ _ ?_
  refine Dvd.dvd.neg_right (Dvd.dvd.mul_right ?_ _)
  push_cast
  exact Dvd.intro_left _ rfl
private def blockShift (L : ℕ) (yi u : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun l => (u l + ((L : ℤ) - 1) / 2) / (L : ℤ) - yi l
private def shiftedByBlock (L : ℕ) (yi u : Fin 4 → ℤ) : Fin 4 → ℤ := fun l => u l - (L : ℤ) * yi l
private theorem parentBlock_siteOfInt_eq_add {L n : ℕ} [NeZero L] [NeZero n] (yi u : Fin 4 → ℤ) :
    parentBlock L (siteOfInt u : TorusSite (n * L)) = siteOfInt yi + siteOfInt (blockShift L yi u) := by
  rw [CongruentBoxes.parentBlock_siteOfInt, ← siteOfInt_add]
  congr 1
  funext l
  simp [blockShift]
private theorem parentBlock_shiftedByBlock {L n : ℕ} [NeZero L] [NeZero n] (yi u : Fin 4 → ℤ) :
    parentBlock L (siteOfInt (shiftedByBlock L yi u) : TorusSite (n * L)) = siteOfInt (blockShift L yi u) := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [CongruentBoxes.parentBlock_siteOfInt]
  congr 1
  funext l
  simp only [shiftedByBlock, blockShift]
  have e : u l - (L : ℤ) * yi l + ((L : ℤ) - 1) / 2 = (u l + ((L : ℤ) - 1) / 2) + (L : ℤ) * (- yi l) := by ring
  rw [e, Int.add_mul_ediv_left _ _ hLpos.ne']
  ring
private theorem offsetFromCentre_shiftedByBlock {L : ℕ} (hL : 0 < L) (hodd : Odd L) (n n' : ℕ)
    (yi u : Fin 4 → ℤ) (l : Fin 4) :
    offsetFromCentre L ((((siteOfInt u : TorusSite (n * L)) l)).cast : ℤ) =
      offsetFromCentre L ((((siteOfInt (shiftedByBlock L yi u) : TorusSite (n' * L)) l)).cast : ℤ) := by
  show offsetFromCentre L ((((u l : ℤ) : ZMod (n * L))).cast : ℤ) =
    offsetFromCentre L ((((shiftedByBlock L yi u l : ℤ) : ZMod (n' * L))).cast : ℤ)
  rw [offsetFromCentre_cast hL hodd, offsetFromCentre_cast hL hodd]
  simp only [shiftedByBlock, sub_eq_add_neg]
  exact (offsetFromCentre_add_dvd hL hodd _ _ (Dvd.dvd.neg_right (Dvd.intro _ rfl))).symm
private theorem norm_torusChart_sub_le {L n n' : ℕ} [NeZero n] [NeZero n'] (w : TorusBond (n * L) → imaginaryQuaternions)
    (w' : TorusBond (n' * L) → imaginaryQuaternions) (V : TorusField n) (V' : TorusField n') (z : TorusSite (n * L))
    (z' : TorusSite (n' * L)) (i : Fin 4)
    (hoff : ∀ l, offsetFromCentre L ((z l).cast : ℤ) = offsetFromCentre L ((z' l).cast : ℤ))
    (hV : IsBlockEndBond L z i → V (parentBlock L z) i = V' (parentBlock L z') i) {B : ℝ} (hB : 0 ≤ B)
    (hw : ¬ IsBlockTreeBond L z i → ‖(w (z, i) : ℍ[ℝ]) - w' (z', i)‖ ≤ B) :
    ‖(torusChart L w V z i : ℍ[ℝ]) - torusChart L w' V' z' i‖ ≤ B := by
  have hc : IsBlockEndBond L z i ↔ IsBlockEndBond L z' i := by
    unfold IsBlockEndBond
    rw [hoff]
  have ht : IsBlockTreeBond L z i ↔ IsBlockTreeBond L z' i := by
    unfold IsBlockTreeBond
    have : (fun l => offsetFromCentre L ((z l).cast : ℤ)) = fun l => offsetFromCentre L ((z' l).cast : ℤ) :=
      funext hoff
    rw [this]
  unfold torusChart
  by_cases h1 : IsBlockEndBond L z i
  · have hnt : ¬ IsBlockTreeBond L z i := fun h => h.1 (by simpa [IsBlockEndBond] using h1)
    rw [if_pos h1, if_pos (hc.mp h1), hV h1]
    have := TopLevelSites.norm_mul_sub_mul_le (expUnit (w (z, i))) (expUnit (w' (z', i)))
      (V' (parentBlock L z') i) (V' (parentBlock L z') i)
    rw [sub_self, norm_zero, add_zero] at this
    exact this.trans ((norm_expUnit_sub_le _ _).trans (hw hnt))
  · rw [if_neg h1, if_neg (fun h => h1 (hc.mpr h))]
    by_cases h2 : IsBlockTreeBond L z i
    · rw [if_pos h2, if_pos (ht.mp h2), sub_self, norm_zero]
      exact hB
    · rw [if_neg h2, if_neg (fun h => h2 (ht.mpr h))]
      exact (norm_expUnit_sub_le _ _).trans (hw h2)
private theorem mem_sitesOfCells_finiteCells {F : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) : x ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.mem_sitesOfCells_finiteCells <;> assumption
private theorem mem_chordBonds_finiteCells {F : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (x, i)) : (x, i) ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.LinearDirections.mem_chordBonds_finiteCells <;> assumption
private def mirrorCoord (ℓ : TorusLumps.StepParameters) (ρA : ℝ) (t n ρ : ℕ) (V : TorusField n) (Y : TorusSite n)
    (b : TorusBond (4 * ρ * ℓ.side)) : imaginaryQuaternions :=
  minimizingBondCoordinate ℓ.coupling ρA (finiteCells (reflectedFrame (torusFrame ℓ.side t n) ρ))
    (torusSiteInFrame (reflectedFrame (torusFrame ℓ.side t n) ρ) (reflectedFrame (torusFrame ℓ.side t n) ρ).depth b.1, b.2)
    (reflectedField ρ (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top Y)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V))
private theorem mirrorCoord_bounds {ℓ : TorusLumps.StepParameters} {δ lam ρA σA cg : ℝ} {N : ℕ → ℝ}
    (hfit : ℓ.Admissible) (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N) (t n ρ : ℕ) [NeZero n]
    [NeZero (4 * ρ)] (hρ : 16 ≤ ρ) (V : TorusField n) (Y : TorusSite n) {s : ℝ} (hs : 0 < s) (hsσ : s ≤ σA)
    (hcold : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox ρ (a + d)) → curvature V (Y + siteOfInt a) μ ν < s) :
    (∀ b, ‖(mirrorCoord ℓ ρA t n ρ V Y b : ℍ[ℝ])‖ ≤ N 0 * s) ∧
      IsCold (s / 8) (torusChart ℓ.side (mirrorCoord ℓ ρA t n ρ V Y) (mirrorField ρ Y V)) := by
  obtain ⟨_, _, _, _, ρle, _, _, Npos, hbody⟩ := hch
  have hπ : ρA < Real.pi := lt_of_le_of_lt ρle (by linarith [Real.pi_gt_three])
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  set F := torusFrame ℓ.side t n with hF
  set M := reflectedFrame F ρ with hM
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  have hnM : ∀ i, M.extent i = 4 * ρ := fun _ => rfl
  have hoddM : Odd M.blockSide := hfit.L_odd
  have hsM : ∀ i, 2 ≤ M.extent i := fun i => by rw [hnM]; omega
  haveI hne : NeZero (4 * ρ * M.blockSide) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  have hamb : IsAdmissibleAmbient M := Or.inr fun i => by rw [hnM]; omega
  have hreg := isOrthantRegular_finiteCells (F := M) (fun i => by have := hsM i; omega) 2047
  have hc := isCold_reflectedField (F := F) hn (m := ρ) (by omega) hs V Y hcold
  have one := (hbody M 2047 _ rfl hamb (by norm_num) hreg s _ hs hsσ hc).1
  obtain ⟨w, hw, hcw, hlc⟩ := minimizingCoordinates_eq (ρ := ρA) hfit.L_odd hsM hπ le_rfl one
  have hmc : ∀ b, mirrorCoord ℓ ρA t n ρ V Y b = w (torusSiteInFrame M M.depth b.1) b.2 := by
    intro b
    unfold mirrorCoord minimizingBondCoordinate
    simp only
    rw [hlc]
  have hpF : ∀ i, M.period M.depth i = 4 * ρ * M.blockSide := fun i => period_depth_of_extent hnM i
  constructor
  · intro b
    rw [hmc]
    by_cases hb : (torusSiteInFrame M M.depth b.1, b.2) ∈ chordBonds (finiteCells M)
    · exact ((hw.2.1 _ hb).trans (min_le_right _ _))
    · have := hw.1 _ hb
      simp only at this
      rw [this]
      have := Npos 0
      simp
      positivity
  · intro x μ ν hlt
    have e0 : reflectedField ρ (torusSiteInFrame F F.top Y) (readAtLevel F F.top V) =
        readAtLevel M M.top (mirrorField ρ Y V) :=
      reflectedField_readAtLevel hn (by omega) Y V
    have hchart : ∀ (z : TorusSite (4 * ρ * M.blockSide)) (i : Fin 4),
        chartedField w (readAtLevel M M.top (mirrorField ρ Y V)) (torusSiteInFrame M M.depth z) i =
          torusChart ℓ.side (mirrorCoord ℓ ρA t n ρ V Y) (mirrorField ρ Y V) z i := by
      intro z i
      rw [chartedField_readAtLevel hnM hoddM (by omega) w (mirrorField ρ Y V) z i]
      exact torusChart_congr _ (hmc (z, i)).symm
    set Ws : TorusField (4 * ρ * M.blockSide) :=
      torusChart ℓ.side (mirrorCoord ℓ ρA t n ρ V Y) (mirrorField ρ Y V) with hWs
    have hread : chartedField w (readAtLevel M M.top (mirrorField ρ Y V)) = readAtLevel M M.depth Ws := by
      funext c i
      change _ = Ws (toTorusSite _ c) i
      rw [← hchart, torusSiteInFrame_toTorusSite hpF]
    have hp : ((torusSiteInFrame M M.depth x, μ, ν) : M.Site M.depth × Fin 4 × Fin 4) ∈
        innerPlaquettes (finiteCells M) M.depth := by
      unfold innerPlaquettes
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨mem_sitesOfCells_finiteCells hoddM hsM _, by simp⟩, hlt, ?_⟩
      intro c _
      exact mem_sitesOfCells_finiteCells hoddM hsM _
    have h1 := hcw _ hp
    rw [e0, hread, TopLevelSites.plaquetteDefect_readAtLevel_eq hpF] at h1
    have e1 : toTorusSite (4 * ρ * M.blockSide) (torusSiteInFrame M M.depth x) = x :=
      toTorusSite_torusSiteInFrame hpF x
    rwa [e1] at h1
private theorem mirrorFields_agree {F : BlockFrame} {n : ℕ} [NeZero n] (hn : ∀ i, F.extent i = n) {m₀ ρ r : ℕ}
    (hρ : 16 ≤ ρ) (hr : r + 2 = ρ) (hρm : ρ ≤ m₀) (V : TorusField n) (Y : TorusSite n) (e : Fin 4 → ℤ)
    (he : WithinRadius 1 e) :
    AgreeOnBall (finiteCells (reflectedFrame F m₀))
      (reflectedField m₀ (torusSiteInFrame F F.top (Y + siteOfInt e)) (readAtLevel F F.top V))
      (finiteCells (reflectedFrame F ρ))
      (reflectedField ρ (torusSiteInFrame F F.top Y) (readAtLevel F F.top V)) 0
      (siteOfCoords (reflectedFrame F ρ).top e) r := by
  haveI : NeZero (4 * m₀) := ⟨by omega⟩
  haveI : NeZero (4 * ρ) := ⟨by omega⟩
  have hs₀ : ∀ i, 0 < (reflectedFrame F m₀).extent i := fun i => by
    change 0 < 4 * m₀
    omega
  have hs₁ : ∀ i, 0 < (reflectedFrame F ρ).extent i := fun i => by
    change 0 < 4 * ρ
    omega
  have hp₀ : ∀ i, (reflectedFrame F m₀).period (reflectedFrame F m₀).top i = 4 * m₀ := fun i => by
    rw [period_top]
    rfl
  have hp₁ : ∀ i, (reflectedFrame F ρ).period (reflectedFrame F ρ).top i = 4 * ρ := fun i => by
    rw [period_top]
    rfl
  refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun h _ => ?_, fun b hb => ?_⟩
  · change 2 * r + 2 < 4 * m₀
    omega
  · change 2 * r + 2 < 4 * ρ
    omega
  · exact ⟨fun _ => mem_finiteCells hs₁ _, fun _ => mem_finiteCells hs₀ _⟩
  · rw [reflectedField_readAtLevel hn (by omega), reflectedField_readAtLevel hn (by omega)]
    have e1 : readAtLevel (reflectedFrame F m₀) (reflectedFrame F m₀).top (mirrorField m₀ (Y + siteOfInt e) V)
        (0 + siteOfCoords (reflectedFrame F m₀).top b.1) b.2 =
        mirrorField m₀ (Y + siteOfInt e) V
          (toTorusSite (4 * m₀) (0 + siteOfCoords (reflectedFrame F m₀).top b.1)) b.2 := rfl
    have e2 : readAtLevel (reflectedFrame F ρ) (reflectedFrame F ρ).top (mirrorField ρ Y V)
        (siteOfCoords (reflectedFrame F ρ).top e + siteOfCoords (reflectedFrame F ρ).top b.1) b.2 =
        mirrorField ρ Y V (toTorusSite (4 * ρ)
          (siteOfCoords (reflectedFrame F ρ).top e + siteOfCoords (reflectedFrame F ρ).top b.1)) b.2 := rfl
    rw [e1, e2, zero_add, toTorusSite_siteOfCoords hp₀, toTorusSite_add hp₁, toTorusSite_siteOfCoords hp₁,
      toTorusSite_siteOfCoords hp₁, ← siteOfInt_add]
    have b₀ : BondOffsetInBox m₀ b := ⟨fun i => (hb.1 i).trans (by push_cast; omega),
      fun i => (hb.2 i).trans (by push_cast; omega)⟩
    have b₁ : BondOffsetInBox ρ (e + b.1, b.2) := by
      constructor
      · intro i
        have h1 := abs_le.mp (he i)
        have h2 := abs_le.mp (hb.1 i)
        rw [abs_le]
        simp only [Pi.add_apply]
        push_cast at h1 h2 ⊢
        constructor <;> omega
      · intro i
        have h1 := abs_le.mp (he i)
        have h2 := abs_le.mp (hb.2 i)
        rw [abs_le]
        simp only [Pi.add_apply] at h2 ⊢
        push_cast at h1 h2 ⊢
        constructor <;> omega
    have a₀ := mirrorField_siteOfInt (n := n) (m := m₀) (by omega) (Y + siteOfInt e) V b b₀
    have a₁ := mirrorField_siteOfInt (n := n) (m := ρ) (by omega) Y V (e + b.1, b.2) b₁
    rw [a₀]
    refine Eq.trans ?_ a₁.symm
    simp only
    rw [siteOfInt_add, add_assoc]
private theorem norm_frameCoord_sub_mirrorCoord_le {ℓ : TorusLumps.StepParameters} {δ lam ρA σA cg : ℝ}
    {N : ℕ → ℝ} (hfit : ℓ.Admissible) (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N)
    (t n m₀ ρ r : ℕ) [NeZero n] [NeZero (4 * ρ)] (hρ : 16 ≤ ρ) (hr : r + 2 = ρ) (hρm : ρ ≤ m₀)
    (hbig : 4 * m₀ + 5 < n) (V : TorusField n) (Y : TorusSite n) {s : ℝ} (hs : 0 < s) (hsσ : s ≤ σA)
    (e : Fin 4 → ℤ) (he : WithinRadius 1 e)
    (hcoldY : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox ρ (a + d)) → curvature V (Y + siteOfInt a) μ ν < s)
    (hcoldy : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m₀ (a + d)) → curvature V (Y + siteOfInt e + siteOfInt a) μ ν < s)
    (b : TorusBond (n * ℓ.side)) (hb : b ∈ StepCosts.chartBonds ℓ.side n) (z' : TorusSite (4 * ρ * ℓ.side))
    (hblock : parentBlock ℓ.side b.1 = Y + siteOfInt e) (hblock' : parentBlock ℓ.side z' = siteOfInt e)
    (hoff : ∀ l, offsetFromCentre ℓ.side ((b.1 l).cast : ℤ) = offsetFromCentre ℓ.side ((z' l).cast : ℤ)) :
    ‖(frameCoord ℓ ρA t m₀ V b : ℍ[ℝ]) - mirrorCoord ℓ ρA t n ρ V Y (z', b.2)‖ ≤
      N 0 * s * Real.exp (-(δ * (r : ℝ))) := by
  obtain ⟨_, _, _, _, _, _, _, _, hbody⟩ := hch
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  have hodd := hfit.L_odd
  set F := torusFrame ℓ.side t n with hF
  set M₀ := reflectedFrame F m₀ with hM₀
  set M := reflectedFrame F ρ with hM
  haveI : NeZero (4 * m₀) := ⟨by omega⟩
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  have hnM₀ : ∀ i, M₀.extent i = 4 * m₀ := fun _ => rfl
  have hnM : ∀ i, M.extent i = 4 * ρ := fun _ => rfl
  have hoddF : Odd F.blockSide := hodd
  have hoddM₀ : Odd M₀.blockSide := hodd
  have hoddM : Odd M.blockSide := hodd
  have h2 : 2 ≤ n := by omega
  have hsF : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; omega
  have hsM₀ : ∀ i, 2 ≤ M₀.extent i := fun i => by rw [hnM₀]; omega
  have hsM : ∀ i, 2 ≤ M.extent i := fun i => by rw [hnM]; omega
  haveI : NeZero (n * F.blockSide) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  haveI : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  haveI : NeZero (4 * ρ * M.blockSide) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  have hamb₀ : IsAdmissibleAmbient M₀ := Or.inr fun i => by rw [hnM₀]; omega
  have hamb : IsAdmissibleAmbient M := Or.inr fun i => by rw [hnM]; omega
  have hreg₀ := isOrthantRegular_finiteCells (F := M₀) (fun i => by have := hsM₀ i; omega) 2047
  have hreg := isOrthantRegular_finiteCells (F := M) (fun i => by have := hsM i; omega) 2047
  have hc₀ := isCold_reflectedField (F := F) hn (m := m₀) (by omega) hs V (Y + siteOfInt e) hcoldy
  have hc := isCold_reflectedField (F := F) hn (m := ρ) (by omega) hs V Y hcoldY
  have hag := mirrorFields_agree (F := F) hn (m₀ := m₀) hρ hr hρm V Y e he
  obtain ⟨_, _, _, _, _, two⟩ := hbody M₀ 2047 _ rfl hamb₀ (by norm_num) hreg₀ s _ hs hsσ hc₀
  have hloc := (two M _ _ 0 (siteOfCoords M.top e) r rfl rfl hamb hreg hc hag).2
  set xp : F.Site F.depth := torusSiteInFrame F F.depth b.1 with hxp
  set o := cellOffset xp with ho
  have hocube : o ∈ centredCube F.blockSide := (centre_cellOffset hoddF hsF xp).1
  have hocube₀ : o ∈ centredCube M₀.blockSide := hocube
  have hcell : enclosingCell xp = torusSiteInFrame F F.top (Y + siteOfInt e) := by
    have c0 : enclosingCell xp = torusSiteInFrame F F.top (parentBlock F.blockSide b.1) :=
      enclosingCell_torusSiteInFrame hn b.1
    rw [c0]
    exact congrArg _ hblock
  have hsides : ∀ i, 4 * m₀ + 5 < F.extent i := fun i => by rw [hn]; exact hbig
  have hfr : frameCoord ℓ ρA t m₀ V b = minimizingBondCoordinate ℓ.coupling ρA (finiteCells M₀)
      (reflectedBond (F := F) m₀ (xp, b.2))
      (reflectedField m₀ (torusSiteInFrame F F.top (Y + siteOfInt e)) (readAtLevel F F.top V)) := by
    unfold StepCosts.frameCoord bondFrameCoord
    rw [if_pos hsides]
    unfold reflectedBondCoord
    simp only
    rw [← hcell]
  have hne' : ∀ i, NeZero (M₀.period M₀.top i) := fun i => ⟨by rw [period_top]; have := hsM₀ i; omega⟩
  have hlow₀ : fineBondAt (0 : M₀.Cell) 0 o b.2 = reflectedBond (F := F) m₀ (xp, b.2) :=
    fineBondAt_zero (F' := M₀) hne' o b.2
  have hpM : ∀ i, M.period M.top i = 4 * ρ := fun i => by rw [period_top]; rfl
  set xq : M.Site M.depth := torusSiteInFrame M M.depth z' with hxq
  have hcell' : enclosingCell xq = siteOfCoords M.top e := by
    have c1 : enclosingCell xq = torusSiteInFrame M M.top (parentBlock M.blockSide z') :=
      enclosingCell_torusSiteInFrame hnM z'
    have e1 : parentBlock M.blockSide z' = siteOfInt e := hblock'
    rw [c1, e1]
    exact torusSiteInFrame_siteOfInt hpM e
  have hoff' : cellOffset xq = o := by
    funext l
    have a1 : cellOffset xq l = offsetFromCentre M.blockSide ((z' l).cast : ℤ) :=
      cellOffset_torusSiteInFrame hnM hoddM (by omega) z' l
    have a2 : o l = offsetFromCentre F.blockSide ((b.1 l).cast : ℤ) :=
      cellOffset_torusSiteInFrame hn hoddF h2 b.1 l
    rw [a1, a2]
    exact (hoff l).symm
  have hlow : fineBondAt (siteOfCoords M.top e) 0 o b.2 = (xq, b.2) := by
    rw [← hcell', ← hoff']
    exact fineBondAt_enclosingCell_cellOffset hoddM hsM xq b.2
  have hnt : ¬ IsTreeOffset ℓ.side (o, b.2) := by
    intro ht
    have h0 : ¬ IsAxialTreeBond (F := stepBlockFrame ℓ.side n)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2) := by
      classical
      exact (Finset.mem_filter.mp hb).2
    apply h0
    refine (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hodd h2
      b.1 b.2).mpr ?_
    have e1 : o = fun l => offsetFromCentre ℓ.side ((b.1 l).cast : ℤ) := by
      funext l
      rw [ho, hxp]
      exact cellOffset_torusSiteInFrame hn hoddF h2 b.1 l
    rw [e1] at ht
    exact ht
  have hchart : fineBondAt (0 : M₀.Cell) 0 o b.2 ∈ chordBonds (finiteCells M₀) := by
    have h1 : IsAxialTreeBond (fineBondAt (0 : M₀.Cell) 0 o b.2) ↔ IsTreeOffset M₀.blockSide (o, b.2) :=
      isAxialTreeBond_iff hoddM₀ hsM₀ _ o hocube₀ b.2
    exact mem_chordBonds_finiteCells hoddM₀ hsM₀ _ _ (fun h => hnt (h1.mp h))
  have hc0 : enclosingCell (fineBondAt (0 : M₀.Cell) 0 o b.2).1 = 0 := by
    have h1 : enclosingCell (fineBondAt (0 : M₀.Cell) 0 o b.2).1 = (0 : M₀.Cell) + siteOfCoords M₀.top 0 :=
      enclosingCell_centre_add hoddM₀ hsM₀ _ o hocube₀
    rw [h1, siteOfCoords_zero, add_zero]
  have hl := (hloc 0 o b.2 hocube₀ hchart (fun i => by simp) (by
    have h1 := cellSupDist_enclosingCell_step_le hoddM₀ hsM₀ (fineBondAt (0 : M₀.Cell) 0 o b.2).1 b.2
    rw [hc0] at h1
    exact h1.trans (by omega))).1
  have hd : cellSupDist (0 : M₀.Cell) (enclosingCell (fineBondAt (0 : M₀.Cell) 0 o b.2).1) = 0 := by
    rw [hc0, cellSupDist_self]
  rw [hd] at hl
  have hle : fineBondAt (siteOfCoords M.top e + siteOfCoords M.top 0) = fineBondAt (siteOfCoords M.top e) := by
    rw [siteOfCoords_zero, add_zero]
  have hl2 : ‖(minimizingBondCoordinate ℓ.coupling ρA (finiteCells M₀) (fineBondAt (0 : M₀.Cell) 0 o b.2)
        (reflectedField m₀ (torusSiteInFrame F F.top (Y + siteOfInt e)) (readAtLevel F F.top V)) : ℍ[ℝ]) -
      minimizingBondCoordinate ℓ.coupling ρA (finiteCells M) (fineBondAt (siteOfCoords M.top e) 0 o b.2)
        (reflectedField ρ (torusSiteInFrame F F.top Y) (readAtLevel F F.top V))‖ ≤
      N 0 * s * Real.exp (-δ * ((r : ℝ) - ((0 : ℕ) : ℝ))) := hl
  rw [hlow₀, hlow] at hl2
  rw [hfr]
  have e3 : -δ * ((r : ℝ) - ((0 : ℕ) : ℝ)) = -(δ * (r : ℝ)) := by push_cast; ring
  rw [e3] at hl2
  exact hl2
private def IsColdNear {n : ℕ} (V : TorusField n) (Y : TorusSite n) (ρ : ℕ) (s : ℝ) : Prop :=
  ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
    (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox ρ (a + d)) → curvature V (Y + siteOfInt a) μ ν < s
private theorem norm_chart_sub_mirror_le {ℓ : TorusLumps.StepParameters} {δ lam ρA σA cg : ℝ} {N : ℕ → ℝ}
    (hfit : ℓ.Admissible) (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N) (t n m₀ ρ r : ℕ)
    [NeZero n] [NeZero (4 * ρ)] (hρ : 16 ≤ ρ) (hr : r + 2 = ρ) (hρm : ρ ≤ m₀) (hbig : 4 * m₀ + 5 < n)
    (V : TorusField n) (W : TorusField (n * ℓ.side)) (yi u : Fin 4 → ℤ)
    {s₁ : ℝ} (hs₁ : 0 < s₁) (hs₁σ : s₁ ≤ σA) (hcoldY : IsColdNear V (siteOfInt yi) ρ s₁)
    (hcoldy : IsColdNear V (siteOfInt yi + siteOfInt (blockShift ℓ.side yi u)) m₀ s₁)
    (he : WithinRadius 1 (blockShift ℓ.side yi u)) (i : Fin 4) {B : ℝ} (hB : 0 ≤ B)
    (hη : ((siteOfInt u : TorusSite (n * ℓ.side)), i) ∈ StepCosts.chartBonds ℓ.side n →
      ‖(frameDeviation ℓ ρA t m₀ V W (siteOfInt u, i) : ℍ[ℝ])‖ ≤ B) :
    ‖(torusChart ℓ.side (chartCoord ℓ V W) V (siteOfInt u) i : ℍ[ℝ]) -
      torusChart ℓ.side (mirrorCoord ℓ ρA t n ρ V (siteOfInt yi)) (mirrorField ρ (siteOfInt yi) V)
        (siteOfInt (shiftedByBlock ℓ.side yi u)) i‖ ≤ B + N 0 * s₁ * Real.exp (-(δ * (r : ℝ))) := by
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  have hodd := hfit.L_odd
  have hNpos := hch.2.2.2.2.2.2.2.1 0
  have h2 : 2 ≤ n := by omega
  haveI : NeZero (n * ℓ.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  haveI : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  set e := blockShift ℓ.side yi u with he'
  refine norm_torusChart_sub_le _ _ V _ _ _ i (offsetFromCentre_shiftedByBlock hLpos hodd n (4 * ρ) yi u) ?_
    (by positivity) ?_
  · intro _
    rw [parentBlock_siteOfInt_eq_add yi u, parentBlock_shiftedByBlock yi u]
    have b₁ : BondOffsetInBox ρ (e, i) := by
      constructor
      · intro l
        exact (he l).trans (by push_cast; omega)
      · intro l
        have h1 := abs_le.mp (he l)
        rw [abs_le]
        simp only [Pi.add_apply]
        have h3 : (Pi.single i 1 : Fin 4 → ℤ) l ≤ 1 ∧ 0 ≤ (Pi.single i 1 : Fin 4 → ℤ) l := by
          by_cases hl : l = i
          · subst hl
            simp
          · simp [Pi.single_eq_of_ne hl]
        obtain ⟨h4, h5⟩ := h3
        push_cast at h1 ⊢
        constructor <;> omega
    exact (mirrorField_siteOfInt (n := n) (m := ρ) (by omega) (siteOfInt yi) V (e, i) b₁).symm
  · intro hnt
    have hb : ((siteOfInt u : TorusSite (n * ℓ.side)), i) ∈ StepCosts.chartBonds ℓ.side n := by
      classical
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ht => hnt ?_⟩
      exact (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hodd h2 _ i).mp ht
    have hfar := norm_frameCoord_sub_mirrorCoord_le hfit hch t n m₀ ρ r hρ hr hρm hbig V (siteOfInt yi) hs₁ hs₁σ
      e he hcoldY hcoldy (siteOfInt u, i) hb (siteOfInt (shiftedByBlock ℓ.side yi u))
      (parentBlock_siteOfInt_eq_add yi u) (parentBlock_shiftedByBlock yi u)
      (offsetFromCentre_shiftedByBlock hLpos hodd n (4 * ρ) yi u)
    have hdec : (chartCoord ℓ V W (siteOfInt u, i) : ℍ[ℝ]) -
        mirrorCoord ℓ ρA t n ρ V (siteOfInt yi) (siteOfInt (shiftedByBlock ℓ.side yi u), i) =
        ((frameDeviation ℓ ρA t m₀ V W (siteOfInt u, i) : imaginaryQuaternions) : ℍ[ℝ]) +
          (((StepCosts.frameCoord ℓ ρA t m₀ V (siteOfInt u, i) : imaginaryQuaternions) : ℍ[ℝ]) -
            mirrorCoord ℓ ρA t n ρ V (siteOfInt yi) (siteOfInt (shiftedByBlock ℓ.side yi u), i)) := by
      have e' : ((frameDeviation ℓ ρA t m₀ V W (siteOfInt u, i) : imaginaryQuaternions) : ℍ[ℝ]) =
          (chartCoord ℓ V W (siteOfInt u, i) : ℍ[ℝ]) -
            ((StepCosts.frameCoord ℓ ρA t m₀ V (siteOfInt u, i) : imaginaryQuaternions) : ℍ[ℝ]) := rfl
      rw [e']
      abel
    rw [hdec]
    exact (norm_add_le _ _).trans (add_le_add (hη hb) hfar)
private theorem ediv_succ_sub_ediv {L : ℕ} (hL : 0 < L) (c : ℤ) :
    (c + 1) / (L : ℤ) - c / (L : ℤ) = 0 ∨ (c + 1) / (L : ℤ) - c / (L : ℤ) = 1 := by
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have h1 : c / (L : ℤ) ≤ (c + 1) / (L : ℤ) := Int.ediv_le_ediv hLz (by omega)
  have h2 : (c + 1) / (L : ℤ) ≤ (c + (L : ℤ)) / (L : ℤ) := Int.ediv_le_ediv hLz (by omega)
  have h3 : (c + (L : ℤ)) / (L : ℤ) = c / (L : ℤ) + 1 := by
    have := Int.add_mul_ediv_right c 1 hLz.ne'
    simpa using this
  omega
private theorem blockShift_unitStep_mem {L : ℕ} (hL : 0 < L) (u : Fin 4 → ℤ) (i : Fin 4) :
    WithinRadius 1 (blockShift L (fun l => (u l + ((L : ℤ) - 1) / 2) / (L : ℤ)) (u + Pi.single i 1)) := by
  intro l
  simp only [blockShift, Pi.add_apply]
  by_cases hl : l = i
  · subst hl
    simp only [Pi.single_eq_same]
    have := ediv_succ_sub_ediv hL (u l + ((L : ℤ) - 1) / 2)
    have e : u l + 1 + ((L : ℤ) - 1) / 2 = u l + ((L : ℤ) - 1) / 2 + 1 := by ring
    rw [e]
    rcases this with h | h <;> rw [h] <;> simp
  · simp [Pi.single_eq_of_ne hl]
private theorem blockShift_self {L : ℕ} (u : Fin 4 → ℤ) :
    blockShift L (fun l => (u l + ((L : ℤ) - 1) / 2) / (L : ℤ)) u = 0 := by
  funext l
  simp [blockShift]
private theorem shiftedByBlock_add (L : ℕ) (yi u d : Fin 4 → ℤ) :
    shiftedByBlock L yi (u + d) = shiftedByBlock L yi u + d := by
  funext l
  simp only [shiftedByBlock, Pi.add_apply]
  ring
private theorem siteOfInt_castCoords {N : ℕ} [NeZero N] (x : TorusSite N) :
    (siteOfInt (fun l => ((x l).cast : ℤ)) : TorusSite N) = x := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_cast_self <;> assumption
private theorem curvature_chart_le {ℓ : TorusLumps.StepParameters} {δ lam ρA σA cg : ℝ} {N : ℕ → ℝ}
    (hfit : ℓ.Admissible) (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N) (t n m₀ ρ r : ℕ)
    [NeZero n] [NeZero (4 * ρ)] (hρ : 16 ≤ ρ) (hr : r + 2 = ρ) (hρm : ρ ≤ m₀) (hbig : 4 * m₀ + 5 < n)
    (V : TorusField n) (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (μ ν : Fin 4) (hlt : μ < ν)
    {s s₁ : ℝ} (hs : 0 < s) (hsσ : s ≤ σA) (hs₁ : 0 < s₁) (hs₁σ : s₁ ≤ σA)
    (hcold : IsColdNear V (parentBlock ℓ.side x) ρ s) (hcold₁ : IsColdNear V (parentBlock ℓ.side x) ρ s₁)
    (hcoldy : ∀ e, WithinRadius 1 e → IsColdNear V (parentBlock ℓ.side x + siteOfInt e) m₀ s₁)
    {B : ℝ} (hB : 0 ≤ B)
    (hη : ∀ b ∈ StepCosts.chartBonds ℓ.side n, (b.1 = x ∨ b.1 = x + TorusFields.unitStep (n * ℓ.side) μ ∨
      b.1 = x + TorusFields.unitStep (n * ℓ.side) ν) → ‖(frameDeviation ℓ ρA t m₀ V W b : ℍ[ℝ])‖ ≤ B) :
    curvature W x μ ν ≤ s / 8 + 4 * (B + N 0 * s₁ * Real.exp (-(δ * (r : ℝ)))) := by
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  have hodd := hfit.L_odd
  have h2 : 2 ≤ n := by omega
  haveI hne0 : NeZero (n * ℓ.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  haveI : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := hne0
  set u₀ : Fin 4 → ℤ := fun l => ((x l).cast : ℤ) with hu₀
  set yi : Fin 4 → ℤ := fun l => (u₀ l + ((ℓ.side : ℤ) - 1) / 2) / (ℓ.side : ℤ) with hyi
  have hY : parentBlock ℓ.side x = siteOfInt yi := rfl
  have hx : (siteOfInt u₀ : TorusSite (n * ℓ.side)) = x := siteOfInt_castCoords x
  rw [hY] at hcold hcold₁ hcoldy
  have hA : curvature W x μ ν = curvature (torusChart ℓ.side (chartCoord ℓ V W) V) x μ ν := by
    have e := gaugeTransform_axialGauge_eq_torusChart (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hodd h2 W V
    have e' : torusChart ℓ.side (chartCoord ℓ V W) V = TorusFields.gaugeTransform
        (fun z => axialGauge 1 (readAtLevel (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth W)
          (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth z)) W := e.symm
    rw [e', curvature_gaugeTransform]
  have hcw := (mirrorCoord_bounds (ρA := ρA) hfit hch t n ρ hρ V (siteOfInt yi) hs hsσ hcold).2
  have hmain := curvature_le_add_four_bonds (torusChart ℓ.side (chartCoord ℓ V W) V)
    (torusChart ℓ.side (mirrorCoord ℓ ρA t n ρ V (siteOfInt yi)) (mirrorField ρ (siteOfInt yi) V)) x
    (siteOfInt (shiftedByBlock ℓ.side yi u₀)) μ ν
  have hc' := hcw (siteOfInt (shiftedByBlock ℓ.side yi u₀)) μ ν hlt
  have hnext : ∀ i : Fin 4, x + TorusFields.unitStep (n * ℓ.side) i = siteOfInt (u₀ + Pi.single i 1) := by
    intro i
    rw [siteOfInt_add, hx, unitStep_eq_siteOfInt]
  have hnext' : ∀ i : Fin 4, (siteOfInt (shiftedByBlock ℓ.side yi u₀) : TorusSite (4 * ρ * ℓ.side)) +
      TorusFields.unitStep (4 * ρ * ℓ.side) i = siteOfInt (shiftedByBlock ℓ.side yi (u₀ + Pi.single i 1)) := by
    intro i
    rw [shiftedByBlock_add, siteOfInt_add, unitStep_eq_siteOfInt]
  have hb0 := norm_chart_sub_mirror_le hfit hch t n m₀ ρ r hρ hr hρm hbig V W yi u₀ hs₁ hs₁σ hcold₁
    (hcoldy _ (by rw [hyi, blockShift_self]; intro l; simp)) (by rw [hyi, blockShift_self]; intro l; simp)
  have hb1 := fun i => norm_chart_sub_mirror_le hfit hch t n m₀ ρ r hρ hr hρm hbig V W yi (u₀ + Pi.single i 1)
    hs₁ hs₁σ hcold₁ (hcoldy _ (blockShift_unitStep_mem hLpos u₀ i)) (blockShift_unitStep_mem hLpos u₀ i)
  have t1 := hb0 μ hB (fun hb => hη _ (by rw [hx] at hb ⊢; exact hb) (Or.inl (by simp only; exact hx)))
  have t4 := hb0 ν hB (fun hb => hη _ hb (Or.inl (by simp only; exact hx)))
  have t2 := hb1 μ ν hB (fun hb => hη _ hb (Or.inr (Or.inl (by simp only; exact (hnext μ).symm))))
  have t3 := hb1 ν μ hB (fun hb => hη _ hb (Or.inr (Or.inr (by simp only; exact (hnext ν).symm))))
  rw [hx] at t1 t4
  rw [← hnext μ, ← hnext' μ] at t2
  rw [← hnext ν, ← hnext' ν] at t3
  rw [hA]
  linarith
private theorem norm_frameCoord_le {ℓ : TorusLumps.StepParameters} {δ lam ρA σA cg : ℝ} {N : ℕ → ℝ}
    (hfit : ℓ.Admissible) (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N) (t n m₀ ρ r : ℕ)
    [NeZero n] [NeZero (4 * ρ)] (hρ : 16 ≤ ρ) (hr : r + 2 = ρ) (hρm : ρ ≤ m₀) (hbig : 4 * m₀ + 5 < n)
    (V : TorusField n) (b : TorusBond (n * ℓ.side)) (hb : b ∈ StepCosts.chartBonds ℓ.side n) {s s₁ : ℝ}
    (hs : 0 < s) (hsσ : s ≤ σA) (hs₁ : 0 < s₁) (hs₁σ : s₁ ≤ σA)
    (hcold : IsColdNear V (parentBlock ℓ.side b.1) ρ s) (hcold₁ : IsColdNear V (parentBlock ℓ.side b.1) ρ s₁)
    (hcoldy : IsColdNear V (parentBlock ℓ.side b.1) m₀ s₁) :
    ‖(StepCosts.frameCoord ℓ ρA t m₀ V b : ℍ[ℝ])‖ ≤ N 0 * s + N 0 * s₁ * Real.exp (-(δ * (r : ℝ))) := by
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  have hodd := hfit.L_odd
  haveI hne0 : NeZero (n * ℓ.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  set u₀ : Fin 4 → ℤ := fun l => ((b.1 l).cast : ℤ) with hu₀
  set yi : Fin 4 → ℤ := fun l => (u₀ l + ((ℓ.side : ℤ) - 1) / 2) / (ℓ.side : ℤ) with hyi
  have hY : parentBlock ℓ.side b.1 = siteOfInt yi := rfl
  have hx : (siteOfInt u₀ : TorusSite (n * ℓ.side)) = b.1 := siteOfInt_castCoords b.1
  have hz : blockShift ℓ.side yi u₀ = 0 := blockShift_self u₀
  have e0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
    funext i
    simp [siteOfInt]
  rw [hY] at hcold hcold₁ hcoldy
  have hsz := (mirrorCoord_bounds (ρA := ρA) hfit hch t n ρ hρ V (siteOfInt yi) hs hsσ hcold).1
    (siteOfInt (shiftedByBlock ℓ.side yi u₀), b.2)
  have hfar := norm_frameCoord_sub_mirrorCoord_le hfit hch t n m₀ ρ r hρ hr hρm hbig V (siteOfInt yi) hs₁ hs₁σ 0
    (fun l => by simp) hcold₁ (by rw [e0, add_zero]; exact hcoldy) b hb (siteOfInt (shiftedByBlock ℓ.side yi u₀))
    (by rw [e0, add_zero]; exact hY)
    (by rw [parentBlock_shiftedByBlock yi u₀, hz])
    (fun l => by rw [← hx]; exact offsetFromCentre_shiftedByBlock hLpos hodd n (4 * ρ) yi u₀ l)
  have := norm_add_le ((StepCosts.frameCoord ℓ ρA t m₀ V b : ℍ[ℝ]) -
    mirrorCoord ℓ ρA t n ρ V (siteOfInt yi) (siteOfInt (shiftedByBlock ℓ.side yi u₀), b.2))
    (mirrorCoord ℓ ρA t n ρ V (siteOfInt yi) (siteOfInt (shiftedByBlock ℓ.side yi u₀), b.2) : ℍ[ℝ])
  rw [sub_add_cancel] at this
  linarith
private theorem le_finsetSupNonneg {α : Type} {S : Finset α} {f : α → ℝ} {a : α} (ha : a ∈ S) :
    f a ≤ finsetSupNonneg S f :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨a, ha, le_rfl⟩)
private theorem finsetSupNonneg_nonneg {α : Type} (S : Finset α) (f : α → ℝ) : 0 ≤ finsetSupNonneg S f :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)
private theorem finsetSupNonneg_le {α : Type} {S : Finset α} {f : α → ℝ} {c : ℝ} (h0 : 0 ≤ c)
    (h : ∀ a ∈ S, f a ≤ c) : finsetSupNonneg S f ≤ c :=
  (Finset.fold_max_le _).mpr ⟨h0, h⟩
private theorem finsetSupNonneg_lt {α : Type} {S : Finset α} {f : α → ℝ} {c : ℝ} (h0 : 0 < c)
    (h : ∀ a ∈ S, f a < c) : finsetSupNonneg S f < c :=
  (Finset.fold_max_lt _).mpr ⟨h0, h⟩
private theorem mem_supBall {n : ℕ} [NeZero n] {o z : TorusSite n} {R : ℝ} :
    z ∈ supBall o R ↔ (supDist z o : ℝ) ≤ R := by
  simp [supBall]
private theorem isColdNear_of_supBall {n : ℕ} [NeZero n] {V : TorusField n} {o : TorusSite n} {R s : ℝ}
    (hb : ∀ p ∈ plaquettesIn (supBall o R), curvature V p.1 p.2.1 p.2.2 < s) (Y : TorusSite n) (ρ : ℕ)
    (hin : ∀ a, OffsetInBox ρ a → Y + siteOfInt a ∈ supBall o R) : IsColdNear V Y ρ s := by
  classical
  intro a μ ν hlt hd
  refine hb (Y + siteOfInt a, μ, ν) ?_
  unfold plaquettesIn
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, fun z hz => ?_⟩
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · have := hin _ (hd 0 (by simp [plaquetteOffsets]))
    simpa using this
  · have := hin _ (hd (Pi.single μ 1) (by simp [plaquetteOffsets]))
    rwa [siteOfInt_add, ← add_assoc, ← unitStep_eq_siteOfInt] at this
  · have := hin _ (hd (Pi.single ν 1) (by simp [plaquetteOffsets]))
    rwa [siteOfInt_add, ← add_assoc, ← unitStep_eq_siteOfInt] at this
  · have := hin _ (hd (Pi.single μ 1 + Pi.single ν 1) (by simp [plaquetteOffsets]))
    rwa [siteOfInt_add, siteOfInt_add, ← add_assoc, ← add_assoc, ← unitStep_eq_siteOfInt,
      ← unitStep_eq_siteOfInt] at this
abbrev _root_.YangMills.DeltaSharedProofs.p502503 := @isColdNear_of_supBall
private theorem add_siteOfInt_mem_supBall {n : ℕ} [NeZero n] {o Y : TorusSite n} {D R : ℝ} {ρ : ℕ}
    (hY : (supDist Y o : ℝ) ≤ D) (hDR : D + ρ ≤ R) (a : Fin 4 → ℤ) (ha : OffsetInBox ρ a) :
    Y + siteOfInt a ∈ supBall o R := by
  have h1 : supDist Y (Y + siteOfInt a) ≤ ρ := supDist_add_siteOfInt_le Y a ρ fun i => by
    have := abs_le.mp (ha i)
    omega
  have h2 := supDist_triangle (Y + siteOfInt a) Y o
  rw [supDist_comm (Y + siteOfInt a) Y] at h2
  have h3 : (supDist (Y + siteOfInt a) o : ℝ) ≤ (supDist Y (Y + siteOfInt a) : ℝ) + supDist Y o := by
    exact_mod_cast h2
  have h4 : (supDist Y (Y + siteOfInt a) : ℝ) ≤ ρ := by exact_mod_cast h1
  rw [mem_supBall]
  linarith
abbrev _root_.YangMills.SharedProofs.p100246 := @add_siteOfInt_mem_supBall
private theorem supDist_parentBlock_le {n L : ℕ} [NeZero n] [NeZero L] {x o' : TorusSite (n * L)} {R : ℝ}
    (h : (supDist x o' : ℝ) ≤ R) : (supDist (parentBlock L x) (parentBlock L o') : ℝ) ≤ R / L + 1 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h0 := TorusBalls.supDist_parentBlock_le_div_add_one L x o'
  have h1 : ((supDist x o' / L : ℕ) : ℝ) ≤ (supDist x o' : ℝ) / L := Nat.cast_div_le
  have h2 : (supDist x o' : ℝ) / L ≤ R / L := div_le_div_of_nonneg_right h hL.le
  have h3 : (supDist (parentBlock L x) (parentBlock L o') : ℝ) ≤ ((supDist x o' / L : ℕ) : ℝ) + 1 := by
    exact_mod_cast h0
  linarith
private theorem pow_le_pow_of_one_le {u : ℝ} (hu : 1 ≤ u) {a b : ℕ} (h : a ≤ b) : u ^ a ≤ u ^ b :=
  pow_le_pow_right₀ hu h
private theorem scale_bounds_of {B K U u x x' : ℝ} (hB : 0 < B) (hK : K = 1800)
    (hU : U = 8 * B * K ^ 2 + 2 ^ 14 * K ^ 3 + 100) (hxpos : 0 < x) (hu : u = x ^ ((1 : ℝ) / 1800))
    (hUu : U ≤ u) (hx' : |x' - x| ≤ 4 * B * Real.log x ^ 2) :
    16 ≤ ⌊Real.log x ^ 3⌋₊ ∧ ⌊Real.log x ^ 3⌋₊ ≤ clusterRange x' / 2 ^ 11 ∧
      ((clusterRange x' / 2 ^ 11 : ℕ) : ℝ) + 4 * (⌊Real.log x ^ 3⌋₊ : ℝ) + 20 * x ^ ((1 : ℝ) / 90) + 4 ≤
        (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := by
  have hKpos : 0 < K := by rw [hK]; norm_num
  have hUpos : 100 ≤ U := by
    rw [hU]
    have : 0 ≤ 8 * B * K ^ 2 := by positivity
    have : 0 ≤ (2 : ℝ) ^ 14 * K ^ 3 := by positivity
    linarith
  have hupos : 0 < u := by rw [hu]; exact Real.rpow_pos_of_pos hxpos _
  have hu100 : 100 ≤ u := hUpos.trans hUu
  have hu1 : 1 ≤ u := by linarith
  have hpow : ∀ (p : ℕ) (q : ℝ), q = (p : ℝ) / 1800 → x ^ q = u ^ p := by
    intro p q hq
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le, hq]
    congr 1
    ring
  have hx1800 : x = u ^ 1800 := by
    have := hpow 1800 1 (by norm_num)
    rwa [Real.rpow_one] at this
  have hlog : Real.log x ≤ K * u := by
    have h1 : Real.log x = 1800 * Real.log u := by
      rw [hx1800, Real.log_pow]
      norm_num
    have h2 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
    rw [h1, hK]
    linarith
  have hx3 : u ^ 3 ≤ x := by
    rw [hx1800]
    exact pow_le_pow_of_one_le hu1 (by norm_num)
  clear hx1800
  have hx27 : (27 : ℝ) ≤ x := by
    have : u ^ 1 ≤ u ^ 3 := pow_le_pow_of_one_le hu1 (by norm_num)
    linarith
  have hlog3 : 3 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
    rw [h1]
    linarith
  have hlogpos : 0 ≤ Real.log x := by linarith
  have hρ3 : Real.log x ^ 3 ≤ K ^ 3 * u ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlogpos hlog 3
  have hρ2 : Real.log x ^ 2 ≤ K ^ 2 * u ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlogpos hlog 2
  have hfloor3 : (⌊Real.log x ^ 3⌋₊ : ℝ) ≤ K ^ 3 * u ^ 3 :=
    (Nat.floor_le (by positivity)).trans hρ3
  have hmove : 4 * B * Real.log x ^ 2 ≤ x / 2 := by
    have h1 : 8 * B * K ^ 2 ≤ u := by
      have : 0 ≤ (2 : ℝ) ^ 14 * K ^ 3 := by positivity
      rw [hU] at hUu
      linarith
    have h2 : u ^ 3 ≤ x := hx3
    have h3 : 8 * B * K ^ 2 * u ^ 2 ≤ u * u ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4 : 4 * B * Real.log x ^ 2 ≤ 4 * B * (K ^ 2 * u ^ 2) := mul_le_mul_of_nonneg_left hρ2 (by positivity)
    have e : u * u ^ 2 = u ^ 3 := by ring
    nlinarith
  obtain ⟨hl, hh⟩ := abs_le.mp (hx'.trans hmove)
  have hx'lo : x / 2 ≤ x' := by linarith
  have hx'hi : x' ≤ 2 * x := by linarith
  have hx'pos : 0 < x' := by linarith
  have hu18 : x ^ ((1 : ℝ) / 100) = u ^ 18 := hpow 18 _ (by norm_num)
  have hlo : u ^ 18 / 2 ≤ x' ^ ((1 : ℝ) / 100) := by
    have h1 : (x / 2) ^ ((1 : ℝ) / 100) ≤ x' ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity) hx'lo (by norm_num)
    have h2 : (x / 2) ^ ((1 : ℝ) / 100) = x ^ ((1 : ℝ) / 100) / 2 ^ ((1 : ℝ) / 100) :=
      Real.div_rpow hxpos.le (by norm_num) _
    have h3 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (show (1 : ℝ) / 100 ≤ 1 by norm_num)
      simpa using this
    have h4 : (0 : ℝ) < 2 ^ ((1 : ℝ) / 100) := by positivity
    have h5 : u ^ 18 / 2 ≤ u ^ 18 / 2 ^ ((1 : ℝ) / 100) :=
      div_le_div_of_nonneg_left (by positivity) h4 h3
    rw [h2, hu18] at h1
    linarith
  have hhi : x' ^ ((1 : ℝ) / 100) ≤ 2 * u ^ 18 := by
    have h1 : x' ^ ((1 : ℝ) / 100) ≤ (2 * x) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow hx'pos.le hx'hi (by norm_num)
    have h2 : (2 * x) ^ ((1 : ℝ) / 100) = 2 ^ ((1 : ℝ) / 100) * x ^ ((1 : ℝ) / 100) :=
      Real.mul_rpow (by norm_num) hxpos.le
    have h3 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (show (1 : ℝ) / 100 ≤ 1 by norm_num)
      simpa using this
    rw [h2, hu18] at h1
    have : (2 : ℝ) ^ ((1 : ℝ) / 100) * u ^ 18 ≤ 2 * u ^ 18 := mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith
  have hrange_lo : x' ^ ((1 : ℝ) / 100) ≤ (clusterRange x' : ℝ) := Nat.le_ceil _
  have hrange_hi : (clusterRange x' : ℝ) ≤ 2 * u ^ 18 + 1 := by
    have := (Nat.ceil_lt_add_one (Real.rpow_nonneg hx'pos.le ((1 : ℝ) / 100))).le
    have e : (clusterRange x' : ℝ) = (⌈x' ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := rfl
    rw [e]
    linarith
  have hK3 : 2 ^ 14 * K ^ 3 ≤ u := by
    have : 0 ≤ 8 * B * K ^ 2 := by positivity
    rw [hU] at hUu
    linarith
  have hu4 : 2 ^ 14 * K ^ 3 * u ^ 3 ≤ u ^ 4 := by
    have := mul_le_mul_of_nonneg_right hK3 (show 0 ≤ u ^ 3 by positivity)
    have e : u * u ^ 3 = u ^ 4 := by ring
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine Nat.le_floor ?_
    have : (3 : ℝ) ^ 3 ≤ Real.log x ^ 3 := pow_le_pow_left₀ (by norm_num) hlog3 3
    norm_num at this ⊢
    linarith
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    have h1 : ((⌊Real.log x ^ 3⌋₊ * 2 ^ 11 : ℕ) : ℝ) ≤ (clusterRange x' : ℝ) := by
      push_cast
      have h2 : (⌊Real.log x ^ 3⌋₊ : ℝ) * 2 ^ 11 ≤ K ^ 3 * u ^ 3 * 2 ^ 11 :=
        mul_le_mul_of_nonneg_right hfloor3 (by positivity)
      have h3 : u ^ 4 ≤ u ^ 18 := pow_le_pow_of_one_le hu1 (by norm_num)
      nlinarith
    exact_mod_cast h1
  · have hm : ((clusterRange x' / 2 ^ 11 : ℕ) : ℝ) ≤ (clusterRange x' : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    have hu90 : x ^ ((1 : ℝ) / 90) = u ^ 20 := hpow 20 _ (by norm_num)
    have hu20 : x ^ ((1 : ℝ) / 20) = u ^ 90 := hpow 90 _ (by norm_num)
    have hfl : u ^ 90 - 1 ≤ (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := by
      have := (Nat.lt_floor_add_one (x ^ ((1 : ℝ) / 20))).le
      rw [hu20] at this ⊢
      linarith
    have h21 : u ^ 21 ≤ u ^ 90 := pow_le_pow_of_one_le hu1 (by norm_num)
    have a1 : 20 * u ^ 20 ≤ u ^ 21 / 4 := by
      have : 80 * u ^ 20 ≤ u * u ^ 20 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have e : u * u ^ 20 = u ^ 21 := by ring
      linarith
    have a2 : 2 * u ^ 18 ≤ u ^ 21 / 8 := by
      have h3 : (100 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu100 3
      have e : u ^ 3 * u ^ 18 = u ^ 21 := by ring
      have : (100 : ℝ) ^ 3 * u ^ 18 ≤ u ^ 3 * u ^ 18 := mul_le_mul_of_nonneg_right h3 (by positivity)
      have : 0 ≤ u ^ 18 := by positivity
      norm_num at *
      linarith
    have a3 : 4 * (K ^ 3 * u ^ 3) ≤ u ^ 21 / 8 := by
      have h4 : u ^ 4 ≤ u ^ 21 := pow_le_pow_of_one_le hu1 (by norm_num)
      have : 0 ≤ K ^ 3 * u ^ 3 := by positivity
      nlinarith
    have a4 : (8 : ℝ) ≤ u ^ 21 / 4 := by
      have : u ^ 1 ≤ u ^ 21 := pow_le_pow_of_one_le hu1 (by norm_num)
      linarith
    rw [hu90]
    linarith
private theorem eventually_scale_bounds (B : ℝ) (hB : 0 < B) : ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ x' : ℝ,
    |x' - x| ≤ 4 * B * Real.log x ^ 2 →
    16 ≤ ⌊Real.log x ^ 3⌋₊ ∧ ⌊Real.log x ^ 3⌋₊ ≤ clusterRange x' / 2 ^ 11 ∧
      ((clusterRange x' / 2 ^ 11 : ℕ) : ℝ) + 4 * (⌊Real.log x ^ 3⌋₊ : ℝ) + 20 * x ^ ((1 : ℝ) / 90) + 4 ≤
        (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := by
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 8 * B * (1800 : ℝ) ^ 2 + 2 ^ 14 * (1800 : ℝ) ^ 3 + 100 := ⟨_, rfl⟩
  have hU1 : 1 ≤ U := by
    rw [hU]
    have : 0 ≤ 8 * B * (1800 : ℝ) ^ 2 := by positivity
    norm_num at this ⊢
    linarith
  refine ⟨U ^ 1800, one_le_pow₀ hU1, fun x hx x' hx' => ?_⟩
  have hU0 : 0 < U := lt_of_lt_of_le one_pos hU1
  have hxpos : 0 < x := lt_of_lt_of_le (pow_pos hU0 _) hx
  have hUu : U ≤ x ^ ((1 : ℝ) / 1800) := by
    have h1 : (U ^ 1800 : ℝ) ^ ((1 : ℝ) / 1800) = U := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
      norm_num
    calc U = (U ^ 1800 : ℝ) ^ ((1 : ℝ) / 1800) := h1.symm
      _ ≤ x ^ ((1 : ℝ) / 1800) := Real.rpow_le_rpow (pow_pos hU0 _).le hx (by norm_num)
  exact scale_bounds_of hB rfl hU hxpos rfl hUu hx'
private theorem plaquettesIn_supBall_mono {n : ℕ} [NeZero n] {o : TorusSite n} {R R' : ℝ} (h : R ≤ R') :
    plaquettesIn (supBall o R) ⊆ plaquettesIn (supBall o R') := by
  classical
  intro p hp
  unfold plaquettesIn at hp ⊢
  obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, fun z hz =>
    mem_supBall.mpr ((mem_supBall.mp (h2 z hz)).trans h)⟩
abbrev _root_.YangMills.SharedProofs.p58549 := @plaquettesIn_supBall_mono
end CurvatureHalves
open CurvatureHalves in
theorem curvatureHalves_of_flowWhereExpansionReturns (hrun : ClusterExpansionOfAStep.FlowWhereExpansionReturns) :
    curvatureHalvesStatement := by
  intro a _
  obtain ⟨C₀, hC₀⟩ := hrun
  refine ⟨0, fun _ => 1, C₀, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hD _ _ _ hCder
  refine ⟨T.floorMin, fun y hy hret _ => ?_⟩
  have hfit : (T.stepParameters y).Admissible := hD.fits y hy
  have hch : ColdChainConstants (T.stepParameters y).coupling T.δ₁ (T.stepParameters y).side T.lam T.ρA T.σA
      T.cg T.N := hD.chain
  have hrun' := (hC₀ (T.stepParameters y) hfit hCder hret).2
  have hσ : 0 < (T.stepParameters y).threshold := hfit.σ_pos
  have hσA : (T.stepParameters y).threshold ≤ T.σA := by
    have h1 := hD.σ_le
    have h2 : (T.stepParameters y).threshold = T.threshold := rfl
    rw [h2] at hσ ⊢
    linarith
  have hδ := hD.δ₁_pos
  have hN : 0 < T.N 0 := hch.2.2.2.2.2.2.2.1 0
  obtain ⟨x₀, hx₀1, hfl⟩ := eventually_scale_bounds (T.stepParameters y).B hfit.B_pos
  refine ⟨1 + T.N 0 + 4 * (T.N 0 * (T.stepParameters y).threshold * Real.exp (2 * T.δ₁)), 2 * T.N 0, T.δ₁, x₀,
    hδ, ?_⟩
  intro Tw β k n _ nn j o V hloc hj hcoldbox
  have hβ : (T.stepParameters y).y₁ ≤ β := hloc.coupling_ge 0 (Nat.zero_le _)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (couplingFlow (T.stepParameters y) β k).1 := ⟨_, rfl⟩
  have hBpos := hfit.B_pos
  have hrunb : ∀ i, i ≤ 2 * WeightedResponses.chainDepth x →
      |(couplingFlow (T.stepParameters y) β (k + i)).1 - x| ≤ 2 * (T.stepParameters y).B * i := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [hx]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 : |(couplingFlow (T.stepParameters y) β (k + i + 1)).1 -
          (couplingFlow (T.stepParameters y) β (k + i)).1| ≤ 2 * (T.stepParameters y).B :=
        ((hrun' β hβ).1 (k + i)).2 (fun l hl => hloc.coupling_ge l (by rw [← hx]; omega))
      have h3 := abs_sub_le (couplingFlow (T.stepParameters y) β (k + i + 1)).1
        (couplingFlow (T.stepParameters y) β (k + i)).1 x
      have e : k + (i + 1) = k + i + 1 := rfl
      rw [e]
      push_cast
      linarith
  have hj' : j < 2 * WeightedResponses.chainDepth x := by
    rw [hx]
    exact hj
  have hxt : |(couplingFlow (T.stepParameters y) β (k + j)).1 - x| ≤
      4 * (T.stepParameters y).B * Real.log x ^ 2 := by
    have h1 := hrunb j hj'.le
    have h2 : (WeightedResponses.chainDepth x : ℝ) ≤ Real.log x ^ 2 := Nat.floor_le (sq_nonneg _)
    have h3 : (j : ℝ) ≤ 2 * (WeightedResponses.chainDepth x : ℝ) := by exact_mod_cast hj'.le
    have h4 : 2 * (T.stepParameters y).B * (j : ℝ) ≤ 2 * (T.stepParameters y).B * (2 * Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hxfloor : x₀ ≤ x := by
    rw [hx]
    exact hloc.floor_le
  obtain ⟨hρ16, hρm', hsum⟩ := hfl x hxfloor _ hxt
  have hlev : (Tw.stage (k + j)).coupling = (couplingFlow (T.stepParameters y) β (k + j)).1 :=
    hloc.onFamily.coupling_eq _ (by rw [← hx]; omega)
  have htab := hloc.onFamily.onFamily (k + j) (by rw [← hx]; omega)
  have hρA : (Tw.stage (k + j)).anchorRadius = T.ρA := htab.anchorRadius_eq
  have hm₀ : (Tw.stage (k + j)).toStepSetup.frameReach =
      clusterRange (couplingFlow (T.stepParameters y) β (k + j)).1 / 2 ^ 11 :=
    congrArg (· / 2 ^ 11) (congrArg clusterRange hlev)
  have hscale : localLogScale (T.stepParameters y) β k = (⌊Real.log x ^ 3⌋₊ : ℝ) := by
    rw [hx]
    rfl
  have hside : localBlockSide (T.stepParameters y) β k = ⌊x ^ ((1 : ℝ) / 20)⌋₊ := by
    rw [hx]
    rfl
  have hn₁ : 2 ^ 10 * (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) ≤ (n : ℝ) := by
    have := hloc.side_ge
    rw [← hx] at this
    exact this
  have hnn : nn ≤ x ^ ((1 : ℝ) / 90) := by
    have := hloc.le_rpow
    rw [← hx] at this
    exact this
  have hnn1 : 1 ≤ nn := hloc.one_le
  rw [hscale]
  rw [hside] at hcoldbox
  rw [hρA]
  generalize hm₀' : (Tw.stage (k + j)).toStepSetup.frameReach = m₀ at *
  rw [← hm₀] at hρm' hsum
  generalize hρ' : ⌊Real.log x ^ 3⌋₊ = ρ at *
  generalize hm' : ⌊x ^ ((1 : ℝ) / 20)⌋₊ = m at *
  obtain ⟨r, hr⟩ : ∃ r, r + 2 = ρ := ⟨ρ - 2, by omega⟩
  haveI : NeZero (4 * ρ) := ⟨by omega⟩
  have hρ0 : (0 : ℝ) ≤ ρ := by positivity
  have hρ1 : (16 : ℝ) ≤ ρ := by exact_mod_cast hρ16
  have hxpos : 0 < x := by linarith
  have hLgt : (2 : ℝ) ≤ (T.stepParameters y).side := by
    have := hfit.L_ge
    have h2 : 2 ≤ (T.stepParameters y).side := by omega
    exact_mod_cast h2
  have hLpos : (0 : ℝ) < (T.stepParameters y).side := by linarith
  have h90 : 0 ≤ x ^ ((1 : ℝ) / 90) := by positivity
  have hm₀0 : (0 : ℝ) ≤ m₀ := by positivity
  have hρm : ρ ≤ m₀ := hρm'
  have hρmr : (ρ : ℝ) ≤ m₀ := by exact_mod_cast hρm
  have hbig : 4 * m₀ + 5 < n := by
    have h1 : (m₀ : ℝ) + 4 ≤ m := by linarith
    have h1' : m₀ + 4 ≤ m := by exact_mod_cast h1
    have h2 : 2 ^ 10 * m ≤ n := by exact_mod_cast hn₁
    omega
  have hRle : ∀ i, ballRadius (T.stepParameters y).side nn (ρ : ℝ) i ≤ 20 * nn + 4 * ρ := by
    intro i
    unfold ballRadius
    have h1 : (1 : ℝ) ≤ ((T.stepParameters y).side : ℝ) ^ i := one_le_pow₀ (by linarith)
    have h2 : 20 * nn / ((T.stepParameters y).side : ℝ) ^ i ≤ 20 * nn := div_le_self (by linarith) h1
    linarith
  have hR0 : ∀ i, 0 ≤ ballRadius (T.stepParameters y).side nn (ρ : ℝ) i := by
    intro i
    unfold ballRadius
    have : 0 ≤ 20 * nn / ((T.stepParameters y).side : ℝ) ^ i := by
      have : 0 ≤ nn := by linarith
      positivity
    linarith
  have hbigc : ∀ {Y : TorusSite n} {D : ℝ} {q : ℕ}, (supDist Y o : ℝ) ≤ D → D + q ≤ m →
      IsColdNear V Y q (T.stepParameters y).threshold :=
    fun hY hDq => isColdNear_of_supBall hcoldbox _ _ (add_siteOfInt_mem_supBall hY hDq)
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-(T.δ₁ * (ρ : ℝ))) := ⟨_, rfl⟩
  have hEpos : 0 < E := by
    rw [hE]
    exact Real.exp_pos _
  rw [← hE]
  have hexp : Real.exp (-(T.δ₁ * (r : ℝ))) = Real.exp (2 * T.δ₁) * E := by
    rw [hE, ← Real.exp_add]
    congr 1
    have h1 : (ρ : ℝ) = r + 2 := by exact_mod_cast hr.symm
    rw [h1]
    ring
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = T.N 0 * (T.stepParameters y).threshold * Real.exp (2 * T.δ₁) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  rw [← hA]
  have hgap : T.N 0 * (T.stepParameters y).threshold * Real.exp (-(T.δ₁ * (r : ℝ))) = A * E := by
    rw [hexp, hA]
    ring
  have hAE : 0 ≤ A * E := by positivity
  have hNE : 0 ≤ T.N 0 * E := by positivity
  have hpick : ∀ cu : ℝ, 0 ≤ cu → cu < (T.stepParameters y).threshold →
      0 < min (T.stepParameters y).threshold (2 * cu + E) ∧ cu < min (T.stepParameters y).threshold (2 * cu + E) ∧
        min (T.stepParameters y).threshold (2 * cu + E) ≤ T.σA ∧
        min (T.stepParameters y).threshold (2 * cu + E) ≤ 2 * cu + E := by
    intro cu h0 h1
    refine ⟨lt_min hσ (by linarith), lt_min h1 (by linarith), (min_le_left _ _).trans hσA, min_le_right _ _⟩
  refine ⟨fun b hb hbox => ?_, fun W o' ho' _ e he0 he1 => ?_⟩
  · set R₁ := ballRadius (T.stepParameters y).side nn (ρ : ℝ) (j + 1) with hR₁
    have hYR : (supDist (parentBlock (T.stepParameters y).side b.1) o : ℝ) ≤ R₁ := by
      refine mem_supBall.mp (hbox (mem_supBall.mpr ?_))
      rw [supDist_self]
      simpa using hρ0
    have hsub : R₁ + m₀ ≤ m := by
      have := hRle (j + 1)
      linarith
    have hsubρ : R₁ + ρ ≤ m := by linarith
    have hcu0 : 0 ≤ maxCurvatureOnBall V o R₁ := finsetSupNonneg_nonneg _ _
    have hcuσ : maxCurvatureOnBall V o R₁ < (T.stepParameters y).threshold :=
      finsetSupNonneg_lt hσ fun p hp => hcoldbox p (plaquettesIn_supBall_mono (by linarith [hR0 (j + 1)]) hp)
    obtain ⟨hs, hcus, hsσ, hs2⟩ := hpick _ hcu0 hcuσ
    have hcold : IsColdNear V (parentBlock (T.stepParameters y).side b.1) ρ
        (min (T.stepParameters y).threshold (2 * maxCurvatureOnBall V o R₁ + E)) := by
      refine isColdNear_of_supBall (R := R₁) (o := o)
        (fun p hp => lt_of_le_of_lt
          (le_finsetSupNonneg (f := fun p : TorusPlaquette n => curvature V p.1 p.2.1 p.2.2) hp) hcus) _ _ ?_
      intro v hv
      refine hbox ?_
      exact add_siteOfInt_mem_supBall (D := 0) (by rw [supDist_self]; simp) (by simp) v hv
    have hf := norm_frameCoord_le (ρA := T.ρA) hfit hch (k + j) n m₀ ρ r hρ16 hr hρm hbig V b hb hs hsσ hσ hσA
      hcold (hbigc hYR hsubρ) (hbigc hYR hsub)
    rw [hgap] at hf
    have h1 := mul_le_mul_of_nonneg_left hs2 hN.le
    have e1 : 2 * T.N 0 * maxCurvatureOnBall V o R₁ + (1 + T.N 0 + 4 * A) * E =
        T.N 0 * (2 * maxCurvatureOnBall V o R₁ + E) + A * E + (E + 3 * (A * E)) := by ring
    rw [e1]
    linarith
  · set R := ballRadius (T.stepParameters y).side nn (ρ : ℝ) j + e with hR
    set R' := ballRadius (T.stepParameters y).side nn (ρ : ℝ) (j + 1) + e with hR'
    have hRRle : R / (T.stepParameters y).side + 1 + ρ ≤ R' := by
      have e1 : R / (T.stepParameters y).side = 20 * nn / ((T.stepParameters y).side : ℝ) ^ (j + 1) +
          (4 * ρ + e) / (T.stepParameters y).side := by
        rw [hR]
        unfold ballRadius
        rw [pow_succ]
        field_simp
        ring
      have e2 : (4 * (ρ : ℝ) + e) / (T.stepParameters y).side ≤ (4 * ρ + e) / 2 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) hLgt
      rw [e1, hR']
      unfold ballRadius
      linarith
    have hRLle : R / (T.stepParameters y).side ≤ R := by
      have hRpos : 0 ≤ R := by
        rw [hR]
        linarith [hR0 j]
      exact div_le_self hRpos (by linarith)
    have hRm : R / (T.stepParameters y).side + 2 + m₀ ≤ m := by
      have := hRle j
      rw [hR] at hRLle
      rw [hR]
      linarith
    have hRm' : R' ≤ m := by
      have := hRle (j + 1)
      rw [hR']
      linarith
    have hcu0 : 0 ≤ maxCurvatureOnBall V o R' := finsetSupNonneg_nonneg _ _
    have hcuσ : maxCurvatureOnBall V o R' < (T.stepParameters y).threshold :=
      finsetSupNonneg_lt hσ fun p hp => hcoldbox p (plaquettesIn_supBall_mono hRm' hp)
    obtain ⟨hs, hcus, hsσ, hs2⟩ := hpick _ hcu0 hcuσ
    have hmx0 : 0 ≤ maxDeviationOnBall Tw (k + j) V W o (R / (T.stepParameters y).side + 2) :=
      finsetSupNonneg_nonneg _ _
    refine finsetSupNonneg_le (by positivity) fun p hp => ?_
    obtain ⟨xp, μ, ν⟩ := p
    have hp' := hp
    unfold plaquettesIn at hp'
    obtain ⟨_, hlt, hcorn⟩ := Finset.mem_filter.mp hp'
    simp only at hlt hcorn ⊢
    have hxc : ∀ z ∈ plaquetteVertices xp μ ν,
        (supDist (parentBlock (T.stepParameters y).side z) o : ℝ) ≤ R / (T.stepParameters y).side + 1 := by
      intro z hz
      have := supDist_parentBlock_le (mem_supBall.mp (hcorn z hz))
      rwa [ho'] at this
    have hx0 := hxc xp (by simp [plaquetteVertices])
    have hcold : IsColdNear V (parentBlock (T.stepParameters y).side xp) ρ
        (min (T.stepParameters y).threshold (2 * maxCurvatureOnBall V o R' + E)) :=
      isColdNear_of_supBall (R := R') (o := o)
        (fun p hp => lt_of_le_of_lt
          (le_finsetSupNonneg (f := fun p : TorusPlaquette n => curvature V p.1 p.2.1 p.2.2) hp) hcus) _ _
        (add_siteOfInt_mem_supBall hx0 hRRle)
    have hcold₁ : IsColdNear V (parentBlock (T.stepParameters y).side xp) ρ (T.stepParameters y).threshold :=
      hbigc hx0 (by linarith)
    have hcoldy : ∀ e', WithinRadius 1 e' →
        IsColdNear V (parentBlock (T.stepParameters y).side xp + siteOfInt e') m₀ (T.stepParameters y).threshold := by
      intro e' he'
      refine hbigc (D := R / (T.stepParameters y).side + 2) ?_ hRm
      have h1 : supDist (parentBlock (T.stepParameters y).side xp)
          (parentBlock (T.stepParameters y).side xp + siteOfInt e') ≤ 1 :=
        supDist_add_siteOfInt_le _ e' 1 fun i => by
          have := abs_le.mp (he' i)
          push_cast at this
          omega
      have h2 := supDist_triangle (parentBlock (T.stepParameters y).side xp + siteOfInt e')
        (parentBlock (T.stepParameters y).side xp) o
      rw [supDist_comm (parentBlock (T.stepParameters y).side xp + siteOfInt e')
        (parentBlock (T.stepParameters y).side xp)] at h2
      have h3 : (supDist (parentBlock (T.stepParameters y).side xp + siteOfInt e') o : ℝ) ≤
          (supDist (parentBlock (T.stepParameters y).side xp)
            (parentBlock (T.stepParameters y).side xp + siteOfInt e') : ℝ) +
            supDist (parentBlock (T.stepParameters y).side xp) o := by exact_mod_cast h2
      have h4 : (supDist (parentBlock (T.stepParameters y).side xp)
          (parentBlock (T.stepParameters y).side xp + siteOfInt e') : ℝ) ≤ 1 := by
        exact_mod_cast h1
      linarith
    have hη : ∀ b ∈ StepCosts.chartBonds (T.stepParameters y).side n,
        (b.1 = xp ∨ b.1 = xp + TorusFields.unitStep (n * (T.stepParameters y).side) μ ∨
          b.1 = xp + TorusFields.unitStep (n * (T.stepParameters y).side) ν) →
        ‖(frameDeviation (T.stepParameters y) T.ρA (k + j) m₀ V W b : ℍ[ℝ])‖ ≤
          maxDeviationOnBall Tw (k + j) V W o (R / (T.stepParameters y).side + 2) := by
      intro b hb hz
      have hmem : b.1 ∈ plaquetteVertices xp μ ν := by
        rcases hz with h | h | h <;> rw [h] <;> simp [plaquetteVertices]
      have hin : b ∈ MarkedIntegrals.chartBondsInBlocks (T.stepParameters y).side
          (supBall o (R / (T.stepParameters y).side + 2)) := by
        classical
        refine Finset.mem_filter.mpr ⟨hb, mem_supBall.mpr ?_⟩
        have := hxc _ hmem
        linarith
      have key := le_finsetSupNonneg (f := fun b => ‖(stepDeviation Tw (k + j) V W b : ℍ[ℝ])‖) hin
      have e1 : ‖(stepDeviation Tw (k + j) V W b : ℍ[ℝ])‖ =
          ‖(frameDeviation (T.stepParameters y) T.ρA (k + j) m₀ V W b : ℍ[ℝ])‖ := by
        unfold stepDeviation
        rw [hρA, hm₀']
      rw [← e1]
      exact key
    have hpb := curvature_chart_le (ρA := T.ρA) hfit hch (k + j) n m₀ ρ r hρ16 hr hρm hbig V W xp μ ν hlt hs hsσ
      hσ hσA hcold hcold₁ hcoldy hmx0 hη
    rw [hgap] at hpb
    linarith
end YangMills.Construction.ResponseInTheExpansion
end
