import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ContourMeanInTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.ContourOfAChartField
import YangMills.Construction.ColdStepAtMirrorFrames.EmbeddedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOne
import YangMills.Construction.ColdStepAtMirrorFrames.GapsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.GlueOfTwoCharts
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.PairedVariablesOfTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfTheChartOnTwoToriProof
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenStayNear
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames.GapPartComparison
open BlockAverages Interpolation
variable {F F' : BlockFrame}
private abbrev LatticeOffset : Type := Fin 4 → ℤ
private def siteAtOffset (Y : F.Cell) (p : LatticeOffset) : F.Site F.depth :=
  cellCentre F.depth Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth p
private def NearBox (L r : ℕ) (p : LatticeOffset) : Prop :=
  ∀ i, |p i| ≤ (L : ℤ) * r + BlockOffsets.halfSide L
private theorem siteAtOffset_decomp (Y : F.Cell) (g q : LatticeOffset) :
    siteAtOffset Y (fun i => (F.blockSide : ℤ) * g i + q i) =
      cellCentre F.depth (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth q := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.siteAtOffset_blockSplit <;> assumption
private theorem fineBondAt_mem_chordBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (g q : LatticeOffset) (j : Fin 4) (ht : ¬ IsAxialTreeBond (fineBondAt Y g q j)) :
    fineBondAt Y g q j ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.fineBondAt_mem_chordBonds <;> assumption
private theorem chartedField_agree {L r : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius r b → V (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top b.1) b.2 = V' (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y g q j).1 j = w' (fineBondAt Y' g q j).1 j)
    (p : LatticeOffset) (j : Fin 4) (hp : NearBox L r p) (hp' : NearBox L r (p + Pi.single j 1)) :
    chartedField w V (siteAtOffset Y p) j = chartedField w' V' (siteAtOffset Y' p) j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.chartedField_eq <;> assumption
private theorem refineSite_eq (Y : F.Cell) : _root_.YangMills.Construction.BlockAverages.refineSite Y = cellCentre F.depth Y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
private theorem refineSite_eq_siteAtOffset (Y : F.Cell) (g : LatticeOffset) :
    _root_.YangMills.Construction.BlockAverages.refineSite (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) =
      siteAtOffset Y ((0 : LatticeOffset) + fun i => (F.blockSide : ℤ) * g i) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.refineSite_add_eq_siteAtOffset <;> assumption
private theorem contourAverage_agree {L : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    {Y : F.Cell} {Y' : F'.Cell} {X : F.GaugeField F.depth} {X' : F'.GaugeField F'.depth}
    (g : LatticeOffset) (d : Fin 4)
    (h : ∀ v k, (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      (v + LatticeFractionalIntegration.basisVector k - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      X (siteAtOffset Y v) k = X' (siteAtOffset Y' v) k) :
    _root_.YangMills.Construction.BlockAverages.contourAverage X ((Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
      _root_.YangMills.Construction.BlockAverages.contourAverage X' ((Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.contourAverage_eq_of_agree <;> assumption
private theorem nearBox_of_twoBlockHull {L r : ℕ} (hL : Odd L) {g v : LatticeOffset} {d : Fin 4}
    (hg : WithinRadius r g) (hg' : WithinRadius r (g + Pi.single d 1))
    (hv : (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d) : NearBox L r v := by exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.nearBox_of_mem_twoBlockHull hL hg hg' hv
private theorem contourAverage_eq_of_far (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {X X' : F.GaugeField F.depth} (c : F.Site (F.depth + 1) × Fin 4) (x : F.Site F.depth)
    (hag : ∀ y k, y ≠ x → X y k = X' y k) (h1 : enclosingCell x ≠ c.1)
    (h2 : enclosingCell x ≠ c.1 + unitStep F.top c.2) : _root_.YangMills.Construction.BlockAverages.contourAverage X c = _root_.YangMills.Construction.BlockAverages.contourAverage X' c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopeOnTwoTori.contourAverage_eq_of_ne <;> assumption
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
private structure TwiceBounded (C₁ C₂ : ℝ) (Ψ : P → ℝ) (p : P) : Prop where
  smooth : ContDiffAt ℝ 3 Ψ p
  first : ∀ u, |fderiv ℝ Ψ p u| ≤ C₁ * ‖u‖
  second : ∀ u v, |fderiv ℝ (fun z => fderiv ℝ Ψ z u) p v| ≤ C₂ * ‖u‖ * ‖v‖
private theorem differentiableAt_fderiv_apply {Ψ : P → ℝ} {p : P} (h : ContDiffAt ℝ 3 Ψ p) (u : P) :
    DifferentiableAt ℝ (fun z => fderiv ℝ Ψ z u) p := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ Ψ) p := h.fderiv_right (m := 2) (by norm_num)
  exact (h1.clm_apply contDiffAt_const).differentiableAt (by norm_num)
private theorem TwiceBounded.add {C₁ C₂ D₁ D₂ : ℝ} {Ψ Θ : P → ℝ} {p : P} (h : TwiceBounded C₁ C₂ Ψ p)
    (g : TwiceBounded D₁ D₂ Θ p) : TwiceBounded (C₁ + D₁) (C₂ + D₂) (fun z => Ψ z + Θ z) p := by
  have dΨ : DifferentiableAt ℝ Ψ p := h.smooth.differentiableAt (by norm_num)
  have dΘ : DifferentiableAt ℝ Θ p := g.smooth.differentiableAt (by norm_num)
  refine ⟨h.smooth.add g.smooth, fun u => ?_, fun u v => ?_⟩
  · rw [fderiv_fun_add dΨ dΘ]
    have h1 := h.first u
    have h2 := g.first u
    calc _ ≤ |fderiv ℝ Ψ p u| + |fderiv ℝ Θ p u| := abs_add_le _ _
      _ ≤ _ := by linarith
  · have ev : (fun z => fderiv ℝ (fun y => Ψ y + Θ y) z u) =ᶠ[nhds p]
        fun z => fderiv ℝ Ψ z u + fderiv ℝ Θ z u := by
      have e1 := h.smooth.eventually (by simp)
      have e2 := g.smooth.eventually (by simp)
      filter_upwards [e1, e2] with z h1 h2
      rw [fderiv_fun_add (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num))]
      rfl
    rw [ev.fderiv_eq, fderiv_fun_add (differentiableAt_fderiv_apply h.smooth u)
      (differentiableAt_fderiv_apply g.smooth u)]
    have h1 := h.second u v
    have h2 := g.second u v
    calc _ ≤ |fderiv ℝ (fun z => fderiv ℝ Ψ z u) p v| + |fderiv ℝ (fun z => fderiv ℝ Θ z u) p v| :=
          abs_add_le _ _
      _ ≤ _ := by linarith
private theorem TwiceBounded.sum {C₁ C₂ : ℝ} {Ψ : Fin 4 → P → ℝ} {p : P} (h : ∀ d, TwiceBounded C₁ C₂ (Ψ d) p) :
    TwiceBounded (4 * C₁) (4 * C₂) (fun z => ∑ d, Ψ d z) p := by
  have e : (fun z => ∑ d, Ψ d z) = fun z => Ψ 0 z + Ψ 1 z + Ψ 2 z + Ψ 3 z := by
    funext z
    exact Fin.sum_univ_four _
  rw [e]
  have h4 := (((h 0).add (h 1)).add (h 2)).add (h 3)
  have e1 : 4 * C₁ = C₁ + C₁ + C₁ + C₁ := by ring
  have e2 : 4 * C₂ = C₂ + C₂ + C₂ + C₂ := by ring
  rw [e1, e2]
  exact h4
private theorem abs_sub_le_of_segment {Ψ : P → ℝ} {a Δ : P} {C : ℝ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ Ψ (a + t • Δ))
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |fderiv ℝ Ψ (a + t • Δ) Δ| ≤ C) : |Ψ (a + Δ) - Ψ a| ≤ C := by
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => Ψ (a + t • Δ)) (f' := fun t => fderiv ℝ Ψ (a + t • Δ) Δ) (C := C) (x := 0) (y := 1)
    (fun t ht => by
      have h1 : HasDerivAt (fun t : ℝ => a + t • Δ) Δ t := by
        simpa using ((hasDerivAt_id t).smul_const Δ).const_add a
      exact ((hd t ht).hasFDerivAt.comp_hasDerivAt t h1).hasDerivWithinAt)
    (fun t ht => hb t ht) (by simp) (by simp)
  simpa using h
private theorem fderiv_eq_zero_of_line_const {Ψ : P → ℝ} {p v : P} (hd : DifferentiableAt ℝ Ψ p)
    (h : ∀ t : ℝ, Ψ (p + t • v) = Ψ p) : fderiv ℝ Ψ p v = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have h2 : HasFDerivAt Ψ (fderiv ℝ Ψ p) ((fun t : ℝ => p + t • v) 0) := by
    simpa using hd.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  have e : (Ψ ∘ fun t : ℝ => p + t • v) = fun _ => Ψ p := by
    funext t
    exact h t
  rw [e] at h3
  exact h3.unique (hasDerivAt_const _ _)
end Calculus
private theorem centredCube_card_real (M : ℕ) (hM : Odd M) : ((centredCube M).card : ℝ) = (M : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
private theorem contourAverage_norm_bounds (hL : Odd F.blockSide) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4)
    (h : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖((pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) * (V c.1 c.2)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ ∧ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ ≤ 1 := by
  classical
  set z : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    ((pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) with hz
  set v : ℍ[ℝ] := (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hv
  have hnv : ‖v‖ = 1 := BlockOffsets.norm_coe_unitQuaternion _
  have hnz : ∀ h π, ‖z h π‖ = 1 := fun h π => BlockOffsets.norm_coe_unitQuaternion _
  have hr : ∀ h π, ((pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) * (V c.1 c.2)⁻¹ :
      UnitQuaternion) : ℍ[ℝ]) = z h π * v := fun h π => rfl
  have hLpos : (0 : ℝ) < F.blockSide := by
    have := hL.pos
    exact_mod_cast this
  set n : ℝ := 24 * (F.blockSide : ℝ) ^ 4 with hn
  have hn0 : 0 < n := by positivity
  have hcount : ((centredCube F.blockSide).card : ℝ) * 24 = n := by
    rw [centredCube_card_real _ hL, hn]
    ring
  have hmean : _root_.YangMills.Construction.BlockAverages.contourAverage W c = (1 / n) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), z h π := rfl
  have hsum1 : ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) = n := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
    rw [← hcount]
    norm_num
  refine ⟨?_, ?_⟩
  · have e1 : _root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1 =
        (1 / n) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1) := by
      have h1 : (∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ])) = (n : ℝ) • (1 : ℍ[ℝ]) := by
        rw [← hsum1, Finset.sum_smul]
        refine Finset.sum_congr rfl fun h' _ => ?_
        rw [Finset.sum_smul]
        simp
      have h2 : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1) =
          (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), z h π) * v - (n : ℝ) • (1 : ℍ[ℝ]) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_mul]
        rw [h1]
      rw [hmean, h2, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hn0.ne', one_smul, smul_mul_assoc]
    have e2 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1‖ ≤ 1 / 2 := by
      rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h2 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1)‖ ≤ n * (1 / 2) := by
        refine (norm_sum_le _ _).trans ?_
        have : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4), (z h π * v - 1)‖ ≤
            ∑ _π : Equiv.Perm (Fin 4), (1 / 2 : ℝ) := fun h' hh =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => by
            rw [← hr]; exact h h' π hh)
        refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
        rw [← hsum1]
        simp
        ring
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1 / n)
      have h4 : 1 / n * (n * (1 / 2)) = 1 / 2 := by field_simp
      linarith
    have e3 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v‖ = ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ := by rw [norm_mul, hnv, mul_one]
    have e4 : 1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v‖ ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1‖ := by
      have := norm_sub_norm_le (1 : ℍ[ℝ]) (_root_.YangMills.Construction.BlockAverages.contourAverage W c * v)
      rw [norm_one, norm_sub_rev] at this
      exact this
    linarith
  · rw [hmean, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), z h π‖ ≤ n := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4), z h π‖ ≤
          ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) :=
        fun h' _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => (hnz h' π).le)
      exact (Finset.sum_le_sum this).trans (le_of_eq hsum1)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1 / n)
    have h4 : 1 / n * n = 1 := by field_simp
    linarith
private def gapTerm (A : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) (η : StepVariable (finiteCells F)) : ℝ :=
  haarGap (A * ‖chartedContourAverage w V c η‖) - haarGap A
private def IsSmallChart (L : ℕ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (p : StepVariable (finiteCells F)) : Prop :=
  ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 + stepCoordinates p b.1 b.2‖ ≤ 1 / (10 * (L : ℝ))
private def AverageDerivBound (L : ℕ) (C : ℝ) : Prop :=
  ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) (p : StepVariable (finiteCells F)), F.blockSide = L → (∀ i, 2 ≤ F.extent i) →
    (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 + stepCoordinates p b.1 b.2‖ ≤ 1) →
    ContDiff ℝ 3 (chartedContourAverage w V c) ∧
    ∀ u v : StepVariable (finiteCells F),
      ‖fderiv ℝ (chartedContourAverage w V c) p u‖ ≤ C * ‖u‖ ∧
      ‖fderiv ℝ (fun z => fderiv ℝ (chartedContourAverage w V c) z u) p v‖ ≤ C * ‖u‖ * ‖v‖
private def HaarGapDerivBound (K : ℝ) : Prop :=
  ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (M : P → ℍ[ℝ]) (A : ℝ),
    2 ≤ A → ContDiffAt ℝ 3 M 0 → 1 / 2 ≤ ‖M 0‖ → ‖M 0‖ ≤ 1 →
    ContDiffAt ℝ 3 (fun ζ => haarGap (A * ‖M ζ‖) - haarGap A) 0 ∧
    ∀ u v : P,
      |fderiv ℝ (fun ζ => haarGap (A * ‖M ζ‖) - haarGap A) 0 u| ≤ K * ‖fderiv ℝ M 0 u‖ ∧
      |fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => haarGap (A * ‖M ξ‖) - haarGap A) ζ u) 0 v| ≤
        K * (‖fderiv ℝ M 0 u‖ * ‖fderiv ℝ M 0 v‖ + ‖fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v‖)
private theorem gapTerm_twiceBounded {L : ℕ} {C K A : ℝ} (hMB : AverageDerivBound L C) (hGB : HaarGapDerivBound K)
    (hC0 : 0 < C) (hK0 : 0 < K) (hCon : ChartedFieldContourBound) (hF : F.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hA : 2 ≤ A) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4)
    (p : StepVariable (finiteCells F)) (hp : IsSmallChart L w p) :
    TwiceBounded (K * C) (K * (C ^ 2 + C)) (gapTerm A w V c) p := by
  have hLF : Odd F.blockSide := hF ▸ hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL.pos
  have hp1 : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 + stepCoordinates p b.1 b.2‖ ≤ 1 := fun b hb =>
    (hp b hb).trans (by
      rw [div_le_one (by positivity)]
      linarith)
  obtain ⟨hsm, hd⟩ := hMB F w V c p hF hs hp1
  have hnorm : 1 / 2 ≤ ‖chartedContourAverage w V c p‖ ∧ ‖chartedContourAverage w V c p‖ ≤ 1 := by
    refine contourAverage_norm_bounds hLF _ V c fun h π hh => ?_
    have h1 := hCon F (fun x i => w x i + stepCoordinates p x i) V (1 / (10 * (L : ℝ))) hLF hs (by positivity)
      hp c h π hh
    have e : 5 * (F.blockSide : ℝ) * (1 / (10 * (L : ℝ))) = 1 / 2 := by
      rw [hF]
      field_simp
      norm_num
    rw [e] at h1
    exact h1
  set M : StepVariable (finiteCells F) → ℍ[ℝ] := fun ζ => chartedContourAverage w V c (p + ζ) with hM
  have hMc : ContDiffAt ℝ 3 M 0 := (hsm.comp (contDiff_const.add contDiff_id)).contDiffAt
  have hM0 : M 0 = chartedContourAverage w V c p := by simp [hM]
  obtain ⟨hcd, hb⟩ := hGB _ M A hA hMc (by rw [hM0]; exact hnorm.1) (by rw [hM0]; exact hnorm.2)
  have eM : ∀ z, fderiv ℝ M z = fderiv ℝ (chartedContourAverage w V c) (p + z) := fun z =>
    fderiv_comp_add_left (𝕜 := ℝ) (f := chartedContourAverage w V c) (x := z) p
  have eP : (fun ζ => haarGap (A * ‖M ζ‖) - haarGap A) = fun ζ => gapTerm A w V c (p + ζ) := rfl
  have eφ : ∀ z, fderiv ℝ (fun ζ => gapTerm A w V c (p + ζ)) z = fderiv ℝ (gapTerm A w V c) (p + z) := fun z =>
    fderiv_comp_add_left (𝕜 := ℝ) (f := gapTerm A w V c) (x := z) p
  have e2M : ∀ u, fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 =
      fderiv ℝ (fun z => fderiv ℝ (chartedContourAverage w V c) z u) p := fun u => by
    have e : (fun ζ => fderiv ℝ M ζ u) =
        fun ζ => (fun z => fderiv ℝ (chartedContourAverage w V c) z u) (p + ζ) := by
      funext ζ
      rw [eM]
    rw [e]
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun z => fderiv ℝ (chartedContourAverage w V c) z u)
      (x := (0 : StepVariable (finiteCells F))) p
    simpa using this
  have e2φ : ∀ u, fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => gapTerm A w V c (p + ξ)) ζ u) 0 =
      fderiv ℝ (fun z => fderiv ℝ (gapTerm A w V c) z u) p := fun u => by
    have e : (fun ζ => fderiv ℝ (fun ξ => gapTerm A w V c (p + ξ)) ζ u) =
        fun ζ => (fun z => fderiv ℝ (gapTerm A w V c) z u) (p + ζ) := by
      funext ζ
      rw [eφ]
    rw [e]
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun z => fderiv ℝ (gapTerm A w V c) z u)
      (x := (0 : StepVariable (finiteCells F))) p
    simpa using this
  have bM : ∀ u, ‖fderiv ℝ M 0 u‖ ≤ C * ‖u‖ := fun u => by
    rw [eM, add_zero]
    exact (hd u 0).1
  refine ⟨?_, fun u => ?_, fun u v => ?_⟩
  · have h1 : ContDiffAt ℝ 3 (fun ζ => gapTerm A w V c (p + ζ)) ((fun z => z - p) p) := by
      rw [← eP]
      simpa using hcd
    have h2 := ContDiffAt.comp (g := fun ζ => gapTerm A w V c (p + ζ)) (f := fun z => z - p) p h1
      (contDiffAt_id.sub contDiffAt_const)
    have e : (fun ζ => gapTerm A w V c (p + ζ)) ∘ (fun z => z - p) = gapTerm A w V c := by
      funext z
      simp
    rw [e] at h2
    exact h2
  · have h1 := (hb u 0).1
    rw [eP, eφ, add_zero] at h1
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (bM u) hK0.le
  · have h1 := (hb u v).2
    rw [eP, e2φ, e2M] at h1
    refine h1.trans ?_
    have b1 := bM u
    have b2 := bM v
    have b3 := (hd u v).2
    have nu := norm_nonneg u
    have nv := norm_nonneg v
    have t1 : ‖fderiv ℝ M 0 u‖ * ‖fderiv ℝ M 0 v‖ ≤ (C * ‖u‖) * (C * ‖v‖) := by gcongr
    have : K * (‖fderiv ℝ M 0 u‖ * ‖fderiv ℝ M 0 v‖ +
        ‖fderiv ℝ (fun z => fderiv ℝ (chartedContourAverage w V c) z u) p v‖) ≤
        K * ((C * ‖u‖) * (C * ‖v‖) + C * ‖u‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (add_le_add t1 b3) hK0.le
    refine this.trans (le_of_eq ?_)
    ring
private theorem chartedContourAverage_eq_of_far (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) (p : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
    (e : EuclideanSpace ℝ (Fin 3)) (h1 : enclosingCell b.1.1 ≠ c.1)
    (h2 : enclosingCell b.1.1 ≠ c.1 + unitStep F.top c.2) (t : ℝ) :
    chartedContourAverage w V c (p + t • bondVariation b e) = chartedContourAverage w V c p := by
  classical
  unfold chartedContourAverage
  refine contourAverage_eq_of_far hL hs c b.1.1 (fun y k hy => ?_) h1 h2
  have hc : stepCoordinates (p + t • bondVariation b e) y k = stepCoordinates p y k := by
    unfold stepCoordinates
    by_cases h : (y, k) ∈ chordBonds (finiteCells F)
    · rw [dif_pos h, dif_pos h]
      have hne : (⟨(y, k), h⟩ : ↥(chordBonds (finiteCells F))) ≠ b := by
        intro he
        apply hy
        rw [← he]
      have : (p + t • bondVariation b e) ⟨(y, k), h⟩ = p ⟨(y, k), h⟩ := by
        simp [bondVariation, Pi.single_eq_of_ne hne]
      rw [this]
    · rw [dif_neg h, dif_neg h]
  simp only [chartedField, hc]
private def interpolatedCoords (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun y i => interpolatedFrame s a ρA m (y, i) V
private theorem interpolatedGapPart_eq (hs : ∀ i, 2 ≤ F.extent i) (s a ρA x : ℝ) (m : ℕ) (z : F.Cell)
    (V : F.GaugeField F.top) :
    interpolatedGapPart s a ρA x m z V =
      fun η => ∑ d : Fin 4, gapTerm (a * x) (interpolatedCoords s a ρA m V) V (z, d) η := by
  classical
  funext η
  unfold interpolatedGapPart
  symm
  refine Finset.sum_bij (fun d _ => ((z, d) : F.Site F.top × Fin 4)) (fun d _ => ?_) (fun d _ d' _ h => ?_)
    (fun c hc => ?_) (fun d _ => rfl)
  · simp only [Finset.mem_filter, and_true, innerBonds, Finset.mem_product, Finset.mem_univ]
    exact ⟨mem_sitesOfCells_top.2 (BlockOffsets.mem_finiteCells hs _),
      mem_sitesOfCells_top.2 (BlockOffsets.mem_finiteCells hs _)⟩
  · exact (Prod.ext_iff.1 h).2
  · have h1 := (Finset.mem_filter.1 hc).2
    exact ⟨c.2, Finset.mem_univ _, Prod.ext h1.symm rfl⟩
private theorem gapParts_compare_core {L : ℕ} {C K θ ρ A : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hMB : AverageDerivBound L C) (hGB : HaarGapDerivBound K) (hC0 : 0 < C) (hK0 : 0 < K)
    (hCon : ChartedFieldContourBound) (hO : TorusOffsetsAboutCell)
    (hP : PairedCoordinatesAgree) (hE : PushforwardFieldProperties)
    (hGl : TwoChartsGlue) (hLC : ImaginaryCoordinatesIsometric)
    (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L) {q r : ℕ} (hrq : r ≤ q) (hq2 : 2 ≤ q)
    (hsd : ∀ i, 2 * q + 2 < F.extent i) (hsd' : ∀ i, 2 * q + 2 < F'.extent i)
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius q b → V (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top b.1) b.2 = V' (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top b.1) b.2)
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hj : Function.Injective j) (hj' : Function.Injective j') (hpair : AreOffsetPaired Y Y' q j j')
    {o : Fin 4 → ℤ} (ho : WithinRadius r o) (ho' : ∀ d, WithinRadius r (o + Pi.single d 1))
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    (hθ : 0 ≤ θ) (hnear : CoordinatesCloseOnBall F.blockSide Y Y' r θ w w') (hA : 2 ≤ A) (hρ : 0 < ρ)
    (hsmall : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ + ρ + θ ≤ 1 / (10 * (L : ℝ)))
    (G : StepVariable (finiteCells F) → ℝ) (G' : StepVariable (finiteCells F') → ℝ)
    (hG : G = fun η => ∑ d : Fin 4, gapTerm A w V (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o, d) η)
    (hG' : G' = fun η => ∑ d : Fin 4, gapTerm A w' V' (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o, d) η) :
    ContDiffOn ℝ 1 (fun ζ => G' (pushforwardField j' ζ) - G (pushforwardField j ζ)) (openPolyball ι ρ) ∧
    ∀ ξ ∈ openPolyball ι ρ, |G' (pushforwardField j' ξ) - G (pushforwardField j ξ)| ≤ 4 * (K * C) * θ ∧
      ∀ k, bondGradNorm (fun ζ => G' (pushforwardField j' ζ) - G (pushforwardField j ζ)) k ξ = 0 ∨
        (cellSupDist (enclosingCell (j k).1.1) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ≤ 1 ∧
          bondGradNorm (fun ζ => G' (pushforwardField j' ζ) - G (pushforwardField j ζ)) k ξ ≤
            4 * (K * (C ^ 2 + C)) * θ) := by
  classical
  have hLF : Odd F.blockSide := hF ▸ hL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by have := hsd i; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by have := hsd' i; omega
  have hsr : ∀ i, 2 * r + 2 < F.extent i := fun i => by have := hsd i; omega
  obtain ⟨Δ, wx, hΔ, -, hwx, hwx'⟩ := hGl F F' Y Y' r θ w w' (hF.trans hF'.symm) hLF hsr hθ hnear
  obtain ⟨-, -, hnorm, -, hmm, -, -⟩ := hLC
  obtain ⟨-, -, eAt, eImg, eOff, -, eSm⟩ := hE ι _ j hj
  have hboxq : ∀ g : LatticeOffset, WithinRadius r g → WithinRadius q g :=
    fun g hg i => (hg i).trans (by exact_mod_cast hrq)
  have htr : ∀ (ξ : BondField ι) (d : Fin 4),
      chartedContourAverage w' V' (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o, d) (pushforwardField j' ξ) =
        chartedContourAverage w V (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o, d) (pushforwardField j ξ + Δ) := by
    intro ξ d
    unfold chartedContourAverage
    symm
    refine contourAverage_agree hF hF' hL o d (fun v k h1 h2 => ?_)
    refine chartedField_agree hF hF' hL hs hs' (r := r)
      (fun b hb => hV b ⟨hboxq _ hb.1, hboxq _ hb.2⟩) (fun g u i hg hu hb => ?_) v k
      (nearBox_of_twoBlockHull hL ho (ho' d) h1) (nearBox_of_twoBlockHull hL ho (ho' d) h2)
    have huF : u ∈ centredCube F.blockSide := by rw [hF]; exact hu
    have e1 := congrFun (congrFun (hmm F w Δ (pushforwardField j ξ)) (fineBondAt Y g u i).1) i
    have e2 : w (fineBondAt Y g u i).1 i + stepCoordinates Δ (fineBondAt Y g u i).1 i =
        wx (fineBondAt Y g u i).1 i :=
      (hwx (fineBondAt Y g u i) hb).symm
    have e3 := hwx' g u i hg huF
    have e4 := (hP F F' Y Y' q ι j j' ξ g u i (hF.trans hF'.symm) hLF hsd hsd' hj hj' hpair (hboxq _ hg) huF).2
    rw [add_comm (pushforwardField j ξ) Δ]
    simp only [shiftCoordinates] at e1
    rw [← e1, e2, e3, e4]
  have hGG : ∀ ξ : BondField ι, G' (pushforwardField j' ξ) = G (pushforwardField j ξ + Δ) := by
    intro ξ
    rw [hG, hG']
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold gapTerm
    rw [htr]
  have hemb : ∀ ξ ∈ openPolyball ι ρ, ∀ b, ‖pushforwardField j ξ b‖ ≤ ρ := by
    intro ξ hξ b
    by_cases hb : ∃ k, j k = b
    · obtain ⟨k, rfl⟩ := hb
      rw [eImg]
      exact (hξ k).le
    · rw [eOff ξ b (fun k h => hb ⟨k, h⟩), norm_zero]
      exact hρ.le
  have hcoord : ∀ (ζ : StepVariable (finiteCells F)) (b : F.Site F.depth × Fin 4)
      (hb : b ∈ chordBonds (finiteCells F)), ‖stepCoordinates ζ b.1 b.2‖ = ‖ζ ⟨b, hb⟩‖ := by
    intro ζ b hb
    unfold stepCoordinates
    rw [dif_pos hb]
    exact hnorm _
  have hnice : ∀ ξ ∈ openPolyball ι ρ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      TwiceBounded (4 * (K * C)) (4 * (K * (C ^ 2 + C))) G (pushforwardField j ξ + t • Δ) := by
    intro ξ hξ t ht
    rw [hG]
    refine TwiceBounded.sum fun d => gapTerm_twiceBounded hMB hGB hC0 hK0 hCon hF hL hs hA w V _ _ fun b hb => ?_
    refine le_trans ?_ (hsmall b hb)
    refine (norm_add_le _ _).trans ?_
    rw [hcoord _ b hb]
    have h1 := hemb ξ hξ ⟨b, hb⟩
    have h2 := hΔ ⟨b, hb⟩
    have h3 : ‖(pushforwardField j ξ + t • Δ) ⟨b, hb⟩‖ ≤ ρ + θ := by
      refine (norm_add_le _ _).trans (add_le_add h1 ?_)
      change ‖t • Δ ⟨b, hb⟩‖ ≤ _
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      nlinarith [ht.2, norm_nonneg (Δ ⟨b, hb⟩)]
    linarith
  have hΔn : ‖Δ‖ ≤ θ := (pi_norm_le_iff_of_nonneg hθ).2 hΔ
  set f : StepVariable (finiteCells F) → ℝ := fun η => G (η + Δ) - G η with hf
  have hH : (fun ζ => G' (pushforwardField j' ζ) - G (pushforwardField j ζ)) =
      fun ζ => f (pushforwardField j ζ) := by
    funext ζ
    rw [hGG]
  have hend0 : ∀ ξ ∈ openPolyball ι ρ,
      TwiceBounded (4 * (K * C)) (4 * (K * (C ^ 2 + C))) G (pushforwardField j ξ) := by
    intro ξ hξ
    simpa using hnice ξ hξ 0 (by simp)
  have hend1 : ∀ ξ ∈ openPolyball ι ρ,
      TwiceBounded (4 * (K * C)) (4 * (K * (C ^ 2 + C))) G (pushforwardField j ξ + Δ) := by
    intro ξ hξ
    simpa using hnice ξ hξ 1 (by simp)
  have hfs : ∀ ξ ∈ openPolyball ι ρ, ContDiffAt ℝ 3 f (pushforwardField j ξ) := by
    intro ξ hξ
    have h1 : ContDiffAt ℝ 3 (fun η => G (η + Δ)) (pushforwardField j ξ) :=
      ContDiffAt.comp (g := G) (f := fun η => η + Δ) _ (hend1 ξ hξ).smooth (contDiffAt_id.add contDiffAt_const)
    exact h1.sub (hend0 ξ hξ).smooth
  rw [hH]
  refine ⟨fun ξ hξ => ((eSm 3 f ξ (hfs ξ hξ)).1.of_le (by norm_num)).contDiffWithinAt,
    fun ξ hξ => ⟨?_, fun k => ?_⟩⟩
  · have h1 := abs_sub_le_of_segment (Ψ := G) (a := pushforwardField j ξ) (Δ := Δ) (C := 4 * (K * C) * θ)
      (fun t ht => (hnice ξ hξ t ht).smooth.differentiableAt (by norm_num))
      (fun t ht => ((hnice ξ hξ t ht).first Δ).trans (by
        have : 0 ≤ 4 * (K * C) := by positivity
        exact mul_le_mul_of_nonneg_left hΔn this))
    rw [hGG ξ]
    exact h1
  · have hd : ∀ u, fderiv ℝ (fun ζ => f (pushforwardField j ζ)) ξ u =
        fderiv ℝ G (pushforwardField j ξ + Δ) (pushforwardField j u) -
          fderiv ℝ G (pushforwardField j ξ) (pushforwardField j u) := by
      intro u
      have h1 := (eSm 3 f ξ (hfs ξ hξ)).2.1 (by norm_num) u
      refine h1.trans ?_
      have d1 : DifferentiableAt ℝ (fun η => G (η + Δ)) (pushforwardField j ξ) := by
        have : ContDiffAt ℝ 3 (fun η => G (η + Δ)) (pushforwardField j ξ) :=
          ContDiffAt.comp (g := G) (f := fun η => η + Δ) _ (hend1 ξ hξ).smooth
            (contDiffAt_id.add contDiffAt_const)
        exact this.differentiableAt (by norm_num)
      have d0 : DifferentiableAt ℝ G (pushforwardField j ξ) :=
        (hend0 ξ hξ).smooth.differentiableAt (by norm_num)
      rw [hf, fderiv_fun_sub d1 d0, fderiv_comp_add_right (𝕜 := ℝ) (f := G) (x := pushforwardField j ξ) Δ]
      rfl
    have hpn : ∀ B : ℝ, 0 ≤ B →
        (∀ e : EuclideanSpace ℝ (Fin 3), |fderiv ℝ G (pushforwardField j ξ + Δ) (bondVariation (j k) e) -
          fderiv ℝ G (pushforwardField j ξ) (bondVariation (j k) e)| ≤ B * ‖e‖) →
        bondGradNorm (fun ζ => f (pushforwardField j ζ)) k ξ ≤ B := by
      intro B hB h
      refine ContinuousLinearMap.opNorm_le_bound _ hB fun e => ?_
      have e1 : (fderiv ℝ (fun ζ => f (pushforwardField j ζ)) ξ).comp
          (ContinuousLinearMap.single ℝ (fun _ : ι => EuclideanSpace ℝ (Fin 3)) k) e =
          fderiv ℝ (fun ζ => f (pushforwardField j ζ)) ξ (bondVariation k e) := rfl
      rw [e1, hd, eAt]
      exact h e
    by_cases hnb : ∃ d : Fin 4, enclosingCell (j k).1.1 = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o ∨
        enclosingCell (j k).1.1 = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o + unitStep F.top d
    · right
      refine ⟨?_, hpn _ (by positivity) fun e => ?_⟩
      · obtain ⟨d, h | h⟩ := hnb
        · rw [h]
          simp [cellSupDist]
        · rw [h]
          have hq : ∀ i, 2 * 1 + 2 < F.extent i := fun i => by have := hsd i; omega
          have h3 := (hO F 1 (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) hLF hq).2.2.1 (Pi.single d 1) (fun i => by
            by_cases hi : i = d
            · subst hi
              simp
            · simp [Pi.single_eq_of_ne hi])
          have e3 : (unitStep F.top d : F.Cell) = _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top (Pi.single d 1) := rfl
          rw [e3, h3.1]
          refine Finset.sup_le fun i _ => ?_
          by_cases hi : i = d
          · subst hi
            simp
          · simp [Pi.single_eq_of_ne hi]
      · have hnu : ‖bondVariation (j k) e‖ = ‖e‖ := by
          unfold bondVariation
          exact Pi.norm_single _
        have h1 := abs_sub_le_of_segment (Ψ := fun z => fderiv ℝ G z (bondVariation (j k) e))
          (a := pushforwardField j ξ) (Δ := Δ)
          (C := 4 * (K * (C ^ 2 + C)) * θ * ‖e‖)
          (fun t ht => differentiableAt_fderiv_apply (hnice ξ hξ t ht).smooth _)
          (fun t ht => ((hnice ξ hξ t ht).second (bondVariation (j k) e) Δ).trans (by
            rw [hnu]
            have : 0 ≤ 4 * (K * (C ^ 2 + C)) * ‖e‖ := by positivity
            have h2 := mul_le_mul_of_nonneg_left hΔn this
            refine h2.trans (le_of_eq ?_)
            ring))
        exact h1
    · left
      have hfar : ∀ p : StepVariable (finiteCells F), DifferentiableAt ℝ G p →
          ∀ e : EuclideanSpace ℝ (Fin 3), fderiv ℝ G p (bondVariation (j k) e) = 0 := by
        intro p hp e
        refine fderiv_eq_zero_of_line_const hp fun t => ?_
        rw [hG]
        refine Finset.sum_congr rfl fun d _ => ?_
        unfold gapTerm
        rw [chartedContourAverage_eq_of_far hLF hs w V _ p (j k) e (fun h => hnb ⟨d, Or.inl h⟩)
          (fun h => hnb ⟨d, Or.inr h⟩) t]
      refine le_antisymm (hpn 0 le_rfl fun e => ?_) (norm_nonneg _)
      rw [hfar _ ((hend1 ξ hξ).smooth.differentiableAt (by norm_num)) e,
        hfar _ ((hend0 ξ hξ).smooth.differentiableAt (by norm_num)) e]
      simp
private structure ParameterFloors (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  Ct : 1 ≤ T.Ct
  δ₂ : 0 < T.chainParams.δ₂
  κ : 64 * T.κ ≤ T.chainParams.δ₂
  blockIndex : 16 ≤ T.blockIndex
  n₀ : 2 ≤ T.n₀
  coupling : 2 ≤ T.coupling
  numbers : ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ AverageDerivBound T.L C ∧ HaarGapDerivBound K ∧
    3 * (4 * (K * C) + 4 * (K * (C ^ 2 + C))) * T.σ ≤ 1 ∧ 10 * (T.L : ℝ) * (2 * T.Ct + 1) * T.σ ≤ 1
private theorem eventually_parameterFloors (hM : ChartedContourAverageSmooth) (hG : HaarGapOfNormNearOne) :
    EventuallyInParameters ParameterFloors := by
  obtain ⟨K, hK0, hK⟩ := hG
  intro a _
  refine ⟨0, fun L hodd _ c hc => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hM L hodd
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨1, fun Ct hCt => ⟨c.δ₂ / 64, by positivity, fun κ _ hκ' => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨16, fun nss hn => ?_⟩⟩⟩⟩
  have hL0 : (0 : ℝ) ≤ L := by positivity
  set S₁ : ℝ := 3 * (4 * (K * C) + 4 * (K * (C ^ 2 + C))) with hS₁
  set S₂ : ℝ := 10 * (L : ℝ) * (2 * Ct + 1) with hS₂
  have h1 : 0 < S₁ := by positivity
  have h2 : 0 ≤ S₂ := by positivity
  refine ⟨1 / (S₁ + S₂), by positivity, fun σ hσ hσ' p _ => ⟨0, fun Cs _ E _ => ⟨2, fun n₀ hn₀ =>
    ⟨0, fun CE _ => ⟨2, fun y₁ hy => ?_⟩⟩⟩⟩⟩
  have hsum : (S₁ + S₂) * σ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hσ' (by positivity : 0 ≤ S₁ + S₂)
    rwa [mul_one_div_cancel (by positivity)] at this
  refine ⟨hCt, hδ, by linarith, hn, hn₀, hy, C, K, hC0, hK0, hC, hK, ?_, ?_⟩
  · change S₁ * σ ≤ 1
    nlinarith
  · change S₂ * σ ≤ 1
    nlinarith
private theorem scaled_bound_le {Ct σ E1 B e₁ e₂ W : ℝ} (hCt : 0 ≤ Ct) (hB3 : 3 * (B * σ) ≤ 1) (hE : 0 ≤ E1)
    (hexp : E1 ≤ e₁ * e₂) (hW : 1 ≤ W) (h1 : 0 ≤ e₁) (h2 : 0 ≤ e₂) :
    B * (Ct * σ * E1) ≤ Ct / 3 * e₁ * W * e₂ := by
  calc B * (Ct * σ * E1) = Ct / 3 * (3 * (B * σ)) * E1 := by ring
    _ ≤ Ct / 3 * 1 * E1 := by gcongr
    _ ≤ Ct / 3 * 1 * (e₁ * e₂) := by gcongr
    _ ≤ Ct / 3 * 1 * (e₁ * e₂) * W := le_mul_of_one_le_right (by positivity) hW
    _ = _ := by ring
private theorem gapPartsCompareAt_of_floors (hCon : ChartedFieldContourBound) (hO : TorusOffsetsAboutCell)
    (hP : PairedCoordinatesAgree) (hE : PushforwardFieldProperties)
    (hGl : TwoChartsGlue) (hLC : ImaginaryCoordinatesIsometric) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered)
    (hFl : ParameterFloors T) (hFr : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x) :
    GapPartsCompareAt T := by
  intro t x s h F F' V V' Y Y' q ι _ _ j j' o hS
  obtain ⟨C, K, hC0, hK0, hMB, hGB, hσ1, hσ2⟩ := hFl.numbers
  obtain ⟨hFL, hFt, n, hn, hn₀⟩ := hS.top
  obtain ⟨hFL', hFt', n', hn', hn₀'⟩ := hS.top'
  have hodd : Odd T.L := hT.odd_L
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hq16 : 16 ≤ q := hFl.blockIndex.trans hS.radius_le
  have hn2 := hFl.n₀.trans hn₀
  have hn2' := hFl.n₀.trans hn₀'
  have hagree := hS.agree
  obtain ⟨hag1, hag2, -, hagV⟩ := hagree
  have hsd : ∀ i, 2 * q + 2 < F.extent i := fun i => (hag1 i).resolve_left (by rw [hn i]; omega)
  have hsd' : ∀ i, 2 * q + 2 < F'.extent i := fun i => (hag2 i).resolve_left (by rw [hn' i]; omega)
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by have := hsd i; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by have := hsd' i; omega
  have hx2 : 2 ≤ x := hFl.coupling.trans hS.coupling_le
  have hσ0 : 0 < T.σ := hT.σ_pos
  have hCt1 := hFl.Ct
  have hδ := hFl.δ₂
  have hκ0 := hT.κ_pos
  have hL1 : (1 : ℝ) ≤ T.L := by exact_mod_cast hodd.pos
  obtain ⟨hone, hsm⟩ := (hFr t x hS.coupling_le).single F V s hS.top hS.small hS.interp_mem.1 hS.interp_mem.2
  have hloc := (hFr t x hS.coupling_le).pair F F' V V' Y Y' q s hS.top hS.top' hS.small hS.small' hS.agree
    hS.interp_mem.1 hS.interp_mem.2
  set E1 : ℝ := Real.exp (-(T.chainParams.δ₂ * q / 8)) with hE1
  have hE1p : 0 < E1 := Real.exp_pos _
  have hE1le : E1 ≤ 1 := by
    rw [hE1]
    refine Real.exp_le_one_iff.2 ?_
    have : (0 : ℝ) ≤ T.chainParams.δ₂ * q / 8 := by positivity
    linarith
  set θ : ℝ := T.Ct * T.σ * E1 with hθd
  have hθ0 : 0 ≤ θ := by positivity
  have hθle : θ ≤ T.Ct * T.σ := by
    have : 0 ≤ T.Ct * T.σ := by positivity
    calc θ ≤ T.Ct * T.σ * 1 := mul_le_mul_of_nonneg_left hE1le this
      _ = _ := mul_one _
  set r : ℕ := q / 8 + 2 with hr
  have hrq : r + 1 ≤ q := by omega
  have hqR : (16 : ℝ) ≤ q := by exact_mod_cast hq16
  have hrR : (r : ℝ) ≤ q / 8 + 2 := by
    have h8 : 8 * (q / 8) ≤ q := Nat.mul_div_le q 8
    have : (8 : ℝ) * ((q / 8 : ℕ) : ℝ) ≤ q := by exact_mod_cast h8
    rw [hr]
    push_cast
    linarith
  have hoffs := hO F q Y hoddF hsd
  obtain ⟨c1, -, d1, -, -, n1, sy, -, -⟩ := hoffs
  have hsup : ∀ h' : Fin 4 → ℤ, WithinRadius r h' → (Finset.univ.sup fun i => (h' i).natAbs) ≤ r := by
    intro h' hh
    refine Finset.sup_le fun i _ => ?_
    have := hh i
    rw [Int.abs_eq_natAbs] at this
    omega
  have hnearbox : CoordinatesCloseOnBall F.blockSide Y Y' r θ
      (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V)
      (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V') := by
    intro g u i hg hu hb
    have hgq : WithinRadius q g := fun l => (hg l).trans (by exact_mod_cast (by omega : r ≤ q))
    have hc1 := (c1 g u i hu).1
    have hd1 := (d1 g hgq).2
    have hdist : cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) ≤ r := by
      rw [hc1, hd1]
      exact hsup g hg
    have hnext : cellSupDist Y (enclosingCell ((fineBondAt Y g u i).1 + unitStep F.depth i)) ≤ q := by
      have h1 := n1 (fineBondAt Y g u i).1 i
      rw [sy] at h1
      have h2 : cellSupDist (enclosingCell (fineBondAt Y g u i).1) Y ≤ r := by
        rw [sy]
        exact hdist
      omega
    have hbox : IsFineBondWithinRadius Y q g u i := ⟨hu, hb, hgq, by omega, hnext⟩
    have h3 := hloc.norm_sub_le g u i hbox
    refine le_trans h3 ?_
    have hdR : ((cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) : ℕ) : ℝ) ≤ r := by
      exact_mod_cast hdist
    have he : Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y g u i).1)))) ≤
        E1 := by
      rw [hE1]
      refine Real.exp_le_exp.2 ?_
      have : (q : ℝ) / 2 ≤ (q : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) := by linarith
      nlinarith
    have : 0 ≤ T.Ct * T.σ := by positivity
    exact mul_le_mul_of_nonneg_left he this
  have ho : WithinRadius r o := fun i => by
    have := hS.offset_le i
    rw [abs_le]
    have h2 := abs_le.1 (le_refl |o i|)
    omega
  have ho' : ∀ d, WithinRadius r (o + Pi.single d 1) := fun d i => by
    have := hS.offset_le i
    have h2 := abs_le.1 (le_refl |o i|)
    rw [abs_le]
    by_cases hi : i = d
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
      omega
  have hA : 2 ≤ T.a * x := by
    have := hT.one_le_a
    nlinarith
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hsmall : ∀ b ∈ chordBonds (finiteCells F),
      ‖interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V b.1 b.2‖ + T.ballRadius + θ ≤
        1 / (10 * (T.L : ℝ)) := by
    intro b hb
    have h1 : ‖interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V b.1 b.2‖ ≤ T.Ct * T.σ := hsm.norm_le b hb
    have h2 : T.ballRadius ≤ T.σ := by
      unfold StepParameters.ballRadius
      linarith
    rw [le_div_iff₀ (by positivity)]
    have h3 : (‖interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V b.1 b.2‖ + T.ballRadius + θ) ≤
        (2 * T.Ct + 1) * T.σ := by
      nlinarith
    have h4 : 0 ≤ 10 * (T.L : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h3 h4
    nlinarith
  obtain ⟨hsmooth, hb⟩ := gapParts_compare_core hMB hGB hC0 hK0 hCon hO hP hE hGl hLC hFL hFL' hodd
    (by omega : r ≤ q) (by omega : 2 ≤ q) hsd hsd' (fun b hb => hagV b hb) hS.injective hS.injective'
    hS.paired ho ho' hθ0 hnearbox hA hρ hsmall _ _
    (interpolatedGapPart_eq hs s T.a T.chainParams.ρA x (frameRadius x) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) V)
    (interpolatedGapPart_eq hs' s T.a T.chainParams.ρA x (frameRadius x) (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o) V')
  refine ⟨hsmooth, fun ξ hξ => ?_⟩
  obtain ⟨hv, hk⟩ := hb ξ hξ
  have hx0 : 0 ≤ x := by linarith
  have hCt0 : 0 < T.Ct := by linarith
  have hq0 : (1 : ℝ) ≤ q := by linarith
  have hκδ := hFl.κ
  have hKC : 3 * (4 * (K * C)) * T.σ ≤ 1 := by
    have : 0 ≤ 3 * (4 * (K * (C ^ 2 + C))) * T.σ := by positivity
    nlinarith
  have hKC2 : 3 * (4 * (K * (C ^ 2 + C))) * T.σ ≤ 1 := by
    have : 0 ≤ 3 * (4 * (K * C)) * T.σ := by positivity
    nlinarith
  have hexp0 : E1 ≤ Real.exp (-(4 * T.κ * q)) := by
    rw [hE1]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  refine ⟨?_, fun k => ?_⟩
  · refine hv.trans ?_
    have hsq : 0 ≤ weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ := by
      unfold weightedSqNormNear
      exact Finset.sum_nonneg fun b _ => by positivity
    have h1 : (1 : ℝ) ≤ x * weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F)
        (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ + 1 := by
      have := mul_nonneg hx0 hsq
      linarith
    have h2 : 4 * (K * C) * θ ≤ T.Ct / 3 * Real.exp (-(4 * T.κ * q)) := by
      have e : 4 * (K * C) * θ = T.Ct / 3 * (3 * (4 * (K * C)) * T.σ) * E1 := by
        rw [hθd]
        ring
      rw [e]
      have : 0 ≤ T.Ct / 3 := by positivity
      calc T.Ct / 3 * (3 * (4 * (K * C)) * T.σ) * E1 ≤ T.Ct / 3 * 1 * E1 := by gcongr
        _ ≤ T.Ct / 3 * 1 * Real.exp (-(4 * T.κ * q)) := by gcongr
        _ = _ := by ring
    have h3 : 0 ≤ T.Ct / 3 * Real.exp (-(4 * T.κ * q)) := by positivity
    calc _ ≤ T.Ct / 3 * Real.exp (-(4 * T.κ * q)) := h2
      _ ≤ T.Ct / 3 * Real.exp (-(4 * T.κ * q)) * (x * weightedSqNormNear T.κ (fun k => bondBlock F (j k))
          (blockDist F) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ + 1) := le_mul_of_one_le_right h3 h1
  · have hB : 0 ≤ T.Ct / 3 * Real.exp (-(4 * T.κ * q)) *
        (x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F)
          (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ) + 1) *
        Real.exp (-(2 * T.κ * blockDist F (bondBlock F (j k)) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o))) := by
      have := Real.sqrt_nonneg (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F)
        (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ)
      positivity
    rcases hk k with h0 | ⟨hd1, hle⟩
    · rw [h0]
      exact hB
    · refine hle.trans ?_
      have hdR : blockDist F (bondBlock F (j k)) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ≤ 1 := by
        unfold blockDist bondBlock
        exact_mod_cast hd1
      have hsq1 : (1 : ℝ) ≤ x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F)
          (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ) + 1 := by
        have := mul_nonneg hx0 (Real.sqrt_nonneg (weightedSqNormNear T.κ (fun k => bondBlock F (j k))
          (blockDist F) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ))
        linarith
      have hexp : E1 ≤ Real.exp (-(4 * T.κ * q)) *
          Real.exp (-(2 * T.κ * blockDist F (bondBlock F (j k)) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o))) := by
        rw [← Real.exp_add, hE1]
        refine Real.exp_le_exp.2 ?_
        have h5 : T.κ * blockDist F (bondBlock F (j k)) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ≤ T.κ * q := by
          have := hdR.trans hq0
          exact mul_le_mul_of_nonneg_left this hκ0.le
        have h6 : 64 * T.κ * q ≤ T.chainParams.δ₂ * q := mul_le_mul_of_nonneg_right hκδ (by linarith)
        have h7 : 0 ≤ T.κ * q := by positivity
        linarith
      exact scaled_bound_le (B := 4 * (K * (C ^ 2 + C))) hCt0.le (by linarith) hE1p.le hexp hsq1
        (Real.exp_pos _).le (Real.exp_pos _).le
theorem gapPartsCompare_proof (hj : EventuallyInParametersCombines) (hfr : interpolatedFramesControlled)
    (hG : HaarGapOfNormNearOne) (hM : ChartedContourAverageSmooth)
    (hCon : ChartedFieldContourBound) (hO : TorusOffsetsAboutCell)
    (hP : PairedCoordinatesAgree) (hE : PushforwardFieldProperties)
    (hGl : TwoChartsGlue) (hLC : ImaginaryCoordinatesIsometric) : GapPartsCompare := by
  refine hj.2 _ _ (fun T hT h => ?_) (hj.1 _ _ (eventually_parameterFloors hM hG) hfr)
  exact gapPartsCompareAt_of_floors hCon hO hP hE hGl hLC T hT h.1 h.2
end YangMills.Construction.ColdStepAtMirrorFrames.GapPartComparison
end
