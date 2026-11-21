import YangMills.Construction.ColdStepAtMirrorFrames.CutOfANearFlatField
import YangMills.Construction.ColdStepAtMirrorFrames.EntriesOfTheExpansionNearTheFlatField
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtANearFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionNearTheFlatField
import YangMills.Construction.ColdStepAtMirrorFrames.FieldNearTheFlatField
import YangMills.Construction.ColdStepAtMirrorFrames.FirstOrderAtTheFlatFieldForm
import YangMills.Construction.ColdStepAtMirrorFrames.FirstPartOfAChartMotion
import YangMills.Construction.ColdStepAtMirrorFrames.TwoMotionsNearAField
import YangMills.Construction.HoleBesideASecondHole.CoordinatesOfAFieldNearATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongATiltProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages Interpolation Estimates
namespace ColdStepAtMirrorFrames
namespace CentredExpansionNearUniformTopProof
open BlockOffsets
variable {F : BlockFrame}
theorem isCubicTorusAbove_of_isCubicTopTorus {L t n₀ : ℕ} (hL : 0 < L) (h : IsCubicTopTorus L t n₀ F) :
    IsCubicTorusAbove L t n₀ F := by
  obtain ⟨h1, h2, n, h3, h4⟩ := h
  exact ⟨h1, h2, n, h3, h4.trans (Nat.le_mul_of_pos_right n hL)⟩
theorem isLargeCubicTorus_of_isCubicTopTorus {L t n₀ : ℕ} (h64 : 64 ≤ n₀) (h : IsCubicTopTorus L t n₀ F) :
    IsLargeCubicTorus F := by
  obtain ⟨_, _, n, h3, h4⟩ := h
  exact ⟨n, by omega, h3⟩
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem gap_fieldAboveFrame_le (hcover : BlocksCoverLowerLevel) (hfield : ChartedFieldNearOne)
    (hgeo : CubicTorusCellGeometry) {Ct σ : ℝ} {R : ℕ} (star : Bool) (a ρA : ℝ) (m : ℕ)
    (hσ : 0 < σ) (hCt : 0 ≤ Ct) (hodd : Odd F.blockSide) (hcub : IsLargeCubicTorus F)
    (hs : ∀ i, 2 * R + 2 < F.extent i)
    (V : F.GaugeField F.top) (Y : F.Cell) (η : StepVariable (finiteCells F))
    (hsize : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star a ρA m b V‖ ≤ Ct * σ)
    (hη : ∀ b, ‖η b‖ ≤ σ / 64) (hn : IsNearUniformAbout (5 / 4 * σ) R V Y) (b : F.Site F.depth × Fin 4)
    (hb : cellSupDist (enclosingCell b.1) Y + 1 ≤ R) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (fieldAboveFrame star a ρA m V η b.1 b.2) ≤
      (Ct + 5) * (1 + cellSupDist (enclosingCell b.1) Y) * σ := by
  obtain ⟨_, _, hsym, _, _⟩ := hgeo.1 F hodd hcub
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hq : ∀ b', ¬ IsAxialTreeBond b' → ‖coordsAboveFrame star a ρA m V η b'.1 b'.2‖ ≤ (Ct + 1) * σ := by
    intro b' ht
    have hb' : b' ∈ chordBonds (finiteCells F) := by
      simp only [chordBonds, innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨⟨hcover F hodd hpos _, hcover F hodd hpos _⟩, ht⟩
    have h1 := hsize b' hb'
    have h2 : ‖stepCoordinates η b'.1 b'.2‖ ≤ σ / 64 := by
      have e : stepCoordinates η b'.1 b'.2 = toImaginary (η ⟨b', hb'⟩) := by
        simp only [stepCoordinates]
        rw [dif_pos hb']
      rw [e, norm_toImaginary]
      exact hη _
    have h3 := norm_add_le (stepFrame star a ρA m (b'.1, b'.2) V) (stepCoordinates η b'.1 b'.2)
    show ‖stepFrame star a ρA m (b'.1, b'.2) V + stepCoordinates η b'.1 b'.2‖ ≤ _
    have e2 : (b'.1, b'.2) = b' := rfl
    rw [e2] at h3 ⊢
    nlinarith
  have h1 := hfield F (coordsAboveFrame star a ρA m V η) V Y ((Ct + 1) * σ) (5 / 4 * σ) R b hs (by positivity)
    (by positivity) hn hq (by rw [hsym]; exact hb)
  rw [hsym] at h1
  have hd : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1) Y := by positivity
  refine h1.trans ?_
  nlinarith [mul_nonneg hCt hd, mul_nonneg hCt hσ.le, mul_nonneg (mul_nonneg hCt hd) hσ.le, mul_nonneg hd hσ.le]
theorem siteSupDist_add_le (hc : IsLargeCubicTorus F) (hL : 3 ≤ F.blockSide) (y : F.Site F.depth)
    (o : Fin 4 → ℤ) (r : ℕ) (ho : WithinRadius r o) :
    siteSupDist (y + siteOfCoords F.depth o) y ≤ r := by
  obtain ⟨n, hn, hs⟩ := hc
  refine Finset.sup_le fun l _ => ?_
  have hp : F.period F.depth l = F.extent l * F.blockSide := period_depth l
  have hp2 : 0 < F.period F.depth l := by
    rw [hp, hs l]
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
theorem agreeOnBox_of_flow (hgeo : CubicTorusCellGeometry) (hodd : Odd F.blockSide) (hcub : IsLargeCubicTorus F)
    (hL : 3 ≤ F.blockSide) (W : F.GaugeField F.depth) (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (Y : F.Cell) (y : F.Site F.depth)
    (R₁ r : ℕ) (hy : enclosingCell y = Y) (hr : r + F.blockSide ≤ F.blockSide * R₁)
    (hagree : ∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₁ →
      expFlow B (uniformField F F.depth) 1 b.1 b.2 = W b.1 b.2)
    (hper : ∀ i, 2 * r + 2 < F.period F.depth i) :
    AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r := by
  refine ⟨hper, hper, fun b hb => (hagree (y + siteOfCoords F.depth b.1, b.2) ?_).symm⟩
  obtain ⟨_, _, _, _, hcell⟩ := hgeo.1 F hodd hcub
  have h1 := hcell (y + siteOfCoords F.depth b.1) y
  have h2 := siteSupDist_add_le hcub hL y b.1 r hb.1
  rw [hy] at h1
  have h3 : F.blockSide * cellSupDist (enclosingCell (y + siteOfCoords F.depth b.1)) Y ≤ F.blockSide * R₁ := by
    omega
  exact Nat.le_of_mul_le_mul_left h3 (by omega)
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem bondSpread_single {j p : ℕ} (c : Fin p → F.Site j × Fin 4) (X : Fin p → imaginaryQuaternions) (l : Fin p)
    (s : Fin 1 → ℝ) :
    bondSpread c X (s 0 • Pi.single l 1) = bondSpread ![c l] ![X l] s := by
  classical
  funext y i
  have r : bondSpread ![c l] ![X l] s y i = if c l = (y, i) then s 0 • X l else 0 := by
    show (∑ m : Fin 1, if (![c l] : Fin 1 → _) m = (y, i) then
      s m • (![X l] : Fin 1 → imaginaryQuaternions) m else 0) = _
    rw [Fin.sum_univ_one]
    rfl
  rw [r]
  show (∑ m, if c m = (y, i) then (s 0 • (Pi.single l 1 : Fin p → ℝ)) m • X m else 0) = _
  rw [Finset.sum_eq_single l]
  · by_cases e : c l = (y, i) <;> simp [e]
  · intro m _ hm
    by_cases e : c m = (y, i) <;> simp [e, Pi.single_eq_of_ne hm]
  · simp
theorem fderiv_line {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P]
    [NormedSpace ℝ P] (φ : P → E) (v : P) (h : DifferentiableAt ℝ φ 0) :
    fderiv ℝ (fun s : Fin 1 → ℝ => φ (s 0 • v)) 0 (Pi.single 0 1) = fderiv ℝ φ 0 v := by
  let ι : (Fin 1 → ℝ) →L[ℝ] P := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight v
  have e : (fun s : Fin 1 → ℝ => φ (s 0 • v)) = φ ∘ ι := rfl
  have h0 : DifferentiableAt ℝ φ (ι 0) := by rw [map_zero]; exact h
  rw [e, fderiv_comp (0 : Fin 1 → ℝ) h0 ι.differentiableAt, map_zero, ContinuousLinearMap.fderiv]
  simp [ι]
theorem fderiv_param_eq_bondDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℕ}
    (G : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) (c : Fin p → F.Site F.top × Fin 4) (X : Fin p → imaginaryQuaternions) (l : Fin p)
    (h : DifferentiableAt ℝ (fun τ : Fin p → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0) :
    fderiv ℝ (fun τ : Fin p → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0 (Pi.single l 1) =
      bondDeriv G V ![c l] ![X l] := by
  unfold bondDeriv
  have h1 : iteratedFDeriv ℝ 1 (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![c l] ![X l] τ) V)) 0
      (fun l' => Pi.single l' 1) =
      fderiv ℝ (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![c l] ![X l] τ) V)) 0 (Pi.single 0 1) :=
    iteratedFDeriv_one_apply _
  rw [h1]
  have e : (fun s : Fin 1 → ℝ => G (leftTranslate (bondSpread ![c l] ![X l] s) V)) =
      fun s : Fin 1 → ℝ =>
        (fun τ : Fin p → ℝ => G (leftTranslate (bondSpread c X τ) V)) (s 0 • Pi.single l 1) := by
    funext s
    show _ = G (leftTranslate (bondSpread c X (s 0 • Pi.single l 1)) V)
    rw [bondSpread_single]
  rw [e, fderiv_line _ _ h]
def crossingComponent {p : ℕ} (c : Fin p → F.Site F.top × Fin 4) (X : Fin p → imaginaryQuaternions)
    (x : F.Site F.depth) (i : Fin 4) (τ : Fin p → ℝ) : imaginaryQuaternions := by
  classical
  exact if IsCrossingBond (x, i) then bondSpread c X τ (enclosingCell x) i else 0
theorem expUnit_motion_eq {p : ℕ} (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (c : Fin p → F.Site F.top × Fin 4)
    (X : Fin p → imaginaryQuaternions) (τ : Fin p → ℝ) (α : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (x : F.Site F.depth) (i : Fin 4) (ht : ¬ IsAxialTreeBond (x, i))
    (h : chartedField w' (leftTranslate (bondSpread c X τ) V) = leftTranslate α (chartedField w V)) :
    expUnit (α x i) = expUnit (w' x i) * expUnit (crossingComponent c X x i τ) * (expUnit (w x i))⁻¹ := by
  classical
  have h1 := congrFun (congrFun h x) i
  simp only [leftTranslate, chartedField] at h1
  by_cases hc : IsCrossingBond (x, i)
  · simp only [if_pos hc] at h1
    have e : crossingComponent c X x i τ = bondSpread c X τ (enclosingCell x) i := by
      simp only [crossingComponent]; rw [if_pos hc]
    rw [e]
    have h2 : expUnit (w' x i) * expUnit (bondSpread c X τ (enclosingCell x) i) =
        expUnit (α x i) * expUnit (w x i) := by
      have := congrArg (fun g => g * (V (enclosingCell x) i)⁻¹) h1
      simpa [mul_assoc] using this
    rw [h2]
    group
  · have e : crossingComponent c X x i τ = 0 := by
      simp only [crossingComponent]; rw [if_neg hc]
    rw [e, expUnit_zero, mul_one]
    simp only [if_neg hc, if_neg ht] at h1
    rw [h1]
    group
theorem single_basis_one {p : ℕ} (l : Fin p) :
    (fun m : Fin 1 => (Pi.single (![l] m) 1 : Fin p → ℝ)) = fun _ => Pi.single l 1 := by
  funext m; fin_cases m; rfl
theorem crossingComponent_linear {p : ℕ} (c : Fin p → F.Site F.top × Fin 4) (X : Fin p → imaginaryQuaternions)
    (hX : AreUnitVectors X) (x : F.Site F.depth) (i : Fin 4) :
    ∃ Λ : (Fin p → ℝ) →L[ℝ] imaginaryQuaternions, (crossingComponent c X x i = Λ) ∧
      ∀ l, ‖Λ (Pi.single l 1)‖ ≤ 1 := by
  classical
  by_cases hc : IsCrossingBond (x, i)
  · let Λ : (Fin p → ℝ) →L[ℝ] imaginaryQuaternions :=
      ∑ m, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m).smulRight
        (if c m = (enclosingCell x, i) then X m else 0)
    have hΛ : ∀ τ, Λ τ = ∑ m, τ m • (if c m = (enclosingCell x, i) then X m else 0) := fun τ => by
      simp [Λ]
    refine ⟨Λ, ?_, fun l => ?_⟩
    · funext τ
      have e : crossingComponent c X x i τ = bondSpread c X τ (enclosingCell x) i := by
        simp only [crossingComponent]; rw [if_pos hc]
      rw [e, hΛ]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases e2 : c m = (enclosingCell x, i) <;> simp [e2]
    · rw [hΛ, Finset.sum_eq_single l]
      · by_cases e2 : c l = (enclosingCell x, i)
        · simp [e2, hX l]
        · simp [e2]
      · intro m _ hm
        simp [Pi.single_eq_of_ne hm]
      · simp
  · refine ⟨0, ?_, fun l => by simp⟩
    funext τ
    simp only [crossingComponent]
    rw [if_neg hc]
    rfl
theorem motionComponent_near {C : ℝ} (hC : ∀ (p : ℕ) (α u v : (Fin p → ℝ) → imaginaryQuaternions) (e : Fin p → ℝ),
      ContDiffAt ℝ 1 α 0 → ContDiffAt ℝ 1 u 0 → ContDiffAt ℝ 1 v 0 → α 0 = 0 → v 0 = 0 → ‖u 0‖ ≤ 1 →
      (∀ᶠ τ in nhds 0, expUnit (α τ) = expUnit (u τ) * expUnit (v τ) * (expUnit (u 0))⁻¹) →
      ‖fderiv ℝ α 0 e - (fderiv ℝ u 0 e + fderiv ℝ v 0 e)‖ ≤
        C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖))
    {p : ℕ} (w : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions) (c : Fin p → F.Site F.top × Fin 4)
    (X : Fin p → imaginaryQuaternions) (l : Fin p)
    (x : F.Site F.depth) (i : Fin 4) (ht : ¬ IsAxialTreeBond (x, i)) (hX : AreUnitVectors X)
    (h0 : ∀ x i, α 0 x i = 0) (hc : ContDiffAt ℝ 3 (fun τ => α τ x i) 0)
    (hw : ContDiffAt ℝ 3 (fun τ => w (leftTranslate (bondSpread c X τ) V) x i) 0) (hu : ‖w V x i‖ ≤ 1)
    (hid : ∀ᶠ τ in 𝓝 0, chartedField (w (leftTranslate (bondSpread c X τ) V)) (leftTranslate (bondSpread c X τ) V) =
      leftTranslate (α τ) (chartedField (w V) V)) :
    ‖motionComponent α ![l] x i - (bondDeriv (fun V' => w V' x i) V ![c l] ![X l] +
        fderiv ℝ (crossingComponent c X x i) 0 (Pi.single l 1))‖ ≤
      C * ‖w V x i‖ * (‖bondDeriv (fun V' => w V' x i) V ![c l] ![X l]‖ +
        ‖fderiv ℝ (crossingComponent c X x i) 0 (Pi.single l 1)‖) := by
  obtain ⟨Λ, hΛ, _⟩ := crossingComponent_linear c X hX x i
  have hsp0 : leftTranslate (bondSpread c X 0) V = V := by
    funext y j
    simp [leftTranslate, bondSpread, expUnit_zero]
  have hv : ContDiffAt ℝ 1 (crossingComponent c X x i) 0 := by rw [hΛ]; exact Λ.contDiff.contDiffAt
  have hm : motionComponent α ![l] x i = fderiv ℝ (fun τ => α τ x i) 0 (Pi.single l 1) := by
    unfold motionComponent
    rw [single_basis_one]
    exact iteratedFDeriv_one_apply _
  have hdu := fderiv_param_eq_bondDeriv (fun V' => w V' x i) V c X l (hw.differentiableAt (by norm_num))
  have hu0 : w (leftTranslate (bondSpread c X 0) V) x i = w V x i := by
    rw [hsp0]
  have key := hC p (fun τ => α τ x i) (fun τ => w (leftTranslate (bondSpread c X τ) V) x i)
    (crossingComponent c X x i)
    (Pi.single l 1) (hc.of_le (by norm_num)) (hw.of_le (by norm_num)) hv (h0 x i)
    (by rw [hΛ, map_zero]) (by rw [hu0]; exact hu)
    (hid.mono fun τ h => by
      have := expUnit_motion_eq (w V) (w (leftTranslate (bondSpread c X τ) V)) V c X τ (α τ) x i ht h
      rw [hu0]
      exact this)
  rw [hm, ← hdu]
  rw [hu0] at key
  exact key
theorem bondDeriv_sub_const {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (U : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : 1 ≤ k) : bondDeriv (fun V => G V - a) U c X = bondDeriv G U c X := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  unfold bondDeriv
  have e : iteratedFDeriv ℝ (n + 1) (fun τ : Fin (n + 1) → ℝ => G (leftTranslate (bondSpread c X τ) U) - a) =
      iteratedFDeriv ℝ (n + 1) (fun τ : Fin (n + 1) → ℝ => G (leftTranslate (bondSpread c X τ) U)) := by
    funext x
    have e2 : (fderiv ℝ fun τ : Fin (n + 1) → ℝ => G (leftTranslate (bondSpread c X τ) U) - a) =
        fderiv ℝ fun τ : Fin (n + 1) → ℝ => G (leftTranslate (bondSpread c X τ) U) := by
      funext τ
      exact fderiv_sub_const _
    rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, e2]
  rw [e]
theorem bondDeriv_add_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (a : E) (U : F.GaugeField F.top) (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions) :
    bondDeriv (fun V => G V + a) U ![e] ![X] = bondDeriv G U ![e] ![X] := by
  unfold bondDeriv
  have h1 : ∀ g : (Fin 1 → ℝ) → E, iteratedFDeriv ℝ 1 g 0 (fun l => Pi.single l 1) =
      fderiv ℝ g 0 (Pi.single 0 1) :=
    fun g => iteratedFDeriv_one_apply _
  rw [h1, h1]
  have e2 : (fderiv ℝ fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![e] ![X] τ) U) + a) =
      fderiv ℝ fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![e] ![X] τ) U) := by
    funext τ
    exact fderiv_add_const _
  rw [e2]
theorem motionComponent_sub_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (p : ℕ) (α u v : (Fin p → ℝ) → imaginaryQuaternions) (e : Fin p → ℝ),
      ContDiffAt ℝ 1 α 0 → ContDiffAt ℝ 1 u 0 → ContDiffAt ℝ 1 v 0 → α 0 = 0 → v 0 = 0 → ‖u 0‖ ≤ 1 →
      (∀ᶠ τ in nhds 0, expUnit (α τ) = expUnit (u τ) * expUnit (v τ) * (expUnit (u 0))⁻¹) →
      ‖fderiv ℝ α 0 e - (fderiv ℝ u 0 e + fderiv ℝ v 0 e)‖ ≤
        C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖))
    {p : ℕ} (w w₀ : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (α α₀ : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions) (c : Fin p → F.Site F.top × Fin 4)
    (X : Fin p → imaginaryQuaternions) (l : Fin p)
    (x : F.Site F.depth) (i : Fin 4) (ht : ¬ IsAxialTreeBond (x, i)) (hX : AreUnitVectors X)
    (h0 : ∀ x i, α 0 x i = 0) (h00 : ∀ x i, α₀ 0 x i = 0) (hc : ContDiffAt ℝ 3 (fun τ => α τ x i) 0)
    (hc0 : ContDiffAt ℝ 3 (fun τ => α₀ τ x i) 0)
    (hw : ContDiffAt ℝ 3 (fun τ => w (leftTranslate (bondSpread c X τ) V) x i) 0)
    (hw0 : ContDiffAt ℝ 3 (fun τ => w₀ (leftTranslate (bondSpread c X τ) (uniformField F F.top)) x i) 0)
    (hu : ‖w V x i‖ ≤ 1) (hu0 : w₀ (uniformField F F.top) x i = 0) {K₁ : ℝ}
    (hK : ‖bondDeriv (fun V' => w V' x i) V ![c l] ![X l]‖ ≤ K₁)
    (hid : ∀ᶠ τ in 𝓝 0, chartedField (w (leftTranslate (bondSpread c X τ) V)) (leftTranslate (bondSpread c X τ) V) =
      leftTranslate (α τ) (chartedField (w V) V))
    (hid0 : ∀ᶠ τ in 𝓝 0, chartedField (w₀ (leftTranslate (bondSpread c X τ) (uniformField F F.top)))
        (leftTranslate (bondSpread c X τ) (uniformField F F.top)) =
      leftTranslate (α₀ τ) (chartedField (w₀ (uniformField F F.top)) (uniformField F F.top))) :
    ‖motionComponent α ![l] x i - motionComponent α₀ ![l] x i‖ ≤ C * ‖w V x i‖ * (K₁ + 1) +
      ‖bondDeriv (fun V' => w V' x i) V ![c l] ![X l] -
        bondDeriv (fun V' => w₀ V' x i) (uniformField F F.top) ![c l] ![X l]‖ := by
  obtain ⟨Λ, hΛ, hΛ1⟩ := crossingComponent_linear c X hX x i
  have hv : ‖fderiv ℝ (crossingComponent c X x i) 0 (Pi.single l 1)‖ ≤ 1 := by
    rw [hΛ, ContinuousLinearMap.fderiv]
    exact hΛ1 l
  have a1 := motionComponent_near hC w V α c X l x i ht hX h0 hc hw hu hid
  have a2 := motionComponent_near hC w₀ (uniformField F F.top) α₀ c X l x i ht hX h00 hc0 hw0
    (by rw [hu0]; simp) hid0
  rw [hu0, norm_zero, mul_zero, zero_mul] at a2
  have a3 : motionComponent α₀ ![l] x i =
      bondDeriv (fun V' => w₀ V' x i) (uniformField F F.top) ![c l] ![X l] +
      fderiv ℝ (crossingComponent c X x i) 0 (Pi.single l 1) := sub_eq_zero.mp (norm_le_zero_iff.mp a2)
  rw [a3]
  set A := bondDeriv (fun V' => w V' x i) V ![c l] ![X l]
  set A₀ := bondDeriv (fun V' => w₀ V' x i) (uniformField F F.top) ![c l] ![X l]
  set Dv := fderiv ℝ (crossingComponent c X x i) 0 (Pi.single l 1)
  have e : motionComponent α ![l] x i - (A₀ + Dv) = (motionComponent α ![l] x i - (A + Dv)) + (A - A₀) := by
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (a1.trans ?_) le_rfl)
  have hn := norm_nonneg (w V x i)
  have : ‖A‖ + ‖Dv‖ ≤ K₁ + 1 := add_le_add hK hv
  exact mul_le_mul_of_nonneg_left this (mul_nonneg hC0 hn)
theorem norm_minimizingBondCoordinate_le {G : BlockFrame} (a ρ : ℝ) (S : Finset G.Cell)
    (b : G.Site G.depth × Fin 4) (V : G.GaugeField G.top)
    (hρ : 0 ≤ ρ) : ‖minimizingBondCoordinate a ρ S b V‖ ≤ ρ := by
  classical
  unfold minimizingBondCoordinate minimizingCoordinates
  split_ifs with h
  · have hs := h.choose_spec
    by_cases hb : b ∈ chordBonds S
    · exact hs.2.1 b hb
    · rw [hs.1 b hb, norm_zero]
      exact hρ
  · simpa using hρ
theorem norm_stepFrame_le (star : Bool) (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top)
    (hρ : 0 ≤ ρ) : ‖stepFrame star a ρ m b V‖ ≤ ρ := by
  unfold stepFrame
  split_ifs
  · exact norm_minimizingBondCoordinate_le _ _ _ _ _ hρ
  · unfold bondFrameCoord
    split_ifs
    · exact norm_minimizingBondCoordinate_le _ _ _ _ _ hρ
    · exact norm_minimizingBondCoordinate_le _ _ _ _ _ hρ
theorem norm_coordsAboveFrame_le (star : Bool) (a ρ σ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hroom : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star a ρ m b V‖ + σ / 64 ≤ ρ)
    (hη : ∀ b, ‖η b‖ ≤ σ / 64) (x : F.Site F.depth) (i : Fin 4) : ‖coordsAboveFrame star a ρ m V η x i‖ ≤ 1 := by
  show ‖stepFrame star a ρ m (x, i) V + stepCoordinates η x i‖ ≤ 1
  by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
  · have e : stepCoordinates η x i = toImaginary (η ⟨(x, i), hb⟩) := by
      simp only [stepCoordinates]
      rw [dif_pos hb]
    have h1 := hroom _ hb
    have h2 : ‖stepCoordinates η x i‖ ≤ σ / 64 := by rw [e, norm_toImaginary]; exact hη _
    have h3 := norm_add_le (stepFrame star a ρ m (x, i) V) (stepCoordinates η x i)
    linarith
  · have e : stepCoordinates η x i = 0 := by
      simp only [stepCoordinates]
      rw [dif_neg hb]
    rw [e, add_zero]
    exact (norm_stepFrame_le star a ρ m _ V hρ).trans hρ1
theorem sum_fineBonds_le {κ Cg q : ℝ} (_hκ : 0 < κ) (hq : 0 ≤ q)
    (hCg : ∀ (G : BlockFrame), Odd G.blockSide → IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(κ * cellSupDist (enclosingCell b.1) z)) ≤ Cg * (G.blockSide : ℝ) ^ 4)
    (hodd : Odd F.blockSide) (hcub : IsLargeCubicTorus F) (z : F.Cell) (g : F.Site F.depth × Fin 4 → ℝ)
    (hg : ∀ b, g b ≤ q * Real.exp (-(κ * cellSupDist (enclosingCell b.1) z))) :
    ∑ b ∈ fineBonds F, g b ≤ q * (Cg * (F.blockSide : ℝ) ^ 4) := by
  refine (Finset.sum_le_sum fun b _ => hg b).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hCg F hodd hcub z) hq
theorem motionComponent_axial_eq_zero {C : ℝ}
    (hC : ∀ (p : ℕ) (α u v : (Fin p → ℝ) → imaginaryQuaternions) (e : Fin p → ℝ),
      ContDiffAt ℝ 1 α 0 → ContDiffAt ℝ 1 u 0 → ContDiffAt ℝ 1 v 0 → α 0 = 0 → v 0 = 0 → ‖u 0‖ ≤ 1 →
      (∀ᶠ τ in nhds 0, expUnit (α τ) = expUnit (u τ) * expUnit (v τ) * (expUnit (u 0))⁻¹) →
      ‖fderiv ℝ α 0 e - (fderiv ℝ u 0 e + fderiv ℝ v 0 e)‖ ≤
        C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖))
    {p : ℕ} (w : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions) (c : Fin p → F.Site F.top × Fin 4)
    (X : Fin p → imaginaryQuaternions) (l : Fin p)
    (x : F.Site F.depth) (i : Fin 4) (ht : IsAxialTreeBond (x, i)) (h0 : ∀ x i, α 0 x i = 0)
    (hc : ContDiffAt ℝ 3 (fun τ => α τ x i) 0)
    (hid : ∀ᶠ τ in 𝓝 0, chartedField (w (leftTranslate (bondSpread c X τ) V)) (leftTranslate (bondSpread c X τ) V) =
      leftTranslate (α τ) (chartedField (w V) V)) : motionComponent α ![l] x i = 0 := by
  classical
  have hm : motionComponent α ![l] x i = fderiv ℝ (fun τ => α τ x i) 0 (Pi.single l 1) := by
    unfold motionComponent
    rw [single_basis_one]
    exact iteratedFDeriv_one_apply _
  have key := hC p (fun τ => α τ x i) (fun _ => 0) (fun _ => 0) (Pi.single l 1) (hc.of_le (by norm_num))
    contDiffAt_const contDiffAt_const (h0 x i) rfl (by simp)
    (hid.mono fun τ h => by
      have h1 := congrFun (congrFun h x) i
      simp only [leftTranslate, chartedField, if_neg ht.1, if_pos ht, mul_one] at h1
      rw [expUnit_zero]
      simp [← h1])
  simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, add_zero, sub_zero, norm_zero,
    mul_zero] at key
  rw [hm]
  exact norm_le_zero_iff.mp key
theorem sum_fineBonds_split_le {κ Cg εb M₁ : ℝ} {R₃ : ℕ} (hκ : 0 < κ) (hε : 0 ≤ εb)
    (hM : 0 ≤ M₁)
    (hCg : ∀ (G : BlockFrame), Odd G.blockSide → IsLargeCubicTorus G → ∀ z : G.Cell,
      ∑ b ∈ fineBonds G, Real.exp (-(κ / 2 * cellSupDist (enclosingCell b.1) z)) ≤ Cg * (G.blockSide : ℝ) ^ 4)
    (hodd : Odd F.blockSide) (hcub : IsLargeCubicTorus F) (z : F.Cell) (g : F.Site F.depth × Fin 4 → ℝ)
    (hnear : ∀ b, cellSupDist (enclosingCell b.1) z ≤ R₃ → g b ≤ εb)
    (hfar : ∀ b, g b ≤ 2 * M₁ * Real.exp (-(κ * cellSupDist (enclosingCell b.1) z))) :
    ∑ b ∈ fineBonds F, g b ≤
      (εb * Real.exp (κ / 2 * R₃) + 2 * M₁ * Real.exp (-(κ / 2 * R₃))) * (Cg * (F.blockSide : ℝ) ^ 4) := by
  refine sum_fineBonds_le (by positivity) (by positivity) hCg hodd hcub z g fun b => ?_
  set D : ℝ := ((cellSupDist (enclosingCell b.1) z : ℕ) : ℝ) with hD
  by_cases h : cellSupDist (enclosingCell b.1) z ≤ R₃
  · have hDR : D ≤ R₃ := Nat.cast_le.mpr h
    have h1 : 1 ≤ Real.exp (κ / 2 * R₃) * Real.exp (-(κ / 2 * D)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith
    have h2 := hnear b h
    have h3 : 0 ≤ 2 * M₁ * Real.exp (-(κ / 2 * R₃)) * Real.exp (-(κ / 2 * D)) := by positivity
    calc g b ≤ εb := h2
      _ ≤ εb * (Real.exp (κ / 2 * R₃) * Real.exp (-(κ / 2 * D))) := le_mul_of_one_le_right hε h1
      _ ≤ _ := by nlinarith
  · have hDR : (R₃ : ℝ) ≤ D := Nat.cast_le.mpr (not_le.mp h).le
    have h2 := hfar b
    have e : Real.exp (-(κ * D)) = Real.exp (-(κ / 2 * D)) * Real.exp (-(κ / 2 * D)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : Real.exp (-(κ / 2 * D)) ≤ Real.exp (-(κ / 2 * R₃)) := Real.exp_le_exp.mpr (by nlinarith)
    have h4 : 0 ≤ εb * Real.exp (κ / 2 * R₃) * Real.exp (-(κ / 2 * D)) := by positivity
    have h5 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-(κ / 2 * D))).le
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 2 * M₁)
    rw [e] at h2
    nlinarith
theorem card_centredCube (hL : Odd F.blockSide) : (centredCube F.blockSide).card = F.blockSide ^ 4 := by apply _root_.YangMills.Construction.NearTopCoordinates.card_centredCube <;> assumption
open Classical in
theorem card_block_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) :
    ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card ≤ F.blockSide ^ 4 := by
  have hsub : ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y) ⊆
      (centredCube F.blockSide).image fun h => (cellCentre F.depth Y + siteOfCoords F.depth h : F.Site F.depth) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image, top_sub_depth, pow_one] at hx1
    obtain ⟨z, -, h, hh, rfl⟩ := hx1
    rw [enclosingCell_offset hL hs z h hh] at hx2
    subst hx2
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (centredCube F.blockSide).card := Finset.card_image_le
    _ = F.blockSide ^ 4 := card_centredCube hL
open Classical in
theorem abs_sum_block_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (g : F.Site F.depth → ℝ)
    {q : ℝ} (hq : 0 ≤ q)
    (hg : ∀ y, enclosingCell y = Y → |g y| ≤ q) :
    |∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y), g y| ≤
      (F.blockSide : ℝ) ^ 4 * q := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 := Finset.sum_le_card_nsmul ((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
    (fun y => |g y|) q (fun y hy => hg y (Finset.mem_filter.mp hy).2)
  refine h1.trans ?_
  rw [nsmul_eq_mul]
  have h2 := card_block_le hL hs Y
  have h3 : (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤
      (F.blockSide : ℝ) ^ 4 := by
    exact_mod_cast h2
  exact mul_le_mul_of_nonneg_right h3 hq
open Classical in
theorem bondDeriv_cellCentredExpansion {k : ℕ} (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (h : ∀ y : F.Site F.depth, ContDiffAt ℝ k
      (fun τ : Fin k → ℝ => centredExpansion star a ρA m f y η (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv (cellCentredExpansion star a ρA m f Y η) V c X =
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        bondDeriv (centredExpansion star a ρA m f y η) V c X := by
  unfold bondDeriv cellCentredExpansion
  have h1 := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := k)
    (u := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
    (f := fun y (τ : Fin k → ℝ) => centredExpansion star a ρA m f y η (leftTranslate (bondSpread c X τ) V))
    (x := 0) (fun y _ => h y)
  rw [h1]
  simp
theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs with h
  · apply Subtype.ext
    apply Quaternion.ext <;> rfl
  · rfl
theorem fieldAboveFrame_uniform (a ρA : ℝ) (m : ℕ)
    (hz : ∀ b, stepFrame true a ρA m b (uniformField F F.top) = 0) :
    fieldAboveFrame true a ρA m (uniformField F F.top) 0 = uniformField F F.depth := by
  classical
  funext x i
  have h1 : coordsAboveFrame true a ρA m (uniformField F F.top) 0 x i = 0 := by
    show stepFrame true a ρA m (x, i) (uniformField F F.top) + stepCoordinates 0 x i = 0
    rw [hz, stepCoordinates_zero, add_zero]
  simp only [fieldAboveFrame, chartedField, uniformField, h1, expUnit_zero]
  split_ifs <;> simp
theorem isSmallCurvature_uniformField {s : ℝ} (hs : 0 < s) : IsSmallCurvature s (uniformField F F.top) := by apply _root_.YangMills.Construction.BlockMeans.SegmentMean.isSmallCurvature_uniformField <;> assumption
theorem isSmallCurvature_uniformField_fine {s : ℝ} (hs : 0 < s) : IsSmallCurvature s (uniformField F F.depth) := by
  intro p _
  have : plaquetteHolonomy (uniformField F F.depth) p = 1 := by
    simp [plaquetteHolonomy, pathHolonomy, linkValue, uniformField]
  simp [plaquetteDefect, this, hs]
theorem bondDeriv_centredExpansion_eq {k : ℕ} (star : Bool) (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (α : (Fin k → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hid : ∀ᶠ τ in 𝓝 0, fieldAboveFrame star a ρA m (leftTranslate (bondSpread c X τ) V) η =
      leftTranslate (α τ) (fieldAboveFrame star a ρA m V η)) :
    bondDeriv (centredExpansion star a ρA m f y η) V c X =
      iteratedFDeriv ℝ k (fun τ => subtractTrivial f F y (leftTranslate (α τ) (fieldAboveFrame star a ρA m V η))) 0
        (fun l => Pi.single l 1) := by
  unfold bondDeriv
  have e : (fun τ => centredExpansion star a ρA m f y η (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
      fun τ => subtractTrivial f F y (leftTranslate (α τ) (fieldAboveFrame star a ρA m V η)) :=
    hid.mono fun τ h => by
      show subtractTrivial f F y (fieldAboveFrame star a ρA m (leftTranslate (bondSpread c X τ) V) η) = _
      rw [h]
  have e2 := (Filter.EventuallyEq.iteratedFDeriv ℝ e k).self_of_nhds
  rw [e2]
theorem final_constants_le {L4 Kc G₁ G₂ E ε₀ : ℝ} (hL : 0 < L4) (hK : 0 ≤ Kc) (hG1 : 0 < G₁) (hG : G₁ ≤ G₂)
    (hE : 0 ≤ E)
    (hε : ε₀ = 2⁻¹ ^ 14 / (L4 * (1 + Kc) ^ 2 * G₂)) :
    L4 * (ε₀ * E) ≤ 2⁻¹ ^ 8 * E / G₁ ∧ L4 * ((ε₀ * E) * Kc) ≤ 2⁻¹ ^ 10 * E / G₂ ∧
      L4 * ((ε₀ * E) * (Kc ^ 2 + Kc) + 2 * E * Kc * ε₀) ≤ 2⁻¹ ^ 10 * E / G₂ := by
  have hG2 : 0 < G₂ := lt_of_lt_of_le hG1 hG
  have hQ : 0 < (1 + Kc) ^ 2 := by positivity
  have hε0 : 0 ≤ ε₀ := by rw [hε]; positivity
  set v := L4 * ε₀ * E with hv
  have hv0 : 0 ≤ v := by positivity
  have key : v * (1 + Kc) ^ 2 = 2⁻¹ ^ 14 * E / G₂ := by
    rw [hv, hε]
    field_simp
  have hu : 0 ≤ E / G₂ := by positivity
  have e8 : 2⁻¹ ^ 14 * E / G₂ = 2⁻¹ ^ 14 * (E / G₂) := by ring
  have e10 : 2⁻¹ ^ 10 * E / G₂ = 2⁻¹ ^ 10 * (E / G₂) := by ring
  rw [e8] at key
  have h1 : v ≤ v * (1 + Kc) ^ 2 := le_mul_of_one_le_right hv0 (by nlinarith)
  have h2 : v * Kc ≤ v * (1 + Kc) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hv0
  refine ⟨?_, ?_, ?_⟩
  · have e : L4 * (ε₀ * E) = v := by rw [hv]; ring
    rw [e]
    have h4 : E / G₂ ≤ E / G₁ := div_le_div_of_nonneg_left hE hG1 hG
    have e2 : 2⁻¹ ^ 8 * E / G₁ = 2⁻¹ ^ 8 * (E / G₁) := by ring
    rw [e2]
    nlinarith
  · have e : L4 * ((ε₀ * E) * Kc) = v * Kc := by rw [hv]; ring
    rw [e, e10]
    nlinarith
  · have e : L4 * ((ε₀ * E) * (Kc ^ 2 + Kc) + 2 * E * Kc * ε₀) = v * (Kc ^ 2 + 3 * Kc) := by rw [hv]; ring
    rw [e, e10]
    nlinarith
theorem stepFrame_uniform_eq_zero {a : ℝ} {L : ℕ} {c : ColdChainParameters} (hc : c.Admissible a L)
    (F : BlockFrame) (m : ℕ) (hF : IsBlockTorus L F)
    (b : F.Site F.depth × Fin 4) : stepFrame true a c.ρA m b (uniformField F F.top) = 0 := by
  obtain ⟨⟨_, _, hs₀, _, _, _, hC1, _⟩, hall⟩ := hc.classical
  show minimizingBondCoordinate a c.ρA (finiteCells F) b (uniformField F F.top) = 0
  by_cases hb : b ∈ chordBonds (finiteCells F)
  · by_contra hne
    have hv : 0 < ‖torusCoordinate a c.ρA b (uniformField F F.top)‖ := norm_pos_iff.mpr hne
    set v := ‖torusCoordinate a c.ρA b (uniformField F F.top)‖ with hvdef
    set s := min c.s₀ (v / (2 * c.C)) with hs
    have hs0 : 0 < s := lt_min hs₀ (by positivity)
    have h1 := (hall F s (uniformField F F.top) hF hs0 (min_le_left _ _)
      (isSmallCurvature_uniformField hs0)).2.1.1 b hb
    have h2 : c.C * s ≤ v / 2 := by
      have : s ≤ v / (2 * c.C) := min_le_right _ _
      calc c.C * s ≤ c.C * (v / (2 * c.C)) := by gcongr
        _ = v / 2 := by field_simp
    linarith
  · have h1 := (hall F c.s₀ (uniformField F F.top) hF hs₀ le_rfl (isSmallCurvature_uniformField hs₀)).1.1 b hb
    exact h1
theorem exists_mul_exp_neg_le {c q ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ n : ℕ, q * Real.exp (-(c * (n : ℝ))) ≤ ε := by
  have h1 : Filter.Tendsto (fun x : ℝ => Real.exp (-(c * x))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.const_mul_atTop hc))
  have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul q
  simp only [mul_zero] at h2
  obtain ⟨n, hn⟩ := (h2.eventually (gt_mem_nhds hε)).exists
  exact ⟨n, hn.le⟩
theorem exists_torusDecayFactor_large {L : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hL : 1 ≤ L) :
    ∃ R₁ : ℕ, 4 ≤ R₁ ∧ 3 / torusDecayFactor L δ ((L * (R₁ - 1) : ℕ) : ℝ) ≤ ε := by
  let R₁ := ⌈3 / (ε * δ)⌉₊ + 4
  refine ⟨R₁, by omega, ?_⟩
  have hr : 3 / (ε * δ) ≤ ((L * (R₁ - 1) : ℕ) : ℝ) := by
    have h1 : 3 / (ε * δ) ≤ (⌈3 / (ε * δ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈3 / (ε * δ)⌉₊ ≤ L * (R₁ - 1) := by
      have : R₁ - 1 ≤ L * (R₁ - 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact h1.trans (by exact_mod_cast h2)
  set x : ℝ := ((L * (R₁ - 1) : ℕ) : ℝ) with hx
  have hG : δ * x ≤ torusDecayFactor L δ x := by
    unfold torusDecayFactor
    have h1 : (1 : ℝ) ≤ max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_left _ _
    have h2 := Real.add_one_le_exp (δ * x)
    have h3 : 0 ≤ Real.exp (δ * x) := (Real.exp_pos _).le
    nlinarith
  have hpos : 0 < δ * x := by
    have : 0 < 3 / (ε * δ) := by positivity
    have : 0 < x := lt_of_lt_of_le this hr
    positivity
  have h3 : 3 / ε ≤ δ * x := by
    have := mul_le_mul_of_nonneg_left hr hδ.le
    have e : δ * (3 / (ε * δ)) = 3 / ε := by field_simp
    linarith
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hG)]
  have h4 : 3 / ε ≤ torusDecayFactor L δ x := h3.trans hG
  rw [div_le_iff₀ hε] at h4
  linarith
theorem le_frameRadius (m₀ : ℕ) (x : ℝ) (h : (((2 ^ 11 * m₀ : ℕ) : ℝ)) ^ 100 ≤ x) : m₀ ≤ frameRadius x := by
  unfold frameRadius
  rw [Nat.le_div_iff_mul_le (by positivity)]
  have hv : (0 : ℝ) ≤ ((2 ^ 11 * m₀ : ℕ) : ℝ) := by positivity
  have h1 : ((((2 ^ 11 * m₀ : ℕ) : ℝ)) ^ 100) ^ (1 / 100 : ℝ) ≤ x ^ (1 / 100 : ℝ) :=
    Real.rpow_le_rpow (by positivity) h (by norm_num)
  have h2 : ((((2 ^ 11 * m₀ : ℕ) : ℝ)) ^ 100) ^ (1 / 100 : ℝ) = ((2 ^ 11 * m₀ : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv]
    norm_num
  rw [h2] at h1
  have h3 : ((2 ^ 11 * m₀ : ℕ) : ℝ) ≤ (⌈x ^ (1 / 100 : ℝ)⌉₊ : ℝ) := h1.trans (Nat.le_ceil _)
  have h4 : 2 ^ 11 * m₀ ≤ ⌈x ^ (1 / 100 : ℝ)⌉₊ := by exact_mod_cast h3
  omega
theorem entry_constant_le {E η G Cc A L4 σ ε : ℝ} (hE : 0 ≤ E) (hη : 0 < η) (hG : 0 < G) (hCc : 0 ≤ Cc)
    (hA : 0 ≤ A) (hL : 0 ≤ L4)
    (hσ : 0 < σ) (hε : 0 < ε) (h1 : 3 / G ≤ ε / 2) (h2 : σ ≤ ε / 2 * η / (Cc * A * L4 + 1)) :
    3 * E / G + Cc * (E / η) * (A * L4 * σ) ≤ ε * E := by
  have hp : 0 < Cc * A * L4 + 1 := by positivity
  rw [le_div_iff₀ hp] at h2
  have h3 : Cc * A * L4 * σ ≤ ε / 2 * η := by nlinarith
  have e1 : 3 * E / G = 3 / G * E := by ring
  have e2 : Cc * (E / η) * (A * L4 * σ) = (Cc * A * L4 * σ / η) * E := by
    field_simp
  have h4 : Cc * A * L4 * σ / η ≤ ε / 2 := by
    rw [div_le_iff₀ hη]
    exact h3
  rw [e1, e2]
  nlinarith
theorem gap_constant_le {CΘ Ct σ K₁ ε₃ eR Q t ε₀ : ℝ} (hC : 0 ≤ CΘ) (hCt : 0 ≤ Ct) (hK : 0 ≤ K₁) (hσ : 0 < σ)
    (hε₃ : 0 < ε₃)
    (he : 0 < eR) (hQ : 0 ≤ Q)
    (h1 : σ ≤ ε₃ / (3 * (CΘ * (Ct + 1) * (K₁ + 1) + 1))) (h2 : ε₃ * (eR * Q) ≤ ε₀ / 2)
    (h3 : t * Q ≤ ε₀ / 2) :
    ((CΘ * ((Ct + 1) * σ) * (K₁ + 1) + ε₃ / 3 + ε₃ / 3) * eR + t) * Q ≤ ε₀ := by
  have hp : 0 < 3 * (CΘ * (Ct + 1) * (K₁ + 1) + 1) := by positivity
  rw [le_div_iff₀ hp] at h1
  have h5 : (CΘ * ((Ct + 1) * σ) * (K₁ + 1) + ε₃ / 3 + ε₃ / 3) ≤ ε₃ := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 (mul_nonneg he.le hQ)
  nlinarith
end CentredExpansionNearUniformTopProof
end ColdStepAtMirrorFrames
end YangMills.Construction
end
