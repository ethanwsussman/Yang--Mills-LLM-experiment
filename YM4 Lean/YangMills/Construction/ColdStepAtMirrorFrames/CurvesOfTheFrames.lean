import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyInCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyInCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainAboveLevelZeroProof
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongASegment
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages Interpolation Calculus
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace FrameCurves
def imaginaryCoordCLM (α : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (imaginaryCoord α)
theorem imaginaryCoordCLM_apply (α : Fin 3) (w : imaginaryQuaternions) :
    imaginaryCoordCLM α w = imaginaryCoord α w := rfl
theorem abs_imaginaryCoord_le (α : Fin 3) (w : imaginaryQuaternions) : |imaginaryCoord α w| ≤ ‖w‖ := by
  have hn : ‖w‖ ^ 2 = (w : ℍ[ℝ]).re ^ 2 + (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by
    have h1 : ‖w‖ = ‖(w : ℍ[ℝ])‖ := rfl
    rw [h1, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [hn]
  fin_cases α <;> simp only [imaginaryCoord, LinearMap.coe_mk, AddHom.coe_mk] <;> simp <;> nlinarith [sq_nonneg (w : ℍ[ℝ]).re, sq_nonneg (w : ℍ[ℝ]).imI, sq_nonneg (w : ℍ[ℝ]).imJ, sq_nonneg (w : ℍ[ℝ]).imK]
theorem chartCoordinates_add_smul (dw₁ dw₂ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (dv₁ dv₂ : F.Site F.top → Fin 4 → imaginaryQuaternions) (θ : ℝ) :
    chartCoordinates (fun x i => dw₁ x i + θ • dw₂ x i) (fun y i => dv₁ y i + θ • dv₂ y i) =
      chartCoordinates dw₁ dv₁ + θ • chartCoordinates dw₂ dv₂ := by
  funext n
  simp only [chartCoordinates, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases (chartCoordinateEquiv F).symm n with p | p <;> simp [coordinateOfIndex]
theorem analyticAt_chartCoordinates {k : ℕ} (f : F.Site F.depth → Fin 4 → (Fin k → ℝ) → imaginaryQuaternions)
    (g : F.Site F.top → Fin 4 → (Fin k → ℝ) → imaginaryQuaternions)
    (hf : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ (f b.1 b.2) 0)
    (hg : ∀ y i, AnalyticAt ℝ (g y i) 0) :
    AnalyticAt ℝ (fun τ => chartCoordinates (fun x i => f x i τ) (fun y i => g y i τ)) 0 := by
  rw [analyticAt_pi_iff]
  intro n
  simp only [chartCoordinates]
  rcases (chartCoordinateEquiv F).symm n with p | p
  · exact ((imaginaryCoordCLM p.2).analyticAt _).comp (hf p.1.1 p.1.2)
  · exact ((imaginaryCoordCLM p.2).analyticAt _).comp (hg _ _)
theorem iteratedFDeriv_chartCoordinates {k p : ℕ} (f : F.Site F.depth → Fin 4 → (Fin k → ℝ) → imaginaryQuaternions)
    (g : F.Site F.top → Fin 4 → (Fin k → ℝ) → imaginaryQuaternions)
    (hf : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ (f b.1 b.2) 0)
    (hg : ∀ y i, AnalyticAt ℝ (g y i) 0) (vs : Fin p → Fin k → ℝ) :
    iteratedFDeriv ℝ p (fun τ => chartCoordinates (fun x i => f x i τ) (fun y i => g y i τ)) 0 vs =
      chartCoordinates (fun x i => iteratedFDeriv ℝ p (f x i) 0 vs) (fun y i => iteratedFDeriv ℝ p (g y i) 0 vs) := by
  have hΦ := (analyticAt_chartCoordinates f g hf hg).contDiffAt (n := (p : WithTop ℕ∞))
  funext n
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (chartDimension F) => ℝ) n) hΦ (i := p) le_rfl
  have h2 := congrArg (fun T => T vs) h1
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp, ContinuousLinearMap.proj_apply] at h2
  rw [← h2]
  rcases hn : (chartCoordinateEquiv F).symm n with q | q
  · have hfun : (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (chartDimension F) => ℝ) n) ∘
        fun τ => chartCoordinates (fun x i => f x i τ) (fun y i => g y i τ)) = ⇑(imaginaryCoordCLM q.2) ∘ f q.1.1.1 q.1.1.2 := by
      funext τ
      simp only [Function.comp, ContinuousLinearMap.proj_apply, chartCoordinates, hn, coordinateOfIndex, imaginaryCoordCLM_apply]
    have h3 := ContinuousLinearMap.iteratedFDeriv_comp_left (imaginaryCoordCLM q.2)
      ((hf q.1.1 q.1.2).contDiffAt (n := (p : WithTop ℕ∞))) (i := p) le_rfl
    have h4 := congrArg (fun T => T vs) h3
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp] at h4
    simp only [chartCoordinates, hn, coordinateOfIndex]
    rw [hfun]
    exact h4
  · have hfun : (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (chartDimension F) => ℝ) n) ∘
        fun τ => chartCoordinates (fun x i => f x i τ) (fun y i => g y i τ)) = ⇑(imaginaryCoordCLM q.2) ∘ g q.1.1.1 q.1.1.2 := by
      funext τ
      simp only [Function.comp, ContinuousLinearMap.proj_apply, chartCoordinates, hn, coordinateOfIndex, imaginaryCoordCLM_apply]
    have h3 := ContinuousLinearMap.iteratedFDeriv_comp_left (imaginaryCoordCLM q.2)
      ((hg q.1.1.1 q.1.1.2).contDiffAt (n := (p : WithTop ℕ∞))) (i := p) le_rfl
    have h4 := congrArg (fun T => T vs) h3
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp] at h4
    simp only [chartCoordinates, hn, coordinateOfIndex]
    rw [hfun]
    exact h4
theorem iteratedFDeriv_comp_clm_zero {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : A →L[ℝ] B) (f : B → E) (k : ℕ) (hf : ContDiffAt ℝ k f 0) (v : Fin k → A) :
    iteratedFDeriv ℝ k (f ∘ g) 0 v = iteratedFDeriv ℝ k f 0 (fun l => g (v l)) := by
  obtain ⟨U, hU, hUo⟩ : ∃ U ∈ nhds (0 : B), ContDiffOn ℝ k f U := by
    obtain ⟨u, hu, h⟩ := hf.contDiffOn (m := k) le_rfl (by simp)
    exact ⟨u, by simpa using hu, by simpa using h⟩
  obtain ⟨O, hOU, hOo, hO0⟩ := mem_nhds_iff.mp hU
  have hfO : ContDiffOn ℝ k f O := hUo.mono hOU
  have hg0 : g 0 ∈ O := by simpa using hO0
  have hpre : IsOpen (g ⁻¹' O) := hOo.preimage g.continuous
  have h1 := g.iteratedFDerivWithin_comp_right hfO hOo.uniqueDiffOn hpre.uniqueDiffOn hg0
    (i := k) le_rfl
  have e1 : iteratedFDerivWithin ℝ k (f ∘ g) (g ⁻¹' O) 0 = iteratedFDeriv ℝ k (f ∘ g) 0 :=
    iteratedFDerivWithin_of_isOpen k hpre (by simpa using hO0)
  have e2 : iteratedFDerivWithin ℝ k f O (g 0) = iteratedFDeriv ℝ k f 0 := by
    rw [map_zero]
    exact iteratedFDerivWithin_of_isOpen k hOo hO0
  rw [← e1, h1, e2]
  rfl
def placementCLM {k p : ℕ} (e' : Fin p → Fin k) : (Fin p → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin p → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (e' l) (1 : ℝ))
theorem placementCLM_apply {k p : ℕ} (e' : Fin p → Fin k) (σ : Fin p → ℝ) (q : Fin k) :
    placementCLM e' σ q = ∑ l, σ l * (Pi.single (e' l) (1 : ℝ) : Fin k → ℝ) q := by
  simp [placementCLM, Finset.sum_apply]
theorem placementCLM_single {k p : ℕ} (e' : Fin p → Fin k) (l : Fin p) :
    placementCLM e' (Pi.single l 1) = Pi.single (e' l) 1 := by
  funext q
  rw [placementCLM_apply, Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp
theorem iteratedFDeriv_single_eq_bondDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j k p : ℕ}
    (G : F.GaugeField j → E) (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (e' : Fin p → Fin k)
    (hG : ContDiffAt ℝ p (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    iteratedFDeriv ℝ p (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0 (fun l => Pi.single (e' l) 1) =
      bondDeriv G W (c ∘ e') (X ∘ e') := by
  classical
  have hrest : (fun σ : Fin p → ℝ => G (leftTranslate (bondSpread (c ∘ e') (X ∘ e') σ) W)) =
      (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) ∘ placementCLM e' := by
    funext σ
    simp only [Function.comp]
    congr 2
    funext z i
    simp only [bondSpread]
    have step : ∀ q : Fin k, (if c q = (z, i) then placementCLM e' σ q • X q else 0) =
        ∑ l, (if c q = (z, i) then (σ l * (Pi.single (e' l) (1 : ℝ) : Fin k → ℝ) q) • X q else 0) := by
      intro q
      split_ifs with hq
      · rw [placementCLM_apply, Finset.sum_smul]
      · simp
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single (e' l)]
    · simp
    · intro q _ hq
      split_ifs
      · simp [hq]
      · rfl
    · simp
  unfold bondDeriv
  rw [hrest, iteratedFDeriv_comp_clm_zero _ _ p hG]
  simp only [placementCLM_single]
theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j) : leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
def bondSpreadCLM {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (y : F.Site j)
    (i : Fin 4) : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (if c l = (y, i) then X l else 0)
theorem bondSpreadCLM_apply {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (y : F.Site j) (i : Fin 4) (τ : Fin k → ℝ) : bondSpreadCLM c X y i τ = bondSpread c X τ y i := by
  simp only [bondSpreadCLM, bondSpread, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem weightedNorm_chartCoordinates_le (ψ : F.Cell → ℝ) (hψ : ∀ z, 0 ≤ ψ z)
    (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (dv : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    _root_.YangMills.Construction.Calculus.weightedNorm (fun n => ψ (directionCell (chartDirections F n))) (chartCoordinates dw dv) ≤
      3 * (∑ b : ↥(chordBonds (finiteCells F)), ‖dw b.1.1 b.1.2‖ * ψ (enclosingCell b.1.1) +
        ∑ b : ↥(innerBonds (finiteCells F) F.top), ‖dv b.1.1 b.1.2‖ * ψ b.1.1) := by
  classical
  unfold _root_.YangMills.Construction.Calculus.weightedNorm
  have e1 : ∑ n, |chartCoordinates dw dv n| * ψ (directionCell (chartDirections F n)) =
      ∑ ι : ChartCoordinateIndex F, |coordinateOfIndex dw dv ι| * ψ (directionCell (directionOfIndex ι)) :=
    (chartCoordinateEquiv F).symm.sum_comp
      (fun ι => |coordinateOfIndex dw dv ι| * ψ (directionCell (directionOfIndex ι)))
  rw [e1, Fintype.sum_sum_type, mul_add]
  refine add_le_add ?_ ?_
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    simp only [Fin.sum_univ_three, coordinateOfIndex, directionOfIndex, directionCell]
    have h1 := abs_imaginaryCoord_le 0 (dw b.1.1 b.1.2)
    have h2 := abs_imaginaryCoord_le 1 (dw b.1.1 b.1.2)
    have h3 := abs_imaginaryCoord_le 2 (dw b.1.1 b.1.2)
    have h4 := hψ (enclosingCell b.1.1)
    nlinarith
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    simp only [Fin.sum_univ_three, coordinateOfIndex, directionOfIndex, directionCell]
    have h1 := abs_imaginaryCoord_le 0 (dv b.1.1 b.1.2)
    have h2 := abs_imaginaryCoord_le 1 (dv b.1.1 b.1.2)
    have h3 := abs_imaginaryCoord_le 2 (dv b.1.1 b.1.2)
    have h4 := hψ b.1.1
    nlinarith
theorem chartCoordinates_zero : chartCoordinates (F := F) (fun _ _ => 0) (fun _ _ => 0) = 0 := by
  funext n
  simp only [chartCoordinates, Pi.zero_apply]
  rcases (chartCoordinateEquiv F).symm n with p | p <;> simp [coordinateOfIndex]
theorem iteratedFDeriv_comp_add_left_zero {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : E → H) (n : ℕ) (p : E) : iteratedFDeriv ℝ n (fun z => f (p + z)) 0 = iteratedFDeriv ℝ n f p := by
  have h := iteratedFDerivWithin_comp_add_right (𝕜 := ℝ) (f := f) (s := Set.univ) n p 0
  simp only [iteratedFDerivWithin_univ, Set.vadd_set_univ, zero_add] at h
  have e : (fun z => f (p + z)) = fun z => f (z + p) := by
    funext z
    rw [add_comm]
  rw [e]
  exact h
theorem norm_imaginaryUnit (α : Fin 3) : ‖imaginaryUnit α‖ = 1 := by
  have h1 : ‖imaginaryUnit α‖ ^ 2 = 1 := by
    have e : ‖imaginaryUnit α‖ = ‖((imaginaryUnit α : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [e, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    fin_cases α <;> simp [imaginaryUnit]
  have h2 := norm_nonneg (imaginaryUnit α)
  nlinarith
theorem norm_directionVector_chartDirections (n : Fin (chartDimension F)) :
    ‖directionVector (chartDirections F n)‖ = 1 := by
  unfold chartDirections
  generalize (chartCoordinateEquiv F).symm n = ι
  rcases ι with p | p
  · exact norm_imaginaryUnit p.2
  · exact norm_imaginaryUnit p.2
theorem sum_placementCLM_smul {M : Type} [AddCommGroup M] [Module ℝ M] {N p : ℕ} (ρ : Fin p → Fin N)
    (σ : Fin p → ℝ) (f : Fin N → M) : ∑ n, placementCLM ρ σ n • f n = ∑ j, σ j • f (ρ j) := by
  classical
  simp only [placementCLM_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (ρ j)]
  · simp
  · intro n _ hn
    simp [Pi.single_apply, hn]
  · simp
theorem mem_innerBonds_top (hs : ∀ i, 2 ≤ F.extent i) (b : F.Site F.top × Fin 4) :
    b ∈ innerBonds (finiteCells F) F.top := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyCoordinates.mem_innerBonds_top <;> assumption
def frameCurve (star : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : Fin (chartDimension F) → ℝ :=
  chartCoordinates (fun x i => stepFrame star a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame star a ρ m (x, i) V)
    (bondSpread c X τ)
def frameGapCurve (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : Fin (chartDimension F) → ℝ :=
  chartCoordinates (fun x i => frameGap a ρ m (x, i) (leftTranslate (bondSpread c X τ) V)) (fun _ _ => 0)
def cellEnergyAtFrame (star : Bool) (a ρ : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) :
    (Fin (chartDimension F) → ℝ) → ℝ :=
  cellEnergyAlong a Y (fun x i => stepFrame star a ρ m (x, i) V) V (chartDirections F)
theorem cellEnergyAtFrame_frameCurve (hCE : CellEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (star : Bool) (a ρ : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) :
    cellEnergyAtFrame star a ρ m Y V (frameCurve star a ρ m V c X τ) =
      cellEnergyShare a Y (fun x i => stepFrame star a ρ m (x, i) (leftTranslate (bondSpread c X τ) V))
        (leftTranslate (bondSpread c X τ) V) := by
  unfold cellEnergyAtFrame frameCurve
  rw [(hCE F a Y _ _ V _ hL hs).1]
  congr 1
  funext x i
  abel
theorem cellEnergyAtFrame_frameCurve_add_gap (hCE : CellEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (a ρ : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) :
    cellEnergyAtFrame true a ρ m Y V (frameCurve true a ρ m V c X τ + (1 : ℝ) • frameGapCurve a ρ m V c X τ) =
      cellEnergyShare a Y (fun x i => stepFrame false a ρ m (x, i) (leftTranslate (bondSpread c X τ) V))
        (leftTranslate (bondSpread c X τ) V) := by
  have e1 : frameCurve true a ρ m V c X τ + (1 : ℝ) • frameGapCurve a ρ m V c X τ =
      chartCoordinates (fun x i => (stepFrame true a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) -
          stepFrame true a ρ m (x, i) V) + (1 : ℝ) • frameGap a ρ m (x, i) (leftTranslate (bondSpread c X τ) V))
        (fun y i => bondSpread c X τ y i + (1 : ℝ) • (0 : imaginaryQuaternions)) := by
    rw [chartCoordinates_add_smul]
    rfl
  unfold cellEnergyAtFrame
  rw [e1, (hCE F a Y _ _ V _ hL hs).1]
  have e2 : (fun y i => bondSpread c X τ y i + (1 : ℝ) • (0 : imaginaryQuaternions)) = bondSpread c X τ := by
    funext y i
    simp
  rw [e2]
  congr 1
  funext x i
  simp only [frameGap, one_smul]
  abel
theorem frameCurve_zero (star : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    frameCurve star a ρ m V c X 0 = 0 := by
  unfold frameCurve
  rw [leftTranslate_bondSpread_zero]
  have e : bondSpread c X 0 = fun _ _ => 0 := by
    funext y i
    simp [bondSpread]
  simp only [sub_self, e]
  exact chartCoordinates_zero
theorem frameGapCurve_zero (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    frameGapCurve a ρ m V c X 0 = chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0) := by
  unfold frameGapCurve
  rw [leftTranslate_bondSpread_zero]
theorem analyticAt_bondSpread {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (y : F.Site F.top) (i : Fin 4) : AnalyticAt ℝ (fun τ : Fin k → ℝ => bondSpread c X τ y i) 0 := by
  have e : (fun τ : Fin k → ℝ => bondSpread c X τ y i) = bondSpreadCLM c X y i := by
    funext τ
    rw [bondSpreadCLM_apply]
  rw [e]
  exact (bondSpreadCLM c X y i).analyticAt 0
theorem analyticAt_frameCurve {star : Bool} {a ρ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (h1 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame star a ρ m b) V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    AnalyticAt ℝ (frameCurve star a ρ m V c X) 0 := by
  refine analyticAt_chartCoordinates
    (fun x i τ => stepFrame star a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame star a ρ m (x, i) V)
    (fun y i τ => bondSpread c X τ y i) (fun b hb => ?_) (analyticAt_bondSpread c X)
  exact (h1 b hb k c X).sub analyticAt_const
theorem analyticAt_frameGapCurve {a ρ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (h1 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame true a ρ m b) V)
    (h2 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame false a ρ m b) V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    AnalyticAt ℝ (frameGapCurve a ρ m V c X) 0 := by
  refine analyticAt_chartCoordinates (fun x i τ => frameGap a ρ m (x, i) (leftTranslate (bondSpread c X τ) V))
    (fun _ _ _ => 0) (fun b hb => ?_) (fun _ _ => analyticAt_const)
  exact (h2 b hb k c X).sub (h1 b hb k c X)
theorem cellEnergyAtFrame_smul_add (hCE : CellEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a ρ : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) (θ : ℝ) (σ : Fin (chartDimension F) → ℝ) :
    cellEnergyAtFrame true a ρ m Y V (θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0) + σ) =
      cellEnergyAlong a Y (fun x i => interpolatedFrame θ a ρ m (x, i) V) V (chartDirections F) σ := by
  have e1 : θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0) =
      chartCoordinates (fun x i => (0 : imaginaryQuaternions) + θ • frameGap a ρ m (x, i) V)
        (fun _ _ => (0 : imaginaryQuaternions) + θ • (0 : imaginaryQuaternions)) := by
    rw [chartCoordinates_add_smul, chartCoordinates_zero, zero_add]
  have e2 : (fun _ _ => (0 : imaginaryQuaternions) + θ • (0 : imaginaryQuaternions)) =
      (fun (_ : F.Site F.top) (_ : Fin 4) => (0 : imaginaryQuaternions)) := by
    funext y i
    simp
  unfold cellEnergyAtFrame
  rw [e1, e2, (hCE F a Y (fun x i => stepFrame true a ρ m (x, i) V)
    (fun x i => (0 : imaginaryQuaternions) + θ • frameGap a ρ m (x, i) V) V (fun _ _ => 0) hL hs).2 σ]
  have e3 : (fun x i => stepFrame true a ρ m (x, i) V + ((0 : imaginaryQuaternions) + θ • frameGap a ρ m (x, i) V)) =
      fun x i => interpolatedFrame θ a ρ m (x, i) V := by
    funext x i
    simp only [interpolatedFrame, frameGap]
    module
  rw [e3]
theorem analyticAt_cellEnergyAtFrame (hCE : CellEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a ρ : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) (θ : ℝ)
    (hB : AnalyticAt ℝ (cellEnergyAlong a Y (fun x i => interpolatedFrame θ a ρ m (x, i) V) V (chartDirections F)) 0) :
    AnalyticAt ℝ (cellEnergyAtFrame true a ρ m Y V)
      (θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0)) := by
  have e : cellEnergyAtFrame true a ρ m Y V =
      (cellEnergyAlong a Y (fun x i => interpolatedFrame θ a ρ m (x, i) V) V (chartDirections F)) ∘ fun σ =>
        σ - θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0) := by
    funext σ
    have h1 := cellEnergyAtFrame_smul_add hCE hL hs a ρ m Y V θ
      (σ - θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0))
    rw [add_sub_cancel] at h1
    exact h1
  rw [e]
  exact AnalyticAt.comp_of_eq hB (analyticAt_id.sub analyticAt_const) (sub_self _)
theorem cellEnergyAlong_comp (a : ℝ) (Y : F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {N p : ℕ} (q : Fin N → ChartDirection F) (ρ : Fin p → Fin N) :
    cellEnergyAlong a Y w V (q ∘ ρ) = cellEnergyAlong a Y w V q ∘ placementCLM ρ := by
  funext σ
  unfold cellEnergyAlong
  simp only [Function.comp]
  have e1 : (fun x i => w x i + ∑ l, σ l • directionCoordinate (q (ρ l)) x i) =
      fun x i => w x i + ∑ l, placementCLM ρ σ l • directionCoordinate (q l) x i := by
    funext x i
    rw [sum_placementCLM_smul ρ σ (fun n => directionCoordinate (q n) x i)]
  have e2 : (fun y i => ∑ l, σ l • directionMove (q (ρ l)) y i) =
      fun y i => ∑ l, placementCLM ρ σ l • directionMove (q l) y i := by
    funext y i
    rw [sum_placementCLM_smul ρ σ (fun n => directionMove (q n) y i)]
  rw [e1, e2]
theorem iteratedFDeriv_cellEnergyAlong_single (a : ℝ) (Y : F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {N l : ℕ} (q : Fin N → ChartDirection F) (ρ : Fin l → Fin N)
    (hB : AnalyticAt ℝ (cellEnergyAlong a Y w V q) 0) :
    iteratedFDeriv ℝ l (cellEnergyAlong a Y w V q) 0 (fun j => Pi.single (ρ j) 1) =
      cellEnergyKernel a Y w V (q ∘ ρ) := by
  unfold cellEnergyKernel
  rw [cellEnergyAlong_comp, iteratedFDeriv_comp_clm_zero _ _ l hB.contDiffAt]
  simp only [placementCLM_single]
theorem kernel_decay_le_prod (Y : F.Cell) {l : ℕ} (δ₁ β Ckl : ℝ) (hβ0 : 0 ≤ β) (hβ : (l : ℝ) * β ≤ δ₁)
    (hCk : 0 ≤ Ckl) (r : Fin l → Fin (chartDimension F)) :
    Ckl * Real.exp (-(δ₁ * directionReach Y (chartDirections F ∘ r))) ≤
      Ckl * ∏ i, Real.exp (-(β * cellSupDist Y (directionCell (chartDirections F (r i))))) := by
  refine mul_le_mul_of_nonneg_left ?_ hCk
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_neg_distrib, neg_le_neg_iff, ← Finset.mul_sum]
  have hd : ∀ i, cellSupDist Y (directionCell (chartDirections F (r i))) ≤ directionReach Y (chartDirections F ∘ r) :=
    fun i => Finset.le_sup (f := fun l => cellSupDist Y (directionCell ((chartDirections F ∘ r) l))) (Finset.mem_univ i)
  have h2 : ∑ i, (cellSupDist Y (directionCell (chartDirections F (r i))) : ℝ) ≤
      l * directionReach Y (chartDirections F ∘ r) := by
    calc ∑ i, (cellSupDist Y (directionCell (chartDirections F (r i))) : ℝ)
        ≤ ∑ _i : Fin l, (directionReach Y (chartDirections F ∘ r) : ℝ) :=
          Finset.sum_le_sum fun i _ => by exact_mod_cast hd i
      _ = l * directionReach Y (chartDirections F ∘ r) := by simp
  have h3 : (0 : ℝ) ≤ directionReach Y (chartDirections F ∘ r) := by positivity
  calc β * ∑ i, (cellSupDist Y (directionCell (chartDirections F (r i))) : ℝ)
        ≤ β * (l * directionReach Y (chartDirections F ∘ r)) := mul_le_mul_of_nonneg_left h2 hβ0
    _ = ((l : ℝ) * β) * directionReach Y (chartDirections F ∘ r) := by ring
    _ ≤ δ₁ * directionReach Y (chartDirections F ∘ r) := mul_le_mul_of_nonneg_right hβ h3
theorem abs_iteratedFDeriv_le_prod {g : (Fin (chartDimension F) → ℝ) → ℝ} {p : Fin (chartDimension F) → ℝ}
    (a : ℝ) (Y : F.Cell) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hg : (fun z => g (p + z)) = cellEnergyAlong a Y w V (chartDirections F))
    {l : ℕ} (δ₁ β Ckl : ℝ) (hβ0 : 0 ≤ β) (hβ : (l : ℝ) * β ≤ δ₁) (hCk : 0 ≤ Ckl)
    (hB : AnalyticAt ℝ (cellEnergyAlong a Y w V (chartDirections F)) 0)
    (hker : ∀ q : Fin l → ChartDirection F, (∀ j, ‖directionVector (q j)‖ = 1) →
      |cellEnergyKernel a Y w V q| ≤ Ckl * Real.exp (-(δ₁ * directionReach Y q)))
    (r : Fin l → Fin (chartDimension F)) :
    |iteratedFDeriv ℝ l g p (fun i => Pi.single (r i) 1)| ≤
      Ckl * ∏ i, Real.exp (-(β * cellSupDist Y (directionCell (chartDirections F (r i))))) := by
  rw [← iteratedFDeriv_comp_add_left_zero, hg, iteratedFDeriv_cellEnergyAlong_single _ _ _ _ _ _ hB]
  exact (hker _ fun j => norm_directionVector_chartDirections _).trans (kernel_decay_le_prod Y δ₁ β Ckl hβ0 hβ hCk r)
theorem iteratedFDeriv_clm_add_two {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (T : E →L[ℝ] G) (q : ℕ) (x : E) : iteratedFDeriv ℝ (q + 2) T x = 0 := by
  have h : fderiv ℝ T = fun _ => T := by
    funext y
    exact T.fderiv
  rw [iteratedFDeriv_succ_eq_comp_right, h]
  simp only [Function.comp]
  rw [iteratedFDeriv_const_of_ne (by omega)]
  simp only [Pi.zero_apply]
  exact LinearIsometryEquiv.map_zero _
theorem iteratedFDeriv_sub_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k p : ℕ}
    (f : (Fin k → ℝ) → E) (u : E) (hp : p ≠ 0) (hf : ContDiffAt ℝ p f 0) (vs : Fin p → Fin k → ℝ) :
    iteratedFDeriv ℝ p (fun τ => f τ - u) 0 vs = iteratedFDeriv ℝ p f 0 vs := by
  have e : (fun τ => f τ - u) = f + fun _ => -u := by
    funext τ
    simp [sub_eq_add_neg]
  rw [e, iteratedFDeriv_add_apply hf contDiffAt_const, iteratedFDeriv_const_of_ne hp]
  simp
theorem bondListDistance_le_add (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) (Y z : F.Cell) {p : ℕ}
    (e : Fin p → F.Site F.top × Fin 4) : bondListDistance Y e ≤ cellSupDist z Y + bondListDistance z e := by
  refine Finset.sup_le fun l _ => ?_
  have h1 := htri Y z (e l).1
  have h2 : cellSupDist z (e l).1 ≤ bondListDistance z e :=
    Finset.le_sup (f := fun l => cellSupDist z (e l).1) (Finset.mem_univ l)
  rw [hsym Y z] at h1
  omega
theorem chordBonds_subset_fineBonds : chordBonds (finiteCells F) ⊆ fineBonds F := by
  classical
  intro b hb
  unfold chordBonds innerBonds at hb
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
theorem sum_chordBonds_weighted_le (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z)
    (β β₀ M Sg : ℝ) (Y : F.Cell) {p : ℕ} (e : Fin p → F.Site F.top × Fin 4)
    (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (hβ₀ : 0 ≤ β₀) (hM : 0 ≤ M)
    (hSg : ∑ b ∈ fineBonds F, Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) ≤ Sg)
    (hdw : ∀ b ∈ chordBonds (finiteCells F),
      ‖dw b.1 b.2‖ ≤ M * Real.exp (-(β₀ * bondListDistance (enclosingCell b.1) e))) :
    ∑ b : ↥(chordBonds (finiteCells F)), ‖dw b.1.1 b.1.2‖ * Real.exp (-(β * cellSupDist Y (enclosingCell b.1.1))) ≤
      M * Sg * Real.exp (-(β₀ * bondListDistance Y e)) := by
  classical
  have hterm : ∀ b ∈ chordBonds (finiteCells F), ‖dw b.1 b.2‖ * Real.exp (-(β * cellSupDist Y (enclosingCell b.1))) ≤
      M * Real.exp (-(β₀ * bondListDistance Y e)) * Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) := by
    intro b hb
    have h1 := hdw b hb
    have h2 := bondListDistance_le_add hsym htri Y (enclosingCell b.1) e
    have h3 : (bondListDistance Y e : ℝ) ≤ cellSupDist (enclosingCell b.1) Y + bondListDistance (enclosingCell b.1) e := by
      exact_mod_cast h2
    rw [hsym Y]
    calc ‖dw b.1 b.2‖ * Real.exp (-(β * cellSupDist (enclosingCell b.1) Y))
        ≤ M * Real.exp (-(β₀ * bondListDistance (enclosingCell b.1) e)) *
            Real.exp (-(β * cellSupDist (enclosingCell b.1) Y)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = M * (Real.exp (-(β₀ * bondListDistance (enclosingCell b.1) e)) *
            Real.exp (-(β * cellSupDist (enclosingCell b.1) Y))) := by ring
      _ ≤ M * (Real.exp (-(β₀ * bondListDistance Y e)) *
            Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y))) := by
          refine mul_le_mul_of_nonneg_left ?_ hM
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left h3 hβ₀]
      _ = _ := by ring
  have hnn : ∀ b : F.Site F.depth × Fin 4, 0 ≤ M * Real.exp (-(β₀ * bondListDistance Y e)) *
      Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) := fun b => by positivity
  calc ∑ b : ↥(chordBonds (finiteCells F)), ‖dw b.1.1 b.1.2‖ * Real.exp (-(β * cellSupDist Y (enclosingCell b.1.1)))
      = ∑ b ∈ chordBonds (finiteCells F), ‖dw b.1 b.2‖ * Real.exp (-(β * cellSupDist Y (enclosingCell b.1))) :=
        Finset.sum_coe_sort (chordBonds (finiteCells F))
          (fun b => ‖dw b.1 b.2‖ * Real.exp (-(β * cellSupDist Y (enclosingCell b.1))))
    _ ≤ ∑ b ∈ chordBonds (finiteCells F), M * Real.exp (-(β₀ * bondListDistance Y e)) *
        Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) := Finset.sum_le_sum hterm
    _ ≤ ∑ b ∈ fineBonds F, M * Real.exp (-(β₀ * bondListDistance Y e)) *
        Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) :=
        Finset.sum_le_sum_of_subset_of_nonneg chordBonds_subset_fineBonds fun b _ _ => hnn b
    _ = M * Real.exp (-(β₀ * bondListDistance Y e)) *
        ∑ b ∈ fineBonds F, Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) := by
        rw [Finset.mul_sum]
    _ ≤ M * Real.exp (-(β₀ * bondListDistance Y e)) * Sg :=
        mul_le_mul_of_nonneg_left hSg (by positivity)
    _ = _ := by ring
theorem bondSpread_single {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l₀ : Fin k)
    (y : F.Site F.top) (i : Fin 4) :
    bondSpread c X (Pi.single l₀ 1) y i = if c l₀ = (y, i) then X l₀ else 0 := by
  classical
  unfold bondSpread
  rw [Finset.sum_eq_single l₀]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp
theorem sum_innerBonds_top_weighted_le (hs : ∀ i, 2 ≤ F.extent i) (β β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ : β₀ ≤ β)
    (Y : F.Cell) {k p : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (e : Fin p → Fin k) (hp : 0 < p) :
    ∑ b : ↥(innerBonds (finiteCells F) F.top), ‖iteratedFDeriv ℝ p (fun τ : Fin k → ℝ => bondSpread c X τ b.1.1 b.1.2) 0
        (fun l => Pi.single (e l) 1)‖ * Real.exp (-(β * cellSupDist Y b.1.1)) ≤
      Real.exp (-(β₀ * bondListDistance Y (c ∘ e))) := by
  classical
  have hmap : ∀ y i, (fun τ : Fin k → ℝ => bondSpread c X τ y i) = bondSpreadCLM c X y i := fun y i => by
    funext τ
    rw [bondSpreadCLM_apply]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hval : ∀ y i, iteratedFDeriv ℝ (0 + 1) (fun τ : Fin k → ℝ => bondSpread c X τ y i) 0
        (fun l => Pi.single (e l) 1) = if c (e 0) = (y, i) then X (e 0) else 0 := by
      intro y i
      rw [hmap]
      change iteratedFDeriv ℝ 1 (bondSpreadCLM c X y i) 0 (fun l => Pi.single (e l) 1) = _
      rw [iteratedFDeriv_one_apply, (bondSpreadCLM c X y i).fderiv, bondSpreadCLM_apply, bondSpread_single]
    simp only [hval]
    have hb : c (e 0) ∈ innerBonds (finiteCells F) F.top := mem_innerBonds_top hs _
    rw [Finset.sum_eq_single (⟨c (e 0), hb⟩ : ↥(innerBonds (finiteCells F) F.top))]
    · simp only [Prod.mk.eta, if_true, hX (e 0), one_mul]
      apply Real.exp_le_exp.mpr
      have h1 : bondListDistance Y (c ∘ e) = cellSupDist Y (c (e 0)).1 := by
        unfold bondListDistance
        simp [Finset.univ_unique]
      rw [h1]
      have h2 : (0 : ℝ) ≤ cellSupDist Y (c (e 0)).1 := by positivity
      nlinarith
    · intro b _ hne
      have hne' : c (e 0) ≠ (b.1.1, b.1.2) := fun h => hne (Subtype.ext (by simpa using h.symm))
      simp [hne']
    · intro h
      exact absurd (Finset.mem_univ _) h
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hz : ∀ y i, iteratedFDeriv ℝ (q' + 1 + 1) (fun τ : Fin k → ℝ => bondSpread c X τ y i) 0 = 0 := by
      intro y i
      rw [hmap]
      exact iteratedFDeriv_clm_add_two _ _ _
    simp only [hz]
    simp only [ContinuousMultilinearMap.zero_apply, norm_zero, zero_mul, Finset.sum_const_zero]
    exact (Real.exp_pos _).le
theorem weightedNorm_iteratedFDeriv_frameCurve_le (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) (hs : ∀ i, 2 ≤ F.extent i)
    (β β₀ M Sg : ℝ) (hβ₀ : 0 ≤ β₀) (hβ : β₀ ≤ β) (hM : 0 ≤ M) (star : Bool) (a ρ : ℝ) (m : ℕ)
    (V : F.GaugeField F.top) (Y : F.Cell)
    (hSg : ∑ b ∈ fineBonds F, Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) ≤ Sg)
    (hana : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame star a ρ m b) V)
    {k p : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (e : Fin p → Fin k) (hp : 0 < p)
    (hd : ∀ b ∈ chordBonds (finiteCells F), ‖bondDeriv (stepFrame star a ρ m b) V (c ∘ e) (X ∘ e)‖ ≤
      M * Real.exp (-(β₀ * bondListDistance (enclosingCell b.1) (c ∘ e)))) :
    _root_.YangMills.Construction.Calculus.weightedNorm (fun n => Real.exp (-(β * cellSupDist Y (directionCell (chartDirections F n)))))
      (iteratedFDeriv ℝ p (frameCurve star a ρ m V c X) 0 (fun l => Pi.single (e l) 1)) ≤
      3 * (M * Sg + 1) * Real.exp (-(β₀ * bondListDistance Y (c ∘ e))) := by
  have hf : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ
      (fun τ : Fin k → ℝ => stepFrame star a ρ m b (leftTranslate (bondSpread c X τ) V) - stepFrame star a ρ m b V) 0 :=
    fun b hb => (hana b hb k c X).sub analyticAt_const
  have e1 := iteratedFDeriv_chartCoordinates
    (fun x i τ => stepFrame star a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame star a ρ m (x, i) V)
    (fun y i τ => bondSpread c X τ y i) hf (analyticAt_bondSpread c X) (fun l : Fin p => (Pi.single (e l) 1 : Fin k → ℝ))
  unfold frameCurve
  rw [e1]
  refine (weightedNorm_chartCoordinates_le (fun z => Real.exp (-(β * cellSupDist Y z)))
    (fun z => (Real.exp_pos _).le) _ _).trans ?_
  have hdw : ∀ b ∈ chordBonds (finiteCells F), ‖iteratedFDeriv ℝ p (fun τ : Fin k → ℝ =>
      stepFrame star a ρ m (b.1, b.2) (leftTranslate (bondSpread c X τ) V) - stepFrame star a ρ m (b.1, b.2) V) 0
        (fun l => Pi.single (e l) 1)‖ ≤ M * Real.exp (-(β₀ * bondListDistance (enclosingCell b.1) (c ∘ e))) := by
    intro b hb
    have hc : ContDiffAt ℝ p (fun τ : Fin k → ℝ => stepFrame star a ρ m b (leftTranslate (bondSpread c X τ) V)) 0 :=
      (hana b hb k c X).contDiffAt
    rw [iteratedFDeriv_sub_const _ _ (by omega) hc, iteratedFDeriv_single_eq_bondDeriv _ _ _ _ _ hc]
    exact hd b hb
  have h1 := sum_chordBonds_weighted_le hsym htri β β₀ M Sg Y (c ∘ e) (fun x i => iteratedFDeriv ℝ p (fun τ : Fin k → ℝ =>
      stepFrame star a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame star a ρ m (x, i) V) 0
        (fun l => Pi.single (e l) 1)) hβ₀ hM hSg hdw
  have h2 := sum_innerBonds_top_weighted_le hs β β₀ hβ₀ hβ Y c X hX e hp
  have h3 := Real.exp_pos (-(β₀ * bondListDistance Y (c ∘ e)))
  calc _ ≤ 3 * (M * Sg * Real.exp (-(β₀ * bondListDistance Y (c ∘ e))) +
        Real.exp (-(β₀ * bondListDistance Y (c ∘ e)))) := by
        exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
    _ = _ := by ring
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem continuous_leftTranslate_bondSpread {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) (y : F.Site F.top) (i : Fin 4) :
    Continuous fun τ : Fin k → ℝ => leftTranslate (bondSpread c X τ) V y i := by
  unfold leftTranslate bondSpread
  refine (continuous_expUnit.comp ?_).mul continuous_const
  refine continuous_finset_sum _ fun l _ => ?_
  split_ifs
  · exact (continuous_apply l).smul continuous_const
  · exact continuous_const
theorem continuous_plaquetteDefect {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) (p : F.Site F.top × Fin 4 × Fin 4) :
    Continuous fun τ : Fin k → ℝ => plaquetteDefect (leftTranslate (bondSpread c X τ) V) p := by
  have hstep : ∀ (x : F.Site F.top) (st : PathStep), Continuous fun τ : Fin k → ℝ =>
      linkValue (leftTranslate (bondSpread c X τ) V) x st := fun x st => by
    unfold linkValue
    split_ifs
    · exact continuous_leftTranslate_bondSpread c X V _ _
    · exact (continuous_leftTranslate_bondSpread c X V _ _).inv
  have hhol : ∀ (l : List PathStep) (x : F.Site F.top), Continuous fun τ : Fin k → ℝ =>
      pathHolonomy (leftTranslate (bondSpread c X τ) V) x l := by
    intro l
    induction l with
    | nil => intro x; exact continuous_const
    | cons st r ih => intro x; exact (hstep x st).mul (ih _)
  unfold plaquetteDefect plaquetteHolonomy
  exact ((continuous_subtype_val.comp (hhol _ _)).sub continuous_const).norm
theorem eventually_isSmallCurvature {k : ℕ} (hs : ∀ i, 2 ≤ F.extent i) {s : ℝ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top} (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one]
    have := hs i
    omega⟩
  have hfin : Finite F.Cell := by
    have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
      have := hne i
      exact inferInstance
    exact Pi.finite
  have hf : Finite (F.Site F.top × Fin 4 × Fin 4) := inferInstance
  exact show ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ p : F.Site F.top × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      plaquetteDefect (leftTranslate (bondSpread c X τ) V) p < s from by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.2.1 < p.2.2
    · have h1 := hV p hp
      have h2 : plaquetteDefect (leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V) p < s := by
        rw [leftTranslate_bondSpread_zero]
        exact h1
      filter_upwards [(continuous_plaquetteDefect c X V p).continuousAt.eventually_lt continuousAt_const h2]
        with τ hτ _ using hτ
    · exact Filter.Eventually.of_forall fun τ h => absurd h hp
end FrameCurves
end ColdStepAtMirrorFrames
end YangMills.Construction
end
