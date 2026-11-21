import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtANearFlatTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionDensityOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfTheExpansionAtAFlatTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansionProof
import YangMills.Construction.ColdStepAtMirrorFrames.TransportParametersProof
import YangMills.Construction.LawInAState.FamilyAboveTheFrameIsLocal
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfABoundedOperatorFunctionProof
import YangMills.Construction.ResponseInTheExpansion.DerivativesAboveOnTheBalls
import YangMills.Construction.ResponseInTheExpansion.FamilyIsSmoothAboveTheFrame
import YangMills.Construction.ResponseInTheExpansion.FamilyNearAFlatTopForm
import YangMills.Construction.ResponseInTheExpansion.MainTermOfABlockRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ResponseInTheExpansion
namespace BlockRemainderProof
open BlockAverages hiding bondSpread adjointAction
open ColdStepAtMirrorFrames ColdStepAtMirrorFrames.BlockOffsets WeightedResponses LinearResponse
  Estimates Interpolation FrameLocality
variable {F : BlockFrame}
open Classical in
private def supportedOn (F : BlockFrame) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) : LocalFamily :=
  fun F' => if h : F' = F then h ▸ r else fun _ _ => 0
private theorem supportedOn_self (r : F.Site F.depth → F.GaugeField F.depth → ℝ) : supportedOn F r F = r := dif_pos rfl
private theorem supportedOn_of_ne (r : F.Site F.depth → F.GaugeField F.depth → ℝ) {F' : BlockFrame} (h : F' ≠ F) :
    supportedOn F r F' = fun _ _ => 0 := dif_neg h
private theorem decayFactor_pos (L : ℕ) (δ u : ℝ) : 0 < torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
private theorem decayFactor_mono {L : ℕ} {δ u v : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) (hu : 0 ≤ u) (huv : u ≤ v) :
    torusDecayFactor L δ u ≤ torusDecayFactor L δ v := by apply _root_.YangMills.SharedProofs.p54195 <;> assumption
private theorem uniform_smallCurvature {j : ℕ} {σ : ℝ} (hσ : 0 < σ) : IsSmallCurvature σ (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
private theorem expUnit_zero_eq : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem stepCoordinates_zero {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
private theorem coordsAboveFrame_zero (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) :
    coordsAboveFrame true a ρ m V 0 x i = torusCoordinate a ρ (x, i) V := by
  simp [coordsAboveFrame, stepFrame, torusCoordinate, stepCoordinates_zero]
open Classical in
private theorem motionComponent_uniform (a ρ : ℝ) (m : ℕ) (cc : Fin 2 → F.Site F.top × Fin 4)
    (X : Fin 2 → imaginaryQuaternions)
    (α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions) (h0 : ∀ x i, α 0 x i = 0)
    (hC : ∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0)
    (hev : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), fieldAboveFrame true a ρ m (leftTranslate (bondSpread cc X τ) (uniformField F F.top)) 0 =
      leftTranslate (α τ) (uniformField F F.depth))
    (hzero : ∀ b, torusCoordinate a ρ b (uniformField F F.top) = 0)
    (hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    (hdiff : ∀ b ∈ chordBonds (finiteCells F), ∀ l, DifferentiableAt ℝ
      (fun τ : Fin 1 → ℝ => torusCoordinate a ρ b (leftTranslate (bondSpread ![cc l] ![X l] τ) (uniformField F F.top))) 0)
    (l : Fin 2) (x : F.Site F.depth) (i : Fin 4) :
    motionComponent α ![l] x i = bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![cc l] ![X l] +
      (if IsCrossingBond (x, i) ∧ enclosingCell x = (cc l).1 ∧ i = (cc l).2 then X l else 0) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatTopExpansionHessian.motionComponent_first <;> assumption
private def SecondOrderBlockBound (a del Ca : ℝ) (L₀ : ℕ) : Prop :=
  ∀ (F : BlockFrame) (δ σ e e₃ : ℝ) (Y : F.Cell)
    (c : Fin 2 → F.Site F.top × Fin 4) (B : Fin 2 → FormChain F) (W : Fin 2 → LevelForm F F.depth)
    (X : Fin 2 → imaginaryQuaternions)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ), Odd F.blockSide → L₀ ≤ F.blockSide → IsLargeCubicTorus F →
    0 < δ → δ ≤ del / 64 → 0 < σ →
    0 ≤ e → (∀ i, IsFlatChain a (c i) (B i)) → (∀ i, IsAxialResponse (c i) (B i) (W i)) → AreUnitVectors X →
    IsDecayingSiteFamily F.blockSide σ δ e e₃ r →
    |∑ y ∈ blockFineSites Y, mixedDerivAlong (r y) (uniformField F F.depth)
        ![unitForm (W 0) (X 0), unitForm (W 1) (X 1)]| ≤
      Ca * (F.blockSide : ℝ) ^ (50 / 640 : ℝ) * e / torusDecayFactor F.blockSide δ (bondSpan Y c)
private theorem bondDeriv_sub_const (G : F.GaugeField F.depth → ℝ) (a : ℝ) (W : F.GaugeField F.depth)
    (c : Fin 2 → F.Site F.depth × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (hs : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun W' => G W' - a) W c X = bondDeriv G W c X := by
  unfold bondDeriv
  have h := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := 2) (f := fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread c X τ) W))
    (g := fun _ => a) (x := 0) (hs.of_le (by norm_num)) contDiffAt_const
  have e : (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread c X τ) W) - a) =
      (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread c X τ) W)) - fun _ => a := rfl
  rw [e, h, iteratedFDeriv_const_of_ne (by norm_num)]
  simp
private theorem bondDeriv_block_sum {r : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (hsm : ∀ y, ContDiffThreeAlongBonds (r y) (uniformField F F.depth)) (S : Finset (F.Site F.depth))
    (c : Fin 2 → F.Site F.depth × Fin 4) (X : Fin 2 → imaginaryQuaternions) :
    bondDeriv (fun W => ∑ y ∈ S, (r y W - r y (uniformField F F.depth))) (uniformField F F.depth) c X =
      ∑ y ∈ S, bondDeriv (r y) (uniformField F F.depth) c X := by
  have hs : ∀ y ∈ S, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun τ : Fin 2 → ℝ =>
      r y (leftTranslate (bondSpread c X τ) (uniformField F F.depth)) - r y (uniformField F F.depth)) 0 := by
    intro y _
    exact ((hsm y 2 c X).sub contDiffAt_const).of_le (by norm_num)
  have h := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (f := fun y => fun τ : Fin 2 → ℝ =>
    r y (leftTranslate (bondSpread c X τ) (uniformField F F.depth)) - r y (uniformField F F.depth)) (u := S) (n := 2)
    (x := 0) hs
  have e2 : bondDeriv (fun W => ∑ y ∈ S, (r y W - r y (uniformField F F.depth))) (uniformField F F.depth) c X =
      ∑ y ∈ S, bondDeriv (fun W => r y W - r y (uniformField F F.depth)) (uniformField F F.depth) c X := by
    unfold bondDeriv
    rw [h, ContinuousMultilinearMap.sum_apply]
  rw [e2]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact bondDeriv_sub_const (r y) _ _ c X (hsm y 2 c X)
private theorem iteratedFDeriv_one_linear (p q : imaginaryQuaternions) (l : Fin 2) :
    iteratedFDeriv ℝ 1 (fun τ : Fin 2 → ℝ => τ 0 • p + τ 1 • q) 0 (fun _ : Fin 1 => (Pi.single l 1 : Fin 2 → ℝ)) =
      (Pi.single l 1 : Fin 2 → ℝ) 0 • p + (Pi.single l 1 : Fin 2 → ℝ) 1 • q := by
  let Λ : (Fin 2 → ℝ) →L[ℝ] imaginaryQuaternions :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight p +
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight q
  have e : (fun τ : Fin 2 → ℝ => τ 0 • p + τ 1 • q) = Λ := by
    funext τ
    simp [Λ]
  rw [e, iteratedFDeriv_one_apply, Λ.fderiv]
  simp [Λ]
private theorem mixedDerivAlong_eq_sum (hA : SecondOrderAlongMotionFormula) {G : F.GaugeField F.depth → ℝ}
    {T : Finset (F.Site F.depth × Fin 4)}
    (hT : ∀ b, b ∈ T) (hG : ContDiffThreeAlongBonds G (uniformField F F.depth))
    (hN : ∀ (c : Fin 1 → F.Site F.depth × Fin 4) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X →
      bondDeriv G (uniformField F F.depth) c X = 0)
    (u₀ u₁ : LevelForm F F.depth) (X₀ X₁ : imaginaryQuaternions) :
    mixedDerivAlong G (uniformField F F.depth) ![unitForm u₀ X₀, unitForm u₁ X₁] =
      ∑ b ∈ T, ∑ b' ∈ T, bondDeriv G (uniformField F F.depth) ![b, b'] ![X₀, X₁] * u₀ b.1 b.2 * u₁ b'.1 b'.2 := by
  set α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun τ x i => τ 0 • (u₀ x i • X₀) + τ 1 • (u₁ x i • X₁) with hα
  have hC : ∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0 := by
    intro x i
    have h0 : ContDiff ℝ 3 (fun τ : Fin 2 → ℝ => τ 0) := contDiff_apply ℝ ℝ 0
    have h1 : ContDiff ℝ 3 (fun τ : Fin 2 → ℝ => τ 1) := contDiff_apply ℝ ℝ 1
    exact (h0.smul contDiff_const).add (h1.smul contDiff_const) |>.contDiffAt
  have hp0 : ∀ x i, motionComponent α ![0] x i = u₀ x i • X₀ := by
    intro x i
    have := iteratedFDeriv_one_linear (u₀ x i • X₀) (u₁ x i • X₁) 0
    simpa [motionComponent, hα] using this
  have hp1 : ∀ x i, motionComponent α ![1] x i = u₁ x i • X₁ := by
    intro x i
    have := iteratedFDeriv_one_linear (u₀ x i • X₀) (u₁ x i • X₁) 1
    simpa [motionComponent, hα] using this
  have h := hA F F.depth T G (uniformField F F.depth) α u₀ u₁ X₀ X₁ hT hG hN (fun x i => by simp [hα]) hC hp0 hp1
  rw [← h]
  unfold mixedDerivAlong
  have e1 : (fun τ : Fin 2 → ℝ => G (leftTranslate (fun x b => ∑ l, τ l •
      (![unitForm u₀ X₀, unitForm u₁ X₁] : Fin 2 → _) l x b) (uniformField F F.depth))) =
      fun τ => G (leftTranslate (α τ) (uniformField F F.depth)) := by
    funext τ
    congr 2
    funext x b
    simp [hα, Fin.sum_univ_two, unitForm]
  have e3 : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
    funext l
    fin_cases l <;> rfl
  rw [e1, e3]
set_option maxHeartbeats 4000000 in
private theorem uniform_block_second_order (hA : SecondOrderAlongMotionFormula) (hN : FirstDerivVanishesAtUniform)
    (hSc : FlatCoordinatesScalar) (hFc : AxialResponseOfMinimizers)
    (hM : motionAboveFrameStatement) (hS : SiteDecomposition) {a del Ca : ℝ} {L₁ : ℕ} (ha : 1 ≤ a)
    (hsum : SecondOrderBlockBound a del Ca L₁) {L : ℕ} (hodd : Odd L) (hL₁ : L₁ ≤ L) (hL1 : 1 ≤ L)
    {c : ColdChainParameters}
    (hc : c.Admissible a L) {σ δ E E₃ : ℝ} {n₀ t m : ℕ} {f : LocalFamily} {F : BlockFrame} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδd : δ ≤ del / 64) (hE : 0 ≤ E) (hn₀ : 64 + 2 * L + 3 ≤ n₀) (hrow : IsRegularOnTorus L t n₀ σ δ E E₃ f F)
    (hF : IsCubicTopTorus L t n₀ F) (Y : F.Cell) (cc : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (hX : AreUnitVectors X) :
    |bondDeriv (cellCentredExpansion true a c.ρA m f Y 0) (uniformField F F.top) cc X| ≤
      Ca * (L : ℝ) ^ (50 / 640 : ℝ) * E / torusDecayFactor L δ (bondSpan Y cc) := by
  classical
  obtain ⟨hFL, hFt, n, hside, hn⟩ := id hF
  subst hFL
  subst hFt
  have hcub : IsLargeCubicTorus F := ⟨n, by omega, hside⟩
  have hchainT : IsBlockTorus F.blockSide F := ⟨rfl, hcub⟩
  have hlow : IsCubicTorusAbove F.blockSide F.depth n₀ F :=
    ⟨rfl, rfl, n, hside, hn.trans (Nat.le_mul_of_pos_right n hL1)⟩
  have hper : ∀ i, 2 * F.blockSide ^ 2 + 2 < F.period F.depth i := by
    intro i
    rw [period_depth, hside i]
    have h1 : 2 * F.blockSide + 3 ≤ n := by omega
    nlinarith
  have hper0 : ∀ i, F.period F.depth i ≠ 0 := fun i => by have := hper i; omega
  have hside2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hcover : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth := by
    intro x
    obtain ⟨-, h2, -⟩ := hS F hodd hside2
    obtain ⟨e, hcu⟩ := h2 x
    refine mem_sitesOfCells.2 ⟨enclosingCell x, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hside2 _, cellOffset x, ?_, e.symm⟩
    rw [top_sub_depth, pow_one]
    exact hcu
  have hT : ∀ b : F.Site F.depth × Fin 4, b ∈ fineBonds F := fun b =>
    Finset.mem_product.2 ⟨hcover _, Finset.mem_univ _⟩
  have hchart : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd =>
    Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hcover _, Finset.mem_univ _⟩, hcover _⟩, hd⟩
  obtain ⟨-, -, -, hσA, -⟩ := hc.positivity
  obtain ⟨⟨-, -, hs₀, hδ₂, hκ₂, -, -, hKk⟩, hcl⟩ := hc.classical
  have hCl := hc.estimates F c.σA (uniformField F F.top) hchainT hσA le_rfl (uniform_smallCurvature hσA)
  have hdec := (hcl F c.s₀ (uniformField F F.top) hchainT hs₀ le_rfl (uniform_smallCurvature hs₀)).2.2.1
  have hzero : ∀ b, torusCoordinate a c.ρA b (uniformField F F.top) = 0 := fun b =>
    (hSc a F.blockSide c hodd hc F b (cc 0) (X 0) hchainT (hX 0)).1
  have hbetween : ∀ d : F.Site F.depth × Fin 4, interpolatedFrame 0 a c.ρA m d = torusCoordinate a c.ρA d := by
    intro d
    funext V
    simp [interpolatedFrame, stepFrame, torusCoordinate]
  obtain ⟨M, -, hMall⟩ := hM 3 c.Kk fun k => (hKk k).le
  have hκ0 : 0 ≤ c.κ₂ := by
    have : 0 < (2 : ℝ) ^ 6 * c.δ₂ := by positivity
    linarith
  obtain ⟨α, h0, hC, -, hev, -⟩ := hMall F 0 a c.ρA c.κ₂ m 2 (uniformField F F.top) 0
    (fun l => Perturbation.top (cc l) (X l)) hper0 hκ0
    hchart
    (by
      intro x i _
      have e : interpolatedCoords 0 a c.ρA m (uniformField F F.top) (0 : StepVariable (finiteCells F)) x i = 0 := by
        unfold interpolatedCoords
        rw [hbetween, hzero, stepCoordinates_zero, add_zero]
      rw [e, norm_zero]
      exact zero_le_one)
    (by
      intro d hd
      rw [hbetween]
      exact (hCl.coordinates d hd).1)
    (by
      intro d hd k c' X' hk hX'
      rw [hbetween]
      exact hdec d hd k c' X' hk hX')
    (fun l => hX l)
  have hf0 : ∀ V : F.GaugeField F.top, interpolatedField 0 a c.ρA m V (0 : StepVariable (finiteCells F)) =
      fieldAboveFrame true a c.ρA m V 0 := by
    intro V
    unfold interpolatedField fieldAboveFrame
    congr 1
    funext x i
    rw [coordsAboveFrame_zero]
    unfold interpolatedCoords
    rw [hbetween, stepCoordinates_zero, add_zero]
  have hflat : fieldAboveFrame true a c.ρA m (uniformField F F.top) (0 : StepVariable (finiteCells F)) =
      uniformField F F.depth := by
    funext x i
    unfold fieldAboveFrame chartedField
    simp only [coordsAboveFrame_zero, hzero, expUnit_zero_eq]
    split_ifs <;> simp [uniformField]
  have hmv : ∀ τ : Fin 2 → ℝ, perturbedVariable (0 : StepVariable (finiteCells F))
      (fun l => Perturbation.top (cc l) (X l)) τ = 0 := by
    intro τ
    simp [perturbedVariable, Perturbation.variableDirection]
  have hev' : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ),
      fieldAboveFrame true a c.ρA m (leftTranslate (bondSpread cc X τ) (uniformField F F.top)) 0 =
      leftTranslate (α τ) (uniformField F F.depth) := by
    filter_upwards [hev] with τ h
    rw [hmv, hf0, hf0, hflat] at h
    exact h
  have hdiff : ∀ b ∈ chordBonds (finiteCells F), ∀ l, DifferentiableAt ℝ
      (fun τ : Fin 1 → ℝ => torusCoordinate a c.ρA b (leftTranslate (bondSpread ![cc l] ![X l] τ) (uniformField F F.top)))
      0 :=
    fun b hb l => ((hCl.coordinates b hb).1 1 ![cc l] ![X l]).differentiableAt
  have hu : ∀ l x i, motionComponent α ![l] x i = minimizerResponse a c.ρA (cc l) (X l) x i • X l := by
    intro l x i
    rw [motionComponent_uniform a c.ρA m cc X α h0 hC hev' hzero hchart hdiff l x i]
    unfold minimizerResponse
    rw [add_smul, ← (hSc a F.blockSide c hodd hc F (x, i) (cc l) (X l) hchainT (hX l)).2]
    congr 1
    split_ifs <;> simp
  have hsm : ∀ y, ContDiffThreeAlongBonds (f F y) (uniformField F F.depth) := fun y =>
    hrow.smooth hlow y _ (uniform_smallCurvature hσ)
  have hGs : ContDiffThreeAlongBonds (fun W => ∑ y ∈ blockFineSites Y, (f F y W - f F y (uniformField F F.depth)))
      (uniformField F F.depth) := by
    intro k c' X'
    refine ContDiffAt.sum fun y _ => ?_
    exact (hsm y k c' X').sub contDiffAt_const
  have hinv : ∀ (W : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W →
      (fun W => ∑ y ∈ blockFineSites Y, (f F y W - f F y (uniformField F F.depth))) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ W) =
        (fun W => ∑ y ∈ blockFineSites Y, (f F y W - f F y (uniformField F F.depth))) W := by
    intro W γ hW
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hrow.gauge_invariant hlow y W γ hW]
  have hmain := hA F F.depth (fineBonds F)
    (fun W => ∑ y ∈ blockFineSites Y, (f F y W - f F y (uniformField F F.depth))) (uniformField F F.depth) α
    (minimizerResponse a c.ρA (cc 0) (X 0)) (minimizerResponse a c.ρA (cc 1) (X 1)) (X 0) (X 1) hT hGs
    (fun c' X' hX' => hN F F.depth _ σ c' X' hσ hinv hX') h0 hC (hu 0) (hu 1)
  have hleft : bondDeriv (cellCentredExpansion true a c.ρA m f Y 0) (uniformField F F.top) cc X =
      iteratedFDeriv ℝ 2 (fun τ => (fun W => ∑ y ∈ blockFineSites Y, (f F y W - f F y (uniformField F F.depth)))
        (leftTranslate (α τ) (uniformField F F.depth))) 0 ![Pi.single 0 1, Pi.single 1 1] := by
    have e1 : (fun τ => cellCentredExpansion true a c.ρA m f Y 0 (leftTranslate (bondSpread cc X τ) (uniformField F F.top)))
        =ᶠ[𝓝 0] fun τ => (fun W => ∑ y ∈ blockFineSites Y, (f F y W - f F y (uniformField F F.depth)))
          (leftTranslate (α τ) (uniformField F F.depth)) := by
      filter_upwards [hev'] with τ h
      show ∑ y ∈ blockFineSites Y, subtractTrivial f F y (fieldAboveFrame true a c.ρA m _ 0) = _
      rw [h]
      rfl
    have e2 := (Filter.EventuallyEq.iteratedFDeriv ℝ e1 2).eq_of_nhds
    have e3 : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
      funext l
      fin_cases l <;> rfl
    unfold bondDeriv
    rw [e2, e3]
  rw [hleft, hmain]
  choose B hBf hBt using fun l => hFc a ha F.blockSide hodd c hc F (cc l) (X l) rfl hcub (hX l)
  have hfam : IsDecayingSiteFamily F.blockSide σ δ E E₃ (f F) :=
    ⟨hrow.smooth hlow, hrow.gauge_invariant hlow, hrow.decay hlow⟩
  have hfin := hsum F δ σ E E₃ Y cc B (fun l => minimizerResponse a c.ρA (cc l) (X l)) X (f F) hodd hL₁ hcub hδ hδd
    hσ hE hBf hBt hX hfam
  have hslot : ∀ y, mixedDerivAlong (f F y) (uniformField F F.depth)
      ![unitForm (minimizerResponse a c.ρA (cc 0) (X 0)) (X 0),
        unitForm (minimizerResponse a c.ρA (cc 1) (X 1)) (X 1)] =
      ∑ b ∈ fineBonds F, ∑ b' ∈ fineBonds F, bondDeriv (f F y) (uniformField F F.depth) ![b, b'] ![X 0, X 1] *
        minimizerResponse a c.ρA (cc 0) (X 0) b.1 b.2 * minimizerResponse a c.ρA (cc 1) (X 1) b'.1 b'.2 := fun y =>
    mixedDerivAlong_eq_sum hA hT (hsm y) (fun c' X' hX' => hN F F.depth (f F y) σ c' X' hσ
      (fun W γ hW => hrow.gauge_invariant hlow y W γ hW) hX') _ _ _ _
  have hswap : ∑ b ∈ fineBonds F, ∑ b' ∈ fineBonds F,
      bondDeriv (fun W => ∑ y ∈ blockFineSites Y, (f F y W - f F y (uniformField F F.depth))) (uniformField F F.depth)
        ![b, b'] ![X 0, X 1] *
        minimizerResponse a c.ρA (cc 0) (X 0) b.1 b.2 * minimizerResponse a c.ρA (cc 1) (X 1) b'.1 b'.2 =
      ∑ y ∈ blockFineSites Y, mixedDerivAlong (f F y) (uniformField F F.depth)
        ![unitForm (minimizerResponse a c.ρA (cc 0) (X 0)) (X 0),
          unitForm (minimizerResponse a c.ρA (cc 1) (X 1)) (X 1)] := by
    simp only [hslot]
    calc _ = ∑ b ∈ fineBonds F, ∑ b' ∈ fineBonds F, ∑ y ∈ blockFineSites Y,
          bondDeriv (f F y) (uniformField F F.depth) ![b, b'] ![X 0, X 1] *
            minimizerResponse a c.ρA (cc 0) (X 0) b.1 b.2 *
            minimizerResponse a c.ρA (cc 1) (X 1) b'.1 b'.2 := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
          rw [bondDeriv_block_sum hsm, Finset.sum_mul, Finset.sum_mul]
      _ = ∑ b ∈ fineBonds F, ∑ y ∈ blockFineSites Y, ∑ b' ∈ fineBonds F,
          bondDeriv (f F y) (uniformField F F.depth) ![b, b'] ![X 0, X 1] *
            minimizerResponse a c.ρA (cc 0) (X 0) b.1 b.2 *
            minimizerResponse a c.ρA (cc 1) (X 1) b'.1 b'.2 :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  exact hfin
private def UniformGainAt (T : StepParameters) : Prop :=
  ∀ (t m : ℕ) (f : LocalFamily) (F : BlockFrame),
    IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f F →
    IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (c : Fin 2 → F.Site F.top × Fin 4)
      (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv (cellCentredExpansion true T.a T.chainParams.ρA m f Y 0) (uniformField F F.top) c X| ≤
        2⁻¹ ^ 8 * ((T.L : ℝ) * T.E) / torusDecayFactor T.L T.decayRate (bondSpan Y c)
private theorem rpow_mul_le_side {Ca : ℝ} {L : ℕ} (hCa : 0 ≤ Ca) (hL : 1 ≤ L) (h : (2 ^ 8 * Ca) ^ 2 ≤ L) :
    Ca * (L : ℝ) ^ (50 / 640 : ℝ) ≤ 2⁻¹ ^ 8 * (L : ℝ) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have h1 : 2 ^ 8 * Ca ≤ (L : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le h
  have h2 : (L : ℝ) ^ (50 / 640 : ℝ) * (L : ℝ) ^ (1 / 2 : ℝ) ≤ (L : ℝ) := by
    rw [← Real.rpow_add hL0]
    calc (L : ℝ) ^ (50 / 640 + 1 / 2 : ℝ) ≤ (L : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLr (by norm_num)
      _ = L := Real.rpow_one _
  have hp : 0 ≤ (L : ℝ) ^ (50 / 640 : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 hp
  nlinarith
private theorem uniformGain_eventually (hA : SecondOrderAlongMotionFormula) (hN : FirstDerivVanishesAtUniform)
    (hSc : FlatCoordinatesScalar) (hFc : AxialResponseOfMinimizers)
    (hM : motionAboveFrameStatement) (hS : SiteDecomposition) (h1 : BlockSecondDerivativeBound) :
    EventuallyInParameters UniformGainAt := by
  intro a ha
  obtain ⟨del, Ca, hdel, hCa, L₁, hsum⟩ := h1 a ha
  refine ⟨max (max L₁ 1) ⌈(2 ^ 8 * Ca) ^ 2⌉₊, fun L hodd hL c hc => ?_⟩
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLC : (2 ^ 8 * Ca) ^ 2 ≤ L := by
    have h2 : ⌈(2 ^ 8 * Ca) ^ 2⌉₊ ≤ L := (le_max_right _ _).trans hL
    exact (Nat.le_ceil _).trans (by exact_mod_cast h2)
  refine ⟨0, fun Ct _ => ⟨16 * del, mul_pos (by norm_num) hdel, fun κ hκ hκ0 => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨1, one_pos, fun σ hσ _ p _ => ⟨0, fun Cs _ E hE => ⟨64 + 2 * L + 3, fun n₀ hn₀ =>
      ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩
  intro t m f F hrow hF Y cc X hX
  have hδ : 0 < κ / 2 ^ 10 := by positivity
  have hδd : κ / 2 ^ 10 ≤ del / 64 := by
    norm_num
    linarith
  have hE0 : (0 : ℝ) ≤ E := by linarith
  refine (uniform_block_second_order hA hN hSc hFc hM hS ha hsum hodd hL₁ hL1 hc hσ hδ hδd hE0 hn₀ hrow hF Y cc X
    hX).trans ?_
  have hp := rpow_mul_le_side hCa.le hL1 hLC
  have hG : 0 < torusDecayFactor L (κ / 2 ^ 10) (bondSpan Y cc) := decayFactor_pos _ _ _
  refine div_le_div_of_nonneg_right ?_ hG.le
  calc Ca * (L : ℝ) ^ (50 / 640 : ℝ) * E ≤ 2⁻¹ ^ 8 * (L : ℝ) * E := mul_le_mul_of_nonneg_right hp hE0
    _ = 2⁻¹ ^ 8 * ((L : ℝ) * E) := by ring
private theorem bondListDistance_le_bondSpan {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    bondListDistance Y c ≤ bondSpan Y c := le_max_left _ _
private theorem bondDeriv_zero {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
private theorem axialGaugeRotated_units {k : ℕ} (V : F.GaugeField F.top) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) : AreUnitVectors (axialGaugeRotated V Y c X) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.axialGaugeRotated_areUnitVectors <;> assumption
private theorem far_constant_bound {Ct A Gn E : ℝ} (h : 2 ^ 10 * Ct * Gn * A ≤ 1) (hG : 0 < Gn) (hE : 0 ≤ E) :
    Ct * E * A ≤ 2⁻¹ ^ 10 * E / Gn := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.far_tail_bound <;> assumption
private theorem axialGaugeRotated_agree {F' : BlockFrame} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r k : ℕ}
    (hag : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hs : ∀ i, 2 * r + 2 < F.extent i) (hs' : ∀ i, 2 * r + 2 < F'.extent i)
    (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions) (hb : ∀ l, BondWithinRadius r (h l)) :
    axialGaugeRotated V Y (bondsAt Y h) X = axialGaugeRotated V' Y' (bondsAt Y' h) X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.axialGaugeRotated_eq_of_agree <;> assumption
private theorem bondListDistance_le_of_within {r k : ℕ} (Y : F.Cell) (hs : ∀ i, 2 * r + 2 < F.extent i)
    (h : Fin k → (Fin 4 → ℤ) × Fin 4) (hb : ∀ l, BondWithinRadius r (h l)) :
    bondListDistance Y (bondsAt Y h) ≤ r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.bondListDistance_bondsAt_le <;> assumption
section
open Filter
private theorem tails_tendsto_zero {δ b A : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.exp (-(δ * x)) + (1 + A * x ^ 16000) * Real.exp (-(b * x))) atTop (𝓝 0) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TransportConditions.tendsto_exp_tails_atTop <;> assumption
private theorem decay_tail_bound {L : ℕ} {δ κ : ℝ} (hL : 32 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ κ) (n : ℕ) :
    torusDecayFactor L δ n * (1 / torusDecayFactor L δ ((L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * κ * n))) ≤
      Real.exp (-(δ * n)) + (1 + (1 / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 * (n : ℝ) ^ 16000) * Real.exp (-(κ * n)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TransportConditions.torusDecayFactor_mul_tails_le <;> assumption
end
open Classical in
private theorem block_card_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) :
    ((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card ≤ F.blockSide ^ 4 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.card_block_le <;> assumption
private theorem bondDeriv_add_const {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W : F.GaugeField j)
    (c : Fin (k + 1) → F.Site j × Fin 4) (X : Fin (k + 1) → imaginaryQuaternions) :
    bondDeriv (fun W' => G W' + a) W c X = bondDeriv G W c X := by
  unfold bondDeriv
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  have : (fderiv ℝ fun τ : Fin (k + 1) → ℝ => G (leftTranslate (bondSpread c X τ) W) + a) =
      fderiv ℝ fun τ : Fin (k + 1) → ℝ => G (leftTranslate (bondSpread c X τ) W) := by
    funext τ
    exact fderiv_add_const _
  simp only [Function.comp, this]
abbrev _root_.YangMills.SharedProofs.p46198 := @bondDeriv_add_const
private theorem bondDeriv_const_mul {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (h : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun W' => a * G W') W c X = a * bondDeriv G W c X := by
  unfold bondDeriv
  have e := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := a) h
  have e' : (fun τ : Fin k → ℝ => a * G (leftTranslate (bondSpread c X τ) W)) =
      a • fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W) := by
    funext τ
    simp [smul_eq_mul]
  rw [e', e]
  simp
private def scaledBy (b : ℝ) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) :
    F.Site F.depth → F.GaugeField F.depth → ℝ := fun y W => b * r y W
private theorem decaying_of_remainder {L : ℕ} {σ δ e E η₃ : ℝ} {r : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (he : 0 < e) (hE : 0 < E) (hη : 0 < η₃) (hr : IsTorusRemainder L σ δ e (e / η₃) r) :
    IsDecayingSiteFamily L σ δ E (E / η₃) (scaledBy (E / e) r) := by
  refine ⟨fun y W hW k c X => contDiffAt_const.mul (hr.decaying.smooth y W hW k c X), fun y W γ hW => ?_,
    fun y W k c X hW h1 h3 hX => ?_⟩
  · simp only [scaledBy]
    rw [hr.decaying.gauge_invariant y W γ hW]
  · have hs := hr.decaying.smooth y W hW k c X
    have hb := hr.decaying.decay y W k c X hW h1 h3 hX
    have hG := decayFactor_pos L δ (bondSpan y c)
    show |bondDeriv (fun W' => E / e * r y W') W c X| ≤ _
    rw [bondDeriv_const_mul _ _ _ _ _ (hs.of_le (by exact_mod_cast h3)), abs_mul, abs_of_pos (div_pos hE he)]
    calc E / e * |bondDeriv (r y) W c X| ≤
          E / e * ((if k = 3 then e / η₃ else e) / torusDecayFactor L δ (bondSpan y c)) :=
          mul_le_mul_of_nonneg_left hb (div_pos hE he).le
      _ = _ := by
          split_ifs <;> field_simp
private theorem regular_of_remainder {L t n₀ : ℕ} {σ δ e E η₃ : ℝ} {r : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (he : 0 < e) (hE : 0 < E) (hη : 0 < η₃) (hr : IsTorusRemainder L σ δ e (e / η₃) r) :
    IsRegularOnTorus L t n₀ σ δ E (E / η₃) (supportedOn F (scaledBy (E / e) r)) F := by
  have hfam := decaying_of_remainder he hE hη hr
  refine ⟨fun _ y W hW => ?_, fun _ y W γ hW => ?_, fun _ y W k c X hW h1 h3 hX => ?_,
    fun _ y W W' m k h X hW hW' hag hk hb hX => ?_⟩
  · rw [supportedOn_self]
    exact hfam.smooth y W hW
  · rw [supportedOn_self]
    exact hfam.gauge_invariant y W γ hW
  · rw [supportedOn_self]
    exact hfam.decay y W k c X hW h1 h3 hX
  · have hc : subtractTrivial (supportedOn F (scaledBy (E / e) r)) F y = fun W => E / e * remainderHat r y W := by
      funext U
      simp only [subtractTrivial, supportedOn_self, scaledBy, remainderHat]
      rw [show uniformField F F.depth = (fun _ _ => 1 : F.GaugeField F.depth) from rfl]
      ring
    have hsm : ∀ U : F.GaugeField F.depth, IsSmallCurvature σ U →
        ContDiffAt ℝ k (fun τ : Fin k → ℝ => remainderHat r y (leftTranslate (bondSpread (bondsAt y h) X τ) U)) 0 :=
      fun U hU =>
      ((hr.decaying.smooth y U hU k (bondsAt y h) X).sub contDiffAt_const).of_le (by
        exact_mod_cast (by omega : k ≤ 3))
    have hG := decayFactor_pos L δ (m : ℝ)
    rw [hc, bondDeriv_const_mul _ _ _ _ _ (hsm W hW), bondDeriv_const_mul _ _ _ _ _ (hsm W' hW'), ← mul_sub, abs_mul,
      abs_of_pos (div_pos hE he)]
    calc E / e * |bondDeriv (remainderHat r y) W (bondsAt y h) X - bondDeriv (remainderHat r y) W' (bondsAt y h) X|
        ≤ E / e * (e / torusDecayFactor L δ m) :=
          mul_le_mul_of_nonneg_left (hr.agreement y W W' m k h X hW hW' hag hk hb hX) (div_pos hE he).le
      _ = E / torusDecayFactor L δ m := by field_simp
private theorem boundedDerivatives_of_decaying {L t n₀ : ℕ} {σ δ E E₃ : ℝ}
    {r : F.Site F.depth → F.GaugeField F.depth → ℝ} (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃)
    (hf : IsDecayingSiteFamily L σ δ E E₃ r) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then E₃ else E) (supportedOn F r) := by
  refine ⟨fun F' _ y W hW j c X => ?_, fun F' _ y W γ hW => ?_, fun F' _ y W j c X hW h1 h3 hX => ?_⟩
  · by_cases h : F' = F
    · subst h
      rw [supportedOn_self]
      exact_mod_cast hf.smooth y W hW j c X
    · rw [supportedOn_of_ne r h]
      exact contDiffAt_const
  · by_cases h : F' = F
    · subst h
      rw [supportedOn_self]
      exact hf.gauge_invariant y W γ hW
    · rw [supportedOn_of_ne r h]
  · by_cases h : F' = F
    · subst h
      rw [supportedOn_self]
      exact hf.decay y W j c X hW h1 h3 hX
    · rw [supportedOn_of_ne r h]
      have h0 : bondDeriv (fun _ : F'.GaugeField F'.depth => (0 : ℝ)) W c X = 0 := by
        simp [bondDeriv]
      simp only [h0, abs_zero]
      refine div_nonneg ?_ (decayFactor_pos _ _ _).le
      split_ifs
      · exact hE₃
      · exact hE
private theorem interpolatedField_one (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    interpolatedField 1 a ρA m V η = fieldAboveFrame false a ρA m V η := by
  have h1 : interpolatedCoords 1 a ρA m V η = coordsAboveFrame false a ρA m V η := by
    funext z i
    simp [interpolatedCoords, coordsAboveFrame, interpolatedFrame]
  simp only [interpolatedField, fieldAboveFrame, h1]
abbrev _root_.YangMills.SharedProofs.p24311 := @interpolatedField_one
private theorem interpolatedExpansion_one (a ρA : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    interpolatedExpansion 1 a ρA m f y η V = centredExpansion false a ρA m f y η V := by
  simp only [interpolatedExpansion, centredExpansion, interpolatedField_one]
abbrev _root_.YangMills.SharedProofs.p6614 := @interpolatedExpansion_one
open Classical in
private def uniformBlockSum (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell) : ℝ :=
  ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y), r y (uniformField F F.depth)
private theorem blockSum_eq (Q : ColdHalfLaw) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) {b : ℝ} (hb : b ≠ 0)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    Q.blockSum r Y η V = b⁻¹ * cellCentredExpansion false Q.a Q.chartRadius Q.mirrorRadius (supportedOn F (scaledBy b r)) Y η V +
      uniformBlockSum r Y := by
  unfold ColdHalfLaw.blockSum cellCentredExpansion uniformBlockSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [ColdHalfLaw.liftedExpansion, centredExpansion, subtractTrivial, supportedOn_self, scaledBy, interpolatedField_one]
  field_simp
  ring
private theorem bondDeriv_blockSum (Q : ColdHalfLaw) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) {b : ℝ}
    (hb : b ≠ 0) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hsm : ContDiffAt ℝ k (fun τ : Fin k → ℝ => cellCentredExpansion false Q.a Q.chartRadius Q.mirrorRadius
      (supportedOn F (scaledBy b r)) Y η (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv (Q.blockSum r Y η) V c X =
      b⁻¹ * bondDeriv (cellCentredExpansion false Q.a Q.chartRadius Q.mirrorRadius (supportedOn F (scaledBy b r)) Y η) V c X +
        (if k = 0 then uniformBlockSum r Y else 0) := by
  have e : Q.blockSum r Y η = fun V' =>
      b⁻¹ * cellCentredExpansion false Q.a Q.chartRadius Q.mirrorRadius (supportedOn F (scaledBy b r)) Y η V' +
        uniformBlockSum r Y := by
    funext V'
    exact blockSum_eq Q r hb Y η V'
  rw [e]
  cases k with
  | zero =>
    rw [bondDeriv_zero, bondDeriv_zero]
    simp
  | succ k =>
    rw [bondDeriv_add_const (fun V' => b⁻¹ * cellCentredExpansion false Q.a Q.chartRadius Q.mirrorRadius
        (supportedOn F (scaledBy b r)) Y η V'),
      bondDeriv_const_mul _ _ _ _ _ hsm]
    simp
private theorem bound_on_closedBall {ρ B : ℝ} (hρ : 0 < ρ) {φ : StepVariable (finiteCells F) → ℝ}
    {η : StepVariable (finiteCells F)}
    (hη : ∀ b, ‖η b‖ ≤ ρ) (hc : ContinuousAt φ η)
    (hb : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ < ρ) → |φ ζ| ≤ B) :
    |φ η| ≤ B := by
  have ht : Filter.Tendsto (fun s : ℝ => s • η) (𝓝[<] 1) (𝓝 η) := by
    have hcs : Continuous (fun s : ℝ => s • η) := continuous_id.smul continuous_const
    have h := hcs.tendsto 1
    simp only [one_smul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun s : ℝ => |φ (s • η)|) (𝓝[<] 1) (𝓝 |φ η|) := (hc.tendsto.comp ht).abs
  refine le_of_tendsto h2 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
  refine hb _ fun b => ?_
  have e : ‖(s • η) b‖ = s * ‖η b‖ := by
    simp [norm_smul, abs_of_pos hs.1]
  rw [e]
  calc s * ‖η b‖ ≤ s * ρ := mul_le_mul_of_nonneg_left (hη b) hs.1.le
    _ < 1 * ρ := mul_lt_mul_of_pos_right hs.2 hρ
    _ = ρ := one_mul _
private theorem le_of_pos_limit {A : ℝ} {b : ℝ → ℝ} (hb : Continuous b) (h : ∀ ε, 0 < ε → A ≤ b ε) : A ≤ b 0 := by apply _root_.YangMills.Construction.PeriodicOperators.CauchyTaylorBounds.le_apply_zero_of_forall_pos <;> assumption
private def FarDecayAt (Cf : StepParameters → ℝ) (T : StepParameters) : Prop :=
  ∀ n : ℕ, T.blockIndex ≤ n → 2 ^ 10 * ((T.L : ℝ) ^ 4 * Cf (rateParameters T)) * torusDecayFactor T.L T.decayRate n *
    (1 / torusDecayFactor T.L T.decayRate ((T.L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * T.κ * n))) ≤ 1
private theorem farDecay_eventually (Cf : StepParameters → ℝ) (hC : ∀ U, 0 < Cf U) :
    EventuallyInParameters (FarDecayAt Cf) := by
  intro a _
  refine ⟨32, fun L _ hL c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ hκ _ => ?_⟩⟩⟩
  have hδ0 : 0 < κ / 2 ^ 10 := by positivity
  have hδκ : κ / 2 ^ 10 ≤ κ := by
    have : κ / 2 ^ 10 = κ * (1 / 2 ^ 10) := by ring
    rw [this]
    nlinarith
  let U : StepParameters := ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  have hC0 := hC U
  have hev := (tails_tendsto_zero (A := (1 / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) hδ0 hκ).comp
    tendsto_natCast_atTop_atTop
  have hsm : ∀ᶠ n : ℕ in Filter.atTop, Real.exp (-(κ / 2 ^ 10 * n)) +
      (1 + (1 / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 * (n : ℝ) ^ 16000) * Real.exp (-(κ * n)) <
      1 / (2 ^ 10 * ((L : ℝ) ^ 4 * Cf U)) :=
    hev.eventually (gt_mem_nhds (by positivity))
  obtain ⟨ns, hns⟩ := Filter.eventually_atTop.mp hsm
  have hfar0 : ∀ n : ℕ, ns ≤ n → 2 ^ 10 * ((L : ℝ) ^ 4 * Cf U) * torusDecayFactor L (κ / 2 ^ 10) n *
      (1 / torusDecayFactor L (κ / 2 ^ 10) ((L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * κ * n))) ≤ 1 := by
    intro n hn
    have h1 := decay_tail_bound hL hδ0 hδκ n
    have h2 := hns n hn
    have h3 := h1.trans h2.le
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith
  refine ⟨1, one_pos, fun η₃ _ _ _ => ⟨ns, fun nss hnss => ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ =>
    ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩
  intro n hn
  exact hfar0 n (hnss.trans hn)
private structure ParameterFacts (T : StepParameters) (C₀ : ℝ) (Ck : ℕ → ℝ) : Prop where
  conditions : TransportConditionsAt T (Ck 3)
  transport : TransportBoundsAt T C₀ Ck
  pos : 0 < C₀
  far : ∀ n : ℕ, T.blockIndex ≤ n → 2 ^ 10 * ((T.L : ℝ) ^ 4 * C₀) * torusDecayFactor T.L T.decayRate n *
    (1 / torusDecayFactor T.L T.decayRate ((T.L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * T.κ * n))) ≤ 1
  near : NearUniformTopResponse T
  locality : frameFamilyLocalAt T
  smooth : CentredExpansionContDiffAt T
  gain : UniformGainAt T
private theorem cellCentredExpansion_jointly {T : StepParameters} (hs : CentredExpansionContDiffAt T) {t : ℕ} {x : ℝ}
    {g : LocalFamily} {V : F.GaugeField F.top} (hx : T.coupling ≤ x)
    (hrow : IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio g F)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (Y : F.Cell) :
    JointlyContDiffOnBalls T.ballRadius V (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y) := by
  intro k c X η hη
  unfold cellCentredExpansion
  exact ContDiffAt.sum fun y _ => hs t x g F V false hx hrow hF hV y η k c X hη
private theorem contDiffAt_slice {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (hJ : JointlyContDiffOnBalls ρ V G) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    ContDiffAt ℝ k (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 := by
  have h1 := hJ k c X η hη
  have h2 : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => ((τ, η) : (Fin k → ℝ) × StepVariable (finiteCells F))) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have h3 := ContDiffAt.comp (0 : Fin k → ℝ) h1 h2
  exact h3.of_le (by exact_mod_cast hk)
private theorem far_low_order {T : StepParameters} {C₀ : ℝ} {Ck : ℕ → ℝ} (hD : T.IsOrdered)
    (hf : ParameterFacts T C₀ Ck) {t : ℕ} {x : ℝ}
    {g : LocalFamily} {V : F.GaugeField F.top} (hx : T.coupling ≤ x)
    (hrow : IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio g F)
    (hder : HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate 3 (fun j => if j = 3 then T.energyRatio else T.E) g)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 2) (hX : AreUnitVectors X) (hn : T.blockIndex ≤ bondSpan Y c) :
    |bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y η) V c X| ≤
      2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
  classical
  obtain ⟨_, hL40, _, hn0, _, _, _⟩ := hf.conditions
  have hE0 : 0 < T.E := by linarith [hD.one_le_E]
  have hE3 : 0 < T.energyRatio := by
    unfold StepParameters.energyRatio
    have := hD.η₃_pos
    positivity
  have hC₀ := hf.pos
  obtain ⟨hFL, _, n, hsn, hnn⟩ := id hF
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hsn i]; omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hD.odd_L
  set vec : ℕ → ℝ := fun j => if j = 3 then T.energyRatio else T.E with hvec
  have hv0 : ∀ j, 0 ≤ vec j := fun j => by
    simp only [hvec]
    split_ifs
    · exact hE3.le
    · exact hE0.le
  have hTr := hf.transport x t 3 vec g F V 1 η hx le_rfl (by norm_num) hv0 hder hF hV zero_le_one le_rfl hη
  have hcd : ∀ y : F.Site F.depth, ContDiffAt ℝ k
      (fun τ : Fin k → ℝ => centredExpansion false T.a T.chainParams.ρA (frameRadius x) g y η
        (leftTranslate (bondSpread c X τ) V)) 0 := by
    intro y
    have h1 := hf.smooth t x g F V false hx hrow hF hV y η k c X hη
    have h2 : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => ((τ, η) : (Fin k → ℝ) × StepVariable (finiteCells F))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have h3 := ContDiffAt.comp (0 : Fin k → ℝ) h1 h2
    exact h3.of_le (by exact_mod_cast (by omega : k ≤ 3))
  have e : bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y η) V c X =
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        bondDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) g y η) V c X := by
    unfold bondDeriv cellCentredExpansion
    have h1 := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := k)
      (u := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
      (f := fun y (τ : Fin k → ℝ) => centredExpansion false T.a T.chainParams.ρA (frameRadius x) g y η
        (leftTranslate (bondSpread c X τ) V))
      (x := 0) (fun y _ => hcd y)
    rw [h1]
    simp
  rw [e]
  set A := 1 / torusDecayFactor T.L T.decayRate ((T.L : ℝ) * bondSpan Y c / 16) +
    Real.exp (-(2 ^ 6 * T.κ * bondSpan Y c)) with hA
  have hA0 : 0 ≤ A := by
    have h1 := decayFactor_pos T.L T.decayRate ((T.L : ℝ) * bondSpan Y c / 16)
    have h2 := Real.exp_pos (-(2 ^ 6 * T.κ * bondSpan Y c))
    positivity
  set bnd := C₀ * T.E * A with hbnd
  have hb0 : 0 ≤ bnd := by positivity
  have hsite : ∀ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      |bondDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) g y η) V c X| ≤ bnd := by
    intro y hy
    have h := hTr.decay y k c X hk1 (by omega) hX
    rw [(Finset.mem_filter.mp hy).2] at h
    have hl : runningMax vec k = T.E := by
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · simp [runningMax, hvec, hE0.le]
      · simp [runningMax, hvec, hE0.le]
    have hr' : interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) g y η =
        centredExpansion false T.a T.chainParams.ρA (frameRadius x) g y η := by
      funext V'
      exact interpolatedExpansion_one _ _ _ _ _ _ _
    rw [hr', hl] at h
    rw [hbnd, hA, one_div]
    exact h
  have h2 := Finset.abs_sum_le_sum_abs
    (fun y => bondDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) g y η) V c X)
    ((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
  have h3 : ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
      |bondDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) g y η) V c X| ≤
      (((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y)).card : ℝ) * bnd := by
    have := Finset.sum_le_card_nsmul ((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y))
      (fun y => |bondDeriv (centredExpansion false T.a T.chainParams.ρA (frameRadius x) g y η) V c X|) bnd hsite
    simpa using this
  have h4 : (((sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y)).card : ℝ) ≤
      (T.L : ℝ) ^ 4 := by
    have := block_card_le hLF hs2 Y
    rw [hFL] at this
    exact_mod_cast this
  have h5 := mul_le_mul_of_nonneg_right h4 hb0
  have hfin : (T.L : ℝ) ^ 4 * C₀ * T.E * A ≤ 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) :=
    far_constant_bound (hf.far _ hn) (decayFactor_pos T.L T.decayRate (bondSpan Y c)) hE0.le
  have e2 : (T.L : ℝ) ^ 4 * bnd = (T.L : ℝ) ^ 4 * C₀ * T.E * A := by
    rw [hbnd]
    ring
  linarith
private structure CentredExpansionGain (T : StepParameters) (G : F.Cell → AboveFrames F) (V : F.GaugeField F.top) : Prop where
  low : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), InClosedBallProduct T.ballRadius η → 1 ≤ k → k ≤ 2 → AreUnitVectors X →
    |bondDeriv (G Y η) V c X| ≤ 2⁻¹ ^ 7 * ((T.L : ℝ) * T.E) / torusDecayFactor T.L T.decayRate (bondSpan Y c)
  third : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (c : Fin 3 → F.Site F.top × Fin 4)
    (X : Fin 3 → imaginaryQuaternions), InClosedBallProduct T.ballRadius η → AreUnitVectors X →
    |bondDeriv (G Y η) V c X| ≤
      2⁻¹ ^ 7 * ((T.L : ℝ) * T.energyRatio) / torusDecayFactor T.L T.decayRate (bondSpan Y c)
  value : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), InClosedBallProduct T.ballRadius η →
    |G Y η V| ≤ 2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate T.blockIndex
private theorem centredExpansion_gain {T : StepParameters} {C₀ : ℝ} {Ck : ℕ → ℝ} (hD : T.IsOrdered)
    (hf : ParameterFacts T C₀ Ck)
    (hDA : mixedDerivativesOnBallsStatement) {t : ℕ} {x : ℝ} {g : LocalFamily} {V : F.GaugeField F.top}
    (hx : T.coupling ≤ x)
    (hrow : IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio g F)
    (hder : HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate 3 (fun j => if j = 3 then T.energyRatio else T.E) g)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) :
    CentredExpansionGain T (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g) V := by
  obtain ⟨_, hL40, _, hn0, _, _, hq⟩ := hf.conditions
  have hσ := hD.σ_pos
  have hη3 := hD.η₃_pos
  have hE0 : 0 < T.E := by linarith [hD.one_le_E]
  have hδ : 0 ≤ T.decayRate := by
    have := hD.κ_pos
    unfold StepParameters.decayRate
    positivity
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hE3 : 0 < T.energyRatio := by
    unfold StepParameters.energyRatio
    positivity
  have hEE : T.E = T.η₃ * T.energyRatio := by
    unfold StepParameters.energyRatio
    field_simp
  have hLp : 0 < T.L := lt_of_lt_of_le (by positivity) hL40
  have hLr : (2 : ℝ) ^ 40 ≤ T.L := by exact_mod_cast hL40
  have hLE : T.E ≤ (T.L : ℝ) * T.E := by nlinarith
  have G0 : ∀ y : ℝ, 0 < torusDecayFactor T.L T.decayRate y := decayFactor_pos _ _
  have inv_le : ∀ {u v A : ℝ}, 0 ≤ A → 0 ≤ u → u ≤ v →
      A / torusDecayFactor T.L T.decayRate v ≤ A / torusDecayFactor T.L T.decayRate u := fun hA hu huv =>
    div_le_div_of_nonneg_left hA (G0 _) (decayFactor_mono hLp hδ hu huv)
  have hJ := cellCentredExpansion_jointly hf.smooth hx hrow hF hV
  have read := fun Y => (hDA F T.ballRadius V).2 _ (hJ Y)
  obtain ⟨Hsize, H1, H2⟩ := hf.near t x g F V hx hrow hF hV false
  have sc : ∀ {A B : ℝ}, A ≤ B → 0 ≤ B → A * T.E ≤ B * ((T.L : ℝ) * T.E) := fun hAB hB =>
    (mul_le_mul_of_nonneg_right hAB hE0.le).trans (mul_le_mul_of_nonneg_left hLE hB)
  refine ⟨?_, ?_, ?_⟩
  · intro Y η k c X hη hk1 hk2 hX
    have hGn := G0 (bondSpan Y c)
    by_cases hn' : T.blockIndex ≤ bondSpan Y c
    · exact (far_low_order hD hf hx hrow hder hF hV Y η hη c X hk1 hk2 hX hn').trans
        (div_le_div_of_nonneg_right (sc (by norm_num) (by norm_num)) hGn.le)
    · have hnlt : bondSpan Y c < T.blockIndex := not_le.mp hn'
      have hld : bondListDistance Y c ≤ T.blockIndex := (bondListDistance_le_bondSpan Y c).trans hnlt.le
      have hnn2 : ((bondSpan Y c : ℕ) : ℝ) ≤ 2 * T.blockIndex := by
        have : bondSpan Y c ≤ 2 * T.blockIndex := by omega
        exact_mod_cast this
      have hG2 : 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex) ≤
          2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) :=
        inv_le (by positivity) (by positivity) hnn2
      refine bound_on_closedBall hρ hη
        (φ := fieldDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y) V c X)
        ((read Y).contDiffAt_one c X η hk2 hη).continuousAt fun ζ hζ => ?_
      show |bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y ζ) V c X| ≤ _
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · exact (H1 Y ζ c X hζ hX hld).trans (hG2.trans
          (div_le_div_of_nonneg_right (sc (by norm_num) (by norm_num)) hGn.le))
      · have a := H2 Y ζ c X hζ hX hld
        rw [show (flatTopField : F.GaugeField F.top) = uniformField F F.top from rfl] at a
        have b := hf.gain t (frameRadius x) g F hrow hF Y c (axialGaugeRotated V Y c X)
          (axialGaugeRotated_units V Y c X hX)
        have c1 := abs_sub_abs_le_abs_sub
          (bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y ζ) V c X)
          (bondDeriv (cellCentredExpansion true T.a T.chainParams.ρA (frameRadius x) g Y 0) (uniformField F F.top) c
            (axialGaugeRotated V Y c X))
        have c2 : 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
            2⁻¹ ^ 8 * ((T.L : ℝ) * T.E) / torusDecayFactor T.L T.decayRate (bondSpan Y c) ≤
            2⁻¹ ^ 7 * ((T.L : ℝ) * T.E) / torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
          rw [← add_div]
          refine div_le_div_of_nonneg_right ?_ hGn.le
          linarith
        linarith
  · intro Y η c X hη hX
    have hGn := G0 (bondSpan Y c)
    have hv0 : ∀ j, 0 ≤ (fun j => if j = 3 then T.energyRatio else T.E : ℕ → ℝ) j := fun j => by
      show 0 ≤ if j = 3 then T.energyRatio else T.E
      split_ifs
      · exact hE3.le
      · exact hE0.le
    have a := (hf.transport x t 3 _ g F V 1 η hx le_rfl (by norm_num) hv0 hder hF hV zero_le_one le_rfl
      hη).blockDeriv_le Y c X hX
    have e : interpolatedBlockExpansion 1 T.a T.chainParams.ρA (frameRadius x) g Y η =
        cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y η := by
      funext V'
      unfold interpolatedBlockExpansion cellCentredExpansion
      exact Finset.sum_congr rfl fun y _ => interpolatedExpansion_one _ _ _ _ _ _ _
    have hlu : runningMax (fun j => if j = 3 then T.energyRatio else T.E) (3 - 1) = T.E := by
      simp [runningMax, hE0.le]
    rw [e, hlu, if_pos rfl] at a
    refine a.trans (div_le_div_of_nonneg_right ?_ hGn.le)
    have c5 : Ck 3 * T.E ≤ 2⁻¹ ^ 9 * T.energyRatio := by
      rw [hEE]
      have := mul_le_mul_of_nonneg_right hq hE3.le
      nlinarith
    have key : (1 / 4 + 2⁻¹ ^ 9 : ℝ) ≤ 2⁻¹ ^ 7 * 2 ^ 40 := by norm_num
    calc 1 / 4 * T.energyRatio + Ck 3 * T.E ≤ 1 / 4 * T.energyRatio + 2⁻¹ ^ 9 * T.energyRatio := by linarith
      _ = (1 / 4 + 2⁻¹ ^ 9) * T.energyRatio := by ring
      _ ≤ (2⁻¹ ^ 7 * 2 ^ 40) * T.energyRatio := mul_le_mul_of_nonneg_right key hE3.le
      _ = 2⁻¹ ^ 7 * (2 ^ 40 * T.energyRatio) := by ring
      _ ≤ 2⁻¹ ^ 7 * ((T.L : ℝ) * T.energyRatio) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLr hE3.le) (by norm_num)
  · intro Y η hη
    exact bound_on_closedBall hρ hη
      (φ := fun ζ => cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y ζ V)
      ((read Y).contDiffAt_three η hη).continuousAt fun ζ hζ => Hsize Y ζ hζ
private theorem centredExpansion_agreement {T : StepParameters} {C₀ : ℝ} {Ck : ℕ → ℝ} (hD : T.IsOrdered)
    (hf : ParameterFacts T C₀ Ck) {t : ℕ} {x : ℝ}
    {g : LocalFamily} {V V' : F.GaugeField F.top} (hx : T.coupling ≤ x)
    (hrow : IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio g F)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hV' : IsSmallCurvature (5 / 4 * T.σ) V') (Y : F.Cell) (r k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hA : AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y r) (hk : k ≤ 2) (hb : ∀ l, BondWithinRadius r (h l))
    (hX : AreUnitVectors X) :
    |bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y 0) V (bondsAt Y h) X -
      bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y 0) V' (bondsAt Y h) X| ≤
      2⁻¹ ^ 6 * ((T.L : ℝ) * T.E) / torusDecayFactor T.L T.decayRate r := by
  obtain ⟨_, hL40, _, hn0, _, _, _⟩ := hf.conditions
  have hσ := hD.σ_pos
  have hE0 : 0 < T.E := by linarith [hD.one_le_E]
  have hδ : 0 ≤ T.decayRate := by
    have := hD.κ_pos
    unfold StepParameters.decayRate
    positivity
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hLp : 0 < T.L := lt_of_lt_of_le (by positivity) hL40
  have hLr : (2 : ℝ) ^ 40 ≤ T.L := by exact_mod_cast hL40
  have hL1 : (1 : ℝ) ≤ T.L := le_trans (by norm_num) hLr
  have hLE : T.E ≤ (T.L : ℝ) * T.E := by nlinarith
  have G0 : ∀ y : ℝ, 0 < torusDecayFactor T.L T.decayRate y := decayFactor_pos _ _
  have inv_le : ∀ {u v A : ℝ}, 0 ≤ A → 0 ≤ u → u ≤ v →
      A / torusDecayFactor T.L T.decayRate v ≤ A / torusDecayFactor T.L T.decayRate u := fun hA hu huv =>
    div_le_div_of_nonneg_left hA (G0 _) (decayFactor_mono hLp hδ hu huv)
  have hGr := G0 r
  have sc : ∀ {A B : ℝ}, A ≤ B → 0 ≤ B → A * T.E ≤ B * ((T.L : ℝ) * T.E) := fun hAB hB =>
    (mul_le_mul_of_nonneg_right hAB hE0.le).trans (mul_le_mul_of_nonneg_left hLE hB)
  by_cases hr : T.blockIndex ≤ r
  · exact (hf.locality t x g F V hx hrow hF hV false V' Y r k h X hV' hA hr hk hb hX).trans
      (div_le_div_of_nonneg_right (sc (by norm_num) (by norm_num)) hGr.le)
  · have hrlt : r < T.blockIndex := not_le.mp hr
    obtain ⟨_, _, n, hsn, hnn⟩ := id hF
    have hs : ∀ i, 2 * r + 2 < F.extent i := fun i => by
      rcases hA.1 i with e | e
      · have := hsn i
        omega
      · exact e
    have b0 : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ < T.ballRadius := fun b => by simpa using hρ
    obtain ⟨Hs, H1, H2⟩ := hf.near t x g F V hx hrow hF hV false
    obtain ⟨Hs', H1', H2'⟩ := hf.near t x g F V' hx hrow hF hV' false
    have hld : bondListDistance Y (bondsAt Y h) ≤ T.blockIndex := (bondListDistance_le_of_within Y hs h hb).trans hrlt.le
    have hrn : (r : ℝ) ≤ T.blockIndex := by exact_mod_cast hrlt.le
    have hr2 : (r : ℝ) ≤ 2 * T.blockIndex := by
      have : r ≤ 2 * T.blockIndex := by omega
      exact_mod_cast this
    have q1 : 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex) ≤
        2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate r :=
      inv_le (by positivity) (by positivity) hr2
    have q0 : 2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate T.blockIndex ≤
        2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate r :=
      inv_le (by positivity) (by positivity) hrn
    have two : ∀ {A : ℝ}, 2 * A ≤ 2⁻¹ ^ 6 →
        A * T.E / torusDecayFactor T.L T.decayRate r + A * T.E / torusDecayFactor T.L T.decayRate r ≤
        2⁻¹ ^ 6 * ((T.L : ℝ) * T.E) / torusDecayFactor T.L T.decayRate r := fun {A} h2 => by
      rw [← add_div, ← add_mul]
      refine div_le_div_of_nonneg_right ?_ hGr.le
      exact sc (by linarith) (by norm_num)
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    · rw [bondDeriv_zero, bondDeriv_zero]
      have a := abs_le.mp (Hs Y 0 b0)
      have a' := abs_le.mp (Hs' Y 0 b0)
      have c := two (A := 2⁻¹ ^ 8) (by norm_num)
      exact abs_le.mpr ⟨by linarith [a.2, a'.1, a.1, a'.2], by linarith [a.2, a'.1, a.1, a'.2]⟩
    · have a := abs_le.mp (H1 Y 0 _ X b0 hX hld)
      have a' := abs_le.mp (H1' Y 0 _ X b0 hX hld)
      have c := two (A := 2⁻¹ ^ 10) (by norm_num)
      exact abs_le.mpr ⟨by linarith [a.2, a'.1, a.1, a'.2], by linarith [a.2, a'.1, a.1, a'.2]⟩
    · have hU := axialGaugeRotated_agree hA.2.2.2 hs hs h X hb
      have a := abs_le.mp (H2 Y 0 _ X b0 hX hld)
      have a' := abs_le.mp (H2' Y 0 _ X b0 hX hld)
      rw [← hU] at a'
      have c := two (A := 2⁻¹ ^ 10) (by norm_num)
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [a.1, a.2, a'.1, a'.2]
private theorem torusRemainder_mono {L : ℕ} {σ δ e e' η₃ : ℝ} {r : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (hee : e ≤ e') (hη : 0 < η₃) (hr : IsTorusRemainder L σ δ e (e / η₃) r) :
    IsTorusRemainder L σ δ e' (e' / η₃) r := by
  have hG : ∀ u : ℝ, 0 < torusDecayFactor L δ u := decayFactor_pos L δ
  refine ⟨⟨hr.decaying.smooth, hr.decaying.gauge_invariant, fun y W k c X hW h1 h3 hX => ?_⟩,
    fun y W W' m k h X hW hW' hag hk hb hX => ?_⟩
  · refine (hr.decaying.decay y W k c X hW h1 h3 hX).trans ?_
    have : (if k = 3 then e / η₃ else e) ≤ (if k = 3 then e' / η₃ else e') := by
      split_ifs
      · gcongr
      · exact hee
    gcongr
    exact (hG _).le
  · refine (hr.agreement y W W' m k h X hW hW' hag hk hb hX).trans ?_
    gcongr
    exact (hG _).le
private theorem holds_of_pos {T : StepParameters} {C₀ : ℝ} {Ck : ℕ → ℝ} (hD : T.IsOrdered) (hf : ParameterFacts T C₀ Ck)
    (hDA : mixedDerivativesOnBallsStatement) {t : ℕ} {x e : ℝ} {f : LocalFamily} {F : BlockFrame}
    {V V' : F.GaugeField F.top}
    {r : F.Site F.depth → F.GaugeField F.depth → ℝ} (hx : T.coupling ≤ x) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hV' : IsSmallCurvature (5 / 4 * T.σ) V') (he : 0 < e)
    (hr : IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r) :
    BlockRemainderBounds T (coldHalfLawAt T x f) e r V ∧
    ∀ (Y : F.Cell) (q k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
      AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → k ≤ 2 → (∀ l, BondWithinRadius q (h l)) →
      AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).blockSum r Y 0) V (bondsAt Y h) X -
          bondDeriv ((coldHalfLawAt T x f).blockSum r Y 0) V' (bondsAt Y h) X| ≤
        2⁻¹ ^ 6 * ((T.L : ℝ) * e) / torusDecayFactor T.L T.decayRate q := by
  obtain ⟨_, hL40, _, hn0, _, _, _⟩ := hf.conditions
  have hE0 : 0 < T.E := by linarith [hD.one_le_E]
  have hη3 := hD.η₃_pos
  have hσ := hD.σ_pos
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hE3 : 0 < T.energyRatio := by
    unfold StepParameters.energyRatio
    positivity
  have hLr : (2 : ℝ) ^ 40 ≤ T.L := by exact_mod_cast hL40
  have hL1 : (1 : ℝ) ≤ T.L := le_trans (by norm_num) hLr
  set b := T.E / e with hbdef
  have hb : 0 < b := div_pos hE0 he
  have hbi : 0 < b⁻¹ := inv_pos.2 hb
  have hbe : b⁻¹ = e / T.E := by
    rw [hbdef, inv_div]
  set g := supportedOn F (scaledBy b r) with hg
  have hfam : IsDecayingSiteFamily T.L T.σ T.decayRate T.E T.energyRatio (scaledBy b r) :=
    decaying_of_remainder he hE0 hη3 hr
  have hrow : IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio g F := regular_of_remainder he hE0 hη3 hr
  have hder : HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate 3 (fun j => if j = 3 then T.energyRatio else T.E) g :=
    boundedDerivatives_of_decaying hE0.le hE3.le hfam
  have RG := centredExpansion_gain hD hf hDA hx hrow (boundedDerivatives_of_decaying hE0.le hE3.le hfam) hF hV
  have hJ := cellCentredExpansion_jointly hf.smooth hx hrow hF hV
  have hJ' := cellCentredExpansion_jointly hf.smooth hx hrow hF hV'
  have link : ∀ {W : F.GaugeField F.top},
      (∀ Y, JointlyContDiffOnBalls T.ballRadius W (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y)) →
      ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), InClosedBallProduct T.ballRadius η →
        ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
        (X : Fin k → imaginaryQuaternions), k ≤ 3 → bondDeriv ((coldHalfLawAt T x f).blockSum r Y η) W c X =
          b⁻¹ * bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y η) W c X +
            (if k = 0 then uniformBlockSum r Y else 0) := fun {W} hW Y η hη k c X hk =>
    bondDeriv_blockSum (coldHalfLawAt T x f) r hb.ne' Y η W c X (contDiffAt_slice (hW Y) hη c X hk)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro Y η k c X hη h1 h2 hX
    rw [link hJ Y η hη c X (by omega), if_neg (by omega), add_zero, abs_mul, abs_of_pos hbi]
    calc b⁻¹ * |bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y η) V c X|
        ≤ b⁻¹ * (2⁻¹ ^ 7 * ((T.L : ℝ) * T.E) / torusDecayFactor T.L T.decayRate (bondSpan Y c)) :=
          mul_le_mul_of_nonneg_left (RG.low Y η k c X hη h1 h2 hX) hbi.le
      _ = _ := by
          rw [hbe]
          field_simp
  · intro Y η c X hη hX
    rw [link hJ Y η hη c X (by omega), if_neg (by omega), add_zero, abs_mul, abs_of_pos hbi]
    calc b⁻¹ * |bondDeriv (cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y η) V c X|
        ≤ b⁻¹ * (2⁻¹ ^ 7 * ((T.L : ℝ) * T.energyRatio) / torusDecayFactor T.L T.decayRate (bondSpan Y c)) :=
          mul_le_mul_of_nonneg_left (RG.third Y η c X hη hX) hbi.le
      _ = _ := by
          rw [hbe]
          unfold StepParameters.energyRatio
          field_simp
  · intro Y η hη
    have e1 : blockRemainderHat (coldHalfLawAt T x f) r Y η V =
        b⁻¹ * cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y η V := by
      unfold blockRemainderHat
      rw [blockSum_eq (coldHalfLawAt T x f) r hb.ne' Y η V]
      unfold uniformBlockSum uniformField
      simp only [add_sub_cancel_right]
      rfl
    rw [e1, abs_mul, abs_of_pos hbi]
    have hG := decayFactor_pos T.L T.decayRate (T.blockIndex : ℝ)
    calc b⁻¹ * |cellCentredExpansion false T.a T.chainParams.ρA (frameRadius x) g Y η V|
        ≤ b⁻¹ * (2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate T.blockIndex) :=
          mul_le_mul_of_nonneg_left (RG.value Y η hη) hbi.le
      _ = 2⁻¹ ^ 8 * e / torusDecayFactor T.L T.decayRate T.blockIndex := by
          rw [hbe]
          field_simp
      _ ≤ _ := by
          refine div_le_div_of_nonneg_right ?_ hG.le
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          nlinarith
  · intro Y q k h X hA hk hbx hX
    have z : InClosedBallProduct T.ballRadius (0 : StepVariable (finiteCells F)) := fun b' => by simpa using hρ.le
    rw [link hJ Y 0 z _ X (by omega), link hJ' Y 0 z _ X (by omega), add_sub_add_right_eq_sub, ← mul_sub, abs_mul,
      abs_of_pos hbi]
    calc _ ≤ b⁻¹ * (2⁻¹ ^ 6 * ((T.L : ℝ) * T.E) / torusDecayFactor T.L T.decayRate q) :=
          mul_le_mul_of_nonneg_left (centredExpansion_agreement hD hf hx hrow hF hV hV' Y q k h X hA hk hbx hX) hbi.le
      _ = _ := by
          rw [hbe]
          field_simp
private theorem holds_at {T : StepParameters} {C₀ : ℝ} {Ck : ℕ → ℝ} (hD : T.IsOrdered) (hf : ParameterFacts T C₀ Ck)
    (hDA : mixedDerivativesOnBallsStatement) : blockRemainderStatementAt T := by
  intro t x e f F V V' r hx hF hV hV' he0 hr
  rcases he0.eq_or_lt with rfl | he
  · have all : ∀ ε : ℝ, 0 < ε → _ := fun ε hε =>
      holds_of_pos (f := f) hD hf hDA hx hF hV hV' hε (torusRemainder_mono hε.le hD.η₃_pos hr)
    refine ⟨⟨fun Y η k c X h1 h2 h3 hX => ?_, fun Y η c X h1 hX => ?_, fun Y η h1 => ?_⟩,
      fun Y q k h X hA hk hb hX => ?_⟩
    · exact le_of_pos_limit
        (b := fun ε => 2⁻¹ ^ 7 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate (bondSpan Y c)) (by fun_prop)
        fun ε hε => (all ε hε).1.low_order Y η k c X h1 h2 h3 hX
    · exact le_of_pos_limit
        (b := fun ε => 2⁻¹ ^ 7 * ((T.L : ℝ) * ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c))
        (by fun_prop)
        fun ε hε => (all ε hε).1.third_order Y η c X h1 hX
    · exact le_of_pos_limit
        (b := fun ε => 2⁻¹ ^ 8 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate T.blockIndex) (by fun_prop)
        fun ε hε => (all ε hε).1.value_bound Y η h1
    · exact le_of_pos_limit (b := fun ε => 2⁻¹ ^ 6 * ((T.L : ℝ) * ε) / torusDecayFactor T.L T.decayRate q)
        (by fun_prop)
        fun ε hε => (all ε hε).2 Y q k h X hA hk hb hX
  · exact holds_of_pos hD hf hDA hx hF hV hV' he hr
end BlockRemainderProof
open BlockAverages ColdStepAtMirrorFrames WeightedResponses LinearResponse Estimates Interpolation FrameLocality
  BlockRemainderProof
theorem blockRemainder_above_frame (hTr : transportBoundsStatement) (hNear : nearUniformTopResponseStatement)
    (hLoc : frameFamilyLocalStatement) (hSm : CentredExpansionContDiff)
    (hDA : mixedDerivativesOnBallsStatement) (hLet : transportConditionsEventually)
    (hJ : EventuallyInParametersCombines)
    (hMain : BlockSecondDerivativeBound) (hA : SecondOrderAlongMotionFormula)
    (hN : FirstDerivVanishesAtUniform) (hSc : FlatCoordinatesScalar)
    (hFc : AxialResponseOfMinimizers) (hM : motionAboveFrameStatement)
    (hS : SiteDecomposition) : blockRemainderStatement := by
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨C, Ck, hC, -, hTrT⟩ := hTr
  refine weaken _ _ (fun T hD h => holds_at hD (C₀ := C (rateParameters T)) (Ck := Ck (rateParameters T))
    ⟨h.2.1, h.1, hC _, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩ hDA)
    (join _ _ hTrT (join _ _ (hLet fun U => Ck U 3) (join _ _ (farDecay_eventually C hC) (join _ _ hNear
      (join _ _ hLoc (join _ _ hSm (uniformGain_eventually hA hN hSc hFc hM hS hMain)))))))
end YangMills.Construction.ResponseInTheExpansion
end
