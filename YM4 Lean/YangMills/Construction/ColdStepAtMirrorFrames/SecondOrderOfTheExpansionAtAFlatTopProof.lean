import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalar
import YangMills.Construction.ColdStepAtMirrorFrames.NoFirstOrderAtTheFlatField
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAlongAMotion
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderKillsGradients
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfAnExpansionAtPotentialsProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfTheExpansionAtAFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.TreeResponseOfTheLeastCoordinatesProof
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MotionAboveTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages Estimates Interpolation
namespace ColdStepAtMirrorFrames
open BlockOffsets
namespace FlatTopExpansionHessian
variable {F : BlockFrame}
theorem isSmallCurvature_uniformField {j : ℕ} {σ : ℝ} (hσ : 0 < σ) : IsSmallCurvature σ (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem hasDerivAt_expUnit_path (u : ℝ → imaginaryQuaternions) (u' : imaginaryQuaternions) (h0 : u 0 = 0)
    (hu : HasDerivAt u u' 0) :
    HasDerivAt (fun s => ((expUnit (u s) : UnitQuaternion) : ℍ[ℝ])) (u' : ℍ[ℝ]) 0 := by
  have hc : HasDerivAt (fun s => (u s : ℍ[ℝ])) (u' : ℍ[ℝ]) 0 :=
    imaginaryQuaternions.subtypeL.hasFDerivAt.comp_hasDerivAt 0 hu
  have he : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      ((u 0 : imaginaryQuaternions) : ℍ[ℝ]) := by
    rw [h0]
    exact hasFDerivAt_exp_zero
  exact he.comp_hasDerivAt 0 hc
theorem bondSpread_single {j : ℕ} (cc : Fin 2 → F.Site j × Fin 4) (X : Fin 2 → imaginaryQuaternions) (l : Fin 2)
    (s : ℝ) (y : F.Site j) (i : Fin 4) :
    bondSpread cc X (s • (Pi.single l 1 : Fin 2 → ℝ)) y i = if cc l = (y, i) then s • X l else 0 := by
  unfold bondSpread
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp
theorem bondSpread_one {j : ℕ} (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (τ : Fin 1 → ℝ) (y : F.Site j)
    (i : Fin 4) : bondSpread ![c] ![X] τ y i = if c = (y, i) then τ 0 • X else 0 := by
  simp [bondSpread]
theorem stepCoordinates_zero {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
theorem coordsAboveFrame_zero (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) :
    coordsAboveFrame true a ρ m V 0 x i = torusCoordinate a ρ (x, i) V := by
  simp [coordsAboveFrame, stepFrame, torusCoordinate, stepCoordinates_zero]
theorem torusCoordinate_eq_zero_of_not_mem (a ρ : ℝ) (b : F.Site F.depth × Fin 4)
    (hb : b ∉ chordBonds (finiteCells F)) (V : F.GaugeField F.top) :
    torusCoordinate a ρ b V = 0 := by apply _root_.YangMills.SharedProofs.p33224 <;> assumption
open Classical in
theorem motionComponent_first (a ρ : ℝ) (m : ℕ) (cc : Fin 2 → F.Site F.top × Fin 4)
    (X : Fin 2 → imaginaryQuaternions)
    (α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions) (h0 : ∀ x i, α 0 x i = 0)
    (hC : ∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0)
    (hev : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ),
      fieldAboveFrame true a ρ m (leftTranslate (bondSpread cc X τ) (uniformField F F.top)) 0 =
        leftTranslate (α τ) (uniformField F F.depth))
    (hzero : ∀ b, torusCoordinate a ρ b (uniformField F F.top) = 0)
    (hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    (hdiff : ∀ b ∈ chordBonds (finiteCells F), ∀ l, DifferentiableAt ℝ
      (fun τ : Fin 1 → ℝ =>
        torusCoordinate a ρ b (leftTranslate (bondSpread ![cc l] ![X l] τ) (uniformField F F.top))) 0)
    (l : Fin 2) (x : F.Site F.depth) (i : Fin 4) :
    motionComponent α ![l] x i = bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![cc l] ![X l] +
      (if IsCrossingBond (x, i) ∧ enclosingCell x = (cc l).1 ∧ i = (cc l).2 then X l else 0) := by
  classical
  set e₁ : Fin 2 → ℝ := Pi.single l 1 with he₁
  have hπ : HasDerivAt (fun s : ℝ => s • e₁) e₁ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const e₁
  have hπ0 : ((0 : ℝ) • e₁) = 0 := zero_smul _ _
  have ha : HasDerivAt (fun s : ℝ => α (s • e₁) x i) (motionComponent α ![l] x i) 0 := by
    have hd : HasFDerivAt (fun τ => α τ x i) (fderiv ℝ (fun τ => α τ x i) ((0 : ℝ) • e₁)) ((0 : ℝ) • e₁) := by
      rw [hπ0]
      exact ((hC x i).differentiableAt (by norm_num)).hasFDerivAt
    have h2 := hd.comp_hasDerivAt (0 : ℝ) hπ
    rw [hπ0] at h2
    have e : motionComponent α ![l] x i = fderiv ℝ (fun τ => α τ x i) 0 e₁ := by
      unfold motionComponent
      rw [iteratedFDeriv_one_apply]
      rfl
    rw [e]
    exact h2
  have hexp := hasDerivAt_expUnit_path (fun s : ℝ => α (s • e₁) x i) _ (by simp [h0]) ha
  set V : ℝ → F.GaugeField F.top := fun s => leftTranslate (bondSpread cc X (s • e₁)) (uniformField F F.top)
    with hV
  have htend : Filter.Tendsto (fun s : ℝ => s • e₁) (𝓝 0) (𝓝 0) := by
    have := (hπ.continuousAt).tendsto
    simpa using this
  have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), ((fieldAboveFrame true a ρ m (V s) 0 x i : UnitQuaternion) : ℍ[ℝ]) =
      ((expUnit (α (s • e₁) x i) : UnitQuaternion) : ℍ[ℝ]) := by
    filter_upwards [htend.eventually hev] with s hs
    simp only [hV]
    rw [hs]
    simp [leftTranslate, uniformField]
  have hQ := hexp.congr_of_eventuallyEq hev2
  have hfield : ∀ s, fieldAboveFrame true a ρ m (V s) 0 x i =
      chartedField (fun x i => torusCoordinate a ρ (x, i) (V s)) (V s) x i := by
    intro s
    unfold fieldAboveFrame
    congr 1
    funext x' i'
    exact coordsAboveFrame_zero _ _ _ _ _ _
  have hcoord : ∀ (hb : (x, i) ∈ chordBonds (finiteCells F)),
      HasDerivAt (fun s => torusCoordinate a ρ (x, i) (V s))
        (bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![cc l] ![X l]) 0 := by
    intro hb
    set H : (Fin 1 → ℝ) → imaginaryQuaternions := fun τ =>
      torusCoordinate a ρ (x, i) (leftTranslate (bondSpread ![cc l] ![X l] τ) (uniformField F F.top)) with hH
    have hHd := (hdiff _ hb l).hasFDerivAt
    have hpt : HasDerivAt (fun s : ℝ => s • (fun _ => 1 : Fin 1 → ℝ)) (fun _ => 1 : Fin 1 → ℝ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (fun _ => 1 : Fin 1 → ℝ)
    have hpt0 : ((0 : ℝ) • (fun _ => 1 : Fin 1 → ℝ)) = 0 := zero_smul _ _
    have hHd' : HasFDerivAt H (fderiv ℝ H 0) ((0 : ℝ) • (fun _ => 1 : Fin 1 → ℝ)) := by
      rw [hpt0]
      exact hHd
    have h2 := hHd'.comp_hasDerivAt (0 : ℝ) hpt
    have e1 : (H ∘ fun s : ℝ => s • (fun _ => 1 : Fin 1 → ℝ)) = fun s => torusCoordinate a ρ (x, i) (V s) := by
      funext s
      simp only [Function.comp, hH, hV]
      congr 1
      funext y j
      simp only [leftTranslate]
      rw [bondSpread_one, bondSpread_single]
      simp
    have e2 : bondDeriv (torusCoordinate a ρ (x, i)) (uniformField F F.top) ![cc l] ![X l] =
        fderiv ℝ H 0 (fun _ => 1) := by
      unfold bondDeriv
      rw [iteratedFDeriv_one_apply]
      have e3 : (Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) = fun _ => 1 := by
        funext m
        simp [Pi.single_apply, Subsingleton.elim m 0]
      simp only [e3]
      rfl
    rw [e1] at h2
    rw [e2]
    exact h2
  have hz0 : torusCoordinate a ρ (x, i) (V 0) = 0 := by
    have e : V 0 = uniformField F F.top := by
      funext y j
      simp only [hV, leftTranslate]
      rw [bondSpread_single]
      simp [expUnit_zero, uniformField]
    rw [e]
    exact hzero _
  apply Subtype.ext
  by_cases hcr : IsCrossingBond (x, i)
  · have hnt : ¬ IsAxialTreeBond (x, i) := fun h => h.1 hcr
    have hb := hcoord (hchart _ hnt)
    have h1 := hasDerivAt_expUnit_path (fun s => torusCoordinate a ρ (x, i) (V s)) _ hz0 hb
    have hsp : HasDerivAt (fun s : ℝ => bondSpread cc X (s • e₁) (enclosingCell x) i)
        (if cc l = (enclosingCell x, i) then X l else 0) 0 := by
      have e : (fun s : ℝ => bondSpread cc X (s • e₁) (enclosingCell x) i) =
          fun s : ℝ => if cc l = (enclosingCell x, i) then s • X l else 0 := by
        funext s
        exact bondSpread_single _ _ _ _ _ _
      rw [e]
      split_ifs
      · simpa using (hasDerivAt_id (0 : ℝ)).smul_const (X l)
      · exact hasDerivAt_const _ _
    have h2 := hasDerivAt_expUnit_path (fun s : ℝ => bondSpread cc X (s • e₁) (enclosingCell x) i) _
      (by simp [bondSpread]) hsp
    have h3 := h1.mul h2
    have e3 : (fun s => ((fieldAboveFrame true a ρ m (V s) 0 x i : UnitQuaternion) : ℍ[ℝ])) =
        (fun s => ((expUnit (torusCoordinate a ρ (x, i) (V s)) : UnitQuaternion) : ℍ[ℝ])) *
          fun s : ℝ => ((expUnit (bondSpread cc X (s • e₁) (enclosingCell x) i) : UnitQuaternion) : ℍ[ℝ]) := by
      funext s
      rw [hfield]
      simp [chartedField, if_pos hcr, hV, leftTranslate, uniformField]
    rw [e3] at hQ
    have hu := hQ.unique h3
    rw [hu]
    have hval : torusCoordinate a ρ (x, i) (V 0) = 0 := hz0
    have hs0 : bondSpread cc X ((0 : ℝ) • e₁) (enclosingCell x) i = 0 := by
      rw [zero_smul]
      simp [bondSpread]
    simp only [hval, hs0, expUnit_zero]
    by_cases e : cc l = (enclosingCell x, i)
    · have e' : IsCrossingBond (x, i) ∧ enclosingCell x = (cc l).1 ∧ i = (cc l).2 :=
        ⟨hcr, by rw [e], by rw [e]⟩
      rw [if_pos e, if_pos e']
      simp
    · have e' : ¬ (IsCrossingBond (x, i) ∧ enclosingCell x = (cc l).1 ∧ i = (cc l).2) := by
        rintro ⟨-, h1, h2⟩
        exact e (Prod.ext h1.symm h2.symm)
      rw [if_neg e, if_neg e']
      simp
  · have e' : ¬ (IsCrossingBond (x, i) ∧ enclosingCell x = (cc l).1 ∧ i = (cc l).2) := fun h => hcr h.1
    rw [if_neg e', add_zero]
    by_cases ht : IsAxialTreeBond (x, i)
    · have e3 : (fun s => ((fieldAboveFrame true a ρ m (V s) 0 x i : UnitQuaternion) : ℍ[ℝ])) = fun _ => 1 := by
        funext s
        rw [hfield]
        simp [chartedField, if_neg hcr, if_pos ht]
      rw [e3] at hQ
      have hu := hQ.unique (hasDerivAt_const _ _)
      rw [hu]
      have hnc : (x, i) ∉ chordBonds (finiteCells F) := fun h => (Finset.mem_filter.1 h).2 ht
      have e4 : (fun τ : Fin 1 → ℝ =>
          torusCoordinate a ρ (x, i) (leftTranslate (bondSpread ![cc l] ![X l] τ) (uniformField F F.top))) =
          fun _ => 0 := by
        funext τ
        exact torusCoordinate_eq_zero_of_not_mem _ _ _ hnc _
      unfold bondDeriv
      rw [e4, iteratedFDeriv_const_of_ne (by norm_num)]
      rfl
    · have hb := hcoord (hchart _ ht)
      have h1 := hasDerivAt_expUnit_path (fun s => torusCoordinate a ρ (x, i) (V s)) _ hz0 hb
      have e3 : (fun s => ((fieldAboveFrame true a ρ m (V s) 0 x i : UnitQuaternion) : ℍ[ℝ])) =
          fun s => ((expUnit (torusCoordinate a ρ (x, i) (V s)) : UnitQuaternion) : ℍ[ℝ]) := by
        funext s
        rw [hfield]
        simp [chartedField, if_neg hcr, if_neg ht]
      rw [e3] at hQ
      exact hQ.unique h1
def BilinearBoundAt (a del : ℝ) (L₀ : ℕ) : Prop :=
  ∀ (F : BlockFrame) (δ E : ℝ) (Y : F.Cell)
    (c : Fin 2 → F.Site F.top × Fin 4) (B : Fin 2 → FormChain F) (W : Fin 2 → LevelForm F F.depth)
    (q : F.Site F.depth → F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ), Odd F.blockSide →
    L₀ ≤ F.blockSide →
    IsLargeCubicTorus F → 0 < δ → δ ≤ del / 64 → 0 ≤ E → (∀ i, IsFlatChain a (c i) (B i)) →
    (∀ i, IsAxialResponse (c i) (B i) (W i)) →
    (∀ y (A : LevelForm F F.depth) (φ : F.Site F.depth → ℝ),
      bondPairing (q y) (addGradient (fun _ _ => 0) φ) A = 0 ∧
      bondPairing (q y) A (addGradient (fun _ _ => 0) φ) = 0) →
    (∀ y b b', |q y b b'| ≤ E / torusDecayFactor F.blockSide δ (bondSpan y ![b, b'])) →
    (∀ y (Fm Fm' : Fin 4 → Fin 4 → ℝ), (∀ μ ν, Fm μ ν = - Fm ν μ) → (∀ μ ν, Fm' μ ν = - Fm' ν μ) →
      |∑ b ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
        ∑ b' ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
          q y b b' * axialGaugePotential y Fm b.1 b.2 * axialGaugePotential y Fm' b'.1 b'.2| ≤
        (F.blockSide : ℝ) ^ (-(7000 : ℝ)) * E * (∑ μ, ∑ ν, |Fm μ ν|) * ∑ μ, ∑ ν, |Fm' μ ν|) →
    |∑ y ∈ blockFineSites Y, bondPairing (q y) (W 0) (W 1)| ≤
      (F.blockSide : ℝ) ^ (-(1 / 4 : ℝ)) * E / torusDecayFactor F.blockSide δ (bondSpan Y c)
def AxialBoundAt (L₀ : ℕ) : Prop :=
  ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame) (X₀ X₁ : imaginaryQuaternions)
    (y : F.Site F.depth) (Fm Fm' : Fin 4 → Fin 4 → ℝ),
    L₀ ≤ L → Odd L → 0 < σ → 0 ≤ δ → 0 ≤ E → IsRegularFamily L t n₀ σ δ E E₃ f → IsCubicTorusAbove L t n₀ F →
    (∀ i, 2 * L ^ 2 + 2 < F.period F.depth i) → ‖X₀‖ = 1 → ‖X₁‖ = 1 →
    (∀ μ ν, Fm μ ν = - Fm ν μ) → (∀ μ ν, Fm' μ ν = - Fm' ν μ) →
    |∑ b ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
      ∑ b' ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
        bondDeriv (f F y) (uniformField F F.depth) ![b, b'] ![X₀, X₁] * axialGaugePotential y Fm b.1 b.2 *
          axialGaugePotential y Fm' b'.1 b'.2| ≤
      (F.blockSide : ℝ) ^ (-(7000 : ℝ)) * E * (∑ μ, ∑ ν, |Fm μ ν|) * ∑ μ, ∑ ν, |Fm' μ ν|
theorem bondDeriv_subtractTrivial (f : LocalFamily) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (c : Fin 2 → F.Site F.depth × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (hs : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => f F y (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (subtractTrivial f F y) W c X = bondDeriv (f F y) W c X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialSecondOrder.bondDeriv_subtractTrivial <;> assumption
theorem bondDeriv_block_sum {n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (hrow : IsRegularFamily F.blockSide F.depth n₀ σ δ E E₃ f)
    (hlow : IsCubicTorusAbove F.blockSide F.depth n₀ F) (hσ : 0 < σ) (S : Finset (F.Site F.depth))
    (c : Fin 2 → F.Site F.depth × Fin 4) (X : Fin 2 → imaginaryQuaternions) :
    bondDeriv (fun W => ∑ y ∈ S, subtractTrivial f F y W) (uniformField F F.depth) c X =
      ∑ y ∈ S, bondDeriv (f F y) (uniformField F F.depth) c X := by
  have hs : ∀ y ∈ S, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun τ : Fin 2 → ℝ =>
      subtractTrivial f F y (leftTranslate (bondSpread c X τ) (uniformField F F.depth))) 0 := by
    intro y _
    exact ((hrow.smooth F hlow y _ (isSmallCurvature_uniformField hσ) 2 c X).sub contDiffAt_const).of_le
      (by norm_num)
  have h := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (f := fun y => fun τ : Fin 2 → ℝ =>
    subtractTrivial f F y (leftTranslate (bondSpread c X τ) (uniformField F F.depth))) (u := S) (n := 2) (x := 0) hs
  have e2 : bondDeriv (fun W => ∑ y ∈ S, subtractTrivial f F y W) (uniformField F F.depth) c X =
      ∑ y ∈ S, bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X := by
    unfold bondDeriv
    rw [h, ContinuousMultilinearMap.sum_apply]
  rw [e2]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact bondDeriv_subtractTrivial f y _ c X (hrow.smooth F hlow y _ (isSmallCurvature_uniformField hσ) 2 c X)
set_option maxHeartbeats 4000000 in
theorem expansionSecondDeriv_bound (hA : SecondOrderAlongMotionFormula) (hN : FirstDerivVanishesAtUniform)
    (hK : SecondDerivGradientInvariant) (hSc : FlatCoordinatesScalar)
    (hFc : AxialResponseOfMinimizers) (hM : motionAboveFrameStatement)
    (hS : SiteDecomposition) {a del : ℝ} {L₁ L₂ : ℕ} (ha : 1 ≤ a) (hsum : BilinearBoundAt a del L₁)
    (hpot : AxialBoundAt L₂)
    {L : ℕ} (hodd : Odd L) (hL₁ : L₁ ≤ L) (hL₂ : L₂ ≤ L) (hL1 : 1 ≤ L) {c : ColdChainParameters}
    (hc : c.Admissible a L)
    {σ δ E E₃ : ℝ} {n₀ t m : ℕ} {f : LocalFamily} {F : BlockFrame} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδd : δ ≤ del / 64)
    (hE : 0 ≤ E) (hn₀ : 64 + 2 * L + 3 ≤ n₀) (hrow : IsRegularFamily L t n₀ σ δ E E₃ f)
    (hF : IsCubicTopTorus L t n₀ F)
    (Y : F.Cell) (cc : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions) (hX : AreUnitVectors X) :
    |bondDeriv (cellCentredExpansion true a c.ρA m f Y 0) (uniformField F F.top) cc X| ≤
      (L : ℝ) ^ (-(1 / 4 : ℝ)) * E / torusDecayFactor L δ (bondSpan Y cc) := by
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
  have hCl := hc.estimates F c.σA (uniformField F F.top) hchainT hσA le_rfl (isSmallCurvature_uniformField hσA)
  have hdec := (hcl F c.s₀ (uniformField F F.top) hchainT hs₀ le_rfl (isSmallCurvature_uniformField hs₀)).2.2.1
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
    simp only [coordsAboveFrame_zero, hzero, expUnit_zero]
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
      (fun τ : Fin 1 → ℝ =>
        torusCoordinate a c.ρA b (leftTranslate (bondSpread ![cc l] ![X l] τ) (uniformField F F.top))) 0 :=
    fun b hb l => ((hCl.coordinates b hb).1 1 ![cc l] ![X l]).differentiableAt
  have hu : ∀ l x i, motionComponent α ![l] x i = minimizerResponse a c.ρA (cc l) (X l) x i • X l := by
    intro l x i
    rw [motionComponent_first a c.ρA m cc X α h0 hC hev' hzero hchart hdiff l x i]
    unfold minimizerResponse
    rw [add_smul, ← (hSc a F.blockSide c hodd hc F (x, i) (cc l) (X l) hchainT (hX l)).2]
    congr 1
    split_ifs <;> simp
  have hGs : ContDiffThreeAlongBonds (fun W => ∑ y ∈ blockFineSites Y, subtractTrivial f F y W)
      (uniformField F F.depth) := by
    intro k c' X'
    refine ContDiffAt.sum fun y _ => ?_
    exact (hrow.smooth F hlow y _ (isSmallCurvature_uniformField hσ) k c' X').sub contDiffAt_const
  have hinv : ∀ (W : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W →
      (fun W => ∑ y ∈ blockFineSites Y, subtractTrivial f F y W) (gaugeTransform γ W) =
        (fun W => ∑ y ∈ blockFineSites Y, subtractTrivial f F y W) W := by
    intro W γ hW
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold subtractTrivial
    rw [hrow.gauge_invariant F hlow y W γ hW]
  have hmain := hA F F.depth (fineBonds F) (fun W => ∑ y ∈ blockFineSites Y, subtractTrivial f F y W)
    (uniformField F F.depth) α
    (minimizerResponse a c.ρA (cc 0) (X 0)) (minimizerResponse a c.ρA (cc 1) (X 1)) (X 0) (X 1) hT hGs
    (fun c' X' hX' => hN F F.depth _ σ c' X' hσ hinv hX') h0 hC (hu 0) (hu 1)
  have hleft : bondDeriv (cellCentredExpansion true a c.ρA m f Y 0) (uniformField F F.top) cc X =
      iteratedFDeriv ℝ 2 (fun τ => (fun W => ∑ y ∈ blockFineSites Y, subtractTrivial f F y W)
        (leftTranslate (α τ) (uniformField F F.depth))) 0
        ![Pi.single 0 1, Pi.single 1 1] := by
    have e1 : (fun τ => cellCentredExpansion true a c.ρA m f Y 0
        (leftTranslate (bondSpread cc X τ) (uniformField F F.top))) =ᶠ[𝓝 0]
        fun τ => (fun W => ∑ y ∈ blockFineSites Y, subtractTrivial f F y W)
          (leftTranslate (α τ) (uniformField F F.depth)) := by
      filter_upwards [hev'] with τ h
      show ∑ y ∈ blockFineSites Y, subtractTrivial f F y (fieldAboveFrame true a c.ρA m _ 0) = _
      rw [h]
    have e2 := (Filter.EventuallyEq.iteratedFDeriv ℝ e1 2).eq_of_nhds
    have e3 : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
      funext l
      fin_cases l <;> rfl
    unfold bondDeriv
    rw [e2, e3]
  rw [hleft, hmain]
  choose B hBf hBt using fun l => hFc a ha F.blockSide hodd c hc F (cc l) (X l) rfl hcub (hX l)
  set q : F.Site F.depth → F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ :=
    fun y b b' => bondDeriv (f F y) (uniformField F F.depth) ![b, b'] ![X 0, X 1] with hq
  have hfin := hsum F δ E Y cc B (fun l => minimizerResponse a c.ρA (cc l) (X l)) q hodd hL₁ hcub hδ hδd hE hBf hBt
    (by
      intro y A φ
      have hsm := hrow.smooth F hlow y _ (isSmallCurvature_uniformField hσ)
      have hgi : ∀ (W : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W →
          f F y (gaugeTransform γ W) = f F y W :=
        fun W γ hW => hrow.gauge_invariant F hlow y W γ hW
      constructor
      · have h := hK F F.depth (fineBonds F) (f F y) σ (X 0) (X 1) (fun z => - φ z) (fun _ => 0) (fun _ _ => 0) A hT
          hper0 hσ hsm hgi (hX 0) (hX 1)
        unfold bondPairing
        simp only [zero_add, mul_zero, zero_mul, Finset.sum_const_zero, sub_self, add_zero] at h
        refine Eq.trans ?_ h
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        simp only [addGradient, hq]
        ring
      · have h := hK F F.depth (fineBonds F) (f F y) σ (X 0) (X 1) (fun _ => 0) (fun z => - φ z) A (fun _ _ => 0) hT
          hper0 hσ hsm hgi (hX 0) (hX 1)
        unfold bondPairing
        simp only [zero_add, mul_zero, zero_mul, Finset.sum_const_zero, sub_self, add_zero] at h
        refine Eq.trans ?_ h
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        simp only [addGradient, hq]
        ring)
    (by
      intro y b b'
      have h := hrow.decay F hlow y _ 2 ![b, b'] ![X 0, X 1] (isSmallCurvature_uniformField hσ) (by norm_num)
        (by norm_num) (by intro l; fin_cases l; exacts [hX 0, hX 1])
      rwa [if_neg (by norm_num)] at h)
    (fun y Fm Fm' h h' => hpot F.blockSide F.depth n₀ σ δ E E₃ f F (X 0) (X 1) y Fm Fm' hL₂ hodd hσ hδ.le hE hrow
      hlow hper (hX 0) (hX 1) h h')
  have hswap : ∑ b ∈ fineBonds F, ∑ b' ∈ fineBonds F,
      bondDeriv (fun W => ∑ y ∈ blockFineSites Y, subtractTrivial f F y W) (uniformField F F.depth) ![b, b']
        ![X 0, X 1] *
        minimizerResponse a c.ρA (cc 0) (X 0) b.1 b.2 * minimizerResponse a c.ρA (cc 1) (X 1) b'.1 b'.2 =
      ∑ y ∈ blockFineSites Y, bondPairing (q y) (minimizerResponse a c.ρA (cc 0) (X 0))
        (minimizerResponse a c.ρA (cc 1) (X 1)) := by
    unfold bondPairing
    calc _ = ∑ b ∈ fineBonds F, ∑ b' ∈ fineBonds F, ∑ y ∈ blockFineSites Y,
          q y b b' * minimizerResponse a c.ρA (cc 0) (X 0) b.1 b.2 *
            minimizerResponse a c.ρA (cc 1) (X 1) b'.1 b'.2 := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
          rw [bondDeriv_block_sum hrow hlow hσ, Finset.sum_mul, Finset.sum_mul]
      _ = ∑ b ∈ fineBonds F, ∑ y ∈ blockFineSites Y, ∑ b' ∈ fineBonds F,
          q y b b' * minimizerResponse a c.ρA (cc 0) (X 0) b.1 b.2 *
            minimizerResponse a c.ρA (cc 1) (X 1) b'.1 b'.2 :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  exact hfin
end FlatTopExpansionHessian
open FlatTopExpansionHessian in
theorem expansionSecondDerivFlat_holds (h1 : BilinearResponseBound)
    (h2 : AxialResponseOfMinimizers) (h3 : FlatCoordinatesScalar)
    (h4 : SecondOrderAlongMotionFormula) (h5 : FirstDerivVanishesAtUniform)
    (h6 : SecondDerivGradientInvariant) (h7 : SecondOrderAxialBound)
    (h8 : motionAboveFrameStatement) (h9 : SiteDecomposition) :
    ExpansionSecondDerivFlat := by
  intro a ha
  obtain ⟨del, hdel, L₁, hsum⟩ := h1 a ha
  obtain ⟨L₂, hpot⟩ := h7
  refine ⟨max (max L₁ L₂) 1, fun L hodd hL c hc => ?_⟩
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL₂ : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  refine ⟨0, fun Ct _ => ⟨16 * del, mul_pos (by norm_num) hdel, fun κ hκ hκ0 => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨1, one_pos, fun σ hσ _ p _ => ⟨0, fun Cs _ E hE => ⟨64 + 2 * L + 3, fun n₀ hn₀ =>
      ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩
  intro t m f F hrow hF Y cc X hX
  have hδ : 0 < κ / 2 ^ 10 := by positivity
  have hδd : κ / 2 ^ 10 ≤ del / 64 := by
    norm_num
    linarith
  exact expansionSecondDeriv_bound h4 h5 h6 h3 h2 h8 h9 ha hsum hpot hodd hL₁ hL₂ hL1 hc hσ hδ hδd (by linarith) hn₀
    hrow hF Y cc X hX
end ColdStepAtMirrorFrames
end YangMills.Construction
end
