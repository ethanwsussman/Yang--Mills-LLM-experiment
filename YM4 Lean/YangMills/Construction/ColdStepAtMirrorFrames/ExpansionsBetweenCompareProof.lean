import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.DensityOfTheFramesProof
import YangMills.Construction.ColdStepAtMirrorFrames.EmbeddedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsCompareOnPairedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsFromSlopesProof
import YangMills.Construction.ColdStepAtMirrorFrames.GlueOfTwoCharts
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenStayNear
import YangMills.Construction.SummableBoundsOfTheFlow.ShortMovesOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
private theorem agreeOnBall_mono {F F' : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
    {S' : Finset F'.Cell} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r r₂ : ℕ} (hle : r₂ ≤ r)
    (hA : AgreeOnBall S V S' V' Y Y' r) : AgreeOnBall S V S' V' Y Y' r₂ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameDensity.agreeOnBall_mono <;> assumption
private theorem mem_finiteCells_local {F : BlockFrame} (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
open Classical in
private theorem sum_block_sites (hS : SiteDecomposition) (F : BlockFrame) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (g : F.Site F.depth → ℝ) :
    ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = z), g y =
      ∑ u ∈ centredCube F.blockSide, g (cellCentre F.depth z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth u) := by
  obtain ⟨a1, a2, _, _⟩ := hS F hodd hs
  refine Finset.sum_nbij' (fun y => cellOffset y) (fun u => cellCentre F.depth z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth u)
    ?_ ?_ ?_ ?_ ?_
  · intro y _
    exact (a2 y).2
  · intro u hu
    refine Finset.mem_filter.2 ⟨?_, (a1 z u hu).1⟩
    unfold sitesOfCells
    refine Finset.mem_biUnion.2 ⟨z, mem_finiteCells_local hs z, Finset.mem_image.2 ⟨u, ?_, rfl⟩⟩
    simpa [BlockFrame.top] using hu
  · intro y hy
    have hc : enclosingCell y = z := (Finset.mem_filter.1 hy).2
    show cellCentre F.depth z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth (cellOffset y) = y
    rw [← hc]
    exact (a2 y).1
  · intro u hu
    exact (a1 z u hu).2
  · intro y hy
    have hc : enclosingCell y = z := (Finset.mem_filter.1 hy).2
    rw [← hc, (a2 y).1]
private def interpCoords {F : BlockFrame} (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun z i => interpolatedFrame s a ρA m (z, i) V
private theorem interpolatedBlockExpansion_eq (hS : SiteDecomposition) {F : BlockFrame} (s a ρA : ℝ) (m : ℕ)
    (f : LocalFamily) (V : F.GaugeField F.top) (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (η : StepVariable (finiteCells F)) :
    interpolatedBlockExpansion s a ρA m f z η V =
      ∑ u ∈ centredCube F.blockSide, subtractTrivial f F (cellCentre F.depth z + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.depth u)
        (chartedField (shiftCoordinates (interpCoords s a ρA m V) η) V) :=
  sum_block_sites hS F hodd hs z fun y => interpolatedExpansion s a ρA m f y η V
private theorem isOpen_openPolyball_local {ι : Type} [Fintype ι] (ρ : ℝ) : IsOpen (openPolyball ι ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.isOpen_openPolyball <;> assumption
private theorem bondGradNorm_le_of {ι : Type} [Fintype ι] [DecidableEq ι] {f : BondField ι → ℝ} {k : ι}
    {ξ : BondField ι} {B : ℝ} (hB : 0 ≤ B) (h : ∀ e : BondVector, ‖e‖ = 1 → |bondPartialDeriv f k ξ e| ≤ B) :
    bondGradNorm f k ξ ≤ B := by
  unfold bondGradNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun e => ?_
  by_cases he : e = 0
  · simp [he]
  have hn : 0 < ‖e‖ := norm_pos_iff.2 he
  have h1 := h (‖e‖⁻¹ • e) (norm_smul_inv_norm he)
  have h2 : bondPartialDeriv f k ξ (‖e‖⁻¹ • e) =
      ‖e‖⁻¹ * ((fderiv ℝ f ξ).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k)) e := by
    have : bondPartialDeriv f k ξ (‖e‖⁻¹ • e) =
        ((fderiv ℝ f ξ).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k)) (‖e‖⁻¹ • e) := rfl
    rw [this, map_smul, smul_eq_mul]
  rw [h2, abs_mul, abs_of_pos (inv_pos.2 hn), inv_mul_le_iff₀ hn] at h1
  rw [Real.norm_eq_abs, mul_comm B]
  linarith [h1]
private theorem sum_diff_bounds {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset (Fin 4 → ℤ))
    (A A' : (Fin 4 → ℤ) → BondField ι → ℝ) (ρ Bv Bg : ℝ) (hρ : 0 < ρ) (hBg : 0 ≤ Bg)
    (c1 : ∀ u ∈ S, ContDiffOn ℝ 2 (A u) (openPolyball ι (2 * ρ)))
    (c2 : ∀ u ∈ S, ContDiffOn ℝ 2 (A' u) (openPolyball ι (2 * ρ)))
    (hv : ∀ u ∈ S, ∀ ξ ∈ openPolyball ι ρ, |A' u ξ - A u ξ| ≤ Bv)
    (hg : ∀ u ∈ S, ∀ ξ ∈ openPolyball ι ρ, ∀ (k : ι) (e : BondVector), ‖e‖ = 1 →
      |bondPartialDeriv (A' u) k ξ e - bondPartialDeriv (A u) k ξ e| ≤ Bg) :
    ContDiffOn ℝ 1 (fun ζ => ∑ u ∈ S, (A' u ζ - A u ζ)) (openPolyball ι ρ) ∧
      ∀ ξ ∈ openPolyball ι ρ, |∑ u ∈ S, (A' u ξ - A u ξ)| ≤ S.card * Bv ∧
        ∀ k, bondGradNorm (fun ζ => ∑ u ∈ S, (A' u ζ - A u ζ)) k ξ ≤ S.card * Bg := by
  have hsub : openPolyball ι ρ ⊆ openPolyball ι (2 * ρ) := fun ξ hξ b => (hξ b).trans (by linarith)
  have hopen := isOpen_openPolyball_local (ι := ι) (2 * ρ)
  have hd : ∀ (G : BondField ι → ℝ), ContDiffOn ℝ 2 G (openPolyball ι (2 * ρ)) → ∀ ξ ∈ openPolyball ι ρ,
      DifferentiableAt ℝ G ξ := fun G hG ξ hξ =>
    (hG.contDiffAt (hopen.mem_nhds (hsub hξ))).differentiableAt (by norm_num)
  refine ⟨ContDiffOn.sum fun u hu => (((c2 u hu).sub (c1 u hu)).mono hsub).of_le (by norm_num),
    fun ξ hξ => ⟨?_, fun k => ?_⟩⟩
  · calc |∑ u ∈ S, (A' u ξ - A u ξ)| ≤ ∑ u ∈ S, |A' u ξ - A u ξ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ S, Bv := Finset.sum_le_sum fun u hu => hv u hu ξ hξ
      _ = S.card * Bv := by simp [Finset.sum_const]
  · refine bondGradNorm_le_of (by positivity) fun e he => ?_
    have hfd : fderiv ℝ (fun ζ => ∑ u ∈ S, (A' u ζ - A u ζ)) ξ =
        ∑ u ∈ S, (fderiv ℝ (A' u) ξ - fderiv ℝ (A u) ξ) := by
      have hh : ∀ u ∈ S, HasFDerivAt (fun ζ => A' u ζ - A u ζ) (fderiv ℝ (A' u) ξ - fderiv ℝ (A u) ξ) ξ :=
        fun u hu => (hd _ (c2 u hu) ξ hξ).hasFDerivAt.sub (hd _ (c1 u hu) ξ hξ).hasFDerivAt
      exact (HasFDerivAt.fun_sum hh).fderiv
    have hval : bondPartialDeriv (fun ζ => ∑ u ∈ S, (A' u ζ - A u ζ)) k ξ e =
        ∑ u ∈ S, (bondPartialDeriv (A' u) k ξ e - bondPartialDeriv (A u) k ξ e) := by
      unfold bondPartialDeriv
      rw [hfd]
      simp
    rw [hval]
    calc |∑ u ∈ S, (bondPartialDeriv (A' u) k ξ e - bondPartialDeriv (A u) k ξ e)|
        ≤ ∑ u ∈ S, |bondPartialDeriv (A' u) k ξ e - bondPartialDeriv (A u) k ξ e| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ S, Bg := Finset.sum_le_sum fun u hu => hg u hu ξ hξ k e he
      _ = S.card * Bg := by simp [Finset.sum_const]
private theorem shifted_small (hM : ChartLipschitz.ChartedFieldLipschitz) (hLC : ImaginaryCoordinatesIsometric)
    {F : BlockFrame} {s a ρA δ₂ c σ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hsm : InterpolatedFrameSmall s a ρA δ₂ c σ m V) (hσ : 0 < σ)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ 3 * (σ / 64)) :
    IsSmallCurvature σ (chartedField (shiftCoordinates (interpCoords s a ρA m V) η) V) ∧
      ∀ b ∈ chordBonds (finiteCells F),
        ‖shiftCoordinates (interpCoords s a ρA m V) η b.1 b.2‖ ≤ c * σ + 3 * (σ / 64) := by
  obtain ⟨_, _, hnorm, _, _, hzero, _⟩ := hLC
  have hε : (0 : ℝ) ≤ 3 * (σ / 64) := by positivity
  have hco : ∀ (z : F.Site F.depth) (i : Fin 4), ‖(stepCoordinates η z i : imaginaryQuaternions)‖ ≤ 3 * (σ / 64) := by
    intro z i
    unfold stepCoordinates
    split_ifs with hb
    · rw [hnorm]
      exact hη _
    · simpa using hε
  have h0 : interpolatedField s a ρA m V (0 : StepVariable (finiteCells F)) =
      chartedField (interpCoords s a ρA m V) V := by
    have := congrArg (fun w => chartedField w V) (hzero F (interpCoords s a ρA m V))
    exact this
  have hmove := (hM.2 F (shiftCoordinates (interpCoords s a ρA m V) η) (interpCoords s a ρA m V) V (3 * (σ / 64))
    (fun z i => by
      show ‖(interpCoords s a ρA m V z i + stepCoordinates η z i) - interpCoords s a ρA m V z i‖ ≤ _
      rw [add_sub_cancel_left]
      exact hco z i) hε).2
  refine ⟨fun p hp => ?_, fun b hb => ?_⟩
  · have h1 := hsm.small_curvature p hp
    rw [h0] at h1
    have h2 := hmove p
    linarith
  · have h1 := hsm.norm_le b hb
    calc ‖shiftCoordinates (interpCoords s a ρA m V) η b.1 b.2‖
        ≤ ‖interpCoords s a ρA m V b.1 b.2‖ + ‖(stepCoordinates η b.1 b.2 : imaginaryQuaternions)‖ :=
          norm_add_le _ _
      _ ≤ c * σ + 3 * (σ / 64) := add_le_add h1 (hco _ _)
private theorem norm_pushforward_le (hE : PushforwardFieldProperties) {F : BlockFrame} {ι : Type} [Fintype ι]
    [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F))) (hj : Function.Injective j) (ξ : BondField ι)
    (B : ℝ) (hB : 0 ≤ B) (hξ : ∀ k, ‖ξ k‖ ≤ B) (b : ↥(chordBonds (finiteCells F))) :
    ‖pushforwardField j ξ b‖ ≤ B := by
  obtain ⟨_, _, _, h4, h5, _⟩ := hE ι ↥(chordBonds (finiteCells F)) j hj
  by_cases hb : ∃ k, j k = b
  · obtain ⟨k, rfl⟩ := hb
    rw [h4]
    exact hξ k
  · rw [h5 ξ b fun k hk => hb ⟨k, hk⟩]
    simpa using hB
private theorem card_ballChordBonds_le (hO : TorusOffsetsAboutCell) {F : BlockFrame} (Y : F.Cell) (r : ℕ)
    (hodd : Odd F.blockSide) (hs : ∀ i, 2 * r + 2 < F.extent i) :
    ((ballChordBonds F Y r).card : ℝ) ≤ 4 * (2 * (r : ℝ) + 1) ^ 4 * (F.blockSide : ℝ) ^ 4 := by
  classical
  obtain ⟨_, _, _, _, h5, _⟩ := hO F r Y hodd hs
  have hsub : (ballChordBonds F Y r).map (Function.Embedding.subtype _) ⊆
      (centredCube (2 * r + 1) ×ˢ centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))).image
        (fun p => fineBondAt Y p.1 p.2.1 p.2.2) := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
    have hd : cellSupDist (enclosingCell b'.1.1) Y ≤ r := (Finset.mem_filter.1 hb').2
    obtain ⟨g, o, h1, h2, h3⟩ := h5 b'.1.1 hd
    refine Finset.mem_image.2 ⟨(g, o, b'.1.2), ?_, h3 _⟩
    refine Finset.mem_product.2 ⟨?_, Finset.mem_product.2 ⟨h2, Finset.mem_univ _⟩⟩
    simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have := abs_le.1 (h1 i)
    have e : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = r := by omega
    rw [e]
    exact this
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_map] at h1
  rw [Finset.card_product, Finset.card_product, LatticePaths.card_centredCube hodd,
    LatticePaths.card_centredCube (⟨r, rfl⟩ : Odd (2 * r + 1)), Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ((ballChordBonds F Y r).card : ℝ) ≤ (((2 * r + 1) ^ 4 * (F.blockSide ^ 4 * 4) : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  linarith [h2]
private theorem poly_mul_exp_le_one (K β : ℝ) (hK : 0 < K) (hβ : 0 < β) :
    ∃ N₀ : ℕ, ∀ q : ℕ, N₀ ≤ q → K * (2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(β * q)) ≤ 1 := by
  have h := isLittleO_pow_exp_pos_mul_atTop (k := 4) hβ
  have hc : 0 < 1 / (81 * K) := by positivity
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 (h.def hc)
  refine ⟨max 1 ⌈X⌉₊, fun q hq => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (le_max_left _ _).trans hq
  have hqX : X ≤ q := (Nat.le_ceil X).trans (by exact_mod_cast (le_max_right _ _).trans hq)
  have h3 := hX q hqX
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at h3
  have h4 : (2 * (q : ℝ) + 1) ^ 4 ≤ 81 * (q : ℝ) ^ 4 := by
    have h5 : 2 * (q : ℝ) + 1 ≤ 3 * q := by linarith
    calc (2 * (q : ℝ) + 1) ^ 4 ≤ (3 * (q : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) h5 4
      _ = 81 * (q : ℝ) ^ 4 := by ring
  have h6 : K * (81 * (1 / (81 * K) * Real.exp (β * q))) = Real.exp (β * q) := by
    field_simp
  have h7 : K * (2 * (q : ℝ) + 1) ^ 4 ≤ Real.exp (β * q) := by
    rw [← h6]
    refine mul_le_mul_of_nonneg_left (h4.trans ?_) hK.le
    exact mul_le_mul_of_nonneg_left h3 (by norm_num)
  calc K * (2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(β * q))
      ≤ Real.exp (β * q) * Real.exp (-(β * q)) := mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp
private def seriesExpansionConst (C Ct : ℝ) (L : ℕ) : ℝ := 2 ^ 14 * (C + 1) * Ct * (L : ℝ) ^ 8
private structure SeriesExpansionBounds (C : ℝ) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  side_large : 2 ^ 15 ≤ T.L
  Ct_ge_one : 1 ≤ T.Ct
  κ_le : 2 ^ 10 * T.κ ≤ T.chainParams.δ₂
  δ₂_pos : 0 < T.chainParams.δ₂
  σ_le : (T.Ct + 1) * T.σ ≤ 1
  n₀_pos : 1 ≤ T.n₀
  blockIndex_ge : 64 ≤ T.blockIndex
  coupling_nonneg : 0 ≤ T.coupling
  decay : ∀ q : ℕ, T.blockIndex ≤ q →
    seriesExpansionConst C T.Ct T.L * Real.exp T.chainParams.δ₂ * (2 * (q : ℝ) + 1) ^ 4 *
        Real.exp (-(T.chainParams.δ₂ / 16 * q)) ≤ Real.exp (-(16 * T.κ * q)) ∧
    seriesExpansionConst C T.Ct T.L * Real.exp (-(T.κ * q)) ≤ 1
private theorem expansionBounds_eventually (C : ℝ) (hC : 0 < C) : EventuallyInParameters (SeriesExpansionBounds C) := by
  intro a _
  refine ⟨2 ^ 15, fun L _ hL c hc => ⟨1, fun Ct hCt => ?_⟩⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨c.δ₂ / 2 ^ 10, by positivity, fun κ hκ hκ₀ => ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩⟩
  have hK : 0 < seriesExpansionConst C Ct L := by
    unfold seriesExpansionConst
    positivity
  have hβ : 0 < c.δ₂ / 16 - 16 * κ := by
    have : 16 * κ ≤ 16 * (c.δ₂ / 2 ^ 10) := by linarith
    norm_num at this ⊢
    linarith
  obtain ⟨N₁, h₁⟩ := poly_mul_exp_le_one (seriesExpansionConst C Ct L * Real.exp c.δ₂) _ (by positivity) hβ
  obtain ⟨N₂, h₂⟩ := poly_mul_exp_le_one (seriesExpansionConst C Ct L) κ hK hκ
  have hCt1 : 0 < Ct + 1 := by linarith
  refine ⟨max 64 (max N₁ N₂), fun nb hnb => ⟨1 / (Ct + 1), by positivity, fun σ hσ hσ₀ p _ =>
    ⟨0, fun Cs _ E _ => ⟨1, fun n₀ hn₀ => ⟨0, fun CE _ => ⟨0, fun y hy => ?_⟩⟩⟩⟩⟩⟩
  refine ⟨hL, hCt, ?_, hδ, ?_, hn₀, (le_max_left _ _).trans hnb, hy, fun q hq => ⟨?_, ?_⟩⟩
  · show 2 ^ 10 * κ ≤ c.δ₂
    have := hκ₀
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · show (Ct + 1) * σ ≤ 1
    rw [le_div_iff₀ hCt1] at hσ₀
    linarith
  · show seriesExpansionConst C Ct L * Real.exp c.δ₂ * (2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(c.δ₂ / 16 * q)) ≤
      Real.exp (-(16 * κ * q))
    have hq1 : N₁ ≤ q := ((le_max_left _ _).trans (le_max_right _ _)).trans (hnb.trans hq)
    have h3 := h₁ q hq1
    have e1 : Real.exp (-((c.δ₂ / 16 - 16 * κ) * q)) =
        Real.exp (-(c.δ₂ / 16 * q)) * Real.exp (16 * κ * q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e1, ← mul_assoc] at h3
    have e2 : Real.exp (16 * κ * q) * Real.exp (-(16 * κ * q)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc seriesExpansionConst C Ct L * Real.exp c.δ₂ * (2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(c.δ₂ / 16 * q))
        = seriesExpansionConst C Ct L * Real.exp c.δ₂ * (2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(c.δ₂ / 16 * q)) *
            Real.exp (16 * κ * q) * Real.exp (-(16 * κ * q)) := by
          rw [mul_assoc _ (Real.exp (16 * κ * q)), e2, mul_one]
      _ ≤ 1 * Real.exp (-(16 * κ * q)) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp (-(16 * κ * q)) := one_mul _
  · show seriesExpansionConst C Ct L * Real.exp (-(κ * q)) ≤ 1
    have hq2 : N₂ ≤ q := ((le_max_right _ _).trans (le_max_right _ _)).trans (hnb.trans hq)
    have h3 := h₂ q hq2
    have h4 : (1 : ℝ) ≤ (2 * (q : ℝ) + 1) ^ 4 := one_le_pow₀ (by
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      linarith)
    calc seriesExpansionConst C Ct L * Real.exp (-(κ * q))
        = seriesExpansionConst C Ct L * 1 * Real.exp (-(κ * q)) := by rw [mul_one]
      _ ≤ seriesExpansionConst C Ct L * (2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(κ * q)) := by
          have := Real.exp_pos (-(κ * q))
          gcongr
      _ ≤ 1 := h3
private theorem value_estimate {E C Ct Lr Q A e8 σ N G : ℝ} (hE : 0 ≤ E) (hC : 0 < C) (hCt : 1 ≤ Ct)
    (hL : 1 ≤ Lr) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (he : 0 < e8) (he1 : e8 ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hN0 : 0 ≤ N) (hN : N ≤ 4 * Q * Lr ^ 4) (hs : 2 ^ 14 * (C + 1) * Ct * Lr ^ 8 * Q * A ≤ e8 * e8)
    (hG : G ≤ E * e8) :
    Lr ^ 4 * (G + C * E * (Ct * σ * A) * N) ≤ E * e8 * (2 ^ 14 * (C + 1) * Ct * Lr ^ 8) := by
  have _ := hσ0
  have hL8 : 1 ≤ Lr ^ 8 := one_le_pow₀ hL
  have hL48 : Lr ^ 4 ≤ Lr ^ 8 := pow_le_pow_right₀ hL (by norm_num)
  have h4 : 4 * C ≤ 2 ^ 14 * (C + 1) := by nlinarith
  have p1 : Lr ^ 4 * (C * E * (Ct * σ * A) * N) ≤ E * e8 := by
    calc Lr ^ 4 * (C * E * (Ct * σ * A) * N) ≤ Lr ^ 4 * (C * E * (Ct * 1 * A) * (4 * Q * Lr ^ 4)) := by gcongr
      _ = E * (4 * C * Ct * Lr ^ 8 * Q * A) := by ring
      _ ≤ E * (2 ^ 14 * (C + 1) * Ct * Lr ^ 8 * Q * A) := by gcongr
      _ ≤ E * (e8 * e8) := by gcongr
      _ ≤ E * e8 := by
        have : e8 * e8 ≤ e8 := by nlinarith
        gcongr
  have p2 : Lr ^ 4 * G ≤ Lr ^ 4 * (E * e8) := by gcongr
  have p3 : Lr ^ 4 + 1 ≤ 2 ^ 14 * (C + 1) * Ct * Lr ^ 8 := by
    have h5 : (1 : ℝ) ≤ (C + 1) * Ct := by nlinarith
    have h6 : 2 * Lr ^ 8 ≤ 2 ^ 14 * ((C + 1) * Ct) * Lr ^ 8 := by
      have : (2 : ℝ) ≤ 2 ^ 14 * ((C + 1) * Ct) := by nlinarith
      gcongr
    nlinarith
  calc Lr ^ 4 * (G + C * E * (Ct * σ * A) * N)
      = Lr ^ 4 * G + Lr ^ 4 * (C * E * (Ct * σ * A) * N) := by ring
    _ ≤ Lr ^ 4 * (E * e8) + E * e8 := add_le_add p2 p1
    _ = E * e8 * (Lr ^ 4 + 1) := by ring
    _ ≤ E * e8 * (2 ^ 14 * (C + 1) * Ct * Lr ^ 8) := by gcongr
private theorem grad_estimate {E C Ct Lr Q A e8 σ N G G₄ : ℝ} (hE : 0 ≤ E) (hC : 0 < C) (hCt : 1 ≤ Ct)
    (hL : 1 ≤ Lr) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (he : 0 < e8) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hN : N ≤ 4 * Q * Lr ^ 4) (hs : 2 ^ 14 * (C + 1) * Ct * Lr ^ 8 * Q * A ≤ e8 * e8) (hG : G ≤ C * E * e8)
    (hG₄ : G₄ ≤ e8) :
    Lr ^ 4 * (G + 2 * (C * E * (Ct * σ * A) * N) / (σ / 64 * e8) + 2 * (C * E) * (σ / 64 * e8) +
      2 * (C * E) * G₄) ≤ E * e8 * (2 ^ 14 * (C + 1) * Ct * Lr ^ 8) := by
  have hL8 : 1 ≤ Lr ^ 8 := one_le_pow₀ hL
  have hL48 : Lr ^ 4 ≤ Lr ^ 8 := pow_le_pow_right₀ hL (by norm_num)
  have t2 : 2 * (C * E * (Ct * σ * A) * N) / (σ / 64 * e8) = 128 * (C * E * Ct * A * N) / e8 := by
    field_simp
    ring
  have h512 : 512 * C ≤ 2 ^ 14 * (C + 1) := by nlinarith
  have p2 : Lr ^ 4 * (128 * (C * E * Ct * A * N) / e8) ≤ E * e8 := by
    rw [mul_div_assoc', div_le_iff₀ he]
    calc Lr ^ 4 * (128 * (C * E * Ct * A * N)) ≤ Lr ^ 4 * (128 * (C * E * Ct * A * (4 * Q * Lr ^ 4))) := by
          gcongr
      _ = E * (512 * C * Ct * Lr ^ 8 * Q * A) := by ring
      _ ≤ E * (2 ^ 14 * (C + 1) * Ct * Lr ^ 8 * Q * A) := by gcongr
      _ ≤ E * (e8 * e8) := by gcongr
      _ = E * e8 * e8 := by ring
  have p3 : 2 * (C * E) * (σ / 64 * e8) ≤ 2 * (C * E) * e8 := by
    have : σ / 64 * e8 ≤ e8 := by
      have : σ / 64 ≤ 1 := by linarith
      nlinarith
    gcongr
  have p4 : 2 * (C * E) * G₄ ≤ 2 * (C * E) * e8 := by gcongr
  have p5 : 5 * C * Lr ^ 4 + 1 ≤ 2 ^ 14 * (C + 1) * Ct * Lr ^ 8 := by
    have h5 : 5 * C * Lr ^ 4 ≤ 5 * C * Lr ^ 8 := by gcongr
    have h6 : (5 * C + 1) * Lr ^ 8 ≤ 2 ^ 14 * (C + 1) * Ct * Lr ^ 8 := by
      have : 5 * C + 1 ≤ 2 ^ 14 * (C + 1) * Ct := by nlinarith
      gcongr
    nlinarith
  rw [t2]
  calc Lr ^ 4 * (G + 128 * (C * E * Ct * A * N) / e8 + 2 * (C * E) * (σ / 64 * e8) + 2 * (C * E) * G₄)
      = Lr ^ 4 * (G + 2 * (C * E) * (σ / 64 * e8) + 2 * (C * E) * G₄) +
        Lr ^ 4 * (128 * (C * E * Ct * A * N) / e8) := by ring
    _ ≤ Lr ^ 4 * (C * E * e8 + 2 * (C * E) * e8 + 2 * (C * E) * e8) + E * e8 := by gcongr
    _ = E * e8 * (5 * C * Lr ^ 4 + 1) := by ring
    _ ≤ E * e8 * (2 ^ 14 * (C + 1) * Ct * Lr ^ 8) := by gcongr
private theorem target_estimate {E E₃ Ct κ q d g : ℝ} (hE : 0 ≤ E) (hE₃ : E ≤ E₃) (hCt : 1 ≤ Ct) (hκ : 0 < κ)
    (hq : 0 ≤ q) (hd : d ≤ 9 / 8 * q) (hg : 1 ≤ g) :
    E * Real.exp (-(7 * κ * q)) ≤ Ct * E₃ * Real.exp (-(4 * κ * q)) * g * Real.exp (-(2 * κ * d)) := by
  have h1 : Real.exp (-(7 * κ * q)) ≤ Real.exp (-(4 * κ * q)) * Real.exp (-(2 * κ * d)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hd hκ.le, mul_nonneg hκ.le hq]
  have h2 : E ≤ Ct * E₃ * g := by
    have hE₃0 : 0 ≤ E₃ := hE.trans hE₃
    have : E₃ ≤ Ct * E₃ := by nlinarith
    have h3 : Ct * E₃ ≤ Ct * E₃ * g := by
      have : 0 ≤ Ct * E₃ := by positivity
      nlinarith
    linarith
  calc E * Real.exp (-(7 * κ * q)) ≤ (Ct * E₃ * g) * (Real.exp (-(4 * κ * q)) * Real.exp (-(2 * κ * d))) := by
        have := Real.exp_pos (-(7 * κ * q))
        have h0 : 0 ≤ Ct * E₃ * g := hE.trans h2
        gcongr
    _ = Ct * E₃ * Real.exp (-(4 * κ * q)) * g * Real.exp (-(2 * κ * d)) := by ring
private theorem div_torusDecayFactor_le {X y : ℝ} (L : ℕ) (δ : ℝ) (hX : 0 ≤ X) :
    X / torusDecayFactor L δ y ≤ X * Real.exp (-(δ * y)) := by
  have h1 : Real.exp (δ * y) ≤ torusDecayFactor L δ y := by
    unfold torusDecayFactor
    exact le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
  rw [Real.exp_neg, div_eq_mul_inv]
  have := Real.exp_pos (δ * y)
  gcongr
set_option maxHeartbeats 1000000 in
theorem interpolatedExpansionsCompare_holds (hRows : PairedExpansionsComparison) (hG : TwoChartsGlue)
    (hO : TorusOffsetsAboutCell) (hLC : ImaginaryCoordinatesIsometric) (hE : PushforwardFieldProperties)
    (hS : SiteDecomposition) (hM : ChartLipschitz.ChartedFieldLipschitz) (hN : interpolatedFramesControlled)
    (hj : EventuallyInParametersCombines) : InterpolatedExpansionsCompare := by
  obtain ⟨C, hC, hR⟩ := hRows
  refine hj.2 _ _ ?_ (hj.1 _ _ hN (expansionBounds_eventually C hC))
  rintro T hT ⟨hNT, hn⟩ t x s h F F' V V' Y Y' q ι _ _ j j' o cs
  have hq64 : 64 ≤ q := hn.blockIndex_ge.trans cs.radius_le
  have hFL : F.blockSide = T.L := cs.top.1
  have hFL' : F'.blockSide = T.L := cs.top'.1
  have hodd : Odd T.L := hT.odd_L
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hoddF' : Odd F'.blockSide := hFL' ▸ hodd
  have hσ : 0 < T.σ := hT.σ_pos
  have hκ : 0 < T.κ := hT.κ_pos
  have hE0 : 0 ≤ T.E := by linarith [hT.one_le_E]
  have hCt : 1 ≤ T.Ct := hn.Ct_ge_one
  have hLbig : (2 : ℝ) ^ 15 ≤ T.L := by exact_mod_cast hn.side_large
  have hLr : (1 : ℝ) ≤ T.L := by linarith [show (1 : ℝ) ≤ 2 ^ 15 by norm_num]
  have hδ₂ := hn.δ₂_pos
  have hsF : ∀ i, 2 * q + 2 < F.extent i := by
    obtain ⟨_, _, n, h1, h2⟩ := cs.top
    intro i
    rcases cs.agree.1 i with h0 | h0
    · have := hn.n₀_pos
      have := h1 i
      omega
    · exact h0
  have hsF' : ∀ i, 2 * q + 2 < F'.extent i := by
    obtain ⟨_, _, n, h1, h2⟩ := cs.top'
    intro i
    rcases cs.agree.2.1 i with h0 | h0
    · have := hn.n₀_pos
      have := h1 i
      omega
    · exact h0
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    have := hsF i
    omega
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by
    have := hsF' i
    omega
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = q / 2 + 2 * (q / 8) + 4 := ⟨_, rfl⟩
  have hr₂q : r₂ + 1 ≤ q := by omega
  have hsr : ∀ i, 2 * r₂ + 2 < F.extent i := fun i => by
    have := hsF i
    omega
  have hqr : (64 : ℝ) ≤ q := by exact_mod_cast hq64
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have c1 : (q : ℝ) ≤ 2 * ((q / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : q ≤ 2 * (q / 2) + 1)
  have c2 : 8 * ((q / 8 : ℕ) : ℝ) ≤ q := by exact_mod_cast (by omega : 8 * (q / 8) ≤ q)
  have c3 : 4 * (r₂ : ℝ) ≤ 3 * q + 16 := by exact_mod_cast (by omega : 4 * r₂ ≤ 3 * q + 16)
  have c4 : (r₂ : ℝ) = ((q / 2 : ℕ) : ℝ) + 2 * ((q / 8 : ℕ) : ℝ) + 4 := by exact_mod_cast hr₂
  have c5 : (0 : ℝ) ≤ ((q / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨A, hAdef⟩ : ∃ A, A = Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - r₂))) := ⟨_, rfl⟩
  have hApos : 0 < A := hAdef ▸ Real.exp_pos _
  obtain ⟨e8, he8⟩ : ∃ e8, e8 = Real.exp (-(8 * T.κ * q)) := ⟨_, rfl⟩
  have he8pos : 0 < e8 := he8 ▸ Real.exp_pos _
  have he81 : e8 ≤ 1 := by
    rw [he8, Real.exp_le_one_iff]
    have := mul_nonneg hκ.le hq0
    linarith
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = (2 * (q : ℝ) + 1) ^ 4 := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    exact one_le_pow₀ (by linarith)
  have hKpos : 0 < seriesExpansionConst C T.Ct T.L := by
    unfold seriesExpansionConst
    have : (0 : ℝ) < T.Ct := by linarith
    have : (0 : ℝ) < (T.L : ℝ) := by linarith
    positivity
  have hstar : seriesExpansionConst C T.Ct T.L * Q * A ≤ e8 * e8 := by
    have d := (hn.decay q cs.radius_le).1
    have hA2 : A ≤ Real.exp T.chainParams.δ₂ * Real.exp (-(T.chainParams.δ₂ / 16 * q)) := by
      rw [hAdef, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith [mul_nonneg hδ₂.le (sub_nonneg.2 c3)]
    have e : e8 * e8 = Real.exp (-(16 * T.κ * q)) := by
      rw [he8, ← Real.exp_add]
      congr 1
      ring
    rw [e]
    refine le_trans ?_ d
    rw [← hQdef]
    calc seriesExpansionConst C T.Ct T.L * Q * A
        ≤ seriesExpansionConst C T.Ct T.L * Q * (Real.exp T.chainParams.δ₂ * Real.exp (-(T.chainParams.δ₂ / 16 * q))) := by
          have : 0 ≤ seriesExpansionConst C T.Ct T.L * Q := by positivity
          exact mul_le_mul_of_nonneg_left hA2 this
      _ = seriesExpansionConst C T.Ct T.L * Real.exp T.chainParams.δ₂ * Q * Real.exp (-(T.chainParams.δ₂ / 16 * q)) := by
          ring
  have hCσpos : 0 < T.Ct * T.σ := mul_pos (by linarith) hσ
  have hσ1 : T.σ ≤ 1 := by linarith [hn.σ_le]
  have hone : T.Ct * T.σ + 3 * (T.σ / 64) ≤ 1 := by linarith [hn.σ_le]
  have hρdef : T.ballRadius = T.σ / 64 := rfl
  have hρ : 0 < T.ballRadius := by
    rw [hρdef]
    positivity
  have hθρ : T.Ct * T.σ * A ≤ T.ballRadius := by
    have h1 : 64 * T.Ct ≤ seriesExpansionConst C T.Ct T.L := by
      unfold seriesExpansionConst
      have hL8 : (1 : ℝ) ≤ (T.L : ℝ) ^ 8 := one_le_pow₀ hLr
      have h2 : (1 : ℝ) ≤ (C + 1) * (T.L : ℝ) ^ 8 :=
        one_le_mul_of_one_le_of_one_le (by linarith) hL8
      have h3 : 0 ≤ T.Ct := by linarith
      calc 64 * T.Ct ≤ 2 ^ 14 * T.Ct * 1 := by linarith
        _ ≤ 2 ^ 14 * T.Ct * ((C + 1) * (T.L : ℝ) ^ 8) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 ^ 14 * (C + 1) * T.Ct * (T.L : ℝ) ^ 8 := by ring
    have h2 : 64 * T.Ct * A ≤ 1 := by
      have h3 : seriesExpansionConst C T.Ct T.L * A ≤ seriesExpansionConst C T.Ct T.L * Q * A := by
        rw [mul_right_comm]
        exact le_mul_of_one_le_right (mul_pos hKpos hApos).le hQ1
      have h4 : e8 * e8 ≤ 1 := mul_le_one₀ he81 he8pos.le he81
      exact (mul_le_mul_of_nonneg_right h1 hApos.le).trans (h3.trans (hstar.trans h4))
    rw [hρdef]
    calc T.Ct * T.σ * A = T.σ / 64 * (64 * T.Ct * A) := by ring
      _ ≤ T.σ / 64 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = T.σ / 64 := mul_one _
  have hθ0 : 0 ≤ T.Ct * T.σ * A := by
    have : (0 : ℝ) < T.Ct := by linarith
    positivity
  obtain ⟨o1, _, o3, _, _, o6, o7, o8, _⟩ := hO F q Y hoddF hsF
  have hdist : ∀ (g : Fin 4 → ℤ) (R : ℕ), WithinRadius q g → WithinRadius R g →
      cellSupDist (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) Y ≤ R ∧ cellSupDist Y (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) ≤ R := by
    intro g R hg hR
    obtain ⟨d1, d2⟩ := o3 g hg
    have h1 : (Finset.univ.sup fun i => (g i).natAbs) ≤ R := Finset.sup_le fun i _ => by
      have := hR i
      rw [Int.abs_eq_natAbs] at this
      omega
    rw [d1, d2]
    exact ⟨h1, h1⟩
  have near := (hNT t x cs.coupling_le).pair F F' V V' Y Y' q s cs.top cs.top' cs.small cs.small' cs.agree
    cs.interp_mem.1 cs.interp_mem.2
  have hnear : CoordinatesCloseOnBall F.blockSide Y Y' r₂ (T.Ct * T.σ * A)
      (interpCoords s T.a T.chainParams.ρA (frameRadius x) V)
      (interpCoords s T.a T.chainParams.ρA (frameRadius x) V') := by
    intro g u i hg hu hb
    have hgq : WithinRadius q g := fun l => (hg l).trans (by exact_mod_cast (by omega : r₂ ≤ q))
    have hc := (o1 g u i hu).1
    have dd := hdist g r₂ hgq hg
    have hD1 : cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) ≤ r₂ := by
      rw [hc]
      exact dd.2
    have hD2 : cellSupDist Y (enclosingCell ((fineBondAt Y g u i).1 + unitStep F.depth i)) ≤ q := by
      rw [o7]
      have h6 := o6 (fineBondAt Y g u i).1 i
      rw [hc] at h6
      have := dd.1
      omega
    have hlow : IsFineBondWithinRadius Y q g u i := ⟨hu, hb, hgq, hD1.trans (by omega), hD2⟩
    have hv := near.norm_sub_le g u i hlow
    refine (le_of_eq ?_).trans (hv.trans ?_)
    · rw [← Submodule.coe_sub]
      rfl
    · have hD : ((cellSupDist Y (enclosingCell (fineBondAt Y g u i).1) : ℕ) : ℝ) ≤ r₂ := by
        exact_mod_cast hD1
      have hCσ : 0 ≤ T.Ct * T.σ := by
        have : (0 : ℝ) < T.Ct := by linarith
        positivity
      rw [hAdef]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCσ
      have h5 := mul_le_mul_of_nonneg_left hD (show 0 ≤ T.chainParams.δ₂ / 4 by positivity)
      linarith
  obtain ⟨Δ, wx, hΔ1, hΔ2, hΔ3, hΔ4⟩ :=
    hG F F' Y Y' r₂ (T.Ct * T.σ * A) _ _ (hFL.trans hFL'.symm) hoddF hsr hθ0 hnear
  have hmoved : ∀ (h₁ o₁ : Fin 4 → ℤ) (i : Fin 4), WithinRadius r₂ h₁ → o₁ ∈ centredCube T.L →
      fineBondAt Y h₁ o₁ i ∈ chordBonds (finiteCells F) →
      shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V) Δ (fineBondAt Y h₁ o₁ i).1 i =
        interpCoords s T.a T.chainParams.ρA (frameRadius x) V' (fineBondAt Y' h₁ o₁ i).1 i :=
    fun h₁ o₁ i hh ho hb => (hΔ3 _ hb).symm.trans (hΔ4 h₁ o₁ i hh (hFL ▸ ho))
  have small := ((hNT t x cs.coupling_le).single F V s cs.top cs.small cs.interp_mem.1 cs.interp_mem.2).2
  have small' := ((hNT t x cs.coupling_le).single F' V' s cs.top' cs.small' cs.interp_mem.1 cs.interp_mem.2).2
  have hsmallF : ∀ ξ ∈ openPolyball ι (2 * T.ballRadius), ∀ v ∈ Set.Icc (0 : ℝ) 1,
      IsSmallCurvature T.σ (chartedField (shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V)
        (pushforwardField j ξ + v • Δ)) V) ∧
        ∀ b ∈ chordBonds (finiteCells F),
          ‖shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V)
            (pushforwardField j ξ + v • Δ) b.1 b.2‖ ≤ 1 := by
    intro ξ hξ v hv
    have hb : ∀ b, ‖(pushforwardField j ξ + v • Δ) b‖ ≤ 3 * (T.σ / 64) := fun b => by
      have e1 := norm_pushforward_le hE j cs.injective ξ (2 * T.ballRadius) (by positivity)
        (fun k => (hξ k).le) b
      have e2 : ‖(v • Δ) b‖ ≤ T.ballRadius := by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hv.1]
        calc v * ‖Δ b‖ ≤ 1 * (T.Ct * T.σ * A) := mul_le_mul hv.2 (hΔ1 b) (norm_nonneg _) zero_le_one
          _ ≤ T.ballRadius := by rw [one_mul]; exact hθρ
      have e3 := norm_add_le (pushforwardField j ξ b) ((v • Δ) b)
      rw [Pi.add_apply]
      rw [hρdef] at e1 e2
      linarith
    obtain ⟨d1, d2⟩ := shifted_small hM hLC small hσ _ hb
    exact ⟨d1, fun b hb' => (d2 b hb').trans hone⟩
  have hsmallF' : ∀ ξ ∈ openPolyball ι (2 * T.ballRadius),
      IsSmallCurvature T.σ (chartedField (shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V')
        (pushforwardField j' ξ)) V') ∧
        ∀ b ∈ chordBonds (finiteCells F'),
          ‖shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V')
            (pushforwardField j' ξ) b.1 b.2‖ ≤ 1 := by
    intro ξ hξ
    have hb : ∀ b, ‖pushforwardField j' ξ b‖ ≤ 3 * (T.σ / 64) := fun b => by
      have e1 := norm_pushforward_le hE j' cs.injective' ξ (2 * T.ballRadius) (by positivity)
        (fun k => (hξ k).le) b
      rw [hρdef] at e1
      linarith [show (0 : ℝ) ≤ T.σ / 64 by positivity]
    obtain ⟨d1, d2⟩ := shifted_small hM hLC small' hσ _ hb
    exact ⟨d1, fun b hb' => (d2 b hb').trans hone⟩
  have hbox : WithinRadius (q / 8) o := fun i => by
    have := cs.offset_le i
    omega
  have hδ0 : 0 ≤ T.decayRate := by
    unfold StepParameters.decayRate
    positivity
  have hhpos : 0 < T.σ / 64 * e8 := by positivity
  have hhρ : T.σ / 64 * e8 ≤ T.ballRadius := by
    rw [hρdef]
    exact mul_le_of_le_one_right (by positivity) he81
  have hlow : IsCubicTorusAbove T.L t T.n₀ F := by
    obtain ⟨h1, h2, n, h3, h4⟩ := cs.top
    have hL0 : 0 < T.L := lt_of_lt_of_le (by norm_num) hn.side_large
    exact ⟨h1, h2, n, h3, h4.trans (Nat.le_mul_of_pos_right n hL0)⟩
  have hlow' : IsCubicTorusAbove T.L t T.n₀ F' := by
    obtain ⟨h1, h2, n, h3, h4⟩ := cs.top'
    have hL0 : 0 < T.L := lt_of_lt_of_le (by norm_num) hn.side_large
    exact ⟨h1, h2, n, h3, h4.trans (Nat.le_mul_of_pos_right n hL0)⟩
  have R := fun (u : Fin 4 → ℤ) (hu : u ∈ centredCube T.L) =>
    hR T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio h hodd hδ0 hE0 cs.family F F' _ _ V V' Y Y' q r₂ (q / 8)
      (T.Ct * T.σ * A) T.ballRadius (T.σ / 64 * e8) Δ ι j j' o u hlow hlow' hθ0 hρ hhpos hhρ (by omega) hsF hsF'
      cs.injective cs.injective' cs.paired hΔ1 hΔ2 hmoved hsmallF hsmallF' (agreeOnBall_mono (by omega) cs.agree)
      hbox (by omega) hu
  have hBg0 : 0 ≤ C * T.E / torusDecayFactor T.L T.decayRate ((T.L : ℝ) * ((r₂ : ℝ) - ((q / 8 : ℕ) : ℝ) - 2)) +
      2 * (C * T.E * (T.Ct * T.σ * A) * ((ballChordBonds F Y r₂).card : ℝ)) / (T.σ / 64 * e8) +
      2 * (C * T.E) * (T.σ / 64 * e8) +
      2 * (C * T.E) * Real.exp (-(T.decayRate * T.L * (((q / 2 : ℕ) : ℝ) - ((q / 8 : ℕ) : ℝ)))) := by
    have hw : 0 ≤ torusDecayFactor T.L T.decayRate ((T.L : ℝ) * ((r₂ : ℝ) - ((q / 8 : ℕ) : ℝ) - 2)) := by
      unfold torusDecayFactor
      positivity
    have : (0 : ℝ) < T.Ct := by linarith
    positivity
  obtain ⟨sm, hall⟩ := sum_diff_bounds (centredCube T.L)
    (fun u ζ => subtractTrivial h F (fineBondAt Y o u 0).1
      (chartedField (shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V)
        (pushforwardField j ζ)) V))
    (fun u ζ => subtractTrivial h F' (fineBondAt Y' o u 0).1
      (chartedField (shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V')
        (pushforwardField j' ζ)) V'))
    T.ballRadius _ _ hρ hBg0 (fun u hu => (R u hu).1) (fun u hu => (R u hu).2.1)
    (fun u hu ξ hξ => ((R u hu).2.2 ξ hξ).1) (fun u hu ξ hξ k e he => ((R u hu).2.2 ξ hξ).2 k e he)
  have hfun : (fun ζ => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h
        (Y' + _root_.YangMills.Construction.BlockAverages.siteOfCoords F'.top o) (pushforwardField j' ζ) V' -
      interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h
        (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) (pushforwardField j ζ) V) =
      fun ζ => ∑ u ∈ centredCube T.L, (subtractTrivial h F' (fineBondAt Y' o u 0).1
        (chartedField (shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V')
          (pushforwardField j' ζ)) V') -
        subtractTrivial h F (fineBondAt Y o u 0).1
          (chartedField (shiftCoordinates (interpCoords s T.a T.chainParams.ρA (frameRadius x) V)
            (pushforwardField j ζ)) V)) := by
    funext ζ
    rw [interpolatedBlockExpansion_eq hS s _ _ _ h V hoddF hs2, interpolatedBlockExpansion_eq hS s _ _ _ h V' hoddF' hs2',
      hFL, hFL', ← Finset.sum_sub_distrib]
    rfl
  have hcard : ((centredCube T.L).card : ℝ) = (T.L : ℝ) ^ 4 := by
    rw [LatticePaths.card_centredCube hodd]
    push_cast
    rfl
  have hN0 : (0 : ℝ) ≤ ((ballChordBonds F Y r₂).card : ℝ) := Nat.cast_nonneg _
  have hNb : ((ballChordBonds F Y r₂).card : ℝ) ≤ 4 * Q * (T.L : ℝ) ^ 4 := by
    have h1 := card_ballChordBonds_le hO Y r₂ hoddF hsr
    rw [hFL] at h1
    refine h1.trans ?_
    have h2 : (r₂ : ℝ) ≤ q := by exact_mod_cast (by omega : r₂ ≤ q)
    have h3 : (2 * (r₂ : ℝ) + 1) ^ 4 ≤ Q := by
      rw [hQdef]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h4 : (0 : ℝ) ≤ (T.L : ℝ) ^ 4 := by positivity
    gcongr
  have hδdef : T.decayRate = T.κ / 2 ^ 10 := rfl
  have hy : Real.exp (-(T.decayRate * ((T.L : ℝ) * ((r₂ : ℝ) - ((q / 8 : ℕ) : ℝ) - 2)))) ≤ e8 := by
    rw [he8]
    refine Real.exp_le_exp.2 ?_
    have hX : (q : ℝ) / 2 ≤ (r₂ : ℝ) - ((q / 8 : ℕ) : ℝ) - 2 := by linarith
    have hLX : (2 : ℝ) ^ 15 * ((q : ℝ) / 2) ≤ (T.L : ℝ) * ((r₂ : ℝ) - ((q / 8 : ℕ) : ℝ) - 2) :=
      mul_le_mul hLbig hX (by positivity) (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hLX hκ.le
    have h2 := mul_nonneg hκ.le hq0
    rw [hδdef]
    linarith
  have hy₄ : Real.exp (-(T.decayRate * T.L * (((q / 2 : ℕ) : ℝ) - ((q / 8 : ℕ) : ℝ)))) ≤ e8 := by
    rw [he8]
    refine Real.exp_le_exp.2 ?_
    have hX : (q : ℝ) / 4 ≤ ((q / 2 : ℕ) : ℝ) - ((q / 8 : ℕ) : ℝ) := by linarith
    have hLX : (2 : ℝ) ^ 15 * ((q : ℝ) / 4) ≤ (T.L : ℝ) * (((q / 2 : ℕ) : ℝ) - ((q / 8 : ℕ) : ℝ)) :=
      mul_le_mul hLbig hX (by positivity) (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hLX hκ.le
    have h2 := mul_nonneg hκ.le hq0
    rw [hδdef]
    linarith
  have hstar' : 2 ^ 14 * (C + 1) * T.Ct * (T.L : ℝ) ^ 8 * Q * A ≤ e8 * e8 := hstar
  have hfin : T.E * e8 * (2 ^ 14 * (C + 1) * T.Ct * (T.L : ℝ) ^ 8) ≤ T.E * Real.exp (-(7 * T.κ * q)) := by
    have h1 : e8 = Real.exp (-(7 * T.κ * q)) * Real.exp (-(T.κ * q)) := by
      rw [he8, ← Real.exp_add]
      congr 1
      ring
    have h2 : 2 ^ 14 * (C + 1) * T.Ct * (T.L : ℝ) ^ 8 * Real.exp (-(T.κ * q)) ≤ 1 :=
      (hn.decay q cs.radius_le).2
    have h3 := Real.exp_pos (-(7 * T.κ * q))
    rw [h1]
    calc T.E * (Real.exp (-(7 * T.κ * q)) * Real.exp (-(T.κ * q))) * (2 ^ 14 * (C + 1) * T.Ct * (T.L : ℝ) ^ 8)
        = T.E * Real.exp (-(7 * T.κ * q)) *
            (2 ^ 14 * (C + 1) * T.Ct * (T.L : ℝ) ^ 8 * Real.exp (-(T.κ * q))) := by ring
      _ ≤ T.E * Real.exp (-(7 * T.κ * q)) * 1 := by gcongr
      _ = T.E * Real.exp (-(7 * T.κ * q)) := mul_one _
  have hE₃ : T.E ≤ T.energyRatio := by
    show T.E ≤ T.E / T.η₃
    rw [le_div_iff₀ hT.η₃_pos]
    exact mul_le_of_le_one_right hE0 hT.η₃_le_one
  have hx0 : 0 ≤ x := hn.coupling_nonneg.trans cs.coupling_le
  have hsq : ∀ ξ : BondField ι,
      0 ≤ weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ :=
    fun ξ => Finset.sum_nonneg fun _ _ => by positivity
  unfold PairedPartsCompareSmoothly PairedPartsCompare
  beta_reduce
  rw [hfun]
  refine ⟨sm, fun ξ hξ => ⟨?_, fun k => ?_⟩⟩
  · have e := congrFun hfun ξ
    beta_reduce at e
    rw [e]
    have v := (hall ξ hξ).1
    rw [hcard] at v
    have vb := value_estimate (N := ((ballChordBonds F Y r₂).card : ℝ)) hE0 hC hCt hLr (by linarith) hApos.le
      he8pos he81 hσ.le hσ1 hN0 hNb hstar'
      ((div_torusDecayFactor_le T.L T.decayRate hE0).trans (mul_le_mul_of_nonneg_left hy hE0))
    have hg : 1 ≤ x * weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F)
        (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ + 1 := by
      have := mul_nonneg hx0 (hsq ξ)
      linarith
    have tn := target_estimate (d := 0) hE0 hE₃ hCt hκ hq0 (by positivity) hg
    rw [mul_zero, neg_zero, Real.exp_zero, mul_one] at tn
    exact v.trans (vb.trans (hfin.trans tn))
  · have v := (hall ξ hξ).2 k
    rw [hcard] at v
    have hCE : 0 ≤ C * T.E := by positivity
    have vb := grad_estimate (N := ((ballChordBonds F Y r₂).card : ℝ)) hE0 hC hCt hLr (by linarith) hApos.le
      he8pos hσ hσ1 hNb hstar'
      ((div_torusDecayFactor_le T.L T.decayRate hCE).trans (mul_le_mul_of_nonneg_left hy hCE)) hy₄
    have hg : 1 ≤ x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F)
        (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ) + 1 := by
      have := mul_nonneg hx0 (Real.sqrt_nonneg (weightedSqNormNear T.κ (fun k => bondBlock F (j k))
        (blockDist F) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ξ))
      linarith
    have hd : blockDist F (bondBlock F (j k)) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ≤ 9 / 8 * (q : ℝ) := by
      obtain ⟨g, u, kk, hu, hg', e1, e2⟩ := cs.paired k
      have hcell : bondBlock F (j k) = Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g := by
        unfold bondBlock
        rw [e1]
        exact (o1 g u kk hu).1
      have hoq : WithinRadius q o := fun l => (hbox l).trans (by exact_mod_cast (by omega : q / 8 ≤ q))
      have h1 := (hdist g q hg' hg').1
      have h2 := (hdist o (q / 8) hoq hbox).1
      have h3 := o8 (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o)
      have h4 : cellSupDist (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) ≤ q + q / 8 := by omega
      rw [hcell]
      show ((cellSupDist (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) : ℕ) : ℝ) ≤ _
      have h5 : ((cellSupDist (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top g) (Y + _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top o) : ℕ) : ℝ) ≤
          (q : ℝ) + ((q / 8 : ℕ) : ℝ) := by
        exact_mod_cast h4
      linarith
    have tn := target_estimate hE0 hE₃ hCt hκ hq0 hd hg
    exact v.trans (vb.trans (hfin.trans tn))
end YangMills.Construction.ColdStepAtMirrorFrames
end
