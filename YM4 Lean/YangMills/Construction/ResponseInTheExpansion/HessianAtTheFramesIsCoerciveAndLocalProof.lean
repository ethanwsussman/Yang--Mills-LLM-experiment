import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MovesOfFreeBondsForm
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFieldIsCold
import YangMills.Construction.ResponseInTheExpansion.EntriesAtATopNearOneProof
import YangMills.Construction.ResponseInTheExpansion.HessianAtTheFramesIsCoerciveAndLocal
import YangMills.Construction.ResponseInTheExpansion.OneStepToSecondOrderProof
import YangMills.Construction.RunningCouplingSlope.InverseOfTheHessianOfTheChartProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames RenormalizationStepParameters FreeBondMoves TopLevelSites
namespace CoerciveLocal
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
private theorem deriv_deriv_two_lines {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u v : P) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => f (s • u + s' • v)) 0) 0 = fderiv ℝ (fun ζ => fderiv ℝ f ζ v) 0 u := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderStep.deriv_deriv_smul_add_eq_fderiv_fderiv <;> assumption
private theorem deriv_deriv_line {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u : P) :
    deriv (deriv fun τ : ℝ => f (τ • u)) 0 = fderiv ℝ (fun ζ => fderiv ℝ f ζ u) 0 u := by apply _root_.YangMills.SharedProofs.p4878 <;> assumption
private theorem fderiv_fderiv_apply_eq {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u v : P) :
    fderiv ℝ (fun ζ => fderiv ℝ f ζ v) 0 u = fderiv ℝ (fderiv ℝ f) 0 u v := by apply _root_.YangMills.SharedProofs.p13960 <;> assumption
private theorem fderiv_fderiv_symm {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u v : P) :
    fderiv ℝ (fderiv ℝ f) 0 u v = fderiv ℝ (fderiv ℝ f) 0 v u :=
  (hf.isSymmSndFDerivAt (by simp; norm_num)).eq u v
end Calculus
section Frames
variable {F : BlockFrame}
private theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
private theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
private theorem stepCoordinates_smul (τ : ℝ) (U : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (τ • U) x i = τ • stepCoordinates U x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_smul <;> assumption
private theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · simp only [dif_pos h, Pi.zero_apply]
    exact toImaginary_zero
  · simp [dif_neg h]
private theorem chartedField_congr (V : F.GaugeField F.top) {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : ∀ x i, ¬ IsAxialTreeBond ((x, i) : F.Site F.depth × Fin 4) → w x i = w' x i) :
    chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p9062 <;> assumption
private def coordinateUnit (p : ChartCoordinate F) : StepVariable (finiteCells F) :=
  bondVariation p.1 (EuclideanSpace.single (𝕜 := ℝ) p.2 1)
open Classical in
private theorem coordinateUnit_apply (p : ChartCoordinate F) (b : ↥(chordBonds (finiteCells F))) (i : Fin 3) :
    coordinateUnit p b i = if (b, i) = p then 1 else 0 := by
  unfold coordinateUnit bondVariation
  by_cases hb : b = p.1
  · subst hb
    simp only [Pi.single_eq_same, EuclideanSpace.single_apply]
    by_cases hi : i = p.2
    · subst hi
      simp
    · have : ¬ ((p.1, i) = p) := fun h => hi (congrArg Prod.snd h)
      simp [hi, this]
  · have : ¬ ((b, i) = p) := fun h => hb (congrArg Prod.fst h)
    simp [Pi.single_eq_of_ne hb, this]
open Classical in
private theorem twoCoordinateVariation_eq (p q : ChartCoordinate F) (s s' : ℝ) :
    twoCoordinateVariation p q s s' = s • coordinateUnit p + s' • coordinateUnit q := by
  funext b
  ext i
  have e : (s • coordinateUnit p + s' • coordinateUnit q) b i = s * coordinateUnit p b i + s' * coordinateUnit q b i := by
    simp
  rw [e, coordinateUnit_apply, coordinateUnit_apply]
  simp only [twoCoordinateVariation, mul_ite, mul_one, mul_zero]
open Classical in
private theorem sum_smul_coordinateUnit_apply (x : ChartCoordinate F → ℝ) (b : ↥(chordBonds (finiteCells F))) (i : Fin 3) :
    (∑ p, x p • coordinateUnit p) b i = x (b, i) := by
  let ev : StepVariable (finiteCells F) →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).toLinearMap.comp (LinearMap.proj b)
  have h : ev (∑ p, x p • coordinateUnit p) = ∑ p, x p * ev (coordinateUnit p) := by
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have h2 : ∀ p, ev (coordinateUnit p) = if (b, i) = p then 1 else 0 := fun p => coordinateUnit_apply p b i
  have h3 : ev (∑ p, x p • coordinateUnit p) = (∑ p, x p • coordinateUnit p) b i := rfl
  rw [← h3, h]
  simp [h2]
private theorem isAdmissibleChartPoint_of_le (hcov : BlocksCoverLowerLevel) {L : ℕ} {σA s₁ e : ℝ} (hF : IsBlockTorus L F)
    (hL : Odd L) (he0 : 0 ≤ e) (he : e ≤ 1 / (64 * (L : ℝ))) (hs₁ : 0 ≤ s₁) (hlt : s₁ + 8 * e < σA)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ e) (hV : IsSmallCurvature s₁ V) :
    IsAdmissibleChartPoint L σA w V := by
  exact _root_.YangMills.SharedProofs.p28958 (F := F) (L := L) (σA := σA)
    (s₁ := s₁) (e := e) hcov hF hL he0 he hs₁ hlt w V hw hV
end Frames
end CoerciveLocal
set_option maxHeartbeats 1000000 in
open CoerciveLocal in
theorem frameHessian_coercive_local (hEn : ChartEnergyDerivBounds) (hMir : ReflectedFieldSmallCurvature)
    (hcov : BlocksCoverLowerLevel) : frameHessianCoerciveLocalStatement := by
  intro T c hD hTies
  obtain ⟨eδ, elam, eρ, eσA, -, eN, -, hHo⟩ := hTies
  obtain ⟨C, hC, hE⟩ := hEn T.coupling T.side c hD.a_ge hD.L_odd hD.L_ge hHo
  refine ⟨C, hC, fun F m V hF hm hV => ?_⟩
  classical
  obtain ⟨-, -, hlam0, hρ0, hρ1, hσA0, -, hN0, -⟩ := hD.chain
  have hσ := hD.σ_pos
  have hσA : T.threshold ≤ c.σA := by
    rw [eσA]
    linarith [hD.σ_le]
  have hLeast : ∀ (G : BlockFrame) (W : G.GaugeField G.top), IsBlockTorus T.side G → IsSmallCurvature T.threshold W →
      ∀ b, ‖minimizingBondCoordinate T.coupling T.ρA (finiteCells G) b W‖ ≤ T.N 0 * T.threshold := by
    intro G W hG hW b
    have hodd : Odd G.blockSide := hG.1 ▸ hD.L_odd
    obtain ⟨n, hn, hside⟩ := hG.2
    have hs : ∀ i, 2 ≤ G.extent i := fun i => by rw [hside i]; omega
    have hcl := hHo.estimates G T.threshold W hG hσ hσA hW
    have hone : HasColdMinimizer T.coupling T.ρA (T.N 0) T.threshold (finiteCells G) W := by
      have h := hcl.minimizer
      rwa [eρ, eN] at h
    obtain ⟨w₀, hw₀, -, he⟩ := minimizingCoordinates_eq (ρ := T.ρA) hodd hs (by linarith [Real.pi_gt_three]) le_rfl hone
    unfold minimizingBondCoordinate
    rw [he]
    by_cases hb : b ∈ chordBonds (finiteCells G)
    · exact (hw₀.2.1 b hb).trans (min_le_right _ _)
    · rw [hw₀.1 b hb, norm_zero]
      have := hN0 0
      positivity
  have hFrame : ∀ b, ‖stepFrame false T.coupling T.ρA m b V‖ ≤ T.N 0 * T.threshold := by
    intro b
    simp only [stepFrame, Bool.false_eq_true, if_false]
    unfold bondFrameCoord
    split_ifs with hbig
    · exact hLeast (reflectedFrame F m) (reflectedField m (enclosingCell b.1) V) ⟨hF.1, 4 * m, by omega, fun _ => rfl⟩
        (hMir F m (enclosingCell b.1) V T.threshold (by omega) hV) (reflectedBond m b)
    · exact hLeast F V hF hV b
  have hodd : Odd F.blockSide := hF.1 ▸ hD.L_odd
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hall := hcov F hodd fun i => by have := hs i; omega
  have hchart : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
    have : d.1 + unitStep F.depth d.2 ∈ sitesOfCells (finiteCells F) F.depth := hall _
    simp [chordBonds, innerBonds, hall, hd]
  let w : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun x i =>
    if (x, i) ∈ chordBonds (finiteCells F) then stepFrame false T.coupling T.ρA m (x, i) V else 0
  have hwz : ∀ b : F.Site F.depth × Fin 4, b ∉ chordBonds (finiteCells F) → w b.1 b.2 = 0 := fun b hb => if_neg hb
  have hws : ∀ b : F.Site F.depth × Fin 4, ‖w b.1 b.2‖ ≤ T.N 0 * T.threshold := by
    intro b
    by_cases hb : b ∈ chordBonds (finiteCells F)
    · have : w b.1 b.2 = stepFrame false T.coupling T.ρA m b V := if_pos hb
      rw [this]
      exact hFrame b
    · rw [hwz b hb, norm_zero]
      have := hN0 0
      positivity
  have hNσ : 0 ≤ T.N 0 * T.threshold := by
    have := hN0 0
    positivity
  have hρdef : T.ballRadius = T.threshold / 64 := rfl
  have hL1 : (1 : ℝ) ≤ T.side := by exact_mod_cast hD.L_odd.pos
  have hesmall : T.N 0 * T.threshold ≤ 1 / (64 * (T.side : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 := hD.σ_L
    have h2 : (T.side : ℝ) * T.threshold > 0 := by positivity
    nlinarith
  have hlt : T.threshold + 8 * (T.N 0 * T.threshold) < c.σA := by
    rw [eσA]
    have h1 := hD.cold_le
    rw [hρdef] at h1
    nlinarith
  have hsmall : IsAdmissibleChartPoint T.side c.σA w V :=
    isAdmissibleChartPoint_of_le hcov hF hD.L_odd hNσ hesmall hσ.le hlt w V (fun b _ => hws b) hV
  have hmoved : shiftCoordinates w (0 : StepVariable (finiteCells F)) = w := by
    funext x i
    unfold shiftCoordinates
    rw [stepCoordinates_zero, add_zero]
  obtain ⟨hf, -, hsec, -⟩ := hE F w 0 V hF (by rw [hmoved]; exact hsmall)
  have hen : ∀ η, chartedEnergy T.coupling (coordsAboveFrame false T.coupling T.ρA m V η) V =
      chartedEnergyAt T.coupling w V η := by
    intro η
    have h := chartedField_congr V (w := coordsAboveFrame false T.coupling T.ρA m V η)
      (w' := fun x i => w x i + stepCoordinates η x i) fun x i hnt => by
        have hm' := hchart _ hnt
        have e0 : w x i = stepFrame false T.coupling T.ρA m (x, i) V := if_pos hm'
        show stepFrame false T.coupling T.ρA m (x, i) V + stepCoordinates η x i = w x i + stepCoordinates η x i
        rw [e0]
    unfold chartedEnergyAt chartedEnergy
    rw [h]
  have hHess : ∀ p q : ChartCoordinate F, frameHessian T.coupling T.ρA m V p q =
      fderiv ℝ (fderiv ℝ (chartedEnergyAt T.coupling w V)) 0 (coordinateUnit p) (coordinateUnit q) := by
    intro p q
    have e : frameHessian T.coupling T.ρA m V p q =
        deriv (fun s : ℝ => deriv (fun s' : ℝ =>
          chartedEnergyAt T.coupling w V (s • coordinateUnit p + s' • coordinateUnit q)) 0) 0 := by
      show deriv (fun s : ℝ => deriv (fun s' : ℝ =>
        chartedEnergy T.coupling (coordsAboveFrame false T.coupling T.ρA m V (twoCoordinateVariation p q s s')) V) 0) 0 = _
      simp only [hen, twoCoordinateVariation_eq]
    rw [e, deriv_deriv_two_lines hf, fderiv_fderiv_apply_eq hf]
  refine ⟨Matrix.IsSymm.ext fun p q => ?_, fun x => ?_, fun p q => ?_⟩
  · rw [hHess, hHess, fderiv_fderiv_symm hf]
  · set U : StepVariable (finiteCells F) := ∑ p, x p • coordinateUnit p with hU
    have hquad : ∑ p, x p * (frameHessian T.coupling T.ρA m V).mulVec x p =
        fderiv ℝ (fderiv ℝ (chartedEnergyAt T.coupling w V)) 0 U U := by
      have h1 : fderiv ℝ (fderiv ℝ (chartedEnergyAt T.coupling w V)) 0 U U =
          ∑ p, ∑ q, x p * (x q * fderiv ℝ (fderiv ℝ (chartedEnergyAt T.coupling w V)) 0
            (coordinateUnit p) (coordinateUnit q)) := by
        rw [hU]
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        ring
      rw [h1]
      refine Finset.sum_congr rfl fun p _ => ?_
      show x p * ∑ q, frameHessian T.coupling T.ρA m V p q * x q = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hHess]
      ring
    have hcl := hHo.estimates F T.threshold V hF hσ hσA hV
    have hdz : ∀ b : F.Site F.depth × Fin 4, b ∉ chordBonds (finiteCells F) → stepCoordinates U b.1 b.2 = 0 := by
      intro b hb
      unfold stepCoordinates
      rw [dif_neg hb]
    have hwρ : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ c.ρA := by
      intro b _
      rw [eρ]
      have h1 := hD.ρ_le
      have h2 := hws b
      have h3 : 0 < T.ballRadius := by
        rw [hρdef]
        positivity
      linarith
    have hcw : IsCold (finiteCells F) F.depth c.σA (chartedField w V) := fun p hp => by
      simp only [innerPlaquettes, Finset.mem_filter] at hp
      exact hsmall.small_curvature p hp.2.1
    have hfl := hcl.hessian w (stepCoordinates U) hwz hdz hwρ hcw
    have e1 : (fun τ : ℝ => blockEnergy T.coupling (finiteCells F) F.depth
        (chartedField (fun x i => w x i + τ • stepCoordinates U x i) V) V) =
        fun τ : ℝ => chartedEnergyAt T.coupling w V (τ • U) := by
      funext τ
      unfold chartedEnergyAt chartedEnergy
      simp only [stepCoordinates_smul]
    rw [e1, deriv_deriv_line hf, fderiv_fderiv_apply_eq hf, ← hquad, elam] at hfl
    have e2 : ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates U b.1 b.2‖ ^ 2 = ∑ p, x p ^ 2 := by
      rw [← Finset.sum_coe_sort, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hb : stepCoordinates U b.1.1 b.1.2 = toImaginary (U b) := by
        unfold stepCoordinates
        rw [dif_pos b.2]
      rw [hb, norm_toImaginary, EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hU, sum_smul_coordinateUnit_apply]
    rwa [e2] at hfl
  · rw [hHess]
    have h := hsec q.1 p.1 (EuclideanSpace.single q.2 1) (EuclideanSpace.single p.2 1)
    have e : ColdStepAtMirrorFrames.secondDerivAlong (chartedEnergyAt T.coupling w V) 0
        (bondVariation q.1 (EuclideanSpace.single q.2 1)) (bondVariation p.1 (EuclideanSpace.single p.2 1)) =
        fderiv ℝ (fderiv ℝ (chartedEnergyAt T.coupling w V)) 0 (coordinateUnit p) (coordinateUnit q) :=
      fderiv_fderiv_apply_eq hf _ _
    rw [e] at h
    have hd : chordBondDist F q.1 p.1 = chordBondDist F p.1 q.1 := by
      unfold chordBondDist
      rw [cellSupDist_comm]
    rw [hd, eδ] at h
    simpa using h
end YangMills.Construction.ResponseInTheExpansion
end
