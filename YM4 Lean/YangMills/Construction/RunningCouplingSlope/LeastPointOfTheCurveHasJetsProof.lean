import YangMills.Construction.SummableBoundsOfTheFlow.TheSharesAtDrawnParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.FramesAlongUnitsProof
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.OneLeastChart
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import YangMills.Construction.RunningCouplingSlope.LeastPointOfTheCurveHasJets
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepSettings RenormalizationStepParameters StepCosts ColdChain TopLevelSites
open ColdStepAtMirrorFrames hiding bondSpread
namespace RunningCouplingSlope
namespace MinimizerJetAux
section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
private def collectCoords {k j : ℕ} (l : Fin j → Fin k) : (Fin j → ℝ) →L[ℝ] (Fin k → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun σ m => ∑ i, if l i = m then σ i else 0
      map_add' := fun u v => by
        funext m
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      map_smul' := fun r u => by
        funext m
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp }
private theorem collectCoords_apply {k j : ℕ} (l : Fin j → Fin k) (σ : Fin j → ℝ) (m : Fin k) :
    collectCoords l σ m = ∑ i, if l i = m then σ i else 0 := rfl
private theorem collectCoords_single {k j : ℕ} (l : Fin j → Fin k) (i : Fin j) :
    collectCoords l (Pi.single i 1) = Pi.single (l i) 1 := by
  funext m
  rw [collectCoords_apply, Finset.sum_eq_single i]
  · by_cases h : l i = m
    · subst h
      simp
    · simp [h, Ne.symm h]
  · intro b _ hb
    simp [hb]
  · simp
private theorem iteratedFDeriv_single_eq_comp {k j : ℕ} {f : (Fin k → ℝ) → E} (hf : ContDiffAt ℝ j f 0)
    (l : Fin j → Fin k) :
    iteratedFDeriv ℝ j f 0 (fun i => Pi.single (l i) 1) =
      iteratedFDeriv ℝ j (f ∘ collectCoords l) 0 (fun i => Pi.single i 1) := by
  obtain ⟨u, hu, hc⟩ := hf.contDiffOn (m := j) le_rfl (by simp)
  obtain ⟨U, hUu, hUo, h0U⟩ := mem_nhds_iff.1 hu
  have hcU : ContDiffOn ℝ j f U := hc.mono hUu
  have hpo : IsOpen (collectCoords l ⁻¹' U) := hUo.preimage (collectCoords l).continuous
  have h0 : collectCoords l 0 ∈ U := by simpa using h0U
  have key := (collectCoords l).iteratedFDerivWithin_comp_right hcU hUo.uniqueDiffOn hpo.uniqueDiffOn h0
    (i := j) le_rfl
  rw [iteratedFDerivWithin_of_isOpen j hpo (show (0 : Fin j → ℝ) ∈ collectCoords l ⁻¹' U from h0),
    iteratedFDerivWithin_of_isOpen j hUo h0, map_zero] at key
  rw [key, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  exact (collectCoords_single l i).symm
private theorem opNorm_le_of_basis {k j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin k → ℝ) E)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ l : Fin j → Fin k, ‖A fun i => Pi.single (l i) 1‖ ≤ M) :
    ‖A‖ ≤ (k : ℝ) ^ j * M := by apply _root_.YangMills.Construction.MovedTopMarks.UnitFamilies.opNorm_le_of_basis <;> assumption
end Calculus
private def euclideanCLM : imaginaryQuaternions →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := imaginaryToEuclidean
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp [imaginaryToEuclidean]
      map_smul' := fun r u => by
        ext i
        fin_cases i <;> simp [imaginaryToEuclidean] }
private theorem euclideanCLM_apply (v : imaginaryQuaternions) : euclideanCLM v = imaginaryToEuclidean v := rfl
section Top
variable {L t n : ℕ}
private theorem period_torusFrame (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
private def frameBonds {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)
private theorem readAtLevel_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X σ V) =
      rotatedField (bondSpread (frameBonds L t c) X σ) (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.DeltaSharedProofs.p501447 <;> assumption
private theorem bondSpread_collectCoords {F : BlockFrame} {k j : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (l : Fin j → Fin k) (σ : Fin j → ℝ) :
    bondSpread c X (collectCoords l σ) = bondSpread (c ∘ l) (X ∘ l) σ := by
  funext y i
  unfold bondSpread
  simp only [collectCoords_apply, Function.comp]
  have e : ∀ m, (if c m = (y, i) then (∑ s, if l s = m then σ s else 0) • X m else 0) =
      ∑ s, if l s = m then (if c (l s) = (y, i) then σ s • X (l s) else 0) else 0 := by
    intro m
    by_cases h : c m = (y, i)
    · rw [if_pos h, Finset.sum_smul]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : l s = m
      · simp [hs, h]
      · simp [hs]
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      by_cases hs : l s = m
      · simp [hs, h]
      · simp [hs]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp
private theorem isCold_trivialField [NeZero n] {s : ℝ} (hs : 0 < s) :
    IsCold (finiteCells (torusFrame L t n)) (torusFrame L t n).top s
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top (trivialField n)) := by
  rintro ⟨x, μ, ν⟩ _
  have e : readAtLevel (torusFrame L t n) (torusFrame L t n).top (trivialField n) = fun _ _ => 1 := rfl
  rw [e]
  simpa [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue] using hs
private theorem isOrthantRegular_finiteCells (hn : 2 ≤ n) (m : ℕ) :
    IsOrthantRegular (finiteCells (torusFrame L t n)) m := by
  intro z
  exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun q _ _ h _ _ => BlockOffsets.mem_finiteCells (fun _ => hn) _⟩
end Top
private theorem minimizingBondCoordinate_eq_zero (h1 : MinimizingChartUnique) {F : BlockFrame} {a ρ N0 σ : ℝ}
    {V : F.GaugeField F.top}
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hρ : ρ ≤ 1) (hN0 : 0 < N0) (hσ : 0 < σ)
    (hOne : ∀ s : ℝ, 0 < s → s ≤ σ → HasColdMinimizer a ρ N0 s (finiteCells F) V)
    (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds (finiteCells F)) :
    minimizingBondCoordinate a ρ (finiteCells F) b V = 0 := by
  have mono : ∀ {s : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions},
      IsMinimizingChart a (finiteCells F) V (min ρ (N0 * s)) w →
      IsMinimizingChart a (finiteCells F) V ρ w := fun h =>
    ⟨h.1, fun b hb => (h.2.1 b hb).trans (min_le_left _ _), h.2.2⟩
  obtain ⟨w₀, hw₀, -, -⟩ := hOne σ hσ le_rfl
  have hex : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w := ⟨w₀, mono hw₀⟩
  have small : ∀ s : ℝ, 0 < s → s ≤ σ → ‖hex.choose b.1 b.2‖ ≤ N0 * s := by
    intro s hs0 hsσ
    obtain ⟨w, hw, -, -⟩ := hOne s hs0 hsσ
    have e := (h1 F a ρ N0 s V w hL hs hρ (hOne s hs0 hsσ) (mono hw)).1 hex.choose hex.choose_spec
    rw [e]
    exact (hw.2.1 b hb).trans (min_le_right _ _)
  have zero : ‖hex.choose b.1 b.2‖ = 0 := by
    by_contra hne
    have hu : 0 < ‖hex.choose b.1 b.2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    set u := ‖hex.choose b.1 b.2‖ with hud
    have hs0 : 0 < min σ (u / (2 * N0)) := lt_min hσ (by positivity)
    have h2 := small _ hs0 (min_le_left _ _)
    have h3 : N0 * min σ (u / (2 * N0)) ≤ N0 * (u / (2 * N0)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hN0.le
    have h4 : N0 * (u / (2 * N0)) = u / 2 := by
      field_simp
    linarith
  unfold minimizingBondCoordinate minimizingCoordinates
  rw [dif_pos hex]
  exact norm_eq_zero.1 zero
end MinimizerJetAux
open MinimizerJetAux in
theorem minimizerCoordinatesJetBound_of_unique (h1 : MinimizingChartUnique) : MinimizerCoordinatesJetBound := by
  intro T hT k
  have hNpos : ∀ j, 0 < T.N j := hT.chain.2.2.2.2.2.2.2.1
  set D : ℝ := ∑ j ∈ Finset.range 6, (k : ℝ) ^ j * (‖euclideanCLM‖ * T.N j) with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => by
    have := hNpos j
    positivity
  refine ⟨1 + D, 0, by linarith, le_rfl, ?_⟩
  intro y R hy hR n _ c X hn hX
  have hn4096 : 4096 ≤ n := hT.n₀_ge.trans hn
  have hL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have ha : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hch : ColdChainConstants R.params.coupling T.δ₁ T.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hR.anchorRadius_eq]
    exact hT.chain
  obtain ⟨hδ, -, -, -, hρ1, hσ, -, -, hChain⟩ := hch
  have hodd : Odd (torusFrame R.params.side R.depth n).blockSide := by
    show Odd R.params.side
    rw [hL]
    exact hT.L_odd
  have hside : ∀ i, 2 ≤ (torusFrame R.params.side R.depth n).extent i := fun _ => by
    show 2 ≤ n
    omega
  have hamb : IsAdmissibleAmbient (torusFrame R.params.side R.depth n) := Or.inr fun _ => by
    show 64 ≤ n
    omega
  have hall := fun (s : ℝ) (hs : 0 < s) (hsσ : s ≤ T.σA) =>
    hChain (torusFrame R.params.side R.depth n) 1024 (finiteCells (torusFrame R.params.side R.depth n)) hL hamb le_rfl
      (isOrthantRegular_finiteCells (by omega) _) s
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (trivialField n))
      hs hsσ (isCold_trivialField hs)
  have hcoords := (hall T.σA hσ le_rfl).2.2.2.1
  have hcurve : ∀ τ : Fin k → ℝ, perturbedTop R n c X τ =
      rotatedField (bondSpread (frameBonds R.params.side R.depth c) X τ)
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (trivialField n)) :=
    fun τ => readAtLevel_perturb c X τ (trivialField n)
  set f : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))) → (Fin k → ℝ) → imaginaryQuaternions :=
    fun b τ => minimizingBondCoordinate R.params.coupling R.anchorRadius
      (finiteCells (torusFrame R.params.side R.depth n)) b.1 (perturbedTop R n c X τ) with hf
  have : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  have hfan : ∀ b, AnalyticAt ℝ (f b) 0 := fun b => by
    have e : f b = fun σ : Fin k → ℝ => minimizingBondCoordinate R.params.coupling R.anchorRadius
        (finiteCells (torusFrame R.params.side R.depth n)) b.1
        (rotatedField (bondSpread (frameBonds R.params.side R.depth c) X σ)
          (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
            (trivialField n))) := by
      funext σ
      simp only [hf, hcurve]
    rw [e]
    exact (hcoords b.1 b.2).1 k _ X
  have hfd : ∀ b (m : WithTop ℕ∞), ContDiffAt ℝ m (f b) 0 := fun b m => (hfan b).contDiffAt
  have hΓf : ∀ b, (fun τ => minimizerCoordinatesAlong R n c X τ b) = euclideanCLM ∘ f b := fun b => rfl
  have hΓ : ∀ m : WithTop ℕ∞, ContDiffAt ℝ m (minimizerCoordinatesAlong R n c X) 0 := fun m => by
    refine contDiffAt_pi.2 fun b => ?_
    rw [hΓf]
    exact euclideanCLM.contDiff.contDiffAt.comp 0 (hfd b m)
  refine ⟨?_, hΓ 5, ?_⟩
  · funext b
    have e0 : perturbedTop R n c X 0 =
        readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (trivialField n) := by
      rw [hcurve]
      funext x i
      simp [rotatedField, bondSpread, expUnit_zero]
    show imaginaryToEuclidean (minimizingBondCoordinate R.params.coupling R.anchorRadius
      (finiteCells (torusFrame R.params.side R.depth n)) b.1 (perturbedTop R n c X 0)) = 0
    rw [e0, minimizingBondCoordinate_eq_zero h1 hodd hside hρ1 (hNpos 0) hσ (fun s hs hsσ => (hall s hs hsσ).1) b.1 b.2,
      ← euclideanCLM_apply, map_zero]
  · intro j hj1 hj5
    have hbound : ‖iteratedFDeriv ℝ j (minimizerCoordinatesAlong R n c X) 0‖ ≤
        (k : ℝ) ^ j * (‖euclideanCLM‖ * T.N j) := by
      refine opNorm_le_of_basis _ (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (hNpos j).le) fun l => ?_
      rw [iteratedFDeriv_single_eq_comp (hΓ j) l]
      refine (pi_norm_le_iff_of_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (hNpos j).le)).2 fun b => ?_
      have hc1 : ContDiffAt ℝ j (minimizerCoordinatesAlong R n c X ∘ collectCoords l) 0 :=
        ContDiffAt.comp 0 (by simpa using hΓ j) (collectCoords l).contDiff.contDiffAt
      have hc2 : ContDiffAt ℝ j (f b ∘ collectCoords l) 0 :=
        ContDiffAt.comp 0 (by simpa using hfd b j) (collectCoords l).contDiff.contDiffAt
      have e1 := (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))) =>
        EuclideanSpace ℝ (Fin 3)) b).iteratedFDeriv_comp_left hc1 (i := j) le_rfl
      have e2 := euclideanCLM.iteratedFDeriv_comp_left hc2 (i := j) le_rfl
      have e3 : (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))) =>
          EuclideanSpace ℝ (Fin 3)) b) ∘ (minimizerCoordinatesAlong R n c X ∘ collectCoords l) =
            euclideanCLM ∘ (f b ∘ collectCoords l) := rfl
      rw [e3, e2] at e1
      have e4 := congrArg (fun A => A fun i => (Pi.single i 1 : Fin j → ℝ)) e1
      simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousLinearMap.proj_apply] at e4
      rw [← e4]
      refine (euclideanCLM.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _))
      have e5 : f b ∘ collectCoords l = fun σ : Fin j → ℝ =>
          minimizingBondCoordinate R.params.coupling R.anchorRadius
            (finiteCells (torusFrame R.params.side R.depth n)) b.1
            (rotatedField (bondSpread (frameBonds R.params.side R.depth c ∘ l) (X ∘ l) σ)
              (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
                (trivialField n))) := by
        funext σ
        simp only [Function.comp, hf, hcurve, bondSpread_collectCoords]
      rw [e5]
      have hm := ((hcoords b.1 b.2).2 j (frameBonds R.params.side R.depth c ∘ l) (X ∘ l) hj1 fun i => hX (l i))
      refine hm.trans ?_
      have hexp : Real.exp (-T.δ₁ *
          (bondListDistance (enclosingCell b.1.1) (frameBonds R.params.side R.depth c ∘ l) : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0 : ℝ) ≤
            (bondListDistance (enclosingCell b.1.1) (frameBonds R.params.side R.depth c ∘ l) : ℝ) := by
          positivity
        nlinarith
      calc T.N j * Real.exp (-T.δ₁ *
            (bondListDistance (enclosingCell b.1.1) (frameBonds R.params.side R.depth c ∘ l) : ℝ))
          ≤ T.N j * 1 := mul_le_mul_of_nonneg_left hexp (hNpos j).le
        _ = T.N j := mul_one _
    have hterm : (k : ℝ) ^ j * (‖euclideanCLM‖ * T.N j) ≤ D := by
      refine Finset.single_le_sum (f := fun j => (k : ℝ) ^ j * (‖euclideanCLM‖ * T.N j)) (fun i _ => ?_)
        (Finset.mem_range.2 (by omega))
      have := hNpos i
      positivity
    rw [Real.rpow_zero, mul_one]
    linarith
end RunningCouplingSlope
end YangMills.Construction
end
