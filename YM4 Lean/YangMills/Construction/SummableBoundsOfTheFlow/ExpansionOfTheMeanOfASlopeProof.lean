import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfASlope
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfTheMeanOfASlope
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory Topology
namespace YangMills.Construction
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Estimates YangMills.Construction.Cumulants
namespace SlopeMeanExpansion
variable {F : BlockFrame}
theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
def sublistEmbedding {j k : ℕ} (e : Fin j → Fin k) : (Fin j → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ l, if e l = i then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) l else 0
theorem iteratedFDeriv_sublist_eq_bondDeriv (hS : SmoothSlices.IteratedFDerivSlices) {j k : ℕ}
    (g : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) {e : Fin j → Fin k} (he : Function.Injective e)
    (hg : ContDiffAt ℝ j (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V)) 0) :
    iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V)) 0
        (fun l => Pi.single (e l) 1) = bondDeriv g V (c ∘ e) (X ∘ e) := by apply _root_.YangMills.Construction.Estimates.GibbsMeanExpansionInField.iteratedFDeriv_sublist_eq_bondDeriv <;> assumption
section Congr
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A f f' g g' h h' l l' : Ω → ℝ}
theorem gibbsCovariance_congr (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    gibbsCovariance μ A f g = gibbsCovariance μ A f' g' := by apply _root_.YangMills.Construction.Estimates.GibbsMeanExpansionInField.gibbsCovariance_congr_ae <;> assumption
theorem gibbsCumulantThree_congr (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') (hh : h =ᵐ[μ] h') :
    gibbsCumulantThree μ A f g h = gibbsCumulantThree μ A f' g' h' := by apply _root_.YangMills.Construction.Estimates.GibbsMeanExpansionInField.gibbsCumulantThree_congr_ae <;> assumption
theorem gibbsCumulantFour_congr (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') (hh : h =ᵐ[μ] h')
    (hl : l =ᵐ[μ] l') :
    gibbsCumulantFour μ A f g h l = gibbsCumulantFour μ A f' g' h' l' := by apply _root_.YangMills.Construction.Estimates.GibbsMeanExpansionInField.gibbsCumulantFour_congr_ae <;> assumption
end Congr
def cutoffSlopeCLM (p : ℝ → ℝ) (η : StepVariable (finiteCells F)) :
    StepVariable (finiteCells F) →L[ℝ] ℝ :=
  ∑ b, (deriv p ‖η b‖ * ‖η b‖⁻¹) •
    (innerSL ℝ (η b)).comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b)
theorem cutoffSlopeCLM_apply (p : ℝ → ℝ) (η e : StepVariable (finiteCells F)) :
    cutoffSlopeCLM p η e = cutoffSlope p e η := by
  unfold cutoffSlopeCLM cutoffSlope
  simp [_root_.sum_apply]
set_option maxHeartbeats 2000000 in
theorem cutoffSlopeMeanExpansion_holds (hS : SmoothSlices.IteratedFDerivSlices)
    (hSl : cutoffSlopeMeanDerivFormulas) (hRim : CutoffMeanIsGibbsMean)
    (hDom : DominatedFamilyOnClosedBalls) : CutoffSlopeMeanExpansion := by
  intro F ρ p V A e hρ hp hA he
  obtain ⟨hfin, hμ0, hμb, hrm⟩ := hRim F ρ p hρ hp
  have := hfin
  set μ := cutoffLaw F ρ p with hμdef
  have hμc : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ := by
    filter_upwards [hμb] with η hη b using (hη b).le
  have wm : ∀ A₀ f : StepVariable (finiteCells F) → ℝ,
      ballExpectation (cutoffFactor ρ p) A₀ f = gibbsMean μ A₀ f := fun A₀ f => hrm A₀ f
  have wc : ∀ A₀ f g : StepVariable (finiteCells F) → ℝ,
      ballCovariance (cutoffFactor ρ p) A₀ f g = gibbsCovariance μ A₀ f g := fun A₀ f g => by
    simp only [ballCovariance, gibbsCovariance, wm]
  have wt : ∀ A₀ f g h : StepVariable (finiteCells F) → ℝ,
      ballThirdCumulant (cutoffFactor ρ p) A₀ f g h = gibbsCumulantThree μ A₀ f g h :=
    fun A₀ f g h => by
      simp only [ballThirdCumulant, gibbsCumulantThree, wm]
  have wf : ∀ A₀ f g h l : StepVariable (finiteCells F) → ℝ,
      ballFourthCumulant (cutoffFactor ρ p) A₀ f g h l = gibbsCumulantFour μ A₀ f g h l :=
    fun A₀ f g h l => by
      simp only [ballFourthCumulant, gibbsCumulantFour, wm]
  have dom : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G →
      ∃ r M : ℝ, 0 < r ∧ IsDominatedSmoothFamily μ 3 (Metric.ball 0 r) M
        (fun τ η => G η (leftTranslate (bondSpread c X τ) V)) := by
    intro k c X G hG
    have hπ : ContDiff ℝ 3
        (fun z : (Fin k → ℝ) × (ℝ × StepVariable (finiteCells F)) => (z.1, z.2.2)) :=
      contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
    obtain ⟨r, M, hr, hD⟩ := hDom ↥(chordBonds (finiteCells F)) k ρ μ
      (fun z => G z.2.2 (leftTranslate (bondSpread c X z.1) V)) hμc
      (fun v η _ hη => ContDiffAt.comp
        (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
          G q.2 (leftTranslate (bondSpread c X q.1) V))
        (0, v, η) (hG k c X η hη) hπ.contDiffAt)
    exact ⟨r, M, hr, hD 0 (by simp)⟩
  have mono : ∀ {k : ℕ} {B B' : Set (Fin k → ℝ)} {K K' : ℝ}
      {G : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ},
      B' ⊆ B → K ≤ K' → IsDominatedSmoothFamily μ 3 B K G → IsDominatedSmoothFamily μ 3 B' K' G := by
    intro k B B' K K' G hB hK h
    refine ⟨fun τ hτ => h.aestronglyMeasurable τ (hB hτ), ?_, ?_⟩
    · filter_upwards [h.contDiffOn] with ω hω using hω.mono hB
    · filter_upwards [h.norm_iteratedFDeriv_le] with ω hω j hj τ hτ using le_trans (hω j hj τ (hB hτ)) hK
  have vec : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ∃ (r M : ℝ), 0 < r ∧
        ContDiffOn ℝ 3 (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V))
          (Metric.ball 0 r) ∧ ∀ j, j ≤ 3 → ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
          ‖iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) τ‖ ≤ M := by
    intro k c X
    obtain ⟨u, hu, hc⟩ := (he k c X).contDiffOn (m := 3) le_rfl (by simp)
    obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hu
    have hc' : ContDiffOn ℝ 3 (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V))
        (Metric.ball 0 r₀) :=
      hc.mono hball
    have hK : IsCompact (Metric.closedBall (0 : Fin k → ℝ) (r₀ / 2)) := isCompact_closedBall _ _
    have hsub : Metric.closedBall (0 : Fin k → ℝ) (r₀ / 2) ⊆ Metric.ball 0 r₀ :=
      Metric.closedBall_subset_ball (by linarith)
    have hb : ∀ j : ℕ, j ≤ 3 → ∃ M, ∀ τ ∈ Metric.closedBall (0 : Fin k → ℝ) (r₀ / 2),
        ‖iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) τ‖ ≤ M := by
      intro j hj
      have hco0 : ContinuousOn (iteratedFDerivWithin ℝ j
          (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) (Metric.ball 0 r₀))
          (Metric.ball 0 r₀) :=
        ContDiffOn.continuousOn_iteratedFDerivWithin hc' (by exact_mod_cast hj)
          Metric.isOpen_ball.uniqueDiffOn
      have hco : ContinuousOn (iteratedFDeriv ℝ j
          (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V))) (Metric.ball 0 r₀) :=
        hco0.congr fun z hz => (iteratedFDerivWithin_of_isOpen j Metric.isOpen_ball hz).symm
      obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hco.mono hsub)
      exact ⟨M, hM⟩
    choose! M hM using hb
    refine ⟨r₀ / 2, ∑ j ∈ Finset.range 4, |M j|, by positivity,
      hc'.mono (Metric.ball_subset_ball (by linarith)), fun j hj τ hτ => ?_⟩
    refine ((hM j hj τ (Metric.ball_subset_closedBall hτ)).trans (le_abs_self _)).trans ?_
    exact Finset.single_le_sum (f := fun j => |M j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have pair : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ∃ (B : Set (Fin k → ℝ)) (K : ℝ), IsOpen B ∧ B ∈ 𝓝 (0 : Fin k → ℝ) ∧
        IsDominatedSmoothFamily μ 3 B K (fun τ η => A η (leftTranslate (bondSpread c X τ) V)) ∧
        ContDiffOn ℝ 3 (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) B ∧
        ∀ j, j ≤ 3 → ∀ τ ∈ B,
          ‖iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) τ‖ ≤ K := by
    intro k c X
    obtain ⟨r₁, M₁, h₁, d₁⟩ := dom k c X A hA
    obtain ⟨r₂, M₂, h₂, d₂, b₂⟩ := vec k c X
    refine ⟨Metric.ball 0 (min r₁ r₂), max M₁ M₂, Metric.isOpen_ball,
      Metric.ball_mem_nhds _ (lt_min h₁ h₂), mono (Metric.ball_subset_ball (min_le_left _ _))
        (le_max_left _ _) d₁, d₂.mono (Metric.ball_subset_ball (min_le_right _ _)), fun j hj τ hτ =>
        (b₂ j hj τ (Metric.ball_subset_ball (min_le_right _ _) hτ)).trans (le_max_right _ _)⟩
  have fam : ∀ {k j : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G → j ≤ 3 →
      ∀ (v : Fin j → Fin k → ℝ) (e : Fin j → Fin k) (c' : Fin j → F.Site F.top × Fin 4)
        (X' : Fin j → imaginaryQuaternions),
      Function.Injective e → v = (fun l => Pi.single (e l) 1) → c ∘ e = c' → X ∘ e = X' →
      paramIteratedDeriv (fun τ η => G η (leftTranslate (bondSpread c X τ) V)) v 0 =ᵐ[μ]
        fieldDeriv G V c' X' := by
    intro k j c X G hG hj v e c' X' he hv hc hX
    filter_upwards [hμc] with η hη
    have hs : ContDiffAt ℝ j (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 := by
      have h3 := hG k c X η hη
      have hemb : ContDiff ℝ 3 (fun τ : Fin k → ℝ => (τ, η)) := contDiff_id.prodMk contDiff_const
      have := ContDiffAt.comp
        (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
          G q.2 (leftTranslate (bondSpread c X q.1) V))
        (0 : Fin k → ℝ) h3 hemb.contDiffAt
      exact ContDiffAt.of_le this (by exact_mod_cast hj)
    subst hv hc hX
    exact iteratedFDeriv_sublist_eq_bondDeriv hS (G η) V c X he hs
  have fam1 : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G →
      ∀ i : Fin k,
      paramIteratedDeriv (fun τ η => G η (leftTranslate (bondSpread c X τ) V)) ![Pi.single i 1] 0 =ᵐ[μ]
        fieldDerivOne G V c X i := by
    intro k c X G hG i
    exact fam (j := 1) c X G hG (by norm_num) _ ![i] _ _ (Function.injective_of_subsingleton _)
      (by funext l; fin_cases l; rfl) (by funext l; fin_cases l; rfl) (by funext l; fin_cases l; rfl)
  have fam2 : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G →
      ∀ i j : Fin k, i ≠ j →
      paramIteratedDeriv (fun τ η => G η (leftTranslate (bondSpread c X τ) V))
        ![Pi.single i 1, Pi.single j 1] 0 =ᵐ[μ] fieldDerivTwo G V c X i j := by
    intro k c X G hG i j hij
    exact fam (j := 2) c X G hG (by norm_num) _ ![i, j] _ _
      (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
      (by funext l; fin_cases l <;> rfl) (by funext l; fin_cases l <;> rfl)
      (by funext l; fin_cases l <;> rfl)
  have famFull : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G → k ≤ 3 →
      ∀ v : Fin k → Fin k → ℝ, v = (fun l => Pi.single l 1) →
      paramIteratedDeriv (fun τ η => G η (leftTranslate (bondSpread c X τ) V)) v 0 =ᵐ[μ]
        fieldDeriv G V c X := by
    intro k c X G hG hk v hv
    exact fam c X G hG hk v id c X Function.injective_id hv rfl rfl
  have sl : ∀ {k j : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), j ≤ 3 →
      ∀ (v : Fin j → Fin k → ℝ) (i : Fin j → Fin k) (c' : Fin j → F.Site F.top × Fin 4)
        (X' : Fin j → imaginaryQuaternions),
      Function.Injective i → v = (fun l => Pi.single (i l) 1) → c ∘ i = c' → X ∘ i = X' →
      cutoffSlope p
          (iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) 0 v) =
        fieldDeriv (cutoffSlopeAlong p e) V c' X' := by
    intro k j c X hj v i c' X' hi hv hc hX
    funext η
    have hat : ContDiffAt ℝ j (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) 0 :=
      (he k c X).of_le (by exact_mod_cast hj)
    have hco := (cutoffSlopeCLM p η).iteratedFDeriv_comp_left hat (i := j) le_rfl
    have hsm : ContDiffAt ℝ j
        (fun τ : Fin k → ℝ => cutoffSlopeAlong p e η (leftTranslate (bondSpread c X τ) V)) 0 := by
      have h1 : (fun τ : Fin k → ℝ => cutoffSlopeAlong p e η (leftTranslate (bondSpread c X τ) V)) =
          (cutoffSlopeCLM p η) ∘ fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V) := by
        funext τ
        simp only [Function.comp, cutoffSlopeCLM_apply, cutoffSlopeAlong]
      rw [h1]
      exact (cutoffSlopeCLM p η).contDiff.contDiffAt.comp 0 hat
    subst hv hc hX
    have h2 := iteratedFDeriv_sublist_eq_bondDeriv hS (cutoffSlopeAlong p e η) V c X hi hsm
    have h1 : (fun τ : Fin k → ℝ => cutoffSlopeAlong p e η (leftTranslate (bondSpread c X τ) V)) =
        (cutoffSlopeCLM p η) ∘ fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V) := by
      funext τ
      simp only [Function.comp, cutoffSlopeCLM_apply, cutoffSlopeAlong]
    show _ = bondDeriv (cutoffSlopeAlong p e η) V (c ∘ i) (X ∘ i)
    rw [← h2, h1, hco]
    rw [← cutoffSlopeCLM_apply]
    rfl
  have sl1 : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (i : Fin k),
      cutoffSlope p (iteratedFDeriv ℝ 1 (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) 0
        ![Pi.single i 1]) = fieldDerivOne (cutoffSlopeAlong p e) V c X i := by
    intro k c X i
    exact sl (j := 1) c X (by norm_num) _ ![i] _ _ (Function.injective_of_subsingleton _)
      (by funext l; fin_cases l; rfl) (by funext l; fin_cases l; rfl) (by funext l; fin_cases l; rfl)
  have sl2 : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (i j : Fin k), i ≠ j →
      cutoffSlope p (iteratedFDeriv ℝ 2 (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) 0
        ![Pi.single i 1, Pi.single j 1]) = fieldDerivTwo (cutoffSlopeAlong p e) V c X i j := by
    intro k c X i j hij
    exact sl (j := 2) c X (by norm_num) _ ![i, j] _ _
      (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
      (by funext l; fin_cases l <;> rfl) (by funext l; fin_cases l <;> rfl)
      (by funext l; fin_cases l <;> rfl)
  have slFull : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      ∀ v : Fin k → Fin k → ℝ, v = (fun l => Pi.single l 1) →
      cutoffSlope p
          (iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) 0 v) =
        fieldDeriv (cutoffSlopeAlong p e) V c X := by
    intro k c X hk v hv
    exact sl c X hk v id c X Function.injective_id hv rfl rfl
  have h0 : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ),
      (fun η => G η (leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V)) = fun η => G η V := by
    intro k c X G
    funext η
    rw [leftTranslate_bondSpread_zero]
  have h0e : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      cutoffSlope p (e (leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V)) =
        fun η => cutoffSlopeAlong p e η V := by
    intro k c X
    rw [leftTranslate_bondSpread_zero]
    rfl
  have hmeanEq : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      (fun τ : Fin k → ℝ =>
          gibbsMeanAt μ A (cutoffSlopeAlong p e) (leftTranslate (bondSpread c X τ) V)) =
        fun τ => ballExpectation (cutoffFactor ρ p) (fun η => A η (leftTranslate (bondSpread c X τ) V))
          (cutoffSlope p (e (leftTranslate (bondSpread c X τ) V))) := by
    intro k c X
    funext τ
    rw [wm]
    rfl
  refine ⟨fun k c X => ?_, ?_⟩
  · obtain ⟨B, K, hBo, hB0, dA, dE, bE⟩ := pair k c X
    rw [hmeanEq]
    exact (hSl F ρ p k B K _ _ hρ hp hBo dA dE bE).1.contDiffAt hB0
  constructor
  · intro c X
    obtain ⟨B, K, hBo, hB0, dA, dE, bE⟩ := pair 1 c X
    have hM := (hSl F ρ p 1 B K _ _ hρ hp hBo dA dE bE).2 0 (mem_of_mem_nhds hB0)
      (Pi.single 0 1) (Pi.single 0 1) (Pi.single 0 1)
    have hu : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = ![Pi.single 0 1] := by
      funext l
      fin_cases l; rfl
    have e0 : bondDeriv (gibbsMeanAt μ A (cutoffSlopeAlong p e)) V c X =
        iteratedFDeriv ℝ 1 (fun τ : Fin 1 → ℝ =>
          ballExpectation (cutoffFactor ρ p) (fun η => A η (leftTranslate (bondSpread c X τ) V))
            (cutoffSlope p (e (leftTranslate (bondSpread c X τ) V)))) 0 ![Pi.single 0 1] := by
      unfold bondDeriv
      rw [hmeanEq, hu]
    rw [e0]
    refine hM.1.trans ?_
    beta_reduce
    rw [h0 c X A, h0e c X, wm, wc, slFull c X (by norm_num) _ hu.symm]
    rw [gibbsCovariance_congr Filter.EventuallyEq.rfl (famFull c X A hA (by norm_num) _ hu.symm)]
  · intro c X
    obtain ⟨B, K, hBo, hB0, dA, dE, bE⟩ := pair 2 c X
    have hM := (hSl F ρ p 2 B K _ _ hρ hp hBo dA dE bE).2 0 (mem_of_mem_nhds hB0)
      (Pi.single 1 1) (Pi.single 0 1) (Pi.single 0 1)
    have hu : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
      funext l
      fin_cases l <;> rfl
    have e0 : bondDeriv (gibbsMeanAt μ A (cutoffSlopeAlong p e)) V c X =
        iteratedFDeriv ℝ 2 (fun τ : Fin 2 → ℝ =>
          ballExpectation (cutoffFactor ρ p) (fun η => A η (leftTranslate (bondSpread c X τ) V))
            (cutoffSlope p (e (leftTranslate (bondSpread c X τ) V)))) 0
          ![Pi.single 0 1, Pi.single 1 1] := by
      unfold bondDeriv
      rw [hmeanEq, hu]
    rw [e0]
    refine hM.2.1.trans ?_
    beta_reduce
    simp only [wm, wc, wt]
    rw [h0 c X A, h0e c X, slFull c X (by norm_num) _ hu.symm, sl1 c X 0, sl1 c X 1]
    have eH0 : (fun η => cutoffSlopeAlong p e η V) =ᵐ[μ] fun η => cutoffSlopeAlong p e η V :=
      Filter.EventuallyEq.rfl
    rw [gibbsCovariance_congr Filter.EventuallyEq.rfl (fam1 c X A hA 1),
      gibbsCovariance_congr Filter.EventuallyEq.rfl (fam1 c X A hA 0)]
    rw [gibbsCovariance_congr eH0 (famFull c X A hA (by norm_num) _ hu.symm),
      gibbsCumulantThree_congr eH0 (fam1 c X A hA 1) (fam1 c X A hA 0)]
  · intro c X
    obtain ⟨B, K, hBo, hB0, dA, dE, bE⟩ := pair 3 c X
    have hM := (hSl F ρ p 3 B K _ _ hρ hp hBo dA dE bE).2 0 (mem_of_mem_nhds hB0)
      (Pi.single 2 1) (Pi.single 1 1) (Pi.single 0 1)
    have hu : (fun l : Fin 3 => (Pi.single l 1 : Fin 3 → ℝ)) =
        ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
      funext l
      fin_cases l <;> rfl
    have e0 : bondDeriv (gibbsMeanAt μ A (cutoffSlopeAlong p e)) V c X =
        iteratedFDeriv ℝ 3 (fun τ : Fin 3 → ℝ =>
          ballExpectation (cutoffFactor ρ p) (fun η => A η (leftTranslate (bondSpread c X τ) V))
            (cutoffSlope p (e (leftTranslate (bondSpread c X τ) V)))) 0
          ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
      unfold bondDeriv
      rw [hmeanEq, hu]
    rw [e0]
    refine hM.2.2.trans ?_
    beta_reduce
    simp only [wm, wc, wt, wf]
    rw [h0 c X A, h0e c X, slFull c X (by norm_num) _ hu.symm, sl2 c X 1 2 (by decide),
      sl2 c X 0 2 (by decide), sl2 c X 0 1 (by decide), sl1 c X 2, sl1 c X 1, sl1 c X 0]
    have eH0 : (fun η => cutoffSlopeAlong p e η V) =ᵐ[μ] fun η => cutoffSlopeAlong p e η V :=
      Filter.EventuallyEq.rfl
    have er : ∀ {f : StepVariable (finiteCells F) → ℝ}, f =ᵐ[μ] f := Filter.EventuallyEq.rfl
    rw [gibbsCovariance_congr er (fam1 c X A hA 0), gibbsCovariance_congr er (fam1 c X A hA 1),
      gibbsCovariance_congr er (fam1 c X A hA 2),
      gibbsCovariance_congr er (fam2 c X A hA 0 1 (by decide)),
      gibbsCovariance_congr er (fam2 c X A hA 0 2 (by decide)),
      gibbsCovariance_congr er (fam2 c X A hA 1 2 (by decide)),
      gibbsCumulantThree_congr er (fam1 c X A hA 1) (fam1 c X A hA 0),
      gibbsCumulantThree_congr er (fam1 c X A hA 2) (fam1 c X A hA 0),
      gibbsCumulantThree_congr er (fam1 c X A hA 2) (fam1 c X A hA 1),
      gibbsCovariance_congr eH0 (famFull c X A hA (by norm_num) _ hu.symm),
      gibbsCumulantThree_congr eH0 (fam2 c X A hA 1 2 (by decide)) (fam1 c X A hA 0),
      gibbsCumulantThree_congr eH0 (fam2 c X A hA 0 2 (by decide)) (fam1 c X A hA 1),
      gibbsCumulantThree_congr eH0 (fam2 c X A hA 0 1 (by decide)) (fam1 c X A hA 2),
      gibbsCumulantFour_congr eH0 (fam1 c X A hA 2) (fam1 c X A hA 1) (fam1 c X A hA 0)]
end SlopeMeanExpansion
end YangMills.Construction
end
