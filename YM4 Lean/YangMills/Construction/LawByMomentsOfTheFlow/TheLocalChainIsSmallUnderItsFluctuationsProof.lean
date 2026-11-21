import YangMills.Construction.LawByMomentsOfTheFlow.TheLocalChainIsSmallUnderItsFluctuations
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChainProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory Filter Topology
namespace YangMills.Construction.MomentLaw
open ResponseInTheExpansion WeightedResponses TorusFields TorusLumps RenormalizationStepParameters StepCosts MarkedIntegrals BoxMarks
namespace LocalChainSmall
section Sizes
variable {ℓ : TorusLumps.StepParameters}
private theorem finsetSupNonneg_nonneg {α : Type} (S : Finset α) (f : α → ℝ) : 0 ≤ finsetSupNonneg S f :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)
private theorem finsetSupNonneg_le {α : Type} {S : Finset α} {f : α → ℝ} {c : ℝ} (h0 : 0 ≤ c)
    (h : ∀ b ∈ S, f b ≤ c) : finsetSupNonneg S f ≤ c :=
  (Finset.fold_max_le _).2 ⟨h0, h⟩
private theorem mem_supBall {n : ℕ} [NeZero n] {o z : TorusSite n} {r : ℝ} :
    z ∈ supBall o r ↔ (supDist z o : ℝ) ≤ r := by
  simp [supBall]
private theorem supBall_mono {n : ℕ} [NeZero n] (o : TorusSite n) {r r' : ℝ} (h : r ≤ r') :
    supBall o r ⊆ supBall o r' :=
  fun _ hz => mem_supBall.2 ((mem_supBall.1 hz).trans h)
private theorem plaquettesIn_mono {n : ℕ} [NeZero n] {S S' : Finset (TorusSite n)} (h : S ⊆ S') :
    plaquettesIn S ⊆ plaquettesIn S' := by
  intro p hp
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, fun z hz => h (hp.2 z hz)⟩
private theorem maxCurvature_nonneg {n : ℕ} [NeZero n] (W : TorusField n) (o : TorusSite n) (r : ℝ) :
    0 ≤ maxCurvatureOnBall W o r :=
  finsetSupNonneg_nonneg _ _
private theorem maxDeviation_nonneg (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (o : TorusSite n) (r : ℝ) : 0 ≤ maxDeviationOnBall T t V W o r :=
  finsetSupNonneg_nonneg _ _
private def weightedDeviationSum (T : StageTower ℓ) (s : ℕ) (nn ρ₀ : ℝ) (w : ℕ → ℝ) :
    (D n : ℕ) → [NeZero n] → MarkedSample ℓ (s + D) n → TorusSite (fineSide ℓ.side D n) → ℝ
  | 0, _, _, _, _ => 0
  | D + 1, n, _, u, o =>
    weightedDeviationSum T s nn ρ₀ w D (n * ℓ.side) u.1 o +
      w D * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side (D + 1) n o)
        ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)
private theorem weightedDeviationSum_nonneg (T : StageTower ℓ) (s : ℕ) (nn ρ₀ : ℝ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) :
    ∀ (D n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      0 ≤ weightedDeviationSum T s nn ρ₀ w D n u o := by
  intro D
  induction D with
  | zero => intro n _ u o; exact le_rfl
  | succ D ih =>
    intro n _ u o
    exact add_nonneg (ih (n * ℓ.side) u.1 o) (mul_nonneg (hw D) (maxDeviation_nonneg _ _ _ _ _ _))
private structure CurvatureHalving (T : StageTower ℓ) (s : ℕ) (nn ρ₀ m e N₀ minSide : ℝ) (A : ℕ) : Prop where
  frame : ∀ D, D < A → ∀ (n : ℕ) [NeZero n], minSide ≤ n → ∀ (o : TorusSite n) (V : TorusField n),
    IsColdOnBall ℓ.threshold V o m →
    ∀ b ∈ chartBonds ℓ.side n, supBall (parentBlock ℓ.side b.1) ρ₀ ⊆ supBall o (ballRadius ℓ.side nn ρ₀ (D + 1)) →
      ‖(frameCoord ℓ (T.stage (s + D)).anchorRadius (s + D) (T.stage (s + D)).toStepSetup.frameReach V b : ℍ[ℝ])‖ ≤
        N₀ * maxCurvatureOnBall V o (ballRadius ℓ.side nn ρ₀ (D + 1)) + e
  falls : ∀ D, D < A → ∀ (n : ℕ) [NeZero n], minSide ≤ n → ∀ (o : TorusSite n) (V : TorusField n),
    IsColdOnBall ℓ.threshold V o m →
    ∀ (W : TorusField (n * ℓ.side)) (o' : TorusSite (n * ℓ.side)), parentBlock ℓ.side o' = o →
      (∀ b ∈ chartBondsInBlocks ℓ.side (supBall o m), ‖(stepDeviation T (s + D) V W b : ℍ[ℝ])‖ < ℓ.threshold / 64) →
      maxCurvatureOnBall W o' (ballRadius ℓ.side nn ρ₀ D + 1) ≤
        (1 / 2) * maxCurvatureOnBall V o (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
          4 * maxDeviationOnBall T (s + D) V W o ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2) + e
private theorem le_side_mul {minSide : ℝ} {n : ℕ} (h0 : 0 ≤ minSide) (h : minSide ≤ n) :
    minSide ≤ ((n * ℓ.side : ℕ) : ℝ) := by apply _root_.YangMills.SharedProofs.p36346 <;> assumption
variable {T : StageTower ℓ} {s : ℕ} {nn ρ₀ m e N₀ minSide : ℝ} {A : ℕ}
private theorem curvature_descent (H : CurvatureHalving T s nn ρ₀ m e N₀ minSide A) (hs : 0 ≤ minSide) :
    ∀ D, D ≤ A → ∀ (n : ℕ) [NeZero n], minSide ≤ n → ∀ (u : MarkedSample ℓ (s + D) n)
      (o : TorusSite (fineSide ℓ.side D n)),
      coldAlongSteps T s m D n u o →
      maxCurvatureOnBall (topField ℓ s _ (sampleBelow ℓ s D n u)) o (ballRadius ℓ.side nn ρ₀ 0 + 1) ≤
        (1 / 2) ^ D * maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o)
          (ballRadius ℓ.side nn ρ₀ D + 1) +
          weightedDeviationSum T s nn ρ₀ (fun i => (1 / 2) ^ i * 4) D n u o + (2 - 2 * (1 / 2) ^ D) * e := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ u o _
    show maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) ≤
      (1 / 2) ^ 0 * maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) + 0 +
        (2 - 2 * (1 / 2) ^ 0) * e
    simp
  | succ D ih =>
    intro hD n _ hn u o hg
    obtain ⟨hc, hη, hg'⟩ := hg
    have h1 := ih (by omega) (n * ℓ.side) (le_side_mul hs hn) u.1 o hg'
    have h2 := H.falls D (by omega) n hn (siteAbove ℓ.side (D + 1) n o) u.2.2.1 hc
      (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side D (n * ℓ.side) o) rfl hη
    have hp : (0 : ℝ) ≤ (1 / 2) ^ D := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hp
    refine h1.trans ?_
    show _ ≤ (1 / 2) ^ (D + 1) * maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o)
        (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
      (weightedDeviationSum T s nn ρ₀ (fun i => (1 / 2) ^ i * 4) D (n * ℓ.side) u.1 o +
        ((1 / 2) ^ D * 4) * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1)
          (siteAbove ℓ.side (D + 1) n o) ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)) +
      (2 - 2 * (1 / 2) ^ (D + 1)) * e
    rw [pow_succ]
    linarith
private theorem stageSum_descent (H : CurvatureHalving T s nn ρ₀ m e N₀ minSide A) (hs : 0 ≤ minSide) :
    ∀ D, D ≤ A → ∀ (n : ℕ) [NeZero n], minSide ≤ n → ∀ (u : MarkedSample ℓ (s + D) n)
      (o : TorusSite (fineSide ℓ.side D n)),
      coldAlongSteps T s m D n u o →
      widenedStageSum T s nn ρ₀ D n u o ≤
        2 * maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) (ballRadius ℓ.side nn ρ₀ D + 1) +
          9 * weightedDeviationSum T s nn ρ₀ (fun _ => 1) D n u o + 2 * D * e := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ u o _
    have h0 := maxCurvature_nonneg (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1)
    show (0 : ℝ) ≤ 2 * maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) + 9 * 0 +
      2 * ((0 : ℕ) : ℝ) * e
    have : (2 : ℝ) * ((0 : ℕ) : ℝ) * e = 0 := by simp
    linarith
  | succ D ih =>
    intro hD n _ hn u o hg
    obtain ⟨hc, hη, hg'⟩ := hg
    have h1 := ih (by omega) (n * ℓ.side) (le_side_mul hs hn) u.1 o hg'
    have h2 := H.falls D (by omega) n hn (siteAbove ℓ.side (D + 1) n o) u.2.2.1 hc
      (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side D (n * ℓ.side) o) rfl hη
    show maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
        maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side (D + 1) n o)
          ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2) + widenedStageSum T s nn ρ₀ D (n * ℓ.side) u.1 o ≤
      2 * maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
        9 * (weightedDeviationSum T s nn ρ₀ (fun _ => 1) D (n * ℓ.side) u.1 o +
          1 * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1)
            (siteAbove ℓ.side (D + 1) n o) ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)) +
        2 * ((D + 1 : ℕ) : ℝ) * e
    push_cast
    linarith
private theorem stageMax_descent (H : CurvatureHalving T s nn ρ₀ m e N₀ minSide A) (hs : 0 ≤ minSide) (he : 0 ≤ e) :
    ∀ D, D ≤ A → ∀ (n : ℕ) [NeZero n], minSide ≤ n → ∀ (u : MarkedSample ℓ (s + D) n)
      (o : TorusSite (fineSide ℓ.side D n)),
      coldAlongSteps T s m D n u o →
      widenedStageMax s nn ρ₀ D n u o ≤
        maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) (ballRadius ℓ.side nn ρ₀ D + 1) +
          4 * weightedDeviationSum T s nn ρ₀ (fun _ => 1) D n u o + D * e := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ u o _
    show maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) ≤
      maxCurvatureOnBall (topField ℓ s n u) o (ballRadius ℓ.side nn ρ₀ 0 + 1) + 4 * 0 + ((0 : ℕ) : ℝ) * e
    simp
  | succ D ih =>
    intro hD n _ hn u o hg
    obtain ⟨hc, hη, hg'⟩ := hg
    have h1 := ih (by omega) (n * ℓ.side) (le_side_mul hs hn) u.1 o hg'
    have h2 := H.falls D (by omega) n hn (siteAbove ℓ.side (D + 1) n o) u.2.2.1 hc
      (topField ℓ (s + D) (n * ℓ.side) u.1) (siteAbove ℓ.side D (n * ℓ.side) o) rfl hη
    have hS := weightedDeviationSum_nonneg T s nn ρ₀ (w := fun _ => 1) (fun _ => zero_le_one) D (n * ℓ.side) u.1 o
    have hm := maxDeviation_nonneg T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1)
      (siteAbove ℓ.side (D + 1) n o) ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)
    have hc0 := maxCurvature_nonneg u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1)
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hDe : 0 ≤ (D : ℝ) * e := mul_nonneg hD0 he
    show max (maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1))
        (widenedStageMax s nn ρ₀ D (n * ℓ.side) u.1 o) ≤
      maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (D + 1) n o) (ballRadius ℓ.side nn ρ₀ (D + 1) + 1) +
        4 * (weightedDeviationSum T s nn ρ₀ (fun _ => 1) D (n * ℓ.side) u.1 o +
          1 * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1)
            (siteAbove ℓ.side (D + 1) n o) ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2)) +
        ((D + 1 : ℕ) : ℝ) * e
    push_cast
    refine max_le (by nlinarith) ?_
    linarith
end Sizes
section Descent
variable {ℓ : TorusLumps.StepParameters}
private theorem measurable_coarse (ℓ : TorusLumps.StepParameters) (h n : ℕ) :
    Measurable fun u : MarkedSample ℓ (h + 1) n => u.1 := by apply _root_.YangMills.SharedProofs.p1941 <;> assumption
private theorem measurable_sampleBelow (ℓ : TorusLumps.StepParameters) (s : ℕ) :
    ∀ (D n : ℕ), Measurable (sampleBelow ℓ s D n) := by apply _root_.YangMills.SharedProofs.p11381 <;> assumption
private def topEvent (T : StageTower ℓ) (h : ℕ) (m : ℝ) {n : ℕ} [NeZero n] (o : TorusSite n) :
    Set (MarkedSample ℓ (h + 1) n) :=
  {u | Disjoint (stageState T (h + 1) n u).2.1 (supBall o m) ∧ StepAvoids T h m o u}
private def ChainEvent (T : StageTower ℓ) (s : ℕ) (m : ℝ) (D n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + D) n)
    (o : TorusSite (fineSide ℓ.side D n)) : Prop :=
  Disjoint (stageState T (s + D) n u).2.1 (supBall (siteAbove ℓ.side D n o) m) ∧ StepsAvoidOrigin T s m D n u o
private structure DescentHypotheses (T : StageTower ℓ) (β : ℝ) (k H : ℕ) (m minSide : ℝ) : Prop where
  side_nonneg : 0 ≤ minSide
  below : ∀ (s D n : ℕ) [NeZero n],
    Measure.map (sampleBelow ℓ s D n) (markedSampleLaw T β (s + D) n) = markedSampleLaw T β s (fineSide ℓ.side D n)
  down : ∀ h, k ≤ h → h < H → ∀ (n : ℕ) [NeZero n], minSide ≤ n → ℓ.side ∣ n → ∀ o : TorusSite n,
    ∀ᵐ u ∂(markedSampleLaw T β (h + 1) n), Disjoint (stageState T (h + 1) n u).2.1 (supBall o m) →
      IsColdOnBall ℓ.threshold u.2.2.1 o m ∧
      (StepAvoids T h m o u →
        (∀ o' : TorusSite (n * ℓ.side), parentBlock ℓ.side o' = o →
          Disjoint (stageState T h (n * ℓ.side) u.1).2.1 (supBall o' m)) ∧
        ∀ b ∈ chartBondsInBlocks ℓ.side (supBall o m),
          ‖(stepDeviation T h u.2.2.1 (topField ℓ h (n * ℓ.side) u.1) b : ℍ[ℝ])‖ < ℓ.threshold / 64)
variable {T : StageTower ℓ} {β : ℝ} {k H s : ℕ} {nn ρ₀ m minSide : ℝ}
private theorem DescentHypotheses.measurePreserving_coarse (S : DescentHypotheses T β k H m minSide) (h n : ℕ)
    [NeZero n] :
    MeasurePreserving (fun u : MarkedSample ℓ (h + 1) n => u.1) (markedSampleLaw T β (h + 1) n)
      (markedSampleLaw T β h (n * ℓ.side)) :=
  ⟨measurable_coarse ℓ h n, S.below h 1 n⟩
private theorem side_dvd_mul {n : ℕ} : ℓ.side ∣ n * ℓ.side := Dvd.intro_left n rfl
private theorem chainEvent_succ (S : DescentHypotheses T β k H m minSide) (hs : k ≤ s) {D : ℕ} (hD : s + D < H)
    {n : ℕ} [NeZero n] (hn : minSide ≤ n) (hLn : ℓ.side ∣ n) (o : TorusSite (fineSide ℓ.side (D + 1) n)) :
    ∀ᵐ u ∂(markedSampleLaw T β (s + (D + 1)) n), (ChainEvent T s m (D + 1) n u o ↔
      u ∈ topEvent T (s + D) m (siteAbove ℓ.side (D + 1) n o) ∧ ChainEvent T s m D (n * ℓ.side) u.1 o) := by
  have hdn := S.down (s + D) (by omega) hD n hn hLn (siteAbove ℓ.side (D + 1) n o)
  refine hdn.mono fun u hu => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hdis, hsm, hfc⟩ := h
    have h2 := (hu hdis).2 hfc
    exact ⟨⟨hdis, hfc⟩, h2.1 (siteAbove ℓ.side D (n * ℓ.side) o) rfl, hsm⟩
  · obtain ⟨⟨hd, hm⟩, _, hsm⟩ := h
    exact ⟨hd, hsm, hm⟩
private theorem ae_cold_of_chainEvent (S : DescentHypotheses T β k H m minSide) (hs : k ≤ s) :
    ∀ D, s + D ≤ H → ∀ (n : ℕ) [NeZero n], minSide ≤ n → ℓ.side ∣ n → ∀ o : TorusSite (fineSide ℓ.side D n),
      ∀ᵐ u ∂(markedSampleLaw T β (s + D) n), ChainEvent T s m D n u o →
        coldAlongSteps T s m D n u o ∧ Disjoint (stageState T s _ (sampleBelow ℓ s D n u)).2.1 (supBall o m) := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ _ o
    exact Filter.Eventually.of_forall fun u h => ⟨trivial, h.1⟩
  | succ D ih =>
    intro hD n _ hn hLn o
    have hih := ih (by omega) (n * ℓ.side) (le_side_mul S.side_nonneg hn) side_dvd_mul o
    have hlift : ∀ᵐ u ∂(markedSampleLaw T β (s + (D + 1)) n), ChainEvent T s m D (n * ℓ.side) u.1 o →
        coldAlongSteps T s m D (n * ℓ.side) u.1 o ∧
          Disjoint (stageState T s _ (sampleBelow ℓ s D (n * ℓ.side) u.1)).2.1 (supBall o m) :=
      (S.measurePreserving_coarse (s + D) n).quasiMeasurePreserving.ae hih
    have hdn := S.down (s + D) (by omega) (by omega) n hn hLn (siteAbove ℓ.side (D + 1) n o)
    filter_upwards [hlift, hdn, chainEvent_succ S hs (by omega) hn hLn o] with u h1 h2 h3 hEv
    obtain ⟨htop, hlow⟩ := h3.1 hEv
    have hg := h1 hlow
    have hd := h2 htop.1
    exact ⟨⟨hd.1, (hd.2 htop.2).2, hg.1⟩, hg.2⟩
private theorem maxCurvature_top_le {T : StageTower ℓ} {s D n : ℕ} [NeZero n] {m σ' r : ℝ}
    {u : MarkedSample ℓ (s + D) n} {o : TorusSite (fineSide ℓ.side D n)} (hD : 1 ≤ D) (hσ : 0 ≤ σ')
    (hσ' : ℓ.threshold ≤ σ') (hr : r ≤ m) (hg : coldAlongSteps T s m D n u o) :
    maxCurvatureOnBall (topField ℓ (s + D) n u) (siteAbove ℓ.side D n o) r ≤ σ' := by
  cases D with
  | zero => omega
  | succ D =>
    refine finsetSupNonneg_le hσ fun p hp => ?_
    exact (hg.1 p (plaquettesIn_mono (supBall_mono _ hr) hp)).le.trans hσ'
variable {t d d' N : ℕ}
private theorem ae_localEvent (S : DescentHypotheses T β k H m minSide) (ht : k ≤ t) (hH : t + d + d' ≤ H) [NeZero N]
    (hN : minSide ≤ N) (hLN : ℓ.side ∣ N) (hLd : ℓ.side ∣ fineSide ℓ.side d' N)
    (hbs : minSide ≤ fineSide ℓ.side d' N) (o : TorusSite (fineSide ℓ.side d (fineSide ℓ.side d' N))) :
    ∀ᵐ u ∂(markedSampleLaw T β (t + d + d') N),
      (IsLocalEventFrom T t d d' m N u o →
        ChainEvent T (t + d) m d' N u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) ∧
          ChainEvent T t m d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o) ∧
      (ChainEvent T (t + d) m d' N u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o) →
        coldAlongSteps T (t + d) m d' N u (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)) ∧
      (ChainEvent T t m d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o →
        coldAlongSteps T t m d (fineSide ℓ.side d' N) (sampleBelow ℓ (t + d) d' N u) o) := by
  have h1 := ae_cold_of_chainEvent S (s := t + d) (by omega) d' hH N hN hLN
    (siteAbove ℓ.side d (fineSide ℓ.side d' N) o)
  have hmp : MeasurePreserving (sampleBelow ℓ (t + d) d' N) (markedSampleLaw T β (t + d + d') N)
      (markedSampleLaw T β (t + d) (fineSide ℓ.side d' N)) := ⟨measurable_sampleBelow ℓ _ d' N, S.below _ d' N⟩
  have h2 := hmp.quasiMeasurePreserving.ae
    (ae_cold_of_chainEvent S (s := t) ht d (by omega) (fineSide ℓ.side d' N) hbs hLd o)
  filter_upwards [h1, h2] with u a1 a2
  refine ⟨fun h => ?_, fun h => (a1 h).1, fun h => (a2 h).1⟩
  obtain ⟨hd, hs1, hs2⟩ := h
  exact ⟨⟨hd, hs1⟩, (a1 ⟨hd, hs1⟩).2, hs2⟩
private theorem weightedDeviationSum_le {τ : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) :
    ∀ (D n : ℕ) [NeZero n] (u : MarkedSample ℓ (s + D) n) (o : TorusSite (fineSide ℓ.side D n)),
      deviationsBoundedAlong T s nn ρ₀ τ D n u o →
        weightedDeviationSum T s nn ρ₀ w D n u o ≤ (∑ i ∈ Finset.range D, w i) * τ := by
  intro D
  induction D with
  | zero =>
    intro n _ u o _
    simp [weightedDeviationSum]
  | succ D ih =>
    intro n _ u o h
    obtain ⟨h1, h2⟩ := h
    have h3 := ih (n * ℓ.side) u.1 o h2
    have h4 := mul_le_mul_of_nonneg_left h1 (hw D)
    rw [Finset.sum_range_succ, add_mul]
    show weightedDeviationSum T s nn ρ₀ w D (n * ℓ.side) u.1 o +
      w D * maxDeviationOnBall T (s + D) u.2.2.1 (topField ℓ (s + D) (n * ℓ.side) u.1)
        (siteAbove ℓ.side (D + 1) n o) ((ballRadius ℓ.side nn ρ₀ D + 1) / (ℓ.side : ℝ) + 2) ≤ _
    linarith
private theorem sum_geometric_half_le (D : ℕ) : ∑ i ∈ Finset.range D, ((1 : ℝ) / 2) ^ i * 4 ≤ 8 := by apply _root_.YangMills.SharedProofs.p85945 <;> assumption
end Descent
section Table
private theorem ballRadius_div_pow (L : ℕ) (hL : 0 < L) (nn ρ₀ : ℝ) (a D : ℕ) :
    ballRadius L (nn / (L : ℝ) ^ a) ρ₀ D = ballRadius L nn ρ₀ (a + D) := by apply _root_.YangMills.SharedProofs.p21218 <;> assumption
private theorem ballRadius_le (L : ℕ) (hL : 0 < L) {nn ρ₀ : ℝ} (hnn : 0 ≤ nn) (D : ℕ) :
    ballRadius L nn ρ₀ D ≤ 20 * nn + 4 * ρ₀ := by apply _root_.YangMills.SharedProofs.p10514 <;> assumption
private theorem holdsOnParameters_of_three {P₁ P₂ P₃ Q : ParameterAssignment → ℝ → Prop}
    (h₁ : HoldsOnParameterFamilies P₁) (h₂ : HoldsOnParameterFamilies P₂) (h₃ : HoldsOnParameterFamilies P₃)
    (hQ : ∀ Tb y, Tb.Admissible → Tb.floorMin ≤ y → P₁ Tb y → P₂ Tb y → P₃ Tb y → Q Tb y) :
    HoldsOnParameterFamilies Q := by apply _root_.YangMills.SharedProofs.p71980 (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) <;> assumption
variable {Tb : ParameterAssignment} {y : ℝ}
private theorem IsLocalChainAbove.lower {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N n : ℕ} {nn x₀ x₁ : ℝ}
    (h : IsLocalChainAbove Tb y T β k N nn x₀) (hx : x₁ ≤ x₀)
    (hn : 2 ^ 10 * localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1 ≤ (n : ℝ)) :
    IsLocalChainAbove Tb y T β k n nn x₁ :=
  ⟨hx.trans h.floor_le, h.coupling_ge, h.onFamily, h.cutoff, h.measurable, hn, h.one_le, h.le_rpow⟩
private theorem eventually_small_power (P : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x → P * x ^ ((1 : ℝ) / 1000) * x ^ (-(1 / 3 : ℝ)) ≤ x ^ (-(1 / 4 : ℝ)) := by
  have h1 : Tendsto (fun x : ℝ => P * x ^ (-(1 / 20 : ℝ))) atTop (𝓝 (P * 0)) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 20)).const_mul P
  rw [mul_zero] at h1
  filter_upwards [h1.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with x hx hx1
  have hx0 : 0 < x := by linarith
  have e : P * x ^ ((1 : ℝ) / 1000) * x ^ (-(1 / 3 : ℝ)) =
      (P * x ^ (-(1 / 20 : ℝ))) * x ^ ((1 : ℝ) / 20 + 1 / 1000 - 1 / 3) := by
    have : x ^ ((1 : ℝ) / 1000) * x ^ (-(1 / 3 : ℝ)) =
        x ^ (-(1 / 20 : ℝ)) * x ^ ((1 : ℝ) / 20 + 1 / 1000 - 1 / 3) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      norm_num
    rw [mul_assoc, this, mul_assoc]
  rw [e]
  have h2 : x ^ ((1 : ℝ) / 20 + 1 / 1000 - 1 / 3) ≤ x ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h3 : 0 ≤ x ^ ((1 : ℝ) / 20 + 1 / 1000 - 1 / 3) := Real.rpow_nonneg hx0.le _
  have h4 : (P * x ^ (-(1 / 20 : ℝ))) * x ^ ((1 : ℝ) / 20 + 1 / 1000 - 1 / 3) ≤
      1 * x ^ ((1 : ℝ) / 20 + 1 / 1000 - 1 / 3) :=
    mul_le_mul_of_nonneg_right (le_of_lt hx) h3
  linarith
set_option maxHeartbeats 1000000 in
private theorem smallUnderFluctuations_at (hFl : localChainFloorsStatement) (hDraw : lowerMarginalStatement)
    (hD : Tb.Admissible) (hy : Tb.floorMin ≤ y) (hC : curvatureHalvesAt Tb y) (hS : localChainSizeAt Tb y)
    (hO : descentKeepsBallClearAt Tb y) : localChainSmallUnderFluctuationsAt Tb y := by
  obtain ⟨C, N₀, c, xc, hc, hcurv⟩ := hC
  obtain ⟨C₁, c₁, hC₁, hc₁, hq⟩ := hS
  obtain ⟨Cq, xs, hsz⟩ := hq 1
  obtain ⟨xd, hdn⟩ := hO
  have hfit := hD.fits y hy
  have hLgt : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hD.L_gt
  have hσ : 0 < (Tb.stepParameters y).threshold := hD.σ_pos
  have hLbig : 2 ^ 40 ≤ (Tb.stepParameters y).side := hD.L_ge
  have hLpos : 0 < (Tb.stepParameters y).side := by omega
  have hL2 : (2 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    have : 2 ≤ (Tb.stepParameters y).side := by omega
    exact_mod_cast this
  have hNb1 : 1 ≤ max N₀ 1 := le_max_right _ _
  have hCe1 : 1 ≤ max C 1 := le_max_right _ _
  have hc' : 0 < min c c₁ := lt_min hc hc₁
  have hKnn : 0 ≤ (Tb.stepParameters y).threshold + 5 * max C 1 + 1 := by positivity
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.1 (hFl _ _ hKnn hc')
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 (eventually_small_power (14 * C₁))
  refine ⟨max (max X₀ X₁) (max xc (max xs xd)), fun T β k N _ nn o hloc hLN => ?_⟩
  have hfl := hloc.floor_le
  have hX₀x : X₀ ≤ flowCouplings (Tb.stepParameters y) β k :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hfl
  have hX₁x : X₁ ≤ flowCouplings (Tb.stepParameters y) β k :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hfl
  have hxcx : xc ≤ max (max X₀ X₁) (max xc (max xs xd)) := (le_max_left _ _).trans (le_max_right _ _)
  have hxsx : xs ≤ max (max X₀ X₁) (max xc (max xs xd)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hxdx : xd ≤ max (max X₀ X₁) (max xc (max xs xd)) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have F := hX _ hX₀x
  have F₁ := hX₁ _ hX₁x
  set x := flowCouplings (Tb.stepParameters y) β k with hxdef
  set ρ₀ := localLogScale (Tb.stepParameters y) β k with hρdef
  set m : ℝ := (localBlockSide (Tb.stepParameters y) β k : ℝ) with hmdef
  set Ls : ℝ := ((Tb.stepParameters y).side : ℝ) with hLsdef
  set Nb := max N₀ 1 with hNbdef
  set Ce := max C 1 with hCedef
  have hx1 : 1 ≤ x := F.one_le
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hρ1 : 1 ≤ ρ₀ := F.one_le_scale
  have hρ0 : 0 ≤ ρ₀ := by linarith
  have hM1 : 1 ≤ (localChainDepth (Tb.stepParameters y) β k) := F.one_le_depth
  have hrad0 : 20 * x ^ ((1 : ℝ) / 90) + 4 * ρ₀ + 4 ≤ m / 8 := F.radii_le
  have hnn1 : 1 ≤ nn := hloc.one_le
  have hnnx : nn ≤ x ^ ((1 : ℝ) / 90) := hloc.le_rpow
  have hp90 : 0 ≤ x ^ ((1 : ℝ) / 90) := Real.rpow_nonneg hx0 _
  have hm32 : 32 ≤ m := by linarith
  have hside : 2 ^ 10 * m ≤ (N : ℝ) := hloc.side_ge
  have S : DescentHypotheses T β k (k + 2 * (localChainDepth (Tb.stepParameters y) β k)) m (2 ^ 10 * m) := by
    refine ⟨by positivity,
      fun s D n _ => hDraw (Tb.stepParameters y) hfit hLgt T hloc.cutoff hloc.measurable β s D n, ?_⟩
    intro h hk hH n _ hn hLn o
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine (hdn T β k n nn j o (IsLocalChainAbove.lower hloc hxdx hn) hLn (by omega)).mono fun u hu hdis => ?_
    refine ⟨(hu hdis).1, fun hs => ⟨((hu hdis).2 hs).1, fun b hb => (((hu hdis).2 hs).2 b hb).2⟩⟩
  set E := Real.exp (-(c * ρ₀)) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set e := Ce * E with hedef
  have he0 : 0 ≤ e := by positivity
  have hF : ∀ a' A : ℕ, a' + A ≤ 2 * (localChainDepth (Tb.stepParameters y) β k) →
      CurvatureHalving T (k + a') (nn / Ls ^ a') ρ₀ m e Nb (2 ^ 10 * m) A := by
    intro a' A hA
    refine ⟨fun D hD n _ hn o' V hcold b hb hsub => ?_, fun D hD n _ hn o' V hcold W o'' ho hη => ?_⟩
    · have hch := (hcurv T β k n nn (a' + D) o' V (IsLocalChainAbove.lower hloc hxcx hn) (by omega) hcold).1 b hb
        (by rw [hLsdef, ballRadius_div_pow _ hLpos] at hsub; exact hsub)
      rw [hLsdef, ballRadius_div_pow _ hLpos, Nat.add_assoc k a' D]
      exact hch.trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (maxCurvature_nonneg _ _ _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
    · rw [Nat.add_assoc k a' D] at hη
      have hch := (hcurv T β k n nn (a' + D) o' V (IsLocalChainAbove.lower hloc hxcx hn) (by omega) hcold).2
        W o'' ho hη 1 zero_le_one le_rfl
      rw [hLsdef, ballRadius_div_pow _ hLpos, ballRadius_div_pow _ hLpos, Nat.add_assoc k a' D]
      exact hch.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
  have hbsN : (N : ℝ) ≤
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N : ℝ) := by
    rw [fineSide_eq]
    push_cast
    have h1 : (1 : ℝ) ≤ Ls ^ (localChainDepth (Tb.stepParameters y) β k) := one_le_pow₀ (by linarith)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    exact le_mul_of_one_le_right hN0 h1
  have hbs : 2 ^ 10 * m ≤
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N : ℝ) :=
    hside.trans hbsN
  have hLd : (Tb.stepParameters y).side ∣
      fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N := by
    rw [fineSide_eq]
    exact Dvd.dvd.mul_right hLN _
  have H₂ : CurvatureHalving T k nn ρ₀ m e Nb (2 ^ 10 * m) (localChainDepth (Tb.stepParameters y) β k) := by
    have := hF 0 (localChainDepth (Tb.stepParameters y) β k) (by omega)
    simpa using this
  have H₁ : CurvatureHalving T (k + (localChainDepth (Tb.stepParameters y) β k))
      (nn / Ls ^ (localChainDepth (Tb.stepParameters y) β k)) ρ₀ m e Nb (2 ^ 10 * m)
      (localChainDepth (Tb.stepParameters y) β k) :=
    hF (localChainDepth (Tb.stepParameters y) β k) (localChainDepth (Tb.stepParameters y) β k) (by omega)
  have hr : ballRadius (Tb.stepParameters y).side (nn / Ls ^ (localChainDepth (Tb.stepParameters y) β k)) ρ₀ 0 =
      ballRadius (Tb.stepParameters y).side nn ρ₀ (localChainDepth (Tb.stepParameters y) β k) := by
    rw [hLsdef, ballRadius_div_pow _ hLpos]
    rfl
  have hmtop : ballRadius (Tb.stepParameters y).side (nn / Ls ^ (localChainDepth (Tb.stepParameters y) β k)) ρ₀
      (localChainDepth (Tb.stepParameters y) β k) + 1 ≤ m := by
    rw [hLsdef, ballRadius_div_pow _ hLpos]
    have h1 := ballRadius_le (Tb.stepParameters y).side hLpos (nn := nn) (ρ₀ := ρ₀) (by linarith)
      ((localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k))
    linarith
  have hx1' : 1 < x := by
    have := F.rpow_le_self
    rcases eq_or_lt_of_le hx1 with h | h
    · exfalso
      have h1 : x ^ ((1 : ℝ) / 90) = 1 := by rw [← h]; simp
      have h2 := F.rpow_le_self
      rw [h1, ← h] at h2
      norm_num at h2
    · exact h
  have hs1 : x ^ (-(1 / 4 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx1' (by norm_num)
  have hOn : IsLocalChainAbove Tb y T β k N nn xs := { hloc with floor_le := hxsx.trans hloc.floor_le }
  obtain ⟨hsm, -⟩ := hsz T β k N nn k (localChainDepth (Tb.stepParameters y) β k)
    (localChainDepth (Tb.stepParameters y) β k) o hOn hLN le_rfl rfl rfl
  simp only [Nat.sub_self, pow_zero, div_one] at hsm
  filter_upwards [ae_localEvent S (t := k) (d := (localChainDepth (Tb.stepParameters y) β k))
    (d' := (localChainDepth (Tb.stepParameters y) β k)) (N := N) le_rfl (by omega) hside hLN hLd hbs o,
    hsm _ hs1] with u hu hsm' hlocal
  have hl : IsLocalEventFrom T k (localChainDepth (Tb.stepParameters y) β k)
      (localChainDepth (Tb.stepParameters y) β k) m N u o := hlocal
  obtain ⟨ev1, ev2⟩ := hu.1 hl
  have g1 := hu.2.1 ev1
  have g2 := hu.2.2 ev2
  refine ⟨g1, g2, fun he1 he2 => hsm' hl ?_⟩
  set τ := x ^ (-(1 / 3 : ℝ)) with hτ
  have hτ0 : 0 ≤ τ := Real.rpow_nonneg hx0 _
  set o₁ := siteAbove (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) o with ho₁
  set db := sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k))
    (localChainDepth (Tb.stepParameters y) β k) N u with hdb
  have hA := curvature_descent H₁ S.side_nonneg (localChainDepth (Tb.stepParameters y) β k) le_rfl N hside u o₁ g1
  rw [hr] at hA
  have hB := stageSum_descent H₂ S.side_nonneg (localChainDepth (Tb.stepParameters y) β k) le_rfl
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) hbs db o g2
  have hC' := stageMax_descent H₂ S.side_nonneg he0 (localChainDepth (Tb.stepParameters y) β k) le_rfl
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) hbs db o g2
  have htop := maxCurvature_top_le hM1 hσ.le le_rfl hmtop g1
  have s1 := weightedDeviationSum_le (fun i => by positivity : ∀ i : ℕ, 0 ≤ ((1 : ℝ) / 2) ^ i * 4)
    (localChainDepth (Tb.stepParameters y) β k) N u o₁ he1
  have s2 := weightedDeviationSum_le (fun _ => zero_le_one : ∀ i : ℕ, (0 : ℝ) ≤ 1)
    (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o he2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at s2
  have s1' := s1.trans (mul_le_mul_of_nonneg_right (sum_geometric_half_le (localChainDepth (Tb.stepParameters y) β k)) hτ0)
  set cc := maxCurvatureOnBall (topField (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k))
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db) o₁
    (ballRadius (Tb.stepParameters y).side nn ρ₀ (localChainDepth (Tb.stepParameters y) β k) + 1) with hcc
  have hcc0 : 0 ≤ cc := maxCurvature_nonneg _ _ _
  have hxm1 : 0 ≤ x ^ (-1 : ℝ) := Real.rpow_nonneg hx0 _
  have hxm2' : 0 ≤ x ^ (-2 : ℝ) := Real.rpow_nonneg hx0 _
  have hxm2 : x ^ (-2 : ℝ) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hhalf : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) ≤ x ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, one_div, inv_pow]
    exact inv_anti₀ hxpos F.le_two_pow_depth
  have hEE : ∀ c₂ : ℝ, min c c₁ ≤ c₂ → Real.exp (-(c₂ * ρ₀)) ≤ x ^ (-2 : ℝ) := fun c₂ hc₂ => by
    have hexpo : Real.exp (-(min c c₁ * ρ₀)) ≤ x ^ (-2 : ℝ) := F.exp_le
    refine le_trans ?_ hexpo
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hc₂ hρ0
    linarith only [this]
  have hEx : E ≤ x ^ (-2 : ℝ) := hEE c (min_le_left _ _)
  have hE₁ : Real.exp (-(c₁ * ρ₀)) ≤ x ^ (-2 : ℝ) := hEE c₁ (min_le_right _ _)
  have hτ1 : x ^ (-(1 / 2 : ℝ) + 1 / 1000) ≤ τ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hκ : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) * (Tb.stepParameters y).threshold + 2 * e ≤ τ := by
    have h1 := mul_le_mul_of_nonneg_right hhalf hσ.le
    have h2 : e ≤ Ce * x ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left (hEx.trans hxm2) (by positivity)
    have h3 := F.inv_le
    have h4 : ((Tb.stepParameters y).threshold + 2 * Ce) * x ^ (-1 : ℝ) ≤
        ((Tb.stepParameters y).threshold + 5 * Ce + 1) * x ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hxm1
    have h5 : x ^ (-1 : ℝ) * (Tb.stepParameters y).threshold + 2 * (Ce * x ^ (-1 : ℝ)) =
        ((Tb.stepParameters y).threshold + 2 * Ce) * x ^ (-1 : ℝ) := by
      ring
    linarith only [h1, h2, h3, h4, h5, hτ1]
  have hM0 : (0 : ℝ) ≤ (localChainDepth (Tb.stepParameters y) β k) := Nat.cast_nonneg _
  have hc3 : 3 * (((localChainDepth (Tb.stepParameters y) β k) : ℝ) * e) +
      (localChainDepth (Tb.stepParameters y) β k) * Real.exp (-(c₁ * ρ₀)) ≤ τ := by
    have hCe0 : (0 : ℝ) ≤ Ce := (zero_le_one.trans hCe1)
    have h1 : ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * e ≤
        (localChainDepth (Tb.stepParameters y) β k) * (Ce * x ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEx hCe0) hM0
    have h2 : ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * Real.exp (-(c₁ * ρ₀)) ≤
        (localChainDepth (Tb.stepParameters y) β k) * x ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hE₁ hM0
    have h3 : (3 * Ce + 1) * (localChainDepth (Tb.stepParameters y) β k) * x ^ (-2 : ℝ) ≤
        ((Tb.stepParameters y).threshold + 5 * Ce + 1) * (localChainDepth (Tb.stepParameters y) β k) * x ^ (-2 : ℝ) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hM0) hxm2'
      linarith only [hσ, hCe0]
    have h4 : ((Tb.stepParameters y).threshold + 5 * Ce + 1) * ((localChainDepth (Tb.stepParameters y) β k) : ℝ) *
        x ^ (-2 : ℝ) ≤ x ^ (-(1 / 2 : ℝ) + 1 / 1000) := F.depth_inv_sq_le
    have h5 : (3 * Ce + 1) * ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * x ^ (-2 : ℝ) =
        3 * ((localChainDepth (Tb.stepParameters y) β k) * (Ce * x ^ (-2 : ℝ))) +
          (localChainDepth (Tb.stepParameters y) β k) * x ^ (-2 : ℝ) := by ring
    linarith only [h1, h2, h3, h4, h5, hτ1]
  have hcc9 : cc ≤ 9 * τ := by
    have h0 : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) ≥ 0 := by positivity
    have h1 := mul_le_mul_of_nonneg_left htop h0
    have h3 : (2 - 2 * ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k)) * e ≤ 2 * e := by
      have h5 := mul_nonneg h0 he0
      linarith only [h5]
    have h4 : cc ≤ ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) * (Tb.stepParameters y).threshold +
        8 * τ + 2 * e := by
      refine hA.trans ?_
      linarith only [h1, s1', h3]
    linarith only [h4, hκ]
  have hlogs : ρ₀ + (localChainDepth (Tb.stepParameters y) β k) + 4 ≤ x ^ ((1 : ℝ) / 1000) := F.logs_le
  have hsum : ρ₀ * cc + widenedStageSum T k nn ρ₀ (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o +
      widenedStageMax k nn ρ₀ (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o +
      (localChainDepth (Tb.stepParameters y) β k) * Real.exp (-(c₁ * ρ₀)) ≤
      14 * x ^ ((1 : ℝ) / 1000) * τ := by
    have h1 := mul_le_mul_of_nonneg_left hcc9 hρ0
    have h2 : 14 * (ρ₀ + (localChainDepth (Tb.stepParameters y) β k) + 4) * τ ≤ 14 * x ^ ((1 : ℝ) / 1000) * τ :=
      mul_le_mul_of_nonneg_right (by linarith) hτ0
    have h3 : ((localChainDepth (Tb.stepParameters y) β k) : ℝ) * τ ≥ 0 := mul_nonneg hM0 hτ0
    have h4 : ρ₀ * τ ≥ 0 := mul_nonneg hρ0 hτ0
    linarith only [hB, hC', s2, h1, hcc9, hc3, h2, h3, h4, hτ0]
  have hfin : C₁ * (ρ₀ * cc + widenedStageSum T k nn ρ₀ (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o +
      widenedStageMax k nn ρ₀ (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o +
      (localChainDepth (Tb.stepParameters y) β k) * Real.exp (-(c₁ * ρ₀))) ≤ x ^ (-(1 / 4 : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hsum hC₁.le
    have h2 := F₁ hx1
    have h3 : C₁ * (14 * x ^ ((1 : ℝ) / 1000) * τ) = 14 * C₁ * x ^ ((1 : ℝ) / 1000) * τ := by ring
    linarith only [h1, h2, h3]
  exact (min_le_right _ _).trans hfin
end Table
end LocalChainSmall
open LocalChainSmall
theorem localChainSmallUnderFluctuations_holds (hCurv : curvatureHalvesStatement)
    (hSize : localChainSizeStatement) (hDown : descentKeepsBallClearStatement)
    (hFl : localChainFloorsStatement) (hDraw : lowerMarginalStatement) :
    localChainSmallUnderFluctuationsStatement := by
  refine holdsOnParameters_of_three hCurv hSize hDown ?_
  intro Tb y hD hy hC hS hO
  exact smallUnderFluctuations_at hFl hDraw hD hy hC hS hO
end YangMills.Construction.MomentLaw
end
