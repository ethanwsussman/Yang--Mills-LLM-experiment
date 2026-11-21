import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import YangMills.Construction.ClusterExpansionOfAStep.FramesAlongEveryFamily
import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAMovedTop
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.FramesToOrderForty
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
set_option autoImplicit false

noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepCosts RenormalizationStepParameters MovedTopMarks
namespace MovedTopMarks
def FrameAlongMoveBounds : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ (K : ℕ → ℝ) (y₀ : ℝ), (∀ j, 0 ≤ K j) ∧ ∀ (x y : ℝ), y₀ ≤ x →
    ∀ (t n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (5 / 4 * T.threshold) V →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
        ∀ b ∈ chartBonds T.side n,
        ContDiffAt ℝ 40 (frameAlongMove (T.stepParameters y) T.ρA t (boxRadius x) V c X b) 0 ∧
        (∀ u, ‖frameAlongMove (T.stepParameters y) T.ρA t (boxRadius x) V c X b u‖ ≤ T.ρA) ∧
        (∀ i, 1 ≤ i → i ≤ 40 →
          ‖iteratedFDeriv ℝ i (frameAlongMove (T.stepParameters y) T.ρA t (boxRadius x) V c X b) 0‖ ≤
            (k : ℝ) ^ i * K i) ∧
        (4 * boxRadius x + 5 < n →
          (∀ l h, BondOffsetInBox (boxRadius x) h → c l ≠ bondFrom (parentBlock T.side b.1) h) →
          ∀ᶠ u in 𝓝 0, frameAlongMove (T.stepParameters y) T.ρA t (boxRadius x) V c X b u =
            frameAlongMove (T.stepParameters y) T.ρA t (boxRadius x) V c X b 0)
end MovedTopMarks
end YangMills.Construction
end

noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames BondMoves TorusFields RenormalizationStepParameters TorusLumps MovedTopMarks StepCosts
  FrameAnalyticity
namespace MovedTopMarks
namespace UnitFamilies
variable {n : ℕ}
def indexPushLinear {i k : ℕ} (p : Fin i → Fin k) : (Fin i → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ s, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin i => ℝ) s).smulRight (Pi.single (p s) 1)
theorem indexPushLinear_apply {i k : ℕ} (p : Fin i → Fin k) (σ : Fin i → ℝ) :
    indexPushLinear p σ = ∑ s, σ s • (Pi.single (p s) 1 : Fin k → ℝ) := by
  simp [indexPushLinear]
theorem indexPushLinear_single {i k : ℕ} (p : Fin i → Fin k) (s : Fin i) :
    indexPushLinear p (Pi.single s 1) = Pi.single (p s) 1 := by
  rw [indexPushLinear_apply, Finset.sum_eq_single s]
  · simp
  · intro s' _ hs
    simp [hs]
  · simp
theorem bondMoveLinear_single {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (β : TorusBond n) (l : Fin k) :
    bondMoveLinear c X β (Pi.single l 1) = if c l = β then X l else 0 := by
  rw [bondMoveLinear_apply, Finset.sum_eq_single l]
  · simp
  · intro l' _ hl
    simp [hl]
  · simp
theorem bondMoveLinear_comp {i k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (p : Fin i → Fin k) (σ : Fin i → ℝ) (β : TorusBond n) :
    bondMoveLinear (c ∘ p) (X ∘ p) β σ = bondMoveLinear c X β (indexPushLinear p σ) := by
  rw [indexPushLinear_apply, map_sum, bondMoveLinear_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, bondMoveLinear_single]
  simp only [Function.comp]
  split_ifs <;> simp
theorem perturb_comp {i k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (p : Fin i → Fin k)
    (σ : Fin i → ℝ) (A : TorusField n) :
    perturb (c ∘ p) (X ∘ p) σ A = perturb c X (indexPushLinear p σ) A := by
  funext x j
  rw [perturb_eq_expUnit_mul, perturb_eq_expUnit_mul, bondMoveLinear_comp]
theorem iteratedFDeriv_comp_continuousLinearMap {E' E F : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E' →L[ℝ] E) {f : E → F}
    {x : E'} {k : ℕ} (hf : ContDiffAt ℝ k f (L x)) :
    iteratedFDeriv ℝ k (f ∘ L) x = (iteratedFDeriv ℝ k f (L x)).compContinuousLinearMap fun _ => L := by
  obtain ⟨u, uo, xu, hu⟩ := (contDiffWithinAt_univ.mpr hf).contDiffOn' (m := k) le_rfl (by simp)
  have hu' : ContDiffOn ℝ k f u := by simpa using hu
  have hpre : IsOpen (L ⁻¹' u) := uo.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hu' uo.uniqueDiffOn hpre.uniqueDiffOn xu le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hpre xu, iteratedFDerivWithin_of_isOpen k uo xu] at h
  exact h
theorem mixedDeriv_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {i k : ℕ} (G : TorusField n → E)
    (A : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (p : Fin i → Fin k)
    (hG : ContDiffAt ℝ i (fun u : Fin k → ℝ => G (perturb c X u A)) 0) :
    mixedDeriv G A (c ∘ p) (X ∘ p) =
      iteratedFDeriv ℝ i (fun u : Fin k → ℝ => G (perturb c X u A)) 0 fun s => Pi.single (p s) 1 := by
  have e : (fun σ : Fin i → ℝ => G (perturb (c ∘ p) (X ∘ p) σ A)) =
      (fun u : Fin k → ℝ => G (perturb c X u A)) ∘ indexPushLinear p := by
    funext σ
    simp only [Function.comp, perturb_comp]
  unfold mixedDeriv
  rw [e, iteratedFDeriv_comp_continuousLinearMap (indexPushLinear p) (by simpa using hG), map_zero]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, indexPushLinear_single]
theorem opNorm_le_of_basis {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k i : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin k → ℝ) E) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ p : Fin i → Fin k, ‖T fun s => Pi.single (p s) 1‖ ≤ B) : ‖T‖ ≤ (k : ℝ) ^ i * B := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  have hv : v = fun s => ∑ l, v s l • (Pi.single l 1 : Fin k → ℝ) := by
    funext s j
    simp [Finset.sum_apply, Pi.single_apply]
  have e : T v = ∑ r : Fin i → Fin k, (∏ s, v s (r s)) • T fun s => Pi.single (r s) 1 := by
    conv_lhs => rw [hv]
    have := T.toMultilinearMap.map_sum (fun (s : Fin i) (l : Fin k) => v s l • (Pi.single l 1 : Fin k → ℝ))
    refine this.trans (Finset.sum_congr rfl fun r _ => ?_)
    exact T.toMultilinearMap.map_smul_univ _ _
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hone : ∀ r : Fin i → Fin k, ‖(∏ s, v s (r s)) • T fun s => Pi.single (r s) 1‖ ≤ B * ∏ s, ‖v s‖ := by
    intro r
    rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
    refine mul_le_mul (h r) ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hB
    refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun s _ => ?_
    exact norm_le_pi_norm (v s) (r s)
  refine (Finset.sum_le_sum fun r _ => hone r).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  exact le_of_eq (by ring)
theorem norm_minimizingBondCoordinate_le {F : BlockFrame} {a ρ : ℝ} (hρ : 0 ≤ ρ) (S : Finset F.Cell)
    (b : F.Site F.depth × Fin 4) (A : F.GaugeField F.top) :
    ‖((minimizingBondCoordinate a ρ S b A : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ρ := by
  classical
  unfold minimizingBondCoordinate minimizingCoordinates
  split_ifs with h
  · obtain ⟨h0, h1, -⟩ := h.choose_spec
    by_cases hb : b ∈ chordBonds S
    · exact h1 b hb
    · have := h0 b hb
      rw [this]
      simpa using hρ
  · simpa using hρ
theorem norm_frameAlongMove_le (ℓ : StepParameters) {ρA : ℝ} (hρ : 0 ≤ ρA) (t m : ℕ) (A : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * ℓ.side)) (u : Fin k → ℝ) :
    ‖frameAlongMove ℓ ρA t m A c X b u‖ ≤ ρA := by
  unfold frameAlongMove StepCosts.frameCoord bondFrameCoord reflectedBondCoord
  split_ifs
  · exact norm_minimizingBondCoordinate_le hρ _ _ _
  · exact norm_minimizingBondCoordinate_le hρ _ _ _
theorem norm_imaginaryBasis (i : Fin 3) : ‖imaginaryBasis i‖ = 1 := by
  have h : Quaternion.normSq ((imaginaryBasis i : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    fin_cases i <;> (rw [Quaternion.normSq_def']; simp [imaginaryBasis])
  have h2 : ‖((imaginaryBasis i : imaginaryQuaternions) : ℍ[ℝ])‖ *
      ‖((imaginaryBasis i : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, h]
  have h3 : ‖imaginaryBasis i‖ = ‖((imaginaryBasis i : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
  rw [h3]
  nlinarith [norm_nonneg ((imaginaryBasis i : imaginaryQuaternions) : ℍ[ℝ])]
theorem perturb_at_zero {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (A : TorusField n) :
    perturb c X 0 A = A := by apply _root_.YangMills.Construction.TorusFields.perturb_zero <;> assumption
end UnitFamilies
open UnitFamilies in
theorem frameAlongMoveBounds_holds (hO : ClusterExpansionOfAStep.FrameDerivativesBounded)
    (hA : FrameAnalyticAlongFamilies) (hM : PerturbLocallyReparametrized) (hC : ColdNearStatement) :
    FrameAlongMoveBounds := by
  intro T hT
  obtain ⟨K, yO, hKpos, hOf⟩ := hO T hT
  obtain ⟨yA, hAf⟩ := hA T hT
  obtain ⟨a, hMa⟩ := hM
  have hρ : 0 ≤ T.ρA := hT.chain.2.2.2.1.le
  refine ⟨fun j => 16 ^ j * K j, max yO yA, fun j => by have := hKpos j; positivity, ?_⟩
  intro x y hxy t n _ hn V hV k c X hu b hb
  have hxO : yO ≤ x := le_trans (le_max_left _ _) hxy
  have hxA : yA ≤ x := le_trans (le_max_right _ _) hxy
  let G : TorusField n → imaginaryQuaternions := fun V' =>
    StepCosts.frameCoord (T.stepParameters y) T.ρA t (boxRadius x) V' b
  have hana : ∀ V' : TorusField n, IsCold (5 / 4 * T.threshold) V' →
      ∀ (j : ℕ) (c' : Fin j → TorusBond n) (X' : Fin j → imaginaryQuaternions),
      ContDiffAt ℝ 40 (fun u : Fin j → ℝ => G (perturb c' X' u V')) 0 := fun V' hV' j c' X' =>
    (hAf x y hxA t n hn V' hV' b hb j c' X').contDiffAt
  have hsub : ∀ {j i : ℕ} (c' : Fin j → TorusBond n) (X' : Fin j → imaginaryQuaternions) (V' : TorusField n)
      (v : Fin i → Fin j → ℝ),
      ContDiffAt ℝ i (fun u : Fin j → ℝ => G (perturb c' X' u V')) 0 →
      iteratedFDeriv ℝ i (fun u : Fin j → ℝ => ((G (perturb c' X' u V') : imaginaryQuaternions) : ℍ[ℝ])) 0 v =
        ((iteratedFDeriv ℝ i (fun u : Fin j → ℝ => G (perturb c' X' u V')) 0 v : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro j i c' X' V' v hat
    have e := imaginaryQuaternions.subtypeL.iteratedFDeriv_comp_left hat le_rfl
    have e2 : (fun u : Fin j → ℝ => ((G (perturb c' X' u V') : imaginaryQuaternions) : ℍ[ℝ])) =
        imaginaryQuaternions.subtypeL ∘ fun u : Fin j → ℝ => G (perturb c' X' u V') := rfl
    rw [e2, e]
    rfl
  refine ⟨?_, fun u => norm_frameAlongMove_le _ hρ _ _ _ _ _ _ _, ?_, ?_⟩
  · exact imaginaryQuaternions.subtypeL.contDiff.contDiffAt.comp 0 (hana V hV k c X)
  · intro i hi1 hi2
    have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi2
    refine opNorm_le_of_basis _ (by have := hKpos i; positivity) fun p => ?_
    have hat : ContDiffAt ℝ i (fun u : Fin k → ℝ => G (perturb c X u V)) 0 := (hana V hV k c X).of_le hi'
    have e2 := hsub c X V (fun s => Pi.single (p s) 1) hat
    have e3 : iteratedFDeriv ℝ i (frameAlongMove (T.stepParameters y) T.ρA t (boxRadius x) V c X b) 0
        (fun s => Pi.single (p s) 1) =
        ((iteratedFDeriv ℝ i (fun u : Fin k → ℝ => G (perturb c X u V)) 0 (fun s => Pi.single (p s) 1) :
          imaginaryQuaternions) : ℍ[ℝ]) := e2
    rw [e3, ← mixedDeriv_comp G V c X p hat]
    exact (hOf x y hxO t n hn V hV b hb i (c ∘ p) (X ∘ p) hi1 hi2 (fun l => hu (p l))).2.1
  · intro hside hoff
    set f := frameAlongMove (T.stepParameters y) T.ρA t (boxRadius x) V c X b with hf
    have hfat : ContDiffAt ℝ 40 f 0 := imaginaryQuaternions.subtypeL.contDiff.contDiffAt.comp 0 (hana V hV k c X)
    have hcold := hC n V k c X 0 (5 / 4 * T.threshold) (by rw [perturb_at_zero]; exact hV)
    have hdiff : ∀ᶠ u in 𝓝 (0 : Fin k → ℝ), ContDiffAt ℝ 40 f u := hfat.eventually (by simp)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hcold.and hdiff)
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hε) fun u hu' => ?_
    have hzero : ∀ v ∈ Metric.ball (0 : Fin k → ℝ) ε, fderiv ℝ f v = 0 := by
      intro v hv
      obtain ⟨hcoldv, hcd⟩ := hball v hv
      obtain ⟨A, hAc, hA0, hAev, -⟩ := hMa n V k c X v
      set V₁ := perturb c X v V with hV₁
      let c3 := repeatBondsThrice c
      let X3 := basisAtEachBond k
      let Gu : (Fin (k * 3) → ℝ) → ℍ[ℝ] := fun w => ((G (perturb c3 X3 w V₁) : imaginaryQuaternions) : ℍ[ℝ])
      have hGu : ContDiffAt ℝ 40 Gu 0 :=
        imaginaryQuaternions.subtypeL.contDiff.contDiffAt.comp 0 (hana V₁ hcoldv _ c3 X3)
      have hD1 : fderiv ℝ Gu 0 = 0 := by
        have h1 : ‖iteratedFDeriv ℝ 1 Gu 0‖ ≤ ((k * 3 : ℕ) : ℝ) ^ 1 * 0 := by
          refine opNorm_le_of_basis _ le_rfl fun p => ?_
          have hat : ContDiffAt ℝ 1 (fun w : Fin (k * 3) → ℝ => G (perturb c3 X3 w V₁)) 0 :=
            (hana V₁ hcoldv _ c3 X3).of_le (by norm_num)
          have e2 := hsub c3 X3 V₁ (fun s => Pi.single (p s) 1) hat
          have e3 : iteratedFDeriv ℝ 1 Gu 0 (fun s => Pi.single (p s) 1) =
              ((iteratedFDeriv ℝ 1 (fun w : Fin (k * 3) → ℝ => G (perturb c3 X3 w V₁)) 0
                (fun s => Pi.single (p s) 1) : imaginaryQuaternions) : ℍ[ℝ]) := e2
          rw [e3, ← mixedDeriv_comp G V₁ c3 X3 p hat]
          have hz := (hOf x y hxO t n hn V₁ hcoldv b hb 1 (c3 ∘ p) (X3 ∘ p) le_rfl (by norm_num)
            (fun l => norm_imaginaryBasis _)).2.2 hside
            ⟨0, fun h hh => hoff _ h hh⟩
          have hz' : mixedDeriv G V₁ (c3 ∘ p) (X3 ∘ p) = 0 := hz
          rw [hz']
          simp
        have h2 : ‖fderiv ℝ Gu 0‖ = 0 := by
          rw [← norm_iteratedFDeriv_one]
          have h3 : 0 ≤ ‖iteratedFDeriv ℝ 1 Gu 0‖ := norm_nonneg _
          have h4 : ((k * 3 : ℕ) : ℝ) ^ 1 * 0 = 0 := by ring
          linarith
        refine ContinuousLinearMap.ext fun v => norm_le_zero_iff.mp ?_
        have h3 := (fderiv ℝ Gu 0).le_opNorm v
        rw [h2, zero_mul] at h3
        exact h3
      have hev : f =ᶠ[𝓝 v] Gu ∘ A := by
        refine hAev.mono fun τ hτ => ?_
        show ((G (perturb c X τ V) : imaginaryQuaternions) : ℍ[ℝ]) =
          ((G (perturb c3 X3 (A τ) V₁) : imaginaryQuaternions) : ℍ[ℝ])
        rw [hτ]
      have hGd : DifferentiableAt ℝ Gu (A v) := by
        rw [hA0]
        exact hGu.differentiableAt (by simp)
      rw [hev.fderiv_eq, fderiv_comp v hGd (hAc.differentiableAt (by simp)), hA0, hD1]
      simp
    have hmain := (convex_ball (0 : Fin k → ℝ) ε).norm_image_sub_le_of_norm_fderiv_le (f := f) (C := 0)
      (fun v hv => (hball v hv).2.differentiableAt (by simp))
      (fun v hv => by rw [hzero v hv]; simp) (Metric.mem_ball_self hε) hu'
    have h0 : ‖f u - f 0‖ ≤ 0 := by simpa using hmain
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
end MovedTopMarks
end YangMills.Construction
end
