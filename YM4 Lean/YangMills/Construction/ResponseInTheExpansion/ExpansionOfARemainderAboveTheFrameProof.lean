import YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyIsAnExpansionProof
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfARemainderAboveTheFrame
import YangMills.Construction.ResponseInTheExpansion.SharesAtTheFrameProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.Estimates
namespace YangMills.Construction.WeightedResponses
namespace RemainderExpansionAboveFrames
variable {F : BlockFrame}
open Classical in
def extendByZero (F : BlockFrame) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) : LocalFamily :=
  fun F' => if h : F' = F then h ▸ r else fun _ _ => 0
theorem extendByZero_self (r : F.Site F.depth → F.GaugeField F.depth → ℝ) : _root_.YangMills.Construction.WeightedResponses.RemainderExpansionAboveFrames.extendByZero F r F = r := by
  simp [_root_.YangMills.Construction.WeightedResponses.RemainderExpansionAboveFrames.extendByZero]
theorem extendByZero_of_ne {F' : BlockFrame} (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (h : F' ≠ F) :
    _root_.YangMills.Construction.WeightedResponses.RemainderExpansionAboveFrames.extendByZero F r F' = fun _ _ => 0 := by
  simp [_root_.YangMills.Construction.WeightedResponses.RemainderExpansionAboveFrames.extendByZero, h]
def orderBounds (e e₃ : ℝ) : ℕ → ℝ := fun j => if j = 3 then e₃ else e
theorem torusDecayFactor_nonneg (L : ℕ) (δ x : ℝ) : 0 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyRegular.torusDecayWeight_nonneg <;> assumption
theorem bondDeriv_const_zero {j k : ℕ} {F' : BlockFrame} (W : F'.GaugeField j) (c : Fin k → F'.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun _ : F'.GaugeField j => (0 : ℝ)) W c X = 0 := by
  unfold bondDeriv
  have : (fun τ : Fin k → ℝ => (fun _ : F'.GaugeField j => (0 : ℝ)) (leftTranslate (bondSpread c X τ) W)) =
      fun _ => (0 : ℝ) := rfl
  rw [this, iteratedFDeriv_fun_zero]
  rfl
theorem hasBoundedDerivatives_extendByZero {L t n₀ : ℕ} {σ δ e e₃ : ℝ}
    {r : F.Site F.depth → F.GaugeField F.depth → ℝ} (he : 0 ≤ e) (he₃ : 0 ≤ e₃)
    (hr : IsDecayingSiteFamily L σ δ e e₃ r) :
    HasBoundedDerivatives L t n₀ σ δ 3 (orderBounds e e₃) (_root_.YangMills.Construction.WeightedResponses.RemainderExpansionAboveFrames.extendByZero F r) := by
  refine ⟨fun F' _ y W hW j c X => ?_, fun F' _ y W γ hW => ?_, fun F' _ y W j c X hW h1 h3 hX => ?_⟩
  · by_cases h : F' = F
    · subst h
      rw [extendByZero_self]
      exact_mod_cast hr.smooth y W hW j c X
    · rw [extendByZero_of_ne r h]
      exact contDiffAt_const
  · by_cases h : F' = F
    · subst h
      rw [extendByZero_self]
      exact hr.gauge_invariant y W γ hW
    · rw [extendByZero_of_ne r h]
  · by_cases h : F' = F
    · subst h
      rw [extendByZero_self]
      have := hr.decay y W j c X hW h1 h3 hX
      simpa [orderBounds] using this
    · rw [extendByZero_of_ne r h]
      have e0 : (fun _ : F'.GaugeField F'.depth => (0 : ℝ)) =
          (fun _ : F'.Site F'.depth => fun _ : F'.GaugeField F'.depth => (0 : ℝ)) y := rfl
      rw [← e0, bondDeriv_const_zero, abs_zero]
      refine div_nonneg ?_ (torusDecayFactor_nonneg _ _ _)
      unfold orderBounds
      split_ifs <;> assumption
theorem runningMax_orderBounds_one (e e₃ : ℝ) (he : 0 ≤ e) : runningMax (orderBounds e e₃) 1 = e := by
  simp [runningMax, orderBounds, he]
theorem runningMax_orderBounds_two (e e₃ : ℝ) (he : 0 ≤ e) : runningMax (orderBounds e e₃) 2 = e := by
  simp [runningMax, orderBounds, he]
theorem runningMax_orderBounds_three (e e₃ : ℝ) (he : 0 ≤ e) (hee : e ≤ e₃) :
    runningMax (orderBounds e e₃) 3 = e₃ := by
  simp [runningMax, orderBounds, he, hee]
theorem iteratedFDeriv_add_const_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (hn : n ≠ 0)
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ n g x) (c : ℝ) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun z => g z + c) x v = iteratedFDeriv ℝ n g x v := by apply _root_.YangMills.SharedProofs.p68929 <;> assumption
end RemainderExpansionAboveFrames
open RemainderExpansionAboveFrames in
theorem remainderExpansionAboveFrames_proof (hT : transportBoundsStatement)
    (hJS : JointlyContDiffOnBallsOfDisplacements) (hJ : EventuallyInParametersCombines) :
    remainderExpansionAboveFramesStatement := by
  obtain ⟨-, weaken⟩ := hJ
  obtain ⟨C₀, Ck, hC₀, hCk, hP⟩ := hT
  refine ⟨fun U => C₀ (rateParameters U), fun U => hC₀ _, ?_⟩
  refine weaken _ _ ?_ hP
  intro T hDr hPT t x e f F V r hx hF hV he hr
  have hη := hDr.η₃_pos
  have hη1 := hDr.η₃_le_one
  have hle : e ≤ e / T.η₃ := by
    rw [le_div_iff₀ hη]
    nlinarith
  have hle0 : 0 ≤ e / T.η₃ := he.le.trans hle
  have hD := hasBoundedDerivatives_extendByZero (t := t) (n₀ := T.n₀) he.le hle0 hr
  have hnn : ∀ j, 0 ≤ orderBounds e (e / T.η₃) j := fun j => by
    unfold orderBounds
    split_ifs
    · exact hle0
    · exact he.le
  have htr : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsTransportBounded 1 T.a T.chainParams.ρA T.κ T.decayRate (C₀ (rateParameters T)) (Ck (rateParameters T)) T.L
        (frameRadius x) 3 (orderBounds e (e / T.η₃)) (_root_.YangMills.Construction.WeightedResponses.RemainderExpansionAboveFrames.extendByZero F r) V η := fun η hη' =>
    hPT x t 3 _ _ F V 1 η hx le_rfl (by norm_num) hnn hD hF hV zero_le_one le_rfl hη'
  set G₀ : F.Site F.depth → AboveFrames F := fun y =>
    interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) (_root_.YangMills.Construction.WeightedResponses.RemainderExpansionAboveFrames.extendByZero F r) y with hG₀
  have hGe : ∀ y, (coldHalfLawAt T x f).liftedExpansion r y = fun η V' => G₀ y η V' + r y (uniformField F F.depth) :=
    fun y => by
      funext η V'
      simp only [hG₀, interpolatedExpansion, ColdStepAtMirrorFrames.subtractTrivial, extendByZero_self]
      rw [sub_add_cancel]
      rfl
  have hJ0 : ∀ y, JointlyContDiffOnBalls T.ballRadius V (G₀ y) := fun y =>
    hJS F T.ballRadius V (G₀ y) fun η hη' l j b u c X hu hX => by
      have := (htr η hη').smooth y l j b u c X hu hX
      exact_mod_cast this
  have hmove : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)) {l j : ℕ}
      (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
      (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      (∀ i, ‖u i‖ = 1) → AreUnitVectors X → l + j ≠ 0 → l + j ≤ 3 →
      jointMixedDeriv ((coldHalfLawAt T x f).liftedExpansion r y) η V b u c X = jointMixedDeriv (G₀ y) η V b u c X := by
    intro y η l j b u c X hη' hu hX h0 h3
    have e1 : jointDisplacement ((coldHalfLawAt T x f).liftedExpansion r y) η V b u c X =
        fun τ => jointDisplacement (G₀ y) η V b u c X τ + r y (uniformField F F.depth) := by
      funext τ
      unfold jointDisplacement
      rw [hGe]
    unfold jointMixedDeriv
    rw [e1]
    refine iteratedFDeriv_add_const_apply h0 ?_ _ _
    have := (htr η hη').smooth y l j b u c X hu hX
    exact ContDiffAt.of_le this (by exact_mod_cast h3)
  refine ⟨fun y => ?_, fun y ζ b u k c X hζ hu hk hX => ?_, fun y ζ b b' u u' hζ hu hu' => ?_⟩
  · intro k c X η hη'
    rw [hGe]
    exact (hJ0 y k c X η hη').add contDiffAt_const
  · have hu1 : ∀ i, ‖(![u] : Fin 1 → EuclideanSpace ℝ (Fin 3)) i‖ = 1 := fun i => by
      fin_cases i
      simpa using hu
    rw [hmove y ζ ![b] ![u] c X hζ hu1 hX (by omega) (by omega)]
    have h := (htr ζ hζ).jointDeriv_le y 1 k ![b] ![u] c X (by omega) (by omega) hu1 hX
    refine h.trans ?_
    have hl : runningMax (orderBounds e (e / T.η₃)) (1 + k) ≤ (if k = 2 then e / T.η₃ else e) := by
      interval_cases k
      · rw [show 1 + 0 = 1 from rfl, runningMax_orderBounds_one _ _ he.le]
        simp
      · rw [show 1 + 1 = 2 from rfl, runningMax_orderBounds_two _ _ he.le]
        simp
      · rw [show 1 + 2 = 3 from rfl, runningMax_orderBounds_three _ _ he.le hle]
        simp
    have hC := (hC₀ (rateParameters T)).le
    have := Real.exp_pos (-(2 ^ 7 * T.κ *
      (cellSetDiameter (insert (enclosingCell y) (chordBondCells ![b] ∪ topBondCells c)) : ℝ)))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hC) this.le
  · have hu1 : ∀ i, ‖(![u, u'] : Fin 2 → EuclideanSpace ℝ (Fin 3)) i‖ = 1 := fun i => by
      fin_cases i
      · simpa using hu
      · simpa using hu'
    have hX0 : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
    rw [hmove y ζ ![b, b'] ![u, u'] _ _ hζ hu1 hX0 (by omega) (by omega)]
    have h := (htr ζ hζ).jointDeriv_le y 2 0 ![b, b'] ![u, u'] Fin.elim0 Fin.elim0 (by omega) (by omega) hu1 hX0
    rw [show 2 + 0 = 2 from rfl, runningMax_orderBounds_two _ _ he.le] at h
    exact h
end YangMills.Construction.WeightedResponses
end
