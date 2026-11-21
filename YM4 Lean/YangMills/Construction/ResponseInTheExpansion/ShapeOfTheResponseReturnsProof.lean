import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ResponseInTheExpansion.ColdImageIsLinearProof
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStepIsIntegrableProof
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStepKeepsTheGauge
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStepKeepsTranslations
import YangMills.Construction.ResponseInTheExpansion.ShapeOfTheResponseReturns
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepSettings StepGas TorusLumps TorusFields RenormalizationStepParameters StepCosts ClusterExpansionOfAStep
private theorem holdsAtEveryStep_and {P Q : ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop}
    (hP : HoldsAtEveryStep P) (hQ : HoldsAtEveryStep Q) : HoldsAtEveryStep fun T R A => P T R A ∧ Q T R A := by apply _root_.YangMills.SharedProofs.p19358 <;> assumption
private theorem holdsAtEveryStep_of_floor {P : StepSetup → Prop}
    (h : ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → P R) :
    HoldsAtEveryStep fun _ R _ => P R := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ _ => ?_⟩
  obtain ⟨y₀, hy⟩ := h T hT
  exact ⟨y₀, fun y hy' R A _ hA => hy y hy' R hA.onFamily⟩
private theorem holdsAtEveryStep_mono {P Q : ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop}
    (hP : HoldsAtEveryStep P) (h : ∀ (T : ParameterAssignment) (y : ℝ) (R : StepSetup) (A : ResponseSetup R),
      OnStepParameters T y A → P T R A → Q T R A) : HoldsAtEveryStep Q := by apply _root_.YangMills.SharedProofs.p66024 <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem isBlockTorusSide_mul_side (hn : R.params.n₀ ≤ n) : IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
private theorem isLiveState_of_stepWeight_ne_zero (hrow : R.HasExpansions) (hn : R.params.n₀ ≤ n)
    {C : Finset (TorusSite n)} {V : TorusField n}
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    {bad : Finset (TorusBond (n * R.params.side))}
    {b : BaseChoice R.params.side n} (hh : IsHullState R.params R.range W Yt)
    (hw : stepWeight R C V W Yt ωt bad b ≠ 0) :
    IsLiveState R.params R.coupling R.labelWeight W Yt ωt := by apply _root_.YangMills.SharedProofs.p23747 <;> assumption
private theorem caseIntegral_eq_smul_add {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
    {F₁ F₂ F₃ : CaseFunction R n} (c : ℝ) (h₁ : CaseIntegrable R C V q F₁) (h₂ : CaseIntegrable R C V q F₂)
    (h : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsHullState R.params R.range W Yt →
      stepWeight R C V W Yt ωt bad b ≠ 0 → F₃ W Yt ωt bad b = c * F₁ W Yt ωt bad b + F₂ W Yt ωt bad b) :
    caseIntegral R C V q F₃ = c * caseIntegral R C V q F₁ + caseIntegral R C V q F₂ := by apply _root_.YangMills.SharedProofs.p59149 <;> assumption
private theorem caseIntegral_congr_of_weight {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
    {F₁ F₂ : CaseFunction R n}
    (h : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsHullState R.params R.range W Yt →
      stepWeight R C V W Yt ωt bad b ≠ 0 → F₁ W Yt ωt bad b = F₂ W Yt ωt bad b) :
    caseIntegral R C V q F₁ = caseIntegral R C V q F₂ := by apply _root_.YangMills.SharedProofs.p114415 <;> assumption
private theorem caseResponse_smul_add (hW : BlockMeanIsLinearAndLocal) (hodd : Odd R.params.side)
    {A : ResponseSetup R} (hA : A.IsAdmissible) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (y : TorusSite n) (c : ℝ)
    (h h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    caseResponse A V y (c • h + h') W Yt ωt bad b =
      c * caseResponse A V y h W Yt ωt bad b + caseResponse A V y h' W Yt ωt bad b := by apply _root_.YangMills.SharedProofs.p3179 <;> assumption
private theorem caseResponse_congr (hW : BlockMeanIsLinearAndLocal) (hodd : Odd R.params.side)
    {A : ResponseSetup R} (hA : A.IsAdmissible) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (y : TorusSite n)
    (h h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hh : ∀ p, IsPlaquetteAt R.params.side (R.depth + 1) y p → h p = h' p)
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    caseResponse A V y h W Yt ωt bad b = caseResponse A V y h' W Yt ωt bad b := by apply _root_.YangMills.SharedProofs.p104861 <;> assumption
private theorem coldCaseGround_admissible (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n) {V : TorusField n}
    (hc : IsCold R.params.threshold V) : (coldCaseGround R V).IsAdmissibleGround :=
  Or.inl ⟨hn, fun x μ ν h => (hc x μ ν h).trans (by linarith [hfit.σ_pos]), rfl, rfl, rfl⟩
private theorem hotCaseGround_admissible (hZ : CoarseWeightZeroOfFactorZero) (hR : R.IsWellPosed)
    (hgr : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n),
        IsHullState R.params R.nextRange V q.1 →
        (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsHotCase)
    (hn : IsBlockTorusSide R.params n) {V : TorusField n} {Y : Finset (TorusSite n)}
    {ω : Y → CoarseLabel R.labels.Ω R.params.side}
    (hl : IsLiveState R.params R.nextCoupling (coarseWeightExpansion R) V Y ω) :
    (hotCaseGround R V ⟨Y, ω⟩).IsAdmissibleGround := by
  refine Or.inr (hgr n hn V ⟨Y, ω⟩ hl.1 fun X hX h0 => ?_)
  have h1 := hZ R hR n hn V ⟨Y, ω⟩ hl.1 ⟨X, hX, h0⟩
  have h2 := hl.2
  unfold coarseWeightExpansion at h2
  rw [dif_neg (NeZero.ne n)] at h2
  exact h2.ne' h1
theorem responseShapeStatement_holds (hB : StepResponseMeasurable)
    (hI : caseResponse_integrable) (hG : StepResponseGaugeInvariant)
    (hT : StepResponseTranslationInvariant) (hW : BlockMeanIsLinearAndLocal)
    (hgr : HullStateIsHotCase) (hZ : CoarseWeightZeroOfFactorZero) :
    ResponseShapeStatement := by
  classical
  have hgr' : HoldsAtEveryStep fun _ R _ => R.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      ∀ (V : TorusField n) (q : CoarseState R n), IsHullState R.params R.nextRange V q.1 →
        (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsHotCase :=
    holdsAtEveryStep_of_floor (P := fun R => R.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      ∀ (V : TorusField n) (q : CoarseState R n), IsHullState R.params R.nextRange V q.1 →
        (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsHotCase)
      fun T hT' => by
      obtain ⟨y₀, hy⟩ := hgr T hT'
      exact ⟨y₀, fun y hy' R hOn hR n _ hn V q hq hX => hy y hy' R hOn hR n hn V q hq hX⟩
  refine holdsAtEveryStep_mono
    (holdsAtEveryStep_and (holdsAtEveryStep_and hB hI)
      (holdsAtEveryStep_and hG (holdsAtEveryStep_and hT hgr')))
    fun T y R A hA ⟨⟨b, i⟩, g, t, gr⟩ hR hL => ?_
  have hresp := hA.admissible
  have hfit := hR.admissible
  have hodd : Odd R.params.side := hfit.L_odd
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : ∀ {n : ℕ}, IsBlockTorusSide R.params n → R.params.n₀ ≤ n := fun hn =>
    le_trans (Nat.le_mul_of_pos_left _ hL0) hn.2
  have coldInt : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n),
      IsCold R.params.threshold W →
      ∀ h, CaseIntegrable R ∅ W (emptyCoarseState R) (caseResponse A W y h) := fun n _ hn y W hc h =>
    i hR n (coldCaseGround R W) (coldCaseGround_admissible hfit hn hc) y h
  have hullInt : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (y : TorusSite n) (W : TorusField n)
      (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side),
      IsLiveState R.params R.nextCoupling (coarseWeightExpansion R) W Y ω →
      ∀ h, CaseIntegrable R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y h) := fun n _ hn y W Y ω hl h =>
    i hR n (hotCaseGround R W ⟨Y, ω⟩) (hotCaseGround_admissible hZ hR (gr hR) hn hl) y h
  refine
    { cold_linear := fun n _ hn y W hc c h h' => ?_
      hull_linear := fun n _ hn y W Y ω hl c h h' => ?_
      cold_reads := fun n _ hn y W hc h h' hh => ?_
      hull_reads := fun n _ hn y W Y ω hl h h' hh => ?_
      cold_borel := (b hR hL).2.1
      hull_borel := (b hR hL).2.2
      cold_gauge := (g hR hL).1
      hull_gauge := (g hR hL).2
      cold_translation := (t hR hL).1
      hull_translation := (t hR hL).2
      empty := fun n _ hn y W ω hl h => ?_ }
  · show caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y (c • h + h')) =
      c * caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y h) +
        caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y h')
    unfold caseMean
    rw [caseIntegral_eq_smul_add c (coldInt n hn y W hc h) (coldInt n hn y W hc h')
      fun W' Yt ωt bad b' hh hw =>
      caseResponse_smul_add hW hodd hresp (isBlockTorusSide_mul_side hn) W y c h h' W' Yt ωt bad b'
        (isLiveState_of_stepWeight_ne_zero hR.hasExpansions hn hh hw)]
    ring
  · show caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y (c • h + h')) =
      c * caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y h) +
        caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y h')
    unfold caseMean
    rw [caseIntegral_eq_smul_add c (hullInt n hn y W Y ω hl h) (hullInt n hn y W Y ω hl h')
      fun W' Yt ωt bad b' hh hw =>
      caseResponse_smul_add hW hodd hresp (isBlockTorusSide_mul_side (hn₀ hn)) W y c h h' W' Yt ωt bad b'
        (isLiveState_of_stepWeight_ne_zero hR.hasExpansions (hn₀ hn) hh hw)]
    ring
  · show caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y h) =
      caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y h')
    unfold caseMean
    rw [caseIntegral_congr_of_weight fun W' Yt ωt bad b' hh' hw =>
      caseResponse_congr hW hodd hresp (isBlockTorusSide_mul_side hn) W y h h' hh W' Yt ωt bad b'
        (isLiveState_of_stepWeight_ne_zero hR.hasExpansions hn hh' hw)]
  · show caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y h) =
      caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y h')
    unfold caseMean
    rw [caseIntegral_congr_of_weight fun W' Yt ωt bad b' hh' hw =>
      caseResponse_congr hW hodd hresp (isBlockTorusSide_mul_side (hn₀ hn)) W y h h' hh W' Yt ωt bad b'
        (isLiveState_of_stepWeight_ne_zero hR.hasExpansions (hn₀ hn) hh' hw)]
  · have hC : hotCoreSites R W = ∅ := Finset.subset_empty.mp hl.1.1
    have hq : (⟨∅, ω⟩ : CoarseState R n) = emptyCoarseState R := by
      unfold emptyCoarseState
      congr 1
      funext z
      exact absurd z.2 (Finset.notMem_empty _)
    show caseMean R (hotCoreSites R W) W ⟨∅, ω⟩ (caseResponse A W y h) =
      caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y h)
    rw [hC, hq]
end YangMills.Construction.ResponseInTheExpansion
end
