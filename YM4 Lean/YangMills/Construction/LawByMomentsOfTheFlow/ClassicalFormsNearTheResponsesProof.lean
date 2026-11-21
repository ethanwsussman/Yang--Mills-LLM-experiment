import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import YangMills.Construction.LawByMomentsOfTheFlow.ClassicalFormsKillClosedForms
import YangMills.Construction.LawByMomentsOfTheFlow.ClassicalFormsNearTheResponses
import YangMills.Construction.LawByMomentsOfTheFlow.FormIsCarried
import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheResponsesAtOne
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.NumberOfTheFlowNearOne
import YangMills.Construction.LawByMomentsOfTheFlow.StepOfTheRestAtOne
import YangMills.Construction.LawByMomentsOfTheFlow.TheFlowAboveTheWindow
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.FieldsOfOneColour
import YangMills.Construction.ResponseInTheExpansion.SharesAtEveryLevel
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponseProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepCosts ShareFamilies WeightedResponses ResponseInTheExpansion BlockAverages LevelTestFunctions
namespace ClassicalApprox
private theorem forAllParameters_and {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q) (h' : ForAllParameters Q') :
    ForAllParameters fun Λ => Q Λ ∧ Q' Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_holdsOnAllParameters {P : ParameterAssignment → ℝ → Prop} (h : HoldsOnParameterFamilies P) :
    ForAllParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p27928 <;> assumption
private theorem rpow_neg_half_le_of_abs_sub_le {x x' B : ℝ} (hB : 0 ≤ B) (hx : 400 * B ≤ x) (hx0 : 0 < x) (hx'0 : 0 < x')
    (h : |x' - x| ≤ 2 * B) :
    x ^ (-(1 / 2) : ℝ) ≤ 1.01 * x' ^ (-(1 / 2) : ℝ) := by
  have h1 : x' ≤ (1.01 : ℝ) ^ 2 * x := by
    have := (abs_le.mp h).2
    nlinarith
  have h2 : x' ^ (1 / 2 : ℝ) ≤ 1.01 * x ^ (1 / 2 : ℝ) := by
    have e : ((1.01 : ℝ) ^ 2 * x) ^ (1 / 2 : ℝ) = 1.01 * x ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (by positivity) hx0.le, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by norm_num)]
    rw [← e]
    exact Real.rpow_le_rpow hx'0.le h1 (by norm_num)
  have p1 : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have p2 : 0 < x' ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx'0 _
  rw [Real.rpow_neg hx0.le, Real.rpow_neg hx'0.le, inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ p1 p2]
  linarith
private theorem weightLipschitz_nonneg (L t : ℕ) {N : ℕ} (h : PlaquetteWeight N) : 0 ≤ weightLipschitz L t h := by apply _root_.YangMills.Construction.ResponseInTheExpansion.weightLipschitz_nonneg <;> assumption
variable {n : ℕ} [NeZero n]
private theorem sum_imaginaryComponent_sq :
    ∑ e : Fin 3, imaginaryComponent e unitGenerator * imaginaryComponent e unitGenerator = 1 := by
  simp [Fin.sum_univ_three, imaginaryComponent, SingleColourFields.unitGenerator_imI,
    SingleColourFields.unitGenerator_imJ, SingleColourFields.unitGenerator_imK]
private theorem areUnitVectors_unitGenerator : AreUnitVectors ![unitGenerator, unitGenerator] := by
  intro l
  fin_cases l <;> exact SingleColourFields.norm_unitGenerator
private theorem annihilatesGradients_hessianAtIdentity {ψ : TorusField n → ℝ} (h : HasQuadraticFormAtIdentity ψ) :
    AnnihilatesGradients (hessianAtIdentity ψ) := by
  obtain ⟨_, q, _, hq, he⟩ := h
  have e : hessianAtIdentity ψ = q := by
    funext b b'
    show mixedDeriv ψ (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] = q b b'
    rw [he, sum_imaginaryComponent_sq, one_mul]
  rw [e]
  exact hq
abbrev _root_.YangMills.SharedProofs.p35629 := @annihilatesGradients_hessianAtIdentity
private theorem annihilatesGradients_sub {q q' : BondBilinear n} (h : AnnihilatesGradients q)
    (h' : AnnihilatesGradients q') :
    AnnihilatesGradients fun b b' => q b b' - q' b b' := by
  intro φ A
  have e₁ : ∀ B B' : TorusBond n → ℝ,
      bilinearEval (fun b b' => q b b' - q' b b') B B' = bilinearEval q B B' - bilinearEval q' B B' := by
    intro B B'
    unfold bilinearEval
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [e₁, e₁, (h φ A).1, (h' φ A).1, (h φ A).2, (h' φ A).2]
  simp
abbrev _root_.YangMills.SharedProofs.p90134 := @annihilatesGradients_sub
private theorem pullbackForm_sub (a ρA : ℝ) (L u : ℕ) [NeZero L] (q q' : BondBilinear (n * L)) (c c' : TorusBond n) :
    pullbackForm a ρA L u (fun b b' => q b b' - q' b b') c c' =
      pullbackForm a ρA L u q c c' - pullbackForm a ρA L u q' c c' := by
  unfold pullbackForm
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
end ClassicalApprox
namespace ClassicalApprox
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stageOnFlow_at {t : ℕ} (ht : t ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β t ⟨S.tower.stage t, S.resp t⟩ := by apply _root_.YangMills.SharedProofs.p6811 <;> assumption
private def RemainderStepBound (Cb : ℝ) : Prop :=
  ∀ t, t + 1 ≤ S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage (t + 1)).depth n)) (c c' : TorusBond n),
    |remainderHessian (S.resp (t + 1)) n Y h c c' - ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
        pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side (S.tower.stage t).depth
          (n := n) (fun b b' =>
          (blockMean Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side) y h -
              blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h) *
              shareHessian Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth y b b' +
            remainderHessian (S.resp t) (n * Λ.stepParams.side) y h b b') c c'| ≤
      Cb * S.coupling t ^ (-(1 / 2) : ℝ) * weightLipschitz Λ.stepParams.side (S.tower.stage (t + 1)).depth h /
        Λ.stepParams.weight (tripleDiam Y c c')
private def PullbackBound : Prop :=
  ∀ (u n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (Y : TorusSite n) (sz : ℝ), 0 ≤ sz →
    ∀ qs : TorusSite (n * Λ.stepParams.side) → BondBilinear (n * Λ.stepParams.side),
    (∀ y ∈ sitesInBlocks Λ.stepParams.side {Y},
      AnnihilatesGradients (qs y) ∧ IsDecayingAbout Λ.stepParams sz y (qs y)) →
    ∀ c c' : TorusBond n,
      |∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
          pullbackForm Λ.table.coupling Λ.table.ρA Λ.stepParams.side u (qs y) c c'| ≤
      (Λ.stepParams.side : ℝ) ^ ((1 : ℝ) / 2) * sz / Λ.stepParams.weight (tripleDiam Y c c')
private theorem step_arith {Cb u v p l G : ℝ} (hu : u ≤ 1.01 * v) (hu0 : 0 ≤ u) (hl : 0 ≤ l) (hG : 0 < G)
    (hp : 3 ≤ p) :
    Cb * u * (p * p * l) / G + p * (2 * |Cb| * u * l) / G ≤ 2 * |Cb| * v * (p * p * l) / G := by
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hG.le
  have h1 : Cb * (u * (p * p * l)) ≤ |Cb| * (u * (p * p * l)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have h2 : u * (p + 2) ≤ 2 * v * p := by nlinarith
  have h3 : |Cb| * (p * l) * (u * (p + 2)) ≤ |Cb| * (p * l) * (2 * v * p) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith
private theorem weightLipschitz_succ {L t m : ℕ} (hL : 0 < L) (h : PlaquetteWeight m) :
    weightLipschitz L (t + 1) h = (L : ℝ) * weightLipschitz L t h := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  unfold weightLipschitz
  rw [Real.mul_iSup_of_nonneg hL'.le]
  refine congrArg _ (funext fun pp => ?_)
  have e : barycentreDist L (t + 1) pp.1.1 pp.2.1 = barycentreDist L t pp.1.1 pp.2.1 / L := by
    unfold barycentreDist
    rw [pow_succ]
    field_simp
  rw [e, div_div_eq_mul_div]
  ring
abbrev _root_.YangMills.SharedProofs.p7308 := @weightLipschitz_succ
private theorem remainderHessian_near_classical {Cb : ℝ} (hb : RemainderStepBound S Cb) (hc : PullbackBound (Λ := Λ))
    (hk : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      AnnihilatesGradients (remainderHessian (S.resp t) n y h) ∧
        AnnihilatesGradients (classicalRemainder S.tower S.resp t n h y))
    (hx : ∀ t, t + 1 ≤ S.data.windowLevel →
      S.coupling t ^ (-(1 / 2) : ℝ) ≤ 1.01 * S.coupling (t + 1) ^ (-(1 / 2) : ℝ))
    (hx0 : ∀ t ≤ S.data.windowLevel, 0 < S.coupling t) (hL : 9 ≤ Λ.stepParams.side)
    (hρ : ∀ t ≤ S.data.windowLevel, (S.tower.stage t).anchorRadius = Λ.table.ρA) :
    ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)) (b b' : TorusBond n),
      |remainderHessian (S.resp t) n y h b b' - classicalRemainder S.tower S.resp t n h y b b'| ≤
        2 * |Cb| * S.coupling t ^ (-(1 / 2) : ℝ) * weightLipschitz Λ.stepParams.side (S.tower.stage t).depth h /
          Λ.stepParams.weight (tripleDiam y b b') := by
  intro t
  induction t with
  | zero =>
    intro h0 n _ hn y h b b'
    have e : classicalRemainder S.tower S.resp 0 n h y b b' = remainderHessian (S.resp 0) n y h b b' := rfl
    rw [e, sub_self, abs_zero]
    have : 0 ≤ S.coupling 0 ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos (hx0 0 h0) _).le
    have := _root_.YangMills.Construction.MomentLaw.ClassicalApprox.weightLipschitz_nonneg Λ.stepParams.side (S.tower.stage 0).depth h
    have := TermCalculus.weight_pos Λ.stepParams (tripleDiam y b b')
    positivity
  | succ t ih =>
    intro ht n _ hn Y h c c'
    have ht' : t ≤ S.data.windowLevel := by omega
    have hLpos : 0 < Λ.stepParams.side := by omega
    have hnL : Λ.stepParams.n₀ ≤ n * Λ.stepParams.side := hn.trans (Nat.le_mul_of_pos_right _ hLpos)
    have hu0 : 0 ≤ S.coupling t ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos (hx0 t ht') _).le
    have hl : 0 ≤ weightLipschitz Λ.stepParams.side (S.tower.stage t).depth
        (show PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side)) from h) :=
      _root_.YangMills.Construction.MomentLaw.ClassicalApprox.weightLipschitz_nonneg _ _ _
    have hsz : 0 ≤ 2 * |Cb| * S.coupling t ^ (-(1 / 2) : ℝ) *
        weightLipschitz Λ.stepParams.side (S.tower.stage t).depth
          (show PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side)) from h) := by
      positivity
    have carried := hc (S.tower.stage t).depth n hn Y _ hsz
      (fun y b b' => remainderHessian (S.resp t) (n * Λ.stepParams.side) y h b b' -
        classicalRemainder S.tower S.resp t (n * Λ.stepParams.side) h y b b')
      (fun y _ => ⟨annihilatesGradients_sub (hk t ht' (n * Λ.stepParams.side) hnL y h).1
          (hk t ht' (n * Λ.stepParams.side) hnL y h).2,
        fun b b' => ih ht' (n * Λ.stepParams.side) hnL y h b b'⟩) c c'
    have step := hb t ht n hn Y h c c'
    have e₁ : classicalRemainder S.tower S.resp (t + 1) n h Y c c' = ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
        pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side (S.tower.stage t).depth
          (n := n) (fun b b' =>
          (blockMean Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side) y h -
              blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h) *
              shareHessian Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth y b b' +
            classicalRemainder S.tower S.resp t (n * Λ.stepParams.side) h y b b') c c' := rfl
    have e₂ : ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
          pullbackForm Λ.table.coupling Λ.table.ρA Λ.stepParams.side (S.tower.stage t).depth (n := n)
          (fun b b' => remainderHessian (S.resp t) (n * Λ.stepParams.side) y h b b' -
            classicalRemainder S.tower S.resp t (n * Λ.stepParams.side) h y b b') c c' =
        (∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
          pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side
            (S.tower.stage t).depth (n := n) (fun b b' =>
            (blockMean Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side) y h -
                blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h) *
                shareHessian Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth y b b' +
              remainderHessian (S.resp t) (n * Λ.stepParams.side) y h b b') c c') -
          classicalRemainder S.tower S.resp (t + 1) n h Y c c' := by
      rw [e₁, ← Finset.sum_sub_distrib, hρ t ht']
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← pullbackForm_sub]
      refine congrArg (fun q : BondBilinear (n * Λ.stepParams.side) =>
        pullbackForm Λ.table.coupling Λ.table.ρA Λ.stepParams.side (S.tower.stage t).depth (n := n) q c c') ?_
      funext b b'
      ring
    rw [e₂] at carried
    set A₀ := ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
        pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side (S.tower.stage t).depth
          (n := n) (fun b b' =>
          (blockMean Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side) y h -
              blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h) *
              shareHessian Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth y b b' +
            remainderHessian (S.resp t) (n * Λ.stepParams.side) y h b b') c c' with hA₀
    have hp : (3 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ ((1 : ℝ) / 2) := by
      have h9 : (9 : ℝ) ≤ Λ.stepParams.side := by exact_mod_cast hL
      have e : ((9 : ℝ)) ^ ((1 : ℝ) / 2) = 3 := by
        rw [← Real.sqrt_eq_rpow, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← e]
      exact Real.rpow_le_rpow (by norm_num) h9 (by norm_num)
    have hpp : (Λ.stepParams.side : ℝ) ^ ((1 : ℝ) / 2) * (Λ.stepParams.side : ℝ) ^ ((1 : ℝ) / 2) =
        Λ.stepParams.side := by
      rw [← Real.rpow_add (by exact_mod_cast hLpos)]
      norm_num
    have hlip : weightLipschitz Λ.stepParams.side (S.tower.stage (t + 1)).depth h =
        (Λ.stepParams.side : ℝ) ^ ((1 : ℝ) / 2) * (Λ.stepParams.side : ℝ) ^ ((1 : ℝ) / 2) *
        weightLipschitz Λ.stepParams.side (S.tower.stage t).depth
          (show PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side)) from h) := by
      rw [hpp]
      exact weightLipschitz_succ hLpos _
    have ar := step_arith (Cb := Cb) (hx t ht) hu0 hl (TermCalculus.weight_pos Λ.stepParams (tripleDiam Y c c')) hp
    rw [hlip] at step ⊢
    have tri : |remainderHessian (S.resp (t + 1)) n Y h c c' - classicalRemainder S.tower S.resp (t + 1) n h Y c c'| ≤
        |remainderHessian (S.resp (t + 1)) n Y h c c' - A₀| +
          |A₀ - classicalRemainder S.tower S.resp (t + 1) n h Y c c'| :=
      abs_sub_le _ _ _
    linarith
end Point
end ClassicalApprox
namespace ClassicalApprox
section Response
variable {Λ : MomentParameters} (S : MomentPoint Λ) {n : ℕ} [NeZero n]
private theorem responseHessian_eq (hCold : ColdNearStatement) (hσ : 0 < Λ.stepParams.threshold) {t : ℕ}
    (ht : t ≤ S.data.windowLevel) (hn : Λ.stepParams.n₀ ≤ n)
    (y : TorusSite n) (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)) (b b' : TorusBond n)
    (hsm : ContDiffThreeAt (levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y)
      (trivialField n)) :
    responseHessian (S.resp t) n y h b b' = remainderHessian (S.resp t) n y h b b' +
      blockMean Λ.stepParams.side (S.tower.stage t).depth n y h *
      ((S.resp t).coeff * shareHessian Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth y b b' +
        mixedDeriv ((S.resp t).siteRemainder n y) (trivialField n) ![b, b'] ![unitGenerator, unitGenerator]) := by
  have row := (stageOnFlow_at S ht).onFamily.admissible.bounds
  have cold : IsCold Λ.stepParams.threshold (trivialField n) := TermCalculus.isCold_trivialField hσ n
  have ev : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ),
      IsCold Λ.stepParams.threshold (perturb ![b, b'] ![unitGenerator, unitGenerator] τ (trivialField n)) :=
    hCold n (trivialField n) 2 _ _ 0 _ (by rw [perturb_zero]; exact cold)
  have hRa : ContDiffThreeAt ((S.resp t).siteRemainder n y) (trivialField n) :=
    row.site_family.smooth n hn y (trivialField n) cold
  have hRc : ContDiffThreeAt (responseRemainder (S.resp t).cold n y h) (trivialField n) :=
    row.remainder_smooth n hn y (trivialField n) cold h
  set G₁ : TorusField n → ℝ := fun W => (S.resp t).coeff *
      levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y W +
    (S.resp t).siteRemainder n y W with hG₁
  set e : ℝ := (S.resp t).siteRemainder n y (trivialField n) -
    (S.resp t).cold n y (trivialField n) (constOneWeight _) with he
  have eq1 : ∀ W : TorusField n, IsCold Λ.stepParams.threshold W →
      (S.resp t).cold n y W (constOneWeight _) = G₁ W - e := by
    intro W hW
    have := row.share_site n hn y W hW
    unfold centeredResponse centered at this
    simp only [hG₁, he]
    linarith
  have c₁ : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => (S.resp t).coeff *
      levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y
      (perturb ![b, b'] ![unitGenerator, unitGenerator] τ (trivialField n))) 0 := contDiffAt_const.mul (hsm 2 _ _)
  have c₂ : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ =>
      G₁ (perturb ![b, b'] ![unitGenerator, unitGenerator] τ (trivialField n))) 0 :=
    c₁.add (hRa 2 _ _)
  have c₃ : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ =>
      G₁ (perturb ![b, b'] ![unitGenerator, unitGenerator] τ (trivialField n)) - e) 0 :=
    c₂.sub contDiffAt_const
  have eqe : (fun τ : Fin 2 → ℝ => (S.resp t).cold n y
        (perturb ![b, b'] ![unitGenerator, unitGenerator] τ (trivialField n)) (constOneWeight _)) =ᶠ[𝓝 0]
      fun τ => G₁ (perturb ![b, b'] ![unitGenerator, unitGenerator] τ (trivialField n)) - e :=
    ev.mono fun τ hτ => eq1 _ hτ
  have c₄ : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ =>
      (S.resp t).cold n y (perturb ![b, b'] ![unitGenerator, unitGenerator] τ (trivialField n)) (constOneWeight _)) 0 :=
    c₃.congr_of_eventuallyEq eqe
  have d₁ : mixedDeriv (fun W => (S.resp t).cold n y W (constOneWeight _)) (trivialField n) ![b, b']
        ![unitGenerator, unitGenerator] =
      mixedDeriv (fun W => G₁ W - e) (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] := by
    unfold mixedDeriv
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ eqe 2).eq_of_nhds]
  have d₂ := TermCalculus.mixedDeriv_sub_const G₁ e (trivialField n) ![b, b'] ![unitGenerator, unitGenerator]
    (by norm_num) (by norm_num) c₂
  have d₃ := TermCalculus.mixedDeriv_add (fun W => (S.resp t).coeff *
      levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y W)
    ((S.resp t).siteRemainder n y)
    (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] (by norm_num) c₁ (hRa 2 _ _)
  have d₄ := TermCalculus.mixedDeriv_const_mul (S.resp t).coeff
    (levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y)
    (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] (by norm_num) (hsm 2 _ _)
  have e₁ : (fun W => (S.resp t).cold n y W h) = fun W => responseRemainder (S.resp t).cold n y h W +
      blockMean Λ.stepParams.side (S.tower.stage t).depth n y h * (S.resp t).cold n y W (constOneWeight _) := by
    funext W
    unfold responseRemainder
    ring
  have d₅ := TermCalculus.mixedDeriv_add (responseRemainder (S.resp t).cold n y h)
    (fun W => blockMean Λ.stepParams.side (S.tower.stage t).depth n y h * (S.resp t).cold n y W (constOneWeight _))
    (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] (by norm_num) (hRc 2 _ _) (contDiffAt_const.mul c₄)
  have d₆ := TermCalculus.mixedDeriv_const_mul (blockMean Λ.stepParams.side (S.tower.stage t).depth n y h)
    (fun W => (S.resp t).cold n y W (constOneWeight _))
    (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] (by norm_num) c₄
  show mixedDeriv (fun W => (S.resp t).cold n y W h) (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] =
    mixedDeriv (responseRemainder (S.resp t).cold n y h) (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] +
      blockMean Λ.stepParams.side (S.tower.stage t).depth n y h *
      ((S.resp t).coeff * mixedDeriv
          (levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y)
          (trivialField n) ![b, b'] ![unitGenerator, unitGenerator] +
        mixedDeriv ((S.resp t).siteRemainder n y) (trivialField n) ![b, b'] ![unitGenerator, unitGenerator])
  rw [e₁, d₅, d₆, d₁, d₂, hG₁, d₃, d₄]
private theorem abs_remainder_add_le {H u l G aa r al Cn Csh Ka D Ccl sz : ℝ} (hH : |H| ≤ sz) (hsz : 0 ≤ sz)
    (hl : l ≤ sz) (hu : 0 ≤ u) (hG : 0 < G)
    (hCsh : 0 ≤ Csh) (hKa : 0 ≤ Ka) (hCcl : 0 ≤ Ccl) (hal : |al - 1| ≤ Cn * u) (haa : |aa| ≤ Csh / G)
    (hr : |r| ≤ Ka * u / G) (hD : |D| ≤ Ccl * u * l / G) :
    |D + H * ((al - 1) * aa + r)| ≤ (Ccl + |Cn| * Csh + Ka) * u * sz / G := by
  have h1 : |al - 1| ≤ |Cn| * u := hal.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hu)
  have h2 : |(al - 1) * aa| ≤ |Cn| * u * (Csh / G) := by
    rw [abs_mul]
    exact mul_le_mul h1 haa (abs_nonneg _) (by positivity)
  have h3 : |(al - 1) * aa + r| ≤ |Cn| * u * (Csh / G) + Ka * u / G := (abs_add_le _ _).trans (add_le_add h2 hr)
  have h4 : |H * ((al - 1) * aa + r)| ≤ sz * (|Cn| * u * (Csh / G) + Ka * u / G) := by
    rw [abs_mul]
    exact mul_le_mul hH h3 (abs_nonneg _) hsz
  have h5 : Ccl * u * l / G ≤ Ccl * u * sz / G :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity)) hG.le
  have e : (Ccl + |Cn| * Csh + Ka) * u * sz / G = Ccl * u * sz / G + sz * (|Cn| * u * (Csh / G) + Ka * u / G) := by
    field_simp
    ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add (hD.trans h5) h4)
end Response
end ClassicalApprox
open ClassicalApprox in
theorem classicalFormsApproxStatement_holds (hS : remainderOneStepStatement) (hN : responseCoeffNearOneStatement)
    (hC : pullbackFormBoundStatement) (hF : responsesHaveFormsStatement) (hK : classicalFormsAnnihilateClosedStatement)
    (hR : CouplingFlowAboveWindow) (hSh : levelSharesUniformStatement) (hW : WeightsCloseToBlockMeans)
    (hCold : ColdNearStatement) : classicalFormsApproxStatement := by
  unfold remainderOneStepStatement ForAllPoints at hS
  unfold responseCoeffNearOneStatement ForAllPoints at hN
  unfold responsesHaveFormsStatement ForAllPoints at hF
  unfold classicalFormsAnnihilateClosedStatement ForAllPoints at hK
  unfold pullbackFormBoundStatement at hC
  unfold levelSharesUniformStatement at hSh
  have all := forAllParameters_and hS (forAllParameters_and hN (forAllParameters_and hF (forAllParameters_and hK
    (forAllParameters_and (forAllParameters_of_holdsOnAllParameters hC) (forAllParameters_of_holdsOnAllParameters hSh)))))
  unfold classicalFormsApproxStatement ForAllPoints ForAllParameters
  intro a ha
  obtain ⟨L₀, r₀, C₀, p₀, g⟩ := all a ha
  refine ⟨L₀, r₀, C₀, p₀, fun L hodd hL T hTa hTL hD hCS hOn hrt hCd Kr hFit => ?_⟩
  obtain ⟨y₀, f⟩ := g L hodd hL T hTa hTL hD hCS hOn hrt hCd Kr hFit
  refine ⟨max y₀ (max T.floorMin (400 * T.B)), fun y hy hRt hWy gg hg hgy k _ hk2 hk8 R d hd => ?_⟩
  have hy₁ : y₀ ≤ y := (le_max_left _ _).trans hy
  have hy₂ : T.floorMin ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₃ : 400 * T.B ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hy₄ : 1 ≤ y := hD.yC_ge.trans ((le_max_left _ _).trans hy₂)
  obtain ⟨⟨Cs, _, _, _, _, bS⟩, ⟨Cn, _, _, _, _, bN⟩, ⟨_, _, _, _, _, bF⟩, ⟨_, _, _, _, _, bK⟩, bC, bSh⟩ :=
    f y hy₁ hRt hWy gg hg hgy k hk2 hk8 R d hd
  obtain ⟨Csh, hCsh, bFam⟩ := bSh
  have hAdm : AdmissibleStep (T.stepParameters y) := ⟨hD.fits y hy₂, hRt, hWy⟩
  have hodd' : Odd (T.stepParameters y).side := by
    rw [show (T.stepParameters y).side = L from hTL]; exact hodd
  have hσ : 0 < (T.stepParameters y).threshold := hD.σ_pos
  have hB : 0 ≤ T.B := by linarith [hD.B_ge]
  have hL9 : 9 ≤ (T.stepParameters y).side := by
    have : 2 ^ 40 ≤ T.side := hD.L_ge
    show 9 ≤ T.side
    omega
  set Ccl : ℝ := 2 * |Cs 0| with hCcl
  have hKa : 0 ≤ Kr.Ka := (hFit y).Ka_nonneg
  have hKc : 0 ≤ Kr.Kc := by linarith [(hFit y).Kc_ge]
  refine ⟨fun i => if i = 0 then Ccl else if i = 1 then Ccl + |Cn 0| * Csh + Kr.Ka else Kr.Kc + Ccl, 1, y, one_pos,
    le_rfl, fun S => ?_⟩
  intro t ht n _ hn z h b b'
  obtain ⟨hxK, hmove⟩ := hR (T.stepParameters y) hAdm gg hg hgy S.β S.data.windowLevel S.window_le S.passage
  have hxy : ∀ j ≤ S.data.windowLevel, y ≤ S.coupling j := hxK
  have hx0 : ∀ j ≤ S.data.windowLevel, 0 < S.coupling j := fun j hj => by linarith [hxy j hj]
  have hxs : ∀ j, j + 1 ≤ S.data.windowLevel →
      S.coupling j ^ (-(1 / 2) : ℝ) ≤ 1.01 * S.coupling (j + 1) ^ (-(1 / 2) : ℝ) := by
    intro j hj
    have h₂ := hmove j (j + 1) (by omega) hj
    have e : 2 * (T.stepParameters y).B * (((j + 1 : ℕ) : ℝ) - (j : ℝ)) = 2 * T.B := by
      push_cast
      show 2 * T.B * _ = _
      ring
    rw [e] at h₂
    exact rpow_neg_half_le_of_abs_sub_le hB (hy₃.trans (hxy j (by omega))) (hx0 j (by omega)) (hx0 (j + 1) hj) h₂
  have hρ : ∀ j ≤ S.data.windowLevel, (S.tower.stage j).anchorRadius = T.ρA :=
    fun j hj => (stageOnFlow_at S hj).onFamily.onFamily.anchorRadius_eq
  have hkills : ∀ j ≤ S.data.windowLevel, ∀ (m : ℕ) [NeZero m], (T.stepParameters y).n₀ ≤ m → ∀ (w : TorusSite m)
      (q : PlaquetteWeight (fineSide (T.stepParameters y).side (S.tower.stage j).depth m)),
      AnnihilatesGradients (remainderHessian (S.resp j) m w q) ∧
        AnnihilatesGradients (classicalRemainder S.tower S.resp j m q w) := fun j hj m _ hm w q =>
    ⟨annihilatesGradients_hessianAtIdentity (bF S j hj m hm w q).2.1, (bK S j hj m hm w q).1.1⟩
  have hnear := remainderHessian_near_classical S (Cb := Cs 0) (bS S) bC hkills hxs hx0 hL9 hρ t ht n hn z h b b'
  have hG := TermCalculus.weight_pos (T.stepParameters y) (tripleDiam z b b')
  have hxt : 0 < S.coupling t := hx0 t ht
  have hu0 : 0 ≤ S.coupling t ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos hxt _).le
  have hu1 : S.coupling t ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hy₄.trans (hxy t ht)) (by norm_num)
  have hl0 := _root_.YangMills.Construction.MomentLaw.ClassicalApprox.weightLipschitz_nonneg (T.stepParameters y).side (S.tower.stage t).depth h
  have st := stageOnFlow_at S ht
  have row := st.onFamily.admissible.bounds
  have cold : IsCold (T.stepParameters y).threshold (trivialField n) := TermCalculus.isCold_trivialField hσ n
  have hK : (S.resp t).responseParams = Kr := st.params_eq
  have hxc : (S.tower.stage t).coupling = S.coupling t := st.coupling_eq
  refine ⟨?_, ?_, ?_⟩
  · have hr := row.remainder_decay n hn z (trivialField n) cold h 2 ![b, b'] ![unitGenerator, unitGenerator]
      (by norm_num) (by norm_num) areUnitVectors_unitGenerator
    simp only [show ¬ (2 = 3) by norm_num, if_false, hK] at hr
    have hr' : |remainderHessian (S.resp t) n z h b b'| ≤
        Kr.Kc * weightLipschitz (T.stepParameters y).side (S.tower.stage t).depth h /
          (T.stepParameters y).weight (tripleDiam z b b') := hr
    have t₁ : |classicalRemainder S.tower S.resp t n h z b b'| ≤ |remainderHessian (S.resp t) n z h b b'| +
        |remainderHessian (S.resp t) n z h b b' - classicalRemainder S.tower S.resp t n h z b b'| := by
      have := abs_sub_abs_le_abs_sub (classicalRemainder S.tower S.resp t n h z b b')
        (remainderHessian (S.resp t) n z h b b')
      rw [abs_sub_comm (classicalRemainder S.tower S.resp t n h z b b')] at this
      linarith
    have hCcl0 : 0 ≤ Ccl := by positivity
    have t₂ : Ccl * S.coupling t ^ (-(1 / 2) : ℝ) * weightLipschitz (T.stepParameters y).side (S.tower.stage t).depth h /
          (T.stepParameters y).weight (tripleDiam z b b') ≤
        Ccl * weightLipschitz (T.stepParameters y).side (S.tower.stage t).depth h /
          (T.stepParameters y).weight (tripleDiam z b b') := by
      refine div_le_div_of_nonneg_right ?_ hG.le
      nlinarith [mul_nonneg hCcl0 hl0]
    have e : (if (2 : ℕ) = 0 then Ccl else if (2 : ℕ) = 1 then Ccl + |Cn 0| * Csh + Kr.Ka else Kr.Kc + Ccl) =
        Kr.Kc + Ccl := by norm_num
    show |classicalRemainder S.tower S.resp t n h z b b'| ≤
      (if (2 : ℕ) = 0 then Ccl else if (2 : ℕ) = 1 then Ccl + |Cn 0| * Csh + Kr.Ka else Kr.Kc + Ccl) * _ / _
    rw [e, add_mul, add_div]
    linarith
  · simpa using hnear
  · have hFam := (bFam (S.tower.stage t).depth).1
    have eS : levelShareFamily (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth n z =
        levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z := by
      funext W
      unfold levelShareFamily
      rw [dif_neg (NeZero.ne n)]
    have hsm : ContDiffThreeAt
        (levelShare (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth Finset.univ z)
        (trivialField n) := by
      rw [← eS]
      exact hFam.smooth n hn z (trivialField n) cold
    have hsplit := responseHessian_eq S hCold hσ ht hn z h b b' hsm
    have haa : |shareHessian (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth z b b'| ≤
        Csh / (T.stepParameters y).weight (tripleDiam z b b') := by
      have := hFam.decay n hn z (trivialField n) cold 2 ![b, b'] ![unitGenerator, unitGenerator] (by norm_num)
        (by norm_num) areUnitVectors_unitGenerator
      rw [eS] at this
      exact this
    have hra := row.site_family.decay n hn z (trivialField n) cold 2 ![b, b'] ![unitGenerator, unitGenerator]
      (by norm_num) (by norm_num) areUnitVectors_unitGenerator
    simp only [show ¬ (2 = 3) by norm_num, if_false, hK, hxc] at hra
    have hsup := ((hW (T.stepParameters y).side hodd' (S.tower.stage t).depth n z).1 h)
    have hsz0 : 0 ≤ weightNorm (T.stepParameters y).side (S.tower.stage t).depth h := hl0.trans (le_max_right _ _)
    have key := abs_remainder_add_le (H := blockMean (T.stepParameters y).side (S.tower.stage t).depth n z h)
      (u := S.coupling t ^ (-(1 / 2) : ℝ))
      (l := weightLipschitz (T.stepParameters y).side (S.tower.stage t).depth h)
      (G := (T.stepParameters y).weight (tripleDiam z b b'))
      (aa := shareHessian (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth z b b')
      (r := mixedDeriv ((S.resp t).siteRemainder n z) (trivialField n) ![b, b'] ![unitGenerator, unitGenerator])
      (al := (S.resp t).coeff) (Cn := Cn 0) (Csh := Csh) (Ka := Kr.Ka)
      (D := remainderHessian (S.resp t) n z h b b' - classicalRemainder S.tower S.resp t n h z b b') (Ccl := Ccl)
      (sz := weightNorm (T.stepParameters y).side (S.tower.stage t).depth h) (hsup.trans (le_max_left _ _)) hsz0
      (le_max_right _ _) hu0 hG hCsh hKa (by positivity)
      (bN S t ht) haa hra hnear
    have e : responseHessian (S.resp t) n z h b b' - classicalQuadratic S.tower S.resp t n h z b b' =
        remainderHessian (S.resp t) n z h b b' - classicalRemainder S.tower S.resp t n h z b b' +
          blockMean (T.stepParameters y).side (S.tower.stage t).depth n z h *
          (((S.resp t).coeff - 1) *
              shareHessian (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth z b b' +
            mixedDeriv ((S.resp t).siteRemainder n z) (trivialField n) ![b, b'] ![unitGenerator, unitGenerator]) := by
      rw [hsplit]
      show _ - (blockMean (T.stepParameters y).side (S.tower.stage t).depth n z h *
          shareHessian (T.stepParameters y).coupling (T.stepParameters y).side (S.tower.stage t).depth z b b' +
        classicalRemainder S.tower S.resp t n h z b b') = _
      ring
    rw [e]
    simpa using key
end YangMills.Construction.MomentLaw
end
