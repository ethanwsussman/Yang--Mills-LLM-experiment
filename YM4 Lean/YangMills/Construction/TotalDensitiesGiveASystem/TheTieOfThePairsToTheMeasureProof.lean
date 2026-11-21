import YangMills.Construction.FourPointCondition.ConnectedFunctionsAreHomogeneous
import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindow
import YangMills.Construction.ParameterData.TheNumberOfTheFlowIsNearOne
import YangMills.Construction.ResponseInTheExpansion.TheConnectedLawAtAPairIsTheFreeKernel
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheExpansionFlowIsTheTotalFlow
import YangMills.Construction.TotalDensitiesGiveASystem.TheParametersAreDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheShapesAreATuple
import YangMills.Construction.TotalDensitiesGiveASystem.TheTieOfThePairsToTheMeasure
import YangMills.Construction.TotalDensitiesGiveASystem.TheWindowHasItsData
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
private theorem rpow_half_ratio_near_one {x r al a Kf C c κ : ℝ} (hx : 1 ≤ x) (ha : 0 < a) (hκ : 0 < κ) (hK : κ ≤ Kf) (hc : 0 ≤ c)
    (hC : |x ^ 2 * r - al ^ 2 * (a * Kf)| ≤ C * x ^ (-(1 / 100 : ℝ)))
    (hal : |al - 1| ≤ c * x ^ (-(1 / 2) : ℝ)) (hal' : c * x ^ (-(1 / 2) : ℝ) ≤ 1 / 4)
    (hsmall : (C / (a * κ) + 3 * c) * x ^ (-(1 / 100 : ℝ)) ≤ 1 / 2) :
    0 < r ∧ |(a * Kf / r) ^ ((1 : ℝ) / 2) / x - 1| ≤ (C / (a * κ) + 3 * c) * x ^ (-(1 / 100 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set u := x ^ (-(1 / 100 : ℝ)) with hu
  have hupos : 0 < u := Real.rpow_pos_of_pos hx0 _
  have hv : x ^ (-(1 / 2) : ℝ) ≤ u := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hC0 : 0 ≤ C := by
    have h0 := le_trans (abs_nonneg _) hC
    exact nonneg_of_mul_nonneg_left h0 hupos
  have hKf : 0 < Kf := lt_of_lt_of_le hκ hK
  have haK : 0 < a * Kf := mul_pos ha hKf
  set e := x ^ 2 * r / (a * Kf) - 1 with he
  have hal2 : |al ^ 2 - 1| ≤ 3 * (c * u) := by
    have h1 : |al - 1| ≤ 1 / 4 := le_trans hal hal'
    have h2 : |al + 1| ≤ 3 := by
      have := abs_le.1 h1
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    have h3 : al ^ 2 - 1 = (al - 1) * (al + 1) := by ring
    rw [h3, abs_mul]
    have h4 : |al - 1| ≤ c * u := le_trans hal (mul_le_mul_of_nonneg_left hv hc)
    calc |al - 1| * |al + 1| ≤ (c * u) * 3 := mul_le_mul h4 h2 (abs_nonneg _) (by positivity)
      _ = 3 * (c * u) := by ring
  have heb : |e| ≤ (C / (a * κ) + 3 * c) * u := by
    have h1 : e = (x ^ 2 * r - al ^ 2 * (a * Kf)) / (a * Kf) + (al ^ 2 - 1) := by
      rw [he]
      field_simp
      ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    have h2 : |(x ^ 2 * r - al ^ 2 * (a * Kf)) / (a * Kf)| ≤ C / (a * κ) * u := by
      rw [abs_div, abs_of_pos haK, div_le_iff₀ haK]
      have h3 : C / (a * κ) * u * (a * Kf) = C * u * (Kf / κ) := by
        field_simp
      rw [h3]
      have h4 : 1 ≤ Kf / κ := (one_le_div hκ).2 hK
      have h5 : 0 ≤ C * u := by positivity
      nlinarith
    have : (C / (a * κ) + 3 * c) * u = C / (a * κ) * u + 3 * (c * u) := by ring
    linarith
  have hehalf : |e| ≤ 1 / 2 := le_trans heb hsmall
  have he' := abs_le.1 hehalf
  have h1e : 0 < 1 + e := by linarith [he'.1]
  have hxr : x ^ 2 * r = (a * Kf) * (1 + e) := by
    rw [he]
    field_simp
    ring
  have hr : 0 < r := by
    have h1 : 0 < x ^ 2 * r := by rw [hxr]; positivity
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < x ^ 2)).1 h1
  refine ⟨hr, ?_⟩
  set w := Real.sqrt (1 + e) with hw
  have hw2 : w ^ 2 = 1 + e := Real.sq_sqrt h1e.le
  have hw0 : 0 < w := Real.sqrt_pos.2 h1e
  have hw7 : 7 / 10 ≤ w := by
    apply Real.le_sqrt_of_sq_le
    linarith [he'.1]
  have hval : (a * Kf / r) ^ ((1 : ℝ) / 2) / x = 1 / w := by
    have h1 : a * Kf / r = (x / w) ^ 2 := by
      rw [div_pow, hw2, div_eq_div_iff hr.ne' h1e.ne']
      exact hxr.symm
    rw [h1, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    field_simp
  rw [hval]
  have h2 : |1 / w - 1| ≤ |e| := by
    have h3 : 1 / w - 1 = -e / (w * (1 + w)) := by
      have : e = w ^ 2 - 1 := by linarith
      rw [this]
      field_simp
      ring
    rw [h3, abs_div, abs_neg, abs_of_pos (by positivity : 0 < w * (1 + w))]
    apply div_le_self (abs_nonneg _)
    nlinarith
  exact h2.trans heb
private theorem separation_scale_bounds {G P x : ℝ} {L : ℕ} (hG : (2 : ℝ) ^ 18 ≤ G) (hP2 : P ≤ 2 * G) (hGP : G ≤ P)
    (hL : ((2 : ℝ) ^ 13 * L) ^ (1900 : ℕ) ≤ P) (hL0 : 0 < L) (hx₁ : G < x) (hx₂ : x ≤ P) :
    2 ^ 12 * (L : ℝ) * (TorusLumps.clusterRange x : ℝ) ≤ P ^ ((1 : ℝ) / 95) ∧ P ^ ((1 : ℝ) / 95) ≤ x ^ ((1 : ℝ) / 90) := by
  have hG0 : 0 < G := lt_of_lt_of_le (by norm_num) hG
  have hP0 : 0 < P := lt_of_lt_of_le hG0 hGP
  have hx0 : 0 < x := hG0.trans hx₁
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ 2 ^ 18 := by norm_num
    linarith
  constructor
  · have hu1 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
    have hc : (TorusLumps.clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by
      have := (Nat.ceil_lt_add_one (a := x ^ ((1 : ℝ) / 100)) (by linarith)).le
      unfold TorusLumps.clusterRange
      linarith
    have hxP : x ^ ((1 : ℝ) / 100) ≤ P ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hx0.le hx₂ (by norm_num)
    have hpow : (2 : ℝ) ^ 13 * L ≤ P ^ ((1 : ℝ) / 1900) := by
      have h1 : (((2 : ℝ) ^ 13 * L) ^ (1900 : ℕ)) ^ ((1 : ℝ) / 1900) = (2 : ℝ) ^ 13 * L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [← h1]
      exact Real.rpow_le_rpow (by positivity) hL (by norm_num)
    have hsplit : P ^ ((1 : ℝ) / 95) = P ^ ((1 : ℝ) / 1900) * P ^ ((1 : ℝ) / 100) := by
      rw [← Real.rpow_add hP0]
      norm_num
    have hQ : 0 ≤ P ^ ((1 : ℝ) / 100) := (Real.rpow_pos_of_pos hP0 _).le
    rw [hsplit]
    calc 2 ^ 12 * (L : ℝ) * (TorusLumps.clusterRange x : ℝ) ≤ 2 ^ 12 * (L : ℝ) * (2 * P ^ ((1 : ℝ) / 100)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (2 ^ 13 * L) * P ^ ((1 : ℝ) / 100) := by ring
      _ ≤ P ^ ((1 : ℝ) / 1900) * P ^ ((1 : ℝ) / 100) := mul_le_mul_of_nonneg_right hpow hQ
  · have h2 : (2 : ℝ) ≤ G ^ ((1 : ℝ) / 18) := by
      have h1 : ((2 : ℝ) ^ (18 : ℕ)) ^ ((1 : ℝ) / 18) = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [← h1]
      exact Real.rpow_le_rpow (by norm_num) hG (by norm_num)
    have h3 : P ≤ G ^ ((19 : ℝ) / 18) := by
      have : G ^ ((19 : ℝ) / 18) = G ^ ((1 : ℝ) / 18) * G := by
        rw [← Real.rpow_add_one hG0.ne']
        norm_num
      rw [this]
      nlinarith
    calc P ^ ((1 : ℝ) / 95) ≤ (G ^ ((19 : ℝ) / 18)) ^ ((1 : ℝ) / 95) :=
          Real.rpow_le_rpow hP0.le h3 (by norm_num)
      _ = G ^ ((1 : ℝ) / 90) := by
          rw [← Real.rpow_mul hG0.le]
          norm_num
      _ ≤ x ^ ((1 : ℝ) / 90) := Real.rpow_le_rpow hG0.le hx₁.le (by norm_num)
private theorem forty_rpow_le_of_exp_log_cube_le {P l : ℝ} (hP : (2 : ℝ) ^ 18 ≤ P) (hl : Real.exp (Real.log P ^ 3) ≤ l) :
    40 * P ^ ((1 : ℝ) / 95) ≤ l := by
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hP1 : 1 ≤ P := le_trans (by norm_num) hP
  have hlog : 6 ≤ Real.log P := by
    have h1 : (18 : ℝ) * Real.log 2 ≤ Real.log P := by
      have := Real.log_le_log (by norm_num) hP
      rwa [Real.log_pow] at this
    have h2 := Real.log_two_gt_d9
    linarith
  have h3 : Real.log P + 4 ≤ Real.log P ^ 3 := by nlinarith [sq_nonneg (Real.log P)]
  have h4 : Real.exp 4 * P ≤ Real.exp (Real.log P ^ 3) := by
    calc Real.exp 4 * P = Real.exp (Real.log P + 4) := by
          rw [Real.exp_add, Real.exp_log hP0]; ring
      _ ≤ _ := Real.exp_le_exp.2 h3
  have h5 : (40 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (1 : ℝ)
    have h2 : (2 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have h6 : Real.exp 1 ^ 4 = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h7 : (2.7 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have h8 : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h7 4
    rw [← h6]
    norm_num at h8 ⊢
    linarith
  have h6 : P ^ ((1 : ℝ) / 95) ≤ P := by
    calc P ^ ((1 : ℝ) / 95) ≤ P ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
      _ = P := Real.rpow_one P
  have h7 : 0 ≤ P ^ ((1 : ℝ) / 95) := (Real.rpow_pos_of_pos hP0 _).le
  nlinarith
theorem pairsTiedToWilsonMeasure_holds (hT : TotalDensitiesGiveASystem.ResponseParametersToAdmissibleParameters)
    (hL : FourPointCondition.cumulantLawsAtWindowLevel) (hK : ResponseInTheExpansion.pairCumulantEqFreeKernelStatement)
    (hN : TrajectoryData.responseCoeffNearOneStatement) (hA : TotalDensitiesGiveASystem.BumpPairIsSeparatedTuple)
    (hR : FourPointCondition.connectedFunctionsHomogeneousStatement) (hW : TotalDensitiesGiveASystem.passageWindowDataStatement)
    (hJ : TotalDensities.expansionFlowEqTotalFlow) : TotalDensities.PairsTiedToWilsonMeasure := by
  have h₂ : ResponseInTheExpansion.HoldsOnParameterFamilies fun T y => ∃ Kr : WeightedResponses.ResponseParameters,
      Kr.Admissible (T.stepParameters y) ∧ ∀ (β : ℝ) (k : ℕ),
      (∀ j ≤ k, y ≤ ResponseInTheExpansion.flowCouplings (T.stepParameters y) β j) → ∃ al : ℕ → ℝ,
        ResponseInTheExpansion.IsChainResponseCoeff (T.stepParameters y) Kr β k al ∧
        |al k - 1| ≤ 6 * Kr.Cstar / (3 / 4 * CouplingFlow.slopeConst T.side) *
          ResponseInTheExpansion.flowCouplings (T.stepParameters y) β k ^ (-(1 / 2) : ℝ) ∧
        6 * Kr.Cstar / (3 / 4 * CouplingFlow.slopeConst T.side) *
          ResponseInTheExpansion.flowCouplings (T.stepParameters y) β k ^ (-(1 / 2) : ℝ) ≤ 1 / 4 := by
    intro a ha
    obtain ⟨L₀, rt₀, C₀, hrt, f⟩ := hN a ha
    refine ⟨L₀, rt₀, C₀, hrt, fun L hodd hge T h1 h2 h3 h4 h5 h6 h7 => ?_⟩
    obtain ⟨Kr, hKr, y₀, g⟩ := f L hodd hge T h1 h2 h3 h4 h5 h6 h7
    exact ⟨y₀, fun y hy hr hw => ⟨Kr, hKr y, g y hy hr hw⟩⟩
  refine TotalDensities.HoldsAtAdmissibleParameters.mono (TotalDensities.HoldsAtAdmissibleParameters.and
    (TotalDensities.HoldsAtAdmissibleParameters.and (TotalDensities.HoldsAtAdmissibleParameters.and (hT _ hL) (hT _ h₂)) hW) hJ)
    fun T y hDr hAll => ?_
  obtain ⟨⟨⟨hl, Kr, hKr, hn⟩, hw⟩, hj⟩ := hAll
  obtain ⟨C, X, hCX⟩ := hl Kr hKr (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨c₅, -, y₁, fW⟩ := hw (2 * T.B) le_rfl
  obtain ⟨y₂, fJ⟩ := hj (2 * T.B) le_rfl
  have hLpos : 0 < T.side := lt_of_lt_of_le (by norm_num) hDr.L_ge
  have hB := hDr.B_ge
  have hLr : (1 : ℝ) < T.side := by
    have h : 2 ^ 40 ≤ T.side := hDr.L_ge
    have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
    exact_mod_cast h'
  have hslope : 0 < CouplingFlow.slopeConst T.side := by
    have hlog := Real.log_pos hLr
    have hpi := Real.pi_pos
    unfold CouplingFlow.slopeConst
    positivity
  set c := 6 * Kr.Cstar / (3 / 4 * CouplingFlow.slopeConst T.side) with hc
  have hc0 : 0 ≤ c := by
    have := hKr.Cstar_nonneg
    positivity
  set a : ℝ := 9 / Real.pi ^ 4 with ha
  have ha0 : 0 < a := by have := Real.pi_pos; positivity
  set κ : ℝ := (10 : ℝ) ^ (-8 : ℤ) * (1 / 4) ^ 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set E := C / (a * κ) + 3 * c with hE
  refine ⟨|E| + 1, by positivity, max y₁ (max y₂ (max X (max y (max (2 ^ 18) (max (4 * T.B) (max (((2 : ℝ) ^ 13 * T.side) ^ (1900 : ℕ))
    (|2 * E| ^ (100 : ℕ)))))))), fun g hg hy => ?_⟩
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ : y₁ ≤ g ^ (-2 : ℤ) ∧ y₂ ≤ g ^ (-2 : ℤ) ∧ X ≤ g ^ (-2 : ℤ) ∧ y ≤ g ^ (-2 : ℤ) ∧
      (2 : ℝ) ^ 18 ≤ g ^ (-2 : ℤ) ∧ 4 * T.B ≤ g ^ (-2 : ℤ) ∧ ((2 : ℝ) ^ 13 * T.side) ^ (1900 : ℕ) ≤ g ^ (-2 : ℤ) ∧
      |2 * E| ^ (100 : ℕ) ≤ g ^ (-2 : ℤ) := by
    simpa only [max_le_iff] using hy
  have w := fW g hg a₁
  have j := fJ g hg a₂
  intro K β hp m hside
  have hrow : TotalDensities.IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β := by
    have h' : β ∈ SequencePassage.definedPassageWindow (TotalDensityFlow.IsDefinedUpTo (T.stepParameters y)) (2 * T.B) g
      (TotalDensityFlow.coupling (T.stepParameters y)) K := hp
    rw [(j K).1] at h'
    exact h'
  have hxe : TotalDensityFlow.coupling (T.stepParameters y) β K = (TorusLumps.couplingFlow (T.stepParameters y) β K).1 :=
    (j K).2 β hrow K le_rfl
  set G := g ^ (-2 : ℤ) with hGdef
  set Pn := SequencePassage.passageThreshold (2 * T.B) g with hPn
  have hPG : Pn = G + 2 * T.B := rfl
  set x := (TorusLumps.couplingFlow (T.stepParameters y) β K).1 with hxdef
  have hxG : G < x := w.coupling_gt K β hrow K le_rfl
  have hxP : x ≤ Pn := hrow.2.1
  have hrun : ∀ j' ≤ (K : ℕ), G < (TorusLumps.couplingFlow (T.stepParameters y) β j').1 :=
    fun j' hj' => w.coupling_gt K β hrow j' hj'
  have hG18 : (2 : ℝ) ^ 18 ≤ Pn := by rw [hPG]; linarith
  have hP2 : Pn ≤ 2 * G := by rw [hPG]; linarith
  have hGP : G ≤ Pn := by rw [hPG]; linarith
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ 2 ^ 18 := by norm_num
    linarith
  obtain ⟨wa, wb⟩ := separation_scale_bounds a₅ hP2 hGP (le_trans a₇ hGP) hLpos hxG hxP
  set n := Pn ^ ((1 : ℝ) / 95) with hn'
  have hn0 : 0 < n := Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hG18) _
  have h40 : 40 * n ≤ PeriodicLattice.torusSide (T.stepParameters y).side m := forty_rpow_le_of_exp_log_cube_le hG18 hside
  obtain ⟨tup, pair, hKf⟩ := hA (T.stepParameters y) m n hLpos m.pos hn0 h40
  obtain ⟨al, hnum, hal, hal'⟩ := hn β K fun j' hj' => a₄.trans (hrun j' hj').le
  have hlog : Real.exp (Real.log x ^ 3) ≤
      PeriodicLattice.torusSide (T.stepParameters y).side m / FourPointCondition.levelMesh (T.stepParameters y).side K K := by
    have h1 : FourPointCondition.levelMesh (T.stepParameters y).side K K = 1 := by
      simp [FourPointCondition.levelMesh, PeriodicLattice.meshSize]
    rw [h1, div_one]
    refine le_trans (Real.exp_le_exp.2 ?_) hside
    have h2 : Real.log x ≤ Real.log Pn := Real.log_le_log (by linarith) hxP
    have h3 : 0 ≤ Real.log x := Real.log_nonneg hx1
    exact pow_le_pow_left₀ h3 h2 3
  have h1s : FourPointCondition.levelMesh (T.stepParameters y).side K K = 1 := by
    simp [FourPointCondition.levelMesh, PeriodicLattice.meshSize]
  have hlaw := hCX β K al (fun j' hj' => a₃.trans (hrun j' hj').le) hnum K m n hlog
    (by rw [h1s, div_one]; exact wa) (by rw [h1s, div_one]; exact wb) 1 (Or.inl rfl) _ tup
  have hbeta : 0 < β := by
    have h1 : SequencePassage.passageThreshold (2 * T.B) g ≤ β := hrow.1
    linarith
  have hstand : Conventions.IsAdmissibleBlockingFactor (T.stepParameters y).side :=
    ⟨hDr.L_odd, le_trans (by norm_num) hDr.L_ge⟩
  have him := (hR.1 ⟨(T.stepParameters y).side, hstand, K, m⟩ β 2 _ (fun _ => 1) hbeta (by norm_num) (by
    intro i
    exact tup.lipschitz i)).1
  set S := PeriodicLattice.torusUrsellFunction (T.stepParameters y).side m K β
    ![TrajectoryData.firstBump (T.stepParameters y).side m n 0, TrajectoryData.translatedBump (T.stepParameters y).side m n 0] with hS
  have hSr : S = ((S.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hlaw' : |x ^ 2 * S.re - al K ^ 2 * (a * TestFunctions.inverseEighthKernelTorus
      (TrajectoryData.firstBump (T.stepParameters y).side m n 0)
      (TrajectoryData.translatedBump (T.stepParameters y).side m n 0))| ≤ C * x ^ (-(1 / 100 : ℝ)) := by
    have hq := hK (T.stepParameters y) m n (1 / 4) _ _ hn0 (by norm_num) h40 pair
    have e1 : ((x ^ (1 + 1) : ℝ) : ℂ) * S - ((al K ^ (1 + 1) * ResponseInTheExpansion.gaussianCumulantLimit
        (PeriodicLattice.torusSide (T.stepParameters y).side m) ![TrajectoryData.firstBump (T.stepParameters y).side m n 0,
        TrajectoryData.translatedBump (T.stepParameters y).side m n 0] : ℝ) : ℂ) =
        ((x ^ 2 * S.re - al K ^ 2 * (a * TestFunctions.inverseEighthKernelTorus
          (TrajectoryData.firstBump (T.stepParameters y).side m n 0)
          (TrajectoryData.translatedBump (T.stepParameters y).side m n 0)) : ℝ) : ℂ) := by
      rw [hq, ← ha]
      nth_rw 1 [hSr]
      push_cast
      ring
    have := hlaw
    rw [e1, Complex.norm_real, Real.norm_eq_abs] at this
    simpa using this
  have hsmall : E * x ^ (-(1 / 100 : ℝ)) ≤ 1 / 2 := by
    have hx0 : 0 < x := by linarith
    have h1 : |2 * E| ≤ x ^ ((1 : ℝ) / 100) := by
      have h2 : (|2 * E| ^ (100 : ℕ)) ≤ x := a₈.trans hxG.le
      have h3 : ((|2 * E| ^ (100 : ℕ)) : ℝ) ^ ((1 : ℝ) / 100) = |2 * E| := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
        norm_num
      rw [← h3]
      exact Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    have h4 : x ^ (-(1 / 100 : ℝ)) * x ^ ((1 : ℝ) / 100) = 1 := by
      rw [← Real.rpow_add hx0]
      norm_num
    have h5 : 0 < x ^ (-(1 / 100 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have h6 : 2 * E ≤ x ^ ((1 : ℝ) / 100) := le_trans (le_abs_self _) h1
    nlinarith
  obtain ⟨r0, rb⟩ := rpow_half_ratio_near_one hx1 ha0 hκ0 hKf hc0 hlaw' hal hal' hsmall
  have hamp : TwoPointFunction.amplitudeConstant = a := by
    unfold TwoPointFunction.amplitudeConstant
    rw [ha]
    norm_num [ParameterChoice.colorNumber]
  refine ⟨S.re, r0, hSr, ?_, ?_, ?_⟩
  · rw [hamp, hxe]
    refine rb.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _))
    linarith [le_abs_self E]
  · rw [hxe]
    exact hxG
  · rw [hxe]
    exact hxP
end YangMills.Construction.TotalDensitiesGiveASystem
end
