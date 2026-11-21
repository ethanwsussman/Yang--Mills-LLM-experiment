import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.ColdGroundIsTheColdSetting
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.GasDensitiesForget
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAgreeingStates
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasAtAStep
import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXi
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAgreeingGrounds
import YangMills.Construction.ClusterExpansionOfAStep.StateOverAColdField
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheGasDensities
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps StepGas StepSettings StepCosts ShareFamilies HoledShares RenormalizationStepParameters StepMarks
namespace ImageDensities
theorem eq_mul_exp_of_logs {ι : Type} [Fintype ι] {D₁ P c ξ c₁ ξ₁ x' A Dq Dp : ℝ} {ζ g ζ₁ g₁ a : ι → ℝ}
    (hc : 0 < c) (hξ : 0 < ξ) (hc₁ : 0 < c₁) (hξ₁ : 0 < ξ₁)
    (hq : Dq = D₁ * P * c * ξ) (h₁ : Dp = D₁ * c₁ * ξ₁)
    (lc : Real.log c = ∑ i, ζ i) (lξ : Real.log ξ = ∑ i, g i)
    (lc₁ : Real.log c₁ = ∑ i, ζ₁ i) (lξ₁ : Real.log ξ₁ = ∑ i, g₁ i) (hA : ∑ i, a i = A) :
    Dq = Dp * Real.exp (-x' * A + ∑ i, (ζ i + g i + x' * a i - (ζ₁ i + g₁ i))) * P := by
  have hsum : -x' * A + ∑ i, (ζ i + g i + x' * a i - (ζ₁ i + g₁ i)) =
      Real.log c + Real.log ξ - (Real.log c₁ + Real.log ξ₁) := by
    have h : ∑ i, (ζ i + g i + x' * a i - (ζ₁ i + g₁ i)) =
        ∑ i, ζ i + ∑ i, g i + x' * ∑ i, a i - (∑ i, ζ₁ i + ∑ i, g₁ i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [h, lc, lξ, lc₁, lξ₁, hA]
    ring
  rw [hsum, Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hc, Real.exp_log hξ, Real.exp_log hc₁,
    Real.exp_log hξ₁, hq, h₁]
  field_simp
theorem abs_sub_le_of_parts {e₁ e₂ e₃ E zV zV' z₁ z₁' gV gV' g₁ g₁' aV aV' x' : ℝ}
    (h₁ : |zV - zV'| ≤ e₁) (h₂ : |z₁ - z₁'| ≤ e₁) (h₃ : |gV - gV'| ≤ e₂) (h₄ : |g₁ - g₁'| ≤ e₂)
    (h₅ : |x' * aV - x' * aV'| ≤ e₃) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₃ : 0 ≤ e₃)
    (hE : 4 * e₁ + 3 * e₂ + e₃ ≤ E) :
    |(zV + gV + x' * aV - (z₁ + g₁)) - (zV' + gV' + x' * aV' - (z₁' + g₁'))| ≤ E := by
  have e : (zV + gV + x' * aV - (z₁ + g₁)) - (zV' + gV' + x' * aV' - (z₁' + g₁')) =
      (zV - zV') + (gV - gV') + (x' * aV - x' * aV') - (z₁ - z₁') - (g₁ - g₁') := by ring
  rw [e]
  rw [abs_le] at h₁ h₂ h₃ h₄ h₅ ⊢
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2, h₄.1, h₄.2, h₅.1, h₅.2]
variable {n : ℕ} [NeZero n]
theorem isCold_trivialField {s : ℝ} (hs : 0 < s) : IsCold s (trivialField n) := by
  intro x μ ν _
  simp [curvature, holonomy, trivialField, hs]
theorem thickening_empty (m : ℕ) : thickening m (∅ : Finset (TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.thickening_empty <;> assumption
theorem torusHotSites_eq_empty {ℓ : StepParameters} {r : ℕ} {V : TorusField n} (h : IsHullState ℓ r V ∅) :
    torusHotSites ℓ V = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
  have : z ∈ thickening (2 * r) (torusHotSites ℓ V) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz, by simp [supDist]⟩
  exact absurd (h.1 this) (Finset.notMem_empty z)
theorem isCold_of_isHullState_empty {ℓ : StepParameters} {r : ℕ} {V : TorusField n} (hfit : ℓ.Admissible)
    (hLn : ℓ.side ∣ n) (h : IsHullState ℓ r V ∅) : IsCold ℓ.threshold V := by
  classical
  intro x μ ν hlt
  by_contra hc
  push Not at hc
  have hl : torusLumpOf ℓ x ∈ torusHotLumps ℓ V :=
    (mem_torusHotLumps_iff ℓ hfit hLn V _).mpr ⟨x, μ, ν, hlt, hc, x, by simp [plaquetteVertices], rfl⟩
  have hz : x ∈ torusHotSites ℓ V := Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self _⟩
  rw [torusHotSites_eq_empty h] at hz
  exact absurd hz (Finset.notMem_empty x)
theorem hotCaseGround_empty {R : StepSetup} {V : TorusField n} (h : IsHullState R.params R.nextRange V ∅)
    (ω : (∅ : Finset (TorusSite n)) → CoarseLabel R.labels.Ω R.params.side) :
    hotCaseGround R V ⟨∅, ω⟩ = coldCaseGround R V := by
  have h0 := torusHotSites_eq_empty h
  unfold hotCaseGround coldCaseGround coldRegion hotCoreSites emptyCoarseState
  rw [h0, thickening_empty, thickening_empty]
  simp only [Finset.sdiff_empty, GasGround.mk.injEq, true_and]
  congr 1
  funext z
  exact absurd z.2 (Finset.notMem_empty _)
theorem noHotLumpNear_of_isHullState {ℓ : StepParameters} {r : ℕ} {V : TorusField n} {Y : Finset (TorusSite n)}
    {y : TorusSite n} {m : ℕ}
    (hY : IsHullState ℓ r V Y) (hno : ¬ ∃ h, OffsetInBox m h ∧ y + siteOfInt h ∈ Y) : NoHotLumpNear ℓ V y m := by
  classical
  intro z hz
  by_contra hc
  push Not at hc
  have hzY : z ∈ Y := hY.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz, by simp [supDist]⟩)
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist y z
  refine hno ⟨e, fun i => ?_, he ▸ hzY⟩
  have h1 := hb i
  have h2 : (e i).natAbs ≤ m := h1.trans hc
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h2
structure StepHypotheses (T : ParameterAssignment) (R : StepSetup) : Prop where
  wellPosed : R.IsWellPosed
  threshold_eq : R.params.threshold = T.threshold
  n₀_eq : R.params.n₀ = T.n₀
  rt_eq : R.params.rt = T.rt
  nextCoupling_eq : R.nextCoupling = R.shiftedCoupling T.lam
  nextCoupling_le : R.nextCoupling ≤ 1.01 * R.coupling
  coupling_le : R.coupling ≤ 1.01 * R.nextCoupling
  tail_bound : ∀ m : ℕ, (clusterRange R.coupling : ℝ) - 1 ≤ 64 * m →
    4 * Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5)) +
      3 * Real.exp (-(T.gasRate * R.coupling) - T.rt * m / 2 ^ 8) +
      2 * R.coupling * T.N 0 * Real.exp (-(T.δ₁ * m / 2)) ≤ Real.exp (-(T.rt / 2 ^ 12 * m))
  gas_form : ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    G.groundSetting.IsAdmissible ∧ 0 < G.coldWeight ∧
    G.coldWeight = ∫ η, G.groundSetting.cutoffProduct η * Real.exp (-G.groundSetting.potential η) ∧
    coarseStateWeight R G.cut G.coarse G.state =
      R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
        (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) * G.coldWeight * G.xi ∅
  log_integral : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
    Real.log (∫ η, s.cutoffProduct η * Real.exp (-s.potential η)) = ∑ Y : TorusSite n, s.blockActivity T.lam Y
  log_partition : ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    Real.log (G.xi ∅) = ∑ Y : TorusSite n, G.blockDensity Y
  partition_pos : ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → 0 < G.xi ∅
  locality : ∀ (n n' : ℕ) [NeZero n] [NeZero n'], T.n₀ ≤ n → T.n₀ ≤ n' →
    ∀ (s : ChartSetting R n) (s' : ChartSetting R n') (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ),
      s.IsAdmissible → s'.IsAdmissible →
      16 * R.frameReach ≤ m → SettingsAgreeAwayFromFrames s s' Y Y' m →
      |s.blockActivity T.lam Y - s'.blockActivity T.lam Y'| ≤ Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5))
  ground_forget : ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround R n) (G' : GasGround R n')
    (Y : TorusSite n) (Y' : TorusSite n')
    (N : ℕ), G.IsAdmissibleGround → G'.IsAdmissibleGround → 1 ≤ N → GroundsAgreeNear G G' Y Y' N →
    |G.blockDensity Y - G'.blockDensity Y'| ≤ Real.exp (-(T.gasRate * R.coupling) - T.rt * N / 2 ^ 8)
  marked : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
    ∀ Y : TorusSite n, (coldCaseGround R V).blockDensity Y = R.blockDensity n Y V
  cold_step : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
    ∀ Y : TorusSite n,
    coldLocalDensity R T.lam n Y V =
      coldInteractionDensity R T.lam n Y V + coldExpansionDensity R n Y V + coldFrameDensity R n Y V
  empty_state : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (V : TorusField n) (ω : (∅ : Finset (TorusSite n)) → CoarseLabel R.labels.Ω R.params.side),
    coarseStateWeight R ∅ V ⟨∅, ω⟩ = kernelImage R.params R.coupling R.functional n V
  hot_case : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n),
    IsHullState R.params R.nextRange V q.1 →
    (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) → (hotCaseGround R V q).IsHotCase
  zero_factor : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero
  grounds_agree : StepGas.GroundsAgreeNearOfStatesAgreeNear
  settings_agree : StepSettings.SettingsAgreeOfGroundsAgree
  shares_sum : StepCosts.SharesSumToAction
  holed_forget : HoledShares.SharesOfHoledFieldsForget
  chain_constants : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius
    T.σA T.cg T.N
  threshold_le : R.params.threshold ≤ T.σA
  threshold_le_one : R.params.threshold ≤ 1
  flat_top : BlockAverages.flatTopVanishingStatement
  cold_activity : StepGas.ColdCaseGroundActivityEq
section Step
variable {T : ParameterAssignment} {R : StepSetup} (C : StepHypotheses T R)
include C
theorem coupling_pos : 0 < R.coupling := C.wellPosed.coupling_pos
theorem n₀_le_of_isBlockTorusSide (n : ℕ) (h : IsBlockTorusSide R.params n) : T.n₀ ≤ n := by
  have h1 := h.2
  have h2 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  rw [← C.n₀_eq]
  nlinarith
theorem two_le_of_n₀_le (n : ℕ) (h : T.n₀ ≤ n) : 2 ≤ n := by
  have h1 := C.wellPosed.admissible.n₀_ge
  rw [C.n₀_eq] at h1
  omega
theorem coldCaseGround_isAdmissible {n : ℕ} [NeZero n] (hn : T.n₀ ≤ n) {V : TorusField n}
    (hV : IsCold (9 / 8 * T.threshold) V) : (coldCaseGround R V).IsAdmissibleGround :=
  Or.inl ⟨by rw [C.n₀_eq]; exact hn, by rw [C.threshold_eq]; exact hV, rfl, rfl, rfl⟩
theorem coldCaseGround_trivialField_isAdmissible {n : ℕ} [NeZero n] (hn : T.n₀ ≤ n) :
    (coldCaseGround R (trivialField n)).IsAdmissibleGround := by
  refine coldCaseGround_isAdmissible C hn (isCold_trivialField ?_)
  have := C.wellPosed.admissible.σ_pos
  rw [C.threshold_eq] at this
  positivity
theorem log_coldWeight {n : ℕ} [NeZero n] (hn : T.n₀ ≤ n) {G : GasGround R n} (hG : G.IsAdmissibleGround) :
    Real.log G.coldWeight = ∑ Y : TorusSite n, G.groundSetting.blockActivity T.lam Y := by
  obtain ⟨hs, _, he, _⟩ := C.gas_form n G hG
  rw [he]
  exact C.log_integral n hn _ hs
theorem levelShare_trivialField {n : ℕ} [NeZero n] (Y : TorusSite n) :
    levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y (trivialField n) = 0 := by
  have hF := C.flat_top (torusFrame R.params.side R.depth n) R.params.coupling
    (cellsOfSites (torusFrame R.params.side R.depth n) (Finset.univ : Finset (TorusSite n)))
    (by have := C.wellPosed.admissible.a_ge; linarith) C.wellPosed.admissible.L_odd
  exact hF.2.2 _
theorem kernelImage_trivialField {n : ℕ} [NeZero n] (hn : T.n₀ ≤ n) :
    kernelImage R.params R.coupling R.functional n (trivialField n) =
      R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
      (coldCaseGround R (trivialField n)).coldWeight * (coldCaseGround R (trivialField n)).xi ∅ := by
  classical
  obtain ⟨_, _, _, h⟩ := C.gas_form n _ (coldCaseGround_trivialField_isAdmissible C hn)
  have hc : chainComponents R.nextRange (coldCaseGround R (trivialField n)).state.1 = ∅ := by
    show chainComponents R.nextRange (∅ : Finset (TorusSite n)) = ∅
    simp [chainComponents]
  rw [hc, Finset.prod_empty, mul_one] at h
  have h0 := C.empty_state n (by rw [C.n₀_eq]; exact hn) (trivialField n) (emptyCoarseState R).2
  rw [← h0]
  exact h
theorem coarseStateWeight_hotCoreSites {n : ℕ} [NeZero n] (hside : IsBlockTorusSide R.params n)
    {V : TorusField n} {q : CoarseState R n}
    (hG : (hotCaseGround R V q).IsAdmissibleGround) :
    coarseStateWeight R (hotCoreSites R V) V q = kernelImage R.params R.coupling R.functional n (trivialField n) *
      Real.exp (-R.nextCoupling * actionAtLevel R.params.coupling R.params.side (R.depth + 1)
        (Finset.univ \ thickening LumpContours.lumpRange (torusHotSites R.params V)) V +
        ∑ y, groundDensity R (hotCaseGround R V q) T.lam y) *
      ∏ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X := by
  have hn := n₀_le_of_isBlockTorusSide C n hside
  have h₁ := coldCaseGround_trivialField_isAdmissible C hn
  obtain ⟨_, hc, _, hq⟩ := C.gas_form n _ hG
  obtain ⟨_, hc₁, _, _⟩ := C.gas_form n _ h₁
  have hA : ∑ i, levelShare R.params.coupling R.params.side (R.depth + 1) (coldRegion R.params V) i V =
      actionAtLevel R.params.coupling R.params.side (R.depth + 1)
        (Finset.univ \ thickening LumpContours.lumpRange (torusHotSites R.params V)) V :=
    C.shares_sum R.params.coupling R.params.side R.depth n _ V
      (by have := C.wellPosed.admissible.a_ge; linarith)
      (Nat.pos_of_ne_zero (NeZero.ne _)) (two_le_of_n₀_le C n hn)
  exact eq_mul_exp_of_logs hc (C.partition_pos n _ hG) hc₁ (C.partition_pos n _ h₁) hq
    (kernelImage_trivialField C hn) (log_coldWeight C hn hG)
    (C.log_partition n _ hG) (log_coldWeight C hn h₁) (C.log_partition n _ h₁) hA
theorem centered_renormalizedDensity {n : ℕ} [NeZero n] (hn : T.n₀ ≤ n) {V : TorusField n}
    (hV : IsCold (9 / 8 * T.threshold) V) (y : TorusSite n) :
    centered (R.renormalizedDensity T.lam) n y V = groundDensity R (coldCaseGround R V) T.lam y := by
  have hσp : 0 < 9 / 8 * T.threshold := by
    have := C.wellPosed.admissible.σ_pos
    rw [C.threshold_eq] at this
    positivity
  have hf : IsCold (9 / 8 * T.threshold) (trivialField n) := isCold_trivialField hσp
  have s1 := C.cold_step n hn V hV y
  have s2 := C.cold_step n hn (trivialField n) hf y
  have m1 := C.marked n hn V hV y
  have m2 := C.marked n hn (trivialField n) hf y
  have z1 := C.cold_activity R n V T.lam y C.wellPosed.admissible.L_odd (two_le_of_n₀_le C n hn)
  have z2 := C.cold_activity R n (trivialField n) T.lam y C.wellPosed.admissible.L_odd (two_le_of_n₀_le C n hn)
  have a1 := levelShare_trivialField C y
  have hc1 : coldLocalDensity R T.lam n y V = (coldChartSetting R V).blockActivity T.lam y +
      R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ y V -
      R.coldBlockConstant T.lam := dif_neg (NeZero.ne n)
  have hc2 : coldLocalDensity R T.lam n y (trivialField n) =
      (coldChartSetting R (trivialField n)).blockActivity T.lam y +
      R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ y (trivialField n) -
      R.coldBlockConstant T.lam := dif_neg (NeZero.ne n)
  have hs : ∀ W : TorusField n, levelShareFamily R.params.coupling R.params.side (R.depth + 1) n y W =
      levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ y W := fun W => dif_neg (NeZero.ne n)
  have e : R.nextCoupling = R.coupling - R.couplingShift T.lam := C.nextCoupling_eq
  show (coldInteractionDensity R T.lam n y V + coldExpansionDensity R n y V + coldFrameDensity R n y V +
      R.blockDensity n y V -
      R.couplingShift T.lam * levelShareFamily R.params.coupling R.params.side (R.depth + 1) n y V) -
    (coldInteractionDensity R T.lam n y (trivialField n) + coldExpansionDensity R n y (trivialField n) +
      coldFrameDensity R n y (trivialField n) + R.blockDensity n y (trivialField n) -
      R.couplingShift T.lam * levelShareFamily R.params.coupling R.params.side (R.depth + 1) n y (trivialField n)) =
    ((coldCaseGround R V).groundSetting.blockActivity T.lam y + (coldCaseGround R V).blockDensity y) +
      R.nextCoupling * levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ y V -
      ((coldCaseGround R (trivialField n)).groundSetting.blockActivity T.lam y +
        (coldCaseGround R (trivialField n)).blockDensity y)
  rw [hs, hs, e]
  linear_combination (hc1 - s1) - (hc2 - s2) - m1 + m2 - z1 + z2 + (R.couplingShift T.lam - R.coupling) * a1
theorem markAt_empty {n : ℕ} [NeZero n] (y : TorusSite n) :
    (emptyCoarseState R : CoarseState R n).markAt y = none := by
  classical
  unfold CoarseState.markAt
  exact dif_neg (Finset.notMem_empty y)
theorem groundsAgreeNear_trivialField {n n' m : ℕ} [NeZero n] [NeZero n'] (hs : 2 * m + 2 < n)
    (hs' : 2 * m + 2 < n') (y : TorusSite n) (y' : TorusSite n') :
    GroundsAgreeNear (coldCaseGround R (trivialField n)) (coldCaseGround R (trivialField n')) y y' m := by
  refine ⟨hs, hs', fun b _ => rfl, fun h _ => ?_, fun h _ => ?_⟩
  · show y + siteOfInt h ∈ (∅ : Finset (TorusSite n)) ↔ y' + siteOfInt h ∈ (∅ : Finset (TorusSite n'))
    simp
  · show (emptyCoarseState R : CoarseState R n).markAt _ = (emptyCoarseState R : CoarseState R n').markAt _
    rw [markAt_empty C, markAt_empty C]
theorem frame_bounds_of_range {m : ℕ} (hm : (clusterRange R.nextCoupling : ℝ) / 64 ≤ m) :
    16 * R.frameReach ≤ m ∧ 2 ^ 17 ≤ m ∧ (clusterRange R.coupling : ℝ) - 1 ≤ 64 * m := by
  have h1 : ((clusterRange R.nextCoupling : ℕ) : ℝ) ≤ ((64 * m : ℕ) : ℝ) := by
    push_cast
    linarith
  have h2 : clusterRange R.nextCoupling ≤ 64 * m := by exact_mod_cast h1
  have h3 : R.range ≤ R.nextRange + 1 := C.wellPosed.range_le
  have h4 : 2 ^ 40 * R.params.side ≤ R.range := C.wellPosed.range_ge_side
  have h5 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have h6 : R.nextRange = clusterRange R.nextCoupling := rfl
  have h7 : R.range = clusterRange R.coupling := rfl
  have h8 : 2 ^ 40 ≤ R.range := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · show 16 * (R.range / 2 ^ 11) ≤ m
    omega
  · omega
  · have h9 : ((clusterRange R.coupling : ℕ) : ℝ) ≤ ((64 * m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : clusterRange R.coupling ≤ 64 * m + 1)
    push_cast at h9
    linarith
theorem groundDensity_forget {n n' : ℕ} [NeZero n] [NeZero n'] {G : GasGround R n} {G' : GasGround R n'}
    {y : TorusSite n} {y' : TorusSite n'} {m : ℕ} (hn : T.n₀ ≤ n) (hn' : T.n₀ ≤ n')
    (hG : G.IsAdmissibleGround) (hG' : G'.IsAdmissibleGround)
    (hag : GroundsAgreeNear G G' y y' m) (hm : (clusterRange R.nextCoupling : ℝ) / 64 ≤ m)
    (ha : |levelShare R.params.coupling R.params.side (R.depth + 1) G.region y G.coarse -
        levelShare R.params.coupling R.params.side (R.depth + 1) G'.region y' G'.coarse| ≤
      R.params.threshold ^ 2 * T.N 0 * Real.exp (-T.δ₁ * ((m - 2 ^ 16 : ℕ) : ℝ))) :
    |groundDensity R G T.lam y - groundDensity R G' T.lam y'| ≤ Real.exp (-R.params.decayRate * m) := by
  obtain ⟨h16, h17, h64⟩ := frame_bounds_of_range C hm
  have hodd := C.wellPosed.admissible.L_odd
  obtain ⟨_, _, _, _, _, _, _, hNpos, _⟩ := C.chain_constants
  have hN := hNpos 0
  have hδ : 0 < T.δ₁ := by
    obtain ⟨h, _⟩ := C.chain_constants
    exact h
  have hf := coldCaseGround_trivialField_isAdmissible C hn
  have hf' := coldCaseGround_trivialField_isAdmissible C hn'
  have hfa := groundsAgreeNear_trivialField C hag.lt_extent hag.lt_extent' y y'
  have z1 := C.locality n n' hn hn' _ _ y y' m (C.gas_form n G hG).1 (C.gas_form n' G' hG').1 h16
    (C.settings_agree R n n' G G' y y' m hodd (two_le_of_n₀_le C n hn) (two_le_of_n₀_le C n' hn') hag)
  have z2 := C.locality n n' hn hn' _ _ y y' m (C.gas_form n _ hf).1 (C.gas_form n' _ hf').1 h16
    (C.settings_agree R n n' _ _ y y' m hodd (two_le_of_n₀_le C n hn) (two_le_of_n₀_le C n' hn') hfa)
  have hm1 : 1 ≤ m := by omega
  have g1 := C.ground_forget n n' G G' y y' m hG hG' hm1 hag
  have g2 := C.ground_forget n n' _ _ y y' m hf hf' hm1 hfa
  have hxpos := coupling_pos C
  have hx'pos : 0 < R.nextCoupling := by
    have h1 := C.wellPosed.coupling_pos
    have h2 := C.coupling_le
    linarith
  have hshare : |R.nextCoupling * levelShare R.params.coupling R.params.side (R.depth + 1) G.region y G.coarse -
      R.nextCoupling * levelShare R.params.coupling R.params.side (R.depth + 1) G'.region y' G'.coarse| ≤
      2 * R.coupling * T.N 0 * Real.exp (-(T.δ₁ * m / 2)) := by
    rw [← mul_sub, abs_mul, abs_of_pos hx'pos]
    have hσ1 : R.params.threshold ^ 2 ≤ 1 := by
      have h1 := C.threshold_le_one
      have h2 := C.wellPosed.admissible.σ_pos
      nlinarith
    have hcast : (((m - 2 ^ 16 : ℕ)) : ℝ) = (m : ℝ) - 2 ^ 16 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hm17 : (2 : ℝ) ^ 17 ≤ m := by exact_mod_cast h17
    have hexp : Real.exp (-T.δ₁ * ((m - 2 ^ 16 : ℕ) : ℝ)) ≤ Real.exp (-(T.δ₁ * m / 2)) := by
      apply Real.exp_le_exp.mpr
      rw [hcast]
      nlinarith
    have hepos := Real.exp_pos (-(T.δ₁ * m / 2))
    have hb : R.params.threshold ^ 2 * T.N 0 * Real.exp (-T.δ₁ * ((m - 2 ^ 16 : ℕ) : ℝ)) ≤
        T.N 0 * Real.exp (-(T.δ₁ * m / 2)) := by
      have e1 : R.params.threshold ^ 2 * T.N 0 ≤ T.N 0 := by nlinarith
      exact mul_le_mul e1 hexp (Real.exp_pos _).le hN.le
    have h2x : R.nextCoupling ≤ 2 * R.coupling := by
      have := C.nextCoupling_le
      linarith
    calc R.nextCoupling * |levelShare R.params.coupling R.params.side (R.depth + 1) G.region y G.coarse -
          levelShare R.params.coupling R.params.side (R.depth + 1) G'.region y' G'.coarse|
        ≤ R.nextCoupling * (T.N 0 * Real.exp (-(T.δ₁ * m / 2))) :=
          mul_le_mul_of_nonneg_left (ha.trans hb) hx'pos.le
      _ ≤ 2 * R.coupling * (T.N 0 * Real.exp (-(T.δ₁ * m / 2))) :=
          mul_le_mul_of_nonneg_right h2x (by positivity)
      _ = 2 * R.coupling * T.N 0 * Real.exp (-(T.δ₁ * m / 2)) := by ring
  have hE := C.tail_bound m h64
  have hfin : Real.exp (-(T.rt / 2 ^ 12 * m)) = Real.exp (-R.params.decayRate * m) := by
    unfold StepParameters.decayRate
    rw [C.rt_eq]
    congr 1
    ring
  rw [← hfin]
  exact abs_sub_le_of_parts z1 z2 g1 g2 hshare (Real.exp_pos _).le (Real.exp_pos _).le (by positivity) hE
theorem isCold_of_threshold {n : ℕ} {V : TorusField n} (hV : IsCold R.params.threshold V) :
    IsCold (9 / 8 * T.threshold) V := by
  intro x μ ν hlt
  have h1 := hV x μ ν hlt
  have h2 := C.wellPosed.admissible.σ_pos
  rw [C.threshold_eq] at h1 h2
  linarith
theorem hullExpansionDisplay (h : ClusterExpansionOfAStep.CoarseLabelFacts R) :
    HullExpansionDisplay R.params (R.depth + 1) R.nextCoupling (kernelImage R.params R.coupling R.functional)
      (R.renormalizedDensity T.lam) (ClusterExpansionOfAStep.coarseLabelSpace R h)
      (coarseWeightExpansion R) (coarseFactorExpansion R) (R.stateDensity T.lam) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n _ hside V Y ω hq
    have e1 : coarseWeightExpansion R n V Y ω = coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ :=
      dif_neg (NeZero.ne n)
    have e2 : ∀ X, coarseFactorExpansion R n V Y ω X = coarseFactor V ⟨Y, ω⟩ X := fun X => dif_neg (NeZero.ne n)
    have e3 : ∀ y, R.stateDensity T.lam n y V Y ω = groundDensity R (hotCaseGround R V ⟨Y, ω⟩) T.lam y :=
      fun y => dif_neg (NeZero.ne n)
    rw [e1]
    simp only [e2, e3]
    by_cases hz : ∃ X ∈ chainComponents R.nextRange Y, coarseFactor V ⟨Y, ω⟩ X = 0
    · rw [C.zero_factor R C.wellPosed n hside V ⟨Y, ω⟩ hq hz]
      obtain ⟨X, hX, h0⟩ := hz
      have hP : ∏ X ∈ chainComponents (clusterRange R.nextCoupling) Y, coarseFactor V ⟨Y, ω⟩ X = 0 :=
        Finset.prod_eq_zero hX h0
      rw [hP, mul_zero]
    · push Not at hz
      exact coarseStateWeight_hotCoreSites C hside (Or.inr (C.hot_case n hside V ⟨Y, ω⟩ hq hz))
  · intro n _ hside V ω y hq
    have e3 : R.stateDensity T.lam n y V ∅ ω = groundDensity R (hotCaseGround R V ⟨∅, ω⟩) T.lam y :=
      dif_neg (NeZero.ne n)
    rw [e3, hotCaseGround_empty hq ω]
    exact (centered_renormalizedDensity C (n₀_le_of_isBlockTorusSide C n hside)
      (isCold_of_threshold C (isCold_of_isHullState_empty C.wellPosed.admissible hside.1 hq)) y).symm
  · intro n n' _ _ hs hs' W W' Y Y' ω ω' y y' m hq hq' hΦ hΦ' hm hag
    have e3 : R.stateDensity T.lam n y W Y ω = groundDensity R (hotCaseGround R W ⟨Y, ω⟩) T.lam y :=
      dif_neg (NeZero.ne n)
    have e4 : R.stateDensity T.lam n' y' W' Y' ω' = groundDensity R (hotCaseGround R W' ⟨Y', ω'⟩) T.lam y' :=
      dif_neg (NeZero.ne n')
    have e2 : ∀ X ∈ chainComponents R.nextRange Y, coarseFactor W ⟨Y, ω⟩ X ≠ 0 := fun X hX => by
      have := hΦ X hX
      rwa [show coarseFactorExpansion R n W Y ω X = coarseFactor W ⟨Y, ω⟩ X from dif_neg (NeZero.ne n)] at this
    have e2' : ∀ X ∈ chainComponents R.nextRange Y', coarseFactor W' ⟨Y', ω'⟩ X ≠ 0 := fun X hX => by
      have := hΦ' X hX
      rwa [show coarseFactorExpansion R n' W' Y' ω' X = coarseFactor W' ⟨Y', ω'⟩ X from dif_neg (NeZero.ne n')] at this
    rw [e3, e4]
    obtain ⟨_, h17, _⟩ := frame_bounds_of_range C hm
    have hGr := (C.grounds_agree R n n' W W' Y ω y y' m C.wellPosed.admissible C.wellPosed.nextRange_ge hs.1 hq
      e2).1 Y' ω' hs'.1 hq' e2' hag
    refine groundDensity_forget C (n₀_le_of_isBlockTorusSide C n hs) (n₀_le_of_isBlockTorusSide C n' hs')
      (Or.inr (C.hot_case n hs W ⟨Y, ω⟩ hq e2))
      (Or.inr (C.hot_case n' hs' W' ⟨Y', ω'⟩ hq' e2')) hGr hm ?_
    have hb : SameBlockPosition R.params y y' ∨ (NoHotLumpNear R.params W y m ∧ NoHotLumpNear R.params W' y' m) := by
      by_cases hex : ∃ h, OffsetInBox m h ∧ y + siteOfInt h ∈ Y
      · exact Or.inl (hag.2.2.2.2.2 hex)
      · refine Or.inr ⟨noHotLumpNear_of_isHullState hq hex, noHotLumpNear_of_isHullState hq' ?_⟩
        rintro ⟨h, hh, hy⟩
        exact hex ⟨h, hh, (hag.2.2.2.1 h hh).mpr hy⟩
    exact (C.holed_forget T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N R.params C.chain_constants
      C.wellPosed.admissible C.threshold_le R.depth n n' W W' y y' m hs.1
      (by omega) hag.1 hag.2.1 hag.2.2.1).1 hs'.1 hb
  · intro n n' _ _ hs hn' W W' Y ω ω' y y' m hq hcold hΦ hm hag
    have e3 : R.stateDensity T.lam n y W Y ω = groundDensity R (hotCaseGround R W ⟨Y, ω⟩) T.lam y :=
      dif_neg (NeZero.ne n)
    have e2 : ∀ X ∈ chainComponents R.nextRange Y, coarseFactor W ⟨Y, ω⟩ X ≠ 0 := fun X hX => by
      have := hΦ X hX
      rwa [show coarseFactorExpansion R n W Y ω X = coarseFactor W ⟨Y, ω⟩ X from dif_neg (NeZero.ne n)] at this
    have hn'' : T.n₀ ≤ n' := by rw [← C.n₀_eq]; exact hn'
    have hW9 := isCold_of_threshold C hcold
    rw [e3, centered_renormalizedDensity C hn'' hW9 y']
    obtain ⟨_, h17, _⟩ := frame_bounds_of_range C hm
    have hGr := (C.grounds_agree R n n' W W' Y ω y y' m C.wellPosed.admissible C.wellPosed.nextRange_ge hs.1 hq
      e2).2 ω' hag
    refine groundDensity_forget C (n₀_le_of_isBlockTorusSide C n hs) hn''
      (Or.inr (C.hot_case n hs W ⟨Y, ω⟩ hq e2)) (coldCaseGround_isAdmissible C hn'' hW9) hGr hm ?_
    have hno : NoHotLumpNear R.params W y m := noHotLumpNear_of_isHullState hq (by
      rintro ⟨h, hh, hy⟩
      exact absurd ((hag.2.2.2.1 h hh).mp hy) (Finset.notMem_empty _))
    exact (C.holed_forget T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N R.params C.chain_constants
      C.wellPosed.admissible C.threshold_le R.depth n n' W W' y y' m hs.1
      (by omega) hag.1 hag.2.1 hag.2.2.1).2 hcold hno
end Step
theorem imageHasHullExpansion_holds (hGas : StepSettings.coarseStateGasStatement)
    (hSum : ClusterExpansionOfAStep.LogIntegralEqSumActivity)
    (hGs : StepGas.LogPartitionEqSumDensities) (hFg : ClusterExpansionOfAStep.GasDensityForgets)
    (hMk : StepGas.MarkedIntegralEqPartitionOfCouplingLe) (hLoc : StepLocality.DensityLocality)
    (hCol : ClusterExpansionOfAStep.GasColumnsSmall) (hRat : ClusterExpansionOfAStep.PartitionRatioBounds)
    (hCI : StepSettings.ColdImageFactorsThroughColdStep)
    (hSC : StepSettings.coldFieldStateStatement) (hHG : StepGas.HullStateIsHotCase)
    (hZ : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero) (hGr : StepGas.GroundsAgreeNearOfStatesAgreeNear)
    (hSg : StepSettings.SettingsAgreeOfGroundsAgree) (hSh : StepCosts.SharesSumToAction)
    (hHo : HoledShares.SharesOfHoledFieldsForget) (hFlat : BlockAverages.flatTopVanishingStatement)
    (hCG : StepGas.ColdCaseGroundActivityEq) (hFl : StepFloors.EventuallyFloorConditions) :
    ImageHasHullExpansion := by
  obtain ⟨r1, p1, f1⟩ := hGas
  obtain ⟨r2, p2, f2⟩ := hSum
  obtain ⟨r3, p3, f3⟩ := hGs
  obtain ⟨r4, p4, f4⟩ := hFg
  obtain ⟨r5, p5, f5⟩ := hMk
  obtain ⟨r6, p6, f6⟩ := hLoc
  obtain ⟨r7, p7, f7⟩ := hCol
  refine ⟨fun c => min (r1 c) (min (r2 c) (min (r3 c) (min (r4 c) (min (r5 c) (min (r6 c) (r7 c)))))),
    fun c => lt_min (p1 c) (lt_min (p2 c) (lt_min (p3 c) (lt_min (p4 c) (lt_min (p5 c) (lt_min (p6 c) (p7 c)))))), ?_⟩
  intro T hD hCS hrt
  simp only [le_min_iff] at hrt
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := hrt
  obtain ⟨y1, g1⟩ := f1 T hD t1
  obtain ⟨y2, g2⟩ := f2 T hD t2
  obtain ⟨y3, g3⟩ := f3 T hD t3
  obtain ⟨y4, g4⟩ := f4 T hD t4
  obtain ⟨y5, g5⟩ := f5 T hD t5
  obtain ⟨y6, g6⟩ := f6 T hD t6
  obtain ⟨y7, g7⟩ := f7 T hD t7
  obtain ⟨y8, g8⟩ := hCI T hD hCS
  obtain ⟨y9, g9⟩ := hHG T hD
  obtain ⟨y10, g10⟩ := hFl T hD 1 1 one_pos one_pos
  refine ⟨max y1 (max y2 (max y3 (max y4 (max y5 (max y6 (max y7 (max y8 (max y9 y10)))))))),
    fun y hy R hR hF hnext hnear h => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10⟩ := hy
  have fl := g10 R.coupling (u10.trans hR.le_coupling)
  have hB : R.params.B = T.B := by rw [hR.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have ha : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  obtain ⟨b1, b2, _, _⟩ := fl.stable_nearby.2 R.nextCoupling (by rw [← hB]; exact hnear)
  have ctx : StepHypotheses T R :=
    { wellPosed := hF
      threshold_eq := hσ
      n₀_eq := by rw [hR.params_eq]; rfl
      rt_eq := by rw [hR.params_eq]; rfl
      nextCoupling_eq := hnext
      nextCoupling_le := b2
      coupling_le := b1
      tail_bound := fl.chain_tail
      gas_form := fun n _ G hG => by
        obtain ⟨a1, a2, a3, _, a4⟩ := g1 y u1 R hR b2 n G hG
        exact ⟨a1, a2, a3, a4⟩
      log_integral := fun n _ hn s hs => g2 y u2 R hR n hn s hs
      log_partition := fun n _ G hG => (g3 y u3 R hR b2 n G hG).1
      partition_pos := fun n _ G hG => (hRat R n G T.gasRate (g7 y u7 R hR b2 n G hG)).2.1 ∅
      locality := fun n n' _ _ hn hn' s s' Y Y' m hs hs' h16 hoff => by
        have := (g6 y u6 R hR n n' hn hn' s s' Y Y' m hs hs').2 h16 hoff
        exact this.1.trans this.2
      ground_forget := fun n n' _ _ G G' Y Y' N hG hG' hN hag =>
        g4 y u4 R hR b2 n n' G G' Y Y' N hG hG' hN hag
      marked := fun n _ hn V hV Y => (g5 y u5 R hR hF.functional_spec b2 n hn V hV).2 Y
      cold_step := fun n _ hn V hV Y => (g8 y u8 R hR n hn V hV).2 Y
      empty_state := fun n _ hn V ω => (hSC R hF n hn).1 V ω
      hot_case := g9 y u9 R hR hF
      zero_factor := hZ
      grounds_agree := hGr
      settings_agree := hSg
      shares_sum := hSh
      holed_forget := hHo
      chain_constants := by
        rw [ha, hL, hR.anchorRadius_eq]
        exact hD.chain
      threshold_le := by
        rw [hσ]
        have h1 := hD.σ_le
        have h2 := hD.σ_pos
        linarith
      threshold_le_one := by
        rw [hσ]
        exact hD.σ_one
      flat_top := hFlat
      cold_activity := hCG }
  exact hullExpansionDisplay ctx h
end ImageDensities
end YangMills.Construction
end
