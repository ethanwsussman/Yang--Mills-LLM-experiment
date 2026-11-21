import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASetting
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.TheHotHalf
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.ValueOfTheFlowAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open TorusFields TorusLumps StepSettings StepCosts ShareFamilies WeightedResponses RenormalizationStepParameters ClusterExpansionOfAStep
private theorem trivialField_isCold {m : ℕ} {s : ℝ} (hs : 0 < s) : IsCold s (trivialField m) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private theorem translate_trivialField {m : ℕ} (v : TorusSite m) :
    TorusFields.translate v (trivialField m) = trivialField m := rfl
private theorem blockActivityAtTrivial_eq {S : StepSetup} {lam : ℝ} {m : ℕ} [NeZero m] (B : TorusSite m)
    (hDecomp : coldLocalDensity S lam m B (trivialField m) = coldInteractionDensity S lam m B (trivialField m) +
      coldExpansionDensity S m B (trivialField m) + coldFrameDensity S m B (trivialField m)) :
    blockActivityAtTrivial lam S m B = S.renormalizedDensity lam m B (trivialField m) +
      (S.couplingShift lam - S.coupling) * levelShareFamily S.params.coupling S.params.side (S.depth + 1) m B (trivialField m) +
        S.coldBlockConstant lam := by
  have hLocal : coldLocalDensity S lam m B (trivialField m) = (coldChartSetting S (trivialField m)).blockActivity lam B +
      S.coupling * levelShare S.params.coupling S.params.side (S.depth + 1) Finset.univ B (trivialField m) -
        S.coldBlockConstant lam := by
    simp [coldLocalDensity, NeZero.ne m]
  have hBlock : S.blockDensity m B (trivialField m) = S.blockDensityAt B (trivialField m) := by
    simp [StepSetup.blockDensity, NeZero.ne m]
  have hShare : levelShareFamily S.params.coupling S.params.side (S.depth + 1) m B (trivialField m) =
      levelShare S.params.coupling S.params.side (S.depth + 1) Finset.univ B (trivialField m) := by
    simp [levelShareFamily, NeZero.ne m]
  have hRenorm : S.renormalizedDensity lam m B (trivialField m) = coldInteractionDensity S lam m B (trivialField m) +
      coldExpansionDensity S m B (trivialField m) + coldFrameDensity S m B (trivialField m) +
      S.blockDensity m B (trivialField m) -
        S.couplingShift lam * levelShareFamily S.params.coupling S.params.side (S.depth + 1) m B (trivialField m) := rfl
  unfold blockActivityAtTrivial
  rw [hRenorm, hShare, hBlock, ← hDecomp, hLocal]
  ring
theorem logFlowAtTrivialEqSum_holds (hFlow : FreeEnergies.expansionAlongFlow)
    (hHot : ClusterExpansionOfAStep.HotFactorization) (hSum : ClusterExpansionOfAStep.LogIntegralEqSumActivity)
    (hChart : StepSettings.ColdChartSettingIsAdmissible) (hImage : ImageColdExpansion.ImageHasColdExpansion)
    (hFactor : StepSettings.ColdImageFactorsThroughColdStep)
    (hShares : ShareFamilies.LevelSharesFormCurvatureFamily) :
    FreeEnergies.logFlowAtTrivialEqSum := by
  obtain ⟨r₁, hr₁, h₁⟩ := hHot
  obtain ⟨r₂, hr₂, h₂⟩ := hSum
  obtain ⟨r₃, hr₃, h₃⟩ := hImage
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)),
    fun T hT hCold hrt => ?_⟩
  obtain ⟨y₁, k₁⟩ := h₁ T hT (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, k₂⟩ := h₂ T hT (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₃, k₃⟩ := h₃ T hT hCold (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨y₄, k₄⟩ := hChart T hT
  obtain ⟨y₅, k₅⟩ := hFactor T hT hCold
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max y₅ T.floorMin), fun y hy hSt => ?_⟩
  have e₁ : y₁ ≤ y := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hy
  have e₂ : y₂ ≤ y := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hy
  have e₃ : y₃ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hy
  have e₄ : y₄ ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hy
  have e₅ : y₅ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have e₆ : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hσ0 := hT.σ_pos
  intro β t hr R hR n _ hn
  have hstep : ∀ u < t, ∀ (m : ℕ) [NeZero m], T.n₀ ≤ m →
      (∀ B B' : TorusSite m, blockActivityAtTrivial T.lam (R u) m B = blockActivityAtTrivial T.lam (R u) m B') ∧
      Real.log (flowFunctionalAtTrivial (T.stepParameters y) β (u + 1) m) =
        Real.log (flowFunctionalAtTrivial (T.stepParameters y) β u (m * T.side)) +
          (m : ℝ) ^ 4 * blockActivityAtTrivial T.lam (R u) m 0 := by
    intro u hu m _ hm
    obtain ⟨hOn, hlev, hcoup, hnext, hweight⟩ := hR u hu
    have hParams : (R u).params = T.stepParameters y := hOn.params_eq
    have hSymm : (R u).IsSymmetricWeight := by
      have hexp := (hFlow _ hSt β u (fun j hj => hr j (by omega))).1.1
      unfold StepSetup.IsSymmetricWeight
      rw [hParams, hweight]
      exact hexp
    have hSide : (R u).params.side = T.side := by rw [hParams]; rfl
    have hThreshold : (R u).params.threshold = T.threshold := by rw [hParams]; rfl
    have hMinSide : (R u).params.n₀ = T.n₀ := by rw [hParams]; rfl
    have hCoupling : (R u).params.coupling = T.coupling := by rw [hParams]; rfl
    have hColdWide : IsCold (9 / 8 * T.threshold) (trivialField m) := trivialField_isCold (by positivity)
    have hColdBase : IsCold T.threshold (trivialField m) := trivialField_isCold hσ0
    have hexpansion := (k₃ y e₃ (R u) hOn hSymm).1
    have hfamily := (hShares T hT y e₆ (R u).depth).1
    have hsame : ∀ B B' : TorusSite m,
        blockActivityAtTrivial T.lam (R u) m B = blockActivityAtTrivial T.lam (R u) m B' := by
      intro B B'
      have hDecomp : ∀ Z : TorusSite m, coldLocalDensity (R u) T.lam m Z (trivialField m) =
          coldInteractionDensity (R u) T.lam m Z (trivialField m) +
          coldExpansionDensity (R u) m Z (trivialField m) + coldFrameDensity (R u) m Z (trivialField m) := fun Z =>
        (k₅ y e₅ (R u) hOn m hm (trivialField m) hColdWide).2 Z
      rw [blockActivityAtTrivial_eq B (hDecomp B), blockActivityAtTrivial_eq B' (hDecomp B')]
      have htr := hexpansion.translation m (by rw [hMinSide]; exact hm) B (B' - B) (trivialField m)
        (by rw [hThreshold]; exact hColdBase)
      have hsh := hfamily.translation m hm B (B' - B) (trivialField m) hColdBase
      rw [translate_trivialField, add_sub_cancel] at htr hsh
      have hfam : levelShareFamily (R u).params.coupling (R u).params.side ((R u).depth + 1) =
          levelShareFamily T.coupling T.side ((R u).depth + 1) := by
        rw [hCoupling, hSide]
      rw [htr, hfam, hsh]
    refine ⟨hsame, ?_⟩
    obtain ⟨-, hdisplay⟩ := k₁ y e₁ (R u) hOn hSymm
    obtain ⟨hpos, hint, hlog⟩ := hdisplay m hm (trivialField m) hColdBase
    have hsumz := k₂ y e₂ (R u) hOn m hm (coldChartSetting (R u) (trivialField m))
      (k₄ y e₄ (R u) hOn m hm (trivialField m) hColdWide)
    have hval : ∀ K : ℕ, (R u).functional K (trivialField K) = flowFunctionalAtTrivial (T.stepParameters y) β u K := by
      intro K
      rw [hweight]
      rfl
    have himg : kernelImage (R u).params (R u).coupling (R u).functional m (trivialField m) =
        flowFunctionalAtTrivial (T.stepParameters y) β (u + 1) m := by
      rw [hParams, hcoup, hweight]
      rfl
    have hcold : coldImageIntegral (R u) (trivialField m) =
        (R u).functional (m * (R u).params.side) (trivialField _) *
          ∫ η, (coldChartSetting (R u) (trivialField m)).cutoffProduct η *
            Real.exp (-(coldChartSetting (R u) (trivialField m)).potential η) := rfl
    rw [hcold] at hpos hlog
    have hne1 := left_ne_zero_of_mul hpos.ne'
    have hne2 := right_ne_zero_of_mul hpos.ne'
    rw [Real.log_mul hne1 hne2, hsumz, himg, hval, hSide] at hlog
    have hsumBlock : ∑ B : TorusSite m, (R u).blockDensity m B (trivialField m) =
        ∑ B : TorusSite m, (R u).blockDensityAt B (trivialField m) :=
      Finset.sum_congr rfl fun B _ => by simp [StepSetup.blockDensity, NeZero.ne m]
    rw [hsumBlock] at hlog
    have hcard : (Fintype.card (TorusSite m) : ℝ) = (m : ℝ) ^ 4 := by
      simp [TorusSite, ZMod.card]
    have hall : ∑ B : TorusSite m, blockActivityAtTrivial T.lam (R u) m B =
        (m : ℝ) ^ 4 * blockActivityAtTrivial T.lam (R u) m 0 := by
      rw [Finset.sum_congr rfl fun B _ => hsame B 0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    rw [← hall]
    unfold blockActivityAtTrivial
    rw [Finset.sum_add_distrib]
    linarith
  have hbase : ∀ (m : ℕ) [NeZero m], Real.log (flowFunctionalAtTrivial (T.stepParameters y) β 0 m) = 0 := by
    intro m _
    have : flowFunctionalAtTrivial (T.stepParameters y) β 0 m = 1 := by
      show wilsonWeight β m (trivialField m) = 1
      simp [wilsonWeight, NeZero.ne m, wilsonAction_trivialField]
    rw [this, Real.log_one]
  have hL1 : 1 ≤ T.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hlevels : ∀ t' : ℕ, t' ≤ t → ∀ (m : ℕ) [NeZero m], T.n₀ ≤ m →
      Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t' m) =
        ∑ u ∈ Finset.range t', (T.side : ℝ) ^ (4 * (t' - 1 - u)) * (m : ℝ) ^ 4 *
          blockActivityAtTrivial T.lam (R u) (fineSide T.side (t' - 1 - u) m) 0 := by
    intro t'
    induction t' with
    | zero =>
      intro _ m _ _
      simpa using hbase m
    | succ t' ih =>
      intro ht m _ hm
      have hmL : T.n₀ ≤ m * T.side := by nlinarith
      rw [(hstep t' ht m hm).2, ih (by omega) (m * T.side) hmL, Finset.sum_range_succ]
      have hlast : t' + 1 - 1 - t' = 0 := by omega
      have hB : ∀ {k k' : ℕ}, k = k' → ∀ (M : ℕ) [NeZero M] (u : ℕ),
          blockActivityAtTrivial T.lam (R u) (fineSide T.side k M) 0 =
            blockActivityAtTrivial T.lam (R u) (fineSide T.side k' M) 0 := by
        rintro k _ rfl M _ u
        rfl
      have hmid : ∑ u ∈ Finset.range t', (T.side : ℝ) ^ (4 * (t' - 1 - u)) * ((m * T.side : ℕ) : ℝ) ^ 4 *
            blockActivityAtTrivial T.lam (R u) (fineSide T.side (t' - 1 - u) (m * T.side)) 0 =
          ∑ u ∈ Finset.range t', (T.side : ℝ) ^ (4 * (t' + 1 - 1 - u)) * (m : ℝ) ^ 4 *
            blockActivityAtTrivial T.lam (R u) (fineSide T.side (t' + 1 - 1 - u) m) 0 := by
        refine Finset.sum_congr rfl fun u hu => ?_
        have hu' : u < t' := Finset.mem_range.mp hu
        have hk : t' + 1 - 1 - u = (t' - 1 - u) + 1 := by omega
        have eB : blockActivityAtTrivial T.lam (R u) (fineSide T.side (t' + 1 - 1 - u) m) 0 =
            blockActivityAtTrivial T.lam (R u) (fineSide T.side (t' - 1 - u) (m * T.side)) 0 := hB hk m u
        rw [eB, hk]
        push_cast
        ring
      rw [hmid, hB hlast m t']
      have e0 : blockActivityAtTrivial T.lam (R t') (fineSide T.side 0 m) 0 =
          blockActivityAtTrivial T.lam (R t') m 0 := rfl
      rw [e0, hlast]
      simp only [mul_zero, pow_zero, one_mul]
  have hn₀ : T.n₀ ≤ n := by
    have h1 : T.side * T.n₀ ≤ n := hn.2
    nlinarith
  refine ⟨fun u hu B B' => ?_, hlevels t le_rfl n hn₀⟩
  have hLk : 1 ≤ T.side ^ (t - 1 - u) := Nat.one_le_pow _ _ (by omega)
  have hS : T.n₀ ≤ fineSide T.side (t - 1 - u) n := by
    rw [fineSide_eq]
    nlinarith
  exact (hstep u hu _ hS).1 B B'
end YangMills.Construction.FreeEnergies
end
