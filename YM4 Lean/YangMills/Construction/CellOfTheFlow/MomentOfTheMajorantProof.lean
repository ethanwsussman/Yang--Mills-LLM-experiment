import YangMills.Construction.CellOfTheFlow.MomentOfTheMajorant
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyFromBelow
import YangMills.Construction.FreeEnergiesOfTheFlow.MassOfTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.LawOnABoxOfTheFlow.DensityOfTheStateAlongTheFlow
import YangMills.Construction.ResponseInTheExpansion.ScoredMassOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.FreeEnergies
private theorem le_clusterRange_of_pow_le {k : ℕ} {y : ℝ} (hy : (k : ℝ) ^ 100 ≤ y) : k ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem sum_siteScore_eq {n : ℕ} {Ω : Type} (s : Ω → ℝ) (Y : Finset (TorusSite n)) (ω : Y → Ω) :
    ∑ z ∈ Y, siteScore s Y ω z = ∑ y : Y, s (ω y) := by
  classical
  calc ∑ z ∈ Y, siteScore s Y ω z = ∑ y : Y, siteScore s Y ω y := (Finset.sum_coe_sort Y _).symm
    _ = ∑ y : Y, s (ω y) := Finset.sum_congr rfl fun y _ => by simp [siteScore]
private theorem measurable_sigma_of_forall {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun x : β a => f ⟨a, x⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
private theorem stage_functional_eq {Tb : ParameterAssignment} {y β : ℝ} {T : StageTower (Tb.stepParameters y)} {k : ℕ}
    (hT : IsTowerAtParameters Tb y T β k) : ∀ u ≤ k, (T.stage u).functional = flowFunctional (Tb.stepParameters y) β u
  | 0, _ => hT.startsAtWilson.functional_eq
  | u + 1, h => by
    show kernelImage _ (T.stage u).coupling (T.stage u).functional =
      kernelImage _ (couplingFlow (Tb.stepParameters y) β u).1 (couplingFlow (Tb.stepParameters y) β u).2
    rw [hT.coupling_eq u (by omega), stage_functional_eq hT u (by omega)]
    rfl
private theorem mul_exp_le_of_log_le {D Z C l E Cf N : ℝ} {M : ℕ} (hM : (M : ℝ) = N) (hN : 0 ≤ N) (hZ : 0 < Z)
    (hb : Real.log D - (C + 6 * l) * N ≤ Real.log Z) (hl : 0 ≤ l) (hE : 0 ≤ E)
    (hCf : Cf = |C| + Real.log 2 + 2 * E + 6) :
    D * 2 ^ M * Real.exp (2 * E * M) ≤ Z * Real.exp (Cf * (1 + l) * N) := by
  rcases le_or_gt D 0 with hD | hD
  · have hnp : D * 2 ^ M * Real.exp (2 * E * M) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hD (by positivity)) (Real.exp_nonneg _)
    exact hnp.trans (by positivity)
  have hpow : (2 : ℝ) ^ M = Real.exp (M * Real.log 2) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log two_pos, Real.rpow_natCast]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hDZ : D ≤ Z * Real.exp ((C + 6 * l) * N) := by
    have hlog : Real.log D ≤ Real.log Z + (C + 6 * l) * N := by linarith
    have hexpl := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hD, Real.exp_add, Real.exp_log hZ] at hexpl
  have hexp : (C + 6 * l) * N + N * Real.log 2 + 2 * E * N ≤ Cf * (1 + l) * N := by
    have hCf6 : 6 ≤ Cf := by
      have := abs_nonneg C
      rw [hCf]
      linarith
    have hcoef : C + 6 * l + Real.log 2 + 2 * E ≤ Cf * (1 + l) := by
      have hsix : 6 * l ≤ Cf * l := mul_le_mul_of_nonneg_right hCf6 hl
      have habs := le_abs_self C
      have hsplit : Cf * (1 + l) = Cf + Cf * l := by ring
      rw [hsplit, hCf] at *
      linarith
    have := mul_le_mul_of_nonneg_right hcoef hN
    linarith
  calc D * 2 ^ M * Real.exp (2 * E * M)
      ≤ Z * Real.exp ((C + 6 * l) * N) * 2 ^ M * Real.exp (2 * E * M) := by gcongr
    _ = Z * Real.exp ((C + 6 * l) * N + N * Real.log 2 + 2 * E * N) := by
        rw [hpow, hM, Real.exp_add, Real.exp_add]
        ring
    _ ≤ Z * Real.exp (Cf * (1 + l) * N) := by gcongr
abbrev _root_.YangMills.SharedProofs.p49832 := @mul_exp_le_of_log_le
private theorem isBlockTorusSide_two_mul_pow {ℓ : StepParameters} {e : ℕ} (hn : 1 ≤ ℓ.n₀)
    (h : ℓ.side * ℓ.n₀ ≤ 2 * ℓ.side ^ e) (hodd : 3 ≤ ℓ.side) : IsBlockTorusSide ℓ (2 * ℓ.side ^ e) := by
  refine ⟨?_, h⟩
  rcases e with _ | e
  · exfalso
    have : ℓ.side * 1 ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_left _ hn
    simp only [pow_zero] at h
    omega
  · exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.succ_ne_zero _)) _
theorem majorantExpMomentStatement_holds (hD : YangMills.Construction.StageDensity.stageStateDensityStatement)
    (hS : ScoredMassStatement) (hB : freeEnergyLowerBound) (hM : flowFunctionalIntegral) :
    majorantExpMomentStatement := by
  intro a ha
  obtain ⟨L₁, rtD, hrtD, hD'⟩ := hD a ha
  obtain ⟨rtB, hrtB, hB'⟩ := hB
  refine ⟨L₁, fun c => min (rtD c) (rtB c), 0, fun c => lt_min (hrtD c) (hrtB c), ?_⟩
  intro L hL hLL Tb hTa hTL hAdm hCold _ hrt _ C' s₁ _ _
  obtain ⟨yD, hyD⟩ := hD' L hL hLL Tb hTa hTL hAdm (hrt.trans (min_le_left _ _))
  obtain ⟨yB, hyB⟩ := hB' Tb hAdm hCold (hrt.trans (min_le_right _ _))
  refine ⟨max (max yD yB) (max Tb.floorMin (((4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100)), ?_⟩
  intro y hy hret hwil
  have hyD' : yD ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyB' : yB ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hyT : Tb.floorMin ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyk : ((4 * Tb.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hfit : (Tb.stepParameters y).Admissible := hAdm.fits y hyT
  obtain ⟨C, hC⟩ := hyB y hyB' ⟨hret, hwil⟩
  have hDens := hyD y hyD' hret hwil
  have hE1 : 1 ≤ (Tb.stepParameters y).E := hfit.E_ge
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hCf : 0 ≤ |C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6 := by
    have := abs_nonneg C
    linarith
  refine ⟨|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6, |C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6, ?_⟩
  intro T β s₀ k hOn _ _ hcarry e he
  have hstands := hOn.onFamily
  have hstep := hstands.onFamily k le_rfl
  obtain ⟨⟨hc, hh⟩, -, -⟩ := hstep.isStep
  have hxy : y ≤ (T.stage k).coupling := hstep.le_coupling
  have hy1 : (1 : ℝ) ≤ y := hfit.y₁_ge
  have hx0 : 0 < (T.stage k).coupling := by linarith
  have hfl : 4 * (Tb.stepParameters y).n₀ + 2 ^ 16 ≤ clusterRange (T.stage k).coupling :=
    le_clusterRange_of_pow_le (hyk.trans hxy)
  have hweight := hcarry k le_rfl
  have hxk : (T.stage k).coupling = flowCoupling (Tb.stepParameters y) β k := hstands.coupling_eq k (Nat.le_succ k)
  have hReach : CouplingsAboveFloor (Tb.stepParameters y) β k := fun j hj => by
    have hj1 : (T.stage j).coupling = flowCoupling (Tb.stepParameters y) β j := hstands.coupling_eq j (by omega)
    have hj2 : y ≤ (T.stage j).coupling := (hstands.onFamily j hj).le_coupling
    rw [← hj1]
    exact hj2
  have harr : (T.stage k).functional = flowFunctional (Tb.stepParameters y) β k := stage_functional_eq hstands k le_rfl
  have hn : IsBlockTorusSide (Tb.stepParameters y) (2 * (Tb.stepParameters y).side ^ e) := by
    have htwo : 2 ≤ (Tb.stepParameters y).side := T.two_le_side
    have hodd : Odd (Tb.stepParameters y).side := by
      show Odd Tb.side
      rw [hTL]
      exact hL
    have hthree : 3 ≤ (Tb.stepParameters y).side := by
      rcases hodd with ⟨m, hm⟩
      omega
    have hone : 1 ≤ (Tb.stepParameters y).n₀ := by
      have := hfit.n₀_ge
      omega
    exact isBlockTorusSide_two_mul_pow hone he hthree
  have key : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
      ∫⁻ u, ENNReal.ofReal (Real.exp (hullMajorantSum T s₀ s₁ k n u)) ∂(markedSampleLaw T β k n) ≤
        ENNReal.ofReal (Real.exp ((|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
          (1 + Real.log (flowCoupling (Tb.stepParameters y) β k)) * (n : ℝ) ^ 4)) := by
    intro n _ hn
    have hup := hS (Tb.stepParameters y) (T.stage k).depth (T.stage k).coupling (T.stage k).functional
      (T.stage k).density (T.stage k).labels (T.stage k).labelWeight (T.stage k).clusterFactor
      (T.stage k).siteDensity (labelMajorant T s₀ s₁ k) hfit hfit.E_ge hx0 hfl hc hh hweight n hn
    obtain ⟨-, -, -, -, hZ⟩ := hM (Tb.stepParameters y) hfit β k n
    have hZ0 : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β k n) ≠ 0 := by
      simpa using hZ
    have hZt : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β k n) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hsig : Measurable fun p : (Σ Y : Finset (TorusSite n), (Y → (T.stage k).labels.Ω)) =>
        ∑ i : p.1, labelMajorant T s₀ s₁ k (p.2 i) := by
      refine measurable_sigma_of_forall fun Y => ?_
      show Measurable fun ν : Y → (T.stage k).labels.Ω => ∑ i : Y, labelMajorant T s₀ s₁ k (ν i)
      exact Finset.measurable_sum _ fun i _ => hweight.borel.comp (measurable_pi_apply i)
    obtain ⟨G, hGdef⟩ : ∃ G : StageState T k n → ENNReal, ∀ q, G q =
        ENNReal.ofReal (Real.exp (∑ i : q.2.1, labelMajorant T s₀ s₁ k (q.2.2 i))) := ⟨_, fun _ => rfl⟩
    have hG : Measurable G := by
      have : G = fun q => ENNReal.ofReal (Real.exp (∑ i : q.2.1, labelMajorant T s₀ s₁ k (q.2.2 i))) := funext hGdef
      rw [this]
      exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hsig.comp measurable_snd))
    have hW : ∀ W : TorusField n, (open Classical in
        ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) W),
          ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ≤
        ENNReal.ofReal ((T.stage k).functional n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
          Real.exp (2 * (Tb.stepParameters y).E * Fintype.card (TorusSite n))) := by
      intro W
      refine le_trans (le_of_eq ?_) (hup W)
      refine Finset.sum_congr rfl fun Y _ => lintegral_congr fun ω => ?_
      rw [hGdef]
      rw [ENNReal.ofReal_mul' (Real.exp_nonneg _), mul_comm]
    have hmain : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β k n) *
        ∫⁻ u, G (stageState T k n u) ∂(markedSampleLaw T β k n) ≤
        ENNReal.ofReal ((T.stage k).functional n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
          Real.exp (2 * (Tb.stepParameters y).E * Fintype.card (TorusSite n))) := by
      refine (le_of_eq (hDens T β k n hstands hOn.measurable hn G hG)).trans ?_
      refine (lintegral_mono hW).trans ?_
      simp
    have hcard : ((Fintype.card (TorusSite n) : ℕ) : ℝ) = (n : ℝ) ^ 4 := by
      simp [TorusSite, ZMod.card]
    have hl : 0 ≤ Real.log (flowCoupling (Tb.stepParameters y) β k) :=
      Real.log_nonneg (hfit.y₁_ge.trans (hReach k le_rfl))
    have hnum := mul_exp_le_of_log_le (Cf := |C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) hcard
      (by positivity) hZ (hC β k hReach n hn) hl (by linarith) rfl
    have htriv : (T.stage k).functional n (trivialField n) = flowFunctionalAtTrivial (Tb.stepParameters y) β k n := by
      rw [harr]
      rfl
    rw [← htriv] at hnum
    have hI : ∫⁻ u, G (stageState T k n u) ∂(markedSampleLaw T β k n) ≤
        ENNReal.ofReal (Real.exp ((|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
          (1 + Real.log (flowCoupling (Tb.stepParameters y) β k)) * (n : ℝ) ^ 4)) := by
      have hprod : ENNReal.ofReal (torusPartition (Tb.stepParameters y) β k n) *
            ∫⁻ u, G (stageState T k n u) ∂(markedSampleLaw T β k n) ≤
          ENNReal.ofReal (torusPartition (Tb.stepParameters y) β k n) *
            ENNReal.ofReal (Real.exp ((|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) *
              (1 + Real.log (flowCoupling (Tb.stepParameters y) β k)) * (n : ℝ) ^ 4)) := by
        rw [← ENNReal.ofReal_mul hZ.le]
        exact hmain.trans (ENNReal.ofReal_le_ofReal hnum)
      have hcancel := mul_le_mul_right hprod (ENNReal.ofReal (torusPartition (Tb.stepParameters y) β k n))⁻¹
      rwa [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hZ0 hZt, one_mul, one_mul] at hcancel
    have hGf : ∀ u, ENNReal.ofReal (Real.exp (hullMajorantSum T s₀ s₁ k n u)) = G (stageState T k n u) := fun u => by
      rw [hGdef]
      show ENNReal.ofReal (Real.exp (∑ z ∈ (stageState T k n u).2.1,
        siteScore (labelMajorant T s₀ s₁ k) (stageState T k n u).2.1 (stageState T k n u).2.2 z)) = _
      rw [sum_siteScore_eq]
    simp only [hGf]
    exact hI
  have hrw : (|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6 +
      (|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) * Real.log (T.stage k).coupling) *
        (2 * ((Tb.stepParameters y).side : ℝ) ^ e) ^ 4 =
      (|C| + Real.log 2 + 2 * (Tb.stepParameters y).E + 6) * (1 + Real.log (flowCoupling (Tb.stepParameters y) β k)) *
        (((2 * (Tb.stepParameters y).side ^ e : ℕ)) : ℝ) ^ 4 := by
    rw [hxk]
    push_cast
    ring
  rw [hrw]
  exact key _ hn
end YangMills.Construction.CellWindows
end
