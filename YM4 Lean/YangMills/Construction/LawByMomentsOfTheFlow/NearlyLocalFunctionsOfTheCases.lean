import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import YangMills.Construction.ResponseInTheExpansion.FunctionsOfTheCases
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open StepSettings StepCosts TorusFields TorusLumps WeightedResponses ResponseInTheExpansion ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n]
structure IsNearlyLocalCaseFunction (R : StepSetup) (o : TorusSite (n * R.params.side)) (Rr : ℕ) (Sz : ℝ) (F : CaseFunction R n) : Prop where
  abs_le : ∀ W Yt ωt bad b, |F W Yt ωt bad b| ≤ Sz
  measurable : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b
  gaugeInvariant : IsGaugeInvariantCase F
  abs_sub_le : ∀ (m : ℕ), (clusterRange R.coupling : ℝ) / 64 ≤ m → ∀ W W' Yt Yt' ωt ωt' bad bad' b b',
    IsLiveState R.params R.coupling R.labelWeight W Yt ωt → IsLiveState R.params R.coupling R.labelWeight W' Yt' ωt' →
    (∀ c : TorusBond (n * R.params.side), c.1 ∈ supBall o ((Rr : ℝ) + m) → c.1 + unitStep (n * R.params.side) c.2 ∈ supBall o ((Rr : ℝ) + m) →
      W c.1 c.2 = W' c.1 c.2 ∧ (c ∈ bad ↔ c ∈ bad')) →
    (∀ y ∈ supBall o ((Rr : ℝ) + m), (y ∈ Yt ↔ y ∈ Yt') ∧
      ∀ (hy : y ∈ Yt) (hy' : y ∈ Yt'), ωt ⟨y, hy⟩ = ωt' ⟨y, hy'⟩) →
    (∀ c, (supDist (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) (parentBlock R.params.side o) : ℝ) ≤ Rr → b c = b' c) →
    |F W Yt ωt bad b - F W' Yt' ωt' bad' b'| ≤ Sz * Real.exp (-(R.params.decayRate * (m : ℝ)))
structure IsNearlyLocalStateFunction (R : StepSetup) (Q : ResponseInTheExpansion.StateFunction R n) (y : TorusSite n) (K ρ : ℝ) : Prop where
  measurable : ∀ Y : Finset (TorusSite n), Measurable fun p : TorusField n × (Y → R.labels.Ω) => Q p.1 Y p.2
  abs_le : ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω), |Q W Y ω| ≤ K
  abs_sub_le : ∀ (W W' : TorusField n) (Y Y' : Finset (TorusSite n)) (ω : Y → R.labels.Ω) (ω' : Y' → R.labels.Ω) (m : ℕ),
    IsLiveState R.params R.coupling R.labelWeight W Y ω → IsLiveState R.params R.coupling R.labelWeight W' Y' ω' →
    ρ + (clusterRange R.coupling : ℝ) / 64 ≤ m → StatesAgreeNear R.params W W' Y Y' ω ω' y y m →
    |Q W Y ω - Q W' Y' ω'| ≤ K * Real.exp (-R.params.decayRate * (m - ρ))
section Boxes
variable {N : ℕ} [NeZero N]
theorem exists_offsetInBox_of_supDist_le {x y : TorusSite N} {k : ℕ} (h : (supDist x y : ℝ) ≤ k) :
    ∃ e, OffsetInBox k e ∧ x = y + siteOfInt e := by
  have hk : supDist x y ≤ k := by exact_mod_cast h
  refine ⟨fun i => (x i - y i).valMinAbs, fun i => ?_, ?_⟩
  · have h1 : ((x i - y i).valMinAbs).natAbs ≤ supDist x y :=
      Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1.trans hk
  · funext i
    simp [siteOfInt, ZMod.coe_valMinAbs]
theorem offsetInBox_add_single {k : ℕ} {y : TorusSite N} {e e' : Fin 4 → ℤ} {i : Fin 4} (hs : 2 * k + 2 < N) (he : OffsetInBox k e)
    (he' : OffsetInBox k e') (hh : y + siteOfInt e + unitStep N i = y + siteOfInt e') : OffsetInBox k (e + Pi.single i 1) := by
  have h0 : (siteOfInt (e + Pi.single i 1) : TorusSite N) = siteOfInt e' := by
    have h1 : (siteOfInt e : TorusSite N) + unitStep N i = siteOfInt e' := by
      have := add_right_cancel (a := (siteOfInt e : TorusSite N) + unitStep N i) (b := y) (c := siteOfInt e') (by
        rw [add_comm _ y, ← add_assoc, hh, add_comm y])
      exact this
    rw [← h1]
    funext l
    by_cases hl : l = i
    · subst hl
      simp [siteOfInt, unitStep]
    · simp [siteOfInt, unitStep, Pi.single_eq_of_ne hl]
  intro l
  have h1 := congrFun h0 l
  simp only [siteOfInt] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have a' := abs_le.mp (he l)
  have b' := abs_le.mp (he' l)
  have hsm : |(Pi.single i 1 : Fin 4 → ℤ) l| ≤ 1 := by
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Pi.single_eq_of_ne hl]
  have c' := abs_le.mp hsm
  have h3 : |e' l - (e + Pi.single i 1 : Fin 4 → ℤ) l| < (N : ℤ) := by
    simp only [Pi.add_apply]
    rw [abs_lt]
    constructor <;> omega
  have h4 := Int.eq_zero_of_abs_lt_dvd h1 h3
  have h5 : (e + Pi.single i 1 : Fin 4 → ℤ) l = e' l := by omega
  rw [h5]
  exact he' l
end Boxes
private theorem chartDensity_nonneg {R : StepSetup} (s : ChartSetting R n) (η : FreeCoords s.free) : 0 ≤ chartDensity s η := by
  unfold chartDensity ChartSetting.cutoffProduct
  refine mul_nonneg (Finset.prod_nonneg fun b _ => ?_) (Real.exp_pos _).le
  unfold cutoffFactor
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
private theorem abs_integral_ratio_le {ι : Type} [MeasurableSpace ι] {μ : Measure ι} {d f : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ x, 0 ≤ d x)
    (hf : ∀ x, |f x * d x| ≤ c * d x) : |(∫ x, f x * d x ∂μ) / ∫ x, d x ∂μ| ≤ c := by
  by_cases h0 : ∫ x, d x ∂μ = 0
  · rw [h0, div_zero, abs_zero]
    exact hc
  have hint : Integrable d μ := by
    by_contra hi
    exact h0 (integral_undef hi)
  have hpos : 0 < ∫ x, d x ∂μ := lt_of_le_of_ne (integral_nonneg hd) (Ne.symm h0)
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have h1 := norm_integral_le_of_norm_le (hint.const_mul c) (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact hf x)
  rw [integral_const_mul] at h1
  simpa using h1
theorem abs_weightedMean_le {R : StepSetup} {s : ChartSetting R n} {g : FreeCoords s.free → ℝ} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ η, |g η| ≤ c) :
    |weightedMean (chartDensity s) g| ≤ c := by
  unfold weightedMean
  refine abs_integral_ratio_le hc (chartDensity_nonneg s) fun η => ?_
  rw [abs_mul, abs_of_nonneg (chartDensity_nonneg s η)]
  exact mul_le_mul_of_nonneg_right (hg η) (chartDensity_nonneg s η)
theorem IsNearlyLocalCaseFunction.abs_sub_le_of_statesAgree {R : StepSetup} {F : CaseFunction R n} {y : TorusSite (n * R.params.side)} {K : ℝ} {ρ : ℕ}
    (hF : IsNearlyLocalCaseFunction R y ρ K F)
    {W W' : TorusField (n * R.params.side)} {A A' : Finset (TorusSite (n * R.params.side))} {ω : A → R.labels.Ω} {ω' : A' → R.labels.Ω} {k : ℕ}
    (hl : IsLiveState R.params R.coupling R.labelWeight W A ω) (hl' : IsLiveState R.params R.coupling R.labelWeight W' A' ω')
    (hk : (ρ : ℝ) + (clusterRange R.coupling : ℝ) / 64 ≤ k) (hst : StatesAgreeNear R.params W W' A A' ω ω' y y k)
    {bad bad' : Finset (TorusBond (n * R.params.side))} {b b' : BaseChoice R.params.side n}
    (hbad : ∀ c : TorusBond (n * R.params.side), c.1 ∈ supBall y (k : ℝ) → (c ∈ bad ↔ c ∈ bad'))
    (hb : ∀ c, (supDist (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) (parentBlock R.params.side y) : ℝ) ≤ ρ → b c = b' c) :
    |F W A ω bad b - F W' A' ω' bad' b'| ≤ K * Real.exp (-R.params.decayRate * ((k : ℝ) - ρ)) := by
  have hρk : ρ ≤ k := by
    have h1 : (0 : ℝ) ≤ (clusterRange R.coupling : ℝ) / 64 := by positivity
    have h2 : (ρ : ℝ) ≤ k := by linarith
    exact_mod_cast h2
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hρk
  have hcast : ((ρ + m : ℕ) : ℝ) = (ρ : ℝ) + m := by push_cast; ring
  obtain ⟨s1, -, hf, hY, hlb, -⟩ := hst
  have offset : ∀ x ∈ supBall y ((ρ : ℝ) + m), ∃ h, OffsetInBox (ρ + m) h ∧ x = y + siteOfInt h := by
    intro x hx
    exact exists_offsetInBox_of_supDist_le (k := ρ + m) (by rw [hcast]; exact (Finset.mem_filter.mp hx).2)
  have h := hF.abs_sub_le m (by rw [hcast] at hk; linarith) W W' A A' ω ω' bad bad' b b' hl hl' ?_ ?_ hb
  · refine h.trans (le_of_eq ?_)
    rw [hcast]
    congr 2
    ring
  · intro c h1 h2
    refine ⟨?_, hbad c (by rw [hcast]; exact h1)⟩
    obtain ⟨e, he, e1⟩ := offset _ h1
    obtain ⟨e', he', e2⟩ := offset _ h2
    have hb' : BondOffsetInBox (ρ + m) (e, c.2) := ⟨he, offsetInBox_add_single s1 he he' (by rw [← e1, ← e2])⟩
    have := hf (e, c.2) hb'
    simp only [bondFrom] at this
    rw [← e1] at this
    exact this
  · intro x hx
    obtain ⟨e, he, rfl⟩ := offset x hx
    exact ⟨hY e he, fun h1 h2 => hlb e he h1 h2 (Finset.mem_univ _)⟩
theorem IsNearlyLocalCaseFunction.toStateFunction {R : StepSetup} {F : CaseFunction R n} {y : TorusSite (n * R.params.side)} {K : ℝ} {ρ : ℕ}
    (hF : IsNearlyLocalCaseFunction R y ρ K F) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    IsNearlyLocalStateFunction R (fun W A ω => F W A ω bad b) y K ρ where
  measurable := fun A => hF.measurable A bad b
  abs_le := fun _ _ _ => hF.abs_le _ _ _ _ _
  abs_sub_le := fun _ _ _ _ _ _ _ hl hl' hk hst => hF.abs_sub_le_of_statesAgree hl hl' hk hst (fun _ _ => Iff.rfl) (fun _ _ => rfl)
end YangMills.Construction.MomentLaw
end
