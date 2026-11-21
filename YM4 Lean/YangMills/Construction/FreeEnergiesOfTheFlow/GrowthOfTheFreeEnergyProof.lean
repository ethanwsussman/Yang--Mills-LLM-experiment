import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyFromAbove
import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyFromBelow
import YangMills.Construction.FreeEnergiesOfTheFlow.GrowthOfTheFreeEnergy
import YangMills.Construction.FreeEnergiesOfTheFlow.MassOfTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.ValuesAtFlatOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings
open YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.WeightedResponses
private theorem le_clusterRange {k : ℕ} {y : ℝ} (hy : (k : ℝ) ^ 100 ≤ y) : k ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
theorem freeEnergyVolumeScaling_of_bounds (hUpper : freeEnergyUpperBound) (hLower : freeEnergyLowerBound)
    (hTrivial : logFlowAtTrivialTwoTori) (hIntegral : flowFunctionalIntegral) : freeEnergyVolumeScaling := by
  obtain ⟨r₁, hr₁, hB⟩ := hLower
  obtain ⟨r₂, hr₂, hF⟩ := hTrivial
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), fun T hT hCold hrt => ?_⟩
  obtain ⟨y₁, hy₁⟩ := hB T hT hCold (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, hy₂⟩ := hF T hT hCold (hrt.trans (min_le_right _ _))
  refine ⟨max (max y₁ y₂) (max T.floorMin (((4 * T.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100)), fun y hy hS => ?_⟩
  have h1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have h2 : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have h3 : T.floorMin ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have h4 : (((4 * T.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100) ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hadm := hT.fits y h3
  obtain ⟨C₁, hC₁⟩ := hy₁ y h1 hS
  obtain ⟨nS, Sm, hnS, -, hSm, hTriv⟩ := hy₂ y h2 hS
  set c₀ : ℝ := Real.log 2 + 2 * (T.stepParameters y).E with hc₀
  set Sum : ℝ := ∑' j, scaleRate T nS j with hSum
  refine ⟨|Sum| + |c₀| + |C₁| + 6, nS, by positivity, hnS, fun β t hr n n' _ _ hb hb' hnn hside => ?_⟩
  have hZ := (hIntegral _ hadm β t n).2.2.2.2
  have hZ' := (hIntegral _ hadm β t n').2.2.2.2
  refine ⟨hZ, hZ', ?_⟩
  have hrange : 4 * (T.stepParameters y).n₀ + 2 ^ 16 ≤ clusterRange (T.stepParameters y).y₁ := le_clusterRange h4
  obtain ⟨-, a1⟩ := hUpper _ hadm hrange hS β t hr n hb
  obtain ⟨-, a2⟩ := hUpper _ hadm hrange hS β t hr n' hb'
  have b1 := hC₁ β t hr n hb
  have b2 := hC₁ β t hr n' hb'
  have f1 := abs_le.mp (hTriv β t hr n n' hb hb' hnn hside)
  set a := Real.log (torusPartition (T.stepParameters y) β t n)
  set a' := Real.log (torusPartition (T.stepParameters y) β t n')
  set b := Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n)
  set b' := Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n')
  have hx1 : 1 ≤ flowCoupling (T.stepParameters y) β t := hadm.y₁_ge.trans (hr t le_rfl)
  set lx := Real.log (flowCoupling (T.stepParameters y) β t)
  have hlx : 0 ≤ lx := Real.log_nonneg hx1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn'0 : (0 : ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  set q : ℝ := (n' : ℝ) ^ 4 / (n : ℝ) ^ 4 with hq
  have hq0 : 0 ≤ q := by positivity
  have hqn : q * (n : ℝ) ^ 4 = (n' : ℝ) ^ 4 := by
    rw [hq]
    field_simp
  set V' : ℝ := (n' : ℝ) ^ 4 with hV'
  have hV0 : 0 ≤ V' := by positivity
  have a1' : q * a ≤ q * b + c₀ * V' := by
    have h := mul_le_mul_of_nonneg_left a1 hq0
    have e : q * (b + c₀ * (n : ℝ) ^ 4) = q * b + c₀ * (q * (n : ℝ) ^ 4) := by ring
    rw [e, hqn] at h
    exact h
  have b1' : q * b - (C₁ + 6 * lx) * V' ≤ q * a := by
    have h := mul_le_mul_of_nonneg_left b1 hq0
    have e : q * (b - (C₁ + 6 * lx) * (n : ℝ) ^ 4) = q * b - (C₁ + 6 * lx) * (q * (n : ℝ) ^ 4) := by ring
    rw [e, hqn] at h
    exact h
  have hbig : (Sum + c₀ + C₁ + 6 * lx) * V' ≤ (|Sum| + |c₀| + |C₁| + 6) * (1 + lx) * V' := by
    refine mul_le_mul_of_nonneg_right ?_ hV0
    have i1 := le_abs_self Sum
    have i2 := le_abs_self c₀
    have i3 := le_abs_self C₁
    have p1 := abs_nonneg Sum
    have p2 := abs_nonneg c₀
    have p3 := abs_nonneg C₁
    nlinarith [mul_nonneg p1 hlx, mul_nonneg p2 hlx, mul_nonneg p3 hlx]
  have hneg : (Sum + (-c₀) + (-C₁) + 6 * lx) * V' ≤ (|Sum| + |c₀| + |C₁| + 6) * (1 + lx) * V' := by
    refine mul_le_mul_of_nonneg_right ?_ hV0
    have i1 := le_abs_self Sum
    have i2 := neg_abs_le c₀
    have i3 := neg_abs_le C₁
    have p1 := abs_nonneg Sum
    have p2 := abs_nonneg c₀
    have p3 := abs_nonneg C₁
    nlinarith [mul_nonneg p1 hlx, mul_nonneg p2 hlx, mul_nonneg p3 hlx]
  have f1a := f1.1
  have f1b := f1.2
  have e1 : (Sum + c₀ + C₁ + 6 * lx) * V' = Sum * V' + c₀ * V' + (C₁ + 6 * lx) * V' := by ring
  have hSV : V' * Sum = Sum * V' := mul_comm _ _
  rw [abs_le]
  constructor
  · have h6 : -((Sum + c₀ + C₁ + 6 * lx) * V') ≤ a' - q * a := by
      rw [e1]
      linarith
    linarith
  · have h5 : a' - q * a ≤ (Sum + c₀ + C₁ + 6 * lx) * V' := by
      rw [e1]
      linarith
    linarith
end YangMills.Construction.FreeEnergies
end
