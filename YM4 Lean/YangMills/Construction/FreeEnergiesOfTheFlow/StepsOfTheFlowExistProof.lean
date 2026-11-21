import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.StepsOfTheFlowExist
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open TorusLumps RenormalizationStepParameters StepSettings ClusterExpansionOfAStep WeightedResponses
private theorem clusterRange_le_succ {x x' B : ℝ} (hB : 0 ≤ B) (hx' : (2 * B + 1) ^ 100 ≤ x')
    (hxx : x ≤ x' + 2 * B) (hx : 0 ≤ x) :
    clusterRange x ≤ clusterRange x' + 1 := by
  have h0 : 0 ≤ x' := le_trans (by positivity) hx'
  set u : ℝ := x' ^ ((1 : ℝ) / 100) with hu
  have hu100 : u ^ 100 = x' := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
  have hu2 : 2 * B + 1 ≤ u := by
    have h1 : ((2 * B + 1) ^ 100) ^ ((1 : ℝ) / 100) = 2 * B + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hx' (by norm_num)
  have hu1 : 1 ≤ u := by linarith
  have hbig : x ≤ (u + 1) ^ 100 := by
    have hb : u ^ 100 + 100 * u ^ 99 ≤ (u + 1) ^ 100 := by
      have h1 : 1 + (100 : ℝ) * (1 / u) ≤ (1 + 1 / u) ^ 100 :=
        one_add_mul_le_pow (by have : 0 ≤ 1 / u := by positivity
                               linarith) 100
      have hup : 0 < u ^ 100 := by positivity
      have h2 := mul_le_mul_of_nonneg_left h1 hup.le
      have e1 : u ^ 100 * (1 + (100 : ℝ) * (1 / u)) = u ^ 100 + 100 * u ^ 99 := by
        field_simp
      have e2 : u ^ 100 * (1 + 1 / u) ^ 100 = (u + 1) ^ 100 := by
        rw [← mul_pow]
        congr 1
        field_simp
      rwa [e1, e2] at h2
    have hpow : u ≤ u ^ 99 := le_self_pow₀ hu1 (by norm_num)
    nlinarith
  have hle : x ^ ((1 : ℝ) / 100) ≤ u + 1 := by
    have h1 : ((u + 1) ^ 100) ^ ((1 : ℝ) / 100) = u + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [← h1]
    exact Real.rpow_le_rpow hx hbig (by norm_num)
  unfold clusterRange
  refine Nat.ceil_le.mpr (hle.trans ?_)
  push_cast
  have := Nat.le_ceil u
  linarith
theorem flowStepsExist_of_expansionAlongFlow (hA : expansionAlongFlow) : flowStepsExist := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ _ => ?_⟩
  refine ⟨max T.floorMin (max (200 * T.B) ((2 * T.B + 1) ^ 100)), fun y hy hS => ?_⟩
  have hy₀ : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hyB : 200 * T.B ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyP : (2 * T.B + 1) ^ 100 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hfit := hT.fits y hy₀
  have hB : 1 ≤ T.B := hT.B_ge
  intro β t hr
  have hone : ∀ s : ℕ, ∃ R : StepSetup, s < t → IsFlowStep T y β s R := by
    intro s
    by_cases hs : s < t
    · have hrs : CouplingsAboveFloor (T.stepParameters y) β s := fun j hj => hr j (by omega)
      have hrs' : CouplingsAboveFloor (T.stepParameters y) β (s + 1) := fun j hj => hr j (by omega)
      obtain ⟨-, f, hf, Λ, Dq, Φ, φ, hH⟩ := (hA _ hS β s hrs).1
      have hmove := (hA _ hS β (s + 1) hrs').2 s (Nat.lt_succ_self s)
      have hx : y ≤ flowCoupling (T.stepParameters y) β s := hr s hs.le
      have hx' : y ≤ flowCoupling (T.stepParameters y) β (s + 1) := hr (s + 1) hs
      have hab := abs_le.mp hmove
      have hB' : (T.stepParameters y).B = T.B := rfl
      rw [hB'] at hab
      refine ⟨⟨T.stepParameters y, s, flowCoupling (T.stepParameters y) β s,
        flowCoupling (T.stepParameters y) β (s + 1),
        flowFunctional (T.stepParameters y) β s, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩, fun _ => ?_⟩
      refine ⟨⟨rfl, rfl, rfl, hx, ⟨hf, hH⟩, ?_, ?_⟩, rfl, rfl, rfl, rfl⟩
      · show flowCoupling (T.stepParameters y) β s ≤ 1.01 * flowCoupling (T.stepParameters y) β (s + 1)
        linarith [hab.1]
      · show clusterRange (flowCoupling (T.stepParameters y) β s) ≤
          clusterRange (flowCoupling (T.stepParameters y) β (s + 1)) + 1
        exact clusterRange_le_succ (by linarith) (hyP.trans hx') (by linarith [hab.1]) (by linarith)
    · obtain ⟨-, f, hf, Λ, Dq, Φ, φ, hH⟩ := (hA _ hS β 0 (fun j hj => hr j (by omega))).1
      exact ⟨⟨T.stepParameters y, 0, 0, 0, wilsonWeight β, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩,
        fun h => absurd h hs⟩
  choose R hR using hone
  exact ⟨R, fun s hs => hR s hs⟩
end YangMills.Construction.FreeEnergies
end
