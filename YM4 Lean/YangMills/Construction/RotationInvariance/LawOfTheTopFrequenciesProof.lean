import YangMills.Construction.RotationInvariance.ConvexityOfTheTopFrequency
import YangMills.Construction.RotationInvariance.DivisibilityOfTheTopFrequency
import YangMills.Construction.RotationInvariance.LawOfTheTopFrequencies
import YangMills.Construction.RotationInvariance.TopFrequencyRangeSumsAndRate
import YangMills.Construction.Sequences.ConvexNatSequenceLinear
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MaxFrequencyLaw
theorem holds_of (hLinear : ConvexNatSequence.LinearOfConvexBoundedDivisible)
    (hConvex : MaxFrequencyConvex.Holds)
    (hTop : MaxFrequencyFacts.Holds)
    (hDiv : MaxFrequencyDivisible.Holds) : Holds := by
  intro m S d
  have hEven : ∀ k : ℕ, maxFrequency S d.angle (2 * k) = k * maxFrequency S d.angle 2 := by
    have hLine := hLinear (fun k => maxFrequency S d.angle (2 * k)) rfl
      (fun k hk => by
        have hc := hConvex m S d (k - 1) (k + 1)
        have hsum : k - 1 + (k + 1) = 2 * k := by omega
        rw [hsum] at hc
        exact hc)
      ⟨d.base.expo / 2, fun k => by
        have hr := (hTop m S d).1 (2 * k)
        have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
        rw [hcast] at hr
        calc (maxFrequency S d.angle (2 * k) : ℝ)
            ≤ d.base.expo * (2 * (k : ℝ)) / 4 := hr
          _ = d.base.expo / 2 * (k : ℝ) := by ring⟩
      (fun k hk => hDiv m S d k hk)
    intro k
    simpa using hLine k
  refine ⟨hEven, fun n => ?_⟩
  have hc := hConvex m S d (n / 2) (n - n / 2)
  have hsum : n / 2 + (n - n / 2) = n := by omega
  rw [hsum, hEven, hEven] at hc
  have hnat : 2 * maxFrequency S d.angle n ≤ n * maxFrequency S d.angle 2 := by
    calc 2 * maxFrequency S d.angle n
        ≤ n / 2 * maxFrequency S d.angle 2 + (n - n / 2) * maxFrequency S d.angle 2 := hc
      _ = (n / 2 + (n - n / 2)) * maxFrequency S d.angle 2 := by ring
      _ = n * maxFrequency S d.angle 2 := by rw [hsum]
  have hreal : (2 : ℝ) * (maxFrequency S d.angle n : ℝ) ≤
      (n : ℝ) * (maxFrequency S d.angle 2 : ℝ) := by exact_mod_cast hnat
  linarith
end YangMills.Construction.EuclideanFunctionals.MaxFrequencyLaw
end
