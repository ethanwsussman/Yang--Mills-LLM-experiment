import YangMills.Construction.RealFunctions.SmoothBumps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Bumps
def GevreyBumpBounds : Prop :=
  (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) expNegInv ∧
    ∀ (r : ℕ) (t : ℝ),
      |iteratedDeriv r expNegInv t| ≤ gevreyConst ^ r * (r.factorial : ℝ) ^ 2) ∧
  (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) smoothTransition ∧
    Monotone smoothTransition ∧
    (∀ t : ℝ, t ≤ 0 → smoothTransition t = 0) ∧
    (∀ t : ℝ, 1 ≤ t → smoothTransition t = 1) ∧
    ∀ t : ℝ, 0 < t → 0 < smoothTransition t) ∧
  (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) symmetricTransition ∧
    (∀ t : ℝ, symmetricTransition (-t) = symmetricTransition t) ∧
    (∀ t : ℝ, symmetricTransition t ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, symmetricTransition t = 0) ∧
    (∀ t : ℝ, 1 < |t| → 0 < symmetricTransition t) ∧
    (∀ t : ℝ, t ∉ Set.Ioo (-2 : ℝ) 2 → symmetricTransition t = 1) ∧
    ∀ s s' : ℝ, |s| ≤ |s'| → symmetricTransition s ≤ symmetricTransition s') ∧
  (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) mollifiedIndicator ∧
    (∀ t : ℝ, 0 ≤ mollifiedIndicator t ∧ mollifiedIndicator t ≤ 1) ∧
    tsupport mollifiedIndicator ⊆ Set.Icc (-(3 / 4) : ℝ) (3 / 4) ∧
    ∀ t : ℝ,
      HasSum (fun l : ℤ => mollifiedIndicator (t - l)) 1 ∧
        {l : ℤ | mollifiedIndicator (t - l) ≠ 0}.encard ≤ 2) ∧
  (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cubeBump ∧
    HasCompactSupport cubeBump ∧
    (∀ y : Fin 4 → ℝ, 0 ≤ cubeBump y ∧ cubeBump y ≤ 1) ∧
    (∀ y : Fin 4 → ℝ, (∀ c, y c ∈ Set.Icc (-(3 / 4) : ℝ) (3 / 4)) → cubeBump y = 1) ∧
    tsupport cubeBump ⊆ Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-1 : ℝ) 1) ∧
    ∀ y : Fin 4 → ℝ,
      Real.sqrt (∑ c : Fin 4, (fderiv ℝ cubeBump y (Pi.single c 1)) ^ 2) ≤
        cubeBumpGradConst) ∧
  ∀ (r : ℕ) (t : ℝ),
    |iteratedDeriv r smoothTransition t| ≤
        normalizerBound * twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2 ∧
      |iteratedDeriv r symmetricTransition t| ≤
        normalizerBound * twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2 ∧
      |iteratedDeriv r mollifiedIndicator t| ≤
        normalizerBound * twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2
end Bumps
end YangMills.Construction
