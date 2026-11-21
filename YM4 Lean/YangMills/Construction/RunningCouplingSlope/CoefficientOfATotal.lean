import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction.SlopeCoefficient
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages
abbrev GaugeTotal : Type := (n : ℕ) → TorusField n → ℝ
def secondAxis : Fin 4 := 1
def hessianAtTrivial (H : GaugeTotal) (n : ℕ) (c c' : TorusBond n) (X X' : imaginaryQuaternions) : ℝ :=
  mixedDeriv (H n) (trivialField n) ![c, c'] ![X, X']
structure IsGaugeTotalAt (H : GaugeTotal) (n : ℕ) : Prop where
  contDiffAt_perturb : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
    ContDiffAt ℝ 2 (fun t : Fin k → ℝ => H n (perturb c X t (trivialField n))) 0
  gauge_invariant_near : ∀ᶠ p : (TorusSite n → UnitQuaternion) × TorusField n in 𝓝 (1, trivialField n),
    H n (gaugeTransform p.1 p.2) = H n p.2
  constant_gauge_invariant : ∀ g : UnitQuaternion, ∀ᶠ V in 𝓝 (trivialField n),
    H n (gaugeTransform (fun _ => g) V) = H n V
  isometry_invariant : ∀ g : TorusIsometry, ∀ᶠ V in 𝓝 (trivialField n), ∀ V' : TorusField n,
    g.Transports V V' → H n V' = H n V
structure IsLocalGaugeTotal (l : Filter ℕ) (H : GaugeTotal) (K : LatticeBond → LatticeBond → ℝ) : Prop where
  eventually_isGaugeTotalAt : ∀ᶠ n in l, IsGaugeTotalAt H n
  exp_decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ᶠ n in l, ∀ (c c' : TorusBond n) (X X' : imaginaryQuaternions),
    ‖X‖ = 1 → ‖X'‖ = 1 →
    |hessianAtTrivial H n c c' X X'| ≤ M * Real.exp (-(θ * supDist c.1 c'.1))
  tendsto_kernel : ∀ (c c' : LatticeBond) (X X' : imaginaryQuaternions),
    Filter.Tendsto (fun n => hessianAtTrivial H n (bondFrom 0 c) (bondFrom 0 c') X X') l
      (𝓝 (inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * K c c'))
def secondMomentTerm (K : LatticeBond → LatticeBond → ℝ) (z : Fin 4 → ℤ) : ℝ :=
  -(1 / 2) * K (0, secondAxis) (z, secondAxis) * ((z 0 : ℤ) : ℝ) ^ 2
def HasSlopeCoefficient (l : Filter ℕ) (H : GaugeTotal) (b : ℝ) : Prop :=
  ∃ K : LatticeBond → LatticeBond → ℝ, IsLocalGaugeTotal l H K ∧ HasSum (secondMomentTerm K) b
end YangMills.Construction.SlopeCoefficient
end
