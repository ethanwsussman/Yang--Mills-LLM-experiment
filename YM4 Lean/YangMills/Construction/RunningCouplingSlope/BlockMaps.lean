import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction.SlopeCoefficient
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def BlockFieldMap (L : ℕ) : Type := (n : ℕ) → TorusField n → TorusField (n * L)
def pullbackTotal {L : ℕ} (H : GaugeTotal) (p : BlockFieldMap L) : GaugeTotal :=
  fun n V => H (n * L) (p n V)
def blockCentreSite (L : ℕ) {n : ℕ} (y : TorusSite n) : TorusSite (n * L) :=
  fun i => ((L * (y i).val : ℕ) : ZMod (n * L))
def constantOneForm (ν : Fin 4) (c : TorusLumps.LatticeBond) : ℝ := if c.2 = ν then 1 else 0
def latticeGradient (f : (Fin 4 → ℤ) → ℝ) (b : TorusLumps.LatticeBond) : ℝ :=
  f (b.1 + Pi.single b.2 1) - f b.1
def offsetNormReal (z : Fin 4 → ℤ) : ℝ := (TorusLumps.offsetNorm z : ℝ)
def HasPolynomialGrowth (f : (Fin 4 → ℤ) → ℝ) : Prop :=
  ∃ C m : ℝ, ∀ z, |f z| ≤ C * (1 + offsetNormReal z) ^ m
structure IsBlockMap (L : ℕ) (p : BlockFieldMap L)
    (P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ)
    (Pl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ) : Prop where
  map_trivial : ∀ᶠ n in Filter.atTop, p n (trivialField n) = trivialField (n * L)
  contDiffAt_perturb : ∀ᶠ n in Filter.atTop, ∀ (k : ℕ) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * L)),
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ =>
      ((p n (perturb c X σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) 0
  hasDerivAt_perturb : ∀ᶠ n in Filter.atTop, ∀ (b : TorusBond (n * L)) (c : TorusBond n)
    (X : imaginaryQuaternions),
    HasDerivAt (fun s : ℝ =>
      ((p n (perturb ![c] ![X] ![s] (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]))
      (P n b c • (X : ℍ[ℝ])) 0
  exp_decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ᶠ n in Filter.atTop, ∀ (b : TorusBond (n * L)) (c : TorusBond n),
    |P n b c| ≤ M * Real.exp (-(θ * supDist b.1 (blockCentreSite L c.1)))
  translation_invariant : ∀ᶠ n in Filter.atTop, ∀ (b : TorusBond (n * L)) (c : TorusBond n)
    (u : TorusSite n),
    P n (b.1 + blockCentreSite L u, b.2) (c.1 + u, c.2) = P n b c
  tendsto_kernel : ∀ b c : TorusLumps.LatticeBond,
    Filter.Tendsto (fun n => P n (TorusLumps.bondFrom 0 b) (TorusLumps.bondFrom 0 c))
      Filter.atTop (𝓝 (Pl b c))
  constant_form : ∀ ν : Fin 4, ∃ f : (Fin 4 → ℤ) → ℝ, (∃ C, ∀ z, |f z| ≤ C) ∧
    ∀ b : TorusLumps.LatticeBond,
    HasSum (fun c => Pl b c * constantOneForm ν c)
      ((L : ℝ)⁻¹ * constantOneForm ν b + latticeGradient f b)
  linear_potential : ∃ (f : (Fin 4 → ℤ) → ℝ) (κ : Fin 4 → ℝ), HasPolynomialGrowth f ∧
    ∀ b : TorusLumps.LatticeBond,
    HasSum (fun c : TorusLumps.LatticeBond => Pl b c * ((c.1 0 : ℤ) : ℝ) * constantOneForm secondAxis c)
      ((L : ℝ)⁻¹ ^ 2 * ((b.1 0 : ℤ) : ℝ) * constantOneForm secondAxis b + κ b.2 + latticeGradient f b)
end YangMills.Construction.SlopeCoefficient
end
