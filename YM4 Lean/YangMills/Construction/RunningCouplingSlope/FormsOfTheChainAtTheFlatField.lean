import YangMills.Construction.RunningCouplingSlope.BlockMaps
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction.FlatLinearization
open BlockAverages hiding unitStep
open TorusFields TorusLumps SlopeCoefficient
abbrev RealOneForm (n : ℕ) : Type := TorusBond n → ℝ
abbrev BondKernel : Type := (m : ℕ) → TorusBond m → TorusBond m → ℝ
variable {m n : ℕ}
def stepEndpoint (x : TorusSite m) (s : PathStep) : TorusSite m :=
  if s.2 then x + unitStep m s.1 else x - unitStep m s.1
def pathIntegral (ξ : RealOneForm m) : TorusSite m → List PathStep → ℝ
  | _, [] => 0
  | x, s :: r => (if s.2 then ξ (x, s.1) else - ξ (x - unitStep m s.1, s.1)) +
      pathIntegral ξ (stepEndpoint x s) r
def contourAverage (L : ℕ) (ξ : RealOneForm (n * L)) (c : TorusBond n) : ℝ :=
  (1 / (24 * (L : ℝ) ^ 4)) * ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
    pathIntegral ξ (blockCentreSite L c.1) (bondContour L h π c.2)
def coarseSite (L : ℕ) (x : TorusSite (n * L)) : TorusSite n :=
  fun i => ((((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ)
def offsetFromCentre (L : ℕ) (x : TorusSite (n * L)) : Fin 4 → ℤ :=
  fun i => ((x - blockCentreSite L (coarseSite L x)) i).valMinAbs
def CrossesBlockBoundary (L : ℕ) (b : TorusBond (n * L)) : Prop :=
  coarseSite L (b.1 + unitStep (n * L) b.2) ≠ coarseSite L b.1
def IsBlockTreeBond (L : ℕ) (b : TorusBond (n * L)) : Prop :=
  ¬ CrossesBlockBoundary L b ∧ ∀ l, b.2 < l → offsetFromCentre L b.1 l = 0
def VanishesOnBlockTrees (L : ℕ) (ξ : RealOneForm (n * L)) : Prop :=
  ∀ b, IsBlockTreeBond L b → ξ b = 0
def indicatorForm (c : TorusBond n) : RealOneForm n := fun c' => if c' = c then 1 else 0
def kernelPairing [NeZero m] (K : TorusBond m → TorusBond m → ℝ) (ξ ζ : RealOneForm m) : ℝ :=
  ∑ b, ∑ c, K b c * ξ b * ζ c
def plaquetteCurl (ξ : RealOneForm m) (x : TorusSite m) (μ ν : Fin 4) : ℝ :=
  ξ (x, μ) + ξ (x + unitStep m μ, ν) - ξ (x + unitStep m ν, μ) - ξ (x, ν)
def curlEnergy [NeZero m] (ξ : RealOneForm m) : ℝ :=
  ∑ x : TorusSite m, ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then plaquetteCurl ξ x μ ν ^ 2 else 0
def reflectedBond (b : TorusBond m) : TorusBond m := (- b.1 - unitStep m b.2, b.2)
def IsMinimizerFamily (a : ℝ) (L : ℕ) [NeZero n] [NeZero L]
    (K : TorusBond (n * L) → TorusBond (n * L) → ℝ)
    (P : TorusBond (n * L) → TorusBond n → ℝ) : Prop :=
  ∀ c, VanishesOnBlockTrees L (fun b => P b c) ∧ ∀ ζ : RealOneForm (n * L), VanishesOnBlockTrees L ζ →
    kernelPairing K (fun b => P b c) ζ +
      a * ∑ c', (contourAverage L (fun b => P b c) c' - indicatorForm c c') * contourAverage L ζ c' = 0
def IsPositiveOnTreeGauge (a : ℝ) (L : ℕ) [NeZero n] [NeZero L]
    (K : TorusBond (n * L) → TorusBond (n * L) → ℝ) : Prop :=
  ∀ ξ : RealOneForm (n * L), VanishesOnBlockTrees L ξ → ξ ≠ 0 →
    0 < kernelPairing K ξ ξ + a * ∑ c : TorusBond n, contourAverage L ξ c ^ 2
open Classical in
def renormalizedKernel (a : ℝ) (L : ℕ) (h : BondKernel)
    (P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ) : BondKernel :=
  fun n c c' =>
    if hn : n ≠ 0 ∧ L ≠ 0 then
      haveI : NeZero n := ⟨hn.1⟩
      haveI : NeZero L := ⟨hn.2⟩
      kernelPairing (h (n * L)) (fun b => P n b c) (fun b => P n b c') +
        a * ∑ c'', (indicatorForm c c'' - contourAverage L (fun b => P n b c) c'') *
          (indicatorForm c' c'' - contourAverage L (fun b => P n b c') c'')
    else 0
structure IsFlowKernel (h : BondKernel) : Prop where
  symm : ∀ᶠ m in Filter.atTop, ∀ b c : TorusBond m, h m b c = h m c b
  decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ᶠ m in Filter.atTop, ∀ b c : TorusBond m,
    |h m b c| ≤ M * Real.exp (-(θ * supDist b.1 c.1))
  translation_invariant : ∀ᶠ m in Filter.atTop, ∀ (u : TorusSite m) (b c : TorusBond m),
    h m (b.1 + u, b.2) (c.1 + u, c.2) = h m b c
  reflection_invariant : ∀ᶠ m in Filter.atTop, ∀ b c : TorusBond m,
    h m (reflectedBond b) (reflectedBond c) = h m b c
  annihilates_gradients : ∀ᶠ m in Filter.atTop, ∀ [NeZero m] (b : TorusBond m) (φ : TorusSite m → ℝ),
    ∑ c : TorusBond m, h m b c * (φ (c.1 + unitStep m c.2) - φ c.1) = 0
  annihilates_constants : ∀ᶠ m in Filter.atTop, ∀ [NeZero m] (b : TorusBond m) (ν : Fin 4),
    ∑ c : TorusBond m, h m b c * (if c.2 = ν then 1 else 0) = 0
  tendsto : ∃ hl : LatticeBond → LatticeBond → ℝ, ∀ b c : LatticeBond,
    Filter.Tendsto (fun m => h m (bondFrom 0 b) (bondFrom 0 c)) Filter.atTop (𝓝 (hl b c))
  curl_lower_bound : ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ m in Filter.atTop, ∀ [NeZero m] (ξ : RealOneForm m),
    κ * curlEnergy ξ ≤ kernelPairing (h m) ξ ξ
structure HasHessianAtTrivial (H : GaugeTotal) (K : TorusBond m → TorusBond m → ℝ) : Prop where
  smooth : ∀ (r k : ℕ) (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions),
    ContDiffAt ℝ (r : ℕ) (fun σ : Fin k → ℝ => H m (perturb c X σ (trivialField m))) 0
  hessian_eq : ∀ (c c' : TorusBond m) (X X' : imaginaryQuaternions),
    hessianAtTrivial H m c c' X X' = inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * K c c'
structure IsBlockKernel (L : ℕ) (P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ)
    (Pl : LatticeBond → LatticeBond → ℝ) : Prop where
  decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ᶠ n in Filter.atTop, ∀ (b : TorusBond (n * L)) (c : TorusBond n),
    |P n b c| ≤ M * Real.exp (-(θ * supDist b.1 (blockCentreSite L c.1)))
  translation_invariant : ∀ᶠ n in Filter.atTop, ∀ (b : TorusBond (n * L)) (c : TorusBond n) (u : TorusSite n),
    P n (b.1 + blockCentreSite L u, b.2) (c.1 + u, c.2) = P n b c
  tendsto : ∀ b c : LatticeBond,
    Filter.Tendsto (fun n => P n (bondFrom 0 b) (bondFrom 0 c)) Filter.atTop (𝓝 (Pl b c))
  constant_form : ∀ ν : Fin 4, ∃ f : (Fin 4 → ℤ) → ℝ, (∃ C, ∀ z, |f z| ≤ C) ∧ ∀ b : LatticeBond,
    HasSum (fun c => Pl b c * constantOneForm ν c) ((L : ℝ)⁻¹ * constantOneForm ν b + latticeGradient f b)
  linear_potential : ∃ (f : (Fin 4 → ℤ) → ℝ) (κ : Fin 4 → ℝ), HasPolynomialGrowth f ∧ ∀ b : LatticeBond,
    HasSum (fun c : LatticeBond => Pl b c * ((c.1 0 : ℤ) : ℝ) * constantOneForm secondAxis c)
      ((L : ℝ)⁻¹ ^ 2 * ((b.1 0 : ℤ) : ℝ) * constantOneForm secondAxis b + κ b.2 + latticeGradient f b)
end YangMills.Construction.FlatLinearization
end
