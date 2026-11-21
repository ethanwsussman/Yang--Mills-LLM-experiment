import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open StepSettings RenormalizationStepParameters TorusFields
variable {R : StepSetup} {n n' : ℕ}
def StepSettings.ChartSetting.lawDensity (s : ChartSetting R n) (u : FreeCoords s.free → ℝ)
    (η : FreeCoords s.free) : ℝ :=
  s.cutoffProduct η * Real.exp (-(u η))
open Classical in
def StepSettings.ChartSetting.restrictedPotential (s : ChartSetting R n) (lam v : ℝ) (X : Finset s.free)
    (u : FreeCoords s.free → ℝ) (η : FreeCoords s.free) : ℝ :=
  v * u η + (1 - v) * (u (s.restrictTo X η) + R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2)
namespace ClusterExpansionOfAStep
def SameNearIndices [NeZero n] [NeZero n'] (s : ChartSetting R n) (s' : ChartSetting R n') (Y : TorusSite n)
    (Y' : TorusSite n') (m : ℕ) (X : Finset s.free) (X' : Finset s'.free) : Prop :=
  ∀ (q : NearBondIndex) (h : nearBond R.params.side Y q ∈ s.free) (h' : nearBond R.params.side Y' q ∈ s'.free),
    IsNearIndex R.params.side m q → ((⟨_, h⟩ : s.free) ∈ X ↔ (⟨_, h'⟩ : s'.free) ∈ X')
inductive AlikePotentials [NeZero n] [NeZero n'] (s : ChartSetting R n) (s' : ChartSetting R n') (lam : ℝ)
    (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ) : (FreeCoords s.free → ℝ) → (FreeCoords s'.free → ℝ) → Prop
  | part_potential (ν : ℝ) : 0 ≤ ν → ν ≤ 1 →
      AlikePotentials s s' lam Y Y' m (s.partPotential ν) (s'.partPotential ν)
  | restrict (v : ℝ) (X : Finset s.free) (X' : Finset s'.free) (u : FreeCoords s.free → ℝ)
      (u' : FreeCoords s'.free → ℝ) : 0 ≤ v → v ≤ 1 → SameNearIndices s s' Y Y' m X X' →
      AlikePotentials s s' lam Y Y' m u u' →
      AlikePotentials s s' lam Y Y' m (s.restrictedPotential lam v X u) (s'.restrictedPotential lam v X' u')
  | convex (c : ℝ) (u w : FreeCoords s.free → ℝ) (u' w' : FreeCoords s'.free → ℝ) : 0 ≤ c → c ≤ 1 →
      AlikePotentials s s' lam Y Y' m u u' → AlikePotentials s s' lam Y Y' m w w' →
      AlikePotentials s s' lam Y Y' m (fun η => c * u η + (1 - c) * w η) (fun η => c * u' η + (1 - c) * w' η)
def CoordsInBalls (R : StepSetup) (z : NearBondIndex → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ q, coordNorm (z q) ≤ R.ballRadius
def LocalMeansClose : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
      ∀ (n n' : ℕ) [NeZero n] [NeZero n'], T.n₀ ≤ n → T.n₀ ≤ n' → ∀ (s : ChartSetting R n)
        (s' : ChartSetting R n') (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ), s.IsAdmissible →
        s'.IsAdmissible → SettingsAgreeNear s s' Y Y' m →
        (R.range : ℝ) / (4 * T.side) ≤ m →
        ∀ (u : FreeCoords s.free → ℝ) (u' : FreeCoords s'.free → ℝ), AlikePotentials s s' T.lam Y Y' m u u' →
        ∀ (F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ) (o : ℝ), Measurable F →
          DependsWithin T.side (m / 4) F →
          (∀ z z', CoordsInBalls R z → CoordsInBalls R z' → |F z - F z'| ≤ o) →
          |weightedMean (s.lawDensity u) (fun η => F (s.coordsByIndex Y η)) -
              weightedMean (s'.lawDensity u') (fun η => F (s'.coordsByIndex Y' η))| ≤
            o * Real.exp (-(T.rt * m / 2 ^ 3))
end ClusterExpansionOfAStep
end YangMills.Construction
end
