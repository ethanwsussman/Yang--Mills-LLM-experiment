import YangMills.Construction.BackgroundField.AxialToLandauGaugeWhereCubesCover
import YangMills.Construction.BackgroundField.PositiveDefiniteOperatorsAndTheWallOfARegion
import YangMills.Construction.BackgroundField.VariationalProblemWithPrescribedAverages
import YangMills.Construction.Lattice.SequencesAtACubeSizeAndAGap
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.BackgroundField.GreenBoundMinimizers
open PrescribedAverageProblem
variable {L m k : ℕ}
def DatumSmallAtBoundary (K : ℕ) (σ : NestedRegions L m k) (δ : ℝ)
    (W : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) : Prop :=
  CurvatureSmallAtBoundary σ K δ (extendByOne (bondsTouching (σ.fineSitesOf K 0)) (W 0))
def ConclusionHoldsWith (L n r : ℕ) (a₀ a₁ B₃ : ℝ) (B₄ : ℝ → ℝ) : Prop :=
  ∀ (m K k : ℕ), 0 < m → 1 ≤ k →
    6 * ((L : ℝ) ^ r * (L : ℝ) ^ n) ≤ RegionChains.sitesPerAxis L m K k →
    ∀ σ : NestedRegions L m k, IsDomainSequence n r K σ →
    ShellCubesCoverPlaquettes σ n K (gaugeFixingConstants L n r).cubeConst →
    ∀ (W : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) (ε₁ : ℝ), 0 < ε₁ → ε₁ ≤ a₁ →
      IsShellDatum K σ W → IsSmallCurvatureDatum K σ ε₁ W →
      DatumSmallAtBoundary K σ ((gaugeFixingConstants L n r).cubeConst * (L : ℝ) ^ n * (B₃ * ε₁)) W →
      ∃ O : Set (FineBond L m K → Matrices.ComplexMatrix2),
        IsMinimizingOrbit K σ (admissibleFields K σ (B₃ * ε₁) W) O ∧
        (∀ ε₀, B₃ * ε₁ ≤ ε₀ → ε₀ ≤ a₀ →
          IsCriticalOrbitIn K σ (admissibleFields K σ ε₀ W) O ∧
          ∀ O', IsCriticalOrbitIn K σ (admissibleFields K σ ε₀ W) O' → O' = O) ∧
        ∀ V ∈ O, ∀ i ≤ k, ∀ M' : ℕ, 0 < M' →
          (M' : ℝ) * ((L : ℝ) ^ r * (L : ℝ) ^ n) ≤ (L : ℝ) ^ r * (L : ℝ) ^ n * (a₁ / ε₁) →
          ∀ Q : Set (FourTorus L m), IsAdmissibleCube K n r σ i (M' * (L ^ r * L ^ n)) Q →
            IsSmoothOnCube (fun β₀ => 0 < β₀ ∧ β₀ < 1) B₃ B₄ ε₁ K k i (M' * (L ^ r * L ^ n)) Q V
def ServingConstants (L n r : ℕ) (B₃ : ℝ) (c : MinimizerConstants) : Prop :=
  0 < c.a₀ ∧ 0 < c.a₁ ∧ B₃ * c.a₁ ≤ c.a₀ ∧ (∀ β₀, 0 < c.B₄ β₀) ∧
    ConclusionHoldsWith L n r c.a₀ c.a₁ B₃ c.B₄
def IsValidB₃ (L : ℕ) (B₃ : ℝ) (e₀ r₀ : ℕ) : Prop :=
  0 < B₃ ∧ ∀ n r : ℕ, e₀ ≤ n → r₀ ≤ r → ∃ c, ServingConstants L n r B₃ c
def b₃AndFloors (L : ℕ) : ℝ × ℕ × ℕ :=
  Classical.epsilon fun T : ℝ × ℕ × ℕ => IsValidB₃ L T.1 T.2.1 T.2.2
def b₃Const (L : ℕ) : ℝ := (b₃AndFloors L).1
def minimizerConstants (L n r : ℕ) : MinimizerConstants :=
  Classical.epsilon (ServingConstants L n r (b₃Const L))
end YangMills.Construction.BackgroundField.GreenBoundMinimizers
