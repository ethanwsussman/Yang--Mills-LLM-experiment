import YangMills.Construction.Conventions.TorusBoundDefs
import YangMills.Construction.Lattice.SumsOverTheScales
import YangMills.Construction.Lattice.SystemsOfRadiusInTheSettingOfTheTorusBound
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusBound
namespace ConstantParameters
variable (c : ConstantParameters)
def uvReal (d : ℝ) : ℝ := (c.uvConstant d).toReal
def volumeExponent : ℝ := max (c.Eplus + c.Clow) (1 / 2)
def partitionBound (ℓ : ℝ) : ℝ := Real.exp ((c.Eplus + c.Clow) * ℓ ^ 4)
def truncatedConstant (ϱ : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  (c.uvReal d + 4 ^ n * Real.log 2) * ((n : ℝ) / ϱ) ^ n
def mixedDerivCoeff (ϱ : ℝ) (n : ℕ) (d v : ℝ) : ℝ :=
  v * c.uvReal d * ((n : ℝ) / ϱ) ^ n
def truncatedCoeff (ϱ : ℝ) (n : ℕ) (d v Q : ℝ) : ℝ :=
  (v * c.uvReal d + Real.log 2 * (2 * Q + 2) ^ n) * ((n : ℝ) / ϱ) ^ n
def volumeCoeff (ϱ : ℝ) (n : ℕ) (d v : ℝ) : ℝ :=
  c.truncatedConstant ϱ n d * Real.exp (n * c.volumeExponent * v)
structure UVConstantWellBehaved : Prop where
  pos : ∀ d : ℝ, 0 < d → 0 < c.uvConstant d
  lt_top : ∀ d : ℝ, 0 < d → c.uvConstant d < ⊤
  antitoneOn : AntitoneOn c.uvConstant (Ioi 0)
  eq_of_params : ∀ c' : ConstantParameters, c'.L = c.L → c'.cubeSide = c.cubeSide → c'.Ce = c.Ce →
    c'.κe = c.κe → ∀ d : ℝ, 0 < d → c'.uvConstant d = c.uvConstant d
  satisfies : ∀ d : ℝ, 0 < d → c.SatisfiesUVBound d
  uvBound_eq_of_params : ∀ c' : ConstantParameters, c'.cubeSide = c.cubeSide → c'.Ce = c.Ce →
    c'.κe = c.κe → c'.uvBound = c.uvBound
end ConstantParameters
section Family
variable {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ} (e : D.RadiusFamily ϱ hϱ)
  {n : ℕ} (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f)
include hf in
theorem smear_mem_sources {z : Fin n → ℂ} (hz : z ∈ D.disc ϱ f) :
    D.smear z f ∈ D.sources ϱ :=
  (D.mem_sources_iff ϱ _).2 ⟨n, f, z, hf, hz, rfl⟩
open Classical in
def energyOnDisc (z : Fin n → ℂ) : ℂ :=
  if hz : z ∈ D.disc ϱ f then e.totalEnergy ⟨D.smear z f, smear_mem_sources f hf hz⟩ else 0
open Classical in
def partitionRatio (z : Fin n → ℂ) : ℂ :=
  if hz : z ∈ D.disc ϱ f then
    e.normalizedZ ⟨D.smear z f, smear_mem_sources f hf hz⟩ /
      e.normalizedZ (D.zeroSourceAt ϱ hϱ)
  else 0
def partitionRatioAsExpectation (z : Fin n → ℂ) : ℂ :=
  Complex.exp (-energyOnDisc e f hf z) *
    D.expect fun U => Complex.exp (∑ i, z i * ((D.obs (f i) U : ℝ) : ℂ))
structure Conclusions (c : ConstantParameters) : Prop where
  energy_holomorphic :
    ComplexVariables.IsHolomorphicScalar (D.disc ϱ f) (energyOnDisc e f hf)
  energy_zero : energyOnDisc e f hf 0 = 0
  mixed_bound : ∀ d : ℝ, 2 ≤ n → TestFunctions.HasSeparatedSupportsTorus f d →
    TorusBoundNotation.MixedDerivFormed (D.disc ϱ f) (energyOnDisc e f hf) ∧
      ‖TorusBoundNotation.mixedDeriv (energyOnDisc e f hf) 0‖ ≤
        c.mixedDerivCoeff ϱ n d (D.side ^ 4) * ∏ i, D.sharpNorm (f i)
  ratio_holomorphic :
    ComplexVariables.IsHolomorphicScalar (D.disc ϱ f) (partitionRatio e f hf)
  ratio_zero : partitionRatio e f hf 0 = 1
  ratio_bound : ∀ z ∈ D.disc ϱ f, ‖partitionRatio e f hf z‖ ≤ c.partitionBound D.side
  ratio_eq : ∀ z ∈ D.disc ϱ f, partitionRatio e f hf z = partitionRatioAsExpectation e f hf z
  one_le_partitionBound : 1 ≤ c.partitionBound D.side
  truncated_bound : ∀ d : ℝ, 2 ≤ n → TestFunctions.HasSeparatedSupportsTorus f d →
    ‖D.truncatedCorrelation f‖ ≤
      c.truncatedCoeff ϱ n d (D.side ^ 4) (c.partitionBound D.side) * ∏ i, D.sharpNorm (f i)
  volume_bound : ∀ d : ℝ, 2 ≤ n → 0 < d →
    c.truncatedCoeff ϱ n d (D.side ^ 4) (c.partitionBound D.side) * ∏ i, D.sharpNorm (f i) ≤
      c.volumeCoeff ϱ n d (D.side ^ 4) * ∏ i, D.sharpNorm (f i)
  eq_of_sum : ∀ c' : ConstantParameters, c'.Eplus + c'.Clow = c.Eplus + c.Clow →
    c'.volumeExponent = c.volumeExponent ∧ ∀ ℓ : ℝ, c'.partitionBound ℓ = c.partitionBound ℓ
  truncatedConstant_eq_of_params : ∀ c' : ConstantParameters, c'.L = c.L →
    c'.cubeSide = c.cubeSide → c'.Ce = c.Ce → c'.κe = c.κe → ∀ d : ℝ, 0 < d →
      c'.truncatedConstant ϱ n d = c.truncatedConstant ϱ n d
  truncatedConstant_antitoneOn : 2 ≤ n → AntitoneOn (c.truncatedConstant ϱ n) (Ioi 0)
end Family
def TorusBoundHolds : Prop :=
  (∀ c : ConstantParameters, c.UVConstantWellBehaved) ∧
    ∀ (D : Setup) (Ce κe Eplus Clow ϱ : ℝ) (hCe : 0 ≤ Ce)
      (hκe : PolymerActivities.DomainCounting.countingRate < κe)
      (hϱ : 0 < ϱ) (e : D.RadiusFamily ϱ hϱ),
      e.Local → e.Analytic → e.ExpBounded Ce κe →
        e.UpperStable Eplus → e.FloorBounded Clow →
        ∀ (n : ℕ) (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f),
          (∀ D' : Setup, D'.L = D.L → D'.cubeExp = D.cubeExp →
            ConstantParameters.ofSetup D' Ce κe Eplus Clow hCe hκe =
              ConstantParameters.ofSetup D Ce κe Eplus Clow hCe hκe) ∧
            Conclusions e f hf (ConstantParameters.ofSetup D Ce κe Eplus Clow hCe hκe)
end YangMills.Construction.TorusBound
end
