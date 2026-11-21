import YangMills.Construction.Conventions.TorusBoundDefs
import YangMills.Construction.Lattice.ConstantsOfTheTorusBound
import YangMills.Construction.Lattice.SystemsOfRadiusInTheSettingOfTheTorusBound
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TotalEnergyDerivative
open TorusBound
variable {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ} {n : ℕ}
open Classical in
def diskEnergy (e : D.RadiusFamily ϱ hϱ) (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f)
    (z : Coordinates.ComplexCoordinates n) : ℂ :=
  if hz : z ∈ D.disc ϱ f then
    e.totalEnergy ⟨D.smear z f, (D.mem_sources_iff ϱ _).2 ⟨n, f, z, hf, hz, rfl⟩⟩
  else 0
theorem diskEnergy_of_mem (e : D.RadiusFamily ϱ hϱ) (f : Fin n → D.Torus → ℝ)
    (hf : D.IsRealFamily f) {z : Coordinates.ComplexCoordinates n} (hz : z ∈ D.disc ϱ f) :
    diskEnergy e f hf z =
      e.totalEnergy ⟨D.smear z f, (D.mem_sources_iff ϱ _).2 ⟨n, f, z, hf, hz, rfl⟩⟩ :=
  dif_pos hz
def sharpNormFactor (D : Setup) (ϱ : ℝ) (f : Fin n → D.Torus → ℝ) : ℝ :=
  ((n : ℝ) / ϱ) ^ n * ∏ i, D.sharpNorm (f i)
def MixedDerivBound : Prop :=
  ∀ (D : Setup) (ϱ : ℝ) (hϱ : 0 < ϱ) (Ce κe : ℝ) (hCe : 0 ≤ Ce)
    (hκe : PolymerActivities.DomainCounting.countingRate < κe)
    (e : D.RadiusFamily ϱ hϱ), e.Local → e.Analytic → e.ExpBounded Ce κe →
    ∀ (n : ℕ) (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f),
      ComplexVariables.IsHolomorphicScalar (D.disc ϱ f) (diskEnergy e f hf) ∧
        diskEnergy e f hf 0 = 0 ∧
        ∀ (hn : 2 ≤ n) (d : ℝ), TestFunctions.HasSeparatedSupportsTorus f d →
          ENNReal.ofReal ‖TorusBoundNotation.mixedDeriv (diskEnergy e f hf) 0‖ ≤
              ENNReal.ofReal (D.side ^ 4) *
                  (ConstantParameters.ofSetup D Ce κe 0 0 hCe hκe).uvConstant d *
                ENNReal.ofReal (sharpNormFactor D ϱ f) ∧
            ∀ R : ℝ, 0 < R →
              (∃ B, D.IsBallOfRadius R B ∧ ∀ y, y ∉ B → f ⟨0, by omega⟩ y = 0) →
              ENNReal.ofReal ‖TorusBoundNotation.mixedDeriv (diskEnergy e f hf) 0‖ ≤
                (ConstantParameters.ofSetup D Ce κe 0 0 hCe hκe).uvConstantInBall d R *
                  ENNReal.ofReal (sharpNormFactor D ϱ f)
end YangMills.Construction.TotalEnergyDerivative
end
