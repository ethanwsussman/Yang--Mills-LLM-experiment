import YangMills.Construction.FreeEnergiesOfTheFlow.ScoresOverAStepDefs
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace FreeEnergies
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def liveCaseFunction (F : CaseFunction R n) : CaseFunction R n :=
  fun W Yt ωt bad b => if IsLiveState R.params R.coupling R.labelWeight W Yt ωt then F W Yt ωt bad b else 0
def lowerSites (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    Finset (TorusSite (n * R.params.side)) :=
  weightSupportSites R.params.side R.depth (n * R.params.side) f
def upperSites (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : Finset (TorusSite n) :=
  weightSupportSites R.params.side (R.depth + 1) n f
theorem parentBlocks_lowerSites (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    parentBlocks (lowerSites f) = upperSites f := by
  classical
  ext Y
  unfold parentBlocks lowerSites upperSites weightSupportSites
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨p, ⟨ho, c, hc, hb⟩, hp⟩, rfl⟩
    exact ⟨p, ⟨ho, c, hc, Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr rfl⟩, hb⟩⟩, hp⟩
  · rintro ⟨p, ⟨ho, c, hc, hb⟩, hp⟩
    obtain ⟨y, hy, hb'⟩ := Finset.mem_biUnion.mp hb
    exact ⟨y, ⟨p, ⟨ho, c, hc, hb'⟩, hp⟩, Finset.mem_singleton.mp (Finset.mem_filter.mp hy).2⟩
structure WellSeparated {ι : Type} (I : Finset ι) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (D : ℕ) : Prop where
  norm_le : ∀ i ∈ I, weightNorm R.params.side (R.depth + 1) (f i) ≤ 1
  lower_norm_le : ∀ i ∈ I, weightNorm R.params.side R.depth (f i) ≤ 1
  nonempty : ∀ i ∈ I, (upperSites (f i)).Nonempty
  range_le : 2 ^ 10 * R.range ≤ D
  eight_lt : 8 < D
  separated : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ thickening 2 (upperSites (f i)),
    ∀ Y' ∈ thickening 2 (upperSites (f j)), D ≤ supDist Y Y'
def settingMean (s : ChartSetting R n) (bad : Finset (TorusBond (n * R.params.side))) (F : CaseFunction R n) : ℝ :=
  weightedMean (chartDensity s) fun η => F (s.field η) s.support s.labelling bad s.bases
def gasSupportMean (A : ResponseSetup R) (G : GasGround R n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (σ : G.Config) : ℝ :=
  settingMean (configSetting G σ) (G.badBondsOf σ) (liveCaseFunction (centeredSupportResponse A G.coarse f))
def gasMeanSiteScore (A : ResponseSetup R) (G : GasGround R n) (B : Finset (TorusSite (n * R.params.side)))
    (σ : G.Config) : ℝ :=
  meanSiteScore A.score B (configSetting G σ).support (configSetting G σ).labelling
def lowerSizeConst (A : ResponseSetup R) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : ℝ :=
  A.responseParams.C₀ * ((lowerSites f).card : ℝ)
end FreeEnergies
end YangMills.Construction
end
