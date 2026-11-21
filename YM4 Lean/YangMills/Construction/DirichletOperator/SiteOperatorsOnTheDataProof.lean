import YangMills.Construction.DirichletOperator.BoundsOnTheOperatorsOfASeparatedSequenceProof
import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNorms
import YangMills.Construction.Torus.OperatorsOfAnAdmissiblePair
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence.TorusDataComparison
variable {𝒮 : NestedRegions} {M R₁ : ℕ} {h : 𝒮.IsTorusData M R₁}
theorem dataScale_zero : h.toTorusData.scale 0 = 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.scale_zero <;> assumption
theorem mem_spacingLattice_iff (p : 𝒮.Point) :
    p ∈ Torus.spacingLattice 4 𝒮.side 𝒮.ξ ↔
      p ∈ h.toTorusData.latticeAt (h.toTorusData.scale 0) := by
  rw [dataScale_zero]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    funext μ
    show (((k μ : ℝ) * 𝒮.ξ : ℝ) : AddCircle 𝒮.side) = ((𝒮.ξ * (k μ : ℝ) : ℝ) : AddCircle 𝒮.side)
    rw [mul_comm]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    funext μ
    show ((𝒮.ξ * (k μ : ℝ) : ℝ) : AddCircle 𝒮.side) = (((k μ : ℝ) * 𝒮.ξ : ℝ) : AddCircle 𝒮.side)
    rw [mul_comm]
def fineSiteEquiv (h : 𝒮.IsTorusData M R₁) : 𝒮.FineSite ≃ h.toTorusData.BareSite where
  toFun x := ⟨x.1, (mem_spacingLattice_iff (h := h) x.1).1 x.2⟩
  invFun x := ⟨x.1, (mem_spacingLattice_iff (h := h) x.1).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable {B : Weighted.SeparatedChain h.toTorusData}
theorem mem_bareSites_stage_zero_iff (hmem : B.stage = 𝒮.Ω) (x : 𝒮.FineSite) :
    fineSiteEquiv h x ∈ h.toTorusData.bareSites (B.stage 0) ↔ (x : 𝒮.Point) ∈ 𝒮.Ω 0 := by
  show (x : 𝒮.Point) ∈ B.stage 0 ↔ _
  rw [hmem]
  exact Iff.rfl
theorem level_eq (hsame : NestedRegions.AgreesWithTorusData B) (y : 𝒮.Point) :
    𝒮.level y = B.level y := by
  have hset : {n | y ∈ 𝒮.centresAt n} = {n | y ∈ B.layerSites n} := by
    ext n
    show y ∈ 𝒮.centresAt n ↔ y ∈ B.layerSites n
    rw [hsame.centres_data n]
    exact Iff.rfl
  exact congrArg sInf hset
theorem centreOfSite_eq (hsame : NestedRegions.AgreesWithTorusData B) (x : 𝒮.FineSite) :
    𝒮.centreOfSite x = B.blockCenter (fineSiteEquiv h x) := by
  have hp : (fun y : 𝒮.Point => y ∈ 𝒮.allCentres ∧ (x : 𝒮.Point) ∈ 𝒮.cellOf y) =
      fun y : h.toTorusData.Space => y ∈ B.allSites ∧ fineSiteEquiv h x ∈ B.block y := by
    funext y
    apply propext
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨hsame.allCentres_data ▸ h₁, ?_⟩
      show (x : 𝒮.Point) ∈ B.siteCube y
      rw [← hsame.cell_data y h₁]
      exact h₂
    · rintro ⟨h₁, h₂⟩
      have h₁' : y ∈ 𝒮.allCentres := hsame.allCentres_data.symm ▸ h₁
      refine ⟨h₁', ?_⟩
      rw [hsame.cell_data y h₁']
      exact h₂
  unfold NestedRegions.centreOfSite Weighted.SeparatedChain.blockCenter
  exact congrArg (fun p => @Classical.epsilon 𝒮.Point ⟨0⟩ p) hp
theorem layerEval_of_mem (w : B.LayerFn) {y : h.toTorusData.Space} (hy : y ∈ B.allSites) :
    B.layerEval w y = w ⟨y, hy⟩ :=
  dif_pos hy
theorem blockAvgAdj_eq (hadj : CellStructure.AdjointFacts 𝒮) (hmem : B.stage = 𝒮.Ω)
    (hsame : NestedRegions.AgreesWithTorusData B) {ω : 𝒮.Coarse} {ω' : B.LayerFn}
    (hω : EqOnLayerSites B ω ω') (x : 𝒮.FineSite) :
    NestedRegions.blockAvgAdj ω x =
      (B.avgOpAdjoint ω' : h.toTorusData.BareSite → ℝ) (fineSiteEquiv h x) := by
  obtain ⟨hin, hval⟩ := hadj.avgAdj_apply ω
  have hin' : Dirichlet.VanishesOff (𝒮.Ω 0) (NestedRegions.blockAvgAdj ω) := hin
  by_cases hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0
  · obtain ⟨hc, hv⟩ := hval x hx
    rw [hv]
    have hx' : fineSiteEquiv h x ∈ h.toTorusData.bareSites (B.stage 0) :=
      (mem_bareSites_stage_zero_iff hmem x).2 hx
    have hc' : B.blockCenter (fineSiteEquiv h x) ∈ B.allSites := by
      rw [← centreOfSite_eq hsame x]
      exact hsame.allCentres_data ▸ hc
    have hT : (B.avgOpAdjoint ω' : h.toTorusData.BareSite → ℝ) (fineSiteEquiv h x) =
        B.layerEval ω' (B.blockCenter (fineSiteEquiv h x)) :=
      indicator_of_mem hx' fun x => B.layerEval ω' (B.blockCenter x)
    rw [hT, layerEval_of_mem _ hc']
    exact hω ⟨_, hc⟩ ⟨_, hc'⟩ (centreOfSite_eq hsame x)
  · rw [hin' x hx]
    exact ((B.avgOpAdjoint ω').2 _ fun hc => hx ((mem_bareSites_stage_zero_iff hmem x).1 hc)).symm
end YangMills.Construction.RegionSequence.TorusDataComparison
