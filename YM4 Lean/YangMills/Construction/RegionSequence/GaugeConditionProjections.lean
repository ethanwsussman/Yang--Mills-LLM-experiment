import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
namespace NestedRegions
variable {𝒮 : NestedRegions}
def transferOp (ω : 𝒮.Coarse) : 𝒮.FineSite → ℝ := gaugeGreenOp (blockAvgAdj ω)
def transferAdj (f : 𝒮.FineSite → ℝ) : 𝒮.Coarse :=
  adjointValue univ coarseInner innerSum transferOp f
def transferGram (ω : 𝒮.Coarse) : 𝒮.Coarse := transferAdj (transferOp ω)
def avgGreenSq (ω : 𝒮.Coarse) : 𝒮.Coarse :=
  blockAvg (gaugeGreenOp (gaugeGreenOp (blockAvgAdj ω)))
def transferGramInv (ω : 𝒮.Coarse) : 𝒮.Coarse :=
  inverseValue univ transferGram ω
def avgGreenSqInv (ω : 𝒮.Coarse) : 𝒮.Coarse :=
  inverseValue univ avgGreenSq ω
variable (𝒮) in
def innerNbhd : Set 𝒮.FineSite :=
  {x | (x : 𝒮.Point) ∈ 𝒮.Ω 1 ∨ ∃ x' : 𝒮.FineSite, (x' : 𝒮.Point) ∈ 𝒮.Ω 1 ∧ IsNeighbor x x'}
def fineBlockMean (n : ℕ) (y : 𝒮.Point) (f : 𝒮.FineSite → ℝ) : ℝ :=
  ((𝒮.L : ℝ) ^ (n * 4))⁻¹ * ∑ᶠ x ∈ 𝒮.fineBlock n y, f x
variable (𝒮) in
def zeroMeanOnInner : Set (𝒮.FineSite → ℝ) :=
  {f | VanishesOff (𝒮.Ω 1) f ∧ ∀ n, 1 ≤ n → ∀ y ∈ 𝒮.centresAt n, fineBlockMean n y f = 0}
end NestedRegions
structure BaseReplacement (𝒮 : NestedRegions) where
  newBase : Set 𝒮.Point
  newBonds : Set 𝒮.FineBond
  Ω_one_subset : 𝒮.Ω 1 ⊆ newBase
  isCubeUnion : IsCubeUnion (𝒮.scale 0) newBase
  mem_newBonds_of_mem : ∀ b : 𝒮.FineBond,
    (b.source : 𝒮.Point) ∈ newBase → (b.target : 𝒮.Point) ∈ newBase → b ∈ newBonds
  mem_of_mem_newBonds : ∀ b ∈ newBonds,
    (b.source : 𝒮.Point) ∈ newBase ∨ (b.target : 𝒮.Point) ∈ newBase
def BaseReplacement.toNestedRegions {𝒮 : NestedRegions} (c : BaseReplacement 𝒮) : NestedRegions where
  L := 𝒮.L
  odd_L := 𝒮.odd_L
  thirteen_le_L := 𝒮.thirteen_le_L
  ξ := 𝒮.ξ
  ξ_pos := 𝒮.ξ_pos
  side := 𝒮.side
  side_pos := 𝒮.side_pos
  s := 𝒮.s
  side_mem_zmultiples := 𝒮.side_mem_zmultiples
  Ω := Function.update 𝒮.Ω 0 c.newBase
  Ω_succ_subset := fun n hn => by
    cases n with
    | zero => simpa using c.Ω_one_subset
    | succ m => simpa using 𝒮.Ω_succ_subset (m + 1) hn
  isCubeUnion_Ω := fun n hn => by
    cases n with
    | zero => simpa [NestedRegions.scale] using c.isCubeUnion
    | succ m => simpa using 𝒮.isCubeUnion_Ω (m + 1) hn
  Ω_eq_empty := fun n hn => by
    have h0 : n ≠ 0 := by omega
    simpa [h0] using 𝒮.Ω_eq_empty n hn
  bonds := c.newBonds
  mem_bonds_of_mem := fun b h₁ h₂ => by
    simpa using c.mem_newBonds_of_mem b (by simpa using h₁) (by simpa using h₂)
  mem_of_mem_bonds := fun b hb => by simpa using c.mem_of_mem_newBonds b hb
namespace GaugeProjections
open NestedRegions
structure TransferRange (𝒮 : NestedRegions) : Prop where
  transferOp_mem : ∀ ω : 𝒮.Coarse, transferOp ω ∈ 𝒮.siteFns
  transferOp_injective : Function.Injective (transferOp (𝒮 := 𝒮))
  transferGram_bijective : Function.Bijective (transferGram (𝒮 := 𝒮))
  avgGreenSq_bijective : Function.Bijective (avgGreenSq (𝒮 := 𝒮))
  transferGramInv_eq : ∀ ω : 𝒮.Coarse, transferGramInv ω = avgGreenSqInv ω
  complProj_eq_transfer : ∀ f ∈ 𝒮.siteFns, complProj f =
    transferOp (transferGramInv (transferAdj f))
  complProj_eq_green : ∀ f ∈ 𝒮.siteFns, complProj f =
    gaugeGreenOp (blockAvgAdj (avgGreenSqInv (blockAvg (gaugeGreenOp f))))
  rangeProj_transferOp : ∀ ω : 𝒮.Coarse, rangeProj (transferOp ω) = 0
end GaugeProjections
end YangMills.Construction.RegionSequence
