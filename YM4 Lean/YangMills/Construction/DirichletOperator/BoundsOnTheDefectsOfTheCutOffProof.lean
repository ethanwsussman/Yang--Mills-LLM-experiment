import YangMills.Construction.DirichletOperator.BoundsOnTheDefectsOfTheCutOff
import YangMills.Construction.DirichletOperator.CellsCommonToACubeAndItsTorusProof
import YangMills.Construction.DirichletOperator.CubeNearASiteProof
import YangMills.Construction.DirichletOperator.DivergenceRuleOnTheCubesProof
import YangMills.Construction.DirichletOperator.PropagatorBoundsOnTheAdjointSeriesProof
import YangMills.Construction.DirichletOperator.WeightedDistanceNearALayerSiteProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
open scoped ENNReal
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.CubeTorusComparison
open YangMills.Construction.DirichletGreen (fieldModulusAt)
noncomputable section
namespace YangMills.Construction.CubeTorusComparison.CutoffDefects
variable {𝒮 : NestedRegions} {M : ℕ}
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_piSingle_le {ξ : ℝ} (hξ : 0 ≤ ξ) (ν : Fin 4) :
    ‖(Pi.single ν ξ : Fin 4 → ℝ)‖ ≤ ξ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.norm_pi_single_le <;> assumption
theorem norm_unitStep_le (ν : Fin 4) : ‖(unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)‖ ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeDivergence.norm_unitStep_le <;> assumption
theorem supSetDist_singleton_le_add {S : ℝ} (A : Set (PeriodicTorus 4 S))
    (x x' : PeriodicTorus 4 S) :
    supSetDist {x'} A ≤ supSetDist {x} A + ENNReal.ofReal ‖x' - x‖ := by
  rw [← tsub_le_iff_right]
  refine le_iInf₂ fun p hp => le_iInf₂ fun q hq => ?_
  obtain rfl : p = x := hp
  rw [tsub_le_iff_right]
  have h₀ : supSetDist {x'} A ≤ ENNReal.ofReal (supNorm (x' - q)) :=
    iInf₂_le_of_le x' rfl (iInf₂_le q hq)
  refine h₀.trans ?_
  rw [supNorm_eq_norm, supNorm_eq_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : x' - q = (p - q) + (x' - p) := by abel
  rw [e]
  exact norm_add_le _ _
theorem mem_thicken_of_near (Q : LevelCube 𝒮 M) {ς ς' : ℝ} {x x' : 𝒮.Point}
    (hς : 0 ≤ ς * mollifyRadius 𝒮 M Q.level) (hx : x ∈ Q.thicken ς)
    (h : ς * mollifyRadius 𝒮 M Q.level + ‖x' - x‖ ≤ ς' * mollifyRadius 𝒮 M Q.level) :
    x' ∈ Q.thicken ς' := by
  have h₁ := supSetDist_singleton_le_add Q.supp x x'
  have hx' : supSetDist {x} Q.supp ≤ ENNReal.ofReal (ς * mollifyRadius 𝒮 M Q.level) := hx
  change supSetDist {x'} Q.supp ≤ ENNReal.ofReal (ς' * mollifyRadius 𝒮 M Q.level)
  refine h₁.trans ((add_le_add_left hx' _).trans ?_)
  rw [← ENNReal.ofReal_add hς (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h
theorem finite_fineSite (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem spacingLattice_scale_subset (𝒯 : NestedRegions) (i j : ℕ) (h : i ≤ j) :
    (spacingLattice 4 𝒯.side (𝒯.scale j) : Set 𝒯.Point) ⊆ spacingLattice 4 𝒯.side (𝒯.scale i) := by
  rintro x ⟨k, rfl⟩
  refine ⟨fun μ => k μ * (𝒯.L : ℤ) ^ (j - i), ?_⟩
  funext μ
  have : 𝒯.scale j = (𝒯.L : ℝ) ^ (j - i) * 𝒯.scale i := by
    simp only [scale_eq_pow_mul]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  simp only [torusProj, this]
  push_cast
  ring_nf
theorem scale_zero (𝒯 : NestedRegions) : 𝒯.scale 0 = 𝒯.ξ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.scale_zero <;> assumption
theorem scale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem eq_of_mem_spacingLattice_of_near {S σ : ℝ} (hσ : 0 < σ) (N : ℤ) (hS : S = (N : ℝ) * σ)
    {x y : PeriodicTorus 4 S} (hx : x ∈ spacingLattice 4 S σ) (hy : y ∈ spacingLattice 4 S σ)
    (h : ‖x - y‖ ≤ σ / 2) : x = y := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  funext μ
  have h₁ : ‖((((k μ - l μ : ℤ) : ℝ) * σ : ℝ) : AddCircle S)‖ ≤ σ / 2 := by
    refine le_trans (le_of_eq ?_) ((norm_le_pi_norm _ μ).trans h)
    congr 1
    simp only [torusProj, Pi.sub_apply]
    push_cast
    rw [sub_mul, AddCircle.coe_sub]
  rw [AddCircle.norm_eq] at h₁
  set m : ℤ := round (S⁻¹ * (((k μ - l μ : ℤ) : ℝ) * σ)) with hm
  have h₂ : |(((k μ - l μ - m * N : ℤ) : ℝ))| * σ ≤ σ / 2 := by
    have e : ((k μ - l μ : ℤ) : ℝ) * σ - (m : ℝ) * S = (((k μ - l μ - m * N : ℤ) : ℝ)) * σ := by
      rw [hS]
      push_cast
      ring
    rw [e, abs_mul, abs_of_pos hσ] at h₁
    exact h₁
  have h₃ : |(((k μ - l μ - m * N : ℤ) : ℝ))| < 1 := by
    by_contra hc
    have := not_lt.mp hc
    nlinarith
  have h₄ : k μ - l μ - m * N = 0 := by
    have : |k μ - l μ - m * N| < 1 := by exact_mod_cast h₃
    exact Int.abs_lt_one_iff.mp this
  have h₅ : k μ = l μ + m * N := by omega
  simp only [torusProj]
  rw [h₅]
  push_cast
  have e : ((l μ : ℝ) + (m : ℝ) * (N : ℝ)) * σ = (l μ : ℝ) * σ + (m : ℝ) * S := by
    rw [hS]
    ring
  rw [e, AddCircle.coe_add]
  have : (((m : ℝ) * S : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨m, by simp⟩
  rw [this, add_zero]
theorem exists_side_eq_mul_scale (𝒯 : NestedRegions) (j : ℕ) (h : j ≤ 𝒯.s) :
    ∃ N : ℤ, 𝒯.side = (N : ℝ) * 𝒯.scale j := by apply _root_.YangMills.Construction.PartitionCubes.SharedCellsProof.side_mem_zmultiples_scale <;> assumption
theorem latticeLaplacian_apply {S ξ : ℝ} (f : LatticeSite 4 S ξ → ℝ) (x : LatticeSite 4 S ξ) :
    latticeLaplacian f x =
      ∑ ν, (ξ ^ 2)⁻¹ * (2 * f x - f (x + unitStep 4 S ξ ν) - f (x - unitStep 4 S ξ ν)) := by
  simp only [latticeLaplacian, latticeDiv, Dirichlet.grad, backwardDiff, forwardDiff, sub_add_cancel]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [pow_two, mul_inv]
  ring
theorem latticeLaplacian_congr {S ξ : ℝ} {f g : LatticeSite 4 S ξ → ℝ} {x : LatticeSite 4 S ξ}
    (h₀ : f x = g x) (h₁ : ∀ ν, f (x + unitStep 4 S ξ ν) = g (x + unitStep 4 S ξ ν))
    (h₂ : ∀ ν, f (x - unitStep 4 S ξ ν) = g (x - unitStep 4 S ξ ν)) :
    latticeLaplacian f x = latticeLaplacian g x := by
  simp only [latticeLaplacian_apply, h₀, h₁, h₂]
def levelWeight (𝒯 : NestedRegions) (y : 𝒯.Point) : ℝ :=
  blockWeights 𝒯.L (𝒯.level y) * (𝒯.scale (𝒯.level y) ^ 2)⁻¹ *
    ((𝒯.L : ℝ) ^ (𝒯.level y * 4))⁻¹
def gaugeStencil (𝒯 : NestedRegions) (G : 𝒯.FineSite → ℝ) (x : 𝒯.FineSite) : ℝ :=
  latticeLaplacian G x + levelWeight 𝒯 (𝒯.centreOfSite x) *
    ∑ᶠ x' ∈ 𝒯.fineBlock (𝒯.level (𝒯.centreOfSite x)) (𝒯.centreOfSite x), G x'
theorem blockAvgAdj_weightMul_apply {𝒯 : NestedRegions} (A : CellStructure.AdjointFacts 𝒯)
    (G : 𝒯.FineSite → ℝ) (x : 𝒯.FineSite) (hx : (x : 𝒯.Point) ∈ 𝒯.Ω 0) :
    blockAvgAdj (weightMul (blockAvg G)) x =
      levelWeight 𝒯 (𝒯.centreOfSite x) *
        ∑ᶠ x' ∈ 𝒯.fineBlock (𝒯.level (𝒯.centreOfSite x)) (𝒯.centreOfSite x), G x' := by
  obtain ⟨h, e⟩ := (A.avgAdj_apply (weightMul (blockAvg G))).2 x hx
  rw [e]
  simp only [weightMul, blockAvg, levelWeight]
  ring
theorem gaugeLap_eq_gaugeStencil {𝒯 : NestedRegions} (A : CellStructure.AdjointFacts 𝒯)
    (G : 𝒯.FineSite → ℝ) (x : 𝒯.FineSite) (hx : (x : 𝒯.Point) ∈ 𝒯.Ω 0)
    (h₁ : ∀ ν, ((x + unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) ∈ 𝒯.Ω 0 ∨
      G (x + unitStep 4 𝒯.side 𝒯.ξ ν) = 0)
    (h₂ : ∀ ν, ((x - unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) ∈ 𝒯.Ω 0 ∨
      G (x - unitStep 4 𝒯.side 𝒯.ξ ν) = 0) :
    gaugeLap G x = gaugeStencil 𝒯 G x := by
  have hchi : ∀ x' : 𝒯.FineSite, ((x' : 𝒯.Point) ∈ 𝒯.Ω 0 ∨ G x' = 0) →
      projSites G x' = G x' := by
    intro x' h
    rcases h with h | h
    · exact indicator_of_mem (s := {x : 𝒯.FineSite | (x : 𝒯.Point) ∈ 𝒯.Ω 0}) h G
    · by_cases h' : (x' : 𝒯.Point) ∈ 𝒯.Ω 0
      · exact indicator_of_mem (s := {x : 𝒯.FineSite | (x : 𝒯.Point) ∈ 𝒯.Ω 0}) h' G
      · rw [h]
        exact indicator_of_notMem (s := {x : 𝒯.FineSite | (x : 𝒯.Point) ∈ 𝒯.Ω 0}) h' G
  have e₁ : dirichletLap G x = latticeLaplacian G x := by
    have : dirichletLap G x = latticeLaplacian (projSites G) x :=
      indicator_of_mem (s := {x : 𝒯.FineSite | (x : 𝒯.Point) ∈ 𝒯.Ω 0}) hx _
    rw [this]
    exact latticeLaplacian_congr (hchi _ (Or.inl hx)) (fun ν => hchi _ (h₁ ν))
      fun ν => hchi _ (h₂ ν)
  simp only [gaugeLap, Pi.add_apply, e₁, blockAvgAdj_weightMul_apply A G x hx, gaugeStencil]
def cutoffDefect (𝒯 : NestedRegions) (φ F : 𝒯.FineSite → ℝ) (u : 𝒯.FineSite) : ℝ :=
  φ u * gaugeStencil 𝒯 F u - gaugeStencil 𝒯 (fun x => φ x * F x) u
theorem mem_cellAndNeighbours_of_mem_fineBlock (u x : 𝒮.FineSite)
    (h : x ∈ 𝒮.fineBlock (𝒮.level (𝒮.centreOfSite u)) (𝒮.centreOfSite u)) :
    x ∈ cellAndNeighbours u := Or.inl h
theorem add_mem_cellAndNeighbours (u : 𝒮.FineSite) (ν : Fin 4) :
    u + unitStep 4 𝒮.side 𝒮.ξ ν ∈ cellAndNeighbours u := Or.inr ⟨ν, Or.inl rfl⟩
theorem sub_mem_cellAndNeighbours (u : 𝒮.FineSite) (ν : Fin 4) :
    u - unitStep 4 𝒮.side 𝒮.ξ ν ∈ cellAndNeighbours u := Or.inr ⟨ν, Or.inr rfl⟩
theorem gaugeStencil_congr {F G : 𝒮.FineSite → ℝ} {u : 𝒮.FineSite} (hu : u ∈ cellAndNeighbours u)
    (h : ∀ x ∈ cellAndNeighbours u, F x = G x) : gaugeStencil 𝒮 F u = gaugeStencil 𝒮 G u := by
  simp only [gaugeStencil]
  rw [latticeLaplacian_congr (h _ hu) (fun ν => h _ (add_mem_cellAndNeighbours u ν))
    fun ν => h _ (sub_mem_cellAndNeighbours u ν)]
  congr 1
  congr 1
  exact finsum_mem_congr rfl fun x hx => h x (mem_cellAndNeighbours_of_mem_fineBlock u x hx)
theorem cutoffDefect_eq_zero_of_const (hl : TorusLengthsStatement) {φ F : 𝒮.FineSite → ℝ}
    {u : 𝒮.FineSite} (hu : u ∈ cellAndNeighbours u)
    (h : ∀ x ∈ cellAndNeighbours u, φ x = φ u) :
    cutoffDefect 𝒮 φ F u = 0 := by
  have := finite_fineSite hl 𝒮
  have e : gaugeStencil 𝒮 (fun x => φ x * F x) u = gaugeStencil 𝒮 (fun x => φ u * F x) u :=
    gaugeStencil_congr hu fun x hx => by simp only [h x hx]
  rw [cutoffDefect, e]
  simp only [gaugeStencil]
  have e₁ : latticeLaplacian (fun x => φ u * F x) u = φ u * latticeLaplacian F u := by
    simp only [latticeLaplacian_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have e₂ : ∑ᶠ x' ∈ 𝒮.fineBlock (𝒮.level (𝒮.centreOfSite u)) (𝒮.centreOfSite u), φ u * F x' =
      φ u * ∑ᶠ x' ∈ 𝒮.fineBlock (𝒮.level (𝒮.centreOfSite u)) (𝒮.centreOfSite u), F x' :=
    (mul_finsum_mem' F (φ u) (Set.toFinite _)).symm
  rw [e₁, e₂]
  ring
section Cells
variable {𝒯 : NestedRegions}
theorem levelScale_eq (y : 𝒯.Point) : 𝒯.levelScale y = 𝒯.scale (𝒯.level y) := rfl
theorem norm_sub_le_of_mem_cellOf {x y : 𝒯.Point} (h : x ∈ 𝒯.cellOf y) :
    ‖x - y‖ ≤ 𝒯.levelScale y / 2 := by
  have h' : supNorm (x - y) ≤ 𝒯.levelScale y / 2 := h
  rwa [supNorm_eq_norm] at h'
theorem mem_cellOf_self (y : 𝒯.Point) : y ∈ 𝒯.cellOf y := by
  change supNorm (y - y) ≤ 𝒯.levelScale y / 2
  rw [sub_self, supNorm_eq_norm, norm_zero, levelScale_eq]
  linarith [scale_pos 𝒯 (𝒯.level y)]
theorem mem_centresAt_level {y : 𝒯.Point} (h : y ∈ 𝒯.allCentres) :
    y ∈ 𝒯.centresAt (𝒯.level y) := by apply _root_.YangMills.Construction.CubeNearSite.mem_centresAt_level <;> assumption
theorem mem_spacingLattice_of_mem_centresAt {y : 𝒯.Point} {n : ℕ} (h : y ∈ 𝒯.centresAt n) :
    y ∈ spacingLattice 4 𝒯.side (𝒯.scale n) := h.2.1
theorem le_s_of_mem_centresAt {y : 𝒯.Point} {n : ℕ} (h : y ∈ 𝒯.centresAt n) : n ≤ 𝒯.s := by apply _root_.YangMills.Construction.PartitionCubes.WeightedDistNearShell.le_s_of_mem_centresAt <;> assumption
theorem mem_allCentres_of_mem_centresAt {y : 𝒯.Point} {n : ℕ} (h : y ∈ 𝒯.centresAt n) :
    y ∈ 𝒯.allCentres :=
  ⟨n, le_s_of_mem_centresAt h, h⟩
theorem mem_spacingLattice_of_mem_allCentres {y : 𝒯.Point} (h : y ∈ 𝒯.allCentres) :
    y ∈ spacingLattice 4 𝒯.side 𝒯.ξ := by apply _root_.YangMills.Construction.BaseOperatorCoercivity.allCentres_subset_spacingLattice <;> assumption
theorem cellOf_subset_Ω_zero (C : CellStructure.CellFacts 𝒯) {y : 𝒯.Point}
    (h : y ∈ 𝒯.allCentres) : 𝒯.cellOf y ⊆ 𝒯.Ω 0 := by apply _root_.YangMills.Construction.AdjointNeumannBounds.cellOf_subset_Ω_zero <;> assumption
theorem centreOfSite_spec (C : CellStructure.CellFacts 𝒯) (x : 𝒯.FineSite)
    (hx : (x : 𝒯.Point) ∈ 𝒯.Ω 0) :
    𝒯.centreOfSite x ∈ 𝒯.allCentres ∧ (x : 𝒯.Point) ∈ 𝒯.cellOf (𝒯.centreOfSite x) := by
  obtain ⟨y, hy, hi, -⟩ := C.fine_site x hx
  exact Classical.epsilon_spec (p := fun y => y ∈ 𝒯.allCentres ∧ (x : 𝒯.Point) ∈ 𝒯.cellOf y)
    ⟨y, hy, interior_subset hi⟩
theorem centreOfSite_eq (C : CellStructure.CellFacts 𝒯) (x : 𝒯.FineSite) {y : 𝒯.Point}
    (hy : y ∈ 𝒯.allCentres) (hxy : (x : 𝒯.Point) ∈ 𝒯.cellOf y) : 𝒯.centreOfSite x = y := by
  have hx := cellOf_subset_Ω_zero C hy hxy
  obtain ⟨y₀, hy₀, -, hu⟩ := C.fine_site x hx
  have h := centreOfSite_spec C x hx
  rw [hu _ h.1 h.2, hu y hy hxy]
theorem Ω_antitone {i k : ℕ} (h : i ≤ k) (hk : k ≤ 𝒯.s) : 𝒯.Ω k ⊆ 𝒯.Ω i := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.Ω_antitone <;> assumption
theorem level_eq_of_mem_centresAt (C : CellStructure.CellFacts 𝒯) {y : 𝒯.Point} {k : ℕ}
    (h : y ∈ 𝒯.centresAt k) : 𝒯.level y = k := by
  have hk := le_s_of_mem_centresAt h
  have hy := mem_allCentres_of_mem_centresAt h
  have hle : 𝒯.level y ≤ k := Nat.sInf_le (s := {n | y ∈ shellSites 𝒯.L 𝒯.ξ 𝒯.Ω n}) h
  by_contra hne
  have hlt : 𝒯.level y < k := lt_of_le_of_ne hle hne
  set j := 𝒯.level y with hj
  have hjs : j ≤ 𝒯.s := by omega
  have hyj := mem_centresAt_level hy
  have hmem : 𝒯.cellOf y ∈ CellStructure.shellCubes 𝒯 j := by
    rw [C.shellCubes_eq j hjs]
    exact ⟨y, hyj, rfl⟩
  have hdis := C.interior_disjoint j hjs (𝒯.cellOf y) hmem
  have hyΩ : y ∈ 𝒯.Ω k := ((C.cell_subset k hk y h).2 h.2.2).1
  have hyΩ' : y ∈ 𝒯.Ω (j + 1) := Ω_antitone (by omega) hk hyΩ
  have hint : y ∈ interior (𝒯.cellOf y) := by
    obtain ⟨y₂, hy₂, hi, hu⟩ := C.fine_site ⟨y, mem_spacingLattice_of_mem_allCentres hy⟩
      (cellOf_subset_Ω_zero C hy (mem_cellOf_self y))
    rwa [← hu y hy (mem_cellOf_self y)] at hi
  exact disjoint_left.mp hdis hint hyΩ'
end Cells
theorem exists_rep_mem_Ico {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    ∃ v : ℝ, v ∈ Ico (-(S / 2)) (S / 2) ∧ (v : AddCircle S) = θ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_centred_rep <;> assumption
structure FirstTypeData (c : ℝ) (Q : LevelCube 𝒮 M) : Prop where
  cells : CellStructure.CellStructureClaim
  lengths : TorusLengthsStatement
  one_le : 1 ≤ c
  floor : 𝒮.L ^ 5 ≤ M
  kind : ¬Q.IsSecondType
  facts : Q.FirstTypeProperties
  side_ge : 2 * cubeSide 𝒮 M Q.level ≤ 𝒮.side
  position : CubeGeometry.FirstTypePlacement Q
  agreement : CubeGeometry.FirstTypeTransfer Q
  near : Q.thicken (5 / 6) ⊆ {x | supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level}
  cutoff : Q.CutoffProperties
  bounded : CubeGeometry.IsScaleBounded c (mollifyRadius 𝒮 M Q.level) Q.largeCutoff
namespace FirstTypeData
variable {c : ℝ} {Q : LevelCube 𝒮 M} (H : FirstTypeData c Q)
include H
theorem setting_ξ_eq : Q.system.setting.ξ = 𝒮.ξ := by
  obtain ⟨hadm, hset⟩ := H.facts.setting_eq
  rw [hset]
  rfl
theorem setting_L_eq : Q.system.setting.L = 𝒮.L := by
  obtain ⟨hadm, hset⟩ := H.facts.setting_eq
  rw [hset]
  rfl
theorem setting_s_eq : Q.system.setting.s = Q.level + 1 := by
  obtain ⟨hadm, hset⟩ := H.facts.setting_eq
  rw [hset]
  rfl
theorem setting_side_eq : Q.system.setting.side = 8 * cubeSide 𝒮 M Q.level := by
  obtain ⟨hadm, hset⟩ := H.facts.setting_eq
  rw [hset]
  rfl
theorem setting_scale_eq (j : ℕ) : Q.system.setting.scale j = 𝒮.scale j := by
  rw [scale_eq_pow_mul, scale_eq_pow_mul, H.setting_ξ_eq, H.setting_L_eq]
theorem mem_setting_Ω_zero (x : Q.system.setting.Point) : x ∈ Q.system.setting.Ω 0 := by
  obtain ⟨hadm, hset⟩ := H.facts.setting_eq
  have key : ∀ 𝒯 : NestedRegions, 𝒯 = Q.torusSetting hadm → ∀ x : 𝒯.Point, x ∈ 𝒯.Ω 0 := by
    rintro _ rfl x
    have e : Q.torusRegions 0 = univ := by simp [LevelCube.torusRegions]
    change x ∈ Q.torusRegions 0
    rw [e]
    exact mem_univ _
  exact key _ hset x
theorem adjointFacts : CellStructure.AdjointFacts 𝒮 := (H.cells 𝒮).2.2.2.1
theorem settingAdjointFacts : CellStructure.AdjointFacts Q.system.setting :=
  (H.cells Q.system.setting).2.2.2.1
theorem cellFacts : CellStructure.CellFacts 𝒮 := (H.cells 𝒮).2.1
theorem settingCellFacts : CellStructure.CellFacts Q.system.setting :=
  (H.cells Q.system.setting).2.1
theorem thirteen_le_L_real : (13 : ℝ) ≤ 𝒮.L := by exact_mod_cast 𝒮.thirteen_le_L
theorem L_pow_five_le_M : (𝒮.L : ℝ) ^ 5 ≤ M := by exact_mod_cast H.floor
theorem one_le_M : (1 : ℝ) ≤ M := by
  have hL := H.thirteen_le_L_real
  have hM := H.L_pow_five_le_M
  have : (1 : ℝ) ≤ (𝒮.L : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  linarith
theorem scale_level_succ : 𝒮.scale (Q.level + 1) = (𝒮.L : ℝ) * 𝒮.scale Q.level := by
  simp only [scale_eq_pow_mul, pow_succ]
  ring
theorem ξ_le_scale : 𝒮.ξ ≤ 𝒮.scale Q.level := by
  have hL := H.thirteen_le_L_real
  have hn : (1 : ℝ) ≤ (𝒮.L : ℝ) ^ Q.level := one_le_pow₀ (by linarith)
  rw [scale_eq_pow_mul]
  nlinarith [𝒮.ξ_pos]
theorem mollifyRadius_eq :
    mollifyRadius 𝒮 M Q.level = (M : ℝ) * 𝒮.scale Q.level / (6 * (𝒮.L : ℝ)) := rfl
theorem mollifyRadius_pos : 0 < mollifyRadius 𝒮 M Q.level := by
  have hL := H.thirteen_le_L_real
  have hM := H.one_le_M
  have := scale_pos 𝒮 Q.level
  rw [H.mollifyRadius_eq]
  positivity
theorem cubeSide_eq : cubeSide 𝒮 M Q.level = 6 * (𝒮.L : ℝ) * mollifyRadius 𝒮 M Q.level := by
  have hL := H.thirteen_le_L_real
  rw [H.mollifyRadius_eq]
  simp only [cubeSide]
  field_simp
theorem scale_succ_small : 24 * 𝒮.scale (Q.level + 1) ≤ mollifyRadius 𝒮 M Q.level := by
  have hL := H.thirteen_le_L_real
  have hM := H.L_pow_five_le_M
  have hx := scale_pos 𝒮 Q.level
  have h5 : 144 * (𝒮.L : ℝ) ^ 2 ≤ M := by
    have h3 : (144 : ℝ) ≤ (𝒮.L : ℝ) ^ 3 := by
      have : (13 : ℝ) ^ 3 ≤ (𝒮.L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
      linarith
    have : (𝒮.L : ℝ) ^ 5 = (𝒮.L : ℝ) ^ 3 * (𝒮.L : ℝ) ^ 2 := by ring
    nlinarith [sq_nonneg (𝒮.L : ℝ)]
  rw [H.mollifyRadius_eq, H.scale_level_succ, le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right h5 hx.le]
theorem ξ_le_scale_succ : 𝒮.ξ ≤ 𝒮.scale (Q.level + 1) := by
  have hL := H.thirteen_le_L_real
  have hx := scale_pos 𝒮 Q.level
  rw [H.scale_level_succ]
  nlinarith [H.ξ_le_scale]
theorem scale_le_scale_succ : 𝒮.scale Q.level ≤ 𝒮.scale (Q.level + 1) := by
  have hL := H.thirteen_le_L_real
  have hx := scale_pos 𝒮 Q.level
  rw [H.scale_level_succ]
  nlinarith
theorem mollifyRadius_le_cubeSide : 78 * mollifyRadius 𝒮 M Q.level ≤ cubeSide 𝒮 M Q.level := by
  have hL := H.thirteen_le_L_real
  have hr := H.mollifyRadius_pos
  rw [H.cubeSide_eq]
  nlinarith
theorem thicken_mono {ς ς' : ℝ} (h₀ : 0 ≤ ς) (h : ς ≤ ς') : Q.thicken ς ⊆ Q.thicken ς' := by
  intro x hx
  have hr := H.mollifyRadius_pos
  refine mem_thicken_of_near Q (mul_nonneg h₀ hr.le) hx ?_
  rw [sub_self, norm_zero, add_zero]
  exact mul_le_mul_of_nonneg_right h hr.le
theorem norm_sub_centre_lt {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6)) :
    ‖x - Q.centre‖ < 5 / 6 * cubeSide 𝒮 M Q.level := by
  have := H.near hx
  rw [mem_ofPred_eq, supNorm_eq_norm] at this
  exact this
theorem mem_strictPts_of_norm {x : 𝒮.Point} (h : ‖x - Q.centre‖ < cubeSide 𝒮 M Q.level) :
    x ∈ Q.strictPts := by
  change supNorm (x - Q.centre) < cubeSide 𝒮 M Q.level
  rwa [supNorm_eq_norm]
theorem mem_strictPts_of_thicken {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6)) : x ∈ Q.strictPts := by
  have hr := H.mollifyRadius_pos
  have := H.mollifyRadius_le_cubeSide
  exact H.mem_strictPts_of_norm (by linarith [H.norm_sub_centre_lt hx])
theorem largeCutoff_eq_zero {x : 𝒮.Point} (hx : x ∉ Q.thicken (2 / 3)) : Q.largeCutoff x = 0 := by
  by_contra h
  exact hx (H.cutoff.outer_support (subset_tsupport _ h))
theorem mem_thicken_of_tsupport {x : 𝒮.Point} (hx : x ∈ tsupport Q.largeCutoff) :
    x ∈ Q.thicken (5 / 6) :=
  H.thicken_mono (by norm_num) (by norm_num) (H.cutoff.outer_support hx)
theorem mem_thicken_of_ne_zero {x : 𝒮.Point} (hx : Q.largeCutoff x ≠ 0) :
    x ∈ Q.thicken (2 / 3) := by
  by_contra h
  exact hx (H.largeCutoff_eq_zero h)
theorem mem_Ω_zero_of_near {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6)) (y : 𝒮.FineSite)
    (hle : ‖x - (y : 𝒮.Point)‖ ≤ 𝒮.ξ) : (y : 𝒮.Point) ∈ 𝒮.Ω 0 := by
  have hξ := 𝒮.ξ_pos
  have hM1 := H.one_le_M
  have h0 := scale_zero 𝒮
  by_contra hy
  have hcomp : (y : 𝒮.Point) ∈ 𝒮.cubeComplementAt 0 (𝒮.Ω 0) := by
    have hy0 : (y : 𝒮.Point) ∈ cubeAt (y : 𝒮.Point) (𝒮.scale 0) := by
      change supNorm ((y : 𝒮.Point) - (y : 𝒮.Point)) ≤ 𝒮.scale 0 / 2
      rw [sub_self, supNorm_eq_norm, norm_zero, h0]
      positivity
    exact ⟨cubeAt (y : 𝒮.Point) (𝒮.scale 0),
      ⟨⟨y, by rw [h0]; exact y.2, rfl⟩, fun hsub => hy (hsub hy0)⟩, hy0⟩
  have h₁ : supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0)) ≤
      ENNReal.ofReal (supNorm (x - (y : 𝒮.Point))) :=
    iInf₂_le_of_le _ hx (iInf₂_le _ hcomp)
  rw [supNorm_eq_norm] at h₁
  have h₂ := lt_of_lt_of_le H.position.away h₁
  have h₃ : ENNReal.ofReal ‖x - (y : 𝒮.Point)‖ ≤ ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  exact absurd h₂ (not_lt.mpr h₃)
theorem mem_Ω_zero_of_thicken (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.thicken (5 / 6)) :
    (x : 𝒮.Point) ∈ 𝒮.Ω 0 :=
  H.mem_Ω_zero_of_near hx x (by rw [sub_self, norm_zero]; exact 𝒮.ξ_pos.le)
theorem torusProj_liftedCentre : torusProj 4 𝒮.side Q.liftedCentre = Q.centre := by
  funext μ
  exact (Classical.epsilon_spec (exists_rep_mem_Ico 𝒮.side_pos (Q.centre μ))).2
theorem abs_sub_liftedCentre_le {p : Fin 4 → ℝ} (hp : p ∈ Q.liftedOpenCube) (μ : Fin 4) :
    |p μ - Q.liftedCentre μ| ≤ ‖torusProj 4 𝒮.side p - Q.centre‖ := by
  have hS := 𝒮.side_pos
  have hside := H.side_ge
  have h1 : |p μ - Q.liftedCentre μ| ≤ |𝒮.side| / 2 := by
    rw [abs_of_pos hS]
    linarith [hp μ]
  have h2 := (AddCircle.norm_coe_eq_abs_iff 𝒮.side hS.ne').2 h1
  rw [← h2]
  have : ((p μ - Q.liftedCentre μ : ℝ) : AddCircle 𝒮.side) = (torusProj 4 𝒮.side p - Q.centre) μ := by
    rw [← H.torusProj_liftedCentre]
    simp [torusProj]
  rw [this]
  exact norm_le_pi_norm _ μ
theorem embed_add_torusProj (x : 𝒮.Point) (v : Fin 4 → ℝ) (hx : x ∈ Q.strictPts)
    (hv : ‖x - Q.centre‖ + ‖v‖ < cubeSide 𝒮 M Q.level) :
    Q.system.embed (x + torusProj 4 𝒮.side v) = Q.system.embed x + Q.localProj v := by
  obtain ⟨p, hp, rfl⟩ := H.facts.cover_bijective.surjOn hx
  refine H.facts.embed_add p v hp fun μ => ?_
  have h1 := H.abs_sub_liftedCentre_le hp μ
  have h2 := norm_le_pi_norm v μ
  rw [Real.norm_eq_abs] at h2
  have e : (p + v) μ - Q.liftedCentre μ = (p μ - Q.liftedCentre μ) + v μ := by
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
theorem coe_mapSite (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
      Q.system.embed x := by
  have h0 := scale_zero 𝒮
  have hm : Q.system.embed x ∈ spacingLattice 4 Q.system.setting.side Q.system.setting.ξ := by
    have h2 : Q.system.embed x ∈ Q.system.embed ''
        ((spacingLattice 4 𝒮.side (𝒮.scale 0) : Set 𝒮.Point) ∩ Q.strictPts) :=
      ⟨x, ⟨by rw [h0]; exact x.2, hx⟩, rfl⟩
    rw [H.facts.embed_sites 0 (Or.inl (Nat.zero_le _))] at h2
    rw [H.setting_ξ_eq.trans h0.symm]
    exact h2.1
  exact Classical.epsilon_spec
    (p := fun y : Q.system.setting.FineSite => (y : Q.system.setting.Point) = Q.system.embed x)
    ⟨⟨_, hm⟩, rfl⟩
theorem mapSite_injective_on {x y : 𝒮.FineSite} (hx : (x : 𝒮.Point) ∈ Q.strictPts)
    (hy : (y : 𝒮.Point) ∈ Q.strictPts) (e : Q.system.mapSite x = Q.system.mapSite y) : x = y := by
  have e' := congrArg (fun s : Q.system.setting.FineSite => (s : Q.system.setting.Point)) e
  simp only [H.coe_mapSite _ hx, H.coe_mapSite _ hy] at e'
  exact Subtype.ext (H.facts.embed_bijective.injOn hx hy e')
theorem exists_fineSite_of_embed {x₀ : 𝒮.Point} (hx : x₀ ∈ Q.strictPts)
    (w : Q.system.setting.FineSite) (hw : (w : Q.system.setting.Point) = Q.system.embed x₀) :
    ∃ x : 𝒮.FineSite, (x : 𝒮.Point) = x₀ ∧ Q.system.mapSite x = w := by
  have h0 := scale_zero 𝒮
  have hmem : (w : Q.system.setting.Point) ∈
      (spacingLattice 4 Q.system.setting.side (𝒮.scale 0) : Set Q.system.setting.Point) ∩
        Q.localProj '' Q.liftedOpenCube := by
    refine ⟨?_, ?_⟩
    · rw [h0, ← H.setting_ξ_eq]
      exact w.2
    · rw [hw]
      exact H.facts.embed_bijective.mapsTo hx
  rw [← H.facts.embed_sites 0 (Or.inl (Nat.zero_le _))] at hmem
  obtain ⟨x₁, ⟨hl, hi⟩, he⟩ := hmem
  have hx₁ : x₁ = x₀ := H.facts.embed_bijective.injOn hi hx (he.trans hw)
  refine ⟨⟨x₁, by rw [← h0]; exact hl⟩, hx₁, ?_⟩
  apply Subtype.ext
  rw [H.coe_mapSite _ hi]
  exact he
theorem norm_add_unitStep_sub_centre (x : 𝒮.Point) (ν : Fin 4) :
    ‖(x + (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)) - Q.centre‖ ≤ ‖x - Q.centre‖ + 𝒮.ξ := by
  have e : (x + (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)) - Q.centre =
      (x - Q.centre) + (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point) := by abel
  rw [e]
  linarith [norm_add_le (x - Q.centre) (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point),
    norm_unitStep_le (𝒮 := 𝒮) ν]
theorem norm_sub_unitStep_sub_centre (x : 𝒮.Point) (ν : Fin 4) :
    ‖(x - (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)) - Q.centre‖ ≤ ‖x - Q.centre‖ + 𝒮.ξ := by
  have e : (x - (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)) - Q.centre =
      (x - Q.centre) - (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point) := by abel
  rw [e]
  linarith [norm_sub_le (x - Q.centre) (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point),
    norm_unitStep_le (𝒮 := 𝒮) ν]
theorem mapSite_add_unitStep (y : 𝒮.FineSite) (ν : Fin 4)
    (h : ‖(y : 𝒮.Point) - Q.centre‖ + 𝒮.ξ < cubeSide 𝒮 M Q.level) :
    Q.system.mapSite (y + unitStep 4 𝒮.side 𝒮.ξ ν) =
      Q.system.mapSite y + unitStep 4 Q.system.setting.side Q.system.setting.ξ ν := by
  have hξ0 := 𝒮.ξ_pos
  have hy := H.mem_strictPts_of_norm (x := y) (by linarith)
  have hy' : ((y + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ Q.strictPts := by
    apply H.mem_strictPts_of_norm
    rw [AddSubgroup.coe_add]
    linarith [H.norm_add_unitStep_sub_centre (y : 𝒮.Point) ν]
  apply Subtype.ext
  rw [AddSubgroup.coe_add, H.coe_mapSite _ hy', H.coe_mapSite _ hy]
  change Q.system.embed ((y : 𝒮.Point) + torusProj 4 𝒮.side (Pi.single ν 𝒮.ξ)) =
    Q.system.embed y + torusProj 4 Q.system.setting.side (Pi.single ν Q.system.setting.ξ)
  rw [H.setting_ξ_eq]
  exact H.embed_add_torusProj _ _ hy (by linarith [norm_piSingle_le hξ0.le ν])
theorem mapSite_sub_unitStep (y : 𝒮.FineSite) (ν : Fin 4)
    (h : ‖(y : 𝒮.Point) - Q.centre‖ + 2 * 𝒮.ξ < cubeSide 𝒮 M Q.level) :
    Q.system.mapSite (y - unitStep 4 𝒮.side 𝒮.ξ ν) =
      Q.system.mapSite y - unitStep 4 Q.system.setting.side Q.system.setting.ξ ν := by
  have e := H.mapSite_add_unitStep (y - unitStep 4 𝒮.side 𝒮.ξ ν) ν (by
    rw [AddSubgroup.coe_sub]
    linarith [H.norm_sub_unitStep_sub_centre (y : 𝒮.Point) ν])
  rw [sub_add_cancel] at e
  exact eq_sub_of_add_eq e.symm
theorem cellOf_subset_strictPts {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres)
    (hm : CubeGeometry.CellMeetsThicken Q y) : 𝒮.cellOf y ⊆ Q.strictPts :=
  H.agreement.cell_inside y hy hm
theorem level_eq_of_meets {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres)
    (hm : CubeGeometry.CellMeetsThicken Q y) :
    𝒮.level y = Q.level ∨ (𝒮.level y = Q.level + 1 ∧ Q.level < 𝒮.s) := by
  rcases H.agreement.cell_levels y hy hm with h | h
  · exact Or.inl (level_eq_of_mem_centresAt H.cellFacts h)
  · exact Or.inr ⟨level_eq_of_mem_centresAt H.cellFacts h,
      by have := le_s_of_mem_centresAt h; omega⟩
theorem levelScale_le_scale_succ {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres)
    (hm : CubeGeometry.CellMeetsThicken Q y) : 𝒮.levelScale y ≤ 𝒮.scale (Q.level + 1) := by
  rw [levelScale_eq]
  rcases H.level_eq_of_meets hy hm with h | ⟨h, -⟩
  · rw [h]
    exact H.scale_le_scale_succ
  · rw [h]
theorem scale_le_levelScale {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres)
    (hm : CubeGeometry.CellMeetsThicken Q y) : 𝒮.scale Q.level ≤ 𝒮.levelScale y := by
  rw [levelScale_eq]
  rcases H.level_eq_of_meets hy hm with h | ⟨h, -⟩
  · rw [h]
  · rw [h]
    exact H.scale_le_scale_succ
theorem norm_sub_le_of_mem_cellOf_pair {y p q : 𝒮.Point} (hy : y ∈ 𝒮.allCentres)
    (hm : CubeGeometry.CellMeetsThicken Q y) (hp : p ∈ 𝒮.cellOf y) (hq : q ∈ 𝒮.cellOf y) :
    ‖p - q‖ ≤ 𝒮.scale (Q.level + 1) := by
  have h₁ := norm_sub_le_of_mem_cellOf hp
  have h₂ := norm_sub_le_of_mem_cellOf hq
  have h₃ := H.levelScale_le_scale_succ hy hm
  have e : p - q = (p - y) - (q - y) := by abel
  rw [e]
  linarith [norm_sub_le (p - y) (q - y)]
theorem embed_eq_of_transported {y : 𝒮.Point} {y' : Q.system.setting.Point}
    (hy : y ∈ 𝒮.allCentres) (hm : CubeGeometry.CellMeetsThicken Q y)
    (hy' : y' ∈ Q.system.setting.allCentres) (hc : CubeGeometry.CellTransported Q y y') :
    Q.system.embed y = y' := by
  set j := 𝒮.level y with hj
  have hT : Q.system.setting.level y' = j := hc.2
  have hlat' : y' ∈ spacingLattice 4 Q.system.setting.side (𝒮.scale j) := by
    have := mem_spacingLattice_of_mem_centresAt (mem_centresAt_level hy')
    rwa [hT, H.setting_scale_eq] at this
  have hyin : y ∈ Q.strictPts := H.cellOf_subset_strictPts hy hm (mem_cellOf_self y)
  have hcond : j ≤ Q.level ∨ (j = Q.level + 1 ∧ Q.level < 𝒮.s) := by
    rcases H.level_eq_of_meets hy hm with h | h
    · exact Or.inl h.le
    · exact Or.inr h
  have hlat : Q.system.embed y ∈ spacingLattice 4 Q.system.setting.side (𝒮.scale j) := by
    have h2 : Q.system.embed y ∈ Q.system.embed ''
        ((spacingLattice 4 𝒮.side (𝒮.scale j) : Set 𝒮.Point) ∩ Q.strictPts) :=
      ⟨y, ⟨mem_spacingLattice_of_mem_centresAt (mem_centresAt_level hy), hyin⟩, rfl⟩
    rw [H.facts.embed_sites j hcond] at h2
    exact h2.1
  have hcell : Q.system.embed y ∈ Q.system.setting.cellOf y' := by
    rw [← hc.1]
    exact ⟨y, mem_cellOf_self y, rfl⟩
  have hnear : ‖Q.system.embed y - y'‖ ≤ 𝒮.scale j / 2 := by
    have := norm_sub_le_of_mem_cellOf hcell
    rwa [levelScale_eq, hT, H.setting_scale_eq] at this
  have hjs : j ≤ Q.system.setting.s := by
    rw [H.setting_s_eq]
    rcases hcond with h | h <;> omega
  obtain ⟨N, hN⟩ := exists_side_eq_mul_scale Q.system.setting j hjs
  rw [H.setting_scale_eq] at hN
  exact eq_of_mem_spacingLattice_of_near (scale_pos 𝒮 j) N hN hlat hlat' hnear
theorem embed_transported {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres)
    (hm : CubeGeometry.CellMeetsThicken Q y) :
    Q.system.embed y ∈ Q.system.setting.allCentres ∧
      CubeGeometry.CellTransported Q y (Q.system.embed y) := by
  obtain ⟨y', hy', -, hc⟩ := H.agreement.cell_carried y hy hm
  rw [H.embed_eq_of_transported hy hm hy' hc]
  exact ⟨hy', hc⟩
structure NearSite (Q : LevelCube 𝒮 M) (u : 𝒮.FineSite) : Prop where
  omega : (u : 𝒮.Point) ∈ 𝒮.Ω 0
  site : 𝒮.centreOfSite u ∈ 𝒮.allCentres
  mem : (u : 𝒮.Point) ∈ 𝒮.cellOf (𝒮.centreOfSite u)
  meets : CubeGeometry.CellMeetsThicken Q (𝒮.centreOfSite u)
  inner : 𝒮.cellOf (𝒮.centreOfSite u) ⊆ Q.strictPts
  norm_lt : ‖(u : 𝒮.Point) - Q.centre‖ < 5 / 6 * cubeSide 𝒮 M Q.level
  image_site : Q.system.embed (𝒮.centreOfSite u) ∈ Q.system.setting.allCentres
  carried : CubeGeometry.CellTransported Q (𝒮.centreOfSite u) (Q.system.embed (𝒮.centreOfSite u))
  local_centre :
    Q.system.setting.centreOfSite (Q.system.mapSite u) = Q.system.embed (𝒮.centreOfSite u)
theorem nearSite_of_mem {u : 𝒮.FineSite} (hu : (u : 𝒮.Point) ∈ Q.thicken (5 / 6)) :
    NearSite Q u := by
  have h₀ := H.mem_Ω_zero_of_thicken u hu
  obtain ⟨h₁, h₂⟩ := centreOfSite_spec H.cellFacts u h₀
  have hm : CubeGeometry.CellMeetsThicken Q (𝒮.centreOfSite u) := ⟨u, h₂, hu⟩
  obtain ⟨h₃, h₄⟩ := H.embed_transported h₁ hm
  refine ⟨h₀, h₁, h₂, hm, H.cellOf_subset_strictPts h₁ hm, H.norm_sub_centre_lt hu, h₃, h₄, ?_⟩
  refine centreOfSite_eq H.settingCellFacts _ h₃ ?_
  rw [H.coe_mapSite _ (H.mem_strictPts_of_thicken hu), ← h₄.1]
  exact ⟨u, h₂, rfl⟩
end FirstTypeData
namespace FirstTypeData
variable {c : ℝ} {Q : LevelCube 𝒮 M} (H : FirstTypeData c Q)
include H
theorem ξ_small : 24 * 𝒮.ξ ≤ mollifyRadius 𝒮 M Q.level := by
  linarith [H.scale_succ_small, H.ξ_le_scale_succ]
theorem norm_add_two_ξ_lt {u : 𝒮.FineSite} (hN : NearSite Q u) :
    ‖(u : 𝒮.Point) - Q.centre‖ + 2 * 𝒮.ξ < cubeSide 𝒮 M Q.level := by
  have h₁ := hN.norm_lt
  have h₂ := H.ξ_small
  have h₃ := H.mollifyRadius_le_cubeSide
  have h₄ := H.mollifyRadius_pos
  linarith
theorem norm_add_two_ξ_lt_of_thicken {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6)) :
    ‖x - Q.centre‖ + 2 * 𝒮.ξ < cubeSide 𝒮 M Q.level := by
  have h₁ := H.norm_sub_centre_lt hx
  have h₂ := H.ξ_small
  have h₃ := H.mollifyRadius_le_cubeSide
  have h₄ := H.mollifyRadius_pos
  linarith
theorem gaugeLap_mapSite {u : 𝒮.FineSite} (hN : NearSite Q u)
    (G : Q.system.setting.FineSite → ℝ) :
    gaugeLap G (Q.system.mapSite u) =
      gaugeStencil 𝒮 (fun x => G (Q.system.mapSite x)) u := by
  rw [gaugeLap_eq_gaugeStencil H.settingAdjointFacts G _ (H.mem_setting_Ω_zero _)
    (fun _ => Or.inl (H.mem_setting_Ω_zero _)) (fun _ => Or.inl (H.mem_setting_Ω_zero _))]
  simp only [gaugeStencil]
  have hz := H.norm_add_two_ξ_lt hN
  have hξ0 := 𝒮.ξ_pos
  have e₁ : latticeLaplacian G (Q.system.mapSite u) =
      latticeLaplacian (fun x => G (Q.system.mapSite x)) u := by
    rw [latticeLaplacian_apply, latticeLaplacian_apply]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have e : (Q.system.setting.ξ ^ 2)⁻¹ = (𝒮.ξ ^ 2)⁻¹ := by rw [H.setting_ξ_eq]
    rw [e, H.mapSite_add_unitStep u ν (by linarith), H.mapSite_sub_unitStep u ν hz]
  have e₂ : levelWeight Q.system.setting (Q.system.setting.centreOfSite (Q.system.mapSite u)) =
      levelWeight 𝒮 (𝒮.centreOfSite u) := by
    rw [hN.local_centre]
    simp only [levelWeight]
    rw [hN.carried.2, H.setting_L_eq, H.setting_scale_eq]
  have e₃ : ∑ᶠ x' ∈ Q.system.setting.fineBlock
        (Q.system.setting.level (Q.system.setting.centreOfSite (Q.system.mapSite u)))
        (Q.system.setting.centreOfSite (Q.system.mapSite u)), G x' =
      ∑ᶠ x' ∈ 𝒮.fineBlock (𝒮.level (𝒮.centreOfSite u)) (𝒮.centreOfSite u),
        G (Q.system.mapSite x') := by
    rw [hN.local_centre]
    symm
    refine finsum_mem_eq_of_bijOn Q.system.mapSite ⟨?_, ?_, ?_⟩ fun _ _ => rfl
    · intro x hx
      have hx' : (x : 𝒮.Point) ∈ 𝒮.cellOf (𝒮.centreOfSite u) := hx
      change ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) ∈
        Q.system.setting.cellOf (Q.system.embed (𝒮.centreOfSite u))
      rw [H.coe_mapSite _ (hN.inner hx'), ← hN.carried.1]
      exact ⟨x, hx', rfl⟩
    · intro x hx x' hx' e
      exact H.mapSite_injective_on (hN.inner hx) (hN.inner hx') e
    · intro w hw
      have hw' : (w : Q.system.setting.Point) ∈
          Q.system.setting.cellOf (Q.system.embed (𝒮.centreOfSite u)) := hw
      rw [← hN.carried.1] at hw'
      obtain ⟨x₀, hx₀, e⟩ := hw'
      obtain ⟨x, rfl, e'⟩ := H.exists_fineSite_of_embed (hN.inner hx₀) w e.symm
      exact ⟨x, hx₀, e'⟩
  rw [e₁, e₂, e₃]
theorem mem_strictPts_of_mem_cellAndNeighbours {u : 𝒮.FineSite} (hN : NearSite Q u)
    {x : 𝒮.FineSite} (hx : x ∈ cellAndNeighbours u) : (x : 𝒮.Point) ∈ Q.strictPts := by
  have hz := H.norm_add_two_ξ_lt hN
  have hξ0 := 𝒮.ξ_pos
  rcases hx with h | ⟨ν, h | h⟩
  · exact hN.inner h
  · apply H.mem_strictPts_of_norm
    rw [h, AddSubgroup.coe_add]
    linarith [H.norm_add_unitStep_sub_centre (u : 𝒮.Point) ν]
  · apply H.mem_strictPts_of_norm
    rw [h, AddSubgroup.coe_sub]
    linarith [H.norm_sub_unitStep_sub_centre (u : 𝒮.Point) ν]
theorem pullSites_mapSite (g : 𝒮.FineSite → ℝ) (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    Q.system.pullSites Q.largeCutoff g (Q.system.mapSite x) =
      Q.largeCutoff (x : 𝒮.Point) * g x := by
  have hu : ∀ x' : 𝒮.FineSite, (x' : 𝒮.Point) ∈ tsupport Q.largeCutoff →
      Q.system.mapSite x' = Q.system.mapSite x → x' = x := fun x' h e =>
    H.mapSite_injective_on (H.mem_strictPts_of_thicken (H.mem_thicken_of_tsupport h)) hx e
  unfold CubeSystem.pullSites
  by_cases h₀ : (x : 𝒮.Point) ∈ tsupport Q.largeCutoff
  · have : {x' : 𝒮.FineSite | (x' : 𝒮.Point) ∈ tsupport Q.largeCutoff ∧
        Q.system.mapSite x' = Q.system.mapSite x} = {x} := by
      ext x'
      constructor
      · rintro ⟨h₁, h₂⟩
        exact hu x' h₁ h₂
      · rintro rfl
        exact ⟨h₀, rfl⟩
    rw [this, finsum_mem_singleton]
  · have : {x' : 𝒮.FineSite | (x' : 𝒮.Point) ∈ tsupport Q.largeCutoff ∧
        Q.system.mapSite x' = Q.system.mapSite x} = ∅ := by
      ext x'
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h₁ h₂
      exact h₀ (hu x' h₁ h₂ ▸ h₁)
    rw [this, finsum_mem_empty, image_eq_zero_of_notMem_tsupport h₀, zero_mul]
theorem pullSites_eq_zero (g : 𝒮.FineSite → ℝ) (w : Q.system.setting.FineSite)
    (hn : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ tsupport Q.largeCutoff →
      Q.system.mapSite x ≠ w) :
    Q.system.pullSites Q.largeCutoff g w = 0 := by
  unfold CubeSystem.pullSites
  have : {x : 𝒮.FineSite | (x : 𝒮.Point) ∈ tsupport Q.largeCutoff ∧
      Q.system.mapSite x = w} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact hn x
  rw [this, finsum_mem_empty]
theorem coarsePull_apply (ω : 𝒮.Coarse) (y : 𝒮.allCentres) (hy : (y : 𝒮.Point) ∈ Q.strictPts)
    (w : Q.system.setting.allCentres) (hw : (w : Q.system.setting.Point) = Q.system.embed y) :
    coarsePull Q ω w = Q.largeCutoff (y : 𝒮.Point) * ω y := by
  have hu : ∀ y' : 𝒮.allCentres, (y' : 𝒮.Point) ∈ tsupport Q.largeCutoff →
      Q.system.embed y' = w → y' = y := fun y' h e =>
    Subtype.ext (H.facts.embed_bijective.injOn
      (H.mem_strictPts_of_thicken (H.mem_thicken_of_tsupport h)) hy (e.trans hw))
  unfold coarsePull
  by_cases h₀ : (y : 𝒮.Point) ∈ tsupport Q.largeCutoff
  · have : {y' : 𝒮.allCentres | (y' : 𝒮.Point) ∈ tsupport Q.largeCutoff ∧
        Q.system.embed y' = w} = {y} := by
      ext y'
      constructor
      · rintro ⟨h₁, h₂⟩
        exact hu y' h₁ h₂
      · rintro rfl
        exact ⟨h₀, hw.symm⟩
    rw [this, finsum_mem_singleton]
  · have : {y' : 𝒮.allCentres | (y' : 𝒮.Point) ∈ tsupport Q.largeCutoff ∧
        Q.system.embed y' = w} = ∅ := by
      ext y'
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h₁ h₂
      exact h₀ (hu y' h₁ h₂ ▸ h₁)
    rw [this, finsum_mem_empty, image_eq_zero_of_notMem_tsupport h₀, zero_mul]
theorem add_unitStep_mem_Ω_zero {u : 𝒮.FineSite} (hu : (u : 𝒮.Point) ∈ Q.thicken (5 / 6))
    (ν : Fin 4) : ((u + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ 𝒮.Ω 0 := by
  refine H.mem_Ω_zero_of_near hu _ ?_
  have e : (u : 𝒮.Point) - ((u + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) =
      -(unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point) := by
    rw [AddSubgroup.coe_add]
    abel
  rw [e, norm_neg]
  exact norm_unitStep_le ν
theorem sub_unitStep_mem_Ω_zero {u : 𝒮.FineSite} (hu : (u : 𝒮.Point) ∈ Q.thicken (5 / 6))
    (ν : Fin 4) : ((u - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ 𝒮.Ω 0 := by
  refine H.mem_Ω_zero_of_near hu _ ?_
  have e : (u : 𝒮.Point) - ((u - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) =
      (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point) := by
    rw [AddSubgroup.coe_sub]
    abel
  rw [e]
  exact norm_unitStep_le ν
theorem pushLapCommutator_eq {u : 𝒮.FineSite} (hu : (u : 𝒮.Point) ∈ Q.thicken (5 / 6))
    (f : (CubeTorus.torusSetting Q).FineSite → ℝ) :
    pushLapCommutator Q f u =
      cutoffDefect 𝒮 (fun x => Q.largeCutoff (x : 𝒮.Point))
        (fun x => f (Q.system.mapSite x)) u := by
  have hN := H.nearSite_of_mem hu
  change Q.largeCutoff (u : 𝒮.Point) * gaugeLap f (Q.system.mapSite u) -
    gaugeLap (cutoffPush Q f) u = _
  rw [H.gaugeLap_mapSite hN, gaugeLap_eq_gaugeStencil H.adjointFacts _ u hN.omega
    (fun ν => Or.inl (H.add_unitStep_mem_Ω_zero hu ν))
    (fun ν => Or.inl (H.sub_unitStep_mem_Ω_zero hu ν))]
  rfl
theorem pullLapCommutator_mapSite {u : 𝒮.FineSite} (hu : (u : 𝒮.Point) ∈ Q.thicken (5 / 6))
    (g : 𝒮.FineSite → ℝ) :
    pullLapCommutator Q g (Q.system.mapSite u) =
      cutoffDefect 𝒮 (fun x => Q.largeCutoff (x : 𝒮.Point)) g u := by
  have hN := H.nearSite_of_mem hu
  change cutoffPull Q (gaugeLap g) (Q.system.mapSite u) -
    gaugeLap (cutoffPull Q g) (Q.system.mapSite u) = _
  have e : cutoffPull Q (gaugeLap g) (Q.system.mapSite u) =
      Q.largeCutoff (u : 𝒮.Point) * gaugeLap g u :=
    H.pullSites_mapSite _ u (H.mem_strictPts_of_thicken hu)
  rw [e, H.gaugeLap_mapSite hN, gaugeLap_eq_gaugeStencil H.adjointFacts _ u hN.omega
    (fun ν => Or.inl (H.add_unitStep_mem_Ω_zero hu ν))
    (fun ν => Or.inl (H.sub_unitStep_mem_Ω_zero hu ν))]
  simp only [cutoffDefect]
  congr 1
  exact gaugeStencil_congr (Or.inl hN.mem) fun x hx =>
    H.pullSites_mapSite g x (H.mem_strictPts_of_mem_cellAndNeighbours hN hx)
theorem pushAvgDefect_eq {u : 𝒮.FineSite} (hu : (u : 𝒮.Point) ∈ Q.thicken (5 / 6))
    (ω : (CubeTorus.torusSetting Q).Coarse) :
    ∃ h : Q.system.embed (𝒮.centreOfSite u) ∈ Q.system.setting.allCentres,
      pushAvgDefect Q ω u =
        (Q.largeCutoff (u : 𝒮.Point) - Q.largeCutoff (𝒮.centreOfSite u)) * ω ⟨_, h⟩ := by
  have hN := H.nearSite_of_mem hu
  refine ⟨hN.image_site, ?_⟩
  change Q.largeCutoff (u : 𝒮.Point) * blockAvgAdj ω (Q.system.mapSite u) -
    blockAvgAdj (coarsePush Q ω) u = _
  obtain ⟨h₁, e₁⟩ := (H.settingAdjointFacts.avgAdj_apply ω).2 (Q.system.mapSite u)
    (H.mem_setting_Ω_zero _)
  obtain ⟨h₂, e₂⟩ := (H.adjointFacts.avgAdj_apply (coarsePush Q ω)).2 u hN.omega
  have e₃ : ω ⟨_, h₁⟩ = ω ⟨_, hN.image_site⟩ := congrArg ω (Subtype.ext hN.local_centre)
  have e₄ : coarsePush Q ω ⟨_, h₂⟩ =
      Q.largeCutoff (𝒮.centreOfSite u) * ω ⟨_, hN.image_site⟩ := dif_pos hN.image_site
  rw [e₁, e₂, e₃, e₄]
  ring
theorem pullAvgDefect_mapSite {u : 𝒮.FineSite} (hu : (u : 𝒮.Point) ∈ Q.thicken (5 / 6))
    (ω : 𝒮.Coarse) :
    ∃ h : 𝒮.centreOfSite u ∈ 𝒮.allCentres,
      pullAvgDefect Q ω (Q.system.mapSite u) =
        (Q.largeCutoff (u : 𝒮.Point) - Q.largeCutoff (𝒮.centreOfSite u)) * ω ⟨_, h⟩ := by
  have hN := H.nearSite_of_mem hu
  refine ⟨hN.site, ?_⟩
  change cutoffPull Q (blockAvgAdj ω) (Q.system.mapSite u) -
    blockAvgAdj (coarsePull Q ω) (Q.system.mapSite u) = _
  have e : cutoffPull Q (blockAvgAdj ω) (Q.system.mapSite u) =
      Q.largeCutoff (u : 𝒮.Point) * blockAvgAdj ω u :=
    H.pullSites_mapSite _ u (H.mem_strictPts_of_thicken hu)
  obtain ⟨h₁, e₁⟩ := (H.adjointFacts.avgAdj_apply ω).2 u hN.omega
  obtain ⟨h₂, e₂⟩ := (H.settingAdjointFacts.avgAdj_apply (coarsePull Q ω)).2
    (Q.system.mapSite u) (H.mem_setting_Ω_zero _)
  rw [e, e₁, e₂, H.coarsePull_apply ω ⟨_, hN.site⟩ (hN.inner (mem_cellOf_self _)) ⟨_, h₂⟩
    hN.local_centre]
  have e₃ : ω ⟨_, h₁⟩ = ω ⟨_, hN.site⟩ := rfl
  rw [e₃]
  ring
end FirstTypeData
namespace FirstTypeData
variable {c : ℝ} {Q : LevelCube 𝒮 M} (H : FirstTypeData c Q)
include H
theorem mem_thicken_of_near' {ς ς' : ℝ} (h₀ : 0 ≤ ς) {x x' : 𝒮.Point} (hx : x ∈ Q.thicken ς)
    (h : ς * mollifyRadius 𝒮 M Q.level + ‖x' - x‖ ≤ ς' * mollifyRadius 𝒮 M Q.level) :
    x' ∈ Q.thicken ς' :=
  mem_thicken_of_near Q (mul_nonneg h₀ H.mollifyRadius_pos.le) hx h
theorem mem_thicken_five_sixths {x : 𝒮.Point} (h : x ∈ Q.thicken (2 / 3)) :
    x ∈ Q.thicken (5 / 6) := H.thicken_mono (by norm_num) (by norm_num) h
theorem norm_sub_le_of_isNeighbor {u u' : 𝒮.FineSite} (h : IsNeighbor u u') :
    ‖(u' : 𝒮.Point) - (u : 𝒮.Point)‖ ≤ 𝒮.ξ := by
  obtain ⟨ν, rfl | rfl⟩ := h
  · rw [AddSubgroup.coe_add, add_sub_cancel_left]
    exact norm_unitStep_le ν
  · rw [AddSubgroup.coe_sub, sub_sub_cancel_left, norm_neg]
    exact norm_unitStep_le ν
theorem meets_of_mem_nonconstantCells {y : 𝒮.Point} (hy : y ∈ nonconstantCells Q) :
    CubeGeometry.CellMeetsThicken Q y := by
  obtain ⟨hys, u, huc, u', hu', hne⟩ := hy
  have hcen : 𝒮.centreOfSite u = y := centreOfSite_eq H.cellFacts u hys huc
  have hsm := H.ξ_small
  have hr := H.mollifyRadius_pos
  by_cases h₁ : Q.largeCutoff (u : 𝒮.Point) = 0
  · have h₂ : Q.largeCutoff (u' : 𝒮.Point) ≠ 0 := fun h => hne (by rw [h, h₁])
    have h₃ := H.mem_thicken_of_ne_zero h₂
    rcases hu' with h | h
    · rw [hcen] at h
      exact ⟨u', h, H.mem_thicken_five_sixths h₃⟩
    · refine ⟨u, huc, H.mem_thicken_of_near' (by norm_num) h₃ ?_⟩
      have := H.norm_sub_le_of_isNeighbor h
      rw [norm_sub_rev] at this
      linarith
  · exact ⟨u, huc, H.mem_thicken_five_sixths (H.mem_thicken_of_ne_zero h₁)⟩
theorem cellOf_subset_annulus {y : 𝒮.Point} (hy : y ∈ nonconstantCells Q) :
    𝒮.cellOf y ⊆ Q.thicken (5 / 6) \ Q.thicken (5 / 12) := by
  have hm := H.meets_of_mem_nonconstantCells hy
  obtain ⟨hys, u, huc, u', hu', hne⟩ := hy
  have hcen : 𝒮.centreOfSite u = y := centreOfSite_eq H.cellFacts u hys huc
  have hsm := H.scale_succ_small
  have hr := H.mollifyRadius_pos
  have hxi := H.ξ_le_scale_succ
  set σ := 𝒮.scale (Q.level + 1) with hσ
  have hd : ‖(u' : 𝒮.Point) - (u : 𝒮.Point)‖ ≤ σ := by
    rcases hu' with h | h
    · rw [hcen] at h
      exact H.norm_sub_le_of_mem_cellOf_pair hys hm h huc
    · exact (H.norm_sub_le_of_isNeighbor h).trans hxi
  have hv' : ∃ v : 𝒮.FineSite, (v = u ∨ v = u') ∧ (v : 𝒮.Point) ∈ Q.thicken (2 / 3) := by
    by_cases h₁ : Q.largeCutoff (u : 𝒮.Point) = 0
    · exact ⟨u', Or.inr rfl, H.mem_thicken_of_ne_zero fun h => hne (by rw [h, h₁])⟩
    · exact ⟨u, Or.inl rfl, H.mem_thicken_of_ne_zero h₁⟩
  have hv : ∃ v : 𝒮.FineSite, (v = u ∨ v = u') ∧ (v : 𝒮.Point) ∉ Q.thicken (1 / 2) := by
    by_contra hc
    have hc' : ∀ v : 𝒮.FineSite, (v = u ∨ v = u') → (v : 𝒮.Point) ∈ Q.thicken (1 / 2) :=
      fun v hv => by_contra fun h => hc ⟨v, hv, h⟩
    have e₁ := H.cutoff.outer_eq_one _ (hc' u (Or.inl rfl))
    have e₂ := H.cutoff.outer_eq_one _ (hc' u' (Or.inr rfl))
    exact hne (by rw [e₁, e₂])
  intro p hp
  have hpu : ‖p - (u : 𝒮.Point)‖ ≤ σ := H.norm_sub_le_of_mem_cellOf_pair hys hm hp huc
  have hall : ∀ v : 𝒮.FineSite, (v = u ∨ v = u') → ‖p - (v : 𝒮.Point)‖ ≤ 2 * σ := by
    rintro v (rfl | rfl)
    · have : 0 ≤ σ := le_trans (norm_nonneg _) hd
      linarith
    · have e : p - (v : 𝒮.Point) = (p - (u : 𝒮.Point)) - ((v : 𝒮.Point) - (u : 𝒮.Point)) := by
        abel
      rw [e]
      linarith [norm_sub_le (p - (u : 𝒮.Point)) ((v : 𝒮.Point) - (u : 𝒮.Point))]
  obtain ⟨v', hv'₁, hv'₂⟩ := hv'
  obtain ⟨v, hv₁, hv₂⟩ := hv
  refine ⟨H.mem_thicken_of_near' (by norm_num) hv'₂ ?_,
    fun hp' => hv₂ (H.mem_thicken_of_near' (by norm_num) hp' ?_)⟩
  · have := hall v' hv'₁
    linarith
  · have := hall v hv₁
    rw [norm_sub_rev] at this
    linarith
theorem mem_thicken_of_inNonconstantCell {u : 𝒮.FineSite} (h : InNonconstantCell Q u) :
    (u : 𝒮.Point) ∈ Q.thicken (5 / 6) := by
  obtain ⟨y, hy, hu⟩ := h
  exact (H.cellOf_subset_annulus hy hu).1
theorem encard_spacingLattice_le {S σ : ℝ} {N : ℕ} (hN : 0 < N) (hS : S = (N : ℝ) * σ) :
    (spacingLattice 4 S σ : Set (PeriodicTorus 4 S)).encard ≤ ((N ^ 4 : ℕ) : ℕ∞) := by
  let g : (Fin 4 → Fin N) → PeriodicTorus 4 S := fun k => torusProj 4 S fun μ => ((k μ : ℕ) : ℝ) * σ
  have hsub : (spacingLattice 4 S σ : Set (PeriodicTorus 4 S)) ⊆ range g := by
    rintro x ⟨k, rfl⟩
    have hNz : (0 : ℤ) < N := by exact_mod_cast hN
    refine ⟨fun μ => ⟨(k μ % N).toNat, ?_⟩, ?_⟩
    · have h₁ := Int.emod_nonneg (k μ) hNz.ne'
      have h₂ := Int.emod_lt_of_pos (k μ) hNz
      omega
    · funext μ
      simp only [g, torusProj]
      have h₁ := Int.emod_nonneg (k μ) hNz.ne'
      have e₁ : (((k μ % N).toNat : ℕ) : ℝ) = ((k μ % N : ℤ) : ℝ) := by
        have : (((k μ % N).toNat : ℕ) : ℤ) = k μ % N := Int.toNat_of_nonneg h₁
        exact_mod_cast this
      rw [e₁]
      have e₂ : (k μ : ℝ) * σ = ((k μ % N : ℤ) : ℝ) * σ + ((k μ / N : ℤ) : ℝ) * S := by
        have : (k μ : ℝ) = ((k μ % N : ℤ) : ℝ) + (N : ℝ) * ((k μ / N : ℤ) : ℝ) := by
          have := Int.emod_add_mul_ediv (k μ) N
          exact_mod_cast this.symm
        rw [hS]
        nth_rw 1 [this]
        ring
      rw [e₂, AddCircle.coe_add]
      have : ((((k μ / N : ℤ) : ℝ) * S : ℝ) : AddCircle S) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨k μ / N, by simp⟩
      rw [this, add_zero]
  refine (encard_le_encard hsub).trans ?_
  rw [← image_univ]
  refine (encard_image_le _ _).trans ?_
  rw [encard_univ, ENat.card_eq_coe_fintype_card]
  simp
theorem encard_nonconstantCells_le : (nonconstantCells Q).encard ≤ ((8 * M) ^ 4 : ℕ) := by
  have hM := H.one_le_M
  have hMn : 0 < M := by exact_mod_cast (by linarith : (0 : ℝ) < M)
  have hS : Q.system.setting.side = ((8 * M : ℕ) : ℝ) * 𝒮.scale Q.level := by
    rw [H.setting_side_eq]
    simp only [cubeSide]
    push_cast
    ring
  refine le_trans ?_ (H.encard_spacingLattice_le (by omega) hS)
  refine encard_le_encard_of_injOn (f := Q.system.embed) ?_ ?_
  · intro y hy
    have hm := H.meets_of_mem_nonconstantCells hy
    have hin : y ∈ Q.strictPts := H.cellOf_subset_strictPts hy.1 hm (mem_cellOf_self y)
    have hlat : y ∈ spacingLattice 4 𝒮.side (𝒮.scale Q.level) := by
      rcases H.agreement.cell_levels y hy.1 hm with h | h
      · exact mem_spacingLattice_of_mem_centresAt h
      · exact spacingLattice_scale_subset 𝒮 _ _ (Nat.le_succ _)
          (mem_spacingLattice_of_mem_centresAt h)
    have h2 : Q.system.embed y ∈ Q.system.embed ''
        ((spacingLattice 4 𝒮.side (𝒮.scale Q.level) : Set 𝒮.Point) ∩ Q.strictPts) :=
      ⟨y, ⟨hlat, hin⟩, rfl⟩
    rw [H.facts.embed_sites Q.level (Or.inl le_rfl)] at h2
    exact h2.1
  · intro y hy y' hy' e
    exact H.facts.embed_bijective.injOn
      (H.cellOf_subset_strictPts hy.1 (H.meets_of_mem_nonconstantCells hy) (mem_cellOf_self y))
      (H.cellOf_subset_strictPts hy'.1 (H.meets_of_mem_nonconstantCells hy') (mem_cellOf_self y')) e
theorem largeCutoff_eq_of_not_inNonconstantCell {u : 𝒮.FineSite} (h₀ : (u : 𝒮.Point) ∈ 𝒮.Ω 0)
    (hn : ¬InNonconstantCell Q u) (u' : 𝒮.FineSite) (hu' : u' ∈ cellAndNeighbours u) :
    Q.largeCutoff (u' : 𝒮.Point) = Q.largeCutoff (u : 𝒮.Point) := by
  by_contra hne
  obtain ⟨h₁, h₂⟩ := centreOfSite_spec H.cellFacts u h₀
  exact hn ⟨_, ⟨h₁, u, h₂, u', hu', hne⟩, h₂⟩
theorem gaugeLap_eq_zero_of_not_mem {𝒯 : NestedRegions} (A : CellStructure.AdjointFacts 𝒯)
    {u : 𝒯.FineSite} (hu : (u : 𝒯.Point) ∉ 𝒯.Ω 0) (G : 𝒯.FineSite → ℝ) : gaugeLap G u = 0 := by
  have e₁ : dirichletLap G u = 0 :=
    indicator_of_notMem (s := {x : 𝒯.FineSite | (x : 𝒯.Point) ∈ 𝒯.Ω 0}) hu _
  have e₂ := (A.avgAdj_apply (weightMul (blockAvg G))).1 u hu
  simp only [gaugeLap, Pi.add_apply, e₁, e₂, add_zero]
theorem largeCutoff_eq_zero_of_not_mem {u : 𝒮.FineSite} (hu : (u : 𝒮.Point) ∉ 𝒮.Ω 0) :
    Q.largeCutoff (u : 𝒮.Point) = 0 :=
  H.largeCutoff_eq_zero fun h => hu (H.mem_Ω_zero_of_thicken u (H.mem_thicken_five_sixths h))
theorem gaugeStencil_zero {𝒯 : NestedRegions} (x : 𝒯.FineSite) :
    gaugeStencil 𝒯 (fun _ => 0) x = 0 := by
  simp [gaugeStencil, latticeLaplacian_apply]
theorem pushLapCommutator_eq_zero (f : (CubeTorus.torusSetting Q).FineSite → ℝ) (u : 𝒮.FineSite)
    (hn : ¬InNonconstantCell Q u) : pushLapCommutator Q f u = 0 := by
  by_cases h₀ : (u : 𝒮.Point) ∈ 𝒮.Ω 0
  · have hself : u ∈ cellAndNeighbours u := Or.inl (centreOfSite_spec H.cellFacts u h₀).2
    have hc := H.largeCutoff_eq_of_not_inNonconstantCell h₀ hn
    by_cases ht : Q.largeCutoff (u : 𝒮.Point) = 0
    · have hG : ∀ x ∈ cellAndNeighbours u, cutoffPush Q f x = 0 := fun x hx => by
        change Q.largeCutoff (x : 𝒮.Point) * _ = 0
        rw [hc x hx, ht, zero_mul]
      change Q.largeCutoff (u : 𝒮.Point) * _ - gaugeLap (cutoffPush Q f) u = 0
      rw [ht, zero_mul, gaugeLap_eq_gaugeStencil H.adjointFacts _ u h₀
        (fun ν => Or.inr (hG _ (add_mem_cellAndNeighbours u ν)))
        (fun ν => Or.inr (hG _ (sub_mem_cellAndNeighbours u ν))),
        gaugeStencil_congr hself hG, H.gaugeStencil_zero, sub_zero]
    · have hu := H.mem_thicken_five_sixths (H.mem_thicken_of_ne_zero ht)
      rw [H.pushLapCommutator_eq hu]
      exact cutoffDefect_eq_zero_of_const H.lengths hself hc
  · change Q.largeCutoff (u : 𝒮.Point) * _ - gaugeLap (cutoffPush Q f) u = 0
    rw [H.largeCutoff_eq_zero_of_not_mem h₀, zero_mul,
      H.gaugeLap_eq_zero_of_not_mem H.adjointFacts h₀, sub_zero]
theorem centreOfSite_mem_cellAndNeighbours {u : 𝒮.FineSite} (h₀ : (u : 𝒮.Point) ∈ 𝒮.Ω 0) :
    (⟨𝒮.centreOfSite u, mem_spacingLattice_of_mem_allCentres
        (centreOfSite_spec H.cellFacts u h₀).1⟩ : 𝒮.FineSite) ∈ cellAndNeighbours u :=
  Or.inl (mem_cellOf_self _)
theorem largeCutoff_centreOfSite_eq {u : 𝒮.FineSite} (h₀ : (u : 𝒮.Point) ∈ 𝒮.Ω 0)
    (hn : ¬InNonconstantCell Q u) :
    Q.largeCutoff (𝒮.centreOfSite u) = Q.largeCutoff (u : 𝒮.Point) :=
  H.largeCutoff_eq_of_not_inNonconstantCell h₀ hn
    ⟨𝒮.centreOfSite u, mem_spacingLattice_of_mem_allCentres (centreOfSite_spec H.cellFacts u h₀).1⟩
    (H.centreOfSite_mem_cellAndNeighbours h₀)
theorem pushAvgDefect_eq_zero (ω : (CubeTorus.torusSetting Q).Coarse) (u : 𝒮.FineSite)
    (hn : ¬InNonconstantCell Q u) : pushAvgDefect Q ω u = 0 := by
  by_cases h₀ : (u : 𝒮.Point) ∈ 𝒮.Ω 0
  · have hc := H.largeCutoff_centreOfSite_eq h₀ hn
    by_cases ht : Q.largeCutoff (u : 𝒮.Point) = 0
    · change Q.largeCutoff (u : 𝒮.Point) * _ - blockAvgAdj (coarsePush Q ω) u = 0
      obtain ⟨h₂, e₂⟩ := (H.adjointFacts.avgAdj_apply (coarsePush Q ω)).2 u h₀
      have e₃ : coarsePush Q ω ⟨_, h₂⟩ = 0 := by
        unfold coarsePush
        split_ifs with h
        · change Q.largeCutoff (𝒮.centreOfSite u) * _ = 0
          rw [hc, ht, zero_mul]
        · rfl
      rw [e₂, e₃, ht, zero_mul, sub_zero]
    · have hu := H.mem_thicken_five_sixths (H.mem_thicken_of_ne_zero ht)
      obtain ⟨h, e⟩ := H.pushAvgDefect_eq hu ω
      rw [e, hc, sub_self, zero_mul]
  · change Q.largeCutoff (u : 𝒮.Point) * _ - blockAvgAdj (coarsePush Q ω) u = 0
    rw [H.largeCutoff_eq_zero_of_not_mem h₀, zero_mul, (H.adjointFacts.avgAdj_apply _).1 u h₀,
      sub_zero]
theorem false_of_no_near_preimage {w : (CubeTorus.torusSetting Q).FineSite}
    (hex : ¬∃ u : 𝒮.FineSite, (u : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧ Q.system.mapSite u = w)
    {x₀ : 𝒮.Point} (hx₀ : x₀ ∈ Q.thicken (2 / 3)) {y' : Q.system.setting.Point}
    (hy' : y' ∈ Q.system.setting.allCentres)
    (hw : (w : Q.system.setting.Point) ∈ Q.system.setting.cellOf y')
    (hc : Q.system.embed x₀ ∈ Q.system.setting.cellOf y') : False := by
  have hthick := H.mem_thicken_five_sixths hx₀
  have hm : CubeGeometry.TorusCellMeetsThicken Q y' := ⟨_, hc, x₀, hthick, rfl⟩
  obtain ⟨y, hy, hym, hcar⟩ := H.agreement.cell_onto y' hy' hm
  have hw' := hw
  rw [← hcar.1] at hw' hc
  obtain ⟨x₂, hx₂, e₂⟩ := hw'
  obtain ⟨x₄, hx₄, e₄⟩ := hc
  have hin := H.cellOf_subset_strictPts hy hym
  have hx₄' : x₄ = x₀ :=
    H.facts.embed_bijective.injOn (hin hx₄) (H.mem_strictPts_of_thicken hthick) e₄
  subst hx₄'
  obtain ⟨x₃, rfl, e₃⟩ := H.exists_fineSite_of_embed (hin hx₂) w e₂.symm
  refine hex ⟨x₃, H.mem_thicken_of_near' (by norm_num) hx₀ ?_, e₃⟩
  have h₁ := H.norm_sub_le_of_mem_cellOf_pair hy hym hx₂ hx₄
  have h₂ := H.scale_succ_small
  have h₃ := norm_nonneg ((x₃ : 𝒮.Point) - x₄)
  linarith
theorem pullLapCommutator_eq_zero (g : 𝒮.FineSite → ℝ) (w : (CubeTorus.torusSetting Q).FineSite)
    (hw : ∀ u : 𝒮.FineSite, InNonconstantCell Q u → Q.system.mapSite u ≠ w) :
    pullLapCommutator Q g w = 0 := by
  by_cases hex : ∃ u : 𝒮.FineSite, (u : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧ Q.system.mapSite u = w
  · obtain ⟨u, hu, rfl⟩ := hex
    have hN := H.nearSite_of_mem hu
    rw [H.pullLapCommutator_mapSite hu]
    exact cutoffDefect_eq_zero_of_const H.lengths (Or.inl hN.mem)
      (H.largeCutoff_eq_of_not_inNonconstantCell hN.omega fun h => hw u h rfl)
  · have hz : ∀ (G : 𝒮.FineSite → ℝ) (w' : (CubeTorus.torusSetting Q).FineSite),
        (∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ tsupport Q.largeCutoff →
          Q.system.mapSite x ≠ w') → cutoffPull Q G w' = 0 :=
      fun G w' h => H.pullSites_eq_zero G w' h
    have hthick : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ tsupport Q.largeCutoff →
        (x : 𝒮.Point) ∈ Q.thicken (5 / 6) := fun x h => H.mem_thicken_of_tsupport h
    have hξ := H.ξ_small
    have hself : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ tsupport Q.largeCutoff →
        Q.system.mapSite x ≠ w := fun x h e => hex ⟨x, hthick x h, e⟩
    have hplus : ∀ ν,
        cutoffPull Q g (w + unitStep 4 Q.system.setting.side Q.system.setting.ξ ν) = 0 := by
      intro ν
      refine hz _ _ fun x h e => ?_
      have hx₂ := H.cutoff.outer_support h
      have e₁ := H.mapSite_sub_unitStep x ν (H.norm_add_two_ξ_lt_of_thicken (hthick x h))
      rw [e, add_sub_cancel_right] at e₁
      refine hex ⟨x - unitStep 4 𝒮.side 𝒮.ξ ν, H.mem_thicken_of_near' (by norm_num) hx₂ ?_, e₁⟩
      rw [AddSubgroup.coe_sub, sub_sub_cancel_left, norm_neg]
      linarith [norm_unitStep_le (𝒮 := 𝒮) ν, H.mollifyRadius_pos]
    have hminus : ∀ ν,
        cutoffPull Q g (w - unitStep 4 Q.system.setting.side Q.system.setting.ξ ν) = 0 := by
      intro ν
      refine hz _ _ fun x h e => ?_
      have hx₂ := H.cutoff.outer_support h
      have hz' := H.norm_add_two_ξ_lt_of_thicken (hthick x h)
      have e₁ := H.mapSite_add_unitStep x ν (by linarith [𝒮.ξ_pos])
      rw [e, sub_add_cancel] at e₁
      refine hex ⟨x + unitStep 4 𝒮.side 𝒮.ξ ν, H.mem_thicken_of_near' (by norm_num) hx₂ ?_, e₁⟩
      rw [AddSubgroup.coe_add, add_sub_cancel_left]
      linarith [norm_unitStep_le (𝒮 := 𝒮) ν, H.mollifyRadius_pos]
    have hcell := centreOfSite_spec H.settingCellFacts w (H.mem_setting_Ω_zero _)
    have hblock : ∀ w' ∈ Q.system.setting.fineBlock
        (Q.system.setting.level (Q.system.setting.centreOfSite w)) (Q.system.setting.centreOfSite w),
        cutoffPull Q g w' = 0 := by
      intro w' hw'
      refine hz _ _ fun x h e => ?_
      have hw'' : (w' : Q.system.setting.Point) ∈
          Q.system.setting.cellOf (Q.system.setting.centreOfSite w) := hw'
      rw [← e, H.coe_mapSite _ (H.mem_strictPts_of_thicken (hthick x h))] at hw''
      exact H.false_of_no_near_preimage hex (H.cutoff.outer_support h) hcell.1 hcell.2 hw''
    change cutoffPull Q (gaugeLap g) w - gaugeLap (cutoffPull Q g) w = 0
    rw [hz _ _ hself, gaugeLap_eq_gaugeStencil H.settingAdjointFacts _ w (H.mem_setting_Ω_zero _)
      (fun _ => Or.inl (H.mem_setting_Ω_zero _)) (fun _ => Or.inl (H.mem_setting_Ω_zero _))]
    simp only [gaugeStencil, latticeLaplacian_apply, hplus, hminus, hz g w hself]
    rw [finsum_mem_congr rfl hblock]
    simp
theorem pullAvgDefect_eq_zero (ω : 𝒮.Coarse) (w : (CubeTorus.torusSetting Q).FineSite)
    (hw : ∀ u : 𝒮.FineSite, InNonconstantCell Q u → Q.system.mapSite u ≠ w) :
    pullAvgDefect Q ω w = 0 := by
  by_cases hex : ∃ u : 𝒮.FineSite, (u : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧ Q.system.mapSite u = w
  · obtain ⟨u, hu, rfl⟩ := hex
    have hN := H.nearSite_of_mem hu
    obtain ⟨h, e⟩ := H.pullAvgDefect_mapSite hu ω
    have hc := H.largeCutoff_centreOfSite_eq hN.omega fun h => hw u h rfl
    rw [e, hc, sub_self, zero_mul]
  · change cutoffPull Q (blockAvgAdj ω) w - blockAvgAdj (coarsePull Q ω) w = 0
    have e₁ : cutoffPull Q (blockAvgAdj ω) w = 0 :=
      H.pullSites_eq_zero _ w fun x h e => hex ⟨x, H.mem_thicken_of_tsupport h, e⟩
    obtain ⟨h₂, e₂⟩ := (H.settingAdjointFacts.avgAdj_apply (coarsePull Q ω)).2 w
      (H.mem_setting_Ω_zero _)
    have hcell := centreOfSite_spec H.settingCellFacts w (H.mem_setting_Ω_zero _)
    have e₃ : coarsePull Q ω ⟨_, h₂⟩ = 0 := by
      unfold coarsePull
      have : ∀ y ∈ {y : 𝒮.allCentres | (y : 𝒮.Point) ∈ tsupport Q.largeCutoff ∧
          Q.system.embed y = Q.system.setting.centreOfSite w},
          Q.largeCutoff (y : 𝒮.Point) * ω y = 0 := by
        rintro y ⟨h₁, h₃⟩
        by_cases ht : Q.largeCutoff (y : 𝒮.Point) = 0
        · rw [ht, zero_mul]
        · exfalso
          refine H.false_of_no_near_preimage hex (H.mem_thicken_of_ne_zero ht) hcell.1 hcell.2 ?_
          rw [h₃]
          exact mem_cellOf_self _
      rw [finsum_mem_congr rfl this]
      simp
    rw [e₁, e₂, e₃, sub_zero]
end FirstTypeData
theorem latticeLaplacian_mul_sub {S ξ : ℝ} (φ F : LatticeSite 4 S ξ → ℝ) (u : LatticeSite 4 S ξ) :
    φ u * latticeLaplacian F u - latticeLaplacian (fun x => φ x * F x) u =
      ∑ ν, (forwardDiff ν φ u * forwardDiff ν F u + backwardDiff ν φ u * backwardDiff ν F u -
        backwardDiff ν (forwardDiff ν φ) u * F u) := by
  rw [latticeLaplacian_apply, latticeLaplacian_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [forwardDiff, backwardDiff, sub_add_cancel]
  ring
theorem cutoffDefect_eq (hl : TorusLengthsStatement) (φ F : 𝒮.FineSite → ℝ) (u : 𝒮.FineSite) :
    cutoffDefect 𝒮 φ F u = (φ u * latticeLaplacian F u - latticeLaplacian (fun x => φ x * F x) u) +
      levelWeight 𝒮 (𝒮.centreOfSite u) *
        ∑ᶠ x ∈ 𝒮.fineBlock (𝒮.level (𝒮.centreOfSite u)) (𝒮.centreOfSite u), (φ u - φ x) * F x := by
  have := finite_fineSite hl 𝒮
  have hfin : (𝒮.fineBlock (𝒮.level (𝒮.centreOfSite u)) (𝒮.centreOfSite u)).Finite :=
    Set.toFinite _
  simp only [cutoffDefect, gaugeStencil]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
theorem abs_finsum_fineBlock_le (hl : TorusLengthsStatement) (hcell : CellStructure.CellStructureClaim)
    {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) (G : 𝒮.FineSite → ℝ) (b : ℝ)
    (h : ∀ x ∈ 𝒮.fineBlock (𝒮.level y) y, |G x| ≤ b) :
    |∑ᶠ x ∈ 𝒮.fineBlock (𝒮.level y) y, G x| ≤ (𝒮.L : ℝ) ^ (𝒮.level y * 4) * b := by
  have := finite_fineSite hl 𝒮
  have hfin : (𝒮.fineBlock (𝒮.level y) y).Finite := Set.toFinite _
  have hsites := mem_centresAt_level hy
  have hcard := ((hcell 𝒮).1.block_sites (𝒮.level y) (le_s_of_mem_centresAt hsites) y
    (mem_spacingLattice_of_mem_centresAt hsites)).2
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h₁ := Finset.sum_le_card_nsmul hfin.toFinset (fun x => |G x|) b
    fun x hx => h x (hfin.mem_toFinset.mp hx)
  refine h₁.trans (le_of_eq ?_)
  rw [← Set.ncard_eq_toFinset_card _ hfin, hcard, nsmul_eq_mul]
  push_cast
  rfl
namespace FirstTypeData
variable {c : ℝ} {Q : LevelCube 𝒮 M} (H : FirstTypeData c Q)
include H
theorem inv_mollifyRadius :
    (mollifyRadius 𝒮 M Q.level)⁻¹ = 6 * (𝒮.L : ℝ) * (M : ℝ)⁻¹ * (𝒮.scale Q.level)⁻¹ := by
  have hL := H.thirteen_le_L_real
  have hM := H.one_le_M
  have hx := scale_pos 𝒮 Q.level
  rw [H.mollifyRadius_eq]
  field_simp
theorem const_pos : 0 < c := by linarith [H.one_le]
theorem abs_largeCutoff_sub_le {x x' : 𝒮.Point} {σ : ℝ} (h : ‖x - x'‖ ≤ σ) :
    |Q.largeCutoff x - Q.largeCutoff x'| ≤ c * (mollifyRadius 𝒮 M Q.level)⁻¹ * (4 * σ) := by
  have h₁ := H.bounded.lipschitz x x'
  have h₂ := ((H.lengths 4 𝒮.side 𝒮.side_pos).1).lOneNorm_le_supNorm (x - x')
  rw [supNorm_eq_norm] at h₂
  have hr := H.mollifyRadius_pos
  have hc := H.const_pos
  refine h₁.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  push_cast at h₂
  linarith
theorem backwardDiff_eq_neg (F : 𝒮.FineSite → ℝ) (u : 𝒮.FineSite) (ν : Fin 4) :
    backwardDiff ν F u = -forwardDiff ν F (u - unitStep 4 𝒮.side 𝒮.ξ ν) := by
  simp only [forwardDiff, backwardDiff, sub_add_cancel]
  ring
theorem abs_latticeLaplacian_defect_le {u : 𝒮.FineSite} (hself : u ∈ cellAndNeighbours u)
    (F : 𝒮.FineSite → ℝ) (a b : ℝ) (hF : ∀ x ∈ cellAndNeighbours u, |F x| ≤ a)
    (hd₁ : ∀ ν, |forwardDiff ν F u| ≤ b)
    (hd₂ : ∀ ν, |forwardDiff ν F (u - unitStep 4 𝒮.side 𝒮.ξ ν)| ≤ b) :
    |Q.largeCutoff (u : 𝒮.Point) * latticeLaplacian F u -
        latticeLaplacian (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point) * F x) u| ≤
      4 * (c * (mollifyRadius 𝒮 M Q.level)⁻¹ * b + c * (mollifyRadius 𝒮 M Q.level)⁻¹ * b +
        c * (mollifyRadius 𝒮 M Q.level)⁻¹ ^ 2 * a) := by
  have hc := H.const_pos
  have hr := H.mollifyRadius_pos
  have hP := latticeLaplacian_mul_sub (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) F u
  refine (le_of_eq (congrArg abs hP)).trans ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ ν : Fin 4,
      |forwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) u * forwardDiff ν F u +
        backwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) u *
          backwardDiff ν F u -
        backwardDiff ν (forwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point))) u *
          F u| ≤
      c * (mollifyRadius 𝒮 M Q.level)⁻¹ * b + c * (mollifyRadius 𝒮 M Q.level)⁻¹ * b +
        c * (mollifyRadius 𝒮 M Q.level)⁻¹ ^ 2 * a := by
    intro ν
    have t₁ : |forwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) u| ≤
        c * (mollifyRadius 𝒮 M Q.level)⁻¹ :=
      H.bounded.difference (forwardDiff ν) ⟨ν, Or.inl rfl⟩ u
    have t₂ : |backwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) u| ≤
        c * (mollifyRadius 𝒮 M Q.level)⁻¹ :=
      H.bounded.difference (backwardDiff ν) ⟨ν, Or.inr rfl⟩ u
    have t₃ : |backwardDiff ν
        (forwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point))) u| ≤
        c * (mollifyRadius 𝒮 M Q.level)⁻¹ ^ 2 :=
      H.bounded.second_difference (backwardDiff ν) (forwardDiff ν) ⟨ν, Or.inr rfl⟩
        ⟨ν, Or.inl rfl⟩ u
    have t₄ : |backwardDiff ν F u| ≤ b := by
      rw [H.backwardDiff_eq_neg, abs_neg]
      exact hd₂ ν
    have t₅ := hF u hself
    have s₁ := abs_mul (forwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) u)
      (forwardDiff ν F u)
    have s₂ := abs_mul (backwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) u)
      (backwardDiff ν F u)
    have s₃ := abs_mul
      (backwardDiff ν (forwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point))) u) (F u)
    have m₁ := mul_le_mul t₁ (hd₁ ν) (abs_nonneg _) (by positivity)
    have m₂ := mul_le_mul t₂ t₄ (abs_nonneg _) (by positivity)
    have m₃ := mul_le_mul t₃ t₅ (abs_nonneg _) (by positivity)
    refine (abs_sub _ _).trans ?_
    have := abs_add_le
      (forwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) u * forwardDiff ν F u)
      (backwardDiff ν (fun x : 𝒮.FineSite => Q.largeCutoff (x : 𝒮.Point)) u * backwardDiff ν F u)
    linarith
  refine (Finset.sum_le_sum fun ν _ => hterm ν).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
theorem abs_block_defect_le {u : 𝒮.FineSite} (hN : NearSite Q u) (F : 𝒮.FineSite → ℝ) (a : ℝ)
    (hF : ∀ x ∈ cellAndNeighbours u, |F x| ≤ a) :
    |levelWeight 𝒮 (𝒮.centreOfSite u) *
        ∑ᶠ x ∈ 𝒮.fineBlock (𝒮.level (𝒮.centreOfSite u)) (𝒮.centreOfSite u),
          (Q.largeCutoff (u : 𝒮.Point) - Q.largeCutoff (x : 𝒮.Point)) * F x| ≤
      4 * c * (mollifyRadius 𝒮 M Q.level)⁻¹ * (𝒮.scale Q.level)⁻¹ * a := by
  have hc := H.const_pos
  have hr := H.mollifyRadius_pos
  have hL := H.thirteen_le_L_real
  have hX := scale_pos 𝒮 Q.level
  have ha : 0 ≤ a := (abs_nonneg _).trans (hF u (Or.inl hN.mem))
  obtain ⟨y, hyd⟩ : ∃ y, y = 𝒮.centreOfSite u := ⟨_, rfl⟩
  rw [← hyd]
  have hy : y ∈ 𝒮.allCentres := hyd ▸ hN.site
  have hm : CubeGeometry.CellMeetsThicken Q y := hyd ▸ hN.meets
  have hmem : (u : 𝒮.Point) ∈ 𝒮.cellOf y := hyd ▸ hN.mem
  have hσX := H.scale_le_levelScale hy hm
  obtain ⟨σ, hσd⟩ : ∃ σ, σ = 𝒮.levelScale y := ⟨_, rfl⟩
  rw [← hσd] at hσX
  have hσ0 : 0 < σ := lt_of_lt_of_le hX hσX
  have hB : ∀ x ∈ 𝒮.fineBlock (𝒮.level y) y,
      |(Q.largeCutoff (u : 𝒮.Point) - Q.largeCutoff (x : 𝒮.Point)) * F x| ≤
      c * (mollifyRadius 𝒮 M Q.level)⁻¹ * (4 * σ) * a := by
    intro x hx
    have hx' : (x : 𝒮.Point) ∈ 𝒮.cellOf y := hx
    have h₁ := norm_sub_le_of_mem_cellOf hmem
    have h₂ := norm_sub_le_of_mem_cellOf hx'
    rw [← hσd] at h₁ h₂
    have h₃ : ‖(u : 𝒮.Point) - (x : 𝒮.Point)‖ ≤ σ := by
      have e : (u : 𝒮.Point) - (x : 𝒮.Point) = ((u : 𝒮.Point) - y) - ((x : 𝒮.Point) - y) := by
        abel
      rw [e]
      linarith [norm_sub_le ((u : 𝒮.Point) - y) ((x : 𝒮.Point) - y)]
    rw [abs_mul]
    exact mul_le_mul (H.abs_largeCutoff_sub_le h₃) (hF x (Or.inl (hyd ▸ hx))) (abs_nonneg _)
      (by positivity)
  have hS := abs_finsum_fineBlock_le H.lengths H.cells hy _ _ hB
  have hw := ((H.cells 𝒮).2.2.2.2.2.2.1 (𝒮.level y))
  have hw₀ : 0 ≤ blockWeights 𝒮.L (𝒮.level y) := by
    have : ((𝒮.L : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    linarith [hw.1]
  have hσ' : 𝒮.scale (𝒮.level y) = σ := hσd.symm
  have hW : 0 ≤ levelWeight 𝒮 y := by
    simp only [levelWeight, hσ']
    positivity
  rw [abs_mul, abs_of_nonneg hW]
  refine (mul_le_mul_of_nonneg_left hS hW).trans ?_
  have e : levelWeight 𝒮 y * ((𝒮.L : ℝ) ^ (𝒮.level y * 4) *
        (c * (mollifyRadius 𝒮 M Q.level)⁻¹ * (4 * σ) * a)) =
      blockWeights 𝒮.L (𝒮.level y) * (4 * c * (mollifyRadius 𝒮 M Q.level)⁻¹ * σ⁻¹ * a) := by
    simp only [levelWeight, hσ']
    generalize (mollifyRadius 𝒮 M Q.level)⁻¹ = ri
    generalize blockWeights 𝒮.L (𝒮.level y) = w
    field_simp
  rw [e]
  have hinv : σ⁻¹ ≤ (𝒮.scale Q.level)⁻¹ := inv_anti₀ hX hσX
  have h₁ : 4 * c * (mollifyRadius 𝒮 M Q.level)⁻¹ * σ⁻¹ * a ≤
      4 * c * (mollifyRadius 𝒮 M Q.level)⁻¹ * (𝒮.scale Q.level)⁻¹ * a := by
    have : 0 ≤ 4 * c * (mollifyRadius 𝒮 M Q.level)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv this) ha
  have h₂ : 0 ≤ 4 * c * (mollifyRadius 𝒮 M Q.level)⁻¹ * σ⁻¹ * a := by positivity
  nlinarith [hw.2]
theorem defect_constant_le {cc l m x a b ri : ℝ} (hc : 0 < cc) (hl : 13 ≤ l) (hm0 : 0 < m)
    (hm1 : m ≤ 1) (hx : 0 < x) (ha : 0 ≤ a) (hb : 0 ≤ b) (hri : ri = 6 * l * m * x) :
    4 * (cc * ri * b + cc * ri * b + cc * ri ^ 2 * a) + 4 * cc * ri * x * a ≤
      216 * cc * l ^ 2 * m * (x * b + x ^ 2 * a) := by
  subst hri
  have P : 0 ≤ cc * m * x * b := by positivity
  have R : 0 ≤ cc * m * x ^ 2 * a := by positivity
  have h₁ : 48 * l ≤ 216 * l ^ 2 := by nlinarith
  have h₂ : 144 * l ^ 2 * m + 24 * l ≤ 216 * l ^ 2 := by nlinarith [sq_nonneg l]
  have q₁ := mul_le_mul_of_nonneg_right h₁ P
  have q₂ := mul_le_mul_of_nonneg_right h₂ R
  nlinarith [q₁, q₂]
theorem abs_cutoffDefect_le {u : 𝒮.FineSite} (hN : NearSite Q u) (F : 𝒮.FineSite → ℝ) (a b : ℝ)
    (hF : ∀ x ∈ cellAndNeighbours u, |F x| ≤ a) (hd₁ : ∀ ν, |forwardDiff ν F u| ≤ b)
    (hd₂ : ∀ ν, |forwardDiff ν F (u - unitStep 4 𝒮.side 𝒮.ξ ν)| ≤ b) :
    |cutoffDefect 𝒮 (fun x => Q.largeCutoff (x : 𝒮.Point)) F u| ≤
      216 * c * (𝒮.L : ℝ) ^ 2 * (M : ℝ)⁻¹ *
        ((CubeTorus.levelSpacing Q)⁻¹ * b + (CubeTorus.levelSpacing Q ^ 2)⁻¹ * a) := by
  have hself : u ∈ cellAndNeighbours u := Or.inl hN.mem
  have hM := H.one_le_M
  have hX := scale_pos 𝒮 Q.level
  have ha : 0 ≤ a := (abs_nonneg _).trans (hF u hself)
  have hb : 0 ≤ b := (abs_nonneg _).trans (hd₁ 0)
  have hscale : CubeTorus.levelSpacing Q = 𝒮.scale Q.level := rfl
  rw [cutoffDefect_eq H.lengths]
  refine (abs_add_le _ _).trans ((add_le_add
    (H.abs_latticeLaplacian_defect_le hself F a b hF hd₁ hd₂)
    (H.abs_block_defect_le hN F a hF)).trans ?_)
  rw [hscale, ← inv_pow]
  exact H.defect_constant_le H.const_pos H.thirteen_le_L_real (by positivity)
    (inv_le_one_of_one_le₀ hM) (by positivity) ha hb (by rw [H.inv_mollifyRadius])
theorem abs_largeCutoff_sub_centre_le {u : 𝒮.FineSite} (hN : NearSite Q u) :
    |Q.largeCutoff (u : 𝒮.Point) - Q.largeCutoff (𝒮.centreOfSite u)| ≤
      216 * c * (𝒮.L : ℝ) ^ 2 * (M : ℝ)⁻¹ := by
  have hc := H.const_pos
  have hL := H.thirteen_le_L_real
  have hM := H.one_le_M
  have hX := scale_pos 𝒮 Q.level
  have h₁ := norm_sub_le_of_mem_cellOf hN.mem
  have h₂ := H.levelScale_le_scale_succ hN.site hN.meets
  have h₃ : ‖(u : 𝒮.Point) - 𝒮.centreOfSite u‖ ≤ 𝒮.scale (Q.level + 1) / 2 := by linarith
  refine (H.abs_largeCutoff_sub_le h₃).trans ?_
  rw [H.inv_mollifyRadius, H.scale_level_succ]
  have e : c * (6 * (𝒮.L : ℝ) * (M : ℝ)⁻¹ * (𝒮.scale Q.level)⁻¹) *
      (4 * ((𝒮.L : ℝ) * 𝒮.scale Q.level / 2)) = 12 * c * (𝒮.L : ℝ) ^ 2 * (M : ℝ)⁻¹ := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ c * (𝒮.L : ℝ) ^ 2 * (M : ℝ)⁻¹ := by positivity
  nlinarith
theorem forwardDiff_mapSite {x : 𝒮.FineSite} (f : (CubeTorus.torusSetting Q).FineSite → ℝ)
    (ν : Fin 4) (hz : ‖(x : 𝒮.Point) - Q.centre‖ + 𝒮.ξ < cubeSide 𝒮 M Q.level) :
    forwardDiff ν (fun x => f (Q.system.mapSite x)) x = forwardDiff ν f (Q.system.mapSite x) := by
  simp only [forwardDiff]
  rw [H.mapSite_add_unitStep x ν hz]
  have e : Q.system.setting.ξ⁻¹ = 𝒮.ξ⁻¹ := by rw [H.setting_ξ_eq]
  rw [e]
theorem abs_le_fieldModulusAt {S ξ : ℝ} (G : BondField 4 S ξ) (x : LatticeSite 4 S ξ) (ν : Fin 4) :
    |G ν x| ≤ fieldModulusAt G x :=
  le_ciSup (f := fun μ => |G μ x|) (Set.finite_range _).bddAbove ν
theorem bounds : Bounds (216 * c * (𝒮.L : ℝ) ^ 2) Q where
  cellOf_subset_annulus := fun y hy => H.cellOf_subset_annulus hy
  encard_le := H.encard_nonconstantCells_le
  pushLapCommutator_eq_zero := H.pushLapCommutator_eq_zero
  pushAvgDefect_eq_zero := H.pushAvgDefect_eq_zero
  pushLapCommutator_le := by
    intro f u a b hin ha hb
    have hu := H.mem_thicken_of_inNonconstantCell hin
    have hN := H.nearSite_of_mem hu
    have hz := H.norm_add_two_ξ_lt hN
    have hξ := 𝒮.ξ_pos
    rw [H.pushLapCommutator_eq hu]
    refine H.abs_cutoffDefect_le hN _ a b ha (fun ν => ?_) fun ν => ?_
    · rw [H.forwardDiff_mapSite f ν (by linarith)]
      exact (H.abs_le_fieldModulusAt (Dirichlet.grad f) _ ν).trans (hb u (Or.inl hN.mem))
    · rw [H.forwardDiff_mapSite f ν (by
        rw [AddSubgroup.coe_sub]
        linarith [H.norm_sub_unitStep_sub_centre (u : 𝒮.Point) ν])]
      exact (H.abs_le_fieldModulusAt (Dirichlet.grad f) _ ν).trans
        (hb _ (sub_mem_cellAndNeighbours u ν))
  pushAvgDefect_le := by
    intro ω u y a hy huy ha hω
    have hu := (H.cellOf_subset_annulus hy huy).1
    have hN := H.nearSite_of_mem hu
    have hcen : 𝒮.centreOfSite u = y := centreOfSite_eq H.cellFacts u hy.1 huy
    obtain ⟨h, e⟩ := H.pushAvgDefect_eq hu ω
    rw [e, abs_mul]
    have h₁ := H.abs_largeCutoff_sub_centre_le hN
    have h₂ := hω ⟨_, h⟩ (congrArg Q.system.embed hcen)
    exact mul_le_mul h₁ h₂ (abs_nonneg _) ((abs_nonneg _).trans h₁)
  pullLapCommutator_eq_zero := H.pullLapCommutator_eq_zero
  pullAvgDefect_eq_zero := H.pullAvgDefect_eq_zero
  pullLapCommutator_le := by
    intro g u a b hin ha hb
    have hu := H.mem_thicken_of_inNonconstantCell hin
    have hN := H.nearSite_of_mem hu
    rw [H.pullLapCommutator_mapSite hu]
    refine H.abs_cutoffDefect_le hN _ a b ha (fun ν => ?_) fun ν => ?_
    · exact (H.abs_le_fieldModulusAt (Dirichlet.grad g) _ ν).trans (hb u (Or.inl hN.mem))
    · exact (H.abs_le_fieldModulusAt (Dirichlet.grad g) _ ν).trans
        (hb _ (sub_mem_cellAndNeighbours u ν))
  pullAvgDefect_le := by
    intro ω u y hy huy
    have hu := (H.cellOf_subset_annulus hy huy).1
    have hN := H.nearSite_of_mem hu
    have hcen : 𝒮.centreOfSite u = y := centreOfSite_eq H.cellFacts u hy.1 huy
    obtain ⟨h, e⟩ := H.pullAvgDefect_mapSite hu ω
    have hω : ω ⟨_, h⟩ = ω y := congrArg ω (Subtype.ext hcen)
    rw [e, hω, abs_mul]
    exact mul_le_mul_of_nonneg_right (H.abs_largeCutoff_sub_centre_le hN) (abs_nonneg _)
end FirstTypeData
end YangMills.Construction.CubeTorusComparison.CutoffDefects
