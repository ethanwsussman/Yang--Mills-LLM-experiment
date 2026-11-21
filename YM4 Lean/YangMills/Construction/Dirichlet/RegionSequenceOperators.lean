import YangMills.Construction.Dirichlet.LatticeCalculus
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.RegionSequence
def adjointValue {V W : Type} [Nonempty V] (X : Set V) (p : V → V → ℝ) (q : W → W → ℝ) (T : V → W)
    (w : W) : V :=
  Classical.epsilon fun v => v ∈ X ∧ ∀ u ∈ X, p v u = q w (T u)
def orthProjValue {V : Type} [Nonempty V] [Sub V] (Y : Set V) (p : V → V → ℝ) (f : V) : V :=
  Classical.epsilon fun r => r ∈ Y ∧ ∀ w ∈ Y, p (f - r) w = 0
def inverseValue {V : Type} [Nonempty V] (X : Set V) (T : V → V) (f : V) : V :=
  Classical.epsilon fun g => g ∈ X ∧ T g = f
def gaugeParam : ℝ := 1
structure NestedRegions where
  L : ℕ
  odd_L : Odd L
  thirteen_le_L : 13 ≤ L
  ξ : ℝ
  ξ_pos : 0 < ξ
  side : ℝ
  side_pos : 0 < side
  s : ℕ
  side_mem_zmultiples : ∃ k : ℤ, side = (k : ℝ) * (2 * scaleSpacing L ξ s)
  Ω : ℕ → Set (PeriodicTorus 4 side)
  Ω_succ_subset : ∀ n, n < s → Ω (n + 1) ⊆ Ω n
  isCubeUnion_Ω : ∀ n ≤ s, IsCubeUnion (scaleSpacing L ξ n) (Ω n)
  Ω_eq_empty : ∀ n, s < n → Ω n = ∅
  bonds : Set (LatticeBond 4 side ξ)
  mem_bonds_of_mem : ∀ b : LatticeBond 4 side ξ,
    (b.source : PeriodicTorus 4 side) ∈ Ω 0 → (b.target : PeriodicTorus 4 side) ∈ Ω 0 → b ∈ bonds
  mem_of_mem_bonds : ∀ b ∈ bonds,
    (b.source : PeriodicTorus 4 side) ∈ Ω 0 ∨ (b.target : PeriodicTorus 4 side) ∈ Ω 0
namespace NestedRegions
variable (𝒮 : NestedRegions)
abbrev Point : Type := PeriodicTorus 4 𝒮.side
abbrev FineSite : Type := LatticeSite 4 𝒮.side 𝒮.ξ
abbrev FineBond : Type := LatticeBond 4 𝒮.side 𝒮.ξ
abbrev FinePlaquette : Type := 𝒮.FineSite × {p : Fin 4 × Fin 4 // p.1 < p.2}
def scale (n : ℕ) : ℝ := scaleSpacing 𝒮.L 𝒮.ξ n
abbrev SiteAt (n : ℕ) : Type := LatticeSite 4 𝒮.side (𝒮.scale n)
abbrev BondAt (n : ℕ) : Type := LatticeBond 4 𝒮.side (𝒮.scale n)
def shellOf (n : ℕ) : Set 𝒮.Point := shell 𝒮.Ω n
def centresAt (n : ℕ) : Set 𝒮.Point := shellSites 𝒮.L 𝒮.ξ 𝒮.Ω n
def allCentres : Set 𝒮.Point := unionShellSites 𝒮.L 𝒮.ξ 𝒮.s 𝒮.Ω
def level (y : 𝒮.Point) : ℕ := shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y
def levelScale (y : 𝒮.Point) : ℝ := shellSpacing 𝒮.L 𝒮.ξ 𝒮.Ω y
def cellOf (y : 𝒮.Point) : Set 𝒮.Point := siteCube 𝒮.L 𝒮.ξ 𝒮.Ω y
def centreOfSite (x : 𝒮.FineSite) : 𝒮.Point :=
  Classical.epsilon fun y => y ∈ 𝒮.allCentres ∧ (x : 𝒮.Point) ∈ 𝒮.cellOf y
def fineBlock (n : ℕ) (y : 𝒮.Point) : Set 𝒮.FineSite :=
  {x | (x : 𝒮.Point) ∈ cubeAt y (𝒮.scale n)}
open Classical in
def anchor (b : 𝒮.FineBond) : 𝒮.FineSite :=
  if (b.source : 𝒮.Point) ∉ 𝒮.Ω 0 ∧ (b.target : 𝒮.Point) ∈ 𝒮.Ω 0 then b.target else b.source
def siteFns : Submodule ℝ (𝒮.FineSite → ℝ) where
  carrier := {f | VanishesOff (𝒮.Ω 0) f}
  add_mem' := fun hf hg x hx => by simp [hf x hx, hg x hx]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ hf x hx => by simp [hf x hx]
def oneForms : Submodule ℝ (𝒮.FineBond → ℝ) where
  carrier := {A | ∀ b, b ∉ 𝒮.bonds → A b = 0}
  add_mem' := fun hA hB b hb => by simp [hA b hb, hB b hb]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ hA b hb => by simp [hA b hb]
abbrev Tensor (r : ℕ) : Type := (Fin r → Fin 4) → 𝒮.FineBond → ℝ
abbrev Coarse : Type := 𝒮.allCentres → ℝ
variable {𝒮}
def AnchoredIn (X : Set 𝒮.Point) (b : 𝒮.FineBond) : Prop := (𝒮.anchor b : 𝒮.Point) ∈ X
def AnchorSupported (X : Set 𝒮.Point) (A : 𝒮.FineBond → ℝ) : Prop :=
  ∀ b, ¬AnchoredIn X b → A b = 0
def cellCutSite (y : 𝒮.Point) (f : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ := restrictTo (𝒮.cellOf y) f
def cellCutBond (y : 𝒮.Point) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  indicator {b | AnchoredIn (𝒮.cellOf y) b} A
def cellCutTensor {r : ℕ} (y : 𝒮.Point) (J : 𝒮.Tensor r) : 𝒮.Tensor r :=
  fun ν => cellCutBond y (J ν)
def pointCut (y : 𝒮.allCentres) (ω : 𝒮.Coarse) : 𝒮.Coarse := indicator {y} ω
def bondInner (A A' : 𝒮.FineBond → ℝ) : ℝ := 𝒮.ξ ^ 4 * ∑ᶠ b, A b * A' b
def tensorInner {r : ℕ} (J J' : 𝒮.Tensor r) : ℝ := ∑ ν, bondInner (J ν) (J' ν)
def coarseInner (ω ω' : 𝒮.Coarse) : ℝ :=
  ∑ᶠ y : 𝒮.allCentres, 𝒮.levelScale y ^ 4 * ω y * ω' y
def plaqInner (F F' : 𝒮.FinePlaquette → ℝ) : ℝ := 𝒮.ξ ^ 4 * ∑ᶠ p, F p * F' p
def bondL2 (A : 𝒮.FineBond → ℝ) : ℝ := √(bondInner A A)
def tensorL2 {r : ℕ} (J : 𝒮.Tensor r) : ℝ := √(tensorInner J J)
def shiftUp (ν : Fin 4) (b : 𝒮.FineBond) : 𝒮.FineBond :=
  ⟨b.source + unitStep 4 𝒮.side 𝒮.ξ ν, b.dir⟩
def shiftDown (ν : Fin 4) (b : 𝒮.FineBond) : 𝒮.FineBond :=
  ⟨b.source - unitStep 4 𝒮.side 𝒮.ξ ν, b.dir⟩
def fwdDiff (ν : Fin 4) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => 𝒮.ξ⁻¹ * (A (shiftUp ν b) - A b)
def bwdDiff (ν : Fin 4) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => 𝒮.ξ⁻¹ * (A (shiftDown ν b) - A b)
def bondLap (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => ∑ ν, bwdDiff ν (fwdDiff ν A) b
def constIdx (ν : Fin 4) : Fin 1 → Fin 4 := fun _ => ν
def nablaOne (A : 𝒮.FineBond → ℝ) : 𝒮.Tensor 1 := fun ν => fwdDiff (ν 0) A
def nablaTwo (J : 𝒮.Tensor 1) : 𝒮.Tensor 2 :=
  fun ν => fwdDiff (ν 0) (J (constIdx (ν 1)))
def projBonds (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ := indicator 𝒮.bonds A
def projSites (f : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ := restrictTo (𝒮.Ω 0) f
def divOne (J : 𝒮.Tensor 1) : 𝒮.FineBond → ℝ :=
  projBonds fun b => ∑ ν, bwdDiff ν (J (constIdx ν)) b
def divTwo (J : 𝒮.Tensor 2) : 𝒮.FineBond → ℝ :=
  adjointValue (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) bondInner tensorInner
    (fun A => nablaTwo (nablaOne A)) J
def comp (A : 𝒮.FineBond → ℝ) (ν : Fin 4) (x : 𝒮.FineSite) : ℝ := A ⟨x, ν⟩
def dTorus (f : 𝒮.FineSite → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => forwardDiff b.dir f b.source
def curlTorus (A : 𝒮.FineBond → ℝ) : 𝒮.FinePlaquette → ℝ :=
  fun p => forwardDiff p.2.1.1 (comp A p.2.1.2) p.1 - forwardDiff p.2.1.2 (comp A p.2.1.1) p.1
def dTorusAdj (A : 𝒮.FineBond → ℝ) : 𝒮.FineSite → ℝ :=
  adjointValue univ innerSum bondInner dTorus A
def curlTorusAdj (F : 𝒮.FinePlaquette → ℝ) : 𝒮.FineBond → ℝ :=
  adjointValue univ bondInner plaqInner curlTorus F
def dirichletLap (f : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  projSites (latticeLaplacian (projSites f))
def dDir (f : 𝒮.FineSite → ℝ) : 𝒮.FineBond → ℝ :=
  projBonds (dTorus (projSites f))
def dDirAdj (A : 𝒮.FineBond → ℝ) : 𝒮.FineSite → ℝ :=
  projSites (dTorusAdj (projBonds A))
def curlSqDir (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  projBonds (curlTorusAdj (curlTorus (projBonds A)))
def blockAvg (f : 𝒮.FineSite → ℝ) : 𝒮.Coarse :=
  fun y => ((𝒮.L : ℝ) ^ (𝒮.level y * 4))⁻¹ * ∑ᶠ x ∈ 𝒮.fineBlock (𝒮.level y) y, f x
variable (𝒮) in
def coarseBonds (n : ℕ) : Set (𝒮.BondAt n) :=
  {c | if n = 0 then
      ∃ b ∈ 𝒮.bonds, (b.source : 𝒮.Point) = c.source ∧ b.dir = c.dir ∧
        (b.source : 𝒮.Point) ∉ 𝒮.Ω 1 ∧ (b.target : 𝒮.Point) ∉ 𝒮.Ω 1
    else
      ((c.source : 𝒮.Point) ∈ 𝒮.Ω n ∨ (c.target : 𝒮.Point) ∈ 𝒮.Ω n) ∧
        (c.source : 𝒮.Point) ∉ 𝒮.Ω (n + 1) ∧ (c.target : 𝒮.Point) ∉ 𝒮.Ω (n + 1)}
def pathBond (μ : Fin 4) (x : 𝒮.FineSite) (i : ℕ) : 𝒮.FineBond :=
  ⟨x + i • unitStep 4 𝒮.side 𝒮.ξ μ, μ⟩
def bondAvg (n : ℕ) (A : 𝒮.FineBond → ℝ) (c : 𝒮.BondAt n) : ℝ :=
  ((𝒮.L : ℝ) ^ (n * (4 + 1)))⁻¹ *
    ∑ᶠ x ∈ 𝒮.fineBlock n c.source, ∑ i ∈ Finset.range (𝒮.L ^ n), A (pathBond c.dir x i)
def avgWeight (n : ℕ) (c : 𝒮.BondAt n) (b : 𝒮.FineBond) : ℝ :=
  ((𝒮.L : ℝ) ^ (n * (4 + 1)))⁻¹ *
    (Set.ncard {p : 𝒮.FineSite × ℕ | p.1 ∈ 𝒮.fineBlock n c.source ∧ p.2 < 𝒮.L ^ n ∧
      pathBond c.dir p.1 p.2 = b} : ℝ)
def blockAvgAdj (ω : 𝒮.Coarse) : 𝒮.FineSite → ℝ :=
  adjointValue (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) innerSum coarseInner blockAvg ω
def weightMul (ω : 𝒮.Coarse) : 𝒮.Coarse :=
  fun y => blockWeights 𝒮.L (𝒮.level y) * (𝒮.scale (𝒮.level y) ^ 2)⁻¹ * ω y
def gaugeLap (f : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  dirichletLap f + blockAvgAdj (weightMul (blockAvg f))
def gaugeGreenOp (f : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  inverseValue (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) gaugeLap f
variable (𝒮) in
def avgKernel : Set (𝒮.FineSite → ℝ) := {f | f ∈ 𝒮.siteFns ∧ blockAvg f = 0}
def rangeProj (f : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  orthProjValue (dirichletLap '' 𝒮.avgKernel) innerSum f
def complProj (f : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ := f - rangeProj f
def avgForm (A A' : 𝒮.FineBond → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (𝒮.s + 1), ∑ᶠ c ∈ 𝒮.coarseBonds n,
    gaugeParam * 𝒮.scale n ^ (4 - 2) * (bondAvg n A c * bondAvg n A' c)
theorem avgForm_self (A : 𝒮.FineBond → ℝ) :
    avgForm A A = ∑ n ∈ Finset.range (𝒮.s + 1), ∑ᶠ c ∈ 𝒮.coarseBonds n,
      gaugeParam * 𝒮.scale n ^ (4 - 2) * |bondAvg n A c| ^ 2 := by
  simp only [avgForm, sq_abs]
  simp only [pow_two]
def avgOp (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  Classical.epsilon fun B => B ∈ 𝒮.oneForms ∧
    ∀ A' ∈ 𝒮.oneForms, bondInner B A' = avgForm A A'
def baseOp (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  curlSqDir A + dDir (rangeProj (dDirAdj A)) + avgOp A
def longOp (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  dDir (complProj (dDirAdj A))
variable (𝒮) in
def BaseOpInvertible : Prop :=
  BijOn baseOp (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) 𝒮.oneForms
def baseGreen (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  inverseValue (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) baseOp A
end NestedRegions
end YangMills.Construction.RegionSequence
