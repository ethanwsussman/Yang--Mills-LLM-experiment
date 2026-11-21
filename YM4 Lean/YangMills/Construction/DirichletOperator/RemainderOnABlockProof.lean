import YangMills.Construction.DirichletOperator.PointwiseBoundsOfTheDirichletGreenOperatorProof
import YangMills.Construction.DirichletOperator.RemainderOnABlock
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet YangMills.Construction.WeightedGreen
open YangMills.Construction.Dirichlet.WalkExpansion
noncomputable section
namespace YangMills.Construction.Dirichlet.LocalRemainderBound
section Lengths
variable {d : ℕ} {S : ℝ}
theorem exists_torusProj_eq (p : PeriodicTorus d S) : ∃ v : Fin d → ℝ, torusProj d S v = p := by apply _root_.YangMills.Construction.Dirichlet.Commutator.exists_torusProj_eq <;> assumption
theorem supNorm_zero_le : supNorm (0 : PeriodicTorus d S) ≤ 0 := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_zero_le <;> assumption
theorem supNorm_sub_le (p q r : PeriodicTorus d S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_le_add <;> assumption
theorem lOneNorm_sub_le (p q r : PeriodicTorus d S) :
    lOneNorm (p - q) ≤ lOneNorm (p - r) + lOneNorm (q - r) := by apply _root_.YangMills.Construction.Dirichlet.Commutator.lOneNorm_sub_le_add <;> assumption
theorem supNorm_sub_le_of_isNeighbor {ξ : ℝ} (hξ : 0 < ξ) {x x' : LatticeSite d S ξ}
    (h : IsNeighbor x x') :
    supNorm ((x' : PeriodicTorus d S) - (x : PeriodicTorus d S)) ≤ ξ := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_le_of_isNeighbor <;> assumption
theorem abs_finsum_mem_le_ncard_mul {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ) (K : ℝ)
    (h : ∀ x ∈ s, |f x| ≤ K) : |∑ᶠ x ∈ s, f x| ≤ (s.ncard : ℝ) * K := by apply _root_.YangMills.Construction.Dirichlet.Commutator.abs_finsum_mem_le_ncard_mul <;> assumption
end Lengths
section Places
variable {d L : ℕ} {S aMinus aPlus : ℝ} (B : BlockSetting d L aMinus aPlus S)
structure ChainFacts : Prop where
  chain : ChainMemberFacts L B.ξ B.M B.t B.Ω
  shells : ∀ n ≤ lastNonemptyIndex B.Ω, ShellCubeFacts L B.ξ B.M B.t B.Ω n
  location : SiteLocationFacts L B.ξ B.t B.Ω
  cube_sites : ∀ n ≤ lastNonemptyIndex B.Ω, ∀ y ∈ shellSites L B.ξ B.Ω n, ∀ z : Fin d → ℝ,
    torusProj d S z = y → CubeSiteFacts L B.ξ B.Ω y z
  isNeighbor_ncard : ∀ x : LatticeSite d S B.ξ, {x' | IsNeighbor x x'}.ncard = 2 * d
theorem centreSpacing_pos (hL : 1 ≤ L) (y : PeriodicTorus d S) : 0 < B.centreSpacing y :=
  mul_pos (zpow_pos (by exact_mod_cast hL) _) B.isSeparatedChain.scale_pos
theorem le_centreSpacing (hL : 1 ≤ L) (y : PeriodicTorus d S) : B.ξ ≤ B.centreSpacing y := by apply _root_.YangMills.Construction.Dirichlet.Commutator.ξ_le_centreSpacing <;> assumption
theorem cell_subset_base (F : ChainFacts B) {y : PeriodicTorus d S} (hy : y ∈ B.centres) :
    B.cell y ⊆ B.Ω 0 := by
  obtain ⟨n, -, hn⟩ := hy
  have hnt : n ≤ lastNonemptyIndex B.Ω := hn.1
  intro p hp
  have hp' : p ∈ shell B.Ω n := by
    rw [(F.shells n hnt).shell_eq_iUnion]
    exact mem_iUnion₂.mpr ⟨y, hn, hp⟩
  rw [F.chain.zero_eq_iUnion]
  exact mem_iUnion₂.mpr ⟨n, hnt, hp'⟩
theorem centreOf_spec (F : ChainFacts B) (x : LatticeSite d S B.ξ)
    (hx : (x : PeriodicTorus d S) ∈ B.Ω 0) :
    B.centreOf x ∈ B.centres ∧ (x : PeriodicTorus d S) ∈ B.cell (B.centreOf x) := by
  obtain ⟨y, hy, hint, -⟩ := F.location.exists_of_mem x x.2 hx
  exact Classical.epsilon_spec
    (p := fun y => y ∈ B.centres ∧ (x : PeriodicTorus d S) ∈ B.cell y)
    ⟨y, hy, interior_subset hint⟩
theorem centreOf_eq (F : ChainFacts B) (x : LatticeSite d S B.ξ)
    (hx : (x : PeriodicTorus d S) ∈ B.Ω 0) {y : PeriodicTorus d S} (hy : y ∈ B.centres)
    (hxy : (x : PeriodicTorus d S) ∈ B.cell y) : B.centreOf x = y := by
  obtain ⟨y₀, -, -, huniq, -⟩ := F.location.exists_of_mem x x.2 hx
  have h₁ : B.centreOf x = y₀ :=
    by_contra fun hne => huniq _ (centreOf_spec B F x hx).1 hne (centreOf_spec B F x hx).2
  have h₂ : y = y₀ := by_contra fun hne => huniq y hy hne hxy
  rw [h₁, h₂]
theorem centreIndex_le {y : PeriodicTorus d S} (hy : y ∈ B.centres) : B.centreIndex y ≤ B.t := by apply _root_.YangMills.Construction.Dirichlet.Commutator.centreIndex_le_t <;> assumption
theorem commutatorOp_of_mem (h ψ : LatticeSite d S B.ξ → ℝ) (x : LatticeSite d S B.ξ)
    (hx : (x : PeriodicTorus d S) ∈ B.Ω 0) :
    B.commutatorOp h ψ x =
      (∑ᶠ x' ∈ {x' : LatticeSite d S B.ξ | IsNeighbor x x'},
          (B.ξ ^ 2)⁻¹ * (h x' - h x) * (ψ x' - ψ x)) -
        latticeLaplacian h x * ψ x -
        B.a (B.centreIndex (B.centreOf x)) * (B.centreSpacing (B.centreOf x) ^ 2)⁻¹ *
          (B.ξ / B.centreSpacing (B.centreOf x)) ^ d *
          ∑ᶠ x' ∈ {x' : LatticeSite d S B.ξ | (x' : PeriodicTorus d S) ∈ B.cell (B.centreOf x)},
            (h x' - h x) * ψ x' := by apply _root_.YangMills.Construction.Dirichlet.Commutator.commutatorOp_of_mem <;> assumption
theorem cell_card (F : ChainFacts B) {y : PeriodicTorus d S} (hy : y ∈ B.centres) :
    ∃ N₀ : ℕ, (N₀ : ℝ) = B.centreSpacing y / B.ξ ∧
      {x' : LatticeSite d S B.ξ | (x' : PeriodicTorus d S) ∈ B.cell y}.Finite ∧
      {x' : LatticeSite d S B.ξ | (x' : PeriodicTorus d S) ∈ B.cell y}.ncard = N₀ ^ d := by
  obtain ⟨n, -, hn⟩ := id hy
  have hnt : n ≤ lastNonemptyIndex B.Ω := hn.1
  obtain ⟨z, hz⟩ := exists_torusProj_eq y
  obtain ⟨N₀, hN₀, e, -⟩ := (F.cube_sites n hnt y hn z hz).equiv_boxGrid
  have hT : Finite {x' : LatticeSite d S B.ξ | (x' : PeriodicTorus d S) ∈ B.cell y} :=
    Finite.of_equiv _ e
  refine ⟨N₀, hN₀, Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr e.symm).trans (by simp [Nat.card_eq_fintype_card])
theorem siteLOneDist_le_of_mem_cell (F : ChainFacts B) {y : PeriodicTorus d S} (hy : y ∈ B.centres)
    {x x' : LatticeSite d S B.ξ} (hx : (x : PeriodicTorus d S) ∈ B.cell y)
    (hx' : (x' : PeriodicTorus d S) ∈ B.cell y) :
    siteLOneDist x x' ≤ (d : ℝ) * B.centreSpacing y := by
  obtain ⟨n, -, hn⟩ := id hy
  have hnt : n ≤ lastNonemptyIndex B.Ω := hn.1
  obtain ⟨z, hz⟩ := exists_torusProj_eq y
  have CS := F.cube_sites n hnt y hn z hz
  have n₁ : lOneNorm ((x : PeriodicTorus d S) - y) ≤ 1 / 2 * (d : ℝ) * B.centreSpacing y :=
    CS.lOneNorm_sub_centre_le x hx
  have n₂ : lOneNorm ((x' : PeriodicTorus d S) - y) ≤ 1 / 2 * (d : ℝ) * B.centreSpacing y :=
    CS.lOneNorm_sub_centre_le x' hx'
  have n₃ := lOneNorm_sub_le (x : PeriodicTorus d S) (x' : PeriodicTorus d S) y
  unfold siteLOneDist
  linarith
theorem abs_commutatorOp_le (F : ChainFacts B) (hd : 0 < d) (hL : 1 ≤ L) (ha : 0 < aMinus)
    {y : PeriodicTorus d S} (hy : y ∈ B.centres) {c₁ c₂ N : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hN : 0 ≤ N) (h ψ : LatticeSite d S B.ξ → ℝ) (x : LatticeSite d S B.ξ)
    (hxy : (x : PeriodicTorus d S) ∈ B.cell y)
    (step_h : ∀ x' : LatticeSite d S B.ξ, IsNeighbor x x' →
      |h x' - h x| ≤ c₁ * B.ξ / ((B.M : ℝ) * B.centreSpacing y))
    (step_ψ : ∀ x' : LatticeSite d S B.ξ, IsNeighbor x x' →
      |ψ x' - ψ x| ≤ B.ξ * B.centreSpacing y * N)
    (lap_h : |latticeLaplacian h x| ≤ c₂ / ((B.M : ℝ) * B.centreSpacing y) ^ 2)
    (size_ψ : ∀ x' : LatticeSite d S B.ξ, (x' : PeriodicTorus d S) ∈ B.cell y →
      |ψ x'| ≤ B.centreSpacing y ^ 2 * N)
    (cell_h : ∀ x' : LatticeSite d S B.ξ, (x' : PeriodicTorus d S) ∈ B.cell y →
      |h x' - h x| ≤ c₁ * siteLOneDist x x' / ((B.M : ℝ) * B.centreSpacing y)) :
    |B.commutatorOp h ψ x| ≤
      (2 * (d : ℝ) * c₁ + c₂ + aPlus * (d : ℝ) * c₁) * (B.M : ℝ)⁻¹ * N := by
  have hξ : 0 < B.ξ := B.isSeparatedChain.scale_pos
  have hs : 0 < B.centreSpacing y := centreSpacing_pos B hL y
  have hm1 : (1 : ℝ) ≤ (B.M : ℝ) := by
    have := B.isSeparatedChain.blockSize_isPowerGe.1
    exact_mod_cast hL.trans this
  have ht := centreIndex_le B hy
  have han : 0 < B.a (B.centreIndex y) := ha.trans_le (B.weight_mem _ ht).1
  have hale : B.a (B.centreIndex y) ≤ aPlus := (B.weight_mem _ ht).2
  have hap : 0 < aPlus := han.trans_le hale
  have hW₂ : 0 ≤ c₂ * N / (B.M : ℝ) := by positivity
  have hRHS : (2 * (d : ℝ) * c₁ + c₂ + aPlus * (d : ℝ) * c₁) * (B.M : ℝ)⁻¹ * N =
      2 * (d : ℝ) * (c₁ * N / (B.M : ℝ)) + c₂ * N / (B.M : ℝ) +
        aPlus * (d : ℝ) * (c₁ * N / (B.M : ℝ)) := by
    field_simp
  have hx0 := cell_subset_base B F hy hxy
  have hcen := centreOf_eq B F x hx0 hy hxy
  rw [commutatorOp_of_mem B h ψ x hx0, hcen, hRHS]
  have hfin : {x' : LatticeSite d S B.ξ | IsNeighbor x x'}.Finite :=
    Set.finite_of_ncard_ne_zero (by rw [F.isNeighbor_ncard x]; omega)
  have hB₁ : |∑ᶠ x' ∈ {x' : LatticeSite d S B.ξ | IsNeighbor x x'},
      (B.ξ ^ 2)⁻¹ * (h x' - h x) * (ψ x' - ψ x)| ≤ 2 * (d : ℝ) * (c₁ * N / (B.M : ℝ)) := by
    have key := abs_finsum_mem_le_ncard_mul hfin
      (fun x' => (B.ξ ^ 2)⁻¹ * (h x' - h x) * (ψ x' - ψ x)) (c₁ * N / (B.M : ℝ)) (by
        intro x' hx'
        have e₁ := step_h x' hx'
        have e₂ := step_ψ x' hx'
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < (B.ξ ^ 2)⁻¹)]
        calc (B.ξ ^ 2)⁻¹ * |h x' - h x| * |ψ x' - ψ x|
            ≤ (B.ξ ^ 2)⁻¹ * (c₁ * B.ξ / ((B.M : ℝ) * B.centreSpacing y)) *
                (B.ξ * B.centreSpacing y * N) :=
              mul_le_mul (mul_le_mul_of_nonneg_left e₁ (by positivity)) e₂ (abs_nonneg _)
                (by positivity)
          _ = c₁ * N / (B.M : ℝ) := by field_simp)
    rw [F.isNeighbor_ncard x] at key
    push_cast at key
    exact key
  have hB₂ : |latticeLaplacian h x * ψ x| ≤ c₂ * N / (B.M : ℝ) := by
    rw [abs_mul]
    calc |latticeLaplacian h x| * |ψ x|
        ≤ c₂ / ((B.M : ℝ) * B.centreSpacing y) ^ 2 * (B.centreSpacing y ^ 2 * N) :=
          mul_le_mul lap_h (size_ψ x hxy) (abs_nonneg _) (by positivity)
      _ = c₂ * N / (B.M : ℝ) * (B.M : ℝ)⁻¹ := by field_simp
      _ ≤ c₂ * N / (B.M : ℝ) := mul_le_of_le_one_right hW₂ (inv_le_one_of_one_le₀ hm1)
  obtain ⟨N₀, hN₀', hfinb, hcard⟩ := cell_card B F hy
  have hsum := abs_finsum_mem_le_ncard_mul hfinb (fun x' => (h x' - h x) * ψ x')
    (c₁ * ((d : ℝ) * B.centreSpacing y) / ((B.M : ℝ) * B.centreSpacing y) *
      (B.centreSpacing y ^ 2 * N)) (by
      intro x' hx'
      have hx'' : (x' : PeriodicTorus d S) ∈ B.cell y := hx'
      have hdist := siteLOneDist_le_of_mem_cell B F hy hxy hx''
      have e₁ : |h x' - h x| ≤
          c₁ * ((d : ℝ) * B.centreSpacing y) / ((B.M : ℝ) * B.centreSpacing y) :=
        (cell_h x' hx'').trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hc₁) (by positivity))
      rw [abs_mul]
      exact mul_le_mul e₁ (size_ψ x' hx'') (abs_nonneg _) (by positivity))
  rw [hcard] at hsum
  push_cast at hsum
  have hP : 0 ≤ (B.ξ / B.centreSpacing y) ^ d := by positivity
  have hone : (B.ξ / B.centreSpacing y) ^ d * (N₀ : ℝ) ^ d = 1 := by
    rw [← mul_pow, hN₀']
    have : B.ξ / B.centreSpacing y * (B.centreSpacing y / B.ξ) = 1 := by field_simp
    rw [this, one_pow]
  have hB₃ : |B.a (B.centreIndex y) * (B.centreSpacing y ^ 2)⁻¹ * (B.ξ / B.centreSpacing y) ^ d *
      ∑ᶠ x' ∈ {x' : LatticeSite d S B.ξ | (x' : PeriodicTorus d S) ∈ B.cell y},
        (h x' - h x) * ψ x'| ≤
      aPlus * (d : ℝ) * (c₁ * N / (B.M : ℝ)) := by
    have hcoef : 0 ≤ B.a (B.centreIndex y) * (B.centreSpacing y ^ 2)⁻¹ *
        (B.ξ / B.centreSpacing y) ^ d :=
      mul_nonneg (mul_nonneg han.le (by positivity)) hP
    rw [abs_mul, abs_of_nonneg hcoef]
    calc B.a (B.centreIndex y) * (B.centreSpacing y ^ 2)⁻¹ * (B.ξ / B.centreSpacing y) ^ d *
          |∑ᶠ x' ∈ {x' : LatticeSite d S B.ξ | (x' : PeriodicTorus d S) ∈ B.cell y},
            (h x' - h x) * ψ x'|
        ≤ aPlus * (B.centreSpacing y ^ 2)⁻¹ * (B.ξ / B.centreSpacing y) ^ d *
            ((N₀ : ℝ) ^ d * (c₁ * ((d : ℝ) * B.centreSpacing y) /
              ((B.M : ℝ) * B.centreSpacing y) * (B.centreSpacing y ^ 2 * N))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hale (by positivity)) hP) hsum (abs_nonneg _)
            (mul_nonneg (mul_nonneg hap.le (by positivity)) hP)
      _ = aPlus * (B.centreSpacing y ^ 2)⁻¹ * ((B.ξ / B.centreSpacing y) ^ d * (N₀ : ℝ) ^ d) *
            (c₁ * ((d : ℝ) * B.centreSpacing y) / ((B.M : ℝ) * B.centreSpacing y) *
              (B.centreSpacing y ^ 2 * N)) := by ring
      _ = aPlus * (d : ℝ) * (c₁ * N / (B.M : ℝ)) := by
          rw [hone]
          field_simp
  obtain ⟨a₁, a₂⟩ := abs_le.mp hB₁
  obtain ⟨b₁, b₂⟩ := abs_le.mp hB₂
  obtain ⟨c₃, c₄⟩ := abs_le.mp hB₃
  rw [abs_le]
  constructor <;> linarith
theorem abs_le_supNormAll (F : ChainFacts B) {y : PeriodicTorus d S} (hy : y ∈ B.centres)
    {f : LatticeSite d S B.ξ → ℝ} (hf : VanishesOff (B.cell y) f) (x : LatticeSite d S B.ξ) :
    |f x| ≤ supNormAll f := by
  obtain ⟨-, -, hfin, -⟩ := cell_card B F hy
  have hbdd : BddAbove {r | ∃ x : LatticeSite d S B.ξ,
      (x : PeriodicTorus d S) ∈ (univ : Set (PeriodicTorus d S)) ∧ r = |f x|} := by
    refine ((hfin.image fun x => |f x|).insert 0).bddAbove.mono ?_
    rintro r ⟨x', -, rfl⟩
    by_cases hx' : (x' : PeriodicTorus d S) ∈ B.cell y
    · exact Or.inr ⟨x', hx', rfl⟩
    · left
      rw [hf x' hx', abs_zero]
  exact le_csSup hbdd ⟨x, mem_univ _, rfl⟩
theorem supNormAll_nonneg {ξ : ℝ} (f : LatticeSite d S ξ → ℝ) : 0 ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.zero_le_supNormAll <;> assumption
theorem fieldSupNorm_zero {ξ : ℝ} : fieldSupNorm (0 : BondField d S ξ) = 0 := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.fieldSupNorm_zero_eq <;> assumption
theorem latticeDiv_zero {ξ : ℝ} : latticeDiv (0 : BondField d S ξ) = 0 := by apply _root_.YangMills.Construction.Dirichlet.GreenPointwise.latticeDiv_zero <;> assumption
theorem commutatorOp_zero (h : LatticeSite d S B.ξ → ℝ) : B.commutatorOp h 0 = 0 := by
  funext x
  simp [BlockSetting.commutatorOp, restrictTo]
theorem restrictTo_of_mem {ξ : ℝ} {X : Set (PeriodicTorus d S)} (f : LatticeSite d S ξ → ℝ)
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∈ X) : restrictTo X f x = f x :=
  Set.indicator_of_mem (show x ∈ {x : LatticeSite d S ξ | (x : PeriodicTorus d S) ∈ X} from hx) _
theorem restrictTo_eq_zero {ξ : ℝ} {X : Set (PeriodicTorus d S)} {f : LatticeSite d S ξ → ℝ}
    {x : LatticeSite d S ξ} (h : f x = 0) : restrictTo X f x = 0 := by
  unfold restrictTo
  exact Set.indicator_apply_eq_zero.mpr fun _ => h
theorem supSetDist_singleton_le_of_mem {p : PeriodicTorus d S} {X : Set (PeriodicTorus d S)}
    (hp : p ∈ X) {r : ℝ} (hr : 0 ≤ r) : supSetDist {p} X ≤ ENNReal.ofReal r := by
  unfold supSetDist
  refine iInf₂_le_of_le p (mem_singleton p) (iInf₂_le_of_le p hp ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [sub_self]
  exact supNorm_zero_le.trans hr
theorem abs_le_mul_of_abs_inv_mul_le {ξ u K : ℝ} (hξ : 0 < ξ) (h : |ξ⁻¹ * u| ≤ K) :
    |u| ≤ ξ * K := by
  rw [abs_mul, abs_of_pos (inv_pos.mpr hξ)] at h
  calc |u| = ξ * (ξ⁻¹ * |u|) := by field_simp
    _ ≤ ξ * K := mul_le_mul_of_nonneg_left h hξ.le
end Places
theorem claim_holds (hTor : Torus.PartitionsHold)
    (hPou : PartitionOfUnity.PartitionClaim) (hReg : RegionBounds.RegionBoundsStatement)
    (hThr : ThresholdConsequences.Claim) (hComm : Commutator.CommutatorClaim)
    (hLin : GreenLinearity.BlockGreenLinear) : Claim := by
  intro d L aMinus aPlus hLet S B above E hE Q hQ y hy y' hy' f hf
  obtain ⟨-, -, hseq⟩ := hTor d L aMinus aPlus hLet B.ξ S B.isSeparatedChain.scale_pos
    B.isSeparatedChain.period_pos
  obtain ⟨-, hmem, hshell, hloc, hcs, hadj⟩ := hseq B.M B.R₁ B.t B.Ω B.isSeparatedChain
  have F : ChainFacts B := ⟨hmem, hshell, hloc, hcs, hadj⟩
  have C := hThr d L aMinus aPlus hLet S B above
  obtain ⟨hCl, hFn, hDB, hLS⟩ := hPou d L aMinus aPlus hLet S B C.blockSize_floor C.gap_floor
  obtain ⟨-, -, hKs⟩ := hComm d L aMinus aPlus hLet S B
  have hsup := hKs C.blockSize_floor C.gap_floor Q hQ
  have hL : 1 ≤ L := by
    have := hLet.three_le_blockFactor
    omega
  have hd : 0 < d := by
    have := hLet.three_le_dim
    omega
  have hξ : 0 < B.ξ := B.isSeparatedChain.scale_pos
  obtain ⟨n, -, hQn⟩ := id hQ
  have hreg : B.IsCellUnion (B.innerRegion Q) := hCl.region n Q hQn
  have G := hLin d L aMinus aPlus hLet S B (B.innerRegion Q) (E Q) hreg (hE Q hQ)
  have hW0 : B.innerRegion Q ⊆ B.Ω 0 := by
    intro p hp
    obtain ⟨y₁, hy₁, hp₁⟩ := mem_iUnion₂.mp hp
    exact cell_subset_base B F hy₁.1 hp₁
  have hψΩ : VanishesOff (B.Ω 0)
      (B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f)) := fun x hx =>
    G.vanishesOff _ x fun hxW => hx (hW0 hxW)
  have hnz : ∀ x : LatticeSite d S B.ξ, pointwiseMul (B.latticeCutoff Q) f x ≠ 0 →
      (x : PeriodicTorus d S) ∈ B.cell y' ∧ Commutator.CutoffSiteFacts B Q x := by
    intro x hne
    have hne₁ : B.latticeCutoff Q x ≠ 0 := fun h => hne (by simp [pointwiseMul, h])
    have hne₂ : f x ≠ 0 := fun h => hne (by simp [pointwiseMul, h])
    have hxc : (x : PeriodicTorus d S) ∈ B.cell y' := by
      by_contra hc
      exact hne₂ (hf x hc)
    exact ⟨hxc, hsup.site_facts x (cell_subset_base B F hy' hxc) hne₁⟩
  have hzero₂ : y' ∉ B.centresNearBump Q → B.cubeRemainder E Q f = 0 := by
    intro hno
    have hg : pointwiseMul (B.latticeCutoff Q) f = 0 := by
      funext x
      by_contra hne
      obtain ⟨hxc, hs⟩ := hnz x hne
      have hc := centreOf_eq B F x (cell_subset_base B F hy' hxc) hy' hxc
      exact hno (hc ▸ hs.centre_mem)
    have hψ0 : B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f) = 0 := by
      have e := G.map_smul 0 0
      rw [zero_smul, zero_smul] at e
      rw [hg]
      exact e
    funext x
    show restrictTo (B.Ω 0)
      (B.commutatorOp (B.latticeCutoff Q) (B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f)))
        x = 0
    rw [hψ0, commutatorOp_zero]
    exact restrictTo_eq_zero rfl
  have hzero₃ : y ∉ B.centresNearBump Q → ∀ x : LatticeSite d S B.ξ,
      (x : PeriodicTorus d S) ∈ B.cell y → B.cubeRemainder E Q f x = 0 := by
    intro hno x hx
    have hx0 := cell_subset_base B F hy hx
    have hnot : (x : PeriodicTorus d S) ∉ Commutator.nearCells B Q := by
      intro hb
      obtain ⟨y₂, hy₂, hxy₂⟩ := mem_iUnion₂.mp hb
      have e₁ := centreOf_eq B F x hx0 hy hx
      have e₂ := centreOf_eq B F x hx0 hy₂.1 hxy₂
      have e₃ : y = y₂ := e₁.symm.trans e₂
      rw [← e₃] at hy₂
      exact hno hy₂
    exact restrictTo_eq_zero (hsup.eq_zero_off _ hψΩ x hnot)
  have hRHS0 : 0 ≤ remainderConstC d L aMinus aPlus * (B.M : ℝ)⁻¹ *
      WeightedDistance.expDecay B (expDecayRate d L aMinus aPlus / 2) y y' * supNormAll f :=
    mul_nonneg (mul_nonneg (mul_nonneg C.remainderConst_nonneg
      (inv_nonneg.mpr (Nat.cast_nonneg _))) (Real.exp_pos _).le) (supNormAll_nonneg f)
  refine ⟨?_, hzero₂, hzero₃⟩
  intro x hxy
  by_cases hyY : y ∈ B.centresNearBump Q
  swap
  · rw [hzero₃ hyY x hxy, abs_zero]
    exact hRHS0
  by_cases hy'Y : y' ∈ B.centresNearBump Q
  swap
  · rw [hzero₂ hy'Y]
    simpa using hRHS0
  have hx0 := cell_subset_base B F hy hxy
  have hcen := centreOf_eq B F x hx0 hy hxy
  have hdata : RegionBounds.IsRegionSourceData B (B.innerRegion Q) (E Q) y'
      (pointwiseMul (B.latticeCutoff Q) f) 0 :=
    { cellUnion := hreg
      boundaryRule := hE Q hQ
      centre_mem := hy'
      source_vanishesOff := fun x₁ hx₁ => by
        by_contra hne
        exact hx₁ (hnz x₁ hne).2.mem_innerRegion
      source_supportedNear := fun x₁ hx₁ => by
        have hn : (x₁ : PeriodicTorus d S) ∉ B.cell y' := fun hc => hx₁ (Or.inl hc)
        simp [pointwiseMul, hf x₁ hn]
      field_supportedNear := fun _ _ _ => rfl
      field_zero_at_boundary := fun _ _ _ => rfl
      field_zero_away := fun _ _ _ => rfl }
  obtain ⟨⟨hC₁, hBd⟩, -⟩ := hReg d L aMinus aPlus hLet
  have HB := hBd S B C.floors (B.innerRegion Q) (E Q) y' _ 0 hdata y
    (hLS.interior_centre n Q hQn y hyY)
  have hsol : RegionBounds.regionSolution B (B.innerRegion Q) (E Q)
      (pointwiseMul (B.latticeCutoff Q) f) 0 =
        B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f) := by
    unfold RegionBounds.regionSolution BlockSetting.cubeGreen
    rw [latticeDiv_zero]
    have e : restrictTo (B.innerRegion Q) (0 : LatticeSite d S B.ξ → ℝ) = 0 := by
      funext x₁
      exact restrictTo_eq_zero rfl
    rw [e, add_zero]
  have hsize : RegionBounds.sourceScale B y (pointwiseMul (B.latticeCutoff Q) f) 0 =
      B.centreSpacing y ^ 2 * supNormAll (pointwiseMul (B.latticeCutoff Q) f) := by
    unfold RegionBounds.sourceScale
    rw [fieldSupNorm_zero, mul_zero, add_zero]
  have hA : supNormAll (pointwiseMul (B.latticeCutoff Q) f) ≤ supNormAll f := by
    refine Real.sSup_le ?_ (supNormAll_nonneg f)
    rintro r ⟨x₁, -, rfl⟩
    by_cases hx₁ : (x₁ : PeriodicTorus d S) ∈ B.cell y'
    · have hx₀ := cell_subset_base B F hy' hx₁
      obtain ⟨V, -, hUV, -, hV⟩ := hFn.smooth_near
      have hU₁ : (x₁ : PeriodicTorus d S) ∈ B.baseNbhd :=
        supSetDist_singleton_le_of_mem hx₀ (by positivity)
      have hb : 0 ≤ B.latticeCutoff Q x₁ ∧ B.latticeCutoff Q x₁ ≤ 1 := (hV Q hQ).2 x₁ (hUV hU₁)
      have hh : |B.latticeCutoff Q x₁| ≤ 1 := abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
      show |B.latticeCutoff Q x₁ * f x₁| ≤ supNormAll f
      rw [abs_mul]
      calc |B.latticeCutoff Q x₁| * |f x₁| ≤ 1 * |f x₁| :=
            mul_le_mul_of_nonneg_right hh (abs_nonneg _)
        _ = |f x₁| := one_mul _
        _ ≤ supNormAll f := abs_le_supNormAll B F hy' hf x₁
    · have hz : f x₁ = 0 := hf x₁ hx₁
      simpa [pointwiseMul, hz] using supNormAll_nonneg f
  have hap : 0 < aPlus := hLet.lower_pos.trans_le hLet.lower_le_upper
  have hc := C.partitionConst_nonneg
  set ψ := B.cubeGreen E Q (pointwiseMul (B.latticeCutoff Q) f) with hψdef
  set A := supNormAll (pointwiseMul (B.latticeCutoff Q) f) with hAdef
  set e := RegionBounds.decayFactor B y y' with hedef
  set C₁ := RegionBounds.decayConstant d L aMinus aPlus with hC₁def
  set c := PartitionOfUnity.partitionConst d with hcdef
  have he : 0 < e := Real.exp_pos _
  have hN : 0 ≤ C₁ * A * e := mul_nonneg (mul_nonneg hC₁.le (supNormAll_nonneg _)) he.le
  have hs := centreSpacing_pos B hL y
  have hle := le_centreSpacing B hL y
  have hxh : supNorm ((x : PeriodicTorus d S) - y) ≤ B.centreSpacing y / 2 := hxy
  have hval : ∀ x₁ : LatticeSite d S B.ξ, RegionBounds.IsCloseTo B y x₁ →
      |ψ x₁| ≤ B.centreSpacing y ^ 2 * (C₁ * A * e) := by
    intro x₁ hn
    have hb := (HB x₁ hn ⟨0, hd⟩).1
    rw [hsol, hsize] at hb
    calc |ψ x₁| ≤ C₁ * (B.centreSpacing y ^ 2 * A) * e := hb
      _ = B.centreSpacing y ^ 2 * (C₁ * A * e) := by ring
  have hdiff : ∀ x₁ : LatticeSite d S B.ξ, RegionBounds.IsCloseTo B y x₁ → ∀ ν : Fin d,
      |forwardDiff ν ψ x₁| ≤ B.centreSpacing y * (C₁ * A * e) := by
    intro x₁ hn ν
    have hb := (HB x₁ hn ν).2 rfl
    rw [hsol] at hb
    calc |forwardDiff ν ψ x₁| ≤ C₁ * (B.centreSpacing y * A) * e := hb
      _ = B.centreSpacing y * (C₁ * A * e) := by ring
  have near_cell : ∀ x₁ : LatticeSite d S B.ξ, (x₁ : PeriodicTorus d S) ∈ B.cell y →
      RegionBounds.IsCloseTo B y x₁ := by
    intro x₁ hx₁
    have h₁ : supNorm ((x₁ : PeriodicTorus d S) - y) ≤ B.centreSpacing y / 2 := hx₁
    show supNorm ((x₁ : PeriodicTorus d S) - y) ≤ 2 * B.centreSpacing y
    linarith
  have near_adj : ∀ x' : LatticeSite d S B.ξ, IsNeighbor x x' →
      RegionBounds.IsCloseTo B y x' := by
    intro x' hadj'
    have d₁ := supNorm_sub_le_of_isNeighbor hξ hadj'
    have d₂ := supNorm_sub_le (x' : PeriodicTorus d S) (x : PeriodicTorus d S) y
    show supNorm ((x' : PeriodicTorus d S) - y) ≤ 2 * B.centreSpacing y
    linarith
  have step_ψ : ∀ x' : LatticeSite d S B.ξ, IsNeighbor x x' →
      |ψ x' - ψ x| ≤ B.ξ * B.centreSpacing y * (C₁ * A * e) := by
    intro x' hadj'
    obtain ⟨μ, e₁ | e₁⟩ := id hadj'
    · have hb := hdiff x (near_cell x hxy) μ
      have e₂ : forwardDiff μ ψ x = B.ξ⁻¹ * (ψ x' - ψ x) := by
        show B.ξ⁻¹ * (ψ (x + unitStep d S B.ξ μ) - ψ x) = _
        rw [e₁]
      rw [e₂] at hb
      rw [mul_assoc]
      exact abs_le_mul_of_abs_inv_mul_le hξ hb
    · have hb := hdiff x' (near_adj x' hadj') μ
      have e₃ : x' + unitStep d S B.ξ μ = x := by
        rw [e₁]
        exact sub_add_cancel _ _
      have e₂ : forwardDiff μ ψ x' = B.ξ⁻¹ * (ψ x - ψ x') := by
        show B.ξ⁻¹ * (ψ (x' + unitStep d S B.ξ μ) - ψ x') = _
        rw [e₃]
      rw [e₂] at hb
      rw [mul_assoc, abs_sub_comm]
      exact abs_le_mul_of_abs_inv_mul_le hξ hb
  have hrho : B.localScale x = B.centreSpacing y := by
    unfold BlockSetting.localScale
    rw [if_pos hx0, hcen]
  have hU : (x : PeriodicTorus d S) ∈ B.baseNbhd :=
    supSetDist_singleton_le_of_mem hx0 (by positivity)
  have hk := abs_commutatorOp_le B F hd hL hLet.lower_pos hy (c₁ := c * (L : ℝ) ^ 2)
    (c₂ := c * (L : ℝ) ^ 4) (N := C₁ * A * e) (by positivity) (by positivity) hN
    (B.latticeCutoff Q) ψ x hxy
    (fun x' hadj' => by
      have hb := hDB.diff_at_bond Q hQ x x' hU
        (supSetDist_singleton_le_of_mem hx0 (by positivity)) hadj'
      rwa [hrho] at hb)
    step_ψ
    (by
      have hb := hDB.laplacian_at_site Q hQ x hU
        (supSetDist_singleton_le_of_mem hx0 (by positivity))
      rw [hrho] at hb
      calc |latticeLaplacian (B.latticeCutoff Q) x| ≤
          c * (L : ℝ) ^ 4 / ((B.M : ℝ) * B.centreSpacing y) ^ 2 := hb)
    (fun x' hx' => hval x' (near_cell x' hx'))
    (fun x' hx' => by
      have h₁ : supNorm ((x' : PeriodicTorus d S) - y) ≤ B.centreSpacing y / 2 := hx'
      have hb := hDB.diff_near_centre Q hQ y hy x x' (by linarith) (by linarith)
      rwa [abs_sub_comm] at hb)
  have hrem : B.cubeRemainder E Q f x = B.commutatorOp (B.latticeCutoff Q) ψ x :=
    restrictTo_of_mem _ hx0
  have hnum : remainderConstC d L aMinus aPlus =
      (2 * (d : ℝ) * (c * (L : ℝ) ^ 2) + c * (L : ℝ) ^ 4 +
        aPlus * (d : ℝ) * (c * (L : ℝ) ^ 2)) * C₁ := by
    show (2 * (d : ℝ) * c * (L : ℝ) ^ 2 + c * (L : ℝ) ^ 4 + aPlus * (d : ℝ) * c * (L : ℝ) ^ 2) *
      C₁ = _
    ring
  have hdecay : WeightedDistance.expDecay B (expDecayRate d L aMinus aPlus / 2) y y' = e := by
    show Real.exp (-(expDecayRate d L aMinus aPlus / 2) * B.blockDist y y') =
      Real.exp (-(1 / 2 * expDecayRate d L aMinus aPlus) * B.blockDist y y')
    congr 1
    ring
  rw [hrem, hnum, hdecay]
  refine hk.trans ?_
  have hcoef : 0 ≤ (2 * (d : ℝ) * (c * (L : ℝ) ^ 2) + c * (L : ℝ) ^ 4 +
      aPlus * (d : ℝ) * (c * (L : ℝ) ^ 2)) * (B.M : ℝ)⁻¹ := by positivity
  calc (2 * (d : ℝ) * (c * (L : ℝ) ^ 2) + c * (L : ℝ) ^ 4 +
        aPlus * (d : ℝ) * (c * (L : ℝ) ^ 2)) * (B.M : ℝ)⁻¹ * (C₁ * A * e)
      ≤ (2 * (d : ℝ) * (c * (L : ℝ) ^ 2) + c * (L : ℝ) ^ 4 +
        aPlus * (d : ℝ) * (c * (L : ℝ) ^ 2)) * (B.M : ℝ)⁻¹ * (C₁ * supNormAll f * e) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA hC₁.le) he.le) hcoef
    _ = (2 * (d : ℝ) * (c * (L : ℝ) ^ 2) + c * (L : ℝ) ^ 4 +
        aPlus * (d : ℝ) * (c * (L : ℝ) ^ 2)) * C₁ * (B.M : ℝ)⁻¹ * e * supNormAll f := by ring
end YangMills.Construction.Dirichlet.LocalRemainderBound
