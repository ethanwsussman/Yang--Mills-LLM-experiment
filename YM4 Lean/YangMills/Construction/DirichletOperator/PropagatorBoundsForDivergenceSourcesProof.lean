import YangMills.Construction.RegionSequence.BlockAverageLift
import YangMills.Construction.RegionSequence.FineLatticeNorms
import YangMills.Construction.ColdChainAtEveryLevel.WeightedEstimateOnTheSliceProof
import YangMills.Construction.DirichletOperator.LowerBoundOfTheBasicOperatorProof
import YangMills.Construction.DirichletOperator.WhereThePartitionFunctionOfACubeLivesProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes Propagator
  PropagatorThresholds RemainderEstimates Weighted
namespace DivSourceEstimate
section SeminormFunctions
variable {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
structure IsSeminormFun (f : V → ℝ) : Prop where
  add_le : ∀ x y, f (x + y) ≤ f x + f y
  smul_eq : ∀ (a : ℝ) x, f (a • x) = |a| * f x
theorem IsSeminormFun.nonneg {f : V → ℝ} (h : IsSeminormFun f) (x : V) : 0 ≤ f x := by
  have h0 : f 0 = 0 := by simpa using h.smul_eq 0 0
  have h1 := h.add_le x (-x)
  have h2 : f (-x) = f x := by simpa using h.smul_eq (-1) x
  rw [add_neg_cancel, h0, h2] at h1
  linarith
theorem IsSeminormFun.comp_linearMap {f : W → ℝ} (h : IsSeminormFun f) (A : V →ₗ[ℝ] W) :
    IsSeminormFun fun x => f (A x) :=
  ⟨fun x y => by simpa using h.add_le (A x) (A y), fun a x => by simpa using h.smul_eq a (A x)⟩
theorem IsSeminormFun.const_mul {f : V → ℝ} (h : IsSeminormFun f) {w : ℝ} (hw : 0 ≤ w) :
    IsSeminormFun fun x => w * f x :=
  ⟨fun x y => by
      have := mul_le_mul_of_nonneg_left (h.add_le x y) hw
      linarith,
    fun a x => by rw [h.smul_eq]; ring⟩
theorem IsSeminormFun.add {f g : V → ℝ} (h : IsSeminormFun f) (h' : IsSeminormFun g) :
    IsSeminormFun fun x => f x + g x :=
  ⟨fun x y => by
      have := h.add_le x y
      have := h'.add_le x y
      linarith,
    fun a x => by rw [h.smul_eq, h'.smul_eq]; ring⟩
theorem isSeminormFun_iSup {ι : Type} [Finite ι] {f : ι → V → ℝ} (h : ∀ i, IsSeminormFun (f i)) :
    IsSeminormFun fun x => ⨆ i, f i x := by
  have hb : ∀ x, BddAbove (range fun i => f i x) := fun x => (finite_range _).bddAbove
  have hn : ∀ x, 0 ≤ ⨆ i, f i x := fun x => Real.iSup_nonneg fun i => (h i).nonneg x
  refine ⟨fun x y => ?_, fun a x => ?_⟩
  · refine Real.iSup_le (fun i => ?_) (add_nonneg (hn x) (hn y))
    exact ((h i).add_le x y).trans (add_le_add (le_ciSup (hb x) i) (le_ciSup (hb y) i))
  · simp only [fun i => (h i).smul_eq a x]
    rw [Real.mul_iSup_of_nonneg (abs_nonneg a)]
theorem sqrt_sum_sq_add_le {ι : Type} (s : Finset ι) (f g : ι → ℝ) :
    √(∑ i ∈ s, (f i + g i) ^ 2) ≤ √(∑ i ∈ s, f i ^ 2) + √(∑ i ∈ s, g i ^ 2) := by apply _root_.YangMills.Construction.BlockAverages.WeightedSlice.sqrt_sum_sq_add_le <;> assumption
end SeminormFunctions
section FineLattice
variable (𝒯 : NestedRegions)
theorem finite_fineSite : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineSite <;> assumption
theorem finite_fineBond : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
theorem weightedDist_nonneg (a b : 𝒯.Point) : 0 ≤ 𝒯.weightedDist a b := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨Γ, -, -, -, rfl⟩
  have hlen : ∀ X : Set 𝒯.Point, 0 ≤ lengthWithin Γ X := by
    intro X
    refine List.sum_nonneg ?_
    intro r hr
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hr
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) ENNReal.toReal_nonneg
  have hL : (0 : ℝ) < 𝒯.L := by
    have := 𝒯.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒯.L)
  refine add_nonneg (Finset.sum_nonneg fun n _ => ?_) ?_
  · exact mul_nonneg (inv_nonneg.2 (mul_pos (zpow_pos hL _) 𝒯.ξ_pos).le) (hlen _)
  · exact mul_nonneg (inv_nonneg.2 𝒯.ξ_pos.le) (hlen _)
theorem levelScale_pos (y : 𝒯.Point) : 0 < 𝒯.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
theorem ξ_le_levelScale (y : 𝒯.Point) : 𝒯.ξ ≤ 𝒯.levelScale y := by
  have hL : (1 : ℝ) ≤ 𝒯.L := by
    have := 𝒯.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒯.L)
  have h : (1 : ℝ) ≤ (𝒯.L : ℝ) ^ ((shellIndex 𝒯.L 𝒯.ξ 𝒯.Ω y : ℕ) : ℤ) := by
    rw [zpow_natCast]
    exact one_le_pow₀ hL
  exact le_mul_of_one_le_left 𝒯.ξ_pos.le h
end FineLattice
section ConcreteSeminorms
variable {𝒮 : NestedRegions}
theorem isSeminormFun_supBond : IsSeminormFun (supBond : (𝒮.FineBond → ℝ) → ℝ) := by
  have := finite_fineBond 𝒮
  show IsSeminormFun fun x : 𝒮.FineBond → ℝ => ⨆ b, ‖x b‖
  refine isSeminormFun_iSup (f := fun b (x : 𝒮.FineBond → ℝ) => ‖x b‖) fun b =>
    ⟨fun x y => norm_add_le _ _, fun a x => ?_⟩
  show ‖a * x b‖ = |a| * ‖x b‖
  rw [norm_mul, Real.norm_eq_abs]
theorem isSeminormFun_supTensor (r : ℕ) : IsSeminormFun (supTensor : 𝒮.Tensor r → ℝ) := by
  show IsSeminormFun fun J : 𝒮.Tensor r => ⨆ ν, supBond (J ν)
  exact isSeminormFun_iSup fun ν => isSeminormFun_supBond.comp_linearMap
    (LinearMap.proj ν : 𝒮.Tensor r →ₗ[ℝ] 𝒮.FineBond → ℝ)
def restrictLinear (X : Set 𝒮.Point) : 𝒮.Tensor 1 →ₗ[ℝ] 𝒮.Tensor 1 where
  toFun := restrictTensor X
  map_add' f g := by
    funext ν b
    by_cases h : b ∈ {b | AnchoredIn X b} <;> simp [restrictTensor, restrictBonds, h]
  map_smul' a f := by
    funext ν b
    by_cases h : b ∈ {b | AnchoredIn X b} <;> simp [restrictTensor, restrictBonds, h]
def smulLinear (ζ : 𝒮.FineSite → ℝ) : 𝒮.Tensor 1 →ₗ[ℝ] 𝒮.Tensor 1 where
  toFun := smulSiteTensor ζ
  map_add' f g := by
    funext ν b
    simp only [smulSiteTensor, smulSiteBond, Pi.add_apply, smul_eq_mul]
    ring
  map_smul' a f := by
    funext ν b
    simp only [smulSiteTensor, smulSiteBond, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem abs_le_supTensor {r : ℕ} (J : 𝒮.Tensor r) (ν : Fin r → Fin 4) (b : 𝒮.FineBond) :
    |J ν b| ≤ supTensor J := by
  have := finite_fineBond 𝒮
  have h₁ : ‖J ν b‖ ≤ supBond (J ν) :=
    le_ciSup (f := fun b => ‖J ν b‖) (finite_range _).bddAbove b
  have h₂ : supBond (J ν) ≤ supTensor J :=
    le_ciSup (f := fun ν => supBond (J ν)) (finite_range _).bddAbove ν
  exact (Real.norm_eq_abs _ ▸ h₁).trans h₂
theorem supSite_nonneg (ζ : 𝒮.FineSite → ℝ) : 0 ≤ supSite ζ :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem abs_le_supSite (ζ : 𝒮.FineSite → ℝ) (x : 𝒮.FineSite) : |ζ x| ≤ supSite ζ := by
  have := finite_fineSite 𝒮
  exact Real.norm_eq_abs (ζ x) ▸ le_ciSup (f := fun x => ‖ζ x‖) (finite_range _).bddAbove x
theorem supNorm_add_le {S : ℝ} (p q : PeriodicTorus 4 S) :
    supNorm (p + q) ≤ supNorm p + supNorm q := by apply _root_.YangMills.Construction.PartitionCubes.PartitionFnSupport.torusSupNorm_add_le <;> assumption
theorem supNorm_unitStep_le {S ξ : ℝ} (hξ : 0 ≤ ξ) (μ : Fin 4) :
    supNorm ((unitStep 4 S ξ μ : LatticeSite 4 S ξ) : PeriodicTorus 4 S) ≤ ξ := by
  have hbd : BddBelow {r | ∃ v : Fin 4 → ℝ,
      torusProj 4 S v = ((unitStep 4 S ξ μ : LatticeSite 4 S ξ) : PeriodicTorus 4 S) ∧ r = ‖v‖} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, -, rfl⟩
    exact norm_nonneg _
  refine (csInf_le hbd ⟨Pi.single μ ξ, rfl, rfl⟩).trans ?_
  refine (pi_norm_le_iff_of_nonneg hξ).2 fun i => ?_
  by_cases h : i = μ
  · subst h
    simp [abs_of_nonneg hξ]
  · simp [Pi.single_eq_of_ne h, hξ]
theorem wideCell_subset_outerCube (y : 𝒮.Point) :
    wideCell y ⊆ ApproxInverseScales.outerCube y := by
  intro p hp
  have hξ := levelScale_pos 𝒮 y
  have h : supNorm (p - y) ≤ 2 * 𝒮.levelScale y / 2 := hp
  show supNorm (p - y) ≤ 2 * (2 * 𝒮.levelScale y) / 2
  linarith
theorem anchoredIn_outerCube {y : 𝒮.Point} {b : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ wideCell y) :
    AnchoredIn (ApproxInverseScales.outerCube y) b := by
  have hle := ξ_le_levelScale 𝒮 y
  have h : supNorm ((b.source : 𝒮.Point) - y) ≤ 2 * 𝒮.levelScale y / 2 := hb
  unfold AnchoredIn anchor
  split_ifs
  · show supNorm (((b.source + unitStep 4 𝒮.side 𝒮.ξ b.dir : 𝒮.FineSite) : 𝒮.Point) - y) ≤
      2 * (2 * 𝒮.levelScale y) / 2
    have he : ((b.source + unitStep 4 𝒮.side 𝒮.ξ b.dir : 𝒮.FineSite) : 𝒮.Point) - y =
        ((b.source : 𝒮.Point) - y) + ((unitStep 4 𝒮.side 𝒮.ξ b.dir : 𝒮.FineSite) : 𝒮.Point) := by
      rw [AddSubgroup.coe_add]
      abel
    rw [he]
    have h₁ := supNorm_add_le ((b.source : 𝒮.Point) - y)
      ((unitStep 4 𝒮.side 𝒮.ξ b.dir : 𝒮.FineSite) : 𝒮.Point)
    have h₂ := supNorm_unitStep_le (S := 𝒮.side) 𝒮.ξ_pos.le b.dir
    linarith
  · exact wideCell_subset_outerCube y hb
theorem supTensor_smul_le {y : 𝒮.Point} {ζ : 𝒮.FineSite → ℝ} (hζ : VanishesOff (wideCell y) ζ)
    (K : 𝒮.Tensor 1) :
    supTensor (smulSiteTensor ζ K) ≤
      supSite ζ * supTensor (restrictTensor (ApproxInverseScales.outerCube y) K) := by
  have hn : 0 ≤ supSite ζ * supTensor (restrictTensor (ApproxInverseScales.outerCube y) K) :=
    mul_nonneg (supSite_nonneg ζ) ((isSeminormFun_supTensor 1).nonneg _)
  refine Real.iSup_le (fun ν => Real.iSup_le (fun b => ?_) hn) hn
  show ‖ζ b.source * K ν b‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases ht : (b.source : 𝒮.Point) ∈ wideCell y
  · have h₁ : |K ν b| ≤ supTensor (restrictTensor (ApproxInverseScales.outerCube y) K) := by
      have h₂ := abs_le_supTensor (restrictTensor (ApproxInverseScales.outerCube y) K) ν b
      have h₃ : restrictTensor (ApproxInverseScales.outerCube y) K ν b = K ν b :=
        indicator_of_mem (show b ∈ {b | AnchoredIn (ApproxInverseScales.outerCube y) b} from
          anchoredIn_outerCube ht) _
      rwa [h₃] at h₂
    exact mul_le_mul (abs_le_supSite ζ _) h₁ (abs_nonneg _) (supSite_nonneg ζ)
  · rw [hζ _ ht, abs_zero, zero_mul]
    exact hn
end ConcreteSeminorms
section CubeLists
variable {𝒮 : NestedRegions} {M : ℕ}
end CubeLists
section FiniteSums
variable {ι : Type} {s : Set ι}
end FiniteSums
section SeriesEstimate
variable {𝒮 : NestedRegions} {K m M R₁ : ℕ}
structure SeriesBounded (𝒮 : NestedRegions) (M : ℕ) (P : Seminorm ℝ (𝒮.FineBond → ℝ))
    (g : 𝒮.FineBond → ℝ) (X : ℝ) : Prop where
  chains : ∀ i, ∑ᶠ ω ∈ chainsOfLength 𝒮 M i, P (chainTerm ω g) ≤ (2 : ℝ)⁻¹ ^ i * X
  terms : ∀ i, P (neumannTerm 𝒮 M i g) ≤ (2 : ℝ)⁻¹ ^ i * X
  total : P (baseGreen g) ≤ 2 * X
theorem SeriesBounded.mono {P : Seminorm ℝ (𝒮.FineBond → ℝ)} {g : 𝒮.FineBond → ℝ} {X X' : ℝ}
    (h : SeriesBounded 𝒮 M P g X) (hX : X ≤ X') : SeriesBounded 𝒮 M P g X' :=
  ⟨fun i => (h.chains i).trans (mul_le_mul_of_nonneg_left hX (by positivity)),
    fun i => (h.terms i).trans (mul_le_mul_of_nonneg_left hX (by positivity)),
    h.total.trans (by linarith)⟩
end SeriesEstimate
section Functionals
variable {𝒮 : NestedRegions} {M : ℕ}
inductive Functional (𝒮 : NestedRegions) (M : ℕ) : OperatorFunctional 𝒮 → ℝ → Prop
  | total : Functional 𝒮 M (evalAt baseGreen) 1
  | term (i : ℕ) : Functional 𝒮 M (evalAt (neumannTerm 𝒮 M i)) ((2 : ℝ)⁻¹ ^ i)
  | chains (i : ℕ) : Functional 𝒮 M (sumOverChains 𝒮 M i) ((2 : ℝ)⁻¹ ^ i)
theorem Functional.nonneg {R : OperatorFunctional 𝒮} {ρ : ℝ} (h : Functional 𝒮 M R ρ) : 0 ≤ ρ := by
  cases h <;> positivity
theorem holderSite_nonneg (α : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (ζ : 𝒮.FineSite → ℝ) :
    0 ≤ holderSite α lam ζ := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, x', h₁, -, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (div_nonneg hlam h₁.le) _) (norm_nonneg _)
theorem pNorm_nonneg (p : NormExponent) (f : 𝒮.FineBond → ℝ) :
    0 ≤ (formCutSpace 𝒮).pNorm p f := by
  cases p
  · exact Real.sqrt_nonneg _
  · exact isSeminormFun_supBond.nonneg f
theorem levelScale_le_one {K m R₁ : ℕ} (hlev : 𝒮.IsLevelUnitChain K m M R₁) {y : 𝒮.Point}
    (hy : y ∈ 𝒮.allCentres) : 𝒮.levelScale y ≤ 1 := by
  obtain ⟨n, hn, hyn⟩ := hy
  have hi : shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y ≤ 𝒮.s := (Nat.sInf_le hyn).trans hn
  have hL : (1 : ℝ) ≤ 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  have hs : (𝒮.L : ℝ) ^ shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y ≤ (𝒮.L : ℝ) ^ 𝒮.s := pow_le_pow_right₀ hL hi
  have hξe : 𝒮.ξ = ((𝒮.L : ℝ) ^ 𝒮.s)⁻¹ := by
    rw [hlev.spacing_eq, unitSpacing, zpow_neg, zpow_natCast]
  have he : (𝒮.L : ℝ) ^ shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y * 𝒮.ξ =
      (𝒮.L : ℝ) ^ shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y / (𝒮.L : ℝ) ^ 𝒮.s := by
    rw [div_eq_mul_inv, ← hξe]
  show (𝒮.L : ℝ) ^ ((shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y : ℕ) : ℤ) * 𝒮.ξ ≤ 1
  rw [zpow_natCast, he]
  exact (div_le_one (by positivity)).2 hs
end Functionals
end DivSourceEstimate
end YangMills.Construction
