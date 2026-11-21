import YangMills.Construction.Dirichlet.CoverCubeCount
import YangMills.Construction.Dirichlet.GreenOperatorExistence
import YangMills.Construction.DirichletOperator.BoundsAtOneCubeProof
import YangMills.Construction.DirichletOperator.NeumannSeriesOfTheRemainder
import YangMills.Construction.DirichletOperator.NormOfTheRemainder
import YangMills.Construction.DirichletOperator.ParametrixOfTheCubes
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.RemainderNeumann
section Contraction
variable {ι : Type*} [Fintype ι] {V : Submodule ℝ (ι → ℝ)} (T : V →ₗ[ℝ] V) {q : ℝ}
theorem norm_pow_apply_le_of_contraction (hq0 : 0 ≤ q) (hT : ∀ v, ‖T v‖ ≤ q * ‖v‖) (m : ℕ)
    (v : V) : ‖(T ^ m) v‖ ≤ q ^ m * ‖v‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    calc ‖T ((T ^ m) v)‖ ≤ q * ‖(T ^ m) v‖ := hT _
      _ ≤ q * (q ^ m * ‖v‖) := mul_le_mul_of_nonneg_left ih hq0
      _ = q ^ (m + 1) * ‖v‖ := by ring
omit [Fintype ι] in
theorem sum_range_pow_apply_sub (w : V) (N : ℕ) :
    ∑ m ∈ Finset.range N, (T ^ m) (w - T w) = w - (T ^ N) w := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, map_sub, pow_succ, Module.End.mul_apply]
    abel
theorem existsUnique_sub_apply_eq (hq : q < 1) (hT : ∀ v, ‖T v‖ ≤ q * ‖v‖) (f : V) :
    ∃! w : V, w - T w = f := by
  have hinj : Function.Injective (LinearMap.id - T : V →ₗ[ℝ] V) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hfix : v = T v := sub_eq_zero.mp (by simpa using hv)
    have hle := hT v
    rw [← hfix] at hle
    have hmul : (1 - q) * ‖v‖ ≤ 0 := by linarith
    have hnorm : ‖v‖ ≤ 0 := by
      by_contra hc
      have := mul_pos (sub_pos.mpr hq) (not_le.mp hc)
      linarith
    exact norm_le_zero_iff.mp hnorm
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hinj f
  have hw' : w - T w = f := by simpa using hw
  refine ⟨w, hw', fun w' h => hinj ?_⟩
  simpa [hw'] using h
theorem hasSum_apply_pow_apply_sub (hq0 : 0 ≤ q) (hq : q < 1) (hT : ∀ v, ‖T v‖ ≤ q * ‖v‖)
    (A : V →ₗ[ℝ] (ι → ℝ)) (w : V) (x : ι) :
    HasSum (fun m : ℕ => A ((T ^ m) (w - T w)) x) (A w x) := by
  let A' : V →L[ℝ] (ι → ℝ) := A.toContinuousLinearMap
  have hA : ∀ v : V, ‖A v x‖ ≤ ‖A'‖ * ‖v‖ := fun v =>
    (norm_le_pi_norm (A v) x).trans (A'.le_opNorm v)
  have hpow : ∀ (m : ℕ) (v : V), ‖A ((T ^ m) v) x‖ ≤ ‖A'‖ * ‖v‖ * q ^ m := fun m v => by
    calc ‖A ((T ^ m) v) x‖ ≤ ‖A'‖ * ‖(T ^ m) v‖ := hA _
      _ ≤ ‖A'‖ * (q ^ m * ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_pow_apply_le_of_contraction T hq0 hT m v)
          (ContinuousLinearMap.opNorm_nonneg A')
      _ = ‖A'‖ * ‖v‖ * q ^ m := by ring
  have hs : Summable fun m : ℕ => A ((T ^ m) (w - T w)) x :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq).mul_left _)
      fun m => hpow m (w - T w)
  rw [hs.hasSum_iff_tendsto_nat]
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, A ((T ^ i) (w - T w)) x =
      A w x - A ((T ^ N) w) x := fun N => by
    have h := congrArg (fun v => A v x) (sum_range_pow_apply_sub T w N)
    simpa [map_sum, Finset.sum_apply, map_sub] using h
  simp_rw [hpart]
  have hlim : Tendsto (fun N : ℕ => A ((T ^ N) w) x) atTop (𝓝 0) := by
    have hgeo : Tendsto (fun N : ℕ => ‖A'‖ * ‖w‖ * q ^ N) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul (‖A'‖ * ‖w‖)
    exact squeeze_zero_norm (fun N => hpow N w) hgeo
  simpa using tendsto_const_nhds.sub hlim
end Contraction
variable {d L : ℕ} {S aMinus aPlus : ℝ}
theorem abs_le_supNormAll {ξ : ℝ} [Finite (LatticeSite d S ξ)]
    (f : LatticeSite d S ξ → ℝ) (x : LatticeSite d S ξ) :
    |f x| ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.abs_le_supNormAll <;> assumption
theorem supNormAll_nonneg {ξ : ℝ} (f : LatticeSite d S ξ → ℝ) : 0 ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.zero_le_supNormAll <;> assumption
theorem supNormAll_le_norm {ξ : ℝ} [Fintype (LatticeSite d S ξ)]
    (f : LatticeSite d S ξ → ℝ) : supNormAll f ≤ ‖f‖ := by
  unfold supNormAll supNormOn
  refine Real.sSup_le ?_ (norm_nonneg f)
  rintro r ⟨y, -, rfl⟩
  exact norm_le_pi_norm f y
theorem norm_le_supNormAll {ξ : ℝ} [Fintype (LatticeSite d S ξ)]
    (f : LatticeSite d S ξ → ℝ) : ‖f‖ ≤ supNormAll f :=
  (pi_norm_le_iff_of_nonneg (supNormAll_nonneg f)).mpr fun x => abs_le_supNormAll f x
def vanishingSubspace (ξ : ℝ) (X : Set (PeriodicTorus d S)) :
    Submodule ℝ (LatticeSite d S ξ → ℝ) where
  carrier := {f | VanishesOff X f}
  add_mem' := fun {f g} hf hg x hx => by
    have h1 : f x = 0 := hf x hx
    have h2 : g x = 0 := hg x hx
    simp [h1, h2]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r f hf x hx => by
    have h1 : f x = 0 := hf x hx
    simp [h1]
section Operators
variable (𝒮 : BlockSetting d L aMinus aPlus S) (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ))
def remainderEnd (h : RemainderNorm.Conclusions 𝒮 E) :
    vanishingSubspace 𝒮.ξ (𝒮.Ω 0) →ₗ[ℝ] vanishingSubspace 𝒮.ξ (𝒮.Ω 0) where
  toFun v := ⟨𝒮.totalRemainder E v.1, h.vanishesOff v.1 v.2⟩
  map_add' v w := Subtype.ext (h.map_add v.1 w.1 v.2 w.2)
  map_smul' r v := Subtype.ext (h.map_smul r v.1 v.2)
theorem pow_remainderEnd_apply (h : RemainderNorm.Conclusions 𝒮 E) (m : ℕ)
    (v : vanishingSubspace 𝒮.ξ (𝒮.Ω 0)) :
    (((remainderEnd 𝒮 E h) ^ m) v).1 = (𝒮.totalRemainder E)^[m] v.1 := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
    rfl
theorem pointwiseMul_add {ξ : ℝ} (h f g : LatticeSite d S ξ → ℝ) :
    pointwiseMul h (f + g) = pointwiseMul h f + pointwiseMul h g := by
  funext x
  simp [pointwiseMul, mul_add]
theorem pointwiseMul_smul {ξ : ℝ} (h : LatticeSite d S ξ → ℝ) (r : ℝ)
    (f : LatticeSite d S ξ → ℝ) : pointwiseMul h (r • f) = r • pointwiseMul h f := by
  funext x
  simp only [pointwiseMul, Pi.smul_apply, smul_eq_mul]
  ring
theorem sandwichedGreen_add {Q : CentredCube d S}
    (hQ : GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q))
    (f g : LatticeSite d S 𝒮.ξ → ℝ) :
    𝒮.sandwichedGreen E Q (f + g) = 𝒮.sandwichedGreen E Q f + 𝒮.sandwichedGreen E Q g := by
  simp only [BlockSetting.sandwichedGreen, BlockSetting.cubeGreen, pointwiseMul_add, hQ.map_add]
theorem sandwichedGreen_smul {Q : CentredCube d S}
    (hQ : GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q)) (r : ℝ)
    (f : LatticeSite d S 𝒮.ξ → ℝ) :
    𝒮.sandwichedGreen E Q (r • f) = r • 𝒮.sandwichedGreen E Q f := by
  simp only [BlockSetting.sandwichedGreen, BlockSetting.cubeGreen, pointwiseMul_smul,
    hQ.map_smul]
theorem approxGreen_add (hfin : 𝒮.coverCubes.Finite)
    (hlin : ∀ Q ∈ 𝒮.coverCubes, GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q))
    (f g : LatticeSite d S 𝒮.ξ → ℝ) :
    𝒮.approxGreen E (f + g) = 𝒮.approxGreen E f + 𝒮.approxGreen E g := by
  funext x
  simp only [BlockSetting.approxGreen, Pi.add_apply]
  rw [← finsum_mem_add_distrib hfin]
  refine finsum_mem_congr rfl fun Q hQ => ?_
  rw [sandwichedGreen_add 𝒮 E (hlin Q hQ)]
  rfl
theorem approxGreen_smul
    (hlin : ∀ Q ∈ 𝒮.coverCubes, GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q))
    (r : ℝ) (f : LatticeSite d S 𝒮.ξ → ℝ) :
    𝒮.approxGreen E (r • f) = r • 𝒮.approxGreen E f := by
  funext x
  simp only [BlockSetting.approxGreen, Pi.smul_apply, smul_eq_mul]
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl fun Q hQ => ?_
  rw [sandwichedGreen_smul 𝒮 E (hlin Q hQ)]
  rfl
theorem approxGreen_vanishesOff (hsub : ∀ Q ∈ 𝒮.coverCubes, 𝒮.innerRegion Q ⊆ 𝒮.Ω 0)
    (hlin : ∀ Q ∈ 𝒮.coverCubes, GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q))
    (f : LatticeSite d S 𝒮.ξ → ℝ) :
    VanishesOff (𝒮.Ω 0) (𝒮.approxGreen E f) := by
  intro x hx
  have hzero : ∀ Q ∈ 𝒮.coverCubes, 𝒮.sandwichedGreen E Q f x = 0 := fun Q hQ => by
    have h0 := (hlin Q hQ).vanishesOff (pointwiseMul (𝒮.latticeCutoff Q) f) x
      fun hxQ => hx (hsub Q hQ hxQ)
    simp only [BlockSetting.sandwichedGreen, BlockSetting.cubeGreen, pointwiseMul]
    rw [h0, mul_zero]
  have hcongr := finsum_mem_congr (s := 𝒮.coverCubes) (t := 𝒮.coverCubes)
    (f := fun Q => 𝒮.sandwichedGreen E Q f x) (g := fun _ => (0 : ℝ)) rfl hzero
  simpa [BlockSetting.approxGreen] using hcongr
def approxGreenLinear (hfin : 𝒮.coverCubes.Finite)
    (hlin : ∀ Q ∈ 𝒮.coverCubes, GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q)) :
    vanishingSubspace 𝒮.ξ (𝒮.Ω 0) →ₗ[ℝ] (LatticeSite d S 𝒮.ξ → ℝ) where
  toFun v := 𝒮.approxGreen E v.1
  map_add' v w := approxGreen_add 𝒮 E hfin hlin v.1 w.1
  map_smul' r v := approxGreen_smul 𝒮 E hlin r v.1
end Operators
theorem claim_holds (hSites : CentreCellFactsHold) (hCount : CoverCount.coverCubeBounds_statement)
    (hPart : PartitionOfUnity.PartitionClaim) (hFloors : ThresholdConsequences.Claim)
    (hGreen : GreenExistence.GreenOperatorExists) (hLin : GreenLinearity.BlockGreenLinear)
    (hNorm : RemainderNorm.Claim) (hPara : CubeParametrix.Claim) :
    Claim := by
  intro d L aMinus aPlus hL S 𝒮 hF E hE
  have hB := hSites d L aMinus aPlus S hL 𝒮
  have hfinite := hB.finite_site
  let _ : Fintype (LatticeSite d S 𝒮.ξ) := Fintype.ofFinite _
  have hC := hFloors d L aMinus aPlus hL S 𝒮 hF
  have hfin : 𝒮.coverCubes.Finite :=
    (hCount d L aMinus aPlus hL S 𝒮 hC.blockSize_floor hC.gap_floor).finite_cubes
  have hReg := (hPart d L aMinus aPlus hL S 𝒮 hC.blockSize_floor hC.gap_floor).1
  have hlin : ∀ Q ∈ 𝒮.coverCubes, GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q) := by
    rintro Q hQ
    obtain ⟨n, -, hn⟩ := id hQ
    exact hLin d L aMinus aPlus hL S 𝒮 _ _ (PartitionOfUnity.CubePlacement.region
      hReg n Q hn) (hE Q hQ)
  have hsub : ∀ Q ∈ 𝒮.coverCubes, 𝒮.innerRegion Q ⊆ 𝒮.Ω 0 := fun Q _ =>
    Set.iUnion₂_subset fun y hy => hB.cell_subset y hy.1
  have hN := hNorm d L aMinus aPlus hL S 𝒮 hF E hE
  have hM : (0 : ℝ) < 𝒮.M := by linarith [hC.walkConst_pos, hC.two_mul_walkConst_le]
  set q : ℝ := WalkExpansion.walkConstC d L aMinus aPlus * (𝒮.M : ℝ)⁻¹ with hqdef
  have hq0 : 0 ≤ q := mul_nonneg hC.walkConst_pos.le (inv_nonneg.mpr hM.le)
  have hq : q < 1 := by
    have hhalf : q ≤ 1 / 2 := by
      rw [hqdef, ← div_eq_mul_inv, div_le_iff₀ hM]
      linarith [hC.two_mul_walkConst_le]
    linarith
  let T := remainderEnd 𝒮 E hN
  have hT : ∀ v, ‖T v‖ ≤ q * ‖v‖ := fun v => by
    calc ‖T v‖ = ‖𝒮.totalRemainder E v.1‖ := rfl
      _ ≤ supNormAll (𝒮.totalRemainder E v.1) := norm_le_supNormAll _
      _ ≤ q * supNormAll v.1 := hN.supNorm_le v.1 v.2
      _ ≤ q * ‖v.1‖ := mul_le_mul_of_nonneg_left (supNormAll_le_norm _) hq0
      _ = q * ‖v‖ := rfl
  have hgreen : ∀ f g : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
      VanishesOff (𝒮.Ω 0) g → g - 𝒮.totalRemainder E g = f →
      𝒮.fullGreen f = 𝒮.approxGreen E g := by
    intro f g hf hg hfg
    have hA : 𝒮.fullOperator (𝒮.approxGreen E g) = f :=
      (hPara d L aMinus aPlus hL S 𝒮 hF E hE g hg).trans hfg
    have hAf := approxGreen_vanishesOff 𝒮 E hsub hlin g
    have hinv := (hGreen d L aMinus aPlus hL S 𝒮).existsUnique_preimage f hf
    have hres : restrictTo (𝒮.Ω 0) f = f := by
      funext x
      by_cases h : (x : PeriodicTorus d S) ∈ 𝒮.Ω 0
      · simp [restrictTo, indicator, h]
      · simp [restrictTo, indicator, h, hf x h]
    have hspec : VanishesOff (𝒮.Ω 0) (𝒮.fullGreen f) ∧
        𝒮.blockOperator (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0)) (𝒮.fullGreen f) = restrictTo (𝒮.Ω 0) f :=
      Classical.epsilon_spec (p := fun u : LatticeSite d S 𝒮.ξ → ℝ =>
        VanishesOff (𝒮.Ω 0) u ∧
          𝒮.blockOperator (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0)) u = restrictTo (𝒮.Ω 0) f)
        ⟨𝒮.approxGreen E g, hAf, hA.trans hres.symm⟩
    exact hinv.unique ⟨hspec.1, hspec.2.trans hres⟩ ⟨hAf, hA⟩
  refine ⟨fun f hf => ?_, hgreen, fun f hf x => ?_⟩
  · obtain ⟨g, hg, hu⟩ := existsUnique_sub_apply_eq T hq hT ⟨f, hf⟩
    refine ⟨g.1, ⟨g.2, congrArg Subtype.val hg⟩, ?_⟩
    rintro g' ⟨hg'₁, hg'₂⟩
    exact congrArg Subtype.val (hu ⟨g', hg'₁⟩ (Subtype.ext hg'₂))
  · obtain ⟨g, hg, -⟩ := existsUnique_sub_apply_eq T hq hT ⟨f, hf⟩
    have hsum := hasSum_apply_pow_apply_sub T hq0 hq hT (approxGreenLinear 𝒮 E hfin hlin) g x
    rw [hg] at hsum
    have hval : approxGreenLinear 𝒮 E hfin hlin g x = 𝒮.fullGreen f x :=
      (congrFun (hgreen f g.1 hf g.2 (congrArg Subtype.val hg)) x).symm
    rw [hval] at hsum
    have hterm : (fun m : ℕ => 𝒮.approxGreen E ((𝒮.totalRemainder E)^[m] f) x) =
        fun m : ℕ => approxGreenLinear 𝒮 E hfin hlin ((T ^ m) ⟨f, hf⟩) x := by
      funext m
      show _ = 𝒮.approxGreen E (((T ^ m) ⟨f, hf⟩).1) x
      rw [pow_remainderEnd_apply 𝒮 E hN m ⟨f, hf⟩]
    rw [hterm]
    exact hsum
end YangMills.Construction.Dirichlet.RemainderNeumann
