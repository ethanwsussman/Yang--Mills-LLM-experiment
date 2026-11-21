import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.SummableBoundsOfTheFlow.AGapAmongFinitelyManyPoints
import YangMills.Construction.SummableBoundsOfTheFlow.CovarianceOnTheOpenBalls
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantOfMomentsAcrossAGap
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantOfMomentsUnderAShift
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithTheirConstantsForm
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import YangMills.Construction.SummableBoundsOfTheFlow.SumOfTheWeightsAboutACell
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Cumulants
section CellDistance
variable {F : BlockFrame}
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (x y z : F.Cell) :
    cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem cellSupDist_triangle_real (x y z : F.Cell) :
    (cellSupDist x z : ℝ) ≤ (cellSupDist x y : ℝ) + (cellSupDist y z : ℝ) := by
  exact_mod_cast cellSupDist_triangle x y z
end CellDistance
section Holder
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
theorem integral_prod_abs_le_prod {M : ℕ} (s : Finset (Fin M)) (u : Fin M → Ω → ℝ) (A : Fin M → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hi : ∀ i ∈ s, Integrable (fun ω => |u i ω| ^ s.card) ν)
    (hp : Integrable (fun ω => ∏ i ∈ s, |u i ω|) ν)
    (hm : ∀ i ∈ s, ∫ ω, |u i ω| ^ s.card ∂ν ≤ A i ^ s.card) :
    ∫ ω, ∏ i ∈ s, |u i ω| ∂ν ≤ ∏ i ∈ s, A i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hn0 : s.card ≠ 0 := (card_pos.mpr hs).ne'
  have hn : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr hs
  have key : ∀ ε : ℝ, 0 < ε → ∫ ω, ∏ i ∈ s, |u i ω| ∂ν ≤ ∏ i ∈ s, (A i + ε) := by
    intro ε hε
    have hB : ∀ i ∈ s, 0 < A i + ε := fun i h => by linarith [hA i h]
    have hP : 0 < ∏ i ∈ s, (A i + ε) := prod_pos hB
    have hpt : ∀ ω, ∏ i ∈ s, |u i ω| ≤
        (∏ i ∈ s, (A i + ε)) * ∑ i ∈ s, (s.card : ℝ)⁻¹ * (|u i ω| ^ s.card / (A i + ε) ^ s.card) := by
      intro ω
      have hgm := Real.geom_mean_le_arith_mean_weighted s (fun _ => (s.card : ℝ)⁻¹)
        (fun i => (|u i ω| / (A i + ε)) ^ s.card) (fun _ _ => (inv_pos.mpr hn).le)
        (by rw [sum_const, nsmul_eq_mul]; field_simp)
        (fun i h => pow_nonneg (div_nonneg (abs_nonneg _) (hB i h).le) _)
      have hl : ∏ i ∈ s, ((|u i ω| / (A i + ε)) ^ s.card) ^ (s.card : ℝ)⁻¹ =
          (∏ i ∈ s, |u i ω|) / ∏ i ∈ s, (A i + ε) := by
        rw [← prod_div_distrib]
        apply prod_congr rfl
        intro i h
        exact Real.pow_rpow_inv_natCast (div_nonneg (abs_nonneg _) (hB i h).le) hn0
      rw [hl, div_le_iff₀ hP] at hgm
      rw [mul_comm]
      refine hgm.trans (le_of_eq ?_)
      congr 1
      apply sum_congr rfl
      intro i _
      rw [div_pow]
    have hR : Integrable (fun ω => (∏ i ∈ s, (A i + ε)) *
        ∑ i ∈ s, (s.card : ℝ)⁻¹ * (|u i ω| ^ s.card / (A i + ε) ^ s.card)) ν :=
      (integrable_finsetSum _ fun i h => ((hi i h).div_const _).const_mul _).const_mul _
    refine (integral_mono hp hR hpt).trans ?_
    rw [integral_const_mul, integral_finsetSum _ fun i h => ((hi i h).div_const _).const_mul _]
    have hone : ∑ i ∈ s, ∫ ω, (s.card : ℝ)⁻¹ * (|u i ω| ^ s.card / (A i + ε) ^ s.card) ∂ν ≤ 1 := by
      have hterm : ∀ i ∈ s, ∫ ω, (s.card : ℝ)⁻¹ * (|u i ω| ^ s.card / (A i + ε) ^ s.card) ∂ν ≤
          (s.card : ℝ)⁻¹ := by
        intro i h
        rw [integral_const_mul, integral_div]
        have hBp : 0 < (A i + ε) ^ s.card := pow_pos (hB i h) _
        have h1 : ∫ ω, |u i ω| ^ s.card ∂ν ≤ (A i + ε) ^ s.card :=
          (hm i h).trans (pow_le_pow_left₀ (hA i h) (by linarith) _)
        have h2 : (∫ ω, |u i ω| ^ s.card ∂ν) / (A i + ε) ^ s.card ≤ 1 :=
          (div_le_one hBp).mpr h1
        calc (s.card : ℝ)⁻¹ * ((∫ ω, |u i ω| ^ s.card ∂ν) / (A i + ε) ^ s.card)
            ≤ (s.card : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hn).le
          _ = (s.card : ℝ)⁻¹ := mul_one _
      refine (sum_le_sum hterm).trans (le_of_eq ?_)
      rw [sum_const, nsmul_eq_mul]
      field_simp
    calc (∏ i ∈ s, (A i + ε)) *
          ∑ i ∈ s, ∫ ω, (s.card : ℝ)⁻¹ * (|u i ω| ^ s.card / (A i + ε) ^ s.card) ∂ν
        ≤ (∏ i ∈ s, (A i + ε)) * 1 := mul_le_mul_of_nonneg_left hone hP.le
      _ = _ := mul_one _
  have hc : Continuous fun ε : ℝ => ∏ i ∈ s, (A i + ε) :=
    continuous_finsetProd _ fun i _ => continuous_const.add continuous_id
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [add_zero] at ht
  exact ge_of_tendsto ht (eventually_mem_nhdsWithin.mono fun ε hε => key ε hε)
end Holder
section Moments
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
structure HasAllMoments (ν : Measure Ω) (f : Ω → ℝ) : Prop where
  aesm : AEStronglyMeasurable f ν
  integrable_pow : ∀ q : ℕ, Integrable (fun ω => |f ω| ^ q) ν
theorem aestronglyMeasurable_abs {f : Ω → ℝ} (hf : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable (fun ω => |f ω|) ν := by
  simpa [Real.norm_eq_abs] using hf.norm
theorem HasAllMoments.const [IsProbabilityMeasure ν] (c : ℝ) : HasAllMoments ν fun _ => c :=
  ⟨aestronglyMeasurable_const, fun _ => integrable_const _⟩
theorem HasAllMoments.mul {f g : Ω → ℝ} (hf : HasAllMoments ν f) (hg : HasAllMoments ν g) :
    HasAllMoments ν fun ω => f ω * g ω := by
  refine ⟨hf.aesm.mul hg.aesm, fun q => ?_⟩
  refine Integrable.mono' ((hf.integrable_pow (2 * q)).add (hg.integrable_pow (2 * q)))
    ((aestronglyMeasurable_abs (hf.aesm.mul hg.aesm)).pow q) (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _), abs_mul, mul_pow]
  have e1 : |f ω| ^ (2 * q) = (|f ω| ^ q) ^ 2 := by rw [← pow_mul, mul_comm]
  have e2 : |g ω| ^ (2 * q) = (|g ω| ^ q) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [e1, e2]
  nlinarith [sq_nonneg (|f ω| ^ q - |g ω| ^ q)]
theorem HasAllMoments.add {f g : Ω → ℝ} (hf : HasAllMoments ν f) (hg : HasAllMoments ν g) :
    HasAllMoments ν fun ω => f ω + g ω := by
  refine ⟨hf.aesm.add hg.aesm, fun q => ?_⟩
  refine Integrable.mono' (((hf.integrable_pow q).add (hg.integrable_pow q)).const_mul (2 ^ q))
    ((aestronglyMeasurable_abs (hf.aesm.add hg.aesm)).pow q) (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  have ha := abs_nonneg (f ω)
  have hb := abs_nonneg (g ω)
  have hab := abs_add_le (f ω) (g ω)
  rcases le_total (|f ω|) (|g ω|) with h | h
  · have h1 : |f ω + g ω| ≤ 2 * |g ω| := by linarith
    calc |f ω + g ω| ^ q ≤ (2 * |g ω|) ^ q := pow_le_pow_left₀ (abs_nonneg _) h1 q
      _ = 2 ^ q * |g ω| ^ q := mul_pow _ _ _
      _ ≤ 2 ^ q * (|f ω| ^ q + |g ω| ^ q) := by
          have : 0 ≤ |f ω| ^ q := pow_nonneg ha _
          have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
          nlinarith
  · have h1 : |f ω + g ω| ≤ 2 * |f ω| := by linarith
    calc |f ω + g ω| ^ q ≤ (2 * |f ω|) ^ q := pow_le_pow_left₀ (abs_nonneg _) h1 q
      _ = 2 ^ q * |f ω| ^ q := mul_pow _ _ _
      _ ≤ 2 ^ q * (|f ω| ^ q + |g ω| ^ q) := by
          have : 0 ≤ |g ω| ^ q := pow_nonneg hb _
          have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
          nlinarith
theorem HasAllMoments.abs {f : Ω → ℝ} (hf : HasAllMoments ν f) : HasAllMoments ν fun ω => |f ω| := by
  refine ⟨aestronglyMeasurable_abs hf.aesm, fun q => ?_⟩
  simpa only [abs_abs] using hf.integrable_pow q
theorem HasAllMoments.prod [IsProbabilityMeasure ν] {M : ℕ} (s : Finset (Fin M)) {u : Fin M → Ω → ℝ}
    (hu : ∀ i ∈ s, HasAllMoments ν (u i)) : HasAllMoments ν fun ω => ∏ i ∈ s, u i ω := by
  induction s using Finset.induction_on with
  | empty => simpa using HasAllMoments.const (ν := ν) 1
  | insert i s hi ih =>
    have h := (hu i (mem_insert_self _ _)).mul (ih fun j hj => hu j (mem_insert_of_mem hj))
    simpa only [prod_insert hi] using h
theorem HasAllMoments.integrable {f : Ω → ℝ} (hf : HasAllMoments ν f) : Integrable f ν := by
  have h := hf.integrable_pow 1
  simp only [pow_one] at h
  exact (integrable_norm_iff hf.aesm).mp (by simpa [Real.norm_eq_abs] using h)
theorem HasAllMoments.integrable_sq {f : Ω → ℝ} (hf : HasAllMoments ν f) :
    Integrable (fun ω => f ω ^ 2) ν := by
  simpa only [sq_abs] using hf.integrable_pow 2
end Moments
section Gradients
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem contDiffOn_prod_family {M : ℕ} {O : Set (BondField ι)} (G : Fin M → BondField ι → ℝ)
    (hG : ∀ i, ContDiffOn ℝ 1 (G i) O) (U : Finset (Fin M)) :
    ContDiffOn ℝ 1 (fun ζ => ∏ i ∈ U, G i ζ) O := by
  induction U using Finset.induction_on with
  | empty => simpa using contDiffOn_const
  | insert i U hi ih => simpa only [prod_insert hi] using (hG i).mul ih
theorem continuousOn_bondGradNorm {O : Set (BondField ι)} (hO : IsOpen O)
    {f : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f O) (b : ι) : ContinuousOn (bondGradNorm f b) O := by
  unfold bondGradNorm
  exact ((hf.continuousOn_fderiv_of_isOpen hO le_rfl).clm_comp continuousOn_const).norm
theorem bondGradNorm_nonneg (f : BondField ι → ℝ) (b : ι) (η : BondField ι) :
    0 ≤ bondGradNorm f b η := norm_nonneg _
theorem bondGradNorm_sub_const (f : BondField ι → ℝ) (c : ℝ) (b : ι) :
    bondGradNorm (fun ζ => f ζ - c) b = bondGradNorm f b := by
  funext η
  unfold bondGradNorm
  rw [fderiv_sub_const]
theorem bondGradNorm_prod_le {M : ℕ} {O : Set (BondField ι)} (hO : IsOpen O)
    (G : Fin M → BondField ι → ℝ) (hG : ∀ i, ContDiffOn ℝ 1 (G i) O)
    (U : Finset (Fin M)) (b : ι) {η : BondField ι} (hη : η ∈ O) :
    bondGradNorm (fun ζ => ∏ i ∈ U, G i ζ) b η ≤
      ∑ i ∈ U, (∏ j ∈ U.erase i, |G j η|) * bondGradNorm (G i) b η := by
  have hd : HasFDerivAt (fun ζ => ∏ i ∈ U, G i ζ)
      (∑ i ∈ U, (∏ j ∈ U.erase i, G j η) • fderiv ℝ (G i) η) η :=
    HasFDerivAt.finsetProd fun i _ =>
      (((hG i).differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hη)).hasFDerivAt
  unfold bondGradNorm
  rw [hd.fderiv]
  set S := ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b
  have hsum : (∑ i ∈ U, (∏ j ∈ U.erase i, G j η) • fderiv ℝ (G i) η).comp S =
      ∑ i ∈ U, (∏ j ∈ U.erase i, G j η) • (fderiv ℝ (G i) η).comp S := by
    ext e
    simp
  rw [hsum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_prod]
end Gradients
section DoubleSum
variable {ι : Type} [Fintype ι] {M : ℕ}
theorem bondDoubleSum_le_of_gap (κ ell W uf ug : ℝ) (hκ : 0 < κ) (huf : 0 ≤ uf) (hug : 0 ≤ ug) (hW : 0 ≤ W)
    (d : ι → ι → ℝ) (dz : Fin M → ι → ℝ) (U V : Finset (Fin M))
    (Nf Ng : ι → ℝ) (hNf0 : ∀ b, 0 ≤ Nf b) (hNg0 : ∀ b, 0 ≤ Ng b)
    (hNf : ∀ b, Nf b ≤ uf * ∑ i ∈ U, Real.exp (-(2 * κ * dz i b)))
    (hNg : ∀ b, Ng b ≤ ug * ∑ j ∈ V, Real.exp (-(2 * κ * dz j b)))
    (hgap : ∀ i ∈ U, ∀ j ∈ V, ∀ b b', ell ≤ dz i b + d b b' + dz j b')
    (hdz : ∀ i b, 0 ≤ dz i b)
    (hsum : ∀ i, ∑ b, Real.exp (-(κ * dz i b)) ≤ W) :
    ∑ b, ∑ b', Nf b * Real.exp (-(κ * d b b')) * Ng b' ≤
      uf * ug * ((U.card : ℝ) * W) * ((V.card : ℝ) * W) * Real.exp (-(κ * ell)) := by
  set c := Real.exp (-(κ * ell)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set A : ι → ℝ := fun b => ∑ i ∈ U, Real.exp (-(κ * dz i b)) with hA
  set B : ι → ℝ := fun b => ∑ j ∈ V, Real.exp (-(κ * dz j b)) with hB
  have hterm : ∀ b b', Nf b * Real.exp (-(κ * d b b')) * Ng b' ≤ uf * ug * c * (A b * B b') := by
    intro b b'
    have hE : 0 ≤ Real.exp (-(κ * d b b')) := (Real.exp_pos _).le
    have h1 : Nf b * Real.exp (-(κ * d b b')) * Ng b' ≤
        (uf * ∑ i ∈ U, Real.exp (-(2 * κ * dz i b))) * Real.exp (-(κ * d b b')) *
          (ug * ∑ j ∈ V, Real.exp (-(2 * κ * dz j b'))) := by
      have hS : 0 ≤ uf * ∑ i ∈ U, Real.exp (-(2 * κ * dz i b)) :=
        mul_nonneg huf (sum_nonneg fun _ _ => (Real.exp_pos _).le)
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hNf b) hE) (hNg b') (hNg0 b')
        (mul_nonneg hS hE)
    have h2 : (∑ i ∈ U, Real.exp (-(2 * κ * dz i b))) * Real.exp (-(κ * d b b')) *
        (∑ j ∈ V, Real.exp (-(2 * κ * dz j b'))) ≤ c * (A b * B b') := by
      have e1 : (∑ i ∈ U, Real.exp (-(2 * κ * dz i b))) * Real.exp (-(κ * d b b')) *
          (∑ j ∈ V, Real.exp (-(2 * κ * dz j b'))) = ∑ i ∈ U, ∑ j ∈ V,
            Real.exp (-(2 * κ * dz i b)) * Real.exp (-(κ * d b b')) *
              Real.exp (-(2 * κ * dz j b')) := by
        rw [sum_mul, sum_mul_sum]
      have e2 : c * (A b * B b') = ∑ i ∈ U, ∑ j ∈ V,
          c * (Real.exp (-(κ * dz i b)) * Real.exp (-(κ * dz j b'))) := by
        simp only [hA, hB]
        rw [sum_mul_sum, mul_sum]
        simp only [mul_sum]
      rw [e1, e2]
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hc, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hgap i hi j hj b b'
      have h3 := mul_le_mul_of_nonneg_left this hκ.le
      nlinarith [hdz i b, hdz j b']
    calc Nf b * Real.exp (-(κ * d b b')) * Ng b'
        ≤ (uf * ∑ i ∈ U, Real.exp (-(2 * κ * dz i b))) * Real.exp (-(κ * d b b')) *
          (ug * ∑ j ∈ V, Real.exp (-(2 * κ * dz j b'))) := h1
      _ = uf * ug * ((∑ i ∈ U, Real.exp (-(2 * κ * dz i b))) * Real.exp (-(κ * d b b')) *
          (∑ j ∈ V, Real.exp (-(2 * κ * dz j b')))) := by ring
      _ ≤ uf * ug * (c * (A b * B b')) := mul_le_mul_of_nonneg_left h2 (mul_nonneg huf hug)
      _ = uf * ug * c * (A b * B b') := by ring
  have hsA : ∑ b, A b ≤ (U.card : ℝ) * W := by
    simp only [hA]
    rw [sum_comm]
    have := sum_le_card_nsmul U (fun i => ∑ b, Real.exp (-(κ * dz i b))) W fun i _ => hsum i
    simpa [nsmul_eq_mul] using this
  have hsB : ∑ b, B b ≤ (V.card : ℝ) * W := by
    simp only [hB]
    rw [sum_comm]
    have := sum_le_card_nsmul V (fun i => ∑ b, Real.exp (-(κ * dz i b))) W fun i _ => hsum i
    simpa [nsmul_eq_mul] using this
  have hB0 : 0 ≤ ∑ b, B b := sum_nonneg fun b _ => sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc ∑ b, ∑ b', Nf b * Real.exp (-(κ * d b b')) * Ng b'
      ≤ ∑ b, ∑ b', uf * ug * c * (A b * B b') :=
        sum_le_sum fun b _ => sum_le_sum fun b' _ => hterm b b'
    _ = uf * ug * c * ((∑ b, A b) * ∑ b, B b) := by
        rw [sum_mul_sum, mul_sum]
        simp only [mul_sum]
    _ ≤ uf * ug * c * (((U.card : ℝ) * W) * ((V.card : ℝ) * W)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hsA hsB hB0 (mul_nonneg (Nat.cast_nonneg _) hW))
          (mul_nonneg (mul_nonneg huf hug) hc0)
    _ = _ := by ring
end DoubleSum
section GradientOfProduct
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem ballL2Norm_bondGradNorm_prod_le {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} {O : Set (BondField ι)}
    (hO : IsOpen O) {ν : Measure (BondField ι)} [IsProbabilityMeasure ν]
    (hae : ∀ᵐ η ∂ν, η ∈ O)
    (hmean : ∀ f : BondField ι → ℝ, ∫ η, f η ∂ν = ballExpectation r Ψ f)
    (haes : ∀ {φ : BondField ι → ℝ}, ContinuousOn φ O → AEStronglyMeasurable φ ν)
    {M : ℕ} (G : Fin M → BondField ι → ℝ) (hG : ∀ i, ContDiffOn ℝ 1 (G i) O)
    (hGm : ∀ i, HasAllMoments ν (G i)) (b : ι) (hPm : ∀ i, HasAllMoments ν (bondGradNorm (G i) b))
    (a : Fin M → ℝ) (ha : ∀ i, 0 ≤ a i) (sx : ℝ) (hsx : 0 ≤ sx) (e : Fin M → ℝ) (he : ∀ i, 0 ≤ e i)
    (U : Finset (Fin M))
    (hval : ∀ i ∈ U, ∫ η, |G i η| ^ (2 * U.card) ∂ν ≤ a i ^ (2 * U.card))
    (hgrad : ∀ i ∈ U, ∫ η, |bondGradNorm (G i) b η| ^ (2 * U.card) ∂ν ≤
      (a i * sx * e i) ^ (2 * U.card)) :
    Integrable (fun η => bondGradNorm (fun ζ => ∏ i ∈ U, G i ζ) b η ^ 2) ν ∧
    ballL2Norm r Ψ (bondGradNorm (fun ζ => ∏ i ∈ U, G i ζ) b) ≤
      (U.card : ℝ) * (∏ i ∈ U, a i) * sx * ∑ i ∈ U, e i := by
  set n := U.card with hn
  set D := ∏ i ∈ U, a i with hD
  have hD0 : 0 ≤ D := prod_nonneg fun i _ => ha i
  set P := bondGradNorm (fun ζ => ∏ i ∈ U, G i ζ) b with hP
  set Tt : Fin M → BondField ι → ℝ :=
    fun i η => (∏ j ∈ U.erase i, |G j η|) * bondGradNorm (G i) b η with hTt
  have hTm : ∀ i, HasAllMoments ν (Tt i) := fun i =>
    (HasAllMoments.prod _ fun j _ => (hGm j).abs).mul (hPm i)
  have hcP : ContinuousOn P O := continuousOn_bondGradNorm hO (contDiffOn_prod_family G hG U) b
  have hpt : ∀ᵐ η ∂ν, P η ^ 2 ≤ (n : ℝ) * ∑ i ∈ U, Tt i η ^ 2 := by
    filter_upwards [hae] with η hη
    have h1 : P η ≤ ∑ i ∈ U, Tt i η := bondGradNorm_prod_le hO G hG U b hη
    have h0 : 0 ≤ P η := bondGradNorm_nonneg _ _ _
    calc P η ^ 2 ≤ (∑ i ∈ U, Tt i η) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ (n : ℝ) * ∑ i ∈ U, Tt i η ^ 2 := sq_sum_le_card_mul_sum_sq
  have hR : Integrable (fun η => (n : ℝ) * ∑ i ∈ U, Tt i η ^ 2) ν :=
    (integrable_finsetSum _ fun i _ => (hTm i).integrable_sq).const_mul _
  have hPint : Integrable (fun η => P η ^ 2) ν := by
    refine Integrable.mono' hR ((haes hcP).pow 2) ?_
    filter_upwards [hpt] with η hη
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hη
  refine ⟨hPint, ?_⟩
  have hterm : ∀ i ∈ U, ∫ η, Tt i η ^ 2 ∂ν ≤ (D * sx * e i) ^ 2 := by
    intro i hi
    set w : Fin M → BondField ι → ℝ :=
      fun l η => if l = i then bondGradNorm (G i) b η ^ 2 else G l η ^ 2 with hw
    set A : Fin M → ℝ := fun l => if l = i then (a i * sx * e i) ^ 2 else a l ^ 2 with hAdef
    have hwm : ∀ l, HasAllMoments ν (w l) := by
      intro l
      by_cases h : l = i
      · simp only [hw, h, if_true, sq]
        exact (hPm i).mul (hPm i)
      · simp only [hw, h, if_false, sq]
        exact (hGm l).mul (hGm l)
    have hprod : ∀ η, ∏ l ∈ U, |w l η| = Tt i η ^ 2 := by
      intro η
      rw [← mul_prod_erase U _ hi]
      have h1 : |w i η| = bondGradNorm (G i) b η ^ 2 := by
        simp only [hw, if_true]
        exact abs_of_nonneg (sq_nonneg _)
      have h2 : ∏ l ∈ U.erase i, |w l η| = ∏ l ∈ U.erase i, |G l η| ^ 2 := by
        apply prod_congr rfl
        intro l hl
        have hne : l ≠ i := (mem_erase.mp hl).1
        simp only [hw, hne, if_false]
        rw [abs_of_nonneg (sq_nonneg _), sq_abs]
      rw [h1, h2, prod_pow]
      simp only [hTt]
      ring
    have hmom : ∀ l ∈ U, ∫ η, |w l η| ^ n ∂ν ≤ A l ^ n := by
      intro l hl
      by_cases h : l = i
      · subst h
        simp only [hw, hAdef, if_true]
        have e1 : (fun η => |bondGradNorm (G l) b η ^ 2| ^ n) =
            fun η => |bondGradNorm (G l) b η| ^ (2 * n) := by
          funext η
          rw [abs_pow, pow_mul]
        rw [e1, ← pow_mul]
        exact hgrad l hl
      · simp only [hw, hAdef, h, if_false]
        have e1 : (fun η => |G l η ^ 2| ^ n) = fun η => |G l η| ^ (2 * n) := by
          funext η
          rw [abs_pow, pow_mul]
        rw [e1, ← pow_mul]
        exact hval l hl
    have hA0 : ∀ l ∈ U, 0 ≤ A l := by
      intro l _
      simp only [hAdef]
      split_ifs <;> positivity
    have hH := integral_prod_abs_le_prod (ν := ν) U w A hA0
      (fun l _ => (hwm l).integrable_pow _)
      ((HasAllMoments.prod U fun l _ => (hwm l).abs).integrable) hmom
    have e2 : ∫ η, Tt i η ^ 2 ∂ν = ∫ η, ∏ l ∈ U, |w l η| ∂ν := by
      apply integral_congr_ae
      filter_upwards with η
      exact (hprod η).symm
    rw [e2]
    refine hH.trans (le_of_eq ?_)
    rw [← mul_prod_erase U _ hi]
    have h3 : ∏ l ∈ U.erase i, A l = ∏ l ∈ U.erase i, a l ^ 2 := by
      apply prod_congr rfl
      intro l hl
      have hne : l ≠ i := (mem_erase.mp hl).1
      simp only [hAdef, hne, if_false]
    have h4 : A i = (a i * sx * e i) ^ 2 := by simp only [hAdef, if_true]
    rw [h3, h4, prod_pow, hD, ← mul_prod_erase U _ hi]
    ring
  have hmean2 : ∫ η, P η ^ 2 ∂ν ≤ (n : ℝ) * ∑ i ∈ U, (D * sx * e i) ^ 2 := by
    refine (integral_mono_ae hPint hR hpt).trans ?_
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (hTm i).integrable_sq]
    exact mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
  set S := ∑ i ∈ U, e i with hS
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => he i
  have hsq : ∑ i ∈ U, e i ^ 2 ≤ S ^ 2 := by
    have : ∀ i ∈ U, e i ^ 2 ≤ e i * S := by
      intro i hi
      rw [sq]
      exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => he j) hi) (he i)
    refine (sum_le_sum this).trans (le_of_eq ?_)
    rw [← sum_mul, sq]
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    exact_mod_cast this
  have hfin : (n : ℝ) * ∑ i ∈ U, (D * sx * e i) ^ 2 ≤ ((n : ℝ) * D * sx * S) ^ 2 := by
    have e3 : ∑ i ∈ U, (D * sx * e i) ^ 2 = (D * sx) ^ 2 * ∑ i ∈ U, e i ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [e3]
    have h5 : (n : ℝ) * ∑ i ∈ U, e i ^ 2 ≤ (n : ℝ) ^ 2 * S ^ 2 :=
      mul_le_mul hnn hsq (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
    calc (n : ℝ) * ((D * sx) ^ 2 * ∑ i ∈ U, e i ^ 2)
        = (D * sx) ^ 2 * ((n : ℝ) * ∑ i ∈ U, e i ^ 2) := by ring
      _ ≤ (D * sx) ^ 2 * ((n : ℝ) ^ 2 * S ^ 2) := mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
      _ = _ := by ring
  unfold ballL2Norm
  rw [← hmean]
  refine Real.sqrt_le_iff.mpr ⟨?_, ?_⟩
  · positivity
  · exact hmean2.trans hfin
end GradientOfProduct
section Bound
def jointCumulantSum {p : ℕ} (mo : Finset (Fin p) → ℝ) : ℝ :=
  ∑ π : Finpartition (univ : Finset (Fin p)),
    (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, mo J
set_option maxHeartbeats 4000000 in
theorem abs_cumulant_le_of_order
    (hCov : ConvexObservables.covarianceOpenBallsStatement) (hShift : CumulantShiftInvariant)
    (hAcross : CumulantSmallAcrossGap) (hGap : FiniteMetricGap.ExistsGapAmongFinitePoints)
    (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement)
    {κ lam W : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (hW0 : 0 ≤ W)
    {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {y : ι → F.Cell} {ρ x : ℝ}
    {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} (hρ : 0 < ρ) (hx : 0 < x)
    (hcut : IsCutoff ρ p)
    (hWs : ∀ z : F.Cell, ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ W)
    (hconv : IsUniformlyConvexDecaying ρ (x * lam / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K)
    {M : ℕ} {H : Fin M → BondField ι → ℝ} {Z : Fin M → F.Cell} {h : Fin M → ℝ}
    {Cq : Fin M → ℕ → ℝ} (hM : 2 ≤ M) (hC : ∀ i, ContDiffOn ℝ 1 (H i) {η | ∀ b, ‖η b‖ < ρ})
    (hh : ∀ i, 0 ≤ h i) (hq : ∀ i q, 0 ≤ Cq i q)
    (hsize : ∀ i, Interpolation.HasLocalSize ρ (cutoffFactor ρ p) Ψ (Cq i) x κ (h i)
      (fun b => (cellSupDist (y b) (Z i) : ℝ)) (H i)) :
    |cumulantFromMoments (cutoffFactor ρ p) Ψ H| ≤
      (partitionWeightSum M * (4 / lam * (M : ℝ) ^ 4 * W ^ 2)) *
        (∏ i, (sizeConstantSum (Cq i) M * h i)) *
          Real.exp (-(κ * ConvexObservables.cellsDiameter Z / ((M : ℝ) - 1))) := by
  have hΨ : Continuous Ψ := hconv.smooth.continuous
  obtain ⟨hprob, hmean, hiff, hae, -, -, -, -, -, -, -⟩ := hLaw ι ρ p Ψ hρ hcut hΨ
  set r := cutoffFactor ρ p with hr
  set ν := ConvexObservables.normalizedBallLaw r Ψ with hν
  set O : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hOdef
  have hOo : IsOpen O := by
    have : O = ⋂ b, {η | ‖η b‖ < ρ} := by
      ext η
      simp [hOdef]
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hae' : ∀ᵐ η ∂ν, η ∈ O := hae
  have haes : ∀ {φ : BondField ι → ℝ}, ContinuousOn φ O → AEStronglyMeasurable φ ν := by
    intro φ hφ
    classical
    have hm' : Measurable (O.indicator φ) := by
      rw [← Set.piecewise_eq_indicator]
      exact ContinuousOn.measurable_piecewise hφ continuous_const.continuousOn hOo.measurableSet
    refine hm'.aestronglyMeasurable.congr ?_
    filter_upwards [hae'] with η hη
    exact Set.indicator_of_mem hη φ
  have hsz := fun i => (hsize i).2
  choose H₀ hH₀ using hsz
  set G : Fin M → BondField ι → ℝ := fun i η => H i η - H₀ i with hGdef
  have hG : ∀ i, ContDiffOn ℝ 1 (G i) O := fun i => (hC i).sub contDiffOn_const
  set c : Fin M → ℝ := fun i => sizeConstantSum (Cq i) M with hc
  set a : Fin M → ℝ := fun i => c i * h i with hadef
  have hCq : ∀ i q, q ≤ 2 * M → Cq i q ≤ c i := by
    intro i q hqM
    have h1 : Cq i q ≤ ∑ q ∈ range (2 * M + 1), Cq i q :=
      single_le_sum (f := Cq i) (fun q _ => hq i q) (mem_range.mpr (by omega))
    simp only [hc, sizeConstantSum]
    linarith
  have hc1 : ∀ i, 1 ≤ c i := by
    intro i
    have h1 : 0 ≤ ∑ q ∈ range (2 * M + 1), Cq i q := sum_nonneg fun q _ => hq i q
    simp only [hc, sizeConstantSum]
    linarith
  have ha : ∀ i, 0 ≤ a i := fun i => mul_nonneg (by linarith [hc1 i]) (hh i)
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hGm : ∀ i, HasAllMoments ν (G i) := by
    intro i
    refine ⟨haes (hG i).continuousOn, fun q => ?_⟩
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp
    · exact (hiff _).mpr (hH₀ i q hq1).1.1
  have hPm : ∀ b i, HasAllMoments ν (bondGradNorm (G i) b) := by
    intro b i
    have e : bondGradNorm (G i) b = bondGradNorm (H i) b := bondGradNorm_sub_const (H i) (H₀ i) b
    refine ⟨haes (continuousOn_bondGradNorm hOo (hG i) b), fun q => ?_⟩
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp
    · rw [e]
      exact (hiff _).mpr ((hH₀ i q hq1).2 b).1
  have hval : ∀ i q, 1 ≤ q → q ≤ 2 * M → ∫ η, |G i η| ^ q ∂ν ≤ a i ^ q := by
    intro i q hq1 hq2
    rw [hmean]
    refine (hH₀ i q hq1).1.2.trans (pow_le_pow_left₀ (mul_nonneg (hq i q) (hh i)) ?_ q)
    exact mul_le_mul_of_nonneg_right (hCq i q hq2) (hh i)
  have hgr : ∀ b i q, 1 ≤ q → q ≤ 2 * M → ∫ η, |bondGradNorm (G i) b η| ^ q ∂ν ≤
      (a i * Real.sqrt x * Real.exp (-(2 * κ * (cellSupDist (y b) (Z i) : ℝ)))) ^ q := by
    intro b i q hq1 hq2
    have e : bondGradNorm (G i) b = bondGradNorm (H i) b := bondGradNorm_sub_const (H i) (H₀ i) b
    rw [hmean, e]
    refine ((hH₀ i q hq1).2 b).2.trans (pow_le_pow_left₀ ?_ ?_ q)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hq i q) hsx) (hh i)) (Real.exp_pos _).le
    · have h1 : Cq i q * Real.sqrt x * h i ≤ a i * Real.sqrt x := by
        have := mul_le_mul_of_nonneg_right (hCq i q hq2) (mul_nonneg hsx (hh i))
        simp only [hadef]
        nlinarith
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hHm : ∀ l, HasAllMoments ν (H l) := by
    intro l
    have h1 := (hGm l).add (HasAllMoments.const (ν := ν) (H₀ l))
    have e : (fun ω => G l ω + H₀ l) = H l := by
      funext ω
      simp [hGdef]
    rwa [e] at h1
  set Hs : Finset (Fin M) → Fin M → BondField ι → ℝ :=
    fun T l => if l ∈ T then G l else H l with hHs
  have hHsm : ∀ T l, HasAllMoments ν (Hs T l) := by
    intro T l
    by_cases hl : l ∈ T
    · simp only [hHs, if_pos hl]
      exact hGm l
    · simp only [hHs, if_neg hl]
      exact hHm l
  set moT : Finset (Fin M) → Finset (Fin M) → ℝ :=
    fun T J => ∫ η, ∏ l ∈ J, Hs T l η ∂ν with hmoT
  have hshift : ∀ T, jointCumulantSum (moT ∅) = jointCumulantSum (moT T) := by
    intro T
    induction T using Finset.induction_on with
    | empty => rfl
    | insert i T hi ih =>
      rw [ih]
      have hsame : ∀ l, l ≠ i → Hs T l = Hs (insert i T) l := by
        intro l hl
        simp only [hHs, mem_insert, hl, false_or]
      refine hShift M i (moT T) (moT (insert i T)) (H₀ i) hM ?_ ?_ ?_
      · simp [hmoT]
      · intro J hJ
        simp only [hmoT]
        apply integral_congr_ae
        filter_upwards with η
        apply prod_congr rfl
        intro l hl
        rw [hsame l fun h => hJ (h ▸ hl)]
      · intro J hJ
        simp only [hmoT]
        have hPm' : HasAllMoments ν fun η => ∏ l ∈ J.erase i, Hs (insert i T) l η :=
          HasAllMoments.prod _ fun l _ => hHsm _ l
        have e1 : ∀ η, ∏ l ∈ J, Hs T l η =
            G i η * ∏ l ∈ J.erase i, Hs (insert i T) l η +
              H₀ i * ∏ l ∈ J.erase i, Hs (insert i T) l η := by
          intro η
          rw [← mul_prod_erase J _ hJ]
          have e2 : ∏ l ∈ J.erase i, Hs T l η = ∏ l ∈ J.erase i, Hs (insert i T) l η := by
            apply prod_congr rfl
            intro l hl
            rw [hsame l (mem_erase.mp hl).1]
          have e3 : Hs T i η = G i η + H₀ i := by
            simp only [hHs, if_neg hi, hGdef]
            ring
          rw [e2, e3]
          ring
        have e4 : ∀ η, ∏ l ∈ J, Hs (insert i T) l η =
            G i η * ∏ l ∈ J.erase i, Hs (insert i T) l η := by
          intro η
          rw [← mul_prod_erase J _ hJ]
          simp only [hHs, mem_insert_self, if_true]
        simp only [e1, e4]
        rw [integral_add ((hGm i).mul hPm').integrable (hPm'.integrable.const_mul _),
          integral_const_mul]
  set mo : Finset (Fin M) → ℝ := fun J => ∫ η, ∏ l ∈ J, G l η ∂ν with hmo
  have hcum : cumulantFromMoments r Ψ H = jointCumulantSum mo := by
    have h1 : cumulantFromMoments r Ψ H = jointCumulantSum (moT ∅) := by
      unfold cumulantFromMoments jointCumulantSum
      apply sum_congr rfl
      intro π _
      congr 1
      apply prod_congr rfl
      intro J _
      simp only [hmoT, hHs, notMem_empty, if_false]
      rw [hmean]
    have h2 : moT univ = mo := by
      funext J
      simp only [hmoT, hHs, mem_univ, if_true, hmo]
    rw [h1, hshift univ, h2]
  have hmo0 : mo ∅ = 1 := by simp [hmo]
  have hbound : ∀ U, |mo U| ≤ ∏ l ∈ U, a l := by
    intro U
    have hcard : U.card ≤ M := by
      simpa using card_le_univ U
    have h1 := integral_prod_abs_le_prod (ν := ν) U G a (fun i _ => ha i)
      (fun i _ => (hGm i).integrable_pow _)
      ((HasAllMoments.prod U fun l _ => (hGm l).abs).integrable)
      (fun i hi => hval i _ (card_pos.mpr ⟨i, hi⟩) (by omega))
    refine (abs_integral_le_integral_abs).trans ?_
    simp only [abs_prod]
    exact h1
  have hne : (univ : Finset (Fin M)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ := exists_mem_eq_sup univ hne
    (fun i => univ.sup fun j => cellSupDist (Z i) (Z j))
  obtain ⟨j₀, -, hj₀⟩ := exists_mem_eq_sup univ hne (fun j => cellSupDist (Z i₀) (Z j))
  have hdiam : ConvexObservables.cellsDiameter Z = cellSupDist (Z i₀) (Z j₀) := by
    unfold ConvexObservables.cellsDiameter
    rw [hi₀, hj₀]
  obtain ⟨A, hA, hA', hAgap⟩ := hGap M F.Cell (fun z z' => (cellSupDist z z' : ℝ)) Z i₀ j₀ hM
    (fun z => by simp [cellSupDist_self]) (fun z z' => by rw [cellSupDist_comm])
    (fun z z' z'' => cellSupDist_triangle_real z z' z'')
  set ell : ℝ := (cellSupDist (Z i₀) (Z j₀) : ℝ) / ((M : ℝ) - 1) with hell
  set cc : ℝ := 4 / lam * (M : ℝ) ^ 4 * W ^ 2 with hcc
  have hcc0 : 0 ≤ cc := by positivity
  set ε : ℝ := cc * Real.exp (-(κ * ell)) with hε
  have hε0 : 0 ≤ ε := mul_nonneg hcc0 (Real.exp_pos _).le
  have hm : 0 < x * lam / 4 := by positivity
  have hdist : IsPseudoMetricOnBonds fun b b' : ι => (cellSupDist (y b) (y b') : ℝ) :=
    ⟨fun b => by simp [cellSupDist_self], fun b b' => by rw [cellSupDist_comm],
      fun b b' b'' => cellSupDist_triangle_real _ _ _⟩
  have hnear : ∀ J, |mo J - mo (J ∩ A) * mo (J \ A)| ≤ ε * ∏ l ∈ J, a l := by
    intro J
    set U := J ∩ A with hU
    set V := J \ A with hV
    have hUc : U.card ≤ M := by simpa using card_le_univ U
    have hVc : V.card ≤ M := by simpa using card_le_univ V
    have hgU := fun b => ballL2Norm_bondGradNorm_prod_le hOo hae' hmean haes G hG hGm b (hPm b) a ha
      (Real.sqrt x) hsx
      (fun i => Real.exp (-(2 * κ * (cellSupDist (y b) (Z i) : ℝ)))) (fun _ => (Real.exp_pos _).le) U
      (fun i hi => hval i _ (by have := card_pos.mpr ⟨i, hi⟩; omega) (by omega))
      (fun i hi => hgr b i _ (by have := card_pos.mpr ⟨i, hi⟩; omega) (by omega))
    have hgV := fun b => ballL2Norm_bondGradNorm_prod_le hOo hae' hmean haes G hG hGm b (hPm b) a ha
      (Real.sqrt x) hsx
      (fun i => Real.exp (-(2 * κ * (cellSupDist (y b) (Z i) : ℝ)))) (fun _ => (Real.exp_pos _).le) V
      (fun i hi => hval i _ (by have := card_pos.mpr ⟨i, hi⟩; omega) (by omega))
      (fun i hi => hgr b i _ (by have := card_pos.mpr ⟨i, hi⟩; omega) (by omega))
    have hcov := hCov ι ρ (x * lam / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K p hρ hm hκ.le
      hcut hdist hconv (fun ζ => ∏ i ∈ U, G i ζ) (fun ζ => ∏ i ∈ V, G i ζ)
      (contDiffOn_prod_family G hG U) (contDiffOn_prod_family G hG V)
      (HasAllMoments.prod U fun i _ => hGm i).integrable_sq
      (HasAllMoments.prod V fun i _ => hGm i).integrable_sq
      (fun b => (hgU b).1) (fun b => (hgV b).1)
    set DU := ∏ i ∈ U, a i with hDU
    set DV := ∏ i ∈ V, a i with hDV
    have hDU0 : 0 ≤ DU := prod_nonneg fun i _ => ha i
    have hDV0 : 0 ≤ DV := prod_nonneg fun i _ => ha i
    have hgap := bondDoubleSum_le_of_gap κ ell W ((U.card : ℝ) * DU * Real.sqrt x)
      ((V.card : ℝ) * DV * Real.sqrt x) hκ
      (by positivity) (by positivity) hW0 (fun b b' : ι => (cellSupDist (y b) (y b') : ℝ))
      (fun i b => (cellSupDist (y b) (Z i) : ℝ)) U V
      (fun b => ballL2Norm r Ψ (bondGradNorm (fun ζ => ∏ i ∈ U, G i ζ) b))
      (fun b => ballL2Norm r Ψ (bondGradNorm (fun ζ => ∏ i ∈ V, G i ζ) b))
      (fun b => Real.sqrt_nonneg _) (fun b => Real.sqrt_nonneg _)
      (fun b => (hgU b).2) (fun b => (hgV b).2)
      (by
        intro i hi j hj b b'
        have hiA : i ∈ A := (mem_inter.mp hi).2
        have hjA : j ∉ A := (mem_sdiff.mp hj).2
        have h1 : ell ≤ (cellSupDist (Z i) (Z j) : ℝ) := hAgap i hiA j hjA
        have h2 := cellSupDist_triangle_real (Z i) (y b) (Z j)
        have h3 := cellSupDist_triangle_real (y b) (y b') (Z j)
        rw [cellSupDist_comm (Z i) (y b)] at h2
        linarith)
      (fun i b => Nat.cast_nonneg _)
      (fun i => hWs (Z i))
    have hdiff : mo J - mo U * mo V =
        ballCovariance r Ψ (fun ζ => ∏ i ∈ U, G i ζ) (fun ζ => ∏ i ∈ V, G i ζ) := by
      unfold ballCovariance
      rw [← hmean, ← hmean, ← hmean]
      simp only [hmo]
      congr 2
      funext η
      exact (prod_inter_mul_prod_sdiff J A _).symm
    rw [hdiff]
    refine hcov.trans ?_
    have hsplit : DU * DV = ∏ l ∈ J, a l := prod_inter_mul_prod_sdiff J A a
    have hJ0 : 0 ≤ ∏ l ∈ J, a l := prod_nonneg fun i _ => ha i
    have hminv : 0 ≤ (x * lam / 4)⁻¹ := (inv_pos.mpr hm).le
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
    have hE : 0 ≤ Real.exp (-(κ * ell)) := (Real.exp_pos _).le
    have hUM : ((U.card : ℝ)) ≤ M := by exact_mod_cast hUc
    have hVM : ((V.card : ℝ)) ≤ M := by exact_mod_cast hVc
    have hcount : (U.card : ℝ) ^ 2 * (V.card : ℝ) ^ 2 ≤ (M : ℝ) ^ 4 := by
      have h1 : (U.card : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hUM 2
      have h2 : (V.card : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hVM 2
      calc (U.card : ℝ) ^ 2 * (V.card : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 * (M : ℝ) ^ 2 :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (M : ℝ) ^ 4 := by ring
    calc (x * lam / 4)⁻¹ * ∑ b, ∑ b',
          ballL2Norm r Ψ (bondGradNorm (fun ζ => ∏ i ∈ U, G i ζ) b) *
            Real.exp (-(κ * (cellSupDist (y b) (y b') : ℝ))) *
          ballL2Norm r Ψ (bondGradNorm (fun ζ => ∏ i ∈ V, G i ζ) b')
        ≤ (x * lam / 4)⁻¹ * ((U.card : ℝ) * DU * Real.sqrt x * ((V.card : ℝ) * DV * Real.sqrt x) *
            ((U.card : ℝ) * W) * ((V.card : ℝ) * W) * Real.exp (-(κ * ell))) :=
          mul_le_mul_of_nonneg_left hgap hminv
      _ = 4 / lam * ((U.card : ℝ) ^ 2 * (V.card : ℝ) ^ 2) * W ^ 2 * Real.exp (-(κ * ell)) *
            (DU * DV) := by
          have hx' : x ≠ 0 := hx.ne'
          have hl' : lam ≠ 0 := hlam.ne'
          calc (x * lam / 4)⁻¹ * ((U.card : ℝ) * DU * Real.sqrt x * ((V.card : ℝ) * DV * Real.sqrt x) *
                ((U.card : ℝ) * W) * ((V.card : ℝ) * W) * Real.exp (-(κ * ell)))
              = (x * lam / 4)⁻¹ * (Real.sqrt x * Real.sqrt x) * ((U.card : ℝ) * DU * ((V.card : ℝ) * DV) *
                ((U.card : ℝ) * W) * ((V.card : ℝ) * W) * Real.exp (-(κ * ell))) := by ring
            _ = _ := by
                rw [hxx]
                field_simp
      _ ≤ 4 / lam * (M : ℝ) ^ 4 * W ^ 2 * Real.exp (-(κ * ell)) * (DU * DV) := by
          have h4 : 0 ≤ W ^ 2 * Real.exp (-(κ * ell)) * (DU * DV) := by positivity
          have h5 : 0 ≤ 4 / lam := by positivity
          calc 4 / lam * ((U.card : ℝ) ^ 2 * (V.card : ℝ) ^ 2) * W ^ 2 * Real.exp (-(κ * ell)) * (DU * DV)
              = 4 / lam * (((U.card : ℝ) ^ 2 * (V.card : ℝ) ^ 2) *
                  (W ^ 2 * Real.exp (-(κ * ell)) * (DU * DV))) := by ring
            _ ≤ 4 / lam * ((M : ℝ) ^ 4 * (W ^ 2 * Real.exp (-(κ * ell)) * (DU * DV))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount h4) h5
            _ = _ := by ring
      _ = ε * ∏ l ∈ J, a l := by
          rw [hsplit, hε, hcc]
  have hfinal := hAcross M A mo a ε hA hA' hmo0 ha hε0 hbound hnear
  rw [hcum]
  refine hfinal.trans (le_of_eq ?_)
  rw [hε, hdiam]
  have : κ * (cellSupDist (Z i₀) (Z j₀) : ℝ) / ((M : ℝ) - 1) = κ * ell := by
    rw [hell]
    ring
  rw [this]
  ring
theorem cumulantDecayBound_holds (hCov : ConvexObservables.covarianceOpenBallsStatement)
    (hShift : CumulantShiftInvariant)
    (hAcross : CumulantSmallAcrossGap) (hGap : FiniteMetricGap.ExistsGapAmongFinitePoints)
    (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement)
    (hWt : CellCounting.ExpDecaySumBounded) :
    cumulantDecayBound := by
  intro N κ lam hκ hlam
  obtain ⟨W, hW0, hW⟩ := hWt N κ hκ
  set t : ℕ → ℝ := fun M => partitionWeightSum M * (4 / lam * (M : ℝ) ^ 4 * W ^ 2) with ht
  have hpc : ∀ M, 0 ≤ partitionWeightSum M := fun M =>
    sum_nonneg fun π _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have ht0 : ∀ M, 0 ≤ t M := fun M => mul_nonneg (hpc M) (by positivity)
  refine ⟨∑ M ∈ range 10, t M, sum_nonneg fun M _ => ht0 M, ?_⟩
  intro F ι _ _ y ρ x p Ψ K hρ hx hcut hN hconv hslope M H Z h Cq hM hM9 hC hh hq hsize
  have hb := abs_cumulant_le_of_order hCov hShift hAcross hGap hLaw hκ hlam hW0 hρ hx hcut
    (hW F ι y hN) hconv hM hC hh hq hsize
  have hle : t M ≤ ∑ M ∈ range 10, t M :=
    single_le_sum (f := t) (fun M _ => ht0 M) (mem_range.mpr (by omega))
  have hP0 : 0 ≤ ∏ i, (sizeConstantSum (Cq i) M * h i) := by
    apply prod_nonneg
    intro i _
    have h1 : 0 ≤ ∑ q ∈ range (2 * M + 1), Cq i q := sum_nonneg fun q _ => hq i q
    exact mul_nonneg (by simp only [sizeConstantSum]; linarith) (hh i)
  have h1 : |cumulantFromMoments (cutoffFactor ρ p) Ψ H| ≤
      (∑ M ∈ range 10, t M) * (∏ i, (sizeConstantSum (Cq i) M * h i)) *
        Real.exp (-(κ * ConvexObservables.cellsDiameter Z / ((M : ℝ) - 1))) := by
    refine hb.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hP0) (Real.exp_pos _).le
  refine ⟨h1, h1.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sum_nonneg fun M _ => ht0 M) hP0)
  apply Real.exp_le_exp.mpr
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hM8 : (M : ℝ) - 1 ≤ 8 := by
    have : (M : ℝ) ≤ 9 := by exact_mod_cast hM9
    linarith
  have hd : (0 : ℝ) ≤ ConvexObservables.cellsDiameter Z := Nat.cast_nonneg _
  have h2 : κ / 8 * ConvexObservables.cellsDiameter Z ≤
      κ * ConvexObservables.cellsDiameter Z / ((M : ℝ) - 1) := by
    rw [le_div_iff₀ hM1]
    have := mul_nonneg hκ.le hd
    nlinarith
  linarith
end Bound
end YangMills.Construction.Cumulants
end
