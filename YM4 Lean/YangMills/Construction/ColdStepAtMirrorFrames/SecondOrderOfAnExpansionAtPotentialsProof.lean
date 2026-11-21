import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstTwoFlatResponses
import Mathlib
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocalProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def SecondOrderAxialBound : Prop :=
  ∃ L₀ : ℕ, ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
    (X₀ X₁ : imaginaryQuaternions) (y : F.Site F.depth) (Fm Fm' : Fin 4 → Fin 4 → ℝ),
    L₀ ≤ L → Odd L → 0 < σ → 0 ≤ δ → 0 ≤ E → IsRegularFamily L t n₀ σ δ E E₃ f →
    IsCubicTorusAbove L t n₀ F →
    (∀ i, 2 * L ^ 2 + 2 < F.period F.depth i) → ‖X₀‖ = 1 → ‖X₁‖ = 1 →
    (∀ μ ν, Fm μ ν = - Fm ν μ) → (∀ μ ν, Fm' μ ν = - Fm' ν μ) →
    |∑ b ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
      ∑ b' ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
        bondDeriv (f F y) (uniformField F F.depth) ![b, b'] ![X₀, X₁] *
          axialGaugePotential y Fm b.1 b.2 * axialGaugePotential y Fm' b'.1 b'.2| ≤
      (F.blockSide : ℝ) ^ (-(7000 : ℝ)) * E * (∑ μ, ∑ ν, |Fm μ ν|) * ∑ μ, ∑ ν, |Fm' μ ν|
end ColdStepAtMirrorFrames
end YangMills.Construction
end

noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open BlockOffsets
namespace AxialSecondOrder
def intSize (k : ℤ) : ℝ := max 1 |(k : ℝ)|
def inverseSquareWeight (k : ℤ) : ℝ := (intSize k ^ 2)⁻¹
def bondWeight (p : (Fin 4 → ℤ) × Fin 4) : ℝ := ∏ i, inverseSquareWeight (p.1 i)
theorem one_le_intSize (k : ℤ) : 1 ≤ intSize k := le_max_left _ _
theorem inverseSquareWeight_nonneg (k : ℤ) : 0 ≤ inverseSquareWeight k := inv_nonneg.2 (sq_nonneg _)
theorem summable_inverseSquareWeight : Summable inverseSquareWeight := by
  have hs : Summable fun n : ℕ => inverseSquareWeight (n : ℤ) := by
    refine (summable_nat_add_iff 1).1 ?_
    have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    refine h.congr fun n => ?_
    have e : intSize ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℝ) := by
      unfold intSize
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact max_eq_right (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    simp only [inverseSquareWeight, e, one_div]
  have hn : Summable fun n : ℕ => inverseSquareWeight (-(n : ℤ)) := by
    refine hs.congr fun n => ?_
    simp [inverseSquareWeight, intSize]
  exact Summable.of_nat_of_neg hs hn
theorem sum_bondWeight_le (D : Finset ((Fin 4 → ℤ) × Fin 4)) :
    ∑ p ∈ D, bondWeight p ≤ 4 * (∑' k, inverseSquareWeight k) ^ 4 := by
  classical
  set I : Finset ℤ := D.biUnion fun p => Finset.univ.image p.1 with hI
  have hsub : D ⊆ (Fintype.piFinset fun _ : Fin 4 => I) ×ˢ Finset.univ := by
    intro p hp
    refine Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, Finset.mem_univ _⟩
    exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  have h0 : ∀ p, 0 ≤ bondWeight p := fun p => Finset.prod_nonneg fun i _ => inverseSquareWeight_nonneg _
  have hI0 : 0 ≤ ∑ k ∈ I, inverseSquareWeight k := Finset.sum_nonneg fun k _ => inverseSquareWeight_nonneg k
  have hIK : ∑ k ∈ I, inverseSquareWeight k ≤ ∑' k, inverseSquareWeight k :=
    summable_inverseSquareWeight.sum_le_tsum I fun k _ => inverseSquareWeight_nonneg k
  calc ∑ p ∈ D, bondWeight p ≤ ∑ p ∈ (Fintype.piFinset fun _ : Fin 4 => I) ×ˢ Finset.univ, bondWeight p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => h0 p
    _ = 4 * ∏ _i : Fin 4, ∑ k ∈ I, inverseSquareWeight k := by
        rw [Finset.sum_product, Finset.prod_univ_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [bondWeight]
    _ ≤ 4 * (∑' k, inverseSquareWeight k) ^ 4 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI0 hIK 4) (by norm_num)
theorem abs_finset_sum_le_of_hasSum_zero {ι : Type} (f : ι → ℝ) (hf : HasSum f 0) (S : Finset ι) (M : ℝ)
    (h : ∀ D : Finset ι, Disjoint D S → ∑ p ∈ D, |f p| ≤ M) : |∑ p ∈ S, f p| ≤ M := by
  classical
  have hlim : Filter.Tendsto (fun T : Finset ι => |∑ p ∈ T, f p| + M) Filter.atTop (𝓝 (|(0 : ℝ)| + M)) :=
    (hf.abs.add tendsto_const_nhds)
  rw [abs_zero, zero_add] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop S] with T hT
  have e : ∑ p ∈ T, f p = ∑ p ∈ S, f p + ∑ p ∈ T \ S, f p := by
    rw [add_comm, Finset.sum_sdiff hT]
  have h1 : |∑ p ∈ T \ S, f p| ≤ M :=
    (Finset.abs_sum_le_sum_abs _ _).trans (h _ Finset.sdiff_disjoint)
  have h2 : ∑ p ∈ S, f p = ∑ p ∈ T, f p - ∑ p ∈ T \ S, f p := by
    rw [e]
    ring
  rw [h2]
  exact (abs_sub _ _).trans (by linarith)
theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem torusDecayFactor_mono {L : ℕ} {δ x x' : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (h : x ≤ x') :
    torusDecayFactor L δ x ≤ torusDecayFactor L δ x' := by
  unfold torusDecayFactor
  have hn : 0 < (L : ℝ) ^ (1 / 640 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (lt_of_lt_of_le one_pos (le_max_left _ _)).le
  · refine max_le_max le_rfl (pow_le_pow_left₀ (by positivity) ?_ _)
    exact div_le_div_of_nonneg_right h hn.le
  · exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hδ)
theorem inv_torusDecayFactor_le {L : ℕ} {δ x : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hx : 0 < x) :
    (torusDecayFactor L δ x)⁻¹ ≤ (L : ℝ) ^ 25 / x ^ 16000 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have e : (x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 = x ^ 16000 / (L : ℝ) ^ 25 := by
    rw [div_pow, ← Real.rpow_natCast ((L : ℝ) ^ (1 / 640 : ℝ)) 16000, ← Real.rpow_mul hLr.le]
    norm_num
  have h1 : x ^ 16000 / (L : ℝ) ^ 25 ≤ torusDecayFactor L δ x := by
    unfold torusDecayFactor
    rw [← e]
    have h2 : 1 ≤ Real.exp (δ * x) := Real.one_le_exp (by positivity)
    have h3 : (x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 ≤ max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_right _ _
    calc (x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000 ≤ max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := h3
      _ ≤ _ := le_mul_of_one_le_right (lt_of_lt_of_le one_pos (le_max_left _ _)).le h2
  have hp : 0 < x ^ 16000 / (L : ℝ) ^ 25 := by positivity
  calc (torusDecayFactor L δ x)⁻¹ ≤ (x ^ 16000 / (L : ℝ) ^ 25)⁻¹ := inv_anti₀ hp h1
    _ = (L : ℝ) ^ 25 / x ^ 16000 := by rw [inv_div]
variable {F : BlockFrame}
def supNorm (h : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (h i).natAbs
theorem natAbs_le_supNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ supNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem abs_le_supNorm (h : Fin 4 → ℤ) (i : Fin 4) : |(h i : ℝ)| ≤ supNorm h := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
def linearPotential (Fm : Fin 4 → Fin 4 → ℝ) (p : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  ∑ l : Fin 4, if p.2 < l then (p.1 l : ℝ) * Fm l p.2 else 0
def curvatureNorm (Fm : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ μ, ∑ ν, |Fm μ ν|
theorem curvatureNorm_nonneg (Fm : Fin 4 → Fin 4 → ℝ) : 0 ≤ curvatureNorm Fm :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem abs_linearPotential_le (Fm : Fin 4 → Fin 4 → ℝ) (p : (Fin 4 → ℤ) × Fin 4) :
    |linearPotential Fm p| ≤ supNorm p.1 * curvatureNorm Fm := by
  have h1 : |linearPotential Fm p| ≤ ∑ l, (supNorm p.1 : ℝ) * |Fm l p.2| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_le_supNorm _ _) (abs_nonneg _)
    · rw [abs_zero]
      positivity
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  unfold curvatureNorm
  exact Finset.sum_le_sum fun l _ =>
    Finset.single_le_sum (f := fun ν => |Fm l ν|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.2)
theorem isAntisymmetricCurvature_smul (Fm : Fin 4 → Fin 4 → ℝ) (hFm : ∀ μ ν, Fm μ ν = - Fm ν μ)
    (X : imaginaryQuaternions) :
    IsAntisymmetricCurvature fun μ ν => Fm μ ν • X := by
  intro μ ν
  show Fm μ ν • X = - (Fm ν μ • X)
  rw [hFm μ ν]
  apply Subtype.ext
  simp
theorem isLinearPotential_smul (Fm : Fin 4 → Fin 4 → ℝ) (hFm : ∀ μ ν, Fm μ ν = - Fm ν μ)
    (X : imaginaryQuaternions) :
    IsLinearPotential (fun μ ν => Fm μ ν • X) (fun p => linearPotential Fm p • X) := by
  refine ⟨fun μ ν => if μ < ν then Fm ν μ • X else 0, fun _ => 0, ?_, ?_⟩
  · intro x μ
    simp only [linearPotential, add_zero, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [mul_smul]
    · simp
  · intro μ ν
    rcases lt_trichotomy μ ν with h | h | h
    · have h' : ¬ ν < μ := not_lt.2 h.le
      simp only [if_neg h', if_pos h, zero_sub]
      rw [hFm μ ν]
      apply Subtype.ext
      simp
    · subst h
      have h0 : Fm μ μ = 0 := by linarith [hFm μ μ]
      simp [h0]
    · have h' : ¬ μ < ν := not_lt.2 h.le
      simp only [if_neg h', if_pos h, sub_zero]
theorem inv_pow_eight_le_bondWeight (p : (Fin 4 → ℤ) × Fin 4) (m : ℝ) (hm : 1 ≤ m) (hh : (supNorm p.1 : ℝ) ≤ m) :
    (m ^ 8)⁻¹ ≤ bondWeight p := by
  have h1 : ∀ i, (m ^ 2)⁻¹ ≤ inverseSquareWeight (p.1 i) := by
    intro i
    have hub : intSize (p.1 i) ≤ m := max_le hm ((abs_le_supNorm _ _).trans hh)
    have hpos : 0 < intSize (p.1 i) ^ 2 := by
      have := one_le_intSize (p.1 i)
      positivity
    exact inv_anti₀ hpos (pow_le_pow_left₀ (by linarith [one_le_intSize (p.1 i)]) hub 2)
  have e : (m ^ 8)⁻¹ = ∏ _i : Fin 4, (m ^ 2)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, ← pow_mul]
  rw [e]
  exact Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => h1 i
theorem uniformField_isSmallCurvature {j : ℕ} {σ : ℝ} (hσ : 0 < σ) : IsSmallCurvature σ (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
theorem bondDeriv_subtractTrivial (f : LocalFamily) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (c : Fin 2 → F.Site F.depth × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (hs : ContDiffAt ℝ 3 (fun τ : Fin 2 → ℝ => f F y (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (subtractTrivial f F y) W c X = bondDeriv (f F y) W c X := by
  unfold bondDeriv subtractTrivial
  have h := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := 2)
    (f := fun τ : Fin 2 → ℝ => f F y (leftTranslate (bondSpread c X τ) W))
    (g := fun _ => f F y (uniformField F F.depth)) (x := 0) (hs.of_le (by norm_num)) contDiffAt_const
  have e : (fun τ : Fin 2 → ℝ => f F y (leftTranslate (bondSpread c X τ) W) - f F y (uniformField F F.depth)) =
      (fun τ : Fin 2 → ℝ => f F y (leftTranslate (bondSpread c X τ) W)) - fun _ => f F y (uniformField F F.depth) := rfl
  rw [e, h, iteratedFDeriv_const_of_ne (by norm_num)]
  simp
theorem bondDeriv_smul_smul (hJ : FormCompositionJet) {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (hG : ContDiffThreeAlongBonds G W) (b b' : F.Site j × Fin 4) (X X' : imaginaryQuaternions) (r s : ℝ) :
    bondDeriv G W ![b, b'] ![r • X, s • X'] = r * s * bondDeriv G W ![b, b'] ![X, X'] := by
  classical
  set B : Finset (F.Site j × Fin 4) := {b, b'} with hB
  obtain ⟨-, he, -⟩ := hJ ℝ F j B G W hG
  have hb : b ∈ B := by simp [hB]
  have hb' : b' ∈ B := by simp [hB]
  have e1 := he 2 ![⟨b, hb⟩, ⟨b', hb'⟩] ![r • X, s • X'] (by norm_num)
  have e2 := he 2 ![⟨b, hb⟩, ⟨b', hb'⟩] ![X, X'] (by norm_num)
  have e3 : (fun l => ((![⟨b, hb⟩, ⟨b', hb'⟩] : Fin 2 → ↥B) l).1) = ![b, b'] := by
    funext l
    fin_cases l <;> rfl
  rw [e3] at e1 e2
  rw [← e1, ← e2]
  have e4 : (fun l => singleBondForm ((![⟨b, hb⟩, ⟨b', hb'⟩] : Fin 2 → ↥B) l)
        ((![r • X, s • X'] : Fin 2 → imaginaryQuaternions) l)) =
      fun l => (![r, s] : Fin 2 → ℝ) l • singleBondForm ((![⟨b, hb⟩, ⟨b', hb'⟩] : Fin 2 → ↥B) l)
        ((![X, X'] : Fin 2 → imaginaryQuaternions) l) := by
    funext l
    fin_cases l <;> simp [singleBondForm, Pi.single_smul]
  rw [e4, ContinuousMultilinearMap.map_smul_univ, Fin.prod_univ_two]
  simp
theorem siteOffset_add_siteOfCoords {j : ℕ} (y : F.Site j) (h : Fin 4 → ℤ)
    (hh : ∀ i, 2 * |h i| < (F.period j i : ℤ)) :
    siteOffset y (y + siteOfCoords j h) = h := by
  funext i
  unfold siteOffset
  rw [add_sub_cancel_left]
  exact valMinAbs_intCast_of_small (Or.inr (hh i))
theorem siteSupDist_add_left {j : ℕ} (y : F.Site j) (h : Fin 4 → ℤ) (hh : ∀ i, 2 * |h i| < (F.period j i : ℤ)) :
    siteSupDist (y + siteOfCoords j h) y = supNorm h := by
  unfold siteSupDist supNorm
  refine Finset.sup_congr rfl fun i _ => ?_
  have e : (y + siteOfCoords j h : F.Site j) i - y i = ((h i : ℤ) : ZMod (F.period j i)) := by
    simp [siteOfCoords]
  rw [e, valMinAbs_intCast_of_small (Or.inr (hh i))]
theorem siteSupDist_add_right {j : ℕ} (y : F.Site j) (h : Fin 4 → ℤ) (hh : ∀ i, 2 * |h i| < (F.period j i : ℤ)) :
    siteSupDist y (y + siteOfCoords j h) = supNorm h := by
  unfold siteSupDist supNorm
  refine Finset.sup_congr rfl fun i _ => ?_
  have e : y i - (y + siteOfCoords j h : F.Site j) i = ((- h i : ℤ) : ZMod (F.period j i)) := by
    simp [siteOfCoords]
  rw [e, valMinAbs_intCast_of_small (Or.inr (by rw [abs_neg]; exact hh i)), Int.natAbs_neg]
theorem far_term_le {Lr m : ℝ} (hL : 1 ≤ Lr) (hm : 1 ≤ m) (hm2 : Lr ≤ m ^ 2) :
    Lr ^ 25 / m ^ 16000 * (m * m) ≤ Lr ^ 25 / Lr ^ 7500 * ((m ^ 8)⁻¹ * (m ^ 8)⁻¹) := by
  have hLp : 0 < Lr := by linarith
  have e1 : Lr ^ 25 / m ^ 16000 * (m * m) = Lr ^ 25 / m ^ 15998 := by
    have : m ^ 16000 = m ^ 15998 * (m * m) := by
      rw [← pow_two, ← pow_add]
    rw [this, div_mul_eq_mul_div, mul_div_mul_right _ _ (by positivity)]
  have e2 : Lr ^ 25 / Lr ^ 7500 * ((m ^ 8)⁻¹ * (m ^ 8)⁻¹) = Lr ^ 25 / (Lr ^ 7500 * m ^ 16) := by
    have : m ^ 16 = m ^ 8 * m ^ 8 := by
      rw [← pow_add]
    rw [this, ← mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_inv]
  rw [e1, e2]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have h1 : Lr ^ 7500 ≤ m ^ 15000 := by
    calc Lr ^ 7500 ≤ (m ^ 2) ^ 7500 := pow_le_pow_left₀ hLp.le hm2 _
      _ = m ^ 15000 := by rw [← pow_mul]
  have h2 : m ^ 15000 * m ^ 16 ≤ m ^ 15998 := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hm (by norm_num)
  exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2
theorem near_numeric_bound {Lr R c : ℝ} (hL : 209952 ≤ Lr) (hR1 : 1 ≤ R) (hR2 : R ^ 2 ≤ Lr)
    (hc : c = 4 * (2 * R + 1) ^ 4) :
    c * c * (R * R) * (Lr ^ 25 / (Lr ^ 2) ^ 16000) ≤ 1 / 2 * (Lr ^ 7000)⁻¹ := by
  have hL1 : 1 ≤ Lr := by linarith
  have h3 : 2 * R + 1 ≤ 3 * R := by linarith
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hc1 : c ≤ 324 * R ^ 4 := by
    rw [hc]
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 2 * R + 1) h3 4
    nlinarith
  have hR10 : R ^ 10 ≤ Lr ^ 5 := by
    calc R ^ 10 = (R ^ 2) ^ 5 := by rw [← pow_mul]
      _ ≤ Lr ^ 5 := pow_le_pow_left₀ (by positivity) hR2 5
  have hcc : c * c * (R * R) ≤ 104976 * Lr ^ 5 := by
    have h4 : c * c ≤ (324 * R ^ 4) * (324 * R ^ 4) := mul_le_mul hc1 hc1 hc0 (by positivity)
    calc c * c * (R * R) ≤ (324 * R ^ 4) * (324 * R ^ 4) * (R * R) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = 104976 * R ^ 10 := by ring
      _ ≤ 104976 * Lr ^ 5 := by linarith
  have hkey : c * c * (R * R) * Lr ^ 25 * (2 * Lr ^ 7000) ≤ Lr ^ 32000 := by
    calc c * c * (R * R) * Lr ^ 25 * (2 * Lr ^ 7000) ≤ 104976 * Lr ^ 5 * Lr ^ 25 * (2 * Lr ^ 7000) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hcc (by positivity)
      _ = 209952 * Lr ^ 7030 := by ring
      _ ≤ Lr * Lr ^ 7030 := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = Lr ^ 7031 := by ring
      _ ≤ Lr ^ 32000 := pow_le_pow_right₀ hL1 (by norm_num)
  have e1 : (Lr ^ 2) ^ 16000 = Lr ^ 32000 := by rw [← pow_mul]
  rw [e1, ← mul_div_assoc, show (1 : ℝ) / 2 * (Lr ^ 7000)⁻¹ = 1 / (2 * Lr ^ 7000) by
    rw [one_div, one_div, mul_inv], div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact hkey
theorem far_numeric_bound {Lr K : ℝ} (hL : 1 ≤ Lr) (hK : 2 * K ^ 2 ≤ Lr) :
    Lr ^ 25 / Lr ^ 7500 * K ^ 2 ≤ 1 / 2 * (Lr ^ 7000)⁻¹ := by
  have hkey : Lr ^ 25 * K ^ 2 * (2 * Lr ^ 7000) ≤ Lr ^ 7500 := by
    calc Lr ^ 25 * K ^ 2 * (2 * Lr ^ 7000) = Lr ^ 25 * Lr ^ 7000 * (2 * K ^ 2) := by ring
      _ ≤ Lr ^ 25 * Lr ^ 7000 * Lr := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = Lr ^ 7026 := by ring
      _ ≤ Lr ^ 7500 := pow_le_pow_right₀ hL (by norm_num)
  rw [div_mul_eq_mul_div, show (1 : ℝ) / 2 * (Lr ^ 7000)⁻¹ = 1 / (2 * Lr ^ 7000) by
    rw [one_div, one_div, mul_inv], div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact hkey
theorem bondsAt_pair {G : BlockFrame} {j : ℕ} (y : G.Site j) (p p' : (Fin 4 → ℤ) × Fin 4) :
    bondsAt y ![p, p'] = ![(y + siteOfCoords j p.1, p.2), (y + siteOfCoords j p'.1, p'.2)] := by
  funext l
  fin_cases l <;> rfl
theorem two_mul_abs_lt_of_supNorm {per : ℕ} (h : Fin 4 → ℤ) (i : Fin 4) (hp : 2 * supNorm h < per) :
    2 * |h i| < (per : ℤ) := by
  rw [Int.abs_eq_natAbs]
  have := natAbs_le_supNorm h i
  omega
theorem areUnitVectors_pair {X₀ X₁ : imaginaryQuaternions} (hX₀ : ‖X₀‖ = 1) (hX₁ : ‖X₁‖ = 1) :
    AreUnitVectors ![X₀, X₁] := by apply _root_.YangMills.SharedProofs.p1051 <;> assumption
theorem abs_limit_le_decay {L t n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (hrow : IsRegularFamily L t n₀ σ δ E E₃ f)
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hL : 1 ≤ L) (q : BondBilinearForm)
    (hq : ∀ b b' X X', Filter.Tendsto (fun n => hessianAtTrivial f L t n b b' X X') Filter.atTop
      (𝓝 (q b b' X X')))
    (p p' : (Fin 4 → ℤ) × Fin 4) {X₀ X₁ : imaginaryQuaternions} (hX₀ : ‖X₀‖ = 1) (hX₁ : ‖X₁‖ = 1) :
    |q p p' X₀ X₁| ≤ E / torusDecayFactor L δ ((max (supNorm p.1) (supNorm p'.1) : ℕ) : ℝ) := by
  refine le_of_tendsto ((hq p p' X₀ X₁).abs) ?_
  filter_upwards [Filter.eventually_ge_atTop (n₀ + 2 * (supNorm p.1 + supNorm p'.1) + 3)] with n hn
  have hnL : n ≤ n * L := Nat.le_mul_of_pos_right n hL
  have hlow : IsCubicTorusAbove L t n₀ (cubicTorusFrame L t n) := ⟨rfl, rfl, n, fun _ => rfl, by omega⟩
  have hd := hrow.decay _ hlow 0 (uniformField _ _) 2 (bondsAt 0 ![p, p']) ![X₀, X₁]
    (uniformField_isSmallCurvature hσ) (by norm_num) (by norm_num) (areUnitVectors_pair hX₀ hX₁)
  rw [if_neg (by norm_num)] at hd
  refine le_trans hd ?_
  refine div_le_div_of_nonneg_left hE (torusDecayFactor_pos _ _ _)
    (torusDecayFactor_mono hL hδ (Nat.cast_nonneg _) ?_)
  have hper : ∀ i, (cubicTorusFrame L t n).period (cubicTorusFrame L t n).depth i = n * L :=
    fun i => period_depth i
  have h0 : ∀ l : Fin 2, siteSupDist (0 : (cubicTorusFrame L t n).Site (cubicTorusFrame L t n).depth)
      (bondsAt 0 ![p, p'] l).1 ≤ bondSpan 0 (bondsAt 0 ![p, p']) := fun l =>
    le_max_of_le_left (Finset.le_sup (f := fun l => siteSupDist
      (0 : (cubicTorusFrame L t n).Site (cubicTorusFrame L t n).depth)
      (bondsAt 0 ![p, p'] l).1) (Finset.mem_univ l))
  have e0 : siteSupDist (0 : (cubicTorusFrame L t n).Site (cubicTorusFrame L t n).depth)
      (bondsAt 0 ![p, p'] 0).1 = supNorm p.1 :=
    siteSupDist_add_right 0 p.1 fun i => two_mul_abs_lt_of_supNorm _ _ (by rw [hper]; omega)
  have e1 : siteSupDist (0 : (cubicTorusFrame L t n).Site (cubicTorusFrame L t n).depth)
      (bondsAt 0 ![p, p'] 1).1 = supNorm p'.1 :=
    siteSupDist_add_right 0 p'.1 fun i => two_mul_abs_lt_of_supNorm _ _ (by rw [hper]; omega)
  have h1 := h0 0
  have h2 := h0 1
  rw [e0] at h1
  rw [e1] at h2
  exact_mod_cast max_le h1 h2
theorem abs_bondDeriv_sub_limit_le {F : BlockFrame} {n₀ r : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (hrow : IsRegularFamily F.blockSide F.depth n₀ σ δ E E₃ f)
    (hF : IsCubicTorusAbove F.blockSide F.depth n₀ F) (hσ : 0 < σ) (hL : 1 ≤ F.blockSide)
    (q : BondBilinearForm)
    (hq : ∀ b b' X X', Filter.Tendsto (fun n => hessianAtTrivial f F.blockSide F.depth n b b' X X')
      Filter.atTop (𝓝 (q b b' X X')))
    (hper : ∀ i, 2 * r + 2 < F.period F.depth i) (y : F.Site F.depth) (p p' : (Fin 4 → ℤ) × Fin 4)
    (hp : BondWithinRadius r p) (hp' : BondWithinRadius r p') {X₀ X₁ : imaginaryQuaternions}
    (hX₀ : ‖X₀‖ = 1) (hX₁ : ‖X₁‖ = 1) :
    |bondDeriv (f F y) (uniformField F F.depth) (bondsAt y ![p, p']) ![X₀, X₁] - q p p' X₀ X₁| ≤
      E / torusDecayFactor F.blockSide δ r := by
  refine le_of_tendsto ((tendsto_const_nhds.sub (hq p p' X₀ X₁)).abs) ?_
  filter_upwards [Filter.eventually_ge_atTop (n₀ + 2 * r + 3)] with n hn
  have hnL : n ≤ n * F.blockSide := Nat.le_mul_of_pos_right n hL
  have hlow : IsCubicTorusAbove F.blockSide F.depth n₀ (cubicTorusFrame F.blockSide F.depth n) :=
    ⟨rfl, rfl, n, fun _ => rfl, by omega⟩
  have hper' : ∀ i, 2 * r + 2 <
      (cubicTorusFrame F.blockSide F.depth n).period (cubicTorusFrame F.blockSide F.depth n).depth i := by
    intro i
    have : (cubicTorusFrame F.blockSide F.depth n).period (cubicTorusFrame F.blockSide F.depth n).depth i =
      n * F.blockSide := period_depth i
    omega
  have hl := hrow.locality F (cubicTorusFrame F.blockSide F.depth n) hF hlow y 0 (uniformField F F.depth)
    (uniformField _ _) r 2 ![p, p'] ![X₀, X₁]
    (uniformField_isSmallCurvature hσ) (uniformField_isSmallCurvature hσ) ⟨hper, hper', fun _ _ => rfl⟩
    (by norm_num) (by intro l; fin_cases l; exacts [hp, hp']) (areUnitVectors_pair hX₀ hX₁)
  rw [bondDeriv_subtractTrivial _ _ _ _ _ (hrow.smooth F hF y _ (uniformField_isSmallCurvature hσ) 2 _ _),
    bondDeriv_subtractTrivial _ _ _ _ _
      (hrow.smooth _ hlow 0 _ (uniformField_isSmallCurvature hσ) 2 _ _)] at hl
  exact hl
end AxialSecondOrder
set_option maxHeartbeats 4000000 in
open AxialSecondOrder in
theorem secondOrderAxialBound_holds (hS : SiteDecomposition) (hJ : FormCompositionJet) :
    SecondOrderAxialBound := by
  refine ⟨⌈2 * (4 * (∑' k, inverseSquareWeight k) ^ 4) ^ 2⌉₊ + 209952, ?_⟩
  intro L t n₀ σ δ E E₃ f F X₀ X₁ y Fm Fm' hL0 hodd hσ hδ hE hrow hF hper hX₀ hX₁ hFm hFm'
  classical
  obtain ⟨hFL, hFt, n, hside, hn⟩ := id hF
  subst hFL
  subst hFt
  set K : ℝ := 4 * (∑' k, inverseSquareWeight k) ^ 4 with hKdef
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∑' k, inverseSquareWeight k := tsum_nonneg inverseSquareWeight_nonneg
    positivity
  have hLbig : 209952 ≤ F.blockSide := by omega
  have hLr : (209952 : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast hLbig
  have hL1 : (1 : ℝ) ≤ (F.blockSide : ℝ) := by linarith
  have hKL : 2 * K ^ 2 ≤ (F.blockSide : ℝ) := by
    have h1 := Nat.le_ceil (2 * K ^ 2)
    have h2 : ((⌈2 * K ^ 2⌉₊ : ℕ) : ℝ) ≤ F.blockSide := by
      exact_mod_cast (by omega : ⌈2 * K ^ 2⌉₊ ≤ F.blockSide)
    linarith
  set R : ℕ := ⌊Real.sqrt F.blockSide⌋₊ with hRdef
  have hsq1 : 1 ≤ Real.sqrt F.blockSide := Real.one_le_sqrt.2 hL1
  have hR1 : 1 ≤ R := Nat.le_floor (by simpa using hsq1)
  have hRs : (R : ℝ) ≤ Real.sqrt F.blockSide := Nat.floor_le (Real.sqrt_nonneg _)
  have hR1r : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hR2 : (R : ℝ) ^ 2 ≤ F.blockSide := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg R) hRs 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have hRL : R ≤ F.blockSide := by
    have : (R : ℝ) ≤ F.blockSide := by nlinarith
    exact_mod_cast this
  have hR3 : R + 1 ≤ F.blockSide ^ 2 := by nlinarith
  set box : Finset ((Fin 4 → ℤ) × Fin 4) :=
    (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) R) ×ˢ Finset.univ with hbox
  have hmem : ∀ p, p ∈ box ↔ ∀ i, |p.1 i| ≤ (R : ℤ) := by
    intro p
    simp only [hbox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_univ, and_true, abs_le]
  have hsn : ∀ p ∈ box, supNorm p.1 ≤ R := by
    intro p hp
    refine Finset.sup_le fun i _ => ?_
    have := (hmem p).1 hp i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have hsmall : ∀ p ∈ box, ∀ i, 2 * |p.1 i| < (F.period F.depth i : ℤ) := by
    intro p hp i
    refine two_mul_abs_lt_of_supNorm _ _ ?_
    have h1 := hsn p hp
    have h2 := hper i
    nlinarith
  obtain ⟨q, hlim, hq0⟩ := hrow.flat_limit
  have hside2 : ∀ i, 2 ≤ F.extent i := by
    intro i
    by_contra hlt
    have h1 : F.extent i ≤ 1 := by omega
    have h2 := hper i
    rw [period_depth] at h2
    have h3 : F.extent i * F.blockSide ≤ 1 * F.blockSide := Nat.mul_le_mul_right _ h1
    nlinarith
  have hcover : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth := by
    intro x
    obtain ⟨-, h2, -⟩ := hS F hodd hside2
    obtain ⟨e, hc⟩ := h2 x
    refine mem_sitesOfCells.2 ⟨enclosingCell x, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hside2 _, cellOffset x, ?_, e.symm⟩
    rw [top_sub_depth, pow_one]
    exact hc
  set ι : (Fin 4 → ℤ) × Fin 4 → F.Site F.depth × Fin 4 := fun p => (y + siteOfCoords F.depth p.1, p.2) with hι
  have hinj : Set.InjOn ι box := by
    intro p hp p' hp' e
    have e' : ι p = ι p' := e
    have e1 : y + siteOfCoords F.depth p.1 = y + siteOfCoords F.depth p'.1 :=
      congrArg (fun b : F.Site F.depth × Fin 4 => b.1) e'
    have e2 : p.2 = p'.2 := congrArg (fun b : F.Site F.depth × Fin 4 => b.2) e'
    have e3 : p.1 = p'.1 := by
      rw [← siteOffset_add_siteOfCoords y p.1 (hsmall p hp), ← siteOffset_add_siteOfCoords y p'.1 (hsmall p' hp'), e1]
    exact Prod.ext e3 e2
  have hnearEq : (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide) = box.image ι := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hb⟩
      have hbR : siteSupDist b.1 y ≤ R := Nat.le_floor hb
      refine ⟨(siteOffset y b.1, b.2), (hmem _).2 fun i => ?_, ?_⟩
      · have h1 : ((b.1 i - y i).valMinAbs).natAbs ≤ R :=
          (Finset.le_sup (f := fun i => ((b.1 i - y i).valMinAbs).natAbs) (Finset.mem_univ i)).trans hbR
        show |((b.1 - y) i).valMinAbs| ≤ (R : ℤ)
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h1
      · refine Prod.ext ?_ rfl
        show y + siteOfCoords F.depth (siteOffset y b.1) = b.1
        have hne : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by have := hper i; omega⟩
        funext i
        have e : ((((b.1 - y) i).valMinAbs : ℤ) : ZMod (F.period F.depth i)) = (b.1 - y) i := ZMod.coe_valMinAbs _
        show y i + ((((b.1 - y) i).valMinAbs : ℤ) : ZMod (F.period F.depth i)) = b.1 i
        rw [e]
        simp
    · rintro ⟨p, hp, rfl⟩
      refine ⟨Finset.mem_product.2 ⟨hcover _, Finset.mem_univ _⟩, ?_⟩
      show ((siteSupDist (y + siteOfCoords F.depth p.1) y : ℕ) : ℝ) ≤ Real.sqrt F.blockSide
      rw [siteSupDist_add_left y p.1 (hsmall p hp)]
      exact (Nat.cast_le.2 (hsn p hp)).trans hRs
  have hax : ∀ (G : Fin 4 → Fin 4 → ℝ), ∀ p ∈ box,
      axialGaugePotential y G (ι p).1 (ι p).2 = linearPotential G p := by
    intro G p hp
    unfold axialGaugePotential linearPotential
    have e := siteOffset_add_siteOfCoords y p.1 (hsmall p hp)
    simp only [hι, e]
  have hbf : ∀ p p', bondsAt y ![p, p'] = ![ι p, ι p'] := by
    intro p p'
    funext l
    fin_cases l <;> rfl
  rw [hnearEq, Finset.sum_image hinj]
  have hsumEq : ∑ p ∈ box, ∑ b' ∈ box.image ι,
        bondDeriv (f F y) (uniformField F F.depth) ![ι p, b'] ![X₀, X₁] *
        axialGaugePotential y Fm (ι p).1 (ι p).2 * axialGaugePotential y Fm' b'.1 b'.2 =
      ∑ p ∈ box, ∑ p' ∈ box, bondDeriv (f F y) (uniformField F F.depth) ![ι p, ι p'] ![X₀, X₁] *
        linearPotential Fm p * linearPotential Fm' p' := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun p' hp' => ?_
    rw [hax Fm p hp, hax Fm' p' hp']
  rw [hsumEq]
  have hper2 : ∀ i, 2 * F.blockSide ^ 2 + 2 < F.period F.depth i := hper
  have hinbox : ∀ p ∈ box, BondWithinRadius (F.blockSide ^ 2) p := by
    intro p hp
    have h1 := (hmem p).1 hp
    have hR3' : (R : ℤ) + 1 ≤ ((F.blockSide ^ 2 : ℕ) : ℤ) := by exact_mod_cast hR3
    refine ⟨fun i => (h1 i).trans (by linarith), fun i => ?_⟩
    have h2 : |(p.1 + Pi.single p.2 1 : Fin 4 → ℤ) i| ≤ |p.1 i| + |(Pi.single p.2 (1 : ℤ) : Fin 4 → ℤ) i| :=
      abs_add_le _ _
    have h3 : |(Pi.single p.2 (1 : ℤ) : Fin 4 → ℤ) i| ≤ 1 := by
      by_cases e : i = p.2
      · subst e
        simp
      · simp [e]
    have := h1 i
    linarith
  set e₀ : ℝ := E / torusDecayFactor F.blockSide δ ((F.blockSide ^ 2 : ℕ) : ℝ) with he₀
  have hC : ∀ p ∈ box, ∀ p' ∈ box,
      |bondDeriv (f F y) (uniformField F F.depth) ![ι p, ι p'] ![X₀, X₁] - q p p' X₀ X₁| ≤ e₀ := by
    intro p hp p' hp'
    have h := abs_bondDeriv_sub_limit_le hrow hF hσ (by omega) q hlim hper2 y p p' (hinbox p hp) (hinbox p' hp')
      hX₀ hX₁
    rwa [hbf] at h
  have hnorm : ∀ (G : Fin 4 → Fin 4 → ℝ), ∀ p ∈ box, |linearPotential G p| ≤ R * curvatureNorm G := by
    intro G p hp
    refine (abs_linearPotential_le G p).trans (mul_le_mul_of_nonneg_right ?_ (curvatureNorm_nonneg G))
    exact_mod_cast hsn p hp
  have hcard : (box.card : ℝ) = 4 * (2 * (R : ℝ) + 1) ^ 4 := by
    have h1 : (Finset.Icc (-(R : ℤ)) R).card = 2 * R + 1 := by
      rw [Int.card_Icc]
      omega
    rw [hbox, Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h1]
    push_cast
    ring
  have he₀n : 0 ≤ e₀ := div_nonneg hE (torusDecayFactor_pos _ _ _).le
  have hA : |∑ p ∈ box, ∑ p' ∈ box,
      (bondDeriv (f F y) (uniformField F F.depth) ![ι p, ι p'] ![X₀, X₁] - q p p' X₀ X₁) *
      linearPotential Fm p * linearPotential Fm' p'| ≤
      (box.card : ℝ) * ((box.card : ℝ) * (e₀ * (R * curvatureNorm Fm) * (R * curvatureNorm Fm'))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul box _
      ((box.card : ℝ) * (e₀ * (R * curvatureNorm Fm) * (R * curvatureNorm Fm'))) fun p hp => ?_).trans
      (le_of_eq (nsmul_eq_mul _ _))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul box _ (e₀ * (R * curvatureNorm Fm) * (R * curvatureNorm Fm'))
      fun p' hp' => ?_).trans (le_of_eq (nsmul_eq_mul _ _))
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hC p hp p' hp') (hnorm Fm p hp) (abs_nonneg _) he₀n) (hnorm Fm' p' hp')
      (abs_nonneg _) (by have := curvatureNorm_nonneg Fm; positivity)
  have hom : ∀ (p p' : (Fin 4 → ℤ) × Fin 4) (r s : ℝ), q p p' (r • X₀) (s • X₁) = r * s * q p p' X₀ X₁ := by
    intro p p' r s
    refine tendsto_nhds_unique (hlim p p' (r • X₀) (s • X₁)) ?_
    refine ((hlim p p' X₀ X₁).const_mul (r * s)).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop n₀] with n' hn'
    have hnL : n' ≤ n' * F.blockSide := Nat.le_mul_of_pos_right n' (by omega)
    have hlow : IsCubicTorusAbove F.blockSide F.depth n₀ (cubicTorusFrame F.blockSide F.depth n') :=
      ⟨rfl, rfl, n', fun _ => rfl, by omega⟩
    unfold hessianAtTrivial
    rw [bondsAt_pair]
    exact (bondDeriv_smul_smul hJ _ _ (hrow.smooth _ hlow 0 _ (uniformField_isSmallCurvature hσ)) _ _ _ _ _ _).symm
  have hsum := hq0 (fun μ ν => Fm μ ν • X₀) (fun μ ν => Fm' μ ν • X₁) (fun p => linearPotential Fm p • X₀)
    (fun p => linearPotential Fm' p • X₁) (isAntisymmetricCurvature_smul Fm hFm X₀)
    (isAntisymmetricCurvature_smul Fm' hFm' X₁) (isLinearPotential_smul Fm hFm X₀) (isLinearPotential_smul Fm' hFm' X₁)
  set cc : ℝ := E * curvatureNorm Fm * curvatureNorm Fm' * ((F.blockSide : ℝ) ^ 25 / (F.blockSide : ℝ) ^ 7500)
    with hcc
  have hcc0 : 0 ≤ cc := by
    have h1 := curvatureNorm_nonneg Fm
    have h2 := curvatureNorm_nonneg Fm'
    positivity
  have hout : ∀ p, p ∉ box → R + 1 ≤ supNorm p.1 := by
    intro p hp
    by_contra hlt
    refine hp ((hmem p).2 fun i => ?_)
    rw [Int.abs_eq_natAbs]
    have := natAbs_le_supNorm p.1 i
    omega
  have hpoint : ∀ P : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4), P ∉ box ×ˢ box →
      |q P.1 P.2 (linearPotential Fm P.1 • X₀) (linearPotential Fm' P.2 • X₁)| ≤
        cc * (bondWeight P.1 * bondWeight P.2) := by
    intro P hP
    set m : ℕ := max (supNorm P.1.1) (supNorm P.2.1) with hm
    have hmR : R + 1 ≤ m := by
      by_cases h1 : P.1 ∈ box
      · have h2 : P.2 ∉ box := fun h2 => hP (Finset.mem_product.2 ⟨h1, h2⟩)
        exact (hout _ h2).trans (le_max_right _ _)
      · exact (hout _ h1).trans (le_max_left _ _)
    have hm1 : (1 : ℝ) ≤ m := by
      have : 1 ≤ m := by omega
      exact_mod_cast this
    have hm2 : (F.blockSide : ℝ) ≤ (m : ℝ) ^ 2 := by
      have h1 : Real.sqrt F.blockSide < (R : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : (R : ℝ) + 1 ≤ m := by exact_mod_cast hmR
      have h3 : Real.sqrt F.blockSide ≤ m := by linarith
      have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
      rwa [Real.sq_sqrt (by positivity)] at h4
    have hq1 := abs_limit_le_decay hrow hσ hδ hE (by omega) q hlim P.1 P.2 hX₀ hX₁
    have hw := inv_torusDecayFactor_le (L := F.blockSide) (δ := δ) (x := (m : ℝ)) (by omega) hδ (by linarith)
    have hq2 : |q P.1 P.2 X₀ X₁| ≤ E * ((F.blockSide : ℝ) ^ 25 / (m : ℝ) ^ 16000) := by
      refine hq1.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hw hE
    have hP1 : |linearPotential Fm P.1| ≤ m * curvatureNorm Fm := by
      refine (abs_linearPotential_le Fm P.1).trans (mul_le_mul_of_nonneg_right ?_ (curvatureNorm_nonneg Fm))
      exact_mod_cast (le_max_left _ _ : supNorm P.1.1 ≤ m)
    have hP2 : |linearPotential Fm' P.2| ≤ m * curvatureNorm Fm' := by
      refine (abs_linearPotential_le Fm' P.2).trans (mul_le_mul_of_nonneg_right ?_ (curvatureNorm_nonneg Fm'))
      exact_mod_cast (le_max_right _ _ : supNorm P.2.1 ≤ m)
    have hf1 := curvatureNorm_nonneg Fm
    have hf2 := curvatureNorm_nonneg Fm'
    rw [hom, abs_mul, abs_mul]
    have hg1 := inv_pow_eight_le_bondWeight P.1 (m : ℝ) hm1
      (by exact_mod_cast (le_max_left _ _ : supNorm P.1.1 ≤ m))
    have hg2 := inv_pow_eight_le_bondWeight P.2 (m : ℝ) hm1
      (by exact_mod_cast (le_max_right _ _ : supNorm P.2.1 ≤ m))
    have hterm := far_term_le hL1 hm1 hm2
    calc |linearPotential Fm P.1| * |linearPotential Fm' P.2| * |q P.1 P.2 X₀ X₁|
        ≤ (m * curvatureNorm Fm) * (m * curvatureNorm Fm') * (E * ((F.blockSide : ℝ) ^ 25 / (m : ℝ) ^ 16000)) :=
          mul_le_mul (mul_le_mul hP1 hP2 (abs_nonneg _) (by positivity)) hq2 (abs_nonneg _) (by positivity)
      _ = E * curvatureNorm Fm * curvatureNorm Fm' *
            ((F.blockSide : ℝ) ^ 25 / (m : ℝ) ^ 16000 * ((m : ℝ) * m)) := by ring
      _ ≤ E * curvatureNorm Fm * curvatureNorm Fm' *
            ((F.blockSide : ℝ) ^ 25 / (F.blockSide : ℝ) ^ 7500 * (((m : ℝ) ^ 8)⁻¹ * ((m : ℝ) ^ 8)⁻¹)) :=
          mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = cc * (((m : ℝ) ^ 8)⁻¹ * ((m : ℝ) ^ 8)⁻¹) := by rw [hcc]; ring
      _ ≤ cc * (bondWeight P.1 * bondWeight P.2) := by
          refine mul_le_mul_of_nonneg_left ?_ hcc0
          exact mul_le_mul hg1 hg2 (by positivity) ((by positivity : (0 : ℝ) ≤ ((m : ℝ) ^ 8)⁻¹).trans hg1)
  have hgp0 : ∀ p, 0 ≤ bondWeight p := fun p => Finset.prod_nonneg fun i _ => inverseSquareWeight_nonneg _
  have hB0 := abs_finset_sum_le_of_hasSum_zero (fun P : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
      q P.1 P.2 (linearPotential Fm P.1 • X₀) (linearPotential Fm' P.2 • X₁)) hsum (box ×ˢ box) (cc * K ^ 2) (by
    intro D hD
    have h1 : ∑ P ∈ D, |q P.1 P.2 (linearPotential Fm P.1 • X₀) (linearPotential Fm' P.2 • X₁)| ≤
        ∑ P ∈ D, cc * (bondWeight P.1 * bondWeight P.2) :=
      Finset.sum_le_sum fun P hP => hpoint P (Finset.disjoint_left.1 hD hP)
    refine h1.trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hcc0
    have hsub : D ⊆ D.image Prod.fst ×ˢ D.image Prod.snd := fun P hP =>
      Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hP, Finset.mem_image_of_mem _ hP⟩
    calc ∑ P ∈ D, bondWeight P.1 * bondWeight P.2
          ≤ ∑ P ∈ D.image Prod.fst ×ˢ D.image Prod.snd, bondWeight P.1 * bondWeight P.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun P _ _ => mul_nonneg (hgp0 _) (hgp0 _)
      _ = (∑ p ∈ D.image Prod.fst, bondWeight p) * ∑ p ∈ D.image Prod.snd, bondWeight p := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ K * K := mul_le_mul (sum_bondWeight_le _) (sum_bondWeight_le _)
          (Finset.sum_nonneg fun p _ => hgp0 p) hK0
      _ = K ^ 2 := by ring)
  have hBeq : ∑ P ∈ box ×ˢ box, q P.1 P.2 (linearPotential Fm P.1 • X₀) (linearPotential Fm' P.2 • X₁) =
      ∑ p ∈ box, ∑ p' ∈ box, q p p' X₀ X₁ * linearPotential Fm p * linearPotential Fm' p' := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
    simp only [hom]
    ring
  rw [hBeq] at hB0
  have hsplit : ∑ p ∈ box, ∑ p' ∈ box, bondDeriv (f F y) (uniformField F F.depth) ![ι p, ι p'] ![X₀, X₁] *
        linearPotential Fm p * linearPotential Fm' p' =
      ∑ p ∈ box, ∑ p' ∈ box, (bondDeriv (f F y) (uniformField F F.depth) ![ι p, ι p'] ![X₀, X₁] - q p p' X₀ X₁) *
        linearPotential Fm p * linearPotential Fm' p' +
        ∑ p ∈ box, ∑ p' ∈ box, q p p' X₀ X₁ * linearPotential Fm p * linearPotential Fm' p' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p' _ => ?_
    ring
  rw [hsplit]
  have hrp : (F.blockSide : ℝ) ^ (-(7000 : ℝ)) = ((F.blockSide : ℝ) ^ 7000)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  have hf1 := curvatureNorm_nonneg Fm
  have hf2 := curvatureNorm_nonneg Fm'
  have he₁ : e₀ ≤ E * ((F.blockSide : ℝ) ^ 25 / ((F.blockSide : ℝ) ^ 2) ^ 16000) := by
    have hw := inv_torusDecayFactor_le (L := F.blockSide) (δ := δ) (x := ((F.blockSide ^ 2 : ℕ) : ℝ))
      (by omega) hδ (by positivity)
    rw [he₀, div_eq_mul_inv]
    push_cast at hw ⊢
    exact mul_le_mul_of_nonneg_left hw hE
  have hnear := near_numeric_bound hLr hR1r hR2 hcard
  have hfar := far_numeric_bound hL1 hKL
  have hA2 : (box.card : ℝ) * ((box.card : ℝ) * (e₀ * (R * curvatureNorm Fm) * (R * curvatureNorm Fm'))) ≤
      E * curvatureNorm Fm * curvatureNorm Fm' * (1 / 2 * ((F.blockSide : ℝ) ^ 7000)⁻¹) := by
    have h1 : (box.card : ℝ) * ((box.card : ℝ) * (e₀ * (R * curvatureNorm Fm) * (R * curvatureNorm Fm'))) =
        curvatureNorm Fm * curvatureNorm Fm' * ((box.card : ℝ) * box.card * ((R : ℝ) * R) * e₀) := by ring
    have hc0 : 0 ≤ (box.card : ℝ) * box.card * ((R : ℝ) * R) := by positivity
    have h2 : (box.card : ℝ) * box.card * ((R : ℝ) * R) * e₀ ≤ E * (1 / 2 * ((F.blockSide : ℝ) ^ 7000)⁻¹) := by
      calc (box.card : ℝ) * box.card * ((R : ℝ) * R) * e₀
          ≤ (box.card : ℝ) * box.card * ((R : ℝ) * R) *
              (E * ((F.blockSide : ℝ) ^ 25 / ((F.blockSide : ℝ) ^ 2) ^ 16000)) :=
            mul_le_mul_of_nonneg_left he₁ hc0
        _ = E * ((box.card : ℝ) * box.card * ((R : ℝ) * R) *
              ((F.blockSide : ℝ) ^ 25 / ((F.blockSide : ℝ) ^ 2) ^ 16000)) := by ring
        _ ≤ E * (1 / 2 * ((F.blockSide : ℝ) ^ 7000)⁻¹) := mul_le_mul_of_nonneg_left hnear hE
    rw [h1]
    calc curvatureNorm Fm * curvatureNorm Fm' * ((box.card : ℝ) * box.card * ((R : ℝ) * R) * e₀)
        ≤ curvatureNorm Fm * curvatureNorm Fm' * (E * (1 / 2 * ((F.blockSide : ℝ) ^ 7000)⁻¹)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = E * curvatureNorm Fm * curvatureNorm Fm' * (1 / 2 * ((F.blockSide : ℝ) ^ 7000)⁻¹) := by ring
  have hB2 : cc * K ^ 2 ≤ E * curvatureNorm Fm * curvatureNorm Fm' * (1 / 2 * ((F.blockSide : ℝ) ^ 7000)⁻¹) := by
    rw [hcc, mul_assoc]
    exact mul_le_mul_of_nonneg_left hfar (by positivity)
  have hfin : (F.blockSide : ℝ) ^ (-(7000 : ℝ)) * E * (∑ μ, ∑ ν, |Fm μ ν|) * ∑ μ, ∑ ν, |Fm' μ ν| =
      E * curvatureNorm Fm * curvatureNorm Fm' * (1 / 2 * ((F.blockSide : ℝ) ^ 7000)⁻¹) +
        E * curvatureNorm Fm * curvatureNorm Fm' * (1 / 2 * ((F.blockSide : ℝ) ^ 7000)⁻¹) := by
    rw [hrp]
    unfold curvatureNorm
    ring
  rw [hfin]
  exact (abs_add_le _ _).trans (add_le_add (hA.trans hA2) (hB0.trans hB2))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
