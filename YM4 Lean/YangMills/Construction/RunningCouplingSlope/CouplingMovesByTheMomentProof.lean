import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ClusterExpansionOfAStep.TheHotHalf
import YangMills.Construction.RunningCouplingSlope.CouplingMovesByTheMoment
import YangMills.Construction.RunningCouplingSlope.KernelOfASmallFamily
import YangMills.Construction.RunningCouplingSlope.MomentOfAnExpansion
import YangMills.Construction.RunningCouplingSlope.MomentOfTheLeastAction
import YangMills.Construction.RunningCouplingSlope.StepTotalsHaveCoefficientsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.SlopeCoefficient YangMills.Construction.ShareFamilies Filter
namespace YangMills.Construction.RunningCouplingSlope
private theorem coldExpansion_floor_indep {T : ParameterAssignment} {y y' : ℝ} {t : ℕ} {x : ℝ}
    {D : TorusFunctional} {f : LocalDensity}
    (h : ColdExpansion (T.stepParameters y) t x D f) : ColdExpansion (T.stepParameters y') t x D f := by
  cases h
  constructor <;> assumption
private theorem hullExpansion_floor_indep {T : ParameterAssignment} {y y' : ℝ} {t : ℕ} {x : ℝ}
    {D : TorusFunctional} {f : LocalDensity}
    {Λ : LabelSpace} {w : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
    {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
    {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
    (h : HullExpansion (T.stepParameters y) t x D f Λ w Φ φ) :
    HullExpansion (T.stepParameters y') t x D f Λ w Φ φ := by
  cases h
  constructor <;> assumption
variable {n : ℕ}
private theorem tendsto_perturb_trivial {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) :
    Tendsto (fun s : Fin k → ℝ => perturb c X s (trivialField n)) (𝓝 0) (𝓝 (trivialField n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.StepGaugeTotals.tendsto_perturb_trivialField <;> assumption
private theorem eventually_isCold_nhds_trivial [NeZero n] {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ V in 𝓝 (trivialField n), IsCold σ V := by apply _root_.YangMills.SharedProofs.p23383 <;> assumption
private theorem isCold_trivial {σ : ℝ} (hσ : 0 < σ) : IsCold σ (trivialField n) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private theorem minimalActionTotal_eq (a : ℝ) (L t : ℕ) [hn : NeZero n] (V : TorusField n) :
    minimalActionTotal a L t n V = actionAtLevel a L t Finset.univ V := by
  unfold minimalActionTotal
  rw [dif_neg hn.out]
private theorem centeredDensityTotal_eq (f : LocalDensity) [hn : NeZero n] (V : TorusField n) :
    centeredDensityTotal f n V = ∑ y, centered f n y V := by
  unfold centeredDensityTotal
  rw [dif_neg hn.out]
private theorem goodFieldLogIntegral_eq (R : StepSetup) [hn : NeZero n] (V : TorusField n) :
    goodFieldLogIntegral R n V =
      Real.log (coldImageIntegral R V) - Real.log (coldImageIntegral R (trivialField n)) := by
  unfold goodFieldLogIntegral
  rw [dif_neg hn.out]
private theorem contDiffAt_centeredDensityTotal (g : LocalDensity) [NeZero n]
    (hs : ∀ y : TorusSite n, ContDiffThreeAt (g n y) (trivialField n))
    {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 2 (fun s : Fin k → ℝ => centeredDensityTotal g n (perturb c X s (trivialField n))) 0 := by
  have h : ContDiffAt ℝ 2
      (fun s : Fin k → ℝ => ∑ y, centered g n y (perturb c X s (trivialField n))) 0 := by
    refine ContDiffAt.sum fun y _ => ?_
    have h3 := (hs y) k c X
    have h2 : ContDiffAt ℝ 2 (fun s : Fin k → ℝ => g n y (perturb c X s (trivialField n))) 0 :=
      h3.of_le (by norm_num)
    exact h2.sub contDiffAt_const
  simpa only [centeredDensityTotal_eq] using h
private theorem iteratedFDeriv_two_combination {φ α β γ : (Fin 2 → ℝ) → ℝ} (a : ℝ)
    (hα : ContDiffAt ℝ 2 α 0) (hβ : ContDiffAt ℝ 2 β 0) (hγ : ContDiffAt ℝ 2 γ 0)
    (h : φ =ᶠ[𝓝 0] fun s => a * α s + β s - γ s) (v : Fin 2 → Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 φ 0 v =
      a * iteratedFDeriv ℝ 2 α 0 v + iteratedFDeriv ℝ 2 β 0 v - iteratedFDeriv ℝ 2 γ 0 v := by
  have e : iteratedFDeriv ℝ 2 φ 0 = iteratedFDeriv ℝ 2 (fun s => a * α s + β s - γ s) 0 :=
    (h.iteratedFDeriv ℝ 2).eq_of_nhds
  have a₁ : ContDiffAt ℝ 2 (fun s => a • α s) 0 := hα.const_smul a
  have a₂ := a₁.add hβ
  have e₂ : (fun s => a * α s + β s - γ s) = fun s => a • α s + β s - γ s := by
    funext s
    simp
  have c₁ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s => a • α s) 0 := by exact_mod_cast a₁
  have c₂ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s => a • α s + β s) 0 := by exact_mod_cast a₂
  have c₃ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) β 0 := by exact_mod_cast hβ
  have c₄ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) γ 0 := by exact_mod_cast hγ
  have c₅ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) α 0 := by exact_mod_cast hα
  rw [e, e₂, fun_iteratedFDeriv_sub_apply c₂ c₄, fun_iteratedFDeriv_add_apply c₁ c₃,
    iteratedFDeriv_const_smul_apply' c₅]
  simp
private theorem gaugeTotalMoment_combination (H A F G : GaugeTotal) (a : ℝ) [NeZero n]
    (X : imaginaryQuaternions)
    (hev : ∀ᶠ V in 𝓝 (trivialField n), H n V = a * A n V + F n V - G n V)
    (hA : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun s : Fin k → ℝ => A n (perturb c X s (trivialField n))) 0)
    (hF : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun s : Fin k → ℝ => F n (perturb c X s (trivialField n))) 0)
    (hG : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun s : Fin k → ℝ => G n (perturb c X s (trivialField n))) 0) :
    gaugeTotalMoment H n X =
      a * gaugeTotalMoment A n X + gaugeTotalMoment F n X - gaugeTotalMoment G n X := by
  have key : ∀ c c' : TorusBond n, hessianAtTrivial H n c c' X X =
      a * hessianAtTrivial A n c c' X X + hessianAtTrivial F n c c' X X -
        hessianAtTrivial G n c c' X X := by
    intro c c'
    unfold hessianAtTrivial mixedDeriv
    exact iteratedFDeriv_two_combination a (hA 2 _ _) (hF 2 _ _) (hG 2 _ _)
      ((tendsto_perturb_trivial _ _).eventually hev) _
  simp only [gaugeTotalMoment, kernelSecondMoment]
  have term : ∀ y : TorusSite n, (if supDist 0 y ≤ 2 * momentCutoff n then
        ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 *
          hessianAtTrivial H n (0, secondAxis) (y, secondAxis) X X else 0) =
      a * (if supDist 0 y ≤ 2 * momentCutoff n then
        ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 *
          hessianAtTrivial A n (0, secondAxis) (y, secondAxis) X X else 0) +
      (if supDist 0 y ≤ 2 * momentCutoff n then
        ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 *
          hessianAtTrivial F n (0, secondAxis) (y, secondAxis) X X else 0) -
      (if supDist 0 y ≤ 2 * momentCutoff n then
        ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 *
          hessianAtTrivial G n (0, secondAxis) (y, secondAxis) X X else 0) := by
    intro y
    rw [key]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun y _ => term y, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring
private theorem abs_gaugeTotalMoment_le (G : GaugeTotal) [NeZero n] (X : imaginaryQuaternions)
    {M θ : ℝ} (hM : 0 ≤ M) (hθ : 0 ≤ θ)
    (hX : ‖X‖ = 1) (hK : HessianBoundedBy G n M θ) : |gaugeTotalMoment G n X| ≤ (n : ℝ) ^ 6 * M := by
  have hterm : ∀ y : TorusSite n, |if supDist 0 y ≤ 2 * momentCutoff n then
      ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 *
        hessianAtTrivial G n (0, secondAxis) (y, secondAxis) X X else 0| ≤
      (n : ℝ) ^ 2 * M := by
    intro y
    have hk := hK (0, secondAxis) (y, secondAxis) X X hX hX
    have hexp : Real.exp (-(θ * supDist (0 : TorusSite n) y)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : (0 : ℝ) ≤ θ * supDist (0 : TorusSite n) y := by positivity
      linarith
    have hk' : |hessianAtTrivial G n (0, secondAxis) (y, secondAxis) X X| ≤ M :=
      hk.trans (by simpa using mul_le_mul_of_nonneg_left hexp hM)
    have hoff : ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have h1 : (firstCoordDiff (0 : TorusSite n) y).natAbs ≤ n :=
        (ZMod.natAbs_valMinAbs_le _).trans (Nat.div_le_self _ _)
      have h2 : |firstCoordDiff (0 : TorusSite n) y| ≤ (n : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h1
      have h3 : |((firstCoordDiff (0 : TorusSite n) y : ℤ) : ℝ)| ≤ (n : ℝ) := by exact_mod_cast h2
      exact sq_le_sq' (abs_le.mp h3).1 (abs_le.mp h3).2
    split_ifs
    · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul hoff hk' (abs_nonneg _) (by positivity)
    · simpa using mul_nonneg (sq_nonneg (n : ℝ)) hM
  simp only [gaugeTotalMoment, kernelSecondMoment]
  rw [abs_mul]
  have hs := (Finset.abs_sum_le_sum_abs (fun y : TorusSite n => if supDist 0 y ≤ 2 * momentCutoff n then
      ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 *
        hessianAtTrivial G n (0, secondAxis) (y, secondAxis) X X else 0)
      Finset.univ).trans (Finset.sum_le_sum fun y _ => hterm y)
  have hc : (∑ _y : TorusSite n, (n : ℝ) ^ 2 * M) = (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 * M) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [ZMod.card]
  rw [hc] at hs
  have h12 : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num [abs_of_pos]
  rw [h12]
  have hp : 0 ≤ (n : ℝ) ^ 6 * M := by positivity
  nlinarith
private theorem exp_neg_mul_side_le {c C₁ x : ℝ} {n₀ n : ℕ} (hc : 0 < c) (hC : 1 ≤ c * C₁)
    (hx : 1 ≤ x) (hn : n = stepTorusSide n₀ C₁ x) : Real.exp (-(c * n)) ≤ Real.exp c / x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hfl : C₁ * Real.log x < (n : ℝ) + 1 := by
    have h1 := Nat.lt_floor_add_one (C₁ * Real.log x)
    have h2 : (⌊C₁ * Real.log x⌋₊ : ℝ) ≤ n := by
      rw [hn]
      unfold stepTorusSide
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n₀]
    linarith
  have h3 : Real.log x - c ≤ c * n := by
    have h5 : c * (C₁ * Real.log x) ≤ c * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left hfl.le hc.le
    have h4 : Real.log x ≤ c * C₁ * Real.log x := by nlinarith
    nlinarith
  have hx0 : 0 < x := by linarith
  calc Real.exp (-(c * n)) ≤ Real.exp (c - Real.log x) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp c / x := by rw [Real.exp_sub, Real.exp_log hx0]
private theorem side_pow_mul_exp_le {r C₁ x : ℝ} {n₀ n : ℕ} (hr : 0 < r) (hC : 0 ≤ C₁) (hx : 1 ≤ x)
    (hn : n = stepTorusSide n₀ C₁ x) :
    (n : ℝ) ^ 6 * Real.exp (-(r * x / 2)) ≤ ((n₀ : ℝ) + C₁) ^ 6 * (5040 * (2 / r) ^ 7) / x := by
  have hlog := Real.log_nonneg hx
  have hx0 : 0 < x := by linarith
  have hn₀ : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have hn1 : (n : ℝ) ≤ ((n₀ : ℝ) + C₁) * x := by
    have h1 : (⌊C₁ * Real.log x⌋₊ : ℝ) ≤ C₁ * Real.log x := Nat.floor_le (by positivity)
    have h2 : Real.log x ≤ x := Real.log_le_self hx0.le
    rw [hn]
    unfold stepTorusSide
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h2 hC, mul_le_mul_of_nonneg_left hx hn₀]
  have hu0 : 0 < r * x / 2 := by positivity
  have hb := Real.pow_div_factorial_le_exp (r * x / 2) hu0.le 7
  have h7 : (r * x / 2) ^ 7 ≤ 5040 * Real.exp (r * x / 2) := by
    have hf : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
    rw [hf, div_le_iff₀ (by norm_num)] at hb
    linarith
  have he : Real.exp (-(r * x / 2)) ≤ 5040 / (r * x / 2) ^ 7 := by
    rw [le_div_iff₀ (by positivity)]
    calc Real.exp (-(r * x / 2)) * (r * x / 2) ^ 7
        ≤ Real.exp (-(r * x / 2)) * (5040 * Real.exp (r * x / 2)) :=
          mul_le_mul_of_nonneg_left h7 (Real.exp_pos _).le
      _ = 5040 := by
          rw [Real.exp_neg]
          field_simp
  have hn6 : (n : ℝ) ^ 6 ≤ (((n₀ : ℝ) + C₁) * x) ^ 6 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hn1 6
  calc (n : ℝ) ^ 6 * Real.exp (-(r * x / 2))
      ≤ (((n₀ : ℝ) + C₁) * x) ^ 6 * (5040 / (r * x / 2) ^ 7) :=
        mul_le_mul hn6 he (Real.exp_pos _).le (by positivity)
    _ = ((n₀ : ℝ) + C₁) ^ 6 * (5040 * (2 / r) ^ 7) / x := by
        field_simp
private theorem gasRate_pos_aux {T : ParameterAssignment} (hT : T.Admissible) : 0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
theorem couplingShiftEqualsGaugeMoment (hHot : ClusterExpansionOfAStep.HotFactorization)
    (hRow : CenteredDensityMomentDecay) (hAct : MinimalActionMomentNearOne)
    (hSm : SmallDensityHessianBound) (hSh : LevelSharesFormCurvatureFamily) :
    CouplingShiftEqualsGaugeMoment := by
  obtain ⟨rt₀, hrt₀, hHot⟩ := hHot
  obtain ⟨CA, cA, hCA, hcA, hAct⟩ := hAct
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨y₁, hHot⟩ := hHot T hT hrt
  obtain ⟨CF, cF, hCF, hcF, hRow⟩ := hRow T hT
  obtain ⟨C₃, θ, hC₃, hθ, hSm⟩ := hSm T hT
  have ca := hcA T.toChainParameters
  have Ca := hCA T.toChainParameters
  refine ⟨1 / cA T.toChainParameters + 1 / cF, by positivity, fun C₁ hC₁ => ?_⟩
  have hch := gasRate_pos_aux hT
  have hB : 1 ≤ T.B := hT.B_ge
  have hB0 : 0 < T.B := by linarith
  have hi₁ : 0 < 1 / cA T.toChainParameters := by positivity
  have hi₂ : 0 < 1 / cF := by positivity
  have hC₁0 : 0 < C₁ := by linarith
  have hA1 : 1 ≤ cA T.toChainParameters * C₁ := by
    have h : 1 / cA T.toChainParameters ≤ C₁ := by linarith
    rwa [div_le_iff₀ ca, mul_comm] at h
  have hF1 : 1 ≤ cF * C₁ := by
    have h : 1 / cF ≤ C₁ := by linarith
    rwa [div_le_iff₀ hcF, mul_comm] at h
  have hn₀p : (0 : ℝ) ≤ T.n₀ := Nat.cast_nonneg _
  have hK : 0 < ((T.n₀ : ℝ) + C₁) ^ 6 * (5040 * (2 / T.gasRate) ^ 7) := by positivity
  refine ⟨2 * T.B * (CA T.toChainParameters * Real.exp (cA T.toChainParameters)) + CF * Real.exp cF +
    C₃ * (((T.n₀ : ℝ) + C₁) ^ 6 * (5040 * (2 / T.gasRate) ^ 7)), max 1 y₁, by positivity, ?_⟩
  intro y R x' f' hy hOn hArr hys hmove hrow n _ X hn hX
  obtain ⟨ℓ, t, x, x₂, D, f, Λ, w, Φ, φ, ρA, p⟩ := R
  obtain ⟨hl, hρ, hp, hxy, hstep⟩ := hOn
  change ℓ = T.stepParameters y at hl
  subst hl
  change y ≤ x at hxy
  change max 1 y₁ ≤ x at hys
  change |x' - x| ≤ 2 * T.B at hmove
  change ColdExpansion (T.stepParameters y) (t + 1) x'
    (kernelImage (T.stepParameters y) x D) f' at hrow
  change n = stepTorusSide T.n₀ C₁ x at hn
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hys
  have hyx : y₁ ≤ x := (le_max_right _ _).trans hys
  have hx0 : 0 < x := by linarith
  have hy' : y₁ ≤ max y y₁ := le_max_right _ _
  have hy₀' : T.floorMin ≤ max y y₁ := hy.trans (le_max_left _ _)
  let R₀ : StepSetup := ⟨T.stepParameters y, t, x, x₂, D, f, Λ, w, Φ, φ, ρA, p⟩
  let R' : StepSetup := ⟨T.stepParameters (max y y₁), t, x, x₂, D, f, Λ, w, Φ, φ, ρA, p⟩
  have hOn' : R'.OnParameters T (max y y₁) :=
    ⟨rfl, hρ, hp, max_le hxy hyx,
      ⟨⟨coldExpansion_floor_indep hstep.1.1, hullExpansion_floor_indep hstep.1.2⟩,
        hstep.2.1, hstep.2.2⟩⟩
  have hArr' : R'.IsSymmetricWeight := hArr
  obtain ⟨hsmall, hform⟩ := hHot (max y y₁) hy' R' hOn' hArr'
  have hn₀ : T.n₀ ≤ n := by
    rw [hn]
    exact Nat.le_add_right _ _
  have hn64 : 64 ≤ n := by
    have := hT.n₀_ge
    omega
  have hσ : 0 < T.threshold := hT.σ_pos
  have hflat : IsCold T.threshold (trivialField n) := isCold_trivial hσ
  have hE0 : 0 ≤ Real.exp (-(T.gasRate * x / 2)) := (Real.exp_pos _).le
  obtain ⟨gG, kG⟩ := hSm (max y y₁) _ R'.blockDensity hy₀' hE0 hsmall n hn₀
  obtain ⟨fam, -, hsum⟩ := hSh T hT y hy t
  have hAeq : ∀ᶠ V in 𝓝 (trivialField n), minimalActionTotal T.coupling T.side (t + 1) n V =
      centeredDensityTotal (levelShareFamily T.coupling T.side (t + 1)) n V :=
    (eventually_isCold_nhds_trivial hσ).mono fun V hV => by
      rw [minimalActionTotal_eq, centeredDensityTotal_eq, hsum n hn₀ V hV]
  have sA : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun s : Fin k → ℝ =>
        minimalActionTotal T.coupling T.side (t + 1) n (perturb c X s (trivialField n))) 0 :=
    fun k c X => (contDiffAt_centeredDensityTotal _
      (fun z => fam.smooth n hn₀ z (trivialField n) hflat) c X).congr_of_eventuallyEq
      ((tendsto_perturb_trivial c X).eventually hAeq)
  have sF : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun s : Fin k → ℝ => centeredDensityTotal f' n (perturb c X s (trivialField n))) 0 :=
    fun k c X => contDiffAt_centeredDensityTotal _
      (fun z => hrow.smooth n hn₀ z (trivialField n) hflat) c X
  have hev : ∀ᶠ V in 𝓝 (trivialField n), laplaceRemainder R₀ n V =
      (x - x') * minimalActionTotal T.coupling T.side (t + 1) n V + centeredDensityTotal f' n V -
        centeredDensityTotal R'.blockDensity n V := by
    filter_upwards [eventually_isCold_nhds_trivial (n := n) hσ] with V hV
    have e₁ : Real.log (kernelImage (T.stepParameters y) x D n V) =
        Real.log (coldImageIntegral R' V) + ∑ Y, R'.blockDensity n Y V := (hform n hn₀ V hV).2.2
    have e₂ : Real.log (kernelImage (T.stepParameters y) x D n (trivialField n)) =
        Real.log (coldImageIntegral R' (trivialField n)) +
          ∑ Y, R'.blockDensity n Y (trivialField n) :=
      (hform n hn₀ (trivialField n) hflat).2.2
    have e₃ : Real.log (kernelImage (T.stepParameters y) x D n V) -
        Real.log (kernelImage (T.stepParameters y) x D n (trivialField n)) =
        -x' * actionAtLevel T.coupling T.side (t + 1) Finset.univ V + ∑ z, centered f' n z V :=
      hrow.form n hn₀ V hV
    have dG : centeredDensityTotal R'.blockDensity n V =
        (∑ Y, R'.blockDensity n Y V) - ∑ Y, R'.blockDensity n Y (trivialField n) := by
      rw [centeredDensityTotal_eq]
      simp only [centered]
      rw [Finset.sum_sub_distrib]
    have dL : laplaceRemainder R₀ n V =
        (Real.log (coldImageIntegral R' V) - Real.log (coldImageIntegral R' (trivialField n))) +
        x * minimalActionTotal T.coupling T.side (t + 1) n V := by
      change goodFieldLogIntegral R₀ n V + x * minimalActionTotal T.coupling T.side (t + 1) n V = _
      rw [goodFieldLogIntegral_eq]
      rfl
    rw [dG, centeredDensityTotal_eq, dL, minimalActionTotal_eq]
    linarith
  have hM := gaugeTotalMoment_combination (laplaceRemainder R₀)
    (minimalActionTotal T.coupling T.side (t + 1)) (centeredDensityTotal f')
    (centeredDensityTotal R'.blockDensity) (x - x') X hev sA sF gG.contDiffAt_perturb
  have bA := hAct T hT t n X hn64 hX
  have bF := hRow y (t + 1) x' _ f' hy hrow n X hn₀ hX
  have bG := abs_gaugeTotalMoment_le (centeredDensityTotal R'.blockDensity) X
    (mul_nonneg hC₃.le hE0) hθ.le hX kG
  have eA := exp_neg_mul_side_le (n₀ := T.n₀) ca hA1 hx1 hn
  have eF := exp_neg_mul_side_le (n₀ := T.n₀) hcF hF1 hx1 hn
  have pG := side_pow_mul_exp_le (n₀ := T.n₀) hch hC₁0.le hx1 hn
  change |x - x' - gaugeTotalMoment (laplaceRemainder R₀) n X| ≤ _ / x
  rw [hM]
  have hq : x - x' - ((x - x') * gaugeTotalMoment (minimalActionTotal T.coupling T.side (t + 1)) n X +
        gaugeTotalMoment (centeredDensityTotal f') n X -
        gaugeTotalMoment (centeredDensityTotal R'.blockDensity) n X) =
      -((x - x') * (gaugeTotalMoment (minimalActionTotal T.coupling T.side (t + 1)) n X - 1)) -
        gaugeTotalMoment (centeredDensityTotal f') n X +
        gaugeTotalMoment (centeredDensityTotal R'.blockDensity) n X := by ring
  rw [hq]
  have h1 : |x - x'| ≤ 2 * T.B := by rwa [abs_sub_comm]
  have bA' : |gaugeTotalMoment (minimalActionTotal T.coupling T.side (t + 1)) n X - 1| ≤
      CA T.toChainParameters * (Real.exp (cA T.toChainParameters) / x) :=
    bA.trans (mul_le_mul_of_nonneg_left eA Ca.le)
  have bF' : |gaugeTotalMoment (centeredDensityTotal f') n X| ≤ CF * (Real.exp cF / x) :=
    bF.trans (mul_le_mul_of_nonneg_left eF hCF.le)
  have bG' : |gaugeTotalMoment (centeredDensityTotal R'.blockDensity) n X| ≤
      C₃ * (((T.n₀ : ℝ) + C₁) ^ 6 * (5040 * (2 / T.gasRate) ^ 7) / x) := by
    refine bG.trans ?_
    have := mul_le_mul_of_nonneg_left pG hC₃.le
    calc (n : ℝ) ^ 6 * (C₃ * Real.exp (-(T.gasRate * x / 2)))
        = C₃ * ((n : ℝ) ^ 6 * Real.exp (-(T.gasRate * x / 2))) := by ring
      _ ≤ _ := this
  have b1 : |(x - x') * (gaugeTotalMoment (minimalActionTotal T.coupling T.side (t + 1)) n X - 1)| ≤
      2 * T.B * (CA T.toChainParameters * (Real.exp (cA T.toChainParameters) / x)) := by
    rw [abs_mul]
    exact mul_le_mul h1 bA' (abs_nonneg _) (by positivity)
  have tri : ∀ a b c : ℝ, |-a - b + c| ≤ |a| + |b| + |c| := by
    intro a b c
    calc |-a - b + c| ≤ |-a - b| + |c| := abs_add_le _ _
      _ ≤ |-a| + |b| + |c| := by linarith [abs_sub (-a) b]
      _ = |a| + |b| + |c| := by rw [abs_neg]
  refine (tri _ _ _).trans ?_
  have hfin : (2 * T.B * (CA T.toChainParameters * Real.exp (cA T.toChainParameters)) +
      CF * Real.exp cF + C₃ * (((T.n₀ : ℝ) + C₁) ^ 6 * (5040 * (2 / T.gasRate) ^ 7))) / x =
      2 * T.B * (CA T.toChainParameters * (Real.exp (cA T.toChainParameters) / x)) +
      CF * (Real.exp cF / x) +
      C₃ * (((T.n₀ : ℝ) + C₁) ^ 6 * (5040 * (2 / T.gasRate) ^ 7) / x) := by ring
  rw [hfin]
  linarith
end YangMills.Construction.RunningCouplingSlope
end
