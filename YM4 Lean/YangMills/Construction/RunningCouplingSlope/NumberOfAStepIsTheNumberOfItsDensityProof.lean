import YangMills.Construction.ColdStepAtMirrorFrames.TopOfTheCurvedChainOnATorus
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParametersProof
import YangMills.Construction.RunningCouplingSlope.NumberOfAStepIsTheNumberOfItsDensity
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsTheSumOfItsDensity
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepReadsNoBoundProof
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotalProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters SlopeCoefficient ReferenceDensity
namespace RunningCouplingSlope
variable {n : ℕ}
private def withRate (ℓ : StepParameters) (r : ℝ) : StepParameters := { ℓ with rt := r }
private theorem admissible_withRate {ℓ : StepParameters} (h : ℓ.Admissible) {r : ℝ} (hr : 0 < r) :
    (withRate ℓ r).Admissible :=
  ⟨h.a_ge, h.L_odd, h.L_ge, h.σ_pos, h.κ_pos, h.κ_le, h.κ₁_pos, hr, h.n₁_pos, h.E_pos, h.E_ge, h.depth_lt, h.E₃_pos,
    h.B_pos, h.Cder_ge, h.n₀_ge, h.y₁_ge, h.range_ge⟩
private theorem exists_polyWeight_mul_exp_le (n₁ c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, max 1 (((m : ℝ) / n₁) ^ 16000) * Real.exp (-(c * m)) ≤ K := by
  have hq0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hq : |Real.exp (-c)| < 1 := by
    rw [abs_of_nonneg hq0]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 16000 hq
  obtain ⟨B, hB⟩ := ht.bddAbove_range
  have hB' : ∀ m : ℕ, (m : ℝ) ^ 16000 * Real.exp (-c) ^ m ≤ B := fun m => hB (Set.mem_range_self m)
  have hD : 0 ≤ (1 / n₁) ^ 16000 := Even.pow_nonneg (by decide) _
  have hB0 : 0 ≤ B := le_trans (mul_nonneg (pow_nonneg (Nat.cast_nonneg 1) _) (pow_nonneg hq0 1)) (hB' 1)
  refine ⟨1 + (1 / n₁) ^ 16000 * B, add_pos_of_pos_of_nonneg one_pos (mul_nonneg hD hB0), fun m => ?_⟩
  have he : Real.exp (-(c * m)) = Real.exp (-c) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he1 : Real.exp (-(c * m)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 : 0 ≤ Real.exp (-(c * m)) := (Real.exp_pos _).le
  have hA : 0 ≤ ((m : ℝ) / n₁) ^ 16000 := Even.pow_nonneg (by decide) _
  have hmax : max 1 (((m : ℝ) / n₁) ^ 16000) ≤ 1 + ((m : ℝ) / n₁) ^ 16000 :=
    max_le (by linarith) (by linarith)
  have hprod : ((m : ℝ) / n₁) ^ 16000 * Real.exp (-(c * m)) ≤ (1 / n₁) ^ 16000 * B := by
    have e : ((m : ℝ) / n₁) ^ 16000 = (1 / n₁) ^ 16000 * (m : ℝ) ^ 16000 := by
      rw [← mul_pow]
      congr 1
      ring
    rw [e, mul_assoc, he]
    exact mul_le_mul_of_nonneg_left (hB' m) hD
  calc max 1 (((m : ℝ) / n₁) ^ 16000) * Real.exp (-(c * m))
      ≤ (1 + ((m : ℝ) / n₁) ^ 16000) * Real.exp (-(c * m)) :=
        mul_le_mul_of_nonneg_right hmax he0
    _ = Real.exp (-(c * m)) + ((m : ℝ) / n₁) ^ 16000 * Real.exp (-(c * m)) := by ring
    _ ≤ 1 + (1 / n₁) ^ 16000 * B := add_le_add he1 hprod
private theorem mixedDeriv_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) :
    mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
private theorem mixedDeriv_sub_const {k : ℕ} (hk : 1 ≤ k) (G : TorusField n → ℝ) (κ : ℝ) (W : TorusField n)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (h : ContDiffAt ℝ k (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv (fun V => G V - κ) W c X = mixedDeriv G W c X := by apply _root_.YangMills.SharedProofs.p1322 <;> assumption
private theorem isCold_trivialField {s : ℝ} (hs : 0 < s) (n : ℕ) : TorusFields.IsCold s (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
private theorem exists_isCurvatureFamily_withRate {ℓ : StepParameters} {c C : ℝ} {h : LocalDensity}
    (hf : ℓ.Admissible) (hc : 0 < c) (hC : 0 < C)
    (H : HasStepDensityBounds ℓ.threshold ℓ c C h) :
    ∃ Ch : ℝ, IsCurvatureFamily (withRate ℓ (c * 2 ^ 9)) Ch h := by
  obtain ⟨K, hK, hb⟩ := exists_polyWeight_mul_exp_le ℓ.n₁ (c / 2) (by linarith)
  have hn : 64 ≤ ℓ.n₀ := le_trans (by norm_num) hf.n₀_ge
  have hw : ∀ m : ℕ, 2 * (C * Real.exp (-(c * m))) ≤ 2 * C * K / (withRate ℓ (c * 2 ^ 9)).weight m := by
    intro m
    have hpos : 0 < (withRate ℓ (c * 2 ^ 9)).weight m := by
      unfold StepParameters.weight
      exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
    rw [le_div_iff₀ hpos]
    have e : Real.exp (-(c * m)) * (withRate ℓ (c * 2 ^ 9)).weight m =
        max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) * Real.exp (-(c / 2 * m)) := by
      show Real.exp (-(c * m)) * (max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) * Real.exp (c * 2 ^ 9 / 2 ^ 10 * m)) = _
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    have := hb m
    calc 2 * (C * Real.exp (-(c * m))) * (withRate ℓ (c * 2 ^ 9)).weight m
        = 2 * C * (Real.exp (-(c * m)) * (withRate ℓ (c * 2 ^ 9)).weight m) := by ring
      _ ≤ 2 * C * K := by
        rw [e]
        exact mul_le_mul_of_nonneg_left this (by positivity)
  have hexp : ∀ m : ℕ, 0 ≤ C * Real.exp (-(c * m)) := fun m => by positivity
  refine ⟨2 * C * K, fun n _ hn' y W hW => H.admissible.smooth n (le_trans hn hn') y W hW,
    fun n _ hn' y g W hW => H.admissible.gauge n (le_trans hn hn') y g W hW,
    fun n _ hn' y u W hW => H.admissible.translation n (le_trans hn hn') y u W hW, ?_, ?_⟩
  · intro n _ hn' y W hW k cc X k1 k3 hX
    have b := H.decay n (le_trans hn hn') y W hW k cc X k1 k3 hX
    have b' : |mixedDeriv (h n y) W cc X| ≤ C * Real.exp (-(c * (supportDiam y cc : ℕ))) := b
    exact b'.trans (by linarith [hw (supportDiam y cc), hexp (supportDiam y cc)])
  · intro n n' _ _ hn' hn'' y y' W W' m h1 h2 hW hW' hA k b X hk hb' hX
    have l1 : 64 ≤ n := le_trans hn hn'
    have l2 : 64 ≤ n' := le_trans hn hn''
    have e1 := H.local_comparison n n' l1 l2 y y' W W' m h1 h2 hW hW' hA k b X hk hb' hX
    have e1' : |mixedDeriv (h n y) W (fun l => bondFrom y (b l)) X -
        mixedDeriv (h n' y') W' (fun l => bondFrom y' (b l)) X| ≤
        C * Real.exp (-(c * (m : ℕ))) := e1
    refine le_trans ?_ (hw m)
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hfl : TorusFields.IsCold ℓ.threshold (trivialField n) := isCold_trivialField hf.σ_pos n
      have hfl' : TorusFields.IsCold ℓ.threshold (trivialField n') := isCold_trivialField hf.σ_pos n'
      have e2 := H.local_comparison n n' l1 l2 y y' (trivialField n) (trivialField n') m h1 h2 hfl hfl'
        (fun _ _ => rfl) 0 b X hk hb' hX
      have e2' : |mixedDeriv (h n y) (trivialField n) (fun l => bondFrom y (b l)) X -
          mixedDeriv (h n' y') (trivialField n') (fun l => bondFrom y' (b l)) X| ≤
          C * Real.exp (-(c * (m : ℕ))) := e2
      rw [mixedDeriv_zero, mixedDeriv_zero] at e1' e2' ⊢
      unfold centered
      rw [abs_le] at e1' e2' ⊢
      constructor <;> linarith [e1'.1, e1'.2, e2'.1, e2'.2]
    · have s1 : ContDiffAt ℝ k
          (fun σ : Fin k → ℝ => h n y (perturb (fun l => bondFrom y (b l)) X σ W)) 0 :=
        (H.admissible.smooth n l1 y W hW k _ X).of_le (by exact_mod_cast (by omega : k ≤ 3))
      have s2 : ContDiffAt ℝ k
          (fun σ : Fin k → ℝ => h n' y' (perturb (fun l => bondFrom y' (b l)) X σ W')) 0 :=
        (H.admissible.smooth n' l2 y' W' hW' k _ X).of_le (by exact_mod_cast (by omega : k ≤ 3))
      have a1 : mixedDeriv (centered h n y) W (fun l => bondFrom y (b l)) X =
          mixedDeriv (h n y) W (fun l => bondFrom y (b l)) X := mixedDeriv_sub_const hk1 (h n y) _ W _ X s1
      have a2 : mixedDeriv (centered h n' y') W' (fun l => bondFrom y' (b l)) X =
          mixedDeriv (h n' y') W' (fun l => bondFrom y' (b l)) X :=
        mixedDeriv_sub_const hk1 (h n' y') _ W' _ X s2
      rw [a1, a2]
      linarith [hexp m]
private theorem minimizingCoordinates_eq (hLC : MinimizingChartUnique) {F : BlockFrame} {a ρ₀ ρ N0 s : ℝ}
    {V : F.GaugeField F.top}
    (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (h0 : ρ₀ ≤ 1) (h1 : ρ ≤ 1) (hρ : N0 * s ≤ ρ)
    (H : HasColdMinimizer a ρ₀ N0 s (finiteCells F) V) :
    minimizingCoordinates a (finiteCells F) V ρ = minimizingCoordinates a (finiteCells F) V ρ₀ := by
  obtain ⟨w, hw, hcold, hu⟩ := H
  have mono : ∀ {r r' : ℝ} {w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}, r ≤ r' →
      IsMinimizingChart a (finiteCells F) V r w' → IsMinimizingChart a (finiteCells F) V r' w' :=
    fun hr h => ⟨h.1, fun b hb => (h.2.1 b hb).trans hr, h.2.2⟩
  have H1 : HasColdMinimizer a 1 N0 s (finiteCells F) V :=
    ⟨w, mono (min_le_min_right _ h0) hw, hcold, hu⟩
  have hw1 : IsMinimizingChart a (finiteCells F) V 1 w := mono ((min_le_left _ _).trans h0) hw
  obtain ⟨u, -⟩ := hLC F a 1 N0 s V w hodd hs le_rfl H1 hw1
  have key : ∀ r : ℝ, min ρ₀ (N0 * s) ≤ r → r ≤ 1 → minimizingCoordinates a (finiteCells F) V r = w := by
    intro r hr hr1
    have hex : ∃ w', IsMinimizingChart a (finiteCells F) V r w' := ⟨w, mono hr hw⟩
    have hsp : IsMinimizingChart a (finiteCells F) V r (minimizingCoordinates a (finiteCells F) V r) := by
      unfold minimizingCoordinates
      rw [dif_pos hex]
      exact hex.choose_spec
    exact u _ (mono hr1 hsp)
  rw [key ρ ((min_le_right _ _).trans hρ) h1, key ρ₀ (min_le_left _ _) h0]
private theorem stepLogAmplitude_congr {F : BlockFrame} {a ρ ρ' : ℝ} {V : F.GaugeField F.top}
    (h : minimizingCoordinates a (finiteCells F) V ρ = minimizingCoordinates a (finiteCells F) V ρ') :
    stepLogAmplitude (F := F) a ρ V = stepLogAmplitude (F := F) a ρ' V := by apply _root_.YangMills.SharedProofs.p40020 <;> assumption
private theorem stepGaugeTotal_eq (hLC : MinimizingChartUnique) {T : ParameterAssignment} (hT : T.Admissible) (t : ℕ)
    [NeZero n] (h64 : 64 ≤ n) {ρ s : ℝ} (h1 : ρ ≤ 1) (hs0 : 0 < s) (hsA : s ≤ T.σA) (hρ : T.N 0 * s ≤ ρ)
    {V : TorusField n} (hV : TorusFields.IsCold s V) :
    stepGaugeTotal T.coupling ρ T.side t n V = stepGaugeTotal T.coupling T.ρA T.side t n V := by
  obtain ⟨-, -, -, -, hρA, -, -, -, hmain⟩ := hT.chain
  have hside : ∀ i, (torusFrame T.side t n).extent i = n := fun _ => rfl
  have hpos : ∀ i, 0 < (torusFrame T.side t n).extent i := fun i => by
    rw [hside]
    omega
  have at_field : ∀ U : TorusField n, TorusFields.IsCold s U →
      stepLogAmplitude (F := torusFrame T.side t n) T.coupling ρ
          (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top U) =
        stepLogAmplitude (F := torusFrame T.side t n) T.coupling T.ρA
          (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top U) := by
    intro U hU
    have hc : BlockAverages.IsCold (finiteCells (torusFrame T.side t n)) (torusFrame T.side t n).top s
        (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top U) :=
      TopLevelSites.isCold_readAtLevel hside hU
    have hO := (hmain (torusFrame T.side t n) 1024 (finiteCells _) rfl
      (Or.inr fun i => by rw [hside]; exact h64)
      le_rfl (TopLevelSites.isOrthantRegular_finiteCells hpos 1024) s _ hs0 hsA hc).1
    exact stepLogAmplitude_congr
      (minimizingCoordinates_eq hLC hT.L_odd (fun i => by rw [hside]; omega) hρA h1 hρ hO)
  unfold stepGaugeTotal
  rw [at_field V hV, at_field (trivialField n) (isCold_trivialField hs0 n)]
private theorem exists_conj_quaternionI_of (a b c : ℝ) (hn : a ^ 2 + b ^ 2 + c ^ 2 = 1) (X : imaginaryQuaternions)
    (hx : (X : ℍ[ℝ]).imI = a ^ 2 - b ^ 2 - c ^ 2) (hy : (X : ℍ[ℝ]).imJ = 2 * a * c)
    (hz : (X : ℍ[ℝ]).imK = - (2 * a * b)) :
    ∃ g : UnitQuaternion, (g : ℍ[ℝ]) * (quaternionI : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (X : ℍ[ℝ]) := by
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  set q : ℍ[ℝ] := ⟨a, 0, b, c⟩ with hq
  have hs : Quaternion.normSq q = 1 := by
    rw [Quaternion.normSq_def']
    simp only [hq]
    nlinarith
  have hu : q ∈ unitary ℍ[ℝ] := by
    rw [Unitary.mem_iff]
    constructor
    · rw [Quaternion.star_mul_self, hs]
      simp
    · rw [Quaternion.self_mul_star, hs]
      simp
  refine ⟨⟨q, hu⟩, ?_⟩
  have hi : (((⟨q, hu⟩ : UnitQuaternion)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star q := rfl
  rw [hi]
  change q * (quaternionI : ℍ[ℝ]) * star q = _
  have hqr : q.re = a := rfl
  have hqi : q.imI = 0 := rfl
  have hqj : q.imJ = b := rfl
  have hqk : q.imK = c := rfl
  have hur : (quaternionI : ℍ[ℝ]).re = 0 := rfl
  have hui : (quaternionI : ℍ[ℝ]).imI = 1 := rfl
  have huj : (quaternionI : ℍ[ℝ]).imJ = 0 := rfl
  have huk : (quaternionI : ℍ[ℝ]).imK = 0 := rfl
  ext
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, hqr, hqi, hqj, hqk, hur, hui, huj, huk, hre]
    ring
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, hqr, hqi, hqj, hqk, hur, hui, huj, huk, hx]
    ring
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, hqr, hqi, hqj, hqk, hur, hui, huj, huk, hy]
    ring
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, hqr, hqi, hqj, hqk, hur, hui, huj, huk, hz]
    ring
private theorem exists_conj_quaternionI (X : imaginaryQuaternions) (hX : ‖X‖ = 1) :
    ∃ g : UnitQuaternion, (g : ℍ[ℝ]) * (quaternionI : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (X : ℍ[ℝ]) := by
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  set x := (X : ℍ[ℝ]).imI with hx
  set y := (X : ℍ[ℝ]).imJ with hy
  set z := (X : ℍ[ℝ]).imK with hz
  have hN : x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
    have h1 : ‖(X : ℍ[ℝ])‖ = 1 := hX
    have h2 : Quaternion.normSq (X : ℍ[ℝ]) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, h1]
      norm_num
    rw [Quaternion.normSq_def', hre] at h2
    nlinarith
  have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg z]
  rcases hx1.eq_or_lt with h | h
  · have hy0 : y = 0 := by nlinarith [sq_nonneg y, sq_nonneg z]
    have hz0 : z = 0 := by nlinarith [sq_nonneg y, sq_nonneg z]
    exact exists_conj_quaternionI_of 0 1 0 (by norm_num) X (by rw [← hx, ← h]; norm_num)
      (by rw [← hy, hy0]; norm_num) (by rw [← hz, hz0]; norm_num)
  · have hp : 0 < 1 + x := by linarith
    set r := Real.sqrt (2 * (1 + x)) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 (by linarith)
    have hr2 : r ^ 2 = 2 * (1 + x) := Real.sq_sqrt (by linarith)
    have hrn : r ≠ 0 := hr0.ne'
    refine exists_conj_quaternionI_of ((1 + x) / r) (- z / r) (y / r) ?_ X ?_ ?_ ?_
    · rw [div_pow, div_pow, div_pow, hr2]
      field_simp
      nlinarith
    · rw [div_pow, div_pow, div_pow, hr2, ← hx]
      field_simp
      nlinarith
    · rw [← hy]
      have : 2 * ((1 + x) / r) * (y / r) = 2 * (1 + x) * y / r ^ 2 := by
        field_simp
      rw [this, hr2]
      field_simp
    · rw [← hz]
      have : 2 * ((1 + x) / r) * (- z / r) = - (2 * (1 + x) * z / r ^ 2) := by
        field_simp
      rw [this, hr2]
      field_simp
private theorem gaugeTransform_abelianFieldOfAngles (g : UnitQuaternion) (X : imaginaryQuaternions) (hX : ‖X‖ = 1)
    (hu : ‖quaternionI‖ = 1)
    (h : (g : ℍ[ℝ]) * (quaternionI : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (X : ℍ[ℝ])) (γ : ℝ)
    (ω : Fin 4 → Fin 4 → ℝ) :
    gaugeTransform (fun _ => g) (abelianFieldOfAngles n quaternionI γ ω) = abelianFieldOfAngles n X γ ω := by
  funext x i
  apply Subtype.ext
  have hgg : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul]
    simp
  have hc : ∀ c : ℝ, ((c : ℝ) : ℍ[ℝ]) = c • (1 : ℍ[ℝ]) := fun c => by ext <;> simp
  change (g : ℍ[ℝ]) * ((expUnit (totalAngle γ ω x i • quaternionI) : UnitQuaternion) : ℍ[ℝ]) *
      ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
    ((expUnit (totalAngle γ ω x i • X) : UnitQuaternion) : ℍ[ℝ])
  rw [coe_expUnit_smul quaternionI hu, coe_expUnit_smul X hX, hc, ← h]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, hgg]
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private abbrev firstPlane : Fin 4 → Fin 4 → ℝ := planeUnitForm 0 1
private theorem firstPlane_antisymm (i j : Fin 4) : firstPlane i j = - firstPlane j i := by
  unfold firstPlane planeUnitForm
  by_cases h1 : i = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · by_cases h2 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h2
      simp
    · have h1' : ¬ (j = 0 ∧ i = 1) := fun h => h2 ⟨h.2, h.1⟩
      have h2' : ¬ (j = 1 ∧ i = 0) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2, h1', h2']
private theorem firstPlane_values (i j : Fin 4) :
    firstPlane i j = 0 ∨ firstPlane i j = 1 ∨ firstPlane i j = -1 := by
  unfold firstPlane planeUnitForm
  split_ifs <;> simp
private theorem natCast_mul_firstPlane_int (l : ℕ) (i j : Fin 4) : ∃ z : ℤ, (l : ℝ) * firstPlane i j = z := by
  rcases firstPlane_values i j with h | h | h <;> rw [h]
  · exact ⟨0, by simp⟩
  · exact ⟨l, by simp⟩
  · exact ⟨-l, by simp⟩
private theorem abs_firstPlane_le (i j : Fin 4) : |firstPlane i j| ≤ 1 := by
  rcases firstPlane_values i j with h | h | h <;> rw [h] <;> simp
private theorem curvatureAlong_firstPlane : curvatureAlong quaternionI firstPlane = unitPlaneCurvature := by
  funext i j
  unfold curvatureAlong firstPlane planeUnitForm unitPlaneCurvature planeCurvature
  by_cases h1 : i = 0 ∧ j = 1
  · simp [h1]
  · by_cases h2 : i = 1 ∧ j = 0
    · simp only [h2, if_true, and_self]
      have hn : ¬ ((1 : Fin 4) = 0 ∧ (0 : Fin 4) = 1) := by simp
      obtain ⟨rfl, rfl⟩ := h2
      simp only [hn, if_false]
      exact neg_one_smul ℝ (quaternionI : imaginaryQuaternions)
    · simp [h1, h2]
private theorem isCold_of_isAbelianWithCurvature (X : imaginaryQuaternions) (hX : ‖X‖ = 1) {γ s : ℝ}
    (h0 : 0 < γ) (h1 : γ ≤ 1) (h2 : 2 * γ < s)
    {V : TorusField n} (hV : IsAbelianWithCurvature X firstPlane γ V) : TorusFields.IsCold s V := by
  intro x μ ν hμν
  have e := hV.2 x μ ν hμν
  have b := norm_coe_expUnit_smul_sub_one_le X hX (γ * firstPlane μ ν)
  have c : TorusFields.curvature V x μ ν =
      ‖((expUnit ((γ * firstPlane μ ν) • X) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
    unfold TorusFields.curvature
    rw [e]
  rw [c]
  refine lt_of_le_of_lt b ?_
  have q0 := abs_firstPlane_le μ ν
  have q1 : |γ * firstPlane μ ν| ≤ γ := by
    rw [abs_mul, abs_of_pos h0]
    nlinarith
  have q2 : (γ * firstPlane μ ν) ^ 2 ≤ γ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) q1 2
  nlinarith
private theorem eventually_flux_lt (l : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 2 * Real.pi * (l : ℝ) / (m : ℝ) ^ 2 < δ := by
  have h : Tendsto (fun m : ℕ => 2 * Real.pi * (l : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
  exact h.eventually (gt_mem_nhds hδ)
private theorem card_torusSite [NeZero n] : ((Finset.univ : Finset (TorusSite n)).card : ℝ) = (n : ℝ) ^ 4 := by
  rw [Finset.card_univ]
  simp [ZMod.card]
private theorem abs_sum_sub_le [NeZero n] {f : TorusSite n → ℝ} {a e : ℝ} (h : ∀ y, |f y - a| ≤ e) :
    |∑ y, f y - (n : ℝ) ^ 4 * a| ≤ (n : ℝ) ^ 4 * e := by
  have hc := card_torusSite (n := n)
  have : ∑ y, f y - (n : ℝ) ^ 4 * a = ∑ y : TorusSite n, (f y - a) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hc]
  rw [this]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun y _ => h y).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, hc]
theorem stepCoefficientEqualsDensityValue_holds (hD : StepDensityBoundsAtFixedParameters) (hT : StepTotalEqDensitySum)
    (hS : TorusLumps.SecondOrderAtAbelianFields) (hW : AbelianFieldOfAnglesHasCurvature)
    (hC : ConstantCurvatureTopOnTorus) (hLC : MinimizingChartUnique) :
    StepCoefficientEqualsDensityValue := by
  obtain ⟨rt₀, cD, -, hcD, hD⟩ := hD
  intro T hDr t
  obtain ⟨C, hC0, hD⟩ := hD T hDr
  set ℓ := T.stepParameters T.floorMin with hℓ
  have hf : ℓ.Admissible := hDr.fits _ le_rfl
  set h := paramStepDensity T t with hh
  have hB : HasStepDensityBounds ℓ.threshold ℓ (cD T.toChainParameters) C h := hD.1 _ t le_rfl
  have hc := hcD T.toChainParameters
  obtain ⟨Ch, hF⟩ := exists_isCurvatureFamily_withRate hf hc hC0 hB
  set r := cD T.toChainParameters * 2 ^ 9 with hr
  have hf' : (withRate ℓ r).Admissible := admissible_withRate hf (by positivity)
  have hA := hS (withRate ℓ r) hf' Ch h hF
  have hlast := hA.2.2.2.2.2.2.2
  obtain ⟨v, hv, hvε⟩ := hlast firstPlane 1 quaternionI firstPlane_antisymm one_pos
    (natCast_mul_firstPlane_int 1) norm_quaternionI
  rw [curvatureAlong_firstPlane] at hv
  have hσ : 0 < T.threshold := hDr.σ_pos
  have colour : ∀ X : imaginaryQuaternions, ‖X‖ = 1 → ∀ w : ℝ,
      HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit h cc.1 cc.2 (linearPotential (curvatureAlong X firstPlane) cc.1)
          (linearPotential (curvatureAlong X firstPlane) cc.2)) w → w = v := by
    intro X hX w hw
    obtain ⟨w', hw', hwε⟩ := hlast firstPlane 1 X firstPlane_antisymm one_pos (natCast_mul_firstPlane_int 1) hX
    obtain rfl : w' = w := hw'.unique hw
    obtain ⟨g, hg⟩ := exists_conj_quaternionI X hX
    by_contra hne
    have hd : 0 < |w' - v| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n₁, hn₁⟩ := hvε (|w' - v| / 16) (by positivity)
    obtain ⟨n₂, hn₂⟩ := hwε (|w' - v| / 16) (by positivity)
    have hδ : 0 < min 1 (T.threshold / 2) := lt_min one_pos (by linarith)
    obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ := ((eventually_ge_atTop n₁).and ((eventually_ge_atTop n₂).and
      ((eventually_ge_atTop ℓ.n₀).and ((eventually_ge_atTop 1).and (eventually_flux_lt 1 hδ))))).exists
    have : NeZero m := ⟨by omega⟩
    set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (m : ℝ) ^ 2 with hγ
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm4
    have hγ0 : 0 < γ := by
      rw [hγ]
      have := Real.pi_pos
      positivity
    have hγ1 : γ < 1 := lt_of_lt_of_le hm5 (min_le_left _ _)
    have hγ2 : γ < T.threshold / 2 := lt_of_lt_of_le hm5 (min_le_right _ _)
    have hAb : IsAbelianWithCurvature quaternionI firstPlane γ (abelianFieldOfAngles m quaternionI γ firstPlane) :=
      hW m quaternionI firstPlane 1 norm_quaternionI firstPlane_antisymm (natCast_mul_firstPlane_int 1)
    have hAb' : IsAbelianWithCurvature X firstPlane γ (abelianFieldOfAngles m X γ firstPlane) :=
      hW m X firstPlane 1 hX firstPlane_antisymm (natCast_mul_firstPlane_int 1)
    have hcold : TorusFields.IsCold ℓ.threshold (abelianFieldOfAngles m quaternionI γ firstPlane) :=
      isCold_of_isAbelianWithCurvature quaternionI norm_quaternionI hγ0 hγ1.le
        (by show 2 * γ < T.threshold; linarith) hAb
    have hg' := gaugeTransform_abelianFieldOfAngles (n := m) g X hX norm_quaternionI hg γ firstPlane
    have hgauge : h m 0 (abelianFieldOfAngles m X γ firstPlane) =
        h m 0 (abelianFieldOfAngles m quaternionI γ firstPlane) := by
      rw [← hg']
      exact hF.gauge m hm3 0 (fun _ => g) _ hcold
    have hhat : centered h m 0 (abelianFieldOfAngles m X γ firstPlane) =
        centered h m 0 (abelianFieldOfAngles m quaternionI γ firstPlane) := by
      unfold centered
      rw [hgauge]
    have b1 : |centered h m 0 (abelianFieldOfAngles m quaternionI γ firstPlane) - γ ^ 2 / 2 * v| ≤
        |w' - v| / 16 * γ ^ 2 :=
      hn₁ m hm1 _ hAb 0
    have b2 : |centered h m 0 (abelianFieldOfAngles m X γ firstPlane) - γ ^ 2 / 2 * w'| ≤
        |w' - v| / 16 * γ ^ 2 :=
      hn₂ m hm2 _ hAb' 0
    rw [hhat] at b2
    have s3 : |γ ^ 2 / 2 * w' - γ ^ 2 / 2 * v| ≤ 2 * (|w' - v| / 16 * γ ^ 2) := by
      have := abs_sub_le (γ ^ 2 / 2 * w') (centered h m 0 (abelianFieldOfAngles m quaternionI γ firstPlane))
        (γ ^ 2 / 2 * v)
      rw [abs_sub_comm (γ ^ 2 / 2 * w') (centered h m 0 (abelianFieldOfAngles m quaternionI γ firstPlane))] at this
      linarith
    have s4 : γ ^ 2 / 2 * w' - γ ^ 2 / 2 * v = γ ^ 2 / 2 * (w' - v) := by ring
    rw [s4, abs_mul, abs_of_pos (by positivity : 0 < γ ^ 2 / 2)] at s3
    have hp : 0 < γ ^ 2 := by positivity
    nlinarith
  refine ⟨v, ?_, fun c c' X X' => ⟨_, hA.1 c c' X X'⟩, hv⟩
  intro ρ l X hρ0 hρ1 hl hX
  obtain ⟨w, hw, hwε⟩ := hlast firstPlane l X firstPlane_antisymm (by omega) (natCast_mul_firstPlane_int l) hX
  obtain rfl : w = v := colour X hX w (by
    obtain ⟨w₁, hw₁, -⟩ := hlast firstPlane 1 X firstPlane_antisymm one_pos (natCast_mul_firstPlane_int 1) hX
    rw [hw.unique hw₁]
    exact hw₁)
  have hN0 : 0 < T.N 0 := hDr.chain.2.2.2.2.2.2.2.1 0
  have hσA : 0 < T.σA := hDr.chain.2.2.2.2.2.1
  set s := min (min T.σA (ρ / T.N 0)) (9 / 8 * T.threshold) with hs
  have hs0 : 0 < s := lt_min (lt_min hσA (div_pos hρ0 hN0)) (by linarith)
  have hsA : s ≤ T.σA := (min_le_left _ _).trans (min_le_left _ _)
  have hsρ : T.N 0 * s ≤ ρ := by
    have : s ≤ ρ / T.N 0 := (min_le_left _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ hN0] at this
    linarith
  have hs9 : s ≤ 9 / 8 * T.threshold := min_le_right _ _
  have hδ : 0 < min 1 (s / 2) := lt_min one_pos (by linarith)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n₁, hn₁⟩ := hwε (ε / 4) (by linarith)
  filter_upwards [eventually_ge_atTop n₁, eventually_ge_atTop 64, eventually_flux_lt l hδ] with m hm1 hm2 hm3
  have : NeZero m := ⟨by omega⟩
  set γ : ℝ := 2 * Real.pi * (l : ℝ) / (m : ℝ) ^ 2 with hγ
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hγ0 : 0 < γ := by
    rw [hγ]
    have := Real.pi_pos
    positivity
  have hγ1 : γ < 1 := lt_of_lt_of_le hm3 (min_le_left _ _)
  have hγ2 : γ < s / 2 := lt_of_lt_of_le hm3 (min_le_right _ _)
  have hAb : IsAbelianWithCurvature X firstPlane γ (constantCurvatureField T.side t l m X) :=
    hC (torusFrame T.side t m) X 0 1 m l hDr.L_odd (fun _ => rfl) (by omega) hX (by decide) hγ1.le
  have hcold : TorusFields.IsCold s (constantCurvatureField T.side t l m X) :=
    isCold_of_isAbelianWithCurvature X hX hγ0 hγ1.le (by linarith) hAb
  have hcold' : TorusFields.IsCold (9 / 8 * T.threshold) (constantCurvatureField T.side t l m X) :=
    fun x μ ν hμν => lt_of_lt_of_le (hcold x μ ν hμν) hs9
  have e1 := stepGaugeTotal_eq hLC hDr t hm2 hρ1 hs0 hsA hsρ hcold
  have e2 := hT T hDr t m (constantCurvatureField T.side t l m X) hm2 hcold'
  have e3 : centeredDensityTotal (paramStepDensity T t) m (constantCurvatureField T.side t l m X) =
      ∑ y, centered h m y (constantCurvatureField T.side t l m X) := by
    unfold centeredDensityTotal
    rw [dif_neg (NeZero.ne m)]
  have hb0 : ∀ y, |centered h m y (constantCurvatureField T.side t l m X) - γ ^ 2 / 2 * w| ≤ ε / 4 * γ ^ 2 :=
    hn₁ m hm1 _ hAb
  have hb := abs_sum_sub_le hb0
  have hq : curvatureQuotient T.coupling ρ T.side t l m X =
      2 / ((m : ℝ) ^ 4 * γ ^ 2) * ∑ y, centered h m y (constantCurvatureField T.side t l m X) := by
    unfold curvatureQuotient
    rw [e1, ← e2, e3]
    rfl
  rw [hq, Real.dist_eq]
  have hm4 : 0 < (m : ℝ) ^ 4 := by positivity
  have e4 : 2 / ((m : ℝ) ^ 4 * γ ^ 2) * ∑ y, centered h m y (constantCurvatureField T.side t l m X) - w =
      2 / ((m : ℝ) ^ 4 * γ ^ 2) *
        (∑ y, centered h m y (constantCurvatureField T.side t l m X) - (m : ℝ) ^ 4 * (γ ^ 2 / 2 * w)) := by
    field_simp
  rw [e4, abs_mul, abs_of_pos (by positivity : 0 < 2 / ((m : ℝ) ^ 4 * γ ^ 2))]
  calc 2 / ((m : ℝ) ^ 4 * γ ^ 2) *
        |∑ y, centered h m y (constantCurvatureField T.side t l m X) - (m : ℝ) ^ 4 * (γ ^ 2 / 2 * w)|
      ≤ 2 / ((m : ℝ) ^ 4 * γ ^ 2) * ((m : ℝ) ^ 4 * (ε / 4 * γ ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ε / 2 := by
        field_simp
        ring
    _ < ε := by linarith
end RunningCouplingSlope
end YangMills.Construction
end
