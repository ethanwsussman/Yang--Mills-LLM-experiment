import YangMills.Construction.ResponseInTheExpansion.GradientsUnderTheMaxwellForm
import YangMills.Construction.ResponseInTheExpansion.KernelOfALowSymbol
import YangMills.Construction.ResponseInTheExpansion.TheMaxwellCovarianceAtLongDistance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields LinearResponse WeightedResponses RenormalizationStepParameters
open Classical
private theorem holdsOnParameters_of_two {P Q S : ParameterAssignment → ℝ → Prop}
    (h : ∀ T y, T.Admissible → P T y → Q T y → S T y) (hP : HoldsOnParameterFamilies P)
    (hQ : HoldsOnParameterFamilies Q) :
    HoldsOnParameterFamilies S := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLge T hTa hTL hD hCS hOn hrt hC
  obtain ⟨y₁, G₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hLge) T hTa hTL hD hCS hOn
    (le_trans hrt (min_le_left _ _)) (le_trans (le_max_left _ _) hC)
  obtain ⟨y₂, G₂⟩ := H₂ L hL (le_trans (le_max_right _ _) hLge) T hTa hTL hD hCS hOn
    (le_trans hrt (min_le_right _ _)) (le_trans (le_max_right _ _) hC)
  exact ⟨max y₁ y₂, fun y hy hR hW => h T y hD (G₁ y (le_trans (le_max_left _ _) hy) hR hW)
    (G₂ y (le_trans (le_max_right _ _) hy) hR hW)⟩
section CovarianceBound
variable {m : ℕ} [NeZero m] {a : ℝ} {L k : ℕ} {c : ℝ} {K : TorusPlaquette m → TorusPlaquette m → ℝ}
private def pairing (K : TorusPlaquette m → TorusPlaquette m → ℝ) (h : TorusPlaquette m → ℝ) : ℝ :=
  ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
    ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), h p * K p p' * h p'
private theorem pairing_nonneg (hK : IsMaxwellCovariance a L k K) (h : TorusPlaquette m → ℝ) :
    0 ≤ pairing K h := by
  have h0 := (hK.2 h).1 ⟨0, rfl⟩
  have hz : maxwellDefect a L k h 0 = 0 := by
    simp [maxwellDefect, maxwellForm, curl]
  rw [hz] at h0
  exact h0
private theorem pairing_le (hc : 0 < c)
    (hQ : ∀ A : TorusBond m → ℝ, 2 * c * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2 ≤
      maxwellForm a L k A A)
    (hK : IsMaxwellCovariance a L k K) (h : TorusPlaquette m → ℝ) :
    pairing K h ≤ (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), h p ^ 2) / (2 * c) := by
  refine (hK.2 h).2 ?_
  rintro _ ⟨A, rfl⟩
  have h1 : maxwellDefect a L k h A ≤
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), (2 * (h p * curl A p) - 2 * c * curl A p ^ 2) := by
    have := hQ A
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold maxwellDefect
    linarith
  refine h1.trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (h p - 2 * c * curl A p)]
private theorem sum_indicator_sq {p : TorusPlaquette m} (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m))) :
    ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), (if q = p then (1 : ℝ) else 0) ^ 2 = 1 := by
  simp [hp, ite_pow]
private theorem pairing_polarization (hs : ∀ p p', K p p' = K p' p) {p p' : TorusPlaquette m}
    (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)))
    (hp' : p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m))) :
    pairing K (fun q => (if q = p then 1 else 0) + (if q = p' then 1 else 0)) -
      pairing K (fun q => (if q = p then 1 else 0) - (if q = p' then 1 else 0)) = 4 * K p p' := by
  have e : ∀ q q' : TorusPlaquette m,
      ((if q = p then (1 : ℝ) else 0) + (if q = p' then 1 else 0)) * K q q' *
          ((if q' = p then 1 else 0) + (if q' = p' then 1 else 0)) -
        ((if q = p then (1 : ℝ) else 0) - (if q = p' then 1 else 0)) * K q q' *
          ((if q' = p then 1 else 0) - (if q' = p' then 1 else 0)) =
      2 * ((if q = p then 1 else 0) * ((if q' = p' then 1 else 0) * K q q')) +
        2 * ((if q = p' then 1 else 0) * ((if q' = p then 1 else 0) * K q q')) := by
    intro q q'; ring
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, e, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [Finset.sum_ite_eq', hp, hp', ite_mul]
  rw [hs p' p]
  ring
private theorem abs_covariance_le (hc : 0 < c)
    (hQ : ∀ A : TorusBond m → ℝ, 2 * c * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2 ≤
      maxwellForm a L k A A)
    (hK : IsMaxwellCovariance a L k K) {p p' : TorusPlaquette m}
    (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)))
    (hp' : p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m))) :
    |K p p'| ≤ 1 / (2 * c) := by
  have hpol := pairing_polarization hK.1 hp hp'
  have hu := sum_indicator_sq hp
  have hv := sum_indicator_sq hp'
  have sq1 : ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
      ((if q = p then (1 : ℝ) else 0) + (if q = p' then 1 else 0)) ^ 2 ≤ 4 := by
    calc _ ≤ ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
          (2 * (if q = p then (1 : ℝ) else 0) ^ 2 + 2 * (if q = p' then (1 : ℝ) else 0) ^ 2) :=
          Finset.sum_le_sum fun q _ => by
            nlinarith [sq_nonneg ((if q = p then (1 : ℝ) else 0) - (if q = p' then 1 else 0))]
      _ = 4 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu, hv]; norm_num
  have sq2 : ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
      ((if q = p then (1 : ℝ) else 0) - (if q = p' then 1 else 0)) ^ 2 ≤ 4 := by
    calc _ ≤ ∑ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
          (2 * (if q = p then (1 : ℝ) else 0) ^ 2 + 2 * (if q = p' then (1 : ℝ) else 0) ^ 2) :=
          Finset.sum_le_sum fun q _ => by
            nlinarith [sq_nonneg ((if q = p then (1 : ℝ) else 0) + (if q = p' then 1 else 0))]
      _ = 4 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu, hv]; norm_num
  have pos : 0 < 2 * c := by positivity
  have up1 := pairing_le hc hQ hK (fun q => (if q = p then 1 else 0) + (if q = p' then 1 else 0))
  have up2 := pairing_le hc hQ hK (fun q => (if q = p then 1 else 0) - (if q = p' then 1 else 0))
  have lo1 := pairing_nonneg hK (fun q => (if q = p then 1 else 0) + (if q = p' then 1 else 0))
  have lo2 := pairing_nonneg hK (fun q => (if q = p then 1 else 0) - (if q = p' then 1 else 0))
  have b1 := up1.trans (div_le_div_of_nonneg_right sq1 pos.le)
  have b2 := up2.trans (div_le_div_of_nonneg_right sq2 pos.le)
  have e4 : (4 : ℝ) / (2 * c) = 4 * (1 / (2 * c)) := by ring
  rw [e4] at b1 b2
  rw [abs_le]
  constructor <;> linarith
end CovarianceBound
private theorem abs_hyperplaneReflection_le {z : Fin 4 → ℝ} (hz : 1 ≤ sqNorm z) (i j : Fin 4) :
    |hyperplaneReflection z i j| ≤ 3 := by
  have hs : 0 < sqNorm z := by linarith
  have hi : ∀ l, z l ^ 2 ≤ sqNorm z := fun l =>
    Finset.single_le_sum (f := fun i => z i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ l)
  have hprod : |2 * z i * z j / sqNorm z| ≤ 2 := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs, abs_le]
    constructor <;> nlinarith [hi i, hi j, sq_nonneg (z i - z j), sq_nonneg (z i + z j)]
  unfold hyperplaneReflection
  have h1 : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  calc _ ≤ |(if i = j then (1 : ℝ) else 0)| + |2 * z i * z j / sqNorm z| := abs_sub _ _
    _ ≤ 3 := by linarith
private theorem abs_continuumCurvatureKernel_le {z : Fin 4 → ℝ} (hz : 1 ≤ sqNorm z) (μ ν ρ τ : Fin 4) :
    |continuumCurvatureKernel z μ ν ρ τ| ≤ 18 := by
  have hnum : |hyperplaneReflection z μ ρ * hyperplaneReflection z ν τ -
      hyperplaneReflection z μ τ * hyperplaneReflection z ν ρ| ≤ 18 := by
    have a1 : |hyperplaneReflection z μ ρ * hyperplaneReflection z ν τ| ≤ 9 := by
      rw [abs_mul]; nlinarith [abs_hyperplaneReflection_le hz μ ρ, abs_hyperplaneReflection_le hz ν τ,
        abs_nonneg (hyperplaneReflection z μ ρ), abs_nonneg (hyperplaneReflection z ν τ)]
    have a2 : |hyperplaneReflection z μ τ * hyperplaneReflection z ν ρ| ≤ 9 := by
      rw [abs_mul]; nlinarith [abs_hyperplaneReflection_le hz μ τ, abs_hyperplaneReflection_le hz ν ρ,
        abs_nonneg (hyperplaneReflection z μ τ), abs_nonneg (hyperplaneReflection z ν ρ)]
    exact (abs_sub _ _).trans (by linarith)
  have hden : 1 ≤ Real.pi ^ 2 * sqNorm z ^ 2 := by
    have hp : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hq : (1 : ℝ) ≤ sqNorm z ^ 2 := by nlinarith
    nlinarith
  unfold continuumCurvatureKernel
  rw [abs_div, abs_of_pos (by linarith : 0 < Real.pi ^ 2 * sqNorm z ^ 2)]
  exact (div_le_self (abs_nonneg _) hden).trans hnum
private theorem plaquetteCentreDisplacement_eq {N : ℕ} (p p' : TorusPlaquette N) (i : Fin 4) :
    ∃ w : ℤ, plaquetteCentreDisplacement p p' i = w + ((if i = p'.2.1 then 1 else 0) +
      (if i = p'.2.2 then 1 else 0) - (if i = p.2.1 then 1 else 0) - (if i = p.2.2 then 1 else 0)) / 2 := by
  refine ⟨((p'.1 i).val : ℤ) - ((p.1 i).val : ℤ) -
    (N : ℤ) * round ((((p'.1 i).val : ℝ) - ((p.1 i).val : ℝ)) / (N : ℝ)), ?_⟩
  simp only [plaquetteCentreDisplacement, torusDisplacement, circleSub]
  push_cast
  ring
theorem maxwellCovarianceLongDistance_holds (hG : gradientMaxwellStatement)
    (hS : maxwellSymbolStatement) (hK : lowSymbolKernelStatement) :
    maxwellCovarianceLongDistanceStatement := by
  refine holdsOnParameters_of_two (fun Tb y hD hg hs => ?_) hG hS
  obtain ⟨B, C, c, hc, H⟩ := hs
  obtain ⟨C', N₀, hK'⟩ := hK B C c c hc hc
  have hcK := hD.cK_pos
  set M : ℝ := max N₀ 1 with hMdef
  have hM : 1 ≤ M := le_max_right _ _
  refine ⟨|C'| + (1 / (2 * Tb.coercivity) + 18) * M ^ 4, ?_⟩
  intro k N _ hN K hCov p hp p' hp' h1 h2
  set z := plaquetteCentreDisplacement p p' with hz
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hrp : 0 ≤ sqNorm z ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hNp : 0 ≤ (N : ℝ) ^ (-(4 : ℤ)) := by positivity
  have hE : 0 ≤ sqNorm z ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ)) := by linarith
  have hW : 0 ≤ (1 / (2 * Tb.coercivity) + 18) * M ^ 4 := by positivity
  by_cases hbig : N₀ ≤ (N : ℝ)
  · obtain ⟨hd, ht, hl, hlo, hsum⟩ := H k N hN
    have low : IsLowMomentumSymbol B C c (Real.exp (-(c * (N : ℝ))))
        (maxwellSymbol Tb.coupling (Tb.stepParameters y).side k N) :=
      ⟨fun r μ ν => (hd r μ ν 0).1, ht, fun r μ ν q => (hd r μ ν q).2, hl, hlo⟩
    have hμ : p.2.1 < p.2.2 := (Finset.mem_filter.mp hp).2.1
    have hρ : p'.2.1 < p'.2.2 := (Finset.mem_filter.mp hp').2.1
    have key := hK' N _ _ p.2.1 p.2.2 p'.2.1 p'.2.2 z hbig (Real.exp_pos _).le le_rfl low hμ hρ
      (plaquetteCentreDisplacement_eq p p') h1 h2
    rw [← hsum K hCov p hp p' hp', ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at key
    calc _ ≤ _ := key
      _ ≤ |C'| * _ := mul_le_mul_of_nonneg_right (le_abs_self _) hE
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE
  · rw [not_le] at hbig
    have hNM : (N : ℝ) ≤ M := hbig.le.trans (le_max_left _ _)
    have hlow : 1 ≤ M ^ 4 * (N : ℝ) ^ (-(4 : ℤ)) := by
      rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have : ((N : ℝ) ^ (4 : ℤ)) = (N : ℝ) ^ 4 := by norm_cast
      rw [this, one_mul]
      exact pow_le_pow_left₀ hNpos.le hNM 4
    have hb1 := abs_covariance_le hcK (fun A => ((hg k N hN).2.2 A)) hCov hp hp'
    have hb2 := abs_continuumCurvatureKernel_le h1 p.2.1 p.2.2 p'.2.1 p'.2.2
    have hsum : |K p p' - continuumCurvatureKernel z p.2.1 p.2.2 p'.2.1 p'.2.2| ≤ 1 / (2 * Tb.coercivity) + 18 :=
      (abs_sub _ _).trans (by linarith)
    have hA : 0 ≤ 1 / (2 * Tb.coercivity) + 18 := by positivity
    calc _ ≤ _ := hsum
      _ ≤ (1 / (2 * Tb.coercivity) + 18) * (M ^ 4 * (N : ℝ) ^ (-(4 : ℤ))) := le_mul_of_one_le_right hA hlow
      _ = ((1 / (2 * Tb.coercivity) + 18) * M ^ 4) * (N : ℝ) ^ (-(4 : ℤ)) := by ring
      _ ≤ ((1 / (2 * Tb.coercivity) + 18) * M ^ 4) * (sqNorm z ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hW
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C']) hE
end YangMills.Construction.ResponseInTheExpansion
end
