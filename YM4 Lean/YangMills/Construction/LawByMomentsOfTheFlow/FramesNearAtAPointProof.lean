import YangMills.Construction.LawByMomentsOfTheFlow.ColoursOfForms
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionOfTheResponse
import YangMills.Construction.LawByMomentsOfTheFlow.FramesNearAtAPoint
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheCurvatureInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.PagesJoin
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields
private theorem exists_coupling_floor (K s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x xu : ℝ, X₀ ≤ x → x / 2 ≤ xu → xu ≤ 2 * x →
      16 ≤ ⌈xu ^ ((1 : ℝ) / 100)⌉₊ / 2 ^ 11 ∧ 64 * x ^ (-(1 / 4) : ℝ) < s ∧
      K * Real.exp (-(δ * ((⌈xu ^ ((1 : ℝ) / 100)⌉₊ / 2 ^ 11 : ℕ) : ℝ))) ≤ x ^ (-2 : ℝ) ∧
      ((4 * (⌈xu ^ ((1 : ℝ) / 100)⌉₊ / 2 ^ 11) + 5 : ℕ) : ℝ) < x ^ ((1 : ℝ) / 2) := by
  have ht : Filter.Tendsto (fun x : ℝ => (x / 2) ^ ((1 : ℝ) / 100)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp (Filter.tendsto_id.atTop_div_const (by norm_num))
  have hp : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 100)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, (17 * 2 ^ 11 : ℝ) ≤ (x / 2) ^ ((1 : ℝ) / 100) := ht.eventually_ge_atTop _
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, x ^ (-(1 / 4) : ℝ) < s / 64 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_lt_const (by positivity))
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, (17 : ℝ) ≤ x ^ ((1 : ℝ) / 100) := hp.eventually_ge_atTop _
  have hw : Filter.Tendsto (fun x : ℝ => δ / 2 ^ 12 * (x / 2) ^ ((1 : ℝ) / 100)) Filter.atTop Filter.atTop :=
    ht.const_mul_atTop (by positivity)
  set Q : ℝ := |K| * 4 * (2 ^ 12 / δ) ^ 200 + 1 with hQ
  have hQ0 : 0 < Q := by positivity
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (δ / 2 ^ 12 * (x / 2) ^ ((1 : ℝ) / 100)) ^ 200 *
      Real.exp (-(δ / 2 ^ 12 * (x / 2) ^ ((1 : ℝ) / 100))) < 1 / Q :=
    hw.eventually ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 200).eventually_lt_const (by positivity))
  have e5 : ∀ᶠ x : ℝ in Filter.atTop, (4 : ℝ) ≤ x := Filter.eventually_ge_atTop 4
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨max x₁ 1, le_max_right _ _, fun x xu hx hxu hxu' => ?_⟩
  obtain ⟨f1, f2, f3, f4, f5⟩ := hx₁ x ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := by linarith
  have hy1 : (x / 2) ^ ((1 : ℝ) / 100) ≤ xu ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow (by positivity) hxu (by norm_num)
  have hxu0 : 0 ≤ xu := by linarith [(by positivity : 0 ≤ x / 2)]
  have hy2 : xu ^ ((1 : ℝ) / 100) ≤ (2 * x) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hxu0 hxu' (by norm_num)
  set y := xu ^ ((1 : ℝ) / 100) with hy
  set c := ⌈y⌉₊ with hc
  have hcy : y ≤ c := Nat.le_ceil y
  have hy0 : 0 ≤ y := by positivity
  have hcy2 : (c : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hm16 : 17 ≤ c / 2 ^ 11 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : (17 * 2 ^ 11 : ℝ) ≤ c := f1.trans (hy1.trans hcy)
    exact_mod_cast this
  have hmlow : (c : ℝ) / 2 ^ 11 - 1 ≤ ((c / 2 ^ 11 : ℕ) : ℝ) := by
    have h1 := Nat.lt_div_mul_add (a := c) (b := 2 ^ 11) (by norm_num)
    have h2 : (c : ℝ) < ((c / 2 ^ 11 : ℕ) : ℝ) * 2 ^ 11 + 2 ^ 11 := by exact_mod_cast h1
    rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]
    nlinarith
  have hmhigh : ((c / 2 ^ 11 : ℕ) : ℝ) ≤ c := by exact_mod_cast Nat.div_le_self _ _
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have := mul_lt_mul_of_pos_left f2 (by norm_num : (0 : ℝ) < 64)
    have e : 64 * (s / 64) = s := by ring
    linarith
  · set t := (x / 2) ^ ((1 : ℝ) / 100) with htd
    have hmt : t / 2 ^ 12 ≤ ((c / 2 ^ 11 : ℕ) : ℝ) := by
      have h1 : t / 2 ^ 11 - 1 ≤ (c : ℝ) / 2 ^ 11 - 1 := by
        have : t ≤ c := hy1.trans hcy
        linarith
      have h2 : t / 2 ^ 12 ≤ t / 2 ^ 11 - 1 := by
        have : (17 * 2 ^ 11 : ℝ) ≤ t := f1
        norm_num at this ⊢
        linarith
      linarith
    have hexp : Real.exp (-(δ * ((c / 2 ^ 11 : ℕ) : ℝ))) ≤ Real.exp (-(δ / 2 ^ 12 * t)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hmt hδ.le
      have e : δ * (t / 2 ^ 12) = δ / 2 ^ 12 * t := by ring
      linarith
    have hxt : x = 2 * t ^ 100 := by
      have : t ^ 100 = x / 2 := by
        rw [htd, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [this]
      ring
    have hlhs : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx0.le]
      norm_num
    rw [hlhs]
    have hw4 : (δ / 2 ^ 12 * t) ^ 200 * Real.exp (-(δ / 2 ^ 12 * t)) < 1 / Q := f4
    have hx2 : x ^ 2 = 4 * (2 ^ 12 / δ) ^ 200 * (δ / 2 ^ 12 * t) ^ 200 := by
      rw [hxt]
      have h1 : (2 ^ 12 / δ) ^ 200 * (δ / 2 ^ 12 * t) ^ 200 = t ^ 200 := by
        rw [← mul_pow]
        congr 1
        field_simp
      have e : 4 * (2 ^ 12 / δ) ^ 200 * (δ / 2 ^ 12 * t) ^ 200 = 4 * ((2 ^ 12 / δ) ^ 200 * (δ / 2 ^ 12 * t) ^ 200) := by ring
      rw [e, h1]
      ring
    have hkey : |K| * x ^ 2 * Real.exp (-(δ / 2 ^ 12 * t)) ≤ 1 := by
      rw [hx2]
      have hq := (lt_div_iff₀ hQ0).1 hw4
      have hW0 : 0 ≤ (δ / 2 ^ 12 * t) ^ 200 * Real.exp (-(δ / 2 ^ 12 * t)) := by positivity
      have e : |K| * (4 * (2 ^ 12 / δ) ^ 200 * (δ / 2 ^ 12 * t) ^ 200) * Real.exp (-(δ / 2 ^ 12 * t)) =
          (|K| * 4 * (2 ^ 12 / δ) ^ 200) * ((δ / 2 ^ 12 * t) ^ 200 * Real.exp (-(δ / 2 ^ 12 * t))) := by ring
      rw [e]
      have : (|K| * 4 * (2 ^ 12 / δ) ^ 200) * ((δ / 2 ^ 12 * t) ^ 200 * Real.exp (-(δ / 2 ^ 12 * t))) ≤
          Q * ((δ / 2 ^ 12 * t) ^ 200 * Real.exp (-(δ / 2 ^ 12 * t))) :=
        mul_le_mul_of_nonneg_right (by rw [hQ]; linarith) hW0
      linarith
    have hx2p : 0 < x ^ 2 := by positivity
    have h1 : K * Real.exp (-(δ * ((c / 2 ^ 11 : ℕ) : ℝ))) ≤ |K| * Real.exp (-(δ / 2 ^ 12 * t)) :=
      mul_le_mul (le_abs_self K) hexp (Real.exp_pos _).le (abs_nonneg K)
    refine h1.trans ?_
    rw [← one_div, le_div_iff₀ hx2p]
    have e : |K| * Real.exp (-(δ / 2 ^ 12 * t)) * x ^ 2 = |K| * x ^ 2 * Real.exp (-(δ / 2 ^ 12 * t)) := by ring
    rw [e]
    exact hkey
  · set p := x ^ ((1 : ℝ) / 100) with hpd
    have hp2 : (2 * x) ^ ((1 : ℝ) / 100) ≤ 2 * p := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
      have : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [Real.rpow_one] at this
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hp50 : x ^ ((1 : ℝ) / 2) = p ^ 50 := by
      rw [hpd, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hp1 : (1 : ℝ) ≤ p := by linarith
    have hp3 : p ^ 2 ≤ p ^ 50 := pow_le_pow_right₀ hp1 (by norm_num)
    rw [hp50]
    push_cast
    have h1 : 4 * ((c / 2 ^ 11 : ℕ) : ℝ) + 5 ≤ 4 * (2 * p + 1) + 5 := by linarith
    nlinarith
private theorem supDist_parentBlock_originSite_le {Λ : MomentParameters} (S : MomentPoint Λ)
    (hodd : Odd Λ.stepParams.side) (u n : ℕ) [NeZero n] :
    TorusFields.supDist (TorusLumps.parentBlock Λ.stepParams.side (S.originSite u (n * Λ.stepParams.side)))
      (S.originSite (u + 1) n) ≤ 1 := by apply _root_.YangMills.SharedProofs.p63379 <;> assumption
private theorem weightedFormSize_le {n : ℕ} [NeZero n] {κ S₂ v : ℝ} (hκ : 0 < κ) (hS₂ : 0 ≤ S₂) (hv : 0 ≤ v)
    (hsum : ∀ y : TorusSite n, ∑ x : TorusSite n, Real.exp (-(κ / 2 * TorusFields.supDist y x)) ≤ S₂)
    (A : TorusBond n → BlockAverages.imaginaryQuaternions) (o' Y : TorusSite n)
    (hA : ∀ c : TorusBond n, ‖A c‖ ≤ 4 * ((TorusFields.supDist c.1 o' : ℝ) + 1) * v) :
    weightedFormSize κ Y A ≤ 16 * (1 + 2 / κ) * S₂ * ((1 + (TorusFields.supDist Y o' : ℝ)) * v) := by
  have hterm : ∀ c : TorusBond n, Real.exp (-(κ * (TorusFields.supDist Y c.1 : ℝ))) * ‖A c‖ ≤
      4 * (1 + 2 / κ) * ((1 + (TorusFields.supDist Y o' : ℝ)) * v) *
        Real.exp (-(κ / 2 * TorusFields.supDist Y c.1)) := by
    intro c
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (TorusFields.supDist Y c.1 : ℝ) := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (TorusFields.supDist Y o' : ℝ) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    rw [← ht, ← hD]
    have h1 : (TorusFields.supDist c.1 o' : ℝ) ≤ t + D := by
      have := supDist_triangle c.1 Y o'
      rw [supDist_comm c.1 Y] at this
      rw [ht, hD]
      exact_mod_cast this
    have h2 : ‖A c‖ ≤ 4 * ((1 + t) * (1 + D)) * v := by
      refine (hA c).trans ?_
      have : (TorusFields.supDist c.1 o' : ℝ) + 1 ≤ (1 + t) * (1 + D) := by nlinarith
      have h3 := mul_le_mul_of_nonneg_right this hv
      linarith
    have h3 : 1 + t ≤ (1 + 2 / κ) * Real.exp (κ / 2 * t) := by
      have a1 := Real.add_one_le_exp (κ / 2 * t)
      have a2 : (1 : ℝ) ≤ Real.exp (κ / 2 * t) := Real.one_le_exp (by positivity)
      have e : (1 + 2 / κ) * Real.exp (κ / 2 * t) = Real.exp (κ / 2 * t) + 2 / κ * Real.exp (κ / 2 * t) := by ring
      have a3 : t + 2 / κ ≤ 2 / κ * Real.exp (κ / 2 * t) := by
        have : 2 / κ * (κ / 2 * t + 1) ≤ 2 / κ * Real.exp (κ / 2 * t) :=
          mul_le_mul_of_nonneg_left a1 (by positivity)
        have e2 : 2 / κ * (κ / 2 * t + 1) = t + 2 / κ := by field_simp
        linarith
      have a4 : 0 ≤ 2 / κ := by positivity
      rw [e]
      linarith
    have hE : Real.exp (-(κ * t)) * Real.exp (κ / 2 * t) = Real.exp (-(κ / 2 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hE0 : 0 ≤ Real.exp (-(κ * t)) := (Real.exp_pos _).le
    calc Real.exp (-(κ * t)) * ‖A c‖ ≤ Real.exp (-(κ * t)) * (4 * ((1 + t) * (1 + D)) * v) :=
          mul_le_mul_of_nonneg_left h2 hE0
      _ ≤ Real.exp (-(κ * t)) * (4 * (((1 + 2 / κ) * Real.exp (κ / 2 * t)) * (1 + D)) * v) := by
          refine mul_le_mul_of_nonneg_left ?_ hE0
          have : (1 + t) * (1 + D) ≤ ((1 + 2 / κ) * Real.exp (κ / 2 * t)) * (1 + D) :=
            mul_le_mul_of_nonneg_right h3 (by linarith)
          have h5 := mul_le_mul_of_nonneg_right this hv
          linarith
      _ = 4 * (1 + 2 / κ) * ((1 + D) * v) * (Real.exp (-(κ * t)) * Real.exp (κ / 2 * t)) := by ring
      _ = _ := by rw [hE]
  unfold weightedFormSize
  refine (Finset.sum_le_sum fun c _ => hterm c).trans ?_
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have h0 : 0 ≤ 4 * (1 + 2 / κ) * ((1 + (TorusFields.supDist Y o' : ℝ)) * v) := by positivity
  have := mul_le_mul_of_nonneg_left (hsum Y) h0
  have e : 16 * (1 + 2 / κ) * S₂ * ((1 + (TorusFields.supDist Y o' : ℝ)) * v) =
      4 * (4 * (1 + 2 / κ) * ((1 + (TorusFields.supDist Y o' : ℝ)) * v) * S₂) := by ring
  rw [e]
  push_cast
  nlinarith [this, Finset.sum_nonneg (fun z _ => (Real.exp_pos (-(κ / 2 * (TorusFields.supDist Y z : ℝ)))).le :
    ∀ z ∈ (Finset.univ : Finset (TorusSite n)), 0 ≤ Real.exp (-(κ / 2 * (TorusFields.supDist Y z : ℝ))))]
private def ContractsAtParameters (Λ : MomentParameters) : Prop :=
  ∃ Cw : ℝ, 0 < Cw ∧ Cw * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) ≤
      2⁻¹ ^ 10 * (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) ∧
    ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
      ∀ (ω : TorusPlaquette (n * Λ.stepParams.side) → ℝ) (ω' : TorusPlaquette n → ℝ),
      (∀ p, 0 < ω p) → (∀ p, 0 < ω' p) →
      IsSlowlyVaryingPair Λ.stepParams.side (Λ.stepParams.weightRate / 8) ω ω' →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n) (q : ENNReal), 1 ≤ q → Measurable X →
        weightedCurvatureNorm μ ω q
            (fun e => pushColours Λ.table.coupling Λ.table.ρA Λ.stepParams.side u (X e)) ≤
          ENNReal.ofReal (Cw * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ)) * weightedCurvatureNorm μ ω' q X
private theorem forAllParameters_contracts (hCon : responseContractionStatement) :
    ForAllParameters ContractsAtParameters := by
  intro a ha
  obtain ⟨Cw, hCw, L₀, rt₀, C₀, hrt, h⟩ := hCon a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hLL T hTa hTL hD hS hH hr hCd Kr hKr => ?_⟩
  obtain ⟨hθ, y₀, g⟩ := h L hL hLL T hTa hTL hD hS hH hr hCd
  subst hTL
  exact ⟨y₀, fun y hy hR hW g' _ _ k _ _ _ R d _ => ⟨Cw, hCw, hθ, g y hy hR hW⟩⟩
private theorem eLpNorm_dirac_curlNorm {m : ℕ} (Z : ColourForm m) (p : TorusPlaquette m) :
    eLpNorm (fun _ : Unit => curlNorm Z p) 1 (Measure.dirac ()) = ENNReal.ofReal (curlNorm Z p) := by
  have h0 : 0 ≤ curlNorm Z p := Real.sqrt_nonneg _
  rw [eLpNorm_one_eq_lintegral_enorm]
  simp [Real.enorm_of_nonneg h0]
private theorem curlNorm_pushColours_le {Λ : MomentParameters} (hC : ContractsAtParameters Λ)
    (hL1 : 1 ≤ Λ.stepParams.side) (hrate : 0 ≤ Λ.stepParams.weightRate) (u n : ℕ) [NeZero n]
    (h64 : 64 ≤ n) (X : ColourForm n) (B : ℝ) (hB : 0 ≤ B)
    (hX : ∀ p : WeightedResponses.OrientedPlaquette n, curlNorm X p.1 ≤ B)
    (p : WeightedResponses.OrientedPlaquette (n * Λ.stepParams.side)) :
    curlNorm (pushColours Λ.table.coupling Λ.table.ρA Λ.stepParams.side u X) p.1 ≤ B / 1024 := by
  obtain ⟨Cw, hCw, hθ, hc⟩ := hC
  have hLr : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast hL1
  have hslow : IsSlowlyVaryingPair Λ.stepParams.side (Λ.stepParams.weightRate / 8)
      (fun _ : TorusPlaquette (n * Λ.stepParams.side) => (1 : ℝ)) (fun _ : TorusPlaquette n => (1 : ℝ)) := by
    intro p' p''
    show (1 : ℝ) ≤ Real.exp (Λ.stepParams.weightRate / 8 *
      (1 + (TorusFields.supDist (TorusLumps.parentBlock Λ.stepParams.side p'.1) p''.1 : ℝ))) * 1
    rw [mul_one]
    exact Real.one_le_exp (by positivity)
  have key := hc u n h64 (fun _ => 1) (fun _ => 1) (fun _ => one_pos) (fun _ => one_pos) hslow Unit
    (Measure.dirac ()) (fun _ => X) 1 le_rfl measurable_const
  have hr : weightedCurvatureNorm (Measure.dirac ()) (fun _ : TorusPlaquette n => (1 : ℝ)) (1 : ENNReal)
      (fun _ : Unit => X) ≤ ENNReal.ofReal B := by
    unfold weightedCurvatureNorm
    refine iSup_le fun p' => ?_
    rw [eLpNorm_dirac_curlNorm]
    simp only [ENNReal.ofReal_one, one_mul]
    exact ENNReal.ofReal_le_ofReal (hX p')
  have hl : ENNReal.ofReal (curlNorm (pushColours Λ.table.coupling Λ.table.ρA Λ.stepParams.side u X) p.1) ≤
      weightedCurvatureNorm (Measure.dirac ()) (fun _ : TorusPlaquette (n * Λ.stepParams.side) => (1 : ℝ))
        (1 : ENNReal)
        (fun e : Unit => pushColours Λ.table.coupling Λ.table.ρA Λ.stepParams.side u ((fun _ : Unit => X) e)) := by
    unfold weightedCurvatureNorm
    refine le_trans ?_ (le_iSup _ p)
    rw [eLpNorm_dirac_curlNorm]
    simp
  have hθ0 : 0 ≤ Cw * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
  have h3 := hl.trans (key.trans (mul_le_mul_right hr _))
  rw [← ENNReal.ofReal_mul hθ0] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hθ0 hB)).1 h3
  have hLq : (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hLr (by norm_num)
  have h5 : Cw * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 1024 := by
    refine hθ.trans ?_
    have : (0 : ℝ) ≤ 2⁻¹ ^ 10 := by positivity
    have h6 := mul_le_mul_of_nonneg_left hLq this
    norm_num at h6 ⊢
    linarith
  have h6 := mul_le_mul_of_nonneg_right h5 hB
  linarith
private theorem exists_log_floor (Cv : ℝ) : ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → |Cv| * Real.log x ≤ x / 2 := by
  have h := (Real.isLittleO_log_id_atTop).bound (show (0 : ℝ) < 1 / (2 * (|Cv| + 1)) by positivity)
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨max x₁ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨a1, a2⟩ := hx₁ x ((le_max_left _ _).trans hx)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg a2
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at a1
  have hp : (0 : ℝ) < |Cv| + 1 := by positivity
  have h2 : (|Cv| + 1) * Real.log x ≤ x / 2 := by
    have := mul_le_mul_of_nonneg_left a1 hp.le
    have e : (|Cv| + 1) * (1 / (2 * (|Cv| + 1)) * x) = x / 2 := by
      field_simp
    linarith
  nlinarith
set_option maxHeartbeats 2000000 in
theorem framesNearResponse_holds (hCut : goodConfigCutoffStatement) (hCon : responseContractionStatement)
    (hWin : scaleWindowStatement) (hFr : frameOverCutTopStatement) (hCo : colourFormIdentitiesStatement)
    (hSum : SlopeCoefficient.ExpDecayTorusSumBounded) (hJ : parameterStatementsCombine) :
    framesNearResponseStatement := by
  obtain ⟨j1, j2, -, j4⟩ := hJ
  unfold goodConfigCutoffStatement ForAllPoints at hCut
  unfold scaleWindowStatement ForAllPoints at hWin
  show ForAllParameters framesNearResponseAt
  refine j2 _ _ (fun Λ hf h => ?_) (j1 _ _ hCut (j1 _ _ hWin (forAllParameters_contracts hCon)))
  obtain ⟨⟨Cc, cc, Xc, hcc, hyc, hC⟩, ⟨Cv, cv, Xw, hcv, hyw, hW⟩, hcon⟩ := h
  obtain ⟨cn, nss, hties, -⟩ := hf.coldRegime
  obtain ⟨-, -, e_ρ, -, -, -, -, hholds⟩ := hties
  have ha : 1 ≤ Λ.stepParams.coupling := hf.assignment_admissible.a_ge
  have hodd : Odd Λ.stepParams.side := hf.assignment_admissible.L_odd
  obtain ⟨K, hK0, hK⟩ := hFr Λ.stepParams cn ha hodd hholds
  have hδ₁ : 0 < cn.δ₁ := hholds.positivity.1
  have hcl := hholds.classical.1
  have hs₀ : 0 < cn.s₀ := hcl.2.2.1
  have hδ₂ : 0 < cn.δ₂ := hcl.2.2.2.1
  obtain ⟨S₂, hS₂p, hS₂⟩ := hSum (cn.δ₁ / 2 / 2) (by positivity)
  obtain ⟨X₁, hX₁, hfl⟩ := exists_coupling_floor K cn.s₀ cn.δ₂ hs₀ hδ₂
  obtain ⟨X₂, hX₂, hlog⟩ := exists_log_floor (Cv 0)
  obtain ⟨Ks, hKsd⟩ : ∃ Ks : ℝ, Ks = 16 * (1 + 2 / (cn.δ₁ / 2)) * S₂ := ⟨_, rfl⟩
  have hKs0 : 0 ≤ Ks := by rw [hKsd]; positivity
  refine ⟨1 + 12 + K * (3 * Ks) ^ 2 + K * (3 * Ks), max (max Xc Xw) (max X₁ X₂), by
      have h1 : 0 ≤ K * (3 * Ks) ^ 2 := by positivity
      have h2 : 0 ≤ K * (3 * Ks) := by positivity
      linarith, ?_, fun S hx d n _ hd hn V Y hg => ?_⟩
  · exact le_trans hX₁ ((le_max_left _ _).trans (le_max_right _ _))
  have hxc : Xc ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxw : Xw ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx1 : X₁ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : X₂ ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hxpos : 0 < S.scaleCoupling := by linarith
  obtain ⟨w1, w2, w3, -, -, w6, w7⟩ := hW S hxw
  obtain ⟨hu1, -⟩ := w7 (S.lastSeparated + d) (by omega) (by omega)
  obtain ⟨-, hu2⟩ := w7 (S.lastSeparated + d + 1) (by omega) (by omega)
  have hK' : S.lastSeparated + d ≤ S.data.windowLevel := by omega
  have hz := S.onFlow (S.lastSeparated + d) hK'
  rw [← S.stage_eq (S.lastSeparated + d) hK'] at hz
  have hRt : (S.tower.stage (S.lastSeparated + d)).depth = S.lastSeparated + d := hz.depth_eq
  have hRx : (S.tower.stage (S.lastSeparated + d)).coupling = S.coupling (S.lastSeparated + d) := hz.coupling_eq
  have hOn := hz.onFamily.onFamily
  have hρA : (S.tower.stage (S.lastSeparated + d)).anchorRadius = Λ.table.ρA := hOn.anchorRadius_eq
  have hρc : (S.tower.stage (S.lastSeparated + d)).anchorRadius = cn.ρA := hρA.trans e_ρ.symm
  have hlogx := hlog S.scaleCoupling hx2
  have hu1' : |S.coupling (S.lastSeparated + d) - S.scaleCoupling| ≤ S.scaleCoupling / 2 := by
    refine hu1.trans (le_trans ?_ hlogx)
    have h0 : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg (by linarith)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) h0
  have hua := abs_le.1 hu1'
  obtain ⟨f1, f2, f3, f4⟩ := hfl S.scaleCoupling (S.coupling (S.lastSeparated + d)) hx1
    (by linarith [hua.1]) (by linarith [hua.2])
  have hm₀ : (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach =
      ⌈S.coupling (S.lastSeparated + d) ^ ((1 : ℝ) / 100)⌉₊ / 2 ^ 11 := by
    show TorusLumps.clusterRange (S.tower.stage (S.lastSeparated + d)).coupling / 2 ^ 11 = _
    rw [hRx]
    rfl
  rw [← hm₀] at f1 f3 f4
  have hnbig : S.scaleCoupling ^ ((1 : ℝ) / 2) ≤ (n : ℝ) := by
    have h2N : S.scaleCoupling ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ S.logIndex := by
      have e1 : (2 : ℝ) ^ (-(S.logIndex : ℝ)) = ((2 : ℝ) ^ S.logIndex)⁻¹ := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      have e2 : S.scaleCoupling ^ (-(1 / 2) : ℝ) = (S.scaleCoupling ^ ((1 : ℝ) / 2))⁻¹ := by
        rw [Real.rpow_neg hxpos.le]
      rw [e1, e2] at w2
      exact (inv_le_inv₀ (by positivity) (by positivity)).1 w2
    have hL2 : (2 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by
      have h40 : 2 ^ 40 ≤ Λ.table.side := hf.assignment_admissible.L_ge
      have : 2 ≤ Λ.stepParams.side := le_trans (by norm_num) h40
      exact_mod_cast this
    have h3 : (2 : ℝ) ^ S.logIndex ≤ (Λ.stepParams.side : ℝ) ^ S.logIndex := pow_le_pow_left₀ (by norm_num) hL2 _
    have h4 : ((Λ.stepParams.side ^ S.logIndex : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [hn]
      exact_mod_cast hu2
    push_cast at h4
    linarith
  have hbig : 4 * (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach + 5 < n := by
    have : ((4 * (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach + 5 : ℕ) : ℝ) < (n : ℝ) :=
      f4.trans_le hnbig
    exact_mod_cast this
  have h64 : 64 ≤ n := by omega
  obtain ⟨c1, c2, c3, -⟩ := hC S hxc (S.lastSeparated + d + 1) (by omega) (by omega) n hn V Y hg
  have hv0 : 0 ≤ S.localCurvature (S.lastSeparated + d + 1) n V := Real.iSup_nonneg fun p => norm_nonneg _
  have hvs := hg.curvature_le
  have hm1 : 1 ≤ S.rangeSq := by
    have hr : 0 < S.range := by
      show 0 < ⌈S.scaleCoupling ^ ((1 : ℝ) / 100)⌉₊
      exact Nat.ceil_pos.2 (by positivity)
    show 1 ≤ S.range ^ 2
    exact Nat.one_le_pow _ _ hr
  obtain ⟨o', ho'⟩ : ∃ o' : TorusSite n, o' = S.originSite (S.lastSeparated + d + 1) n := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : TorusBond n → BlockAverages.imaginaryQuaternions,
      A = S.cutoffLie (S.lastSeparated + d + 1) n V := ⟨_, rfl⟩
  obtain ⟨v, hvd⟩ : ∃ v : ℝ, v = S.localCurvature (S.lastSeparated + d + 1) n V := ⟨_, rfl⟩
  have hA : ∀ c : TorusBond n, ‖A c‖ ≤ 4 * ((TorusFields.supDist c.1 o' : ℝ) + 1) * v := by
    intro c
    have e : A c = cutoffProfile o' S.rangeSq c.1 • axialCoords Λ.stepParams V o' c := by rw [hAd, ho']; rfl
    have hc01 : |cutoffProfile o' S.rangeSq c.1| ≤ 1 := by
      have h0 : 0 ≤ cutoffProfile o' S.rangeSq c.1 := le_max_left _ _
      rw [abs_of_nonneg h0]
      exact max_le zero_le_one (min_le_left _ _)
    rw [e, norm_smul, Real.norm_eq_abs]
    have hv0' : 0 ≤ v := by rw [hvd]; exact hv0
    have hd0 : (0 : ℝ) ≤ (TorusFields.supDist c.1 o' : ℝ) := by positivity
    by_cases hc : TorusFields.supDist c.1 o' + 1 ≤ 2 * S.rangeSq
    · have b1 : c.1 ∈ ResponseInTheExpansion.supBall o' (2 * S.rangeSq) := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        have : TorusFields.supDist c.1 o' ≤ 2 * S.rangeSq := by omega
        exact_mod_cast this
      have b2 : c.1 + unitStep n c.2 ∈ ResponseInTheExpansion.supBall o' (2 * S.rangeSq) := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        have h1 := supDist_triangle (c.1 + unitStep n c.2) c.1 o'
        have h2 := supDist_add_unitStep_le c.1 c.2
        rw [supDist_comm] at h2
        have : TorusFields.supDist (c.1 + unitStep n c.2) o' ≤ 2 * S.rangeSq := by omega
        exact_mod_cast this
      rw [ho'] at b1 b2
      have h1 := c1 c b1 b2
      rw [← ho', ← hvd] at h1
      have h2 : ‖axialCoords Λ.stepParams V o' c‖ ≤ 4 * ((TorusFields.supDist c.1 o' : ℝ) + 1) * v := h1
      calc |cutoffProfile o' S.rangeSq c.1| * ‖axialCoords Λ.stepParams V o' c‖ ≤
            1 * ‖axialCoords Λ.stepParams V o' c‖ :=
            mul_le_mul_of_nonneg_right hc01 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h2
    · have hz0 : cutoffProfile o' S.rangeSq c.1 = 0 := by
        unfold cutoffProfile
        have h1 : 2 * S.rangeSq ≤ TorusFields.supDist c.1 o' := by omega
        have h2 : (2 * (S.rangeSq : ℝ)) ≤ (TorusFields.supDist c.1 o' : ℝ) := by exact_mod_cast h1
        have h3 : (1 : ℝ) ≤ (S.rangeSq : ℝ) := by exact_mod_cast hm1
        have h4 : (2 * (S.rangeSq : ℝ) - 1 - (TorusFields.supDist c.1 o' : ℝ)) / ((S.rangeSq : ℝ) - 1) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        exact max_eq_left ((min_le_right _ _).trans h4)
      rw [hz0]
      simp only [abs_zero, zero_mul]
      positivity
  have hv0' : 0 ≤ v := by rw [hvd]; exact hv0
  have hvs' : v ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ) := by rw [hvd]; exact hvs
  have hs : 64 * v < cn.s₀ := by linarith
  have hcold : ∀ u' : ℝ, 0 ≤ u' → u' ≤ 1 → IsCold cn.s₀ (expField u' A) := by
    intro u' a b x μ ν h
    have := c3 u' a b x μ ν h
    rw [← hAd, ← hvd] at this
    exact this.trans_lt hs
  obtain ⟨r1, r2⟩ := hK (S.tower.stage (S.lastSeparated + d)).depth
    (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach n A f1 hbig h64 hcold
  have hsz : ∀ Yb : TorusSite n, weightedFormSize (cn.δ₁ / 2) Yb A ≤ Ks * ((1 + (TorusFields.supDist Yb o' : ℝ)) * v) := by
    intro Yb
    rw [hKsd]
    exact weightedFormSize_le (by positivity) hS₂p.le hv0' (fun y => hS₂ n y) A o' Yb hA
  have hdist : ∀ b : TorusBond (n * Λ.stepParams.side),
      (1 + (TorusFields.supDist (TorusLumps.parentBlock Λ.stepParams.side b.1) o' : ℝ)) ≤
      3 * (1 + (TorusFields.supDist b.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ)) := by
    intro b
    have t1 := supDist_triangle (TorusLumps.parentBlock Λ.stepParams.side b.1)
      (TorusLumps.parentBlock Λ.stepParams.side (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))) o'
    have t2 := TorusBalls.supDist_parentBlock_le_div_add_one Λ.stepParams.side b.1
      (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))
    have t3 := supDist_parentBlock_originSite_le S hodd (S.lastSeparated + d) n
    rw [← ho'] at t3
    have t4 := Nat.div_le_self (TorusFields.supDist b.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)))
      Λ.stepParams.side
    have t5 : TorusFields.supDist (TorusLumps.parentBlock Λ.stepParams.side b.1) o' ≤
        TorusFields.supDist b.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) + 2 := by omega
    have t6 : (TorusFields.supDist (TorusLumps.parentBlock Λ.stepParams.side b.1) o' : ℝ) ≤
        (TorusFields.supDist b.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + 2 := by
      exact_mod_cast t5
    have t7 : (0 : ℝ) ≤ (TorusFields.supDist b.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) := by
      positivity
    linarith
  have hsize3 : ∀ b : TorusBond (n * Λ.stepParams.side),
      weightedFormSize (cn.δ₁ / 2) (TorusLumps.parentBlock Λ.stepParams.side b.1) A ≤
      3 * Ks * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b := by
    intro b
    refine (hsz _).trans ?_
    have h1 := mul_le_mul_of_nonneg_right (hdist b) hv0'
    have h2 := mul_le_mul_of_nonneg_left h1 hKs0
    unfold weightedBondSize
    calc _ ≤ _ := h2
      _ = _ := by ring
  have hsize0 : ∀ b : TorusBond (n * Λ.stepParams.side),
      0 ≤ weightedFormSize (cn.δ₁ / 2) (TorusLumps.parentBlock Λ.stepParams.side b.1) A := fun b =>
    Finset.sum_nonneg fun c _ => by positivity
  have hT0 : ∀ b : TorusBond (n * Λ.stepParams.side),
      0 ≤ weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b := fun b => by
    unfold weightedBondSize
    positivity
  have hcross : ∀ b : TorusBond (n * Λ.stepParams.side), ‖crossingComponent Λ.stepParams A b‖ ≤
      12 * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b := by
    intro b
    classical
    unfold crossingComponent
    split_ifs with h
    · refine (hA _).trans ?_
      have h1 := mul_le_mul_of_nonneg_right (hdist b) hv0'
      unfold weightedBondSize
      have e : 4 * ((TorusFields.supDist (TorusLumps.parentBlock Λ.stepParams.side b.1, b.2).1 o' : ℝ) + 1) * v =
          4 * ((1 + (TorusFields.supDist (TorusLumps.parentBlock Λ.stepParams.side b.1) o' : ℝ)) * v) := by
        simp only
        ring
      rw [e]
      linarith
    · rw [norm_zero]
      have := hT0 b
      linarith
  have hMe : ResponseInTheExpansion.responseOfLieForm Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side
      (S.lastSeparated + d) A =
      ResponseInTheExpansion.responseOfLieForm Λ.stepParams.coupling cn.ρA Λ.stepParams.side
        (S.tower.stage (S.lastSeparated + d)).depth A := by
    rw [hRt, e_ρ]
  have hω : K * Real.exp (-(cn.δ₂ * ((S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach : ℝ))) ≤
      S.scaleCoupling ^ (-2 : ℝ) := f3
  rw [← hAd, ← hvd]
  obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁ : ℝ, κ₁ = K * (3 * Ks) := ⟨_, rfl⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ κ₂ : ℝ, κ₂ = K * (3 * Ks) ^ 2 := ⟨_, rfl⟩
  have hκ₁0 : 0 ≤ κ₁ := by rw [hκ₁]; positivity
  have hκ₂0 : 0 ≤ κ₂ := by rw [hκ₂]; positivity
  rw [← hκ₁, ← hκ₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [hMe]
    exact r1 b hb
  · intro b hb _
    have hρs : (S.tower.stage (S.lastSeparated + d)).toStepSetup.anchorRadius = cn.ρA := hρc
    rw [hMe, hρs]
    refine (r2 b hb).1.trans ?_
    have h1 : K * weightedFormSize (cn.δ₁ / 2) (TorusLumps.parentBlock Λ.stepParams.side b.1) A ^ 2 ≤
        κ₂ * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b ^ 2 := by
      have h2 := pow_le_pow_left₀ (hsize0 b) (hsize3 b) 2
      have h3 := mul_le_mul_of_nonneg_left h2 hK0
      rw [hκ₂]
      calc _ ≤ _ := h3
        _ = _ := by ring
    have h4 : 0 ≤ weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b ^ 2 := by
      positivity
    have h5 : κ₂ * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b ^ 2 ≤
        (1 + 12 + κ₂ + κ₁) * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) h4
    linarith
  · intro b hb _
    rw [hMe]
    refine (r2 b hb).2.trans ?_
    have h3 := mul_le_mul_of_nonneg_left (hsize3 b) hK0
    have h5 : κ₁ * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b ≤
        (1 + 12 + κ₂ + κ₁) * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b :=
      mul_le_mul_of_nonneg_right (by linarith) (hT0 b)
    have e : K * (3 * Ks * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b) =
        κ₁ * weightedBondSize (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) v b := by
      rw [hκ₁]
      ring
    linarith
  · intro b _ _
    refine (hcross b).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (hT0 b)
  · intro x μ ν hμν
    have hL1 : 1 ≤ Λ.stepParams.side := by
      have := hf.assignment_admissible.L_ge
      exact le_trans (by norm_num) this
    have hrate : 0 ≤ Λ.stepParams.weightRate := by
      have := hf.assignment_admissible.rt_pos
      show 0 ≤ Λ.table.rt / 2 ^ 10
      positivity
    have hc2 : ∀ p : WeightedResponses.OrientedPlaquette n, curlNorm (toColourForm A) p.1 ≤ 60 * v := by
      intro p
      rw [hAd, hvd]
      exact c2 p
    have h1 := curlNorm_pushColours_le hcon hL1 hrate (S.lastSeparated + d) n h64 (toColourForm A) (60 * v)
      (by positivity) hc2 ⟨(x, μ, ν), hμν⟩
    have h2 := hCo.2.1 Λ.stepParams.side n Λ.table.coupling Λ.table.ρA (S.lastSeparated + d) A
    rw [h2, hCo.1] at h1
    refine le_trans h1 ?_
    linarith
end YangMills.Construction.MomentLaw
end
