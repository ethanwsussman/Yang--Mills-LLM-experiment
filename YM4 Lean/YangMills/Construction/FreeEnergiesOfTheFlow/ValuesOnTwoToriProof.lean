import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASetting
import YangMills.Construction.ClusterExpansionOfAStep.GasAtColdTops
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.FlatSettingsAgree
import YangMills.Construction.FreeEnergiesOfTheFlow.ValuesOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open StepSettings RenormalizationStepParameters StepGas StepLocality TorusFields TorusLumps ClusterExpansionOfAStep WeightedResponses FlatTops
private theorem trivialField_isCold {m : ℕ} {s : ℝ} (hs : 0 < s) : IsCold s (trivialField m) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private theorem gasRate_nonneg {T : ParameterAssignment} (hT : T.Admissible) : 0 ≤ T.gasRate := by
  have h1 := hT.cE_pos
  have h2 := hT.κ_pos
  have h3 := hT.σ_pos
  have h4 : 0 < T.κ₁ := by
    unfold ParameterAssignment.κ₁
    exact lt_min (by positivity) (by positivity)
  unfold ParameterAssignment.gasRate
  refine mul_nonneg (by positivity) (le_min h1.le (le_min (by positivity) (by positivity)))
abbrev _root_.YangMills.SharedProofs.p19490 := @gasRate_nonneg
private theorem flowCoupling_le_add {ℓ : TorusLumps.StepParameters} {β : ℝ} {t : ℕ}
    (h : ∀ j < t, |flowCoupling ℓ β (j + 1) - flowCoupling ℓ β j| ≤ 2 * ℓ.B) (u : ℕ) :
    ∀ d : ℕ, u + d ≤ t → flowCoupling ℓ β u ≤ flowCoupling ℓ β (u + d) + 2 * ℓ.B * d := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := (abs_le.mp (h (u + d) (by omega))).1
    have e : u + (d + 1) = u + d + 1 := rfl
    rw [e]
    push_cast
    linarith
private theorem clusterRange_le_side {B xu xt : ℝ} {L k n : ℕ} (hB : 1 ≤ B) (hL : 2 ≤ L) (hxt : 1 ≤ xt)
    (hxu : 0 ≤ xu) (hle : xu ≤ xt + 2 * B * ((k + 1 : ℕ) : ℝ))
    (hn : (2 + 2 * B) * xt ^ ((1 : ℝ) / 100) ≤ n) :
    clusterRange xu ≤ n * L ^ k := by
  unfold clusterRange
  refine Nat.ceil_le.mpr ?_
  set X : ℝ := xt ^ ((1 : ℝ) / 100) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hxt (by norm_num)
  set P : ℝ := (L : ℝ) ^ k with hP
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hP1 : 1 ≤ P := one_le_pow₀ hLr
  have hk : ((k + 1 : ℕ) : ℝ) ≤ P := by
    have : k + 1 ≤ L ^ k := by
      have h9 : k < L ^ k := Nat.lt_pow_self (by omega)
      omega
    rw [hP]
    exact_mod_cast this
  have hz : 1 ≤ 2 * B * ((k + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    nlinarith
  have h1 : xu ^ ((1 : ℝ) / 100) ≤ (xt + 2 * B * ((k + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow hxu hle (by norm_num)
  have h2 : (xt + 2 * B * ((k + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 100) ≤
      xt ^ ((1 : ℝ) / 100) + (2 * B * ((k + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 100) :=
    Real.rpow_add_le_add_rpow (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h3 : (2 * B * ((k + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 100) ≤ 2 * B * ((k + 1 : ℕ) : ℝ) := by
    calc (2 * B * ((k + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 100) ≤ (2 * B * ((k + 1 : ℕ) : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
      _ = _ := Real.rpow_one _
  have h4 : 2 * B * ((k + 1 : ℕ) : ℝ) ≤ 2 * B * P := by gcongr
  have h5 : X + 2 * B * P ≤ (2 + 2 * B) * X * P := by nlinarith [mul_pos (show (0:ℝ) < X by linarith) (show (0:ℝ) < P by linarith), mul_nonneg (show (0:ℝ) ≤ X - 1 by linarith) (show (0:ℝ) ≤ P by linarith), mul_nonneg (show (0:ℝ) ≤ B by linarith) (mul_nonneg (show (0:ℝ) ≤ X - 1 by linarith) (show (0:ℝ) ≤ P by linarith)), mul_nonneg (show (0:ℝ) ≤ X by linarith) (show (0:ℝ) ≤ P - 1 by linarith)]
  have h6 : (2 + 2 * B) * X * P ≤ n * P := by gcongr
  push_cast
  rw [← hP]
  linarith
private theorem blockActivity_sub_le {T : ParameterAssignment} (hT : T.Admissible) {y x : ℝ} {ρ : StepSetup}
    (hℓ : ρ.params = T.stepParameters y) (hx : 0 ≤ x) (hρx : ρ.coupling = x)
    {S S' m : ℕ} [NeZero S] [NeZero S']
    (hz : |(coldChartSetting ρ (trivialField S)).blockActivity T.lam 0 -
        (coldChartSetting ρ (trivialField S')).blockActivity T.lam 0| ≤
      Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5)))
    (hg : |ρ.blockDensity S 0 (trivialField S) - ρ.blockDensity S' 0 (trivialField S')| ≤
      Real.exp (-(T.gasRate * ρ.coupling) - ρ.params.rt * m / 2 ^ 8))
    (hm : (S : ℝ) / 4 ≤ m) :
    |blockActivityAtTrivial T.lam ρ S 0 - blockActivityAtTrivial T.lam ρ S' 0| ≤
      2 * Real.exp (-(T.rt * S / 2 ^ 10)) := by
  have hrt := hT.rt_pos
  have hch := gasRate_nonneg hT
  have hh : ∀ (K : ℕ) [NeZero K], ρ.blockDensity K 0 (trivialField K) = ρ.blockDensityAt 0 (trivialField K) := by
    intro K _
    simp [StepSetup.blockDensity, NeZero.ne K]
  rw [hh, hh] at hg
  have hrtl : ρ.params.rt = T.rt := by rw [hℓ]; rfl
  rw [hρx, hrtl] at hg
  have e1 : Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5)) ≤ Real.exp (-(T.rt * S / 2 ^ 10)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have : T.rt * S / 2 ^ 10 = T.rt * ((S : ℝ) / 4) / 2 ^ 8 := by ring
    rw [this]
    have h2 : T.rt * ((S : ℝ) / 4) ≤ T.rt * m := mul_le_mul_of_nonneg_left hm hrt.le
    have h3 : 0 ≤ T.rt * m := le_trans (by positivity) h2
    have : 15 / 16 * T.rt * (m : ℝ) / 2 ^ 5 = (15 / 2) * (T.rt * m / 2 ^ 8) := by ring
    rw [this]
    nlinarith
  have e2 : Real.exp (-(T.gasRate * x) - T.rt * m / 2 ^ 8) ≤ Real.exp (-(T.rt * S / 2 ^ 10)) := by
    refine Real.exp_le_exp.mpr ?_
    have : T.rt * S / 2 ^ 10 = T.rt * ((S : ℝ) / 4) / 2 ^ 8 := by ring
    rw [this]
    have h2 : T.rt * ((S : ℝ) / 4) ≤ T.rt * m := mul_le_mul_of_nonneg_left hm hrt.le
    have h3 : 0 ≤ T.gasRate * x := mul_nonneg hch hx
    linarith
  unfold blockActivityAtTrivial
  have e3 := abs_add_le ((coldChartSetting ρ (trivialField S)).blockActivity T.lam 0 -
      (coldChartSetting ρ (trivialField S')).blockActivity T.lam 0)
    (ρ.blockDensityAt 0 (trivialField S) - ρ.blockDensityAt 0 (trivialField S'))
  have e4 : (coldChartSetting ρ (trivialField S)).blockActivity T.lam 0 + ρ.blockDensityAt 0 (trivialField S) -
      ((coldChartSetting ρ (trivialField S')).blockActivity T.lam 0 + ρ.blockDensityAt 0 (trivialField S')) =
      (coldChartSetting ρ (trivialField S)).blockActivity T.lam 0 -
          (coldChartSetting ρ (trivialField S')).blockActivity T.lam 0 +
        (ρ.blockDensityAt 0 (trivialField S) - ρ.blockDensityAt 0 (trivialField S')) := by ring
  rw [e4]
  linarith
theorem blockActivityTwoTori_of_expansion (hA : expansionAlongFlow) (hF : TrivialFieldSettingsAgree)
    (hLoc : DensityLocality) (hGas : ColdGasBounds)
    (hCS : ColdChartSettingIsAdmissible) : blockActivityTwoTori := by
  obtain ⟨r₁, hr₁, h₁⟩ := hLoc
  obtain ⟨r₂, hr₂, h₂⟩ := hGas
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), fun T hT _ hrt => ?_⟩
  obtain ⟨y₁, k₁⟩ := h₁ T hT (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, k₂⟩ := h₂ T hT (hrt.trans (min_le_right _ _))
  obtain ⟨y₃, k₃⟩ := hCS T hT
  refine ⟨max (max y₁ y₂) (max y₃ T.floorMin), fun y hy hSt => ?_⟩
  have e₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have e₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have e₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have e₄ : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hfit := hT.fits y e₄
  have hB : 1 ≤ T.B := hT.B_ge
  refine ⟨2 + 2 * T.B, by linarith, fun β t hr R hR n n' _ _ hb hb' hnn hside u hu => ?_⟩
  have hy1 : 1 ≤ y := hfit.y₁_ge
  have hx1 : 1 ≤ flowCoupling (T.stepParameters y) β t := hy1.trans (hr t le_rfl)
  set k := t - 1 - u with hk
  obtain ⟨hOn, hlev, hcoup, hnext, harr⟩ := hR u hu
  have hℓ : (R u).params = T.stepParameters y := hOn.params_eq
  have hLT : (R u).params.side = T.side := by rw [hℓ]; rfl
  have hL2 : 2 ≤ T.side := le_trans (by norm_num) hT.L_ge
  have hbelow := flowCoupling_le_add (hA _ hSt β t hr).2 u (k + 1) (by omega)
  have hsum : u + (k + 1) = t := by omega
  rw [hsum] at hbelow
  have hxu : y ≤ flowCoupling (T.stepParameters y) β u := hr u (by omega)
  have hrange : clusterRange (flowCoupling (T.stepParameters y) β u) ≤ n * T.side ^ k :=
    clusterRange_le_side hB hL2 hx1 (by linarith) hbelow hside
  set S : ℕ := fineSide T.side k n with hSdef
  set S' : ℕ := fineSide T.side k n' with hS'def
  have hSe : S = n * T.side ^ k := fineSide_eq _ _ _
  have hS'e : S' = n' * T.side ^ k := fineSide_eq _ _ _
  have hSS : S ≤ S' := by
    rw [hSe, hS'e]
    exact Nat.mul_le_mul_right _ hnn
  have hLk : 1 ≤ T.side ^ k := Nat.one_le_pow _ _ (by omega)
  have hn₀ : T.n₀ ≤ n := by
    have h1 : T.side * T.n₀ ≤ n := hb.2
    nlinarith
  have hSn : n ≤ S := by
    rw [hSe]
    nlinarith
  have hS₀ : T.n₀ ≤ S := hn₀.trans hSn
  have h4096 : 4096 ≤ S := hT.n₀_ge.trans hS₀
  set m : ℕ := S / 2 - 2 with hm
  have hm1 : 2 * m + 2 < S := by omega
  have hm2 : 2 * m + 2 < S' := by omega
  have hrS : (R u).range ≤ S := by
    have : (R u).range = clusterRange (flowCoupling (T.stepParameters y) β u) := by
      show clusterRange (R u).coupling = _
      rw [hcoup]
    rw [this, hSe]
    exact hrange
  have hm16 : 16 * (R u).frameReach ≤ m := by
    show 16 * ((R u).range / 2 ^ 11) ≤ m
    omega
  have hodd : Odd (R u).params.side := by
    rw [hLT]
    exact hT.L_odd
  have agree := hF (R u) S S' m hodd (by omega) (by omega) hm1 hm2
  have hcold : ∀ K : ℕ, IsCold (9 / 8 * T.threshold) (trivialField K) :=
    fun K => trivialField_isCold (by have := hT.σ_pos; positivity)
  have hs := k₃ y e₃ (R u) hOn S hS₀ (trivialField S) (hcold S)
  have hs' := k₃ y e₃ (R u) hOn S' (hS₀.trans hSS) (trivialField S') (hcold S')
  have hz := (k₁ y e₁ (R u) hOn S S' hS₀ (hS₀.trans hSS) (coldChartSetting (R u) (trivialField S))
    (coldChartSetting (R u) (trivialField S')) 0 0 m hs hs').2 hm16 agree
  have hzz := hz.1.trans hz.2
  have hArr : (R u).IsSymmetricWeight := by
    have hrow := (hA _ hSt β u (fun j hj => hr j (by omega))).1.1
    unfold StepSetup.IsSymmetricWeight
    rw [hℓ, harr]
    exact hrow
  have hn₀' : (R u).params.n₀ = T.n₀ := by rw [hℓ]; rfl
  have hσ' : (R u).params.threshold = T.threshold := by rw [hℓ]; rfl
  have hm0 : 1 ≤ m := by omega
  have hg' := (k₂ y e₂ (R u) hOn hArr).2 S S' (by rw [hn₀']; exact hS₀) (by rw [hn₀']; exact hS₀.trans hSS)
    (trivialField S) (trivialField S') 0 0 m hm0 hm1 hm2 (by rw [hσ']; exact hcold S)
    (by rw [hσ']; exact hcold S') (fun _ _ => rfl)
  have hmr : (S : ℝ) / 4 ≤ m := by
    have : S ≤ 4 * m := by omega
    have h2 : (S : ℝ) ≤ 4 * m := by exact_mod_cast this
    linarith
  have hfin := blockActivity_sub_le hT hℓ (x := flowCoupling (T.stepParameters y) β u) (by linarith) hcoup
    hzz hg' hmr
  have e : T.rt * (T.side : ℝ) ^ k * n / 2 ^ 10 = T.rt * S / 2 ^ 10 := by
    rw [hSe]
    push_cast
    ring
  rw [e]
  exact hfin
end YangMills.Construction.FreeEnergies
end
