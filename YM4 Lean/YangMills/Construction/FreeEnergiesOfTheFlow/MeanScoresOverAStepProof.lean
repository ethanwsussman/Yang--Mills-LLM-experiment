import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfAStepAreCounted
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import YangMills.Construction.ClusterExpansionOfAStep.NearBlocksAreCounted
import YangMills.Construction.FreeEnergiesOfTheFlow.FunctionsOfTheLabelsAreIntegrable
import YangMills.Construction.FreeEnergiesOfTheFlow.LabelsOfAConfiguration
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverAStep
import YangMills.Construction.ResponseInTheExpansion.CaseMeanIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.ScoreOfAClassIsPaid
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open Dobrushin StepSettings StepGas RenormalizationStepParameters TorusLumps TorusFields BlockPlaces WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep BlockAverages
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem prod_one_add_inv_mul_bounds {ι : Type} [DecidableEq ι] (I : Finset ι) (S b : ι → ℝ)
    (hS : ∀ k, 0 ≤ S k) (hb : ∀ k, 1 ≤ b k) :
    (1 ≤ ∏ k ∈ I, (1 + (b k)⁻¹ * S k)) ∧ (∏ k ∈ I, (1 + (b k)⁻¹ * S k) ≤ Real.exp (∑ k ∈ I, S k)) ∧
    ∏ k ∈ I, (1 + (b k)⁻¹ * S k) - 1 ≤ 2 ^ I.card * Real.exp (∑ k ∈ I, S k) * ∑ k ∈ I, (b k)⁻¹ := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Real.exp_add]
    have hb0 : 0 < b a := by linarith [hb a]
    have hinv : (b a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hb a)
    have hinv0 : 0 < (b a)⁻¹ := inv_pos.mpr hb0
    have hx0 : 0 ≤ (b a)⁻¹ * S a := mul_nonneg hinv0.le (hS a)
    have hxS : (b a)⁻¹ * S a ≤ S a := by nlinarith [hS a]
    have hxe : 1 + (b a)⁻¹ * S a ≤ Real.exp (S a) := by
      have := Real.add_one_le_exp (S a)
      linarith
    set x := (b a)⁻¹ * S a with hx
    set P := ∏ k ∈ I, (1 + (b k)⁻¹ * S k) with hP
    set Q := Real.exp (∑ k ∈ I, S k) with hQ
    set E := Real.exp (S a) with hE
    set Sg := ∑ k ∈ I, (b k)⁻¹ with hSg
    have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun k _ => (inv_pos.mpr (by linarith [hb k])).le
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · exact mul_le_mul hxe h2 (by linarith) (by linarith)
    · have hxb : x ≤ E * (b a)⁻¹ := by
        rw [hx, mul_comm]
        have : S a ≤ E := by
          have := Real.add_one_le_exp (S a)
          linarith
        exact mul_le_mul_of_nonneg_right this hinv0.le
      have h4 : (P - 1) * (1 + x) ≤ (2 ^ I.card * Q * Sg) * E :=
        mul_le_mul h3 hxe (by linarith) (by positivity)
      have h5 : x ≤ (2 ^ I.card * Q) * E * (b a)⁻¹ := by
        have h6 : 1 ≤ (2 : ℝ) ^ I.card * Q := by
          have : (1 : ℝ) ≤ 2 ^ I.card := one_le_pow₀ (by norm_num)
          nlinarith
        calc x ≤ E * (b a)⁻¹ := hxb
          _ = 1 * E * (b a)⁻¹ := by ring
          _ ≤ _ := by gcongr
      have e : (1 + x) * P - 1 = (P - 1) * (1 + x) + x := by ring
      rw [e]
      have hpos : 0 ≤ (2 : ℝ) ^ I.card * Q * E := by positivity
      calc (P - 1) * (1 + x) + x ≤ (2 ^ I.card * Q * Sg) * E + (2 ^ I.card * Q) * E * (b a)⁻¹ := add_le_add h4 h5
        _ ≤ 2 ^ (I.card + 1) * (E * Q) * ((b a)⁻¹ + Sg) := by
          have : 2 ^ (I.card + 1) * (E * Q) * ((b a)⁻¹ + Sg) =
              2 * (2 ^ I.card * Q * E) * ((b a)⁻¹ + Sg) := by ring
          rw [this]
          nlinarith [mul_nonneg hpos hSg0, mul_nonneg hpos hinv0.le]
private theorem add_sum_le_mul_prod_one_add {ι : Type} [DecidableEq ι] (I : Finset ι) (a : ℝ) (x : ι → ℝ)
    (ha : 1 ≤ a) (hx : ∀ i, 0 ≤ x i) :
    a + ∑ i ∈ I, x i ≤ a * ∏ i ∈ I, (1 + x i) := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert b I hb ih =>
    rw [Finset.sum_insert hb, Finset.prod_insert hb]
    have h1 : 1 ≤ ∏ i ∈ I, (1 + x i) := by
      calc (1 : ℝ) = ∏ _i ∈ I, 1 := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => by linarith [hx i]
    nlinarith [hx b, mul_nonneg (hx b) (by linarith : (0:ℝ) ≤ a - 1), mul_nonneg (mul_nonneg (hx b) (by linarith : (0:ℝ) ≤ a)) (by linarith : (0:ℝ) ≤ ∏ i ∈ I, (1 + x i) - 1)]
private theorem card_sites_le_side_pow_mul_card_supportCore {L : ℕ} [NeZero L] (r : ℕ) (θ : ClusterSupport L n) :
    θ.2.card ≤ L ^ 4 * (supportCore L r θ).card := by
  classical
  have himg : θ.2.image (parentBlock L) ⊆ supportCore L r θ := by
    intro Y hY
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hY
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, ?_⟩
    refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr rfl⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, Finset.mem_union_right _ hz, ?_⟩
    simp [supDist]
  have hfib : ∀ Y ∈ θ.2.image (parentBlock L), (θ.2.filter fun z => parentBlock L z = Y).card ≤ L ^ 4 := by
    intro Y _
    have hinj : Set.InjOn (fun y : TorusSite (n * L) => siteOffset (L := L) y)
        (θ.2.filter fun z => parentBlock L z = Y : Finset _) := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      rw [← blockSite_parentBlock_siteOffset a, ← blockSite_parentBlock_siteOffset b, ha', hb']
      exact congrArg _ hab
    calc (θ.2.filter fun z => parentBlock L z = Y).card
        = ((θ.2.filter fun z => parentBlock L z = Y).image fun y => siteOffset (L := L) y).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ Fintype.card (BlockOffset L) := Finset.card_le_univ _
      _ = L ^ 4 := by simp [BlockOffset]
  calc θ.2.card ≤ L ^ 4 * (θ.2.image (parentBlock L)).card := Finset.card_le_mul_card_image _ _ hfib
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card himg)
private theorem card_supportCore_le_supportUnitCount {L : ℕ} [NeZero L] (hN : NearBlocksCardBound) (r : ℕ)
    (θ : ClusterSupport L n) :
    (supportCore L r θ).card ≤ (20 * r / L + 9) ^ 4 * supportUnitCount L r θ := by
  classical
  refine le_trans (Finset.card_le_card ?_) (hN L r n θ)
  intro Y hY
  obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hY).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, ?_⟩
  have h1 := (Finset.mem_inter.mp hz).1
  obtain ⟨x, hx, hd⟩ := (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2
  exact Finset.mem_inter.mpr ⟨h1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, by omega⟩⟩
private theorem sum_supportsAtBlock_weight_le (hCl : ClusterSumBound) (hN : NearBlocksCardBound)
    {T : ParameterAssignment} (hT : T.Admissible) (hch : 0 < T.gasRate) {y x : ℝ} (hfit : (T.stepParameters y).Admissible)
    (hxy : y ≤ x) (hx0 : 0 < x) (k₅ : ∀ z : ℝ, y ≤ z → T.side ≤ clusterRange z ∧
      (2 ^ 16 + 2 ^ 7 * T.rt) * (clusterRange z : ℝ) ^ 4 ≤ 15 / 16 * T.gasRate * z)
    (k₆ : (2 ^ 16 + 2 ^ 7 * T.rt) * (clusterRange x : ℝ) ^ 4 ≤ T.gasRate / (29 ^ 4 * (T.side : ℝ) ^ 4) * x)
    (n : ℕ) [NeZero n] (Y : TorusSite n) :
    ∑ θ ∈ supportsAtBlock (T.stepParameters y).side (clusterRange x) Y,
      2 ^ ((T.stepParameters y).side ^ 4 * (supportCore (T.stepParameters y).side (clusterRange x) θ).card) *
        clusterWeight (T.stepParameters y).side T.gasRate x (clusterRange x) θ ≤ Real.exp (-(7 * T.gasRate * x)) := by
  classical
  have hLpos : (0 : ℝ) < T.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T.side)
  have hfloor : (T.stepParameters y).RangeFloor (15 / 16 * T.gasRate) := fun z hz => k₅ z hz
  have hcnt := hCl (T.stepParameters y) (15 / 16 * T.gasRate) hfit (by positivity) hfloor x hxy n Y
  have hterm : ∀ θ ∈ supportsAtBlock (T.stepParameters y).side (clusterRange x) Y,
      2 ^ ((T.stepParameters y).side ^ 4 * (supportCore (T.stepParameters y).side (clusterRange x) θ).card) *
          clusterWeight (T.stepParameters y).side T.gasRate x (clusterRange x) θ ≤
        clusterWeight (T.stepParameters y).side (15 / 16 * T.gasRate) x (clusterRange x) θ *
          ((supportCore (T.stepParameters y).side (clusterRange x) θ).card : ℝ) ^ 4 *
          Real.exp (2 * (T.stepParameters y).rt *
            (siteDiameter (supportCore (T.stepParameters y).side (clusterRange x) θ) : ℝ)) := by
    intro θ hθ
    have hcore : Y ∈ supportCore (T.stepParameters y).side (clusterRange x) θ := (Finset.mem_filter.mp hθ).2.2
    have hc1 : (1 : ℝ) ≤ ((supportCore (T.stepParameters y).side (clusterRange x) θ).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨Y, hcore⟩
    have hc4 : (1 : ℝ) ≤ ((supportCore (T.stepParameters y).side (clusterRange x) θ).card : ℝ) ^ 4 := one_le_pow₀ hc1
    have hrt0 : 0 < (T.stepParameters y).rt := hT.rt_pos
    have he1 : 1 ≤ Real.exp (2 * (T.stepParameters y).rt *
        (siteDiameter (supportCore (T.stepParameters y).side (clusterRange x) θ) : ℝ)) :=
      Real.one_le_exp (by positivity)
    set u : ℝ := (supportUnitCount (T.stepParameters y).side (clusterRange x) θ : ℝ) with hu
    have hu0 : 0 ≤ u := Nat.cast_nonneg _
    have hrange := k₆
    set r := clusterRange x with hr
    have hr1 : 1 ≤ r := by
      have h16 := hfit.range_ge
      have : clusterRange (T.stepParameters y).y₁ ≤ r := Nat.ceil_mono (Real.rpow_le_rpow
        (show (0 : ℝ) ≤ (T.stepParameters y).y₁ by
          have : (1 : ℝ) ≤ (T.stepParameters y).y₁ := hfit.y₁_ge
          linarith) hxy (by norm_num))
      omega
    have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hcard : ((supportCore (T.stepParameters y).side r θ).card : ℝ) ≤ (29 * (r : ℝ)) ^ 4 * u := by
      have h1 := card_supportCore_le_supportUnitCount hN r θ
      have h2 : 20 * r / (T.stepParameters y).side + 9 ≤ 29 * r := by
        have : 20 * r / (T.stepParameters y).side ≤ 20 * r := Nat.div_le_self _ _
        omega
      have h3 : (supportCore (T.stepParameters y).side r θ).card ≤
          (29 * r) ^ 4 * supportUnitCount (T.stepParameters y).side r θ :=
        h1.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 4))
      have h4 : ((supportCore (T.stepParameters y).side r θ).card : ℝ) ≤
          ((29 * r) ^ 4 * supportUnitCount (T.stepParameters y).side r θ : ℕ) := by exact_mod_cast h3
      push_cast at h4
      exact h4
    have hLr : ((T.stepParameters y).side : ℝ) = T.side := rfl
    have hfl : (T.side : ℝ) ^ 4 * (29 * (r : ℝ)) ^ 4 ≤ T.gasRate * x := by
      have hrt1 : (0 : ℝ) ≤ 2 ^ 7 * T.rt := by have := hT.rt_pos; positivity
      have h1 : (r : ℝ) ^ 4 ≤ T.gasRate / (29 ^ 4 * (T.side : ℝ) ^ 4) * x := by
        have hr4 : (0 : ℝ) ≤ (r : ℝ) ^ 4 := by positivity
        nlinarith [mul_nonneg hrt1 hr4]
      have hpos : (0 : ℝ) < 29 ^ 4 * (T.side : ℝ) ^ 4 := mul_pos (by norm_num) (pow_pos hLpos 4)
      have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
      have e3 : (29 ^ 4 * (T.side : ℝ) ^ 4) * (T.gasRate / (29 ^ 4 * (T.side : ℝ) ^ 4) * x) = T.gasRate * x := by
        have hne : (29 ^ 4 * (T.side : ℝ) ^ 4) ≠ 0 := hpos.ne'
        rw [← mul_assoc, mul_div_cancel₀ _ hne]
      rw [e3] at h2
      calc (T.side : ℝ) ^ 4 * (29 * (r : ℝ)) ^ 4 = 29 ^ 4 * (T.side : ℝ) ^ 4 * (r : ℝ) ^ 4 := by ring
        _ ≤ _ := h2
    have hpow : (2 : ℝ) ^ ((T.stepParameters y).side ^ 4 * (supportCore (T.stepParameters y).side r θ).card) ≤
        Real.exp (T.gasRate * x * u) := by
      have hlog : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have h1 : (2 : ℝ) ^ ((T.stepParameters y).side ^ 4 * (supportCore (T.stepParameters y).side r θ).card) ≤
          Real.exp 1 ^ ((T.stepParameters y).side ^ 4 * (supportCore (T.stepParameters y).side r θ).card) :=
        pow_le_pow_left₀ (by norm_num) hlog _
      rw [← Real.exp_nat_mul, mul_one] at h1
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      push_cast
      calc ((T.stepParameters y).side : ℝ) ^ 4 * ((supportCore (T.stepParameters y).side r θ).card : ℝ)
          ≤ (T.side : ℝ) ^ 4 * ((29 * (r : ℝ)) ^ 4 * u) := by
            rw [hLr]
            gcongr
        _ = ((T.side : ℝ) ^ 4 * (29 * (r : ℝ)) ^ 4) * u := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfl hu0
    have hw : (2 : ℝ) ^ ((T.stepParameters y).side ^ 4 * (supportCore (T.stepParameters y).side r θ).card) *
          clusterWeight (T.stepParameters y).side T.gasRate x r θ ≤
        clusterWeight (T.stepParameters y).side (15 / 16 * T.gasRate) x r θ := by
      unfold clusterWeight
      calc _ ≤ Real.exp (T.gasRate * x * u) * Real.exp (-(16 * T.gasRate * x * u)) := by
            gcongr
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hz : 0 ≤ clusterWeight (T.stepParameters y).side (15 / 16 * T.gasRate) x r θ := (Real.exp_pos _).le
    calc _ ≤ clusterWeight (T.stepParameters y).side (15 / 16 * T.gasRate) x r θ := hw
      _ = clusterWeight (T.stepParameters y).side (15 / 16 * T.gasRate) x r θ * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  refine (Finset.sum_le_sum hterm).trans (hcnt.trans (Real.exp_le_exp.mpr ?_))
  nlinarith [mul_pos hch hx0]
set_option maxHeartbeats 1000000 in
theorem meanSiteScoresStepBound_holds (hI : labelFunctionsIntegrableStatement)
    (hM : caseMeanEqGasMeanStatement) (hC : clusterScoreIntegralBound) (hW : GasIsActivityBounded)
    (hP : MeanOfProductStatement) (hCl : ClusterSumBound)
    (hFl : CouplingFloorExists) (hN : NearBlocksCardBound) :
    meanSiteScoresStepBound := by
  obtain ⟨r₁, hr₁, h₁⟩ := hI
  obtain ⟨r₂, hr₂, h₂⟩ := hM
  obtain ⟨r₃, hr₃, h₃⟩ := hC
  obtain ⟨r₄, hr₄, h₄⟩ := hW
  refine ⟨fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)),
    fun c => lt_min (lt_min (hr₁ c) (hr₂ c)) (lt_min (hr₃ c) (hr₄ c)), fun T hT hrt K => ?_⟩
  obtain ⟨y₁, k₁⟩ := h₁ T hT (hrt.trans ((min_le_left _ _).trans (min_le_left _ _))) K
  obtain ⟨y₂, k₂⟩ := h₂ T hT (hrt.trans ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨y₃, k₃⟩ := h₃ T hT (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) K
  obtain ⟨y₄, k₄⟩ := h₄ T hT (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hch : 0 < T.gasRate := by
    have h1 := hT.cE_pos
    have h2 := hT.κ_pos
    have h3 := hT.σ_pos
    have h4 : 0 < T.κ₁ := by
      unfold ParameterAssignment.κ₁
      exact lt_min (by positivity) (by positivity)
    unfold ParameterAssignment.gasRate
    exact mul_pos (by positivity) (lt_min h1 (lt_min (by positivity) (by positivity)))
  have hL1 : (1 : ℝ) ≤ T.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T.side)
  obtain ⟨y₅, k₅⟩ := hFl (15 / 16 * T.gasRate) T.side T.rt (by positivity)
  obtain ⟨y₆, k₆⟩ := hFl (T.gasRate / (29 ^ 4 * (T.side : ℝ) ^ 4)) T.side T.rt (by positivity)
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (max y₅ y₆) (max T.floorMin (200 * T.B))),
    fun y hy R A hAK hAt n _ G hG p B hne hdis => ?_⟩
  have e₁ : y₁ ≤ y := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hy
  have e₂ : y₂ ≤ y := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hy
  have e₃ : y₃ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hy
  have e₄ : y₄ ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hy
  have e₅ : y₅ ≤ y := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hy
  have e₆ : y₆ ≤ y := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hy
  have e₇ : T.floorMin ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have e₈ : 200 * T.B ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hOn := hAt.onFamily
  have hresp := hAt.admissible
  have hs : ∀ w, 0 ≤ A.score w := hresp.price.nonneg
  have hb : Measurable A.score := hresp.price.borel
  have hfit := hT.fits y e₇
  have hℓ : R.params = T.stepParameters y := hOn.params_eq
  have hfitR : R.params.Admissible := hℓ ▸ hfit
  have hxy : y ≤ R.coupling := hOn.le_coupling
  have hy1 : 1 ≤ y := hfit.y₁_ge
  have hB1 : 1 ≤ T.B := hT.B_ge
  have hx0 : 0 < R.coupling := by linarith
  have hx'x : R.nextCoupling ≤ 1.01 * R.coupling := by
    have := (abs_le.mp hAt.abs_sub_le).2
    linarith
  have hs₁ : 0 ≤ A.responseParams.s₁ := by
    have hf := hresp.params_admissible
    rw [hf.s₁_eq, hf.C₀_eq]
    have h1 := hfitR.a_ge
    have h2 := hf.N₀_nonneg
    have h3 := hf.Kc_ge
    positivity
  classical
  have hmeanNN : ∀ (k : Fin p) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      1 ≤ meanSiteScore A.score (B k) Yt ωt := by
    intro k Yt ωt
    unfold meanSiteScore
    have : 0 ≤ ∑ y ∈ B k, siteScore A.score Yt ωt y := Finset.sum_nonneg fun y _ => siteScore_nonneg hs _ _ _
    have h2 : 0 ≤ ((B k).card : ℝ)⁻¹ := by positivity
    nlinarith [mul_nonneg h2 this]
  have hbk : ∀ k, (1 : ℝ) ≤ ((B k).card : ℝ) := fun k => by exact_mod_cast Finset.card_pos.mpr (hne k)
  set U : Finset (TorusSite (n * R.params.side)) := Finset.univ.biUnion B with hU
  have hpair : (↑(Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint B := fun i _ j _ hij => hdis i j hij
  have hbound : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω),
      ∏ k, meanSiteScore A.score (B k) Yt ωt ≤ Real.exp (scoreSumOn A U Yt ωt) := by
    intro Yt ωt
    have e1 : scoreSumOn A U Yt ωt = ∑ k, ∑ y ∈ B k, siteScore A.score Yt ωt y := by
      unfold scoreSumOn
      rw [hU, Finset.sum_biUnion hpair]
    rw [e1, Real.exp_sum]
    refine Finset.prod_le_prod (fun k _ => le_trans zero_le_one (hmeanNN k Yt ωt)) fun k _ => ?_
    unfold meanSiteScore
    have h0 : 0 ≤ ∑ y ∈ B k, siteScore A.score Yt ωt y := Finset.sum_nonneg fun y _ => siteScore_nonneg hs _ _ _
    have hinv : ((B k).card : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hbk k)
    have hinv0 : 0 ≤ ((B k).card : ℝ)⁻¹ := by positivity
    have := Real.add_one_le_exp (∑ y ∈ B k, siteScore A.score Yt ωt y)
    nlinarith
  have hmeasH : ∀ Yt : Finset (TorusSite (n * R.params.side)),
      Measurable fun ωt : Yt → R.labels.Ω => ∏ k, meanSiteScore A.score (B k) Yt ωt := by
    intro Yt
    refine Finset.measurable_prod _ fun k _ => ?_
    unfold meanSiteScore
    refine measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun z _ => ?_))
    unfold siteScore
    by_cases hz : z ∈ Yt
    · simp only [hz, dite_true]
      exact hb.comp (measurable_pi_apply _)
    · simp only [hz, dite_false]
      exact measurable_const
  have hint : CaseIntegrable R G.cut G.coarse G.state (prodMeanSiteScores A B) :=
    k₁ y e₁ R A hAK hAt n G hG U (fun Yt ωt => ∏ k, meanSiteScore A.score (B k) Yt ωt) hmeasH
      (fun Yt ωt => by
        rw [abs_of_nonneg (Finset.prod_nonneg fun k _ => le_trans zero_le_one (hmeanNN k Yt ωt))]
        exact hbound Yt ωt)
  refine ⟨hint, ?_⟩
  have hkeep : IsGaugeInvariantCase (prodMeanSiteScores A B) := by
    intro W Yt ωt bad b u _ _ _
    unfold prodMeanSiteScores
    refine Finset.prod_congr rfl fun k _ => ?_
    unfold meanSiteScore
    congr 2
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold siteScore
    by_cases hz : z ∈ Yt
    · simp only [hz, dite_true]
      exact hresp.price.gauge (n * R.params.side) Yt u ωt ⟨z, hz⟩
    · simp only [hz, dite_false]
  have hF : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : StepCosts.BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => prodMeanSiteScores A B p.1 Yt p.2 bad b :=
    fun Yt _ _ => (hmeasH Yt).comp measurable_snd
  rw [((k₂ y e₂ R hOn hx'x n G hG).2 _ hF hkeep hint).2]
  unfold gasExpectationOfCase
  let bk : Fin p → ℝ := fun k => ((B k).card : ℝ)
  let Sk : ∀ i : G.GasSpin, G.SpinValue i → Fin p → ℝ := fun i v k => ∑ y ∈ B k, spinSiteScore A G i y v
  let g : ∀ i : G.GasSpin, G.SpinValue i → ℝ := fun i v => ∏ k, (1 + (bk k)⁻¹ * Sk i v k)
  let Ii : G.GasSpin → Finset (Fin p) := fun i => Finset.univ.filter fun k => (B k ∩ i.1.2).Nonempty
  let wθ : GasSupport R n → ℝ := fun θ =>
    2 ^ (R.params.side ^ 4 * (supportCore R.params.side R.range θ).card) *
      clusterWeight R.params.side T.gasRate R.coupling R.range θ
  let e : G.GasSpin → ℝ := fun i => wθ i.1 * ∑ k ∈ Ii i, (bk k)⁻¹
  have hSk0 : ∀ i v k, 0 ≤ Sk i v k := fun i v k => Finset.sum_nonneg fun y _ => spinSiteScore_nonneg hs i y v
  have hbk1 : ∀ k, 1 ≤ bk k := hbk
  have hw0 : ∀ θ, 0 ≤ wθ θ := fun θ => mul_nonneg (by positivity) (Real.exp_pos _).le
  have hinv0 : ∀ k, 0 ≤ (bk k)⁻¹ := fun k => (inv_pos.mpr (by linarith [hbk1 k])).le
  have he0 : ∀ i, 0 ≤ e i := fun i => mul_nonneg (hw0 _) (Finset.sum_nonneg fun k _ => hinv0 k)
  have hgm : ∀ i, Measurable (g i) := fun i => Finset.measurable_prod _ fun k _ =>
    measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun y _ => measurable_spinSiteScore hb i y))
  have hfac1 : ∀ i v k, 1 ≤ 1 + (bk k)⁻¹ * Sk i v k := fun i v k => by
    have := mul_nonneg (hinv0 k) (hSk0 i v k)
    linarith
  have hg1 : ∀ i s, 1 ≤ g i s := fun i s => by
    have h : ∀ k ∈ (Finset.univ : Finset (Fin p)), (1 : ℝ) ≤ 1 + (bk k)⁻¹ * Sk i s k := fun k _ => hfac1 i s k
    calc (1 : ℝ) = ∏ _k : Fin p, 1 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) h
  have hga : ∀ i, g i (G.pairConstraint.vacant i) = 1 := fun i => by
    have : ∀ y, spinSiteScore A G i y (G.pairConstraint.vacant i) = 0 := fun y => rfl
    simp [g, Sk, this]
  have hweight := k₄ y e₄ R hOn hx'x n G hG (fun j => j.1.Touches ∅)
  have hsmall : G.pairConstraint.HasSmallExcess (G.referenceMeasure ∅) G.weight g e := by
    intro i σ hadm
    have hoff : ∀ (v : G.SpinValue i) (k : Fin p), k ∉ Ii i → Sk i v k = 0 := by
      intro v k hk
      refine Finset.sum_eq_zero fun y hy => ?_
      have hyθ : y ∉ i.1.2 := fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, Finset.mem_inter.mpr ⟨hy, h⟩⟩)
      rcases v with u | w
      · rfl
      · simp [spinSiteScore, hyθ]
    have hgI : ∀ v, g i v = ∏ k ∈ Ii i, (1 + (bk k)⁻¹ * Sk i v k) := by
      intro v
      symm
      refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
      rw [hoff v k hk]
      simp
    have hsumS : ∀ v, ∑ k ∈ Ii i, Sk i v k ≤ spinScore A i v := by
      intro v
      have e2 : spinScore A i v = ∑ z ∈ i.1.2, spinSiteScore A G i z v := by
        rcases v with u | w
        · simp [spinSiteScore, spinScore]
        · show ∑ z : i.1.2, A.score (w.1.2.1 z) = _
          rw [← Finset.sum_coe_sort i.1.2 (fun z => spinSiteScore A G i z (Sum.inr w))]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [spinSiteScore, Sum.elim_inr, dif_pos z.2, Subtype.coe_eta]
      rw [e2]
      have e3 : ∀ k, Sk i v k = ∑ y ∈ B k ∩ i.1.2, spinSiteScore A G i y v := by
        intro k
        symm
        refine Finset.sum_subset Finset.inter_subset_left fun y hy hn => ?_
        have hyθ : y ∉ i.1.2 := fun h => hn (Finset.mem_inter.mpr ⟨hy, h⟩)
        rcases v with u | w
        · rfl
        · simp [spinSiteScore, hyθ]
      have hpd : (↑(Ii i) : Set (Fin p)).PairwiseDisjoint fun k => B k ∩ i.1.2 := by
        intro a _ b _ hab
        exact (hdis a b hab).mono Finset.inter_subset_left Finset.inter_subset_left
      rw [Finset.sum_congr rfl fun k _ => e3 k, ← Finset.sum_biUnion hpd]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => spinSiteScore_nonneg hs i y v
      intro y hy
      obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hy
      exact (Finset.mem_inter.mp hk).2
    have hIcard : (Ii i).card ≤ R.params.side ^ 4 * (supportCore R.params.side R.range i.1).card := by
      refine le_trans ?_ (card_sites_le_side_pow_mul_card_supportCore R.range i.1)
      choose! f hf using fun k (hk : k ∈ Ii i) => (Finset.mem_filter.mp hk).2
      refine Finset.card_le_card_of_injOn f (fun k hk => (Finset.mem_inter.mp (hf k hk)).2) ?_
      intro a ha b hb' hab
      by_contra hne'
      have h1 := (Finset.mem_inter.mp (hf a ha)).1
      have h2 := (Finset.mem_inter.mp (hf b hb')).1
      rw [hab] at h1
      exact Finset.disjoint_left.mp (hdis a b hne') h1 h2
    have hpoint : ∀ v, g i v - 1 ≤
        (2 ^ (R.params.side ^ 4 * (supportCore R.params.side R.range i.1).card) * ∑ k ∈ Ii i, (bk k)⁻¹) *
          Real.exp (spinScore A i v) := by
      intro v
      obtain ⟨-, -, h3⟩ := prod_one_add_inv_mul_bounds (Ii i) (Sk i v) bk (hSk0 i v) hbk1
      rw [hgI v]
      refine h3.trans ?_
      have h4 : (2 : ℝ) ^ (Ii i).card ≤ 2 ^ (R.params.side ^ 4 * (supportCore R.params.side R.range i.1).card) :=
        pow_le_pow_right₀ (by norm_num) hIcard
      have h5 := Real.exp_le_exp.mpr (hsumS v)
      have h6 : 0 ≤ ∑ k ∈ Ii i, (bk k)⁻¹ := Finset.sum_nonneg fun k _ => hinv0 k
      calc (2 : ℝ) ^ (Ii i).card * Real.exp (∑ k ∈ Ii i, Sk i v k) * ∑ k ∈ Ii i, (bk k)⁻¹
          ≤ 2 ^ (R.params.side ^ 4 * (supportCore R.params.side R.range i.1).card) * Real.exp (spinScore A i v) *
              ∑ k ∈ Ii i, (bk k)⁻¹ := by
            gcongr
        _ = _ := by ring
    set Kc : ℝ := 2 ^ (R.params.side ^ 4 * (supportCore R.params.side R.range i.1).card) * ∑ k ∈ Ii i, (bk k)⁻¹
      with hKc
    have hKc0 : 0 ≤ Kc := mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hinv0 k)
    have hpaid := k₃ y e₃ R A hAK hAt n G hG i σ hadm
    have hei : e i = Kc * clusterWeight R.params.side T.gasRate R.coupling R.range i.1 := by
      simp only [e, wθ, hKc]
      ring
    calc ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (g i s - 1) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i s) ∂(G.referenceMeasure ∅ i)
        ≤ ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal Kc * (ENNReal.ofReal (Real.exp (spinScore A i s)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i s)) ∂(G.referenceMeasure ∅ i) := by
          refine setLIntegral_mono' (hweight.measurableSet_vacant i).compl fun v _ => ?_
          rw [← mul_assoc, ← ENNReal.ofReal_mul hKc0]
          gcongr
          exact hpoint v
      _ = ENNReal.ofReal Kc * ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (spinScore A i s)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i s) ∂(G.referenceMeasure ∅ i) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Kc * (ENNReal.ofReal (clusterWeight R.params.side T.gasRate R.coupling R.range i.1) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) := by gcongr
      _ = ENNReal.ofReal (e i) * G.pairConstraint.weightDensity G.weight
          (Function.update σ i (G.pairConstraint.vacant i)) := by
          rw [hei, ENNReal.ofReal_mul hKc0, mul_assoc]
  let ak : Fin p → ℝ := fun k => 1 + (bk k)⁻¹ * ∑ y ∈ B k, recordedSiteScore A G y
  have hst0 : ∀ y, 0 ≤ recordedSiteScore A G y := fun y => siteScore_nonneg hs _ _ _
  have hak1 : ∀ k, 1 ≤ ak k := fun k => by
    have := mul_nonneg (hinv0 k) (Finset.sum_nonneg fun y (_ : y ∈ B k) => hst0 y)
    simp only [ak]
    linarith
  have hstep : ∀ σ : G.Config,
      ∏ k, meanSiteScore A.score (B k) (configSetting G σ).support (configSetting G σ).labelling ≤
        (∏ k, ak k) * ∏ i, g i (σ i) := by
    intro σ
    have h1 : ∀ k, meanSiteScore A.score (B k) (configSetting G σ).support (configSetting G σ).labelling ≤
        ak k * ∏ i, (1 + (bk k)⁻¹ * Sk i (σ i) k) := by
      intro k
      refine le_trans ?_ (add_sum_le_mul_prod_one_add Finset.univ (ak k) (fun i => (bk k)⁻¹ * Sk i (σ i) k) (hak1 k)
        fun i => mul_nonneg (hinv0 k) (hSk0 i _ k))
      unfold meanSiteScore
      have h2 : ∑ y ∈ B k, siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y ≤
          ∑ y ∈ B k, recordedSiteScore A G y + ∑ i, Sk i (σ i) k := by
        simp only [Sk]
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun y _ => siteScore_configSetting_le hs σ y
      have h3 := mul_le_mul_of_nonneg_left h2 (hinv0 k)
      simp only [ak]
      rw [← Finset.mul_sum]
      have e0 : ((B k).card : ℝ)⁻¹ = (bk k)⁻¹ := rfl
      rw [e0]
      linarith
    calc ∏ k, meanSiteScore A.score (B k) (configSetting G σ).support (configSetting G σ).labelling
        ≤ ∏ k, (ak k * ∏ i, (1 + (bk k)⁻¹ * Sk i (σ i) k)) :=
          Finset.prod_le_prod (fun k _ => le_trans zero_le_one (hmeanNN k _ _)) fun k _ => h1 k
      _ = (∏ k, ak k) * ∏ i, g i (σ i) := by
          rw [Finset.prod_mul_distrib, Finset.prod_comm]
  have hc₀0 : 0 ≤ ∏ k, ak k := Finset.prod_nonneg fun k _ => le_trans zero_le_one (hak1 k)
  have hmean := expectation_le_mul_prod (G := G) hP hweight g e hgm hg1 hga he0 hsmall (c := ∏ k, ak k)
    (H := fun σ => weightedMean (chartDensity (configSetting G σ)) fun η =>
      prodMeanSiteScores A B ((configSetting G σ).field η) (configSetting G σ).support (configSetting G σ).labelling
        (G.badBondsOf σ) (configSetting G σ).bases) hc₀0
    (fun σ => weightedMean_const_nonneg
      (c := ∏ k, meanSiteScore A.score (B k) (configSetting G σ).support (configSetting G σ).labelling) _
      (Finset.prod_nonneg fun k _ => le_trans zero_le_one (hmeanNN k _ _)))
    (fun σ => (weightedMean_const_le
      (c := ∏ k, meanSiteScore A.score (B k) (configSetting G σ).support (configSetting G σ).labelling) _
      (Finset.prod_nonneg fun k _ => le_trans zero_le_one (hmeanNN k _ _))).trans (hstep σ))
  refine hmean.trans ?_
  have hLT : ∀ ℓ : StepParameters, ℓ = T.stepParameters y → ∀ Y : TorusSite n,
      ∑ θ ∈ supportsAtBlock ℓ.side (clusterRange R.coupling) Y,
        2 ^ (ℓ.side ^ 4 * (supportCore ℓ.side (clusterRange R.coupling) θ).card) *
          clusterWeight ℓ.side T.gasRate R.coupling (clusterRange R.coupling) θ ≤
        Real.exp (-(7 * T.gasRate * R.coupling)) := by
    rintro ℓ rfl Y
    exact sum_supportsAtBlock_weight_le hCl hN hT hch hfit hxy hx0 (fun z hz => k₅ z (e₅.trans hz))
      (k₆ R.coupling (e₆.trans hxy)).2 n Y
  have hsumk : ∀ k, (∑ i : G.GasSpin, if (B k ∩ i.1.2).Nonempty then wθ i.1 else 0) ≤
      bk k * Real.exp (-(7 * T.gasRate * R.coupling)) := by
    intro k
    have h1 := sum_spin_weight_le_card_parentBlocks_mul (G := G) wθ hw0 (hLT R.params hℓ) (B k)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have : (parentBlocks (B k)).card ≤ (B k).card := Finset.card_image_le
    show ((parentBlocks (B k)).card : ℝ) ≤ ((B k).card : ℝ)
    exact_mod_cast this
  have hsumE : ∑ i, e i ≤ p * Real.exp (-(7 * T.gasRate * R.coupling)) := by
    have e1 : ∑ i, e i =
        ∑ k : Fin p, (bk k)⁻¹ * ∑ i : G.GasSpin, if (B k ∩ i.1.2).Nonempty then wθ i.1 else 0 := by
      simp only [e, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Ii]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    rw [e1]
    calc ∑ k : Fin p, (bk k)⁻¹ * ∑ i : G.GasSpin, (if (B k ∩ i.1.2).Nonempty then wθ i.1 else 0)
        ≤ ∑ _k : Fin p, Real.exp (-(7 * T.gasRate * R.coupling)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hb0 : 0 < bk k := by linarith [hbk1 k]
          calc (bk k)⁻¹ * _ ≤ (bk k)⁻¹ * (bk k * Real.exp (-(7 * T.gasRate * R.coupling))) :=
                mul_le_mul_of_nonneg_left (hsumk k) (hinv0 k)
            _ = _ := by field_simp
      _ = _ := by simp
  have hprod : ∏ i, (1 + e i) ≤ Real.exp (p * Real.exp (-(7 * T.gasRate * R.coupling))) := by
    refine le_trans ?_ (Real.exp_le_exp.mpr hsumE)
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ => by linarith [he0 i]) fun i _ => ?_
    have := Real.add_one_le_exp (e i)
    linarith
  have hak : ∀ k, ak k ≤
      meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks (B k)) G.state.1 G.state.2 := by
    intro k
    unfold meanSiteScore
    simp only [ak]
    have hst := sum_recordedSiteScore_le_parentBlocks (A := A) (G := G) hs hs₁ (B k)
    have hP0 : (0 : ℝ) < ((parentBlocks (B k)).card : ℝ) := by
      have : (parentBlocks (B k)).Nonempty := (hne k).image _
      exact_mod_cast Finset.card_pos.mpr this
    have hPB : ((parentBlocks (B k)).card : ℝ) ≤ bk k := by
      have : (parentBlocks (B k)).card ≤ (B k).card := Finset.card_image_le
      show ((parentBlocks (B k)).card : ℝ) ≤ ((B k).card : ℝ)
      exact_mod_cast this
    have hsum0 : 0 ≤ ∑ Y ∈ parentBlocks (B k), coarseSiteScore A G.state Y :=
      le_trans (Finset.sum_nonneg fun y _ => hst0 y) hst
    have h1 : (bk k)⁻¹ * ∑ y ∈ B k, recordedSiteScore A G y ≤
        (bk k)⁻¹ * ∑ Y ∈ parentBlocks (B k), coarseSiteScore A G.state Y :=
      mul_le_mul_of_nonneg_left hst (hinv0 k)
    have h2 : (bk k)⁻¹ * ∑ Y ∈ parentBlocks (B k), coarseSiteScore A G.state Y ≤
        ((parentBlocks (B k)).card : ℝ)⁻¹ * ∑ Y ∈ parentBlocks (B k), coarseSiteScore A G.state Y :=
      mul_le_mul_of_nonneg_right (inv_anti₀ hP0 hPB) hsum0
    have e0 : ∑ Y ∈ parentBlocks (B k), coarseSiteScore A G.state Y =
        ∑ y ∈ parentBlocks (B k), siteScore (coarseLabelScore A.responseParams.s₁ A.score) G.state.1 G.state.2 y := rfl
    rw [e0] at h2
    exact add_le_add le_rfl (h1.trans h2)
  have hfinal : ∏ k, ak k ≤
      ∏ k, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks (B k)) G.state.1 G.state.2 :=
    Finset.prod_le_prod (fun k _ => le_trans zero_le_one (hak1 k)) fun k _ => hak k
  have hprod0 : 0 ≤ ∏ i, (1 + e i) := Finset.prod_nonneg fun i _ => by linarith [he0 i]
  calc (∏ k, ak k) * ∏ i, (1 + e i)
      ≤ (∏ k, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (parentBlocks (B k)) G.state.1 G.state.2) *
          Real.exp (p * Real.exp (-(7 * T.gasRate * R.coupling))) :=
        mul_le_mul hfinal hprod hprod0 (le_trans hc₀0 hfinal)
    _ = _ := mul_comm _ _
end YangMills.Construction.FreeEnergies
end
