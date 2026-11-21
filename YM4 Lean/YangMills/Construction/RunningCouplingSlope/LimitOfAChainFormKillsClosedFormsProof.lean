import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.RunningCouplingSlope.LatticeResponseOfAKilledFormProof
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorusProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.GreenKernelsOfAChainFormProof
import YangMills.Construction.RunningCouplingSlope.LimitOfAChainFormKillsClosedForms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.FlatLinearization YangMills.Construction.SlopeCoefficient
namespace YangMills.Construction.RunningCouplingSlope
namespace FlowKernelLimit
private theorem natAbs_le_offsetNorm (a : Fin 4 → ℤ) (i : Fin 4) : (a i).natAbs ≤ offsetNorm a := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem offsetNormReal_nonneg (a : Fin 4 → ℤ) : 0 ≤ offsetNormReal a := Nat.cast_nonneg _
private theorem offsetNorm_neg (a : Fin 4 → ℤ) : offsetNorm (-a) = offsetNorm a := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
private theorem offsetNormReal_add_le (a c : Fin 4 → ℤ) :
    offsetNormReal (a + c) ≤ offsetNormReal a + offsetNormReal c := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.offsetNormReal_add_le <;> assumption
private theorem offsetNormReal_single_le (i : Fin 4) :
    offsetNormReal (Pi.single i 1 : Fin 4 → ℤ) ≤ 1 := by apply _root_.YangMills.DeltaSharedProofs.p502556 <;> assumption
private theorem valMinAbs_intCast_of_lt {m : ℕ} [NeZero m] {e : ℤ} (he : 2 * e.natAbs < m) :
    ((e : ZMod m)).valMinAbs = e := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusOffsets.valMinAbs_intCast_of_lt <;> assumption
private theorem supDist_siteOfInt {m : ℕ} [NeZero m] (z w : Fin 4 → ℤ)
    (hm : 2 * offsetNorm (z - w) < m) :
    supDist (siteOfInt z : TorusSite m) (siteOfInt w) = offsetNorm (z - w) := by apply _root_.YangMills.SharedProofs.p74560 <;> assumption
private theorem siteOfInt_add {m : ℕ} (e e' : Fin 4 → ℤ) :
    (siteOfInt (e + e') : TorusSite m) = siteOfInt e + siteOfInt e' := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
private theorem siteOfInt_add_single {m : ℕ} (z : Fin 4 → ℤ) (i : Fin 4) :
    (siteOfInt (z + Pi.single i 1) : TorusSite m) = siteOfInt z + unitStep m i := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [siteOfInt, unitStep]
  · simp [siteOfInt, unitStep, hk]
abbrev _root_.YangMills.SharedProofs.p8359 := @siteOfInt_add_single
private theorem siteOfInt_neg_sub_single {m : ℕ} (z : Fin 4 → ℤ) (i : Fin 4) :
    (siteOfInt (-z - Pi.single i 1) : TorusSite m) = -siteOfInt z - unitStep m i := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [siteOfInt, unitStep]
  · simp [siteOfInt, unitStep, hk]
private theorem bondFrom_zero_fst {m : ℕ} (b : LatticeBond) :
    (bondFrom 0 b : TorusBond m).1 = siteOfInt b.1 := by
  simp [bondFrom]
private theorem latticeKernel_exp_decay {h : BondKernel} {hl : LatticeBond → LatticeBond → ℝ}
    {M θ : ℝ}
    (hdec : ∀ᶠ m in Filter.atTop, ∀ b c : TorusBond m,
      |h m b c| ≤ M * Real.exp (-(θ * supDist b.1 c.1)))
    (hlim : TendstoLatticeKernel h hl) (b c : LatticeBond) :
    |hl b c| ≤ M * Real.exp (-(θ * offsetNormReal (b.1 - c.1))) := by
  refine le_of_tendsto (hlim b c).abs ?_
  filter_upwards [hdec, Filter.eventually_gt_atTop (2 * offsetNorm (b.1 - c.1))] with m hm hbig
  have : NeZero m := ⟨by omega⟩
  have h1 := hm (bondFrom 0 b) (bondFrom 0 c)
  rw [bondFrom_zero_fst, bondFrom_zero_fst, supDist_siteOfInt _ _ hbig] at h1
  exact h1
private theorem hasSum_zero_of_torus_annihilates (hS : TendstoLatticeSumOfTorusSums)
    {h : BondKernel} {hl : LatticeBond → LatticeBond → ℝ} {M θ : ℝ} (hθ : 0 < θ)
    (hdec : ∀ᶠ m in Filter.atTop, ∀ b c : TorusBond m,
      |h m b c| ≤ M * Real.exp (-(θ * supDist b.1 c.1)))
    (hlim : TendstoLatticeKernel h hl) (b : LatticeBond)
    (w : (m : ℕ) → TorusBond m → ℝ) (wl : LatticeBond → ℝ) (W : ℝ)
    (hw : ∀ᶠ m in Filter.atTop, ∀ c : TorusBond m, |w m c| ≤ W)
    (hwl : ∀ c : LatticeBond, ∀ᶠ m in Filter.atTop, w m (bondFrom 0 c) = wl c)
    (h0 : ∀ᶠ m in Filter.atTop, ∀ [NeZero m],
      ∑ c : TorusBond m, h m (bondFrom 0 b) c * w m c = 0) :
    HasSum (fun c => hl b c * wl c) 0 := by
  have key := hS (fun n => n) (M * W * Real.exp (θ * offsetNormReal b.1)) θ
    (fun m c => h m (bondFrom 0 b) c * w m c) (fun c => hl b c * wl c) (fun _ => 0)
    Filter.tendsto_id hθ ?_ ?_ ?_
  · have e : ∑' c, hl b c * wl c = 0 := tendsto_nhds_unique key.2 tendsto_const_nhds
    have := key.1.hasSum
    rwa [e] at this
  · filter_upwards [hdec, hw, Filter.eventually_gt_atTop 0] with m hm hwm hpos c
    have : NeZero m := ⟨by omega⟩
    have h1 := hm (bondFrom 0 b) c
    have h2 := hwm c
    have hM : 0 ≤ M := by
      have := (abs_nonneg _).trans h1
      exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 this
    have hW : 0 ≤ W := (abs_nonneg _).trans h2
    have hd : (supDist c.1 (0 : TorusSite m) : ℝ) ≤
        (supDist (bondFrom 0 b : TorusBond m).1 c.1 : ℝ) + offsetNormReal b.1 := by
      have t1 := supDist_triangle c.1 (bondFrom 0 b : TorusBond m).1 (0 : TorusSite m)
      have t2 : supDist (bondFrom 0 b : TorusBond m).1 (0 : TorusSite m) ≤ offsetNorm b.1 := by
        rw [supDist_comm, bondFrom_zero_fst]
        have := supDist_add_siteOfInt_le (0 : TorusSite m) b.1 (offsetNorm b.1)
          (natAbs_le_offsetNorm b.1)
        rwa [zero_add] at this
      rw [supDist_comm c.1 (bondFrom 0 b : TorusBond m).1] at t1
      unfold offsetNormReal
      exact_mod_cast t1.trans (Nat.add_le_add_left t2 _)
    have hexp : Real.exp (-(θ * supDist (bondFrom 0 b : TorusBond m).1 c.1)) ≤
        Real.exp (θ * offsetNormReal b.1) * Real.exp (-(θ * supDist c.1 (0 : TorusSite m))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left hd hθ.le]
    calc |h m (bondFrom 0 b) c * w m c| = |h m (bondFrom 0 b) c| * |w m c| := abs_mul _ _
      _ ≤ (M * Real.exp (-(θ * supDist (bondFrom 0 b : TorusBond m).1 c.1))) * W :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ (M * (Real.exp (θ * offsetNormReal b.1) *
            Real.exp (-(θ * supDist c.1 (0 : TorusSite m))))) * W := by
        gcongr
      _ = M * W * Real.exp (θ * offsetNormReal b.1) *
            Real.exp (-(θ * supDist c.1 (0 : TorusSite m))) := by
        ring
  · intro c
    refine ((hlim b c).mul_const (wl c)).congr' ?_
    filter_upwards [hwl c] with m hm
    rw [hm]
  · filter_upwards [h0] with m hm
    intro _
    exact (hm).symm
private theorem annihilates_constantOneForm (hS : TendstoLatticeSumOfTorusSums)
    {h : BondKernel} {hl : LatticeBond → LatticeBond → ℝ} {M θ : ℝ} (hc : IsFlowKernel h)
    (hθ : 0 < θ)
    (hdec : ∀ᶠ m in Filter.atTop, ∀ b c : TorusBond m,
      |h m b c| ≤ M * Real.exp (-(θ * supDist b.1 c.1)))
    (hlim : TendstoLatticeKernel h hl) (ν : Fin 4) (b : LatticeBond) :
    HasSum (fun c => hl b c * constantOneForm ν c) 0 := by
  refine hasSum_zero_of_torus_annihilates hS hθ hdec hlim b
    (fun _ c => if c.2 = ν then 1 else 0) (constantOneForm ν) 1
    (Filter.Eventually.of_forall fun _ c => ?_) (fun c => Filter.Eventually.of_forall fun _ => ?_) ?_
  · split_ifs <;> simp
  · simp [bondFrom, constantOneForm]
  · filter_upwards [hc.annihilates_constants] with m hm
    intro _
    exact hm _ ν
private def liftToTorus (φ : (Fin 4 → ℤ) → ℝ) {m : ℕ} (x : TorusSite m) : ℝ :=
  φ fun i => (x i).valMinAbs
private theorem liftToTorus_siteOfInt (φ : (Fin 4 → ℤ) → ℝ) {m : ℕ} [NeZero m] (z : Fin 4 → ℤ)
    (hm : 2 * offsetNorm z < m) : liftToTorus φ (siteOfInt z : TorusSite m) = φ z := by
  unfold liftToTorus
  congr 1
  funext i
  exact valMinAbs_intCast_of_lt (by have := natAbs_le_offsetNorm z i; omega)
private theorem annihilates_gradient_of_bounded (hS : TendstoLatticeSumOfTorusSums)
    {h : BondKernel} {hl : LatticeBond → LatticeBond → ℝ} {M θ : ℝ} (hc : IsFlowKernel h)
    (hθ : 0 < θ)
    (hdec : ∀ᶠ m in Filter.atTop, ∀ b c : TorusBond m,
      |h m b c| ≤ M * Real.exp (-(θ * supDist b.1 c.1)))
    (hlim : TendstoLatticeKernel h hl) (φ : (Fin 4 → ℤ) → ℝ) (C : ℝ) (hφ : ∀ z, |φ z| ≤ C)
    (b : LatticeBond) : HasSum (fun c => hl b c * latticeGradient φ c) 0 := by
  refine hasSum_zero_of_torus_annihilates hS hθ hdec hlim b
    (fun m c => liftToTorus φ (c.1 + unitStep m c.2) - liftToTorus φ c.1) (latticeGradient φ)
    (2 * C) (Filter.Eventually.of_forall fun m c => ?_) (fun c => ?_) ?_
  · have h1 := abs_le.1 (hφ fun i => ((c.1 + unitStep m c.2) i).valMinAbs)
    have h2 := abs_le.1 (hφ fun i => (c.1 i).valMinAbs)
    unfold liftToTorus
    exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  · filter_upwards [Filter.eventually_gt_atTop
      (2 * offsetNorm c.1 + 2 * offsetNorm (c.1 + Pi.single c.2 1))] with m hm
    have : NeZero m := ⟨by omega⟩
    have e1 : (bondFrom 0 c : TorusBond m).1 + unitStep m (bondFrom 0 c : TorusBond m).2 =
        siteOfInt (c.1 + Pi.single c.2 1) := by
      rw [siteOfInt_add_single, bondFrom_zero_fst]
      rfl
    show liftToTorus φ ((bondFrom 0 c : TorusBond m).1 + unitStep m (bondFrom 0 c : TorusBond m).2) -
      liftToTorus φ (bondFrom 0 c : TorusBond m).1 = latticeGradient φ c
    rw [e1, bondFrom_zero_fst, liftToTorus_siteOfInt φ _ (by omega),
      liftToTorus_siteOfInt φ _ (by omega)]
    rfl
  · filter_upwards [hc.annihilates_gradients] with m hm
    intro _
    exact hm (bondFrom 0 b) (liftToTorus φ)
private theorem summable_exp_neg_offsetNormReal {r : ℝ} (hr : 0 < r) :
    Summable fun z : Fin 4 → ℤ => Real.exp (-(r * offsetNormReal z)) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.summable_exp_neg_offsetNormReal <;> assumption
private theorem summable_exp_decay_mul_pow {θ : ℝ} (hθ : 0 < θ) (b : LatticeBond) (k : ℝ)
    (hk : 0 ≤ k) (K : ℕ) :
    Summable fun c : LatticeBond =>
      Real.exp (-(θ * offsetNormReal (b.1 - c.1))) * (k + offsetNormReal c.1) ^ K := by
  have hr : 0 < θ / 2 := by positivity
  have hinj : Function.Injective fun z : Fin 4 → ℤ => b.1 - z := sub_right_injective
  have hz : Summable fun z : Fin 4 → ℤ => Real.exp (-(θ / 2 * offsetNormReal (b.1 - z))) :=
    (summable_exp_neg_offsetNormReal hr).comp_injective hinj
  have hone : Summable fun _ : Fin 4 => (1 : ℝ) := (hasSum_fintype _).summable
  have hbond : Summable fun c : LatticeBond =>
      Real.exp (-(θ / 2 * offsetNormReal (b.1 - c.1))) * (1 : ℝ) :=
    hz.mul_of_nonneg hone (fun _ => (Real.exp_pos _).le) fun _ => zero_le_one
  set A : ℝ := (K.factorial : ℝ) * ((θ / 2)⁻¹) ^ K *
    Real.exp (θ / 2 * (k + offsetNormReal b.1)) with hA
  refine Summable.of_nonneg_of_le (fun c => ?_) (fun c => ?_) (hbond.mul_left A)
  · have := offsetNormReal_nonneg c.1
    positivity
  · set D := offsetNormReal (b.1 - c.1) with hD
    have hx0 : 0 ≤ k + offsetNormReal c.1 := add_nonneg hk (offsetNormReal_nonneg _)
    have hcb : offsetNormReal c.1 ≤ offsetNormReal b.1 + D := by
      have e : c.1 = b.1 + -(b.1 - c.1) := by abel
      have h1 := offsetNormReal_add_le b.1 (-(b.1 - c.1))
      rw [← e] at h1
      have h2 : offsetNormReal (-(b.1 - c.1)) = D := by
        unfold offsetNormReal at *
        rw [hD, offsetNorm_neg]
      linarith
    have hp := Real.pow_div_factorial_le_exp _ (mul_nonneg hr.le hx0) K
    have hfac : (0 : ℝ) < (K.factorial : ℝ) := by exact_mod_cast K.factorial_pos
    have hpow : (k + offsetNormReal c.1) ^ K ≤
        (K.factorial : ℝ) * ((θ / 2)⁻¹) ^ K * Real.exp (θ / 2 * (k + offsetNormReal c.1)) := by
      rw [div_le_iff₀ hfac, mul_pow] at hp
      have hi : (0 : ℝ) < ((θ / 2)⁻¹) ^ K := by positivity
      have e : (k + offsetNormReal c.1) ^ K =
          ((θ / 2)⁻¹) ^ K * ((θ / 2) ^ K * (k + offsetNormReal c.1) ^ K) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
      rw [e]
      calc ((θ / 2)⁻¹) ^ K * ((θ / 2) ^ K * (k + offsetNormReal c.1) ^ K)
          ≤ ((θ / 2)⁻¹) ^ K *
              (Real.exp (θ / 2 * (k + offsetNormReal c.1)) * (K.factorial : ℝ)) := by
            gcongr
        _ = _ := by ring
    have hexp : Real.exp (-(θ * D)) * Real.exp (θ / 2 * (k + offsetNormReal c.1)) ≤
        Real.exp (θ / 2 * (k + offsetNormReal b.1)) * Real.exp (-(θ / 2 * D)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left hcb hr.le]
    calc Real.exp (-(θ * D)) * (k + offsetNormReal c.1) ^ K
        ≤ Real.exp (-(θ * D)) * ((K.factorial : ℝ) * ((θ / 2)⁻¹) ^ K *
            Real.exp (θ / 2 * (k + offsetNormReal c.1))) := by gcongr
      _ = (K.factorial : ℝ) * ((θ / 2)⁻¹) ^ K *
            (Real.exp (-(θ * D)) * Real.exp (θ / 2 * (k + offsetNormReal c.1))) := by ring
      _ ≤ (K.factorial : ℝ) * ((θ / 2)⁻¹) ^ K *
            (Real.exp (θ / 2 * (k + offsetNormReal b.1)) * Real.exp (-(θ / 2 * D))) := by gcongr
      _ = A * (Real.exp (-(θ / 2 * D)) * 1) := by rw [hA]; ring
private theorem abs_latticeGradient_le {ψ : (Fin 4 → ℤ) → ℝ} {B : ℝ} {K : ℕ}
    (hψ : ∀ z, |ψ z| ≤ B * (2 + offsetNormReal z) ^ K) (hB : 0 ≤ B) (c : LatticeBond) :
    |latticeGradient ψ c| ≤ 2 * B * (3 + offsetNormReal c.1) ^ K := by
  have hn := offsetNormReal_nonneg c.1
  have h1 : offsetNormReal (c.1 + Pi.single c.2 1) ≤ offsetNormReal c.1 + 1 :=
    (offsetNormReal_add_le _ _).trans (by linarith [offsetNormReal_single_le c.2])
  have h2 : (2 + offsetNormReal (c.1 + Pi.single c.2 1)) ^ K ≤ (3 + offsetNormReal c.1) ^ K :=
    pow_le_pow_left₀ (add_nonneg zero_le_two (offsetNormReal_nonneg _)) (by linarith) K
  have h3 : (2 + offsetNormReal c.1) ^ K ≤ (3 + offsetNormReal c.1) ^ K :=
    pow_le_pow_left₀ (by linarith) (by linarith) K
  have h4 := (hψ (c.1 + Pi.single c.2 1)).trans (mul_le_mul_of_nonneg_left h2 hB)
  have h5 := (hψ c.1).trans (mul_le_mul_of_nonneg_left h3 hB)
  unfold latticeGradient
  calc |ψ (c.1 + Pi.single c.2 1) - ψ c.1| ≤ |ψ (c.1 + Pi.single c.2 1)| + |ψ c.1| :=
        abs_sub _ _
    _ ≤ 2 * B * (3 + offsetNormReal c.1) ^ K := by linarith
private theorem annihilates_gradient_of_polynomialGrowth (hS : TendstoLatticeSumOfTorusSums)
    {h : BondKernel} {hl : LatticeBond → LatticeBond → ℝ} {M θ : ℝ} (hc : IsFlowKernel h)
    (hθ : 0 < θ)
    (hdec : ∀ᶠ m in Filter.atTop, ∀ b c : TorusBond m,
      |h m b c| ≤ M * Real.exp (-(θ * supDist b.1 c.1)))
    (hlim : TendstoLatticeKernel h hl) (φ : (Fin 4 → ℤ) → ℝ) (hφ : HasPolynomialGrowth φ)
    (b : LatticeBond) : HasSum (fun c => hl b c * latticeGradient φ c) 0 := by
  classical
  obtain ⟨C, p, hCp⟩ := hφ
  obtain ⟨K, hK⟩ := exists_nat_ge p
  have hpoly : ∀ z, |φ z| ≤ |C| * (2 + offsetNormReal z) ^ K := by
    intro z
    have hn := offsetNormReal_nonneg z
    have h1 : (1 + offsetNormReal z) ^ p ≤ (1 + offsetNormReal z) ^ (K : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hK
    rw [Real.rpow_natCast] at h1
    have h2 : (1 + offsetNormReal z) ^ K ≤ (2 + offsetNormReal z) ^ K :=
      pow_le_pow_left₀ (by linarith) (by linarith) K
    have h3 : 0 ≤ (1 + offsetNormReal z) ^ p := Real.rpow_nonneg (by linarith) _
    calc |φ z| ≤ C * (1 + offsetNormReal z) ^ p := hCp z
      _ ≤ |C| * (1 + offsetNormReal z) ^ p := mul_le_mul_of_nonneg_right (le_abs_self C) h3
      _ ≤ |C| * (2 + offsetNormReal z) ^ K :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C)
  set cut : ℕ → (Fin 4 → ℤ) → ℝ := fun R z => if offsetNorm z ≤ R then φ z else 0 with hcut
  have hcut_le : ∀ R z, |cut R z| ≤ |C| * (2 + offsetNormReal z) ^ K := by
    intro R z
    simp only [hcut]
    split_ifs
    · exact hpoly z
    · have := offsetNormReal_nonneg z
      rw [abs_zero]
      positivity
  have hcut_bd : ∀ R z, |cut R z| ≤ |C| * (2 + (R : ℝ)) ^ K := by
    intro R z
    simp only [hcut]
    split_ifs with hz
    · refine (hpoly z).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg C))
      have h1 : offsetNormReal z ≤ (R : ℝ) := by
        unfold offsetNormReal
        exact_mod_cast hz
      exact pow_le_pow_left₀ (add_nonneg zero_le_two (offsetNormReal_nonneg _)) (by linarith) K
    · rw [abs_zero]
      positivity
  have hzero : ∀ R, HasSum (fun c => hl b c * latticeGradient (cut R) c) 0 := fun R =>
    annihilates_gradient_of_bounded hS hc hθ hdec hlim (cut R) _ (hcut_bd R) b
  have hM : 0 ≤ M := by
    have := (abs_nonneg _).trans (latticeKernel_exp_decay hdec hlim b b)
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 this
  set bound : LatticeBond → ℝ := fun c =>
    (M * (2 * |C|)) * (Real.exp (-(θ * offsetNormReal (b.1 - c.1))) *
      (3 + offsetNormReal c.1) ^ K) with hbound
  have hsum : Summable bound := (summable_exp_decay_mul_pow hθ b 3 (by norm_num) K).mul_left _
  have hterm : ∀ (ψ : (Fin 4 → ℤ) → ℝ), (∀ z, |ψ z| ≤ |C| * (2 + offsetNormReal z) ^ K) →
      ∀ c, ‖hl b c * latticeGradient ψ c‖ ≤ bound c := by
    intro ψ hψ c
    have h1 := latticeKernel_exp_decay hdec hlim b c
    have h2 := abs_latticeGradient_le hψ (abs_nonneg C) c
    rw [Real.norm_eq_abs, abs_mul]
    calc |hl b c| * |latticeGradient ψ c|
        ≤ (M * Real.exp (-(θ * offsetNormReal (b.1 - c.1)))) *
            (2 * |C| * (3 + offsetNormReal c.1) ^ K) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = bound c := by simp only [hbound]; ring
  have hlimit := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (R : ℕ) c => hl b c * latticeGradient (cut R) c)
    (g := fun c => hl b c * latticeGradient φ c) hsum
    (fun c => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop
        (offsetNorm c.1 + offsetNorm (c.1 + Pi.single c.2 1))] with R hR
      have e1 : offsetNorm c.1 ≤ R := by omega
      have e2 : offsetNorm (c.1 + Pi.single c.2 1) ≤ R := by omega
      simp only [latticeGradient, hcut, if_pos e1, if_pos e2])
    (Filter.Eventually.of_forall fun R c => hterm (cut R) (hcut_le R) c)
  have e0 : (fun R : ℕ => ∑' c, hl b c * latticeGradient (cut R) c) = fun _ => 0 := by
    funext R
    exact (hzero R).tsum_eq
  rw [e0] at hlimit
  have e : ∑' c, hl b c * latticeGradient φ c = 0 :=
    tendsto_nhds_unique hlimit tendsto_const_nhds
  have hs : Summable fun c => hl b c * latticeGradient φ c :=
    Summable.of_norm_bounded hsum (hterm φ hpoly)
  have := hs.hasSum
  rwa [e] at this
private theorem latticeKernel_translate {h : BondKernel} {hl : LatticeBond → LatticeBond → ℝ}
    (hc : IsFlowKernel h) (hlim : TendstoLatticeKernel h hl) (u : Fin 4 → ℤ)
    (b c : LatticeBond) :
    hl (b.1 + u, b.2) (c.1 + u, c.2) = hl b c := by
  refine tendsto_nhds_unique (hlim _ _) ((hlim b c).congr' ?_)
  filter_upwards [hc.translation_invariant] with m hm
  have e : ∀ d : LatticeBond, (bondFrom 0 (d.1 + u, d.2) : TorusBond m) =
      ((bondFrom 0 d : TorusBond m).1 + siteOfInt u, (bondFrom 0 d : TorusBond m).2) := by
    intro d
    refine Prod.ext ?_ rfl
    rw [bondFrom_zero_fst, bondFrom_zero_fst, siteOfInt_add]
  rw [e, e]
  exact (hm _ _ _).symm
private def reflectLatticeBond (c : LatticeBond) : LatticeBond := (-c.1 - Pi.single c.2 1, c.2)
private theorem reflectLatticeBond_reflectLatticeBond (c : LatticeBond) :
    reflectLatticeBond (reflectLatticeBond c) = c := by
  refine Prod.ext ?_ rfl
  simp [reflectLatticeBond]
private theorem latticeKernel_reflect {h : BondKernel} {hl : LatticeBond → LatticeBond → ℝ}
    (hc : IsFlowKernel h) (hlim : TendstoLatticeKernel h hl) (b c : LatticeBond) :
    hl (reflectLatticeBond b) (reflectLatticeBond c) = hl b c := by
  refine tendsto_nhds_unique (hlim _ _) ((hlim b c).congr' ?_)
  filter_upwards [hc.reflection_invariant] with m hm
  have e : ∀ d : LatticeBond, (bondFrom 0 (reflectLatticeBond d) : TorusBond m) =
      reflectedBond (bondFrom 0 d : TorusBond m) := by
    intro d
    refine Prod.ext ?_ rfl
    rw [bondFrom_zero_fst]
    show (siteOfInt (-d.1 - Pi.single d.2 1) : TorusSite m) =
      -(bondFrom 0 d : TorusBond m).1 - unitStep m (bondFrom 0 d : TorusBond m).2
    rw [bondFrom_zero_fst, siteOfInt_neg_sub_single]
    rfl
  rw [e, e]
  exact (hm _ _).symm
private theorem annihilates_linearForm {h : BondKernel} {hl : LatticeBond → LatticeBond → ℝ}
    {M θ : ℝ} (hc : IsFlowKernel h) (hθ : 0 < θ) (hlim : TendstoLatticeKernel h hl)
    (hdecl : ∀ b c : LatticeBond, |hl b c| ≤ M * Real.exp (-(θ * offsetNormReal (b.1 - c.1))))
    (hconst : ∀ b : LatticeBond, HasSum (fun c => hl b c * constantOneForm secondAxis c) 0)
    (b₀ : LatticeBond) :
    HasSum (fun c => hl b₀ c * (((c.1 0 : ℤ) : ℝ) * constantOneForm secondAxis c)) 0 := by
  set f : LatticeBond → ℝ := fun c => ((c.1 0 : ℤ) : ℝ) * constantOneForm secondAxis c with hf
  have hsum : ∀ b, Summable fun c => hl b c * f c := by
    intro b
    refine Summable.of_norm_bounded
      (((summable_exp_decay_mul_pow hθ b 0 le_rfl 1).mul_left M)) fun c => ?_
    have h1 := hdecl b c
    have h2 : |f c| ≤ (0 + offsetNormReal c.1) ^ 1 := by
      have h3 : |((c.1 0 : ℤ) : ℝ)| ≤ offsetNormReal c.1 := by
        have := natAbs_le_offsetNorm c.1 0
        have h4 : ((c.1 0).natAbs : ℝ) ≤ (offsetNorm c.1 : ℝ) := by exact_mod_cast this
        rwa [Nat.cast_natAbs, Int.cast_abs] at h4
      have h5 : |constantOneForm secondAxis c| ≤ 1 := by
        unfold constantOneForm
        split_ifs <;> simp
      simp only [hf, abs_mul, zero_add, pow_one]
      calc |((c.1 0 : ℤ) : ℝ)| * |constantOneForm secondAxis c| ≤ offsetNormReal c.1 * 1 :=
            mul_le_mul h3 h5 (abs_nonneg _) (offsetNormReal_nonneg _)
        _ = offsetNormReal c.1 := mul_one _
    rw [Real.norm_eq_abs, abs_mul]
    calc |hl b c| * |f c|
        ≤ (M * Real.exp (-(θ * offsetNormReal (b.1 - c.1)))) * (0 + offsetNormReal c.1) ^ 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
      _ = _ := by ring
  set w : LatticeBond → ℝ := fun b => ∑' c, hl b c * f c with hw
  have htr : ∀ (b : LatticeBond) (u : Fin 4 → ℤ), w (b.1 + u, b.2) = w b := by
    intro b u
    let τ : LatticeBond ≃ LatticeBond := (Equiv.addRight u).prodCongr (Equiv.refl _)
    have e1 : w (b.1 + u, b.2) = ∑' c, hl (b.1 + u, b.2) (τ c) * f (τ c) :=
      (τ.tsum_eq fun c => hl (b.1 + u, b.2) c * f c).symm
    have e2 : ∀ c, hl (b.1 + u, b.2) (τ c) * f (τ c) =
        hl b c * f c + ((u 0 : ℤ) : ℝ) * (hl b c * constantOneForm secondAxis c) := by
      intro c
      have e3 : hl (b.1 + u, b.2) (τ c) = hl b c := latticeKernel_translate hc hlim u b c
      have e4 : f (τ c) =
          (((c.1 0 : ℤ) : ℝ) + ((u 0 : ℤ) : ℝ)) * constantOneForm secondAxis c := by
        simp [hf, τ, constantOneForm]
      rw [e3, e4, hf]
      ring
    have e5 := ((hsum b).hasSum.add ((hconst b).mul_left ((u 0 : ℤ) : ℝ))).tsum_eq
    rw [e1, tsum_congr e2, e5]
    simp [hw]
  have hneg : ∀ c, f (reflectLatticeBond c) = - f c := by
    intro c
    simp only [hf, reflectLatticeBond, constantOneForm]
    by_cases hcd : c.2 = secondAxis
    · have e : (Pi.single c.2 1 : Fin 4 → ℤ) 0 = 0 := by
        rw [hcd]
        simp [secondAxis]
      simp only [if_pos hcd]
      simp [e]
    · simp [hcd]
  have hinv : ∀ b, w (reflectLatticeBond b) = - w b := by
    intro b
    let ι : LatticeBond ≃ LatticeBond :=
      Function.Involutive.toPerm reflectLatticeBond reflectLatticeBond_reflectLatticeBond
    have e1 : w (reflectLatticeBond b) =
        ∑' c, hl (reflectLatticeBond b) (ι c) * f (ι c) :=
      (ι.tsum_eq fun c => hl (reflectLatticeBond b) c * f c).symm
    have e2 : ∀ c, hl (reflectLatticeBond b) (ι c) * f (ι c) = - (hl b c * f c) := by
      intro c
      have e3 : hl (reflectLatticeBond b) (ι c) = hl b c := latticeKernel_reflect hc hlim b c
      have e4 : f (ι c) = - f c := hneg c
      rw [e3, e4]
      ring
    rw [e1, tsum_congr e2, tsum_neg]
  have hzero : w b₀ = 0 := by
    have e : reflectLatticeBond b₀ = (b₀.1 + (-b₀.1 - Pi.single b₀.2 1 - b₀.1), b₀.2) := by
      refine Prod.ext ?_ rfl
      show -b₀.1 - Pi.single b₀.2 1 = b₀.1 + (-b₀.1 - Pi.single b₀.2 1 - b₀.1)
      abel
    have h1 := hinv b₀
    rw [e, htr] at h1
    linarith
  have := (hsum b₀).hasSum
  have e : ∑' c, hl b₀ c * f c = 0 := hzero
  rwa [e] at this
end FlowKernelLimit
open FlowKernelLimit in
theorem flowKernelLimitAnnihilatesClosed (hS : TendstoLatticeSumOfTorusSums) :
    flowKernelLimitAnnihilatesClosedStatement := by
  intro h hl hc hlim
  obtain ⟨M, θ, hθ, hdec⟩ := hc.decay
  have hconst := fun ν b => annihilates_constantOneForm hS hc hθ hdec hlim ν b
  exact ⟨⟨M, θ, hθ, latticeKernel_exp_decay hdec hlim⟩, hconst,
    fun φ hφ b => annihilates_gradient_of_polynomialGrowth hS hc hθ hdec hlim φ hφ b,
    annihilates_linearForm hc hθ hlim (latticeKernel_exp_decay hdec hlim) (hconst secondAxis)⟩
end YangMills.Construction.RunningCouplingSlope
end
