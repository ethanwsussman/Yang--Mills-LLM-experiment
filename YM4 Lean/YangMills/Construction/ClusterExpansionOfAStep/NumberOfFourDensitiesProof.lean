import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.PotentialsInAPatch
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.NumberOfFourDensities
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocalProof
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImageProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.TorusLumps.SumOfFourCurvature
open BlockAverages TorusFields
variable {n : ℕ}
abbrev restrictToBonds {k : ℕ} (G : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) : (Fin k → ℝ) → ℝ := fun σ => G (perturb c X σ W)
theorem iteratedFDeriv_comp_continuousLinearMap_zero {k : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (D : E →L[ℝ] E) (hf : ContDiffAt ℝ k f (D 0)) :
    iteratedFDeriv ℝ k (f ∘ D) 0 =
      (iteratedFDeriv ℝ k f (D 0)).compContinuousLinearMap fun _ => D := by apply _root_.YangMills.SharedProofs.p19667 <;> assumption
theorem perturb_smul {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (lam σ : Fin k → ℝ) (W : TorusField n) :
    perturb c (fun l => lam l • X l) σ W = perturb c X (fun l => lam l * σ l) W := by apply _root_.YangMills.SharedProofs.p106687 <;> assumption
theorem mixedDeriv_smul {k : ℕ} (G : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (lam : Fin k → ℝ)
    (hs : ContDiffAt ℝ k (restrictToBonds G W c X) 0) :
    mixedDeriv G W c (fun l => lam l • X l) = (∏ l, lam l) * mixedDeriv G W c X := by apply _root_.YangMills.DeltaSharedProofs.p501338 <;> assumption
theorem mixedDeriv_pair_smul (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 2 → TorusBond n)
    (X X' : imaginaryQuaternions) (a a' : ℝ)
    (hs : ContDiffAt ℝ (2 : ℕ) (restrictToBonds G W c ![X, X']) 0) :
    mixedDeriv G W c ![a • X, a' • X'] = a * a' * mixedDeriv G W c ![X, X'] := by apply _root_.YangMills.DeltaSharedProofs.p502158 <;> assumption
theorem mixedDeriv_add {k : ℕ} (G G' : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions)
    (h : ContDiffAt ℝ k (restrictToBonds G W c X) 0) (h' : ContDiffAt ℝ k (restrictToBonds G' W c X) 0) :
    mixedDeriv (fun V => G V + G' V) W c X = mixedDeriv G W c X + mixedDeriv G' W c X := by
  unfold mixedDeriv
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) (x := (0 : Fin k → ℝ)) h h'
  have e : (fun σ : Fin k → ℝ => (fun V => G V + G' V) (perturb c X σ W)) =
      restrictToBonds G W c X + restrictToBonds G' W c X := rfl
  rw [e, this]
  rfl
theorem mixedDeriv_const {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun _ : TorusField n => κ) W c X = 0 := by
  unfold mixedDeriv
  have h : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => κ) = 0 :=
    iteratedFDeriv_const_of_ne (by omega) κ
  rw [h]
  rfl
theorem mixedDeriv_sub_const {k : ℕ} (hk : 1 ≤ k) (G : TorusField n → ℝ) (κ : ℝ) (W : TorusField n)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (h : ContDiffAt ℝ k (restrictToBonds G W c X) 0) :
    mixedDeriv (fun V => G V - κ) W c X = mixedDeriv G W c X := by apply _root_.YangMills.DeltaSharedProofs.p1303 <;> assumption
theorem mixedDeriv_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
theorem trivialField_isCold {s : ℝ} (hs : 0 < s) (n : ℕ) : IsCold s (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
theorem fieldsAgreeNear_trivialField {n n' : ℕ} (y : TorusSite n) (y' : TorusSite n') (m : ℕ) :
    FieldsAgreeNear (trivialField n) (trivialField n') y y' m := fun _ _ => rfl
variable {ℓ : StepParameters} {h : LocalDensity}
theorem contDiffAt_restrictToBonds (hp : IsAdmissibleDensity ℓ h) [NeZero n] (hn : ℓ.n₀ ≤ n)
    (y : TorusSite n) {W : TorusField n} (hW : IsCold ℓ.threshold W) {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ k (restrictToBonds (h n y) W c X) 0 :=
  (hp.smooth n hn y W hW k c X).of_le (by exact_mod_cast hk)
theorem contDiffAt_restrictToBonds_centered (hp : IsAdmissibleDensity ℓ h) [NeZero n] (hn : ℓ.n₀ ≤ n)
    (y : TorusSite n) {W : TorusField n} (hW : IsCold ℓ.threshold W) {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ k (restrictToBonds (centeredFamily h n y) W c X) 0 :=
  (contDiffAt_restrictToBonds hp hn y hW hk c X).sub contDiffAt_const
theorem mixedDeriv_centeredFamily (hp : IsAdmissibleDensity ℓ h) [NeZero n] (hn : ℓ.n₀ ≤ n)
    (y : TorusSite n) {W : TorusField n} (hW : IsCold ℓ.threshold W) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (centeredFamily h n y) W c X = mixedDeriv (h n y) W c X :=
  mixedDeriv_sub_const hk1 (h n y) (h n y (trivialField n)) W c X
    (contDiffAt_restrictToBonds hp hn y hW hk c X)
theorem localComparison_centeredFamily (hσ : 0 < ℓ.threshold) (hp : IsAdmissibleDensity ℓ h)
    {e : ℕ → ℝ} (he : ∀ m, 0 ≤ e m)
    (hc : LocalComparison ℓ h e) : LocalComparison ℓ (centeredFamily h) fun m => 2 * e m := by
  intro n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have a1 := hc n n' hn hn' y y' W W' m h1 h2 hW hW' hA 0 b X hk hb hX
    have a2 := hc n n' hn hn' y y' (trivialField n) (trivialField n') m h1 h2
      (trivialField_isCold hσ n) (trivialField_isCold hσ n')
      (fieldsAgreeNear_trivialField y y' m) 0 b X hk hb hX
    simp only [mixedDeriv_zero] at a1 a2 ⊢
    simp only [centeredFamily, centered]
    rw [abs_le] at a1 a2 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · have a1 := hc n n' hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX
    rw [mixedDeriv_centeredFamily hp hn y hW hk1 (by omega),
      mixedDeriv_centeredFamily hp hn' y' hW' hk1 (by omega)]
    linarith [he m]
theorem mixedDeriv_sumOfFour {u s τ g : LocalDensity} (y : TorusSite n) (W : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hu : ContDiffAt ℝ k (restrictToBonds (u n y) W c X) 0)
    (hs : ContDiffAt ℝ k (restrictToBonds (s n y) W c X) 0)
    (hτ : ContDiffAt ℝ k (restrictToBonds (τ n y) W c X) 0)
    (hg : ContDiffAt ℝ k (restrictToBonds (g n y) W c X) 0) :
    mixedDeriv (sumOfFour u s τ g n y) W c X =
      mixedDeriv (u n y) W c X + mixedDeriv (s n y) W c X + mixedDeriv (τ n y) W c X +
        mixedDeriv (g n y) W c X := by
  have e3 := mixedDeriv_add (u n y) (s n y) W c X hu hs
  have e2 := mixedDeriv_add (fun V => u n y V + s n y V) (τ n y) W c X (hu.add hs) hτ
  have e1 := mixedDeriv_add (fun V => u n y V + s n y V + τ n y V) (g n y) W c X
    ((hu.add hs).add hτ) hg
  show mixedDeriv (fun V => u n y V + s n y V + τ n y V + g n y V) W c X = _
  rw [e1, e2, e3]
theorem centeredFamily_sumOfFour (u s τ g : LocalDensity) :
    centeredFamily (sumOfFour u s τ g) =
      sumOfFour (centeredFamily u) (centeredFamily s) (centeredFamily τ) (centeredFamily g) := by
  funext n y W
  simp only [centeredFamily, centered, sumOfFour]
  ring
theorem weight_pos (ℓ : StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem isCurvatureFamily_sumOfFour (h2 : PotentialSumsFinite) (hF : ℓ.Admissible) {Cs CE ε e x : ℝ}
    {u s τ g : LocalDensity} (hCs : 0 ≤ Cs) (hCE : 0 ≤ CE) (hε : 0 ≤ ε) (he : 0 ≤ e) (hx : 0 < x)
    (H : ExpansionDensityBounds ℓ Cs CE ε e x u s τ g) :
    IsCurvatureFamily ℓ (2 * 2 * Cs * weightGrowthSup ℓ.rt ℓ.n₁ + ℓ.E + ℓ.E₃ +
      CE * x ^ (-(1 / 2 : ℝ)) * weightGrowthSup ℓ.rt ℓ.n₁ + 2 * 2 * ε + e) (sumOfFour u s τ g) := by
  obtain ⟨-, -, -, hle, -, -, hG1⟩ := h2 ℓ.rt ℓ.n₁ hF.rt_pos hF.n₁_pos
  set G := weightGrowthSup ℓ.rt ℓ.n₁ with hGdef
  set CX := CE * x ^ (-(1 / 2 : ℝ)) with hCX
  have hCX0 : 0 ≤ CX := mul_nonneg hCE (Real.rpow_nonneg hx.le _)
  have hrt := hF.rt_pos
  have hE := hF.E_pos
  have hE₃ := hF.E₃_pos
  have hexp9 : ∀ m : ℕ, Real.exp (-(ℓ.rt / 2 ^ 9 * m)) ≤ G / ℓ.weight m := by
    intro m
    rw [le_div_iff₀ (weight_pos ℓ m)]
    have h := hle m
    have e1 : 2 * (ℓ.rt / 2 ^ 10) * (m : ℝ) = ℓ.rt / 2 ^ 9 * m := by ring
    rw [e1] at h
    have e2 : ℓ.weight m = expansionWeight ℓ.rt ℓ.n₁ m := rfl
    rw [e2, mul_comm]
    exact h
  have hexp6 : ∀ m : ℕ, Real.exp (-(ℓ.rt / 2 ^ 6 * m)) ≤ G / ℓ.weight m := by
    intro m
    refine le_trans ?_ (hexp9 m)
    rw [Real.exp_le_exp]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have h3 : ℓ.rt / 2 ^ 9 * m ≤ ℓ.rt / 2 ^ 6 * m := by
      apply mul_le_mul_of_nonneg_right _ this
      apply div_le_div_of_nonneg_left hrt.le (by norm_num) (by norm_num)
    linarith
  have hG0 : 0 ≤ G := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n _ hn y W hW k c X
    exact (((H.admissible_u.smooth n hn y W hW k c X).add (H.admissible_s.smooth n hn y W hW k c X)).add
      (H.admissible_τ.smooth n hn y W hW k c X)).add (H.admissible_g.smooth n hn y W hW k c X)
  · intro n _ hn y γ W hW
    simp only [sumOfFour]
    rw [H.admissible_u.gauge n hn y γ W hW, H.admissible_s.gauge n hn y γ W hW,
      H.admissible_τ.gauge n hn y γ W hW, H.admissible_g.gauge n hn y γ W hW]
  · intro n _ hn y v W hW
    simp only [sumOfFour]
    rw [H.admissible_u.translation n hn y v W hW, H.admissible_s.translation n hn y v W hW,
      H.admissible_τ.translation n hn y v W hW, H.admissible_g.translation n hn y v W hW]
  · intro n _ hn y W hW k c X hk1 hk3 hX
    rw [mixedDeriv_sumOfFour y W c X (contDiffAt_restrictToBonds H.admissible_u hn y hW hk3 c X)
      (contDiffAt_restrictToBonds H.admissible_s hn y hW hk3 c X)
      (contDiffAt_restrictToBonds H.admissible_τ hn y hW hk3 c X)
      (contDiffAt_restrictToBonds H.admissible_g hn y hW hk3 c X)]
    have bu := H.decay_u n hn y W hW k c X hk1 hk3 hX
    have bs := H.decay_s n hn y W hW k c X hk1 hk3 hX
    have bτ := H.decay_τ n hn y W hW k c X hk1 hk3 hX
    have bg := H.decay_g n hn y W hW k c X hk1 hk3 hX
    set m := supportDiam y c
    have hw := weight_pos ℓ m
    have e6 := hexp6 m
    have hEk : 2⁻¹ ^ 6 * (if k = 3 then ℓ.E₃ else ℓ.E) ≤ ℓ.E + ℓ.E₃ := by
      split_ifs <;> norm_num <;> linarith
    have t1 : Cs * Real.exp (-(ℓ.rt / 2 ^ 6 * m)) ≤ Cs * G / ℓ.weight m := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left e6 hCs
    have t2 : CX * Real.exp (-(ℓ.rt / 2 ^ 6 * m)) ≤ CX * G / ℓ.weight m := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left e6 hCX0
    have t3 : 2⁻¹ ^ 6 * (if k = 3 then ℓ.E₃ else ℓ.E) / ℓ.weight m ≤ (ℓ.E + ℓ.E₃) / ℓ.weight m :=
      div_le_div_of_nonneg_right hEk hw.le
    have hsum : Cs * G / ℓ.weight m + ((ℓ.E + ℓ.E₃) / ℓ.weight m + CX * G / ℓ.weight m) +
        ε / ℓ.weight m + e / ℓ.weight m ≤
          (2 * 2 * Cs * G + ℓ.E + ℓ.E₃ + CX * G + 2 * 2 * ε + e) / ℓ.weight m := by
      rw [← add_div, ← add_div, ← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hw.le
      nlinarith [mul_nonneg hCs hG0]
    calc _ ≤ |mixedDeriv (u n y) W c X| + |mixedDeriv (s n y) W c X| + |mixedDeriv (τ n y) W c X| +
          |mixedDeriv (g n y) W c X| := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by linarith
  · intro n n' _ _ hn hn' y y' W W' m h1 h2' hW hW' hA k b X hk hb hX
    have hk3 : k ≤ 3 := by omega
    have cu := localComparison_centeredFamily hF.σ_pos H.admissible_u
      (e := fun m => Cs * Real.exp (-(ℓ.rt / 2 ^ 9 * m)))
      (fun m => mul_nonneg hCs (Real.exp_pos _).le) H.local_u
    have cτ := localComparison_centeredFamily hF.σ_pos H.admissible_τ (e := fun m => ε / ℓ.weight m)
      (fun m => div_nonneg hε (weight_pos ℓ m).le) H.local_τ
    have bu := cu n n' hn hn' y y' W W' m h1 h2' hW hW' hA k b X hk hb hX
    have bs := H.local_s n n' hn hn' y y' W W' m h1 h2' hW hW' hA k b X hk hb hX
    have bτ := cτ n n' hn hn' y y' W W' m h1 h2' hW hW' hA k b X hk hb hX
    have bg := H.local_g n n' hn hn' y y' W W' m h1 h2' hW hW' hA k b X hk hb hX
    have key : ∀ (N : ℕ) [NeZero N] (hN : ℓ.n₀ ≤ N) (z : TorusSite N) (U : TorusField N)
        (hU : IsCold ℓ.threshold U) (d : Fin k → TorusBond N),
        mixedDeriv (centered (sumOfFour u s τ g) N z) U d X =
          mixedDeriv (centeredFamily u N z) U d X + mixedDeriv (centeredFamily s N z) U d X +
            mixedDeriv (centeredFamily τ N z) U d X + mixedDeriv (centeredFamily g N z) U d X := by
      intro N _ hN z U hU d
      have e0 : centered (sumOfFour u s τ g) N z = sumOfFour (centeredFamily u) (centeredFamily s)
          (centeredFamily τ) (centeredFamily g) N z := by
        rw [← centeredFamily_sumOfFour]
        rfl
      rw [e0]
      exact mixedDeriv_sumOfFour z U d X
        (contDiffAt_restrictToBonds_centered H.admissible_u hN z hU hk3 d X)
        (contDiffAt_restrictToBonds_centered H.admissible_s hN z hU hk3 d X)
        (contDiffAt_restrictToBonds_centered H.admissible_τ hN z hU hk3 d X)
        (contDiffAt_restrictToBonds_centered H.admissible_g hN z hU hk3 d X)
    rw [key n hn y W hW, key n' hn' y' W' hW']
    have hw := weight_pos ℓ m
    have e9 := hexp9 m
    have t1 : 2 * (Cs * Real.exp (-(ℓ.rt / 2 ^ 9 * m))) ≤ 2 * (Cs * G) / ℓ.weight m := by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e9 hCs) (by norm_num)
    have t2 : 2⁻¹ ^ 4 * ℓ.E / ℓ.weight m ≤ ℓ.E / ℓ.weight m := by
      apply div_le_div_of_nonneg_right _ hw.le
      norm_num
      linarith
    have hsum : 2 * (Cs * G) / ℓ.weight m + ℓ.E / ℓ.weight m + 2 * (ε / ℓ.weight m) +
        e / ℓ.weight m ≤ (2 * 2 * Cs * G + ℓ.E + ℓ.E₃ + CX * G + 2 * 2 * ε + e) / ℓ.weight m := by
      have e2 : 2 * (ε / ℓ.weight m) = 2 * ε / ℓ.weight m := by rw [mul_div_assoc]
      rw [e2, ← add_div, ← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hw.le
      nlinarith [mul_nonneg hCs hG0, mul_nonneg hCX0 hG0]
    have ab : ∀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℝ, |a₁ + a₂ + a₃ + a₄ - (b₁ + b₂ + b₃ + b₄)| ≤
        |a₁ - b₁| + |a₂ - b₂| + |a₃ - b₃| + |a₄ - b₄| := by
      intro a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
      have e0 : a₁ + a₂ + a₃ + a₄ - (b₁ + b₂ + b₃ + b₄) =
          (a₁ - b₁) + (a₂ - b₂) + (a₃ - b₃) + (a₄ - b₄) := by ring
      rw [e0]
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    refine (ab _ _ _ _ _ _ _ _).trans ?_
    beta_reduce at bu bτ
    linarith
theorem supDist_siteOfInt {n : ℕ} (h h' : Fin 4 → ℤ) (hn : 2 * offsetNorm (h - h') < n) :
    supDist (siteOfInt h : TorusSite n) (siteOfInt h') = offsetNorm (h - h') := by
  haveI : NeZero n := ⟨by omega⟩
  unfold supDist offsetNorm
  refine Finset.sup_congr rfl fun i _ => ?_
  have hi : ((h - h') i).natAbs ≤ offsetNorm (h - h') :=
    Finset.le_sup (f := fun i => ((h - h') i).natAbs) (Finset.mem_univ i)
  have e : ((siteOfInt h : TorusSite n) i - (siteOfInt h' : TorusSite n) i) =
      (((h - h') i : ℤ) : ZMod n) := by
    simp [siteOfInt]
  rw [e]
  have hv : ((((h - h') i : ℤ) : ZMod n)).valMinAbs = (h - h') i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> omega
  rw [hv]
theorem sup_univ_fin_two (f : Fin 2 → ℕ) : Finset.univ.sup f = max (f 0) (f 1) := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup (Finset.mem_univ _)) (Finset.le_sup (Finset.mem_univ _))
theorem offsetNorm_neg (h : Fin 4 → ℤ) : offsetNorm (-h) = offsetNorm h := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
theorem offsetNorm_sub_le (h h' : Fin 4 → ℤ) : offsetNorm (h - h') ≤ offsetNorm h + offsetNorm h' := by apply _root_.YangMills.Construction.PatchPotentials.supNorm_sub_le <;> assumption
theorem supportDiam_bondFrom_pair {n : ℕ} (c c' : LatticeBond)
    (hn : 2 * (offsetNorm c.1 + offsetNorm c'.1) + 2 < n) :
    supportDiam (0 : TorusSite n) ![bondFrom 0 c, bondFrom 0 c'] = bondPairDiam c c' := by
  haveI : NeZero n := ⟨by omega⟩
  have z : (0 : TorusSite n) = siteOfInt 0 := by
    funext i
    simp [siteOfInt]
  have d := offsetNorm_sub_le c.1 c'.1
  have d' : offsetNorm (c'.1 - c.1) = offsetNorm (c.1 - c'.1) := by
    rw [← neg_sub, offsetNorm_neg]
  have e1 : supDist (0 : TorusSite n) (0 + siteOfInt c.1) = offsetNorm c.1 := by
    rw [zero_add, z, supDist_siteOfInt _ _ (by simp [offsetNorm_neg]; omega)]
    simp [offsetNorm_neg]
  have e2 : supDist (0 : TorusSite n) (0 + siteOfInt c'.1) = offsetNorm c'.1 := by
    rw [zero_add, z, supDist_siteOfInt _ _ (by simp [offsetNorm_neg]; omega)]
    simp [offsetNorm_neg]
  have e3 : supDist ((0 : TorusSite n) + siteOfInt c.1) (0 + siteOfInt c'.1) =
      offsetNorm (c.1 - c'.1) := by
    rw [zero_add, zero_add, supDist_siteOfInt _ _ (by omega)]
  have e4 : supDist ((0 : TorusSite n) + siteOfInt c'.1) (0 + siteOfInt c.1) =
      offsetNorm (c.1 - c'.1) := by
    rw [supDist_comm, e3]
  unfold supportDiam bondPairDiam
  simp only [sup_univ_fin_two, bondFrom, Matrix.cons_val_zero, Matrix.cons_val_one, supDist_self,
    e1, e2, e3, e4]
  omega
theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
theorem exists_smul_unit (X : imaginaryQuaternions) :
    ∃ (a : ℝ) (X₀ : imaginaryQuaternions), ‖X₀‖ = 1 ∧ X = a • X₀ ∧ |a| = ‖X‖ := by
  by_cases h : X = 0
  · exact ⟨0, quaternionI, norm_quaternionI, by simp [h], by simp [h]⟩
  · have hn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr h
    refine ⟨‖X‖, ‖X‖⁻¹ • X, ?_, ?_, by simp⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
theorem bondOffsetInBox_of_le (c : LatticeBond) {m : ℕ} (hm : offsetNorm c.1 + 1 ≤ m) :
    BondOffsetInBox m c := by apply _root_.YangMills.SharedProofs.p38965 <;> assumption
def PairComparisonAtTrivial (ℓ : StepParameters) (h : LocalDensity) (e : ℕ → ℝ) : Prop :=
  ∀ (n n' : ℕ) [NeZero n] [NeZero n'], ℓ.n₀ ≤ n → ℓ.n₀ ≤ n' → ∀ m : ℕ, 2 * m + 2 < n → 2 * m + 2 < n' →
    ∀ (c c' : LatticeBond) (X X' : imaginaryQuaternions), BondOffsetInBox m c → BondOffsetInBox m c' →
    ‖X‖ = 1 → ‖X'‖ = 1 →
    |mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] -
      mixedDeriv (h n' 0) (trivialField n') ![bondFrom 0 c, bondFrom 0 c'] ![X, X']| ≤ e m
theorem bondFrom_pair (N : ℕ) (c c' : LatticeBond) :
    (fun l => bondFrom (0 : TorusSite N) ((![c, c'] : Fin 2 → LatticeBond) l)) =
      ![bondFrom 0 c, bondFrom 0 c'] := by
  funext l
  fin_cases l <;> rfl
theorem areUnitVectors_pair {X X' : imaginaryQuaternions} (h : ‖X‖ = 1) (h' : ‖X'‖ = 1) :
    AreUnitVectors ![X, X'] := by apply _root_.YangMills.SharedProofs.p1051 <;> assumption
theorem pairComparison_of_localComparison (hσ : 0 < ℓ.threshold) {e : ℕ → ℝ}
    (hc : LocalComparison ℓ h e) : PairComparisonAtTrivial ℓ h e := by
  intro n n' _ _ hn hn' m h1 h2 c c' X X' hb hb' hX hX'
  have := hc n n' hn hn' 0 0 (trivialField n) (trivialField n') m h1 h2 (trivialField_isCold hσ n)
    (trivialField_isCold hσ n') (fieldsAgreeNear_trivialField _ _ _) 2 ![c, c'] ![X, X'] le_rfl
    (by intro l; fin_cases l; exacts [hb, hb']) (areUnitVectors_pair hX hX')
  rwa [bondFrom_pair, bondFrom_pair] at this
theorem pairComparison_of_localComparison_centered (hσ : 0 < ℓ.threshold)
    (hp : IsAdmissibleDensity ℓ h) {e : ℕ → ℝ}
    (hc : LocalComparison ℓ (centeredFamily h) e) : PairComparisonAtTrivial ℓ h e := by
  intro n n' _ _ hn hn' m h1 h2 c c' X X' hb hb' hX hX'
  have := pairComparison_of_localComparison hσ hc n n' hn hn' m h1 h2 c c' X X' hb hb' hX hX'
  rwa [mixedDeriv_centeredFamily hp hn 0 (trivialField_isCold hσ n) (by norm_num) (by norm_num),
    mixedDeriv_centeredFamily hp hn' 0 (trivialField_isCold hσ n') (by norm_num) (by norm_num)] at this
theorem hasLimitSecondDeriv_of_pairComparison (hF : ℓ.Admissible) (hp : IsAdmissibleDensity ℓ h)
    {e : ℕ → ℝ} (he : Filter.Tendsto e Filter.atTop (𝓝 0)) (H2 : PairComparisonAtTrivial ℓ h e) :
    HasLimitSecondDeriv h := by
  intro c c' X X'
  obtain ⟨a, X₀, hX₀, rfl, -⟩ := exists_smul_unit X
  obtain ⟨a', X₀', hX₀', rfl, -⟩ := exists_smul_unit X'
  have hn₀ := hF.n₀_ge
  have hC : CauchySeq fun n : ℕ =>
      mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X₀, X₀'] := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have h1 : ∀ᶠ m in Filter.atTop, e m < ε := he.eventually (gt_mem_nhds hε)
    obtain ⟨M, hM, hM'⟩ := (h1.and (Filter.eventually_ge_atTop
      (offsetNorm c.1 + offsetNorm c'.1 + 1))).exists
    refine ⟨max ℓ.n₀ (2 * M + 3), fun n hn n' hn' => ?_⟩
    have a1 := le_max_left ℓ.n₀ (2 * M + 3)
    have a2 := le_max_right ℓ.n₀ (2 * M + 3)
    haveI : NeZero n := ⟨by omega⟩
    haveI : NeZero n' := ⟨by omega⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (H2 n n' (by omega) (by omega) M (by omega) (by omega) c c' X₀ X₀'
      (bondOffsetInBox_of_le c (by omega)) (bondOffsetInBox_of_le c' (by omega)) hX₀ hX₀') hM
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨a * a' * v, (hv.const_mul (a * a')).congr' ?_⟩
  filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with n hn
  haveI : NeZero n := ⟨by omega⟩
  exact (mixedDeriv_pair_smul _ _ _ _ _ _ _
    (contDiffAt_restrictToBonds hp hn 0 (trivialField_isCold hF.σ_pos n) (by norm_num) _ _)).symm
theorem tendsto_secondDerivLimit (hL : HasLimitSecondDeriv h) (c c' : LatticeBond)
    (X X' : imaginaryQuaternions) :
    Filter.Tendsto (fun n : ℕ =>
      mixedDeriv (h n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
      Filter.atTop (𝓝 (secondDerivLimit h c c' X X')) := by
  obtain ⟨v, hv⟩ := hL c c' X X'
  have e : secondDerivLimit h c c' X X' = v := hv.limUnder_eq
  rw [e]
  exact hv
theorem abs_secondDerivLimit_le (hF : ℓ.Admissible) (hp : IsAdmissibleDensity ℓ h)
    (hL : HasLimitSecondDeriv h) {e : ℕ → ℕ → ℝ}
    (D : DerivDecay ℓ h e) (c c' : LatticeBond) (X X' : imaginaryQuaternions) :
    |secondDerivLimit h c c' X X'| ≤ ‖X‖ * ‖X'‖ * e 2 (bondPairDiam c c') := by
  obtain ⟨a, X₀, hX₀, rfl, ha⟩ := exists_smul_unit X
  obtain ⟨a', X₀', hX₀', rfl, ha'⟩ := exists_smul_unit X'
  have ht := (tendsto_secondDerivLimit hL c c' (a • X₀) (a' • X₀')).abs
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop
    (max ℓ.n₀ (2 * (offsetNorm c.1 + offsetNorm c'.1) + 3))] with n hn
  have a1 := le_trans (le_max_left _ _) hn
  have a2 := le_trans (le_max_right _ _) hn
  haveI : NeZero n := ⟨by omega⟩
  have hcold := trivialField_isCold hF.σ_pos n
  rw [mixedDeriv_pair_smul _ _ _ _ _ _ _ (contDiffAt_restrictToBonds hp a1 0 hcold (by norm_num) _ _),
    abs_mul, abs_mul, ha, ha']
  have hb := D n a1 0 (trivialField n) hcold 2 ![bondFrom 0 c, bondFrom 0 c'] ![X₀, X₀']
    (by norm_num) (by norm_num) (areUnitVectors_pair hX₀ hX₀')
  rw [supportDiam_bondFrom_pair c c' (by omega)] at hb
  exact mul_le_mul_of_nonneg_left hb (by positivity)
theorem tendsto_const_mul_exp_neg {r : ℝ} (hr : 0 < r) (C : ℝ) :
    Filter.Tendsto (fun m : ℕ => C * Real.exp (-(r * m))) Filter.atTop (𝓝 0) := by apply _root_.YangMills.SharedProofs.p101442 <;> assumption
theorem tendsto_div_weight (hF : ℓ.Admissible) {C : ℝ} (hC : 0 ≤ C) :
    Filter.Tendsto (fun m : ℕ => C / ℓ.weight m) Filter.atTop (𝓝 0) := by
  have hr : 0 < ℓ.weightRate := by
    have := hF.rt_pos
    unfold StepParameters.weightRate
    positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_mul_exp_neg hr C)
    (fun m => div_nonneg hC (weight_pos ℓ m).le) (fun m => ?_)
  have hw : Real.exp (ℓ.weightRate * m) ≤ ℓ.weight m := by
    unfold StepParameters.weight
    have : (1 : ℝ) ≤ max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) := le_max_left _ _
    nlinarith [Real.exp_pos (ℓ.weightRate * m)]
  simp only []
  rw [Real.exp_neg, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (Real.exp_pos _) hw) hC
theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    unitPlaneCurvature μ ν = - unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
theorem curvaturePairing_unitPlaneCurvature :
    curvaturePairing unitPlaneCurvature unitPlaneCurvature = 1 := by apply _root_.YangMills.SharedProofs.p11741 <;> assumption
theorem curvatureCoefficientOfSum_holds (h1 : InvariantFamilyCurvatureForm) (h2 : PotentialSumsFinite) :
    CurvatureCoefficientOfSum := by
  intro ℓ hF Cs CE ε e x u s τ g hCs hCE hε he hx H hcar hfl
  have hσ := hF.σ_pos
  have hrt := hF.rt_pos
  have hn₀ := hF.n₀_ge
  obtain ⟨sB, sG, -, -, sB0, sG0, -⟩ := h2 ℓ.rt ℓ.n₁ hrt hF.n₁_pos
  have Lu : HasLimitSecondDeriv u := hasLimitSecondDeriv_of_pairComparison hF H.admissible_u
    (tendsto_const_mul_exp_neg (r := ℓ.rt / 2 ^ 9) (by positivity) Cs)
    (pairComparison_of_localComparison hσ H.local_u)
  have Ls : HasLimitSecondDeriv s := hasLimitSecondDeriv_of_pairComparison hF H.admissible_s
    (tendsto_div_weight hF (C := 2⁻¹ ^ 4 * ℓ.E) (by have := hF.E_pos; positivity))
    (pairComparison_of_localComparison_centered hσ H.admissible_s H.local_s)
  have Lτ : HasLimitSecondDeriv τ := hasLimitSecondDeriv_of_pairComparison hF H.admissible_τ
    (tendsto_div_weight hF hε) (pairComparison_of_localComparison hσ H.local_τ)
  have Lg : HasLimitSecondDeriv g := hasLimitSecondDeriv_of_pairComparison hF H.admissible_g
    (tendsto_div_weight hF he)
    (pairComparison_of_localComparison_centered hσ H.admissible_g H.local_g)
  have hfam := isCurvatureFamily_sumOfFour h2 hF hCs hCE hε he hx H
  obtain ⟨hT, b₀, hb₀⟩ := h1 ℓ hF _ _ hfam hcar
  have hLf : HasLimitSecondDeriv (sumOfFour u s τ g) := fun c c' X X' => ⟨_, hT c c' X X'⟩
  have hsum0 := hb₀ unitPlaneCurvature unitPlaneCurvature unitPlaneCurvature_antisymm
    unitPlaneCurvature_antisymm
  rw [curvaturePairing_unitPlaneCurvature, mul_one] at hsum0
  have hnum : curvatureCoefficient (sumOfFour u s τ g) = b₀ := hsum0.tsum_eq
  have hterm : ∀ cc, limitFormTerm (sumOfFour u s τ g) unitPlaneCurvature unitPlaneCurvature cc =
      limitFormTerm u unitPlaneCurvature unitPlaneCurvature cc +
        limitFormTerm s unitPlaneCurvature unitPlaneCurvature cc +
        limitFormTerm τ unitPlaneCurvature unitPlaneCurvature cc +
        limitFormTerm g unitPlaneCurvature unitPlaneCurvature cc := by
    rintro ⟨c, c'⟩
    set X := linearPotential unitPlaneCurvature c
    set X' := linearPotential unitPlaneCurvature c'
    have t := (((tendsto_secondDerivLimit Lu c c' X X').add (tendsto_secondDerivLimit Ls c c' X X')).add
      (tendsto_secondDerivLimit Lτ c c' X X')).add (tendsto_secondDerivLimit Lg c c' X X')
    have t' : Filter.Tendsto (fun n : ℕ => mixedDeriv (sumOfFour u s τ g n 0) (trivialField n)
        ![bondFrom 0 c, bondFrom 0 c'] ![X, X']) Filter.atTop _ := t.congr' (by
      filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with n hn
      haveI : NeZero n := ⟨by omega⟩
      have hc := trivialField_isCold hσ n
      exact (mixedDeriv_sumOfFour 0 (trivialField n) _ _
        (contDiffAt_restrictToBonds H.admissible_u hn 0 hc (by norm_num) _ _)
        (contDiffAt_restrictToBonds H.admissible_s hn 0 hc (by norm_num) _ _)
        (contDiffAt_restrictToBonds H.admissible_τ hn 0 hc (by norm_num) _ _)
        (contDiffAt_restrictToBonds H.admissible_g hn 0 hc (by norm_num) _ _)).symm)
    exact t'.limUnder_eq
  have bu : ∀ cc, ‖limitFormTerm u unitPlaneCurvature unitPlaneCurvature cc‖ ≤
      Cs * (potentialNorm cc.1 * potentialNorm cc.2 *
        Real.exp (-(ℓ.rt / 2 ^ 6 * bondPairDiam cc.1 cc.2))) := by
    rintro ⟨c, c'⟩
    have := abs_secondDerivLimit_le hF H.admissible_u Lu H.decay_u c c'
      (linearPotential unitPlaneCurvature c) (linearPotential unitPlaneCurvature c')
    rw [Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    simp only [potentialNorm]
    ring
  have su := (sB.hasSum.mul_left Cs)
  have Su : Summable (limitFormTerm u unitPlaneCurvature unitPlaneCurvature) :=
    Summable.of_norm_bounded su.summable bu
  have nu : |curvatureCoefficient u| ≤ Cs * potentialDecaySum ℓ.rt := tsum_of_norm_bounded su bu
  have bτ : ∀ cc, ‖limitFormTerm τ unitPlaneCurvature unitPlaneCurvature cc‖ ≤
      ε * (potentialNorm cc.1 * potentialNorm cc.2 /
        expansionWeight ℓ.rt ℓ.n₁ (bondPairDiam cc.1 cc.2)) := by
    rintro ⟨c, c'⟩
    have := abs_secondDerivLimit_le hF H.admissible_τ Lτ H.decay_τ c c'
      (linearPotential unitPlaneCurvature c) (linearPotential unitPlaneCurvature c')
    rw [Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    simp only [potentialNorm, StepParameters.weight, expansionWeight, StepParameters.weightRate]
    ring
  have bg : ∀ cc, ‖limitFormTerm g unitPlaneCurvature unitPlaneCurvature cc‖ ≤
      e * (potentialNorm cc.1 * potentialNorm cc.2 /
        expansionWeight ℓ.rt ℓ.n₁ (bondPairDiam cc.1 cc.2)) := by
    rintro ⟨c, c'⟩
    have := abs_secondDerivLimit_le hF H.admissible_g Lg H.decay_g c c'
      (linearPotential unitPlaneCurvature c) (linearPotential unitPlaneCurvature c')
    rw [Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    simp only [potentialNorm, StepParameters.weight, expansionWeight, StepParameters.weightRate]
    ring
  have sτ := (sG.hasSum.mul_left ε)
  have sg := (sG.hasSum.mul_left e)
  have Sτ : Summable (limitFormTerm τ unitPlaneCurvature unitPlaneCurvature) :=
    Summable.of_norm_bounded sτ.summable bτ
  have Sg : Summable (limitFormTerm g unitPlaneCurvature unitPlaneCurvature) :=
    Summable.of_norm_bounded sg.summable bg
  have nτ : |curvatureCoefficient τ| ≤ ε * _ := tsum_of_norm_bounded sτ bτ
  have ng : |curvatureCoefficient g| ≤ e * _ := tsum_of_norm_bounded sg bg
  obtain ⟨v, hv, hvb⟩ := H.flat_s quaternionI 0 1 norm_quaternionI (by decide)
  have hv' : HasSum (limitFormTerm s unitPlaneCurvature unitPlaneCurvature) v := hv
  have ns : curvatureCoefficient s = v := hv'.tsum_eq
  have hall : HasSum (limitFormTerm (sumOfFour u s τ g) unitPlaneCurvature unitPlaneCurvature)
      (curvatureCoefficient u + curvatureCoefficient s + curvatureCoefficient τ +
        curvatureCoefficient g) := by
    have h4 := ((Su.hasSum.add hv').add Sτ.hasSum).add Sg.hasSum
    have e4 : limitFormTerm (sumOfFour u s τ g) unitPlaneCurvature unitPlaneCurvature = fun cc =>
        limitFormTerm u unitPlaneCurvature unitPlaneCurvature cc +
          limitFormTerm s unitPlaneCurvature unitPlaneCurvature cc +
          limitFormTerm τ unitPlaneCurvature unitPlaneCurvature cc +
          limitFormTerm g unitPlaneCurvature unitPlaneCurvature cc := funext hterm
    rw [e4, ns]
    exact h4
  have hnsum := hall.tsum_eq
  refine ⟨Lu, Ls, Lτ, Lg, hnsum, ⟨hLf, fun A A' hA hA' => ?_⟩, ?_⟩
  · rw [hnum]
    exact hb₀ A A' hA hA'
  · have hnsum' : curvatureCoefficient (sumOfFour u s τ g) =
        curvatureCoefficient u + curvatureCoefficient s + curvatureCoefficient τ +
          curvatureCoefficient g := hnsum
    rw [hnsum', ns]
    set T := ∑' cc : LatticeBond × LatticeBond, potentialNorm cc.1 * potentialNorm cc.2 /
      expansionWeight ℓ.rt ℓ.n₁ (bondPairDiam cc.1 cc.2) with hTdef
    have hG : potentialWeightSum ℓ.rt ℓ.n₁ = 2 * T := rfl
    have hT0 : 0 ≤ T := by
      have := sG0
      rw [hG] at this
      linarith
    rw [hG] at hfl
    have t1 : 0 ≤ ε * T := mul_nonneg hε hT0
    have t2 : 0 ≤ e * T := mul_nonneg he hT0
    have hab : |curvatureCoefficient u + v + curvatureCoefficient τ + curvatureCoefficient g| ≤
        |curvatureCoefficient u| + |v| + |curvatureCoefficient τ| + |curvatureCoefficient g| :=
      (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    unfold baseConstant
    nlinarith
end YangMills.Construction.TorusLumps.SumOfFourCurvature
end
