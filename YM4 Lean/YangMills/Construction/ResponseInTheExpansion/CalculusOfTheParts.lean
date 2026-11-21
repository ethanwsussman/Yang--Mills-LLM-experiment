import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfFourDensitiesProofForm
import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImageProof
import YangMills.Construction.ClusterExpansionOfAStep.FourDensitiesOfAStepProof
import YangMills.Construction.ResponseInTheExpansion.TotalOfTheResponseFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open ColdStepAtMirrorFrames FamilyNorms
namespace ResponseInTheExpansion
open TorusFields TorusLumps BlockAverages
namespace TermCalculus
section Calculus
variable {n k : ℕ}
theorem mixedDeriv_add (G₁ G₂ : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (h₁ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₁ (perturb c X σ W)) 0)
    (h₂ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₂ (perturb c X σ W)) 0) :
    mixedDeriv (fun V => G₁ V + G₂ V) W c X = mixedDeriv G₁ W c X + mixedDeriv G₂ W c X := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.mixedDeriv_add <;> assumption
theorem mixedDeriv_const_mul (b : ℝ) (G : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (h : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv (fun V => b * G V) W c X = b * mixedDeriv G W c X := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.mixedDeriv_const_mul <;> assumption
end Calculus
section Weight
theorem weight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem torusDecayFactor_eq_weight {ℓ : TorusLumps.StepParameters}
    (hn : ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ)) (m : ℕ) :
    torusDecayFactor ℓ.side (ℓ.rt / 2 ^ 10) (m : ℝ) = ℓ.weight m := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdStepDensities.torusDecayFactor_eq_weight <;> assumption
theorem exp_le_weightGrowthSup_div (ℓ : TorusLumps.StepParameters) (hrt : 0 < ℓ.rt) (hn : 0 < ℓ.n₁)
    (m : ℕ) (κ : ℝ) (hκ : 2 * (ℓ.rt / 2 ^ 10) ≤ κ) :
    Real.exp (-(κ * m)) ≤ weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight m := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.exp_le_weightGrowthSup_div <;> assumption
theorem weightGrowthSup_nonneg (rt n₁ : ℝ) : 0 ≤ weightGrowthSup rt n₁ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.weightGrowthSup_nonneg <;> assumption
end Weight
def scaledDensity (b : ℝ) (h : LocalDensity) : LocalDensity := fun n y W => b * h n y W
theorem centered_scaledDensity (b : ℝ) (h : LocalDensity) (n : ℕ) (y : TorusSite n) :
    centered (scaledDensity b h) n y = fun W => b * centered h n y W := by
  funext W
  simp only [centered, scaledDensity]
  ring
variable {ℓ : TorusLumps.StepParameters}
theorem termBounds_scaled {e e₃ d b : ℝ} {g : LocalDensity} (hb : 0 ≤ b) (hg : TermBounds ℓ e e₃ d g) :
    TermBounds ℓ (b * e) (b * e₃) (b * d) (scaledDensity b g) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro n _ hn y W hW k c X
    exact contDiffAt_const.mul (hg.admissible.smooth n hn y W hW k c X)
  · intro n _ hn y γ W hW
    simp only [scaledDensity]
    rw [hg.admissible.gauge n hn y γ W hW]
  · intro n _ hn y u W hW
    simp only [scaledDensity]
    rw [hg.admissible.translation n hn y u W hW]
  · intro n _ hn y W hW k c X h1 h3 hX
    have e₁ : mixedDeriv (scaledDensity b g n y) W c X = b * mixedDeriv (g n y) W c X :=
      mixedDeriv_const_mul b (g n y) W c X h3 (hg.admissible.smooth n hn y W hW k c X)
    rw [e₁, abs_mul, abs_of_nonneg hb]
    refine (mul_le_mul_of_nonneg_left (hg.derivDecay n hn y W hW k c X h1 h3 hX) hb).trans (le_of_eq ?_)
    beta_reduce
    split_ifs <;> rw [mul_div_assoc]
  · intro n n' _ _ hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    have hk3 : k ≤ 3 := by omega
    have e₁ : mixedDeriv (centeredFamily (scaledDensity b g) n y) W (fun l => bondFrom y (bb l)) X =
        b * mixedDeriv (centeredFamily g n y) W (fun l => bondFrom y (bb l)) X := by
      have : centeredFamily (scaledDensity b g) n y = fun V => b * centeredFamily g n y V :=
        centered_scaledDensity b g n y
      rw [this]
      exact mixedDeriv_const_mul b _ W _ X hk3 ((hg.admissible.smooth n hn y W hW k _ X).sub contDiffAt_const)
    have e₂ : mixedDeriv (centeredFamily (scaledDensity b g) n' y') W' (fun l => bondFrom y' (bb l)) X =
        b * mixedDeriv (centeredFamily g n' y') W' (fun l => bondFrom y' (bb l)) X := by
      have : centeredFamily (scaledDensity b g) n' y' = fun V => b * centeredFamily g n' y' V :=
        centered_scaledDensity b g n' y'
      rw [this]
      exact mixedDeriv_const_mul b _ W' _ X hk3 ((hg.admissible.smooth n' hn' y' W' hW' k _ X).sub contDiffAt_const)
    rw [e₁, e₂, ← mul_sub, abs_mul, abs_of_nonneg hb]
    refine (mul_le_mul_of_nonneg_left
      (hg.centered_compare n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu) hb).trans (le_of_eq ?_)
    beta_reduce
    rw [mul_div_assoc]
theorem termBounds_mono {e e₃ d e' e₃' d' : ℝ} {g : LocalDensity} (he : e ≤ e') (he₃ : e₃ ≤ e₃') (hd : d ≤ d')
    (hg : TermBounds ℓ e e₃ d g) : TermBounds ℓ e' e₃' d' g := by
  refine ⟨hg.admissible, ?_, ?_⟩
  · intro n _ hn y W hW k c X h1 h3 hX
    refine (hg.derivDecay n hn y W hW k c X h1 h3 hX).trans ?_
    refine div_le_div_of_nonneg_right ?_ (weight_pos ℓ _).le
    split_ifs <;> assumption
  · intro n n' _ _ hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    exact (hg.centered_compare n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu).trans
      (div_le_div_of_nonneg_right hd (weight_pos ℓ _).le)
theorem termBounds_add {e e₃ d e' e₃' d' : ℝ} {g g' : LocalDensity} (hg : TermBounds ℓ e e₃ d g)
    (hg' : TermBounds ℓ e' e₃' d' g') :
    TermBounds ℓ (e + e') (e₃ + e₃') (d + d') (fun n y W => g n y W + g' n y W) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro n _ hn y W hW k c X
    exact (hg.admissible.smooth n hn y W hW k c X).add (hg'.admissible.smooth n hn y W hW k c X)
  · intro n _ hn y γ W hW
    show g n y _ + g' n y _ = g n y _ + g' n y _
    rw [hg.admissible.gauge n hn y γ W hW, hg'.admissible.gauge n hn y γ W hW]
  · intro n _ hn y u W hW
    show g n y _ + g' n y _ = g n _ _ + g' n _ _
    rw [hg.admissible.translation n hn y u W hW, hg'.admissible.translation n hn y u W hW]
  · intro n _ hn y W hW k c X h1 h3 hX
    have e₁ := mixedDeriv_add (g n y) (g' n y) W c X h3 (hg.admissible.smooth n hn y W hW k c X)
      (hg'.admissible.smooth n hn y W hW k c X)
    have d₁ := hg.derivDecay n hn y W hW k c X h1 h3 hX
    have d₂ := hg'.derivDecay n hn y W hW k c X h1 h3 hX
    show |mixedDeriv (fun V => g n y V + g' n y V) W c X| ≤ _
    rw [e₁]
    refine (abs_add_le _ _).trans ((add_le_add d₁ d₂).trans (le_of_eq ?_))
    beta_reduce
    split_ifs <;> rw [add_div]
  · intro n n' _ _ hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    have hk3 : k ≤ 3 := by omega
    have eh : ∀ (p : ℕ) (z : TorusSite p), centeredFamily (fun n y W => g n y W + g' n y W) p z =
        fun V => centeredFamily g p z V + centeredFamily g' p z V := fun p z => by
      funext V
      simp only [centeredFamily, centered]
      ring
    have e₁ : mixedDeriv (centeredFamily (fun n y W => g n y W + g' n y W) n y) W (fun l => bondFrom y (bb l)) X =
        mixedDeriv (centeredFamily g n y) W (fun l => bondFrom y (bb l)) X +
          mixedDeriv (centeredFamily g' n y) W (fun l => bondFrom y (bb l)) X := by
      rw [eh]
      exact mixedDeriv_add _ _ W _ X hk3 ((hg.admissible.smooth n hn y W hW k _ X).sub contDiffAt_const)
        ((hg'.admissible.smooth n hn y W hW k _ X).sub contDiffAt_const)
    have e₂ : mixedDeriv (centeredFamily (fun n y W => g n y W + g' n y W) n' y') W' (fun l => bondFrom y' (bb l)) X =
        mixedDeriv (centeredFamily g n' y') W' (fun l => bondFrom y' (bb l)) X +
          mixedDeriv (centeredFamily g' n' y') W' (fun l => bondFrom y' (bb l)) X := by
      rw [eh]
      exact mixedDeriv_add _ _ W' _ X hk3 ((hg.admissible.smooth n' hn' y' W' hW' k _ X).sub contDiffAt_const)
        ((hg'.admissible.smooth n' hn' y' W' hW' k _ X).sub contDiffAt_const)
    have d₁ := hg.centered_compare n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    have d₂ := hg'.centered_compare n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    rw [e₁, e₂]
    have : ∀ p q r s : ℝ, p + q - (r + s) = (p - r) + (q - s) := fun p q r s => by ring
    rw [this]
    refine (abs_add_le _ _).trans ((add_le_add d₁ d₂).trans (le_of_eq ?_))
    beta_reduce
    rw [add_div]
theorem derivDecay_mono {L t n₀ : ℕ} {s : ℝ} {g : TopLevelFamily} {e e' : ℕ → ℕ → ℝ}
    (h : DerivDecay L t n₀ s g e) (he : ∀ k m, 1 ≤ k → k ≤ 3 → e k m ≤ e' k m) : DerivDecay L t n₀ s g e' :=
  fun F hF Y V k c X hV h1 h3 hX => (h F hF Y V k c X hV h1 h3 hX).trans (he _ _ h1 h3)
theorem isLocalOnTori_mono {L t n₀ : ℕ} {s : ℝ} {g : TopLevelFamily} {e e' : ℕ → ℝ}
    (h : IsLocalOnTori L t n₀ s g e) (he : ∀ m, e m ≤ e' m) : IsLocalOnTori L t n₀ s g e' :=
  fun F F' hF hF' Y Y' V V' r k b X hV hV' hA hk hb hX =>
    (h F F' hF hF' Y Y' V V' r k b X hV hV' hA hk hb hX).trans (he r)
theorem termBounds_of_topLevelFamily (hA : TopFamilyOnTori) (hF : ℓ.Admissible) {t : ℕ} {s s' e e₃ c : ℝ}
    {g : TopLevelFamily} (hs : ℓ.threshold ≤ s) (hs' : ℓ.threshold ≤ s') (hd : IsLocalDensity ℓ.side t ℓ.n₀ s g)
    (hdec : DerivDecay ℓ.side t ℓ.n₀ s g fun k m => (if k = 3 then e₃ else e) / ℓ.weight m)
    (hloc : IsLocalOnTori ℓ.side t ℓ.n₀ s' (centredFamily g) fun m => c / ℓ.weight m) :
    TermBounds ℓ e e₃ c (densityOfTopFamily ℓ.side t g) := by
  obtain ⟨p, d, -, -, -⟩ := hA ℓ hF t s g hs
  obtain ⟨-, -, -, l, -⟩ := hA ℓ hF t s' g hs'
  exact ⟨p hd, d _ hdec, l _ hloc⟩
theorem isCold_trivialField {s : ℝ} (hs : 0 < s) (n : ℕ) : IsCold s (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
theorem mixedDeriv_sub_const {n k : ℕ} (G : TorusField n → ℝ) (e : ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (hk : 1 ≤ k) (hk3 : k ≤ 3)
    (h : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv (fun V => G V - e) W c X = mixedDeriv G W c X := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.mixedDeriv_sub_const <;> assumption
theorem localComparison_centeredFamily {h : LocalDensity} {e : ℕ → ℝ} (hσ : 0 < ℓ.threshold)
    (hp : IsAdmissibleDensity ℓ h) (hc : LocalComparison ℓ h e) (he : ∀ m, 0 ≤ e m) :
    LocalComparison ℓ (centeredFamily h) fun m => 2 * e m := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.localComparison_centered <;> assumption
theorem termBounds_of_exp_bounds (hA : TopFamilyOnTori) (hF : ℓ.Admissible) {t : ℕ} {s s' B : ℝ}
    {g : TopLevelFamily} (hs : ℓ.threshold ≤ s) (hs' : ℓ.threshold ≤ s') (hB : 0 ≤ B)
    (hd : IsLocalDensity ℓ.side t ℓ.n₀ s g)
    (hdec : DerivDecay ℓ.side t ℓ.n₀ s g fun _ m => B * Real.exp (-(ℓ.rt / 2 ^ 9 * m)))
    (hloc : IsLocalOnTori ℓ.side t ℓ.n₀ s' g fun m => B * Real.exp (-(ℓ.rt / 2 ^ 9 * m))) :
    TermBounds ℓ (weightGrowthSup ℓ.rt ℓ.n₁ * B) (weightGrowthSup ℓ.rt ℓ.n₁ * B)
      (2 * (weightGrowthSup ℓ.rt ℓ.n₁ * B)) (densityOfTopFamily ℓ.side t g) := by
  obtain ⟨p, d, -, -, -⟩ := hA ℓ hF t s g hs
  obtain ⟨-, -, l, -, -⟩ := hA ℓ hF t s' g hs'
  have hrt := hF.rt_pos
  have hn₁ := hF.n₁_pos
  have hcap : ∀ m : ℕ, B * Real.exp (-(ℓ.rt / 2 ^ 9 * m)) ≤ weightGrowthSup ℓ.rt ℓ.n₁ * B / ℓ.weight m :=
    fun m => by
    have he := exp_le_weightGrowthSup_div ℓ hrt hn₁ m (ℓ.rt / 2 ^ 9) (le_of_eq (by ring))
    calc B * Real.exp (-(ℓ.rt / 2 ^ 9 * m)) ≤ B * (weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight m) :=
          mul_le_mul_of_nonneg_left he hB
      _ = weightGrowthSup ℓ.rt ℓ.n₁ * B / ℓ.weight m := by ring
  have hσ := hF.σ_pos
  have hC0 := weightGrowthSup_nonneg ℓ.rt ℓ.n₁
  refine ⟨p hd, ?_, ?_⟩
  · intro n _ hn y W hW k c X h1 h3 hX
    refine (d _ hdec n hn y W hW k c X h1 h3 hX).trans ((hcap _).trans (le_of_eq ?_))
    beta_reduce
    split_ifs <;> rfl
  · have l' := l _ (isLocalOnTori_mono hloc hcap)
    have := localComparison_centeredFamily hσ (by
      exact p hd) l' (fun m => div_nonneg (mul_nonneg hC0 hB) (weight_pos ℓ m).le)
    intro n n' _ _ hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    refine (this n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu).trans (le_of_eq ?_)
    ring
theorem termBounds_scaled_abs {e e₃ d b : ℝ} {g : LocalDensity} (hg : TermBounds ℓ e e₃ d g) :
    TermBounds ℓ (|b| * e) (|b| * e₃) (|b| * d) (scaledDensity b g) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro n _ hn y W hW k c X
    exact contDiffAt_const.mul (hg.admissible.smooth n hn y W hW k c X)
  · intro n _ hn y γ W hW
    simp only [scaledDensity]
    rw [hg.admissible.gauge n hn y γ W hW]
  · intro n _ hn y u W hW
    simp only [scaledDensity]
    rw [hg.admissible.translation n hn y u W hW]
  · intro n _ hn y W hW k c X h1 h3 hX
    have e₁ : mixedDeriv (scaledDensity b g n y) W c X = b * mixedDeriv (g n y) W c X :=
      mixedDeriv_const_mul b (g n y) W c X h3 (hg.admissible.smooth n hn y W hW k c X)
    rw [e₁, abs_mul]
    refine (mul_le_mul_of_nonneg_left (hg.derivDecay n hn y W hW k c X h1 h3 hX) (abs_nonneg b)).trans
      (le_of_eq ?_)
    beta_reduce
    split_ifs <;> rw [mul_div_assoc]
  · intro n n' _ _ hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu
    have hk3 : k ≤ 3 := by omega
    have e₁ : mixedDeriv (centeredFamily (scaledDensity b g) n y) W (fun l => bondFrom y (bb l)) X =
        b * mixedDeriv (centeredFamily g n y) W (fun l => bondFrom y (bb l)) X := by
      have : centeredFamily (scaledDensity b g) n y = fun V => b * centeredFamily g n y V :=
        centered_scaledDensity b g n y
      rw [this]
      exact mixedDeriv_const_mul b _ W _ X hk3 ((hg.admissible.smooth n hn y W hW k _ X).sub contDiffAt_const)
    have e₂ : mixedDeriv (centeredFamily (scaledDensity b g) n' y') W' (fun l => bondFrom y' (bb l)) X =
        b * mixedDeriv (centeredFamily g n' y') W' (fun l => bondFrom y' (bb l)) X := by
      have : centeredFamily (scaledDensity b g) n' y' = fun V => b * centeredFamily g n' y' V :=
        centered_scaledDensity b g n' y'
      rw [this]
      exact mixedDeriv_const_mul b _ W' _ X hk3 ((hg.admissible.smooth n' hn' y' W' hW' k _ X).sub contDiffAt_const)
    rw [e₁, e₂, ← mul_sub, abs_mul]
    refine (mul_le_mul_of_nonneg_left
      (hg.centered_compare n n' hn hn' y y' W W' m h2 h2' hW hW' ag k bb X hk hbox hu) (abs_nonneg b)).trans
      (le_of_eq ?_)
    beta_reduce
    rw [mul_div_assoc]
theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
theorem rpow_mul_exp_frameRadius_le_one {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∃ y₀ : ℝ, ∀ x : ℝ, y₀ ≤ x → K * x ^ (3 / 2 : ℝ) * Real.exp (-(c * frameRadius x)) ≤ 1 := by
  set K' : ℝ := |K| * Real.exp c * (2 ^ 11 / c) ^ 150 with hK'
  have t₁ : Filter.Tendsto (fun v : ℝ => v ^ 150 * Real.exp (-v)) Filter.atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 150
  have t₂ : Filter.Tendsto (fun x : ℝ => c / 2 ^ 11 * x ^ (1 / 100 : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) (tendsto_rpow_atTop (by norm_num))
  have t₃ := (t₁.comp t₂).const_mul K'
  rw [mul_zero] at t₃
  have ev := (t₃.eventually (gt_mem_nhds (one_pos))).and (Filter.eventually_gt_atTop (0 : ℝ))
  obtain ⟨y₀, hy⟩ := Filter.eventually_atTop.mp ev
  refine ⟨y₀, fun x hx => ?_⟩
  obtain ⟨h1, hx0⟩ := hy x hx
  simp only [Function.comp] at h1
  set u : ℝ := x ^ (1 / 100 : ℝ) with hu
  have hpow : x ^ (3 / 2 : ℝ) = u ^ 150 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hm : u / 2 ^ 11 - 1 ≤ (frameRadius x : ℝ) := by
    have h2 : ⌈u⌉₊ < 2 ^ 11 * (⌈u⌉₊ / 2 ^ 11 + 1) := Nat.lt_mul_div_succ _ (by norm_num)
    have h3 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have h4 : ((⌈u⌉₊ : ℕ) : ℝ) ≤ 2 ^ 11 * (((⌈u⌉₊ / 2 ^ 11 : ℕ) : ℝ) + 1) := by exact_mod_cast h2.le
    have h5 : (frameRadius x : ℝ) = ((⌈u⌉₊ / 2 ^ 11 : ℕ) : ℝ) := rfl
    rw [h5]
    have : u / 2 ^ 11 ≤ ((⌈u⌉₊ / 2 ^ 11 : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hexp : Real.exp (-(c * frameRadius x)) ≤ Real.exp c * Real.exp (-(c / 2 ^ 11 * u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : c * (u / 2 ^ 11 - 1) ≤ c * frameRadius x := mul_le_mul_of_nonneg_left hm hc.le
    linarith
  have hpos : 0 ≤ u ^ 150 := by positivity
  have e₂ : K' * ((c / 2 ^ 11 * u) ^ 150 * Real.exp (-(c / 2 ^ 11 * u))) =
      |K| * u ^ 150 * (Real.exp c * Real.exp (-(c / 2 ^ 11 * u))) := by
    rw [hK', mul_pow]
    have : (2 ^ 11 / c) ^ 150 * (c / 2 ^ 11) ^ 150 = (1 : ℝ) := by
      rw [← mul_pow]
      have : (2 ^ 11 / c) * (c / 2 ^ 11) = (1 : ℝ) := by field_simp
      rw [this, one_pow]
    calc _ = |K| * Real.exp c * ((2 ^ 11 / c) ^ 150 * (c / 2 ^ 11) ^ 150) * u ^ 150 *
          Real.exp (-(c / 2 ^ 11 * u)) := by ring
      _ = _ := by rw [this]; ring
  rw [hpow]
  calc K * u ^ 150 * Real.exp (-(c * frameRadius x))
      ≤ |K| * u ^ 150 * Real.exp (-(c * frameRadius x)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hpos) (Real.exp_pos _).le
    _ ≤ |K| * u ^ 150 * (Real.exp c * Real.exp (-(c / 2 ^ 11 * u))) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) hpos)
    _ = K' * ((c / 2 ^ 11 * u) ^ 150 * Real.exp (-(c / 2 ^ 11 * u))) := e₂.symm
    _ ≤ 1 := h1.le
theorem rpow_mul_exp_le_one {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∃ y₀ : ℝ, ∀ x : ℝ, y₀ ≤ x → K * x ^ (3 / 2 : ℝ) * Real.exp (-(c * x)) ≤ 1 := by
  have t₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 2) c hc).const_mul K
  rw [mul_zero] at t₁
  obtain ⟨y₀, hy⟩ := Filter.eventually_atTop.mp (t₁.eventually (gt_mem_nhds one_pos))
  refine ⟨y₀, fun x hx => ?_⟩
  have := hy x hx
  have e : K * (x ^ (3 / 2 : ℝ) * Real.exp (-c * x)) = K * x ^ (3 / 2 : ℝ) * Real.exp (-(c * x)) := by
    rw [neg_mul, mul_assoc]
  rw [← e]
  exact this.le
end TermCalculus
end ResponseInTheExpansion
end YangMills.Construction
end
