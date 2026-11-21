import YangMills.Construction.LawByMomentsOfTheFlow.GradientsOfAStepAreFarApartProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion YangMills.Construction.CompletedForms YangMills.Construction.RenormalizationStepParameters
namespace CompletedFormMoments
section LpBounds
variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {k : ℕ}
private def HasLpBound (μ : Measure Ω) (k : ℕ) (F : Ω → ℝ) (B : ℝ) : Prop :=
  0 ≤ B ∧ MemLp F k μ ∧ eLpNorm F k μ ≤ ENNReal.ofReal B
private theorem HasLpBound.congr_le {F G : Ω → ℝ} {B B' : ℝ} (h : HasLpBound μ k F B) (e : ∀ ω, F ω = G ω)
    (hB : B ≤ B') : HasLpBound μ k G B' := by
  obtain rfl : F = G := funext e
  exact ⟨h.1.trans hB, h.2.1, h.2.2.trans (ENNReal.ofReal_le_ofReal hB)⟩
private theorem HasLpBound.add (hk : 1 ≤ k) {F G : Ω → ℝ} {B B' : ℝ} (h : HasLpBound μ k F B)
    (h' : HasLpBound μ k G B') : HasLpBound μ k (fun ω => F ω + G ω) (B + B') := by
  refine ⟨add_nonneg h.1 h'.1, h.2.1.add h'.2.1, ?_⟩
  have h1 : (1 : ENNReal) ≤ (k : ENNReal) := by exact_mod_cast hk
  refine (eLpNorm_add_le h.2.1.1 h'.2.1.1 h1).trans ?_
  rw [ENNReal.ofReal_add h.1 h'.1]
  exact add_le_add h.2.2 h'.2.2
private theorem HasLpBound.zero : HasLpBound μ k (fun _ => 0) 0 :=
  ⟨le_rfl, MemLp.zero', by simp⟩
private theorem HasLpBound.sum (hk : 1 ≤ k) {ι : Type} (s : Finset ι) {F : ι → Ω → ℝ} {B : ι → ℝ}
    (h : ∀ i ∈ s, HasLpBound μ k (F i) (B i)) :
    HasLpBound μ k (fun ω => ∑ i ∈ s, F i ω) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasLpBound.zero
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self i s)).add hk (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr_le
      (fun ω => by rw [Finset.sum_insert hi]) ?_
    rw [Finset.sum_insert hi]
private theorem HasLpBound.const_mul {F : Ω → ℝ} {B : ℝ} (h : HasLpBound μ k F B) (c : ℝ) :
    HasLpBound μ k (fun ω => c * F ω) (|c| * B) := by
  refine ⟨mul_nonneg (abs_nonneg c) h.1, h.2.1.const_mul c, ?_⟩
  have h1 : eLpNorm (c • F) k μ ≤ ‖c‖ₑ * eLpNorm F k μ := eLpNorm_const_smul_le
  refine le_trans h1 ?_
  rw [ENNReal.ofReal_mul (abs_nonneg c), Real.enorm_eq_ofReal_abs]
  gcongr
  exact h.2.2
private theorem HasLpBound.const [IsProbabilityMeasure μ] (hk : k ≠ 0) (c : ℝ) :
    HasLpBound μ k (fun _ => c) |c| := by
  refine ⟨abs_nonneg c, memLp_const c, ?_⟩
  rw [eLpNorm_const c (by exact_mod_cast hk) (IsProbabilityMeasure.ne_zero μ)]
  simp [Real.enorm_eq_ofReal_abs]
private theorem HasLpBound.of_abs_le {F G : Ω → ℝ} {B : ℝ} (h : HasLpBound μ k G B)
    (hF : AEStronglyMeasurable F μ) (hle : ∀ ω, |F ω| ≤ |G ω|) : HasLpBound μ k F B :=
  ⟨h.1, h.2.1.of_le hF (Filter.Eventually.of_forall hle), (eLpNorm_mono hle).trans h.2.2⟩
private theorem HasLpBound.map_iff {f : Ω → Ω'} {g : Ω' → ℝ} {B : ℝ} (hg : AEStronglyMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : HasLpBound (μ.map f) k g B ↔ HasLpBound μ k (g ∘ f) B := by
  unfold HasLpBound
  rw [memLp_map_measure_iff hg hf, eLpNorm_map_measure hg hf]
private theorem HasLpBound.moment (hk : k ≠ 0) {F : Ω → ℝ} {B : ℝ} (h : HasLpBound μ k F B) :
    Integrable (fun ω => |F ω| ^ k) μ ∧ ∫ ω, |F ω| ^ k ∂μ ≤ B ^ k := by
  have hint : Integrable (fun ω => |F ω| ^ k) μ := by
    simpa [Real.norm_eq_abs] using h.2.1.integrable_norm_pow hk
  refine ⟨hint, ?_⟩
  have h0 : (k : ENNReal) ≠ 0 := by exact_mod_cast hk
  have e := h.2.1.eLpNorm_eq_integral_rpow_norm h0 (ENNReal.natCast_ne_top k)
  have h2 := h.2.2
  rw [e, ENNReal.toReal_natCast] at h2
  simp only [Real.norm_eq_abs, Real.rpow_natCast] at h2
  have hI : 0 ≤ ∫ ω, |F ω| ^ k ∂μ := integral_nonneg fun ω => by positivity
  have h3 := (ENNReal.ofReal_le_ofReal_iff h.1).mp h2
  have h4 := pow_le_pow_left₀ (Real.rpow_nonneg hI _) h3 k
  rwa [Real.rpow_inv_natCast_pow hI hk] at h4
private def stdGaussianSqNorm (k : ℕ) : ℝ := (eLpNorm (fun x : ℝ => x ^ 2) k (gaussianReal 0 1)).toReal
private theorem stdGaussianSqNorm_nonneg (k : ℕ) : 0 ≤ stdGaussianSqNorm k := ENNReal.toReal_nonneg
private theorem memLp_sq_stdGaussian (k : ℕ) : MemLp (fun x : ℝ => x ^ 2) k (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (2 * (k : ENNReal))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top k))).norm_rpow_div 2
  have e : (2 * (k : ENNReal)) / 2 = k := by
    rw [mul_comm, mul_div_assoc, ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  rw [e] at h
  have e2 : (fun x : ℝ => x ^ 2) = fun x => ‖id x‖ ^ (2 : ENNReal).toReal := by
    funext x
    simp
  rw [e2]
  exact h
private theorem aemeasurable_of_map_eq_gaussianReal {G : Ω → ℝ} {v : NNReal} (hlaw : μ.map G = gaussianReal 0 v) :
    AEMeasurable G μ := by
  by_contra h
  rw [Measure.map_of_not_aemeasurable h] at hlaw
  have h1 : (gaussianReal 0 v) Set.univ = 1 := measure_univ
  rw [← hlaw] at h1
  simp at h1
private theorem hasLpBound_sq_of_gaussian {G : Ω → ℝ} {v : NNReal} {V : ℝ} (hv : (v : ℝ) ≤ V)
    (hlaw : μ.map G = gaussianReal 0 v) : HasLpBound μ k (fun ω => G ω ^ 2) (V * stdGaussianSqNorm k) := by
  have hG := aemeasurable_of_map_eq_gaussianReal hlaw
  have hm : Measurable fun x : ℝ => x ^ 2 := by fun_prop
  have base : HasLpBound (gaussianReal 0 1) k (fun x : ℝ => x ^ 2) (stdGaussianSqNorm k) :=
    ⟨stdGaussianSqNorm_nonneg k, memLp_sq_stdGaussian k,
      by rw [stdGaussianSqNorm, ENNReal.ofReal_toReal (memLp_sq_stdGaussian k).2.ne]⟩
  have s1 := base.const_mul (v : ℝ)
  have hT : gaussianReal (0 : ℝ) v = (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  have s2 : HasLpBound (gaussianReal 0 v) k (fun x : ℝ => x ^ 2) (|(v : ℝ)| * stdGaussianSqNorm k) := by
    rw [hT]
    refine (HasLpBound.map_iff hm.aestronglyMeasurable (by fun_prop)).2 (s1.congr_le (fun x => ?_) le_rfl)
    simp [mul_pow, Real.sq_sqrt v.coe_nonneg]
  rw [← hlaw] at s2
  have s3 := (HasLpBound.map_iff hm.aestronglyMeasurable hG).1 s2
  refine s3.congr_le (fun ω => rfl) ?_
  rw [abs_of_nonneg v.coe_nonneg]
  exact mul_le_mul_of_nonneg_right hv (stdGaussianSqNorm_nonneg k)
private theorem hasLpBound_mul_of_sq (hk : 1 ≤ k) {G G' : Ω → ℝ} {B : ℝ} (hG : AEMeasurable G μ)
    (hG' : AEMeasurable G' μ) (h : HasLpBound μ k (fun ω => G ω ^ 2) B) (h' : HasLpBound μ k (fun ω => G' ω ^ 2) B) :
    HasLpBound μ k (fun ω => G ω * G' ω) B := by
  have h2 : HasLpBound μ k (fun ω => 1 / 2 * (G ω ^ 2 + G' ω ^ 2)) B :=
    ((h.add hk h').const_mul (1 / 2)).congr_le (fun ω => rfl)
      (show |(1 / 2 : ℝ)| * (B + B) ≤ B by rw [abs_of_pos (by norm_num)]; linarith)
  refine h2.of_abs_le (hG.mul hG').aestronglyMeasurable fun ω => ?_
  have h3 : 0 ≤ 1 / 2 * (G ω ^ 2 + G' ω ^ 2) := by positivity
  rw [abs_of_nonneg h3, abs_mul]
  nlinarith [sq_nonneg (|G ω| - |G' ω|), sq_abs (G ω), sq_abs (G' ω)]
private theorem hasLpBound_kernel (hk : 1 ≤ k) {P : Type} (A : Finset P) (κ : P → P → ℝ) (G : P → Ω → ℝ) {B : ℝ}
    (hG : ∀ p ∈ A, AEMeasurable (G p) μ) (hs : ∀ p ∈ A, HasLpBound μ k (fun ω => G p ω ^ 2) B) :
    HasLpBound μ k (fun ω => ∑ p ∈ A, ∑ p' ∈ A, κ p p' * G p ω * G p' ω) (∑ p ∈ A, ∑ p' ∈ A, |κ p p'| * B) :=
  HasLpBound.sum hk A fun p hp => HasLpBound.sum hk A fun p' hp' =>
    ((hasLpBound_mul_of_sq hk (hG p hp) (hG p' hp') (hs p hp) (hs p' hp')).const_mul (κ p p')).congr_le
      (fun _ => (mul_assoc _ _ _).symm) le_rfl
end LpBounds
section Chains
variable {L : ℕ} [NeZero L]
private theorem measurable_chainLower {s n : ℕ} :
    Measurable (chainLower : LevelChain L (s + 1) n → LevelChain L s (n * L)) := by apply _root_.YangMills.SharedProofs.p17945 <;> assumption
private theorem measurable_chainTop : ∀ (s n : ℕ), Measurable (chainTop s n : LevelChain L s n → ColourForm n)
  | 0, _ => measurable_id
  | s + 1, n => by
    refine measurable_pi_iff.mpr fun e => measurable_pi_iff.mpr fun b => ?_
    exact (measurable_pi_apply (Sum.inr b : LevelBond L (s + 1) n)).comp (measurable_pi_apply e)
private theorem measurable_chainDescend (l : ℕ) : ∀ (d n : ℕ),
    Measurable (chainDescend l d n : LevelChain L (l + d) n → LevelChain L l (fineSide L d n))
  | 0, _ => measurable_id
  | d + 1, n => (measurable_chainDescend l d (n * L)).comp measurable_chainLower
private theorem chainLower_truncateTop {j s n : ℕ} (h : j + 1 ≤ s + 1) (X : LevelChain L (s + 1) n) :
    chainLower (truncateTop (j + 1) (s + 1) n h X) =
      truncateTop j s (n * L) (Nat.le_of_succ_le_succ h) (chainLower X) := rfl
private theorem chainTop_truncateTop : ∀ (j s n : ℕ) (h : j ≤ s) (X : LevelChain L s n),
    chainTop j n (truncateTop j s n h X) = chainTop s n X
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, h, _ => absurd h (by omega)
  | _ + 1, _ + 1, _, _, _ => rfl
private theorem chainDefect_truncateTop {j s n : ℕ} [NeZero n] (h : j + 1 ≤ s + 1) (X : LevelChain L (s + 1) n) :
    chainDefect (truncateTop (j + 1) (s + 1) n h X) = chainDefect X := by
  funext e c
  unfold chainDefect
  rw [chainLower_truncateTop, chainTop_truncateTop, chainTop_truncateTop]
private theorem chainBottom_truncateTop (l : ℕ) : ∀ (j n : ℕ) (h : j ≤ l + j) (X : LevelChain L (l + j) n),
    chainBottom j n (truncateTop j (l + j) n h X) = chainTop l (fineSide L j n) (chainDescend l j n X)
  | 0, _, _, _ => rfl
  | j + 1, n, h, X => chainBottom_truncateTop l j (n * L) (Nat.le_of_succ_le_succ h) (chainLower X)
private theorem noisePairing_zero : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    noisePairing s n (fun _ => 0) X = 0
  | 0, n, _, X => by simp [noisePairing]
  | s + 1, n, _, X => by
    simp [noisePairing, noisePairing_zero s (n * L)]
private theorem noiseVariance_zero (a : ℝ) : ∀ (s n : ℕ) [NeZero n],
    noiseVariance a s n (fun _ : ChainNoise L s n => 0) = 0
  | 0, n, _ => by simp [noiseVariance, curvatureVariance]
  | s + 1, n, _ => by
    simp [noiseVariance, noiseVariance_zero a s (n * L)]
private def lowerCoeff {s n : ℕ} (co : ChainNoise L s (n * L) → ℝ) : ChainNoise L (s + 1) n → ℝ :=
  Sum.elim co fun _ => 0
open Classical in
private def topUnitCoeff {s n : ℕ} (e : Fin 3) (c : TorusBond n) : ChainNoise L (s + 1) n → ℝ :=
  Sum.elim (fun _ => 0) fun q => if q = (e, c) then 1 else 0
private theorem noisePairing_lowerCoeff {s n : ℕ} [NeZero n] (co : ChainNoise L s (n * L) → ℝ)
    (X : LevelChain L (s + 1) n) :
    noisePairing (s + 1) n (lowerCoeff co) X = noisePairing s (n * L) co (chainLower X) := by
  show noisePairing s (n * L) (fun i => lowerCoeff co (Sum.inl i)) (chainLower X) +
    ∑ b : TorusBond n, ∑ e : Fin 3, lowerCoeff (L := L) (s := s) co (Sum.inr (e, b)) * chainDefect X e b = _
  simp [lowerCoeff]
private theorem noiseVariance_lowerCoeff (a : ℝ) {s n : ℕ} [NeZero n] (co : ChainNoise L s (n * L) → ℝ) :
    noiseVariance a (s + 1) n (lowerCoeff co) = noiseVariance a s (n * L) co := by
  show noiseVariance a s (n * L) (fun i => lowerCoeff co (Sum.inl i)) +
    a⁻¹ * ∑ b : TorusBond n, ∑ e : Fin 3, lowerCoeff (L := L) (s := s) co (Sum.inr (e, b)) ^ 2 = _
  simp [lowerCoeff]
private theorem noisePairing_topUnitCoeff {s n : ℕ} [NeZero n] (e : Fin 3) (c : TorusBond n)
    (X : LevelChain L (s + 1) n) : noisePairing (s + 1) n (topUnitCoeff e c) X = chainDefect X e c := by
  classical
  show noisePairing s (n * L) (fun _ => 0) (chainLower X) +
    ∑ b : TorusBond n, ∑ e' : Fin 3, topUnitCoeff (L := L) (s := s) e c (Sum.inr (e', b)) * chainDefect X e' b = _
  rw [noisePairing_zero, zero_add, Finset.sum_eq_single c, Finset.sum_eq_single e]
  · simp [topUnitCoeff]
  · intro e' _ he
    simp [topUnitCoeff, he]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun e' _ => ?_
    simp [topUnitCoeff, hb]
  · simp
private theorem noiseVariance_topUnitCoeff (a : ℝ) {s n : ℕ} [NeZero n] (e : Fin 3) (c : TorusBond n) :
    noiseVariance a (s + 1) n (topUnitCoeff (L := L) e c) = a⁻¹ := by
  classical
  show noiseVariance a s (n * L) (fun _ => 0) +
    a⁻¹ * ∑ b : TorusBond n, ∑ e' : Fin 3, topUnitCoeff (L := L) (s := s) e c (Sum.inr (e', b)) ^ 2 = _
  rw [noiseVariance_zero, zero_add, Finset.sum_eq_single c, Finset.sum_eq_single e]
  · simp [topUnitCoeff]
  · intro e' _ he
    simp [topUnitCoeff, he]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun e' _ => ?_
    simp [topUnitCoeff, hb]
  · simp
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
private def HasGaussianNoise (μ : Measure Ω) (a : ℝ) (s n : ℕ) [NeZero n] (Ψ : Ω → LevelChain L s n) : Prop :=
  ∀ co : ChainNoise L s n → ℝ, μ.map (fun ω => noisePairing s n co (Ψ ω)) =
    gaussianReal 0 (noiseVariance a s n co).toNNReal
private theorem HasGaussianNoise.lower {a : ℝ} {s n : ℕ} [NeZero n] {Ψ : Ω → LevelChain L (s + 1) n}
    (h : HasGaussianNoise μ a (s + 1) n Ψ) : HasGaussianNoise μ a s (n * L) fun ω => chainLower (Ψ ω) := fun co => by
  have h1 := h (lowerCoeff co)
  simpa only [noisePairing_lowerCoeff, noiseVariance_lowerCoeff] using h1
private theorem HasGaussianNoise.defect {a : ℝ} {s n : ℕ} [NeZero n] {Ψ : Ω → LevelChain L (s + 1) n}
    (h : HasGaussianNoise μ a (s + 1) n Ψ) (e : Fin 3) (c : TorusBond n) :
    μ.map (fun ω => chainDefect (Ψ ω) e c) = gaussianReal 0 (a⁻¹).toNNReal := by
  have h1 := h (topUnitCoeff e c)
  simpa only [noisePairing_topUnitCoeff, noiseVariance_topUnitCoeff] using h1
private theorem hasLpBound_bondScore [IsProbabilityMeasure μ] (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) {s n : ℕ} [NeZero n]
    {Ψ : Ω → LevelChain L (s + 1) n} (h : HasGaussianNoise μ a (s + 1) n Ψ) (c : TorusBond n) :
    HasLpBound μ k (fun ω => (1 / 2) * ∑ e : Fin 3, chainDefect (Ψ ω) e c ^ 2 - 3 / (2 * a))
      (3 / 2 * a⁻¹ * (stdGaussianSqNorm k + 1)) := by
  have hv : (((a⁻¹).toNNReal : NNReal) : ℝ) ≤ a⁻¹ := (Real.coe_toNNReal _ (inv_pos.mpr ha).le).le
  have hs : ∀ e : Fin 3, HasLpBound μ k (fun ω => chainDefect (Ψ ω) e c ^ 2) (a⁻¹ * stdGaussianSqNorm k) := fun e =>
    hasLpBound_sq_of_gaussian hv (h.defect e c)
  have h2 := ((HasLpBound.sum hk Finset.univ fun e _ => hs e).const_mul (1 / 2)).add hk
    (HasLpBound.const (μ := μ) (k := k) (by omega) (-(3 / (2 * a))))
  refine h2.congr_le (fun ω => (sub_eq_add_neg _ _).symm) (le_of_eq ?_)
  have e1 : 3 / (2 * a) = 3 / 2 * a⁻¹ := by field_simp
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_neg, abs_of_pos (by positivity : 0 < 3 / (2 * a)), e1]
  push_cast
  ring
private theorem hasLpBound_cumulativeScores [IsProbabilityMeasure μ] (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) (τ l K : ℕ)
    (w : ∀ m : ℕ, PlaquetteWeight m) (sd : ℕ → ℕ) (hsd : ∀ T, T + 1 ≤ K → sd (T + 1) * L = sd T) {H : ℝ} (hH : 0 ≤ H)
    (hmean : ∀ (T n : ℕ) [NeZero n], l < T → T ≤ τ → n = sd T → ∑ c : TorusBond n, |bondBlockMean L T n (w _) c| ≤ H) :
    ∀ (j s n : ℕ) [NeZero n] (hj : j ≤ s) (Ψ : Ω → LevelChain L s n), l + j ≤ K → n = sd (l + j) →
      HasGaussianNoise μ a s n Ψ →
      HasLpBound μ k (fun ω => cumulativeScores a τ l w j n (truncateTop j s n hj (Ψ ω)))
        ((min j (τ - l) : ℕ) * (a * H * (3 / 2 * a⁻¹ * (stdGaussianSqNorm k + 1)))) := by
  have hE : 0 ≤ 3 / 2 * a⁻¹ * (stdGaussianSqNorm k + 1) := by
    have := stdGaussianSqNorm_nonneg k
    positivity
  have hD : 0 ≤ a * H * (3 / 2 * a⁻¹ * (stdGaussianSqNorm k + 1)) := mul_nonneg (mul_nonneg ha.le hH) hE
  intro j
  induction j with
  | zero =>
    intro s n _ hj Ψ _ _ _
    simpa [cumulativeScores] using HasLpBound.zero (μ := μ) (k := k)
  | succ j ih =>
    intro s n _ hj Ψ hK hn hN
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have IH := ih s (n * L) (Nat.le_of_succ_le_succ hj) (fun ω => chainLower (Ψ ω)) (by omega)
      (by rw [hn]; exact hsd (l + j) (by omega)) hN.lower
    have key : ∀ ω, cumulativeScores a τ l w (j + 1) n (truncateTop (j + 1) (s + 1) n hj (Ψ ω)) =
        cumulativeScores a τ l w j (n * L) (truncateTop j s (n * L) (Nat.le_of_succ_le_succ hj) (chainLower (Ψ ω))) +
          if l + j + 1 ≤ τ then
            a * ∑ c : TorusBond n, bondBlockMean L (l + j + 1) n (w _) c *
              ((1 / 2) * ∑ e : Fin 3, chainDefect (Ψ ω) e c ^ 2 - 3 / (2 * a))
          else 0 := by
      intro ω
      rw [cumulativeScores, chainLower_truncateTop, chainDefect_truncateTop]
    by_cases hc : l + j + 1 ≤ τ
    · have hterm : HasLpBound μ k (fun ω => a * ∑ c : TorusBond n, bondBlockMean L (l + j + 1) n (w _) c *
          ((1 / 2) * ∑ e : Fin 3, chainDefect (Ψ ω) e c ^ 2 - 3 / (2 * a)))
          (a * H * (3 / 2 * a⁻¹ * (stdGaussianSqNorm k + 1))) := by
        refine ((HasLpBound.sum hk Finset.univ fun c _ =>
          (hasLpBound_bondScore hk ha hN c).const_mul _).const_mul a).congr_le (fun ω => rfl) ?_
        rw [abs_of_pos ha, ← Finset.sum_mul, mul_assoc a H]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hmean _ n (by omega) hc (by rw [hn]; rfl)) hE) ha.le
      refine (IH.add hk hterm).congr_le (fun ω => ?_) ?_
      · rw [key, if_pos hc]
      · have e1 : min j (τ - l) = j := min_eq_left (by omega)
        have e2 : min (j + 1) (τ - l) = j + 1 := min_eq_left (by omega)
        rw [e1, e2]
        push_cast
        linarith
    · refine IH.congr_le (fun ω => ?_) ?_
      · rw [key, if_neg hc, add_zero]
      · refine mul_le_mul_of_nonneg_right ?_ hD
        exact_mod_cast min_le_min_right _ (Nat.le_succ j)
end Chains
section BlockMeans
variable {L : ℕ} [NeZero L]
private theorem sum_abs_bondBlockMean_le (hodd : Odd L) (h₆ : BlockMeanIsLinearAndLocal)
    (h₇ : WeightsCloseToBlockMeans) (t n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide L t n)) (hs : weightSup h ≤ 1) :
    ∑ c : TorusBond n, |bondBlockMean L t n h c| ≤ 4 * ((weightSupportSites L t n h).card : ℝ) := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : TorusSite n → ℝ, φ = fun y => |blockMean L t n y h| := ⟨_, rfl⟩
  have hφ1 : ∀ y, φ y ≤ if y ∈ weightSupportSites L t n h then 1 else 0 := by
    intro y
    rw [hφ]
    by_cases hy : y ∈ weightSupportSites L t n h
    · rw [if_pos hy]
      exact ((h₇ L hodd t n y).1 h).trans hs
    · rw [if_neg hy]
      have hz : ∀ p, IsPlaquetteAt L t y p → h p = 0 * h p + 0 * h p := by
        intro p hp
        by_contra hne
        refine hy ?_
        simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨p, hp, fun h0 => hne (by rw [h0]; ring)⟩
      obtain ⟨_, hlin, hloc⟩ := h₆ L hodd t n y
      have h1 := hloc h (fun p => 0 * h p + 0 * h p) hz
      rw [hlin] at h1
      have h2 : blockMean L t n y h = 0 := by linarith
      show |blockMean L t n y h| ≤ 0
      rw [h2, abs_zero]
  have hsum : ∑ y, φ y ≤ ((weightSupportSites L t n h).card : ℝ) := by
    refine (Finset.sum_le_sum fun y _ => hφ1 y).trans (le_of_eq ?_)
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hb : ∀ c : TorusBond n, |bondBlockMean L t n h c| ≤ (φ c.1 + φ (c.1 + unitStep n c.2)) / 2 := by
    intro c
    rw [hφ]
    unfold bondBlockMean
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  refine (Finset.sum_le_sum fun c _ => hb c).trans
    (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)))
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h2 : ∀ i : Fin 4, ∑ x : TorusSite n, (φ x + φ (x + unitStep n i)) / 2 = ∑ y, φ y := by
    intro i
    have h3 : ∑ x : TorusSite n, φ (x + unitStep n i) = ∑ y, φ y :=
      Equiv.sum_comp (Equiv.addRight (unitStep n i)) φ
    rw [← Finset.sum_div, Finset.sum_add_distrib, h3]
    ring
  simp only [h2]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
end BlockMeans
section Curvature
private theorem exists_gaussian_curl {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    (E : ColourForm m → ℝ) (Φ : Ω → ColourForm m) (hΦ : Measurable Φ) (hcan : IsCanonicalGaussian E (μ.map Φ)) (C : ℝ)
    (hb : ∀ (X : ColourForm m) (p : TorusPlaquette m), p.2.1 < p.2.2 → curlNorm X p ^ 2 ≤ C * E X) (e : Fin 3)
    (p : TorusPlaquette m) (hp : p.2.1 < p.2.2) :
    ∃ v : NNReal, (v : ℝ) ≤ |C| ∧ μ.map (fun ω => curl (Φ ω e) p) = gaussianReal 0 v := by
  have hsq : ∀ X : ColourForm m, curl (X e) p ^ 2 ≤ curlNorm X p ^ 2 := by
    intro X
    unfold curlNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.single_le_sum (f := fun e' => curl (X e') p ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ e)
  let f : ColourForm m →ₗ[ℝ] ℝ :=
    { toFun := fun X => curl (X e) p
      map_add' := fun X Y => by simp only [curl, Pi.add_apply]; ring
      map_smul' := fun c X => by simp only [curl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hf : Measurable f := by
    have hc : ∀ b : TorusBond m, Measurable fun X : ColourForm m => X e b := fun b =>
      (measurable_pi_apply b).comp (measurable_pi_apply e)
    show Measurable fun X : ColourForm m => curl (X e) p
    unfold curl
    exact (((hc _).add (hc _)).sub (hc _)).sub (hc _)
  have hker : ∀ X, E X = 0 → f X = 0 := by
    intro X hX
    have h1 := (hsq X).trans (hb X p hp)
    rw [hX, mul_zero] at h1
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h1 (sq_nonneg _))
  have hlaw := hcan.map_eq f hker
  rw [Measure.map_map hf hΦ] at hlaw
  refine ⟨(gaussianVariance E f).toNNReal, ?_, hlaw⟩
  rw [Real.coe_toNNReal']
  refine max_le (Real.sSup_le ?_ (abs_nonneg C)) (abs_nonneg C)
  rintro w ⟨x, hx, rfl⟩
  rw [div_le_iff₀ hx]
  exact ((hsq x).trans (hb x p hp)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hx.le)
private theorem bilinearEval_sum {n : ℕ} [NeZero n] (A : Finset (TorusSite n)) (q : TorusSite n → BondBilinear n)
    (X X' : TorusBond n → ℝ) :
    bilinearEval (fun b b' => ∑ y ∈ A, q y b b') X X' = ∑ y ∈ A, bilinearEval (q y) X X' := by
  unfold bilinearEval
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
abbrev _root_.YangMills.SharedProofs.p7164 := @bilinearEval_sum
private theorem hasLpBound_colourEval {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ} (hk : 1 ≤ k) {n : ℕ}
    [NeZero n] (A : Finset (TorusSite n)) (q : TorusSite n → BondBilinear n) (Y : Ω → ColourForm n) {B Cf : ℝ}
    (hB : 0 ≤ B)
    (hG : ∀ e, ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), AEMeasurable (fun ω => curl (Y ω e) p) μ)
    (hs : ∀ e, ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      HasLpBound μ k (fun ω => curl (Y ω e) p ^ 2) B)
    (hq : ∀ y, ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ,
      (∀ X X' : TorusBond n → ℝ, bilinearEval (q y) X X' = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), κ p p' * curl X p * curl X' p') ∧
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |κ p p'| ≤ Cf) :
    HasLpBound μ k (fun ω => (1 / 2) * colourEval (fun b b' => ∑ y ∈ A, q y b b') (Y ω) (Y ω))
      ((1 / 2) * (3 * ((A.card : ℝ) * (Cf * B)))) := by
  have h1 : ∀ e, ∀ y ∈ A, HasLpBound μ k (fun ω => bilinearEval (q y) (Y ω e) (Y ω e)) (Cf * B) := by
    intro e y _
    obtain ⟨κ, hr, hκ⟩ := hq y
    refine (hasLpBound_kernel hk _ κ (fun p ω => curl (Y ω e) p) (hG e) (hs e)).congr_le
      (fun ω => (hr _ _).symm) ?_
    simp only [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hκ hB
  have h2 := (HasLpBound.sum hk Finset.univ fun e _ => HasLpBound.sum hk A fun y hy => h1 e y hy).const_mul (1 / 2)
  refine h2.congr_le (fun ω => ?_) (le_of_eq ?_)
  · congr 1
    unfold colourEval
    exact Finset.sum_congr rfl fun e _ => (bilinearEval_sum A q _ _).symm
  · rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    simp
end Curvature
section Parameters
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_forAllPoints
    {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop} (h : ForAllPoints Q) :
    ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S := h
private theorem forAllParameters_mono {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q)
    (hq : ∀ Λ : MomentParameters, 2 ≤ Λ.k → Q Λ → Q' Λ) : ForAllParameters Q' := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, H₁⟩ := h a ha
  refine ⟨L₁, rt₁, C₁, hrt₁, ?_⟩
  intro L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd Kr hKr
  refine ⟨y₁, ?_⟩
  intro y hy hRet hHas g hg hyg k _ hk2 hk8 R d hd
  exact hq ⟨Tb, Kr, y, g, k, R, d⟩ hk2 (Y₁ y hy hRet hHas g hg hyg k hk2 hk8 R d hd)
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.stepParams.Admissible := by apply _root_.YangMills.SharedProofs.p7443 <;> assumption
private theorem stage_depth_eq {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (T : StageTower ℓ) (h : T.base.depth = 0) :
    ∀ t, (T.stage t).depth = t
  | 0 => h
  | t + 1 => by
    show (T.stage t).depth + 1 = t + 1
    rw [stage_depth_eq T h t]
end Parameters
end CompletedFormMoments
set_option maxHeartbeats 1000000 in
open CompletedFormMoments in
theorem completedFormMoments_holds (h₁ : gaussianChainCoordinatesStatement) (h₂ : formsReadCurvatureStatement)
    (h₃ : thirdDerivativeBoundsStatement) (h₄ : classicalFormsAnnihilateClosedStatement)
    (h₅ : weightsSitesBelowScaleStatement) (h₆ : BlockMeanIsLinearAndLocal) (h₇ : WeightsCloseToBlockMeans) :
    completedFormMomentsStatement := by
  unfold completedFormMomentsStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and (forAllParameters_and (forAllParameters_of_forAllPoints h₁)
    (forAllParameters_of_forAllPoints h₂)) (forAllParameters_and (forAllParameters_and
    (forAllParameters_of_forAllPoints h₃) (forAllParameters_of_forAllPoints h₄))
    (forAllParameters_and (forAllParameters_of_forAllPoints h₅) forAllParameters_admissible))) fun Λ hk H => ?_
  obtain ⟨⟨⟨C₁, _, _, _, _, f₁⟩, ⟨C₂, _, _, _, _, f₂⟩⟩, ⟨⟨⟨C₃, _, _, _, _, f₃⟩, ⟨_, _, _, _, _, f₄⟩⟩,
    ⟨⟨C₅, _, _, _, _, f₅⟩, hf⟩⟩⟩ := H
  have hk1 : 1 ≤ Λ.k := by omega
  have ha : 0 < Λ.stepParams.coupling := by linarith [hf.a_ge]
  have hodd : Odd Λ.stepParams.side := hf.L_odd
  have hL16 : 2 ^ 16 ≤ Λ.stepParams.side := hf.L_ge
  have hLpos : 0 < Λ.stepParams.side := by omega
  have hL1 : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast hLpos
  have hrate : 0 ≤ Λ.stepParams.weightRate := by
    have := hf.rt_pos
    unfold StepParameters.weightRate
    positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = stdGaussianSqNorm Λ.k := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ stdGaussianSqNorm_nonneg _
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = |C₁ 0| := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := hV ▸ abs_nonneg _
  obtain ⟨sz, hszd⟩ : ∃ sz : ℝ, sz = |C₃ 1| + 1 := ⟨_, rfl⟩
  have hsz : 0 < sz := by rw [hszd]; positivity
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = |C₂ 0| * sz := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  obtain ⟨Es, hEs⟩ : ∃ Es : ℝ, Es = 3 / 2 * Λ.stepParams.coupling⁻¹ * (M + 1) := ⟨_, rfl⟩
  have hEs0 : 0 ≤ Es := by rw [hEs]; positivity
  obtain ⟨C5, hC5⟩ : ∃ C5 : ℝ, C5 = |C₅ 0| := ⟨_, rfl⟩
  have hC50 : 0 ≤ C5 := hC5 ▸ abs_nonneg _
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ, D₁ = 1 / 2 * (3 * (C5 * (Cf * (V * M)))) := ⟨_, rfl⟩
  have hD₁0 : 0 ≤ D₁ := by rw [hD₁]; positivity
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : ℝ, D₂ = Λ.stepParams.coupling * (4 * C5) * Es := ⟨_, rfl⟩
  have hD₂0 : 0 ≤ D₂ := by rw [hD₂]; positivity
  refine ⟨fun _ => 2 * (D₁ + D₂), 1, Λ.floor, one_pos, le_rfl, fun S s hs μ hμ j hj hl i => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, s = l + j := ⟨s - j, by omega⟩
  simp only [Nat.add_sub_cancel] at hl ⊢
  have := hμ.isProbabilityMeasure
  have hts : S.lastSeparated ≤ S.data.scaleLevel := by
    unfold MomentPoint.lastSeparated
    classical exact Nat.findGreatest_le _
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  have hls : l ≤ S.data.scaleLevel := hl.trans hts
  have hlK : l ≤ S.data.windowLevel := by omega
  have hlev := stage_depth_eq S.tower S.startsAtWilson.depth_eq
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - l)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  obtain ⟨hc1, hc2⟩ := f₁ S l j hs
  obtain ⟨hnoise, hcan, _⟩ := hc2 μ hμ
  have hΦ : Measurable fun X : LevelChain Λ.stepParams.side (l + j) (S.data.period Λ.stepParams.side) =>
      chainTop l (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))
        (chainDescend l j (S.data.period Λ.stepParams.side) X) :=
    (measurable_chainTop l _).comp (measurable_chainDescend l j _)
  have hlaw : ∀ (e : Fin 3) (p : TorusPlaquette (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))),
      p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)))) →
      ∃ v : NNReal, (v : ℝ) ≤ V ∧
        μ.map (fun X : LevelChain Λ.stepParams.side (l + j) (S.data.period Λ.stepParams.side) =>
          curl (chainBottom j (S.data.period Λ.stepParams.side)
            (truncateTop j (l + j) (S.data.period Λ.stepParams.side) hj X) e) p) = gaussianReal 0 v := by
    intro e p hp
    have hlt : p.2.1 < p.2.2 := by
      simp only [plaquettesIn, Finset.mem_filter] at hp
      exact hp.2.1
    obtain ⟨v, hv, hl'⟩ := exists_gaussian_curl (kineticForm Λ.stepParams.coupling Λ.stepParams.side l) _ hΦ hcan
      (C₁ 0) (fun X p hp' => hc1 X ⟨p, hp'⟩) e p hlt
    refine ⟨v, hV ▸ hv, ?_⟩
    simp only [chainBottom_truncateTop]
    exact hl'
  have hker : ∀ (n : ℕ) [NeZero n], n = S.levelSide l → ∀ y : TorusSite n,
      ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ,
      (∀ X X' : TorusBond n → ℝ, bilinearEval (classicalQuadratic S.tower S.resp l n (S.weight i _) y) X X' =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
          κ p p' * curl X p * curl X' p') ∧
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |κ p p'| ≤ Cf := by
    intro n _ hn y
    have hn0 : Λ.stepParams.n₀ ≤ n := by
      rw [hn]
      have h1 : Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ hLpos
      have h2 : S.data.period Λ.stepParams.side ≤ S.levelSide l := Nat.le_mul_of_pos_right _ (pow_pos hLpos _)
      exact h1.trans (S.side_le.trans h2)
    have hs1 : weightNorm Λ.stepParams.side (S.tower.stage l).depth
        (S.weight i (fineSide Λ.stepParams.side (S.tower.stage l).depth n)) ≤ 1 := by
      subst hn
      rw [hlev l]
      exact (f₅ S l hls i).1
    have hs0 : 0 ≤ weightNorm Λ.stepParams.side (S.tower.stage l).depth
        (S.weight i (fineSide Λ.stepParams.side (S.tower.stage l).depth n)) :=
      le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
    have hsize : IsDecayingAbout Λ.stepParams sz y (classicalQuadratic S.tower S.resp l n (S.weight i _) y) := by
      intro b b'
      refine ((f₃ S l hlK n hn0 y (S.weight i _)).2 b b').trans ?_
      have hw : 0 < Λ.stepParams.weight (tripleDiam y b b') := mul_pos (lt_max_of_lt_left one_pos) (Real.exp_pos _)
      refine div_le_div_of_nonneg_right ?_ hw.le
      rw [hszd]
      calc C₃ 1 * _ ≤ |C₃ 1| * weightNorm Λ.stepParams.side (S.tower.stage l).depth
              (S.weight i (fineSide Λ.stepParams.side (S.tower.stage l).depth n)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hs0
        _ ≤ |C₃ 1| * 1 := mul_le_mul_of_nonneg_left hs1 (abs_nonneg _)
        _ ≤ |C₃ 1| + 1 := by linarith
    obtain ⟨κ, hr, hκ⟩ := (f₂ S l hlK n hn y sz _ hsz hsize).1 (f₄ S l hlK n hn0 y _).2.1
    refine ⟨κ, hr, le_trans (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun p' _ => ?_) (hκ.trans ?_)⟩
    · refine le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp ?_)
      positivity
    · rw [hCf]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hsz.le
  have hjn : fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) = S.levelSide l := by
    rw [fineSide_eq]
    show _ = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - l)
    congr 2
    omega
  have hQ := hasLpBound_colourEval hk1 (S.supportAt l _ i) (fun y => classicalQuadratic S.tower S.resp l _ (S.weight i _) y)
    (fun X : LevelChain Λ.stepParams.side (l + j) (S.data.period Λ.stepParams.side) =>
      chainBottom j (S.data.period Λ.stepParams.side) (truncateTop j (l + j) (S.data.period Λ.stepParams.side) hj X))
    (B := V * stdGaussianSqNorm Λ.k) (Cf := Cf) (mul_nonneg hV0 (stdGaussianSqNorm_nonneg _))
    (fun e p hp => by
      obtain ⟨v, _, hl'⟩ := hlaw e p hp
      exact aemeasurable_of_map_eq_gaussianReal hl')
    (fun e p hp => by
      obtain ⟨v, hv, hl'⟩ := hlaw e p hp
      exact hasLpBound_sq_of_gaussian hv hl')
    (hker _ hjn)
  have hcard' : ∀ (n : ℕ) [NeZero n], n = S.levelSide l → ((S.supportAt l n i).card : ℝ) ≤ C5 * P := by
    intro n _ hn
    subst hn
    rw [hC5, hP]
    exact (f₅ S l hls i).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hcard := hcard' _ hjn
  have hmean : ∀ (T n : ℕ) [NeZero n], l < T → T ≤ S.lastSeparated → n = S.levelSide T →
      ∑ c : TorusBond n, |bondBlockMean Λ.stepParams.side T n (S.weight i _) c| ≤ 4 * C5 * P := by
    intro T n _ hlT hTt hn
    subst hn
    have hTs : T ≤ S.data.scaleLevel := hTt.trans hts
    obtain ⟨hw, hcd⟩ := f₅ S T hTs i
    refine (sum_abs_bondBlockMean_le hodd h₆ h₇ T _ _ ((le_max_left _ _).trans hw)).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine hcd.trans ?_
    rw [hC5, hP]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ hL1 (by omega)) (by positivity) (abs_nonneg _)
  have hsd : ∀ T, T + 1 ≤ S.data.windowLevel → S.levelSide (T + 1) * Λ.stepParams.side = S.levelSide T := by
    intro T hT
    show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (T + 1)) * Λ.stepParams.side =
      S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - T)
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega
  have hsl : S.data.period Λ.stepParams.side = S.levelSide (l + j) := by
    show _ = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (l + j))
    rw [hs, Nat.sub_self, pow_zero, mul_one]
  have hSt := hasLpBound_cumulativeScores (μ := μ) (k := Λ.k) hk1 ha S.lastSeparated l S.data.windowLevel (S.weight i)
    S.levelSide hsd (H := 4 * C5 * P) (by positivity) hmean
    j (l + j) (S.data.period Λ.stepParams.side) hj id hs.le hsl (fun co => hnoise co)
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = S.data.scaleLevel - l := ⟨_, rfl⟩
  have hxL : (x : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ x := by
    have : x ≤ Λ.stepParams.side ^ x := (Nat.lt_pow_self (by omega : 1 < Λ.stepParams.side)).le
    exact_mod_cast this
  have hLx : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ x := one_le_pow₀ hL1
  have hmin : ((min j (S.lastSeparated - l) : ℕ) : ℝ) ≤ x := by
    have : min j (S.lastSeparated - l) ≤ x := (min_le_right _ _).trans (by omega)
    exact_mod_cast this
  have hF := (hQ.add hk1 hSt).congr_le (G := fun X => S.completedForm l j (S.data.period Λ.stepParams.side) i
      (truncateTop j (l + j) (S.data.period Λ.stepParams.side) hj X))
    (B' := 2 * (D₁ + D₂) * (Λ.stepParams.side : ℝ) ^ (5 * (S.data.scaleLevel - l))) (fun X => rfl) ?_
  · exact hF.moment (by omega)
  · rw [← hx, ← hM, ← hEs]
    have e5 : (Λ.stepParams.side : ℝ) ^ (5 * x) = P * (Λ.stepParams.side : ℝ) ^ x := by
      rw [hP, ← hx, ← pow_add]
      congr 1
      ring
    rw [e5]
    have b1 : 1 / 2 * (3 * (((S.supportAt l (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) i).card : ℝ) *
        (Cf * (V * M)))) ≤ D₁ * P := by
      rw [hD₁]
      have hB0 : 0 ≤ Cf * (V * M) := by positivity
      have := mul_le_mul_of_nonneg_right hcard hB0
      nlinarith
    have b2 : ((min j (S.lastSeparated - l) : ℕ) : ℝ) * (Λ.stepParams.coupling * (4 * C5 * P) * Es) ≤ x * (D₂ * P) := by
      have e : Λ.stepParams.coupling * (4 * C5 * P) * Es = D₂ * P := by rw [hD₂]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hmin (mul_nonneg hD₂0 hP0)
    have a1 : D₁ * P ≤ D₁ * P * (Λ.stepParams.side : ℝ) ^ x := le_mul_of_one_le_right (mul_nonneg hD₁0 hP0) hLx
    have a2 : (x : ℝ) * (D₂ * P) ≤ (Λ.stepParams.side : ℝ) ^ x * (D₂ * P) :=
      mul_le_mul_of_nonneg_right hxL (mul_nonneg hD₂0 hP0)
    have a3 : 0 ≤ (D₁ + D₂) * P * (Λ.stepParams.side : ℝ) ^ x := by positivity
    nlinarith
end YangMills.Construction.MomentLaw
end
