import YangMills.Construction.LawByMomentsOfTheFlow.ChainCumulantIsTheFreeOneProof
import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOfTheGaussianChainProof
import YangMills.Construction.LawByMomentsOfTheFlow.FluctuationsOfTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.ThirdDerivativesAndSizes
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps TorusContours TorusBlocks TorusCounting TorusPaths WeightedResponses ResponseInTheExpansion
  TopLevelSites StepCosts CompletedForms LevelTestFunctions TestFunctions BlockAverages
namespace StepGradients
section Gaussian
private def stdAbsMoment (k : ℕ) : ℝ := ∫ x, |x| ^ k ∂(gaussianReal 0 1)
private theorem stdAbsMoment_nonneg (k : ℕ) : 0 ≤ stdAbsMoment k :=
  integral_nonneg fun x => pow_nonneg (abs_nonneg x) k
private theorem integrable_abs_pow_gaussianReal (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have h : MemLp id (k : NNReal) (gaussianReal 0 v) := memLp_id_gaussianReal k
    have h2 := h.integrable_norm_pow (by exact_mod_cast hk.ne')
    simpa [Real.norm_eq_abs] using h2
private theorem integral_abs_pow_gaussianReal (v : NNReal) (k : ℕ) :
    ∫ x, |x| ^ k ∂(gaussianReal 0 v) = Real.sqrt v ^ k * stdAbsMoment k := by
  have hv : gaussianReal 0 v = (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  rw [hv, integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, mul_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul]
  rfl
variable {V : Type} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
private theorem moment_le_of_energy_bound {E : V → ℝ} {μ : Measure V} (hμ : IsCanonicalGaussian E μ) (f : V →ₗ[ℝ] ℝ)
    {A : ℝ} (hA : 0 ≤ A) (h₀ : ∀ x, E x = 0 → f x = 0) (h₁ : ∀ x, 0 < E x → f x ^ 2 ≤ A ^ 2 * E x) (k : ℕ) :
    AEMeasurable f μ ∧ Integrable (fun x => |f x| ^ k) μ ∧ ∫ x, |f x| ^ k ∂μ ≤ A ^ k * stdAbsMoment k := by
  have := hμ.isProbabilityMeasure
  have hlaw := hμ.map_eq f h₀
  have hae : AEMeasurable f μ := by
    by_contra hn
    rw [Measure.map_of_not_aemeasurable hn] at hlaw
    have h1 : (gaussianReal 0 (gaussianVariance E f).toNNReal) Set.univ = 1 := measure_univ
    rw [← hlaw] at h1
    simp at h1
  have hτ : ((gaussianVariance E f).toNNReal : ℝ) ≤ A ^ 2 := by
    rw [Real.coe_toNNReal']
    refine max_le (Real.sSup_le ?_ (sq_nonneg A)) (sq_nonneg A)
    rintro w ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hx]
    exact h₁ x hx
  have hmeas : AEStronglyMeasurable (fun y : ℝ => |y| ^ k) (μ.map f) :=
    (continuous_abs.pow k).aestronglyMeasurable
  refine ⟨hae, ?_, ?_⟩
  · have h2 : Integrable (fun y : ℝ => |y| ^ k) (μ.map f) := by
      rw [hlaw]
      exact integrable_abs_pow_gaussianReal _ k
    exact (integrable_map_measure hmeas hae).1 h2
  · have e : ∫ x, |f x| ^ k ∂μ = ∫ y, |y| ^ k ∂(μ.map f) := (integral_map hae hmeas).symm
    rw [e, hlaw, integral_abs_pow_gaussianReal]
    have h3 : Real.sqrt ((gaussianVariance E f).toNNReal : ℝ) ≤ A := Real.sqrt_le_iff.2 ⟨hA, hτ⟩
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 k) (stdAbsMoment_nonneg k)
end Gaussian
section Chains
variable {L : ℕ} [NeZero L]
private theorem measurable_chainLower (s n : ℕ) :
    Measurable (chainLower (L := L) (s := s) (n := n)) := by apply _root_.YangMills.SharedProofs.p17945 <;> assumption
private theorem measurable_chainTop : ∀ (s n : ℕ), Measurable (chainTop (L := L) s n)
  | 0, _ => measurable_id
  | s + 1, n => measurable_pi_iff.2 fun e => measurable_pi_iff.2 fun b =>
    (measurable_pi_apply (Sum.inr b : LevelBond L s (n * L) ⊕ TorusBond n)).comp (measurable_pi_apply e)
private theorem measurable_levelPair : ∀ (d s n : ℕ) (h : d + 1 ≤ s), Measurable (levelPair (L := L) d s n h)
  | _, 0, _, h => absurd h (by omega)
  | 0, s + 1, n, _ => (measurable_chainTop (s + 1) n).prodMk ((measurable_chainTop s (n * L)).comp (measurable_chainLower s n))
  | d + 1, s + 1, n, h => (measurable_levelPair d s (n * L) (Nat.le_of_succ_le_succ h)).comp (measurable_chainLower s n)
private theorem chainTop_add : ∀ (s n : ℕ) (X Y : LevelChain L s n), chainTop s n (X + Y) = chainTop s n X + chainTop s n Y
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainTop_smul : ∀ (s n : ℕ) (r : ℝ) (X : LevelChain L s n), chainTop s n (r • X) = r • chainTop s n X
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem levelPair_add : ∀ (d s n : ℕ) (h : d + 1 ≤ s) (X Y : LevelChain L s n),
    levelPair d s n h (X + Y) = levelPair d s n h X + levelPair d s n h Y
  | _, 0, _, h, _, _ => absurd h (by omega)
  | 0, s + 1, n, _, X, Y => Prod.ext (chainTop_add (s + 1) n X Y) (chainTop_add s (n * L) (chainLower X) (chainLower Y))
  | d + 1, s + 1, n, h, X, Y => levelPair_add d s (n * L) (Nat.le_of_succ_le_succ h) (chainLower X) (chainLower Y)
private theorem levelPair_smul : ∀ (d s n : ℕ) (h : d + 1 ≤ s) (r : ℝ) (X : LevelChain L s n),
    levelPair d s n h (r • X) = r • levelPair d s n h X
  | _, 0, _, h, _, _ => absurd h (by omega)
  | 0, s + 1, n, _, r, X => Prod.ext (chainTop_smul (s + 1) n r X) (chainTop_smul s (n * L) r (chainLower X))
  | d + 1, s + 1, n, h, r, X => levelPair_smul d s (n * L) (Nat.le_of_succ_le_succ h) r (chainLower X)
private theorem levelEnergy_nonneg {a : ℝ} (ha : 0 ≤ a) :
    ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n), 0 ≤ levelEnergy a s n X := by apply _root_.YangMills.SharedProofs.p39411 <;> assumption
private theorem defect_sq_le_levelEnergy {a : ℝ} (ha : 0 ≤ a) :
    ∀ (d s n : ℕ) [NeZero n] (h : d + 1 ≤ s) (X : LevelChain L s n) (e : Fin 3) (c : TorusBond (fineSide L d n)),
    a * ((levelPair d s n h X).1 e c - _root_.YangMills.Construction.MomentLaw.contourAverage L ((levelPair d s n h X).2 e) c) ^ 2 ≤ levelEnergy a s n X := by
  intro d
  induction d with
  | zero =>
    intro s n _ h X e c
    cases s with
    | zero => omega
    | succ s =>
      show a * (chainDefect X e c) ^ 2 ≤ levelEnergy a s (n * L) (chainLower X) +
        a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2
      have h1 : chainDefect X e c ^ 2 ≤ ∑ e : Fin 3, chainDefect X e c ^ 2 :=
        Finset.single_le_sum (f := fun e => chainDefect X e c ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ e)
      have h2 : ∑ e : Fin 3, chainDefect X e c ^ 2 ≤ ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 :=
        Finset.single_le_sum (f := fun c => ∑ e : Fin 3, chainDefect X e c ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ c)
      have h3 := levelEnergy_nonneg (L := L) ha s (n * L) (chainLower X)
      have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) ha
      linarith
  | succ d ih =>
    intro s n _ h X e c
    cases s with
    | zero => omega
    | succ s =>
      have h1 := ih s (n * L) (Nat.le_of_succ_le_succ h) (chainLower X) e c
      have h2 : 0 ≤ a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 :=
        mul_nonneg ha (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      show _ ≤ levelEnergy a s (n * L) (chainLower X) + a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2
      exact h1.trans (by linarith)
private theorem levelPair_snd_heq (u : ℕ) : ∀ (j n : ℕ) (h : j + 1 ≤ u + (j + 1)) (X : LevelChain L (u + (j + 1)) n),
    HEq (levelPair j (u + (j + 1)) n h X).2 (chainTop u (fineSide L (j + 1) n) (chainDescend u (j + 1) n X)) := by
  intro j
  induction j with
  | zero => intro n h X; exact HEq.rfl
  | succ j ih => intro n h X; exact ih (n * L) (Nat.le_of_succ_le_succ h) (chainLower X)
end Chains
section Forms
variable {m : ℕ} [NeZero m]
private theorem bilinearEval_add_left (q : BondBilinear m) (A A' B : TorusBond m → ℝ) :
    bilinearEval q (A + A') B = bilinearEval q A B + bilinearEval q A' B := by
  simp only [bilinearEval, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem bilinearEval_add_right (q : BondBilinear m) (A B B' : TorusBond m → ℝ) :
    bilinearEval q A (B + B') = bilinearEval q A B + bilinearEval q A B' := by
  simp only [bilinearEval, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem bilinearEval_smul_left (q : BondBilinear m) (r : ℝ) (A B : TorusBond m → ℝ) :
    bilinearEval q (r • A) B = r * bilinearEval q A B := by
  simp only [bilinearEval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem bilinearEval_smul_right (q : BondBilinear m) (r : ℝ) (A B : TorusBond m → ℝ) :
    bilinearEval q A (r • B) = r * bilinearEval q A B := by
  simp only [bilinearEval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem colourEval_add_left (q : BondBilinear m) (X X' Y : ColourForm m) :
    colourEval q (X + X') Y = colourEval q X Y + colourEval q X' Y := by
  simp only [colourEval]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => bilinearEval_add_left q _ _ _
private theorem colourEval_add_right (q : BondBilinear m) (X Y Y' : ColourForm m) :
    colourEval q X (Y + Y') = colourEval q X Y + colourEval q X Y' := by
  simp only [colourEval]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => bilinearEval_add_right q _ _ _
private theorem colourEval_smul_left (q : BondBilinear m) (r : ℝ) (X Y : ColourForm m) :
    colourEval q (r • X) Y = r * colourEval q X Y := by
  simp only [colourEval]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => bilinearEval_smul_left q _ _ _
private theorem colourEval_smul_right (q : BondBilinear m) (r : ℝ) (X Y : ColourForm m) :
    colourEval q X (r • Y) = r * colourEval q X Y := by
  simp only [colourEval]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => bilinearEval_smul_right q _ _ _
private theorem bilinearEval_sum {α : Type} (s : Finset α) (q : α → BondBilinear m) (A B : TorusBond m → ℝ) :
    bilinearEval (fun b b' => ∑ y ∈ s, q y b b') A B = ∑ y ∈ s, bilinearEval (q y) A B := by apply _root_.YangMills.SharedProofs.p776 <;> assumption
private theorem colourEval_sum {α : Type} (s : Finset α) (q : α → BondBilinear m) (X Y : ColourForm m) :
    colourEval (fun b b' => ∑ y ∈ s, q y b b') X Y = ∑ y ∈ s, ∑ e : Fin 3, bilinearEval (q y) (X e) (Y e) := by
  unfold colourEval
  simp only [bilinearEval_sum]
  exact Finset.sum_comm
private theorem abs_curl_le_of_local {A : TorusBond m → ℝ} {x : TorusSite m} (h₁ : ∀ c, |A c| ≤ 1)
    (h₂ : ∀ c, A c ≠ 0 → c.1 = x) (p : TorusPlaquette m) :
    |curl A p| ≤ if TorusFields.supDist p.1 x ≤ 1 then 4 else 0 := by
  split_ifs with h
  · unfold curl
    have a1 := abs_le.1 (h₁ (p.1, p.2.1))
    have a2 := abs_le.1 (h₁ (p.1 + TorusFields.unitStep m p.2.1, p.2.2))
    have a3 := abs_le.1 (h₁ (p.1 + TorusFields.unitStep m p.2.2, p.2.1))
    have a4 := abs_le.1 (h₁ (p.1, p.2.2))
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  · have z : ∀ c : TorusBond m, TorusFields.supDist p.1 c.1 ≤ 1 → A c = 0 := by
      intro c hc
      by_contra hA
      exact h (h₂ c hA ▸ hc)
    have h0 : TorusFields.supDist p.1 p.1 ≤ 1 := by simp [TorusFields.supDist_self]
    unfold curl
    rw [z (p.1, p.2.1) h0, z (p.1 + TorusFields.unitStep m p.2.1, p.2.2) (TorusFields.supDist_add_unitStep_le _ _),
      z (p.1 + TorusFields.unitStep m p.2.2, p.2.1) (TorusFields.supDist_add_unitStep_le _ _), z (p.1, p.2.2) h0]
    simp
private theorem abs_term_le {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (k a b : ℝ) (D dp dq dx : ℕ) (ha : |a| ≤ R)
    (hb : |b| ≤ if D ≤ 1 then 4 else 0) (hD : dx ≤ D + dq) :
    |k * a * b| ≤ |k| * Real.exp (ρ * ((dp : ℝ) + (dq : ℝ))) * (4 * R * Real.exp ρ * Real.exp (-(ρ * (dx : ℝ)))) := by
  rw [abs_mul, abs_mul]
  have hE0 : 0 ≤ |k| * Real.exp (ρ * ((dp : ℝ) + (dq : ℝ))) * (4 * R * Real.exp ρ * Real.exp (-(ρ * (dx : ℝ)))) := by
    positivity
  split_ifs at hb with h
  · have hexp : 1 ≤ Real.exp (ρ * ((dp : ℝ) + (dq : ℝ))) * (Real.exp ρ * Real.exp (-(ρ * (dx : ℝ)))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.one_le_exp ?_
      have h1 : (dx : ℝ) ≤ 1 + dq := by
        have : dx ≤ 1 + dq := by omega
        exact_mod_cast this
      have h2 : (0 : ℝ) ≤ dp := Nat.cast_nonneg _
      nlinarith
    calc |k| * |a| * |b| ≤ |k| * R * 4 := by
          have := mul_le_mul ha hb (abs_nonneg _) hR
          nlinarith [abs_nonneg k]
      _ = |k| * (4 * R) * 1 := by ring
      _ ≤ |k| * (4 * R) * (Real.exp (ρ * ((dp : ℝ) + (dq : ℝ))) * (Real.exp ρ * Real.exp (-(ρ * (dx : ℝ))))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  · have hb0 : b = 0 := abs_nonpos_iff.1 hb
    simp only [hb0, abs_zero, mul_zero]
    exact hE0
private theorem abs_bilinearEval_le {q : BondBilinear m} {κ : TorusPlaquette m → TorusPlaquette m → ℝ} {y x : TorusSite m}
    {ρ Cz R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hκ : ∀ A A' : TorusBond m → ℝ, bilinearEval q A A' = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), κ p p' * curl A p * curl A' p')
    (hs : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
      |κ p p'| * Real.exp (ρ * ((TorusFields.supDist p.1 y : ℝ) + (TorusFields.supDist p'.1 y : ℝ))) ≤ Cz)
    {A B : TorusBond m → ℝ} (hA : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), |curl A p| ≤ R)
    (hB₁ : ∀ c, |B c| ≤ 1) (hB₂ : ∀ c, B c ≠ 0 → c.1 = x) :
    |bilinearEval q A B| ≤ 4 * R * Cz * Real.exp ρ * Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) ∧
      |bilinearEval q B A| ≤ 4 * R * Cz * Real.exp ρ * Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) := by
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 4 * R * Real.exp ρ * Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have htri : ∀ z : TorusSite m, TorusFields.supDist x y ≤ TorusFields.supDist z x + TorusFields.supDist z y := fun z => by
    have := TorusFields.supDist_triangle x z y
    rw [TorusFields.supDist_comm x z] at this
    exact this
  have e : 4 * R * Cz * Real.exp ρ * Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) = Cz * T := by rw [hT]; ring
  rw [e]
  constructor
  · rw [hκ]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hs hT0)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p' _ => ?_
    rw [hT]
    exact abs_term_le hρ hR _ _ _ (TorusFields.supDist p'.1 x) _ _ _ (hA p hp) (abs_curl_le_of_local hB₁ hB₂ p') (htri p'.1)
  · rw [hκ]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hs hT0)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p' hp' => ?_
    have h1 := abs_term_le hρ hR (κ p p') (curl A p') (curl B p) (TorusFields.supDist p.1 x) (TorusFields.supDist p'.1 y)
      (TorusFields.supDist p.1 y) (TorusFields.supDist x y) (hA p' hp') (abs_curl_le_of_local hB₁ hB₂ p) (htri p.1)
    have e1 : κ p p' * curl B p * curl A p' = κ p p' * curl A p' * curl B p := by ring
    rw [e1, hT, add_comm (TorusFields.supDist p.1 y : ℝ)]
    exact h1
private theorem abs_formPart_le (s : Finset (TorusSite m)) (q : TorusSite m → BondBilinear m) {x : TorusSite m}
    {ρ Cz R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hκ : ∀ y ∈ s, ∃ κ : TorusPlaquette m → TorusPlaquette m → ℝ,
      (∀ A A' : TorusBond m → ℝ, bilinearEval (q y) A A' = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), κ p p' * curl A p * curl A' p') ∧
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
        |κ p p'| * Real.exp (ρ * ((TorusFields.supDist p.1 y : ℝ) + (TorusFields.supDist p'.1 y : ℝ))) ≤ Cz)
    {Y B : ColourForm m} (hY : ∀ e, ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), |curl (Y e) p| ≤ R)
    (hB₁ : ∀ e c, |B e c| ≤ 1) (hB₂ : ∀ e c, B e c ≠ 0 → c.1 = x) :
    |(1 / 2) * (colourEval (fun b b' => ∑ y ∈ s, q y b b') Y B + colourEval (fun b b' => ∑ y ∈ s, q y b b') B Y)| ≤
      12 * R * Cz * Real.exp ρ * ∑ y ∈ s, Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) := by
  have hone : ∀ y ∈ s, ∀ e : Fin 3,
      |bilinearEval (q y) (Y e) (B e)| ≤ 4 * R * Cz * Real.exp ρ * Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) ∧
      |bilinearEval (q y) (B e) (Y e)| ≤ 4 * R * Cz * Real.exp ρ * Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) :=
    fun y hy e => by
      obtain ⟨κ, h1, h2⟩ := hκ y hy
      exact abs_bilinearEval_le hρ hR h1 h2 (hY e) (hB₁ e) (hB₂ e)
  have hsum : ∀ G : TorusSite m → Fin 3 → ℝ,
      (∀ y ∈ s, ∀ e, |G y e| ≤ 4 * R * Cz * Real.exp ρ * Real.exp (-(ρ * (TorusFields.supDist x y : ℝ)))) →
      |∑ y ∈ s, ∑ e : Fin 3, G y e| ≤ 12 * R * Cz * Real.exp ρ * ∑ y ∈ s, Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) := by
    intro G hG
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun e _ => hG y hy e).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    exact le_of_eq (by ring)
  have h1 := hsum _ fun y hy e => (hone y hy e).1
  have h2 := hsum _ fun y hy e => (hone y hy e).2
  rw [colourEval_sum, colourEval_sum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h3 := abs_add_le (∑ y ∈ s, ∑ e : Fin 3, bilinearEval (q y) (Y e) (B e))
    (∑ y ∈ s, ∑ e : Fin 3, bilinearEval (q y) (B e) (Y e))
  linarith
end Forms
section Lift
variable {L : ℕ} [NeZero L] {u n : ℕ} [NeZero n]
private theorem torusFrame_period (i : Fin 4) : (torusFrame L u n).period (torusFrame L u n).depth i = n * L := by
  simp [BlockFrame.period, torusFrame]
private def chartBond (β : ChartBondIndex L u n) : TorusBond (n * L) := (toTorusSite (n * L) β.1.1, β.1.2)
private theorem chart_eq_iff (β : ChartBondIndex L u n) (c : TorusBond (n * L)) :
    (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1, c.2) = β.1 ↔ c = chartBond β := by
  constructor
  · intro h
    have h1 : torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1 = β.1.1 := congrArg Prod.fst h
    have h2 : c.2 = β.1.2 := congrArg Prod.snd h
    refine Prod.ext ?_ h2
    show c.1 = toTorusSite (n * L) β.1.1
    rw [← h1, toTorusSite_torusSiteInFrame torusFrame_period]
  · rintro rfl
    exact Prod.ext (torusSiteInFrame_toTorusSite torusFrame_period β.1.1) rfl
private theorem chartBond_injective : Function.Injective (chartBond (L := L) (u := u) (n := n)) := by
  intro β β' h
  have h1 : toTorusSite (n * L) β.1.1 = toTorusSite (n * L) β'.1.1 :=
    congrArg (Prod.fst : TorusBond (n * L) → TorusSite (n * L)) h
  have h2 : β.1.2 = β'.1.2 := congrArg (Prod.snd : TorusBond (n * L) → Fin 4) h
  exact Subtype.ext (Prod.ext (toTorusSite_injective torusFrame_period h1) h2)
open Classical in
private theorem extendFluctuation_single [DecidableEq (Fin 3 × ChartBondIndex L u n)] (b : Fin 3 × ChartBondIndex L u n)
    (e : Fin 3) (c : TorusBond (n * L)) :
    extendFluctuation (EuclideanSpace.single b (1 : ℝ)) e c = if e = b.1 ∧ c = chartBond b.2 then 1 else 0 := by
  simp only [extendFluctuation, extendChart, chart_eq_iff]
  rw [Finset.sum_eq_single b.2]
  · by_cases h : e = b.1 ∧ c = chartBond b.2
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h]
      by_cases hc : c = chartBond b.2
      · have he : e ≠ b.1 := fun he => h ⟨he, hc⟩
        rw [if_pos hc]
        simp [Prod.ext_iff, he]
      · rw [if_neg hc]
  · intro β _ hβ
    split_ifs
    · simp [Prod.ext_iff, hβ]
    · rfl
  · simp
end Lift
section Contours
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
private theorem sumAlongWord_cons {m : ℕ} (A : TorusBond m → ℝ) (x : TorusBond m × Bool) (w : BondWord m) :
    sumAlongWord A (x :: w) = (if x.2 then A x.1 else -A x.1) + sumAlongWord A w := by
  simp [sumAlongWord]
private theorem sumAlongWord_add {m : ℕ} (A A' : TorusBond m → ℝ) (w : BondWord m) :
    sumAlongWord (A + A') w = sumAlongWord A w + sumAlongWord A' w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
private theorem contourAverage_add (A A' : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (A + A') c = _root_.YangMills.Construction.MomentLaw.contourAverage L A c + _root_.YangMills.Construction.MomentLaw.contourAverage L A' c := by
  simp only [_root_.YangMills.Construction.MomentLaw.contourAverage, sumAlongWord_add, Finset.sum_add_distrib, mul_add]
private theorem contourAverage_smul (r : ℝ) (A : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (r • A) c = r * _root_.YangMills.Construction.MomentLaw.contourAverage L A c := by apply _root_.YangMills.SharedProofs.p14469 <;> assumption
private theorem abs_sumAlongWord_le {m : ℕ} {A : TorusBond m → ℝ} (h : ∀ c, |A c| ≤ 1) (w : BondWord m) :
    |sumAlongWord A w| ≤ w.length := by
  induction w with
  | nil => simp [sumAlongWord]
  | cons x r ih =>
    rw [sumAlongWord_cons]
    have h1 : |if x.2 = true then A x.1 else -A x.1| ≤ 1 := by
      split_ifs
      · exact h _
      · rw [abs_neg]
        exact h _
    simp only [List.length_cons]
    push_cast
    exact (abs_add_le _ _).trans (by linarith)
private theorem sumAlongWord_eq_zero {m : ℕ} {A : TorusBond m → ℝ} (w : BondWord m) (h : ∀ e ∈ w, A e.1 = 0) :
    sumAlongWord A w = 0 := by
  induction w with
  | nil => simp [sumAlongWord]
  | cons x r ih =>
    rw [sumAlongWord_cons, ih fun e he => h e (List.mem_cons_of_mem _ he), h x List.mem_cons_self]
    simp
private theorem contourAverage_local (hL : Odd L) {A : TorusBond (n * L) → ℝ} {x : TorusSite (n * L)}
    (h₁ : ∀ c, |A c| ≤ 1) (h₂ : ∀ c, A c ≠ 0 → c.1 = x) (c : TorusBond n) :
    |_root_.YangMills.Construction.MomentLaw.contourAverage L A c| ≤ 5 * L ∧
      (_root_.YangMills.Construction.MomentLaw.contourAverage L A c ≠ 0 → TorusFields.supDist (blockCentreSite L c.1) x ≤ 5 * L) := by
  constructor
  · unfold _root_.YangMills.Construction.MomentLaw.contourAverage
    rw [abs_mul, abs_of_nonneg (contourWeight_nonneg L)]
    have h3 : |∑ e ∈ contourIndex L, sumAlongWord A (contourWord L c.1 c.2 e)| ≤
        (contourIndex L).card * (5 * (L : ℝ)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun e he => (abs_sumAlongWord_le h₁ _).trans ?_
      exact_mod_cast length_contourWord_le hL c.1 c.2 he
    calc _ ≤ contourWeight L * ((contourIndex L).card * (5 * (L : ℝ))) :=
          mul_le_mul_of_nonneg_left h3 (contourWeight_nonneg L)
      _ = (contourWeight L * (contourIndex L).card) * (5 * (L : ℝ)) := by ring
      _ = 5 * L := by rw [contourWeight_mul_card hL, one_mul]
  · intro hne
    by_contra hfar
    refine hne ?_
    unfold _root_.YangMills.Construction.MomentLaw.contourAverage
    rw [Finset.sum_eq_zero, mul_zero]
    intro e he
    refine sumAlongWord_eq_zero _ fun b hb => ?_
    by_contra hA
    have h3 := _root_.YangMills.Construction.TorusContours.supDist_le_length_of_mem_pathToWord _ _ hb
    have h4 : (bondContour L e.1 e.2 c.2).length ≤ 5 * L := by
      have := length_contourWord_le hL c.1 c.2 he
      rwa [contourWord, length_pathToWord] at this
    exact hfar ((h₂ _ hA) ▸ h3.trans h4)
private theorem abs_fluctuationPart_le (hL : Odd L) {hh : TorusBond n → ℝ} (h₁ : ∀ c, |hh c| ≤ 1)
    (s : Finset (TorusSite (n * L))) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : TorusSite (n * L)} {B : ColourForm (n * L)} (hB₁ : ∀ e c, |B e c| ≤ 1) (hB₂ : ∀ e c, B e c ≠ 0 → c.1 = x)
    (hy : ∀ c : TorusBond n, hh c ≠ 0 →
      ∃ y ∈ s, parentBlock L y = c.1 ∨ parentBlock L y = c.1 + TorusFields.unitStep n c.2)
    (ν : ColourForm n) {V : ℝ} (hν : ∀ e c, |ν e c| ≤ V) :
    |∑ c : TorusBond n, hh c * ∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c| ≤
      V * (4 * 13 ^ 4 * (15 * L * Real.exp (8 * L * ρ))) * ∑ y ∈ s, Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) := by
  classical
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hV : 0 ≤ V := (abs_nonneg _).trans (hν 0 0)
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ y ∈ s, Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  rw [← hW]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = V * (15 * L * Real.exp (8 * L * ρ)) * W := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hterm : ∀ c : TorusBond n, |hh c * ∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c| ≤ K ∧
      (c.1 ∉ thickening 6 {parentBlock L x} → hh c * ∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c = 0) := by
    intro c
    by_cases hc : hh c ≠ 0 ∧ ∃ e, _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c ≠ 0
    · obtain ⟨hc1, e₀, he₀⟩ := hc
      have hnear := (contourAverage_local hL (hB₁ e₀) (hB₂ e₀) c).2 he₀
      have hb1 : TorusFields.supDist (parentBlock L x) c.1 ≤ 6 := by
        have h3 := _root_.YangMills.Construction.TorusCounting.supDist_parentBlock_le (L := L) x (blockCentreSite L c.1)
        rw [parentBlock_blockCentreSite hL, TorusFields.supDist_comm x] at h3
        have h4 : TorusFields.supDist (blockCentreSite L c.1) x / L ≤ 5 := Nat.div_le_of_le_mul (by omega)
        omega
      obtain ⟨y, hys, hyb⟩ := hy c hc1
      have hb2 : TorusFields.supDist (parentBlock L x) (parentBlock L y) ≤ 7 := by
        rcases hyb with h | h
        · rw [h]
          omega
        · rw [h]
          have h3 := TorusFields.supDist_triangle (parentBlock L x) c.1 (c.1 + TorusFields.unitStep n c.2)
          have h4 := TorusFields.supDist_add_unitStep_le c.1 c.2
          omega
      have hxy : TorusFields.supDist x y ≤ 8 * L := by
        have h3 := _root_.YangMills.Construction.TorusBlocks.supDist_le_mul_supDist_parentBlock_add_one hL x y
        calc TorusFields.supDist x y ≤ L * (TorusFields.supDist (parentBlock L x) (parentBlock L y) + 1) := h3
          _ ≤ L * (7 + 1) := Nat.mul_le_mul_left _ (by omega)
          _ = 8 * L := by ring
      have hG : 1 ≤ Real.exp (8 * L * ρ) * W := by
        have h3 : Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) ≤ W := by
          rw [hW]
          exact Finset.single_le_sum (f := fun y => Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))))
            (fun _ _ => (Real.exp_pos _).le) hys
        have h4 : 1 ≤ Real.exp (8 * L * ρ) * Real.exp (-(ρ * (TorusFields.supDist x y : ℝ))) := by
          rw [← Real.exp_add]
          refine Real.one_le_exp ?_
          have h5 : (TorusFields.supDist x y : ℝ) ≤ 8 * L := by exact_mod_cast hxy
          nlinarith
        exact h4.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)
      have hS : |∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c| ≤ V * (15 * L) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have h3 : ∀ e : Fin 3, |ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c| ≤ V * (5 * L) := fun e => by
          rw [abs_mul]
          exact mul_le_mul (hν e c) (contourAverage_local hL (hB₁ e) (hB₂ e) c).1 (abs_nonneg _) hV
        refine (Finset.sum_le_sum fun e _ => h3 e).trans ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        exact le_of_eq (by ring)
      constructor
      · rw [abs_mul, hK]
        calc |hh c| * |∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c| ≤ 1 * (V * (15 * L)) :=
              mul_le_mul (h₁ c) hS (abs_nonneg _) zero_le_one
          _ = V * (15 * L) * 1 := by ring
          _ ≤ V * (15 * L) * (Real.exp (8 * L * ρ) * W) := mul_le_mul_of_nonneg_left hG (by positivity)
          _ = _ := by ring
      · intro hnot
        exact absurd ((mem_thickening _ _ _).2 ⟨parentBlock L x, by simp, by rw [TorusFields.supDist_comm]; exact hb1⟩) hnot
    · have hz : hh c * ∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c = 0 := by
        by_cases h0 : hh c = 0
        · rw [h0, zero_mul]
        · have h3 : ∀ e, _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c = 0 := fun e => by
            by_contra h4
            exact hc ⟨h0, e, h4⟩
          simp [h3]
      rw [hz]
      exact ⟨by simpa using hK0, fun _ => rfl⟩
  have hcard : ((thickening 6 {parentBlock L x} : Finset (TorusSite n)).card : ℝ) ≤ 13 ^ 4 := by
    have h3 := card_thickening_singleton_le 6 (parentBlock L x)
    exact_mod_cast h3
  obtain ⟨P, hP⟩ : ∃ P : Finset (TorusBond n), P = (thickening 6 {parentBlock L x} : Finset (TorusSite n)) ×ˢ Finset.univ :=
    ⟨_, rfl⟩
  have hPc : (P.card : ℝ) ≤ 13 ^ 4 * 4 := by
    rw [hP, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    linarith
  calc |∑ c : TorusBond n, hh c * ∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c|
      ≤ ∑ c : TorusBond n, |hh c * ∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c ∈ P, |hh c * ∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c| := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_).symm
        have h3 : c.1 ∉ thickening 6 {parentBlock L x} := fun h4 =>
          hc (by rw [hP]; exact Finset.mem_product.2 ⟨h4, Finset.mem_univ _⟩)
        rw [(hterm c).2 h3, abs_zero]
    _ ≤ P.card * K := by
        rw [← nsmul_eq_mul]
        exact Finset.sum_le_card_nsmul _ _ _ fun c _ => (hterm c).1
    _ ≤ 13 ^ 4 * 4 * K := mul_le_mul_of_nonneg_right hPc hK0
    _ = _ := by rw [hK]; ring
end Contours
section Sums
variable {L : ℕ} [NeZero L] {u n : ℕ} [NeZero n]
private theorem sum_chartBond_le (f : TorusSite (n * L) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ β : ChartBondIndex L u n, f (chartBond β).1 ≤ 4 * ∑ x : TorusSite (n * L), f x := by
  classical
  have h1 : ∑ β : ChartBondIndex L u n, f (chartBond β).1 =
      ∑ c ∈ Finset.univ.image (chartBond (L := L) (u := u) (n := n)), f c.1 :=
    (Finset.sum_image (f := fun c : TorusBond (n * L) => f c.1) fun a _ b _ h => chartBond_injective h).symm
  rw [h1]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ => hf c.1).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  exact le_of_eq (Finset.sum_congr rfl fun _ _ => by push_cast; ring)
private theorem sum_kernel_le {ι : Type} [Fintype ι] {N : ℕ} [NeZero N] (pos : ι → TorusSite N)
    (hsum : ∀ f : TorusSite N → ℝ, (∀ x, 0 ≤ f x) → ∑ β, f (pos β) ≤ 4 * ∑ x, f x) {g : ι → ι → ℝ} {H c₂ ρ δ : ℝ}
    (hδ : 0 < δ) (h1 : 2 * δ ≤ ρ) (h2 : δ ≤ c₂) (hH : 0 ≤ H)
    (hg : ∀ β β', g β β' ≤ H * Real.exp (-(2 * c₂ * (TorusFields.supDist (pos β) (pos β') : ℝ)))) (y y' : TorusSite N) :
    ∑ β, ∑ β', Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ))) * g β β' *
        Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) ≤
      H * (4 * expSumOnInt (δ / 4) ^ 4) ^ 2 * Real.exp (-(δ * (TorusFields.supDist y y' : ℝ))) := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-(δ * (TorusFields.supDist y y' : ℝ))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hterm : ∀ β β', Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ))) * g β β' *
      Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) ≤
      H * E * (Real.exp (-(δ * (TorusFields.supDist (pos β) y : ℝ))) *
        Real.exp (-(δ * (TorusFields.supDist (pos β') y' : ℝ)))) := by
    intro β β'
    have hD : (TorusFields.supDist y y' : ℝ) ≤ (TorusFields.supDist (pos β) y : ℝ) +
        (TorusFields.supDist (pos β) (pos β') : ℝ) + (TorusFields.supDist (pos β') y' : ℝ) := by
      have t1 := TorusFields.supDist_triangle y (pos β) y'
      have t2 := TorusFields.supDist_triangle (pos β) (pos β') y'
      rw [TorusFields.supDist_comm y (pos β)] at t1
      have : TorusFields.supDist y y' ≤ TorusFields.supDist (pos β) y + TorusFields.supDist (pos β) (pos β') +
          TorusFields.supDist (pos β') y' := by omega
      exact_mod_cast this
    have n1 : (0 : ℝ) ≤ TorusFields.supDist (pos β) y := Nat.cast_nonneg _
    have n2 : (0 : ℝ) ≤ TorusFields.supDist (pos β) (pos β') := Nat.cast_nonneg _
    have n3 : (0 : ℝ) ≤ TorusFields.supDist (pos β') y' := Nat.cast_nonneg _
    calc Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ))) * g β β' *
          Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ)))
        ≤ Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ))) *
            (H * Real.exp (-(2 * c₂ * (TorusFields.supDist (pos β) (pos β') : ℝ)))) *
            Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hg β β') (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = H * Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ)) +
            -(2 * c₂ * (TorusFields.supDist (pos β) (pos β') : ℝ)) +
            -(ρ * (TorusFields.supDist (pos β') y' : ℝ))) := by
          rw [Real.exp_add, Real.exp_add]
          ring
      _ ≤ H * Real.exp (-(δ * (TorusFields.supDist y y' : ℝ)) + -(δ * (TorusFields.supDist (pos β) y : ℝ)) +
            -(δ * (TorusFields.supDist (pos β') y' : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hH
          nlinarith [mul_le_mul_of_nonneg_left hD hδ.le, mul_le_mul_of_nonneg_right h1 n1, mul_le_mul_of_nonneg_right h1 n3,
            mul_le_mul_of_nonneg_right h2 n2, mul_nonneg hδ.le n2]
      _ = _ := by
          rw [Real.exp_add, Real.exp_add, hE]
          ring
  have hS : ∀ z : TorusSite N, ∑ β, Real.exp (-(δ * (TorusFields.supDist (pos β) z : ℝ))) ≤
      4 * expSumOnInt (δ / 4) ^ 4 := fun z =>
    (hsum (fun x => Real.exp (-(δ * (TorusFields.supDist x z : ℝ)))) fun _ => (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (sum_exp_neg_supDist_le hδ z) (by norm_num))
  have hS0 : ∀ z : TorusSite N, 0 ≤ ∑ β, Real.exp (-(δ * (TorusFields.supDist (pos β) z : ℝ))) := fun z =>
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc _ ≤ ∑ β, ∑ β', H * E * (Real.exp (-(δ * (TorusFields.supDist (pos β) y : ℝ))) *
          Real.exp (-(δ * (TorusFields.supDist (pos β') y' : ℝ)))) :=
        Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun β' _ => hterm β β'
    _ = H * E * ((∑ β, Real.exp (-(δ * (TorusFields.supDist (pos β) y : ℝ)))) *
          ∑ β', Real.exp (-(δ * (TorusFields.supDist (pos β') y' : ℝ)))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]
    _ ≤ H * E * ((4 * expSumOnInt (δ / 4) ^ 4) * (4 * expSumOnInt (δ / 4) ^ 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hS y) (hS y') (hS0 y') ((hS0 y).trans (hS y))) (mul_nonneg hH hE0)
    _ = _ := by rw [hE]; ring
private theorem sum_weights_kernel_le {ι : Type} [Fintype ι] {N : ℕ} [NeZero N] (pos : ι → TorusSite N)
    (hsum : ∀ f : TorusSite N → ℝ, (∀ x, 0 ≤ f x) → ∑ β, f (pos β) ≤ 4 * ∑ x, f x) {g : ι → ι → ℝ} {H c₂ ρ δ Dm : ℝ}
    (hδ : 0 < δ) (h1 : 2 * δ ≤ ρ) (h2 : δ ≤ c₂) (hH : 0 ≤ H)
    (hg : ∀ β β', g β β' ≤ H * Real.exp (-(2 * c₂ * (TorusFields.supDist (pos β) (pos β') : ℝ))))
    (A A' : Finset (TorusSite N)) (hD : ∀ y ∈ A, ∀ y' ∈ A', Dm ≤ TorusFields.supDist y y') :
    ∑ β, ∑ β', (∑ y ∈ A, Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ)))) * g β β' *
        ∑ y' ∈ A', Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) ≤
      (A.card : ℝ) * A'.card * (H * (4 * expSumOnInt (δ / 4) ^ 4) ^ 2 * Real.exp (-(δ * Dm))) := by
  have e : ∑ β, ∑ β', (∑ y ∈ A, Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ)))) * g β β' *
        ∑ y' ∈ A', Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) =
      ∑ y ∈ A, ∑ y' ∈ A', ∑ β, ∑ β', Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ))) * g β β' *
        Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) := by
    have t : ∀ β β', (∑ y ∈ A, Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ)))) * g β β' *
          ∑ y' ∈ A', Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) =
        ∑ y ∈ A, ∑ y' ∈ A', Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ))) * g β β' *
          Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) := fun β β' => by
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
    simp only [t]
    refine (Finset.sum_congr rfl fun β _ => Finset.sum_comm).trans
      (Finset.sum_comm.trans (Finset.sum_congr rfl fun y _ => ?_))
    exact (Finset.sum_congr rfl fun β _ => Finset.sum_comm).trans Finset.sum_comm
  rw [e]
  have hb : ∀ y ∈ A, ∀ y' ∈ A', ∑ β, ∑ β', Real.exp (-(ρ * (TorusFields.supDist (pos β) y : ℝ))) * g β β' *
      Real.exp (-(ρ * (TorusFields.supDist (pos β') y' : ℝ))) ≤
      H * (4 * expSumOnInt (δ / 4) ^ 4) ^ 2 * Real.exp (-(δ * Dm)) := by
    intro y hy y' hy'
    refine (sum_kernel_le pos hsum hδ h1 h2 hH hg y y').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have := mul_le_mul_of_nonneg_left (hD y hy y' hy') hδ.le
    linarith
  calc _ ≤ ∑ y ∈ A, ∑ y' ∈ A', H * (4 * expSumOnInt (δ / 4) ^ 4) ^ 2 * Real.exp (-(δ * Dm)) :=
        Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun y' hy' => hb y hy y' hy'
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
end Sums
section BlockMeans
variable {L : ℕ} [NeZero L]
private theorem exists_plaquette_of_blockMean_ne_zero : ∀ (t n : ℕ) [NeZero n] (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)), blockMean L t n Y h ≠ 0 → ∃ p, IsPlaquetteAt L t Y p ∧ h p ≠ 0
  | 0, n, _, Y, h => fun hne => by
    have h1 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), vertexMultiplicity Y p * h p ≠ 0 :=
      right_ne_zero_of_mul hne
    obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have h2 := left_ne_zero_of_mul hpn
    have h3 : Y ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
      by_contra hc
      refine h2 ?_
      simp only [vertexMultiplicity]
      rw [List.count_eq_zero_of_not_mem hc]
      simp
    exact ⟨p, ⟨(Finset.mem_filter.1 hp).2.1, Y, h3, Finset.mem_singleton_self Y⟩, right_ne_zero_of_mul hpn⟩
  | t + 1, n, _, Y, h => fun hne => by
    have h1 : ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y h ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨y, hy, hyn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    obtain ⟨p, ⟨hp1, c, hc1, hc2⟩, hp2⟩ := exists_plaquette_of_blockMean_ne_zero t (n * L) y h hyn
    exact ⟨p, ⟨hp1, c, hc1, Finset.mem_biUnion.2 ⟨y, hy, hc2⟩⟩, hp2⟩
private theorem exists_child_of_blockMean_ne_zero (t n : ℕ) [NeZero n] (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide L (t + 1) n)) (hne : blockMean L (t + 1) n Y h ≠ 0) :
    ∃ y ∈ weightSupportSites L t (n * L) h, parentBlock L y = Y := by
  have h1 : ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y h ≠ 0 := right_ne_zero_of_mul hne
  obtain ⟨y, hy, hyn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨p, hp1, hp2⟩ := exists_plaquette_of_blockMean_ne_zero t (n * L) y h hyn
  refine ⟨y, ?_, by simpa [TorusLumps.sitesInBlocks] using hy⟩
  simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨p, hp1, hp2⟩
private theorem abs_blockMean_le : ∀ (t n : ℕ) [NeZero n] (Y : TorusSite n) (h : PlaquetteWeight (fineSide L t n)),
    (∀ p, |h p| ≤ 1) → |blockMean L t n Y h| ≤ blockMean L t n Y (constOneWeight _)
  | 0, n, _, Y, h => fun hb => by
    show |(1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), vertexMultiplicity Y p * h p| ≤
      (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), vertexMultiplicity Y p * 1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 24)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)) (by norm_num)
    have h0 : 0 ≤ vertexMultiplicity Y p := by simp [vertexMultiplicity]
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hb p) h0
  | t + 1, n, _, Y, h => fun hb => by
    show |((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y h| ≤
      ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y (constOneWeight _)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ 4)⁻¹)]
    exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun y _ => abs_blockMean_le t (n * L) y h hb)) (by positivity)
end BlockMeans
section Moment
variable {L : ℕ} [NeZero L]
private theorem moment_levelStepGradient_le {s top j u : ℕ} [NeZero top] (hj : j + 1 ≤ s) {a : ℝ} (ha : 1 ≤ a)
    {μ : Measure (LevelChain L s top)} (hμ : IsCanonicalGaussian (levelEnergy a s top) μ)
    (hK : IsCanonicalGaussian (kineticForm a L u) (μ.map fun X => (levelPair j s top hj X).2))
    {C : ℝ} (hC : ∀ (Y : ColourForm (fineSide L j top * L)) (e : Fin 3),
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L j top * L))),
        curl (Y e) p ^ 2 ≤ C * kineticForm a L u Y)
    (f₁ : ColourForm (fineSide L j top * L) →ₗ[ℝ] ℝ) (hh : TorusBond (fineSide L j top) → ℝ)
    (t : Fin 3 → TorusBond (fineSide L j top) → ℝ) {W₁ W₂ : ℝ} (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂)
    (h₁ : ∀ (Y : ColourForm (fineSide L j top * L)) (R : ℝ), 0 ≤ R →
      (∀ e, ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L j top * L))), |curl (Y e) p| ≤ R) →
        |f₁ Y| ≤ W₁ * R)
    (h₂ : ∀ (ν : ColourForm (fineSide L j top)) (V : ℝ), (∀ e c, |ν e c| ≤ V) →
      |∑ c : TorusBond (fineSide L j top), hh c * ∑ e : Fin 3, ν e c * t e c| ≤ V * W₂)
    (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun X => |f₁ (levelPair j s top hj X).2 - a * ∑ c : TorusBond (fineSide L j top), hh c * ∑ e : Fin 3,
      ((levelPair j s top hj X).1 e c - _root_.YangMills.Construction.MomentLaw.contourAverage L ((levelPair j s top hj X).2 e) c) * t e c| ^ k) μ ∧
    ∫ X, |f₁ (levelPair j s top hj X).2 - a * ∑ c : TorusBond (fineSide L j top), hh c * ∑ e : Fin 3,
      ((levelPair j s top hj X).1 e c - _root_.YangMills.Construction.MomentLaw.contourAverage L ((levelPair j s top hj X).2 e) c) * t e c| ^ k ∂μ ≤
      (4 * (1 + stdAbsMoment k) * (W₁ * (1 + |C|) + a * W₂)) ^ k := by
  have ha0 : 0 < a := by linarith
  obtain ⟨nu, hnu⟩ : ∃ nu : LevelChain L s top → ColourForm (fineSide L j top),
      nu = fun X e c => (levelPair j s top hj X).1 e c - _root_.YangMills.Construction.MomentLaw.contourAverage L ((levelPair j s top hj X).2 e) c := ⟨_, rfl⟩
  have nu_add : ∀ X Y, nu (X + Y) = nu X + nu Y := by
    intro X Y
    funext e c
    simp only [hnu, levelPair_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [contourAverage_add]
    ring
  have nu_smul : ∀ (r : ℝ) X, nu (r • X) = r • nu X := by
    intro r X
    funext e c
    simp only [hnu, levelPair_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [contourAverage_smul]
    ring
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : LevelChain L s top →ₗ[ℝ] ℝ,
      ∀ X, f₂ X = a * ∑ c : TorusBond (fineSide L j top), hh c * ∑ e : Fin 3, nu X e c * t e c := by
    refine ⟨{ toFun := fun X => a * ∑ c : TorusBond (fineSide L j top), hh c * ∑ e : Fin 3, nu X e c * t e c
              map_add' := fun X Y => ?_
              map_smul' := fun r X => ?_ }, fun _ => rfl⟩
    · rw [nu_add]
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
    · rw [nu_smul]
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring
  have hnuE : ∀ X e c, nu X e c ^ 2 ≤ levelEnergy a s top X := by
    intro X e c
    have h3 := defect_sq_le_levelEnergy (L := L) ha0.le j s top hj X e c
    have h4 : nu X e c ^ 2 ≤ a * nu X e c ^ 2 := le_mul_of_one_le_left (sq_nonneg _) ha
    rw [hnu]
    rw [hnu] at h4
    exact h4.trans h3
  have hA₁ : 0 ≤ W₁ * (1 + |C|) := by positivity
  have hA₂ : 0 ≤ a * W₂ := by positivity
  have k1a : ∀ Y : ColourForm (fineSide L j top * L), kineticForm a L u Y = 0 → f₁ Y = 0 := by
    intro Y hY
    have h3 : ∀ e, ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L j top * L))), |curl (Y e) p| ≤ 0 :=
      fun e p hp => by
        have h4 := hC Y e p hp
        rw [hY, mul_zero] at h4
        have h5 : curl (Y e) p = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 (sq_nonneg _))
        simp [h5]
    have h4 := h₁ Y 0 le_rfl h3
    rw [mul_zero] at h4
    exact abs_nonpos_iff.1 h4
  have k1b : ∀ Y : ColourForm (fineSide L j top * L), 0 < kineticForm a L u Y →
      f₁ Y ^ 2 ≤ (W₁ * (1 + |C|)) ^ 2 * kineticForm a L u Y := by
    intro Y hY
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (1 + |C|) * Real.sqrt (kineticForm a L u Y) := ⟨_, rfl⟩
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    have hR2 : R ^ 2 = (1 + |C|) ^ 2 * kineticForm a L u Y := by
      rw [hR, mul_pow, Real.sq_sqrt hY.le]
    have h3 : ∀ e, ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L j top * L))), |curl (Y e) p| ≤ R :=
      fun e p hp => by
        have h4 := hC Y e p hp
        refine abs_le_of_sq_le_sq ?_ hR0
        rw [hR2]
        refine h4.trans (mul_le_mul_of_nonneg_right ?_ hY.le)
        nlinarith [le_abs_self C, abs_nonneg C]
    have h4 := h₁ Y R hR0 h3
    have h5 : f₁ Y ^ 2 ≤ (W₁ * R) ^ 2 := sq_le_sq' (by linarith [(abs_le.1 h4).1]) (abs_le.1 h4).2
    refine h5.trans (le_of_eq ?_)
    rw [mul_pow, hR2]
    ring
  have k2a : ∀ X, levelEnergy a s top X = 0 → f₂ X = 0 := by
    intro X hX
    have h3 : ∀ e c, |nu X e c| ≤ 0 := fun e c => by
      have h4 := hnuE X e c
      rw [hX] at h4
      have h5 : nu X e c = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 (sq_nonneg _))
      simp [h5]
    have h4 := h₂ (nu X) 0 h3
    rw [zero_mul] at h4
    rw [hf₂, abs_nonpos_iff.1 h4, mul_zero]
  have k2b : ∀ X, 0 < levelEnergy a s top X → f₂ X ^ 2 ≤ (a * W₂) ^ 2 * levelEnergy a s top X := by
    intro X hX
    have hV : 0 ≤ Real.sqrt (levelEnergy a s top X) := Real.sqrt_nonneg _
    have h3 : ∀ e c, |nu X e c| ≤ Real.sqrt (levelEnergy a s top X) := fun e c =>
      Real.abs_le_sqrt (hnuE X e c)
    have h4 := h₂ (nu X) _ h3
    rw [hf₂, mul_pow]
    have h5 : (∑ c : TorusBond (fineSide L j top), hh c * ∑ e : Fin 3, nu X e c * t e c) ^ 2 ≤
        (Real.sqrt (levelEnergy a s top X) * W₂) ^ 2 := sq_le_sq' (by linarith [(abs_le.1 h4).1]) (abs_le.1 h4).2
    rw [mul_pow, Real.sq_sqrt hX.le] at h5
    calc a ^ 2 * _ ≤ a ^ 2 * (levelEnergy a s top X * W₂ ^ 2) := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring
  obtain ⟨ae₁, in₁, le₁⟩ := moment_le_of_energy_bound hK f₁ hA₁ k1a k1b k
  obtain ⟨ae₂, in₂, le₂⟩ := moment_le_of_energy_bound hμ f₂ hA₂ k2a k2b k
  have hp : Measurable fun X : LevelChain L s top => (levelPair j s top hj X).2 :=
    measurable_snd.comp (measurable_levelPair (L := L) j s top hj)
  have hs₁ : AEStronglyMeasurable (fun Y => |f₁ Y| ^ k) (μ.map fun X => (levelPair j s top hj X).2) :=
    in₁.aestronglyMeasurable
  have in₁' : Integrable (fun X => |f₁ (levelPair j s top hj X).2| ^ k) μ :=
    (integrable_map_measure hs₁ hp.aemeasurable).1 in₁
  have le₁' : ∫ X, |f₁ (levelPair j s top hj X).2| ^ k ∂μ ≤ (W₁ * (1 + |C|)) ^ k * stdAbsMoment k := by
    have e1 := integral_map hp.aemeasurable hs₁
    rw [e1] at le₁
    exact le₁
  have ae₁' : AEMeasurable (fun X => f₁ (levelPair j s top hj X).2) μ := ae₁.comp_aemeasurable hp.aemeasurable
  have eG : ∀ X, f₁ (levelPair j s top hj X).2 - a * ∑ c : TorusBond (fineSide L j top), hh c * ∑ e : Fin 3,
      ((levelPair j s top hj X).1 e c - _root_.YangMills.Construction.MomentLaw.contourAverage L ((levelPair j s top hj X).2 e) c) * t e c =
      f₁ (levelPair j s top hj X).2 - f₂ X := fun X => by rw [hf₂, hnu]
  simp only [eG]
  have hpt : ∀ X, |f₁ (levelPair j s top hj X).2 - f₂ X| ^ k ≤
      2 ^ k * (|f₁ (levelPair j s top hj X).2| ^ k + |f₂ X| ^ k) := by
    intro X
    obtain ⟨p, hp'⟩ : ∃ p : ℝ, p = f₁ (levelPair j s top hj X).2 := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = f₂ X := ⟨_, rfl⟩
    rw [← hp', ← hq]
    have h3 := abs_add_le p (-q)
    rw [abs_neg, ← sub_eq_add_neg] at h3
    have hpk : 0 ≤ |p| ^ k := by positivity
    have hqk : 0 ≤ |q| ^ k := by positivity
    rcases le_total |p| |q| with h | h
    · calc |p - q| ^ k ≤ (2 * |q|) ^ k := pow_le_pow_left₀ (abs_nonneg _) (by linarith) k
        _ = 2 ^ k * |q| ^ k := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · calc |p - q| ^ k ≤ (2 * |p|) ^ k := pow_le_pow_left₀ (abs_nonneg _) (by linarith) k
        _ = 2 ^ k * |p| ^ k := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsum := (in₁'.add in₂).const_mul ((2 : ℝ) ^ k)
  have hmeas : AEStronglyMeasurable (fun X => |f₁ (levelPair j s top hj X).2 - f₂ X| ^ k) μ :=
    (continuous_abs.pow k).comp_aestronglyMeasurable (ae₁'.sub ae₂).aestronglyMeasurable
  have hint : Integrable (fun X => |f₁ (levelPair j s top hj X).2 - f₂ X| ^ k) μ := by
    refine hsum.mono' hmeas (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt X
  refine ⟨hint, ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = W₁ * (1 + |C|) + a * W₂ := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = stdAbsMoment k := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact stdAbsMoment_nonneg k
  rw [← hM] at le₁' le₂
  rw [← hM, ← hT]
  have hk0 : k ≠ 0 := by omega
  have c1 : (2 : ℝ) ^ k * 2 ≤ 4 ^ k := by
    have h3 : (2 : ℝ) ≤ 2 ^ k := le_self_pow₀ (by norm_num) hk0
    have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    rw [h4]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have c2 : M ≤ (1 + M) ^ k := by
    have h3 : 1 + M ≤ (1 + M) ^ k := le_self_pow₀ (by linarith) hk0
    linarith
  have t1 : (W₁ * (1 + |C|)) ^ k ≤ T ^ k := pow_le_pow_left₀ hA₁ (by rw [hT]; linarith) k
  have t2 : (a * W₂) ^ k ≤ T ^ k := pow_le_pow_left₀ hA₂ (by rw [hT]; linarith) k
  have hTk : 0 ≤ T ^ k := by positivity
  calc ∫ X, |f₁ (levelPair j s top hj X).2 - f₂ X| ^ k ∂μ
      ≤ ∫ X, (2 : ℝ) ^ k * (|f₁ (levelPair j s top hj X).2| ^ k + |f₂ X| ^ k) ∂μ :=
        integral_mono hint hsum hpt
    _ = 2 ^ k * (∫ X, |f₁ (levelPair j s top hj X).2| ^ k ∂μ + ∫ X, |f₂ X| ^ k ∂μ) := by
        rw [integral_const_mul, integral_add in₁' in₂]
    _ ≤ 2 ^ k * (T ^ k * M + T ^ k * M) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (le₁'.trans ?_) (le₂.trans ?_)) (by positivity)
        · exact mul_le_mul_of_nonneg_right t1 hM0
        · exact mul_le_mul_of_nonneg_right t2 hM0
    _ = (2 ^ k * 2) * M * T ^ k := by ring
    _ ≤ 4 ^ k * (1 + M) ^ k * T ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul c1 c2 hM0 (by positivity)) hTk
    _ = _ := by rw [mul_pow, mul_pow]
end Moment
section Transport
variable {L : ℕ} [NeZero L]
private theorem isCanonicalGaussian_transport {a : ℝ} {u M M' : ℕ} [NeZero M] [NeZero M'] (h : M = M') {Ω : Type}
    [MeasurableSpace Ω] (μ : Measure Ω) {φ : Ω → ColourForm M} {φ' : Ω → ColourForm M'} (hφ : ∀ ω, HEq (φ ω) (φ' ω))
    (hc : IsCanonicalGaussian (kineticForm a L u) (μ.map φ)) : IsCanonicalGaussian (kineticForm a L u) (μ.map φ') := by
  subst h
  have e : φ = φ' := funext fun ω => eq_of_heq (hφ ω)
  subst e
  exact hc
private theorem curlNorm_bound_transport {a C : ℝ} {u M M' : ℕ} [NeZero M] [NeZero M'] (h : M = M')
    (hc : ∀ (X : ColourForm M) (p : OrientedPlaquette M), curlNorm X p.1 ^ 2 ≤ C * kineticForm a L u X) :
    ∀ (X : ColourForm M') (p : OrientedPlaquette M'), curlNorm X p.1 ^ 2 ≤ C * kineticForm a L u X := by
  subst h
  exact hc
private theorem curl_sq_le_curlNorm_sq {m : ℕ} [NeZero m] (X : ColourForm m) (e : Fin 3) (p : TorusPlaquette m) :
    curl (X e) p ^ 2 ≤ curlNorm X p ^ 2 := by
  unfold curlNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.single_le_sum (f := fun e => curl (X e) p ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ e)
open Classical in
private def unitExtension {u n : ℕ} [NeZero n] (b : Fin 3 × ChartBondIndex L u n) : ColourForm (n * L) :=
  extendFluctuation (EuclideanSpace.single b (1 : ℝ))
private theorem abs_unitExtension_le {u n : ℕ} [NeZero n] (b : Fin 3 × ChartBondIndex L u n) (e : Fin 3)
    (c : TorusBond (n * L)) : |unitExtension b e c| ≤ 1 := by
  classical
  unfold unitExtension
  rw [extendFluctuation_single]
  split_ifs <;> simp
private theorem unitExtension_site {u n : ℕ} [NeZero n] (b : Fin 3 × ChartBondIndex L u n) (e : Fin 3)
    (c : TorusBond (n * L)) (h : unitExtension b e c ≠ 0) : c.1 = (chartBond b.2).1 := by
  classical
  unfold unitExtension at h
  rw [extendFluctuation_single] at h
  by_cases h2 : e = b.1 ∧ c = chartBond b.2
  · rw [h2.2]
  · simp [h2] at h
private theorem sum_colours {ι : Type} [Fintype ι] (F : ι → ι → ℝ) :
    ∑ _e : Fin 3, ∑ β : ι, ∑ _e' : Fin 3, ∑ β' : ι, F β β' = 9 * ∑ β, ∑ β', F β β' := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  ring
end Transport
section Parameters
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_forAllPoints
    {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop} (h : ForAllPoints Q) :
    ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S := h
private theorem forAllParameters_mono {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q)
    (hq : ∀ Λ : MomentParameters, 2 ≤ Λ.k → 0 < Λ.d → Q Λ → Q' Λ) : ForAllParameters Q' := by apply _root_.YangMills.SharedProofs.p72371 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.stepParams.Admissible := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _ Kr _
  refine ⟨Tb.floorMin, fun y hy hret hbot g hg hgy k _ _ _ R d _ => ?_⟩
  exact hD.fits y hy
abbrev _root_.YangMills.SharedProofs.p7443 := @forAllParameters_admissible
private theorem admissible_of_supAdmissible {k : ℕ} (P : LevelData k) (L : ℕ) (R d : ℝ) (h : P.SupAdmissible L R d) :
    P.Admissible L (2 * R) d := by apply _root_.YangMills.SharedProofs.p11807 <;> assumption
end Parameters
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem tower_stage_depth (u : ℕ) : (S.tower.stage u).depth = u := by apply _root_.YangMills.SharedProofs.p98506 <;> assumption
private theorem abs_weight_le (i : Fin Λ.k) (m : ℕ) (p : TorusPlaquette m) : |S.weight i m p| ≤ 1 :=
  S.supAdmissible.isSupTestFamily.abs_le_one i _
private theorem levelStepGradient_eq (l m : ℕ) [NeZero m] (i : Fin Λ.k) (Z : ColourForm m)
    (X : ColourForm (m * Λ.stepParams.side)) (b : Fin 3 × ChartBondIndex Λ.stepParams.side l m) :
    S.levelStepGradient l m i Z X b = (1 / 2) * (colourEval (S.supportForm l (m * Λ.stepParams.side) i) X (unitExtension b) +
      colourEval (S.supportForm l (m * Λ.stepParams.side) i) (unitExtension b) X) -
    Λ.stepParams.coupling * ∑ c : TorusBond m, bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _) c * ∑ e : Fin 3,
      (Z e c - _root_.YangMills.Construction.MomentLaw.contourAverage Λ.stepParams.side (X e) c) * _root_.YangMills.Construction.MomentLaw.contourAverage Λ.stepParams.side (unitExtension b e) c := rfl
private theorem exists_child_of_bondBlockMean_ne_zero (u n : ℕ) [NeZero n] (i : Fin Λ.k) (c : TorusBond n)
    (hc : bondBlockMean Λ.stepParams.side (u + 1) n (S.weight i _) c ≠ 0) :
    ∃ y ∈ S.supportAt u (n * Λ.stepParams.side) i, parentBlock Λ.stepParams.side y = c.1 ∨
      parentBlock Λ.stepParams.side y = c.1 + TorusFields.unitStep n c.2 := by
  by_cases h1 : blockMean Λ.stepParams.side (u + 1) n c.1 (S.weight i _) = 0
  · have h2 : blockMean Λ.stepParams.side (u + 1) n (c.1 + TorusFields.unitStep n c.2) (S.weight i _) ≠ 0 := by
      intro h3
      refine hc ?_
      unfold bondBlockMean
      rw [h1, h3]
      simp
    obtain ⟨y, hy, hb⟩ := exists_child_of_blockMean_ne_zero u n _ _ h2
    exact ⟨y, hy, Or.inr hb⟩
  · obtain ⟨y, hy, hb⟩ := exists_child_of_blockMean_ne_zero u n _ _ h1
    exact ⟨y, hy, Or.inl hb⟩
end Point
end StepGradients
open StepGradients in
set_option maxHeartbeats 4000000 in
theorem stepGradientsDecoupled (h₁ : gaussianChainCoordinatesStatement) (h₂ : gaussianChainFluctuationsStatement)
    (h₃ : formsReadCurvatureStatement) (h₄ : classicalFormsAnnihilateClosedStatement) (h₅ : thirdDerivativeBoundsStatement)
    (h₆ : weightsSitesBelowScaleStatement) (h₇ : SupportSiteDistanceBounds)
    (h₈ : BlockMeanIsLinearAndLocal) : stepGradientsDecoupledStatement := by
  unfold stepGradientsDecoupledStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and (forAllParameters_and
    (forAllParameters_and (forAllParameters_of_forAllPoints h₁) (forAllParameters_of_forAllPoints h₂))
    (forAllParameters_and (forAllParameters_of_forAllPoints h₃) (forAllParameters_of_forAllPoints h₄)))
    (forAllParameters_and (forAllParameters_and (forAllParameters_of_forAllPoints h₅) (forAllParameters_of_forAllPoints h₆))
      forAllParameters_admissible)) fun Λ hk hd H => ?_
  obtain ⟨⟨⟨⟨C₁, _, _, _, _, f₁⟩, ⟨_, c₂, _, hc₂, _, f₂⟩⟩, ⟨⟨C₃, _, _, _, _, f₃⟩, ⟨_, _, _, _, _, f₄⟩⟩⟩,
    ⟨⟨⟨C₅, _, _, _, _, f₅⟩, ⟨C₆, _, _, _, _, f₆⟩⟩, hf⟩⟩ := H
  have hodd : Odd Λ.stepParams.side := hf.L_odd
  have ha : 1 ≤ Λ.stepParams.coupling := hf.a_ge
  have hLpos : 0 < Λ.stepParams.side := hodd.pos
  have hLr : (0 : ℝ) < (Λ.stepParams.side : ℝ) := by exact_mod_cast hLpos
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = Λ.stepParams.weightRate / 8 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρd]
    have : 0 < Λ.stepParams.weightRate := by
      unfold TorusLumps.StepParameters.weightRate
      have := hf.rt_pos
      positivity
    positivity
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = min (ρ / 2) c₂ := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδd]
    exact lt_min (by positivity) hc₂
  have hδ1 : 2 * δ ≤ ρ := by
    have : δ ≤ ρ / 2 := by rw [hδd]; exact min_le_left _ _
    linarith
  have hδ2 : δ ≤ c₂ := by rw [hδd]; exact min_le_right _ _
  obtain ⟨sz, hszd⟩ : ∃ sz : ℝ, sz = 1 + |C₅ 1| := ⟨_, rfl⟩
  have hsz : 0 < sz := by rw [hszd]; positivity
  obtain ⟨Cz, hCzd⟩ : ∃ Cz : ℝ, Cz = (1 + |C₃ 0|) * sz := ⟨_, rfl⟩
  have hCz : 0 ≤ Cz := by rw [hCzd]; positivity
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : ℝ, P₁ = 12 * Cz * Real.exp ρ := ⟨_, rfl⟩
  have hP₁0 : 0 ≤ P₁ := by rw [hP₁]; positivity
  obtain ⟨P₂, hP₂⟩ : ∃ P₂ : ℝ, P₂ = 4 * 13 ^ 4 * (15 * Λ.stepParams.side * Real.exp (8 * Λ.stepParams.side * ρ)) :=
    ⟨_, rfl⟩
  have hP₂0 : 0 ≤ P₂ := by rw [hP₂]; positivity
  obtain ⟨Cw, hCw⟩ : ∃ Cw : ℝ,
      Cw = 4 * (1 + stdAbsMoment Λ.k) * (P₁ * (1 + |C₁ 0|) + Λ.stepParams.coupling * P₂) := ⟨_, rfl⟩
  have hCw0 : 0 ≤ Cw := by
    have := stdAbsMoment_nonneg Λ.k
    have ha0 : 0 ≤ Λ.stepParams.coupling := by linarith
    rw [hCw]
    positivity
  obtain ⟨Hc, hHc⟩ : ∃ Hc : ℝ, Hc = |2 / Λ.table.lam| := ⟨_, rfl⟩
  have hHc0 : 0 ≤ Hc := by rw [hHc]; exact abs_nonneg _
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ,
      Kc = Cw ^ 2 * (9 * (C₆ 0 ^ 2 * (Hc * (4 * expSumOnInt (δ / 4) ^ 4) ^ 2 * Real.exp δ))) := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by
    have := expSumOnInt_nonneg (δ / 4)
    rw [hKc]
    positivity
  refine ⟨fun _ => Kc + 1, δ * Λ.d / 2, Λ.floor, by positivity, le_rfl, fun S s hs μ hμ j hj ht => ?_⟩
  generalize hu : s - j - 1 = u at ht ⊢
  obtain rfl : s = u + (j + 1) := by omega
  have hk1 : 1 ≤ Λ.k := by omega
  have hts : S.lastSeparated ≤ S.data.scaleLevel := by
    unfold MomentPoint.lastSeparated
    exact @Nat.findGreatest_le (S.data.SeparatedBelow Λ.stepParams S.β) (fun _ => Classical.propDecidable _)
      S.data.scaleLevel
  have hus : u ≤ S.data.scaleLevel := by omega
  have huK' : u ≤ S.data.windowLevel := by omega
  have hn₀ : Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side :=
    (Nat.le_mul_of_pos_left _ hLpos).trans S.side_le
  have hside : S.data.period Λ.stepParams.side ≤ fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) := by
    rw [fineSide_eq]
    exact Nat.le_mul_of_pos_right _ (pow_pos hLpos j)
  have hm64 : 64 ≤ fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) := by
    have := hf.n₀_ge
    omega
  have hnL : Λ.stepParams.n₀ ≤ fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side :=
    (hn₀.trans hside).trans (Nat.le_mul_of_pos_right _ hLpos)
  have hM : fineSide Λ.stepParams.side (j + 1) (S.data.period Λ.stepParams.side) =
      fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side := by
    rw [fineSide_eq, fineSide_eq, pow_succ]
    ring
  have hN : fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side = S.levelSide u := by
    rw [fineSide_eq]
    show _ = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u)
    have : S.data.windowLevel - u = j + 1 := by omega
    rw [this, pow_succ]
    ring
  have hlevel : (S.tower.stage u).depth = u := tower_stage_depth S u
  have hsize : ∀ i : Fin Λ.k, weightNorm Λ.stepParams.side (S.tower.stage u).depth
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))) ≤ 1 := by
    intro i
    rw [hlevel, hN]
    exact (f₆ S u hus i).1
  have hsize0 : ∀ i : Fin Λ.k, 0 ≤ weightNorm Λ.stepParams.side (S.tower.stage u).depth
      (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))) := fun i =>
    le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
  have hcard : ∀ (N' : ℕ) [NeZero N'], N' = S.levelSide u → ∀ i : Fin Λ.k,
      ((S.supportAt u N' i).card : ℝ) ≤ C₆ 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) := by
    intro N' _ hN' i
    subst hN'
    exact (f₆ S u hus i).2
  have hfits := admissible_of_supAdmissible S.data Λ.stepParams.side Λ.R Λ.d S.supAdmissible
  have hdist : ∀ (N' : ℕ) [NeZero N'], N' = S.levelSide u → ∀ i i' : Fin Λ.k, i ≠ i' →
      ∀ y ∈ S.supportAt u N' i, ∀ y' ∈ S.supportAt u N' i',
      Λ.d / 2 * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u) - 1 ≤ (TorusFields.supDist y y' : ℝ) := by
    intro N' _ hN' i i' hne y hy y' hy'
    subst hN'
    have h3 := (h₇ Λ.stepParams.side hodd Λ.k (2 * Λ.R) Λ.d hd S.data hfits u huK' i i' y hy y' hy').2 hne
    have h4 : ((S.data.scaleLevel : ℤ) - (u : ℤ)) = ((S.data.scaleLevel - u : ℕ) : ℤ) := by omega
    rw [h4, zpow_natCast] at h3
    linarith
  have hκ : ∀ (i : Fin Λ.k),
      ∀ y ∈ S.supportAt u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) i,
      ∃ κ : TorusPlaquette (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) →
          TorusPlaquette (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) → ℝ,
      (∀ A A' : TorusBond (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) → ℝ,
        bilinearEval (classicalQuadratic S.tower S.resp u _ (S.weight i _) y) A A' =
          ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite _)),
          ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite _)), κ p p' * curl A p * curl A' p') ∧
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite
          (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite
          (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))), |κ p p'| *
        Real.exp (ρ * ((TorusFields.supDist p.1 y : ℝ) + (TorusFields.supDist p'.1 y : ℝ))) ≤ Cz := by
    intro i y _
    have hfs : IsDecayingAbout Λ.stepParams sz y (classicalQuadratic S.tower S.resp u _ (S.weight i _) y) := by
      intro b b'
      refine ((f₅ S u huK' _ hnL y (S.weight i _)).2 b b').trans ?_
      refine div_le_div_of_nonneg_right ?_ (mul_pos (lt_max_of_lt_left one_pos) (Real.exp_pos _)).le
      have h3 := hsize i
      have h4 := hsize0 i
      rw [hszd]
      have h5 : |C₅ 1| * weightNorm Λ.stepParams.side (S.tower.stage u).depth
          (S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth
            (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))) ≤ |C₅ 1| * 1 :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      have h6 := mul_le_mul_of_nonneg_right (le_abs_self (C₅ 1)) h4
      linarith
    obtain ⟨κ, h4, h5⟩ := (f₃ S u huK' _ hN y sz _ hsz hfs).1 (f₄ S u huK' _ hnL y _).2.1
    refine ⟨κ, h4, ?_⟩
    rw [← hρd] at h5
    refine h5.trans ?_
    rw [hCzd]
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (C₃ 0), abs_nonneg (C₃ 0)]) hsz.le
  have hcan := ((f₁ S u (j + 1) hs).2 μ hμ).2.1
  have hK : IsCanonicalGaussian (kineticForm Λ.stepParams.coupling Λ.stepParams.side u)
      (μ.map fun X => (levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).2) :=
    isCanonicalGaussian_transport hM μ
      (fun X => (levelPair_snd_heq u j (S.data.period Λ.stepParams.side) hj X).symm) hcan
  have hC0 := curlNorm_bound_transport (L := Λ.stepParams.side) hM (f₁ S u (j + 1) hs).1
  have hC : ∀ (Y : ColourForm (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))
      (e : Fin 3), ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))),
      curl (Y e) p ^ 2 ≤ C₁ 0 * kineticForm Λ.stepParams.coupling Λ.stepParams.side u Y := fun Y e p hp =>
    (curl_sq_le_curlNorm_sq Y e p).trans (hC0 Y ⟨p, (Finset.mem_filter.1 hp).2.1⟩)
  have hhb : ∀ (i : Fin Λ.k) (c : TorusBond (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))),
      |bondBlockMean Λ.stepParams.side (u + 1) (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))
        (S.weight i _) c| ≤ 1 := by
    intro i c
    have hone : ∀ Y : TorusSite (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)),
        |blockMean Λ.stepParams.side (u + 1) (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) Y
          (S.weight i _)| ≤ 1 := fun Y => by
      have h3 := abs_blockMean_le (L := Λ.stepParams.side) (u + 1)
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) Y (S.weight i _) (abs_weight_le S i _)
      rwa [(h₈ Λ.stepParams.side hodd (u + 1) (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) Y).1]
        at h3
    unfold bondBlockMean
    have a1 := abs_le.1 (hone c.1)
    have a2 := abs_le.1 (hone (c.1 + TorusFields.unitStep _ c.2))
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  obtain ⟨W, hWd⟩ : ∃ W : Fin Λ.k → ChartBondIndex Λ.stepParams.side u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) → ℝ, ∀ i β, W i β =
      ∑ y ∈ S.supportAt u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) i,
        Real.exp (-(ρ * (TorusFields.supDist (chartBond β).1 y : ℝ))) := ⟨fun i β => _, fun _ _ => rfl⟩
  have hW0 : ∀ i β, 0 ≤ W i β := fun i β => by
    rw [hWd]
    exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hmom : ∀ (i : Fin Λ.k)
      (b : Fin 3 × ChartBondIndex Λ.stepParams.side u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))),
      Integrable (fun X => |S.levelStepGradient u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) i
        (levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).1
        (levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).2 b| ^ Λ.k) μ ∧
      ∫ X, |S.levelStepGradient u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) i
        (levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).1
        (levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).2 b| ^ Λ.k ∂μ ≤ (Cw * W i b.2) ^ Λ.k := by
    intro i b
    obtain ⟨f, hfd⟩ : ∃ f : ColourForm (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) *
        Λ.stepParams.side) →ₗ[ℝ] ℝ, ∀ Y, f Y = (1 / 2) * (colourEval (S.supportForm u
          (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) i) Y (unitExtension b) +
        colourEval (S.supportForm u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) *
          Λ.stepParams.side) i) (unitExtension b) Y) :=
      ⟨{ toFun := fun Y => (1 / 2) * (colourEval (S.supportForm u
            (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) i) Y (unitExtension b) +
            colourEval (S.supportForm u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) *
              Λ.stepParams.side) i) (unitExtension b) Y)
         map_add' := fun Y Y' => by
          simp only [colourEval_add_left, colourEval_add_right]
          ring
         map_smul' := fun r Y => by
          simp only [colourEval_smul_left, colourEval_smul_right, smul_eq_mul, RingHom.id_apply]
          ring }, fun _ => rfl⟩
    have A₁ : ∀ (Y : ColourForm (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))
        (R : ℝ), 0 ≤ R →
        (∀ e, ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite
          (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side))), |curl (Y e) p| ≤ R) →
        |f Y| ≤ P₁ * W i b.2 * R := by
      intro Y R hR hY
      rw [hfd]
      have h3 : |(1 / 2) * (colourEval (S.supportForm u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) *
          Λ.stepParams.side) i) Y (unitExtension b) + colourEval (S.supportForm u
          (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) i) (unitExtension b) Y)| ≤
          _ :=
        abs_formPart_le (S.supportAt u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) *
            Λ.stepParams.side) i)
          (fun y => classicalQuadratic S.tower S.resp u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) *
            Λ.stepParams.side) (S.weight i _) y) hρ.le hR (hκ i) hY
          (fun e c => abs_unitExtension_le b e c) (fun e c h => unitExtension_site b e c h)
      refine h3.trans (le_of_eq ?_)
      rw [hP₁, hWd]
      ring
    have A₂ : ∀ (ν : ColourForm (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))) (V : ℝ),
        (∀ e c, |ν e c| ≤ V) →
        |∑ c : TorusBond (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)), bondBlockMean Λ.stepParams.side
          (u + 1) (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) (S.weight i _) c *
          ∑ e : Fin 3, ν e c * _root_.YangMills.Construction.MomentLaw.contourAverage Λ.stepParams.side (unitExtension b e) c| ≤ V * (P₂ * W i b.2) := by
      intro ν V hν
      have h3 := abs_fluctuationPart_le hodd (hhb i) (S.supportAt u
          (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) i) hρ.le
        (x := (chartBond b.2).1) (B := unitExtension b)
        (fun e c => abs_unitExtension_le b e c) (fun e c h => unitExtension_site b e c h)
        (fun c hc => exists_child_of_bondBlockMean_ne_zero S u _ i c hc) ν hν
      refine h3.trans (le_of_eq ?_)
      rw [hP₂, hWd]
      ring
    have hg := moment_levelStepGradient_le hj ha hμ hK hC f
      (fun c => bondBlockMean Λ.stepParams.side (u + 1) (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))
        (S.weight i _) c)
      (fun e c => _root_.YangMills.Construction.MomentLaw.contourAverage Λ.stepParams.side (unitExtension b e) c) (mul_nonneg hP₁0 (hW0 i b.2))
      (mul_nonneg hP₂0 (hW0 i b.2)) A₁ A₂ Λ.k hk1
    have eC : 4 * (1 + stdAbsMoment Λ.k) * (P₁ * W i b.2 * (1 + |C₁ 0|) + Λ.stepParams.coupling * (P₂ * W i b.2)) =
        Cw * W i b.2 := by
      rw [hCw]
      ring
    rw [eC] at hg
    have eX : ∀ X, S.levelStepGradient u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) i
        (levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).1
        (levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).2 b =
        f (levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).2 -
        Λ.stepParams.coupling * ∑ c : TorusBond (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)),
          bondBlockMean Λ.stepParams.side (u + 1) (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))
            (S.weight i _) c * ∑ e : Fin 3,
          ((levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).1 e c -
            _root_.YangMills.Construction.MomentLaw.contourAverage Λ.stepParams.side ((levelPair j (u + (j + 1)) (S.data.period Λ.stepParams.side) hj X).2 e) c) *
            _root_.YangMills.Construction.MomentLaw.contourAverage Λ.stepParams.side (unitExtension b e) c := fun X => by
      rw [hfd]
      exact levelStepGradient_eq S u _ i _ _ b
    simp only [eX]
    exact hg
  obtain ⟨Xr, hXr⟩ : ∃ Xr : ℝ, Xr = (Λ.stepParams.side : ℝ) ^ (8 * (S.data.scaleLevel - u)) *
      Real.exp (-(δ * Λ.d / 2 * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u))) := ⟨_, rfl⟩
  have hXr0 : 0 < Xr := by rw [hXr]; positivity
  have hgle : ∀ (b b' : Fin 3 × ChartBondIndex Λ.stepParams.side u
      (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side))),
      |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) b b'| ≤
      |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)))⁻¹ b.2 b'.2| := by
    intro b b'
    unfold fluctuationCov
    split_ifs
    · simp
    · simp
  have hpair : ∀ i i' : Fin Λ.k, i ≠ i' → ∑ b, ∑ b', (Cw * W i b.2 + 0) *
      |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) b b'| * (Cw * W i' b'.2 + 0) ≤ Kc * Xr := by
    intro i i' hne
    have hg : ∀ β β' : ChartBondIndex Λ.stepParams.side u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)),
        |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side u
          (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)))⁻¹ β β'| ≤
        Hc * Real.exp (-(2 * c₂ * (TorusFields.supDist (chartBond β).1 (chartBond β').1 : ℝ))) := fun β β' =>
      ((f₂ S).2 u _ hm64 β β').trans (mul_le_mul_of_nonneg_right (by rw [hHc]; exact le_abs_self _) (Real.exp_pos _).le)
    have hT := sum_weights_kernel_le (fun β : ChartBondIndex Λ.stepParams.side u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) => (chartBond β).1)
      (fun f hf => sum_chartBond_le f hf) hδ hδ1 hδ2 hHc0 hg
      (S.supportAt u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) i)
      (S.supportAt u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) * Λ.stepParams.side) i')
      (hdist _ hN i i' hne)
    simp only [← hWd] at hT
    have hc1 := hcard _ hN i
    have hc2 := hcard _ hN i'
    obtain ⟨Tt, hTt⟩ : ∃ Tt : ℝ, Tt = ∑ β, ∑ β', W i β * |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)))⁻¹ β β'| * W i' β' := ⟨_, rfl⟩
    rw [← hTt] at hT
    have hs1 : ∑ b, ∑ b', (Cw * W i b.2 + 0) * |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) b b'| * (Cw * W i' b'.2 + 0) ≤
        Cw ^ 2 * (9 * Tt) := by
      calc _ ≤ ∑ b : Fin 3 × ChartBondIndex Λ.stepParams.side u
              (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)),
            ∑ b' : Fin 3 × ChartBondIndex Λ.stepParams.side u
              (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)),
            Cw ^ 2 * (W i b.2 * |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side u
              (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)))⁻¹ b.2 b'.2| * W i' b'.2) := by
            refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => ?_
            have h3 := mul_le_mul_of_nonneg_left (hgle b b')
              (mul_nonneg (mul_nonneg hCw0 (hW0 i b.2)) (mul_nonneg hCw0 (hW0 i' b'.2)))
            simp only [add_zero]
            nlinarith [h3]
        _ = Cw ^ 2 * ∑ _e : Fin 3, ∑ β : ChartBondIndex Λ.stepParams.side u
              (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)), ∑ _e' : Fin 3,
            ∑ β' : ChartBondIndex Λ.stepParams.side u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)),
            W i β * |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side u
              (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)))⁻¹ β β'| * W i' β' := by
            simp only [Fintype.sum_prod_type, Finset.mul_sum]
        _ = _ := by
            rw [sum_colours (fun β β' => W i β * |(trivialHessian Λ.stepParams.coupling Λ.stepParams.side u
              (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)))⁻¹ β β'| * W i' β'), hTt]
    have e1 : Real.exp (-(δ * (Λ.d / 2 * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u) - 1))) =
        Real.exp δ * Real.exp (-(δ * Λ.d / 2 * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hcc : ((S.supportAt u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) *
          Λ.stepParams.side) i).card : ℝ) *
        ((S.supportAt u (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) *
          Λ.stepParams.side) i').card : ℝ) ≤
        C₆ 0 ^ 2 * (Λ.stepParams.side : ℝ) ^ (8 * (S.data.scaleLevel - u)) := by
      calc _ ≤ (C₆ 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))) *
            (C₆ 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))) :=
            mul_le_mul hc1 hc2 (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hc1)
        _ = _ := by
            rw [show 8 * (S.data.scaleLevel - u) = 4 * (S.data.scaleLevel - u) + 4 * (S.data.scaleLevel - u) by ring,
              pow_add]
            ring
    have hq0 : 0 ≤ Hc * (4 * expSumOnInt (δ / 4) ^ 4) ^ 2 *
        Real.exp (-(δ * (Λ.d / 2 * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u) - 1))) := by positivity
    calc _ ≤ Cw ^ 2 * (9 * Tt) := hs1
      _ ≤ Cw ^ 2 * (9 * (C₆ 0 ^ 2 * (Λ.stepParams.side : ℝ) ^ (8 * (S.data.scaleLevel - u)) *
            (Hc * (4 * expSumOnInt (δ / 4) ^ 4) ^ 2 *
            Real.exp (-(δ * (Λ.d / 2 * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u) - 1)))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hT.trans ?_) (by norm_num)) (by positivity)
          exact mul_le_mul_of_nonneg_right hcc hq0
      _ = Kc * Xr := by
          rw [hKc, hXr, e1]
          ring
  have hcont : ∀ i i' : Fin Λ.k, Continuous fun ε : ℝ => ∑ b, ∑ b', (Cw * W i b.2 + ε) *
      |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) b b'| * (Cw * W i' b'.2 + ε) := by
    intro i i'
    fun_prop
  have hev : ∀ᶠ ε in nhds (0 : ℝ), ∀ i i' : Fin Λ.k, i ≠ i' →
      ∑ b, ∑ b', (Cw * W i b.2 + ε) * |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) b b'| * (Cw * W i' b'.2 + ε) < (Kc + 1) * Xr := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun i' => ?_
    by_cases hne : i = i'
    · exact Filter.Eventually.of_forall fun _ h => absurd hne h
    · have h3 : ∑ b, ∑ b', (Cw * W i b.2 + 0) * |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 u
          (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) b b'| * (Cw * W i' b'.2 + 0) <
          (Kc + 1) * Xr :=
        (hpair i i' hne).trans_lt (by nlinarith)
      exact ((hcont i i').continuousAt.eventually_lt continuousAt_const h3).mono fun ε h _ => h
  have hev' : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i i' : Fin Λ.k, i ≠ i' →
      ∑ b, ∑ b', (Cw * W i b.2 + ε) * |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 u
        (fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) b b'| * (Cw * W i' b'.2 + ε) < (Kc + 1) * Xr :=
    nhdsWithin_le_nhds hev
  obtain ⟨ε, hε₁, hε₂⟩ := (hev'.and self_mem_nhdsWithin).exists
  have hε : (0 : ℝ) < ε := hε₂
  refine ⟨fun i b => Cw * W i b.2 + ε, fun i b => add_pos_of_nonneg_of_pos (mul_nonneg hCw0 (hW0 i b.2)) hε,
    fun i b => ⟨(hmom i b).1, ?_⟩, fun i i' hne => ?_⟩
  · exact (hmom i b).2.trans (pow_le_pow_left₀ (mul_nonneg hCw0 (hW0 i b.2)) (by linarith) _)
  · refine (hε₁ i i' hne).le.trans (le_of_eq ?_)
    rw [hXr]
    ring
end YangMills.Construction.MomentLaw
end
