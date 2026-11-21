import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOfTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.FirstFormIsTheSquareOfTheCurl
import YangMills.Construction.LawByMomentsOfTheFlow.LeastValueOfAStep
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainHasItsGaussianProof
import YangMills.Construction.ResponseInTheExpansion.LocalRestrictionOfATupleProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses TorusFields TorusPaths RenormalizationStepParameters ResponseInTheExpansion
namespace GaussianChainCoordinates
section Sups
variable {V W : Type} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
  [AddCommGroup W] [Module ℝ W] [MeasurableSpace W]
private theorem gaussianVariance_eq_of_extremal (E : V → ℝ) (f : V →ₗ[ℝ] ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hle : ∀ x, f x ^ 2 ≤ v * E x) (hopt : ∃ x, E x = v ∧ f x = v) : gaussianVariance E f = v := by
  unfold gaussianVariance
  apply le_antisymm
  · refine Real.sSup_le ?_ hv
    rintro w ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hx]
    exact hle x
  · rcases hv.eq_or_lt with h0 | hpos
    · rw [← h0]
      refine Real.sSup_nonneg ?_
      rintro w ⟨x, hx, rfl⟩
      positivity
    · obtain ⟨x, hxE, hxf⟩ := hopt
      refine le_csSup ⟨v, ?_⟩ ⟨x, by rw [hxE]; exact hpos, ?_⟩
      · rintro w ⟨x', hx', rfl⟩
        rw [div_le_iff₀ hx']
        exact hle x'
      · rw [hxE, hxf]
        field_simp
private theorem gaussianVariance_comp_eq (En : V → ℝ) (Kin : W → ℝ) (π : V →ₗ[ℝ] W) (f : W →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ y, 0 ≤ Kin y) (hle : ∀ x, Kin (π x) ≤ En x) (hext : ∀ y, ∃ x, π x = y ∧ En x = Kin y)
    (hb : ∀ y, f y ^ 2 ≤ C * Kin y) : gaussianVariance En (f ∘ₗ π) = gaussianVariance Kin f := by
  unfold gaussianVariance
  have hbd2 : BddAbove {w | ∃ y, 0 < Kin y ∧ w = f y ^ 2 / Kin y} := by
    refine ⟨C, ?_⟩
    rintro w ⟨y, hy, rfl⟩
    rw [div_le_iff₀ hy]
    exact hb y
  have hbd1 : BddAbove {w | ∃ x, 0 < En x ∧ w = (f ∘ₗ π) x ^ 2 / En x} := by
    refine ⟨C, ?_⟩
    rintro w ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hx]
    exact (hb (π x)).trans (mul_le_mul_of_nonneg_left (hle x) hC)
  have hnn1 : 0 ≤ sSup {w | ∃ x, 0 < En x ∧ w = (f ∘ₗ π) x ^ 2 / En x} := by
    refine Real.sSup_nonneg ?_
    rintro w ⟨x, hx, rfl⟩
    positivity
  have hnn2 : 0 ≤ sSup {w | ∃ y, 0 < Kin y ∧ w = f y ^ 2 / Kin y} := by
    refine Real.sSup_nonneg ?_
    rintro w ⟨y, hy, rfl⟩
    positivity
  apply le_antisymm
  · refine Real.sSup_le ?_ hnn2
    rintro w ⟨x, hx, rfl⟩
    rcases (hK (π x)).eq_or_lt with h0 | hpos
    · have h1 : f (π x) ^ 2 ≤ 0 := by simpa [← h0] using hb (π x)
      have h2 : (f ∘ₗ π) x ^ 2 / En x ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 hx.le
      exact h2.trans hnn2
    · refine le_trans ?_ (le_csSup hbd2 ⟨π x, hpos, rfl⟩)
      exact div_le_div_of_nonneg_left (sq_nonneg _) hpos (hle x)
  · refine Real.sSup_le ?_ hnn1
    rintro w ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hE⟩ := hext y
    refine le_csSup hbd1 ⟨x, by rw [hE]; exact hy, ?_⟩
    simp [hx, hE]
end Sups
section Bound
variable {ι : Type} [Fintype ι]
private def bilinSum (M : ι → ι → ℝ) (A B : ι → ℝ) : ℝ := ∑ b, ∑ b', A b * M b b' * B b'
private def symmPart (M : ι → ι → ℝ) : Matrix ι ι ℝ := fun b b' => (M b b' + M b' b) / 2
private theorem dotProduct_symmPart_self (M : ι → ι → ℝ) (A : ι → ℝ) : A ⬝ᵥ (symmPart M).mulVec A = bilinSum M A A := by
  have h : bilinSum M A A = ∑ b, ∑ b', A b * M b' b * A b' := by
    unfold bilinSum
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
  have h2 : A ⬝ᵥ (symmPart M).mulVec A = (bilinSum M A A + ∑ b, ∑ b', A b * M b' b * A b') / 2 := by
    simp only [dotProduct, Matrix.mulVec, symmPart, bilinSum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
  rw [h2, ← h]
  ring
private theorem dotProduct_symmPart_comm (M : ι → ι → ℝ) (u v : ι → ℝ) :
    u ⬝ᵥ (symmPart M).mulVec v = v ⬝ᵥ (symmPart M).mulVec u := by
  have ht : (symmPart M).transpose = symmPart M := by
    ext b b'
    simp only [Matrix.transpose_apply, symmPart]
    ring
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht, dotProduct_comm]
private theorem exists_symmPart_mulVec_eq (M : ι → ι → ℝ) (g : ι → ℝ) (hg : ∀ A, bilinSum M A A = 0 → g ⬝ᵥ A = 0) :
    ∃ x, (symmPart M).mulVec x = g := by
  classical
  by_contra hne
  have hv : g ∉ LinearMap.range (symmPart M).mulVecLin := by
    rintro ⟨x, hx⟩
    exact hne ⟨x, by simpa using hx⟩
  obtain ⟨f, hfg, hpf⟩ := Submodule.exists_le_ker_of_notMem hv
  set z : ι → ℝ := fun i => f (Pi.single i 1) with hz
  have hf : ∀ v : ι → ℝ, f v = z ⬝ᵥ v := by
    intro v
    have : v = ∑ i, v i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp only [map_sum, map_smul, dotProduct, hz, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h0 : z ⬝ᵥ (symmPart M).mulVec z = 0 := by
    rw [← hf]
    exact hpf ⟨z, rfl⟩
  rw [dotProduct_symmPart_self] at h0
  have h1 := hg z h0
  apply hfg
  rw [hf, dotProduct_comm, h1]
private theorem sq_dotProduct_le_mul_bilinSum (M : ι → ι → ℝ) (hpos : ∀ A, 0 ≤ bilinSum M A A) (g : ι → ℝ)
    (hg : ∀ A, bilinSum M A A = 0 → g ⬝ᵥ A = 0) : ∃ C, 0 ≤ C ∧ ∀ A, (g ⬝ᵥ A) ^ 2 ≤ C * bilinSum M A A := by
  obtain ⟨x, hx⟩ := exists_symmPart_mulVec_eq M g hg
  refine ⟨bilinSum M x x, hpos x, fun A => ?_⟩
  rcases (hpos A).eq_or_lt with h0 | hs
  · rw [hg A h0.symm, ← h0]
    simp
  · have hr : g ⬝ᵥ A = x ⬝ᵥ (symmPart M).mulVec A := by
      rw [dotProduct_symmPart_comm, hx, dotProduct_comm]
    set r := g ⬝ᵥ A with hrdef
    set s := bilinSum M A A with hsdef
    have h := hpos (s • x - r • A)
    rw [← dotProduct_symmPart_self] at h
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h
    rw [dotProduct_symmPart_comm M A x, ← hr, dotProduct_symmPart_self, dotProduct_symmPart_self, ← hsdef] at h
    have h2 : 0 ≤ s * (s * bilinSum M x x - r ^ 2) := by nlinarith
    have h3 := nonneg_of_mul_nonneg_right h2 hs
    nlinarith
end Bound
section Colours
variable {m : ℕ} [NeZero m]
private theorem sq_le_mul_sum_bilinSum (q : TorusBond m → TorusBond m → ℝ) (hpos : ∀ A, 0 ≤ bilinSum q A A)
    (f : ColourForm m →ₗ[ℝ] ℝ)
    (hf : ∀ X : ColourForm m, ∑ e, bilinSum q (X e) (X e) = 0 → f X = 0) :
    ∃ C, 0 ≤ C ∧ ∀ X : ColourForm m, f X ^ 2 ≤ C * ∑ e, bilinSum q (X e) (X e) := by
  classical
  have h1 : ∀ e : Fin 3, ∃ C, 0 ≤ C ∧ ∀ A : TorusBond m → ℝ, f (Pi.single e A) ^ 2 ≤ C * bilinSum q A A := by
    intro e
    set g : TorusBond m → ℝ := fun b => f (Pi.single e (Pi.single b 1)) with hg
    have hfg : ∀ A : TorusBond m → ℝ, f (Pi.single e A) = g ⬝ᵥ A := by
      intro A
      have hA : (Pi.single e A : ColourForm m) = ∑ b, A b • (Pi.single e (Pi.single b (1 : ℝ)) : ColourForm m) := by
        funext e' b'
        by_cases h : e' = e
        · subst h
          simp [Finset.sum_apply, Pi.single_apply]
        · simp [Finset.sum_apply, h]
      rw [hA]
      simp only [map_sum, map_smul, dotProduct, hg, smul_eq_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    obtain ⟨C, hC, hb⟩ := sq_dotProduct_le_mul_bilinSum q hpos g (fun A hA => by
      rw [← hfg]
      apply hf
      rw [Finset.sum_eq_single e]
      · simpa using hA
      · intro e' _ h
        simp [Pi.single_eq_of_ne h, bilinSum]
      · simp)
    exact ⟨C, hC, fun A => by rw [hfg]; exact hb A⟩
  choose C hC hb using h1
  refine ⟨3 * ∑ e, C e, mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ => hC e), fun X => ?_⟩
  have hX : f X = ∑ e, f (Pi.single e (X e)) := by
    conv_lhs => rw [← Finset.univ_sum_single X]
    rw [map_sum]
  have hq : ∀ e, 0 ≤ bilinSum q (X e) (X e) := fun e => hpos _
  have hsum : ∑ e, C e * bilinSum q (X e) (X e) ≤ (∑ e, C e) * ∑ e, bilinSum q (X e) (X e) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right ?_ (hq e)
    exact Finset.single_le_sum (f := C) (fun e _ => hC e) (Finset.mem_univ e)
  have h3 : (∑ e : Fin 3, f (Pi.single e (X e))) ^ 2 ≤ 3 * ∑ e : Fin 3, f (Pi.single e (X e)) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3))) (f := fun e => f (Pi.single e (X e)))
  have h4 : ∑ e : Fin 3, f (Pi.single e (X e)) ^ 2 ≤ ∑ e, C e * bilinSum q (X e) (X e) :=
    Finset.sum_le_sum fun e _ => hb e (X e)
  rw [hX]
  nlinarith
end Colours
section Moments
private theorem lintegral_sq_gaussianReal (v : NNReal) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal v := by
  have h1 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal h1 (Filter.Eventually.of_forall fun x => sq_nonneg x)]
  congr 1
  have h2 := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at h2
  simpa [integral_id_gaussianReal] using h2
end Moments
section Chain
variable {L : ℕ}
private theorem chainTop_add (s n : ℕ) (X Y : LevelChain L s n) :
    chainTop s n (X + Y) = chainTop s n X + chainTop s n Y := by
  cases s <;> rfl
private theorem chainTop_smul (s n : ℕ) (c : ℝ) (X : LevelChain L s n) :
    chainTop s n (c • X) = c • chainTop s n X := by
  cases s <;> rfl
private theorem chainDescend_add (u : ℕ) : ∀ (d n : ℕ) (X Y : LevelChain L (u + d) n),
    chainDescend u d n (X + Y) = chainDescend u d n X + chainDescend u d n Y
  | 0, _, _, _ => rfl
  | d + 1, n, X, Y => chainDescend_add u d (n * L) (chainLower X) (chainLower Y)
private theorem chainDescend_smul (u : ℕ) : ∀ (d n : ℕ) (c : ℝ) (X : LevelChain L (u + d) n),
    chainDescend u d n (c • X) = c • chainDescend u d n X
  | 0, _, _, _ => rfl
  | d + 1, n, c, X => chainDescend_smul u d (n * L) c (chainLower X)
private def levelProj (u d n : ℕ) : LevelChain L (u + d) n →ₗ[ℝ] ColourForm (fineSide L d n) where
  toFun X := chainTop u _ (chainDescend u d n X)
  map_add' X Y := by rw [chainDescend_add, chainTop_add]
  map_smul' c X := by rw [chainDescend_smul, chainTop_smul]; rfl
private theorem measurable_chainLower (s n : ℕ) :
    Measurable (chainLower : LevelChain L (s + 1) n → LevelChain L s (n * L)) :=
  measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun c =>
    (measurable_pi_apply (Sum.inl c)).comp (measurable_pi_apply e)
private theorem measurable_chainTop (s n : ℕ) : Measurable (chainTop (L := L) s n) := by
  cases s with
  | zero => exact measurable_id
  | succ s =>
    exact measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun c =>
      (measurable_pi_apply (Sum.inr c)).comp (measurable_pi_apply e)
private theorem measurable_chainDescend (u : ℕ) : ∀ d n : ℕ, Measurable (chainDescend (L := L) u d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_chainDescend u d (n * L)).comp (measurable_chainLower (u + d) n)
private theorem measurable_levelProj (u d n : ℕ) : Measurable (levelProj (L := L) u d n) :=
  (measurable_chainTop u _).comp (measurable_chainDescend u d n)
variable [NeZero L]
private theorem curlNorm_sq {n : ℕ} [NeZero n] (X : ColourForm n) (p : TorusPlaquette n) :
    curlNorm X p ^ 2 = ∑ e, curl (X e) p ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
private theorem kineticForm_eq_sum (a : ℝ) (L u : ℕ) {n : ℕ} [NeZero n] (X : ColourForm n) :
    kineticForm a L u X = ∑ e, maxwellForm a L u (X e) (X e) := rfl
private theorem levelEnergy_zero (a : ℝ) (n : ℕ) [NeZero n] (X : LevelChain L 0 n) :
    levelEnergy a 0 n X = ∑ e : Fin 3, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl (chainTop 0 n X e) p ^ 2 := by
  show ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curlNorm (chainTop 0 n X) p ^ 2 = _
  simp only [curlNorm_sq]
  rw [Finset.sum_comm]
private theorem levelEnergy_succ (a : ℝ) (s n : ℕ) [NeZero n] (X : LevelChain L (s + 1) n) :
    levelEnergy a (s + 1) n X = levelEnergy a s (n * L) (chainLower X) + a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 :=
  rfl
private theorem levelEnergy_nonneg {a : ℝ} (ha : 0 ≤ a) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n), 0 ≤ levelEnergy a s n X := by
  intro s
  induction s with
  | zero =>
    intro n _ X
    rw [levelEnergy_zero]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  | succ s ih =>
    intro n _ X
    rw [levelEnergy_succ]
    exact add_nonneg (ih _ _) (mul_nonneg ha (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
abbrev _root_.YangMills.SharedProofs.p39411 := @levelEnergy_nonneg
private structure ChainHyps (a ρA cK : ℝ) (L n₀ : ℕ) [NeZero L] : Prop where
  coupling_pos : 0 < a
  coercivity_pos : 0 < cK
  side_pos : 0 < L
  maxwell_le : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ (W : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ),
    maxwellForm a L (u + 1) B B ≤ maxwellForm a L u W W + a * ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L W c - B c) ^ 2
  maxwell_eq_response : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ B : TorusBond n → ℝ, maxwellForm a L (u + 1) B B =
    maxwellForm a L u (responseMap a ρA L u B) (responseMap a ρA L u B) +
      a * ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρA L u B) c - B c) ^ 2
  maxwell_zero : ∀ (m : ℕ) [NeZero m] (A : TorusBond m → ℝ),
    maxwellForm a L 0 A A = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2
  coercive : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ A : TorusBond n → ℝ,
    2 * cK * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 ≤ maxwellForm a L u A A
variable {a ρA cK : ℝ} {n₀ : ℕ}
private theorem ChainHyps.le_mul_side (F : ChainHyps a ρA cK L n₀) {n : ℕ} (hn : n₀ ≤ n) : n₀ ≤ n * L :=
  hn.trans (Nat.le_mul_of_pos_right n F.side_pos)
private theorem levelEnergy_zero_eq_kinetic (F : ChainHyps a ρA cK L n₀) (n : ℕ) [NeZero n] (X : LevelChain L 0 n) :
    levelEnergy a 0 n X = kineticForm a L 0 (chainTop 0 n X) := by
  rw [levelEnergy_zero, kineticForm_eq_sum]
  exact Finset.sum_congr rfl fun e _ => (F.maxwell_zero n _).symm
private theorem kineticForm_top_le (F : ChainHyps a ρA cK L n₀) : ∀ (s n : ℕ) [NeZero n], n₀ ≤ n → ∀ X : LevelChain L s n,
    kineticForm a L s (chainTop s n X) ≤ levelEnergy a s n X := by
  intro s
  induction s with
  | zero =>
    intro n _ _ X
    exact (levelEnergy_zero_eq_kinetic F n X).ge
  | succ s ih =>
    intro n _ hn X
    have h := ih (n * L) (F.le_mul_side hn) (chainLower X)
    have h2 : ∀ e, maxwellForm a L (s + 1) (chainTop (s + 1) n X e) (chainTop (s + 1) n X e) ≤
        maxwellForm a L s (chainTop s (n * L) (chainLower X) e) (chainTop s (n * L) (chainLower X) e) +
          a * ∑ c : TorusBond n, chainDefect X e c ^ 2 := by
      intro e
      have h3 := F.maxwell_le s n hn (chainTop s (n * L) (chainLower X) e) (chainTop (s + 1) n X e)
      have h4 : ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) (chainLower X) e) c - chainTop (s + 1) n X e c) ^ 2 =
          ∑ c : TorusBond n, chainDefect X e c ^ 2 :=
        Finset.sum_congr rfl fun c _ => by
          unfold chainDefect
          ring
      rwa [h4] at h3
    rw [levelEnergy_succ, kineticForm_eq_sum]
    have h5 := Finset.sum_le_sum fun e (_ : e ∈ (Finset.univ : Finset (Fin 3))) => h2 e
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))] at h5
    rw [kineticForm_eq_sum] at h
    linarith
private theorem exists_top_eq (F : ChainHyps a ρA cK L n₀) : ∀ (s n : ℕ) [NeZero n], n₀ ≤ n → ∀ Y : ColourForm n,
    ∃ X : LevelChain L s n, chainTop s n X = Y ∧ levelEnergy a s n X = kineticForm a L s Y := by
  intro s
  induction s with
  | zero =>
    intro n _ _ Y
    exact ⟨Y, rfl, levelEnergy_zero_eq_kinetic F n Y⟩
  | succ s ih =>
    intro n _ hn Y
    obtain ⟨X', hX', hE⟩ := ih (n * L) (F.le_mul_side hn) (pushColours a ρA L s Y)
    let X : LevelChain L (s + 1) n := fun e => Sum.elim (X' e) (Y e)
    have h2 : levelEnergy a (s + 1) n X = levelEnergy a s (n * L) X' +
        a * ∑ c : TorusBond n, ∑ e : Fin 3, (Y e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) X' e) c) ^ 2 := rfl
    refine ⟨X, rfl, ?_⟩
    rw [h2, hX', hE, kineticForm_eq_sum, kineticForm_eq_sum, Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [F.maxwell_eq_response s n hn (Y e)]
    have h6 : ∑ c : TorusBond n, (Y e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (pushColours a ρA L s Y e) c) ^ 2 =
        ∑ c : TorusBond n, (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρA L s (Y e)) c - Y e c) ^ 2 :=
      Finset.sum_congr rfl fun c _ => by
        show (Y e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρA L s (Y e)) c) ^ 2 = _
        ring
    rw [h6]
    rfl
private theorem kineticForm_level_le (F : ChainHyps a ρA cK L n₀) (u : ℕ) : ∀ (d n : ℕ) [NeZero n], n₀ ≤ n → ∀ X : LevelChain L (u + d) n,
    kineticForm a L u (levelProj u d n X) ≤ levelEnergy a (u + d) n X := by
  intro d
  induction d with
  | zero =>
    intro n _ hn X
    exact kineticForm_top_le F u n hn X
  | succ d ih =>
    intro n _ hn X
    have h := ih (n * L) (F.le_mul_side hn) (chainLower X)
    have h2 : levelEnergy a (u + (d + 1)) n X = levelEnergy a (u + d) (n * L) (chainLower X) +
        a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 := rfl
    have h3 : 0 ≤ a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 :=
      mul_nonneg F.coupling_pos.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [h2]
    exact h.trans (by linarith)
private theorem exists_level_eq (F : ChainHyps a ρA cK L n₀) (u : ℕ) : ∀ (d n : ℕ) [NeZero n], n₀ ≤ n → ∀ Y : ColourForm (fineSide L d n),
    ∃ X : LevelChain L (u + d) n, levelProj u d n X = Y ∧ levelEnergy a (u + d) n X = kineticForm a L u Y := by
  intro d
  induction d with
  | zero =>
    intro n _ hn Y
    exact exists_top_eq F u n hn Y
  | succ d ih =>
    intro n _ hn Y
    obtain ⟨X', hX', hE⟩ := ih (n * L) (F.le_mul_side hn) Y
    refine ⟨fun e => Sum.elim (X' e) (fun c => _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop (u + d) (n * L) X' e) c), hX', ?_⟩
    have h2 : levelEnergy a (u + (d + 1)) n
        (fun e => Sum.elim (X' e) (fun c => _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop (u + d) (n * L) X' e) c)) =
        levelEnergy a (u + d) (n * L) X' + a * ∑ c : TorusBond n, ∑ e : Fin 3,
          (_root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop (u + d) (n * L) X' e) c - _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop (u + d) (n * L) X' e) c) ^ 2 := rfl
    rw [h2, hE]
    simp
    rfl
end Chain
section Linear
variable {L : ℕ} [NeZero L]
private theorem sumAlongWord_add {m : ℕ} (A B : TorusBond m → ℝ) (w : BondWord m) :
    sumAlongWord (A + B) w = sumAlongWord A w + sumAlongWord B w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
private theorem contourAverage_add {n : ℕ} [NeZero n] (A B : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (A + B) c = _root_.YangMills.Construction.MomentLaw.contourAverage L A c + _root_.YangMills.Construction.MomentLaw.contourAverage L B c := by
  unfold _root_.YangMills.Construction.MomentLaw.contourAverage
  simp only [sumAlongWord_add, Finset.sum_add_distrib, mul_add]
private theorem contourAverage_smul {n : ℕ} [NeZero n] (t : ℝ) (A : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (t • A) c = t * _root_.YangMills.Construction.MomentLaw.contourAverage L A c := by apply _root_.YangMills.SharedProofs.p14469 <;> assumption
private theorem plaqCurl_add {m : ℕ} (A B : TorusBond m → ℝ) (p : TorusPlaquette m) : curl (A + B) p = curl A p + curl B p := by apply _root_.YangMills.SharedProofs.p35838 <;> assumption
private theorem plaqCurl_smul {m : ℕ} (t : ℝ) (A : TorusBond m → ℝ) (p : TorusPlaquette m) : curl (t • A) p = t * curl A p := by apply _root_.YangMills.SharedProofs.p39240 <;> assumption
private theorem chainDefect_add {s n : ℕ} [NeZero n] (X Y : LevelChain L (s + 1) n) (e : Fin 3) (c : TorusBond n) :
    chainDefect (X + Y) e c = chainDefect X e c + chainDefect Y e c := by
  unfold chainDefect
  have h1 : chainLower (X + Y) = chainLower X + chainLower Y := rfl
  rw [h1, chainTop_add, chainTop_add]
  show (chainTop (s + 1) n X e + chainTop (s + 1) n Y e) c -
    _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) (chainLower X) e + chainTop s (n * L) (chainLower Y) e) c = _
  rw [contourAverage_add, Pi.add_apply]
  ring
private theorem chainDefect_smul {s n : ℕ} [NeZero n] (t : ℝ) (X : LevelChain L (s + 1) n) (e : Fin 3) (c : TorusBond n) :
    chainDefect (t • X) e c = t * chainDefect X e c := by
  unfold chainDefect
  have h1 : chainLower (t • X) = t • chainLower X := rfl
  rw [h1, chainTop_smul, chainTop_smul]
  show (t • chainTop (s + 1) n X e) c - _root_.YangMills.Construction.MomentLaw.contourAverage L (t • chainTop s (n * L) (chainLower X) e) c = _
  rw [contourAverage_smul, Pi.smul_apply, smul_eq_mul]
  ring
private theorem noisePairing_succ {s n : ℕ} [NeZero n] (c : ChainNoise L (s + 1) n → ℝ) (X : LevelChain L (s + 1) n) :
    noisePairing (s + 1) n c X = noisePairing s (n * L) (fun i => c (Sum.inl i)) (chainLower X) +
      ∑ b : TorusBond n, ∑ e : Fin 3, c (Sum.inr (e, b)) * chainDefect X e b := rfl
private theorem noisePairing_zero {n : ℕ} [NeZero n] (c : ChainNoise L 0 n → ℝ) (X : LevelChain L 0 n) :
    noisePairing 0 n c X = ∑ e : Fin 3, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      c (e, p) * curl (chainTop 0 n X e) p := by
  show ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), ∑ e : Fin 3, c (e, p) * curl (chainTop 0 n X e) p = _
  rw [Finset.sum_comm]
private theorem noisePairing_add : ∀ (s n : ℕ) [NeZero n] (c : ChainNoise L s n → ℝ) (X Y : LevelChain L s n),
    noisePairing s n c (X + Y) = noisePairing s n c X + noisePairing s n c Y := by
  intro s
  induction s with
  | zero =>
    intro n _ c X Y
    rw [noisePairing_zero, noisePairing_zero, noisePairing_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [chainTop_add]
    show c (e, p) * curl (chainTop 0 n X e + chainTop 0 n Y e) p = _
    rw [plaqCurl_add]
    ring
  | succ s ih =>
    intro n _ c X Y
    rw [noisePairing_succ, noisePairing_succ, noisePairing_succ]
    have h1 : chainLower (X + Y) = chainLower X + chainLower Y := rfl
    rw [h1, ih]
    simp only [chainDefect_add, mul_add, Finset.sum_add_distrib]
    ring
private theorem noisePairing_smul : ∀ (s n : ℕ) [NeZero n] (c : ChainNoise L s n → ℝ) (t : ℝ) (X : LevelChain L s n),
    noisePairing s n c (t • X) = t * noisePairing s n c X := by
  intro s
  induction s with
  | zero =>
    intro n _ c t X
    rw [noisePairing_zero, noisePairing_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [chainTop_smul]
    show c (e, p) * curl (t • chainTop 0 n X e) p = _
    rw [plaqCurl_smul]
    ring
  | succ s ih =>
    intro n _ c t X
    rw [noisePairing_succ, noisePairing_succ]
    have h1 : chainLower (t • X) = t • chainLower X := rfl
    rw [h1, ih, mul_add]
    congr 1
    simp only [chainDefect_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => by ring
private def noisePairingLin (s n : ℕ) [NeZero n] (c : ChainNoise L s n → ℝ) : LevelChain L s n →ₗ[ℝ] ℝ where
  toFun := noisePairing s n c
  map_add' := noisePairing_add s n c
  map_smul' t X := noisePairing_smul s n c t X
end Linear
section Torus
variable {m : ℕ} [NeZero m]
private def curlLinearMap : (TorusBond m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (OrientedPlaquette m) where
  toFun := curlVec
  map_add' A B := by
    ext p
    simp [curlVec, plaqCurl_add]
  map_smul' t A := by
    ext p
    simp [curlVec, plaqCurl_smul]
private theorem curvatureSubspace_eq_range : curvatureSubspace m = LinearMap.range (curlLinearMap (m := m)) := by
  unfold curvatureSubspace
  have h : Set.range (curlVec (m := m)) = (LinearMap.range (curlLinearMap (m := m)) : Set _) := rfl
  rw [h, Submodule.span_eq]
private theorem curlVec_mem (A : TorusBond m → ℝ) : curlVec A ∈ curvatureSubspace m := by
  rw [curvatureSubspace_eq_range]
  exact ⟨A, rfl⟩
private def coeffVec (c : TorusPlaquette m → ℝ) : EuclideanSpace ℝ (OrientedPlaquette m) := WithLp.toLp 2 fun p => c p.1
private theorem sum_plaquettesIn (f : TorusPlaquette m → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), f p = ∑ p : OrientedPlaquette m, f p.1 := by apply _root_.YangMills.SharedProofs.p68842 <;> assumption
private theorem inner_eq_sum (u v : EuclideanSpace ℝ (OrientedPlaquette m)) : inner ℝ u v = ∑ p, u p * v p := by
  simp [PiLp.inner_apply, mul_comm]
private theorem sum_mul_curl_eq_inner (c : TorusPlaquette m → ℝ) (A : TorusBond m → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), c p * curl A p = inner ℝ (coeffVec c) (curlVec A) := by
  rw [sum_plaquettesIn, inner_eq_sum]
  rfl
private theorem norm_curlVec_sq (A : TorusBond m → ℝ) :
    ‖curlVec A‖ ^ 2 = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum, sum_plaquettesIn]
  exact Finset.sum_congr rfl fun p _ => (sq _).symm
private theorem inner_coeffVec_eq_proj (c : TorusPlaquette m → ℝ) (A : TorusBond m → ℝ) :
    inner ℝ (coeffVec c) (curlVec A) = inner ℝ ((curvatureSubspace m).starProjection (coeffVec c)) (curlVec A) := by
  rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (curlVec_mem A)]
private theorem norm_proj_sq (v : EuclideanSpace ℝ (OrientedPlaquette m)) :
    ‖(curvatureSubspace m).starProjection v‖ ^ 2 = inner ℝ v ((curvatureSubspace m).starProjection v) := by
  rw [← real_inner_self_eq_norm_sq, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ v)]
open Classical in
private theorem coeffVec_eq_sum (c : TorusPlaquette m → ℝ) :
    coeffVec c = ∑ p : OrientedPlaquette m, c p.1 • EuclideanSpace.single p (1 : ℝ) := by
  ext q
  simp [coeffVec, Finset.sum_apply, Pi.single_apply]
private theorem curvatureVariance_eq (c : TorusPlaquette m → ℝ) :
    curvatureVariance m c = ‖(curvatureSubspace m).starProjection (coeffVec c)‖ ^ 2 := by
  classical
  rw [norm_proj_sq]
  conv_rhs => rw [coeffVec_eq_sum]
  unfold curvatureVariance
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, torusCurvatureProjection, conj_trivial,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  ring
private theorem exists_curlVec_eq_proj (c : TorusPlaquette m → ℝ) :
    ∃ A : TorusBond m → ℝ, curlVec A = (curvatureSubspace m).starProjection (coeffVec c) := by
  have h := Submodule.starProjection_apply_mem (curvatureSubspace m) (coeffVec c)
  rw [curvatureSubspace_eq_range] at h
  obtain ⟨A, hA⟩ := h
  exact ⟨A, by rw [curvatureSubspace_eq_range]; exact hA⟩
end Torus
section Variance
variable {L : ℕ} [NeZero L]
private theorem sq_add_le_mul_add {x y p q r t : ℝ} (h1 : x ^ 2 ≤ p * r) (h2 : y ^ 2 ≤ q * t) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (ht : 0 ≤ t) : (x + y) ^ 2 ≤ (p + q) * (r + t) := by
  have h3 : (2 * x * y) ^ 2 ≤ (p * t + q * r) ^ 2 := by
    have h4 : (x * y) ^ 2 ≤ (p * r) * (q * t) := by
      rw [mul_pow]
      exact mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg hp hr)
    nlinarith [sq_nonneg (p * t - q * r)]
  have h5 := (abs_le_of_sq_le_sq' h3 (add_nonneg (mul_nonneg hp ht) (mul_nonneg hq hr))).2
  nlinarith
private theorem noiseVariance_zero (a : ℝ) {n : ℕ} [NeZero n] (c : ChainNoise L 0 n → ℝ) :
    noiseVariance a 0 n c = ∑ e : Fin 3, ‖(curvatureSubspace n).starProjection (coeffVec fun p => c (e, p))‖ ^ 2 :=
  Finset.sum_congr rfl fun _ _ => curvatureVariance_eq _
private theorem noiseVariance_succ (a : ℝ) {s n : ℕ} [NeZero n] (c : ChainNoise L (s + 1) n → ℝ) :
    noiseVariance a (s + 1) n c = noiseVariance a s (n * L) (fun i => c (Sum.inl i)) +
      a⁻¹ * ∑ b : TorusBond n, ∑ e : Fin 3, c (Sum.inr (e, b)) ^ 2 := rfl
private theorem levelEnergy_zero_eq_norm (a : ℝ) {n : ℕ} [NeZero n] (X : LevelChain L 0 n) :
    levelEnergy a 0 n X = ∑ e : Fin 3, ‖curlVec (chainTop 0 n X e)‖ ^ 2 := by
  rw [levelEnergy_zero]
  exact Finset.sum_congr rfl fun _ _ => (norm_curlVec_sq _).symm
private theorem noisePairing_zero_eq_inner {n : ℕ} [NeZero n] (c : ChainNoise L 0 n → ℝ) (X : LevelChain L 0 n) :
    noisePairing 0 n c X = ∑ e : Fin 3, inner ℝ ((curvatureSubspace n).starProjection (coeffVec fun p => c (e, p)))
      (curlVec (chainTop 0 n X e)) := by
  rw [noisePairing_zero]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_mul_curl_eq_inner (fun p => c (e, p)), inner_coeffVec_eq_proj]
private theorem exists_noise_extremal {a : ℝ} (ha : 0 < a) : ∀ (s n : ℕ) [NeZero n] (c : ChainNoise L s n → ℝ),
    ∃ X : LevelChain L s n, levelEnergy a s n X = noiseVariance a s n c ∧ noisePairing s n c X = noiseVariance a s n c := by
  intro s
  induction s with
  | zero =>
    intro n _ c
    choose A hA using fun e : Fin 3 => exists_curlVec_eq_proj (m := n) fun p => c (e, p)
    let X : LevelChain L 0 n := A
    refine ⟨X, ?_, ?_⟩
    · rw [levelEnergy_zero_eq_norm, noiseVariance_zero]
      exact Finset.sum_congr rfl fun e _ => by
        show ‖curlVec (A e)‖ ^ 2 = _
        rw [hA]
    · rw [noisePairing_zero_eq_inner, noiseVariance_zero]
      refine Finset.sum_congr rfl fun e _ => ?_
      show inner ℝ _ (curlVec (A e)) = _
      rw [hA, real_inner_self_eq_norm_sq]
  | succ s ih =>
    intro n _ c
    obtain ⟨X', hE, hN⟩ := ih (n * L) fun i => c (Sum.inl i)
    let X : LevelChain L (s + 1) n := fun e =>
      Sum.elim (X' e) fun b => _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) X' e) b + a⁻¹ * c (Sum.inr (e, b))
    have hnu : ∀ e b, chainDefect X e b = a⁻¹ * c (Sum.inr (e, b)) := by
      intro e b
      show _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) X' e) b + a⁻¹ * c (Sum.inr (e, b)) -
        _root_.YangMills.Construction.MomentLaw.contourAverage L (chainTop s (n * L) X' e) b = _
      ring
    have hb : chainLower X = X' := rfl
    refine ⟨X, ?_, ?_⟩
    · rw [levelEnergy_succ, noiseVariance_succ, hb, hE]
      congr 1
      simp only [hnu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
      field_simp
    · rw [noisePairing_succ, noiseVariance_succ, hb, hN]
      congr 1
      simp only [hnu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
      ring
private theorem noiseVariance_nonneg {a : ℝ} (ha : 0 < a) (s n : ℕ) [NeZero n] (c : ChainNoise L s n → ℝ) :
    0 ≤ noiseVariance a s n c := by
  obtain ⟨X, hE, -⟩ := exists_noise_extremal ha s n c
  rw [← hE]
  exact levelEnergy_nonneg ha.le s n X
private theorem sq_noisePairing_le {a : ℝ} (ha : 0 < a) : ∀ (s n : ℕ) [NeZero n] (c : ChainNoise L s n → ℝ) (X : LevelChain L s n),
    noisePairing s n c X ^ 2 ≤ noiseVariance a s n c * levelEnergy a s n X := by
  intro s
  induction s with
  | zero =>
    intro n _ c X
    rw [noisePairing_zero_eq_inner, noiseVariance_zero, levelEnergy_zero_eq_norm]
    set P : Fin 3 → ℝ := fun e => ‖(curvatureSubspace n).starProjection (coeffVec fun p => c (e, p))‖ with hP
    set Q : Fin 3 → ℝ := fun e => ‖curlVec (chainTop 0 n X e)‖ with hQ
    have h1 : |∑ e : Fin 3, inner ℝ ((curvatureSubspace n).starProjection (coeffVec fun p => c (e, p)))
        (curlVec (chainTop 0 n X e))| ≤ ∑ e, P e * Q e :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => abs_real_inner_le_norm _ _)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ P Q
    refine le_trans ?_ h2
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  | succ s ih =>
    intro n _ c X
    rw [noisePairing_succ, noiseVariance_succ, levelEnergy_succ]
    have hS : 0 ≤ ∑ b : TorusBond n, ∑ e : Fin 3, c (Sum.inr (e, b)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hT : 0 ≤ ∑ b : TorusBond n, ∑ e : Fin 3, chainDefect X e b ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine sq_add_le_mul_add (ih (n * L) _ _) ?_ (noiseVariance_nonneg ha _ _ _) (mul_nonneg (inv_nonneg.2 ha.le) hS)
      (levelEnergy_nonneg ha.le _ _ _) (mul_nonneg ha.le hT)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (TorusBond n × Fin 3))
      (fun q => c (Sum.inr (q.2, q.1))) (fun q => chainDefect X q.2 q.1)
    have e1 : ∀ f : TorusBond n × Fin 3 → ℝ, ∑ q, f q = ∑ b, ∑ e, f (b, e) := fun f => Fintype.sum_prod_type f
    rw [e1, e1, e1] at h2
    have h3 : a⁻¹ * (∑ b : TorusBond n, ∑ e : Fin 3, c (Sum.inr (e, b)) ^ 2) *
        (a * ∑ b : TorusBond n, ∑ e : Fin 3, chainDefect X e b ^ 2) =
        (∑ b : TorusBond n, ∑ e : Fin 3, c (Sum.inr (e, b)) ^ 2) * ∑ b : TorusBond n, ∑ e : Fin 3, chainDefect X e b ^ 2 := by
      field_simp
    rw [h3]
    exact h2
end Variance
section Assembly
variable {L : ℕ} [NeZero L] {a ρA cK : ℝ} {n₀ : ℕ}
private theorem le_fineSide (F : ChainHyps a ρA cK L n₀) : ∀ (d n : ℕ), n₀ ≤ n → n₀ ≤ fineSide L d n
  | 0, _, h => h
  | d + 1, n, h => le_fineSide F d (n * L) (F.le_mul_side h)
private theorem maxwellForm_nonneg (F : ChainHyps a ρA cK L n₀) (u : ℕ) {m : ℕ} [NeZero m] (hm : n₀ ≤ m) (A : TorusBond m → ℝ) :
    0 ≤ maxwellForm a L u A A := by
  have h0 : 0 ≤ 2 * cK * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl A p ^ 2 :=
    mul_nonneg (by linarith [F.coercivity_pos]) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact h0.trans (F.coercive u m hm A)
private theorem kineticForm_nonneg (F : ChainHyps a ρA cK L n₀) (u : ℕ) {m : ℕ} [NeZero m] (hm : n₀ ≤ m) (Y : ColourForm m) :
    0 ≤ kineticForm a L u Y := by
  rw [kineticForm_eq_sum]
  exact Finset.sum_nonneg fun _ _ => maxwellForm_nonneg F u hm _
private theorem mem_plaquettesIn {m : ℕ} [NeZero m] (p : OrientedPlaquette m) :
    p.1 ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)) := by
  classical
  simpa [plaquettesIn] using p.2
private theorem curlNorm_sq_le (F : ChainHyps a ρA cK L n₀) (u : ℕ) {m : ℕ} [NeZero m] (hm : n₀ ≤ m) (Y : ColourForm m)
    (p : OrientedPlaquette m) : curlNorm Y p.1 ^ 2 ≤ (2 * cK)⁻¹ * kineticForm a L u Y := by
  have hc : 0 < 2 * cK := by linarith [F.coercivity_pos]
  rw [curlNorm_sq, kineticForm_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [inv_mul_eq_div, le_div_iff₀ hc]
  have h1 : curl (Y e) p.1 ^ 2 ≤ ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl (Y e) p ^ 2 :=
    Finset.single_le_sum (f := fun p => curl (Y e) p ^ 2) (fun _ _ => sq_nonneg _) (mem_plaquettesIn p)
  have h2 := F.coercive u m hm (Y e)
  nlinarith
private theorem exists_bound_kineticForm (F : ChainHyps a ρA cK L n₀) (u : ℕ) {m : ℕ} [NeZero m] (hm : n₀ ≤ m)
    (f : ColourForm m →ₗ[ℝ] ℝ) (hf : ∀ Y, kineticForm a L u Y = 0 → f Y = 0) :
    ∃ C, 0 ≤ C ∧ ∀ Y, f Y ^ 2 ≤ C * kineticForm a L u Y :=
  sq_le_mul_sum_bilinSum (maxwellKernel a L u) (fun A => maxwellForm_nonneg F u hm A) f hf
private theorem measurable_linear {m : ℕ} [NeZero m] (f : ColourForm m →ₗ[ℝ] ℝ) : Measurable f :=
  f.continuous_of_finiteDimensional.measurable
private theorem coordinates_of_hyps (F : ChainHyps a ρA cK L n₀) (u d n : ℕ) [NeZero n] (hn : n₀ ≤ n) :
    (∀ (X : ColourForm (fineSide L d n)) (p : OrientedPlaquette (fineSide L d n)),
      curlNorm X p.1 ^ 2 ≤ 3 / (2 * cK) * kineticForm a L u X) ∧
    ∀ μ : Measure (LevelChain L (u + d) n), IsCanonicalGaussian (levelEnergy a (u + d) n) μ →
      (∀ co : ChainNoise L (u + d) n → ℝ, μ.map (noisePairing (u + d) n co) =
        gaussianReal 0 (noiseVariance a (u + d) n co).toNNReal) ∧
      IsCanonicalGaussian (kineticForm a L u) (μ.map fun X => chainTop u (fineSide L d n) (chainDescend u d n X)) ∧
      ∀ p : OrientedPlaquette (fineSide L d n),
        ∫⁻ X, ENNReal.ofReal (curlNorm (chainTop u (fineSide L d n) (chainDescend u d n X)) p.1 ^ 2) ∂μ ≤
          ENNReal.ofReal (3 / (2 * cK)) := by
  have hm : n₀ ≤ fineSide L d n := le_fineSide F d n hn
  have hc : 0 < 2 * cK := by linarith [F.coercivity_pos]
  have hkin := fun Y : ColourForm (fineSide L d n) => kineticForm_nonneg F u hm Y
  have hle := kineticForm_level_le F u d n hn
  have hext := exists_level_eq F u d n hn
  refine ⟨fun X p => ?_, fun μ h => ?_⟩
  · refine (curlNorm_sq_le F u hm X p).trans (mul_le_mul_of_nonneg_right ?_ (hkin X))
    rw [div_eq_mul_inv]
    have : 0 < (2 * cK)⁻¹ := inv_pos.2 hc
    linarith
  have hvar : ∀ f : ColourForm (fineSide L d n) →ₗ[ℝ] ℝ, (∀ Y, kineticForm a L u Y = 0 → f Y = 0) →
      (∀ X, levelEnergy a (u + d) n X = 0 → (f ∘ₗ levelProj u d n) X = 0) ∧
      gaussianVariance (levelEnergy a (u + d) n) (f ∘ₗ levelProj u d n) = gaussianVariance (kineticForm a L u) f := by
    intro f hf
    obtain ⟨C, hC, hb⟩ := exists_bound_kineticForm F u hm f hf
    refine ⟨fun X hX => hf _ (le_antisymm ((hle X).trans hX.le) (hkin _)), ?_⟩
    exact gaussianVariance_comp_eq _ _ (levelProj u d n) f hC hkin hle hext hb
  have hlaw : ∀ f : ColourForm (fineSide L d n) →ₗ[ℝ] ℝ, (∀ Y, kineticForm a L u Y = 0 → f Y = 0) →
      μ.map (f ∘ₗ levelProj u d n) = gaussianReal 0 (gaussianVariance (kineticForm a L u) f).toNNReal := by
    intro f hf
    obtain ⟨h1, h2⟩ := hvar f hf
    rw [← h2]
    exact h.map_eq _ h1
  have hmeas := measurable_levelProj (L := L) u d n
  have : IsProbabilityMeasure μ := h.isProbabilityMeasure
  refine ⟨fun co => ?_, ⟨Measure.isProbabilityMeasure_map hmeas.aemeasurable, fun f hf => ?_⟩, fun p => ?_⟩
  · have hcs := sq_noisePairing_le F.coupling_pos (u + d) n co
    have hz : ∀ X, levelEnergy a (u + d) n X = 0 → noisePairingLin (u + d) n co X = 0 := by
      intro X hX
      have h1 := hcs X
      rw [hX, mul_zero] at h1
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h1 (sq_nonneg _))
    have h2 := h.map_eq (noisePairingLin (u + d) n co) hz
    rw [gaussianVariance_eq_of_extremal _ _ (noiseVariance_nonneg F.coupling_pos _ _ _) hcs
      (exists_noise_extremal F.coupling_pos (u + d) n co)] at h2
    exact h2
  · have h1 : (μ.map fun X => chainTop u (fineSide L d n) (chainDescend u d n X)).map f = μ.map (f ∘ₗ levelProj u d n) :=
      Measure.map_map (measurable_linear f) hmeas
    rw [h1]
    exact hlaw f hf
  · have hcol : ∀ e : Fin 3, ∫⁻ X, ENNReal.ofReal (curl (levelProj u d n X e) p.1 ^ 2) ∂μ ≤ ENNReal.ofReal (2 * cK)⁻¹ := by
      intro e
      let f : ColourForm (fineSide L d n) →ₗ[ℝ] ℝ :=
        { toFun := fun Y => curl (Y e) p.1
          map_add' := fun Y Y' => plaqCurl_add _ _ _
          map_smul' := fun t Y => plaqCurl_smul _ _ _ }
      have hfb : ∀ Y, f Y ^ 2 ≤ (2 * cK)⁻¹ * kineticForm a L u Y := by
        intro Y
        refine le_trans ?_ (curlNorm_sq_le F u hm Y p)
        rw [curlNorm_sq]
        exact Finset.single_le_sum (f := fun e => curl (Y e) p.1 ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ e)
      have hf : ∀ Y, kineticForm a L u Y = 0 → f Y = 0 := by
        intro Y hY
        have h1 := hfb Y
        rw [hY, mul_zero] at h1
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h1 (sq_nonneg _))
      have hv : gaussianVariance (kineticForm a L u) f ≤ (2 * cK)⁻¹ := by
        refine Real.sSup_le ?_ (inv_pos.2 hc).le
        rintro w ⟨Y, hY, rfl⟩
        rw [div_le_iff₀ hY]
        exact hfb Y
      have hmf : Measurable (f ∘ₗ levelProj u d n) := (measurable_linear f).comp hmeas
      have h1 : ∫⁻ X, ENNReal.ofReal (curl (levelProj u d n X e) p.1 ^ 2) ∂μ =
          ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(μ.map (f ∘ₗ levelProj u d n)) := by
        rw [lintegral_map (by fun_prop) hmf]
        rfl
      rw [h1, hlaw f hf, lintegral_sq_gaussianReal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.coe_toNNReal']
      exact max_le hv (inv_pos.2 hc).le
    have hsum : ∀ X, ENNReal.ofReal (curlNorm (chainTop u (fineSide L d n) (chainDescend u d n X)) p.1 ^ 2) =
        ∑ e : Fin 3, ENNReal.ofReal (curl (levelProj u d n X e) p.1 ^ 2) := by
      intro X
      rw [curlNorm_sq, ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
      rfl
    simp only [hsum]
    have hm2 : ∀ e : Fin 3, Measurable fun X => ENNReal.ofReal (curl (levelProj u d n X e) p.1 ^ 2) := by
      intro e
      let f : ColourForm (fineSide L d n) →ₗ[ℝ] ℝ :=
        { toFun := fun Y => curl (Y e) p.1
          map_add' := fun Y Y' => plaqCurl_add _ _ _
          map_smul' := fun t Y => plaqCurl_smul _ _ _ }
      have hmf : Measurable fun X => f (levelProj u d n X) := (measurable_linear f).comp hmeas
      exact (hmf.pow_const 2).ennreal_ofReal
    rw [lintegral_finsetSum _ fun e _ => hm2 e]
    refine (Finset.sum_le_sum fun e _ => hcol e).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : ENNReal.ofReal (3 / (2 * cK)) = ENNReal.ofReal 3 * ENNReal.ofReal (2 * cK)⁻¹ := by
      rw [← ENNReal.ofReal_mul (by norm_num), div_eq_mul_inv]
    rw [h3]
    norm_num
private theorem chainHyps_of_parameters (Tb : ParameterAssignment) (y : ℝ) (hD : Tb.Admissible) (h₁ : stepMinimumAt Tb y)
    (h₂ : GradientMaxwellPropertiesAt Tb y) (h₃ : maxwellFormAtZeroStatement) :
    ChainHyps Tb.coupling Tb.ρA Tb.coercivity (Tb.stepParameters y).side Tb.n₀ where
  coupling_pos := by linarith [hD.a_ge]
  coercivity_pos := hD.cK_pos
  side_pos := (show Odd (Tb.stepParameters y).side from hD.L_odd).pos
  maxwell_le u n _ hn W B := (h₁ u n hn).1 W B
  maxwell_eq_response u n _ hn B := (h₁ u n hn).2 B
  maxwell_zero m _ A := h₃ Tb.coupling (Tb.stepParameters y).side m A
  coercive u n _ hn A := (h₂ u n hn).2.2 A
end Assembly
end GaussianChainCoordinates
theorem gaussianChainCoordinates_of_stepMinimum (h₁ : stepMinimumStatement) (h₂ : gradientMaxwellStatement)
    (h₃ : maxwellFormAtZeroStatement) : gaussianChainCoordinatesStatement := by
  intro a ha
  obtain ⟨L1, r1, C1, hr1, g1⟩ := h₁ a ha
  obtain ⟨L2, r2, C2, hr2, g2⟩ := h₂ a ha
  refine ⟨max L1 L2, fun c => min (r1 c) (r2 c), max C1 C2, fun c => lt_min (hr1 c) (hr2 c), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hCH hrt hC Kr hKr
  obtain ⟨y1, f1⟩ := g1 L hodd ((le_max_left _ _).trans hL) Tb hTa hTL hD hCS hCH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hC)
  obtain ⟨y2, f2⟩ := g2 L hodd ((le_max_right _ _).trans hL) Tb hTa hTL hD hCS hCH (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hC)
  refine ⟨max y1 y2, fun y hy hR hW g _ _ k _ _ _ R d _ => ?_⟩
  have F := GaussianChainCoordinates.chainHyps_of_parameters Tb y hD (f1 y ((le_max_left _ _).trans hy) hR hW)
    (f2 y ((le_max_right _ _).trans hy) hR hW) h₃
  refine ⟨fun _ => 3 / (2 * Tb.coercivity), 1, y, one_pos, le_rfl, fun S u d' hud => ?_⟩
  have hn : Tb.n₀ ≤ S.data.period (Tb.stepParameters y).side :=
    (Nat.le_mul_of_pos_left _ F.side_pos).trans S.side_le
  exact GaussianChainCoordinates.coordinates_of_hyps F u d' _ hn
end YangMills.Construction.MomentLaw
end
