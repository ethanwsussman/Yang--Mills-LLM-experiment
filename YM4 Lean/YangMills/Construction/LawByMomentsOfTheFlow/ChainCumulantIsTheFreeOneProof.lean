import YangMills.Construction.LawByMomentsOfTheFlow.ChainCumulantIsTheFreeOne
import YangMills.Construction.LawByMomentsOfTheFlow.ChainObeysTheFirstLevelProof
import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStep
import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOfTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.CumulantAcrossAGaussianStep
import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfGaussianSquaresProof
import YangMills.Construction.LawByMomentsOfTheFlow.FarLevelNearTheScaleProof
import YangMills.Construction.LawByMomentsOfTheFlow.GapOfTheSupportsFromAbove
import YangMills.Construction.LawByMomentsOfTheFlow.GradientsOfAStepAreFarApart
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheCompletedForms
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open CompletedForms TorusFields TorusPaths WeightedResponses LevelTestFunctions TorusLumps TestFunctions
namespace LevelCumulantProof
section Chains
variable {L : ℕ} [NeZero L]
private theorem levelChain_ext {s n : ℕ} {X Y : LevelChain L (s + 1) n}
    (h₁ : ∀ e (c : LevelBond L s (n * L)), X e (Sum.inl c) = Y e (Sum.inl c))
    (h₂ : ∀ e (b : TorusBond n), X e (Sum.inr b) = Y e (Sum.inr b)) : X = Y := by
  funext e
  funext (c : LevelBond L s (n * L) ⊕ TorusBond n)
  rcases c with c | b
  · exact h₁ e c
  · exact h₂ e b
private theorem truncateTop_self : ∀ (s n : ℕ) (X : LevelChain L s n), truncateTop s s n le_rfl X = X := by
  intro s
  induction s with
  | zero => intro n X; rfl
  | succ s ih =>
    intro n X
    refine levelChain_ext (fun e c => ?_) (fun e b => rfl)
    show truncateTop s s (n * L) _ (chainLower X) e c = X e (Sum.inl c)
    rw [ih]
    rfl
private theorem chainBottom_truncateTop (u : ℕ) : ∀ (d n : ℕ) (X : LevelChain L (u + d) n),
    chainBottom d n (truncateTop d (u + d) n (Nat.le_add_left d u) X) = chainTop u (fineSide L d n) (chainDescend u d n X) := by
  intro d
  induction d with
  | zero => intro n X; rfl
  | succ d ih =>
    intro n X
    exact ih (n * L) (chainLower X)
private theorem chainTop_extendChain (a ρA : ℝ) (u : ℕ) : ∀ (j n : ℕ) [NeZero n] (Z : LevelChain L j n)
    (η : StepFluctuation L u (fineSide L j n)), chainTop (j + 1) n (extendChain a ρA u j n Z η) = chainTop j n Z := by
  intro j
  cases j with
  | zero => intro n _ Z η; rfl
  | succ j => intro n _ Z η; rfl
private theorem levelPair_truncateTop : ∀ (j s n : ℕ) (h : j + 1 ≤ s) (X : LevelChain L s n),
    levelPair j (j + 1) n le_rfl (truncateTop (j + 1) s n h X) = levelPair j s n h X := by
  intro j
  induction j with
  | zero =>
    intro s n h X
    cases s with
    | zero => omega
    | succ s => rfl
  | succ j ih =>
    intro s n h X
    cases s with
    | zero => omega
    | succ s => exact ih s (n * L) (Nat.le_of_succ_le_succ h) (chainLower X)
private theorem levelPair_extendChain (a ρA : ℝ) (u : ℕ) : ∀ (j n : ℕ) [NeZero n] (Z : LevelChain L j n)
    (η : StepFluctuation L u (fineSide L j n)),
    levelPair j (j + 1) n le_rfl (extendChain a ρA u j n Z η) =
      (chainBottom j n Z, fun e b => pushColours a ρA L u (chainBottom j n Z) e b + extendFluctuation η e b) := by
  intro j
  induction j with
  | zero => intro n _ Z η; rfl
  | succ j ih =>
    intro n _ Z η
    exact ih (n * L) (chainLower Z) η
end Chains
section Measurability
variable {L : ℕ} [NeZero L]
private theorem measurable_chainLower (s n : ℕ) :
    Measurable (chainLower (L := L) (s := s) (n := n)) :=
  measurable_pi_iff.2 fun e => measurable_pi_iff.2 fun c =>
    (measurable_pi_apply (Sum.inl c : LevelBond L s (n * L) ⊕ TorusBond n)).comp (measurable_pi_apply e)
abbrev _root_.YangMills.SharedProofs.p17945 := @measurable_chainLower
private theorem measurable_chainTop : ∀ (s n : ℕ), Measurable (chainTop (L := L) s n)
  | 0, _ => measurable_id
  | s + 1, n => measurable_pi_iff.2 fun e => measurable_pi_iff.2 fun b =>
    (measurable_pi_apply (Sum.inr b : LevelBond L s (n * L) ⊕ TorusBond n)).comp (measurable_pi_apply e)
private theorem measurable_chainBottom : ∀ (s n : ℕ), Measurable (chainBottom (L := L) s n)
  | 0, _ => measurable_id
  | s + 1, n => (measurable_chainBottom s (n * L)).comp (measurable_chainLower s n)
private theorem measurable_levelChain_mk {Ω : Type} [MeasurableSpace Ω] {j n : ℕ} {F : Ω → LevelChain L (j + 1) n}
    (h₁ : ∀ e (c : LevelBond L j (n * L)), Measurable fun ω => F ω e (Sum.inl c))
    (h₂ : ∀ e (b : TorusBond n), Measurable fun ω => F ω e (Sum.inr b)) : Measurable F := by
  refine measurable_pi_iff.2 fun e => measurable_pi_iff.2 fun (c : LevelBond L j (n * L) ⊕ TorusBond n) => ?_
  rcases c with c | b
  · exact h₁ e c
  · exact h₂ e b
private theorem measurable_truncateTop : ∀ (j s n : ℕ) (h : j ≤ s), Measurable (truncateTop (L := L) j s n h)
  | 0, s, n, _ => measurable_chainTop s n
  | j + 1, 0, _, h => absurd h (by omega)
  | j + 1, s + 1, n, h => by
    refine measurable_levelChain_mk (fun e c => ?_) (fun e b => ?_)
    · have h1 := measurable_truncateTop j s (n * L) (Nat.le_of_succ_le_succ h)
      exact ((measurable_pi_apply c).comp ((measurable_pi_apply e).comp h1)).comp (measurable_chainLower s n)
    · exact (measurable_pi_apply b).comp ((measurable_pi_apply e).comp (measurable_chainTop (s + 1) n))
private theorem measurable_sumAlongWord {Ω : Type} [MeasurableSpace Ω] {m : ℕ} {F : Ω → TorusBond m → ℝ} (hF : Measurable F)
    (w : BondWord m) : Measurable fun ω => sumAlongWord (F ω) w := by
  induction w with
  | nil => simpa [sumAlongWord] using measurable_const
  | cons x r ih =>
    have e : ∀ ω, sumAlongWord (F ω) (x :: r) = (if x.2 then F ω x.1 else -F ω x.1) + sumAlongWord (F ω) r := by
      intro ω
      simp [sumAlongWord]
    simp only [e]
    refine Measurable.add ?_ ih
    by_cases h : x.2 = true
    · simp only [if_pos h]
      exact (measurable_pi_apply x.1).comp hF
    · simp only [if_neg h]
      exact ((measurable_pi_apply x.1).comp hF).neg
private theorem measurable_contourAverage {Ω : Type} [MeasurableSpace Ω] {n : ℕ} [NeZero n] {F : Ω → TorusBond (n * L) → ℝ}
    (hF : Measurable F) (c : TorusBond n) : Measurable fun ω => contourAverage L (F ω) c := by
  unfold contourAverage
  exact (Finset.measurable_fun_sum _ fun e _ => measurable_sumAlongWord hF _).const_mul _
private theorem measurable_chainDefect {s n : ℕ} [NeZero n] (e : Fin 3) (c : TorusBond n) :
    Measurable fun X : LevelChain L (s + 1) n => chainDefect X e c := by
  unfold chainDefect
  refine ((measurable_pi_apply c).comp ((measurable_pi_apply e).comp (measurable_chainTop (s + 1) n))).sub ?_
  exact measurable_contourAverage ((measurable_pi_apply e).comp ((measurable_chainTop s (n * L)).comp (measurable_chainLower s n))) c
private theorem measurable_colourEval {Ω : Type} [MeasurableSpace Ω] {n : ℕ} [NeZero n] (q : BondBilinear n) {F G : Ω → ColourForm n}
    (hF : Measurable F) (hG : Measurable G) : Measurable fun ω => colourEval q (F ω) (G ω) := by
  unfold colourEval bilinearEval
  refine Finset.measurable_fun_sum _ fun e _ => Finset.measurable_fun_sum _ fun b _ => Finset.measurable_fun_sum _ fun b' _ => ?_
  exact (((measurable_pi_apply b).comp ((measurable_pi_apply e).comp hF)).mul_const _).mul
    ((measurable_pi_apply b').comp ((measurable_pi_apply e).comp hG))
private theorem measurable_cumulativeScores (a : ℝ) (τ l : ℕ) (w : ∀ m : ℕ, PlaquetteWeight m) :
    ∀ (j n : ℕ) [NeZero n], Measurable (cumulativeScores (L := L) a τ l w j n)
  | 0, _, _ => measurable_const
  | j + 1, n, _ => by
    have h1 := (measurable_cumulativeScores a τ l w j (n * L)).comp (measurable_chainLower j n)
    show Measurable fun Z => cumulativeScores (L := L) a τ l w j (n * L) (chainLower Z) + _
    refine h1.add ?_
    split_ifs
    · refine (Finset.measurable_fun_sum _ fun c _ => ?_).const_mul _
      refine Measurable.const_mul (((Finset.measurable_fun_sum _ fun e _ => ?_).const_mul _).sub_const _) _
      exact (measurable_chainDefect e c).pow_const 2
    · exact measurable_const
end Measurability
section Scores
variable {L : ℕ} [NeZero L]
private theorem add_assoc_of {a b c x y : ℝ} (h : a = b + c) (hx : x = y) : a + x = b + (c + y) := by
  rw [h, hx, add_assoc]
private theorem cumulativeScores_self (a : ℝ) (τ : ℕ) (w : ∀ m : ℕ, PlaquetteWeight m) : ∀ (j n : ℕ) [NeZero n] (Z : LevelChain L j n),
    cumulativeScores a τ τ w j n Z = 0 := by
  intro j
  induction j with
  | zero => intro n _ Z; rfl
  | succ j ih =>
    intro n _ Z
    have h : ¬ τ + j + 1 ≤ τ := by omega
    simp only [cumulativeScores, ih, if_neg h, add_zero]
private theorem cumulativeScores_descend (a : ℝ) (τ : ℕ) (w : ∀ m : ℕ, PlaquetteWeight m) : ∀ (d n : ℕ) [NeZero n] (X : LevelChain L (τ + d) n),
    cumulativeScores a τ 0 w (τ + d) n X = cumulativeScores a τ 0 w τ (fineSide L d n) (chainDescend τ d n X) := by
  intro d
  induction d with
  | zero => intro n _ X; rfl
  | succ d ih =>
    intro n _ X
    have h : ¬ 0 + (τ + d) + 1 ≤ τ := by omega
    show cumulativeScores a τ 0 w ((τ + d) + 1) n X = _
    simp only [cumulativeScores, if_neg h, add_zero]
    exact ih (n * L) (chainLower X)
private theorem completedObservable_eq (a : ℝ) (τ : ℕ) (w : ∀ m : ℕ, PlaquetteWeight m) : ∀ (j n : ℕ) [NeZero n] (Y : LevelChain L j n), j ≤ τ →
    completedObservable a j n (w _) Y =
      (1 / 2) * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L j n))), w _ p * curlNorm (chainBottom j n Y) p ^ 2 +
        cumulativeScores a τ 0 w j n Y := by
  intro j
  induction j with
  | zero =>
    intro n _ Y _
    simp only [completedObservable, cumulativeScores, add_zero]
    rfl
  | succ j ih =>
    intro n _ Y hj
    have h : 0 + j + 1 ≤ τ := by omega
    simp only [completedObservable, cumulativeScores, if_pos h]
    rw [Nat.zero_add j]
    exact add_assoc_of (ih (n * L) (chainLower Y) (by omega)) rfl
end Scores
section LawTransfer
variable {k : ℕ}
private lemma jointCumulant_map {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ν : Measure Ω}
    {T : Ω → Ω'} (hT : Measurable T) {X : Fin k → Ω' → ℝ} (hX : ∀ i, Measurable (X i)) :
    jointCumulant (ν.map T) X = jointCumulant ν (fun i ω => X i (T ω)) := by apply _root_.YangMills.SharedProofs.p3362 <;> assumption
variable {V : Type} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]
private theorem map_eq_of_canonical {E : V → ℝ} {μ ν : Measure V} (hμ : IsCanonicalGaussian E μ) (hν : IsCanonicalGaussian E ν)
    {I : Type} [Fintype I] (f : I → V →ₗ[ℝ] ℝ) (hm : ∀ i, Measurable (f i)) (hf : ∀ i x, E x = 0 → f i x = 0) :
    μ.map (fun x => (WithLp.toLp 2 fun i => f i x : EuclideanSpace ℝ I)) =
      ν.map (fun x => (WithLp.toLp 2 fun i => f i x : EuclideanSpace ℝ I)) := by
  have := hμ.isProbabilityMeasure
  have := hν.isProbabilityMeasure
  have hF : Measurable (fun x => (WithLp.toLp 2 fun i => f i x : EuclideanSpace ℝ I)) := by
    have h1 : Measurable fun w : I → ℝ => (WithLp.toLp 2 w : EuclideanSpace ℝ I) := by fun_prop
    exact h1.comp (measurable_pi_lambda _ hm)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  let g : V →ₗ[ℝ] ℝ := ∑ i, t i • f i
  have hge : ∀ x, g x = ∑ i, t i * f i x := fun x => by simp [g, LinearMap.sum_apply]
  have hg : ∀ x, E x = 0 → g x = 0 := fun x hx => by
    rw [hge]
    exact Finset.sum_eq_zero fun i _ => by rw [hf i x hx, mul_zero]
  have hgm : Measurable g := by
    have : (g : V → ℝ) = fun x => ∑ i, t i * f i x := funext hge
    rw [this]
    exact Finset.measurable_fun_sum _ fun i _ => (hm i).const_mul _
  have key : ∀ ρ : Measure V, charFun (ρ.map fun x => (WithLp.toLp 2 fun i => f i x : EuclideanSpace ℝ I)) t =
      charFun (ρ.map g) 1 := by
    intro ρ
    rw [charFun_apply, charFun_apply, integral_map hF.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop)),
      integral_map hgm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e : inner ℝ (WithLp.toLp 2 fun i => f i x : EuclideanSpace ℝ I) t = inner ℝ (g x) (1 : ℝ) := by
      simp [PiLp.inner_apply, hge]
    simp only [e]
  rw [key, key, hμ.map_eq g hg, hν.map_eq g hg]
end LawTransfer
section Curls
variable {L : ℕ} [NeZero L]
private abbrev CurlIndex (m : ℕ) [NeZero m] : Type := Fin 3 × ↥(plaquettesIn (Finset.univ : Finset (TorusSite m)))
private def curlLinear {m : ℕ} [NeZero m] (x : CurlIndex m) : ColourForm m →ₗ[ℝ] ℝ where
  toFun Y := WeightedResponses.curl (Y x.1) x.2.1
  map_add' Y Y' := by
    simp only [WeightedResponses.curl, Pi.add_apply]
    ring
  map_smul' c Y := by
    simp only [WeightedResponses.curl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
private theorem measurable_curlLinear {m : ℕ} [NeZero m] (x : CurlIndex m) : Measurable (curlLinear x) := by
  show Measurable fun Y : ColourForm m => WeightedResponses.curl (Y x.1) x.2.1
  unfold WeightedResponses.curl
  fun_prop
private def curlVector {m : ℕ} [NeZero m] (Y : ColourForm m) : EuclideanSpace ℝ (CurlIndex m) :=
  WithLp.toLp 2 fun x => curlLinear x Y
private theorem measurable_curlVector {m : ℕ} [NeZero m] : Measurable (curlVector (m := m)) := by
  have h1 : Measurable fun w : CurlIndex m → ℝ => (WithLp.toLp 2 w : EuclideanSpace ℝ (CurlIndex m)) := by fun_prop
  exact h1.comp (measurable_pi_lambda _ measurable_curlLinear)
private def formOfCurls {m : ℕ} [NeZero m] (κ : TorusPlaquette m → TorusPlaquette m → ℝ) (v : EuclideanSpace ℝ (CurlIndex m)) : ℝ :=
  ∑ e : Fin 3, ∑ p : ↥(plaquettesIn (Finset.univ : Finset (TorusSite m))), ∑ p' : ↥(plaquettesIn (Finset.univ : Finset (TorusSite m))),
    κ p.1 p'.1 * v (e, p) * v (e, p')
private theorem measurable_formOfCurls {m : ℕ} [NeZero m] (κ : TorusPlaquette m → TorusPlaquette m → ℝ) : Measurable (formOfCurls κ) := by
  unfold formOfCurls
  refine Finset.measurable_fun_sum _ fun e _ => Finset.measurable_fun_sum _ fun p _ => Finset.measurable_fun_sum _ fun p' _ => ?_
  fun_prop
private theorem formOfCurls_eq {m : ℕ} [NeZero m] (κ : TorusPlaquette m → TorusPlaquette m → ℝ) (Y : ColourForm m) :
    formOfCurls κ (curlVector Y) = ∑ e : Fin 3, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), κ p p' * WeightedResponses.curl (Y e) p * WeightedResponses.curl (Y e) p' := by
  unfold formOfCurls
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_coe_sort (plaquettesIn (Finset.univ : Finset (TorusSite m)))
    (fun p => ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), κ p p' * WeightedResponses.curl (Y e) p * WeightedResponses.curl (Y e) p')]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_coe_sort (plaquettesIn (Finset.univ : Finset (TorusSite m)))
    (fun p' => κ p.1 p' * WeightedResponses.curl (Y e) p.1 * WeightedResponses.curl (Y e) p')]
  rfl
private theorem chainBottom_add : ∀ (s n : ℕ) (X Y : LevelChain L s n), chainBottom s n (X + Y) = chainBottom s n X + chainBottom s n Y
  | 0, _, _, _ => rfl
  | s + 1, n, X, Y => chainBottom_add s (n * L) (chainLower X) (chainLower Y)
private theorem chainBottom_smul : ∀ (s n : ℕ) (c : ℝ) (X : LevelChain L s n), chainBottom s n (c • X) = c • chainBottom s n X
  | 0, _, _, _ => rfl
  | s + 1, n, c, X => chainBottom_smul s (n * L) c (chainLower X)
private theorem sum_curlNorm_sq_le_levelEnergy {a : ℝ} (ha : 0 ≤ a) : ∀ (s n : ℕ) [NeZero n] (X : LevelChain L s n),
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L s n))), curlNorm (chainBottom s n X) p ^ 2 ≤ levelEnergy a s n X := by
  intro s
  induction s with
  | zero => intro n _ X; exact le_of_eq rfl
  | succ s ih =>
    intro n _ X
    refine (ih (n * L) (chainLower X)).trans ?_
    show _ ≤ levelEnergy a s (n * L) (chainLower X) + _
    have : 0 ≤ a * ∑ c : TorusBond n, ∑ e : Fin 3, chainDefect X e c ^ 2 :=
      mul_nonneg ha (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
end Curls
section AtAPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem add_add_of {a b c d x y : ℝ} (h : a + b = c + d) (hx : x = y) : a + (b + x) = (c + y) + d := by
  rw [hx]
  linarith
private theorem cumulativeScores_succ {L : ℕ} [NeZero L] (a : ℝ) (τ l : ℕ) (w : ∀ m : ℕ, PlaquetteWeight m) (j n : ℕ) [NeZero n]
    (Z : LevelChain L (j + 1) n) :
    cumulativeScores a τ l w (j + 1) n Z = cumulativeScores a τ l w j (n * L) (chainLower Z) +
      if l + j + 1 ≤ τ then
        a * ∑ c : TorusBond n, ResponseInTheExpansion.bondBlockMean L (l + j + 1) n (w _) c * ((1 / 2) * ∑ e : Fin 3, chainDefect Z e c ^ 2 - 3 / (2 * a))
      else 0 := rfl
private theorem chainDefect_extendChain {L : ℕ} [NeZero L] (a ρA : ℝ) (u j n : ℕ) [NeZero n] (Z : LevelChain L (j + 1) n)
    (η : StepFluctuation L u (fineSide L (j + 1) n)) (e : Fin 3) (c : TorusBond n) :
    chainDefect (extendChain a ρA u (j + 1) n Z η) e c = chainDefect Z e c := by
  unfold chainDefect
  have h1 : chainTop (j + 1 + 1) n (extendChain a ρA u (j + 1) n Z η) = chainTop (j + 1) n Z := chainTop_extendChain a ρA u (j + 1) n Z η
  have h2 : chainTop (j + 1) (n * L) (chainLower (extendChain a ρA u (j + 1) n Z η)) = chainTop j (n * L) (chainLower Z) :=
    chainTop_extendChain a ρA u j (n * L) (chainLower Z) η
  rw [h1, h2]
private theorem completedForm_extendChain (l : ℕ) (hl : l + 1 ≤ S.lastSeparated) (i : Fin Λ.k) :
    ∀ (j n : ℕ) [NeZero n] (Z : LevelChain Λ.stepParams.side j n)
    (η : StepFluctuation Λ.stepParams.side l (fineSide Λ.stepParams.side j n)),
    S.completedForm l (j + 1) n i (extendChain Λ.stepParams.coupling Λ.table.ρA l j n Z η) =
      cumulativeScores Λ.stepParams.coupling S.lastSeparated (l + 1) (S.weight i) j n Z +
        S.levelStepValue l (fineSide Λ.stepParams.side j n) i (chainBottom j n Z) (descendForm Λ l _ (chainBottom j n Z) η) := by
  intro j
  induction j with
  | zero =>
    intro n _ Z η
    have h : l + 0 + 1 ≤ S.lastSeparated := hl
    simp only [MomentPoint.completedForm, cumulativeScores, if_pos h, zero_add]
    rfl
  | succ j ih =>
    intro n _ Z η
    have hidx : l + (j + 1) + 1 = l + 1 + j + 1 := by omega
    have h := ih (n * Λ.stepParams.side) (chainLower Z) η
    simp only [MomentPoint.completedForm] at h ⊢
    rw [cumulativeScores_succ _ _ _ _ (j + 1) n, cumulativeScores_succ _ _ _ _ j n Z]
    refine add_add_of h ?_
    simp only [chainDefect_extendChain]
    rw [hidx]
private theorem completedForm_truncateTop (d n : ℕ) [NeZero n] (i : Fin Λ.k) (X : LevelChain Λ.stepParams.side (S.lastSeparated + d) n) :
    S.completedForm S.lastSeparated d n i (truncateTop d (S.lastSeparated + d) n (Nat.le_add_left d S.lastSeparated) X) = S.halfForm d n i X := by
  unfold MomentPoint.completedForm MomentPoint.halfForm
  rw [cumulativeScores_self, add_zero, chainBottom_truncateTop]
end AtAPoint
section EndsOfTheChain
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem bilinearEval_sum {n : ℕ} [NeZero n] {α : Type} (A : Finset α) (q : α → BondBilinear n) (X X' : TorusBond n → ℝ) :
    bilinearEval (fun b b' => ∑ y ∈ A, q y b b') X X' = ∑ y ∈ A, bilinearEval (q y) X X' := by apply _root_.YangMills.SharedProofs.p776 <;> assumption
private theorem stepWeight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem exists_isDecayingAbout (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n] (y : TorusSite n) (q : BondBilinear n) :
    ∃ sz : ℝ, 0 < sz ∧ IsDecayingAbout ℓ sz y q := by
  refine ⟨1 + ∑ b : TorusBond n, ∑ b' : TorusBond n, |q b b'| * ℓ.weight (tripleDiam y b b'), ?_, fun b b' => ?_⟩
  · have : 0 ≤ ∑ b : TorusBond n, ∑ b' : TorusBond n, |q b b'| * ℓ.weight (tripleDiam y b b') :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (stepWeight_pos _ _).le
    linarith
  · rw [le_div_iff₀ (stepWeight_pos ℓ _)]
    have h1 : |q b b'| * ℓ.weight (tripleDiam y b b') ≤ ∑ b' : TorusBond n, |q b b'| * ℓ.weight (tripleDiam y b b') :=
      Finset.single_le_sum (f := fun b' => |q b b'| * ℓ.weight (tripleDiam y b b'))
        (fun _ _ => mul_nonneg (abs_nonneg _) (stepWeight_pos _ _).le) (Finset.mem_univ b')
    have h2 : ∑ b' : TorusBond n, |q b b'| * ℓ.weight (tripleDiam y b b') ≤
        ∑ b : TorusBond n, ∑ b' : TorusBond n, |q b b'| * ℓ.weight (tripleDiam y b b') :=
      Finset.single_le_sum (f := fun b => ∑ b' : TorusBond n, |q b b'| * ℓ.weight (tripleDiam y b b'))
        (fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (stepWeight_pos _ _).le) (Finset.mem_univ b)
    linarith
private theorem supportForm_eq_formOfCurls (u n : ℕ) [NeZero n] (i : Fin Λ.k)
    (hF : ∀ (y : TorusSite n) (sz : ℝ) (q : BondBilinear n), 0 < sz → IsDecayingAbout Λ.stepParams sz y q → AnnihilatesClosedForms q →
      ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ, ∀ X X' : TorusBond n → ℝ, bilinearEval q X X' =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), κ p p' * WeightedResponses.curl X p * WeightedResponses.curl X' p')
    (hK : ∀ y : TorusSite n, AnnihilatesClosedForms (classicalQuadratic S.tower S.resp u n (S.weight i _) y)) :
    ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ, ∀ Y : ColourForm n,
      colourEval (S.supportForm u n i) Y Y = formOfCurls κ (curlVector Y) := by
  have hy : ∀ y : TorusSite n, ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ, ∀ X X' : TorusBond n → ℝ,
      bilinearEval (classicalQuadratic S.tower S.resp u n (S.weight i _) y) X X' =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), κ p p' * WeightedResponses.curl X p * WeightedResponses.curl X' p' := by
    intro y
    obtain ⟨sz, h1, h2⟩ := exists_isDecayingAbout Λ.stepParams y (classicalQuadratic S.tower S.resp u n (S.weight i _) y)
    exact hF y sz _ h1 h2 (hK y)
  choose κ hκ using hy
  refine ⟨fun p p' => ∑ y ∈ S.supportAt u n i, κ y p p', fun Y => ?_⟩
  rw [formOfCurls_eq]
  unfold colourEval
  refine Finset.sum_congr rfl fun e _ => ?_
  have e1 : bilinearEval (S.supportForm u n i) (Y e) (Y e) =
      ∑ y ∈ S.supportAt u n i, bilinearEval (classicalQuadratic S.tower S.resp u n (S.weight i _) y) (Y e) (Y e) :=
    bilinearEval_sum _ _ _ _
  rw [e1]
  simp only [hκ, Finset.sum_mul]
  exact (Finset.sum_comm).trans (Finset.sum_congr rfl fun p _ => Finset.sum_comm)
private theorem measurable_chainDescend {L : ℕ} [NeZero L] (u : ℕ) : ∀ (d n : ℕ), Measurable (chainDescend (L := L) u d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_chainDescend u d (n * L)).comp (measurable_chainLower (u + d) n)
private theorem halfForm_cumulant_eq (d n : ℕ) [NeZero n] {μ μ₀ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) n)}
    (h₁ : IsCanonicalGaussian (kineticForm Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated)
      (μ.map fun X => chainTop S.lastSeparated (fineSide Λ.stepParams.side d n) (chainDescend S.lastSeparated d n X)))
    (h₂ : IsCanonicalGaussian (kineticForm Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated)
      (μ₀.map fun X => chainTop S.lastSeparated (fineSide Λ.stepParams.side d n) (chainDescend S.lastSeparated d n X)))
    (hker : ∀ (Y : ColourForm (fineSide Λ.stepParams.side d n)),
      kineticForm Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated Y = 0 → ∀ x, curlLinear x Y = 0)
    (hκ : ∀ i : Fin Λ.k, ∃ κ : TorusPlaquette (fineSide Λ.stepParams.side d n) → TorusPlaquette (fineSide Λ.stepParams.side d n) → ℝ,
      ∀ Y : ColourForm (fineSide Λ.stepParams.side d n),
      colourEval (S.supportForm S.lastSeparated (fineSide Λ.stepParams.side d n) i) Y Y = formOfCurls κ (curlVector Y)) :
    jointCumulant μ (fun i => S.halfForm d n i) = jointCumulant μ₀ (fun i => S.halfForm d n i) := by
  choose κ hκ using hκ
  have hlev : Measurable fun X : LevelChain Λ.stepParams.side (S.lastSeparated + d) n =>
      chainTop S.lastSeparated (fineSide Λ.stepParams.side d n) (chainDescend S.lastSeparated d n X) :=
    (measurable_chainTop _ _).comp (measurable_chainDescend _ _ _)
  have hΨ : ∀ i, Measurable fun v => (1 / 2 : ℝ) * formOfCurls (κ i) v := fun i => (measurable_formOfCurls _).const_mul _
  have e : (fun i => S.halfForm d n i) = fun i X => (1 / 2 : ℝ) *
      formOfCurls (κ i) (curlVector (chainTop S.lastSeparated (fineSide Λ.stepParams.side d n) (chainDescend S.lastSeparated d n X))) := by
    funext i X
    rw [MomentPoint.halfForm, hκ]
  have key : ∀ ν : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) n),
      jointCumulant ν (fun i => S.halfForm d n i) =
        jointCumulant (((ν.map fun X => chainTop S.lastSeparated (fineSide Λ.stepParams.side d n)
          (chainDescend S.lastSeparated d n X))).map curlVector)
          (fun i v => (1 / 2 : ℝ) * formOfCurls (κ i) v) := by
    intro ν
    rw [e, Measure.map_map measurable_curlVector hlev, jointCumulant_map (measurable_curlVector.comp hlev) hΨ]
    rfl
  rw [key, key]
  have hl := map_eq_of_canonical h₁ h₂ (fun x : CurlIndex (fineSide Λ.stepParams.side d n) => curlLinear x) measurable_curlLinear
    (fun x Y hY => hker Y hY x)
  have e2 : (curlVector : ColourForm (fineSide Λ.stepParams.side d n) → _) = fun Y => WithLp.toLp 2 fun x => curlLinear x Y := rfl
  rw [e2, hl]
private def bottomLinear {L : ℕ} [NeZero L] (s n : ℕ) : LevelChain L s n →ₗ[ℝ] ColourForm (fineSide L s n) where
  toFun := chainBottom s n
  map_add' := chainBottom_add s n
  map_smul' := chainBottom_smul s n
private def bottomOfCurls {m : ℕ} [NeZero m] (h : PlaquetteWeight m) (v : EuclideanSpace ℝ (CurlIndex m)) : ℝ :=
  (1 / 2) * ∑ p : ↥(plaquettesIn (Finset.univ : Finset (TorusSite m))), h p.1 * ∑ e : Fin 3, v (e, p) ^ 2
private theorem measurable_bottomOfCurls {m : ℕ} [NeZero m] (h : PlaquetteWeight m) : Measurable (bottomOfCurls h) := by
  unfold bottomOfCurls
  refine (Finset.measurable_fun_sum _ fun p _ => (Finset.measurable_fun_sum _ fun e _ => ?_).const_mul _).const_mul _
  fun_prop
private theorem curlNorm_sq {n : ℕ} [NeZero n] (X : ColourForm n) (p : TorusPlaquette n) :
    curlNorm X p ^ 2 = ∑ e : Fin 3, WeightedResponses.curl (X e) p ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
private theorem bottomOfCurls_eq {m : ℕ} [NeZero m] (h : PlaquetteWeight m) (Y : ColourForm m) :
    bottomOfCurls h (curlVector Y) = (1 / 2) * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), h p * curlNorm Y p ^ 2 := by
  unfold bottomOfCurls
  congr 1
  rw [← Finset.sum_coe_sort (plaquettesIn (Finset.univ : Finset (TorusSite m))) (fun p => h p * curlNorm Y p ^ 2)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [curlNorm_sq]
  rfl
private theorem observableAt_cumulant_eq {a : ℝ} (ha : 0 < a) (s n : ℕ) [NeZero n] {μ μ₀ : Measure (LevelChain Λ.stepParams.side s n)}
    (h₁ : IsCanonicalGaussian (levelEnergy a s n) μ) (h₂ : IsCanonicalGaussian (levelEnergy a s n) μ₀) :
    jointCumulant μ (fun i => S.observableAt s n i) = jointCumulant μ₀ (fun i => S.observableAt s n i) := by
  have hb : Measurable (chainBottom (L := Λ.stepParams.side) s n) := measurable_chainBottom s n
  have hΨ : ∀ i : Fin Λ.k, Measurable (bottomOfCurls (S.weight i (fineSide Λ.stepParams.side s n))) := fun i => measurable_bottomOfCurls _
  have e : (fun i => S.observableAt s n i) = fun i X =>
      bottomOfCurls (S.weight i (fineSide Λ.stepParams.side s n)) (curlVector (chainBottom s n X)) := by
    funext i X
    rw [bottomOfCurls_eq]
    rfl
  have key : ∀ ν : Measure (LevelChain Λ.stepParams.side s n), jointCumulant ν (fun i => S.observableAt s n i) =
      jointCumulant (ν.map fun X => curlVector (chainBottom s n X))
        (fun i v => bottomOfCurls (S.weight i (fineSide Λ.stepParams.side s n)) v) := by
    intro ν
    rw [e]
    exact (jointCumulant_map (measurable_curlVector.comp hb) hΨ).symm
  rw [key, key]
  have hker : ∀ (x : CurlIndex (fineSide Λ.stepParams.side s n)) (X : LevelChain Λ.stepParams.side s n), levelEnergy a s n X = 0 →
      (curlLinear x ∘ₗ bottomLinear s n) X = 0 := by
    intro x X hX
    have h1 := sum_curlNorm_sq_le_levelEnergy ha.le s n X
    rw [hX] at h1
    have h2 : curlNorm (chainBottom s n X) x.2.1 ^ 2 ≤ 0 :=
      (Finset.single_le_sum (f := fun p => curlNorm (chainBottom s n X) p ^ 2) (fun _ _ => sq_nonneg _) x.2.2).trans h1
    rw [curlNorm_sq] at h2
    have h3 : WeightedResponses.curl (chainBottom s n X x.1) x.2.1 ^ 2 ≤ 0 :=
      (Finset.single_le_sum (f := fun e => WeightedResponses.curl (chainBottom s n X e) x.2.1 ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ x.1)).trans h2
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h3 (sq_nonneg _))
  have hl := map_eq_of_canonical h₁ h₂ (fun x : CurlIndex (fineSide Λ.stepParams.side s n) => curlLinear x ∘ₗ bottomLinear s n)
    (fun x => (measurable_curlLinear x).comp hb) hker
  exact congrArg (fun ν => jointCumulant ν (fun i v => bottomOfCurls (S.weight i (fineSide Λ.stepParams.side s n)) v)) hl
end EndsOfTheChain
section OneStep
variable {L : ℕ} [NeZero L]
private theorem measurable_extendFluctuation {u n : ℕ} [NeZero n] (e : Fin 3) (b : TorusBond (n * L)) :
    Measurable fun η : StepFluctuation L u n => extendFluctuation η e b := by
  unfold extendFluctuation extendChart
  refine Finset.measurable_fun_sum _ fun b' _ => ?_
  split_ifs
  · fun_prop
  · exact measurable_const
private theorem measurable_pushColours (a ρA : ℝ) (u n : ℕ) [NeZero n] (e : Fin 3) (b : TorusBond (n * L)) :
    Measurable fun X : ColourForm n => pushColours a ρA L u X e b := by
  unfold pushColours WeightedResponses.responseMap
  refine Finset.measurable_fun_sum _ fun c _ => ?_
  have h : Measurable fun X : ColourForm n => X e c := by fun_prop
  exact h.const_mul _
private theorem measurable_extendChain (a ρA : ℝ) (u : ℕ) : ∀ (j n : ℕ) [NeZero n],
    Measurable fun w : LevelChain L j n × StepFluctuation L u (fineSide L j n) => extendChain a ρA u j n w.1 w.2
  | 0, n, _ => by
    refine measurable_levelChain_mk (fun e b => ?_) (fun e b => ?_)
    · exact ((measurable_pushColours a ρA u n e b).comp measurable_fst).add ((measurable_extendFluctuation e b).comp measurable_snd)
    · exact (measurable_pi_apply b).comp ((measurable_pi_apply e).comp measurable_fst)
  | j + 1, n, _ => by
    refine measurable_levelChain_mk (fun e c => ?_) (fun e b => ?_)
    · have h1 := measurable_extendChain a ρA u j (n * L)
      have h2 : Measurable fun w : LevelChain L (j + 1) n × StepFluctuation L u (fineSide L (j + 1) n) =>
          ((chainLower w.1, w.2) : LevelChain L j (n * L) × StepFluctuation L u (fineSide L j (n * L))) :=
        ((measurable_chainLower j n).comp measurable_fst).prodMk measurable_snd
      exact (measurable_pi_apply c).comp ((measurable_pi_apply e).comp (h1.comp h2))
    · exact (measurable_pi_apply b).comp ((measurable_pi_apply e).comp ((measurable_chainTop (j + 1) n).comp measurable_fst))
private theorem measurable_levelPair : ∀ (d s n : ℕ) (h : d + 1 ≤ s), Measurable (levelPair (L := L) d s n h)
  | _, 0, _, h => absurd h (by omega)
  | 0, s + 1, n, _ => (measurable_chainTop (s + 1) n).prodMk ((measurable_chainTop s (n * L)).comp (measurable_chainLower s n))
  | d + 1, s + 1, n, h => (measurable_levelPair d s (n * L) (Nat.le_of_succ_le_succ h)).comp (measurable_chainLower s n)
end OneStep
section StepAtAPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem measurable_completedForm (l j n : ℕ) [NeZero n] (i : Fin Λ.k) : Measurable (S.completedForm l j n i) := by
  unfold MomentPoint.completedForm
  exact ((measurable_colourEval _ (measurable_chainBottom j n) (measurable_chainBottom j n)).const_mul _).add
    (measurable_cumulativeScores _ _ _ _ _ _)
private theorem measurable_levelStepGradient {Ω : Type} [MeasurableSpace Ω] (l m : ℕ) [NeZero m] (i : Fin Λ.k)
    {F : Ω → ColourForm m} {G : Ω → ColourForm (m * Λ.stepParams.side)} (hF : Measurable F) (hG : Measurable G)
    (b : Fin 3 × ChartBondIndex Λ.stepParams.side l m) :
    Measurable fun ω => S.levelStepGradient l m i (F ω) (G ω) b := by
  unfold MomentPoint.levelStepGradient
  refine Measurable.sub (((measurable_colourEval _ hG measurable_const).add (measurable_colourEval _ measurable_const hG)).const_mul _) ?_
  refine (Finset.measurable_fun_sum _ fun c _ => (Finset.measurable_fun_sum _ fun e _ => ?_).const_mul _).const_mul _
  refine Measurable.mul_const (((measurable_pi_apply c).comp ((measurable_pi_apply e).comp hF)).sub ?_) _
  exact measurable_contourAverage ((measurable_pi_apply e).comp hG) c
private theorem cumulant_step_bound (Cs : ℝ)
    (hC : ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
      (G : Matrix ι ι ℝ) (S : Fin Λ.k → Matrix ι ι ℝ) (W : Fin Λ.k → Ω → ℝ) (l : Fin Λ.k → Ω → ι → ℝ) (c : Fin Λ.k → ℝ)
      (w : Fin Λ.k → ι → ℝ) (A ε : ℝ),
      G.PosSemidef → (∀ i, (S i).IsSymm) → 1 ≤ A → (∀ i b, 0 < w i b) →
      (∀ i, Measurable (W i)) → (∀ i b, Measurable fun ξ => l i ξ b) →
      (∀ i, Integrable (fun ξ => |W i ξ| ^ Λ.k) ρ ∧ ∫ ξ, |W i ξ| ^ Λ.k ∂ρ ≤ A ^ Λ.k) →
      (∀ i, Integrable (fun x => |gaussianStepQuadratic (S i) (W i) (l i) (c i) x| ^ Λ.k) (ρ.prod (multivariateGaussian 0 G)) ∧
        ∫ x, |gaussianStepQuadratic (S i) (W i) (l i) (c i) x| ^ Λ.k ∂(ρ.prod (multivariateGaussian 0 G)) ≤ A ^ Λ.k) →
      (∀ i b, Integrable (fun x => |gaussianStepGradient (S i) (l i) b x| ^ Λ.k) (ρ.prod (multivariateGaussian 0 G)) ∧
        ∫ x, |gaussianStepGradient (S i) (l i) b x| ^ Λ.k ∂(ρ.prod (multivariateGaussian 0 G)) ≤ w i b ^ Λ.k) →
      (∀ i j, i ≠ j → ∑ b, ∑ b', w i b * |G b b'| * w j b' ≤ ε) →
      |jointCumulant (ρ.prod (multivariateGaussian 0 G)) (fun i => gaussianStepQuadratic (S i) (W i) (l i) (c i)) -
        jointCumulant ρ W| ≤ Cs * A ^ Λ.k * ε)
    (s n : ℕ) [NeZero n] (μ₀ : Measure (LevelChain Λ.stepParams.side s n)) [IsProbabilityMeasure μ₀]
    (j l : ℕ) (hj : j + 1 ≤ s) (hlt : l < S.lastSeparated)
    (hPSD : (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 (l) (fineSide Λ.stepParams.side j n)).PosSemidef)
    (hbuilt : μ₀.map (truncateTop (j + 1) s n hj) =
        ((μ₀.map (truncateTop j s n (Nat.le_of_succ_le hj))).prod
          (fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (l) (fineSide Λ.stepParams.side j n))).map
          fun w => extendChain Λ.stepParams.coupling Λ.table.ρA (l) j n w.1 w.2)
    (hX2 : ∀ i : Fin Λ.k, ∃ (Sm : Matrix (Fin 3 × ChartBondIndex Λ.stepParams.side (l) (fineSide Λ.stepParams.side j n))
        (Fin 3 × ChartBondIndex Λ.stepParams.side (l) (fineSide Λ.stepParams.side j n)) ℝ)
      (lin : ColourForm (fineSide Λ.stepParams.side j n) → Fin 3 × ChartBondIndex Λ.stepParams.side (l) (fineSide Λ.stepParams.side j n) → ℝ)
      (c₀ : ℝ),
      Sm.IsSymm ∧ (∀ b, Measurable fun Z => lin Z b) ∧
      ∀ (Z : ColourForm (fineSide Λ.stepParams.side j n)) (η : StepFluctuation Λ.stepParams.side (l) (fineSide Λ.stepParams.side j n)),
        S.levelStepValue (l) (fineSide Λ.stepParams.side j n) i Z (descendForm Λ (l) (fineSide Λ.stepParams.side j n) Z η) =
          (1 / 2) * colourEval (S.supportForm (l + 1) (fineSide Λ.stepParams.side j n) i) Z Z + c₀ + ∑ b, lin Z b * η b +
            (1 / 2) * ∑ b, ∑ b', Sm b b' * η b * η b' ∧
        ∀ b, lin Z b + ∑ b', Sm b b' * η b' = S.levelStepGradient (l) (fineSide Λ.stepParams.side j n) i Z
          (descendForm Λ (l) (fineSide Λ.stepParams.side j n) Z η) b)
    (A ε : ℝ) (hA : 1 ≤ A)
    (hM₁ : ∀ i : Fin Λ.k, Integrable (fun X => |S.completedForm (l) (j + 1) n i (truncateTop (j + 1) s n hj X)| ^ Λ.k) μ₀ ∧
      ∫ X, |S.completedForm (l) (j + 1) n i (truncateTop (j + 1) s n hj X)| ^ Λ.k ∂μ₀ ≤ A ^ Λ.k)
    (hM₀ : ∀ i : Fin Λ.k,
      Integrable (fun X => |S.completedForm (l + 1) j n i (truncateTop j s n (Nat.le_of_succ_le hj) X)| ^ Λ.k) μ₀ ∧
      ∫ X, |S.completedForm (l + 1) j n i (truncateTop j s n (Nat.le_of_succ_le hj) X)| ^ Λ.k ∂μ₀ ≤ A ^ Λ.k)
    (w : Fin Λ.k → Fin 3 × ChartBondIndex Λ.stepParams.side (l) (fineSide Λ.stepParams.side j n) → ℝ) (hw : ∀ i b, 0 < w i b)
    (hv : ∀ i b, Integrable (fun X => |S.levelStepGradient (l) (fineSide Λ.stepParams.side j n) i
            (levelPair j s n hj X).1 (levelPair j s n hj X).2 b| ^ Λ.k) μ₀ ∧
          ∫ X, |S.levelStepGradient (l) (fineSide Λ.stepParams.side j n) i
            (levelPair j s n hj X).1 (levelPair j s n hj X).2 b| ^ Λ.k ∂μ₀ ≤ w i b ^ Λ.k)
    (hε : ∀ i i', i ≠ i' → ∑ b, ∑ b', w i b *
            |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 (l) (fineSide Λ.stepParams.side j n) b b'| * w i' b' ≤ ε) :
    |jointCumulant (μ₀.map (truncateTop (j + 1) s n hj)) (fun i => S.completedForm (l) (j + 1) n i) -
      jointCumulant (μ₀.map (truncateTop j s n (Nat.le_of_succ_le hj))) (fun i => S.completedForm (l + 1) j n i)| ≤
      Cs * A ^ Λ.k * ε := by
  have hρp : IsProbabilityMeasure (μ₀.map (truncateTop j s n (Nat.le_of_succ_le hj))) :=
    Measure.isProbabilityMeasure_map (measurable_truncateTop _ _ _ _).aemeasurable
  have hmt0 := measurable_truncateTop (L := Λ.stepParams.side) j s n (Nat.le_of_succ_le hj)
  have hmt1 := measurable_truncateTop (L := Λ.stepParams.side) (j + 1) s n hj
  choose Sm lin c₀ hsym hlin hval using hX2
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = μ₀.map (truncateTop j s n (Nat.le_of_succ_le hj)) := ⟨_, rfl⟩
  rw [← hρ] at hbuilt hρp ⊢
  have hγ : fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 l (fineSide Λ.stepParams.side j n) =
      multivariateGaussian 0 (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 l (fineSide Λ.stepParams.side j n)) := rfl
  rw [hγ] at hbuilt
  obtain ⟨γ, hγ'⟩ : ∃ γ, γ = multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin 3 × ChartBondIndex Λ.stepParams.side l (fineSide Λ.stepParams.side j n)))
      (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 l (fineSide Λ.stepParams.side j n)) := ⟨_, rfl⟩
  have hgm := measurable_extendChain (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA l j n
  have hlt' : l + 1 ≤ S.lastSeparated := hlt
  have hΦ : ∀ i (x : LevelChain Λ.stepParams.side j n × StepFluctuation Λ.stepParams.side l (fineSide Λ.stepParams.side j n)),
      S.completedForm l (j + 1) n i (extendChain Λ.stepParams.coupling Λ.table.ρA l j n x.1 x.2) =
        gaussianStepQuadratic (Sm i) (S.completedForm (l + 1) j n i) (fun Z b => lin i (chainBottom j n Z) b) (c₀ i) x := by
    intro i x
    rw [completedForm_extendChain S l hlt' i j n x.1 x.2, (hval i (chainBottom j n x.1) x.2).1]
    simp only [gaussianStepQuadratic, MomentPoint.completedForm]
    ring
  have hG : ∀ i b (x : LevelChain Λ.stepParams.side j n × StepFluctuation Λ.stepParams.side l (fineSide Λ.stepParams.side j n)),
      gaussianStepGradient (Sm i) (fun Z b => lin i (chainBottom j n Z) b) b x =
        S.levelStepGradient l (fineSide Λ.stepParams.side j n) i
          (levelPair j (j + 1) n le_rfl (extendChain Λ.stepParams.coupling Λ.table.ρA l j n x.1 x.2)).1
          (levelPair j (j + 1) n le_rfl (extendChain Λ.stepParams.coupling Λ.table.ρA l j n x.1 x.2)).2 b := by
    intro i b x
    rw [levelPair_extendChain]
    exact (hval i (chainBottom j n x.1) x.2).2 b
  have tr : ∀ f : LevelChain Λ.stepParams.side (j + 1) n → ℝ, Measurable f →
      (Integrable (fun X => f (truncateTop (j + 1) s n hj X)) μ₀ →
        Integrable (fun x => f (extendChain Λ.stepParams.coupling Λ.table.ρA l j n x.1 x.2)) (ρ.prod γ)) ∧
      ∫ x, f (extendChain Λ.stepParams.coupling Λ.table.ρA l j n x.1 x.2) ∂(ρ.prod γ) =
        ∫ X, f (truncateTop (j + 1) s n hj X) ∂μ₀ := by
    intro f hf
    rw [hγ']
    refine ⟨fun h => ?_, ?_⟩
    · have h1 : Integrable f (μ₀.map (truncateTop (j + 1) s n hj)) :=
        (integrable_map_measure hf.aestronglyMeasurable hmt1.aemeasurable).2 h
      rw [hbuilt] at h1
      exact (integrable_map_measure hf.aestronglyMeasurable hgm.aemeasurable).1 h1
    · rw [← integral_map hgm.aemeasurable hf.aestronglyMeasurable, ← hbuilt,
        integral_map hmt1.aemeasurable hf.aestronglyMeasurable]
  have hmY : ∀ i, Measurable fun X => |S.completedForm l (j + 1) n i X| ^ Λ.k := fun i =>
    ((measurable_completedForm S l (j + 1) n i).abs).pow_const _
  have hmY0 : ∀ i, Measurable fun X => |S.completedForm (l + 1) j n i X| ^ Λ.k := fun i =>
    ((measurable_completedForm S (l + 1) j n i).abs).pow_const _
  have hmp : ∀ i b, Measurable fun X : LevelChain Λ.stepParams.side (j + 1) n => |S.levelStepGradient l (fineSide Λ.stepParams.side j n) i
      (levelPair j (j + 1) n le_rfl X).1 (levelPair j (j + 1) n le_rfl X).2 b| ^ Λ.k := fun i b =>
    ((measurable_levelStepGradient S l _ i (measurable_fst.comp (measurable_levelPair j (j + 1) n le_rfl))
      (measurable_snd.comp (measurable_levelPair j (j + 1) n le_rfl)) b).abs).pow_const _
  have hPΦ : ∀ i, Integrable (fun x => |gaussianStepQuadratic (Sm i) (S.completedForm (l + 1) j n i)
        (fun Z b => lin i (chainBottom j n Z) b) (c₀ i) x| ^ Λ.k) (ρ.prod γ) ∧
      ∫ x, |gaussianStepQuadratic (Sm i) (S.completedForm (l + 1) j n i)
        (fun Z b => lin i (chainBottom j n Z) b) (c₀ i) x| ^ Λ.k ∂(ρ.prod γ) ≤ A ^ Λ.k := by
    intro i
    obtain ⟨h1, h2⟩ := tr _ (hmY i)
    simp only [hΦ] at h1 h2
    exact ⟨h1 (hM₁ i).1, h2.le.trans (hM₁ i).2⟩
  have hPv : ∀ i b, Integrable (fun x => |gaussianStepGradient (Sm i) (fun Z b => lin i (chainBottom j n Z) b) b x| ^ Λ.k) (ρ.prod γ) ∧
      ∫ x, |gaussianStepGradient (Sm i) (fun Z b => lin i (chainBottom j n Z) b) b x| ^ Λ.k ∂(ρ.prod γ) ≤ w i b ^ Λ.k := by
    intro i b
    obtain ⟨h1, h2⟩ := tr _ (hmp i b)
    simp only [← hG, levelPair_truncateTop] at h1 h2
    exact ⟨h1 (hv i b).1, h2.le.trans (hv i b).2⟩
  have hPW : ∀ i, Integrable (fun Z => |S.completedForm (l + 1) j n i Z| ^ Λ.k) ρ ∧
      ∫ Z, |S.completedForm (l + 1) j n i Z| ^ Λ.k ∂ρ ≤ A ^ Λ.k := by
    intro i
    rw [hρ]
    refine ⟨(integrable_map_measure (hmY0 i).aestronglyMeasurable hmt0.aemeasurable).2 (hM₀ i).1, ?_⟩
    rw [integral_map hmt0.aemeasurable (hmY0 i).aestronglyMeasurable]
    exact (hM₀ i).2
  have hlm : ∀ i b, Measurable fun Z => lin i (chainBottom j n Z) b := fun i b =>
    (hlin i b).comp (measurable_chainBottom j n)
  rw [hγ'] at hPΦ hPv
  have hmain := hC (LevelChain Λ.stepParams.side j n) (Fin 3 × ChartBondIndex Λ.stepParams.side l (fineSide Λ.stepParams.side j n)) ρ
    (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 l (fineSide Λ.stepParams.side j n)) Sm
    (fun i => S.completedForm (l + 1) j n i)
    (fun i Z b => lin i (chainBottom j n Z) b) c₀ w A ε hPSD hsym hA hw (fun i => measurable_completedForm S _ _ _ i) hlm hPW hPΦ hPv hε
  rw [hbuilt, jointCumulant_map hgm (fun i => measurable_completedForm S _ _ _ i)]
  simp only [hΦ]
  exact hmain
end StepAtAPoint
section RealBounds
private theorem pow_mul_exp_neg_le (N : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x ^ N * Real.exp (-(c * x)) ≤ (N.factorial : ℝ) / c ^ N := by
  have h := Real.pow_div_factorial_le_exp (c * x) (by positivity) N
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by positivity
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (pow_pos hc N)]
  calc x ^ N * c ^ N = (c * x) ^ N := by rw [mul_pow]; ring
    _ ≤ Real.exp (c * x) * (N.factorial : ℝ) := h
    _ = _ := by ring
private theorem sum_geometric_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (t : ℕ) : ∑ i ∈ Finset.range t, q ^ i ≤ (1 - q)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.sum_range_geometric_le <;> assumption
private theorem exists_sum_levels_le (Lr : ℝ) (hL : 2 ≤ Lr) (c D : ℝ) (hc : 0 < c) (hD : 0 ≤ D) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s' t : ℕ, t ≤ s' → ∑ l ∈ Finset.range t, D * (Lr ^ (s' - l)) ^ N * Real.exp (-(c * Lr ^ (s' - l))) ≤
      C * Real.exp (-(c / 4 * Lr ^ (s' + 1 - t))) := by
  obtain ⟨q, hq⟩ : ∃ q, q = Real.exp (-(c / 4)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := hq ▸ (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    linarith
  obtain ⟨B, hB⟩ : ∃ B, B = (N.factorial : ℝ) / (c / 2) ^ N := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨D * B * (1 - q)⁻¹, by positivity, fun s' t ht => ?_⟩
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(c / 4 * Lr ^ (s' + 1 - t))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := hE ▸ (Real.exp_pos _).le
  have hterm : ∀ l ∈ Finset.range t, D * (Lr ^ (s' - l)) ^ N * Real.exp (-(c * Lr ^ (s' - l))) ≤
      D * B * E * q ^ (t - 1 - l) := by
    intro l hl
    have hlt := Finset.mem_range.1 hl
    obtain ⟨x, hx⟩ : ∃ x, x = Lr ^ (s' - l) := ⟨_, rfl⟩
    have hL1 : 1 ≤ Lr := by linarith
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    have hxe : Lr ^ (s' + 1 - t) ≤ x := by
      rw [hx]
      exact pow_le_pow_right₀ hL1 (by omega)
    have hxn : ((s' - l : ℕ) : ℝ) ≤ x := by
      rw [hx]
      calc ((s' - l : ℕ) : ℝ) ≤ (2 : ℝ) ^ (s' - l) := by exact_mod_cast (Nat.lt_two_pow_self).le
        _ ≤ Lr ^ (s' - l) := pow_le_pow_left₀ (by norm_num) hL _
    rw [← hx]
    have e1 : Real.exp (-(c * x)) = Real.exp (-(c / 2 * x)) * Real.exp (-(c / 4 * x)) * Real.exp (-(c / 4 * x)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have e2 : x ^ N * Real.exp (-(c / 2 * x)) ≤ B := hB ▸ pow_mul_exp_neg_le N (by positivity) hx0
    have e3 : Real.exp (-(c / 4 * x)) ≤ E := by
      rw [hE]
      refine Real.exp_le_exp.2 ?_
      have : c / 4 * Lr ^ (s' + 1 - t) ≤ c / 4 * x := mul_le_mul_of_nonneg_left hxe (by positivity)
      linarith
    have e4 : Real.exp (-(c / 4 * x)) ≤ q ^ (t - 1 - l) := by
      have h5 : q ^ (t - 1 - l) = Real.exp (-(c / 4 * ((t - 1 - l : ℕ) : ℝ))) := by
        rw [hq, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [h5]
      refine Real.exp_le_exp.2 ?_
      have h6 : ((t - 1 - l : ℕ) : ℝ) ≤ x := by
        refine le_trans ?_ hxn
        exact_mod_cast (by omega : t - 1 - l ≤ s' - l)
      have : c / 4 * ((t - 1 - l : ℕ) : ℝ) ≤ c / 4 * x := mul_le_mul_of_nonneg_left h6 (by positivity)
      linarith
    rw [e1]
    calc D * x ^ N * (Real.exp (-(c / 2 * x)) * Real.exp (-(c / 4 * x)) * Real.exp (-(c / 4 * x)))
        = D * (x ^ N * Real.exp (-(c / 2 * x))) * Real.exp (-(c / 4 * x)) * Real.exp (-(c / 4 * x)) := by ring
      _ ≤ D * B * E * q ^ (t - 1 - l) := by gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hr : ∑ l ∈ Finset.range t, q ^ (t - 1 - l) = ∑ i ∈ Finset.range t, q ^ i :=
    Finset.sum_range_reflect (fun i => q ^ i) t
  rw [hr, hE]
  have := sum_geometric_le hq0 hq1 t
  have hp : 0 ≤ D * B * Real.exp (-(c / 4 * Lr ^ (s' + 1 - t))) := by positivity
  calc D * B * Real.exp (-(c / 4 * Lr ^ (s' + 1 - t))) * ∑ i ∈ Finset.range t, q ^ i
      ≤ D * B * Real.exp (-(c / 4 * Lr ^ (s' + 1 - t))) * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left this hp
    _ = _ := by ring
private theorem clusterRange_mono {x y : ℝ} (h0 : 0 ≤ x) (h : x ≤ y) : clusterRange x ≤ clusterRange y := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem clusterRange_le_of_abs_sub {x x' Cn B : ℝ} (hx : 1 ≤ x) (hx' : 1 ≤ x') (hCn : 1 ≤ Cn) (hB : 0 ≤ B)
    (h : |x' - x| ≤ Cn * Real.log x + 2 * B) :
    (clusterRange x : ℝ) ≤ 2 * (clusterRange x' : ℝ) +
      ((clusterRange (4 * (Cn * Real.log (4 * Cn) + 2 * B) + 4) : ℝ) + 1) := by
  obtain ⟨X₁, hX₁⟩ : ∃ X₁, X₁ = 4 * (Cn * Real.log (4 * Cn) + 2 * B) + 4 := ⟨_, rfl⟩
  rw [← hX₁]
  have hlog4 : 0 ≤ Real.log (4 * Cn) := Real.log_nonneg (by linarith)
  have hX₁0 : 0 ≤ X₁ := by rw [hX₁]; positivity
  rcases lt_or_ge x X₁ with hlt | hge
  · have h1 : (clusterRange x : ℝ) ≤ (clusterRange X₁ : ℝ) := by exact_mod_cast clusterRange_mono (by linarith) hlt.le
    linarith
  · have hx0 : 0 < x := by linarith
    have hcn : 0 < 4 * Cn := by linarith
    have hl : Real.log x ≤ x / (4 * Cn) + Real.log (4 * Cn) := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hx0 hcn)
      rw [Real.log_div hx0.ne' hcn.ne'] at h1
      linarith
    have hl2 : Cn * Real.log x ≤ x / 4 + Cn * Real.log (4 * Cn) := by
      have h1 := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ Cn)
      have h2 : Cn * (x / (4 * Cn)) = x / 4 := by
        field_simp
      rw [mul_add, h2] at h1
      exact h1
    have hx2 : x / 2 ≤ x' := by
      have := (abs_le.1 h).1
      rw [hX₁] at hge
      linarith
    have hx2' : x ^ ((1 : ℝ) / 100) ≤ 2 * (clusterRange x' : ℝ) := by
      have h1 : (x / 2) ^ ((1 : ℝ) / 100) ≤ x' ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by positivity) hx2 (by norm_num)
      have h2 : x' ^ ((1 : ℝ) / 100) ≤ (clusterRange x' : ℝ) := Nat.le_ceil _
      have h3 : x ^ ((1 : ℝ) / 100) ≤ 2 * (x / 2) ^ ((1 : ℝ) / 100) := by
        have e : x = 2 * (x / 2) := by ring
        calc x ^ ((1 : ℝ) / 100) = (2 * (x / 2)) ^ ((1 : ℝ) / 100) := by rw [← e]
          _ = 2 ^ ((1 : ℝ) / 100) * (x / 2) ^ ((1 : ℝ) / 100) := Real.mul_rpow (by norm_num) (by positivity)
          _ ≤ 2 * (x / 2) ^ ((1 : ℝ) / 100) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
      linarith
    have h1 : (clusterRange x : ℝ) ≤ x ^ ((1 : ℝ) / 100) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : (0 : ℝ) ≤ (clusterRange X₁ : ℝ) := by positivity
    linarith
end RealBounds
section BottomValues
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private def bottomValue (w : ∀ m : ℕ, PlaquetteWeight m) (m : ℕ) [NeZero m] (Y : ColourForm m) : ℝ :=
  (1 / 2) * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), w m p * curlNorm Y p ^ 2
private theorem bottomValue_chainDescend {L : ℕ} [NeZero L] (w : ∀ m : ℕ, PlaquetteWeight m) (u : ℕ) :
    ∀ (d n : ℕ) [NeZero n] (X : LevelChain L (u + d) n),
    bottomValue w (fineSide L (u + d) n) (chainBottom (u + d) n X) =
      bottomValue w (fineSide L u (fineSide L d n)) (chainBottom u (fineSide L d n) (chainDescend u d n X)) := by
  intro d
  induction d with
  | zero => intro n _ X; rfl
  | succ d ih => intro n _ X; exact ih (n * L) (chainLower X)
private theorem half_colourEval_eq_bottomValue
    (hrec : ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (h : PlaquetteWeight n)
      (h' : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage 0).depth n)), HEq h h' →
      ∀ A : TorusBond n → ℝ, ∑ y : TorusSite n, bilinearEval (classicalQuadratic S.tower S.resp 0 n h' y) A A =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), h p * WeightedResponses.curl A p ^ 2)
    (hoff : ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage 0).depth n)),
      (∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage 0).depth y p → h p = 0) →
        classicalQuadratic S.tower S.resp 0 n h y = 0)
    (ht0 : (S.tower.stage 0).depth = 0) (n : ℕ) [NeZero n] (hn : Λ.stepParams.n₀ ≤ n) (i : Fin Λ.k) (Y : ColourForm n) :
    (1 / 2) * colourEval (S.supportForm 0 n i) Y Y = bottomValue (S.weight i) n Y := by
  unfold colourEval bottomValue
  congr 1
  have he : fineSide Λ.stepParams.side (S.tower.stage 0).depth n = n := by
    rw [ht0]
    rfl
  have hheq : HEq (S.weight i n) (S.weight i (fineSide Λ.stepParams.side (S.tower.stage 0).depth n)) :=
    (congr_arg_heq (S.weight i) he).symm
  have h1 : ∀ e : Fin 3, bilinearEval (S.supportForm 0 n i) (Y e) (Y e) =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), S.weight i n p * WeightedResponses.curl (Y e) p ^ 2 := by
    intro e
    rw [← hrec n hn _ _ hheq (Y e)]
    have e1 : bilinearEval (S.supportForm 0 n i) (Y e) (Y e) =
        ∑ y ∈ S.supportAt 0 n i, bilinearEval (classicalQuadratic S.tower S.resp 0 n (S.weight i _) y) (Y e) (Y e) :=
      bilinearEval_sum _ _ _ _
    rw [e1]
    refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
    have gen : ∀ T : ℕ, T = 0 → ∀ p : TorusPlaquette (fineSide Λ.stepParams.side T n),
        IsPlaquetteAt Λ.stepParams.side T y p → S.weight i (fineSide Λ.stepParams.side T n) p = 0 := by
      intro T hT
      subst hT
      intro p hp
      by_contra h
      refine hy ?_
      simp only [MomentPoint.supportAt, ResponseInTheExpansion.weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, hp, h⟩
    rw [hoff n hn y _ (gen _ ht0)]
    simp [bilinearEval]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [curlNorm_sq, Finset.mul_sum]
end BottomValues
section ParameterRanges
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁) (h₂ : ForAllParameters Q₂) :
    ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_forAllPoints {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop}
    (h : ForAllPoints Q) :
    ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S := h
private theorem ForAllParameters.imp' {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q)
    (hq : ∀ Λ : MomentParameters, 2 ≤ Λ.k → 0 < Λ.d → Q Λ → Q' Λ) : ForAllParameters Q' := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, H₁⟩ := h a ha
  refine ⟨L₁, rt₁, C₁, hrt₁, ?_⟩
  intro L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd Kr hKr
  refine ⟨y₁, ?_⟩
  intro y hy hRet hHas g hg hyg k _ hk2 hk8 R d hd
  exact hq ⟨Tb, Kr, y, g, k, R, d⟩ hk2 hd (Y₁ y hy hRet hHas g hg hyg k hk2 hk8 R d hd)
abbrev _root_.YangMills.SharedProofs.p72371 := @ForAllParameters.imp'
private theorem forAllParameters_of_holdsOnAllParameters {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : ResponseInTheExpansion.HoldsOnParameterFamilies P) : ForAllParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p27928 <;> assumption
private theorem forAllParameters_step :
    ForAllParameters fun Λ => AdmissibleStep Λ.stepParams ∧ 0 < Λ.g ∧ Λ.stepParams.y₁ ≤ (Λ.g ^ 2)⁻¹ ∧ Λ.table.Admissible := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _ Kr _
  refine ⟨Tb.floorMin, fun y hy hret hbot g hg hgy k _ _ _ R d _ => ?_⟩
  exact ⟨⟨hD.fits y hy, hret, hbot⟩, hg, hgy, hD⟩
private theorem admissible_of_supAdmissible {k : ℕ} (P : LevelData k) (L : ℕ) (R d : ℝ) (h : P.SupAdmissible L R d) :
    P.Admissible L (2 * R) d := by apply _root_.YangMills.SharedProofs.p11807 <;> assumption
end ParameterRanges
end LevelCumulantProof
set_option maxHeartbeats 4000000 in
open LevelCumulantProof in
theorem levelCumulantApprox (h₁ : cumulantAcrossGaussianStepStatement) (h₂ : chainBuiltDownwardStatement)
    (h₃ : CompletedForms.completedFormAcrossStepStatement) (h₄ : completedFormMomentsStatement)
    (h₅ : stepGradientsDecoupledStatement) (h₆ : levelChainFirstOrderStatement)
    (h₇ : classicalQuadraticRecursionStatement) (h₈ : classicalFormsAnnihilateClosedStatement)
    (h₉ : formsReadCurvatureStatement) (h₁₀ : farLevelNearScaleStatement)
    (h₁₁ : LevelTestFunctions.separationUpperBoundStatement)
    (h₁₂ : LevelTestFunctions.CouplingFlowAboveWindow) (h₁₃ : gaussianChainCoordinatesStatement) :
    levelCumulantApproxStatement := by
  unfold levelCumulantApproxStatement ForAllPoints
  refine ForAllParameters.imp' (forAllParameters_and (forAllParameters_and (forAllParameters_and
    (forAllParameters_and (forAllParameters_of_forAllPoints h₃) (forAllParameters_of_forAllPoints h₄))
    (forAllParameters_and (forAllParameters_of_forAllPoints h₅) (forAllParameters_of_forAllPoints h₆)))
    (forAllParameters_and (forAllParameters_and (forAllParameters_of_forAllPoints h₇) (forAllParameters_of_forAllPoints h₈))
      (forAllParameters_and (forAllParameters_of_forAllPoints h₉) (forAllParameters_of_forAllPoints h₁₀))))
    (forAllParameters_and (forAllParameters_and (forAllParameters_of_forAllPoints h₁₃) forAllParameters_step)
      (forAllParameters_of_holdsOnAllParameters h₂))) fun Λ hk hd H => ?_
  obtain ⟨⟨⟨⟨⟨_, _, _, _, _, f₃⟩, ⟨C₄, _, _, _, _, f₄⟩⟩, ⟨⟨C₅, c₅, _, hc₅, _, f₅⟩, ⟨_, _, _, _, _, f₆⟩⟩⟩,
    ⟨⟨⟨_, _, _, _, _, f₇⟩, ⟨_, _, _, _, _, f₈⟩⟩, ⟨⟨_, _, _, _, _, f₉⟩, ⟨C₁₀, _, _, _, _, f₁₀⟩⟩⟩⟩,
    ⟨⟨⟨_, _, _, _, _, f₁₃⟩, hrun, hg, hgy, hDr⟩, fB⟩⟩ := H
  obtain ⟨Cs, hCs0, hC⟩ := h₁ Λ.k hk
  have hf : Λ.stepParams.Admissible := hrun.1
  have hodd : Odd Λ.stepParams.side := hf.L_odd
  have hL16 : 2 ^ 16 ≤ Λ.stepParams.side := hf.L_ge
  have hL3 : 3 ≤ Λ.stepParams.side := le_trans (by norm_num) hL16
  have hLpos : 0 < Λ.stepParams.side := by omega
  have hLr : (2 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by exact_mod_cast (by omega : 2 ≤ Λ.stepParams.side)
  have hLr1 : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by linarith
  obtain ⟨Cg, hCg0, hgap⟩ := h₁₁ Λ.stepParams.side hodd hL3 Λ.k hk (2 * Λ.R) Λ.d hd
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = Cs * (1 + |C₄ 0|) ^ Λ.k * (1 + |C₅ 0|) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  obtain ⟨C₆, hC₆, hS⟩ := exists_sum_levels_le (Λ.stepParams.side : ℝ) hLr c₅ D hc₅ hD0 (5 * Λ.k + 8)
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℝ, Cn = 1 + |C₁₀ 0| := ⟨_, rfl⟩
  have hCn1 : 1 ≤ Cn := by rw [hCn]; linarith [abs_nonneg (C₁₀ 0)]
  have hB0 : 0 ≤ Λ.stepParams.B := hf.B_pos.le
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = (clusterRange (4 * (Cn * Real.log (4 * Cn) + 2 * Λ.stepParams.B) + 4) : ℝ) + 1 := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  obtain ⟨c₂, hc₂d⟩ : ∃ c₂ : ℝ, c₂ = c₅ / 4 / (1 + Cg) := ⟨_, rfl⟩
  have hc₂ : 0 < c₂ := by rw [hc₂d]; positivity
  refine ⟨fun _ => C₆ * Real.exp (c₂ * (1 + K₀)), c₂, Λ.floor, hc₂, le_rfl, fun S d' hd' μ hμ => ?_⟩
  have ht0 : (S.tower.stage 0).depth = 0 :=
    (congrArg (fun z : ResponseInTheExpansion.StageWithResponse Λ.stepParams => z.1.depth)
      (S.stage_eq 0 (Nat.zero_le _))).trans S.isInitial.depth_eq
  have hts : S.lastSeparated ≤ S.data.scaleLevel := (f₁₀ S).1
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  have hn₀ : Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side := (Nat.le_mul_of_pos_left _ hLpos).trans S.side_le
  have h64 : 64 ≤ S.data.period Λ.stepParams.side := le_trans (by have := hf.n₀_ge; omega) hn₀
  have hside : ∀ j : ℕ, S.data.period Λ.stepParams.side ≤ fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) := by
    intro j
    rw [fineSide_eq]
    exact Nat.le_mul_of_pos_right _ (pow_pos hLpos j)
  have fb : ∀ (m : ℕ) [NeZero m], Λ.stepParams.n₀ ≤ m → ∀ (i : Fin Λ.k) (Y : ColourForm m),
      (1 / 2) * colourEval (S.supportForm 0 m i) Y Y = bottomValue (S.weight i) m Y := fun m _ hm i Y =>
    half_colourEval_eq_bottomValue S (f₇ S).2 (fun n _ hn y h hh => ((f₈ S 0 (Nat.zero_le _) n hn y h).2.2.2 hh).2) ht0 m hm i Y
  have hexact : S.lastSeparated = 0 → ∀ (i : Fin Λ.k)
      (X : LevelChain Λ.stepParams.side (S.lastSeparated + d') (S.data.period Λ.stepParams.side)),
      S.halfForm d' (S.data.period Λ.stepParams.side) i X =
        S.observableAt (S.lastSeparated + d') (S.data.period Λ.stepParams.side) i X := by
    intro h0 i X
    have key : ∀ (τ : ℕ), τ = 0 → ∀ (m : ℕ) [NeZero m], Λ.stepParams.n₀ ≤ m → ∀ (Y : LevelChain Λ.stepParams.side τ m),
        (1 / 2) * colourEval (S.supportForm τ m i) (chainTop τ m Y) (chainTop τ m Y) =
          bottomValue (S.weight i) (fineSide Λ.stepParams.side τ m) (chainBottom τ m Y) := by
      intro τ hτ
      subst hτ
      intro m _ hm Y
      exact fb m hm i Y
    have h1 := key S.lastSeparated h0 (fineSide Λ.stepParams.side d' (S.data.period Λ.stepParams.side)) (hn₀.trans (hside d'))
      (chainDescend S.lastSeparated d' (S.data.period Λ.stepParams.side) X)
    have h2 := bottomValue_chainDescend (L := Λ.stepParams.side) (S.weight i) S.lastSeparated d' (S.data.period Λ.stepParams.side) X
    exact h1.trans h2.symm
  obtain ⟨hPSD, hbuild⟩ := fB
  obtain ⟨μ₀, hc₀, hb₀⟩ := hbuild (S.lastSeparated + d') (S.data.period Λ.stepParams.side) h64
  have := hc₀.isProbabilityMeasure
  have := hμ.isProbabilityMeasure
  have hcoord := (f₁₃ S S.lastSeparated d' hd').2 μ hμ
  have hcoord₀ := (f₁₃ S S.lastSeparated d' hd').2 μ₀ hc₀
  have hker : ∀ (Y : ColourForm (fineSide Λ.stepParams.side d' (S.data.period Λ.stepParams.side))),
      kineticForm Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated Y = 0 → ∀ x, curlLinear x Y = 0 := by
    intro Y hY x
    have h1 := (f₁₃ S S.lastSeparated d' hd').1 Y ⟨x.2.1, (Finset.mem_filter.1 x.2.2).2.1⟩
    rw [hY, mul_zero, curlNorm_sq] at h1
    have h4 : WeightedResponses.curl (Y x.1) x.2.1 ^ 2 ≤ 0 :=
      (Finset.single_le_sum (f := fun e => WeightedResponses.curl (Y e) x.2.1 ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x.1)).trans h1
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 (sq_nonneg _))
  have hκ : ∀ i : Fin Λ.k, ∃ κ : TorusPlaquette (fineSide Λ.stepParams.side d' (S.data.period Λ.stepParams.side)) →
      TorusPlaquette (fineSide Λ.stepParams.side d' (S.data.period Λ.stepParams.side)) → ℝ,
      ∀ Y : ColourForm (fineSide Λ.stepParams.side d' (S.data.period Λ.stepParams.side)),
      colourEval (S.supportForm S.lastSeparated (fineSide Λ.stepParams.side d' (S.data.period Λ.stepParams.side)) i) Y Y =
        formOfCurls κ (curlVector Y) := by
    intro i
    have hside' : fineSide Λ.stepParams.side d' (S.data.period Λ.stepParams.side) = S.levelSide S.lastSeparated := by
      rw [fineSide_eq]
      show _ = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - S.lastSeparated)
      congr 2
      omega
    refine supportForm_eq_formOfCurls S S.lastSeparated _ i (fun y sz q h1 h2 h3 => ?_) fun y =>
      (f₈ S S.lastSeparated (by omega) _ (hn₀.trans (hside d')) y _).2.1
    obtain ⟨κ, h4, -⟩ := (f₉ S S.lastSeparated (by omega) _ hside' y sz q h1 h2).1 h3
    exact ⟨κ, h4⟩
  have hT₁ : jointCumulant μ (fun i => S.halfForm d' (S.data.period Λ.stepParams.side) i) =
      jointCumulant μ₀ (fun i => S.halfForm d' (S.data.period Λ.stepParams.side) i) :=
    halfForm_cumulant_eq S d' _ hcoord.2.1 hcoord₀.2.1 hker hκ
  have ha : 0 < Λ.stepParams.coupling := by have := hf.a_ge; linarith
  have hT₂ : jointCumulant μ (fun i => S.observableAt (S.lastSeparated + d') (S.data.period Λ.stepParams.side) i) =
      jointCumulant μ₀ (fun i => S.observableAt (S.lastSeparated + d') (S.data.period Λ.stepParams.side) i) :=
    observableAt_cumulant_eq S ha _ _ hμ hc₀
  have hobey := (f₆ S d' hd' μ₀ hc₀).2
  let F : ℕ → ℝ := fun j => if h : j ≤ S.lastSeparated + d' then
    jointCumulant (μ₀.map (truncateTop j (S.lastSeparated + d') (S.data.period Λ.stepParams.side) h))
      (fun i => S.completedForm (S.lastSeparated + d' - j) j (S.data.period Λ.stepParams.side) i) else 0
  have hFd : F d' = jointCumulant μ₀ (fun i => S.halfForm d' (S.data.period Λ.stepParams.side) i) := by
    have h : d' ≤ S.lastSeparated + d' := Nat.le_add_left _ _
    simp only [F, dif_pos h]
    rw [jointCumulant_map (measurable_truncateTop _ _ _ _) fun i => measurable_completedForm S _ _ _ i, Nat.add_sub_cancel]
    simp only [completedForm_truncateTop]
  have hFK : F (S.lastSeparated + d') = jointCumulant μ₀ (fun i => S.completedAt d' (S.data.period Λ.stepParams.side) i) := by
    simp only [F, dif_pos le_rfl]
    rw [jointCumulant_map (measurable_truncateTop _ _ _ _) fun i => measurable_completedForm S _ _ _ i, Nat.sub_self]
    congr 1
    funext i X
    rw [truncateTop_self]
    unfold MomentPoint.completedForm MomentPoint.completedAt
    rw [fb _ (hn₀.trans (hside _)) i (chainBottom _ _ X), cumulativeScores_descend,
      bottomValue_chainDescend (S.weight i) S.lastSeparated d']
    rw [completedObservable_eq Λ.stepParams.coupling S.lastSeparated (S.weight i) S.lastSeparated _ _ le_rfl]
    rfl
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, δ = fun l => D * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - l)) ^ (5 * Λ.k + 8) *
      Real.exp (-(c₅ * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - l))) := ⟨_, rfl⟩
  have hstep : ∀ e, e < S.lastSeparated → |F (d' + e + 1) - F (d' + e)| ≤ δ (S.lastSeparated - 1 - e) := by
    intro e he
    obtain ⟨j, hjd⟩ : ∃ j, j = d' + e := ⟨_, rfl⟩
    rw [← hjd]
    have hj : j + 1 ≤ S.lastSeparated + d' := by omega
    have hj0 : j ≤ S.lastSeparated + d' := by omega
    simp only [F, dif_pos hj, dif_pos hj0]
    have e1 : S.lastSeparated + d' - (j + 1) = S.lastSeparated + d' - j - 1 := by omega
    have e2 : S.lastSeparated + d' - j = S.lastSeparated + d' - j - 1 + 1 := by omega
    have hl : S.lastSeparated + d' - j - 1 = S.lastSeparated - 1 - e := by omega
    have hlt : S.lastSeparated + d' - j - 1 < S.lastSeparated := by omega
    have hls : S.lastSeparated + d' - j - 1 ≤ S.data.scaleLevel := by omega
    rw [e1]
    rw [show S.lastSeparated + d' - j = S.lastSeparated + d' - j - 1 + 1 from e2]
    have hside2 : fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side) = S.levelSide (S.lastSeparated + d' - j - 1 + 1) := by
      rw [fineSide_eq]
      show _ = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (S.lastSeparated + d' - j - 1 + 1))
      congr 2
      omega
    obtain ⟨w, hw, hv, hε⟩ := f₅ S (S.lastSeparated + d') hd' μ₀ hc₀ j hj hlt
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - (S.lastSeparated + d' - j - 1)) := ⟨_, rfl⟩
    have hx1 : 1 ≤ x := by
      rw [hx]
      exact one_le_pow₀ hLr1
    obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = (1 + |C₄ 0|) * x ^ 5 := ⟨_, rfl⟩
    have hA1 : 1 ≤ A := by
      rw [hAd]
      have h1 : 1 ≤ x ^ 5 := one_le_pow₀ hx1
      nlinarith [abs_nonneg (C₄ 0)]
    have hpow : ∀ z : ℝ, 0 ≤ z → z ≤ x ^ 5 → (C₄ 0 * z) ^ Λ.k ≤ A ^ Λ.k := by
      intro z hz0 hz
      calc (C₄ 0 * z) ^ Λ.k ≤ |(C₄ 0 * z) ^ Λ.k| := le_abs_self _
        _ = |C₄ 0 * z| ^ Λ.k := abs_pow _ _
        _ ≤ A ^ Λ.k := by
            refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
            rw [abs_mul, abs_of_nonneg hz0, hAd]
            have h2 : 0 ≤ x ^ 5 := by positivity
            nlinarith [abs_nonneg (C₄ 0)]
    have hM₁ := fun i => f₄ S (S.lastSeparated + d') hd' μ₀ hc₀ (j + 1) hj (by omega) i
    have hM₀ := fun i => f₄ S (S.lastSeparated + d') hd' μ₀ hc₀ j hj0 (by omega) i
    rw [e1] at hM₁
    rw [show S.lastSeparated + d' - j = S.lastSeparated + d' - j - 1 + 1 from e2] at hM₀
    have hx5 : (Λ.stepParams.side : ℝ) ^ (5 * (S.data.scaleLevel - (S.lastSeparated + d' - j - 1))) = x ^ 5 := by
      rw [hx, ← pow_mul, mul_comm]
    have hstepb := cumulant_step_bound S Cs hC (S.lastSeparated + d') (S.data.period Λ.stepParams.side) μ₀ j
      (S.lastSeparated + d' - j - 1) hj hlt
      (hPSD _ _ (h64.trans (hside j))) (hb₀ j hj)
      (fun i => f₃ S _ hlt _ hside2 i) A
      ((1 + |C₅ 0|) * (Λ.stepParams.side : ℝ) ^ (8 * (S.data.scaleLevel - (S.lastSeparated + d' - j - 1))) * Real.exp (-(c₅ * x))) hA1
      (fun i => ⟨(hM₁ i).1, (hM₁ i).2.trans (by
        rw [hx5]
        exact hpow _ (by positivity) le_rfl)⟩)
      (fun i => ⟨(hM₀ i).1, (hM₀ i).2.trans (hpow _ (by positivity) (by
        rw [← hx5]
        exact pow_le_pow_right₀ hLr1 (by omega)))⟩)
      w hw hv (fun i i' hii => (hε i i' hii).trans (by
        rw [hx]
        have h3 : 0 ≤ (Λ.stepParams.side : ℝ) ^ (8 * (S.data.scaleLevel - (S.lastSeparated + d' - j - 1))) *
            Real.exp (-(c₅ * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - (S.lastSeparated + d' - j - 1)))) := by positivity
        have h4 : C₅ 0 ≤ 1 + |C₅ 0| := by linarith [le_abs_self (C₅ 0)]
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right h4 h3))
    refine hstepb.trans (le_of_eq ?_)
    have h8 : (Λ.stepParams.side : ℝ) ^ (8 * (S.data.scaleLevel - (S.lastSeparated + d' - j - 1))) = x ^ 8 := by
      rw [hx, ← pow_mul, mul_comm]
    rw [hδ, hDdef, ← hl, h8]
    beta_reduce
    rw [← hx, hAd, mul_pow]
    ring
  have htel : ∀ e, e ≤ S.lastSeparated → |F (d' + e) - F d'| ≤ ∑ x ∈ Finset.range e, δ (S.lastSeparated - 1 - x) := by
    intro e
    induction e with
    | zero =>
      intro _
      simp
    | succ e ih =>
      intro he
      have h1 := hstep e (by omega)
      have h2 := ih (by omega)
      rw [Finset.sum_range_succ]
      have e1 : F (d' + (e + 1)) - F d' = (F (d' + e + 1) - F (d' + e)) + (F (d' + e) - F d') := by
        rw [show d' + (e + 1) = d' + e + 1 from rfl]
        ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      linarith
  have hdiff := htel S.lastSeparated le_rfl
  rw [add_comm d' S.lastSeparated, hFK, hFd, hobey, Finset.sum_range_reflect δ S.lastSeparated] at hdiff
  have hsum := hS S.data.scaleLevel S.lastSeparated hts
  rw [← hδ] at hsum
  have hmain : |jointCumulant μ (fun i => S.halfForm d' (S.data.period Λ.stepParams.side) i) -
      jointCumulant μ (fun i => S.observableAt (S.lastSeparated + d') (S.data.period Λ.stepParams.side) i)| ≤
      C₆ * Real.exp (-(c₅ / 4 * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel + 1 - S.lastSeparated))) := by
    rw [hT₁, hT₂, abs_sub_comm]
    exact hdiff.trans hsum
  have hzero : S.lastSeparated = 0 → jointCumulant μ (fun i => S.halfForm d' (S.data.period Λ.stepParams.side) i) =
      jointCumulant μ (fun i => S.observableAt (S.lastSeparated + d') (S.data.period Λ.stepParams.side) i) := by
    intro h0
    congr 1
    funext i X
    exact hexact h0 i X
  refine ⟨?_, hzero⟩
  show _ ≤ C₆ * Real.exp (c₂ * (1 + K₀)) * Real.exp (-(c₂ * (S.range : ℝ)))
  by_cases ht : S.lastSeparated = 0
  · rw [hzero ht, sub_self, abs_zero]
    positivity
  obtain ⟨u, hu⟩ : ∃ u, u + 1 = S.lastSeparated := ⟨S.lastSeparated - 1, by omega⟩
  have hfar : S.data.SeparatedBelow Λ.stepParams S.β S.lastSeparated := by
    classical
    exact Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (fun v hv => absurd hv (Nat.not_lt_zero v))
  obtain ⟨g₁, -⟩ := hfar u (by omega)
  have hg₂ := hgap S.data (admissible_of_supAdmissible _ _ _ _ S.supAdmissible) u (by omega)
  have hz : (Λ.stepParams.side : ℝ) ^ ((S.data.scaleLevel : ℤ) - (u : ℤ)) =
      (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel + 1 - S.lastSeparated) := by
    have : (S.data.scaleLevel : ℤ) - (u : ℤ) = ((S.data.scaleLevel + 1 - S.lastSeparated : ℕ) : ℤ) := by omega
    rw [this, zpow_natCast]
  rw [hz] at hg₂
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel + 1 - S.lastSeparated) := ⟨_, rfl⟩
  rw [← hXd] at hg₂ hmain
  have hX0 : 0 ≤ X := by rw [hXd]; positivity
  obtain ⟨hyj, hrunb⟩ := h₁₂ Λ.stepParams hrun Λ.g hg hgy S.β S.data.windowLevel S.window_le S.passage
  have hy1 : (1 : ℝ) ≤ Λ.stepParams.y₁ := hf.y₁_ge
  have hxs : 1 ≤ S.scaleCoupling := hy1.trans (hyj S.data.scaleLevel hsK)
  have hxu : 1 ≤ (couplingFlow Λ.stepParams S.β u).1 := hy1.trans (hyj u (by omega))
  have hlog : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg hxs
  have hnear := (f₁₀ S).2.2
  have hr1 := hrunb u S.lastSeparated (by omega) (by omega)
  have hcomp : |(couplingFlow Λ.stepParams S.β u).1 - S.scaleCoupling| ≤ Cn * Real.log S.scaleCoupling + 2 * Λ.stepParams.B := by
    have e1 : (couplingFlow Λ.stepParams S.β u).1 - S.scaleCoupling =
        -((couplingFlow Λ.stepParams S.β S.lastSeparated).1 - (couplingFlow Λ.stepParams S.β u).1) +
          (S.coupling S.lastSeparated - S.scaleCoupling) := by
      show _ = -((couplingFlow Λ.stepParams S.β S.lastSeparated).1 - (couplingFlow Λ.stepParams S.β u).1) +
        ((couplingFlow Λ.stepParams S.β S.lastSeparated).1 - S.scaleCoupling)
      ring
    have h4 : ((S.lastSeparated : ℝ) - (u : ℝ)) = 1 := by
      rw [← hu]
      push_cast
      ring
    rw [h4, mul_one] at hr1
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    have h5 : C₁₀ 0 * Real.log S.scaleCoupling ≤ Cn * Real.log S.scaleCoupling := by
      refine mul_le_mul_of_nonneg_right ?_ hlog
      rw [hCn]
      linarith [le_abs_self (C₁₀ 0)]
    linarith
  have hrange := clusterRange_le_of_abs_sub hxs hxu hCn1 hB0 hcomp
  rw [← hK₀] at hrange
  have hr₀ : (S.range : ℝ) = (clusterRange S.scaleCoupling : ℝ) := rfl
  have hg₃ : (2 : ℝ) ^ 10 * (clusterRange (couplingFlow Λ.stepParams S.β u).1 : ℝ) ≤
      (S.data.separation Λ.stepParams.side u : ℝ) := by exact_mod_cast g₁
  have hrr : (S.range : ℝ) - 1 - K₀ ≤ (1 + Cg) * X := by
    rw [hr₀]
    have h6 : (0 : ℝ) ≤ Cg * X := by positivity
    nlinarith
  refine hmain.trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₆
  have hcg : c₂ * (1 + Cg) = c₅ / 4 := by
    rw [hc₂d]
    field_simp
  have h7 : c₂ * ((S.range : ℝ) - 1 - K₀) ≤ c₂ * ((1 + Cg) * X) := mul_le_mul_of_nonneg_left hrr hc₂.le
  have h8 : c₂ * ((1 + Cg) * X) = c₅ / 4 * X := by
    rw [← mul_assoc, hcg]
  nlinarith
end YangMills.Construction.MomentLaw
end
