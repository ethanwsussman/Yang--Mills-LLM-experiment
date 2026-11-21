import YangMills.Construction.Towers.ChainsOfBoundedOperators
import YangMills.Construction.Towers.CoefficientsOfTheResolventAsSumsOverBonds
import YangMills.Construction.Towers.EntriesAlongAFieldAsSumsOverBonds
import YangMills.Construction.Towers.SumsInsideTheChainsOfLocalKernels
import YangMills.Construction.Towers.VariationsOfALocalFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open OperatorCalculus Tower.UnitLatticeL2 Tower.AbelianFieldDensity
open Tower.ResolventDecay Tower.LocalFamilies OneLoopNotation
namespace Tower.LocalFamilies
namespace ResolventCoeffSums
variable {J : Type}
theorem loopSumOne_const_mul (pos : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ : J → J → ℂ) (a : ℂ) :
    loopSumOne pos S₀ (fun i j => a * X i j) S₁ = a * loopSumOne pos S₀ X S₁ := by
  unfold loopSumOne
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [loopTermsOne]
  ring
theorem loopSumTwo_const_mul (pos : J → InfiniteLattice.AmbientSpace) (S₀ X S₁ Y S₂ : J → J → ℂ)
    (a a' : ℂ) :
    loopSumTwo pos S₀ (fun i j => a * X i j) S₁ (fun i j => a' * Y i j) S₂ =
      a * a' * loopSumTwo pos S₀ X S₁ Y S₂ := by
  unfold loopSumTwo
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [loopTermsTwo]
  ring
theorem traceAt_sub {pos : J → InfiniteLattice.AmbientSpace} {m : ℕ} {z C : ℝ}
    (h : IsIndexedL2Space pos m z C) (X Y : BddOp (IndexL2 J)) :
    traceAt pos (X - Y) 0 = traceAt pos X 0 - traceAt pos Y 0 := by
  have h0 : PeriodicOperators.castVec (0 : Fin 4 → ℤ) = (0 : InfiniteLattice.AmbientSpace) := by
    funext μ
    simp [PeriodicOperators.castVec]
  have hlin := (h.trace_bounded 0).1 X Y (-1)
  rw [h0] at hlin
  have e : X + (-1 : ℂ) • Y = X - Y := by simp [sub_eq_add_neg]
  rw [e] at hlin
  beta_reduce at hlin
  rw [hlin]
  ring
end ResolventCoeffSums
open ResolventCoeffSums in
theorem ResolventCoeffSums.bondSumExpansion
    (hS : loopSums_linear_and_tsum)
    (hO : LoopSumsAsTraces)
    (hF : FieldVariationsAsEdgeSums)
    (hV : LocalFamilyVariations) :
    ResolventCoeffSums.BondSumExpansion := by
  intro z C m m' hz hC
  have hc : 0 < resolventDecayRate z C := by
    unfold resolventDecayRate
    have h1 : 0 < z / (4 * 12 * 5 ^ 4 * C) := by positivity
    have h2 : 0 < Real.log (1 + z / (4 * 12 * 5 ^ 4 * C)) := Real.log_pos (by linarith)
    positivity
  obtain ⟨M₀, hM₀, hS'⟩ := hS (resolventDecayRate z C) m hc
  obtain ⟨A, hA, hF'⟩ := hF C m' hC
  refine ⟨M₀ * A + 2 * (M₀ * A * A) * (4 / z), by positivity, ?_⟩
  intro J B pos src T hset ξ hξ w hw
  have hE := hset.space.entryFacts
  have hL := hset.space.placement
  have hlow : UnitLatticeL2.IsBoundedBelowBy (addScalar (T fun _ => 0) z) (z / 2) := by
    obtain ⟨r, hr, hsm⟩ := hset.lower_bound
    exact hsm _ fun _ => by simpa using hr.le
  have hent : ∀ i j, ‖matrixEntry (T fun _ => 0) i j‖ ≤ C := by
    intro i j
    obtain ⟨E, Q, -, -, hQ, heq⟩ := hset.family.entry_smooth i j
    rw [heq]
    simpa using hQ 0 (by norm_num) fun b => (0 : ℝ)
  set s : ℝ := (z / 4 + w)⁻¹ with hsdef
  have hs : 0 ≤ s := by rw [hsdef]; positivity
  have hs4 : s ≤ 4 / z := by
    have h4 : (4 : ℝ) / z = (z / 4)⁻¹ := (inv_div z 4).symm
    rw [hsdef, h4]
    exact inv_anti₀ (by positivity) (by linarith)
  set R : BddOp (IndexL2 J) := baseResolvent T z w with hRdef
  have hR : IsExpDecayKernel pos (resolventDecayRate z C) s (matrixEntry R) :=
    fun κ κ' => hset.space.resolventDecay (T fun _ => 0) (hset.family.selfAdjoint _) hlow hent
      (hset.family.finite_range _) w hw κ κ'
  obtain ⟨-, -, hone, htwo⟩ := hS' J pos hL s hs
  obtain ⟨hop1, hop2, -⟩ := hO (resolventDecayRate z C) m hc J pos hL hE s hs
  obtain ⟨hf1, hf2, he1, he2⟩ := hF' J B pos src m z T hz hset ξ hξ
  have hgrow : ∀ i : J, C ≤ C * (1 + TorusMetric.euclidNormVec (pos i)) ^ 3 := by
    intro i
    have h0 : 0 ≤ TorusMetric.euclidNormVec (pos i) := Real.sqrt_nonneg _
    have h1 : 1 ≤ (1 + TorusMetric.euclidNormVec (pos i)) ^ 3 :=
      one_le_pow₀ (by linarith)
    nlinarith
  have hX1 : ∀ b, IsCubicGrowthLocalKernel pos C (matrixEntry (firstVar T b)) := by
    intro b
    obtain ⟨-, hb, hr, -⟩ := hV J B pos src m m' z C T hz hC hset b b
    exact ⟨fun i j h => (hr i j h).1, fun i j => (hb i j).1.trans (hgrow i)⟩
  have hX2 : ∀ b b', IsCubicGrowthLocalKernel pos C (matrixEntry (secondVar T b b')) := by
    intro b b'
    obtain ⟨-, hb, hr, -⟩ := hV J B pos src m m' z C T hz hC hset b b'
    exact ⟨fun i j h => (hr i j h).2, fun i j => (hb i j).2.trans (hgrow i)⟩
  let F₁ : B → J → J → ℂ := fun b i j => (ξ b : ℂ) * matrixEntry (firstVar T b) i j
  let F₂ : B × B → J → J → ℂ := fun p i j =>
    (ξ p.1 : ℂ) * (ξ p.2 : ℂ) * matrixEntry (secondVar T p.1 p.2) i j
  let P : B × B → ℂ := fun p => loopSumOne pos (matrixEntry R) (F₂ p) (matrixEntry R)
  let Q : B × B → ℂ := fun p =>
    loopSumTwo pos (matrixEntry R) (F₁ p.1) (matrixEntry R) (F₁ p.2) (matrixEntry R)
  have mem1 : ∀ b, (ξ b : ℂ) * traceAt pos (R.comp ((firstVar T b).comp R)) 0 =
      loopSumOne pos (matrixEntry R) (F₁ b) (matrixEntry R) := by
    intro b
    rw [hop1 R R _ C hC.le hR hR (hX1 b)]
    exact (loopSumOne_const_mul pos _ _ _ _).symm
  have memS : ∀ b b', traceAt pos (secondOrderResolvent T z b b' w) 0 =
      loopSumOne pos (matrixEntry R) (matrixEntry (secondVar T b b')) (matrixEntry R) -
        loopSumTwo pos (matrixEntry R) (matrixEntry (firstVar T b)) (matrixEntry R)
          (matrixEntry (firstVar T b')) (matrixEntry R) -
        loopSumTwo pos (matrixEntry R) (matrixEntry (firstVar T b')) (matrixEntry R)
          (matrixEntry (firstVar T b)) (matrixEntry R) := by
    intro b b'
    change traceAt pos
      (R.comp ((secondVar T b b').comp R) -
        R.comp ((firstVar T b).comp (R.comp ((firstVar T b').comp R))) -
        R.comp ((firstVar T b').comp (R.comp ((firstVar T b).comp R)))) 0 = _
    rw [traceAt_sub hset.space, traceAt_sub hset.space, hop1 R R _ C hC.le hR hR (hX2 b b'),
      hop2 R R R _ _ C C hC.le hC.le hR hR hR (hX1 b) (hX1 b'),
      hop2 R R R _ _ C C hC.le hC.le hR hR hR (hX1 b') (hX1 b)]
  have hG : ∀ p : B × B, (ξ p.1 : ℂ) * (ξ p.2 : ℂ) *
      traceAt pos (secondOrderResolvent T z p.1 p.2 w) 0 = P p - Q p - Q p.swap := by
    intro p
    have e1 : P p = (ξ p.1 : ℂ) * (ξ p.2 : ℂ) *
        loopSumOne pos (matrixEntry R) (matrixEntry (secondVar T p.1 p.2)) (matrixEntry R) :=
      loopSumOne_const_mul pos _ _ _ _
    have e2 : Q p = (ξ p.1 : ℂ) * (ξ p.2 : ℂ) *
        loopSumTwo pos (matrixEntry R) (matrixEntry (firstVar T p.1)) (matrixEntry R)
          (matrixEntry (firstVar T p.2)) (matrixEntry R) :=
      loopSumTwo_const_mul pos _ _ _ _ _ _ _
    have e3 : Q p.swap = (ξ p.2 : ℂ) * (ξ p.1 : ℂ) *
        loopSumTwo pos (matrixEntry R) (matrixEntry (firstVar T p.2)) (matrixEntry R)
          (matrixEntry (firstVar T p.1)) (matrixEntry R) :=
      loopSumTwo_const_mul pos _ _ _ _ _ _ _
    rw [memS, e1, e2, e3]
    ring
  obtain ⟨p1, p2, p3⟩ := hone B (matrixEntry R) (matrixEntry R) F₁ A hA hR hR hf1
  obtain ⟨q1, q2, q3⟩ := hone (B × B) (matrixEntry R) (matrixEntry R) F₂ A hA hR hR hf2
  obtain ⟨r1, r2, r3⟩ :=
    htwo B B (matrixEntry R) (matrixEntry R) (matrixEntry R) F₁ F₁ A A hA hA hR hR hR hf1 hf1
  have q1' : Summable fun p => ‖P p‖ := q1
  have q2' : ∑' p, ‖P p‖ ≤ M₀ * A * s ^ 2 := q2
  have r1' : Summable fun p => ‖Q p‖ := r1
  have r2' : ∑' p, ‖Q p‖ ≤ M₀ * A * A * s ^ 3 := r2
  have t1 : Summable fun p : B × B => ‖Q p.swap‖ := (Equiv.prodComm B B).summable_iff.2 r1'
  have t2 : ∑' p : B × B, ‖Q p.swap‖ = ∑' p, ‖Q p‖ :=
    (Equiv.prodComm B B).tsum_eq fun p => ‖Q p‖
  have t3 : ∑' p : B × B, Q p.swap = ∑' p, Q p := (Equiv.prodComm B B).tsum_eq Q
  have k1 : firstVariationKernel T ξ = fun i j => ∑' b, F₁ b i j := by
    funext i j
    exact he1 i j
  have k2 : secondVariationKernel T ξ = fun i j => ∑' p, F₂ p i j := by
    funext i j
    exact he2 i j
  have hs3 : M₀ * A * A * s ^ 3 ≤ M₀ * A * A * (4 / z) * s ^ 2 := by
    have h3 : s ^ 3 ≤ 4 / z * s ^ 2 := by
      calc s ^ 3 = s * s ^ 2 := by ring
        _ ≤ 4 / z * s ^ 2 := mul_le_mul_of_nonneg_right hs4 (sq_nonneg s)
    calc M₀ * A * A * s ^ 3 ≤ M₀ * A * A * (4 / z * s ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = M₀ * A * A * (4 / z) * s ^ 2 := by ring
  have hpos : 0 ≤ M₀ * A * A * (4 / z) * s ^ 2 := by positivity
  have hsum : Summable fun p : B × B => ‖P p‖ + ‖Q p‖ + ‖Q p.swap‖ := (q1'.add r1').add t1
  have hle : ∀ p : B × B, ‖P p - Q p - Q p.swap‖ ≤ ‖P p‖ + ‖Q p‖ + ‖Q p.swap‖ := fun p =>
    (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hsG : Summable fun p : B × B => ‖P p - Q p - Q p.swap‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [mem1]
    exact p1
  · simp only [mem1]
    refine le_trans p2 ?_
    nlinarith
  · change loopSumOne pos (matrixEntry R) (firstVariationKernel T ξ) (matrixEntry R) = _
    rw [k1, p3]
    simp only [mem1]
  · simp only [hG]
    exact hsG
  · simp only [hG]
    refine (Summable.tsum_le_tsum hle hsG hsum).trans ?_
    rw [Summable.tsum_add (q1'.add r1') t1, Summable.tsum_add q1' r1', t2]
    nlinarith
  · change loopSumOne pos (matrixEntry R) (secondVariationKernel T ξ) (matrixEntry R) -
      2 * loopSumTwo pos (matrixEntry R) (firstVariationKernel T ξ) (matrixEntry R)
        (firstVariationKernel T ξ) (matrixEntry R) = _
    have q3' : loopSumOne pos (matrixEntry R) (fun i j => ∑' p, F₂ p i j) (matrixEntry R) =
        ∑' p, P p := q3
    have r3' : loopSumTwo pos (matrixEntry R) (fun i j => ∑' b, F₁ b i j) (matrixEntry R)
        (fun i j => ∑' b, F₁ b i j) (matrixEntry R) = ∑' p, Q p := r3
    rw [k1, k2, q3', r3']
    simp only [hG]
    rw [Summable.tsum_sub (q1'.of_norm.sub r1'.of_norm) t1.of_norm,
      Summable.tsum_sub q1'.of_norm r1'.of_norm, t3]
    ring
end Tower.LocalFamilies
end YangMills.Construction
end
