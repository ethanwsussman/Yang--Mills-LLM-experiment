import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.ClusterExpansionOfAStep.ContoursOnTheTorus
import YangMills.Construction.ClusterExpansionOfAStep.ExponentialSumsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.SizeOfAFlatResponse
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.ResponseInTheExpansion.RowSumsOfTheFunctionals
import YangMills.Construction.ResponseInTheExpansion.TheResponseContractsCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages hiding unitStep
open ColdStepAtMirrorFrames WeightedResponses TorusFields TorusLumps
namespace ResponseInTheExpansion
namespace TransportedCurlBounds
section AdjointPairing
variable {a ρA : ℝ} {L : ℕ} [NeZero L]
private theorem sum_responseAdjoint_mul (u : ℕ) {n : ℕ} [NeZero n] (h : TorusBond (n * L) → ℝ)
    (B : TorusBond n → ℝ) :
    ∑ c, responseAdjoint a ρA L u h c * B c = ∑ b, h b * responseMap a ρA L u B b := by
  unfold responseAdjoint responseMap
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem sum_curlFunctional_mul {m : ℕ} [NeZero m] (q : TorusPlaquette m) (B : TorusBond m → ℝ) :
    ∑ c, curlFunctional q c * B c = WeightedResponses.curl B q := by
  classical
  unfold curlFunctional WeightedResponses.curl
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
private theorem exists_plaquette (m : ℕ) [NeZero m] :
    ∃ q : TorusPlaquette m, q ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)) := by
  classical
  refine ⟨(0, 0, 1), ?_⟩
  unfold plaquettesIn
  simp
private theorem abs_sum_adjointTransport_le (k N : ℕ)
    (H : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (A : TorusBond n → ℝ) (s : ℝ),
      (∀ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |WeightedResponses.curl A q| ≤ s) →
      ∀ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * L))),
        |WeightedResponses.curl (responseMap a ρA L u A) q| ≤ s / 8) :
    ∀ (d n : ℕ) (_ : NeZero n), N ≤ n → ∀ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
      ∀ (B : TorusBond n → ℝ) (s : ℝ), 0 ≤ s →
      (∀ q' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |WeightedResponses.curl B q'| ≤ s) →
      |∑ c, adjointTransport a ρA L k d n (curlFunctional q) c * B c| ≤ (1 / 2 : ℝ) ^ d * s := by
  intro d
  induction d with
  | zero =>
    intro n _ _ q hq B s _ hB
    have e : ∑ c, adjointTransport a ρA L k 0 n (curlFunctional q) c * B c = WeightedResponses.curl B q :=
      sum_curlFunctional_mul q B
    rw [e]
    simpa using hB q hq
  | succ d ih =>
    intro n _ hn q hq B s hs hB
    have hnL : N ≤ n * L := hn.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne L)))
    have e : ∑ c, adjointTransport a ρA L k (d + 1) n (curlFunctional q) c * B c =
        ∑ b, adjointTransport a ρA L k d (n * L) (curlFunctional q) b * responseMap a ρA L (k + d) B b :=
      sum_responseAdjoint_mul (k + d) _ B
    rw [e]
    have h1 := ih (n * L) inferInstance hnL q hq (responseMap a ρA L (k + d) B) (s / 8) (by positivity)
      (H (k + d) n hn B s hB)
    refine h1.trans ?_
    have hp2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ d := by positivity
    rw [pow_succ]
    nlinarith [mul_nonneg hp2 hs]
private theorem abs_curl_le_four {m : ℕ} (B : TorusBond m → ℝ) (hB : ∀ b, |B b| ≤ 1) (q : TorusPlaquette m) :
    |WeightedResponses.curl B q| ≤ 4 := by
  unfold WeightedResponses.curl
  have h1 := abs_le.mp (hB (q.1, q.2.1))
  have h2 := abs_le.mp (hB (q.1 + unitStep m q.2.1, q.2.2))
  have h3 := abs_le.mp (hB (q.1 + unitStep m q.2.2, q.2.1))
  have h4 := abs_le.mp (hB (q.1, q.2.2))
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
private theorem sum_abs_le_of_curl_bound {m : ℕ} [NeZero m] (l : TorusBond m → ℝ) (r : ℝ)
    (h : ∀ B : TorusBond m → ℝ,
      (∀ q' ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), |WeightedResponses.curl B q'| ≤ 4) →
      |∑ c, l c * B c| ≤ r) : ∑ b, |l b| ≤ r := by
  classical
  set S : TorusBond m → ℝ := fun b => if 0 ≤ l b then 1 else -1 with hS
  have hS1 : ∀ b, |S b| ≤ 1 := by
    intro b
    simp only [hS]
    split_ifs <;> simp
  have e : ∑ c, l c * S c = ∑ b, |l b| := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hS]
    split_ifs with h0
    · rw [abs_of_nonneg h0, mul_one]
    · rw [abs_of_neg (not_le.mp h0)]
      ring
  have h1 := h S fun q' _ => abs_curl_le_four S hS1 q'
  rw [e] at h1
  exact (le_abs_self _).trans h1
private def expWeightedSum {m : ℕ} [NeZero m] (g : TorusBond m → ℝ) (o : TorusSite m) (θ : ℝ) : ℝ :=
  ∑ b, |g b| * Real.exp (θ * _root_.YangMills.Construction.TorusFields.supDist b.1 o)
private theorem expWeightedSum_adjointTransport_le (k N : ℕ) {κ K : ℝ} (hK : 0 ≤ K)
    (H : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ b : TorusBond (n * L),
      ∑ c : TorusBond n, |responseKernel a ρA L u b c| * Real.exp (κ * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1) ≤ K) :
    ∀ (d n : ℕ) (_ : NeZero n), N ≤ n → ∀ (h : TorusBond (fineSide L d n) → ℝ) (o : TorusSite (fineSide L d n))
      (θ : ℝ), 0 ≤ θ → θ * (L : ℝ) ^ d ≤ κ →
      expWeightedSum (adjointTransport a ρA L k d n h) (siteAbove L d n o) (θ * (L : ℝ) ^ d) ≤
        (K * Real.exp κ) ^ d * expWeightedSum h o θ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  intro d
  induction d with
  | zero =>
    intro n _ _ h o θ _ _
    have e : expWeightedSum (adjointTransport a ρA L k 0 n h) (siteAbove L 0 n o) (θ * (L : ℝ) ^ 0) =
        expWeightedSum h o θ := by
      rw [pow_zero, mul_one]
      rfl
    rw [e, pow_zero, one_mul]
  | succ d ih =>
    intro n _ hn h o θ hθ hθκ
    have hnL : N ≤ n * L := hn.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne L)))
    set g := adjointTransport a ρA L k d (n * L) h with hg
    set o₁ := siteAbove L d (n * L) o with ho₁
    set θ' := θ * (L : ℝ) ^ d with hθ'
    have hθ'0 : 0 ≤ θ' := by positivity
    have hθ'' : θ * (L : ℝ) ^ (d + 1) = θ' * L := by rw [hθ', pow_succ]; ring
    have hθL : θ' * L ≤ κ := by rw [← hθ'']; exact hθκ
    have hθ'κ : θ' ≤ κ := le_trans (by nlinarith) hθL
    have hIH := ih (n * L) inferInstance hnL h o θ hθ hθ'κ
    have key : ∀ b : TorusBond (n * L), ∑ c : TorusBond n, |responseKernel a ρA L (k + d) b c| *
        Real.exp (θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁)) ≤
          K * Real.exp κ * Real.exp (θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁) := by
      intro b
      have hterm : ∀ c : TorusBond n, Real.exp (θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁)) ≤
          Real.exp (κ * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1) * (Real.exp κ * Real.exp (θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁)) := by
        intro c
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have t1 : (_root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁) : ℝ) ≤
            _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L b.1) + _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) (parentBlock L o₁) := by
          exact_mod_cast _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
        have t2 : (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) (parentBlock L o₁) : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist b.1 o₁ : ℝ) / L + 1 := by
          have h2 := TorusBalls.supDist_parentBlock_le_div_add_one (n := n) L b.1 o₁
          have h3 : ((_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) (parentBlock L o₁) : ℕ) : ℝ) ≤
              ((_root_.YangMills.Construction.TorusFields.supDist b.1 o₁ / L + 1 : ℕ) : ℝ) := by
            exact_mod_cast h2
          push_cast at h3
          exact h3.trans (by gcongr; exact Nat.cast_div_le)
        have t3 : (_root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L b.1) : ℝ) = _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 := by
          rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        have t4 : (0 : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 := Nat.cast_nonneg _
        have t5 : θ' * L * ((_root_.YangMills.Construction.TorusFields.supDist b.1 o₁ : ℝ) / L + 1) = θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁ + θ' * L := by
          field_simp
        calc θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁)
            ≤ θ' * L * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 + ((_root_.YangMills.Construction.TorusFields.supDist b.1 o₁ : ℝ) / L + 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [← t3]
              linarith
          _ = θ' * L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 + (θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁ + θ' * L) := by
              rw [mul_add, t5]
          _ ≤ κ * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 + (κ + θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁) := by
              have := mul_le_mul_of_nonneg_right hθL t4
              linarith
      calc ∑ c : TorusBond n, |responseKernel a ρA L (k + d) b c| *
            Real.exp (θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁))
          ≤ ∑ c : TorusBond n, |responseKernel a ρA L (k + d) b c| *
              (Real.exp (κ * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1) *
              (Real.exp κ * Real.exp (θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁))) :=
            Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hterm c) (abs_nonneg _)
        _ = (∑ c : TorusBond n, |responseKernel a ρA L (k + d) b c| *
              Real.exp (κ * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1)) *
              (Real.exp κ * Real.exp (θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁)) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ K * (Real.exp κ * Real.exp (θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁)) :=
            mul_le_mul_of_nonneg_right (H (k + d) n hn b) (by positivity)
        _ = K * Real.exp κ * Real.exp (θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁) := by ring
    have hcalc : expWeightedSum (adjointTransport a ρA L k (d + 1) n h) (siteAbove L (d + 1) n o) (θ' * L) ≤
        (K * Real.exp κ) * expWeightedSum g o₁ θ' := by
      calc expWeightedSum (adjointTransport a ρA L k (d + 1) n h) (siteAbove L (d + 1) n o) (θ' * L)
          = ∑ c : TorusBond n, |∑ b, g b * responseKernel a ρA L (k + d) b c| *
              Real.exp (θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁)) := rfl
        _ ≤ ∑ c : TorusBond n, ∑ b, |g b| * (|responseKernel a ρA L (k + d) b c| *
              Real.exp (θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁))) := by
            refine Finset.sum_le_sum fun c _ => ?_
            calc |∑ b, g b * responseKernel a ρA L (k + d) b c| *
                  Real.exp (θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁))
                ≤ (∑ b, |g b * responseKernel a ρA L (k + d) b c|) *
                    Real.exp (θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁)) :=
                  mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le
              _ = _ := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun b _ => ?_
                  rw [abs_mul]
                  ring
        _ = ∑ b, |g b| * ∑ c : TorusBond n, |responseKernel a ρA L (k + d) b c| *
              Real.exp (θ' * L * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L o₁)) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ b, |g b| * (K * Real.exp κ * Real.exp (θ' * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁)) :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (key b) (abs_nonneg _)
        _ = (K * Real.exp κ) * expWeightedSum g o₁ θ' := by
            unfold expWeightedSum
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hθ'']
    refine hcalc.trans ?_
    have hQ : 0 ≤ K * Real.exp κ := by positivity
    calc (K * Real.exp κ) * expWeightedSum g o₁ θ' ≤
          (K * Real.exp κ) * ((K * Real.exp κ) ^ d * expWeightedSum h o θ) :=
          mul_le_mul_of_nonneg_left hIH hQ
      _ = (K * Real.exp κ) ^ (d + 1) * expWeightedSum h o θ := by rw [pow_succ]; ring
private theorem expWeightedSum_curlFunctional_le {m : ℕ} [NeZero m] (q : TorusPlaquette m) (o : TorusSite m)
    {θ R : ℝ} (hθ : 0 ≤ θ) (hq : (_root_.YangMills.Construction.TorusFields.supDist q.1 o : ℝ) ≤ R) :
    expWeightedSum (curlFunctional q) o θ ≤ 4 * Real.exp (θ * (R + 1)) := by
  classical
  have hnear : ∀ i : Fin 4, (_root_.YangMills.Construction.TorusFields.supDist (q.1 + unitStep m i) o : ℝ) ≤ R + 1 := by
    intro i
    have h1 : _root_.YangMills.Construction.TorusFields.supDist (q.1 + unitStep m i) q.1 ≤ 1 := by
      have := TorusContours.supDist_sub_unitStep_le (q.1 + unitStep m i) i
      rwa [add_sub_cancel_right] at this
    have h2 : (_root_.YangMills.Construction.TorusFields.supDist (q.1 + unitStep m i) o : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist (q.1 + unitStep m i) q.1 + _root_.YangMills.Construction.TorusFields.supDist q.1 o := by
      exact_mod_cast _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
    have h3 : (_root_.YangMills.Construction.TorusFields.supDist (q.1 + unitStep m i) q.1 : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  set w : TorusBond m → ℝ := fun b => Real.exp (θ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) with hw
  have hb : ∀ b : TorusBond m, (_root_.YangMills.Construction.TorusFields.supDist b.1 o : ℝ) ≤ R + 1 → w b ≤ Real.exp (θ * (R + 1)) := fun b h =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hθ)
  have hone : ∀ b₀ : TorusBond m, ∑ b, (if b₀ = b then (1 : ℝ) else 0) * w b = w b₀ := by
    intro b₀
    simp
  have hterm : ∀ b : TorusBond m, |curlFunctional q b| * w b ≤
      (if (q.1, q.2.1) = b then (1 : ℝ) else 0) * w b +
        (if (q.1 + unitStep m q.2.1, q.2.2) = b then (1 : ℝ) else 0) * w b +
        (if (q.1 + unitStep m q.2.2, q.2.1) = b then (1 : ℝ) else 0) * w b +
        (if (q.1, q.2.2) = b then (1 : ℝ) else 0) * w b := by
    intro b
    have hwp : 0 ≤ w b := (Real.exp_pos _).le
    have hc : |curlFunctional q b| ≤ (if (q.1, q.2.1) = b then (1 : ℝ) else 0) +
        (if (q.1 + unitStep m q.2.1, q.2.2) = b then (1 : ℝ) else 0) +
        (if (q.1 + unitStep m q.2.2, q.2.1) = b then (1 : ℝ) else 0) +
        (if (q.1, q.2.2) = b then (1 : ℝ) else 0) := by
      have e : curlFunctional q b = (if (q.1, q.2.1) = b then (1 : ℝ) else 0) +
          (if (q.1 + unitStep m q.2.1, q.2.2) = b then (1 : ℝ) else 0) -
          (if (q.1 + unitStep m q.2.2, q.2.1) = b then (1 : ℝ) else 0) -
          (if (q.1, q.2.2) = b then (1 : ℝ) else 0) := by
        unfold curlFunctional WeightedResponses.curl
        rfl
      rw [e]
      have n1 : (0 : ℝ) ≤ if (q.1, q.2.1) = b then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      have n2 : (0 : ℝ) ≤ if (q.1 + unitStep m q.2.1, q.2.2) = b then (1 : ℝ) else 0 := by
        split_ifs <;> norm_num
      have n3 : (0 : ℝ) ≤ if (q.1 + unitStep m q.2.2, q.2.1) = b then (1 : ℝ) else 0 := by
        split_ifs <;> norm_num
      have n4 : (0 : ℝ) ≤ if (q.1, q.2.2) = b then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      rw [abs_le]
      constructor <;> linarith
    calc |curlFunctional q b| * w b ≤ _ := mul_le_mul_of_nonneg_right hc hwp
      _ = _ := by ring
  unfold expWeightedSum
  calc ∑ b, |curlFunctional q b| * Real.exp (θ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) ≤ ∑ b, _ :=
        Finset.sum_le_sum fun b _ => hterm b
    _ = w (q.1, q.2.1) + w (q.1 + unitStep m q.2.1, q.2.2) + w (q.1 + unitStep m q.2.2, q.2.1) +
          w (q.1, q.2.2) := by
        simp only [Finset.sum_add_distrib, hone]
    _ ≤ 4 * Real.exp (θ * (R + 1)) := by
        have h1 := hb (q.1, q.2.1) (by simpa using (by linarith : (supDist q.1 o : ℝ) ≤ R + 1))
        have h2 := hb (q.1 + unitStep m q.2.1, q.2.2) (hnear _)
        have h3 := hb (q.1 + unitStep m q.2.2, q.2.1) (hnear _)
        linarith
private theorem sum_abs_adjointTransport_far_le (k N : ℕ) {κ K : ℝ} (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    (H : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ b : TorusBond (n * L),
      ∑ c : TorusBond n, |responseKernel a ρA L u b c| * Real.exp (κ * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1) ≤ K)
    (d n : ℕ) [NeZero n] (hn : N ≤ n) (o : TorusSite (fineSide L d (n * L)))
    (q : TorusPlaquette (fineSide L d (n * L)))
    (nn ρ₀ : ℝ) (hnn : 0 ≤ nn) (hq : q.1 ∈ supBall o (19 * nn)) (S : Finset (TorusBond (n * L)))
    (hS : ∀ b ∈ S, parentBlock L b.1 ∉ supBall (siteAbove L d (n * L) o |> parentBlock L)
      (ballRadius L nn ρ₀ (d + 1) - 3 * ρ₀)) :
    ∑ b ∈ S, |adjointTransport a ρA L k d (n * L) (curlFunctional q) b| ≤
      4 * (K * Real.exp κ) ^ d * Real.exp (2 * κ - κ * ρ₀) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hnL : N ≤ n * L := hn.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne L)))
  set D : ℝ := (L : ℝ) ^ (d + 1) with hD
  have hD1 : 1 ≤ D := one_le_pow₀ hL1
  have hDp : 0 < D := by linarith
  set θ := κ / D with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθd : θ * (L : ℝ) ^ d = κ / L := by
    rw [hθ, hD, pow_succ]
    field_simp
  have hκL : κ / L ≤ κ := div_le_self hκ hL1
  have hW := expWeightedSum_adjointTransport_le k N hK H d (n * L) inferInstance hnL (curlFunctional q) o θ hθ0
    (by rw [hθd]; exact hκL)
  rw [hθd] at hW
  set g := adjointTransport a ρA L k d (n * L) (curlFunctional q) with hg
  set o₁ := siteAbove L d (n * L) o with ho₁
  have hqd : (_root_.YangMills.Construction.TorusFields.supDist q.1 o : ℝ) ≤ 19 * nn := by
    have h0 := hq
    unfold supBall at h0
    exact (Finset.mem_filter.mp h0).2
  have hC := expWeightedSum_curlFunctional_le q o hθ0 hqd
  set R := ballRadius L nn ρ₀ (d + 1) - 3 * ρ₀ with hR
  have hRe : R = 20 * nn / D + ρ₀ := by
    rw [hR, ballRadius]
    ring
  have hfar : ∀ b ∈ S, κ * (R - 1) ≤ κ / L * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁ := by
    intro b hb
    have h1 := hS b hb
    have h2 : R < _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) (parentBlock L o₁) := by
      by_contra hc
      refine h1 ?_
      unfold supBall
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hc⟩
    have h3 : (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) (parentBlock L o₁) : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist b.1 o₁ : ℝ) / L + 1 := by
      have h4 := TorusBalls.supDist_parentBlock_le_div_add_one (n := n) L b.1 o₁
      have h5 : ((_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) (parentBlock L o₁) : ℕ) : ℝ) ≤
          ((_root_.YangMills.Construction.TorusFields.supDist b.1 o₁ / L + 1 : ℕ) : ℝ) := by
        exact_mod_cast h4
      push_cast at h5
      exact h5.trans (by gcongr; exact Nat.cast_div_le)
    have h6 : R - 1 ≤ (_root_.YangMills.Construction.TorusFields.supDist b.1 o₁ : ℝ) / L := by linarith
    calc κ * (R - 1) ≤ κ * ((_root_.YangMills.Construction.TorusFields.supDist b.1 o₁ : ℝ) / L) := mul_le_mul_of_nonneg_left h6 hκ
      _ = κ / L * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁ := by ring
  have hQ0 : 0 ≤ (K * Real.exp κ) ^ d := by positivity
  calc ∑ b ∈ S, |g b|
      ≤ ∑ b ∈ S, |g b| * Real.exp (κ / L * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁) * Real.exp (-(κ * (R - 1))) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have h1 : 1 ≤ Real.exp (κ / L * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁) * Real.exp (-(κ * (R - 1))) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith [hfar b hb])
        calc |g b| = |g b| * 1 := (mul_one _).symm
          _ ≤ |g b| * (Real.exp (κ / L * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁) * Real.exp (-(κ * (R - 1)))) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = _ := by ring
    _ ≤ ∑ b, |g b| * Real.exp (κ / L * _root_.YangMills.Construction.TorusFields.supDist b.1 o₁) * Real.exp (-(κ * (R - 1))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = expWeightedSum g o₁ (κ / L) * Real.exp (-(κ * (R - 1))) := by
        unfold expWeightedSum
        rw [Finset.sum_mul]
    _ ≤ (K * Real.exp κ) ^ d * (4 * Real.exp (θ * (19 * nn + 1))) * Real.exp (-(κ * (R - 1))) :=
        mul_le_mul_of_nonneg_right (hW.trans (mul_le_mul_of_nonneg_left hC hQ0)) (Real.exp_pos _).le
    _ = 4 * (K * Real.exp κ) ^ d * Real.exp (θ * (19 * nn + 1) - κ * (R - 1)) := by
        rw [show θ * (19 * nn + 1) - κ * (R - 1) = θ * (19 * nn + 1) + -(κ * (R - 1)) by ring, Real.exp_add]
        ring
    _ ≤ 4 * (K * Real.exp κ) ^ d * Real.exp (2 * κ - κ * ρ₀) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have q1 : (19 * nn + 1) / D ≤ 20 * nn / D + 1 := by
          rw [div_le_iff₀ hDp]
          have e : (20 * nn / D + 1) * D = 20 * nn + D := by field_simp
          rw [e]
          linarith
        have q2 : θ * (19 * nn + 1) = κ * ((19 * nn + 1) / D) := by
          rw [hθ]
          ring
        have q3 := mul_le_mul_of_nonneg_left q1 hκ
        rw [q2, hRe]
        linarith
end AdjointPairing
private theorem exists_chainDepth_price_le {κ Q : ℝ} (hκ : 0 < κ) (hQ : 1 ≤ Q) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, d < chainDepth x →
      4 * Q ^ d * Real.exp (2 * κ - κ * logCubeScale x) ≤ Real.exp (-(κ / 2 * logCubeScale x)) := by
  set A := Real.log Q with hA
  have hA0 : 0 ≤ A := Real.log_nonneg hQ
  set D := 3 + 3 * κ with hD
  have hD0 : 0 ≤ D := by positivity
  set l₀ := max 1 (2 * (D + A) / κ) with hl₀
  refine ⟨Real.exp l₀, fun x hx d hd => ?_⟩
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hdepth : ((chainDepth x : ℕ) : ℝ) ≤ Real.log x ^ 2 := Nat.floor_le (sq_nonneg _)
  have hρ : Real.log x ^ 3 - 1 ≤ logCubeScale x := by
    have h0 := Nat.lt_floor_add_one (Real.log x ^ 3)
    unfold logCubeScale
    linarith
  set l := Real.log x with hl
  have hll : l₀ ≤ l := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hl1 : 1 ≤ l := (le_max_left _ _).trans hll
  have hl2 : D + A ≤ κ / 2 * l := by
    have h0 : 2 * (D + A) / κ ≤ l := (le_max_right _ _).trans hll
    rw [div_le_iff₀ hκ] at h0
    linarith
  have hdl : (d : ℝ) ≤ l ^ 2 := by
    have h1 : (d : ℝ) ≤ (chainDepth x : ℝ) := by exact_mod_cast hd.le
    exact h1.trans hdepth
  have hlog4 : Real.log 4 ≤ 3 := by
    have h0 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hQd : Q ^ d = Real.exp (d * A) := by
    rw [Real.exp_nat_mul, hA, Real.exp_log (by linarith)]
  rw [hQd]
  calc 4 * Real.exp (d * A) * Real.exp (2 * κ - κ * logCubeScale x)
      = Real.exp (Real.log 4 + d * A + (2 * κ - κ * logCubeScale x)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h5 : (d : ℝ) * A ≤ l ^ 2 * A := mul_le_mul_of_nonneg_right hdl hA0
        have h6 : (D + A) * l ^ 2 ≤ κ / 2 * l * l ^ 2 := mul_le_mul_of_nonneg_right hl2 (by positivity)
        have h7 : D * 1 ≤ D * l ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hD0
        have h8 : κ / 2 * (l ^ 3 - 1) ≤ κ / 2 * logCubeScale x := mul_le_mul_of_nonneg_left hρ (by positivity)
        nlinarith
private theorem norm_unitGenerator : ‖unitGenerator‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
private theorem abs_responseKernel_le {a ρA del C : ℝ} {L L₀ : ℕ} [NeZero L] (hodd : Odd L) (hL : L₀ ≤ L)
    (hC : 0 < C) (hcov : BlocksCoverLowerLevel)
    (hS : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F) (W : LevelForm F F.depth),
      Odd F.blockSide → L₀ ≤ F.blockSide → IsLargeCubicTorus F → IsFlatChain a c B → IsAxialResponse c B W →
      ∀ b ∈ chordBonds (finiteCells F),
        |W b.1 b.2| ≤ C * (F.blockSide : ℝ) ^ 3 * Real.exp (-(del * cellSupDist (enclosingCell b.1) c.1)))
    (hT : ∀ (F : BlockFrame) (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions), F.blockSide = L →
      IsLargeCubicTorus F → ‖X‖ = 1 →
      ∃ B : FormChain F, IsFlatChain a b B ∧ IsAxialResponse b B (minimizerResponse a ρA b X))
    (u n : ℕ) [NeZero n] (hn : 64 ≤ n) (b : TorusBond (n * L)) (c : TorusBond n) :
    |responseKernel a ρA L u b c| ≤ C * (L : ℝ) ^ 3 * Real.exp (-(del * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1)) := by
  classical
  have hcub : IsLargeCubicTorus (torusFrame L u n) := ⟨n, hn, fun _ => rfl⟩
  obtain ⟨B, hf, ht⟩ := hT (torusFrame L u n)
    (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) unitGenerator rfl
    hcub norm_unitGenerator
  by_cases htree : IsAxialTreeBond (F := torusFrame L u n)
      (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
  · have h0 := ht.vanishes_on_tree _ htree
    have e : responseKernel a ρA L u b c = 0 := h0
    rw [e, abs_zero]
    positivity
  · have hpos : ∀ i, 0 < (torusFrame L u n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
    have hall : ∀ x : (torusFrame L u n).Site (torusFrame L u n).depth,
        x ∈ sitesOfCells (finiteCells (torusFrame L u n)) (torusFrame L u n).depth :=
      hcov (torusFrame L u n) hodd hpos
    have hmem : (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∈
        chordBonds (finiteCells (torusFrame L u n)) := by
      unfold chordBonds innerBonds
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hall _, Finset.mem_univ _⟩, hall _⟩, htree⟩
    have h1 := hS (torusFrame L u n) _ B _ hodd hL hcub hf ht _ hmem
    have e : cellSupDist (enclosingCell (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1))
        (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1) =
          _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 := by
      have : NeZero (n * (torusFrame L u n).blockSide) := (inferInstance : NeZero (n * L))
      have e1 : enclosingCell (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1) =
          StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top (parentBlock L b.1) :=
        TopLevelSites.enclosingCell_torusSiteInFrame (F := torusFrame L u n) (n := n) (fun _ => rfl) b.1
      rw [e1, TorusFrame.cellSupDist_torusFrame, TorusFrame.siteOfCell_torusSiteInFrame,
        TorusFrame.siteOfCell_torusSiteInFrame]
    have e2 : (torusFrame L u n).blockSide = L := rfl
    rw [e, e2] at h1
    exact h1
private theorem sum_responseKernel_exp_le {a ρA del C₁ : ℝ} {L N : ℕ} [NeZero L] (hdel : 0 < del) (hC : 0 ≤ C₁)
    (he : ∀ (u n : ℕ) [NeZero n], N ≤ n → ∀ (b : TorusBond (n * L)) (c : TorusBond n),
      |responseKernel a ρA L u b c| ≤ C₁ * Real.exp (-(del * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1)))
    (u n : ℕ) [NeZero n] (hn : N ≤ n) (b : TorusBond (n * L)) :
    ∑ c : TorusBond n, |responseKernel a ρA L u b c| * Real.exp (del / 2 * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1) ≤
      C₁ * (4 * ExponentialSums.expLatticeSum (del / 2)) := by
  calc ∑ c : TorusBond n, |responseKernel a ρA L u b c| * Real.exp (del / 2 * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1)
      ≤ ∑ c : TorusBond n, C₁ * Real.exp (-(del / 2) * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L b.1)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        calc |responseKernel a ρA L u b c| * Real.exp (del / 2 * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1)
            ≤ C₁ * Real.exp (-(del * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1)) *
                Real.exp (del / 2 * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1) :=
              mul_le_mul_of_nonneg_right (he u n hn b c) (Real.exp_pos _).le
          _ = C₁ * Real.exp (-(del / 2) * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L b.1)) := by
              rw [mul_assoc, ← Real.exp_add, _root_.YangMills.Construction.TorusFields.supDist_comm]
              congr 2
              ring
    _ = C₁ * ∑ c : TorusBond n, Real.exp (-(del / 2) * _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock L b.1)) := by
        rw [Finset.mul_sum]
    _ ≤ C₁ * (4 * ExponentialSums.expLatticeSum (del / 2)) :=
        mul_le_mul_of_nonneg_left (ExponentialSums.sum_bonds_exp_le (by positivity) _ Finset.univ) hC
end TransportedCurlBounds
open TransportedCurlBounds in
theorem transportedCurlFunctionalBounds (h₁ : ResponseContractsCurvatureStatement)
    (h₂ : axialResponseDecay) (h₃ : AxialResponseOfMinimizers)
    (h₄ : BlocksCoverLowerLevel) : transportedCurlFunctionalBoundsStatement := by
  intro a ha
  obtain ⟨L₁, rt₀, C₀, hrt, h1⟩ := h₁ a ha
  obtain ⟨del, C, hdel, -, hC, L₂, hS⟩ := h₂ a ha
  refine ⟨max L₁ L₂, rt₀, C₀, hrt, fun L hodd hL T hTa hTL hD hCS hCH hrtle hCd => ?_⟩
  obtain ⟨y₀, hy⟩ := h1 L hodd ((le_max_left _ _).trans hL) T hTa hTL hD hCS hCH hrtle hCd
  refine ⟨y₀, fun y hyy hrow hw => ?_⟩
  have hcon := hy y hyy hrow hw
  obtain ⟨c, nss, hties, -⟩ := hCS
  obtain ⟨-, -, hρ, -, -, -, -, hholds⟩ := hties
  subst hTL
  subst hTa
  have hn64 : ∀ n : ℕ, T.n₀ ≤ n → 64 ≤ n := by
    intro n h
    have := hD.n₀_ge
    omega
  have hcon' : ∀ (u n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (A : TorusBond n → ℝ) (s : ℝ),
      (∀ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |WeightedResponses.curl A q| ≤ s) →
      ∀ q ∈ plaquettesIn (Finset.univ : Finset (TorusSite (n * (T.stepParameters y).side))),
        |WeightedResponses.curl (responseMap T.coupling T.ρA (T.stepParameters y).side u A) q| ≤ s / 8 :=
    fun u n _ hn => hcon u n (hn64 n hn)
  have hT : ∀ (F : BlockFrame) (b : F.Site F.top × Fin 4) (X : imaginaryQuaternions),
      F.blockSide = (T.stepParameters y).side → IsLargeCubicTorus F → ‖X‖ = 1 →
      ∃ B : FormChain F, IsFlatChain T.coupling b B ∧ IsAxialResponse b B (minimizerResponse T.coupling T.ρA b X) := by
    intro F b X hF hcub hX
    have h0 := h₃ T.coupling ha T.side hodd c hholds F b X hF hcub hX
    rwa [hρ] at h0
  set C₁ : ℝ := C * ((T.stepParameters y).side : ℝ) ^ 3 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have he : ∀ (u n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (b : TorusBond (n * (T.stepParameters y).side))
      (c' : TorusBond n),
      |responseKernel T.coupling T.ρA (T.stepParameters y).side u b c'| ≤
        C₁ * Real.exp (-(del * _root_.YangMills.Construction.TorusFields.supDist (parentBlock (T.stepParameters y).side b.1) c'.1)) :=
    fun u n _ hn b c' =>
      abs_responseKernel_le (L₀ := L₂) hodd ((le_max_right _ _).trans hL) hC h₄ hS hT u n (hn64 n hn) b c'
  have hκ : 0 < del / 2 := by positivity
  set K : ℝ := max 1 (C₁ * (4 * ExponentialSums.expLatticeSum (del / 2))) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := by linarith
  have hrowK : ∀ (u n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ b : TorusBond (n * (T.stepParameters y).side),
      ∑ c' : TorusBond n, |responseKernel T.coupling T.ρA (T.stepParameters y).side u b c'| *
        Real.exp (del / 2 * _root_.YangMills.Construction.TorusFields.supDist (parentBlock (T.stepParameters y).side b.1) c'.1) ≤ K :=
    fun u n _ hn b => (sum_responseKernel_exp_le hdel hC₁0 he u n hn b).trans (le_max_right _ _)
  have hQ : 1 ≤ K * Real.exp (del / 2) := by
    have h0 : 1 ≤ Real.exp (del / 2) := Real.one_le_exp hκ.le
    nlinarith
  obtain ⟨x₀, hx₀⟩ := exists_chainDepth_price_le hκ hQ
  unfold transportedCurlFunctionalBoundsAt
  refine ⟨?_, del / 2 / 2, x₀, by positivity, ?_⟩
  · intro k d n _ hn q hq
    have hA : ∀ (B : TorusBond n → ℝ) (s : ℝ),
        (∀ q' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |WeightedResponses.curl B q'| ≤ s) →
        |∑ c', adjointTransport T.coupling T.ρA (T.stepParameters y).side k d n (curlFunctional q) c' * B c'| ≤
          (1 / 2 : ℝ) ^ d * s := by
      intro B s hB
      obtain ⟨q₀, hq₀⟩ := exists_plaquette n
      have hs : 0 ≤ s := (abs_nonneg _).trans (hB q₀ hq₀)
      exact abs_sum_adjointTransport_le k T.n₀ hcon' d n inferInstance hn q hq B s hs hB
    refine ⟨hA, ?_⟩
    refine sum_abs_le_of_curl_bound _ _ fun B hB => ?_
    have h0 := hA B 4 hB
    rwa [mul_comm] at h0
  · intro x nn k d n _ hx hnn hn hd o q _ hbox
    refine (sum_abs_adjointTransport_far_le k T.n₀ hκ.le hK0 hrowK d n hn o q nn (logCubeScale x) hnn hbox _
      fun b hb => (Finset.mem_filter.mp hb).2).trans ?_
    exact hx₀ x hx d hd
end ResponseInTheExpansion
end YangMills.Construction
end
