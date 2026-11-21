import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormFromASmallDifferenceProof
import YangMills.Construction.ClusterExpansionOfAStep.ExponentialSumsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFields
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorusProof
import YangMills.Construction.LawInAState.TheFormOfAFamilyOnABox
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LatticeSums
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.ExponentialSums YangMills.Construction.BoxForm
theorem abs_le_offsetSupNorm (a : Fin 4 → ℤ) (i : Fin 4) : |(a i : ℝ)| ≤ offsetSupNorm a := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
theorem natAbs_le_offsetSupNorm (a : Fin 4 → ℤ) (i : Fin 4) : (a i).natAbs ≤ offsetSupNorm a := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem mem_bondsWithin_iff {m : ℕ} {c : LatticeBond} : c ∈ bondsWithin m ↔ offsetSupNorm c.1 ≤ m := by
  simp only [bondsWithin, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_univ, and_true]
  constructor
  · intro hc
    refine Finset.sup_le fun i _ => ?_
    have := hc i
    omega
  · intro hc i
    have := natAbs_le_offsetSupNorm c.1 i
    omega
variable {n : ℕ}
theorem siteOfInt_add_eq (a b : Fin 4 → ℤ) : (siteOfInt (a + b) : TorusSite n) = siteOfInt a + siteOfInt b := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
theorem siteOfInt_single (i : Fin 4) : (siteOfInt (Pi.single i 1) : TorusSite n) = unitStep n i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
variable [NeZero n]
theorem intCast_valMinAbs_eq {k : ℤ} (hk : 2 * k.natAbs < n) : ((k : ZMod n)).valMinAbs = k := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusOffsets.valMinAbs_intCast_of_lt <;> assumption
theorem supDist_add_siteOfInt_le (z : TorusSite n) (a : Fin 4 → ℤ) :
    supDist (z + siteOfInt a) z ≤ offsetSupNorm a := by
  rw [supDist_le_iff]
  intro i
  have hsub : (z + siteOfInt a : TorusSite n) i - z i = (a i : ZMod n) := by simp [siteOfInt]
  rw [hsub]
  exact (natAbs_valMinAbs_intCast_le _).trans (natAbs_le_offsetSupNorm a i)
theorem supDist_add_siteOfInt (z : TorusSite n) {a : Fin 4 → ℤ} (ha : 2 * offsetSupNorm a < n) :
    supDist (z + siteOfInt a) z = offsetSupNorm a := by
  refine le_antisymm (supDist_add_siteOfInt_le z a) (Finset.sup_le fun i _ => ?_)
  have hsub : (z + siteOfInt a : TorusSite n) i - z i = (a i : ZMod n) := by simp [siteOfInt]
  have hai := natAbs_le_offsetSupNorm a i
  have hval : (((a i : ℤ) : ZMod n)).valMinAbs = a i := intCast_valMinAbs_eq (by omega)
  have hcoord := (supDist_le_iff (z + siteOfInt a) z _).1 le_rfl i
  rw [hsub, hval] at hcoord
  exact hcoord
theorem siteOfInt_inj_of_small {a a' : Fin 4 → ℤ} (ha : 2 * offsetSupNorm a < n) (ha' : 2 * offsetSupNorm a' < n)
    (heq : (siteOfInt a : TorusSite n) = siteOfInt a') : a = a' := by
  funext i
  have hcoord : ((a i : ℤ) : ZMod n) = (a' i : ℤ) := congrFun heq i
  have hai := natAbs_le_offsetSupNorm a i
  have hai' := natAbs_le_offsetSupNorm a' i
  have hval : (((a i : ℤ) : ZMod n)).valMinAbs = a i := intCast_valMinAbs_eq (by omega)
  have hval' : (((a' i : ℤ) : ZMod n)).valMinAbs = a' i := intCast_valMinAbs_eq (by omega)
  rw [← hval, ← hval', hcoord]
theorem bondFrom_inj_of_small (z : TorusSite n) {c c' : LatticeBond} (hc : 2 * offsetSupNorm c.1 < n)
    (hc' : 2 * offsetSupNorm c'.1 < n) (heq : bondFrom z c = bondFrom z c') : c = c' := by
  have hsite : z + siteOfInt c.1 = z + siteOfInt c'.1 := congrArg Prod.fst heq
  have hdir : c.2 = c'.2 := by
    have := congrArg (fun b : TorusBond n => b.2) heq
    simpa [bondFrom] using this
  exact Prod.ext (siteOfInt_inj_of_small hc hc' (add_left_cancel hsite)) hdir
omit [NeZero n] in
theorem summable_pi_prod {f : ℤ → ℝ} (hf : Summable f) (hf0 : ∀ k, 0 ≤ f k) :
    ∀ k : ℕ, Summable fun a : Fin k → ℤ => ∏ i, f (a i)
  | 0 => summable_of_finite_support (Set.toFinite _)
  | k + 1 => by
    have ih := summable_pi_prod hf hf0 k
    have hprod := Summable.mul_of_nonneg hf ih hf0 (fun a => Finset.prod_nonneg fun _ _ => hf0 _)
    let e : (Fin (k + 1) → ℤ) ≃ ℤ × (Fin k → ℤ) :=
      ⟨fun a => (a 0, Fin.tail a), fun p => Fin.cons p.1 p.2, fun a => Fin.cons_self_tail a, fun p => by simp⟩
    have he := e.summable_iff.2 hprod
    refine he.congr fun a => ?_
    simp [e, Fin.prod_univ_succ, Fin.tail]
omit [NeZero n] in
theorem summable_exp_neg_offsetSupNorm {θ : ℝ} (hθ : 0 < θ) :
    Summable fun a : Fin 4 → ℤ => Real.exp (-θ * offsetSupNorm a) := by
  have hpi := summable_pi_prod (summable_exp_neg_mul_abs (show 0 < θ / 4 by positivity))
    (fun _ => (Real.exp_pos _).le) 4
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun a => ?_) hpi
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hsum : ∑ i : Fin 4, |(a i : ℝ)| ≤ 4 * offsetSupNorm a := by
    calc _ ≤ ∑ _i : Fin 4, (offsetSupNorm a : ℝ) := Finset.sum_le_sum fun i _ => abs_le_offsetSupNorm a i
      _ = _ := by simp
  rw [← Finset.mul_sum]
  nlinarith
omit [NeZero n] in
theorem one_add_pow_mul_exp_le {θ : ℝ} (hθ : 0 < θ) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ k * Real.exp (-θ * x) ≤ (2 * (k + 1) / θ + 1) ^ k * Real.exp (-(θ / 2) * x) := by
  set ε := θ / (2 * (k + 1)) with hε
  have hεpos : 0 < ε := by positivity
  set A := 2 * ((k : ℝ) + 1) / θ + 1 with hA
  have hAε : A = 1 / ε + 1 := by
    rw [hA, hε]
    field_simp
  have hlin : 1 + x ≤ A * Real.exp (ε * x) := by
    have hexp := Real.add_one_le_exp (ε * x)
    have haff : 1 + x ≤ A * (ε * x + 1) := by
      rw [hAε]
      have : (1 / ε + 1) * (ε * x + 1) = x + 1 / ε + ε * x + 1 := by
        field_simp
        ring
      rw [this]
      have : 0 < 1 / ε := by positivity
      nlinarith [mul_nonneg hεpos.le hx]
    have hApos : 0 < A := by positivity
    exact haff.trans (mul_le_mul_of_nonneg_left hexp hApos.le)
  have hpow : (1 + x) ^ k ≤ A ^ k * Real.exp (k * (ε * x)) := by
    calc (1 + x) ^ k ≤ (A * Real.exp (ε * x)) ^ k := pow_le_pow_left₀ (by linarith) hlin k
      _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]
  have hkε : (k : ℝ) * ε ≤ θ / 2 := by
    rw [hε]
    rw [show (k : ℝ) * (θ / (2 * (k + 1))) = θ / 2 * (k / (k + 1)) by field_simp]
    have : (k : ℝ) / (k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  calc (1 + x) ^ k * Real.exp (-θ * x)
      ≤ A ^ k * Real.exp (k * (ε * x)) * Real.exp (-θ * x) := by gcongr
    _ = A ^ k * Real.exp (k * (ε * x) + -θ * x) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ A ^ k * Real.exp (-(θ / 2) * x) := by
      have hA0 : 0 ≤ A := by positivity
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg hA0 k)
      nlinarith
omit [NeZero n] in
theorem summable_bond_pow_mul_exp {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    Summable fun c : LatticeBond => (1 + (offsetSupNorm c.1 : ℝ)) ^ k * Real.exp (-θ * offsetSupNorm c.1) := by apply _root_.YangMills.DeltaSharedProofs.p500449 <;> assumption
def bondWeightSum (θ : ℝ) (k : ℕ) : ℝ :=
  ∑' c : LatticeBond, (1 + (offsetSupNorm c.1 : ℝ)) ^ k * Real.exp (-θ * offsetSupNorm c.1)
omit [NeZero n] in
theorem sum_le_bondWeightSum {θ : ℝ} (hθ : 0 < θ) (k : ℕ) (s : Finset LatticeBond) :
    ∑ c ∈ s, (1 + (offsetSupNorm c.1 : ℝ)) ^ k * Real.exp (-θ * offsetSupNorm c.1) ≤ bondWeightSum θ k :=
  (summable_bond_pow_mul_exp hθ k).sum_le_tsum s fun _ _ => by positivity
omit [NeZero n] in
theorem bondWeightSum_nonneg (θ : ℝ) (k : ℕ) : 0 ≤ bondWeightSum θ k := tsum_nonneg fun _ => by positivity
theorem sum_torusBonds_pow_mul_exp_le {θ : ℝ} (hθ : 0 < θ) (k : ℕ) (z : TorusSite n) :
    ∑ b : TorusBond n, (1 + (supDist b.1 z : ℝ)) ^ k * Real.exp (-θ * supDist b.1 z) ≤
      (2 * (k + 1) / θ + 1) ^ k * (4 * expLatticeSum (θ / 2)) := by
  have hexp := sum_bonds_exp_le (show 0 < θ / 2 by positivity) z (Finset.univ : Finset (TorusBond n))
  calc _ ≤ ∑ b : TorusBond n, (2 * (k + 1) / θ + 1) ^ k * Real.exp (-(θ / 2) * supDist b.1 z) :=
        Finset.sum_le_sum fun b _ => one_add_pow_mul_exp_le hθ k (Nat.cast_nonneg _)
    _ = _ * ∑ b : TorusBond n, Real.exp (-(θ / 2) * supDist b.1 z) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
end YangMills.Construction.LatticeSums
end
