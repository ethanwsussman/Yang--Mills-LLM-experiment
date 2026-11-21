import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.ClusterExpansionOfAStep.ExponentialSumsOnATorus
import YangMills.Construction.RunningCouplingSlope.ContourKernelsAreLocal
import YangMills.Construction.RunningCouplingSlope.CurlOfTheMeanOverContoursProof
import YangMills.Construction.RunningCouplingSlope.FloorOfFormsOffTheTrees
import YangMills.Construction.RunningCouplingSlope.GreenKernelsOfAChainForm
import YangMills.Construction.RunningCouplingSlope.InverseOfAPositiveDecayingKernel
import YangMills.Construction.RunningCouplingSlope.SumsOverToriTendToSumsOverTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open TorusFields TorusLumps ExponentialSums FlatLinearization
section Geometry
variable {n L : ℕ}
private theorem blockCentreSite_eq_torusBlockCentreSite [NeZero n] (y : TorusSite n) :
    SlopeCoefficient.blockCentreSite L y = TorusBlocks.blockCentreSite L y := by apply _root_.YangMills.SharedProofs.p7467 <;> assumption
private theorem supDist_parentBlock_le_six [NeZero n] [NeZero L] (hL : Odd L) (x : TorusSite (n * L))
    (y : TorusSite n) (h : supDist x (SlopeCoefficient.blockCentreSite L y) ≤ 5 * L) :
    supDist (parentBlock L x) y ≤ 6 := by
  have hb := TorusBalls.supDist_parentBlock_le_div_add_one (n := n) L x (SlopeCoefficient.blockCentreSite L y)
  rw [blockCentreSite_eq_torusBlockCentreSite, TorusBlocks.parentBlock_blockCentreSite hL] at hb
  rw [blockCentreSite_eq_torusBlockCentreSite] at h
  have : supDist x (TorusBlocks.blockCentreSite L y) / L ≤ 5 :=
    Nat.div_le_of_le_mul (by have e : L * 5 = 5 * L := Nat.mul_comm _ _; omega)
  omega
private theorem sum_bond_exp_supDist_le [NeZero n] {c : ℝ} (hc : 0 < c) (z : TorusSite n) :
    ∑ b : TorusBond n, Real.exp (-c * supDist b.1 z) ≤ 4 * expLatticeSum c := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have := sum_torus_exp_le hc z
  push_cast
  linarith
private theorem sum_abs_contourWeight_le [NeZero n] [NeZero L] (hL : Odd L) {C : ℝ} (hC : 0 ≤ C)
    (hk : ∀ (c : TorusBond n) (b : TorusBond (n * L)), |contourWeight L c b| ≤ C ∧
      (5 * L < supDist b.1 (SlopeCoefficient.blockCentreSite L c.1) → contourWeight L c b = 0))
    (b : TorusBond (n * L)) :
    ∑ c : TorusBond n, |contourWeight L c b| ≤ C * (Real.exp 6 * (4 * expLatticeSum 1)) := by
  have hterm : ∀ c : TorusBond n, |contourWeight L c b| ≤
      C * Real.exp 6 * Real.exp (-1 * supDist c.1 (parentBlock L b.1)) := by
    intro c
    by_cases hd : 5 * L < supDist b.1 (SlopeCoefficient.blockCentreSite L c.1)
    · rw [(hk c b).2 hd, abs_zero]
      positivity
    · have h6 := supDist_parentBlock_le_six hL b.1 c.1 (not_lt.mp hd)
      rw [supDist_comm] at h6
      have h6' : ((supDist c.1 (parentBlock L b.1) : ℕ) : ℝ) ≤ 6 := by exact_mod_cast h6
      have : 1 ≤ Real.exp 6 * Real.exp (-1 * supDist c.1 (parentBlock L b.1)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      calc |contourWeight L c b| ≤ C := (hk c b).1
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * (Real.exp 6 * Real.exp (-1 * supDist c.1 (parentBlock L b.1))) :=
            mul_le_mul_of_nonneg_left this hC
        _ = _ := by ring
  calc ∑ c : TorusBond n, |contourWeight L c b|
      ≤ ∑ c : TorusBond n, C * Real.exp 6 * Real.exp (-1 * supDist c.1 (parentBlock L b.1)) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = C * Real.exp 6 * ∑ c : TorusBond n, Real.exp (-1 * supDist c.1 (parentBlock L b.1)) := by
        rw [Finset.mul_sum]
    _ ≤ C * Real.exp 6 * (4 * expLatticeSum 1) :=
        mul_le_mul_of_nonneg_left (sum_bond_exp_supDist_le one_pos _) (by positivity)
    _ = _ := by ring
end Geometry
section Operator
variable {n L : ℕ}
private theorem flatStepOperator_symm_of_symm [NeZero n] {a : ℝ} {K : TorusBond (n * L) → TorusBond (n * L) → ℝ}
    (hK : ∀ b c, K b c = K c b) (b c : TorusBond (n * L)) :
    flatStepOperator a L K b c = flatStepOperator a L K c b := by
  unfold flatStepOperator
  by_cases h : IsBlockTreeBond L b ∨ IsBlockTreeBond L c
  · rw [if_pos h, if_pos h.symm]
    by_cases e : b = c
    · rw [if_pos e, if_pos e.symm]
    · rw [if_neg e, if_neg (Ne.symm e)]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), hK b c]
    simp only [mul_comm]
private theorem abs_flatStepOperator_le [NeZero n] [NeZero L] (hL : Odd L) {a C Mh θ : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hθ : 0 < θ)
    (hk : ∀ (c : TorusBond n) (b : TorusBond (n * L)), |contourWeight L c b| ≤ C ∧
      (5 * L < supDist b.1 (SlopeCoefficient.blockCentreSite L c.1) → contourWeight L c b = 0))
    {K : TorusBond (n * L) → TorusBond (n * L) → ℝ}
    (hK : ∀ b c, |K b c| ≤ Mh * Real.exp (-(θ * supDist b.1 c.1))) (b c : TorusBond (n * L)) :
    |flatStepOperator a L K b c| ≤
      (1 + |Mh| + a * (C * (C * (Real.exp 6 * (4 * expLatticeSum 1))) * Real.exp (θ * (10 * L)))) *
        Real.exp (-(θ * supDist b.1 c.1)) := by
  set D : ℝ := Real.exp 6 * (4 * expLatticeSum 1) with hD
  have hD0 : 0 ≤ C * D := by
    have := (Finset.sum_nonneg (s := Finset.univ) fun (c' : TorusBond n) _ =>
      abs_nonneg (contourWeight L c' b)).trans (sum_abs_contourWeight_le hL hC hk b)
    exact this
  have hE : 0 < Real.exp (-(θ * supDist b.1 c.1)) := Real.exp_pos _
  have hterm : ∀ c' : TorusBond n, |contourWeight L c' b * contourWeight L c' c| ≤
      |contourWeight L c' b| * (C * (Real.exp (θ * (10 * L)) * Real.exp (-(θ * supDist b.1 c.1)))) := by
    intro c'
    rw [abs_mul]
    by_cases h1 : 5 * L < supDist b.1 (SlopeCoefficient.blockCentreSite L c'.1)
    · rw [(hk c' b).2 h1]; simp
    by_cases h2 : 5 * L < supDist c.1 (SlopeCoefficient.blockCentreSite L c'.1)
    · rw [(hk c' c).2 h2]
      simp only [abs_zero, mul_zero]
      positivity
    have hd : supDist b.1 c.1 ≤ 10 * L := by
      have := supDist_triangle b.1 (SlopeCoefficient.blockCentreSite L c'.1) c.1
      rw [supDist_comm (SlopeCoefficient.blockCentreSite L c'.1) c.1] at this
      omega
    have hd' : ((supDist b.1 c.1 : ℕ) : ℝ) ≤ 10 * L := by exact_mod_cast hd
    have : 1 ≤ Real.exp (θ * (10 * L)) * Real.exp (-(θ * supDist b.1 c.1)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hd' hθ.le
      linarith
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |contourWeight L c' c| ≤ C := (hk c' c).1
      _ = C * 1 := (mul_one C).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left this hC
  have hsum : |∑ c' : TorusBond n, contourWeight L c' b * contourWeight L c' c| ≤
      C * (C * D) * Real.exp (θ * (10 * L)) * Real.exp (-(θ * supDist b.1 c.1)) := by
    calc |∑ c' : TorusBond n, contourWeight L c' b * contourWeight L c' c|
        ≤ ∑ c' : TorusBond n, |contourWeight L c' b * contourWeight L c' c| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c' : TorusBond n, |contourWeight L c' b| *
            (C * (Real.exp (θ * (10 * L)) * Real.exp (-(θ * supDist b.1 c.1)))) :=
          Finset.sum_le_sum fun c' _ => hterm c'
      _ = (∑ c' : TorusBond n, |contourWeight L c' b|) *
            (C * (Real.exp (θ * (10 * L)) * Real.exp (-(θ * supDist b.1 c.1)))) := by
          rw [Finset.sum_mul]
      _ ≤ (C * D) * (C * (Real.exp (θ * (10 * L)) * Real.exp (-(θ * supDist b.1 c.1)))) :=
          mul_le_mul_of_nonneg_right (sum_abs_contourWeight_le hL hC hk b) (by positivity)
      _ = _ := by ring
  have hpos : 0 ≤ a * (C * (C * D) * Real.exp (θ * (10 * L))) := by positivity
  unfold flatStepOperator
  split_ifs with h e
  · subst e
    rw [supDist_self]
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, abs_one, mul_one]
    have := abs_nonneg Mh
    linarith
  · rw [abs_zero]
    have := abs_nonneg Mh
    exact mul_nonneg (by linarith) hE.le
  · calc |K b c + a * ∑ c' : TorusBond n, contourWeight L c' b * contourWeight L c' c|
        ≤ |K b c| + |a * ∑ c' : TorusBond n, contourWeight L c' b * contourWeight L c' c| :=
          abs_add_le _ _
      _ ≤ Mh * Real.exp (-(θ * supDist b.1 c.1)) +
            a * (C * (C * D) * Real.exp (θ * (10 * L)) * Real.exp (-(θ * supDist b.1 c.1))) := by
          refine add_le_add (hK b c) ?_
          rw [abs_mul, abs_of_pos ha]
          exact mul_le_mul_of_nonneg_left hsum ha.le
      _ ≤ _ := by
          have h1 : Mh * Real.exp (-(θ * supDist b.1 c.1)) ≤ |Mh| * Real.exp (-(θ * supDist b.1 c.1)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hE.le
          nlinarith
open Classical in
private theorem flatStepOperator_quadratic_lower [NeZero n] [NeZero L] {a κ C₁ κ' : ℝ} (ha : 0 < a)
    (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) (hκa : κ' * C₁ ≤ a) (hκk : κ' * C₁ ≤ κ)
    (K : TorusBond (n * L) → TorusBond (n * L) → ℝ)
    (hQ : ∀ (ξ : RealOneForm (n * L)) (c : TorusBond n), contourAverage L ξ c = ∑ b, contourWeight L c b * ξ b)
    (hK : ∀ ξ : RealOneForm (n * L), κ * curlEnergy ξ ≤ kernelPairing K ξ ξ)
    (hfl : ∀ ξ : RealOneForm (n * L), VanishesOnBlockTrees L ξ →
      ∑ b, ξ b ^ 2 ≤ C₁ * (curlEnergy ξ + ∑ c : TorusBond n, contourAverage L ξ c ^ 2))
    (ξ : TorusBond (n * L) → ℝ) :
    κ' * ∑ x, ξ x ^ 2 ≤ ∑ x, ∑ y, flatStepOperator a L K x y * ξ x * ξ y := by
  set ζ : RealOneForm (n * L) := fun b => if IsBlockTreeBond L b then 0 else ξ b with hζ
  set t : TorusBond (n * L) → ℝ := fun x => if IsBlockTreeBond L x then ξ x ^ 2 else 0 with ht
  have hterm : ∀ x y, flatStepOperator a L K x y * ξ x * ξ y =
      (if x = y then t x else 0) + K x y * ζ x * ζ y +
        a * ∑ c : TorusBond n, (contourWeight L c x * ζ x) * (contourWeight L c y * ζ y) := by
    intro x y
    unfold flatStepOperator
    by_cases hx : IsBlockTreeBond L x
    · by_cases e : x = y
      · subst e
        simp [hx, hζ, ht, sq]
      · simp [hx, hζ, ht, e]
    · by_cases hy : IsBlockTreeBond L y
      · have e : x ≠ y := fun e => hx (e ▸ hy)
        simp [hx, hy, hζ, ht, e]
      · have h' : ¬ (IsBlockTreeBond L x ∨ IsBlockTreeBond L y) := by tauto
        rw [if_neg h']
        have e0 : (if x = y then t x else 0) = 0 := by
          by_cases e : x = y <;> simp [e, ht, hx, hy]
        rw [e0]
        simp only [hζ, if_neg hx, if_neg hy]
        rw [zero_add]
        have hs : ∑ c : TorusBond n, (contourWeight L c x * ξ x) * (contourWeight L c y * ξ y) =
            (∑ c : TorusBond n, contourWeight L c x * contourWeight L c y) * ξ x * ξ y := by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun c _ => by ring
        rw [hs]
        ring
  have hmean : ∀ c : TorusBond n, contourAverage L ζ c ^ 2 =
      ∑ x, ∑ y, (contourWeight L c x * ζ x) * (contourWeight L c y * ζ y) := fun c => by
    rw [hQ, sq, Finset.sum_mul_sum]
  have h3 : ∑ x, ∑ y, a * ∑ c : TorusBond n, (contourWeight L c x * ζ x) * (contourWeight L c y * ζ y) =
      a * ∑ c : TorusBond n, contourAverage L ζ c ^ 2 := by
    simp only [hmean, Finset.mul_sum]
    calc _ = ∑ x, ∑ c : TorusBond n, ∑ y, a * ((contourWeight L c x * ζ x) * (contourWeight L c y * ζ y)) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hsum : ∑ x, ∑ y, flatStepOperator a L K x y * ξ x * ξ y =
      ∑ x, t x + kernelPairing K ζ ζ + a * ∑ c : TorusBond n, contourAverage L ζ c ^ 2 := by
    simp only [hterm, Finset.sum_add_distrib, h3, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  have hsq : ∑ x, ξ x ^ 2 = ∑ x, t x + ∑ x, ζ x ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : IsBlockTreeBond L x <;> simp [hζ, ht, hx]
  have hoff : VanishesOnBlockTrees L ζ := fun b hb => by simp [hζ, hb]
  have h1 := hfl ζ hoff
  have h2 := hK ζ
  have hcurl : 0 ≤ curlEnergy ζ := by
    unfold curlEnergy
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => ?_
    split_ifs <;> positivity
  have hq2 : 0 ≤ ∑ c : TorusBond n, contourAverage L ζ c ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have ht0 : 0 ≤ ∑ x, t x := Finset.sum_nonneg fun x _ => by
    simp only [ht]
    split_ifs <;> positivity
  have h4 : κ' * ∑ x, ζ x ^ 2 ≤ κ' * (C₁ * (curlEnergy ζ + ∑ c : TorusBond n, contourAverage L ζ c ^ 2)) :=
    mul_le_mul_of_nonneg_left h1 hκ0.le
  have h5 : κ' * C₁ * curlEnergy ζ ≤ κ * curlEnergy ζ := mul_le_mul_of_nonneg_right hκk hcurl
  have h6 : κ' * C₁ * ∑ c : TorusBond n, contourAverage L ζ c ^ 2 ≤
      a * ∑ c : TorusBond n, contourAverage L ζ c ^ 2 :=
    mul_le_mul_of_nonneg_right hκa hq2
  have h7 : κ' * ∑ x, t x ≤ 1 * ∑ x, t x := mul_le_mul_of_nonneg_right hκ1 ht0
  rw [hsum, hsq, mul_add]
  nlinarith
end Operator
section Limits
variable {n L : ℕ}
private theorem supDist_siteOfInt_eq [NeZero n] (u v : Fin 4 → ℤ) (h : 2 * offsetNorm (u - v) < n) :
    supDist (siteOfInt u : TorusSite n) (siteOfInt v) = offsetNorm (u - v) := by
  have key : ∀ i, (((siteOfInt u : TorusSite n) i - (siteOfInt v : TorusSite n) i).valMinAbs).natAbs =
      ((u - v) i).natAbs := by
    intro i
    have hi : ((u - v) i).natAbs ≤ offsetNorm (u - v) :=
      Finset.le_sup (f := fun i => ((u - v) i).natAbs) (Finset.mem_univ i)
    have e : (siteOfInt u : TorusSite n) i - (siteOfInt v : TorusSite n) i = (((u - v) i : ℤ) : ZMod n) := by
      simp [siteOfInt]
    rw [e]
    have : ((((u - v) i : ℤ) : ZMod n)).valMinAbs = (u - v) i := by
      rw [ZMod.valMinAbs_spec]
      refine ⟨rfl, ?_, ?_⟩ <;> omega
    rw [this]
  unfold supDist
  simp only [key]
  rfl
abbrev _root_.YangMills.SharedProofs.p74560 := @supDist_siteOfInt_eq
private theorem eq_of_offsetNorm_sub_eq_zero {u v : Fin 4 → ℤ} (h : offsetNorm (u - v) = 0) : u = v := by
  funext i
  have hi : ((u - v) i).natAbs ≤ offsetNorm (u - v) :=
    Finset.le_sup (f := fun i => ((u - v) i).natAbs) (Finset.mem_univ i)
  have h0 : (u - v) i = 0 := by omega
  simpa [sub_eq_zero] using h0
private theorem supDist_siteOfInt_zero_le [NeZero n] (u : Fin 4 → ℤ) :
    supDist (siteOfInt u : TorusSite n) 0 ≤ offsetNorm u := by
  rw [supDist_le_iff]
  intro i
  have e : (siteOfInt u : TorusSite n) i - (0 : TorusSite n) i = ((u i : ℤ) : ZMod n) := by simp [siteOfInt]
  rw [e]
  exact (natAbs_valMinAbs_intCast_le _).trans
    (Finset.le_sup (f := fun i => (u i).natAbs) (Finset.mem_univ i))
private theorem bondFrom_zero_fst (b : LatticeBond) : (bondFrom 0 b : TorusBond n).1 = siteOfInt b.1 := by
  simp [bondFrom]
private theorem eventually_bondFrom_zero_inj (b c : LatticeBond) :
    ∀ᶠ m : ℕ in Filter.atTop, ((bondFrom 0 b : TorusBond m) = bondFrom 0 c ↔ b = c) := by
  filter_upwards [Filter.eventually_gt_atTop (2 * offsetNorm (b.1 - c.1))] with m hm
  haveI : NeZero m := ⟨by omega⟩
  constructor
  · intro e
    have e1 : (siteOfInt b.1 : TorusSite m) = siteOfInt c.1 := by
      have := congrArg Prod.fst e
      rwa [bondFrom_zero_fst, bondFrom_zero_fst] at this
    have e2' : (bondFrom 0 b : TorusBond m).2 = (bondFrom 0 c : TorusBond m).2 := congrArg Prod.snd e
    have e2 : b.2 = c.2 := e2'
    have e3 := supDist_siteOfInt_eq (n := m) b.1 c.1 hm
    rw [e1, supDist_self] at e3
    exact Prod.ext (eq_of_offsetNorm_sub_eq_zero e3.symm) e2
  · rintro rfl
    rfl
private theorem exp_neg_supDist_le_shift [NeZero n] {θ : ℝ} (hθ : 0 ≤ θ) (x y : TorusSite n) {s : ℕ}
    (hy : supDist y 0 ≤ s) :
    Real.exp (-(θ * supDist x y)) ≤ Real.exp (θ * s) * Real.exp (-(θ * supDist x 0)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := supDist_triangle x y 0
  have h' : (supDist x 0 : ℝ) ≤ supDist x y + s := by exact_mod_cast h.trans (Nat.add_le_add_left hy _)
  have := mul_le_mul_of_nonneg_left h' hθ
  rw [mul_add] at this
  linarith
private theorem blockCentreSite_zero [NeZero n] : SlopeCoefficient.blockCentreSite L (0 : TorusSite n) = 0 := by
  funext i
  simp [SlopeCoefficient.blockCentreSite]
private theorem supDist_zero_le_of_near [NeZero n] [NeZero L] (hL : Odd L) (x : TorusSite (n * L))
    (y : TorusSite n) {s : ℕ} (hx : supDist x 0 ≤ s)
    (h : supDist x (SlopeCoefficient.blockCentreSite L y) ≤ 5 * L) : supDist y 0 ≤ s + 7 := by
  have h6 := supDist_parentBlock_le_six hL x y h
  have hb := TorusBalls.supDist_parentBlock_le_div_add_one (n := n) L x 0
  have e0 : parentBlock L (0 : TorusSite (n * L)) = 0 := by
    have := TorusBlocks.parentBlock_blockCentreSite (n := n) hL 0
    rwa [← blockCentreSite_eq_torusBlockCentreSite, blockCentreSite_zero] at this
  rw [e0] at hb
  have h8 : supDist x 0 / L ≤ s := (Nat.div_le_self _ _).trans hx
  have h9 := supDist_triangle y (parentBlock L x) 0
  rw [supDist_comm y (parentBlock L x)] at h9
  omega
private theorem tendsto_coarse_contourWeight_sum [NeZero L] (hL : Odd L) {C : ℝ} (hC : 0 ≤ C)
    (hS : TendstoLatticeSumOfTorusSums)
    (hk : ∀ᶠ n : ℕ in Filter.atTop, ∀ [NeZero n] (c : TorusBond n) (b : TorusBond (n * L)),
      |contourWeight L c b| ≤ C ∧
      (5 * L < supDist b.1 (SlopeCoefficient.blockCentreSite L c.1) → contourWeight L c b = 0))
    (hlat : ∀ c b : LatticeBond, ∀ᶠ n : ℕ in Filter.atTop,
      contourWeight L (bondFrom 0 c : TorusBond n) (bondFrom 0 b : TorusBond (n * L)) = latticeContourWeight L c b)
    (b b' : LatticeBond) :
    ∃ F : ℕ → ℝ, (∀ (n : ℕ) [NeZero n], F n = ∑ c : TorusBond n,
        contourWeight L c (bondFrom 0 b : TorusBond (n * L)) * contourWeight L c (bondFrom 0 b' : TorusBond (n * L))) ∧
      Filter.Tendsto F Filter.atTop
        (𝓝 (∑' c : LatticeBond, latticeContourWeight L c b * latticeContourWeight L c b')) := by
  classical
  let F : ℕ → ℝ := fun n => if hn : n ≠ 0 then
    haveI : NeZero n := ⟨hn⟩
    ∑ c : TorusBond n, contourWeight L c (bondFrom 0 b : TorusBond (n * L)) *
      contourWeight L c (bondFrom 0 b' : TorusBond (n * L))
    else 0
  have hF : ∀ (n : ℕ) [NeZero n], F n = ∑ c : TorusBond n,
      contourWeight L c (bondFrom 0 b : TorusBond (n * L)) * contourWeight L c (bondFrom 0 b' : TorusBond (n * L)) := by
    intro n _
    simp only [F]
    rw [dif_pos (NeZero.ne n)]
  refine ⟨F, hF, ?_⟩
  refine (hS (fun n => n) (C * C * Real.exp ((offsetNorm b.1 + 7 : ℕ) : ℝ)) 1
    (fun n c => contourWeight L c (bondFrom 0 b : TorusBond (n * L)) *
      contourWeight L c (bondFrom 0 b' : TorusBond (n * L)))
    (fun c => latticeContourWeight L c b * latticeContourWeight L c b') F Filter.tendsto_id one_pos ?_ ?_ ?_).2
  · filter_upwards [hk, Filter.eventually_gt_atTop 0] with n hn hpos c
    haveI : NeZero n := ⟨by omega⟩
    by_cases d : 5 * L < supDist (bondFrom 0 b : TorusBond (n * L)).1 (SlopeCoefficient.blockCentreSite L c.1)
    · rw [(hn c _).2 d, zero_mul, abs_zero]
      positivity
    · have h0 : supDist (bondFrom 0 b : TorusBond (n * L)).1 0 ≤ offsetNorm b.1 := by
        rw [bondFrom_zero_fst]
        exact supDist_siteOfInt_zero_le b.1
      have h7 := supDist_zero_le_of_near hL (bondFrom 0 b : TorusBond (n * L)).1 c.1 h0 (not_lt.mp d)
      have h7' : ((supDist c.1 0 : ℕ) : ℝ) ≤ ((offsetNorm b.1 + 7 : ℕ) : ℝ) := by exact_mod_cast h7
      have h1 : 1 ≤ Real.exp ((offsetNorm b.1 + 7 : ℕ) : ℝ) * Real.exp (-(1 * supDist c.1 0)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      rw [abs_mul]
      calc |contourWeight L c (bondFrom 0 b : TorusBond (n * L))| *
            |contourWeight L c (bondFrom 0 b' : TorusBond (n * L))|
          ≤ C * C := mul_le_mul (hn c _).1 (hn c _).1 (abs_nonneg _) hC
        _ = C * C * 1 := (mul_one _).symm
        _ ≤ C * C * (Real.exp ((offsetNorm b.1 + 7 : ℕ) : ℝ) * Real.exp (-(1 * supDist c.1 0))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by ring
  · intro c
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hlat c b, hlat c b'] with n h1 h2
    rw [h1, h2]
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hpos _
    exact hF n
private def stepKernelSeq (a : ℝ) (L : ℕ) (h : BondKernel) (n : ℕ) (b c : TorusBond (n * L)) : ℝ :=
  if hn : n ≠ 0 then
    haveI : NeZero n := ⟨hn⟩
    flatStepOperator a L (h (n * L)) b c
  else 0
private theorem stepKernelSeq_eq [NeZero n] (a : ℝ) (h : BondKernel) (b c : TorusBond (n * L)) :
    stepKernelSeq a L h n b c = flatStepOperator a L (h (n * L)) b c := by
  rw [stepKernelSeq, dif_pos (NeZero.ne n)]
private theorem tendsto_stepKernelSeq [NeZero L] (hL : Odd L) {a C : ℝ} {h : BondKernel}
    {hl : LatticeBond → LatticeBond → ℝ}
    (hC : 0 ≤ C) (hS : TendstoLatticeSumOfTorusSums)
    (hk : ∀ᶠ n : ℕ in Filter.atTop, ∀ [NeZero n] (c : TorusBond n) (b : TorusBond (n * L)),
      |contourWeight L c b| ≤ C ∧
      (5 * L < supDist b.1 (SlopeCoefficient.blockCentreSite L c.1) → contourWeight L c b = 0))
    (hlat : ∀ c b : LatticeBond, ∀ᶠ n : ℕ in Filter.atTop,
      contourWeight L (bondFrom 0 c : TorusBond n) (bondFrom 0 b : TorusBond (n * L)) = latticeContourWeight L c b)
    (htree : ∀ b : LatticeBond, ∀ᶠ n : ℕ in Filter.atTop,
      (IsBlockTreeBond L (bondFrom 0 b : TorusBond (n * L)) ↔ IsLatticeTreeBond L b))
    (hs : Filter.Tendsto (fun n : ℕ => n * L) Filter.atTop Filter.atTop)
    (hlim : TendstoLatticeKernel h hl) (b c : LatticeBond) :
    Filter.Tendsto (fun n => stepKernelSeq a L h n (bondFrom 0 b) (bondFrom 0 c)) Filter.atTop
      (𝓝 (latticeStepOperator a L hl b c)) := by
  classical
  by_cases ht : IsLatticeTreeBond L b ∨ IsLatticeTreeBond L c
  · rw [latticeStepOperator, if_pos ht]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [htree b, htree c, hs.eventually (eventually_bondFrom_zero_inj b c),
      Filter.eventually_gt_atTop 0] with n h1 h2 h3 h4
    haveI : NeZero n := ⟨by omega⟩
    have ht' : IsBlockTreeBond L (bondFrom 0 b : TorusBond (n * L)) ∨
        IsBlockTreeBond L (bondFrom 0 c : TorusBond (n * L)) := by
      rw [h1, h2]
      exact ht
    rw [stepKernelSeq_eq, flatStepOperator, if_pos ht']
    by_cases e : b = c
    · rw [if_pos e, if_pos (h3.mpr e)]
    · rw [if_neg e, if_neg (fun e' => e (h3.mp e'))]
  · obtain ⟨F, hF, hFl⟩ := tendsto_coarse_contourWeight_sum hL hC hS hk hlat b c
    rw [latticeStepOperator, if_neg ht]
    refine (((hlim b c).comp hs).add (hFl.const_mul a)).congr' ?_
    filter_upwards [htree b, htree c, Filter.eventually_gt_atTop 0] with n h1 h2 h4
    haveI : NeZero n := ⟨by omega⟩
    have ht' : ¬ (IsBlockTreeBond L (bondFrom 0 b : TorusBond (n * L)) ∨
        IsBlockTreeBond L (bondFrom 0 c : TorusBond (n * L))) := by
      rw [h1, h2]
      exact ht
    rw [stepKernelSeq_eq, flatStepOperator, if_neg ht', hF]
    rfl
private abbrev stepMatrix [NeZero n] (a : ℝ) (L : ℕ) (K : TorusBond (n * L) → TorusBond (n * L) → ℝ) :
    Matrix (TorusBond (n * L)) (TorusBond (n * L)) ℝ := Matrix.of (flatStepOperator a L K)
private def resolventPowSeq (a τ : ℝ) (L : ℕ) (h : BondKernel) (k n : ℕ) (b c : TorusBond (n * L)) : ℝ :=
  if hn : n ≠ 0 ∧ L ≠ 0 then
    haveI : NeZero n := ⟨hn.1⟩
    haveI : NeZero L := ⟨hn.2⟩
    ((1 - τ⁻¹ • stepMatrix a L (h (n * L))) ^ k) b c
  else 0
private theorem resolventPowSeq_eq [NeZero n] [NeZero L] (a τ : ℝ) (h : BondKernel) (k : ℕ)
    (b c : TorusBond (n * L)) :
    resolventPowSeq a τ L h k n b c = ((1 - τ⁻¹ • stepMatrix a L (h (n * L))) ^ k) b c := by
  rw [resolventPowSeq, dif_pos ⟨NeZero.ne n, NeZero.ne L⟩]
private theorem resolventPowSeq_one [NeZero n] [NeZero L] (a τ : ℝ) (h : BondKernel) (b c : TorusBond (n * L)) :
    resolventPowSeq a τ L h 1 n b c = (if b = c then 1 else 0) - τ⁻¹ * flatStepOperator a L (h (n * L)) b c := by
  rw [resolventPowSeq_eq, pow_one, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  rfl
private def latticeKernelPow (A : LatticeBond → LatticeBond → ℝ) : ℕ → LatticeBond → LatticeBond → ℝ
  | 0 => fun b c => if b = c then 1 else 0
  | k + 1 => fun b c => ∑' x, latticeKernelPow A k b x * A x c
private theorem tendsto_resolventPowSeq [NeZero L] {a τ q M₁ θ : ℝ} {h : BondKernel}
    {A : LatticeBond → LatticeBond → ℝ}
    (hS : TendstoLatticeSumOfTorusSums)
    (hs : Filter.Tendsto (fun n : ℕ => n * L) Filter.atTop Filter.atTop)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hθ : 0 < θ) (hM₁ : 0 ≤ M₁)
    (hpowb : ∀ᶠ n : ℕ in Filter.atTop, ∀ (k : ℕ) (x y : TorusBond (n * L)),
      |resolventPowSeq a τ L h k n x y| ≤ q ^ k)
    (hA1 : ∀ᶠ n : ℕ in Filter.atTop, ∀ x y : TorusBond (n * L),
      |resolventPowSeq a τ L h 1 n x y| ≤ M₁ * Real.exp (-(θ * supDist x.1 y.1)))
    (hAl : ∀ b c : LatticeBond, Filter.Tendsto (fun n => resolventPowSeq a τ L h 1 n (bondFrom 0 b) (bondFrom 0 c))
      Filter.atTop (𝓝 (A b c))) (k : ℕ) :
    ∀ b c : LatticeBond, Filter.Tendsto (fun n => resolventPowSeq a τ L h k n (bondFrom 0 b) (bondFrom 0 c))
      Filter.atTop (𝓝 (latticeKernelPow A k b c)) := by
  induction k with
  | zero =>
    intro b c
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hs.eventually (eventually_bondFrom_zero_inj b c), Filter.eventually_gt_atTop 0] with n h3 h4
    haveI : NeZero n := ⟨by omega⟩
    rw [resolventPowSeq_eq, pow_zero, Matrix.one_apply]
    simp only [latticeKernelPow]
    by_cases e : b = c
    · rw [if_pos e, if_pos (h3.mpr e)]
    · rw [if_neg e, if_neg (fun e' => e (h3.mp e'))]
  | succ k ih =>
    intro b c
    refine (hS (fun n => n * L) (M₁ * Real.exp (θ * (offsetNorm c.1 : ℕ))) θ
      (fun n x => resolventPowSeq a τ L h k n (bondFrom 0 b) x * resolventPowSeq a τ L h 1 n x (bondFrom 0 c))
      (fun x => latticeKernelPow A k b x * A x c)
      (fun n => resolventPowSeq a τ L h (k + 1) n (bondFrom 0 b) (bondFrom 0 c)) hs hθ ?_ ?_ ?_).2
    · filter_upwards [hpowb, hA1, Filter.eventually_gt_atTop 0] with n p1 p2 p4 x
      haveI : NeZero n := ⟨by omega⟩
      have h0 : supDist (bondFrom 0 c : TorusBond (n * L)).1 0 ≤ offsetNorm c.1 := by
        rw [bondFrom_zero_fst]
        exact supDist_siteOfInt_zero_le c.1
      have h1 := exp_neg_supDist_le_shift hθ.le x.1 (bondFrom 0 c : TorusBond (n * L)).1 h0
      have h2 : q ^ k ≤ 1 := pow_le_one₀ hq0 hq1.le
      rw [abs_mul]
      calc |resolventPowSeq a τ L h k n (bondFrom 0 b) x| * |resolventPowSeq a τ L h 1 n x (bondFrom 0 c)|
          ≤ 1 * (M₁ * Real.exp (-(θ * supDist x.1 (bondFrom 0 c : TorusBond (n * L)).1))) :=
            mul_le_mul ((p1 k _ _).trans h2) (p2 _ _) (abs_nonneg _) zero_le_one
        _ ≤ 1 * (M₁ * (Real.exp (θ * (offsetNorm c.1 : ℕ)) * Real.exp (-(θ * supDist x.1 0)))) := by
            gcongr
        _ = _ := by ring
    · exact fun x => (ih b x).mul (hAl x c)
    · filter_upwards [Filter.eventually_gt_atTop 0] with n p4 _
      haveI : NeZero n := ⟨by omega⟩
      show resolventPowSeq a τ L h (k + 1) n (bondFrom 0 b) (bondFrom 0 c) = ∑ x : TorusBond (n * L), _
      simp only [resolventPowSeq_eq, pow_one]
      rw [pow_succ, Matrix.mul_apply]
end Limits
private def IsDecayingInverse {n : ℕ} [NeZero n] (a τ q M' θ' : ℝ) (L : ℕ) [NeZero L] (h : BondKernel)
    (g : TorusBond (n * L) → TorusBond (n * L) → ℝ) : Prop :=
  (Matrix.of g) * stepMatrix a L (h (n * L)) = 1 ∧ stepMatrix a L (h (n * L)) * (Matrix.of g) = 1 ∧
    (∀ x y : TorusBond (n * L), |g x y| ≤ M' * Real.exp (-(θ' * supDist x.1 y.1))) ∧
    (∀ (k : ℕ) (x y : TorusBond (n * L)), |((1 - τ⁻¹ • stepMatrix a L (h (n * L))) ^ k) x y| ≤ q ^ k) ∧
    ∀ x y : TorusBond (n * L),
      HasSum (fun k : ℕ => τ⁻¹ * ((1 - τ⁻¹ • stepMatrix a L (h (n * L))) ^ k) x y) (g x y)
theorem greenKernelsExist (hI : DecayingKernels.DecayingInverseBound)
    (hS : TendstoLatticeSumOfTorusSums) (hF : offTreeFormLowerBoundStatement)
    (hCK : ContourWeightLocality) : greenKernelsExistStatement := by
  classical
  intro a ha L hL h hl hc hlim
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : Filter.Tendsto (fun n : ℕ => n * L) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hLpos) Filter.tendsto_id
  obtain ⟨C, hC, hck1, hck2, hck3, hck4⟩ := hCK L hL
  obtain ⟨C₁, hC₁, hfl⟩ := hF L hL
  obtain ⟨Mh, θ, hθ, hdec⟩ := hc.decay
  obtain ⟨κ, hκ, hfloor⟩ := hc.curl_lower_bound
  have hlat0 : ∀ c : ℝ, 0 ≤ expLatticeSum c := fun c => by
    unfold expLatticeSum
    exact Even.pow_nonneg (by decide) _
  set MT : ℝ := 1 + |Mh| + a * (C * (C * (Real.exp 6 * (4 * expLatticeSum 1))) * Real.exp (θ * (10 * L)))
    with hMTdef
  have hMT : 0 < MT := by
    have := hlat0 1
    have h1 : 0 ≤ a * (C * (C * (Real.exp 6 * (4 * expLatticeSum 1))) * Real.exp (θ * (10 * L))) := by
      positivity
    have := abs_nonneg Mh
    rw [hMTdef]
    linarith
  set S : ℝ := 4 * expLatticeSum (θ / 2) + 1 with hSdef
  have hS0 : 0 < S := by
    have := hlat0 (θ / 2)
    rw [hSdef]
    linarith
  set κ' : ℝ := min 1 (min κ a / C₁) with hκ'def
  have hκ'0 : 0 < κ' := lt_min one_pos (div_pos (lt_min hκ ha) hC₁)
  have hκ'1 : κ' ≤ 1 := min_le_left _ _
  have hκ'2 : κ' * C₁ ≤ min κ a := (le_div_iff₀ hC₁).mp (min_le_right _ _)
  obtain ⟨M', θ', τ, q, hM', hθ', hτ, hq0, hq1, hinv⟩ := hI MT θ κ' S hMT hθ hκ'0 hS0
  have hkn : ∀ᶠ n : ℕ in Filter.atTop, ∀ [NeZero n] (c : TorusBond n) (b : TorusBond (n * L)),
      |contourWeight L c b| ≤ C ∧
      (5 * L < supDist b.1 (SlopeCoefficient.blockCentreSite L c.1) → contourWeight L c b = 0) := by
    filter_upwards [hck1] with n hn _
    exact (hn).2
  have hgood : ∀ᶠ n : ℕ in Filter.atTop, ∀ [NeZero n],
      (∀ b c : TorusBond (n * L), |flatStepOperator a L (h (n * L)) b c| ≤
        MT * Real.exp (-(θ * supDist b.1 c.1))) ∧
      ∃ g : TorusBond (n * L) → TorusBond (n * L) → ℝ, IsDecayingInverse a τ q M' θ' L h g := by
    filter_upwards [hck1, hs.eventually hc.symm, hs.eventually hdec, hs.eventually hfloor, hfl]
      with n h1 h2 h3 h4 h5 _
    have hdn : ∀ b c : TorusBond (n * L), |flatStepOperator a L (h (n * L)) b c| ≤
        MT * Real.exp (-(θ * supDist b.1 c.1)) :=
      fun b c => abs_flatStepOperator_le hL.1 ha hC.le hθ (h1).2 h3 b c
    refine ⟨hdn, ?_⟩
    obtain ⟨G, g1, g2, g3, g4, g5⟩ := hinv (TorusBond (n * L)) (fun b c => (supDist b.1 c.1 : ℝ))
      (stepMatrix a L (h (n * L))) (fun x => by simp [supDist_self]) (fun x y => Nat.cast_nonneg _)
      (fun x y => by simp only [supDist_comm x.1 y.1])
      (fun x y z => by exact_mod_cast supDist_triangle x.1 y.1 z.1)
      (fun x => by
        have := sum_bond_exp_supDist_le (n := n * L) (c := θ / 2) (by linarith) x.1
        have e : ∀ y : TorusBond (n * L), Real.exp (-(θ / 2 * (supDist x.1 y.1 : ℝ))) =
            Real.exp (-(θ / 2) * supDist y.1 x.1) := fun y => by
          rw [supDist_comm x.1 y.1, neg_mul]
        simp only [e]
        rw [hSdef]
        linarith)
      (Matrix.IsSymm.ext fun x y => flatStepOperator_symm_of_symm h2 y x) hdn
      (fun ξ => flatStepOperator_quadratic_lower ha hκ'0 hκ'1 (hκ'2.trans (min_le_right _ _))
        (hκ'2.trans (min_le_left _ _)) _ (h1).1 h4 h5 ξ)
    exact ⟨G, g1, g2, g3, g4, g5⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hgood
  have hch : ∀ n : ℕ, ∃ g : TorusBond (n * L) → TorusBond (n * L) → ℝ, N ≤ n → ∀ [NeZero n],
      IsDecayingInverse a τ q M' θ' L h g := by
    intro n
    by_cases hn : N ≤ n ∧ n ≠ 0
    · haveI : NeZero n := ⟨hn.2⟩
      obtain ⟨g, hg⟩ := (hN n hn.1).2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨fun _ _ => 0, fun h1 i => absurd ⟨h1, NeZero.ne n⟩ hn⟩
  choose G hG using hch
  have hT : ∀ n : ℕ, N ≤ n → ∀ [NeZero n] (b c : TorusBond (n * L)),
      |flatStepOperator a L (h (n * L)) b c| ≤ MT * Real.exp (-(θ * supDist b.1 c.1)) :=
    fun n hn _ => (hN n hn).1
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, N ≤ n ∧ n ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0] with n h1 h2
    exact ⟨h1, by omega⟩
  have hpowb : ∀ᶠ n : ℕ in Filter.atTop, ∀ (k : ℕ) (x y : TorusBond (n * L)),
      |resolventPowSeq a τ L h k n x y| ≤ q ^ k := by
    filter_upwards [hbig] with n hn k x y
    haveI : NeZero n := ⟨hn.2⟩
    rw [resolventPowSeq_eq]
    exact (hG n hn.1).2.2.2.1 k x y
  set M₁ : ℝ := 1 + τ⁻¹ * MT with hM₁def
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hM₁ : 0 ≤ M₁ := by positivity
  have hA1 : ∀ᶠ n : ℕ in Filter.atTop, ∀ x y : TorusBond (n * L),
      |resolventPowSeq a τ L h 1 n x y| ≤ M₁ * Real.exp (-(θ * supDist x.1 y.1)) := by
    filter_upwards [hbig] with n hn x y
    haveI : NeZero n := ⟨hn.2⟩
    rw [resolventPowSeq_one]
    have h1 : |(if x = y then (1 : ℝ) else 0)| ≤ Real.exp (-(θ * supDist x.1 y.1)) := by
      split_ifs with e
      · subst e
        simp [supDist_self]
      · simpa using (Real.exp_pos _).le
    have h2 := hT n hn.1 x y
    calc |(if x = y then (1 : ℝ) else 0) - τ⁻¹ * flatStepOperator a L (h (n * L)) x y|
        ≤ |(if x = y then (1 : ℝ) else 0)| + |τ⁻¹ * flatStepOperator a L (h (n * L)) x y| := abs_sub _ _
      _ ≤ Real.exp (-(θ * supDist x.1 y.1)) + τ⁻¹ * (MT * Real.exp (-(θ * supDist x.1 y.1))) := by
          refine add_le_add h1 ?_
          rw [abs_mul, abs_of_pos hτi]
          exact mul_le_mul_of_nonneg_left h2 hτi.le
      _ = _ := by rw [hM₁def]; ring
  have hstep : ∀ b c : LatticeBond, Filter.Tendsto (fun n => stepKernelSeq a L h n (bondFrom 0 b) (bondFrom 0 c))
      Filter.atTop (𝓝 (latticeStepOperator a L hl b c)) :=
    tendsto_stepKernelSeq hL.1 hC.le hS hkn hck3 hck4 hs hlim
  let A : LatticeBond → LatticeBond → ℝ := fun b c =>
    (if b = c then 1 else 0) - τ⁻¹ * latticeStepOperator a L hl b c
  have hAl : ∀ b c : LatticeBond, Filter.Tendsto
      (fun n => resolventPowSeq a τ L h 1 n (bondFrom 0 b) (bondFrom 0 c)) Filter.atTop (𝓝 (A b c)) := by
    intro b c
    refine (tendsto_const_nhds.sub ((hstep b c).const_mul τ⁻¹)).congr' ?_
    filter_upwards [hs.eventually (eventually_bondFrom_zero_inj b c), hbig] with n h3 hn
    haveI : NeZero n := ⟨hn.2⟩
    rw [resolventPowSeq_one, stepKernelSeq_eq]
    by_cases e : b = c
    · rw [if_pos e, if_pos (h3.mpr e)]
    · rw [if_neg e, if_neg (fun e' => e (h3.mp e'))]
  have hpow := fun k => tendsto_resolventPowSeq (a := a) (τ := τ) (h := h) (A := A) hS hs hq0 hq1 hθ hM₁
    hpowb hA1 hAl k
  let Gl : LatticeBond → LatticeBond → ℝ := fun b c => ∑' k : ℕ, τ⁻¹ * latticeKernelPow A k b c
  have hGlim : ∀ b c : LatticeBond, Filter.Tendsto (fun n => G n (bondFrom 0 b) (bondFrom 0 c)) Filter.atTop
      (𝓝 (Gl b c)) := by
    intro b c
    have h1 : Filter.Tendsto (fun n => ∑' k : ℕ, τ⁻¹ * resolventPowSeq a τ L h k n (bondFrom 0 b) (bondFrom 0 c))
        Filter.atTop (𝓝 (Gl b c)) := by
      refine tendsto_tsum_of_dominated_convergence (bound := fun k => τ⁻¹ * q ^ k)
        ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
        (fun k => (hpow k b c).const_mul τ⁻¹) ?_
      filter_upwards [hpowb] with n hn k
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hτi]
      exact mul_le_mul_of_nonneg_left (hn k _ _) hτi.le
    refine h1.congr' ?_
    filter_upwards [hbig] with n hn
    haveI : NeZero n := ⟨hn.2⟩
    simp only [resolventPowSeq_eq]
    exact ((hG n hn.1).2.2.2.2 _ _).tsum_eq
  refine ⟨G, Gl, ?_⟩
  refine ⟨⟨M', θ', hθ', ?_⟩, ?_, ?_, hGlim, ⟨M', θ', hθ', ?_⟩, ?_⟩
  · filter_upwards [hbig] with n hn b c
    haveI : NeZero n := ⟨hn.2⟩
    exact (hG n hn.1).2.2.1 b c
  · filter_upwards [hbig] with n hn _ _ b c
    have := congrFun (congrFun (hG n hn.1).2.1 b) c
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  · filter_upwards [hbig] with n hn _ _ b c
    have := congrFun (congrFun (hG n hn.1).1 b) c
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  · intro b c
    refine le_of_tendsto (hGlim b c).abs ?_
    filter_upwards [hbig, Filter.eventually_gt_atTop (2 * offsetNorm (b.1 - c.1))] with n hn h2
    haveI : NeZero n := ⟨hn.2⟩
    have h3 : 2 * offsetNorm (b.1 - c.1) < n * L := lt_of_lt_of_le h2 (Nat.le_mul_of_pos_right n hLpos)
    have hd : supDist (bondFrom 0 b : TorusBond (n * L)).1 (bondFrom 0 c : TorusBond (n * L)).1 =
        offsetNorm (b.1 - c.1) := by
      rw [bondFrom_zero_fst, bondFrom_zero_fst]
      exact supDist_siteOfInt_eq b.1 c.1 h3
    have := (hG n hn.1).2.2.1 (bondFrom 0 b) (bondFrom 0 c)
    rw [hd] at this
    exact this
  · intro b c
    have hmain := hS (fun n => n * L) (M' * MT * Real.exp (θ' * (offsetNorm b.1 : ℕ))) θ'
      (fun n x => G n (bondFrom 0 b) x * stepKernelSeq a L h n x (bondFrom 0 c))
      (fun x => Gl b x * latticeStepOperator a L hl x c)
      (fun _ => if b = c then 1 else 0) hs hθ' ?_ (fun x => (hGlim b x).mul (hstep x c)) ?_
    · have hlimit := tendsto_nhds_unique hmain.2 tendsto_const_nhds
      exact hlimit ▸ hmain.1.hasSum
    · filter_upwards [hbig] with n hn x
      haveI : NeZero n := ⟨hn.2⟩
      have h0 : supDist (bondFrom 0 b : TorusBond (n * L)).1 0 ≤ offsetNorm b.1 := by
        rw [bondFrom_zero_fst]
        exact supDist_siteOfInt_zero_le b.1
      have h1 := exp_neg_supDist_le_shift hθ'.le x.1 (bondFrom 0 b : TorusBond (n * L)).1 h0
      rw [supDist_comm x.1] at h1
      have h2 := (hG n hn.1).2.2.1 (bondFrom 0 b) x
      have h3 := hT n hn.1 x (bondFrom 0 c)
      have h4 : Real.exp (-(θ * supDist x.1 (bondFrom 0 c : TorusBond (n * L)).1)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ θ * supDist x.1 (bondFrom 0 c : TorusBond (n * L)).1 := by positivity
        linarith
      rw [abs_mul, stepKernelSeq_eq]
      calc |G n (bondFrom 0 b) x| * |flatStepOperator a L (h (n * L)) x (bondFrom 0 c)|
          ≤ (M' * (Real.exp (θ' * (offsetNorm b.1 : ℕ)) * Real.exp (-(θ' * supDist x.1 0)))) * (MT * 1) := by
            refine mul_le_mul (h2.trans (mul_le_mul_of_nonneg_left h1 hM'.le))
              (h3.trans (mul_le_mul_of_nonneg_left h4 hMT.le)) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · filter_upwards [hbig, hs.eventually (eventually_bondFrom_zero_inj b c)] with n hn h3 _
      haveI : NeZero n := ⟨hn.2⟩
      have := congrFun (congrFun (hG n hn.1).1 (bondFrom 0 b)) (bondFrom 0 c)
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simp only [stepKernelSeq_eq]
      refine Eq.trans ?_ this.symm
      by_cases e : b = c
      · rw [if_pos e, if_pos (h3.mpr e)]
      · rw [if_neg e, if_neg (fun e' => e (h3.mp e'))]
end YangMills.Construction.RunningCouplingSlope
end
