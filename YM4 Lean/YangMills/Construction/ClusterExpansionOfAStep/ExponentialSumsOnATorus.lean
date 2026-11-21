import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.Dirichlet.CrossingChainSumEstimate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExponentialSums
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages
def expLineSum (c : ℝ) : ℝ := ∑' m : ℤ, Real.exp (-c * |(m : ℝ)|)
def expLatticeSum (c : ℝ) : ℝ := expLineSum (c / 4) ^ 4
theorem summable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℤ => Real.exp (-c * |(m : ℝ)|) := by apply _root_.YangMills.Construction.Dirichlet.ChainSumEstimate.summable_exp_neg_mul_abs <;> assumption
theorem expLineSum_pos {c : ℝ} (hc : 0 < c) : 0 < expLineSum c :=
  (summable_exp_neg_mul_abs hc).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)
theorem expLatticeSum_pos {c : ℝ} (hc : 0 < c) : 0 < expLatticeSum c :=
  pow_pos (expLineSum_pos (by linarith)) 4
variable {n : ℕ} [NeZero n]
theorem sum_zmod_exp_le_expLineSum {c : ℝ} (hc : 0 < c) :
    ∑ a : ZMod n, Real.exp (-c * |((a.valMinAbs : ℤ) : ℝ)|) ≤ expLineSum c := by
  classical
  have hinj : Function.Injective (ZMod.valMinAbs : ZMod n → ℤ) := by
    intro a b hab
    have := congrArg (fun z : ℤ => (z : ZMod n)) hab
    simpa [ZMod.coe_valMinAbs] using this
  have hsum : ∑ a : ZMod n, Real.exp (-c * |((a.valMinAbs : ℤ) : ℝ)|) =
      ∑ m ∈ Finset.univ.image (ZMod.valMinAbs : ZMod n → ℤ), Real.exp (-c * |(m : ℝ)|) := by
    rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
  rw [hsum]
  exact (summable_exp_neg_mul_abs hc).sum_le_tsum _ fun _ _ => (Real.exp_pos _).le
theorem sum_torus_exp_le {c : ℝ} (hc : 0 < c) (z : TorusSite n) :
    ∑ y : TorusSite n, Real.exp (-c * supDist y z) ≤ expLatticeSum c := by
  classical
  have hc4 : 0 < c / 4 := by linarith
  set g : ZMod n → ℝ := fun a => Real.exp (-(c / 4) * |((a.valMinAbs : ℤ) : ℝ)|) with hg
  have hprod : ∀ y : TorusSite n, Real.exp (-c * supDist y z) ≤ ∏ i, g (y i - z i) := by
    intro y
    rw [hg]
    simp only
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have hcoord : ∀ i, |((((y i - z i).valMinAbs : ℤ)) : ℝ)| ≤ (supDist y z : ℝ) := by
      intro i
      have hnat : ((y i - z i).valMinAbs).natAbs ≤ supDist y z := (supDist_le_iff y z _).mp le_rfl i
      have hreal : (((y i - z i).valMinAbs).natAbs : ℝ) ≤ (supDist y z : ℝ) := by exact_mod_cast hnat
      rwa [Nat.cast_natAbs, Int.cast_abs] at hreal
    have hsum : ∑ i : Fin 4, |((((y i - z i).valMinAbs : ℤ)) : ℝ)| ≤ 4 * (supDist y z : ℝ) := by
      calc _ ≤ ∑ _i : Fin 4, (supDist y z : ℝ) := Finset.sum_le_sum fun i _ => hcoord i
        _ = 4 * (supDist y z : ℝ) := by simp
    rw [← Finset.mul_sum]
    nlinarith
  calc ∑ y : TorusSite n, Real.exp (-c * supDist y z) ≤ ∑ y : TorusSite n, ∏ i, g (y i - z i) :=
        Finset.sum_le_sum fun y _ => hprod y
    _ = ∏ i : Fin 4, ∑ a : ZMod n, g (a - z i) := by
        rw [Finset.prod_univ_sum]
        simp
    _ = ∏ _i : Fin 4, ∑ a : ZMod n, g a := by
        refine Finset.prod_congr rfl fun i _ => ?_
        exact Fintype.sum_equiv (Equiv.subRight (z i)) _ _ fun a => rfl
    _ = (∑ a : ZMod n, g a) ^ 4 := by simp
    _ ≤ expLatticeSum c := by
        unfold expLatticeSum
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          (sum_zmod_exp_le_expLineSum hc4) 4
theorem sum_bonds_exp_le {c : ℝ} (hc : 0 < c) (z : TorusSite n) (F : Finset (TorusBond n)) :
    ∑ b ∈ F, Real.exp (-c * supDist b.1 z) ≤ 4 * expLatticeSum c := by
  classical
  calc ∑ b ∈ F, Real.exp (-c * supDist b.1 z) ≤ ∑ b : TorusBond n, Real.exp (-c * supDist b.1 z) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le
    _ = ∑ y : TorusSite n, ∑ _i : Fin 4, Real.exp (-c * supDist y z) := Fintype.sum_prod_type _
    _ = 4 * ∑ y : TorusSite n, Real.exp (-c * supDist y z) := by simp [Finset.mul_sum]
    _ ≤ 4 * expLatticeSum c := by
        have := sum_torus_exp_le hc z
        linarith
theorem supDist_parentBlock_le (L : ℕ) [NeZero L] (x x' : TorusSite (n * L)) :
    L * supDist (parentBlock L x) (parentBlock L x') ≤ supDist x x' + L := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  have key : supDist (parentBlock L x) (parentBlock L x') ≤ (supDist x x' + L) / L := by
    rw [supDist_le_iff]
    intro i
    rw [Nat.le_div_iff_mul_le hL]
    set a : ℤ := ((x i).cast : ℤ) with ha
    set a' : ℤ := ((x' i).cast : ℤ) with ha'
    set e : ℤ := (x i - x' i).valMinAbs with he
    have hed : e.natAbs ≤ supDist x x' := (supDist_le_iff x x' _).mp le_rfl i
    have hcast : ((a - a' - e : ℤ) : ZMod (n * L)) = 0 := by
      simp only [Int.cast_sub, ha, ha', he, ZMod.intCast_zmod_cast, ZMod.coe_valMinAbs, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
    set h : ℤ := ((L : ℤ) - 1) / 2 with hh
    set q₂ : ℤ := (a' + h + e) / (L : ℤ) with hq₂
    set q₀ : ℤ := (a' + h) / (L : ℤ) with hq₀
    have hq : (a + h) / (L : ℤ) = q₂ + k * (n : ℤ) := by
      have : a + h = (a' + h + e) + (k * (n : ℤ)) * (L : ℤ) := by
        push_cast at hk
        linarith [hk, mul_comm ((n : ℤ) * (L : ℤ)) k, mul_assoc k (n : ℤ) (L : ℤ)]
      rw [this, Int.add_mul_ediv_right _ _ hLz.ne']
    have hb : parentBlock L x i - parentBlock L x' i = ((q₂ - q₀ : ℤ) : ZMod n) := by
      have hq0' : (a' + ((L : ℤ) - 1) / 2) / (L : ℤ) = q₀ := rfl
      have hqa : (a + ((L : ℤ) - 1) / 2) / (L : ℤ) = q₂ + k * (n : ℤ) := hq
      simp only [parentBlock]
      rw [← ha, ← ha', hqa, hq0']
      push_cast
      simp
    rw [hb]
    have h1 := natAbs_valMinAbs_intCast_le (n := n) (q₂ - q₀)
    have e1 := Int.emod_add_mul_ediv (a' + h + e) (L : ℤ)
    have e2 := Int.emod_add_mul_ediv (a' + h) (L : ℤ)
    have b1 := Int.emod_nonneg (a' + h + e) hLz.ne'
    have b2 := Int.emod_lt_of_pos (a' + h + e) hLz
    have b3 := Int.emod_nonneg (a' + h) hLz.ne'
    have b4 := Int.emod_lt_of_pos (a' + h) hLz
    have hT : ((q₂ - q₀).natAbs * L : ℕ) ≤ supDist x x' + L := by
      have h3 : (((q₂ - q₀).natAbs * L : ℕ) : ℤ) = |(L : ℤ) * (q₂ - q₀)| := by
        push_cast
        rw [abs_mul, abs_of_pos hLz, mul_comm]
      have h4 : |(L : ℤ) * (q₂ - q₀)| ≤ |e| + (L : ℤ) := by
        rw [abs_le]
        have l1 : (L : ℤ) * (q₂ - q₀) = e + ((a' + h) % (L : ℤ) - (a' + h + e) % (L : ℤ)) := by
          rw [hq₂, hq₀]
          linarith
        have l2 := neg_abs_le e
        have l3 := le_abs_self e
        constructor <;> rw [l1] <;> linarith
      have : (((q₂ - q₀).natAbs * L : ℕ) : ℤ) ≤ ((supDist x x' + L : ℕ) : ℤ) := by
        rw [h3]
        push_cast
        linarith
      exact_mod_cast this
    exact (Nat.mul_le_mul_right L h1).trans hT
  calc L * supDist (parentBlock L x) (parentBlock L x') ≤ L * ((supDist x x' + L) / L) :=
        Nat.mul_le_mul_left L key
    _ ≤ supDist x x' + L := Nat.mul_div_le _ _
end YangMills.Construction.ExponentialSums
end
