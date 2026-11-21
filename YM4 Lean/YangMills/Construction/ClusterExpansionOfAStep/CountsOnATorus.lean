import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.ClusterExpansionOfAStep.NearPotentialAgainstTheCostProof
import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusCounting
section Balls
variable {N : ℕ} [NeZero N]
theorem card_thickening_singleton_le (m : ℕ) (x : TorusFields.TorusSite N) :
    (TorusLumps.thickening m {x}).card ≤ (2 * m + 1) ^ 4 := by apply _root_.YangMills.Construction.TorusBalls.card_thickening_singleton_le <;> assumption
theorem card_thickening_le (m : ℕ) (C : Finset (TorusFields.TorusSite N)) :
    (TorusLumps.thickening m C).card ≤ C.card * (2 * m + 1) ^ 4 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.card_thickening_le <;> assumption
end Balls
section Blocks
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
theorem supDist_le_of_parentBlock_eq {x y : TorusFields.TorusSite (n * L)}
    (h : TorusLumps.parentBlock L x = TorusLumps.parentBlock L y) : TorusFields.supDist x y ≤ L := by apply _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq <;> assumption
theorem supDist_parentBlock_le (x y : TorusFields.TorusSite (n * L)) :
    TorusFields.supDist (TorusLumps.parentBlock L x) (TorusLumps.parentBlock L y) ≤
      TorusFields.supDist x y / L + 1 := by apply _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one <;> assumption
end Blocks
section Sums
variable {N : ℕ} [NeZero N]
def expSumOnInt (c : ℝ) : ℝ := ∑' z : ℤ, Real.exp (-(c * z.natAbs))
theorem summable_exp_neg_mul_natAbs {c : ℝ} (hc : 0 < c) :
    Summable fun z : ℤ => Real.exp (-(c * z.natAbs)) := by apply _root_.YangMills.SharedProofs.p17292 <;> assumption
theorem expSumOnInt_nonneg (c : ℝ) : 0 ≤ expSumOnInt c := tsum_nonneg fun _ => (Real.exp_pos _).le
theorem sum_exp_valMinAbs_le {c : ℝ} (hc : 0 < c) (w : ZMod N) :
    ∑ k : ZMod N, Real.exp (-(c * ((k - w).valMinAbs.natAbs : ℝ))) ≤ expSumOnInt c := by
  classical
  have h1 : ∑ k : ZMod N, Real.exp (-(c * ((k - w).valMinAbs.natAbs : ℝ))) =
      ∑ k : ZMod N, Real.exp (-(c * (k.valMinAbs.natAbs : ℝ))) :=
    Equiv.sum_comp (Equiv.subRight w) fun k : ZMod N => Real.exp (-(c * (k.valMinAbs.natAbs : ℝ)))
  have hinj : Function.Injective fun k : ZMod N => k.valMinAbs := by
    intro a b h
    have := congrArg (fun z : ℤ => (z : ZMod N)) h
    simpa [ZMod.coe_valMinAbs] using this
  rw [h1]
  have h2 : ∑ k : ZMod N, Real.exp (-(c * (k.valMinAbs.natAbs : ℝ))) =
      ∑ z ∈ (Finset.univ : Finset (ZMod N)).image (fun k => k.valMinAbs),
        Real.exp (-(c * (z.natAbs : ℝ))) := by
    rw [Finset.sum_image fun a _ b _ h => hinj h]
  rw [h2]
  exact (summable_exp_neg_mul_natAbs hc).sum_le_tsum _ fun _ _ => (Real.exp_pos _).le
theorem exp_neg_supDist_le_prod {δ : ℝ} (hδ : 0 ≤ δ) (y w : TorusFields.TorusSite N) :
    Real.exp (-(δ * TorusFields.supDist y w)) ≤
      ∏ i : Fin 4, Real.exp (-(δ / 4 * (((y i - w i).valMinAbs).natAbs : ℝ))) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hle : ∀ i : Fin 4, (((y i - w i).valMinAbs).natAbs : ℝ) ≤ TorusFields.supDist y w := fun i => by
    exact_mod_cast Finset.le_sup (f := fun i => ((y i - w i).valMinAbs).natAbs) (Finset.mem_univ i)
  have : ∑ i : Fin 4, (((y i - w i).valMinAbs).natAbs : ℝ) ≤ 4 * (TorusFields.supDist y w : ℝ) := by
    calc _ ≤ ∑ _i : Fin 4, (TorusFields.supDist y w : ℝ) := Finset.sum_le_sum fun i _ => hle i
      _ = _ := by simp
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  nlinarith
theorem sum_exp_neg_supDist_le {δ : ℝ} (hδ : 0 < δ) (w : TorusFields.TorusSite N) :
    ∑ y : TorusFields.TorusSite N, Real.exp (-(δ * TorusFields.supDist y w)) ≤ expSumOnInt (δ / 4) ^ 4 := by
  classical
  calc ∑ y : TorusFields.TorusSite N, Real.exp (-(δ * TorusFields.supDist y w))
      ≤ ∑ y : TorusFields.TorusSite N,
          ∏ i : Fin 4, Real.exp (-(δ / 4 * (((y i - w i).valMinAbs).natAbs : ℝ))) :=
        Finset.sum_le_sum fun y _ => exp_neg_supDist_le_prod hδ.le y w
    _ = ∏ i : Fin 4, ∑ k : ZMod N, Real.exp (-(δ / 4 * (((k - w i).valMinAbs).natAbs : ℝ))) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ ∏ _i : Fin 4, expSumOnInt (δ / 4) :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          fun i _ => sum_exp_valMinAbs_le (by linarith) (w i)
    _ = _ := by simp
end Sums
section OfBlocks
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
theorem card_sitesInBlocks_singleton_le (Y : TorusFields.TorusSite n) :
    (TorusLumps.sitesInBlocks L {Y}).card ≤ (2 * L + 1) ^ 4 := by
  classical
  rcases (TorusLumps.sitesInBlocks L {Y}).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  have hb : ∀ z ∈ TorusLumps.sitesInBlocks L {Y}, TorusLumps.parentBlock L z = Y := fun z hz => by
    simpa [TorusLumps.sitesInBlocks] using hz
  refine (Finset.card_le_card ?_).trans (card_thickening_singleton_le L x)
  intro z hz
  refine (TorusFields.mem_thickening _ _ _).2
    ⟨x, by simp, supDist_le_of_parentBlock_eq ((hb z hz).trans (hb x hx).symm)⟩
end OfBlocks
theorem le_clusterRange_of_pow_le {x : ℝ} {m : ℕ} (hx : ((m : ℝ)) ^ 100 ≤ x) :
    m ≤ TorusLumps.clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.NearPotentialBound.le_clusterRange_of_pow_le <;> assumption
end YangMills.Construction.TorusCounting
end
