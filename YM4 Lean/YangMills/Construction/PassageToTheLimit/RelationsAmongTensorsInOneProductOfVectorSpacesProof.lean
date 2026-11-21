import YangMills.Construction.PassageToTheLimit.RelationsAmongTensorsInOneProductOfVectorSpaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitSpaces
theorem sum_mul_multilinear_eq_zero_of_sum_mul_prod_eq_zero {X : Type} (n : ℕ) :
    ∀ (W : Fin n → Submodule ℝ (X → ℝ)) (Φ : MultilinearMap ℝ (fun k => W k) ℝ)
      (ι : Type) [Fintype ι] (a : ι → ℝ) (v : (i : ι) → (k : Fin n) → W k),
      (∀ t : Fin n → X, ∑ i, a i * ∏ k, (v i k : X → ℝ) (t k) = 0) →
      ∑ i, a i * Φ (v i) = 0 := by
  induction n with
  | zero =>
    intro W Φ ι _ a v hrel
    have hnil := hrel (fun k => k.elim0)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hnil
    have hv : ∀ i, v i = fun k => k.elim0 := fun i => funext fun k => k.elim0
    simp only [hv, ← Finset.sum_mul, hnil, zero_mul]
  | succ n ih =>
    classical
    intro W Φ ι _ a v hrel
    let e := Module.Basis.ofVectorSpace ℝ (W 0)
    let w : ι → W 0 := fun i => v i 0
    let rest : (i : ι) → (k : Fin n) → W k.succ := fun i k => v i k.succ
    have hcomp : ∀ m, ∑ i, (a i * e.coord m (w i)) * (Φ.curryLeft (e m)) (rest i) = 0 := by
      intro m
      refine ih (fun k => W k.succ) (Φ.curryLeft (e m)) ι _ rest ?_
      intro t
      have hvec : ∑ i, (a i * ∏ k, (rest i k : X → ℝ) (t k)) • w i = 0 := by
        apply Subtype.ext
        funext y
        have hy := hrel (Fin.cons y t)
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at hy
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
        rw [← hy]
        exact Finset.sum_congr rfl fun i _ => by simp only [w, rest]; ring
      have hm := congrArg (e.coord m) hvec
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hm
      rw [← hm]
      exact Finset.sum_congr rfl fun i _ => by ring
    let S := Finset.univ.biUnion fun i => (e.repr (w i)).support
    have hexpand : ∀ i, Φ (v i) = ∑ m ∈ S, e.coord m (w i) * (Φ.curryLeft (e m)) (rest i) := by
      intro i
      have hw : w i = ∑ m ∈ S, e.coord m (w i) • e m := by
        conv_lhs => rw [← e.linearCombination_repr (w i)]
        rw [Finsupp.linearCombination_apply]
        exact Finsupp.sum_of_support_subset _
          (fun m hm => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hm⟩) _ (by simp)
      have hΦ : Φ (v i) = (Φ.curryLeft (w i)) (rest i) := by
        rw [MultilinearMap.curryLeft_apply]
        exact congrArg Φ (Fin.cons_self_tail (v i)).symm
      rw [hΦ]
      conv_lhs => rw [hw]
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    calc ∑ i, a i * Φ (v i)
        = ∑ i, ∑ m ∈ S, (a i * e.coord m (w i)) * (Φ.curryLeft (e m)) (rest i) :=
          Finset.sum_congr rfl fun i _ => by
            rw [hexpand i, Finset.mul_sum]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ m ∈ S, ∑ i, (a i * e.coord m (w i)) * (Φ.curryLeft (e m)) (rest i) := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun m _ => hcomp m
theorem tensorRelationsTransfer_holds : TensorRelationsTransfer := by
  intro s E n _ W Φ ι _ a v hrel
  exact sum_mul_multilinear_eq_zero_of_sum_mul_prod_eq_zero n W Φ ι a v hrel
end YangMills.Construction.LimitSpaces
end
