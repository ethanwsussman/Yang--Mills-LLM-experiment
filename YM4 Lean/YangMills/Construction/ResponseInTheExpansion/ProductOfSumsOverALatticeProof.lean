import YangMills.Construction.ResponseInTheExpansion.ProductOfSumsOverALattice
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LatticeFourier
theorem tsum_pi_prod : tsum_pi_prod_statement := by
  intro 𝕜 _ n
  induction n with
  | zero =>
    intro f _
    have hzero : HasSum (fun k : Fin 0 → ℤ => ∏ i, f i (k i)) 1 := by
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact hasSum_unique (fun _ : Fin 0 → ℤ => (1 : 𝕜))
    refine ⟨?_, by simp only [Finset.univ_eq_empty, Finset.prod_empty] at hzero ⊢; exact hzero⟩
    exact (hasSum_unique _).summable
  | succ n ih =>
    intro f hf
    obtain ⟨hTailSumm, hTailSum⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) :=
      { toFun := fun x => Fin.cons x.1 x.2
        invFun := fun k => (k 0, Fin.tail k)
        left_inv := by rintro ⟨m, k⟩; simp
        right_inv := fun k => by simp }
    have hsplit : ∀ (m : ℤ) (k : Fin n → ℤ),
        ∏ i, f i (e (m, k) i) = f 0 m * ∏ i : Fin n, f i.succ (k i) := by
      intro m k
      simp [e, Fin.prod_univ_succ]
    have hNormSumm : Summable (fun x : ℤ × (Fin n → ℤ) => ‖f 0 x.1‖ * ‖∏ i : Fin n, f i.succ (x.2 i)‖) :=
      (hf 0).mul_of_nonneg hTailSumm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hNormComp : (fun k : Fin (n + 1) → ℤ => ‖∏ i, f i (k i)‖) ∘ e =
        fun x : ℤ × (Fin n → ℤ) => ‖f 0 x.1‖ * ‖∏ i : Fin n, f i.succ (x.2 i)‖ := by
      funext x
      obtain ⟨m, k⟩ := x
      show ‖∏ i, f i (e (m, k) i)‖ = _
      rw [hsplit, norm_mul]
    have hComp : (fun k : Fin (n + 1) → ℤ => ∏ i, f i (k i)) ∘ e =
        fun x : ℤ × (Fin n → ℤ) => f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i) := by
      funext x
      obtain ⟨m, k⟩ := x
      show ∏ i, f i (e (m, k) i) = _
      rw [hsplit]
    have hProdSumm : Summable (fun x : ℤ × (Fin n → ℤ) => f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)) := by
      refine Summable.of_norm ?_
      refine hNormSumm.congr ?_
      intro x
      rw [norm_mul]
    have hHeadSumm : Summable (f 0) := Summable.of_norm (hf 0)
    have hProdSum : HasSum (fun x : ℤ × (Fin n → ℤ) => f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i))
        ((∑' m, f 0 m) * ∏ i : Fin n, ∑' m, f i.succ m) :=
      HasSum.mul (f := f 0) (g := fun k : Fin n → ℤ => ∏ i : Fin n, f i.succ (k i)) hHeadSumm.hasSum hTailSum hProdSumm
    refine ⟨e.summable_iff.1 (hNormComp ▸ hNormSumm), ?_⟩
    rw [Fin.prod_univ_succ]
    exact e.hasSum_iff.1 (hComp ▸ hProdSum)
end YangMills.Construction.LatticeFourier
