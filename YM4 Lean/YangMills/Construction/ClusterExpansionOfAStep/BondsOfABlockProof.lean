import YangMills.Construction.ClusterExpansionOfAStep.BondsOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours TorusFields TorusLumps
namespace TorusLumps
namespace BlockCoordinates
variable {L n : ℕ} [NeZero L] [NeZero n]
def offsetCoord (L n : ℕ) (v : ZMod (n * L)) : ℤ := ((v.cast : ℤ) + ((L : ℤ) - 1) / 2)
theorem offsetCoord_range [NeZero (n * L)] (v : ZMod (n * L)) :
    0 ≤ offsetCoord L n v ∧ offsetCoord L n v < (n + 1) * L := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hcast : ((v.cast : ℤ)) = (v.val : ℤ) := by
    simp [ZMod.natCast_val]
  have hval : v.val < n * L := ZMod.val_lt v
  have hhalf : ((L : ℤ) - 1) / 2 < L := by omega
  have hhalf0 : 0 ≤ ((L : ℤ) - 1) / 2 := by omega
  unfold offsetCoord
  rw [hcast]
  constructor
  · positivity
  · nlinarith
def blockTag (L n : ℕ) (v : ZMod (n * L)) : ℤ × Bool :=
  (offsetCoord L n v % L, decide ((n : ℤ) * L ≤ offsetCoord L n v))
theorem eq_of_blockTag_eq [NeZero (n * L)] {v v' : ZMod (n * L)}
    (hblock : ((offsetCoord L n v / (L : ℤ) : ℤ) : ZMod n) =
      ((offsetCoord L n v' / (L : ℤ) : ℤ) : ZMod n))
    (htag : blockTag L n v = blockTag L n v') : v = v' := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨a0, a1⟩ := offsetCoord_range (L := L) (n := n) v
  obtain ⟨b0, b1⟩ := offsetCoord_range (L := L) (n := n) v'
  set A := offsetCoord L n v with hA
  set A' := offsetCoord L n v' with hA'
  simp only [blockTag, Prod.mk.injEq, decide_eq_decide] at htag
  obtain ⟨hmod, hwrap⟩ := htag
  have hdvd : (n : ℤ) ∣ A' / L - A / L := by
    have hcong := (ZMod.intCast_eq_intCast_iff_dvd_sub (A / L) (A' / L) n).mp hblock
    exact_mod_cast hcong
  have q0 : 0 ≤ A / L := Int.ediv_nonneg a0 hL.le
  have q0' : 0 ≤ A' / L := Int.ediv_nonneg b0 hL.le
  have q1 : A / L ≤ n := by
    have hlt := Int.ediv_lt_of_lt_mul hL (by rw [mul_comm]; nlinarith : A < (n + 1) * L)
    omega
  have q1' : A' / L ≤ n := by
    have hlt := Int.ediv_lt_of_lt_mul hL (by nlinarith : A' < (n + 1) * L)
    omega
  have hquot : A / L = A' / L := by
    by_cases hc : (n : ℤ) * L ≤ A
    · have hc' := hwrap.mp hc
      have r1 : (n : ℤ) ≤ A / L := (Int.le_ediv_iff_mul_le hL).mpr hc
      have r2 : (n : ℤ) ≤ A' / L := (Int.le_ediv_iff_mul_le hL).mpr hc'
      omega
    · have hc' : ¬ (n : ℤ) * L ≤ A' := fun h => hc (hwrap.mpr h)
      have r1 : A / L < n := Int.ediv_lt_of_lt_mul hL (not_le.mp hc)
      have r2 : A' / L < n := Int.ediv_lt_of_lt_mul hL (not_le.mp hc')
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : k = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · nlinarith
        · nlinarith
      rw [hk0] at hk
      omega
  have hAA : A = A' := by
    have h1 := Int.emod_add_mul_ediv A L
    have h2 := Int.emod_add_mul_ediv A' L
    rw [hquot, hmod] at h1
    linarith
  have hcast : (v.cast : ℤ) = (v'.cast : ℤ) := by
    simp only [hA, hA', offsetCoord] at hAA
    linarith
  have hvals : (v.val : ℤ) = (v'.val : ℤ) := by
    simpa [ZMod.natCast_val] using hcast
  exact ZMod.val_injective _ (by exact_mod_cast hvals)
end BlockCoordinates
theorem bondsPerBlockBound_holds : BondsPerBlockBound := by
  intro L n _ _ Y
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set S : Finset ((Fin 4 → ℤ × Bool) × Fin 4) :=
    (Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) L ×ˢ (Finset.univ : Finset Bool)) ×ˢ
      Finset.univ with hS
  have hcard : S.card = (L * 2) ^ 4 * 4 := by
    simp [hS, Finset.card_product, Fintype.card_piFinset]
  have hle : (Finset.univ.filter fun b : TorusBond (n * L) => parentBlock L b.1 = Y).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun b => (fun i => BlockCoordinates.blockTag L n (b.1 i), b.2))
    · intro b _
      simp only [hS, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset,
        Finset.mem_product, Finset.mem_Ico, Finset.mem_univ, and_true, Finset.coe_univ, Set.mem_univ]
      intro i
      exact ⟨Int.emod_nonneg _ hL.ne', Int.emod_lt_of_pos _ hL⟩
    · intro b hb b' hb' hbb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hb hb'
      simp only [Prod.mk.injEq] at hbb
      refine Prod.ext (funext fun i => ?_) hbb.2
      refine BlockCoordinates.eq_of_blockTag_eq ?_ (congrFun hbb.1 i)
      have e1 := congrFun hb i
      have e2 := congrFun hb' i
      exact e1.trans e2.symm
  have hreal : ((Finset.univ.filter fun b : TorusBond (n * L) => parentBlock L b.1 = Y).card : ℝ) ≤
      ((L * 2) ^ 4 * 4 : ℕ) := by
    rw [← hcard]
    exact_mod_cast hle
  push_cast at hreal
  calc _ ≤ ((L : ℝ) * 2) ^ 4 * 4 := hreal
    _ = _ := by ring
end TorusLumps
end YangMills.Construction
end
