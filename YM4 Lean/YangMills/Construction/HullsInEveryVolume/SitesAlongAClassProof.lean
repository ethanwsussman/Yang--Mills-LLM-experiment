import YangMills.Construction.HullsInEveryVolume.SitesAlongAClass
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullsInEveryVolume
open TorusFields HullTrees
variable {n : ℕ} [NeZero n]
private def StepWithin (r : ℕ) (A : TorusSite n → Prop) (u v : TorusSite n) : Prop :=
  A u ∧ A v ∧ supDist u v ≤ r
private def FarPart (r : ℕ) (A : TorusSite n → Prop) (a x : TorusSite n) : Prop :=
  A x ∧ 40 * r ≤ supDist x a
private theorem walk_far_or_last_exit (r : ℕ) (A : TorusSite n → Prop) (a w : TorusSite n)
    (hw : 40 * r ≤ supDist w a) {p : TorusSite n}
    (h : Relation.ReflTransGen (StepWithin r A) p w) :
    (40 * r ≤ supDist p a ∧ Relation.ReflTransGen (StepWithin r (FarPart r A a)) p w) ∨
      ∃ b, FarPart r A a b ∧ supDist b a < 41 * r ∧
        Relation.ReflTransGen (StepWithin r (FarPart r A a)) b w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl ⟨hw, Relation.ReflTransGen.refl⟩
  | @head p q hpq _ ih =>
    obtain ⟨hAp, hAq, hd⟩ := hpq
    rcases ih with ⟨hq, hc⟩ | hb
    · by_cases hp : 40 * r ≤ supDist p a
      · exact Or.inl ⟨hp, Relation.ReflTransGen.head ⟨⟨hAp, hp⟩, ⟨hAq, hq⟩, hd⟩ hc⟩
      · refine Or.inr ⟨q, ⟨hAq, hq⟩, ?_, hc⟩
        have h1 := supDist_triangle q p a
        rw [supDist_comm q p] at h1
        omega
    · exact Or.inr hb
private theorem exists_separated_sites_of_walk (r : ℕ) (hr : 1 ≤ r) (w : TorusSite n) (k : ℕ) :
    ∀ (A : TorusSite n → Prop) (a : TorusSite n), A a →
      Relation.ReflTransGen (StepWithin r A) a w → 41 * r * k ≤ supDist a w →
      ∃ ys : ℕ → TorusSite n, ys 0 = a ∧ (∀ i ≤ k, A (ys i)) ∧
        (∀ i ≤ k, ∀ i' ≤ k, i ≠ i' → 40 * r ≤ supDist (ys i) (ys i')) ∧
        ∀ i, i < k → supDist (ys (i + 1)) (ys i) < 41 * r := by
  induction k with
  | zero =>
    intro A a ha _ _
    refine ⟨fun _ => a, rfl, fun _ _ => ha, ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    intro i hi i' hi' hne
    omega
  | succ k ih =>
    intro A a ha hwalk hfar
    have hexp : 41 * r * (k + 1) = 41 * r * k + 41 * r := by ring
    have hwa : 40 * r ≤ supDist w a := by
      rw [supDist_comm]
      omega
    have haa : supDist a a = 0 := supDist_self a
    rcases walk_far_or_last_exit r A a w hwa hwalk with ⟨h0, _⟩ | ⟨b, hb, hba, hc⟩
    · omega
    · have htri := supDist_triangle a b w
      rw [supDist_comm a b] at htri
      obtain ⟨ys, h0, hA, hsep, hnext⟩ := ih (FarPart r A a) b hb hc (by omega)
      refine ⟨fun i => Nat.casesOn i a ys, rfl, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact ha
        | succ i => exact (hA i (by omega)).1
      · intro i hi i' hi' hne
        cases i with
        | zero =>
          cases i' with
          | zero => exact absurd rfl hne
          | succ j =>
            show 40 * r ≤ supDist a (ys j)
            rw [supDist_comm]
            exact (hA j (by omega)).2
        | succ i =>
          cases i' with
          | zero => exact (hA i (by omega)).2
          | succ j => exact hsep i (by omega) j (by omega) (by omega)
      · intro i hi
        cases i with
        | zero =>
          show supDist (ys 0) a < 41 * r
          rw [h0]
          exact hba
        | succ i => exact hnext i (by omega)
private theorem exists_mem_supDiam_le_two_mul {X : Finset (TorusSite n)} {z : TorusSite n} (hz : z ∈ X) :
    ∃ w ∈ X, supDiam X ≤ 2 * supDist z w := by
  obtain ⟨w, hw, hsup⟩ := Finset.exists_mem_eq_sup X ⟨z, hz⟩ fun b => supDist z b
  refine ⟨w, hw, ?_⟩
  have hle : ∀ b ∈ X, supDist z b ≤ supDist z w := fun b hb => by
    rw [← hsup]
    exact Finset.le_sup (f := fun b => supDist z b) hb
  refine Finset.sup_le fun a ha => Finset.sup_le fun b hb => ?_
  have h1 := supDist_triangle a z b
  have h2 := hle a ha
  have h3 := hle b hb
  rw [supDist_comm a z] at h1
  omega
private theorem card_le_of_supDist_lt (r : ℕ) (hr : 1 ≤ r) (z : TorusSite n) (S : Finset (TorusSite n))
    (hS : ∀ a ∈ S, supDist a z < 41 * r) : S.card ≤ (83 * r) ^ 4 := by
  have hmaps : Set.MapsTo (fun (a : TorusSite n) (i : Fin 4) => (a i - z i).valMinAbs) (S : Set (TorusSite n))
      (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(41 * r : ℤ)) (41 * r) : Finset (Fin 4 → ℤ)) := by
    intro a ha
    have h := hS a ha
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hi := (supDist_le_iff a z (supDist a z)).1 le_rfl i
    omega
  have hinj : Set.InjOn (fun (a : TorusSite n) (i : Fin 4) => (a i - z i).valMinAbs) (S : Set (TorusSite n)) := by
    intro a _ b _ hab
    funext i
    have h1 := congrArg (fun v : ℤ => (v : ZMod n)) (congrFun hab i)
    simpa [ZMod.coe_valMinAbs] using h1
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  refine hcard.trans ?_
  simp only [Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine Nat.pow_le_pow_left ?_ 4
  omega
theorem sitesAlongHullClass : sitesAlongHullClassStatement := by
  intro n r _ X z D hr hD hz hX hdiam
  refine ⟨?_, card_le_of_supDist_lt r hr z _ fun a ha => (Finset.mem_filter.1 ha).2⟩
  obtain ⟨w, hw, hzw⟩ := exists_mem_supDiam_le_two_mul hz
  obtain ⟨m, hm⟩ : ∃ m, m = max 1 ⌈D / (82 * (r : ℝ))⌉₊ := ⟨_, rfl⟩
  rw [← hm]
  have hm1 : 1 ≤ m := hm ▸ le_max_left _ _
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 41 * r * k ≤ supDist z w := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · have hlt : k < ⌈D / (82 * (r : ℝ))⌉₊ := by
        rcases le_total 1 ⌈D / (82 * (r : ℝ))⌉₊ with h | h
        · rw [max_eq_right h] at hm
          omega
        · rw [max_eq_left h] at hm
          omega
      have hreal : (k : ℝ) < D / (82 * (r : ℝ)) := Nat.lt_ceil.1 hlt
      rw [lt_div_iff₀ (by positivity)] at hreal
      have hcast : (supDiam X : ℝ) ≤ 2 * (supDist z w : ℝ) := by exact_mod_cast hzw
      have hfin : ((41 * r * k : ℕ) : ℝ) ≤ (supDist z w : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast hfin
  obtain ⟨ys, h0, hA, hsep, hnext⟩ :=
    exists_separated_sites_of_walk r hr w k (· ∈ X) z hz (hX z hz w hw) hk
  refine ⟨ys, h0, fun i hi => hA i (by omega), ?_, fun i hi => hnext i (by omega)⟩
  intro i hi i' hi' hne
  exact hsep i (by omega) i' (by omega) hne
end YangMills.Construction.HullsInEveryVolume
end
