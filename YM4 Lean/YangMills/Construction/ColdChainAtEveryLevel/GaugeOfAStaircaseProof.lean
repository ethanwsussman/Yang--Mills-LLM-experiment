import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormula
import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
set_option autoImplicit false

noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.LatticeFractionalIntegration
namespace StaircaseGauge
def axisProduct (W : Lattice4 → Fin 4 → UnitQuaternion) (v : Lattice4) (m : Fin 4) : ℕ → UnitQuaternion
  | 0 => 1
  | n + 1 => axisProduct W v m n * W (v + (n : ℤ) • basisVector m) m
def staircaseProduct (W : Lattice4 → Fin 4 → UnitQuaternion) (T : Lattice4) :
    List (Fin 4) → Lattice4 → UnitQuaternion
  | [], _ => 1
  | m :: r, v => axisProduct W v m (T m - v m).toNat * staircaseProduct W T r (Function.update v m (T m))
def staircaseGaugeStatement : Prop :=
  ∀ (W : Lattice4 → Fin 4 → UnitQuaternion) (A : Set Lattice4) (T : Lattice4) (R : ℕ) (ε : ℝ), 0 ≤ ε →
    (∀ v ∈ A, ∀ w : Lattice4, (∀ i, v i ≤ w i ∧ w i ≤ T i) → w ∈ A) →
    (∀ v ∈ A, ∀ i, v i ≤ T i ∧ T i - v i ≤ R) →
    (∀ a m k, m ≠ k → a ∈ A → a + basisVector m ∈ A → a + basisVector k ∈ A →
      a + basisVector m + basisVector k ∈ A →
      ‖(((W a m)⁻¹ * W a k * W (a + basisVector k) m * (W (a + basisVector m) k)⁻¹ : UnitQuaternion) : ℍ[ℝ])
        - 1‖ ≤ ε) →
    ∀ (l : List (Fin 4)) (v : Lattice4) (k : Fin 4), l.Nodup → k ∈ l → v ∈ A → v + basisVector k ∈ A →
      ‖(((staircaseProduct W T l v)⁻¹ * W v k * staircaseProduct W T l (v + basisVector k) : UnitQuaternion)
        : ℍ[ℝ]) - 1‖ ≤ l.length * R * ε
end StaircaseGauge
end YangMills.Construction
end

noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StaircaseGauge
open YangMills.Construction.BlockAverages YangMills.Construction.LatticeFractionalIntegration
theorem axisProduct_succ (W : Lattice4 → Fin 4 → UnitQuaternion) (v : Lattice4) (m : Fin 4) (n : ℕ) :
    axisProduct W v m (n + 1) = W v m * axisProduct W (v + basisVector m) m n := by
  induction n with
  | zero => simp [axisProduct]
  | succ n ih =>
    rw [axisProduct, ih, axisProduct, mul_assoc]
    congr 3
    push_cast
    rw [add_smul, one_smul]
    abel
theorem norm_strip_holonomy_sub_one_le {W : Lattice4 → Fin 4 → UnitQuaternion} {A : Set Lattice4} {s : ℝ}
    (hs : 0 ≤ s) {m k : Fin 4} (hmk : m ≠ k) {v : Lattice4} (n : ℕ)
    (hplaq : ∀ t : ℕ, t < n → ∀ a, a = v + (t : ℤ) • basisVector m →
      ‖(((W a m)⁻¹ * W a k * W (a + basisVector k) m * (W (a + basisVector m) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ s) :
    ‖(((axisProduct W v m n)⁻¹ * W v k * axisProduct W (v + basisVector k) m n *
        (W (v + (n : ℤ) • basisVector m) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ n * s := by
  induction n with
  | zero => simp [axisProduct]
  | succ n ih =>
    have h1 := ih fun t ht a ha => hplaq t (by omega) a ha
    have h2 := hplaq n (by omega) _ rfl
    set a : Lattice4 := v + (n : ℤ) • basisVector m with ha
    have e1 : v + basisVector k + (n : ℤ) • basisVector m = a + basisVector k := by rw [ha]; abel
    have e2 : v + ((n + 1 : ℕ) : ℤ) • basisVector m = a + basisVector m := by
      rw [ha]; push_cast; rw [add_smul, one_smul]; abel
    set P : UnitQuaternion := (axisProduct W v m n)⁻¹ * W v k * axisProduct W (v + basisVector k) m n *
      (W a k)⁻¹ with hP
    have e3 : (axisProduct W v m (n + 1))⁻¹ * W v k * axisProduct W (v + basisVector k) m (n + 1) *
        (W (v + ((n + 1 : ℕ) : ℤ) • basisVector m) k)⁻¹ =
        ((W a m)⁻¹ * P * W a m) *
          ((W a m)⁻¹ * W a k * W (a + basisVector k) m * (W (a + basisVector m) k)⁻¹) := by
      rw [e2]
      simp only [axisProduct, e1, ← ha, hP, mul_inv_rev]
      group
    rw [e3]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    have e4 : ‖(((W a m)⁻¹ * P * W a m : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(P : ℍ[ℝ]) - 1‖ := by
      have := norm_coe_conj_sub_one (W a m)⁻¹ P
      simpa using this
    rw [e4]
    have e5 : ((n + 1 : ℕ) : ℝ) * s = n * s + s := by push_cast; ring
    rw [e5]
    linarith
theorem staircaseGaugeStatement_holds : staircaseGaugeStatement := by
  intro W A T R s hs hrise hTop hplaq l
  induction l with
  | nil => intro v k _ hk; simp at hk
  | cons m r ih =>
    intro v k hnd hk hv hvk
    have hnm : m ∉ r := (List.nodup_cons.1 hnd).1
    have hrn : r.Nodup := (List.nodup_cons.1 hnd).2
    have hlen : (((m :: r).length : ℕ) : ℝ) = r.length + 1 := by simp
    by_cases hmk : m = k
    · subst hmk
      have hlt : v m < T m := by
        have h1 := (hTop _ hvk m).1
        simp [basisVector] at h1
        omega
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (T m - v m).toNat = n + 1 := ⟨(T m - v m).toNat - 1, by omega⟩
      have hn' : (T m - (v + basisVector m) m).toNat = n := by
        simp [basisVector]
        omega
      have hupd : Function.update (v + basisVector m) m (T m) = Function.update v m (T m) := by
        funext i
        by_cases hi : i = m
        · subst hi; simp
        · simp [Function.update, hi, basisVector]
      have e1 : (staircaseProduct W T (m :: r) v)⁻¹ * W v m * staircaseProduct W T (m :: r) (v + basisVector m) = 1 := by
        simp only [staircaseProduct, hn, hn', hupd, axisProduct_succ]
        group
      rw [e1]
      simp only [OneMemClass.coe_one, sub_self, norm_zero]
      positivity
    · have hkr : k ∈ r := (List.mem_cons.1 hk).resolve_left (Ne.symm hmk)
      set n := (T m - v m).toNat with hn
      have hn' : (T m - (v + basisVector m) m).toNat = (T m - v m).toNat ∨ True := Or.inr trivial
      have hnk : (T m - (v + basisVector k) m).toNat = n := by
        have : (basisVector k) m = 0 := by simp [basisVector, hmk]
        simp [this, hn]
      set w : Lattice4 := Function.update v m (T m) with hw
      have hvle : ∀ i, v i ≤ T i := fun i => (hTop v hv i).1
      have hwv : v + (n : ℤ) • basisVector m = w := by
        funext i
        by_cases hi : i = m
        · subst hi
          have := hvle i
          simp [hw, basisVector, hn]
          omega
        · simp [hw, basisVector, hi]
      have hupd : Function.update (v + basisVector k) m (T m) = w + basisVector k := by
        funext i
        by_cases hi : i = m
        · subst hi
          simp [hw, basisVector, hmk]
        · simp [hw, Function.update, hi]
      have hmem : ∀ x : Lattice4, (∀ i, v i ≤ x i ∧ x i ≤ T i) → x ∈ A := fun x hx => hrise v hv x hx
      have hvkle : ∀ i, (v + basisVector k) i ≤ T i := fun i => (hTop _ hvk i).1
      have hwA : w ∈ A := hmem _ fun i => by
        rw [hw]
        by_cases hi : i = m
        · subst hi
          simp only [Function.update_self]
          exact ⟨hvle i, le_rfl⟩
        · simp only [Function.update_of_ne hi]
          exact ⟨le_rfl, hvle i⟩
      have hwkA : w + basisVector k ∈ A := by
        rw [← hupd]
        refine hrise _ hvk _ fun i => ?_
        by_cases hi : i = m
        · subst hi
          simp only [Function.update_self]
          exact ⟨hvkle i, le_rfl⟩
        · simp only [Function.update_of_ne hi]
          exact ⟨le_rfl, hvkle i⟩
      have hstrip := norm_strip_holonomy_sub_one_le (W := W) (A := A) hs hmk (v := v) n (fun t ht a ha => by
        have hvm := hvle m
        have htn : (t : ℤ) < T m - v m := by
          have : (t : ℤ) < n := by exact_mod_cast ht
          omega
        have hco : ∀ (b : ℕ) (c : ℤ), (∀ i, v i ≤ (a + (b : ℤ) • basisVector m + c • basisVector k) i) → True :=
          fun _ _ _ => trivial
        have c1 : ∀ i, v i ≤ a i ∧ a i ≤ T i := by
          intro i
          rw [ha]
          by_cases hi : i = m
          · subst hi; simp [basisVector]; omega
          · simp [basisVector, hi, hvle i]
        have c2 : ∀ i, v i ≤ (a + basisVector m) i ∧ (a + basisVector m) i ≤ T i := by
          intro i
          rw [ha]
          by_cases hi : i = m
          · subst hi; simp [basisVector]; omega
          · simp [basisVector, hi, hvle i]
        have c3 : ∀ i, (v + basisVector k) i ≤ (a + basisVector k) i ∧ (a + basisVector k) i ≤ T i := by
          intro i
          have := hvkle i
          rw [ha]
          by_cases hi : i = m
          · subst hi
            have hz : (basisVector k) i = 0 := by simp [basisVector, hmk]
            simp only [Pi.add_apply, hz, add_zero] at this ⊢
            simp [basisVector]; omega
          · have hz : (basisVector m) i = 0 := by simp [basisVector, hi]
            simp [hz]
            simpa using this
        have c4 : ∀ i, (v + basisVector k) i ≤ (a + basisVector m + basisVector k) i ∧
            (a + basisVector m + basisVector k) i ≤ T i := by
          intro i
          have := hvkle i
          rw [ha]
          by_cases hi : i = m
          · subst hi
            have hz : (basisVector k) i = 0 := by simp [basisVector, hmk]
            simp only [Pi.add_apply, hz, add_zero] at this ⊢
            simp [basisVector]; omega
          · have hz : (basisVector m) i = 0 := by simp [basisVector, hi]
            simp [hz]
            simpa using this
        exact hplaq a m k hmk (hmem a c1) (hmem _ c2) (hrise _ hvk _ c3) (hrise _ hvk _ c4))
      rw [hwv] at hstrip
      have hnext := ih w k hrn hkr hwA hwkA
      set Sv := staircaseProduct W T r w with hSv
      set Sk := staircaseProduct W T r (w + basisVector k) with hSk
      set Lv := axisProduct W v m n with hLv
      set Lk := axisProduct W (v + basisVector k) m n with hLk
      set X : UnitQuaternion := Lv⁻¹ * W v k * Lk * (W w k)⁻¹ with hX
      have e1 : (staircaseProduct W T (m :: r) v)⁻¹ * W v k * staircaseProduct W T (m :: r) (v + basisVector k) =
          (Sv⁻¹ * X * Sv) * (Sv⁻¹ * W w k * Sk) := by
        simp only [staircaseProduct, hnk, hupd, ← hn, ← hw, ← hSv, ← hSk, ← hLv, ← hLk, hX]
        group
      rw [e1]
      refine (norm_coe_mul_sub_one_le _ _).trans ?_
      have e2 : ‖((Sv⁻¹ * X * Sv : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(X : ℍ[ℝ]) - 1‖ := by
        have := norm_coe_conj_sub_one Sv⁻¹ X
        simpa using this
      rw [e2, hlen]
      have hnR : (n : ℝ) ≤ R := by
        have h1 := (hTop v hv m).2
        have : n ≤ R := by omega
        exact_mod_cast this
      have h3 : (n : ℝ) * s ≤ R * s := mul_le_mul_of_nonneg_right hnR hs
      nlinarith
end YangMills.Construction.StaircaseGauge
end
