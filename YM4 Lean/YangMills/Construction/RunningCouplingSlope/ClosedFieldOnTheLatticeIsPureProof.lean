import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import YangMills.Construction.RunningCouplingSlope.ClosedFieldOnTheLatticeIsPure
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeCohomology
section AxisTransport
variable {G : Type} [Group G]
private theorem exists_cumulativeProduct (u : ℤ → G) : ∃ T : ℤ → G, T 0 = 1 ∧ ∀ s, T (s + 1) = T s * u s := by
  let up : ℕ → G := fun n => Nat.rec 1 (fun m p => p * u m) n
  let dn : ℕ → G := fun n => Nat.rec 1 (fun m p => p * (u (-(m : ℤ) - 1))⁻¹) n
  have hup : ∀ n : ℕ, up (n + 1) = up n * u n := fun _ => rfl
  have hdn : ∀ n : ℕ, dn (n + 1) = dn n * (u (-(n : ℤ) - 1))⁻¹ := fun _ => rfl
  have hu0 : up 0 = 1 := rfl
  have hd0 : dn 0 = 1 := rfl
  refine ⟨fun s => if 0 ≤ s then up s.toNat else dn (-s).toNat, by simp [hu0], fun s => ?_⟩
  rcases le_or_gt 0 s with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have h1 : (0 : ℤ) ≤ (n : ℤ) + 1 := by omega
    have h2 : ((n : ℤ) + 1).toNat = n + 1 := by omega
    simp only [h, h1, if_true, h2, Int.toNat_natCast, hup]
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -s - 1)
    have hs : s = -(n : ℤ) - 1 := by omega
    subst hs
    have h3 : ¬ (0 : ℤ) ≤ -(n : ℤ) - 1 := by omega
    have h4 : (-(-(n : ℤ) - 1)).toNat = n + 1 := by omega
    simp only [h3, if_false, h4, hdn]
    rw [inv_mul_cancel_right]
    have e : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by ring
    rw [e]
    by_cases h5 : n = 0
    · subst h5
      simp [hu0, hd0]
    · have h6 : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
      have h7 : (-(-(n : ℤ))).toNat = n := by omega
      simp only [h6, if_false, h7]
private theorem cumulativeProduct_unique {u : ℤ → G} {T T' : ℤ → G} (h0 : T 0 = T' 0)
    (h : ∀ s, T (s + 1) = T s * u s) (h' : ∀ s, T' (s + 1) = T' s * u s) : ∀ s, T s = T' s := by
  intro s
  induction s using Int.induction_on with
  | zero => exact h0
  | succ n ih => rw [h, h', ih]
  | pred n ih =>
    have a := h (-(n : ℤ) - 1)
    have b := h' (-(n : ℤ) - 1)
    have e : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by ring
    rw [e] at a b
    rw [ih, b] at a
    exact (mul_right_cancel a).symm
variable (U : (Fin 4 → ℤ) → Fin 4 → G)
private def axisTransport (b : Fin 4 → ℤ) (i : Fin 4) : ℤ → G :=
  (exists_cumulativeProduct fun s : ℤ => U (b + (Pi.single i s : Fin 4 → ℤ)) i).choose
private theorem axisTransport_zero (b : Fin 4 → ℤ) (i : Fin 4) : axisTransport U b i 0 = 1 :=
  (exists_cumulativeProduct fun s : ℤ => U (b + (Pi.single i s : Fin 4 → ℤ)) i).choose_spec.1
private theorem axisTransport_succ (b : Fin 4 → ℤ) (i : Fin 4) (s : ℤ) :
    axisTransport U b i (s + 1) = axisTransport U b i s * U (b + Pi.single i s) i :=
  (exists_cumulativeProduct fun s : ℤ => U (b + (Pi.single i s : Fin 4 → ℤ)) i).choose_spec.2 s
variable {U}
private theorem single_add_one (i : Fin 4) (s : ℤ) :
    (Pi.single i (s + 1) : Fin 4 → ℤ) = Pi.single i s + Pi.single i 1 := by
  funext l
  by_cases hl : l = i
  · subst hl; simp
  · simp [hl]
private theorem axisTransport_translate
    (hflat : ∀ z (i j : Fin 4), i ≠ j → U z i * U (z + Pi.single i 1) j = U z j * U (z + Pi.single j 1) i)
    (b : Fin 4 → ℤ) (i j : Fin 4) (hij : i ≠ j) (s : ℤ) :
    axisTransport U (b + Pi.single j 1) i s = (U b j)⁻¹ * axisTransport U b i s * U (b + Pi.single i s) j := by
  refine cumulativeProduct_unique (u := fun s : ℤ => U (b + Pi.single j 1 + (Pi.single i s : Fin 4 → ℤ)) i)
    (T' := fun s : ℤ => (U b j)⁻¹ * axisTransport U b i s * U (b + (Pi.single i s : Fin 4 → ℤ)) j) ?_
    (axisTransport_succ U _ i) (fun s => ?_) s
  · simp [axisTransport_zero]
  · have e1 : b + Pi.single i (s + 1) = b + Pi.single i s + Pi.single i 1 := by
      rw [single_add_one, add_assoc]
    have e2 : b + Pi.single j 1 + Pi.single i s = b + Pi.single i s + Pi.single j 1 := by abel
    have h := hflat (b + Pi.single i s) i j hij
    rw [axisTransport_succ, e1, e2]
    calc (U b j)⁻¹ * (axisTransport U b i s * U (b + Pi.single i s) i) * U (b + Pi.single i s + Pi.single i 1) j
        = (U b j)⁻¹ * axisTransport U b i s * (U (b + Pi.single i s) i * U (b + Pi.single i s + Pi.single i 1) j) := by group
      _ = _ := by rw [h]; group
private def truncate (z : Fin 4 → ℤ) (k : ℕ) : Fin 4 → ℤ := fun l => if (l : ℕ) < k then z l else 0
variable (U)
open Classical in
private def pathTransport : ℕ → (Fin 4 → ℤ) → G
  | 0, _ => 1
  | k + 1, z => if hk : k < 4 then pathTransport k z * axisTransport U (truncate z k) ⟨k, hk⟩ (z ⟨k, hk⟩) else pathTransport k z
variable {U}
private theorem truncate_congr {z z' : Fin 4 → ℤ} {k : ℕ} (h : ∀ l : Fin 4, (l : ℕ) < k → z l = z' l) :
    truncate z k = truncate z' k := by
  funext l
  unfold truncate
  split_ifs with hl
  · exact h l hl
  · rfl
private theorem pathTransport_congr {z z' : Fin 4 → ℤ} : ∀ k : ℕ, (∀ l : Fin 4, (l : ℕ) < k → z l = z' l) →
    pathTransport U k z = pathTransport U k z' := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    have h1 : ∀ l : Fin 4, (l : ℕ) < k → z l = z' l := fun l hl => h l (by omega)
    simp only [pathTransport]
    split_ifs with hk
    · rw [ih h1, truncate_congr h1, h ⟨k, hk⟩ (by simp)]
    · exact ih h1
private theorem truncate_succ (z : Fin 4 → ℤ) {k : ℕ} (hk : k < 4) :
    truncate z (k + 1) = truncate z k + Pi.single ⟨k, hk⟩ (z ⟨k, hk⟩) := by
  funext l
  by_cases h1 : (l : ℕ) < k
  · have h2 : l ≠ ⟨k, hk⟩ := fun e => by rw [e] at h1; simp at h1
    simp [truncate, h1, Nat.lt_succ_of_lt h1, h2]
  · by_cases h2 : (l : ℕ) = k
    · have h3 : l = ⟨k, hk⟩ := Fin.ext h2
      subst h3
      simp [truncate]
    · have h3 : l ≠ ⟨k, hk⟩ := fun e => h2 (by rw [e])
      have h4 : ¬ (l : ℕ) < k + 1 := by omega
      simp [truncate, h1, h4, h3]
private theorem truncate_four (z : Fin 4 → ℤ) : truncate z 4 = z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.leadingCoords_four <;> assumption
private theorem pathTransport_add_single
    (hflat : ∀ z (i j : Fin 4), i ≠ j → U z i * U (z + Pi.single i 1) j = U z j * U (z + Pi.single j 1) i)
    (i : Fin 4) (z : Fin 4 → ℤ) : ∀ k, (i : ℕ) < k → k ≤ 4 →
      pathTransport U k (z + Pi.single i 1) = pathTransport U k z * U (truncate z k) i := by
  intro k hik
  induction k, hik using Nat.le_induction with
  | base =>
    intro _
    have hk : (i : ℕ) < 4 := i.2
    have hi : (⟨(i : ℕ), hk⟩ : Fin 4) = i := rfl
    simp only [pathTransport, hk, dif_pos, hi]
    have h1 : ∀ l : Fin 4, (l : ℕ) < (i : ℕ) → (z + Pi.single i 1 : Fin 4 → ℤ) l = z l := fun l hl => by
      have : l ≠ i := fun e => by rw [e] at hl; simp at hl
      simp [this]
    have h2 : (z + Pi.single i 1 : Fin 4 → ℤ) i = z i + 1 := by simp
    rw [pathTransport_congr _ h1, truncate_congr h1, h2, axisTransport_succ, truncate_succ z hk, hi, mul_assoc]
  | succ k hik ih =>
    intro hk4
    have hk : k < 4 := by omega
    have hne : (⟨k, hk⟩ : Fin 4) ≠ i := fun e => by
      have : k = (i : ℕ) := congrArg Fin.val e
      simp at hik
      omega
    simp only [pathTransport, hk, dif_pos]
    have hf : truncate (z + Pi.single i 1) k = truncate z k + Pi.single i 1 := by
      funext l
      by_cases hl : l = i
      · subst hl
        have : (l : ℕ) < k := hik
        simp [truncate, this]
      · by_cases h1 : (l : ℕ) < k <;> simp [truncate, h1, hl]
    have hz : (z + Pi.single i 1 : Fin 4 → ℤ) ⟨k, hk⟩ = z ⟨k, hk⟩ := by simp [hne]
    rw [ih (by omega), hf, hz, axisTransport_translate hflat _ _ _ hne, truncate_succ z hk]
    group
end AxisTransport
theorem flatConnection_isPureGauge : FlatConnectionIsPureGauge := by
  intro G _ U hU
  have hflat : ∀ z (i j : Fin 4), i ≠ j → U z i * U (z + Pi.single i 1) j = U z j * U (z + Pi.single j 1) i := by
    intro z i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hU z i j h
    · exact (hU z j i h).symm
  refine ⟨fun z => (pathTransport U 4 z)⁻¹, fun z i => ?_⟩
  have h := pathTransport_add_single hflat i z 4 i.2 le_rfl
  rw [truncate_four] at h
  simp only [inv_inv]
  rw [h]
  group
end YangMills.Construction.LatticeCohomology
end
