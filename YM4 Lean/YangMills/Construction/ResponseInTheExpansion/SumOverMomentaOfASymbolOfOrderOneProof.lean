import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.LawOnABoxOfTheFlow.DecayOfASymbolProof
import YangMills.Construction.ResponseInTheExpansion.SumOverMomentaOfASymbolOfOrderOne
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.TorusFields YangMills.Construction.LinearResponse
namespace ResponseInTheExpansion
namespace OrderOneMomentumSum
section Differences
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def iterDiff (w : V) : ℕ → (V → ℂ) → V → ℂ
  | 0, f => f
  | k + 1, f => iterDiff w k (fun x => f (x + w) - f x)
theorem iterDiff_succ (w : V) (k : ℕ) (f : V → ℂ) (x : V) :
    iterDiff w (k + 1) f x = iterDiff w k f (x + w) - iterDiff w k f x := by
  induction k generalizing f x with
  | zero => rfl
  | succ k ih =>
    have h1 : iterDiff w (k + 1 + 1) f x = iterDiff w (k + 1) (fun x => f (x + w) - f x) x := rfl
    have h2 : ∀ y, iterDiff w (k + 1) f y = iterDiff w k (fun x => f (x + w) - f x) y := fun _ => rfl
    rw [h1, ih, h2, h2]
theorem mul_iterDiff_eq_of_forall (w : V) (k : ℕ) (c d : ℂ) (f g : V → ℂ) (x y : V)
    (H : ∀ s : ℕ, s ≤ k → c * f (x + s • w) = d * g (y + s • w)) :
    c * iterDiff w k f x = d * iterDiff w k g y := by
  induction k generalizing f g with
  | zero => simpa [iterDiff] using H 0 le_rfl
  | succ k ih =>
    refine ih (fun x => f (x + w) - f x) (fun x => g (x + w) - g x) fun s hs => ?_
    have h1 := H s (by omega)
    have h2 := H (s + 1) (by omega)
    have e1 : x + (s + 1) • w = x + s • w + w := by rw [succ_nsmul, add_assoc]
    have e2 : y + (s + 1) • w = y + s • w + w := by rw [succ_nsmul, add_assoc]
    rw [e1, e2] at h2
    rw [mul_sub, mul_sub, h1, h2]
theorem norm_iterDiff_le (w : V) (k : ℕ) (f : V → ℂ) (x : V) (M : ℝ)
    (H : ∀ t ∈ Set.Icc (0 : ℝ) k, ContDiffAt ℝ k f (x + t • w) ∧
      ‖iteratedFDeriv ℝ k f (x + t • w)‖ ≤ M) :
    ‖iterDiff w k f x‖ ≤ ‖w‖ ^ k * M := by
  induction k generalizing f M with
  | zero =>
    have := (H 0 (by simp)).2
    simpa [iterDiff, norm_iteratedFDeriv_zero] using this
  | succ k ih =>
    have key : ‖iterDiff w k (fun x => f (x + w) - f x) x‖ ≤ ‖w‖ ^ k * (‖w‖ * M) := by
      refine ih (fun x => f (x + w) - f x) (‖w‖ * M) fun t ht => ?_
      obtain ⟨ht0, ht1⟩ := ht
      set y := x + t • w with hy
      have hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((k + 1 : ℕ)) f (y + s • w) ∧
          ‖iteratedFDeriv ℝ (k + 1) f (y + s • w)‖ ≤ M := by
        intro s hs
        have e : y + s • w = x + (t + s) • w := by rw [hy, add_smul, add_assoc]
        rw [e]
        refine H (t + s) ⟨by linarith [hs.1], ?_⟩
        push_cast
        linarith [hs.2]
      have h0 := hA 0 (by simp)
      have h1 := hA 1 (by simp)
      simp only [zero_smul, add_zero, one_smul] at h0 h1
      have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast Nat.le_succ k
      have c0 : ContDiffAt ℝ k f y := h0.1.of_le hle
      have c1 : ContDiffAt ℝ k f (y + w) := h1.1.of_le hle
      have c2 : ContDiffAt ℝ k (fun u => f (u + w)) y :=
        ContDiffAt.comp y c1 (contDiffAt_id.add contDiffAt_const)
      refine ⟨c2.sub c0, ?_⟩
      have e1 : iteratedFDeriv ℝ k (fun u => f (u + w) - f u) y =
          iteratedFDeriv ℝ k f (y + w) - iteratedFDeriv ℝ k f y := by
        have := iteratedFDeriv_sub_apply (𝕜 := ℝ) c2 c0
        have e2 : iteratedFDeriv ℝ k (fun u => f (u + w)) y = iteratedFDeriv ℝ k f (y + w) :=
          iteratedFDeriv_comp_add_right k w y
        rw [← e2, ← this]
        rfl
      rw [e1]
      have hseg : ∀ u ∈ segment ℝ y (y + w), ∃ s ∈ Set.Icc (0 : ℝ) 1, u = y + s • w := by
        intro u hu
        rw [segment_eq_image'] at hu
        obtain ⟨s, hs, rfl⟩ := hu
        exact ⟨s, hs, by simp⟩
      have mv := (convex_segment y (y + w)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := iteratedFDeriv ℝ k f) (f' := fderiv ℝ (iteratedFDeriv ℝ k f)) (C := M)
        (x := y) (y := y + w) ?_ ?_ (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
      · simpa [mul_comm] using mv
      · intro u hu
        obtain ⟨s, hs, rfl⟩ := hseg u hu
        have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (y + s • w) :=
          (hA s hs).1.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
        exact hd.hasFDerivAt.hasFDerivWithinAt
      · intro u hu
        obtain ⟨s, hs, rfl⟩ := hseg u hu
        rw [norm_fderiv_iteratedFDeriv]
        exact (hA s hs).2
    calc ‖iterDiff w (k + 1) f x‖ = ‖iterDiff w k (fun x => f (x + w) - f x) x‖ := rfl
      _ ≤ ‖w‖ ^ k * (‖w‖ * M) := key
      _ = ‖w‖ ^ (k + 1) * M := by ring
end Differences
section Boxes
variable {N : ℕ} [NeZero N]
def maxCoord (j : TorusSite N) : ℕ := Finset.univ.sup fun k => (j k).valMinAbs.natAbs
def centredInterval (N : ℕ) [NeZero N] (M : ℕ) : Finset (ZMod N) :=
  Finset.univ.filter fun a => a.valMinAbs.natAbs ≤ M
def centredBox (N : ℕ) [NeZero N] (M : ℕ) : Finset (TorusSite N) :=
  Fintype.piFinset fun _ => centredInterval N M
theorem mem_centredBox {M : ℕ} {j : TorusSite N} : j ∈ centredBox N M ↔ maxCoord j ≤ M := by
  simp [centredBox, centredInterval, maxCoord, Fintype.mem_piFinset, Finset.sup_le_iff]
theorem card_centredInterval_le (M : ℕ) : (centredInterval N M).card ≤ 2 * M + 1 := by
  have hsub : centredInterval N M ⊆ (Finset.Icc (-(M : ℤ)) M).image (fun n : ℤ => (n : ZMod N)) := by
    intro a ha
    simp only [centredInterval, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine Finset.mem_image.2 ⟨a.valMinAbs, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    exact ZMod.coe_valMinAbs a
  calc (centredInterval N M).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.Icc (-(M : ℤ)) M).card := Finset.card_image_le
    _ = 2 * M + 1 := by
      rw [Int.card_Icc]
      omega
theorem card_centredBox_le (M : ℕ) : (centredBox N M).card ≤ (2 * M + 1) ^ 4 := by
  rw [centredBox, Fintype.card_piFinset]
  simpa using Nat.pow_le_pow_left (card_centredInterval_le (N := N) M) 4
theorem maxCoord_le_half (j : TorusSite N) : maxCoord j ≤ N / 2 :=
  Finset.sup_le fun k _ => ZMod.natAbs_valMinAbs_le (j k)
theorem sum_inv_pow_five_far_aux (n : ℕ) : ∀ L : ℕ, 1 ≤ L → N ≤ L + n →
    ∑ j ∈ Finset.univ.filter (fun j : TorusSite N => L < maxCoord j), ((maxCoord j : ℝ) ^ 5)⁻¹ ≤ 1250 / L := by
  induction n with
  | zero =>
    intro L hL hN
    have : Finset.univ.filter (fun j : TorusSite N => L < maxCoord j) = ∅ := by
      refine Finset.filter_false_of_mem fun j _ => ?_
      have := maxCoord_le_half j
      omega
    rw [this]
    simp only [Finset.sum_empty]
    positivity
  | succ n ih =>
    intro L hL hN
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have h2 := ih (2 * L) (by omega) (by omega)
    have hsplit : Finset.univ.filter (fun j : TorusSite N => L < maxCoord j) ⊆
        (Finset.univ.filter (fun j : TorusSite N => L < maxCoord j ∧ maxCoord j ≤ 2 * L)) ∪
        (Finset.univ.filter (fun j : TorusSite N => 2 * L < maxCoord j)) := by
      intro j hj
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      omega
    have h1 : ∑ j ∈ Finset.univ.filter (fun j : TorusSite N => L < maxCoord j ∧ maxCoord j ≤ 2 * L),
        ((maxCoord j : ℝ) ^ 5)⁻¹ ≤ 625 / L := by
      calc _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : TorusSite N => L < maxCoord j ∧ maxCoord j ≤ 2 * L),
            ((L : ℝ) ^ 5)⁻¹ := by
            refine Finset.sum_le_sum fun j hj => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            have : (L : ℝ) ≤ maxCoord j := by exact_mod_cast hj.1.le
            exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hLpos.le this 5)
        _ = (Finset.univ.filter (fun j : TorusSite N => L < maxCoord j ∧ maxCoord j ≤ 2 * L)).card *
            ((L : ℝ) ^ 5)⁻¹ := by simp
        _ ≤ ((5 * L : ℕ) : ℝ) ^ 4 * ((L : ℝ) ^ 5)⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hc : (Finset.univ.filter (fun j : TorusSite N => L < maxCoord j ∧ maxCoord j ≤ 2 * L)).card ≤
                (5 * L) ^ 4 := by
              calc _ ≤ (centredBox N (2 * L)).card := by
                    refine Finset.card_le_card fun j hj => ?_
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                    exact mem_centredBox.2 hj.2
                _ ≤ (2 * (2 * L) + 1) ^ 4 := card_centredBox_le _
                _ ≤ (5 * L) ^ 4 := Nat.pow_le_pow_left (by omega) 4
            exact_mod_cast hc
        _ = 625 / L := by
            push_cast
            field_simp
            ring
    calc _ ≤ ∑ j ∈ (Finset.univ.filter (fun j : TorusSite N => L < maxCoord j ∧ maxCoord j ≤ 2 * L)) ∪
            (Finset.univ.filter (fun j : TorusSite N => 2 * L < maxCoord j)), ((maxCoord j : ℝ) ^ 5)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsplit fun _ _ _ => by positivity
      _ = _ + _ := Finset.sum_union (by
          refine Finset.disjoint_filter.2 fun j _ h1 h2 => ?_
          omega)
      _ ≤ 625 / L + 1250 / ((2 * L : ℕ) : ℝ) := add_le_add h1 h2
      _ = 1250 / L := by
          push_cast
          field_simp
          ring
theorem sum_inv_pow_five_far {L : ℕ} (hL : 1 ≤ L) :
    ∑ j ∈ Finset.univ.filter (fun j : TorusSite N => L < maxCoord j), ((maxCoord j : ℝ) ^ 5)⁻¹ ≤ 1250 / L :=
  sum_inv_pow_five_far_aux N L hL (by omega)
end Boxes
section Momenta
variable {N : ℕ} [NeZero N]
def latticeStep (N : ℕ) (i : Fin 4) : Fin 4 → ℝ := Pi.single i (2 * Real.pi / N)
def fullPeriod (i : Fin 4) : Fin 4 → ℝ := Pi.single i (2 * Real.pi)
def planeWave (z y : Fin 4 → ℝ) : ℂ := Complex.exp (Complex.I * (∑ k, y k * z k : ℝ))
theorem planeWave_add (z y y' : Fin 4 → ℝ) : planeWave z (y + y') = planeWave z y * planeWave z y' := by
  rw [planeWave, planeWave, planeWave, ← Complex.exp_add, ← mul_add]
  congr 2
  rw [← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 2
  funext k
  simp [add_mul]
theorem norm_planeWave (z y : Fin 4 → ℝ) : ‖planeWave z y‖ = 1 := by apply _root_.YangMills.DeltaSharedProofs.p501034 <;> assumption
theorem planeWave_fullPeriod (z : Fin 4 → ℝ) (i : Fin 4) :
    planeWave z (fullPeriod i) = Complex.exp (Complex.I * (2 * Real.pi * z i : ℝ)) := by
  have : ∑ k, fullPeriod i k * z k = 2 * Real.pi * z i := by
    rw [Finset.sum_eq_single i]
    · simp [fullPeriod]
    · intro k _ hk
      simp [fullPeriod, hk]
    · simp
  rw [planeWave, this]
theorem planeWave_latticeStep (z : Fin 4 → ℝ) (i : Fin 4) :
    planeWave z (latticeStep N i) = Complex.exp (Complex.I * (2 * Real.pi / N * z i : ℝ)) := by
  have : ∑ k, latticeStep N i k * z k = 2 * Real.pi / N * z i := by
    rw [Finset.sum_eq_single i]
    · simp [latticeStep]
    · intro k _ hk
      simp [latticeStep, hk]
    · simp
  rw [planeWave, this]
theorem dualMomentum_apply (j : TorusSite N) (k : Fin 4) :
    dualMomentum j k = 2 * Real.pi / N * ((j k).valMinAbs : ℝ) := by
  simp only [dualMomentum]
  ring
theorem valMinAbs_add_one_of_le (a : ZMod N) (h : 2 * (a.valMinAbs + 1) ≤ N) :
    (a + 1).valMinAbs = a.valMinAbs + 1 := by
  rw [ZMod.valMinAbs_spec]
  have h1 := ZMod.valMinAbs_mem_Ioc a
  refine ⟨by simp, ?_⟩
  constructor
  · have := h1.1
    omega
  · omega
theorem valMinAbs_add_one_of_lt (a : ZMod N) (h : (N : ℤ) < 2 * (a.valMinAbs + 1)) :
    (a + 1).valMinAbs = a.valMinAbs + 1 - N := by
  rw [ZMod.valMinAbs_spec]
  have h1 := ZMod.valMinAbs_mem_Ioc a
  refine ⟨by simp, ?_⟩
  have h2 := h1.2
  have hN : (1 : ℤ) ≤ N := by exact_mod_cast NeZero.one_le
  constructor <;> omega
theorem add_single_apply_ne (j : TorusSite N) {i k : Fin 4} (h : k ≠ i) :
    (j + (Pi.single i (1 : ZMod N) : TorusSite N)) k = j k := by
  simp [h]
theorem add_single_apply_self (j : TorusSite N) (i : Fin 4) :
    (j + (Pi.single i (1 : ZMod N) : TorusSite N)) i = j i + 1 := by
  simp
theorem dualMomentum_add_single (j : TorusSite N) (i : Fin 4) :
    dualMomentum (j + Pi.single i 1) = dualMomentum j + latticeStep N i ∨
    (dualMomentum (j + Pi.single i 1) + fullPeriod i = dualMomentum j + latticeStep N i ∧
      (N : ℤ) < 2 * ((j i).valMinAbs + 1)) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  by_cases h : 2 * ((j i).valMinAbs + 1) ≤ N
  · left
    funext k
    by_cases hk : k = i
    · subst hk
      rw [Pi.add_apply, dualMomentum_apply, dualMomentum_apply, add_single_apply_self,
        valMinAbs_add_one_of_le _ h]
      simp only [latticeStep, Pi.single_eq_same]
      push_cast
      ring
    · rw [Pi.add_apply, dualMomentum_apply, dualMomentum_apply, add_single_apply_ne j hk]
      simp [latticeStep, hk]
  · right
    refine ⟨?_, by omega⟩
    funext k
    by_cases hk : k = i
    · subst hk
      rw [Pi.add_apply, Pi.add_apply, dualMomentum_apply, dualMomentum_apply, add_single_apply_self,
        valMinAbs_add_one_of_lt _ (not_le.1 h)]
      simp only [latticeStep, fullPeriod, Pi.single_eq_same]
      push_cast
      field_simp
      ring
    · rw [Pi.add_apply, Pi.add_apply, dualMomentum_apply, dualMomentum_apply, add_single_apply_ne j hk]
      simp [latticeStep, fullPeriod, hk]
def OffDualLattice (p : Fin 4 → ℝ) : Prop := ∀ w : Fin 4 → ℤ, p ≠ fun l => 2 * Real.pi * (w l : ℝ)
theorem offDualLattice_of_coord {y : Fin 4 → ℝ} {k : Fin 4} (h0 : 0 < |y k|) (h1 : |y k| < 2 * Real.pi) :
    OffDualLattice y := by
  intro w h
  have e : y k = 2 * Real.pi * (w k : ℝ) := congrFun h k
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h0 h1
  have h2 : |(w k : ℝ)| < 1 := by
    by_contra hc
    nlinarith [not_lt.1 hc]
  have h3 : |w k| < 1 := by exact_mod_cast h2
  have h4 : w k = 0 := Int.abs_lt_one_iff.1 h3
  rw [h4] at h0
  simp at h0
theorem eventually_offDualLattice {y : Fin 4 → ℝ} {k : Fin 4} (h0 : 0 < |y k|) (h1 : |y k| < 2 * Real.pi) :
    ∀ᶠ u in nhds y, OffDualLattice u := by
  have hc : Continuous fun u : Fin 4 → ℝ => |u k| := (continuous_apply k).abs
  have ho : IsOpen {u : Fin 4 → ℝ | 0 < |u k| ∧ |u k| < 2 * Real.pi} :=
    (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  filter_upwards [ho.mem_nhds ⟨h0, h1⟩] with u hu
  exact offDualLattice_of_coord hu.1 hu.2
theorem OffDualLattice.sub_fullRotation {y : Fin 4 → ℝ} {i : Fin 4} (h : OffDualLattice y) :
    OffDualLattice (y - fullPeriod i) := by
  intro w hw
  refine h (w + Pi.single i 1) ?_
  funext l
  have e := congrFun hw l
  simp only [Pi.sub_apply] at e
  have e2 : y l = 2 * Real.pi * (w l : ℝ) + fullPeriod i l := by linarith
  rw [e2]
  by_cases hl : l = i
  · subst hl
    simp [fullPeriod]
    ring
  · simp [fullPeriod, hl]
theorem planeWave_mul_iterDiff_shift (b : (Fin 4 → ℝ) → ℂ) (z : Fin 4 → ℝ) (i : Fin 4) (hN : 13 ≤ N)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (k : ℕ) (hk : k ≤ 5) (j : TorusSite N) :
    planeWave z (latticeStep N i) * planeWave z (dualMomentum j) *
        iterDiff (latticeStep N i) k b (dualMomentum j + latticeStep N i) =
      planeWave z (dualMomentum (j + Pi.single i 1)) *
        iterDiff (latticeStep N i) k b (dualMomentum (j + Pi.single i 1)) := by
  rcases dualMomentum_add_single j i with h | ⟨h, hw⟩
  · rw [h, planeWave_add]
    ring
  · refine mul_iterDiff_eq_of_forall (latticeStep N i) k _ _ b b _ _ fun s hs => ?_
    have hh : (0 : ℝ) < 2 * Real.pi / N := by positivity
    set p := dualMomentum (j + Pi.single i 1) + s • latticeStep N i with hp
    have hpt : dualMomentum j + latticeStep N i + s • latticeStep N i = p + fullPeriod i := by
      rw [← h, hp]
      abel
    have hci := (ZMod.valMinAbs_mem_Ioc (j i)).2
    have hpi : (p + fullPeriod i) i = 2 * Real.pi / N * ((j i).valMinAbs + 1 + s) := by
      rw [← hpt]
      have e : (s • latticeStep N i) i = s * (2 * Real.pi / N) := by simp [latticeStep]
      rw [Pi.add_apply, Pi.add_apply, e, dualMomentum_apply]
      simp only [latticeStep, Pi.single_eq_same]
      ring
    have ht : fullPeriod i i = 2 * Real.pi := by simp [fullPeriod]
    have hpos : 0 < (p + fullPeriod i) i := by
      rw [hpi]
      refine mul_pos hh ?_
      have : (0 : ℤ) < (j i).valMinAbs + 1 + s := by omega
      exact_mod_cast this
    have hneg : p i < 0 := by
      have e : p i = 2 * Real.pi / N * ((j i).valMinAbs + 1 + s - N) := by
        have : p i = (p + fullPeriod i) i - 2 * Real.pi := by
          rw [Pi.add_apply, ht]
          ring
        rw [this, hpi]
        field_simp
      rw [e]
      refine mul_neg_of_pos_of_neg hh ?_
      have : (j i).valMinAbs + 1 + s - N < (0 : ℤ) := by omega
      exact_mod_cast this
    have hoff : OffDualLattice p := by
      refine offDualLattice_of_coord (k := i) (abs_pos.2 hneg.ne) ?_
      rw [abs_of_neg hneg]
      rw [Pi.add_apply, ht] at hpos
      linarith
    have key := H p hoff
    rw [← key, hpt]
    have hw2 : planeWave z (latticeStep N i) * planeWave z (dualMomentum j) =
        planeWave z (dualMomentum (j + Pi.single i 1)) * planeWave z (fullPeriod i) := by
      rw [← planeWave_add, ← planeWave_add, h, add_comm]
    rw [hw2]
    ring
end Momenta
section Bounds
variable {N : ℕ} [NeZero N] {B : ℕ → ℝ} {b : (Fin 4 → ℝ) → ℂ} {z : Fin 4 → ℝ} {i : Fin 4}
theorem rpow_sq_eq_inv_pow {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    (ρ ^ 2) ^ (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)) / 2) = (ρ ^ n)⁻¹ := by
  have e : ((1 : ℝ) - ((n + 1 : ℕ) : ℝ)) / 2 = -((n : ℝ) / 2) := by
    push_cast
    ring
  rw [e, Real.rpow_neg (by positivity), ← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
  have e2 : ((2 : ℕ) : ℝ) * ((n : ℝ) / 2) = n := by
    push_cast
    ring
  rw [e2, Real.rpow_natCast]
theorem sqNorm_nonneg (y : Fin 4 → ℝ) : 0 ≤ sqNorm y := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.sumSq_nonneg <;> assumption
theorem sq_le_sqNorm (y : Fin 4 → ℝ) (k : Fin 4) : y k ^ 2 ≤ sqNorm y := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.sq_apply_le_sumSq <;> assumption
theorem ne_zero_of_sqNorm_pos {y : Fin 4 → ℝ} (h : 0 < sqNorm y) : y ≠ 0 := by
  rintro rfl
  simp [sqNorm] at h
theorem norm_iteratedFDeriv_le_of_mem_cube (hb : IsSymbolOfOrder B 1 b) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Fin 4 → ℝ} (hy : ∀ k, |y k| ≤ Real.pi) (hs : ρ ^ 2 ≤ sqNorm y) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n + 1) b y‖ ≤ |B (n + 1)| * (ρ ^ n)⁻¹ := by
  have hpos : 0 < sqNorm y := lt_of_lt_of_le (by positivity) hs
  have h1 := hb.deriv_le (n + 1) y (ne_zero_of_sqNorm_pos hpos) hy
  have hexp : ((1 : ℝ) - ((n + 1 : ℕ) : ℝ)) / 2 ≤ 0 := by
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h2 : sqNorm y ^ (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)) / 2) ≤ (ρ ^ n)⁻¹ := by
    rw [← rpow_sq_eq_inv_pow hρ n]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hs hexp
  calc _ ≤ B (n + 1) * sqNorm y ^ (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)) / 2) := h1
    _ ≤ |B (n + 1)| * sqNorm y ^ (((1 : ℝ) - ((n + 1 : ℕ) : ℝ)) / 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hpos.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
theorem contDiffAt_of_coord (hb : IsSymbolOfOrder B 1 b) (r : ℕ) {y : Fin 4 → ℝ} {k : Fin 4}
    (h0 : 0 < |y k|) (h1 : |y k| < 2 * Real.pi) : ContDiffAt ℝ r b y := by
  refine (hb.smooth r).contDiffAt ?_
  filter_upwards [eventually_offDualLattice h0 h1] with u hu
  exact hu
theorem norm_iteratedFDeriv_sub_fullPeriod (hb : IsSymbolOfOrder B 1 b)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (r : ℕ) {y : Fin 4 → ℝ} {k : Fin 4} (h0 : 0 < |y k|) (h1 : |y k| < 2 * Real.pi) :
    ‖iteratedFDeriv ℝ r b y‖ = ‖iteratedFDeriv ℝ r b (y - fullPeriod i)‖ := by
  have hc : ContDiffAt ℝ r b y := contDiffAt_of_coord hb r h0 h1
  have hev : (fun u => planeWave z (fullPeriod i) • b u) =ᶠ[nhds y] fun u => b (u - fullPeriod i) := by
    filter_upwards [eventually_offDualLattice h0 h1] with u hu
    have := H (u - fullPeriod i) hu.sub_fullRotation
    rw [sub_add_cancel] at this
    rw [← this, smul_eq_mul, mul_comm]
  have e1 := (Filter.EventuallyEq.iteratedFDeriv ℝ hev r).eq_of_nhds
  rw [iteratedFDeriv_const_smul_apply' hc, iteratedFDeriv_comp_sub r (fullPeriod i) y] at e1
  rw [← e1, norm_smul, norm_planeWave, one_mul]
theorem abs_dualMomentum_le (j : TorusSite N) (k : Fin 4) :
    |dualMomentum j k| ≤ 2 * Real.pi / N * maxCoord j := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have h1 : (j k).valMinAbs.natAbs ≤ maxCoord j :=
    Finset.le_sup (f := fun k => (j k).valMinAbs.natAbs) (Finset.mem_univ k)
  have h2 : |((j k).valMinAbs : ℝ)| ≤ maxCoord j := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast h1
  rw [dualMomentum_apply, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / N)]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)
theorem maxCoord_mul_le_pi (j : TorusSite N) : 2 * Real.pi / N * maxCoord j ≤ Real.pi := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have h1 : ((maxCoord j : ℕ) : ℝ) ≤ N / 2 := by
    have := maxCoord_le_half j
    have h2 : 2 * maxCoord j ≤ N := by omega
    have : (2 : ℝ) * maxCoord j ≤ N := by exact_mod_cast h2
    linarith
  calc _ ≤ 2 * Real.pi / N * (N / 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.pi := by
      field_simp
theorem exists_abs_dualMomentum_eq (j : TorusSite N) :
    ∃ k, |dualMomentum j k| = 2 * Real.pi / N * maxCoord j := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty
    (fun k => (j k).valMinAbs.natAbs)
  refine ⟨k, ?_⟩
  have e : maxCoord j = (j k).valMinAbs.natAbs := hk
  rw [dualMomentum_apply, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / N), e]
  congr 1
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  simp
theorem iteratedFDeriv_bound_along_step (hb : IsSymbolOfOrder B 1 b)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (hN : 24 ≤ N) (j : TorusSite N) (hm : 12 ≤ maxCoord j) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 6) (n : ℕ) :
    ContDiffAt ℝ ((n + 1 : ℕ)) b (dualMomentum j + t • latticeStep N i) ∧
    ‖iteratedFDeriv ℝ (n + 1) b (dualMomentum j + t • latticeStep N i)‖ ≤
      |B (n + 1)| * (((2 * Real.pi / N * maxCoord j) / 2) ^ n)⁻¹ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hN24 : (24 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  set h := 2 * Real.pi / N with hh
  have hhpos : 0 < h := by positivity
  have h12 : 12 * h ≤ Real.pi := by
    rw [hh]
    have : 12 * (2 * Real.pi / N) = 24 * Real.pi / N := by ring
    rw [this, div_le_iff₀ hNpos]
    nlinarith
  have hm' : (12 : ℝ) ≤ maxCoord j := by exact_mod_cast hm
  set ρ := h * maxCoord j / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρπ : ρ ≤ Real.pi / 2 := by
    have := maxCoord_mul_le_pi j
    rw [hρ]
    linarith
  set y := dualMomentum j + t • latticeStep N i with hy
  have hyk : ∀ k, k ≠ i → y k = dualMomentum j k := by
    intro k hk
    simp [hy, latticeStep, hk]
  have hyi : y i = dualMomentum j i + t * h := by
    simp [hy, latticeStep, hh]
  have hq : ∀ k, |dualMomentum j k| ≤ Real.pi :=
    fun k => (abs_dualMomentum_le j k).trans (maxCoord_mul_le_pi j)
  obtain ⟨k₀, hk₀⟩ := exists_abs_dualMomentum_eq j
  have ht6 : t * h ≤ 6 * h := mul_le_mul_of_nonneg_right ht.2 hhpos.le
  have ht0 : 0 ≤ t * h := mul_nonneg ht.1 hhpos.le
  have hqi := abs_le.1 (hq i)
  by_cases hcase : y i ≤ Real.pi
  · have hcube : ∀ k, |y k| ≤ Real.pi := by
      intro k
      by_cases hk : k = i
      · subst hk
        rw [abs_le]
        constructor
        · rw [hyi]
          linarith [hqi.1]
        · exact hcase
      · rw [hyk k hk]
        exact hq k
    have hlow : ρ ≤ |y k₀| := by
      by_cases hk : k₀ = i
      · subst hk
        rw [hyi]
        have hA : h * maxCoord j = |dualMomentum j k₀| := hk₀.symm
        rcases le_total 0 (dualMomentum j k₀) with hs | hs
        · rw [abs_of_nonneg hs] at hA
          rw [abs_of_nonneg (by linarith)]
          rw [hρ]
          nlinarith
        · rw [abs_of_nonpos hs] at hA
          have hle : ρ ≤ -(dualMomentum j k₀ + t * h) := by
            rw [hρ]
            nlinarith
          exact hle.trans (neg_le_abs _)
      · rw [hyk k₀ hk, hk₀, hρ]
        nlinarith
    have hs : ρ ^ 2 ≤ sqNorm y := by
      refine le_trans ?_ (sq_le_sqNorm y k₀)
      rw [← sq_abs (y k₀)]
      exact pow_le_pow_left₀ hρpos.le hlow 2
    have hk1 : |y k₀| < 2 * Real.pi := by
      have := hcube k₀
      linarith
    exact ⟨contDiffAt_of_coord hb _ (lt_of_lt_of_le hρpos hlow) hk1,
      norm_iteratedFDeriv_le_of_mem_cube hb hρpos hcube hs n⟩
  · have hgt : Real.pi < y i := not_le.1 hcase
    set y' := y - fullPeriod i with hy'
    have ht' : fullPeriod i i = 2 * Real.pi := by simp [fullPeriod]
    have hy'i : y' i = y i - 2 * Real.pi := by
      rw [hy', Pi.sub_apply, ht']
    have hy'k : ∀ k, k ≠ i → y' k = dualMomentum j k := by
      intro k hk
      rw [hy', Pi.sub_apply, hyk k hk]
      simp [fullPeriod, hk]
    have hcube : ∀ k, |y' k| ≤ Real.pi := by
      intro k
      by_cases hk : k = i
      · subst hk
        rw [abs_le, hy'i, hyi]
        constructor <;> linarith [hqi.2]
      · rw [hy'k k hk]
        exact hq k
    have hlow : ρ ≤ |y' k₀| := by
      by_cases hk : k₀ = i
      · subst hk
        have hneg : ρ ≤ -(y' k₀) := by
          rw [hy'i, hyi]
          linarith [hqi.2]
        exact hneg.trans (neg_le_abs _)
      · rw [hy'k k₀ hk, hk₀, hρ]
        nlinarith
    have hs : ρ ^ 2 ≤ sqNorm y' := by
      refine le_trans ?_ (sq_le_sqNorm y' k₀)
      rw [← sq_abs (y' k₀)]
      exact pow_le_pow_left₀ hρpos.le hlow 2
    have hi0 : 0 < |y i| := by
      rw [abs_of_pos (by linarith)]
      linarith
    have hi1 : |y i| < 2 * Real.pi := by
      rw [abs_of_pos (by linarith), hyi]
      linarith [hqi.2]
    refine ⟨contDiffAt_of_coord hb _ hi0 hi1, ?_⟩
    rw [norm_iteratedFDeriv_sub_fullPeriod hb H (n + 1) hi0 hi1]
    exact norm_iteratedFDeriv_le_of_mem_cube hb hρpos hcube hs n
theorem norm_latticeStep (i : Fin 4) : ‖latticeStep N i‖ = 2 * Real.pi / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [latticeStep, Pi.norm_single, Real.norm_of_nonneg (by positivity)]
def derivConstant (B : ℕ → ℝ) : ℝ := 64 * ∑ k ∈ Finset.range 7, |B k|
theorem derivConstant_nonneg (B : ℕ → ℝ) : 0 ≤ derivConstant B :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
theorem abs_le_sum_range_seven (B : ℕ → ℝ) {k : ℕ} (hk : k ≤ 6) :
    |B k| ≤ ∑ k ∈ Finset.range 7, |B k| :=
  Finset.single_le_sum (f := fun k => |B k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))
theorem norm_symbol_le (hb : IsSymbolOfOrder B 1 b) (j : TorusSite N) (hj : dualMomentum j ≠ 0) :
    ‖b (dualMomentum j)‖ ≤ derivConstant B * (2 * Real.pi / N) * maxCoord j := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  set h := 2 * Real.pi / N with hh
  have hq : ∀ k, |dualMomentum j k| ≤ Real.pi :=
    fun k => (abs_dualMomentum_le j k).trans (maxCoord_mul_le_pi j)
  have h1 := hb.deriv_le 0 (dualMomentum j) hj hq
  rw [norm_iteratedFDeriv_zero] at h1
  have hsl : sqNorm (dualMomentum j) ≤ (2 * (h * maxCoord j)) ^ 2 := by
    have : ∀ k, dualMomentum j k ^ 2 ≤ (h * maxCoord j) ^ 2 := fun k => by
      rw [← sq_abs (dualMomentum j k)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_dualMomentum_le j k) 2
    calc sqNorm (dualMomentum j) ≤ ∑ _k : Fin 4, (h * maxCoord j) ^ 2 :=
          Finset.sum_le_sum fun k _ => this k
      _ = (2 * (h * maxCoord j)) ^ 2 := by
          simp
          ring
  have hroot : sqNorm (dualMomentum j) ^ (((1 : ℝ) - ((0 : ℕ) : ℝ)) / 2) ≤ 2 * (h * maxCoord j) := by
    have e : ((1 : ℝ) - ((0 : ℕ) : ℝ)) / 2 = 1 / 2 := by norm_num
    rw [e, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.2 ⟨by positivity, hsl⟩
  have hsum := abs_le_sum_range_seven B (k := 0) (by omega)
  have hS : 0 ≤ ∑ k ∈ Finset.range 7, |B k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hx : 0 ≤ h * maxCoord j := by positivity
  calc _ ≤ B 0 * sqNorm (dualMomentum j) ^ (((1 : ℝ) - ((0 : ℕ) : ℝ)) / 2) := h1
    _ ≤ |B 0| * sqNorm (dualMomentum j) ^ (((1 : ℝ) - ((0 : ℕ) : ℝ)) / 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _)
          (Real.rpow_nonneg (sqNorm_nonneg _) _)
    _ ≤ |B 0| * (2 * (h * maxCoord j)) := mul_le_mul_of_nonneg_left hroot (abs_nonneg _)
    _ ≤ (∑ k ∈ Finset.range 7, |B k|) * (2 * (h * maxCoord j)) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ ≤ (64 * ∑ k ∈ Finset.range 7, |B k|) * (h * maxCoord j) := by nlinarith
    _ = _ := by rw [derivConstant]; ring
theorem norm_iterDiff_far_le (hb : IsSymbolOfOrder B 1 b)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (hN : 24 ≤ N) (j : TorusSite N) (hm : 12 ≤ maxCoord j) (k : ℕ) (hk : k ≤ 6) :
    ‖iterDiff (latticeStep N i) k b (dualMomentum j)‖ ≤
      derivConstant B * (2 * Real.pi / N) * maxCoord j / (maxCoord j : ℝ) ^ k := by
  have hm' : (12 : ℝ) ≤ maxCoord j := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < maxCoord j := by linarith
  have hS : 0 ≤ ∑ k ∈ Finset.range 7, |B k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  cases k with
  | zero =>
    have hj : dualMomentum j ≠ 0 := by
      obtain ⟨k₀, hk₀⟩ := exists_abs_dualMomentum_eq j
      intro h0
      have e : dualMomentum j k₀ = 0 := by
        rw [h0]
        rfl
      rw [e, abs_zero] at hk₀
      have : 0 < 2 * Real.pi / N * maxCoord j := by positivity
      linarith
    simpa [iterDiff] using norm_symbol_le hb j hj
  | succ n =>
    set h := 2 * Real.pi / N with hh
    have hhpos : 0 < h := by positivity
    have h1 := norm_iterDiff_le (latticeStep N i) (n + 1) b (dualMomentum j)
      (|B (n + 1)| * (((h * maxCoord j) / 2) ^ n)⁻¹) (fun t ht => by
        refine iteratedFDeriv_bound_along_step hb H hN j hm ⟨ht.1, ht.2.trans ?_⟩ n
        exact_mod_cast hk)
    rw [norm_latticeStep, ← hh] at h1
    refine h1.trans ?_
    have aux : ∀ x m c : ℝ, 0 < x → 0 < m →
        x ^ (n + 1) * (c * (((x * m) / 2) ^ n)⁻¹) = c * 2 ^ n * x * m / m ^ (n + 1) := by
      intro x m c hx hm
      rw [div_pow, mul_pow]
      field_simp
      ring
    have e := aux h (maxCoord j) |B (n + 1)| hhpos hmpos
    rw [e]
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 := abs_le_sum_range_seven B (k := n + 1) hk
    have h4 : |B (n + 1)| * 2 ^ n ≤ derivConstant B := by
      rw [derivConstant]
      have : |B (n + 1)| * 2 ^ n ≤ (∑ k ∈ Finset.range 7, |B k|) * 2 ^ 5 :=
        mul_le_mul h3 h2 (by positivity) hS
      linarith
    have h5 : 0 ≤ h * maxCoord j / (maxCoord j : ℝ) ^ (n + 1) := by positivity
    calc _ = |B (n + 1)| * 2 ^ n * (h * maxCoord j / (maxCoord j : ℝ) ^ (n + 1)) := by ring
      _ ≤ derivConstant B * (h * maxCoord j / (maxCoord j : ℝ) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_right h4 h5
      _ = _ := by ring
end Bounds
section Sums
variable {N : ℕ} [NeZero N] {B : ℕ → ℝ} {b : (Fin 4 → ℝ) → ℂ} {z : Fin 4 → ℝ} {i : Fin 4}
def partsTerm (N : ℕ) [NeZero N] (b : (Fin 4 → ℝ) → ℂ) (z : Fin 4 → ℝ) (i : Fin 4) (k : ℕ)
    (j : TorusSite N) : ℂ :=
  planeWave z (dualMomentum j) * iterDiff (latticeStep N i) k b (dualMomentum j)
def shiftAlong (N : ℕ) [NeZero N] (i : Fin 4) : Equiv.Perm (TorusSite N) :=
  Equiv.addRight (Pi.single i (1 : ZMod N))
theorem sum_partsTerm_succ (F : Finset (TorusSite N)) (hN : 13 ≤ N)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (k : ℕ) (hk : k ≤ 5) :
    planeWave z (latticeStep N i) * ∑ j ∈ F, partsTerm N b z i (k + 1) j =
      ∑ j ∈ F, partsTerm N b z i k (shiftAlong N i j) -
        planeWave z (latticeStep N i) * ∑ j ∈ F, partsTerm N b z i k j := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := planeWave_mul_iterDiff_shift b z i hN H k hk j
  have e : partsTerm N b z i k (shiftAlong N i j) = planeWave z (dualMomentum (j + Pi.single i 1)) *
      iterDiff (latticeStep N i) k b (dualMomentum (j + Pi.single i 1)) := rfl
  rw [e, ← h]
  simp only [partsTerm]
  rw [iterDiff_succ]
  ring
theorem norm_sum_perm_sub_le {G : Type*} [DecidableEq G] (F P : Finset G) (T : Equiv.Perm G)
    (f : G → ℂ) (h1 : ∀ j, T.symm j ∈ F → j ∉ F → j ∈ P)
    (h2 : ∀ j, j ∈ F → T.symm j ∉ F → j ∈ P) :
    ‖∑ j ∈ F, f (T j) - ∑ j ∈ F, f j‖ ≤ ∑ j ∈ P, ‖f j‖ := by
  set M := F.map T.toEmbedding with hM
  have hmem : ∀ j, j ∈ M ↔ T.symm j ∈ F := fun j => by
    rw [hM, Finset.mem_map_equiv]
  have e1 : ∑ j ∈ F, f (T j) = ∑ j ∈ M, f j := by
    rw [hM, Finset.sum_map]
    rfl
  rw [e1, ← Finset.sum_sdiff_sub_sum_sdiff]
  have hdis : Disjoint (M \ F) (F \ M) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    exact (Finset.mem_sdiff.1 hj').2 (Finset.mem_sdiff.1 hj).1
  have hsub : (M \ F) ∪ (F \ M) ⊆ P := by
    intro j hj
    rcases Finset.mem_union.1 hj with hj | hj
    · obtain ⟨a, c⟩ := Finset.mem_sdiff.1 hj
      exact h1 j ((hmem j).1 a) c
    · obtain ⟨a, c⟩ := Finset.mem_sdiff.1 hj
      exact h2 j a fun d => c ((hmem j).2 d)
  calc _ ≤ ‖∑ j ∈ M \ F, f j‖ + ‖∑ j ∈ F \ M, f j‖ := norm_sub_le _ _
    _ ≤ ∑ j ∈ M \ F, ‖f j‖ + ∑ j ∈ F \ M, ‖f j‖ :=
        add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ = ∑ j ∈ (M \ F) ∪ (F \ M), ‖f j‖ := (Finset.sum_union hdis).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _
theorem norm_sum_partsTerm_le_once (F P : Finset (TorusSite N)) (hN : 13 ≤ N)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (h1 : ∀ j, (shiftAlong N i).symm j ∈ F → j ∉ F → j ∈ P)
    (h2 : ∀ j, j ∈ F → (shiftAlong N i).symm j ∉ F → j ∈ P)
    {W : ℝ} (hW : W * ‖1 - planeWave z (latticeStep N i)‖ = 1) (hW0 : 0 ≤ W) (k : ℕ) (hk : k ≤ 5) :
    ‖∑ j ∈ F, partsTerm N b z i k j‖ ≤
      W * (‖∑ j ∈ F, partsTerm N b z i (k + 1) j‖ + ∑ j ∈ P, ‖partsTerm N b z i k j‖) := by
  set A := ∑ j ∈ F, partsTerm N b z i k j with hA
  set A' := ∑ j ∈ F, partsTerm N b z i (k + 1) j with hA'
  set X := ∑ j ∈ F, partsTerm N b z i k (shiftAlong N i j) with hX
  set ω := planeWave z (latticeStep N i) with hω
  have e := sum_partsTerm_succ (z := z) (b := b) (i := i) F hN H k hk
  rw [← hA, ← hA', ← hX, ← hω] at e
  have e2 : (1 - ω) * A = ω * A' - (X - A) := by
    rw [e]
    ring
  have n1 : ‖1 - ω‖ * ‖A‖ ≤ ‖A'‖ + ∑ j ∈ P, ‖partsTerm N b z i k j‖ := by
    rw [← norm_mul, e2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, hω, norm_planeWave, one_mul]
    exact add_le_add le_rfl (norm_sum_perm_sub_le F P (shiftAlong N i) _ h1 h2)
  calc ‖A‖ = W * (‖1 - ω‖ * ‖A‖) := by
        rw [← mul_assoc, hW, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left n1 hW0
theorem norm_sum_partsTerm_le_iter (F P : Finset (TorusSite N)) (hN : 13 ≤ N)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (h1 : ∀ j, (shiftAlong N i).symm j ∈ F → j ∉ F → j ∈ P)
    (h2 : ∀ j, j ∈ F → (shiftAlong N i).symm j ∉ F → j ∈ P)
    {W : ℝ} (hW : W * ‖1 - planeWave z (latticeStep N i)‖ = 1) (hW0 : 0 ≤ W) (n : ℕ) (hn : n ≤ 6) :
    ‖∑ j ∈ F, partsTerm N b z i 0 j‖ ≤
      ∑ k ∈ Finset.range n, W ^ (k + 1) * ∑ j ∈ P, ‖partsTerm N b z i k j‖ +
        W ^ n * ‖∑ j ∈ F, partsTerm N b z i n j‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := norm_sum_partsTerm_le_once F P hN H h1 h2 hW hW0 n (by omega)
    have hp : 0 ≤ W ^ n := pow_nonneg hW0 n
    refine (ih (by omega)).trans ?_
    rw [Finset.sum_range_succ]
    have := mul_le_mul_of_nonneg_left h hp
    calc _ ≤ ∑ k ∈ Finset.range n, W ^ (k + 1) * ∑ j ∈ P, ‖partsTerm N b z i k j‖ +
          W ^ n * (W * (‖∑ j ∈ F, partsTerm N b z i (n + 1) j‖ +
            ∑ j ∈ P, ‖partsTerm N b z i n j‖)) := by
          gcongr
      _ = _ := by ring
def boxFace (N : ℕ) [NeZero N] (L : ℕ) (i : Fin 4) (a : ZMod N) : Finset (TorusSite N) :=
  Fintype.piFinset fun k => if k = i then {a} else centredInterval N L
theorem card_boxFace_le (L : ℕ) (i : Fin 4) (a : ZMod N) :
    (boxFace N L i a).card ≤ (2 * L + 1) ^ 3 := by
  rw [boxFace, Fintype.card_piFinset]
  have e : ∀ k : Fin 4, (if k = i then ({a} : Finset (ZMod N)) else centredInterval N L).card =
      if k = i then 1 else (centredInterval N L).card := fun k => by
    split_ifs <;> simp
  simp only [e]
  have h3 : ∏ k : Fin 4, (if k = i then 1 else (centredInterval N L).card) =
      (centredInterval N L).card ^ 3 := by
    fin_cases i <;> simp [Fin.prod_univ_four] <;> ring
  rw [h3]
  exact Nat.pow_le_pow_left (card_centredInterval_le L) 3
theorem mem_centredInterval {L : ℕ} {a : ZMod N} :
    a ∈ centredInterval N L ↔ a.valMinAbs.natAbs ≤ L := by
  simp [centredInterval]
theorem valMinAbs_intCast_of_bounds {n : ℤ} (h1 : -(N : ℤ) < n * 2) (h2 : n * 2 ≤ N) :
    ((n : ZMod N)).valMinAbs = n := by
  rw [ZMod.valMinAbs_spec]
  exact ⟨rfl, h1, h2⟩
theorem intCast_mem_centredInterval {L : ℕ} (hL : 2 * (L + 1) ≤ N) {n : ℤ} (h1 : -(L : ℤ) ≤ n)
    (h2 : n ≤ L) : ((n : ZMod N)) ∈ centredInterval N L := by
  rw [mem_centredInterval, valMinAbs_intCast_of_bounds (by omega) (by omega)]
  omega
theorem mem_centredBox_iff {L : ℕ} {j : TorusSite N} :
    j ∈ centredBox N L ↔ ∀ k, j k ∈ centredInterval N L := by
  simp [centredBox, Fintype.mem_piFinset]
theorem shiftAlong_symm_apply (j : TorusSite N) (k : Fin 4) :
    (shiftAlong N i).symm j k = j k - (Pi.single i (1 : ZMod N) : TorusSite N) k := by
  simp [shiftAlong, sub_eq_add_neg]
theorem mem_boxFace_lower {L : ℕ} (hL : 2 * (L + 1) ≤ N) {j : TorusSite N} (h1 : j ∈ centredBox N L)
    (h2 : (shiftAlong N i).symm j ∉ centredBox N L) :
    j ∈ boxFace N L i (((-(L : ℤ) : ℤ)) : ZMod N) := by
  rw [mem_centredBox_iff] at h1
  rw [boxFace, Fintype.mem_piFinset]
  intro k
  by_cases hk : k = i
  · subst hk
    simp only [if_true, Finset.mem_singleton]
    by_contra hne
    apply h2
    rw [mem_centredBox_iff]
    intro l
    rw [shiftAlong_symm_apply]
    by_cases hl : l = k
    · subst hl
      have hc := mem_centredInterval.1 (h1 l)
      have hj : j l = (((j l).valMinAbs : ℤ) : ZMod N) := (ZMod.coe_valMinAbs _).symm
      have hc2 : (j l).valMinAbs ≠ -(L : ℤ) := fun h => hne (by rw [hj, h])
      have e : j l - (Pi.single l (1 : ZMod N) : TorusSite N) l =
          (((j l).valMinAbs - 1 : ℤ) : ZMod N) := by
        push_cast
        simp
      rw [e]
      exact intCast_mem_centredInterval hL (by omega) (by omega)
    · simpa [hl] using h1 l
  · simpa [hk] using h1 k
theorem mem_boxFace_upper {L : ℕ} (hL : 2 * (L + 1) ≤ N) {j : TorusSite N} (h1 : j ∉ centredBox N L)
    (h2 : (shiftAlong N i).symm j ∈ centredBox N L) :
    j ∈ boxFace N L i (((L + 1 : ℤ)) : ZMod N) := by
  rw [mem_centredBox_iff] at h2
  have hother : ∀ k, k ≠ i → j k ∈ centredInterval N L := fun k hk => by
    have := h2 k
    rw [shiftAlong_symm_apply] at this
    simpa [hk] using this
  rw [boxFace, Fintype.mem_piFinset]
  intro k
  by_cases hk : k = i
  · subst hk
    simp only [if_true, Finset.mem_singleton]
    by_contra hne
    apply h1
    rw [mem_centredBox_iff]
    intro l
    by_cases hl : l = k
    · subst hl
      have h3 := h2 l
      rw [shiftAlong_symm_apply] at h3
      simp only [Pi.single_eq_same] at h3
      have hc := mem_centredInterval.1 h3
      have e : j l = (((j l - 1).valMinAbs + 1 : ℤ) : ZMod N) := by
        simp
      have hc2 : (j l - 1).valMinAbs ≠ (L : ℤ) := fun h => hne (by
        rw [e, h])
      rw [e]
      exact intCast_mem_centredInterval hL (by omega) (by omega)
    · exact hother l hl
  · simpa [hk] using hother k hk
theorem maxCoord_of_mem_boxFace {L : ℕ} {a : ZMod N} {j : TorusSite N} (hj : j ∈ boxFace N L i a)
    (v : ℕ) (hv : a.valMinAbs.natAbs = v) (hLv : L ≤ v) : maxCoord j = v := by
  rw [boxFace, Fintype.mem_piFinset] at hj
  have hi : j i = a := by simpa using hj i
  apply le_antisymm
  · refine Finset.sup_le fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      rw [hi, hv]
    · have := hj k
      simp only [hk, if_false] at this
      exact (mem_centredInterval.1 this).trans hLv
  · have : (j i).valMinAbs.natAbs ≤ maxCoord j :=
      Finset.le_sup (f := fun k => (j k).valMinAbs.natAbs) (Finset.mem_univ i)
    rwa [hi, hv] at this
def boxBoundary (N : ℕ) [NeZero N] (L : ℕ) (i : Fin 4) : Finset (TorusSite N) :=
  boxFace N L i (((-(L : ℤ) : ℤ)) : ZMod N) ∪ boxFace N L i (((L + 1 : ℤ)) : ZMod N)
theorem card_boxBoundary_le (L : ℕ) (i : Fin 4) :
    (boxBoundary N L i).card ≤ 2 * (2 * L + 1) ^ 3 := by
  calc _ ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ (2 * L + 1) ^ 3 + (2 * L + 1) ^ 3 :=
        add_le_add (card_boxFace_le _ _ _) (card_boxFace_le _ _ _)
    _ = _ := by ring
theorem maxCoord_of_mem_boxBoundary {L : ℕ} (hL : 2 * (L + 1) ≤ N) {j : TorusSite N}
    (hj : j ∈ boxBoundary N L i) : L ≤ maxCoord j ∧ maxCoord j ≤ L + 1 := by
  rcases Finset.mem_union.1 hj with h | h
  · have := maxCoord_of_mem_boxFace h L
      (by rw [valMinAbs_intCast_of_bounds (by omega) (by omega)]; omega) le_rfl
    omega
  · have := maxCoord_of_mem_boxFace h (L + 1)
      (by rw [valMinAbs_intCast_of_bounds (by omega) (by omega)]; omega) (by omega)
    omega
end Sums
section Total
variable {N : ℕ} [NeZero N] {B : ℕ → ℝ} {b : (Fin 4 → ℝ) → ℂ} {z : Fin 4 → ℝ} {i : Fin 4}
theorem sum_norm_partsTerm_boundary_le (hb : IsSymbolOfOrder B 1 b)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (hN : 24 ≤ N) {L : ℕ} (hL12 : 12 ≤ L) (hL : 2 * (L + 1) ≤ N) (k : ℕ) (hk : k ≤ 6) :
    ∑ j ∈ boxBoundary N L i, ‖partsTerm N b z i k j‖ ≤
      108 * (L : ℝ) ^ 4 * (derivConstant B * (2 * Real.pi / N)) / (L : ℝ) ^ k := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set c := derivConstant B * (2 * Real.pi / N) with hc
  have hc0 : 0 ≤ c := mul_nonneg (derivConstant_nonneg B) (by positivity)
  have hone : ∀ j ∈ boxBoundary N L i, ‖partsTerm N b z i k j‖ ≤ c * (2 * L) / (L : ℝ) ^ k := by
    intro j hj
    obtain ⟨s1, s2⟩ := maxCoord_of_mem_boxBoundary hL hj
    have hd := norm_iterDiff_far_le (i := i) hb H hN j (by omega) k hk
    have hm1 : (L : ℝ) ≤ maxCoord j := by exact_mod_cast s1
    have hm2 : (maxCoord j : ℝ) ≤ 2 * L := by
      have : maxCoord j ≤ 2 * L := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < maxCoord j := by linarith
    rw [← hc] at hd
    rw [partsTerm, norm_mul, norm_planeWave, one_mul]
    refine hd.trans ?_
    rw [mul_div_assoc c, mul_div_assoc c]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    cases k with
    | zero => simpa using hm2
    | succ n =>
      rw [pow_succ, pow_succ]
      have e1 : (maxCoord j : ℝ) / ((maxCoord j : ℝ) ^ n * maxCoord j) = ((maxCoord j : ℝ) ^ n)⁻¹ := by
        field_simp
      have e2 : 2 * (L : ℝ) / ((L : ℝ) ^ n * L) = 2 * ((L : ℝ) ^ n)⁻¹ := by
        field_simp
      rw [e1, e2]
      have h3 : ((maxCoord j : ℝ) ^ n)⁻¹ ≤ ((L : ℝ) ^ n)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hLpos.le hm1 n)
      have h4 : 0 ≤ ((L : ℝ) ^ n)⁻¹ := by positivity
      linarith
  have hcard : ((boxBoundary N L i).card : ℝ) ≤ 54 * (L : ℝ) ^ 3 := by
    have h1 := card_boxBoundary_le (N := N) L i
    have h2 : 2 * L + 1 ≤ 3 * L := by omega
    have h3 : (boxBoundary N L i).card ≤ 2 * (3 * L) ^ 3 :=
      h1.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h2 3))
    have h4 : ((boxBoundary N L i).card : ℝ) ≤ ((2 * (3 * L) ^ 3 : ℕ) : ℝ) := by exact_mod_cast h3
    refine h4.trans (le_of_eq ?_)
    push_cast
    ring
  calc _ ≤ ∑ _j ∈ boxBoundary N L i, c * (2 * L) / (L : ℝ) ^ k := Finset.sum_le_sum hone
    _ = ((boxBoundary N L i).card : ℝ) * (c * (2 * L) / (L : ℝ) ^ k) := by simp
    _ ≤ (54 * (L : ℝ) ^ 3) * (c * (2 * L) / (L : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring
theorem norm_sum_outside_box_le (hb : IsSymbolOfOrder B 1 b)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (hN : 24 ≤ N) {L : ℕ} (hL12 : 12 ≤ L) (hL : 2 * (L + 1) ≤ N)
    {W : ℝ} (hW : W * ‖1 - planeWave z (latticeStep N i)‖ = 1) (hW0 : 0 ≤ W) (hWL : W ≤ L) :
    ‖∑ j ∈ (centredBox N L)ᶜ, partsTerm N b z i 0 j‖ ≤
      648 * W * (L : ℝ) ^ 4 * (derivConstant B * (2 * Real.pi / N)) +
        W ^ 6 * (derivConstant B * (2 * Real.pi / N) * (1250 / L)) := by
  set c := derivConstant B * (2 * Real.pi / N) with hc
  have hc0 : 0 ≤ c := mul_nonneg (derivConstant_nonneg B) (by positivity)
  have h1 : ∀ j, (shiftAlong N i).symm j ∈ (centredBox N L)ᶜ → j ∉ (centredBox N L)ᶜ →
      j ∈ boxBoundary N L i := by
    intro j ha hb'
    rw [Finset.mem_compl] at ha hb'
    exact Finset.mem_union_left _ (mem_boxFace_lower hL (not_not.1 hb') ha)
  have h2 : ∀ j, j ∈ (centredBox N L)ᶜ → (shiftAlong N i).symm j ∉ (centredBox N L)ᶜ →
      j ∈ boxBoundary N L i := by
    intro j ha hb'
    rw [Finset.mem_compl] at ha hb'
    exact Finset.mem_union_right _ (mem_boxFace_upper hL ha (not_not.1 hb'))
  have hm := norm_sum_partsTerm_le_iter (z := z) (b := b) (i := i) ((centredBox N L)ᶜ)
    (boxBoundary N L i) (by omega) H h1 h2 hW hW0 6 le_rfl
  refine hm.trans (add_le_add ?_ ?_)
  · have hk : ∀ k ∈ Finset.range 6, W ^ (k + 1) * ∑ j ∈ boxBoundary N L i, ‖partsTerm N b z i k j‖ ≤
        108 * W * (L : ℝ) ^ 4 * c := by
      intro k hk
      have hk6 : k < 6 := Finset.mem_range.1 hk
      have hr := sum_norm_partsTerm_boundary_le (z := z) (i := i) hb H hN hL12 hL k (by omega)
      rw [← hc] at hr
      have hWk : W ^ k ≤ (L : ℝ) ^ k := pow_le_pow_left₀ hW0 hWL k
      have hq : W ^ k / (L : ℝ) ^ k ≤ 1 := (div_le_one (by positivity)).2 hWk
      calc _ ≤ W ^ (k + 1) * (108 * (L : ℝ) ^ 4 * c / (L : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left hr (by positivity)
        _ = (W ^ k / (L : ℝ) ^ k) * (108 * W * (L : ℝ) ^ 4 * c) := by
            rw [pow_succ]
            ring
        _ ≤ 1 * (108 * W * (L : ℝ) ^ 4 * c) := mul_le_mul_of_nonneg_right hq (by positivity)
        _ = _ := one_mul _
    calc _ ≤ ∑ _k ∈ Finset.range 6, 108 * W * (L : ℝ) ^ 4 * c := Finset.sum_le_sum hk
      _ = _ := by
          simp
          ring
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hfar : ∑ j ∈ (centredBox N L)ᶜ, ‖partsTerm N b z i 6 j‖ ≤ c * (1250 / L) := by
      have e : (centredBox N L)ᶜ = Finset.univ.filter (fun j : TorusSite N => L < maxCoord j) := by
        ext j
        simp [mem_centredBox]
      rw [e]
      calc _ ≤ ∑ j ∈ Finset.univ.filter (fun j : TorusSite N => L < maxCoord j),
            c * ((maxCoord j : ℝ) ^ 5)⁻¹ := by
            refine Finset.sum_le_sum fun j hj => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            have hd := norm_iterDiff_far_le (i := i) hb H hN j (by omega) 6 le_rfl
            have hmpos : (0 : ℝ) < maxCoord j := by
              have : 0 < maxCoord j := by omega
              exact_mod_cast this
            rw [partsTerm, norm_mul, norm_planeWave, one_mul]
            refine hd.trans (le_of_eq ?_)
            rw [← hc]
            field_simp
        _ = c * ∑ j ∈ Finset.univ.filter (fun j : TorusSite N => L < maxCoord j),
            ((maxCoord j : ℝ) ^ 5)⁻¹ := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_pow_five_far (by omega)) hc0
    exact (norm_sum_le _ _).trans hfar
theorem dualMomentum_ne_zero {j : TorusSite N} (hj : j ≠ 0) : dualMomentum j ≠ 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hj
  intro h0
  have e := congrFun h0 k
  rw [dualMomentum_apply] at e
  have h1 : ((j k).valMinAbs : ℝ) = 0 := by
    rcases mul_eq_zero.1 e with h | h
    · exact absurd h (by positivity)
    · exact h
  have h2 : (j k).valMinAbs = 0 := by exact_mod_cast h1
  exact hk ((ZMod.valMinAbs_eq_zero _).1 h2)
theorem norm_sum_nonzero_le (hb : IsSymbolOfOrder B 1 b)
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (hN : 24 ≤ N) {L : ℕ} (hL12 : 12 ≤ L) (hL : 2 * (L + 1) ≤ N)
    {W : ℝ} (hW : W * ‖1 - planeWave z (latticeStep N i)‖ = 1) (hW0 : 0 ≤ W) (hWL : W ≤ L) :
    ‖∑ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0,
        b (dualMomentum j) * planeWave z (dualMomentum j)‖ ≤
      81 * (L : ℝ) ^ 5 * (derivConstant B * (2 * Real.pi / N)) +
      (648 * W * (L : ℝ) ^ 4 * (derivConstant B * (2 * Real.pi / N)) +
        W ^ 6 * (derivConstant B * (2 * Real.pi / N) * (1250 / L))) := by
  set c := derivConstant B * (2 * Real.pi / N) with hc
  have hc0 : 0 ≤ c := mul_nonneg (derivConstant_nonneg B) (by positivity)
  have h0box : (0 : TorusSite N) ∈ centredBox N L := by
    rw [mem_centredBox_iff]
    intro k
    simp [mem_centredInterval]
  have hsplit : (Finset.univ : Finset (TorusSite N)).erase 0 =
      (centredBox N L).erase 0 ∪ (centredBox N L)ᶜ := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_compl]
    constructor
    · intro h
      by_cases hj : j ∈ centredBox N L
      · exact Or.inl ⟨h, hj⟩
      · exact Or.inr hj
    · rintro (h | h)
      · exact h.1
      · rintro rfl
        exact h h0box
  have hdis : Disjoint ((centredBox N L).erase 0) (centredBox N L)ᶜ := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    exact (Finset.mem_compl.1 h2) (Finset.mem_of_mem_erase h1)
  rw [hsplit, Finset.sum_union hdis]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hone : ∀ j ∈ (centredBox N L).erase 0,
        ‖b (dualMomentum j) * planeWave z (dualMomentum j)‖ ≤ c * L := by
      intro j hj
      have h1 := Finset.mem_erase.1 hj
      have h2 := norm_symbol_le hb j (dualMomentum_ne_zero h1.1)
      have h3 : (maxCoord j : ℝ) ≤ L := by exact_mod_cast mem_centredBox.1 h1.2
      rw [norm_mul, norm_planeWave, mul_one]
      exact h2.trans (mul_le_mul_of_nonneg_left h3 hc0)
    have hcard : (((centredBox N L).erase 0).card : ℝ) ≤ 81 * (L : ℝ) ^ 4 := by
      have h1 : ((centredBox N L).erase 0).card ≤ (3 * L) ^ 4 :=
        (Finset.card_erase_le).trans ((card_centredBox_le L).trans
          (Nat.pow_le_pow_left (by omega) 4))
      have h2 : (((centredBox N L).erase 0).card : ℝ) ≤ (((3 * L) ^ 4 : ℕ) : ℝ) := by
        exact_mod_cast h1
      refine h2.trans (le_of_eq ?_)
      push_cast
      ring
    calc _ ≤ ∑ j ∈ (centredBox N L).erase 0, ‖b (dualMomentum j) * planeWave z (dualMomentum j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ (centredBox N L).erase 0, c * L := Finset.sum_le_sum hone
      _ = (((centredBox N L).erase 0).card : ℝ) * (c * L) := by simp
      _ ≤ (81 * (L : ℝ) ^ 4) * (c * L) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  · have := norm_sum_outside_box_le (z := z) (i := i) hb H hN hL12 hL hW hW0 hWL
    rw [← hc] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [partsTerm, iterDiff]
    ring
theorem le_norm_one_sub_planeWave (hN : 0 < N) {ζ : ℝ} (h1 : ζ ≤ 2 * |z i|) (h2 : |z i| ≤ (N : ℝ) / 8) :
    2 * ζ / N ≤ ‖1 - planeWave z (latticeStep N i)‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  set θ := 2 * Real.pi / N * z i with hθ
  rw [norm_sub_rev, planeWave_latticeStep, Complex.norm_exp_I_mul_ofReal_sub_one, ← hθ,
    Real.norm_eq_abs, abs_mul, abs_two]
  have hab : |θ| = 2 * Real.pi / N * |z i| := by
    rw [hθ, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / N)]
  have hle : |θ| ≤ Real.pi := by
    rw [hab]
    calc _ ≤ 2 * Real.pi / N * ((N : ℝ) / 8) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.pi / 4 := by
          field_simp
          ring
      _ ≤ _ := by linarith
  have hsin : 2 / Real.pi * (|θ| / 2) ≤ |Real.sin (θ / 2)| := by
    have h3 := Real.mul_le_sin (x := |θ| / 2) (by positivity) (by linarith)
    refine h3.trans ?_
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h]
      exact le_abs_self _
    · rw [abs_of_nonpos h, neg_div, Real.sin_neg]
      exact neg_le_abs _
  have e : 2 * (2 / Real.pi * (|θ| / 2)) = 4 * |z i| / N := by
    rw [hab]
    field_simp
    ring
  have h4 : 2 * ζ / N ≤ 4 * |z i| / N := by
    refine div_le_div_of_nonneg_right ?_ hNpos.le
    linarith
  calc _ ≤ 4 * |z i| / N := h4
    _ = 2 * (2 / Real.pi * (|θ| / 2)) := e.symm
    _ ≤ _ := by linarith
theorem exists_coord_sqNorm_le (z : Fin 4 → ℝ) : ∃ i, sqNorm z ≤ 4 * z i ^ 2 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4)) (fun k => z k ^ 2)
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc sqNorm z ≤ ∑ _k : Fin 4, z i ^ 2 := Finset.sum_le_sum hi
    _ = _ := by simp
theorem momentum_sum_arithmetic {x L W h Nr c ζ : ℝ} (hNr : 0 < Nr) (hζ : 0 < ζ) (hx : x = Nr / ζ)
    (hh : h = 2 * Real.pi / Nr) (hc : 0 ≤ c) (hW0 : 0 ≤ W) (hW : W ≤ x / 2) (hL1 : 2 * x ≤ L)
    (hL2 : L ≤ 3 * x) :
    (Nr ^ 4)⁻¹ * (81 * L ^ 5 * (c * h) + (648 * W * L ^ 4 * (c * h) + W ^ 6 * (c * h * (1250 / L)))) ≤
      100000 * Real.pi * c * (ζ ^ 5)⁻¹ := by
  have hxpos : 0 < x := by rw [hx]; positivity
  have hLpos : 0 < L := by linarith
  have hhpos : 0 < h := by rw [hh]; positivity
  have hch : 0 ≤ c * h := by positivity
  have t1 : 81 * L ^ 5 * (c * h) ≤ 81 * (3 * x) ^ 5 * (c * h) := by
    have := pow_le_pow_left₀ hLpos.le hL2 5
    gcongr
  have t2 : 648 * W * L ^ 4 * (c * h) ≤ 648 * (x / 2) * (3 * x) ^ 4 * (c * h) := by
    have := pow_le_pow_left₀ hLpos.le hL2 4
    gcongr
  have t3 : W ^ 6 * (c * h * (1250 / L)) ≤ (x / 2) ^ 6 * (c * h * (1250 / (2 * x))) := by
    have h6 := pow_le_pow_left₀ hW0 hW 6
    have hd : 1250 / L ≤ 1250 / (2 * x) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hL1
    have : c * h * (1250 / L) ≤ c * h * (1250 / (2 * x)) := mul_le_mul_of_nonneg_left hd hch
    exact mul_le_mul h6 this (by positivity) (by positivity)
  have hsum : 81 * L ^ 5 * (c * h) + (648 * W * L ^ 4 * (c * h) + W ^ 6 * (c * h * (1250 / L))) ≤
      50000 * (c * h) * x ^ 5 := by
    have e : 81 * (3 * x) ^ 5 * (c * h) + (648 * (x / 2) * (3 * x) ^ 4 * (c * h) +
        (x / 2) ^ 6 * (c * h * (1250 / (2 * x)))) =
        (19683 + 26244 + 625 / 64) * (c * h) * x ^ 5 := by
      field_simp
      ring
    have hx5 : 0 ≤ (c * h) * x ^ 5 := by positivity
    nlinarith
  have hfin : (Nr ^ 4)⁻¹ * (50000 * (c * h) * x ^ 5) = 100000 * Real.pi * c * (ζ ^ 5)⁻¹ := by
    rw [hx, hh]
    field_simp
    ring
  calc _ ≤ (Nr ^ 4)⁻¹ * (50000 * (c * h) * x ^ 5) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := hfin
end Total
section Final
variable {N : ℕ} [NeZero N] {B : ℕ → ℝ} {b : (Fin 4 → ℝ) → ℂ} {z : Fin 4 → ℝ}
theorem nonzeroMomentumWave_eq (N : ℕ) [NeZero N] (b : (Fin 4 → ℝ) → ℂ) (z : Fin 4 → ℝ) :
    nonzeroMomentumWave N b z = ((N : ℂ) ^ 4)⁻¹ *
      ∑ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0,
        b (dualMomentum j) * planeWave z (dualMomentum j) := by
  simp only [nonzeroMomentumWave, planeWave]
theorem norm_inv_natCast_pow_four : ‖((N : ℂ) ^ 4)⁻¹‖ = ((N : ℝ) ^ 4)⁻¹ := by
  rw [norm_inv, norm_pow, Complex.norm_natCast]
theorem norm_nonzeroMomentumWave_le (hb : IsSymbolOfOrder B 1 b) :
    ‖nonzeroMomentumWave N b z‖ ≤ derivConstant B * Real.pi := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hpi := Real.pi_pos
  rw [nonzeroMomentumWave_eq, norm_mul, norm_inv_natCast_pow_four]
  have hone : ∀ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0,
      ‖b (dualMomentum j) * planeWave z (dualMomentum j)‖ ≤ derivConstant B * Real.pi := by
    intro j hj
    rw [norm_mul, norm_planeWave, mul_one]
    refine (norm_symbol_le hb j (dualMomentum_ne_zero (Finset.mem_erase.1 hj).1)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (maxCoord_mul_le_pi j) (derivConstant_nonneg B)
  have hcard : (((Finset.univ : Finset (TorusSite N)).erase 0).card : ℝ) ≤ (N : ℝ) ^ 4 := by
    have h1 : ((Finset.univ : Finset (TorusSite N)).erase 0).card ≤ N ^ 4 := by
      refine Finset.card_erase_le.trans (le_of_eq ?_)
      simp [ZMod.card]
    exact_mod_cast h1
  have hc0 : 0 ≤ derivConstant B * Real.pi := mul_nonneg (derivConstant_nonneg B) hpi.le
  calc _ ≤ ((N : ℝ) ^ 4)⁻¹ * (((N : ℝ) ^ 4) * (derivConstant B * Real.pi)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc _ ≤ ∑ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0,
              ‖b (dualMomentum j) * planeWave z (dualMomentum j)‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ (Finset.univ : Finset (TorusSite N)).erase 0, derivConstant B * Real.pi :=
              Finset.sum_le_sum hone
          _ = (((Finset.univ : Finset (TorusSite N)).erase 0).card : ℝ) *
              (derivConstant B * Real.pi) := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right hcard hc0
    _ = _ := by
        field_simp
theorem norm_nonzeroMomentumWave_le_of_large (hb : IsSymbolOfOrder B 1 b) {i : Fin 4}
    (H : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p)
    (hN : 24 ≤ N) {ζ : ℝ} (hζ : 24 ≤ ζ) (hζN : ζ ≤ (N : ℝ) / 8) (h1 : ζ ≤ 2 * |z i|)
    (h2 : |z i| ≤ (N : ℝ) / 8) :
    ‖nonzeroMomentumWave N b z‖ ≤ 100000 * Real.pi * derivConstant B * (ζ ^ 5)⁻¹ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hζ0 : 0 < ζ := by linarith
  set x := (N : ℝ) / ζ with hx
  have hx8 : 8 ≤ x := by
    rw [hx, le_div_iff₀ hζ0]
    linarith
  have hxN : x * 24 ≤ N := by
    have e : x * ζ = N := by
      rw [hx]
      field_simp
    nlinarith
  set L := ⌈2 * x⌉₊ with hLdef
  have hL1 : 2 * x ≤ L := Nat.le_ceil _
  have hL2 : (L : ℝ) ≤ 3 * x := by
    have : (L : ℝ) < 2 * x + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hL12 : 12 ≤ L := by
    have : (12 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hL : 2 * (L + 1) ≤ N := by
    have : (2 : ℝ) * (L + 1) ≤ N := by
      linarith
    exact_mod_cast this
  have hd := le_norm_one_sub_planeWave (NeZero.pos N) h1 h2
  set d := ‖1 - planeWave z (latticeStep N i)‖ with hdd
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hW : d⁻¹ * d = 1 := inv_mul_cancel₀ hd0.ne'
  have hW0 : 0 ≤ d⁻¹ := by positivity
  have hWx : d⁻¹ ≤ x / 2 := by
    have e : x / 2 = (2 * ζ / N)⁻¹ := by
      rw [hx]
      field_simp
    rw [e]
    exact inv_anti₀ (by positivity) hd
  have hWL : d⁻¹ ≤ L := by linarith
  have T := norm_sum_nonzero_le (z := z) (i := i) hb H hN hL12 hL hW hW0 hWL
  have A := momentum_sum_arithmetic (x := x) (L := L) (W := d⁻¹) (h := 2 * Real.pi / N) (Nr := N)
    (c := derivConstant B) (ζ := ζ) hNpos hζ0 hx rfl (derivConstant_nonneg B) hW0 hWx hL1 hL2
  rw [nonzeroMomentumWave_eq, norm_mul, norm_inv_natCast_pow_four]
  exact (mul_le_mul_of_nonneg_left T (by positivity)).trans A
end Final
end OrderOneMomentumSum
open OrderOneMomentumSum in
theorem orderOneMomentumSum_holds : orderOneMomentumSumStatement := by
  intro B
  refine ⟨8100000 * Real.pi * derivConstant B, 24, ?_⟩
  intro N _ b z hN hb H h1 h2
  have hN24 : 24 ≤ N := by exact_mod_cast hN
  have hc0 := derivConstant_nonneg B
  set ζ := Real.sqrt (sqNorm z) with hζdef
  have hsq : ζ ^ 2 = sqNorm z := Real.sq_sqrt (sqNorm_nonneg z)
  have hζ1 : 1 ≤ ζ := Real.one_le_sqrt.2 h1
  have hζ0 : 0 < ζ := by linarith
  have hζN : ζ ≤ (N : ℝ) / 8 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, h2⟩
  have hrp : sqNorm z ^ (-(5 / 2 : ℝ)) = (ζ ^ 5)⁻¹ := by
    have := rpow_sq_eq_inv_pow hζ0 5
    rw [hsq] at this
    rw [← this]
    norm_num
  have hgoal : ‖nonzeroMomentumWave N b z‖ ≤ 8100000 * Real.pi * derivConstant B * (ζ ^ 5)⁻¹ := by
    by_cases hs : ζ < 24
    · refine (norm_nonzeroMomentumWave_le hb).trans ?_
      have h5 : ζ ^ 5 ≤ 8100000 := by
        have := pow_le_pow_left₀ hζ0.le hs.le 5
        norm_num at this
        linarith
      have h6 : (8100000 : ℝ)⁻¹ ≤ (ζ ^ 5)⁻¹ := inv_anti₀ (by positivity) h5
      calc derivConstant B * Real.pi =
            8100000 * Real.pi * derivConstant B * (8100000 : ℝ)⁻¹ := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h6 (by positivity)
    · obtain ⟨i, hi⟩ := exists_coord_sqNorm_le z
      have hi1 : ζ ≤ 2 * |z i| := by
        refine (sq_le_sq₀ hζ0.le (by positivity)).1 ?_
        rw [hsq, mul_pow, sq_abs]
        linarith
      have hi2 : |z i| ≤ (N : ℝ) / 8 := by
        refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 ?_
        rw [sq_abs]
        exact (sq_le_sqNorm z i).trans h2
      have H' : ∀ p : Fin 4 → ℝ, OffDualLattice p → b (p + fullPeriod i) * planeWave z (fullPeriod i) = b p := by
        intro p hp
        rw [planeWave_fullPeriod]
        exact H p i hp
      refine (norm_nonzeroMomentumWave_le_of_large hb H' hN24 (not_lt.1 hs) hζN hi1 hi2).trans ?_
      have h7 : (0 : ℝ) ≤ (ζ ^ 5)⁻¹ := by positivity
      have h8 : 100000 * Real.pi * derivConstant B ≤ 8100000 * Real.pi * derivConstant B := by
        have : 0 ≤ Real.pi * derivConstant B := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right h8 h7
  refine hgoal.trans ?_
  rw [hrp]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have : (0 : ℝ) ≤ (N : ℝ) ^ (-(4 : ℤ)) := by positivity
  linarith
end ResponseInTheExpansion
end YangMills.Construction
end
