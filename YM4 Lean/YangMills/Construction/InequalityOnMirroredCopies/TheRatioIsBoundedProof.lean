import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.PowerOfThePartitionFunction
import YangMills.Construction.InequalityOnMirroredCopies.BoundsOnWilsonsMass
import YangMills.Construction.InequalityOnMirroredCopies.CouplingAtTheLevelOfARadius
import YangMills.Construction.InequalityOnMirroredCopies.PartitionNumberIsWilsonsMass
import YangMills.Construction.LawInAState.DominationOnTheLeastTorusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori TorusLumps ClusterExpansionOfAStep WeightedResponses
private def partitionPowerBoundAt (ℓ : StepParameters) (C nS : ℝ) : Prop :=
  ∀ (β : ℝ) (t : ℕ), FreeEnergies.CouplingsAboveFloor ℓ β t →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'], IsBlockTorusSide ℓ n → IsBlockTorusSide ℓ n' → n ≤ n' →
      nS * flowCoupling ℓ β t ^ ((1 : ℝ) / 100) ≤ n →
        FreeEnergies.torusPartition ℓ β t n ^ ((n' : ℝ) ^ 4 / (n : ℝ) ^ 4) ≤
          Real.exp (C * (1 + Real.log (flowCoupling ℓ β t)) * (n' : ℝ) ^ 4) * FreeEnergies.torusPartition ℓ β t n'
private def wilsonPartitionBoundsAt (C : ℝ) : Prop :=
  ∀ β : ℝ, 1 ≤ β → ∀ (n : ℕ) [NeZero n],
    0 < wilsonPartition β n ∧ wilsonPartition β n ≤ 1 ∧
      -((C + 6 * Real.log β) * (n : ℝ) ^ 4) ≤ Real.log (wilsonPartition β n)
private theorem log_mul_pow_le_of_le_rpow {K A x m : ℝ} (hK : 0 ≤ K) (hx : 1 ≤ x) (hm0 : 0 ≤ m)
    (hm : m ≤ A * x ^ ((1 : ℝ) / 100)) :
    K * (1 + Real.log x) * m ^ 4 ≤ K * 101 * A ^ 4 * x ^ ((1 : ℝ) / 20) := by
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = x ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  rw [← hu] at hm
  have hu1 : 1 ≤ u := hu ▸ Real.one_le_rpow hx (by norm_num)
  have hlog : Real.log x ≤ 100 * u := by
    have h := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 100)
    rw [← hu] at h
    linarith
  have hx20 : x ^ ((1 : ℝ) / 20) = u ^ 5 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have h1 : 1 + Real.log x ≤ 101 * u := by linarith
  have h2 : m ^ 4 ≤ (A * u) ^ 4 := pow_le_pow_left₀ hm0 hm 4
  calc K * (1 + Real.log x) * m ^ 4 ≤ K * (101 * u) * (A * u) ^ 4 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) h2 (by positivity) (by positivity)
    _ = K * 101 * A ^ 4 * x ^ ((1 : ℝ) / 20) := by rw [hx20]; ring
private theorem rpow_twentieth_le_of_le {C x p : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (hp : 0 ≤ p) (h : x ≤ C * (1 + p)) :
    x ^ ((1 : ℝ) / 20) ≤ C ^ ((1 : ℝ) / 20) * (1 + p ^ ((1 : ℝ) / 20)) := by
  have h1 : ((1 : ℝ) + p) ^ ((1 : ℝ) / 20) ≤ 1 + p ^ ((1 : ℝ) / 20) := by
    have := Real.rpow_add_le_add_rpow (zero_le_one' ℝ) hp (by norm_num : (0 : ℝ) ≤ 1 / 20)
      (by norm_num : (1 : ℝ) / 20 ≤ 1)
    simpa using this
  calc x ^ ((1 : ℝ) / 20) ≤ (C * (1 + p)) ^ ((1 : ℝ) / 20) :=
        Real.rpow_le_rpow (by linarith) h (by norm_num)
    _ = C ^ ((1 : ℝ) / 20) * (1 + p) ^ ((1 : ℝ) / 20) := Real.mul_rpow hC (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hC _)
private theorem one_le_side_pow_add_logPos {L : ℝ} (hL : 3 ≤ L) (q : ℤ) :
    1 ≤ (L ^ q) ^ 4 + TorusBound.logPos (1 / L ^ q) ^ ((1 : ℝ) / 20) := by
  have hL1 : 1 < L := by linarith
  have hp0 : 0 ≤ TorusBound.logPos (1 / L ^ q) := le_max_right _ _
  rcases le_or_gt 0 q with hq | hq
  · have h1 : 1 ≤ L ^ q := one_le_zpow₀ hL1.le hq
    have h4 : 1 ≤ (L ^ q) ^ 4 := one_le_pow₀ h1
    have := Real.rpow_nonneg hp0 ((1 : ℝ) / 20)
    linarith
  · have hlog : 1 ≤ Real.log (1 / L ^ q) := by
      have e : 1 / L ^ q = L ^ (-q) := by rw [zpow_neg, one_div]
      rw [e]
      have h1 : L ≤ L ^ (-q) := by
        have := zpow_le_zpow_right₀ hL1.le (show (1 : ℤ) ≤ -q by omega)
        simpa using this
      have h2 : (1 : ℝ) ≤ Real.log L := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        have := Real.exp_one_lt_d9
        linarith
      exact h2.trans (Real.log_le_log (by linarith) h1)
    have h1 : 1 ≤ TorusBound.logPos (1 / L ^ q) := hlog.trans (le_max_left _ _)
    have h2 := Real.one_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 1 / 20)
    have h3 : 0 ≤ (L ^ q) ^ 4 := by
      have : 0 < L ^ q := zpow_pos (by linarith) _
      positivity
    linarith
private theorem mul_one_add_le_of_one_le {Q W l p : ℝ} (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hl : 0 ≤ l) (hp : 0 ≤ p)
    (h : 1 ≤ l + p) :
    Q * (1 + p) ≤ (W + 2 * Q) * l + (W + 2 * Q) * p := by
  nlinarith [mul_nonneg hQ hl, mul_nonneg hQ hp, mul_nonneg hW hl, mul_nonneg hW hp,
    mul_le_mul_of_nonneg_left h hQ]
private theorem rpow_div_rpow_le_exp {Z₂ Zb N E : ℝ} (h₂ : 0 < Z₂) (hb : 0 < Zb) (hN : 0 < N)
    (h : Z₂ ^ (N / 16) ≤ Real.exp (E * N) * Zb) : Z₂ ^ (1 / 16 : ℝ) / Zb ^ (1 / N) ≤ Real.exp E := by
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg h₂.le _) h (by positivity : 0 ≤ 1 / N)
  rw [← Real.rpow_mul h₂.le, Real.mul_rpow (Real.exp_pos _).le hb.le, ← Real.exp_mul] at h1
  have e1 : N / 16 * (1 / N) = 1 / 16 := by field_simp
  have e2 : E * N * (1 / N) = E := by field_simp
  rw [e1, e2] at h1
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hb _)]
  exact h1
private theorem cellCount_cubicCounts_cast (D : ChessboardSetup) (j : ℕ) :
    (cellCount (cubicCounts D j) : ℝ) = (2 * (D.L : ℝ) ^ j) ^ 4 := by apply _root_.YangMills.SharedProofs.p78545 <;> assumption
private theorem torusPartitionRatio_le_of_wilson (hZ : TorusPartitionIsWilsonPartition) {D : ChessboardSetup}
    (g : ReflectionGrid D) (hg : g.HasAdmissibleSide) (j m₂ mb : ℕ) [NeZero m₂] [NeZero mb]
    (h₂ : (m₂ : ℤ) = 2 * g.cellRatio)
    (hb : (mb : ℤ) = 2 * (D.L : ℤ) ^ j * g.cellRatio) (p₂ : 0 < wilsonPartition D.β m₂)
    (pb : 0 < wilsonPartition D.β mb)
    (E : ℝ) (h : wilsonPartition D.β m₂ ^ ((D.L : ℝ) ^ (4 * j)) ≤
      Real.exp (E * (2 * (D.L : ℝ) ^ j) ^ 4) * wilsonPartition D.β mb) :
    torusPartitionRatio g j ≤ Real.exp E := by
  have e₂ : torusPartition g (minimalCounts D) = wilsonPartition D.β m₂ :=
    hZ D g hg 0 m₂ (by simpa [cubicCounts] using h₂)
  have eb : torusPartition g (cubicCounts D j) = wilsonPartition D.β mb :=
    hZ D g hg j mb (by simpa [cubicCounts] using hb)
  have hL : (0 : ℝ) < D.L := by linarith [D.one_lt_factor]
  unfold torusPartitionRatio
  rw [e₂, eb, cellCount_cubicCounts_cast]
  refine rpow_div_rpow_le_exp p₂ pb (by positivity) ?_
  have e : (2 * (D.L : ℝ) ^ j) ^ 4 / 16 = (D.L : ℝ) ^ (4 * j) := by
    rw [mul_comm 4 j, pow_mul]
    ring
  rw [e]
  exact h
private theorem torusPartitionRatio_le_of_covered (hZ : TorusPartitionIsWilsonPartition) {ℓ : StepParameters}
    (hfit : ℓ.Admissible)
    {Cw C₁ nS c : ℝ} (hW : wilsonPartitionBoundsAt Cw) (hpow : partitionPowerBoundAt ℓ C₁ nS) (hnS : 1 ≤ nS)
    (hcn : nS ≤ c)
    (hcL : ((ℓ.side * ℓ.n₀ : ℕ) : ℝ) ≤ c) (D : ChessboardSetup) (hDL : D.L = ℓ.side) (hβ : 1 ≤ D.β) {s : ℕ}
    (hr : FreeEnergies.CouplingsAboveFloor ℓ D.β s) (g : ReflectionGrid D) (hg : g.HasAdmissibleSide) (j : ℕ)
    (hs : RadiusCoversScale ℓ D c g.cellSide s) :
    torusPartitionRatio g j ≤
      Real.exp (C₁ * (1 + Real.log (flowCoupling ℓ D.β s)) * (g.cellSide / levelMesh D s) ^ 4) := by
  have hLr : (1 : ℝ) < D.L := D.one_lt_factor
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have hLc : (D.L : ℝ) = (ℓ.side : ℝ) := by rw [hDL]
  have hLz : (D.L : ℤ) = (ℓ.side : ℤ) := by rw [hDL]
  have hx1 : 1 ≤ flowCoupling ℓ D.β s := hfit.y₁_ge.trans (hr s le_rfl)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = flowCoupling ℓ D.β s := ⟨_, rfl⟩
  rw [← hx] at hx1 ⊢
  have hrg : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  have hu1 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
  have hc0 : 0 ≤ c := by linarith
  have hcov : c * (clusterRange x : ℝ) ≤ g.cellSide / levelMesh D s := by
    rw [hx]
    exact hs
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = g.q + ((D.K : ℕ) : ℤ) - (s : ℤ) := ⟨_, rfl⟩
  have hm : g.cellSide / levelMesh D s = (D.L : ℝ) ^ e := by
    unfold ReflectionGrid.cellSide levelMesh
    rw [← zpow_sub₀ hL0, he]
    congr 1
    ring
  rw [hm] at hcov ⊢
  have hr1 : (1 : ℝ) ≤ clusterRange x := hu1.trans hrg
  have hcm : c ≤ (D.L : ℝ) ^ e :=
    le_trans (by simpa using mul_le_mul_of_nonneg_left hr1 hc0) hcov
  have hnat1 : (ℓ.side : ℝ) ≤ ((ℓ.side * ℓ.n₀ : ℕ) : ℝ) := by
    have : ℓ.side ≤ ℓ.side * ℓ.n₀ := Nat.le_mul_of_pos_right _ (by have := hfit.n₀_ge; omega)
    exact_mod_cast this
  have he1 : 1 ≤ e := by
    have h : (D.L : ℝ) ^ (1 : ℤ) ≤ (D.L : ℝ) ^ e := by
      rw [zpow_one, hLc]
      rw [hLc] at hcm
      linarith
    exact (zpow_le_zpow_iff_right₀ hLr).mp h
  obtain ⟨u, hu⟩ : ∃ u : ℕ, e = u := ⟨e.toNat, by omega⟩
  have hLu : (D.L : ℝ) ^ e = (D.L : ℝ) ^ u := by rw [hu, zpow_natCast]
  rw [hLu] at hcov hcm ⊢
  have : NeZero (2 * ℓ.side ^ u) := ⟨mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne _))⟩
  have : NeZero (2 * ℓ.side ^ (u + j)) := ⟨mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne _))⟩
  have hnR : ((2 * ℓ.side ^ u : ℕ) : ℝ) = 2 * (D.L : ℝ) ^ u := by
    push_cast
    rw [hLc]
  have hnR' : ((2 * ℓ.side ^ (u + j) : ℕ) : ℝ) = 2 * (D.L : ℝ) ^ u * (D.L : ℝ) ^ j := by
    push_cast
    rw [hLc, pow_add]
    ring
  have hbig : ℓ.side * ℓ.n₀ ≤ 2 * ℓ.side ^ u := by
    have h : ((ℓ.side * ℓ.n₀ : ℕ) : ℝ) ≤ ((2 * ℓ.side ^ u : ℕ) : ℝ) := by
      rw [hnR]
      linarith
    exact_mod_cast h
  have hnn : 2 * ℓ.side ^ u ≤ 2 * ℓ.side ^ (u + j) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne _)) (by omega))
  have hb : IsBlockTorusSide ℓ (2 * ℓ.side ^ u) :=
    ⟨Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2, hbig⟩
  have hb' : IsBlockTorusSide ℓ (2 * ℓ.side ^ (u + j)) :=
    ⟨Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2, hbig.trans hnn⟩
  have hns : nS * flowCoupling ℓ D.β s ^ ((1 : ℝ) / 100) ≤ ((2 * ℓ.side ^ u : ℕ) : ℝ) := by
    rw [← hx, hnR]
    have h1 : nS * x ^ ((1 : ℝ) / 100) ≤ c * (clusterRange x : ℝ) :=
      mul_le_mul hcn hrg (by linarith) hc0
    linarith
  have hp := hpow D.β s hr _ _ hb hb' hnn hns
  rw [← hx] at hp
  have e1 : ((2 * ℓ.side ^ (u + j) : ℕ) : ℝ) ^ 4 / ((2 * ℓ.side ^ u : ℕ) : ℝ) ^ 4 = (D.L : ℝ) ^ (4 * j) := by
    rw [hnR, hnR', mul_comm 4 j, pow_mul]
    field_simp
  have e2 : C₁ * (1 + Real.log x) * ((2 * ℓ.side ^ (u + j) : ℕ) : ℝ) ^ 4 =
      C₁ * (1 + Real.log x) * ((D.L : ℝ) ^ u) ^ 4 * (2 * (D.L : ℝ) ^ j) ^ 4 := by
    rw [hnR']
    ring
  rw [e1, e2] at hp
  have ht : (g.q + ((D.K : ℕ) : ℤ)).toNat = u + s := by omega
  refine torusPartitionRatio_le_of_wilson hZ g hg j (fineSide ℓ.side s (2 * ℓ.side ^ u))
    (fineSide ℓ.side s (2 * ℓ.side ^ (u + j)))
    ?_ ?_ (hW D.β hβ _).1 (hW D.β hβ _).1 _ hp
  · rw [fineSide_eq]
    unfold ReflectionGrid.cellRatio
    rw [ht, hLz]
    push_cast
    ring
  · rw [fineSide_eq]
    unfold ReflectionGrid.cellRatio
    rw [ht, hLz]
    push_cast
    ring
private theorem torusPartitionRatio_le_of_uncovered (hZ : TorusPartitionIsWilsonPartition) {Cw K : ℝ}
    (hW : wilsonPartitionBoundsAt Cw)
    (hK : |Cw| + 6 ≤ K) (D : ChessboardSetup) (hβ : 1 ≤ D.β) (g : ReflectionGrid D) (hg : g.HasAdmissibleSide)
    (j : ℕ) :
    torusPartitionRatio g j ≤ Real.exp (K * (1 + Real.log D.β) * (g.cellRatio : ℝ) ^ 4) := by
  have hD0 : D.L ≠ 0 := by
    have := D.isAdmissible.2
    omega
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = (g.q + ((D.K : ℕ) : ℤ)).toNat := ⟨_, rfl⟩
  have hrat : g.cellRatio = (D.L : ℤ) ^ t := by
    unfold ReflectionGrid.cellRatio
    rw [ht]
  have hratR : (g.cellRatio : ℝ) = (D.L : ℝ) ^ t := by
    rw [hrat]
    push_cast
    rfl
  have : NeZero (2 * D.L ^ t) := ⟨mul_ne_zero two_ne_zero (pow_ne_zero _ hD0)⟩
  have : NeZero (2 * D.L ^ j * D.L ^ t) :=
    ⟨mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ hD0)) (pow_ne_zero _ hD0)⟩
  have p₂ := (hW D.β hβ (2 * D.L ^ t)).1
  have hZ₂ := (hW D.β hβ (2 * D.L ^ t)).2.1
  have pb := (hW D.β hβ (2 * D.L ^ j * D.L ^ t)).1
  have hlow := (hW D.β hβ (2 * D.L ^ j * D.L ^ t)).2.2
  refine torusPartitionRatio_le_of_wilson hZ g hg j (2 * D.L ^ t) (2 * D.L ^ j * D.L ^ t) ?_ ?_ p₂ pb _ ?_
  · rw [hrat]
    push_cast
    rfl
  · rw [hrat]
    push_cast
    rfl
  · have h1 : wilsonPartition D.β (2 * D.L ^ t) ^ ((D.L : ℝ) ^ (4 * j)) ≤ 1 :=
      Real.rpow_le_one p₂.le hZ₂ (by positivity)
    refine h1.trans ?_
    have hexp := (Real.le_log_iff_exp_le pb).mp hlow
    have hlogβ : 0 ≤ Real.log D.β := Real.log_nonneg hβ
    have hmb : (((2 * D.L ^ j * D.L ^ t : ℕ) : ℝ)) ^ 4 = (2 * (D.L : ℝ) ^ j) ^ 4 * ((D.L : ℝ) ^ t) ^ 4 := by
      push_cast
      ring
    have hCK : Cw + 6 * Real.log D.β ≤ K * (1 + Real.log D.β) := by
      have h1 : Cw ≤ |Cw| := le_abs_self _
      have h2 : 0 ≤ |Cw| := abs_nonneg _
      nlinarith
    have hN0 : 0 ≤ (2 * (D.L : ℝ) ^ j) ^ 4 * ((D.L : ℝ) ^ t) ^ 4 := by positivity
    have hle : (Cw + 6 * Real.log D.β) * (((2 * D.L ^ j * D.L ^ t : ℕ) : ℝ)) ^ 4 ≤
        K * (1 + Real.log D.β) * (g.cellRatio : ℝ) ^ 4 * (2 * (D.L : ℝ) ^ j) ^ 4 := by
      rw [hmb, hratR]
      calc (Cw + 6 * Real.log D.β) * ((2 * (D.L : ℝ) ^ j) ^ 4 * ((D.L : ℝ) ^ t) ^ 4)
          ≤ K * (1 + Real.log D.β) * ((2 * (D.L : ℝ) ^ j) ^ 4 * ((D.L : ℝ) ^ t) ^ 4) :=
            mul_le_mul_of_nonneg_right hCK hN0
        _ = _ := by ring
    calc (1 : ℝ) = Real.exp (K * (1 + Real.log D.β) * (g.cellRatio : ℝ) ^ 4 * (2 * (D.L : ℝ) ^ j) ^ 4) *
          Real.exp (-(K * (1 + Real.log D.β) * (g.cellRatio : ℝ) ^ 4 * (2 * (D.L : ℝ) ^ j) ^ 4)) := by
          rw [← Real.exp_add]
          simp
      _ ≤ Real.exp (K * (1 + Real.log D.β) * (g.cellRatio : ℝ) ^ 4 * (2 * (D.L : ℝ) ^ j) ^ 4) *
          Real.exp (-((Cw + 6 * Real.log D.β) * (((2 * D.L ^ j * D.L ^ t : ℕ) : ℝ)) ^ 4)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
          linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
private theorem clusterRange_le_two_mul {x : ℝ} (hx : 1 ≤ x) :
    (clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by
  have hu1 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx (by norm_num)
  have h2 : (clusterRange x : ℝ) < x ^ ((1 : ℝ) / 100) + 1 :=
    Nat.ceil_lt_add_one (show 0 ≤ x ^ ((1 : ℝ) / 100) by linarith)
  linarith
abbrev _root_.YangMills.SharedProofs.p52588 := @clusterRange_le_two_mul
private theorem clusterRange_le_of_abs_sub_le {x x' B : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x) (hx' : 1 ≤ x')
    (h : |x' - x| ≤ 2 * B) :
    (clusterRange x' : ℝ) ≤ (2 + 2 * B) * x ^ ((1 : ℝ) / 100) := by
  have hu1 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx (by norm_num)
  have h2 : (clusterRange x' : ℝ) < x' ^ ((1 : ℝ) / 100) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
  have h3 : x' ≤ (1 + 2 * B) * x := by
    have := (abs_le.mp h).2
    nlinarith
  have h4 : x' ^ ((1 : ℝ) / 100) ≤ (1 + 2 * B) * x ^ ((1 : ℝ) / 100) := by
    calc x' ^ ((1 : ℝ) / 100) ≤ ((1 + 2 * B) * x) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow (by linarith) h3 (by norm_num)
      _ = (1 + 2 * B) ^ ((1 : ℝ) / 100) * x ^ ((1 : ℝ) / 100) :=
          Real.mul_rpow (by linarith) (by linarith)
      _ ≤ (1 + 2 * B) * x ^ ((1 : ℝ) / 100) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          calc (1 + 2 * B) ^ ((1 : ℝ) / 100) ≤ (1 + 2 * B) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = 1 + 2 * B := Real.rpow_one _
  nlinarith
private theorem levelMesh_pos' (D : ChessboardSetup) (t : ℕ) : 0 < levelMesh D t :=
  zpow_pos (by linarith [D.one_lt_factor]) _
private theorem levelMesh_succ' (D : ChessboardSetup) (t : ℕ) :
    levelMesh D (t + 1) = (D.L : ℝ) * levelMesh D t := by
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
  unfold levelMesh
  rw [show ((t + 1 : ℕ) : ℤ) - ((D.K : ℕ) : ℤ) = ((t : ℤ) - ((D.K : ℕ) : ℤ)) + 1 by push_cast; ring,
    zpow_add_one₀ hL0]
  ring
private theorem exists_torusRatioBound_of_params (hR : FreeEnergies.expansionAlongFlow)
    (hC : CouplingBoundAtRadiusScale)
    (hZ : TorusPartitionIsWilsonPartition) {ℓ : StepParameters} (hS : FreeEnergies.ExpansionHolds ℓ)
    (hfit : ℓ.Admissible)
    {Cw C₁ nS : ℝ} (hW : wilsonPartitionBoundsAt Cw) (hC₁ : 0 ≤ C₁) (hnS : 1 ≤ nS)
    (hpow : partitionPowerBoundAt ℓ C₁ nS) (Ξ : ℝ) :
    ∃ b₁ : ℝ, 0 ≤ b₁ ∧ ∀ D : ChessboardSetup, IsAdmissibleSetup ℓ Ξ D → TorusRatioBound D b₁ := by
  have hL1 : (1 : ℝ) ≤ (ℓ.side : ℝ) := by
    have := hfit.L_ge
    exact_mod_cast (by omega : 1 ≤ ℓ.side)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max nS ((ℓ.side * ℓ.n₀ : ℕ) : ℝ) := ⟨_, rfl⟩
  have hcn : nS ≤ c := hc ▸ le_max_left _ _
  have hcL : ((ℓ.side * ℓ.n₀ : ℕ) : ℝ) ≤ c := hc ▸ le_max_right _ _
  have hc1 : 1 ≤ c := hnS.trans hcn
  obtain ⟨C₇, hC₇, hcoup⟩ := hC ℓ Ξ c hfit hc1
  have hB := hfit.B_pos
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (ℓ.side : ℝ) * c * (2 + 2 * ℓ.B) := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀def⟩ : ∃ K₀ : ℝ, K₀ = C₁ + |Cw| + 6 := ⟨_, rfl⟩
  have hK₀ : 0 ≤ K₀ := by
    rw [hK₀def]
    positivity
  have hKC : C₁ ≤ K₀ := by
    rw [hK₀def]
    linarith [abs_nonneg Cw]
  have hKW : |Cw| + 6 ≤ K₀ := by
    rw [hK₀def]
    linarith
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = K₀ * 101 * A ^ 4 * C₇ ^ ((1 : ℝ) / 20) := ⟨_, rfl⟩
  have hQ : 0 ≤ Q := by
    rw [hQdef]
    have := Real.rpow_nonneg hC₇ ((1 : ℝ) / 20)
    positivity
  have hlogΞ : 0 ≤ Real.log (max Ξ 1) := Real.log_nonneg (le_max_right _ _)
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = K₀ * (1 + Real.log (max Ξ 1)) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    positivity
  refine ⟨W + 2 * Q, by linarith, fun D hD g hg j => ?_⟩
  obtain ⟨hDL, hfloor, hceil⟩ := id hD
  have hDLc : (D.L : ℝ) = (ℓ.side : ℝ) := by rw [hDL]
  have hL3 : (3 : ℝ) ≤ D.L := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 3 ≤ D.L)
  have hβ : 1 ≤ D.β := hfit.y₁_ge.trans (hfloor 0 (Nat.zero_le _))
  have hside : 0 < g.cellSide := zpow_pos (by linarith) _
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = TorusBound.logPos (1 / g.cellSide) := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := hpdef ▸ le_max_right _ _
  have hp20 : 0 ≤ p ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hp0 _
  have hl0 : 0 ≤ g.cellSide ^ 4 := by positivity
  have hone : 1 ≤ g.cellSide ^ 4 + p ^ ((1 : ℝ) / 20) := by
    rw [hpdef]
    exact one_le_side_pow_add_logPos hL3 g.q
  have hreach : FreeEnergies.CouplingsAboveFloor ℓ D.β (D.K : ℕ) := fun t ht => hfloor t ht
  have hstep : ∀ t : ℕ, t < (D.K : ℕ) →
      |(couplingFlow ℓ D.β (t + 1)).1 - (couplingFlow ℓ D.β t).1| ≤ 2 * ℓ.B :=
    fun t ht => (hR ℓ hS D.β (D.K : ℕ) hreach).2 t ht
  obtain ⟨hcl, hcn'⟩ := hcoup D hD hstep g.cellSide hside
  rw [← hpdef] at hcl hcn'
  have hfin : ∀ x m : ℝ, 1 ≤ x → 0 ≤ m → m ≤ A * x ^ ((1 : ℝ) / 100) → x ≤ C₇ * (1 + p) →
      K₀ * (1 + Real.log x) * m ^ 4 ≤
        (W + 2 * Q) * g.cellSide ^ 4 + (W + 2 * Q) * p ^ ((1 : ℝ) / 20) := by
    intro x m hx hm0 hm hxC
    have h1 := log_mul_pow_le_of_le_rpow hK₀ hx hm0 hm
    have h2 := rpow_twentieth_le_of_le hC₇ hx hp0 hxC
    have h3 : K₀ * 101 * A ^ 4 * x ^ ((1 : ℝ) / 20) ≤ Q * (1 + p ^ ((1 : ℝ) / 20)) := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ K₀ * 101 * A ^ 4)
      rw [hQdef]
      linarith
    exact h1.trans (h3.trans (mul_one_add_le_of_one_le hQ hW0 hl0 hp20 hone))
  rw [← hpdef]
  classical
  by_cases hex : ∃ s : ℕ, s ≤ (D.K : ℕ) ∧ RadiusCoversScale ℓ D c g.cellSide s
  · obtain ⟨s₀, hs₀K, hs₀⟩ := hex
    obtain ⟨s, hs⟩ : ∃ s : ℕ, s = Nat.findGreatest (fun t => RadiusCoversScale ℓ D c g.cellSide t) (D.K : ℕ) :=
      ⟨_, rfl⟩
    have hsP : RadiusCoversScale ℓ D c g.cellSide s := by
      rw [hs]
      exact Nat.findGreatest_spec (P := fun t => RadiusCoversScale ℓ D c g.cellSide t) hs₀K hs₀
    have hsK : s ≤ (D.K : ℕ) := by
      rw [hs]
      exact Nat.findGreatest_le _
    have hgreat : ∀ t : ℕ, s < t → t ≤ (D.K : ℕ) → ¬ RadiusCoversScale ℓ D c g.cellSide t := by
      intro t h1 h2
      rw [hs] at h1
      exact Nat.findGreatest_is_greatest h1 h2
    have hxC := hcl s ⟨hsK, hsP, hgreat⟩
    have hb := torusPartitionRatio_le_of_covered hZ hfit hW hpow hnS hcn hcL D hDL hβ
      (fun t ht => hfloor t (ht.trans hsK)) g hg j hsP
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = flowCoupling ℓ D.β s := ⟨_, rfl⟩
    rw [← hx] at hb
    have hxC' : x ≤ C₇ * (1 + p) := by
      rw [hx]
      exact hxC
    have hx1 : 1 ≤ x := by
      rw [hx]
      exact hfit.y₁_ge.trans (hfloor s hsK)
    have hlog0 := Real.log_nonneg hx1
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = g.cellSide / levelMesh D s := ⟨_, rfl⟩
    rw [← hm] at hb
    have hm0 : 0 ≤ m := by
      rw [hm]
      exact (div_pos hside (levelMesh_pos' D s)).le
    have hCK : C₁ * (1 + Real.log x) * m ^ 4 ≤ K₀ * (1 + Real.log x) * m ^ 4 := by
      have h1 : 0 ≤ 1 + Real.log x := by linarith
      have h2 : 0 ≤ m ^ 4 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC h1) h2
    refine hb.trans (Real.exp_le_exp.mpr (hCK.trans ?_))
    rcases hsK.lt_or_eq with hlt | heq
    · have hnot : ¬ (c * (clusterRange (couplingFlow ℓ D.β (s + 1)).1 : ℝ) ≤ g.cellSide / levelMesh D (s + 1)) :=
        hgreat (s + 1) (by omega) hlt
      have hnot' := not_le.mp hnot
      have hx'1 : 1 ≤ (couplingFlow ℓ D.β (s + 1)).1 := hfit.y₁_ge.trans (hfloor (s + 1) hlt)
      have hstepx : |(couplingFlow ℓ D.β (s + 1)).1 - x| ≤ 2 * ℓ.B := by
        rw [hx]
        exact hstep s hlt
      have hrn := clusterRange_le_of_abs_sub_le hB.le hx1 hx'1 hstepx
      refine hfin x m hx1 hm0 ?_ hxC'
      have hsp : m = (ℓ.side : ℝ) * (g.cellSide / levelMesh D (s + 1)) := by
        have h1 := (levelMesh_pos' D s).ne'
        have h2 : (ℓ.side : ℝ) ≠ 0 := by linarith
        rw [hm, levelMesh_succ', hDLc]
        field_simp
      have hc0 : 0 ≤ c := by linarith
      have hLpos : 0 ≤ (ℓ.side : ℝ) := by linarith
      rw [hsp, hAdef]
      calc (ℓ.side : ℝ) * (g.cellSide / levelMesh D (s + 1))
          ≤ (ℓ.side : ℝ) * (c * ((2 + 2 * ℓ.B) * x ^ ((1 : ℝ) / 100))) := by
            refine mul_le_mul_of_nonneg_left ?_ hLpos
            exact hnot'.le.trans (mul_le_mul_of_nonneg_left hrn hc0)
        _ = _ := by ring
    · have hxΞ : x ≤ Ξ := by
        rw [hx, heq]
        exact hceil
      have hmside : m = g.cellSide := by
        rw [hm, heq]
        simp [levelMesh]
      have hlogle : Real.log x ≤ Real.log (max Ξ 1) :=
        Real.log_le_log (by linarith) (hxΞ.trans (le_max_left _ _))
      have h1 : K₀ * (1 + Real.log x) * g.cellSide ^ 4 ≤ W * g.cellSide ^ 4 := by
        rw [hWdef]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK₀) hl0
      rw [hmside]
      have e : (W + 2 * Q) * g.cellSide ^ 4 + (W + 2 * Q) * p ^ ((1 : ℝ) / 20) =
          W * g.cellSide ^ 4 + 2 * (Q * g.cellSide ^ 4) + W * p ^ ((1 : ℝ) / 20) +
            2 * (Q * p ^ ((1 : ℝ) / 20)) := by ring
      rw [e]
      linarith [mul_nonneg hQ hl0, mul_nonneg hW0 hp20, mul_nonneg hQ hp20]
  · have hall : ∀ t : ℕ, t ≤ (D.K : ℕ) → ¬ RadiusCoversScale ℓ D c g.cellSide t :=
      fun t ht h => hex ⟨t, ht, h⟩
    have hβC : D.β ≤ C₇ * (1 + p) := hcn' hall
    have hb := torusPartitionRatio_le_of_uncovered hZ hW hKW D hβ g hg j
    have hr2 : (2 : ℝ) ≤ (g.cellRatio : ℝ) := by exact_mod_cast g.two_le_cellRatio
    refine hb.trans (Real.exp_le_exp.mpr (hfin D.β _ hβ (by linarith) ?_ hβC))
    have h0 : ¬ (c * (clusterRange D.β : ℝ) ≤ g.cellSide / levelMesh D 0) := hall 0 (Nat.zero_le _)
    have h0' := not_le.mp h0
    have hsp0 : levelMesh D 0 = D.mesh := by
      simp [levelMesh, ChessboardSetup.mesh, PeriodicLattice.meshSize]
    have hr : g.cellSide / levelMesh D 0 = (g.cellRatio : ℝ) := by
      have := D.mesh_pos.ne'
      rw [hsp0, g.cellSide_eq]
      field_simp
    rw [hr] at h0'
    have hc0 : 0 ≤ c := by linarith
    have hu1 : 1 ≤ D.β ^ ((1 : ℝ) / 100) := Real.one_le_rpow hβ (by norm_num)
    have h1 : c * (clusterRange D.β : ℝ) ≤ c * (2 * D.β ^ ((1 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left (clusterRange_le_two_mul hβ) hc0
    have h2 : c * 2 ≤ A := by
      rw [hAdef]
      have e1 : c ≤ (ℓ.side : ℝ) * c := le_mul_of_one_le_left hc0 hL1
      have e2 : 0 ≤ (ℓ.side : ℝ) * c * (2 * ℓ.B) := by positivity
      linarith
    have h3 : c * 2 * D.β ^ ((1 : ℝ) / 100) ≤ A * D.β ^ ((1 : ℝ) / 100) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    linarith
theorem torusRatioBoundedStatement_holds (hP : FreeEnergies.partitionPowerBound)
    (hR : FreeEnergies.expansionAlongFlow)
    (hC : CouplingBoundAtRadiusScale) (hZ : TorusPartitionIsWilsonPartition)
    (hW : WilsonPartitionBounds) : TorusRatioBoundedStatement := by
  obtain ⟨rt₀, hrt, hP⟩ := hP
  obtain ⟨Cw, hW⟩ := hW
  refine ⟨rt₀, hrt, fun T hT hcs hr => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hP T hT hcs hr
  refine ⟨max y₀ T.floorMin, fun y hy hS Ξ => ?_⟩
  have hfit := hT.fits y ((le_max_right _ _).trans hy)
  obtain ⟨C₁, nS, hC₁, hnS, hpow⟩ := hy₀ y ((le_max_left _ _).trans hy) hS
  exact exists_torusRatioBound_of_params hR hC hZ hS hfit hW hC₁ hnS hpow Ξ
end YangMills.Construction.ReflectedCopies
end
