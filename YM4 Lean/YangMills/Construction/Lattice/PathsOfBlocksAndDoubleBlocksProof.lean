import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlockProof
import YangMills.Construction.Lattice.DoubleBlockFromItsLowestCornerProof
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlockPaths
variable {L m : ℕ} {j j' : ℤ}
theorem offsetSite_zero (w : Site L m j') : offsetSite w 0 = w := by
  simp [offsetSite]
theorem offsetSite_offsetSite (w : Site L m j') (p q : Fin 4 → ℤ) :
    offsetSite (offsetSite w p) q = offsetSite w (p + q) := by
  simp only [offsetSite, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
theorem offsetSite_single (w : Site L m j') (ν : Fin 4) (a : ℤ) :
    offsetSite w (Pi.single ν a) = w + a • unitStep L m j' ν := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlockCorner.offsetSite_single <;> assumption
theorem offsetSite_add_base (w a : Site L m j') (p : Fin 4 → ℤ) :
    offsetSite (w + a) p = offsetSite w p + a := by
  simp only [offsetSite]
  abel
theorem coe_zsmul_unitStep (a : ℤ) (μ : Fin 4) :
    ((a • unitStep L m j' μ : Site L m j') : FourTorus L m) =
      pointOnAxis L m μ ((a : ℝ) * meshSize L j') := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_zsmul_unitStep <;> assumption
theorem coe_offsetSite (w : Site L m j') (n : Fin 4 → ℤ) :
    ((offsetSite w n : Site L m j') : FourTorus L m) =
      (w : FourTorus L m) + ∑ μ, pointOnAxis L m μ ((n μ : ℝ) * meshSize L j') := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.coe_offsetSite <;> assumption
theorem coe_toSublattice {y : Site L m j} (h : (y : FourTorus L m) ∈ sublattice L m j') :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.coe_toSublattice <;> assumption
theorem isBlockOffset_iff {y : Site L m j} {w x : Site L m j'}
    (hw : (w : FourTorus L m) = y) (n : Fin 4 → ℤ) :
    IsBlockOffset y x n ↔
      x = offsetSite w n ∧ ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1 := by
  unfold IsBlockOffset
  rw [← hw]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Subtype.ext ?_, h2⟩
    rw [coe_offsetSite, ← h1]
    abel
  · rintro ⟨rfl, h2⟩
    refine ⟨?_, h2⟩
    rw [coe_offsetSite]
    abel
theorem eq_of_offsetSite_eq (hc : SublatticeCoordinates L m j') {w : Site L m j'}
    {a b : Fin 4 → ℤ}
    (hd : ∀ μ, |a μ - b μ| < 2 * (halfPeriod L m j' : ℤ))
    (h : offsetSite w a = offsetSite w b) : a = b := by
  obtain ⟨-, -, -, -, h5, -⟩ := hc
  have hm := (h5 w a b).1 h
  funext μ
  have hdvd : ((2 * halfPeriod L m j' : ℕ) : ℤ) ∣ a μ - b μ :=
    Int.modEq_iff_dvd.1 (hm μ).symm
  have hz := Int.eq_zero_of_abs_lt_dvd hdvd (by push_cast; exact hd μ)
  omega
theorem zsmul_unitStep_inj (hc : SublatticeCoordinates L m j') {μ ν : Fin 4} {a b : ℤ}
    (ha : |a| < (halfPeriod L m j' : ℤ)) (hb : |b| < (halfPeriod L m j' : ℤ))
    (h : a • unitStep L m j' μ = b • unitStep L m j' ν) (ha0 : a ≠ 0) : μ = ν ∧ a = b := by
  have h' : offsetSite (0 : Site L m j') (Pi.single μ a) =
      offsetSite 0 (Pi.single ν b) := by
    rw [offsetSite_single, offsetSite_single, h]
  rw [abs_lt] at ha hb
  have hq : (Pi.single μ a : Fin 4 → ℤ) = Pi.single ν b := by
    refine eq_of_offsetSite_eq hc (fun κ => ?_) h'
    simp only [Pi.single_apply]
    split_ifs <;> rw [abs_lt] <;> constructor <;> omega
  have hμ := congrFun hq μ
  by_cases e : μ = ν
  · subst e
    exact ⟨rfl, by simpa using hμ⟩
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne e] at hμ
    exact absurd hμ ha0
theorem sign_ne_zero_and_abs_eq_one {a : ℤ} (h : a ≠ 0) : a.sign ≠ 0 ∧ |a.sign| = 1 := by
  rcases lt_or_gt_of_ne h with h | h
  · simp [Int.sign_eq_neg_one_of_neg h]
  · simp [Int.sign_eq_one_of_pos h]
def Joins : List (Bond L m j') → Site L m j' → Site L m j' → Prop
  | [], x, y => x = y
  | b :: Γ, x, y => b.source = x ∧ Joins Γ b.target y
theorem Joins.isBondPathFromTo {Γ : List (Bond L m j')} {x y : Site L m j'}
    (h : Joins Γ x y) : IsBondPathFromTo Γ x y := by
  induction Γ generalizing x with
  | nil => exact ⟨List.isChain_nil, fun _ => h, by simp, by simp⟩
  | cons b Γ ih =>
    obtain ⟨hb, hΓ⟩ := h
    obtain ⟨c1, c2, c3, c4⟩ := ih hΓ
    refine ⟨?_, by simp, ?_, ?_⟩
    · cases Γ with
      | nil => exact List.isChain_singleton _
      | cons b' Γ' => exact List.isChain_cons_cons.2 ⟨(c3 b' (by simp)).symm, c1⟩
    · intro b' hb'
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb'
      exact hb' ▸ hb
    · cases Γ with
      | nil =>
        intro b' hb'
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hb'
        exact hb' ▸ hΓ
      | cons b' Γ' =>
        intro b'' hb''
        rw [List.getLast?_cons_cons] at hb''
        exact c4 b'' hb''
theorem Joins.append {Γ Γ' : List (Bond L m j')} {x y z : Site L m j'} (h : Joins Γ x y)
    (h' : Joins Γ' y z) : Joins (Γ ++ Γ') x z := by
  induction Γ generalizing x with
  | nil =>
    have : x = y := h
    subst this
    exact h'
  | cons b Γ ih => exact ⟨h.1, ih h.2⟩
theorem Joins.mem_pathSites {Γ : List (Bond L m j')} {x y : Site L m j'} (h : Joins Γ x y)
    {b : Bond L m j'} (hb : b ∈ Γ) :
    b.source ∈ sitesOfPath x Γ ∧ b.target ∈ sitesOfPath x Γ := by
  induction Γ generalizing x with
  | nil => cases hb
  | cons b₀ Γ ih =>
    obtain ⟨h0, h1⟩ := h
    have sub : ∀ z, z ∈ sitesOfPath b₀.target Γ → z ∈ sitesOfPath x (b₀ :: Γ) :=
      fun z hz => List.mem_cons_of_mem _ hz
    rw [List.mem_cons] at hb
    rcases hb with rfl | hb
    · constructor
      · simp [sitesOfPath, h0]
      · simp [sitesOfPath]
    · exact ⟨sub _ (ih h1 hb).1, sub _ (ih h1 hb).2⟩
theorem joins_forwardFlow (x : Site L m j') (μ : Fin 4) (k : ℕ) :
    Joins (forwardAxisPath x μ k) x (x + (k : ℤ) • unitStep L m j' μ) := by
  induction k generalizing x with
  | zero => simp [Joins, forwardAxisPath]
  | succ k ih =>
    rw [forwardAxisPath]
    refine ⟨rfl, ?_⟩
    have := ih (x + unitStep L m j' μ)
    have e : x + ((k + 1 : ℕ) : ℤ) • unitStep L m j' μ =
        x + unitStep L m j' μ + (k : ℤ) • unitStep L m j' μ := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e]
    exact this
theorem joins_backwardFlow (x : Site L m j') (μ : Fin 4) (k : ℕ) :
    Joins (backwardAxisPath x μ k) x (x - (k : ℤ) • unitStep L m j' μ) := by
  induction k generalizing x with
  | zero => simp [Joins, backwardAxisPath]
  | succ k ih =>
    rw [backwardAxisPath]
    refine ⟨rfl, ?_⟩
    have := ih (x - unitStep L m j' μ)
    have e : x - ((k + 1 : ℕ) : ℤ) • unitStep L m j' μ =
        x - unitStep L m j' μ - (k : ℤ) • unitStep L m j' μ := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e]
    exact this
theorem joins_flowAlong (x : Site L m j') (μ : Fin 4) (n : ℤ) :
    Joins (flowAlong x μ n) x (x + n • unitStep L m j' μ) := by
  unfold flowAlong
  split_ifs with h
  · have := joins_forwardFlow x μ n.toNat
    rwa [Int.toNat_of_nonneg h] at this
  · have := joins_backwardFlow x μ (-n).toNat
    rw [Int.toNat_of_nonneg (by omega), neg_smul, sub_neg_eq_add] at this
    exact this
theorem joins_stepsThroughAxes (n : Fin 4 → ℤ) (x : Site L m j') (l : List (Fin 4)) :
    Joins (stepsThroughAxes n x l) x (x + (l.map fun μ => n μ • unitStep L m j' μ).sum) := by
  induction l generalizing x with
  | nil => simp [Joins, stepsThroughAxes]
  | cons μ l ih =>
    rw [stepsThroughAxes]
    refine (joins_flowAlong x μ (n μ)).append ?_
    have := ih (x + n μ • unitStep L m j' μ)
    simpa [add_assoc] using this
theorem add_sum_eq_offsetSite (n : Fin 4 → ℤ) (x : Site L m j') {l : List (Fin 4)}
    (hl : l.Nodup) (hoff : ∀ ν, ν ∉ l → n ν = 0) :
    x + (l.map fun μ => n μ • unitStep L m j' μ).sum = offsetSite x n := by
  unfold offsetSite
  congr 1
  rw [← List.sum_toFinset _ hl]
  refine Finset.sum_subset (Finset.subset_univ _) fun ν _ hν => ?_
  rw [hoff ν (by simpa using hν), zero_smul]
theorem target_sub_source_of_mem_forwardFlow {x : Site L m j'} {μ : Fin 4} {k : ℕ}
    {b : Bond L m j'} (h : b ∈ forwardAxisPath x μ k) : b.target - b.source = unitStep L m j' μ := by
  induction k generalizing x with
  | zero => simp [forwardAxisPath] at h
  | succ k ih =>
    rw [forwardAxisPath, List.mem_cons] at h
    rcases h with rfl | h
    · simp [Bond.forwardFrom]
    · exact ih h
theorem target_sub_source_of_mem_backwardFlow {x : Site L m j'} {μ : Fin 4} {k : ℕ}
    {b : Bond L m j'} (h : b ∈ backwardAxisPath x μ k) :
    b.target - b.source = -unitStep L m j' μ := by
  induction k generalizing x with
  | zero => simp [backwardAxisPath] at h
  | succ k ih =>
    rw [backwardAxisPath, List.mem_cons] at h
    rcases h with rfl | h
    · simp [Bond.backwardFrom]
    · exact ih h
theorem length_forwardFlow (x : Site L m j') (μ : Fin 4) (k : ℕ) :
    (forwardAxisPath x μ k).length = k := by apply _root_.YangMills.SharedProofs.p1058 <;> assumption
theorem length_backwardFlow (x : Site L m j') (μ : Fin 4) (k : ℕ) :
    (backwardAxisPath x μ k).length = k := by apply _root_.YangMills.SharedProofs.p8383 <;> assumption
theorem length_flowAlong (x : Site L m j') (μ : Fin 4) (n : ℤ) :
    (flowAlong x μ n).length = n.natAbs := by
  unfold flowAlong
  split_ifs with h
  · rw [length_forwardFlow]
    omega
  · rw [length_backwardFlow]
    omega
theorem target_sub_source_of_mem_flowAlong {x : Site L m j'} {μ : Fin 4} {n : ℤ}
    {b : Bond L m j'} (h : b ∈ flowAlong x μ n) :
    n ≠ 0 ∧ b.target - b.source = n.sign • unitStep L m j' μ := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp [flowAlong, forwardAxisPath] at h
  refine ⟨hn, ?_⟩
  unfold flowAlong at h
  split_ifs at h with h0
  · rw [Int.sign_eq_one_of_pos (by omega), one_smul]
    exact target_sub_source_of_mem_forwardFlow h
  · rw [Int.sign_eq_neg_one_of_neg (by omega), neg_smul, one_smul]
    exact target_sub_source_of_mem_backwardFlow h
theorem target_sub_source_of_mem_stepsThroughAxes {n : Fin 4 → ℤ} {x : Site L m j'}
    {l : List (Fin 4)} {b : Bond L m j'} (h : b ∈ stepsThroughAxes n x l) :
    ∃ ν ∈ l, n ν ≠ 0 ∧ b.target - b.source = (n ν).sign • unitStep L m j' ν := by
  induction l generalizing x with
  | nil => simp [stepsThroughAxes] at h
  | cons μ l ih =>
    rw [stepsThroughAxes, List.mem_append] at h
    rcases h with h | h
    · exact ⟨μ, by simp, target_sub_source_of_mem_flowAlong h⟩
    · obtain ⟨ν, hν, h⟩ := ih h
      exact ⟨ν, List.mem_cons_of_mem _ hν, h⟩
theorem countSteps_append (A B : List (Bond L m j')) (s : Site L m j') :
    countSteps (A ++ B) s = countSteps A s + countSteps B s := by
  simp [countSteps, List.countP_append]
theorem countSteps_of_forall_eq {Γ : List (Bond L m j')} {s : Site L m j'}
    (h : ∀ b ∈ Γ, b.target - b.source = s) : countSteps Γ s = Γ.length := by
  unfold countSteps
  rw [List.countP_eq_length]
  simpa using h
theorem countSteps_of_forall_ne {Γ : List (Bond L m j')} {s : Site L m j'}
    (h : ∀ b ∈ Γ, b.target - b.source ≠ s) : countSteps Γ s = 0 := by
  unfold countSteps
  rw [List.countP_eq_zero]
  simpa using h
theorem countSteps_stepsThroughAxes (hc : SublatticeCoordinates L m j')
    (hH : 2 ≤ (halfPeriod L m j' : ℤ)) (n : Fin 4 → ℤ) (x : Site L m j') {l : List (Fin 4)}
    (hl : l.Nodup) {ν : Fin 4} (hν : ν ∈ l) (h0 : n ν ≠ 0) :
    countSteps (stepsThroughAxes n x l) ((n ν).sign • unitStep L m j' ν) = (n ν).natAbs := by
  have small : ∀ {a : ℤ}, a ≠ 0 → |a.sign| < (halfPeriod L m j' : ℤ) := fun ha => by
    rw [(sign_ne_zero_and_abs_eq_one ha).2]
    omega
  induction l generalizing x with
  | nil => cases hν
  | cons μ l ih =>
    obtain ⟨hμl, hl'⟩ := List.nodup_cons.1 hl
    rw [stepsThroughAxes, countSteps_append]
    rcases List.mem_cons.1 hν with rfl | hν'
    · rw [countSteps_of_forall_eq (fun b hb => (target_sub_source_of_mem_flowAlong hb).2),
        length_flowAlong, countSteps_of_forall_ne, add_zero]
      intro b hb
      obtain ⟨κ, hκ, hk0, hd⟩ := target_sub_source_of_mem_stepsThroughAxes hb
      rw [hd]
      intro he
      have := (zsmul_unitStep_inj hc (small hk0) (small h0) he
        (sign_ne_zero_and_abs_eq_one hk0).1).1
      exact hμl (this ▸ hκ)
    · have hμν : μ ≠ ν := fun e => hμl (e ▸ hν')
      rw [countSteps_of_forall_ne, zero_add]
      · exact ih _ hl' hν'
      · intro b hb
        obtain ⟨h1, h2⟩ := target_sub_source_of_mem_flowAlong hb
        rw [h2]
        intro he
        exact hμν (zsmul_unitStep_inj hc (small h1) (small h0) he
          (sign_ne_zero_and_abs_eq_one h1).1).1
theorem mem_pathSites_forwardFlow {x : Site L m j'} {μ : Fin 4} {k : ℕ} {z : Site L m j'} :
    z ∈ sitesOfPath x (forwardAxisPath x μ k) ↔
      ∃ i : ℕ, i ≤ k ∧ z = x + (i : ℤ) • unitStep L m j' μ := by
  induction k generalizing x with
  | zero => simp [sitesOfPath, forwardAxisPath]
  | succ k ih =>
    have e : sitesOfPath x (forwardAxisPath x μ (k + 1)) =
        x :: sitesOfPath (x + unitStep L m j' μ) (forwardAxisPath (x + unitStep L m j' μ) μ k) := by
      simp [sitesOfPath, forwardAxisPath, Bond.forwardFrom]
    rw [e, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        push_cast
        rw [add_smul, one_smul]
        abel
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero =>
        left
        simp
      | succ i =>
        right
        refine ⟨i, by omega, ?_⟩
        push_cast
        rw [add_smul, one_smul]
        abel
theorem exists_of_mem_pathSites_backwardFlow {x : Site L m j'} {μ : Fin 4} {k : ℕ}
    {z : Site L m j'} (h : z ∈ sitesOfPath x (backwardAxisPath x μ k)) :
    ∃ i : ℕ, i ≤ k ∧ z = x - (i : ℤ) • unitStep L m j' μ := by
  induction k generalizing x with
  | zero =>
    simp only [sitesOfPath, backwardAxisPath, List.map_nil, List.mem_singleton] at h
    exact ⟨0, le_rfl, by simp [h]⟩
  | succ k ih =>
    have e : sitesOfPath x (backwardAxisPath x μ (k + 1)) =
        x :: sitesOfPath (x - unitStep L m j' μ) (backwardAxisPath (x - unitStep L m j' μ) μ k) := by
      simp [sitesOfPath, backwardAxisPath, Bond.backwardFrom]
    rw [e, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := ih h
      refine ⟨i + 1, by omega, ?_⟩
      push_cast
      rw [add_smul, one_smul]
      abel
theorem exists_of_mem_pathSites_flowAlong {x : Site L m j'} {μ : Fin 4} {n : ℤ}
    {z : Site L m j'} (h : z ∈ sitesOfPath x (flowAlong x μ n)) :
    ∃ t : ℤ, min 0 n ≤ t ∧ t ≤ max 0 n ∧ z = x + t • unitStep L m j' μ := by
  unfold flowAlong at h
  split_ifs at h with h0
  · obtain ⟨i, hi, rfl⟩ := mem_pathSites_forwardFlow.1 h
    exact ⟨i, by omega, by omega, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := exists_of_mem_pathSites_backwardFlow h
    refine ⟨-(i : ℤ), by omega, by omega, ?_⟩
    rw [neg_smul]
    abel
theorem exists_of_mem_pathSites_stepsThroughAxes {n : Fin 4 → ℤ} {x z : Site L m j'}
    {l : List (Fin 4)} (hl : l.Nodup)
    (h : z ∈ sitesOfPath x (stepsThroughAxes n x l)) :
    ∃ q : Fin 4 → ℤ, (∀ ν, ν ∉ l → q ν = 0) ∧
      (∀ ν, min 0 (n ν) ≤ q ν ∧ q ν ≤ max 0 (n ν)) ∧ z = offsetSite x q := by
  induction l generalizing x with
  | nil =>
    simp only [sitesOfPath, stepsThroughAxes, List.map_nil, List.mem_singleton] at h
    refine ⟨0, by simp, fun ν => ?_, by rw [h, offsetSite_zero]⟩
    simp only [Pi.zero_apply]
    omega
  | cons μ l ih =>
    obtain ⟨hμl, hl'⟩ := List.nodup_cons.1 hl
    rw [stepsThroughAxes] at h
    have hsplit : z ∈ sitesOfPath x (flowAlong x μ (n μ)) ∨
        z ∈ sitesOfPath (x + n μ • unitStep L m j' μ)
          (stepsThroughAxes n (x + n μ • unitStep L m j' μ) l) := by
      simp only [sitesOfPath, List.map_append, List.mem_cons, List.mem_append] at h ⊢
      tauto
    rcases hsplit with h | h
    · obtain ⟨t, h1, h2, rfl⟩ := exists_of_mem_pathSites_flowAlong h
      refine ⟨Pi.single μ t, fun ν hν => ?_, fun ν => ?_, by rw [offsetSite_single]⟩
      · rw [Pi.single_eq_of_ne]
        rintro rfl
        exact hν (by simp)
      · by_cases e : ν = μ
        · subst e
          rw [Pi.single_eq_same]
          exact ⟨h1, h2⟩
        · rw [Pi.single_eq_of_ne e]
          omega
    · obtain ⟨q, hq0, hq1, rfl⟩ := ih hl' h
      refine ⟨Pi.single μ (n μ) + q, fun ν hν => ?_, fun ν => ?_, ?_⟩
      · have h1 : ν ≠ μ := by
          rintro rfl
          exact hν (by simp)
        have h2 : ν ∉ l := fun h => hν (List.mem_cons_of_mem _ h)
        simp [Pi.single_eq_of_ne h1, hq0 ν h2]
      · by_cases e : ν = μ
        · subst e
          have := hq0 ν hμl
          simp only [Pi.add_apply, Pi.single_eq_same, this]
          omega
        · have := hq1 ν
          simp only [Pi.add_apply, Pi.single_eq_of_ne e, zero_add]
          exact this
      · rw [← offsetSite_offsetSite, offsetSite_single]
theorem exists_offset_of_mem_pathSites {lo hi n p₀ : Fin 4 → ℤ} {w z : Site L m j'}
    {l : List (Fin 4)} (hl : l.Nodup)
    (h0 : ∀ ν, lo ν ≤ p₀ ν ∧ p₀ ν ≤ hi ν) (h1 : ∀ ν, lo ν ≤ p₀ ν + n ν ∧ p₀ ν + n ν ≤ hi ν)
    (hz : z ∈ sitesOfPath (offsetSite w p₀) (stepsThroughAxes n (offsetSite w p₀) l)) :
    ∃ p : Fin 4 → ℤ, (∀ ν, lo ν ≤ p ν ∧ p ν ≤ hi ν) ∧ z = offsetSite w p := by
  obtain ⟨q, -, hq, rfl⟩ := exists_of_mem_pathSites_stepsThroughAxes hl hz
  refine ⟨p₀ + q, fun ν => ?_, offsetSite_offsetSite w p₀ q⟩
  have a := h0 ν
  have b := h1 ν
  have c := hq ν
  simp only [Pi.add_apply]
  omega
theorem translatePath_append (A B : List (Bond L m j')) (a : Site L m j') :
    translatePath (A ++ B) a = translatePath A a ++ translatePath B a := by
  simp [translatePath]
theorem translatePath_forwardFlow (x a : Site L m j') (μ : Fin 4) (k : ℕ) :
    translatePath (forwardAxisPath x μ k) a = forwardAxisPath (x + a) μ k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have ih' := ih (x + unitStep L m j' μ)
    rw [add_right_comm] at ih'
    rw [forwardAxisPath, forwardAxisPath, ← ih']
    simp only [translatePath, List.map_cons, List.cons.injEq, and_true]
    exact Bond.ext rfl (add_right_comm _ _ _)
theorem translatePath_backwardFlow (x a : Site L m j') (μ : Fin 4) (k : ℕ) :
    translatePath (backwardAxisPath x μ k) a = backwardAxisPath (x + a) μ k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have ih' := ih (x - unitStep L m j' μ)
    rw [sub_add_eq_add_sub] at ih'
    rw [backwardAxisPath, backwardAxisPath, ← ih']
    simp only [translatePath, List.map_cons, List.cons.injEq, and_true]
    exact Bond.ext rfl (sub_add_eq_add_sub _ _ _)
theorem translatePath_flowAlong (x a : Site L m j') (μ : Fin 4) (n : ℤ) :
    translatePath (flowAlong x μ n) a = flowAlong (x + a) μ n := by
  unfold flowAlong
  split_ifs
  · exact translatePath_forwardFlow _ _ _ _
  · exact translatePath_backwardFlow _ _ _ _
theorem translatePath_stepsThroughAxes (n : Fin 4 → ℤ) (x a : Site L m j') (l : List (Fin 4)) :
    translatePath (stepsThroughAxes n x l) a = stepsThroughAxes n (x + a) l := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    rw [stepsThroughAxes, stepsThroughAxes, translatePath_append, translatePath_flowAlong, ih,
      add_right_comm]
theorem coord_nonneg_or_nonpos {s : List (Fin 4 → ℤ)} (h : IsMonotoneSteps s) (ν : Fin 4) :
    (∀ t ∈ s, 0 ≤ t ν) ∨ ∀ t ∈ s, t ν ≤ 0 := by
  obtain ⟨h1, h2⟩ := h
  by_cases hn : (-Pi.single ν 1 : Fin 4 → ℤ) ∈ s
  · right
    intro t ht
    obtain ⟨κ, rfl | rfl⟩ := h1 t ht
    · by_cases e : κ = ν
      · subst e
        exact absurd ⟨ht, hn⟩ (h2 κ)
      · simp [Pi.single_eq_of_ne (Ne.symm e)]
    · by_cases e : κ = ν
      · subst e
        simp
      · simp [Pi.single_eq_of_ne (Ne.symm e)]
  · left
    intro t ht
    obtain ⟨κ, rfl | rfl⟩ := h1 t ht
    · by_cases e : κ = ν
      · subst e
        simp
      · simp [Pi.single_eq_of_ne (Ne.symm e)]
    · by_cases e : κ = ν
      · subst e
        exact absurd ht hn
      · simp [Pi.single_eq_of_ne (Ne.symm e)]
theorem list_sum_apply_nonneg (u : List (Fin 4 → ℤ)) (ν : Fin 4) (h : ∀ t ∈ u, 0 ≤ t ν) :
    0 ≤ u.sum ν := by
  induction u with
  | nil => simp
  | cons t u ih =>
    have a := h t (by simp)
    have b := ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [List.sum_cons, Pi.add_apply]
    omega
theorem list_sum_apply_nonpos (u : List (Fin 4 → ℤ)) (ν : Fin 4) (h : ∀ t ∈ u, t ν ≤ 0) :
    u.sum ν ≤ 0 := by
  induction u with
  | nil => simp
  | cons t u ih =>
    have a := h t (by simp)
    have b := ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [List.sum_cons, Pi.add_apply]
    omega
theorem monotonePathsRemainIn_of_box {w : Site L m j'} {Q : Set (Fin 4 → ℤ)}
    {R : Set (FourTorus L m)}
    (lo hi : Fin 4 → ℤ) (hQ : ∀ p, p ∈ Q ↔ ∀ ν, lo ν ≤ p ν ∧ p ν ≤ hi ν)
    (hR : ∀ p ∈ Q, (offsetSite w p : FourTorus L m) ∈ R) :
    MonotonePathsRemainIn w Q R := by
  intro p hp s hs hend i _
  rw [offsetSite_offsetSite]
  refine hR _ ((hQ _).2 fun ν => ?_)
  have e : s.sum = (s.take i).sum + (s.drop i).sum := by
    rw [← List.sum_append, List.take_append_drop]
  have e' := congrFun e ν
  have h1 := (hQ _).1 hp ν
  have h2 := (hQ _).1 hend ν
  simp only [Pi.add_apply] at e' h2 ⊢
  rcases coord_nonneg_or_nonpos hs ν with h | h
  · have a := list_sum_apply_nonneg (s.take i) ν fun t ht => h t (List.mem_of_mem_take ht)
    have b := list_sum_apply_nonneg (s.drop i) ν fun t ht => h t (List.mem_of_mem_drop ht)
    omega
  · have a := list_sum_apply_nonpos (s.take i) ν fun t ht => h t (List.mem_of_mem_take ht)
    have b := list_sum_apply_nonpos (s.drop i) ν fun t ht => h t (List.mem_of_mem_drop ht)
    omega
def axisList {D : Finset (Fin 4)} (σ : Fin D.card ≃ D) : List (Fin 4) :=
  (List.finRange _).map fun i => ((σ i : D) : Fin 4)
theorem exists_axisList_eq {D D' : Finset (Fin 4)} (h : D = D') (σ : Fin D.card ≃ D) :
    ∃ σ' : Fin D'.card ≃ D', axisList σ' = axisList σ := by
  subst h
  exact ⟨σ, rfl⟩
theorem orderedContour_eq (y : Site L m j) (x : Site L m j') (σ : AxisOrdering y x) :
    orderedContour y x σ =
      stepsThroughAxes (blockOffset y x) (y.toSublattice j') (axisList σ) := rfl
theorem exists_of_mem_contourSet {y : Site L m j} {x : Site L m j'} {p : Fin 4 → ℤ}
    {Γ : List (Bond L m j')} (hΓ : Γ ∈ contourSet y x) (hb : blockOffset y x = p) :
    ∃ l : List (Fin 4), l.Nodup ∧ (∀ ν, ν ∈ l ↔ p ν ≠ 0) ∧
      Γ = stepsThroughAxes p (y.toSublattice j') l := by
  obtain ⟨σ, rfl⟩ := hΓ
  refine ⟨(List.finRange _).map fun i => ((σ i : offsetAxes y x) : Fin 4), ?_, ?_, ?_⟩
  · refine (List.nodup_finRange _).map ?_
    intro a b h
    exact σ.injective (Subtype.ext h)
  · intro ν
    rw [← hb]
    constructor
    · intro h
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
      exact (Finset.mem_filter.1 (σ i).2).2
    · intro h
      have hν : ν ∈ offsetAxes y x := by simp [offsetAxes, h]
      exact List.mem_map.2 ⟨σ.symm ⟨ν, hν⟩, List.mem_finRange _, by simp⟩
  · subst hb
    rfl
structure LevelPair (L m : ℕ) (j j' : ℤ) : Prop where
  odd : Odd L
  le_side : 13 ≤ L
  level_nonneg : 0 ≤ (m : ℤ) + j'
  coords : SublatticeCoordinates L m j'
  sq_le : (L : ℤ) * L ≤ halfPeriod L m j'
  mem_sublattice : ∀ y : Site L m j, (y : FourTorus L m) ∈ sublattice L m j'
  unitBlock_eq : ∀ y : Site L m j, unitBlock y =
    (fun p => (offsetSite (y.toSublattice j') p : FourTorus L m)) '' blockIndexBox L
  ncard_unitBlock : ∀ y : Site L m j, (unitBlock y).ncard = L ^ 4
  isSiteBox : ∀ z : Site L m j', IsSiteBox j' (sitesFromCorner z fun _ => (L : ℤ))
  toSublattice_target : ∀ (c : Bond L m j) (μ : Fin 4), c.target - c.source = unitStep L m j μ →
    c.target.toSublattice j' = c.source.toSublattice j' + blockTranslation L m j' μ
namespace LevelPair
variable (S : LevelPair L m j j')
include S
theorem two_mul_centreToFaceSteps : 2 * centreToFaceSteps L = (L : ℤ) - 1 := by
  obtain ⟨k, hk⟩ := S.odd
  have : (L : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  unfold centreToFaceSteps
  omega
theorem thirteen_le : (13 : ℤ) ≤ L := by exact_mod_cast S.le_side
theorem side_add_one_le : (L : ℤ) + 1 ≤ halfPeriod L m j' := by
  have h1 := S.sq_le
  have h2 := S.thirteen_le
  nlinarith
theorem coe_centre (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  coe_toSublattice (S.mem_sublattice y)
theorem offsetSite_mem_unitBlock (y : Site L m j) {p : Fin 4 → ℤ} (hp : p ∈ blockIndexBox L) :
    (offsetSite (y.toSublattice j') p : FourTorus L m) ∈ unitBlock y := by
  rw [S.unitBlock_eq y]
  exact ⟨p, hp, rfl⟩
theorem mem_sitesInBlock (y : Site L m j) {x : Site L m j'} :
    x ∈ sitesInBlock j' y ↔ ∃ p ∈ blockIndexBox L, x = offsetSite (y.toSublattice j') p := by
  change (x : FourTorus L m) ∈ unitBlock y ↔ _
  rw [S.unitBlock_eq y]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, Subtype.ext h.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
theorem abs_sub_lt_of_mem {a b : Fin 4 → ℤ} (ha : a ∈ blockIndexBox L)
    (hb : b ∈ blockIndexBox L) (μ : Fin 4) :
    |a μ - b μ| < 2 * (halfPeriod L m j' : ℤ) := by
  have h1 := ha μ
  have h2 := hb μ
  have h3 := S.two_mul_centreToFaceSteps
  have h4 := S.side_add_one_le
  rw [abs_lt]
  constructor <;> omega
theorem injOn_offsetSite (w : Site L m j') : InjOn (offsetSite w) (blockIndexBox L) :=
  fun _ ha _ hb h => eq_of_offsetSite_eq S.coords (S.abs_sub_lt_of_mem ha hb) h
theorem blockOffset_offsetSite (y : Site L m j) {p : Fin 4 → ℤ} (hp : p ∈ blockIndexBox L) :
    blockOffset y (offsetSite (y.toSublattice j') p) = p := by
  have hw := S.coe_centre y
  have two := S.two_mul_centreToFaceSteps
  have hd : ∀ μ, 2 * |p μ| ≤ (L : ℤ) - 1 := fun μ => by
    have h1 : |p μ| ≤ centreToFaceSteps L := abs_le.2 (hp μ)
    omega
  have hex : ∃ n, IsBlockOffset y (offsetSite (y.toSublattice j') p) n :=
    ⟨p, (isBlockOffset_iff hw p).2 ⟨rfl, hd⟩⟩
  have hs : IsBlockOffset y (offsetSite (y.toSublattice j') p)
      (blockOffset y (offsetSite (y.toSublattice j') p)) :=
    Classical.epsilon_spec hex
  obtain ⟨h1, h2⟩ := (isBlockOffset_iff hw _).1 hs
  have hq : blockOffset y (offsetSite (y.toSublattice j') p) ∈ blockIndexBox L :=
    fun μ => by
      have h3 := h2 μ
      exact abs_le.1 (by omega)
  exact S.injOn_offsetSite _ hq hp h1.symm
theorem meshSize_pos : 0 < meshSize L j' := by
  have h : 0 < L := by
    have := S.le_side
    omega
  exact zpow_pos (by exact_mod_cast h) _
theorem torusSide_half : torusSide L m / 2 = (halfPeriod L m j' : ℝ) * meshSize L j' := by
  obtain ⟨h1, -⟩ := S.coords
  rw [div_eq_iff S.meshSize_pos.ne'] at h1
  rw [h1]
  push_cast
  ring
theorem isChartOffset_of_small {o x : Site L m j'} {d : Fin 4 → ℤ} (hx : x = offsetSite o d)
    (hd : ∀ μ, |d μ| < (halfPeriod L m j' : ℤ)) : IsChartOffset o x d := by
  refine ⟨by rw [hx]; simp [offsetSite], fun μ => ?_⟩
  rw [S.torusSide_half]
  have h3 : ((|d μ| : ℤ) : ℝ) < (halfPeriod L m j' : ℝ) := by exact_mod_cast hd μ
  exact mul_lt_mul_of_pos_right h3 S.meshSize_pos
theorem chartOffset_eq {o x : Site L m j'} {d : Fin 4 → ℤ}
    (hx : x = offsetSite o d) (hd : ∀ μ, |d μ| < (halfPeriod L m j' : ℤ)) :
    chartOffset o x = d := by
  have hs : IsChartOffset o x (chartOffset o x) :=
    Classical.epsilon_spec ⟨d, S.isChartOffset_of_small hx hd⟩
  obtain ⟨h1, h2⟩ := hs
  have hbound : ∀ μ, |chartOffset o x μ| < (halfPeriod L m j' : ℤ) := fun μ => by
    have h3 := h2 μ
    rw [S.torusSide_half] at h3
    have h4 := lt_of_mul_lt_mul_right h3 S.meshSize_pos.le
    exact_mod_cast h4
  have he : offsetSite o (chartOffset o x) = offsetSite o d := by
    rw [← hx]
    simp only [offsetSite] at h1 ⊢
    rw [← h1]
    abel
  refine eq_of_offsetSite_eq S.coords (fun μ => ?_) he
  have h3 := hbound μ
  have h4 := hd μ
  rw [abs_lt] at h3 h4 ⊢
  constructor <;> omega
theorem coordinateComb_eq {o x : Site L m j'} {d : Fin 4 → ℤ} (hx : x = offsetSite o d)
    (hd : ∀ μ, |d μ| < (halfPeriod L m j' : ℤ)) :
    coordinateComb o x = stepsThroughAxes d o [3, 2, 1, 0] := by
  unfold coordinateComb
  rw [S.chartOffset_eq hx hd]
omit S in
theorem blockCorner_eq (y : Site L m j) :
    blockAnchor j' y = offsetSite (y.toSublattice j') fun _ => -centreToFaceSteps L := by
  show y.toSublattice j' - centreToFaceSteps L • ∑ μ, unitStep L m j' μ =
    y.toSublattice j' + ∑ μ, (-centreToFaceSteps L) • unitStep L m j' μ
  rw [Finset.smul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [neg_smul]
theorem contourCoordinates (y : Site L m j) {p : Fin 4 → ℤ} (hp : p ∈ blockIndexBox L) :
    ContourCoordinates y (offsetSite (y.toSublattice j') p) p := by
  intro Γ hΓ
  have two := S.two_mul_centreToFaceSteps
  have t13 := S.thirteen_le
  have big := S.side_add_one_le
  obtain ⟨l, hl, hmem, rfl⟩ := exists_of_mem_contourSet hΓ (S.blockOffset_offsetSite y hp)
  have hoff : ∀ ν, ν ∉ l → p ν = 0 := fun ν hν => by
    by_contra h
    exact hν ((hmem ν).2 h)
  have hlead : Joins (stepsThroughAxes p (y.toSublattice j') l) (y.toSublattice j')
      (offsetSite (y.toSublattice j') p) := by
    have := joins_stepsThroughAxes p (y.toSublattice j') l
    rwa [add_sum_eq_offsetSite _ _ hl hoff] at this
  have hsites : ∀ z ∈ sitesOfPath (y.toSublattice j') (stepsThroughAxes p (y.toSublattice j') l),
      (z : FourTorus L m) ∈ unitBlock y := by
    intro z hz
    have hz' : z ∈ sitesOfPath (offsetSite (y.toSublattice j') 0)
        (stepsThroughAxes p (offsetSite (y.toSublattice j') 0) l) := by
      rwa [offsetSite_zero]
    have h0 : ∀ ν, (fun _ => -centreToFaceSteps L : Fin 4 → ℤ) ν ≤ (0 : Fin 4 → ℤ) ν ∧
        (0 : Fin 4 → ℤ) ν ≤ (fun _ => centreToFaceSteps L : Fin 4 → ℤ) ν := fun ν => by
      simp only [Pi.zero_apply]
      omega
    have h1 : ∀ ν, (fun _ => -centreToFaceSteps L : Fin 4 → ℤ) ν ≤ (0 : Fin 4 → ℤ) ν + p ν ∧
        (0 : Fin 4 → ℤ) ν + p ν ≤ (fun _ => centreToFaceSteps L : Fin 4 → ℤ) ν := fun ν => by
      simpa using hp ν
    obtain ⟨q, hq, rfl⟩ := exists_offset_of_mem_pathSites hl h0 h1 hz'
    exact S.offsetSite_mem_unitBlock y hq
  refine ⟨hlead.isBondPathFromTo, fun ν h0 => ⟨?_, abs_le.2 (hp ν)⟩, fun b hb => ?_, hsites,
    fun b hb => ⟨hsites _ (hlead.mem_pathSites hb).1, hsites _ (hlead.mem_pathSites hb).2⟩⟩
  · exact countSteps_stepsThroughAxes S.coords (by omega) p _ hl ((hmem ν).2 h0) h0
  · obtain ⟨ν, -, h0, hd⟩ := target_sub_source_of_mem_stepsThroughAxes hb
    exact ⟨ν, h0, hd⟩
theorem offsetSite_from_corner (y : Site L m j) {p : Fin 4 → ℤ} (hp : p ∈ blockIndexBox L) :
    offsetSite (y.toSublattice j') p =
        offsetSite (blockAnchor j' y) (fun ν => p ν + centreToFaceSteps L) ∧
      (∀ ν, 0 ≤ p ν + centreToFaceSteps L ∧ p ν + centreToFaceSteps L ≤ (L : ℤ) - 1) ∧
      ∀ ν, |p ν + centreToFaceSteps L| < (halfPeriod L m j' : ℤ) := by
  have two := S.two_mul_centreToFaceSteps
  have big := S.side_add_one_le
  have h0 : ∀ ν, 0 ≤ p ν + centreToFaceSteps L ∧ p ν + centreToFaceSteps L ≤ (L : ℤ) - 1 :=
    fun ν => by
      have := hp ν
      omega
  refine ⟨?_, h0, fun ν => ?_⟩
  · rw [blockCorner_eq, offsetSite_offsetSite]
    congr 1
    funext ν
    simp
  · have := h0 ν
    rw [abs_lt]
    constructor <;> omega
theorem coordinateComb_blockCorner (y : Site L m j) {p : Fin 4 → ℤ} (hp : p ∈ blockIndexBox L) :
    coordinateComb (blockAnchor j' y) (offsetSite (y.toSublattice j') p) =
      stepsThroughAxes (fun ν => p ν + centreToFaceSteps L) (blockAnchor j' y) [3, 2, 1, 0] :=
  S.coordinateComb_eq (S.offsetSite_from_corner y hp).1 (S.offsetSite_from_corner y hp).2.2
theorem cornerCombCoordinates (y : Site L m j) {p : Fin 4 → ℤ} (hp : p ∈ blockIndexBox L) :
    CornerCombCoordinates y (offsetSite (y.toSublattice j') p) p := by
  have two := S.two_mul_centreToFaceSteps
  have t13 := S.thirteen_le
  have big := S.side_add_one_le
  obtain ⟨hx, hd0, hdH⟩ := S.offsetSite_from_corner y hp
  have hc := S.coordinateComb_blockCorner y hp
  have hl : ([3, 2, 1, 0] : List (Fin 4)).Nodup := by decide
  have hall : ∀ ν : Fin 4, ν ∈ ([3, 2, 1, 0] : List (Fin 4)) := by decide
  have ho := blockCorner_eq (j' := j') y
  unfold CornerCombCoordinates
  rw [hc]
  generalize hdd : (fun ν => p ν + centreToFaceSteps L) = d at hx hc ⊢
  have hdν : ∀ ν, d ν = p ν + centreToFaceSteps L := fun ν => by rw [← hdd]
  generalize hoo : blockAnchor j' y = o at hx hc ho ⊢
  generalize hxx : offsetSite (y.toSublattice j') p = x at hx hc ⊢
  have hlead : Joins (stepsThroughAxes d o [3, 2, 1, 0]) o x := by
    have := joins_stepsThroughAxes d o [3, 2, 1, 0]
    rwa [add_sum_eq_offsetSite _ _ hl (fun ν hν => absurd (hall ν) hν), ← hx] at this
  have hdH' : ∀ ν, |d ν| < (halfPeriod L m j' : ℤ) := fun ν => by
    rw [hdν]
    exact hdH ν
  have hsites : ∀ z ∈ sitesOfPath o (stepsThroughAxes d o [3, 2, 1, 0]),
      (z : FourTorus L m) ∈ unitBlock y := by
    intro z hz
    rw [ho] at hz
    have h0 : ∀ ν, (fun _ => -centreToFaceSteps L : Fin 4 → ℤ) ν ≤
          (fun _ => -centreToFaceSteps L : Fin 4 → ℤ) ν ∧
        (fun _ => -centreToFaceSteps L : Fin 4 → ℤ) ν ≤
          (fun _ => centreToFaceSteps L : Fin 4 → ℤ) ν := fun ν => by
      dsimp only
      constructor <;> omega
    have h1 : ∀ ν, (fun _ => -centreToFaceSteps L : Fin 4 → ℤ) ν ≤
          (fun _ => -centreToFaceSteps L : Fin 4 → ℤ) ν + d ν ∧
        (fun _ => -centreToFaceSteps L : Fin 4 → ℤ) ν + d ν ≤
          (fun _ => centreToFaceSteps L : Fin 4 → ℤ) ν := fun ν => by
      have := hd0 ν
      have := hdν ν
      dsimp only
      constructor <;> omega
    obtain ⟨q, hq, rfl⟩ := exists_offset_of_mem_pathSites hl h0 h1 hz
    exact S.offsetSite_mem_unitBlock y hq
  have hpos : ∀ b ∈ stepsThroughAxes d o [3, 2, 1, 0], ∃ ν, d ν ≠ 0 ∧ 0 < d ν ∧
      b.target - b.source = unitStep L m j' ν ∧
        b.target - b.source = (d ν).sign • unitStep L m j' ν := by
    intro b hb
    obtain ⟨κ, -, hk0, hd⟩ := target_sub_source_of_mem_stepsThroughAxes hb
    have hk : 0 < d κ := by
      have := hd0 κ
      have := hdν κ
      omega
    refine ⟨κ, hk0, hk, ?_, hd⟩
    rw [hd, Int.sign_eq_one_of_pos hk, one_smul]
  refine ⟨⟨_, S.isSiteBox o, ⟨0, fun ν => ⟨le_rfl, by simp only [Pi.zero_apply]; omega⟩,
      (offsetSite_zero o).symm⟩,
      ⟨d, fun ν => ?_, hx⟩⟩, S.isChartOffset_of_small hx hdH', hlead.isBondPathFromTo,
    fun ν => ⟨?_, (hd0 ν).2⟩,
    fun b hb => ?_, hsites,
    fun b hb => ⟨hsites _ (hlead.mem_pathSites hb).1, hsites _ (hlead.mem_pathSites hb).2⟩⟩
  · have := hd0 ν
    have := hdν ν
    show 0 ≤ d ν ∧ d ν < (L : ℤ)
    constructor <;> omega
  · rw [← hdν ν]
    by_cases h0 : d ν = 0
    · rw [h0]
      refine countSteps_of_forall_ne fun b hb => ?_
      obtain ⟨κ, hk0, -, -, hd⟩ := hpos b hb
      rw [hd]
      intro he
      have hone : (d κ).sign • unitStep L m j' κ = (1 : ℤ) • unitStep L m j' ν := by
        rw [he, one_smul]
      have hs : |(d κ).sign| < (halfPeriod L m j' : ℤ) := by
        rw [(sign_ne_zero_and_abs_eq_one hk0).2]
        omega
      have h1 : |(1 : ℤ)| < (halfPeriod L m j' : ℤ) := by
        rw [abs_one]
        omega
      have := (zsmul_unitStep_inj S.coords hs h1 hone (sign_ne_zero_and_abs_eq_one hk0).1).1
      exact hk0 (this ▸ h0)
    · have hp0 : 0 < d ν := by
        have := hd0 ν
        have := hdν ν
        omega
      have := countSteps_stepsThroughAxes S.coords (by omega) d o hl (hall ν) h0
      rw [Int.sign_eq_one_of_pos hp0, one_smul] at this
      rw [this]
      omega
  · obtain ⟨κ, -, -, hd, -⟩ := hpos b hb
    exact ⟨κ, hd⟩
theorem blockCoordinates (y : Site L m j) : BlockCoordinates j' y := by
  have two := S.two_mul_centreToFaceSteps
  have t13 := S.thirteen_le
  refine ⟨⟨S.injOn_offsetSite _, (S.unitBlock_eq y).symm⟩, S.ncard_unitBlock y, ?_⟩
  rw [blockCorner_eq]
  exact S.offsetSite_mem_unitBlock y fun ν => by constructor <;> omega
theorem monotone_unitBlock (y : Site L m j) :
    MonotonePathsRemainIn (y.toSublattice j') (blockIndexBox L) (unitBlock y) :=
  monotonePathsRemainIn_of_box (fun _ => -centreToFaceSteps L) (fun _ => centreToFaceSteps L)
    (fun _ => Iff.rfl) fun _ hp => S.offsetSite_mem_unitBlock y hp
omit S in
theorem mem_doubleBlockIndexBox_iff (μ : Fin 4) (p : Fin 4 → ℤ) :
    p ∈ doubleBlockIndexBox L μ ↔ ∀ ν, -centreToFaceSteps L ≤ p ν ∧
      p ν ≤ if ν = μ then centreToFaceSteps L + L else centreToFaceSteps L := by
  constructor
  · rintro ⟨a, b, c⟩ ν
    by_cases e : ν = μ
    · subst e
      simp [a, b]
    · have := abs_le.1 (c ν e)
      simp [e, this.1, this.2]
  · intro h
    refine ⟨(h μ).1, by simpa using (h μ).2, fun ν e => abs_le.2 ?_⟩
    simpa [e] using h ν
omit S in
theorem offsetSite_add_blockTranslation (w : Site L m j') (p : Fin 4 → ℤ) (μ : Fin 4) :
    offsetSite w p + blockTranslation L m j' μ =
      offsetSite w (p + Pi.single μ (L : ℤ)) := by
  rw [← offsetSite_offsetSite, offsetSite_single]
  rfl
theorem offsetSite_target {c : Bond L m j} {μ : Fin 4}
    (hcμ : c.target - c.source = unitStep L m j μ) (p : Fin 4 → ℤ) :
    offsetSite (c.target.toSublattice j') p =
      offsetSite (c.source.toSublattice j') p + blockTranslation L m j' μ := by
  rw [S.toSublattice_target c μ hcμ, offsetSite_add_base]
theorem blockCorner_target {c : Bond L m j} {μ : Fin 4}
    (hcμ : c.target - c.source = unitStep L m j μ) :
    blockAnchor j' c.target = blockAnchor j' c.source + blockTranslation L m j' μ := by
  rw [blockCorner_eq, blockCorner_eq, S.offsetSite_target hcμ]
theorem shiftAcross_eq {c : Bond L m j} {μ : Fin 4} (hcμ : c.target - c.source = unitStep L m j μ)
    (x : Site L m j') : shiftAcross c x = x + blockTranslation L m j' μ := by
  unfold shiftAcross
  congr 1
  apply Subtype.ext
  rw [coe_toSublattice (S.mem_sublattice _)]
  have e : ((c.target.toSublattice j' : Site L m j') : FourTorus L m) =
      ((c.source.toSublattice j' : Site L m j') : FourTorus L m) +
        ((blockTranslation L m j' μ : Site L m j') : FourTorus L m) := by
    rw [S.toSublattice_target c μ hcμ]
    rfl
  rw [S.coe_centre, S.coe_centre] at e
  rw [AddSubgroup.coe_sub, e]
  abel
omit S in
theorem add_single_mem_doubleBlockIndexBox {p : Fin 4 → ℤ} (hp : p ∈ blockIndexBox L)
    (μ : Fin 4) {i : ℤ} (h0 : 0 ≤ i) (h1 : i ≤ L) :
    p + Pi.single μ i ∈ doubleBlockIndexBox L μ := by
  refine ⟨?_, ?_, fun ν e => abs_le.2 ?_⟩
  · have := (hp μ).1
    simp only [Pi.add_apply, Pi.single_eq_same]
    omega
  · have := (hp μ).2
    simp only [Pi.add_apply, Pi.single_eq_same]
    omega
  · simpa [Pi.single_eq_of_ne e] using hp ν
theorem image_doubleBlockIndexBox {c : Bond L m j} {μ : Fin 4}
    (hcμ : c.target - c.source = unitStep L m j μ) :
    (fun p => (offsetSite (c.source.toSublattice j') p : FourTorus L m)) ''
      doubleBlockIndexBox L μ = bondDoubleBlock c := by
  have two := S.two_mul_centreToFaceSteps
  ext z
  constructor
  · rintro ⟨p, ⟨a, b, c'⟩, rfl⟩
    by_cases e : p μ ≤ centreToFaceSteps L
    · refine Or.inl (S.offsetSite_mem_unitBlock c.source fun ν => ?_)
      by_cases eν : ν = μ
      · subst eν
        exact ⟨a, e⟩
      · exact abs_le.1 (c' ν eν)
    · have hq : p - Pi.single μ (L : ℤ) ∈ blockIndexBox L := by
        intro ν
        by_cases eν : ν = μ
        · subst eν
          simp only [Pi.sub_apply, Pi.single_eq_same]
          constructor <;> omega
        · simpa [Pi.single_eq_of_ne eν] using abs_le.1 (c' ν eν)
      have := S.offsetSite_mem_unitBlock c.target hq
      rw [S.offsetSite_target hcμ, offsetSite_add_blockTranslation, sub_add_cancel] at this
      exact Or.inr this
  · rintro (h | h)
    · rw [S.unitBlock_eq] at h
      obtain ⟨p, hp, rfl⟩ := h
      have := add_single_mem_doubleBlockIndexBox hp μ le_rfl (Int.natCast_nonneg L)
      simp only [Pi.single_zero, add_zero] at this
      exact ⟨p, this, rfl⟩
    · rw [S.unitBlock_eq] at h
      obtain ⟨p, hp, rfl⟩ := h
      refine ⟨p + Pi.single μ (L : ℤ),
        add_single_mem_doubleBlockIndexBox hp μ (Int.natCast_nonneg L) le_rfl, ?_⟩
      beta_reduce
      rw [S.offsetSite_target hcμ, offsetSite_add_blockTranslation]
theorem doubleBlockCoordinates (c : Bond L m j) (μ : Fin 4)
    (hcμ : c.target - c.source = unitStep L m j μ) :
    DoubleBlockCoordinates j' c μ := by
  have two := S.two_mul_centreToFaceSteps
  have big := S.side_add_one_le
  refine ⟨S.toSublattice_target c μ hcμ, S.blockCorner_target hcμ, ?_, ?_,
    fun x _ => S.shiftAcross_eq hcμ x,
    fun a ha b hb h => eq_of_offsetSite_eq S.coords (fun ν => ?_) h,
    S.image_doubleBlockIndexBox hcμ⟩
  · rw [S.unitBlock_eq c.target, S.unitBlock_eq c.source, image_image]
    refine image_congr fun p _ => ?_
    rw [S.offsetSite_target hcμ]
    rfl
  · ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨p, hp, rfl⟩ := (S.mem_sitesInBlock _).1 hx
      exact (S.mem_sitesInBlock _).2 ⟨p, hp, (S.offsetSite_target hcμ p).symm⟩
    · intro hx
      obtain ⟨p, hp, rfl⟩ := (S.mem_sitesInBlock _).1 hx
      exact ⟨_, (S.mem_sitesInBlock _).2 ⟨p, hp, rfl⟩, (S.offsetSite_target hcμ p).symm⟩
  · have ha' := (mem_doubleBlockIndexBox_iff μ a).1 ha ν
    have hb' := (mem_doubleBlockIndexBox_iff μ b).1 hb ν
    rw [abs_lt]
    split_ifs at ha' hb' <;> constructor <;> omega
theorem monotone_bondDoubleBlock (c : Bond L m j) (μ : Fin 4)
    (hcμ : c.target - c.source = unitStep L m j μ) :
    MonotonePathsRemainIn (c.source.toSublattice j') (doubleBlockIndexBox L μ)
      (bondDoubleBlock c) :=
  monotonePathsRemainIn_of_box (fun _ => -centreToFaceSteps L)
    (fun ν => if ν = μ then centreToFaceSteps L + L else centreToFaceSteps L)
    (mem_doubleBlockIndexBox_iff μ) fun p hp => by
      rw [← S.image_doubleBlockIndexBox hcμ]
      exact ⟨p, hp, rfl⟩
theorem contoursAndCombsTranslate (c : Bond L m j) (μ : Fin 4)
    (hcμ : c.target - c.source = unitStep L m j μ) :
    ContoursAndCombsTranslate j' c μ := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := (S.mem_sitesInBlock _).1 hx
  rw [← S.offsetSite_target hcμ p]
  have e1 := S.blockOffset_offsetSite c.source hp
  have e2 := S.blockOffset_offsetSite c.target hp
  have eS : offsetAxes c.source (offsetSite (c.source.toSublattice j') p) =
      offsetAxes c.target (offsetSite (c.target.toSublattice j') p) := by
    simp only [offsetAxes, e1, e2]
  refine ⟨?_, ?_⟩
  · ext Γ
    constructor
    · rintro ⟨Γ₀, ⟨σ, rfl⟩, rfl⟩
      obtain ⟨σ', hσ⟩ := exists_axisList_eq eS σ
      refine ⟨σ', ?_⟩
      beta_reduce
      rw [orderedContour_eq, orderedContour_eq, hσ, e1, e2, translatePath_stepsThroughAxes,
        S.toSublattice_target c μ hcμ]
    · rintro ⟨σ', rfl⟩
      obtain ⟨σ, hσ⟩ := exists_axisList_eq eS.symm σ'
      refine ⟨_, ⟨σ, rfl⟩, ?_⟩
      beta_reduce
      rw [orderedContour_eq, orderedContour_eq, hσ, e1, e2, translatePath_stepsThroughAxes]
      exact congrArg (fun w => stepsThroughAxes p w (axisList σ'))
        (S.toSublattice_target c μ hcμ).symm
  · rw [S.coordinateComb_blockCorner c.source hp, S.coordinateComb_blockCorner c.target hp,
      translatePath_stepsThroughAxes, S.blockCorner_target hcμ]
theorem side_zpow_eq : (L : ℝ) ^ ((m : ℤ) + j') = (halfPeriod L m j' : ℝ) := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le S.level_nonneg
  simp [halfPeriod, hk]
theorem isAxialDisplacement (x : Site L m j') (μ : Fin 4) :
    IsAxialDisplacement x (x + blockTranslation L m j' μ) μ (L : ℤ) := by
  refine ⟨by simp [blockTranslation], ?_⟩
  rw [S.side_zpow_eq]
  have big := S.side_add_one_le
  have : |(L : ℤ)| < (halfPeriod L m j' : ℤ) := by
    rw [abs_of_nonneg (Int.natCast_nonneg L)]
    omega
  exact_mod_cast this
theorem axialPath_eq (x : Site L m j') (μ : Fin 4) :
    axialPath x (x + blockTranslation L m j' μ) = forwardAxisPath x μ L := by
  have big := S.side_add_one_le
  have t13 := S.thirteen_le
  have hL : |(L : ℤ)| < (halfPeriod L m j' : ℤ) := by
    rw [abs_of_nonneg (Int.natCast_nonneg L)]
    omega
  have key : ∀ q : Fin 4 × ℤ, IsAxialDisplacement x (x + blockTranslation L m j' μ) q.1 q.2 →
      q = (μ, (L : ℤ)) := by
    rintro ⟨ν, a⟩ ⟨h1, h2⟩
    rw [S.side_zpow_eq] at h2
    have ha : |a| < (halfPeriod L m j' : ℤ) := by exact_mod_cast h2
    have hs : (L : ℤ) • unitStep L m j' μ = a • unitStep L m j' ν := by
      rw [← h1]
      simp [blockTranslation]
    obtain ⟨rfl, rfl⟩ := zsmul_unitStep_inj S.coords hL ha hs (by omega)
    rfl
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x (x + blockTranslation L m j' μ) q.1 q.2 :=
    ⟨(μ, (L : ℤ)), S.isAxialDisplacement x μ⟩
  unfold axialPath
  rw [dif_pos hex, key _ hex.choose_spec]
  simp [flowAlong]
theorem crossingPath_eq {c : Bond L m j} {μ : Fin 4}
    (hcμ : c.target - c.source = unitStep L m j μ)
    (x : Site L m j') : crossingPath c x = forwardAxisPath x μ L := by
  unfold crossingPath
  rw [S.shiftAcross_eq hcμ, S.axialPath_eq]
theorem add_zsmul_mem_bondDoubleBlock {c : Bond L m j} {μ : Fin 4}
    (hcμ : c.target - c.source = unitStep L m j μ)
    {x : Site L m j'} (hx : x ∈ sitesInBlock j' c.source) {i : ℕ} (hi : i ≤ L) :
    ((x + (i : ℤ) • unitStep L m j' μ : Site L m j') : FourTorus L m) ∈ bondDoubleBlock c := by
  obtain ⟨p, hp, rfl⟩ := (S.mem_sitesInBlock _).1 hx
  rw [← S.image_doubleBlockIndexBox hcμ]
  refine ⟨p + Pi.single μ (i : ℤ), add_single_mem_doubleBlockIndexBox hp μ
    (Int.natCast_nonneg i) (by exact_mod_cast hi), ?_⟩
  beta_reduce
  rw [← offsetSite_offsetSite, offsetSite_single]
theorem doubleBlockAxialPaths (c : Bond L m j) (μ : Fin 4)
    (hcμ : c.target - c.source = unitStep L m j μ) :
    DoubleBlockAxialPaths j' c μ := by
  refine ⟨fun x hx => ⟨S.isAxialDisplacement x μ, S.crossingPath_eq hcμ x, fun z => ?_,
    fun i hi => S.add_zsmul_mem_bondDoubleBlock hcμ hx hi⟩, ?_, ?_⟩
  · rw [S.crossingPath_eq hcμ]
    exact mem_pathSites_forwardFlow
  · rw [S.crossingPath_eq hcμ, S.toSublattice_target c μ hcμ, S.axialPath_eq]
  · rw [S.crossingPath_eq hcμ, S.blockCorner_target hcμ, S.axialPath_eq]
theorem pathsInsideDoubleBlock (c : Bond L m j) (μ : Fin 4)
    (hcμ : c.target - c.source = unitStep L m j μ) :
    PathsInsideDoubleBlock j' c := by
  refine ⟨fun y hy x hx => ?_, fun x hx b hb => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := (S.mem_sitesInBlock _).1 hx
    have sub : unitBlock y ⊆ bondDoubleBlock c := by
      rcases hy with rfl | rfl
      · exact subset_union_left
      · exact subset_union_right
    refine ⟨fun Γ hΓ b hb => ?_, fun b hb => ?_⟩
    · have h := (S.contourCoordinates y hp Γ hΓ).2.2.2.2 b hb
      exact ⟨sub h.1, sub h.2⟩
    · have h := (S.cornerCombCoordinates y hp).2.2.2.2.2.2 b hb
      exact ⟨sub h.1, sub h.2⟩
  · rw [S.crossingPath_eq hcμ] at hb
    have hl := (joins_forwardFlow x μ L).mem_pathSites hb
    obtain ⟨i, hi, h1⟩ := mem_pathSites_forwardFlow.1 hl.1
    obtain ⟨i', hi', h2⟩ := mem_pathSites_forwardFlow.1 hl.2
    exact ⟨h1 ▸ S.add_zsmul_mem_bondDoubleBlock hcμ hx hi,
      h2 ▸ S.add_zsmul_mem_bondDoubleBlock hcμ hx hi'⟩
end LevelPair
theorem unitBlock_facts {j j' : ℤ} (hj : j + ((1 : ℕ) : ℤ) = j')
    (hb : RefinedBlockCoordinates L m j 1)
    (hQ : blockOffsets L 1 = blockIndexBox L) (y : Site L m j) :
    (y : FourTorus L m) ∈ sublattice L m j' ∧
      unitBlock y = (fun p => (offsetSite (y.toSublattice j') p : FourTorus L m)) ''
        blockIndexBox L ∧
      (unitBlock y).ncard = L ^ 4 := by
  subst hj
  obtain ⟨h1, h2, -, h4, -⟩ := hb y
  refine ⟨h1, ?_, by simpa using h4⟩
  rw [← hQ]
  exact h2
theorem levelPair (h₁ : CoordinateDescription)
    (h₂ : CornerBoxProperties) {L m K n : ℕ} (hodd : Odd L) (h13 : 13 ≤ L)
    (hm : 0 < m) (hn : n < K) : LevelPair L m (levelDepth K (n + 1)) (levelDepth K n) := by
  obtain ⟨a1, a2, a3, -⟩ := h₁ L m hodd h13 hm
  have hK : 0 < K := by omega
  have hdepth : levelDepth K (n + 1) + ((1 : ℕ) : ℤ) = levelDepth K n := by
    simp only [levelDepth]
    push_cast
    ring
  have hlow : -(m : ℤ) ≤ levelDepth K (n + 1) := by
    simp only [levelDepth]
    omega
  have hlow' : -(m : ℤ) ≤ levelDepth K n := by
    simp only [levelDepth]
    omega
  have two : 2 * centreToFaceSteps L = (L : ℤ) - 1 := by
    obtain ⟨k, hk⟩ := hodd
    have : (L : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    unfold centreToFaceSteps
    omega
  have hQ : blockOffsets L 1 = blockIndexBox L := by
    ext p
    constructor
    · intro h ν
      have h1 := h ν
      rw [pow_one] at h1
      exact abs_le.1 (by omega)
    · intro h ν
      have h1 : |p ν| ≤ centreToFaceSteps L := abs_le.2 (h ν)
      rw [pow_one]
      omega
  have hexp : ((m : ℤ) + levelDepth K n).toNat = m + K - n := by
    simp only [levelDepth]
    omega
  have hpow : L ^ 2 ≤ L ^ (m + K - n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hbl := unitBlock_facts hdepth (a3 (levelDepth K (n + 1)) 1 hlow) hQ
  refine
    { odd := hodd
      le_side := h13
      level_nonneg := by omega
      coords := a1 _ hlow'
      sq_le := ?_
      mem_sublattice := fun y => (hbl y).1
      unitBlock_eq := fun y => (hbl y).2.1
      ncard_unitBlock := fun y => (hbl y).2.2
      isSiteBox := fun z => ?_
      toSublattice_target := fun c μ hcμ => ?_ }
  · unfold halfPeriod
    rw [hexp]
    have : L * L ≤ L ^ (m + K - n) := by
      rw [← pow_two]
      exact hpow
    exact_mod_cast this
  · refine ((h₂ L m K ⟨hodd, h13⟩ hm hK n hn.le).1 z fun _ => (L : ℤ)) (fun _ => ⟨?_, ?_⟩) |>.1
    · omega
    · have h3 : L < L ^ (m + K - n) := by
        have : L ^ 1 < L ^ 2 := Nat.pow_lt_pow_right (by omega) (by omega)
        rw [pow_one] at this
        exact this.trans_le hpow
      exact_mod_cast h3
  · exact (a2 K n hK hn.le).2.2.2.2 hn c μ hcμ
theorem statement_holds (h₁ : CoordinateDescription)
    (h₂ : CornerBoxProperties) : Statement := by
  intro L m K hodd h13 hm n hn
  have S := levelPair h₁ h₂ (n := n) hodd h13 hm hn
  exact ⟨fun y => ⟨S.blockCoordinates y, S.monotone_unitBlock y,
      fun p hp => ⟨S.contourCoordinates y hp, S.cornerCombCoordinates y hp⟩⟩,
    fun c μ hcμ => ⟨S.doubleBlockCoordinates c μ hcμ, S.monotone_bondDoubleBlock c μ hcμ,
      S.contoursAndCombsTranslate c μ hcμ, S.doubleBlockAxialPaths c μ hcμ,
      S.pathsInsideDoubleBlock c μ hcμ⟩⟩
end YangMills.Construction.PeriodicLattice.BlockPaths
