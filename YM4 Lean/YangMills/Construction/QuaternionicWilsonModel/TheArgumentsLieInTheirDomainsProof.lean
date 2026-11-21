import YangMills.Construction.Continuum.ArgumentsOfTheConditionsLieInTheirDomainsAndTheirSumsAreFiniteProof
import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuples
import YangMills.Construction.Continuum.LinearCombinationsAndTensorsLieInTheFlatSpaces
import YangMills.Construction.Continuum.TheThreeOpenSetsAndTheThreeSpaces
import YangMills.Construction.QuaternionicWilsonModel.TheArgumentsLieInTheirDomains
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction.ConditionDomains
open ConfigSpace SystemsWithFiveBounds
open SeparatedTuples (TupleFunctional)
def zeroBeyondDegreeZero : FlatSequence
  | 0 => fun c => show ℂ from c.1
  | _ + 1 => fun _ => 0
theorem isLinearFunctionalSeq_zeroBeyondDegreeZero : IsLinearFunctionalSeq zeroBeyondDegreeZero :=
  ⟨fun _ => rfl, fun m c c' φ ψ χ _ => by
    simp [FlatSequence.atSucc, zeroBeyondDegreeZero]⟩
theorem evalAt_zeroOfDegree {S : FlatSequence} (hseq : IsLinearFunctionalSeq S) {n : ℕ}
    (h0 : zeroOfDegree n ∈ flatOffDiagonalAt n) : S.evalAt (zeroOfDegree n) = 0 := by
  rw [FlatSequence.evalAt_of_mem S h0]
  cases n with
  | zero => exact hseq.1 ⟨zeroOfDegree 0, h0⟩
  | succ m =>
    have h := hseq.2 m 0 0 ⟨zeroOfDegree (m + 1), h0⟩ ⟨zeroOfDegree (m + 1), h0⟩
      ⟨zeroOfDegree (m + 1), h0⟩ (by
        funext y
        show (0 : ℂ) = 0 * 0 + 0 * 0
        simp)
    exact show S.atSucc m ⟨zeroOfDegree (m + 1), h0⟩ = 0 from by simpa using h
theorem reflectionPairing_eq_pairedValueSum {T : FlatSequence} (hseq : IsLinearFunctionalSeq T)
    {φ ψ : (q : ℕ) → FnOrScalar q}
    (h : ∀ q q' : ℕ, tensorAt (flipConjAt (φ q)) (ψ q') ∈
      flatOffDiagonalAt (q + q')) {N : ℕ} (hφ : ∀ q, N ≤ q → φ q = zeroOfDegree q)
    (hψ : ∀ q, N ≤ q → ψ q = zeroOfDegree q) :
    T.reflectionPairing φ ψ = pairedValueSum T h N := by
  unfold FlatSequence.reflectionPairing pairedValueSum
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N ×ˢ Finset.range N)]
  · exact Finset.sum_congr rfl fun p _ => FlatSequence.evalAt_of_mem T (h p.1 p.2)
  · intro p hp
    by_contra hn
    apply hp
    have h0 := h p.1 p.2
    have hcase : N ≤ p.1 ∨ N ≤ p.2 := by
      by_contra hc
      exact hn (by simpa using ⟨not_le.1 fun e => hc (Or.inl e), not_le.1 fun e => hc (Or.inr e)⟩)
    rcases hcase with hc | hc
    · rw [hφ _ hc, flipConjAt_zeroOfDegree, tensorAt_zero_left] at h0
      show T.evalAt _ = 0
      rw [hφ _ hc, flipConjAt_zeroOfDegree, tensorAt_zero_left]
      exact evalAt_zeroOfDegree hseq h0
    · rw [hψ _ hc, tensorAt_zero_right] at h0
      show T.evalAt _ = 0
      rw [hψ _ hc, tensorAt_zero_right]
      exact evalAt_zeroOfDegree hseq h0
theorem finsum_evalAt_eq_sum_range {T : FlatSequence} (hseq : IsLinearFunctionalSeq T)
    {φ : (q : ℕ) → FnOrScalar q} (h : ∀ q : ℕ, φ q ∈ flatOffDiagonalAt q) {N : ℕ}
    (hφ : ∀ q, N ≤ q → φ q = zeroOfDegree q) :
    ∑ᶠ q : ℕ, T.evalAt (φ q) = ∑ q ∈ Finset.range N, T q ⟨_, h q⟩ := by
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
  · exact Finset.sum_congr rfl fun q _ => FlatSequence.evalAt_of_mem T (h q)
  · intro q hq
    by_contra hn
    apply hq
    have hc : N ≤ q := by simpa using hn
    have h0 := h q
    rw [hφ _ hc] at h0
    show T.evalAt _ = 0
    rw [hφ _ hc]
    exact evalAt_zeroOfDegree hseq h0
theorem exists_degree_bound {Φ : PosTimeSeq} (hΦ : PosTimeSeq.IsFinitelySupported Φ) :
    ∃ N : ℕ, ∀ q, N ≤ q → (Φ q).1 = zeroOfDegree q := by
  obtain ⟨b, hb⟩ := hΦ.bddAbove
  refine ⟨b + 1, fun q hq => ?_⟩
  by_contra hn
  have : q ≤ b := hb hn
  omega
theorem domainsContainArguments_of
    (hA : domainsAndFiniteSumsStatement)
    (hL : FlatSpaceClosure) : DomainsContainArguments where
  seminorm_finite m φ k hk := φ.2.1.2 k hk
  motion_mem m φ r := ((hA zeroBeyondDegreeZero isLinearFunctionalSeq_zeroBeyondDegreeZero).1 m φ).1 r
  perm_mem m φ ς := ((hA zeroBeyondDegreeZero isLinearFunctionalSeq_zeroBeyondDegreeZero).1 m φ).2.1 ς
  flipConj_mem m φ := ((hA zeroBeyondDegreeZero isLinearFunctionalSeq_zeroBeyondDegreeZero).1 m φ).2.2
  linComb_mem m c c' φ ψ := by
    obtain ⟨χ, hχ⟩ := (hL (m + 1) (Nat.succ_pos m)).1 c c' φ ψ
    exact hχ ▸ χ.2
  tensor_mem m X hX := (hL (m + 1) (Nat.succ_pos m)).2 X hX
  update_exists n i b b' X X' h :=
    ⟨⟨Function.update X.1 i (b • X.1 i + b' • X'.1 i),
      update_linComb_mem_separatedFamilies i b b' X X' h⟩, by simp,
      fun j hj => by simp [Function.update_of_ne hj]⟩
  finSupp_mem Φ Ψ hΦ hΨ := by
    obtain ⟨h₁, h₂, h₃, h₄, -⟩ :=
      (hA zeroBeyondDegreeZero isLinearFunctionalSeq_zeroBeyondDegreeZero).2 Φ Ψ hΦ hΨ
    exact ⟨h₁, h₂, h₃, h₄⟩
theorem sequenceIdentitiesEverywhere_of (hD : DomainsContainArguments) {σ : SeparatedFamily → ℝ}
    {T : FlatSequence} (h : IsSchwingerSequenceOf σ T) :
    SequenceIdentitiesEverywhere σ T where
  degree_zero c := ⟨Set.mem_univ _, h.2.1 ⟨c, Set.mem_univ _⟩⟩
  map_linComb m c c' φ ψ :=
    ⟨hD.linComb_mem m c c' φ ψ, (h.2.2 m).1.1 c c' φ ψ ⟨_, hD.linComb_mem m c c' φ ψ⟩ rfl⟩
  map_tensor m X hX := ⟨hD.tensor_mem m X hX, (h.2.2 m).2 X hX _⟩
  multilinear n hn i b b' X X' hXX' := by
    obtain ⟨X'', h₁, h₂⟩ := hD.update_exists n i b b' X X' hXX'
    exact ⟨X'', h₁, h₂, h.1.2 n hn i b b' X X' X'' hXX' h₁ h₂⟩
theorem axiomsEverywhere_of (hD : DomainsContainArguments) {T : FlatSequence}
    (hseq : IsLinearFunctionalSeq T) (hE : IsEuclidInvariant T)
    (hR : IsOSPositive T) (hP : IsPermSymmetric T) (hC : HasClusterProperty T)
    (hC' : IsReflectionReal T) : AxiomsEverywhere T where
  euclid_inv m φ r := ⟨hD.motion_mem m φ r, hE m φ r _⟩
  os_positive Φ hΦ := by
    obtain ⟨-, -, h, -⟩ := hD.finSupp_mem Φ Φ hΦ hΦ
    obtain ⟨N, hN⟩ := exists_degree_bound hΦ
    refine ⟨h, N, hN, ?_⟩
    have e := reflectionPairing_eq_pairedValueSum hseq (φ := fun q => (Φ q).1) (ψ := fun q => (Φ q).1) h hN hN
    have hp := hR Φ hΦ
    rwa [e] at hp
  perm_symm m φ ς := ⟨hD.perm_mem m φ ς, hP m φ ς _⟩
  cluster Φ Ψ hΦ hΨ v hv hv0 := by
    obtain ⟨h₁, h₂, -, h₄⟩ := hD.finSupp_mem Φ Ψ hΦ hΨ
    obtain ⟨N₁, hN₁⟩ := exists_degree_bound hΦ
    obtain ⟨N₂, hN₂⟩ := exists_degree_bound hΨ
    have hb₁ : ∀ q, max N₁ N₂ ≤ q → (Φ q).1 = zeroOfDegree q :=
      fun q hq => hN₁ q (le_trans (le_max_left _ _) hq)
    have hb₂ : ∀ q, max N₁ N₂ ≤ q → (Ψ q).1 = zeroOfDegree q :=
      fun q hq => hN₂ q (le_trans (le_max_right _ _) hq)
    refine ⟨h₄ v hv, h₁, h₂, max N₁ N₂, fun q hq => ⟨hb₁ q hq, hb₂ q hq⟩, ?_⟩
    have hc := hC Φ Ψ hΦ hΨ v hv hv0
    have e₁ : (fun t : ℝ => T.reflectionPairing (fun q => (Φ q).1)
        fun q => shiftActAt (t • v) (Ψ q).1) =
        fun t : ℝ => pairedValueSum T (φ := fun q => (Φ q).1)
          (ψ := fun q => shiftActAt (t • v) (Ψ q).1) (h₄ v hv t) (max N₁ N₂) :=
      funext fun t => reflectionPairing_eq_pairedValueSum hseq (h₄ v hv t) hb₁ fun q hq => by
        show shiftActAt (t • v) (Ψ q).1 = zeroOfDegree q
        rw [hb₂ q hq, shiftActAt_zeroOfDegree]
    have e₂ := finsum_evalAt_eq_sum_range hseq (φ := fun q => flipConjAt (Φ q).1) h₁
      (N := max N₁ N₂) fun q hq => by
        show flipConjAt (Φ q).1 = zeroOfDegree q
        rw [hb₁ q hq, flipConjAt_zeroOfDegree]
    have e₃ := finsum_evalAt_eq_sum_range hseq (φ := fun q => (Ψ q).1) h₂ hb₂
    rw [e₁, e₂, e₃] at hc
    exact hc
  reality m φ := ⟨hD.flipConj_mem m φ, hC' m φ _⟩
def unitBump (c : Fin 4 → ℝ) : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
theorem unitBump_self (c : Fin 4 → ℝ) : (unitBump c) c = 1 :=
  (unitBump c).one_of_mem_closedBall (Metric.mem_closedBall_self (unitBump c).rIn_pos.le)
theorem tsupport_unitBump (c : Fin 4 → ℝ) : tsupport (unitBump c) = Metric.closedBall c (1 / 2) :=
  (unitBump c).tsupport_eq
theorem unitBump_mem_realSmoothCompactIn (c : Fin 4 → ℝ) : (unitBump c : (Fin 4 → ℝ) → ℝ) ∈
    realSmoothCompactIn Set.univ :=
  mem_realSmoothCompactIn_iff.2
    ⟨isOpen_univ, (unitBump c).contDiff, (unitBump c).hasCompactSupport, Set.subset_univ _⟩
theorem unitBump_mem_realC1CompactIn (c : Fin 4 → ℝ) : (unitBump c : (Fin 4 → ℝ) → ℝ) ∈
    realC1CompactIn Set.univ :=
  mem_realC1CompactIn_iff.2
    ⟨isOpen_univ, (unitBump c).contDiff, (unitBump c).hasCompactSupport, Set.subset_univ _⟩
def timeAxisPoint (i : ℕ) : Fin 4 → ℝ := Pi.single 3 (2 * (i : ℝ) + 2)
theorem timeAxisPoint_three (i : ℕ) : timeAxisPoint i 3 = 2 * (i : ℝ) + 2 := by
  simp [timeAxisPoint]
theorem disjoint_closedBall_timeAxisPoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Metric.closedBall (timeAxisPoint i) (1 / 2 : ℝ))
      (Metric.closedBall (timeAxisPoint j) (1 / 2 : ℝ)) := by
  apply Metric.closedBall_disjoint_closedBall
  have h₁ := dist_le_pi_dist (timeAxisPoint i) (timeAxisPoint j) 3
  rw [timeAxisPoint_three, timeAxisPoint_three, Real.dist_eq] at h₁
  have h₂ : (1 : ℝ) ≤ |(i : ℝ) - j| := by
    have hz : ((i : ℤ) - j) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hij)
    have := Int.one_le_abs hz
    exact_mod_cast this
  have h₃ : |2 * (i : ℝ) + 2 - (2 * (j : ℝ) + 2)| = 2 * |(i : ℝ) - j| := by
    rw [show 2 * (i : ℝ) + 2 - (2 * (j : ℝ) + 2) = 2 * ((i : ℝ) - j) by ring, abs_mul]
    norm_num
  rw [h₃] at h₁
  linarith
def bumpFamily (n : ℕ) : SepFamilyOfLength n :=
  ⟨fun i => (unitBump (timeAxisPoint i) : (Fin 4 → ℝ) → ℝ), fun i => unitBump_mem_realC1CompactIn _, fun i j hij => by
    show Disjoint (tsupport (unitBump (timeAxisPoint i))) (tsupport (unitBump (timeAxisPoint j)))
    rw [tsupport_unitBump, tsupport_unitBump]
    exact disjoint_closedBall_timeAxisPoint fun h => hij (Fin.ext h)⟩
theorem bumpFamily_allSmoothCompact (n : ℕ) : AllSmoothCompact (bumpFamily n).1 :=
  fun _ => unitBump_mem_realSmoothCompactIn _
theorem tsupport_bumpFamily_subset (n : ℕ) (i : Fin n) :
    tsupport ((bumpFamily n).1 i) ⊆ upperHalfSpace := by
  show tsupport (unitBump (timeAxisPoint i)) ⊆ upperHalfSpace
  rw [tsupport_unitBump]
  intro u hu
  have h₁ := (dist_le_pi_dist u (timeAxisPoint i) 3).trans (Metric.mem_closedBall.1 hu)
  rw [timeAxisPoint_three, Real.dist_eq] at h₁
  have h₂ := (abs_le.1 h₁).1
  show u 3 > 0
  linarith
theorem tensorRealFamily_bumpFamily_timeAxis (n : ℕ) :
    tensorRealFamily (bumpFamily n).1 (fun i => timeAxisPoint i) = 1 := by
  show ∏ i : Fin n, (((unitBump (timeAxisPoint i)) (timeAxisPoint i) : ℝ) : ℂ) = 1
  simp [unitBump_self]
theorem tensorRealFamily_bumpFamily_ne_zero (n : ℕ) : tensorRealFamily (bumpFamily n).1 ≠ 0 := by
  intro h
  have := congrFun h fun i => timeAxisPoint i
  rw [tensorRealFamily_bumpFamily_timeAxis] at this
  simp at this
theorem zeroOfDegree_mem_flatOffPosTimeAt (hS : OpenLociAndFlatSubspaces) (q : ℕ) :
    zeroOfDegree q ∈ flatOffPosTimeAt q := by
  cases q with
  | zero => exact Set.mem_univ _
  | succ k =>
    obtain ⟨-, -, S, W, Wp, Wm, -, -, hWp, -⟩ := hS (k + 1) (Nat.succ_pos k)
    show (fun _ => 0 : Config (k + 1) → ℂ) ∈ schwartzFlatOffPosTime (k + 1)
    rw [← hWp]
    exact Wp.zero_mem
theorem tensorRealFamily_bumpFamily_mem (hC : CompactSupportTensorFacts) (m : ℕ) :
    tensorRealFamily (bumpFamily (m + 1)).1 ∈ schwartzFlatOffPosTime (m + 1) := by
  obtain ⟨-, -, h₃, -, h₅, -⟩ := hC (m + 1) (Nat.succ_pos m)
  exact h₃ ((h₅ _ (bumpFamily (m + 1)).2 (bumpFamily_allSmoothCompact _)).2
    (tsupport_bumpFamily_subset (m + 1)))
theorem tensorAt_flipConjAt_self_ne_zero {m : ℕ} {φ : Config (m + 1) → ℂ} (hφ : φ ≠ 0) :
    tensorAt (p := m + 1) (p' := m + 1) (flipConjAt (n := m + 1) φ) φ ≠
      zeroOfDegree (m + 1 + (m + 1)) := by
  intro e
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hφ
  have e' : tensorFn (p := m + 1) (p' := m + 1) (flipConj φ) φ = fun _ => 0 := e
  have h := congrFun e' (concatConfig (fun i => timeFlip (x i)) x)
  rw [tensorFn_concatConfig] at h
  have hθ : (fun i => timeFlip (timeFlip (x i))) = x :=
    funext fun i => timeFlip_timeFlip (x i)
  simp only [flipConj, hθ] at h
  have hx' : φ x ≠ 0 := hx
  simp [hx'] at h
theorem argumentsNotAllZero_of (hS : OpenLociAndFlatSubspaces)
    (hC : CompactSupportTensorFacts) : ArgumentsNotAllZero where
  exists_family n _ := ⟨bumpFamily n, bumpFamily_allSmoothCompact n, tsupport_bumpFamily_subset n,
    tensorRealFamily_bumpFamily_ne_zero n⟩
  exists_seq m := by
    let Z : PosTimeSeq := fun q => ⟨zeroOfDegree q, zeroOfDegree_mem_flatOffPosTimeAt hS q⟩
    let P : flatOffPosTimeAt (m + 1) :=
      ⟨tensorRealFamily (bumpFamily (m + 1)).1, tensorRealFamily_bumpFamily_mem hC m⟩
    have hself : (Function.update Z (m + 1) P (m + 1)).1 =
        tensorRealFamily (bumpFamily (m + 1)).1 := by
      rw [Function.update_self]
    refine ⟨Function.update Z (m + 1) P, ?_, ?_, ?_⟩
    · refine (Set.finite_singleton (m + 1)).subset fun q hq => ?_
      by_contra hne
      apply hq
      rw [Function.update_of_ne hne]
    · rw [hself]
      exact tensorRealFamily_bumpFamily_ne_zero (m + 1)
    · rw [hself]
      exact tensorAt_flipConjAt_self_ne_zero (tensorRealFamily_bumpFamily_ne_zero (m + 1))
  exists_direction := ⟨Pi.single 0 1, by
    show (Pi.single 0 1 : Fin 4 → ℝ) 3 = 0
    simp, fun h => by simpa using congrFun h 0⟩
end YangMills.Construction.ConditionDomains
end
