import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LatticeFractionalIntegration FiniteDifferences
namespace FlatPairing
namespace Walks
section Lengths
theorem natAbs_le_supNorm (u : Lattice4) (μ : Fin 4) : (u μ).natAbs ≤ supNorm u := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem supNorm_le_iff (u : Lattice4) (n : ℕ) : supNorm u ≤ n ↔ ∀ μ, (u μ).natAbs ≤ n := by apply _root_.YangMills.Construction.LatticePaths.supNorm_le_iff <;> assumption
theorem supNorm_zero : supNorm (0 : Lattice4) = 0 := by apply _root_.YangMills.Construction.LatticePaths.supNorm_zero <;> assumption
theorem supNorm_neg (u : Lattice4) : supNorm (-u) = supNorm u := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
theorem supNorm_add_le (u v : Lattice4) : supNorm (u + v) ≤ supNorm u + supNorm v := by apply _root_.YangMills.Construction.LatticePaths.supNorm_add_le <;> assumption
theorem supNorm_basisVector (μ : Fin 4) : supNorm (basisVector μ) = 1 := by apply _root_.YangMills.Construction.LatticePaths.supNorm_basisVector <;> assumption
theorem supNorm_stepDisplacement (st : PathStep) : supNorm (stepDisplacement st) = 1 := by apply _root_.YangMills.Construction.LatticePaths.supNorm_stepDisplacement <;> assumption
theorem supNorm_le_of_coord {u v : Lattice4} (h : ∀ μ, v μ = u μ ∨ v μ = 0) : supNorm v ≤ supNorm u := by
  rw [supNorm_le_iff]
  intro μ
  rcases h μ with h | h
  · rw [h]; exact natAbs_le_supNorm u μ
  · rw [h]; simp
end Lengths
section Paths
def pathForall (p : Lattice4 → Prop) : Lattice4 → List PathStep → Prop
  | u, [] => p u
  | u, st :: r => p u ∧ pathForall p (u + stepDisplacement st) r
def pathEndpoint : Lattice4 → List PathStep → Lattice4
  | u, [] => u
  | u, st :: r => pathEndpoint (u + stepDisplacement st) r
variable {p q : Lattice4 → Prop}
theorem pathForall_head {u : Lattice4} {l : List PathStep} (h : pathForall p u l) : p u := by
  cases l with
  | nil => exact h
  | cons st r => exact h.1
theorem pathForall_endpoint {u : Lattice4} {l : List PathStep} (h : pathForall p u l) : p (pathEndpoint u l) := by
  induction l generalizing u with
  | nil => exact h
  | cons st r ih => exact ih h.2
theorem pathForall_append {u : Lattice4} {l l' : List PathStep} (h : pathForall p u l)
    (h' : pathForall p (pathEndpoint u l) l') : pathForall p u (l ++ l') := by
  induction l generalizing u with
  | nil => exact h'
  | cons st r ih => exact ⟨h.1, ih h.2 h'⟩
theorem pathEndpoint_append (u : Lattice4) (l l' : List PathStep) :
    pathEndpoint u (l ++ l') = pathEndpoint (pathEndpoint u l) l' := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih => exact ih _
theorem pathForall_mono (hpq : ∀ v, p v → q v) {u : Lattice4} {l : List PathStep} (h : pathForall p u l) :
    pathForall q u l := by
  induction l generalizing u with
  | nil => exact hpq _ h
  | cons st r ih => exact ⟨hpq _ h.1, ih h.2⟩
theorem pathEndpoint_add (u w : Lattice4) (l : List PathStep) :
    pathEndpoint (u + w) l = pathEndpoint u l + w := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    show pathEndpoint (u + w + stepDisplacement st) r = pathEndpoint (u + stepDisplacement st) r + w
    rw [add_right_comm, ih]
theorem pathForall_add {w u : Lattice4} {l : List PathStep} (h : pathForall p u l) :
    pathForall (fun v => p (v - w)) (u + w) l := by
  induction l generalizing u with
  | nil => simpa [pathForall] using h
  | cons st r ih =>
    refine ⟨by simpa using h.1, ?_⟩
    have := ih h.2
    rwa [add_right_comm] at this
theorem stepDisplacement_flip (st : PathStep) : stepDisplacement (st.1, !st.2) = - stepDisplacement st := by apply _root_.YangMills.Construction.LatticePaths.stepDisplacement_flip <;> assumption
theorem reversePath_cons (st : PathStep) (r : List PathStep) :
    reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
  simp [reversePath]
theorem pathEndpoint_reversePath (u : Lattice4) (l : List PathStep) :
    pathEndpoint (pathEndpoint u l) (reversePath l) = u := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    rw [reversePath_cons, pathEndpoint_append]
    show pathEndpoint (pathEndpoint (pathEndpoint (u + stepDisplacement st) r) (reversePath r))
      [(st.1, !st.2)] = u
    rw [ih]
    show u + stepDisplacement st + stepDisplacement (st.1, !st.2) = u
    rw [stepDisplacement_flip]
    abel
theorem pathForall_reversePath {u : Lattice4} {l : List PathStep} (h : pathForall p u l) :
    pathForall p (pathEndpoint u l) (reversePath l) := by
  induction l generalizing u with
  | nil => exact h
  | cons st r ih =>
    rw [reversePath_cons]
    refine pathForall_append (ih h.2) ?_
    have e : pathEndpoint (pathEndpoint (u + stepDisplacement st) r) (reversePath r) =
      u + stepDisplacement st := pathEndpoint_reversePath _ _
    show pathForall p (pathEndpoint (pathEndpoint (u + stepDisplacement st) r) (reversePath r))
      [(st.1, !st.2)]
    rw [e]
    refine ⟨pathForall_head h.2, ?_⟩
    show p (u + stepDisplacement st + stepDisplacement (st.1, !st.2))
    rw [stepDisplacement_flip]
    have : u + stepDisplacement st + - stepDisplacement st = u := by abel
    rw [this]
    exact h.1
theorem pathEndpoint_replicate (u : Lattice4) (st : PathStep) (n : ℕ) :
    pathEndpoint u (List.replicate n st) = u + (n : ℤ) • stepDisplacement st := by
  induction n generalizing u with
  | zero => simp [pathEndpoint]
  | succ n ih =>
    rw [List.replicate_succ]
    show pathEndpoint (u + stepDisplacement st) (List.replicate n st) = _
    rw [ih]
    push_cast
    rw [add_smul, one_smul]
    abel
theorem pathForall_replicate {u : Lattice4} {st : PathStep} {n : ℕ}
    (h : ∀ k : ℕ, k ≤ n → p (u + (k : ℤ) • stepDisplacement st)) :
    pathForall p u (List.replicate n st) := by
  induction n generalizing u with
  | zero => simpa [pathForall] using h 0 le_rfl
  | succ n ih =>
    rw [List.replicate_succ]
    refine ⟨by simpa using h 0 (Nat.zero_le _), ih fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    have e : u + stepDisplacement st + (k : ℤ) • stepDisplacement st =
        u + ((k + 1 : ℕ) : ℤ) • stepDisplacement st := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rwa [e]
end Paths
section Legs
def axisSegment (h : Lattice4) (i : Fin 4) : List PathStep :=
  List.replicate (h i).natAbs (i, decide (0 ≤ h i))
theorem axisPath_eq (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    axisPath h π = axisSegment h (π 0) ++ (axisSegment h (π 1) ++ (axisSegment h (π 2) ++ axisSegment h (π 3))) := by apply _root_.YangMills.Construction.LatticePaths.axisPath_eq <;> assumption
def betweenOrigin (h v : Lattice4) : Prop := ∀ μ, min 0 (h μ) ≤ v μ ∧ v μ ≤ max 0 (h μ)
theorem axisSegment_displacement (h : Lattice4) (i : Fin 4) :
    (((h i).natAbs : ℕ) : ℤ) • stepDisplacement (i, decide (0 ≤ h i)) = h i • basisVector i := by apply _root_.YangMills.Construction.LatticePaths.axisFlow_displacement <;> assumption
theorem pathEndpoint_axisSegment (h : Lattice4) (i : Fin 4) (u : Lattice4) :
    pathEndpoint u (axisSegment h i) = u + h i • basisVector i := by
  unfold axisSegment
  rw [pathEndpoint_replicate, axisSegment_displacement]
theorem pathForall_axisSegment {h u : Lattice4} {i : Fin 4} (hu : betweenOrigin h u) (h0 : u i = 0) :
    pathForall (betweenOrigin h) u (axisSegment h i) := by
  refine pathForall_replicate fun k hk μ => ?_
  by_cases hμ : μ = i
  · subst hμ
    by_cases hs : 0 ≤ h μ
    · simp [stepDisplacement, hs, basisVector, h0]
      omega
    · simp [stepDisplacement, hs, basisVector, h0]
      omega
  · have : (stepDisplacement (i, decide (0 ≤ h i))) μ = 0 := by
      by_cases hs : 0 ≤ h i <;> simp [stepDisplacement, hs, basisVector, hμ]
    simpa [this] using hu μ
theorem axisPath_spec (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    pathForall (betweenOrigin h) 0 (axisPath h π) ∧ pathEndpoint 0 (axisPath h π) = h := by
  have hz : betweenOrigin h 0 := fun μ => by simp
  have n01 : π 1 ≠ π 0 := π.injective.ne (by decide)
  have n02 : π 2 ≠ π 0 := π.injective.ne (by decide)
  have n03 : π 3 ≠ π 0 := π.injective.ne (by decide)
  have n12 : π 2 ≠ π 1 := π.injective.ne (by decide)
  have n13 : π 3 ≠ π 1 := π.injective.ne (by decide)
  have n23 : π 3 ≠ π 2 := π.injective.ne (by decide)
  have p0 := pathForall_axisSegment (i := π 0) hz rfl
  have e0 := pathEndpoint_axisSegment h (π 0) 0
  have z1 : pathEndpoint 0 (axisSegment h (π 0)) (π 1) = 0 := by
    rw [e0]; simp [basisVector, n01]
  have p1 := pathForall_axisSegment (i := π 1) (pathForall_endpoint p0) z1
  have e1 := pathEndpoint_axisSegment h (π 1) (pathEndpoint 0 (axisSegment h (π 0)))
  have z2 : pathEndpoint (pathEndpoint 0 (axisSegment h (π 0))) (axisSegment h (π 1)) (π 2) = 0 := by
    rw [e1, e0]; simp [basisVector, n02, n12]
  have p2 := pathForall_axisSegment (i := π 2) (pathForall_endpoint p1) z2
  have e2 := pathEndpoint_axisSegment h (π 2)
    (pathEndpoint (pathEndpoint 0 (axisSegment h (π 0))) (axisSegment h (π 1)))
  have z3 : pathEndpoint (pathEndpoint (pathEndpoint 0 (axisSegment h (π 0))) (axisSegment h (π 1)))
      (axisSegment h (π 2)) (π 3) = 0 := by
    rw [e2, e1, e0]; simp [basisVector, n03, n13, n23]
  have p3 := pathForall_axisSegment (i := π 3) (pathForall_endpoint p2) z3
  have e3 := pathEndpoint_axisSegment h (π 3)
    (pathEndpoint (pathEndpoint (pathEndpoint 0 (axisSegment h (π 0))) (axisSegment h (π 1)))
      (axisSegment h (π 2)))
  rw [axisPath_eq]
  refine ⟨pathForall_append p0 (pathForall_append p1 (pathForall_append p2 p3)), ?_⟩
  rw [pathEndpoint_append, pathEndpoint_append, pathEndpoint_append, e3, e2, e1, e0]
  have := Equiv.sum_comp π (fun i => h i • basisVector i)
  rw [Fin.sum_univ_four] at this
  rw [zero_add, this]
  funext ν
  simp [basisVector, Finset.sum_apply, Pi.single_apply]
end Legs
section Contours
theorem mem_centredCube_iff (L : ℕ) (h : Lattice4) :
    h ∈ centredCube L ↔ ∀ i, -(((L : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem mem_twoBlockHull_of_betweenOrigin {L : ℕ} {h v : Lattice4} {i : Fin 4} (hh : h ∈ centredCube L)
    (hv : betweenOrigin h v) (hL : 1 ≤ L) : v ∈ twoBlockHull L i := by apply _root_.YangMills.Construction.LatticePaths.mem_twoBlockHull_of_between <;> assumption
theorem bondContour_spec {L : ℕ} {h : Lattice4} (π : Equiv.Perm (Fin 4)) (i : Fin 4) (hL : 1 ≤ L)
    (hh : h ∈ centredCube L) :
    pathForall (fun v => v ∈ twoBlockHull L i) 0 (bondContour L h π i) ∧
      pathEndpoint 0 (bondContour L h π i) = (L : ℤ) • basisVector i := by
  obtain ⟨l1, l2⟩ := axisPath_spec h π
  have e1 : stepDisplacement (i, true) = basisVector i := by simp [stepDisplacement]
  have q1 : pathForall (fun v => v ∈ twoBlockHull L i) 0 (axisPath h π) :=
    pathForall_mono (fun v hv => mem_twoBlockHull_of_betweenOrigin hh hv hL) l1
  have q2 : pathForall (fun v => v ∈ twoBlockHull L i) (pathEndpoint 0 (axisPath h π))
      (List.replicate L (i, true)) := by
    rw [l2]
    refine pathForall_replicate fun k hk μ => ?_
    have h1 := ((mem_centredCube_iff L h).1 hh) μ
    rw [e1]
    by_cases hμ : μ = i
    · subst hμ
      simp [basisVector]
      constructor <;> omega
    · simp [basisVector, hμ]
      exact h1
  have e2 : pathEndpoint (pathEndpoint 0 (axisPath h π)) (List.replicate L (i, true)) =
      h + (L : ℤ) • basisVector i := by
    rw [l2, pathEndpoint_replicate, e1]
  have q3 : pathForall (fun v => v ∈ twoBlockHull L i)
      (pathEndpoint (pathEndpoint 0 (axisPath h π)) (List.replicate L (i, true)))
      (reversePath (axisPath h π)) := by
    rw [e2]
    have s1 := pathForall_add (w := (L : ℤ) • basisVector i) l1
    have s2 := pathForall_reversePath s1
    rw [pathEndpoint_add, l2] at s2
    refine pathForall_mono (fun v hv μ => ?_) s2
    have h1 := ((mem_centredCube_iff L h).1 hh) μ
    have h2 := hv μ
    have a1 : min 0 (h μ) ≥ -(((L : ℤ) - 1) / 2) := le_min (by omega) h1.1
    have a2 : max 0 (h μ) ≤ ((L : ℤ) - 1) / 2 := max_le (by omega) h1.2
    by_cases hμ : μ = i
    · subst hμ
      simp [basisVector] at h2 ⊢
      omega
    · simp [basisVector, hμ] at h2 ⊢
      omega
  refine ⟨pathForall_append (pathForall_append q1 q2) ?_, ?_⟩
  · rw [pathEndpoint_append]
    exact q3
  · unfold bondContour
    rw [pathEndpoint_append, pathEndpoint_append, e2, pathEndpoint_add]
    have := pathEndpoint_reversePath 0 (axisPath h π)
    rw [l2] at this
    rw [this, zero_add]
theorem length_bondContour_le {L : ℕ} {h : Lattice4} (π : Equiv.Perm (Fin 4)) (i : Fin 4) (hL : 1 ≤ L)
    (hh : h ∈ centredCube L) :
    (bondContour L h π i).length ≤ 5 * L := by apply _root_.YangMills.Construction.LatticePaths.length_bondContour_le <;> assumption
end Contours
end Walks
open Walks
section AlmostAdditive
def intBox (lo hi : Fin 4 → ℤ) : Set Lattice4 := {u | ∀ μ, lo μ ≤ u μ ∧ u μ ≤ hi μ}
variable {G : Lattice4 → ℍ[ℝ]} {lo hi : Fin 4 → ℤ} {E : ℝ}
theorem mem_intBox_of_coord (hlo : ∀ μ, lo μ ≤ -1) (hhi : ∀ μ, 1 ≤ hi μ) {u v : Lattice4}
    (hu : u ∈ intBox lo hi) (h : ∀ μ, v μ = u μ ∨ v μ = 0) : v ∈ intBox lo hi := by
  intro μ
  rcases h μ with h | h
  · rw [h]; exact hu μ
  · rw [h]
    have := hlo μ
    have := hhi μ
    constructor <;> linarith
theorem norm_zsmul_sub_le_of_almost_additive (hE : 0 ≤ E) (h0 : G 0 = 0)
    (hadd : ∀ u u', u ∈ intBox lo hi → u' ∈ intBox lo hi → u + u' ∈ intBox lo hi →
      ‖G (u + u') - G u - G u'‖ ≤ E * supNorm u * supNorm u')
    {e : Lattice4} (he : supNorm e = 1) (he' : e ∈ intBox lo hi) (n : ℕ)
    (hn : ∀ k ≤ n, (k : ℤ) • e ∈ intBox lo hi) :
    ‖G ((n : ℤ) • e) - (n : ℝ) • G e‖ ≤ E * (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have h1 := ih fun k hk => hn k (hk.trans (Nat.le_succ n))
    have h2 := hadd ((n : ℤ) • e) e (hn n (Nat.le_succ n)) he' (by
      have := hn (n + 1) le_rfl
      have e1 : ((n + 1 : ℕ) : ℤ) • e = (n : ℤ) • e + e := by
        push_cast; rw [add_smul, one_smul]
      rwa [e1] at this)
    have e1 : (((n + 1 : ℕ) : ℤ)) • e = (n : ℤ) • e + e := by
      push_cast; rw [add_smul, one_smul]
    have hs : (supNorm ((n : ℤ) • e) : ℝ) ≤ n := by
      have : supNorm ((n : ℤ) • e) ≤ n := by
        rw [supNorm_le_iff]
        intro μ
        have h3 := natAbs_le_supNorm e μ
        rw [he] at h3
        simp only [Pi.smul_apply, smul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
        nlinarith
      exact_mod_cast this
    rw [e1]
    have e2 : G ((n : ℤ) • e + e) - ((n + 1 : ℕ) : ℝ) • G e =
        (G ((n : ℤ) • e + e) - G ((n : ℤ) • e) - G e) + (G ((n : ℤ) • e) - (n : ℝ) • G e) := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    have h4 : ‖G ((n : ℤ) • e + e) - G ((n : ℤ) • e) - G e‖ ≤ E * n := by
      refine h2.trans ?_
      rw [he]
      simp only [Nat.cast_one, mul_one]
      exact mul_le_mul_of_nonneg_left hs hE
    push_cast
    nlinarith
theorem norm_sub_linear_le_of_almost_additive (hE : 0 ≤ E) (h0 : G 0 = 0) (hlo : ∀ μ, lo μ ≤ -1)
    (hhi : ∀ μ, 1 ≤ hi μ)
    (hadd : ∀ u u', u ∈ intBox lo hi → u' ∈ intBox lo hi → u + u' ∈ intBox lo hi →
      ‖G (u + u') - G u - G u'‖ ≤ E * supNorm u * supNorm u')
    {u : Lattice4} (hu : u ∈ intBox lo hi) :
    ‖G u - ∑ μ, (u μ : ℝ) • G (basisVector μ)‖ ≤ 11 * E * (supNorm u : ℝ) ^ 2 := by
  have hunit : ∀ μ, basisVector μ ∈ intBox lo hi := by
    intro μ ν
    have a1 := hlo ν
    have a2 := hhi ν
    by_cases h : ν = μ
    · subst h; simp [basisVector]; constructor <;> linarith
    · simp [basisVector, h]; constructor <;> linarith
  have hunit' : ∀ μ, - basisVector μ ∈ intBox lo hi := by
    intro μ ν
    have a1 := hlo ν
    have a2 := hhi ν
    by_cases h : ν = μ
    · subst h; simp [basisVector]; constructor <;> linarith
    · simp [basisVector, h]; constructor <;> linarith
  have hcoord : ∀ (μ : Fin 4) (k : ℤ), lo μ ≤ k → k ≤ hi μ →
      ‖G (k • basisVector μ) - (k : ℝ) • G (basisVector μ)‖ ≤ 2 * E * (k : ℝ) ^ 2 := by
    intro μ k hk1 hk2
    have hbox : ∀ m : ℤ, lo μ ≤ m → m ≤ hi μ → m • basisVector μ ∈ intBox lo hi := by
      intro m hm1 hm2 ν
      have a1 := hlo ν
      have a2 := hhi ν
      by_cases h : ν = μ
      · subst h; simp [basisVector]; exact ⟨hm1, hm2⟩
      · simp [basisVector, h]; constructor <;> linarith
    rcases le_total 0 k with hk | hk
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      have := norm_zsmul_sub_le_of_almost_additive hE h0 hadd (supNorm_basisVector μ) (hunit μ) n
        (fun m hm => hbox m (by have := hlo μ; omega) (by omega))
      have e1 : (((n : ℤ) : ℝ)) = (n : ℝ) := by simp
      rw [e1]
      refine this.trans ?_
      have : 0 ≤ E * (n : ℝ) ^ 2 := by positivity
      linarith
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hk)
      have hkn : k = -(n : ℤ) := by omega
      subst hkn
      have h1 := norm_zsmul_sub_le_of_almost_additive hE h0 hadd (e := - basisVector μ)
        (by rw [supNorm_neg]; exact supNorm_basisVector μ)
        (hunit' μ) n (fun m hm => by
          have : (m : ℤ) • (- basisVector μ) = (-(m : ℤ)) • basisVector μ := by simp
          rw [this]
          exact hbox _ (by omega) (by have := hhi μ; omega))
      have h2 := hadd (basisVector μ) (- basisVector μ) (hunit μ) (hunit' μ) (by
        simp only [add_neg_cancel]
        intro ν
        have a1 := hlo ν
        have a2 := hhi ν
        simp only [Pi.zero_apply]
        constructor <;> linarith)
      rw [add_neg_cancel, h0, supNorm_neg, supNorm_basisVector] at h2
      simp only [Nat.cast_one, mul_one] at h2
      have e1 : (-(n : ℤ)) • basisVector μ = (n : ℤ) • (- basisVector μ) := by simp
      rw [e1]
      have e2 : G ((n : ℤ) • (- basisVector μ)) - (((-(n : ℤ) : ℤ)) : ℝ) • G (basisVector μ) =
          (G ((n : ℤ) • (- basisVector μ)) - (n : ℝ) • G (- basisVector μ)) -
            (n : ℝ) • (0 - G (basisVector μ) - G (- basisVector μ)) := by
        push_cast
        simp only [neg_smul, smul_sub, smul_neg, smul_zero]
        abel
      rw [e2]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h3 : (n : ℝ) * ‖(0 : ℍ[ℝ]) - G (basisVector μ) - G (- basisVector μ)‖ ≤ n * E :=
        mul_le_mul_of_nonneg_left h2 hn0
      have hn1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp
        · have : (1 : ℝ) ≤ n := by exact_mod_cast h
          nlinarith
      have h4 : (n : ℝ) * E ≤ (n : ℝ) ^ 2 * E := mul_le_mul_of_nonneg_right hn1 hE
      push_cast
      nlinarith
  set a : Fin 4 → Lattice4 := fun μ => (u μ) • basisVector μ with ha
  have hau : ∀ μ, supNorm (a μ) ≤ supNorm u := by
    intro μ
    refine supNorm_le_of_coord fun ν => ?_
    by_cases h : ν = μ
    · subst h; left; simp [ha, basisVector]
    · right; simp [ha, basisVector, h]
  have hab : ∀ μ, a μ ∈ intBox lo hi := by
    intro μ
    refine mem_intBox_of_coord hlo hhi hu fun ν => ?_
    by_cases h : ν = μ
    · subst h; left; simp [ha, basisVector]
    · right; simp [ha, basisVector, h]
  have hp1 : ∀ ν, (a 0 + a 1) ν = u ν ∨ (a 0 + a 1) ν = 0 := by
    intro ν; fin_cases ν <;> simp [ha, basisVector]
  have hp2 : ∀ ν, (a 0 + a 1 + a 2) ν = u ν ∨ (a 0 + a 1 + a 2) ν = 0 := by
    intro ν; fin_cases ν <;> simp [ha, basisVector]
  have hsum : a 0 + a 1 + a 2 + a 3 = u := by
    funext ν; fin_cases ν <;> simp [ha, basisVector]
  have b1 := mem_intBox_of_coord hlo hhi hu hp1
  have b2 := mem_intBox_of_coord hlo hhi hu hp2
  have s1 := supNorm_le_of_coord hp1
  have s2 := supNorm_le_of_coord hp2
  have t1 := hadd (a 0) (a 1) (hab 0) (hab 1) b1
  have t2 := hadd (a 0 + a 1) (a 2) b1 (hab 2) b2
  have t3 := hadd (a 0 + a 1 + a 2) (a 3) b2 (hab 3) (by rw [hsum]; exact hu)
  rw [hsum] at t3
  have hU : (0 : ℝ) ≤ supNorm u := Nat.cast_nonneg _
  have bound : ∀ x y : ℕ, x ≤ supNorm u → y ≤ supNorm u →
      E * (x : ℝ) * (y : ℝ) ≤ E * (supNorm u : ℝ) ^ 2 := by
    intro x y hx hy
    have hx' : (x : ℝ) ≤ supNorm u := by exact_mod_cast hx
    have hy' : (y : ℝ) ≤ supNorm u := by exact_mod_cast hy
    have : (x : ℝ) * y ≤ (supNorm u : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul hx' hy' (Nat.cast_nonneg _) hU
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this hE
  have u1 := t1.trans (bound _ _ (hau 0) (hau 1))
  have u2 := t2.trans (bound _ _ s1 (hau 2))
  have u3 := t3.trans (bound _ _ s2 (hau 3))
  have hc : ∀ μ, ‖G (a μ) - (u μ : ℝ) • G (basisVector μ)‖ ≤ 2 * E * (supNorm u : ℝ) ^ 2 := by
    intro μ
    refine (hcoord μ (u μ) (hu μ).1 (hu μ).2).trans ?_
    have : ((u μ : ℝ)) ^ 2 ≤ (supNorm u : ℝ) ^ 2 := by
      have h1 : |(u μ : ℝ)| ≤ supNorm u := by
        have := natAbs_le_supNorm u μ
        have h2 : ((u μ).natAbs : ℝ) = |(u μ : ℝ)| := by
          simp [Nat.cast_natAbs]
        rw [← h2]
        exact_mod_cast this
      exact sq_le_sq' (by linarith [neg_abs_le (u μ : ℝ)]) (by linarith [le_abs_self (u μ : ℝ)])
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have e1 : G u - ∑ μ, (u μ : ℝ) • G (basisVector μ) =
      (G u - G (a 0 + a 1 + a 2) - G (a 3)) + (G (a 0 + a 1 + a 2) - G (a 0 + a 1) - G (a 2)) +
        (G (a 0 + a 1) - G (a 0) - G (a 1)) + (G (a 0) - (u 0 : ℝ) • G (basisVector 0)) +
        (G (a 1) - (u 1 : ℝ) • G (basisVector 1)) + (G (a 2) - (u 2 : ℝ) • G (basisVector 2)) +
        (G (a 3) - (u 3 : ℝ) • G (basisVector 3)) := by
    rw [Fin.sum_univ_four]
    abel
  rw [e1]
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  calc _ ≤ ‖G u - G (a 0 + a 1 + a 2) - G (a 3)‖ + ‖G (a 0 + a 1 + a 2) - G (a 0 + a 1) - G (a 2)‖ +
        ‖G (a 0 + a 1) - G (a 0) - G (a 1)‖ + ‖G (a 0) - (u 0 : ℝ) • G (basisVector 0)‖ +
        ‖G (a 1) - (u 1 : ℝ) • G (basisVector 1)‖ + ‖G (a 2) - (u 2 : ℝ) • G (basisVector 2)‖ +
        ‖G (a 3) - (u 3 : ℝ) • G (basisVector 3)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ 11 * E * (supNorm u : ℝ) ^ 2 := by linarith
end AlmostAdditive
section Area
variable (F : Fin 4 → Fin 4 → ℍ[ℝ])
def bilinForm (u v : Lattice4) : ℍ[ℝ] := ∑ μ, ∑ ν, ((u μ : ℝ) * (v ν : ℝ)) • F μ ν
theorem bilinForm_add_left (u u' v : Lattice4) :
    bilinForm F (u + u') v = bilinForm F u v + bilinForm F u' v := by
  simp only [bilinForm, Pi.add_apply, Int.cast_add, add_mul, add_smul, Finset.sum_add_distrib]
theorem bilinForm_add_right (u v v' : Lattice4) :
    bilinForm F u (v + v') = bilinForm F u v + bilinForm F u v' := by
  simp only [bilinForm, Pi.add_apply, Int.cast_add, mul_add, add_smul, Finset.sum_add_distrib]
theorem bilinForm_zsmul_left (k : ℤ) (u v : Lattice4) : bilinForm F (k • u) v = (k : ℝ) • bilinForm F u v := by
  simp only [bilinForm, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.smul_sum, smul_smul, mul_assoc]
theorem bilinForm_zsmul_right (k : ℤ) (u v : Lattice4) : bilinForm F u (k • v) = (k : ℝ) • bilinForm F u v := by
  simp only [bilinForm, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  ring
variable {F}
theorem bilinForm_swap (hF : ∀ μ ν, F ν μ = - F μ ν) (u v : Lattice4) :
    bilinForm F v u = - bilinForm F u v := by
  simp only [bilinForm]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hF μ ν, smul_neg, mul_comm]
theorem quaternion_eq_zero_of_eq_neg {x : ℍ[ℝ]} (h : x = - x) : x = 0 := by
  have h2 : x + x = 0 := by
    nth_rewrite 2 [h]
    simp
  have h3 : (2 : ℝ) • x = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
theorem bilinForm_self (hF : ∀ μ ν, F ν μ = - F μ ν) (u : Lattice4) : bilinForm F u u = 0 :=
  quaternion_eq_zero_of_eq_neg (bilinForm_swap hF u u)
variable (F) in
def discreteArea : Lattice4 → List PathStep → ℍ[ℝ]
  | _, [] => 0
  | u, st :: r => bilinForm F u (stepDisplacement st) + discreteArea (u + stepDisplacement st) r
theorem discreteArea_add_base (u w : Lattice4) (l : List PathStep) :
    discreteArea F (u + w) l = discreteArea F u l + bilinForm F w (pathEndpoint 0 l) := by
  induction l generalizing u with
  | nil =>
    have : bilinForm F w 0 = 0 := by simp [bilinForm]
    simpa [discreteArea, pathEndpoint] using this.symm
  | cons st r ih =>
    show bilinForm F (u + w) (stepDisplacement st) + discreteArea F (u + w + stepDisplacement st) r =
      bilinForm F u (stepDisplacement st) + discreteArea F (u + stepDisplacement st) r +
        bilinForm F w (pathEndpoint (0 + stepDisplacement st) r)
    rw [add_right_comm, ih, pathEndpoint_add, bilinForm_add_left, bilinForm_add_right]
    abel
theorem discreteArea_append (u : Lattice4) (l l' : List PathStep) :
    discreteArea F u (l ++ l') = discreteArea F u l + discreteArea F (pathEndpoint u l) l' := by
  induction l generalizing u with
  | nil => simp [discreteArea, pathEndpoint]
  | cons st r ih =>
    show bilinForm F u (stepDisplacement st) + discreteArea F (u + stepDisplacement st) (r ++ l') =
      bilinForm F u (stepDisplacement st) + discreteArea F (u + stepDisplacement st) r +
        discreteArea F (pathEndpoint (u + stepDisplacement st) r) l'
    rw [ih]
    abel
theorem discreteArea_reversePath (hF : ∀ μ ν, F ν μ = - F μ ν) (u : Lattice4) (l : List PathStep) :
    discreteArea F (pathEndpoint u l) (reversePath l) = - discreteArea F u l := by
  induction l generalizing u with
  | nil => simp [discreteArea, pathEndpoint, reversePath]
  | cons st r ih =>
    rw [reversePath_cons, discreteArea_append]
    show discreteArea F (pathEndpoint (u + stepDisplacement st) r) (reversePath r) +
        discreteArea F (pathEndpoint (pathEndpoint (u + stepDisplacement st) r) (reversePath r))
          [(st.1, !st.2)] =
      - (bilinForm F u (stepDisplacement st) + discreteArea F (u + stepDisplacement st) r)
    rw [ih, pathEndpoint_reversePath]
    show _ + (bilinForm F (u + stepDisplacement st) (stepDisplacement (st.1, !st.2)) + 0) = _
    rw [stepDisplacement_flip, bilinForm_add_left]
    have e1 : bilinForm F (stepDisplacement st) (- stepDisplacement st) = 0 := by
      have := bilinForm_zsmul_right F (-1) (stepDisplacement st) (stepDisplacement st)
      simp only [neg_smul, one_smul] at this
      rw [this, bilinForm_self hF]
      simp
    have e2 : bilinForm F u (- stepDisplacement st) = - bilinForm F u (stepDisplacement st) := by
      have := bilinForm_zsmul_right F (-1) u (stepDisplacement st)
      simpa using this
    rw [e1, e2]
    abel
theorem discreteArea_replicate (hF : ∀ μ ν, F ν μ = - F μ ν) (u : Lattice4) (st : PathStep) (n : ℕ) :
    discreteArea F u (List.replicate n st) = (n : ℝ) • bilinForm F u (stepDisplacement st) := by
  induction n generalizing u with
  | zero => simp [discreteArea]
  | succ n ih =>
    rw [List.replicate_succ]
    show bilinForm F u (stepDisplacement st) +
      discreteArea F (u + stepDisplacement st) (List.replicate n st) = _
    rw [ih, bilinForm_add_left, bilinForm_self hF]
    push_cast
    rw [add_smul, one_smul, add_zero]
    abel
theorem discreteArea_bondContour (hF : ∀ μ ν, F ν μ = - F μ ν) (L : ℕ) (h : Lattice4)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    discreteArea F 0 (bondContour L h π i) = (2 * (L : ℝ)) • bilinForm F h (basisVector i) := by
  have hend := (axisPath_spec h π).2
  unfold bondContour
  rw [discreteArea_append, discreteArea_append, hend, pathEndpoint_append, hend, pathEndpoint_replicate]
  have e1 : stepDisplacement (i, true) = basisVector i := by simp [stepDisplacement]
  rw [e1, discreteArea_replicate hF, (by simp [stepDisplacement] : stepDisplacement (i, true) = basisVector i)]
  have e2 : pathEndpoint (0 : Lattice4) (reversePath (axisPath h π)) = - h := by
    have h1 := pathEndpoint_reversePath 0 (axisPath h π)
    rw [hend] at h1
    have h2 := pathEndpoint_add 0 h (reversePath (axisPath h π))
    rw [zero_add, h1] at h2
    exact eq_neg_of_add_eq_zero_left h2.symm
  have e3 : discreteArea F h (reversePath (axisPath h π)) = - discreteArea F 0 (axisPath h π) := by
    have := discreteArea_reversePath hF 0 (axisPath h π)
    rwa [hend] at this
  have e4 := discreteArea_add_base (F := F) h ((L : ℤ) • basisVector i) (reversePath (axisPath h π))
  rw [e4, e3, e2, bilinForm_zsmul_left]
  have e5 : bilinForm F (basisVector i) (-h) = bilinForm F h (basisVector i) := by
    have h1 := bilinForm_zsmul_right F (-1) (basisVector i) h
    have h2 : (-1 : ℤ) • h = -h := by simp
    rw [h2] at h1
    rw [h1, bilinForm_swap hF h (basisVector i)]
    simp
  rw [e5]
  simp only [Int.cast_natCast, two_mul, add_smul]
  abel
theorem sum_centredCube_bilinForm (hF : ∀ μ ν, F ν μ = - F μ ν) (L : ℕ) (v : Lattice4) :
    ∑ h ∈ centredCube L, bilinForm F h v = 0 := by
  have hmem : ∀ h : Lattice4, h ∈ centredCube L ↔ - h ∈ centredCube L := by
    intro h
    simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply]
    constructor
    · intro hh i
      have := hh i
      constructor <;> omega
    · intro hh i
      have := hh i
      constructor <;> omega
  have e1 : ∑ h ∈ centredCube L, bilinForm F h v = ∑ h ∈ centredCube L, bilinForm F (-h) v :=
    (Finset.sum_equiv (Equiv.neg Lattice4) (fun h => by simpa using hmem h) (fun h _ => by simp))
  have e2 : ∑ h ∈ centredCube L, bilinForm F (-h) v = - ∑ h ∈ centredCube L, bilinForm F h v := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    have := bilinForm_zsmul_left F (-1) h v
    simpa using this
  rw [e2] at e1
  exact quaternion_eq_zero_of_eq_neg e1
end Area
section Triangles
abbrev PointTriple : Type := Lattice4 × Lattice4 × Lattice4
def tripleNorm (κ : ℝ) (t : PointTriple) : ℝ :=
  κ * ((supNorm t.1 : ℝ) + supNorm t.2.1 + supNorm t.2.2)
def trianglePairing (P0 : Lattice4 × Lattice4 → ℝ) (P1 : Lattice4 × Lattice4 → ℍ[ℝ]) (t : PointTriple) : ℍ[ℝ] :=
  pairingValue P0 P1 t.1 t.2.1 * pairingValue P0 P1 t.2.1 t.2.2 * pairingValue P0 P1 t.2.2 t.1
def fstSndHom : PointTriple →+ Lattice4 × Lattice4 :=
  AddMonoidHom.mk' (fun t => (t.1, t.2.1)) (fun _ _ => rfl)
def sndThdHom : PointTriple →+ Lattice4 × Lattice4 :=
  AddMonoidHom.mk' (fun t => (t.2.1, t.2.2)) (fun _ _ => rfl)
def thdFstHom : PointTriple →+ Lattice4 × Lattice4 :=
  AddMonoidHom.mk' (fun t => (t.2.2, t.1)) (fun _ _ => rfl)
theorem finiteDiffBound_coe_real {A : Type} [AddCommGroup A] {len : A → ℝ} {k : ℕ} {D : Set A} {B : ℝ}
    {f : A → ℝ} (h : FiniteDiffBound len k D B f) :
    FiniteDiffBound len k D B (fun x => ((f x : ℝ) : ℍ[ℝ])) := by apply _root_.YangMills.Construction.NearlyConstantKernel.finiteDiffBound_coe <;> assumption
variable {κ ρ B : ℝ} {D : Set Lattice4} {P0 : Lattice4 × Lattice4 → ℝ} {P1 : Lattice4 × Lattice4 → ℍ[ℝ]}
theorem scaledPairNorm_nonneg (hκ : 0 ≤ κ) (a : Lattice4 × Lattice4) : 0 ≤ scaledPairNorm κ a := by
  unfold scaledPairNorm; positivity
theorem tripleNorm_nonneg (hκ : 0 ≤ κ) (a : PointTriple) : 0 ≤ tripleNorm κ a := by
  unfold tripleNorm; positivity
theorem finiteDiffBound_fstSnd (hκ : 0 ≤ κ) {W : Type} [NormedAddCommGroup W] {Bf : ℝ}
    {f : Lattice4 × Lattice4 → W} (hB : 0 ≤ Bf)
    (h : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) Bf f) :
    FiniteDiffBound (tripleNorm κ) 3 (D ×ˢ D ×ˢ D) Bf (fun t => f (t.1, t.2.1)) := by
  refine (h.comp (scaledPairNorm_nonneg hκ) fstSndHom (fun a => ?_) hB).mono fun t ht => ?_
  · show κ * ((supNorm a.1 : ℝ) + supNorm a.2.1) ≤
      κ * ((supNorm a.1 : ℝ) + supNorm a.2.1 + supNorm a.2.2)
    have : (0 : ℝ) ≤ supNorm a.2.2 := Nat.cast_nonneg _
    nlinarith
  · exact ⟨ht.1, ht.2.1⟩
theorem finiteDiffBound_sndThd (hκ : 0 ≤ κ) {W : Type} [NormedAddCommGroup W] {Bf : ℝ}
    {f : Lattice4 × Lattice4 → W} (hB : 0 ≤ Bf)
    (h : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) Bf f) :
    FiniteDiffBound (tripleNorm κ) 3 (D ×ˢ D ×ˢ D) Bf (fun t => f (t.2.1, t.2.2)) := by
  refine (h.comp (scaledPairNorm_nonneg hκ) sndThdHom (fun a => ?_) hB).mono fun t ht => ?_
  · show κ * ((supNorm a.2.1 : ℝ) + supNorm a.2.2) ≤
      κ * ((supNorm a.1 : ℝ) + supNorm a.2.1 + supNorm a.2.2)
    have : (0 : ℝ) ≤ supNorm a.1 := Nat.cast_nonneg _
    nlinarith
  · exact ⟨ht.2.1, ht.2.2⟩
theorem finiteDiffBound_thdFst (hκ : 0 ≤ κ) {W : Type} [NormedAddCommGroup W] {Bf : ℝ}
    {f : Lattice4 × Lattice4 → W} (hB : 0 ≤ Bf)
    (h : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) Bf f) :
    FiniteDiffBound (tripleNorm κ) 3 (D ×ˢ D ×ˢ D) Bf (fun t => f (t.2.2, t.1)) := by
  refine (h.comp (scaledPairNorm_nonneg hκ) thdFstHom (fun a => ?_) hB).mono fun t ht => ?_
  · show κ * ((supNorm a.2.2 : ℝ) + supNorm a.1) ≤
      κ * ((supNorm a.1 : ℝ) + supNorm a.2.1 + supNorm a.2.2)
    have : (0 : ℝ) ≤ supNorm a.2.1 := Nat.cast_nonneg _
    nlinarith
  · exact ⟨ht.2.2, ht.1⟩
theorem finiteDiffBound_pairingValue (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hρ1 : ρ ≤ 1)
    (h0 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0)
    (h1 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1) :
    FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) (2 * B) (fun p => pairingValue P0 P1 p.1 p.2) := by
  have := (finiteDiffBound_coe_real h0).add h1
  exact this.bound_mono (scaledPairNorm_nonneg hκ) (by linarith)
theorem finiteDiffBound_trianglePairing (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hρ1 : ρ ≤ 1)
    (h0 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0)
    (h1 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1) :
    FiniteDiffBound (tripleNorm κ) 3 (D ×ˢ D ×ˢ D) (512 * B ^ 3) (trianglePairing P0 P1) := by
  have hl := tripleNorm_nonneg hκ
  have hb : 0 ≤ 2 * B := by linarith
  have hp := finiteDiffBound_pairingValue hκ hB hρ1 h0 h1
  have f1 := finiteDiffBound_fstSnd hκ hb hp
  have f2 := finiteDiffBound_sndThd hκ hb hp
  have f3 := finiteDiffBound_thdFst hκ hb hp
  have m1 := FiniteDiffBound.mul hl hb hb f1 f2
  have m2 := FiniteDiffBound.mul hl (by positivity) hb m1 f3
  have e : (2 : ℝ) ^ 3 * (2 ^ 3 * (2 * B) * (2 * B)) * (2 * B) = 512 * B ^ 3 := by ring
  rw [e] at m2
  exact m2
theorem finiteDiffBound_pure_trianglePairing (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (h0 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0)
    (h1 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1) :
    FiniteDiffBound (tripleNorm κ) 3 (D ×ˢ D ×ˢ D) (768 * B ^ 2 * ρ)
      (fun t => pureComponent (trianglePairing P0 P1 t)) := by
  have hl := tripleNorm_nonneg hκ
  have hb : 0 ≤ 2 * B := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hp := finiteDiffBound_pairingValue hκ hB hρ1 h0 h1
  have f2 := finiteDiffBound_sndThd hκ hb hp
  have f3 := finiteDiffBound_thdFst hκ hb hp
  have a1 := finiteDiffBound_fstSnd hκ hB0 (finiteDiffBound_coe_real h0)
  have a2 := finiteDiffBound_sndThd hκ hB0 (finiteDiffBound_coe_real h0)
  have b1 := finiteDiffBound_fstSnd hκ hρ0 h1
  have b2 := finiteDiffBound_sndThd hκ hρ0 h1
  have b3 := finiteDiffBound_thdFst hκ hρ0 h1
  have t1 := FiniteDiffBound.mul hl (by positivity) hb (FiniteDiffBound.mul hl hρ0 hb b1 f2) f3
  have t2 := FiniteDiffBound.mul hl (by positivity) hb (FiniteDiffBound.mul hl hB0 hρ0 a1 b2) f3
  have t3 := FiniteDiffBound.mul hl (by positivity) hρ0 (FiniteDiffBound.mul hl hB0 hB0 a1 a2) b3
  have u1 := t1.bound_mono hl (C' := 256 * B ^ 2 * ρ) (by
    have : (2 : ℝ) ^ 3 * (2 ^ 3 * ρ * (2 * B)) * (2 * B) = 256 * B ^ 2 * ρ := by ring
    rw [this])
  have u2 := t2.bound_mono hl (C' := 256 * B ^ 2 * ρ) (by
    have : (2 : ℝ) ^ 3 * (2 ^ 3 * B * ρ) * (2 * B) = 128 * B ^ 2 * ρ := by ring
    rw [this]
    nlinarith [mul_nonneg (sq_nonneg B) hρ0])
  have u3 := t3.bound_mono hl (C' := 256 * B ^ 2 * ρ) (by
    have : (2 : ℝ) ^ 3 * (2 ^ 3 * B * B) * ρ = 64 * B ^ 2 * ρ := by ring
    rw [this]
    nlinarith [mul_nonneg (sq_nonneg B) hρ0])
  have s := (u1.add u2).add u3
  have s' := s.map pureComponentHom (fun w => norm_pureComponent_le w)
  have e : 256 * B ^ 2 * ρ + 256 * B ^ 2 * ρ + 256 * B ^ 2 * ρ = 768 * B ^ 2 * ρ := by ring
  rw [e] at s'
  refine s'.congr fun t => ?_
  simp only [pureComponentHom_apply]
  have e1 : trianglePairing P0 P1 t =
      ((P0 (t.1, t.2.1) * P0 (t.2.1, t.2.2) * P0 (t.2.2, t.1) : ℝ) : ℍ[ℝ]) +
      (P1 (t.1, t.2.1) * pairingValue P0 P1 t.2.1 t.2.2 * pairingValue P0 P1 t.2.2 t.1 +
        (P0 (t.1, t.2.1) : ℍ[ℝ]) * P1 (t.2.1, t.2.2) * pairingValue P0 P1 t.2.2 t.1 +
        (P0 (t.1, t.2.1) : ℍ[ℝ]) * (P0 (t.2.1, t.2.2) : ℍ[ℝ]) * P1 (t.2.2, t.1)) := by
    simp only [trianglePairing, pairingValue, Quaternion.coe_mul]
    noncomm_ring
  have e2 := congrArg pureComponent e1
  rw [pureComponent_add, pureComponent_coe, zero_add] at e2
  exact e2.symm
variable (hsym : ∀ a b, pairingValue P0 P1 b a = star (pairingValue P0 P1 a b))
include hsym
theorem star_pairingValue_self (a : Lattice4) : star (pairingValue P0 P1 a a) = pairingValue P0 P1 a a :=
  (hsym a a).symm
theorem pureComponent_pairingValue_self (a : Lattice4) : pureComponent (pairingValue P0 P1 a a) = 0 :=
  pureComponent_eq_zero (star_pairingValue_self hsym a)
theorem pure_trianglePairing_fst_eq (a c : Lattice4) : pureComponent (trianglePairing P0 P1 (a, a, c)) = 0 := by
  have e : trianglePairing P0 P1 (a, a, c) =
      (((pairingValue P0 P1 a a).re * Quaternion.normSq (pairingValue P0 P1 a c) : ℝ) : ℍ[ℝ]) := by
    simp only [trianglePairing]
    rw [hsym a c, mul_assoc, Quaternion.self_mul_star, Quaternion.coe_mul]
    congr 1
    exact eq_coe_re_of_star_eq (star_pairingValue_self hsym a)
  rw [e, pureComponent_coe]
theorem pure_trianglePairing_thd_eq (a b : Lattice4) : pureComponent (trianglePairing P0 P1 (a, b, a)) = 0 := by
  have e : trianglePairing P0 P1 (a, b, a) =
      ((Quaternion.normSq (pairingValue P0 P1 a b) * (pairingValue P0 P1 a a).re : ℝ) : ℍ[ℝ]) := by
    simp only [trianglePairing]
    rw [hsym a b, Quaternion.self_mul_star, Quaternion.coe_mul]
    congr 1
    exact eq_coe_re_of_star_eq (star_pairingValue_self hsym a)
  rw [e, pureComponent_coe]
theorem pure_trianglePairing_snd_eq (a b : Lattice4) : pureComponent (trianglePairing P0 P1 (a, b, b)) = 0 := by
  have hr := eq_coe_re_of_star_eq (star_pairingValue_self hsym b)
  have e : trianglePairing P0 P1 (a, b, b) =
      (((pairingValue P0 P1 b b).re * Quaternion.normSq (pairingValue P0 P1 a b) : ℝ) : ℍ[ℝ]) := by
    simp only [trianglePairing]
    rw [hsym a b, hr, ← Quaternion.coe_commutes, mul_assoc, Quaternion.self_mul_star,
      Quaternion.coe_mul]
    simp
  rw [e, pureComponent_coe]
theorem pure_trianglePairing_swap (a b c : Lattice4) :
    pureComponent (trianglePairing P0 P1 (a, c, b)) = - pureComponent (trianglePairing P0 P1 (a, b, c)) := by
  have e : trianglePairing P0 P1 (a, c, b) = star (trianglePairing P0 P1 (a, b, c)) := by
    simp only [trianglePairing, star_mul]
    rw [← hsym c a, ← hsym b c, ← hsym a b, mul_assoc]
  rw [e, pureComponent_star]
end Triangles
section Fan
def fanProduct (R : Lattice4 → Lattice4 → UnitQuaternion) : Lattice4 → List PathStep → UnitQuaternion
  | _, [] => 1
  | u, st :: r => (R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0) *
      fanProduct R (u + stepDisplacement st) r
def fanSum (T : Lattice4 → PathStep → ℍ[ℝ]) : Lattice4 → List PathStep → ℍ[ℝ]
  | _, [] => 0
  | u, st :: r => T u st + fanSum T (u + stepDisplacement st) r
theorem fanProduct_eq {R : Lattice4 → Lattice4 → UnitQuaternion} (hinv : ∀ a b, R b a = (R a b)⁻¹)
    (u : Lattice4) (l : List PathStep) :
    R 0 u * pathProduct R u l * R (pathEndpoint u l) 0 = fanProduct R u l := by
  induction l generalizing u with
  | nil =>
    show R 0 u * 1 * R u 0 = 1
    rw [mul_one, hinv 0 u, mul_inv_cancel]
  | cons st r ih =>
    show R 0 u * (R u (u + stepDisplacement st) * pathProduct R (u + stepDisplacement st) r) *
        R (pathEndpoint (u + stepDisplacement st) r) 0 =
      (R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0) *
        fanProduct R (u + stepDisplacement st) r
    rw [← ih (u + stepDisplacement st)]
    have h1 : R (u + stepDisplacement st) 0 * R 0 (u + stepDisplacement st) = 1 := by
      rw [hinv 0 (u + stepDisplacement st), inv_mul_cancel]
    calc _ = R 0 u * R u (u + stepDisplacement st) * (1 * (pathProduct R (u + stepDisplacement st) r *
          R (pathEndpoint (u + stepDisplacement st) r) 0)) := by simp only [one_mul, mul_assoc]
      _ = R 0 u * R u (u + stepDisplacement st) *
          ((R (u + stepDisplacement st) 0 * R 0 (u + stepDisplacement st)) *
          (pathProduct R (u + stepDisplacement st) r * R (pathEndpoint (u + stepDisplacement st) r) 0)) := by
          rw [h1]
      _ = _ := by simp only [mul_assoc]
theorem norm_fanProduct_sub_one_le {R : Lattice4 → Lattice4 → UnitQuaternion} {good : Lattice4 → Prop}
    {e : ℝ} (he0 : 0 ≤ e)
    (he : ∀ u st, good u → good (u + stepDisplacement st) →
      ‖((R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e)
    {u : Lattice4} {l : List PathStep} (h : pathForall good u l) :
    ‖((fanProduct R u l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * e ∧
      ‖((fanProduct R u l : UnitQuaternion) : ℍ[ℝ]) - 1 - fanSum (fun u st =>
        ((R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 : UnitQuaternion) : ℍ[ℝ]) - 1)
          u l‖ ≤ (l.length * e) ^ 2 := by
  induction l generalizing u with
  | nil => simp [fanProduct, fanSum]
  | cons st r ih =>
    obtain ⟨i1, i2⟩ := ih h.2
    have hT := he u st h.1 (pathForall_head h.2)
    set T : UnitQuaternion := R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 with hTdef
    set G : UnitQuaternion := fanProduct R (u + stepDisplacement st) r with hG
    have hlen : ((st :: r).length : ℝ) = r.length + 1 := by simp
    have hr0 : (0 : ℝ) ≤ r.length := Nat.cast_nonneg _
    constructor
    · show ‖((T * G : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
      refine (norm_coe_mul_sub_one_le T G).trans ?_
      rw [hlen]
      nlinarith
    · show ‖((T * G : UnitQuaternion) : ℍ[ℝ]) - 1 - (((T : ℍ[ℝ]) - 1) + fanSum (fun u st =>
        ((R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 : UnitQuaternion) : ℍ[ℝ]) - 1)
          (u + stepDisplacement st) r)‖ ≤ _
      have e1 : ((T * G : UnitQuaternion) : ℍ[ℝ]) - 1 - (((T : ℍ[ℝ]) - 1) + fanSum (fun u st =>
          ((R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 : UnitQuaternion) : ℍ[ℝ]) - 1)
            (u + stepDisplacement st) r) =
          ((T : ℍ[ℝ]) - 1) * ((G : ℍ[ℝ]) - 1) + ((G : ℍ[ℝ]) - 1 - fanSum (fun u st =>
          ((R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 : UnitQuaternion) : ℍ[ℝ]) - 1)
            (u + stepDisplacement st) r) := by
        rw [Submonoid.coe_mul]
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        abel
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hlen]
      have a1 : ‖(T : ℍ[ℝ]) - 1‖ * ‖(G : ℍ[ℝ]) - 1‖ ≤ e * (r.length * e) :=
        mul_le_mul hT i1 (norm_nonneg _) he0
      nlinarith [mul_nonneg he0 he0, mul_nonneg (mul_nonneg hr0 he0) he0]
theorem norm_pure_fanSum_sub_discreteArea_le {T : Lattice4 → PathStep → ℍ[ℝ]} {F : Fin 4 → Fin 4 → ℍ[ℝ]}
    {good : Lattice4 → Prop} {z e : ℝ}
    (he : ∀ u st, good u → good (u + stepDisplacement st) →
      ‖pureComponent (T u st) - z • bilinForm F u (stepDisplacement st)‖ ≤ e)
    {u : Lattice4} {l : List PathStep} (h : pathForall good u l) :
    ‖pureComponent (fanSum T u l) - z • discreteArea F u l‖ ≤ l.length * e := by
  induction l generalizing u with
  | nil => simp [fanSum, discreteArea, pureComponent]
  | cons st r ih =>
    have h1 := he u st h.1 (pathForall_head h.2)
    have h2 := ih h.2
    have e1 : pureComponent (fanSum T u (st :: r)) - z • discreteArea F u (st :: r) =
        (pureComponent (T u st) - z • bilinForm F u (stepDisplacement st)) +
          (pureComponent (fanSum T (u + stepDisplacement st) r) -
            z • discreteArea F (u + stepDisplacement st) r) := by
      show pureComponent (T u st + fanSum T (u + stepDisplacement st) r) -
        z • (bilinForm F u (stepDisplacement st) + discreteArea F (u + stepDisplacement st) r) = _
      rw [pureComponent_add, smul_add]
      abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have : ((st :: r).length : ℝ) = r.length + 1 := by simp
    rw [this]
    linarith
end Fan
section Main
variable {κ ρ B : ℝ} {D : Set Lattice4} {P0 : Lattice4 × Lattice4 → ℝ} {P1 : Lattice4 × Lattice4 → ℍ[ℝ]}
theorem re_sub_norm_sub_le_re (a b : ℍ[ℝ]) : a.re - ‖a - b‖ ≤ b.re := by
  have h := quaternion_re_le_norm (a - b)
  have e : (a - b).re = a.re - b.re := by simp
  rw [e] at h
  linarith
theorem abs_coord_le_supNorm (u : Lattice4) (μ : Fin 4) : |(u μ : ℝ)| ≤ supNorm u := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
variable (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
  (h0 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0)
  (h1 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1)
  (hsym : ∀ a b, pairingValue P0 P1 b a = star (pairingValue P0 P1 a b))
  (hlow : ∀ a ∈ D, 1 ≤ (pairingValue P0 P1 a a).re)
include hκ hB hρ1 h0 h1 in
theorem norm_pairingValue_sub_diag_le {a b : Lattice4} (ha : a ∈ D) (hb : b ∈ D) :
    ‖pairingValue P0 P1 a b - pairingValue P0 P1 a a‖ ≤ 2 * B * (κ * supNorm (b - a)) := by
  have hp := finiteDiffBound_pairingValue hκ hB hρ1 h0 h1
  have e : ((a, a) : Lattice4 × Lattice4) + ((0 : Lattice4), b - a) = (a, b) := by simp
  have hl : scaledPairNorm κ ((0 : Lattice4), b - a) = κ * supNorm (b - a) := by
    simp [scaledPairNorm, supNorm_zero]
  have := hp.norm_sub_le (x := (a, a)) (a := ((0 : Lattice4), b - a)) ⟨ha, ha⟩ (by rw [e]; exact ⟨ha, hb⟩)
  rw [e, hl] at this
  exact this
include hsym h1 in
theorem norm_pure_pairingValue_le {a b : Lattice4} (ha : a ∈ D) (hb : b ∈ D) :
    ‖pureComponent (pairingValue P0 P1 a b)‖ ≤ ρ * (κ * supNorm (b - a)) := by
  have e : ((a, a) : Lattice4 × Lattice4) + ((0 : Lattice4), b - a) = (a, b) := by simp
  have hl : scaledPairNorm κ ((0 : Lattice4), b - a) = κ * supNorm (b - a) := by
    simp [scaledPairNorm, supNorm_zero]
  have h2 := h1.norm_sub_le (x := (a, a)) (a := ((0 : Lattice4), b - a)) ⟨ha, ha⟩ (by rw [e]; exact ⟨ha, hb⟩)
  rw [e, hl] at h2
  have e1 : pureComponent (pairingValue P0 P1 a b) = pureComponent (P1 (a, b) - P1 (a, a)) := by
    have h3 := pureComponent_pairingValue_self hsym a
    simp only [pairingValue, pureComponent_add, pureComponent_coe, zero_add] at h3 ⊢
    rw [pureComponent_sub, h3, sub_zero]
  rw [e1]
  exact (norm_pureComponent_le _).trans h2
include hκ hB hρ1 h0 h1 hlow in
theorem half_le_re_pairingValue {a b : Lattice4} (ha : a ∈ D) (hb : b ∈ D)
    (hd : 2 * B * (κ * supNorm (b - a)) ≤ 1 / 2) :
    1 / 2 ≤ (pairingValue P0 P1 a b).re := by
  have h2 := re_sub_norm_sub_le_re (pairingValue P0 P1 a a) (pairingValue P0 P1 a b)
  have h3 := norm_pairingValue_sub_diag_le hκ hB hρ1 h0 h1 ha hb
  rw [norm_sub_rev] at h2
  have := hlow a ha
  linarith
theorem ne_zero_of_half_le_re {q : ℍ[ℝ]} (h : 1 / 2 ≤ q.re) : q ≠ 0 := by
  intro h0
  rw [h0] at h
  norm_num at h
theorem half_le_norm_of_half_le_re {q : ℍ[ℝ]} (h : 1 / 2 ≤ q.re) : 1 / 2 ≤ ‖q‖ :=
  h.trans (quaternion_re_le_norm q)
theorem norm_polarUnit_sub_one_le_of_half_le_re {q : ℍ[ℝ]} (h : 1 / 2 ≤ q.re) :
    ‖((polarUnit q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * ‖pureComponent q‖ := by apply _root_.YangMills.Construction.ReferenceBounds.norm_polarUnit_sub_one_le_of_half_le_re <;> assumption
include hκ hB hρ1 h0 h1 in
theorem norm_trianglePairing_sub_diag_le {y x x' : Lattice4} (hy : y ∈ D) (hx : x ∈ D) (hx' : x' ∈ D) :
    ‖trianglePairing P0 P1 (y, x, x') - trianglePairing P0 P1 (y, y, y)‖ ≤
      512 * B ^ 3 * (κ * ((supNorm (x - y) : ℝ) + supNorm (x' - y))) := by
  have hq := finiteDiffBound_trianglePairing hκ hB hρ1 h0 h1
  have e : ((y, y, y) : PointTriple) + ((0 : Lattice4), x - y, x' - y) = (y, x, x') := by simp
  have hl : tripleNorm κ ((0 : Lattice4), x - y, x' - y) =
      κ * ((supNorm (x - y) : ℝ) + supNorm (x' - y)) := by
    simp [tripleNorm, supNorm_zero]
  have := hq.norm_sub_le (x := (y, y, y)) (a := ((0 : Lattice4), x - y, x' - y)) ⟨hy, hy, hy⟩
    (by rw [e]; exact ⟨hy, hx, hx'⟩)
  rw [e, hl] at this
  exact this
include hsym hlow in
theorem one_le_re_trianglePairing_diag {y : Lattice4} (hy : y ∈ D) :
    1 ≤ (trianglePairing P0 P1 (y, y, y)).re := by
  have hr := eq_coe_re_of_star_eq (star_pairingValue_self hsym y)
  have hl := hlow y hy
  have e : trianglePairing P0 P1 (y, y, y) = (((pairingValue P0 P1 y y).re ^ 3 : ℝ) : ℍ[ℝ]) := by
    simp only [trianglePairing]
    rw [hr]
    simp [pow_succ, Quaternion.coe_mul]
  rw [e]
  exact one_le_pow₀ hl
include hκ hB hρ1 h0 h1 hsym hlow in
theorem half_le_re_trianglePairing {y x x' : Lattice4} (hy : y ∈ D) (hx : x ∈ D) (hx' : x' ∈ D)
    (hd : 512 * B ^ 3 * (κ * ((supNorm (x - y) : ℝ) + supNorm (x' - y))) ≤ 1 / 2) :
    1 / 2 ≤ (trianglePairing P0 P1 (y, x, x')).re := by
  have h2 := re_sub_norm_sub_le_re (trianglePairing P0 P1 (y, y, y)) (trianglePairing P0 P1 (y, x, x'))
  have h3 := norm_trianglePairing_sub_diag_le hκ hB hρ1 h0 h1 hy hx hx'
  rw [norm_sub_rev] at h2
  have := one_le_re_trianglePairing_diag hsym hlow hy
  linarith
include hκ hB hρ0 hρ1 h0 h1 hsym in
theorem norm_pure_trianglePairing_le {y x t : Lattice4} (hy : y ∈ D) (hx : x ∈ D) (hxt : x + t ∈ D) :
    ‖pureComponent (trianglePairing P0 P1 (y, x, x + t))‖ ≤
      768 * B ^ 2 * ρ * (κ * supNorm (x - y)) * (κ * supNorm t) := by
  have hW := finiteDiffBound_pure_trianglePairing hκ hB hρ0 hρ1 h0 h1
  have e1 : ((y, y, x) : PointTriple) + ((0 : Lattice4), x - y, (0 : Lattice4)) = (y, x, x) := by simp
  have e2 : ((y, y, x) : PointTriple) + ((0 : Lattice4), (0 : Lattice4), t) = (y, y, x + t) := by simp
  have e3 : ((y, y, x + t) : PointTriple) + ((0 : Lattice4), x - y, (0 : Lattice4)) = (y, x, x + t) := by simp
  have hl1 : tripleNorm κ ((0 : Lattice4), x - y, (0 : Lattice4)) = κ * supNorm (x - y) := by
    simp [tripleNorm, supNorm_zero]
  have hl2 : tripleNorm κ ((0 : Lattice4), (0 : Lattice4), t) = κ * supNorm t := by
    simp [tripleNorm, supNorm_zero]
  have := hW.norm_second_diff_le (x := (y, y, x)) (a := ((0 : Lattice4), x - y, (0 : Lattice4)))
    (b := ((0 : Lattice4), (0 : Lattice4), t))
    ⟨hy, hy, hx⟩ (by rw [e1]; exact ⟨hy, hx, hx⟩) (by rw [e2]; exact ⟨hy, hy, hxt⟩)
    (by rw [e2, e3]; exact ⟨hy, hx, hxt⟩)
  rw [e2, e3, e1, hl1, hl2] at this
  simp only [pure_trianglePairing_fst_eq hsym, pure_trianglePairing_snd_eq hsym, sub_zero] at this
  exact this
theorem polarUnit_trianglePairing {y x x' : Lattice4} (h1' : pairingValue P0 P1 y x ≠ 0)
    (h2' : pairingValue P0 P1 x x' ≠ 0) (h3' : pairingValue P0 P1 x' y ≠ 0) :
    polarUnit (pairingValue P0 P1 y x) * polarUnit (pairingValue P0 P1 x x') *
        polarUnit (pairingValue P0 P1 x' y) =
      polarUnit (trianglePairing P0 P1 (y, x, x')) := by
  simp only [trianglePairing]
  rw [polarUnit_mul (mul_ne_zero h1' h2') h3', polarUnit_mul h1' h2']
end Main
section FanBilinear
variable {κ ρ B : ℝ} {D : Set Lattice4} {P0 : Lattice4 × Lattice4 → ℝ} {P1 : Lattice4 × Lattice4 → ℍ[ℝ]}
def fanPure (P0 : Lattice4 × Lattice4 → ℝ) (P1 : Lattice4 × Lattice4 → ℍ[ℝ]) (u v : Lattice4) : ℍ[ℝ] :=
  pureComponent (trianglePairing P0 P1 (0, u, v))
variable (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
  (h0 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0)
  (h1 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1)
  (hsym : ∀ a b, pairingValue P0 P1 b a = star (pairingValue P0 P1 a b))
include hκ hB hρ0 hρ1 h0 h1 hsym in
theorem norm_fanPure_add_left_le {u u' v : Lattice4} (hz : (0 : Lattice4) ∈ D) (hu : u ∈ D) (hu' : u' ∈ D)
    (hv : v ∈ D) (huu : u + u' ∈ D) :
    ‖fanPure P0 P1 (u + u') v - fanPure P0 P1 u v - fanPure P0 P1 u' v‖ ≤
      768 * B ^ 2 * ρ * κ ^ 3 * supNorm v * supNorm u * supNorm u' := by
  have hW := finiteDiffBound_pure_trianglePairing hκ hB hρ0 hρ1 h0 h1
  have hu'u : u' + u ∈ D := by rwa [add_comm]
  have := hW.norm_third_diff_le (x := ((0 : Lattice4), (0 : Lattice4), (0 : Lattice4)))
    (a := ((0 : Lattice4), (0 : Lattice4), v))
    (b := ((0 : Lattice4), u, (0 : Lattice4))) (c := ((0 : Lattice4), u', (0 : Lattice4)))
    ⟨hz, hz, hz⟩ (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hz, hv⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu, hz⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu, hv⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu', hz⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu', hv⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu'u, hz⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu'u, hv⟩)
  simp only [Prod.mk_add_mk, add_zero, zero_add, pure_trianglePairing_thd_eq hsym,
    pure_trianglePairing_fst_eq hsym, sub_zero, tripleNorm, supNorm_zero, Nat.cast_zero] at this
  unfold fanPure
  rw [add_comm u u']
  have e : ‖pureComponent (trianglePairing P0 P1 (0, u' + u, v)) - pureComponent (trianglePairing P0 P1 (0, u, v)) -
      pureComponent (trianglePairing P0 P1 (0, u', v))‖ =
      ‖pureComponent (trianglePairing P0 P1 (0, u' + u, v)) - pureComponent (trianglePairing P0 P1 (0, u', v)) -
      pureComponent (trianglePairing P0 P1 (0, u, v))‖ := by
    congr 1
    abel
  rw [e]
  refine this.trans (le_of_eq ?_)
  ring
include hκ hB hρ0 hρ1 h0 h1 hsym in
theorem norm_fanPure_add_right_le {u v v' : Lattice4} (hz : (0 : Lattice4) ∈ D) (hu : u ∈ D) (hv : v ∈ D)
    (hv' : v' ∈ D) (hvv : v + v' ∈ D) :
    ‖fanPure P0 P1 u (v + v') - fanPure P0 P1 u v - fanPure P0 P1 u v'‖ ≤
      768 * B ^ 2 * ρ * κ ^ 3 * supNorm u * supNorm v * supNorm v' := by
  have hW := finiteDiffBound_pure_trianglePairing hκ hB hρ0 hρ1 h0 h1
  have hv'v : v' + v ∈ D := by rwa [add_comm]
  have := hW.norm_third_diff_le (x := ((0 : Lattice4), (0 : Lattice4), (0 : Lattice4)))
    (a := ((0 : Lattice4), u, (0 : Lattice4)))
    (b := ((0 : Lattice4), (0 : Lattice4), v)) (c := ((0 : Lattice4), (0 : Lattice4), v'))
    ⟨hz, hz, hz⟩ (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu, hz⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hz, hv⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu, hv⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hz, hv'⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu, hv'⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hz, hv'v⟩)
    (by simp only [Prod.mk_add_mk, add_zero, zero_add]; exact ⟨hz, hu, hv'v⟩)
  simp only [Prod.mk_add_mk, add_zero, zero_add, pure_trianglePairing_thd_eq hsym,
    pure_trianglePairing_fst_eq hsym, sub_zero, tripleNorm, supNorm_zero, Nat.cast_zero] at this
  unfold fanPure
  rw [add_comm v v']
  have e : ‖pureComponent (trianglePairing P0 P1 (0, u, v' + v)) - pureComponent (trianglePairing P0 P1 (0, u, v)) -
      pureComponent (trianglePairing P0 P1 (0, u, v'))‖ =
      ‖pureComponent (trianglePairing P0 P1 (0, u, v' + v)) - pureComponent (trianglePairing P0 P1 (0, u, v')) -
      pureComponent (trianglePairing P0 P1 (0, u, v))‖ := by
    congr 1
    abel
  rw [e]
  refine this.trans (le_of_eq ?_)
  ring
def fanMatrix (P0 : Lattice4 × Lattice4 → ℝ) (P1 : Lattice4 × Lattice4 → ℍ[ℝ]) : Fin 4 → Fin 4 → ℍ[ℝ] :=
  fun μ ν => fanPure P0 P1 (basisVector μ) (basisVector ν)
include hsym in
theorem fanMatrix_antisymm (μ ν : Fin 4) : fanMatrix P0 P1 ν μ = - fanMatrix P0 P1 μ ν :=
  pure_trianglePairing_swap hsym 0 (basisVector μ) (basisVector ν)
include hκ hB hρ0 hρ1 h0 h1 hsym in
theorem norm_fanPure_sub_bilinForm_le {lo hi : Fin 4 → ℤ} (hlo : ∀ μ, lo μ ≤ -1) (hhi : ∀ μ, 1 ≤ hi μ)
    (hD : ∀ x ∈ intBox lo hi, x ∈ D) {u v : Lattice4} (hu : u ∈ intBox lo hi) (hv : v ∈ intBox lo hi) :
    ‖fanPure P0 P1 u v - bilinForm (fanMatrix P0 P1) u v‖ ≤
      768 * B ^ 2 * ρ * κ ^ 3 * (11 * (supNorm u : ℝ) ^ 2 * supNorm v +
        44 * supNorm u * (supNorm v : ℝ) ^ 2) := by
  set E0 : ℝ := 768 * B ^ 2 * ρ * κ ^ 3 with hE0
  have hE : 0 ≤ E0 := by positivity
  have hz : (0 : Lattice4) ∈ intBox lo hi := by
    intro μ
    have a1 := hlo μ
    have a2 := hhi μ
    simp only [Pi.zero_apply]
    constructor <;> linarith
  have hunit : ∀ μ, basisVector μ ∈ intBox lo hi := by
    intro μ ν
    have a1 := hlo ν
    have a2 := hhi ν
    by_cases h : ν = μ
    · subst h; simp [basisVector]; constructor <;> linarith
    · simp [basisVector, h]; constructor <;> linarith
  have hu0 : (0 : ℝ) ≤ supNorm u := Nat.cast_nonneg _
  have n1 := norm_sub_linear_le_of_almost_additive (G := fun w => fanPure P0 P1 w v)
    (E := E0 * supNorm v) (lo := lo) (hi := hi)
    (by positivity) (pure_trianglePairing_fst_eq hsym 0 v) hlo hhi (fun a a' ha ha' haa => by
      have := norm_fanPure_add_left_le hκ hB hρ0 hρ1 h0 h1 hsym (hD _ hz) (hD _ ha) (hD _ ha') (hD _ hv)
        (hD _ haa)
      exact this) hu
  have n2 : ∀ μ, ‖fanPure P0 P1 (basisVector μ) v - ∑ ν, (v ν : ℝ) • fanMatrix P0 P1 μ ν‖ ≤
      11 * E0 * (supNorm v : ℝ) ^ 2 := by
    intro μ
    have := norm_sub_linear_le_of_almost_additive (G := fun w => fanPure P0 P1 (basisVector μ) w)
      (E := E0) (lo := lo) (hi := hi)
      hE (pure_trianglePairing_thd_eq hsym 0 (basisVector μ)) hlo hhi (fun a a' ha ha' haa => by
        have := norm_fanPure_add_right_le hκ hB hρ0 hρ1 h0 h1 hsym (hD _ hz) (hD _ (hunit μ)) (hD _ ha)
          (hD _ ha') (hD _ haa)
        rw [supNorm_basisVector] at this
        simpa using this) hv
    exact this
  have e1 : bilinForm (fanMatrix P0 P1) u v = ∑ μ, (u μ : ℝ) • ∑ ν, (v ν : ℝ) • fanMatrix P0 P1 μ ν := by
    simp only [bilinForm, Finset.smul_sum, smul_smul]
  have e2 : fanPure P0 P1 u v - bilinForm (fanMatrix P0 P1) u v =
      (fanPure P0 P1 u v - ∑ μ, (u μ : ℝ) • fanPure P0 P1 (basisVector μ) v) +
        ∑ μ, (u μ : ℝ) • (fanPure P0 P1 (basisVector μ) v - ∑ ν, (v ν : ℝ) • fanMatrix P0 P1 μ ν) := by
    rw [e1]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  have e3 : ‖∑ μ, (u μ : ℝ) • (fanPure P0 P1 (basisVector μ) v - ∑ ν, (v ν : ℝ) • fanMatrix P0 P1 μ ν)‖ ≤
      4 * ((supNorm u : ℝ) * (11 * E0 * (supNorm v : ℝ) ^ 2)) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ μ ∈ (Finset.univ : Finset (Fin 4)),
        ‖(u μ : ℝ) • (fanPure P0 P1 (basisVector μ) v - ∑ ν, (v ν : ℝ) • fanMatrix P0 P1 μ ν)‖ ≤
          (supNorm u : ℝ) * (11 * E0 * (supNorm v : ℝ) ^ 2) := by
      intro μ _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (abs_coord_le_supNorm u μ) (n2 μ) (norm_nonneg _) hu0
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have n1' : ‖fanPure P0 P1 u v - ∑ μ, (u μ : ℝ) • fanPure P0 P1 (basisVector μ) v‖ ≤
      11 * (E0 * supNorm v) * (supNorm u : ℝ) ^ 2 := n1
  calc _ ≤ 11 * (E0 * supNorm v) * (supNorm u : ℝ) ^ 2 +
        4 * ((supNorm u : ℝ) * (11 * E0 * (supNorm v : ℝ) ^ 2)) := add_le_add n1' e3
    _ = _ := by ring
end FanBilinear
section Estimates
variable {κ ρ B : ℝ} {D : Set Lattice4} {P0 : Lattice4 × Lattice4 → ℝ} {P1 : Lattice4 × Lattice4 → ℍ[ℝ]}
variable (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
  (h0 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0)
  (h1 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1)
  (hsym : ∀ a b, pairingValue P0 P1 b a = star (pairingValue P0 P1 a b))
  (hlow : ∀ a ∈ D, 1 ≤ (pairingValue P0 P1 a a).re)
include hsym in
theorem polarUnit_pairingValue_swap (a b : Lattice4) :
    polarUnit (pairingValue P0 P1 b a) = (polarUnit (pairingValue P0 P1 a b))⁻¹ := by
  rw [hsym a b, polarUnit_star]
include hsym hlow in
theorem polarUnit_pairingValue_self {a : Lattice4} (ha : a ∈ D) : polarUnit (pairingValue P0 P1 a a) = 1 := by
  have hr := eq_coe_re_of_star_eq (star_pairingValue_self hsym a)
  have hl := hlow a ha
  rw [hr]
  exact polarUnit_coe (by linarith)
theorem supNorm_sub_comm (a b : Lattice4) : supNorm (a - b) = supNorm (b - a) := by
  rw [← neg_sub, supNorm_neg]
theorem fan_step_bounds (L : ℕ) (i : Fin 4) (hL3 : 3 ≤ L) (hr : κ * (3 * L) ≤ 1 / (4096 * B ^ 3))
    (hD : ∀ x ∈ twoBlockHull L i, x ∈ D) (u : Lattice4) (st : PathStep) (hu : u ∈ twoBlockHull L i)
    (hv : u + stepDisplacement st ∈ twoBlockHull L i) (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (h0 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0)
    (h1 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1)
    (hsym : ∀ a b, pairingValue P0 P1 b a = star (pairingValue P0 P1 a b))
    (hlow : ∀ a ∈ D, 1 ≤ (pairingValue P0 P1 a a).re) :
    ‖((polarUnit (pairingValue P0 P1 0 u) * polarUnit (pairingValue P0 P1 u (u + stepDisplacement st)) *
        polarUnit (pairingValue P0 P1 (u + stepDisplacement st) 0) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        8 * (768 * B ^ 2) * ρ * κ ^ 2 * L ∧
      ‖pureComponent (((polarUnit (pairingValue P0 P1 0 u) *
          polarUnit (pairingValue P0 P1 u (u + stepDisplacement st)) *
          polarUnit (pairingValue P0 P1 (u + stepDisplacement st) 0) : UnitQuaternion) : ℍ[ℝ]) - 1) -
        (‖trianglePairing P0 P1 (0, 0, 0)‖)⁻¹ • bilinForm (fanMatrix P0 P1) u (stepDisplacement st)‖ ≤
        (16 * (768 * B ^ 2) * (512 * B ^ 3) + 136 * (768 * B ^ 2)) * ρ * κ ^ 3 * (L : ℝ) ^ 2 := by
  set v := u + stepDisplacement st with hvdef
  set t := stepDisplacement st with htdef
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hL1 : (1 : ℝ) ≤ L := by
    have : 1 ≤ L := by omega
    exact_mod_cast this
  have hB3 : (1 : ℝ) ≤ B ^ 3 := one_le_pow₀ hB
  have hr' : 512 * B ^ 3 * (κ * (3 * L)) ≤ 1 / 8 := by
    have : 512 * B ^ 3 * (κ * (3 * L)) ≤ 512 * B ^ 3 * (1 / (4096 * B ^ 3)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
    norm_num
  have hBB : B ≤ B ^ 3 := by nlinarith [sq_nonneg B, mul_self_nonneg (B - 1)]
  have hz : (0 : Lattice4) ∈ twoBlockHull L i := by
    intro μ
    have : (0 : ℤ) ≤ if μ = i then (L : ℤ) else 0 := by split_ifs <;> omega
    simp only [Pi.zero_apply]
    constructor <;> omega
  have hlen : ∀ w ∈ twoBlockHull L i, (supNorm w : ℝ) ≤ 2 * L := by
    intro w hw
    have : supNorm w ≤ 2 * L := by
      rw [supNorm_le_iff]
      intro μ
      have h2 := hw μ
      have a3 : (if μ = i then (L : ℤ) else 0) ≤ L := by split_ifs <;> omega
      omega
    exact_mod_cast this
  have ht1 : supNorm t = 1 := supNorm_stepDisplacement st
  have ht : t ∈ twoBlockHull L i := by
    intro μ
    have a : |t μ| ≤ 1 := by
      have := natAbs_le_supNorm t μ
      rw [ht1] at this
      rw [Int.abs_eq_natAbs]
      exact_mod_cast this
    have a3 : (0 : ℤ) ≤ if μ = i then (L : ℤ) else 0 := by split_ifs <;> omega
    have := abs_le.1 a
    constructor <;> omega
  have du := hD _ hu
  have dv := hD _ hv
  have dz := hD _ hz
  have dt := hD _ ht
  have lu := hlen u hu
  have lv := hlen v hv
  have hpr : ∀ a ∈ D, ∀ b ∈ D, (supNorm (b - a) : ℝ) ≤ 2 * L → 1 / 2 ≤ (pairingValue P0 P1 a b).re := by
    intro a ha b hb hd
    refine half_le_re_pairingValue hκ hB hρ1 h0 h1 hlow ha hb ?_
    have : 2 * B * (κ * supNorm (b - a)) ≤ 512 * B ^ 3 * (κ * (3 * L)) := by
      have q1 : κ * supNorm (b - a) ≤ κ * (3 * L) := mul_le_mul_of_nonneg_left (by linarith) hκ
      have q2 : 2 * B ≤ 512 * B ^ 3 := by linarith
      exact mul_le_mul q2 q1 (by positivity) (by positivity)
    linarith
  have p1 := hpr 0 dz u du (by simpa using lu)
  have p2 := hpr u du v dv (by rw [hvdef]; simp only [add_sub_cancel_left]; rw [ht1]; simp; linarith)
  have p3 := hpr v dv 0 dz (by
    have : supNorm ((0 : Lattice4) - v) = supNorm v := by simp [supNorm_neg]
    rw [this]; exact lv)
  set q := trianglePairing P0 P1 (0, u, v) with hq
  set q0 := trianglePairing P0 P1 (0, 0, 0) with hq0
  have hcl : ‖q - q0‖ ≤ 512 * B ^ 3 * (κ * (4 * L)) := by
    have := norm_trianglePairing_sub_diag_le hκ hB hρ1 h0 h1 dz du dv
    simp only [sub_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hκ) (by positivity))
    linarith
  have hqre : 1 / 2 ≤ q.re := by
    refine half_le_re_trianglePairing hκ hB hρ1 h0 h1 hsym hlow dz du dv ?_
    simp only [sub_zero]
    have : κ * ((supNorm u : ℝ) + supNorm v) ≤ κ * (4 * L) :=
      mul_le_mul_of_nonneg_left (by linarith) hκ
    have h2 : 512 * B ^ 3 * (κ * ((supNorm u : ℝ) + supNorm v)) ≤ 512 * B ^ 3 * (κ * (4 * L)) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hW : ‖pureComponent q‖ ≤ 768 * B ^ 2 * ρ * (κ * (2 * L)) * κ := by
    have := norm_pure_trianglePairing_le hκ hB hρ0 hρ1 h0 h1 hsym (y := 0) (x := u) (t := t) dz du dv
    rw [sub_zero, ht1] at this
    refine this.trans ?_
    simp only [Nat.cast_one, mul_one]
    refine mul_le_mul_of_nonneg_right ?_ hκ
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left lu hκ) (by positivity)
  have hT : polarUnit (pairingValue P0 P1 0 u) * polarUnit (pairingValue P0 P1 u v) *
      polarUnit (pairingValue P0 P1 v 0) = polarUnit q :=
    polarUnit_trianglePairing (ne_zero_of_half_le_re p1) (ne_zero_of_half_le_re p2) (ne_zero_of_half_le_re p3)
  rw [hT]
  constructor
  · refine (norm_polarUnit_sub_one_le_of_half_le_re hqre).trans ?_
    have : 4 * ‖pureComponent q‖ ≤ 4 * (768 * B ^ 2 * ρ * (κ * (2 * L)) * κ) := by linarith
    refine this.trans (le_of_eq ?_)
    ring
  · have hqn : 1 / 2 ≤ ‖q‖ := half_le_norm_of_half_le_re hqre
    have hq0n : 1 ≤ ‖q0‖ := (one_le_re_trianglePairing_diag hsym hlow dz).trans (quaternion_re_le_norm _)
    set Bv := bilinForm (fanMatrix P0 P1) u t with hBv
    have e1 : pureComponent (((polarUnit q : UnitQuaternion) : ℍ[ℝ]) - 1) = ‖q‖⁻¹ • pureComponent q := by
      rw [pureComponent_sub, pureComponent_one, sub_zero, pureComponent_polarUnit (ne_zero_of_half_le_re hqre)]
    rw [e1]
    have hb : ‖pureComponent q - Bv‖ ≤ 136 * (768 * B ^ 2 * ρ * κ ^ 3) * (L : ℝ) ^ 2 := by
      have a1 := norm_fanPure_add_right_le hκ hB hρ0 hρ1 h0 h1 hsym dz du du dt (hD _ hv)
      have a2 := norm_fanPure_sub_bilinForm_le (lo := fun _ => -(((L : ℤ) - 1) / 2))
        (hi := fun μ => ((L : ℤ) - 1) / 2 + if μ = i then (L : ℤ) else 0) hκ hB hρ0 hρ1 h0 h1 hsym
        (fun μ => by omega) (fun μ => by
          have : (0 : ℤ) ≤ if μ = i then (L : ℤ) else 0 := by split_ifs <;> omega
          omega) hD hu ht
      have e2 : fanPure P0 P1 u u = 0 := pure_trianglePairing_snd_eq hsym 0 u
      rw [e2, ht1] at a1
      rw [ht1] at a2
      have e3 : pureComponent q - Bv = (fanPure P0 P1 u (u + t) - 0 - fanPure P0 P1 u t) +
          (fanPure P0 P1 u t - bilinForm (fanMatrix P0 P1) u t) := by
        simp only [fanPure, hq, hvdef, hBv, sub_zero]
        abel
      rw [e3]
      refine (norm_add_le _ _).trans ?_
      have hE : 0 ≤ 768 * B ^ 2 * ρ * κ ^ 3 := by positivity
      have s2 : (supNorm u : ℝ) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by nlinarith
      have s3 : (supNorm u : ℝ) ≤ 2 * (L : ℝ) ^ 2 := by nlinarith
      simp only [Nat.cast_one, mul_one, one_pow] at a1 a2
      have t1 : 768 * B ^ 2 * ρ * κ ^ 3 * (supNorm u : ℝ) * (supNorm u : ℝ) ≤
          768 * B ^ 2 * ρ * κ ^ 3 * (4 * (L : ℝ) ^ 2) := by
        have : (supNorm u : ℝ) * supNorm u ≤ 4 * (L : ℝ) ^ 2 := by nlinarith
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left this hE
      have t2 : 768 * B ^ 2 * ρ * κ ^ 3 * (11 * (supNorm u : ℝ) ^ 2 + 44 * (supNorm u : ℝ)) ≤
          768 * B ^ 2 * ρ * κ ^ 3 * (132 * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hE
      linarith
    have e4 : ‖q‖⁻¹ • pureComponent q - (‖q0‖)⁻¹ • Bv =
        (‖q‖⁻¹ - (‖q0‖)⁻¹) • pureComponent q + (‖q0‖)⁻¹ • (pureComponent q - Bv) := by
      rw [sub_smul, smul_sub]
      abel
    rw [e4]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hqpos : 0 < ‖q‖ := by linarith
    have b1 : |‖q‖⁻¹ - (‖q0‖)⁻¹| ≤ 2 * (512 * B ^ 3 * (κ * (4 * L))) := by
      have e5 : ‖q‖⁻¹ - (‖q0‖)⁻¹ = (‖q0‖ - ‖q‖) * (‖q‖⁻¹ * (‖q0‖)⁻¹) := by
        field_simp
      rw [e5, abs_mul]
      have c1 : |‖q0‖ - ‖q‖| ≤ ‖q - q0‖ := by
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le q q0
      have c2 : |‖q‖⁻¹ * (‖q0‖)⁻¹| ≤ 2 := by
        rw [abs_of_nonneg (by positivity)]
        have d1 : ‖q‖⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hqpos (by norm_num)]
          linarith
        have d2 : (‖q0‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq0n
        have d3 : 0 ≤ (‖q0‖)⁻¹ := by positivity
        nlinarith [inv_nonneg.2 hqpos.le]
      calc _ ≤ (512 * B ^ 3 * (κ * (4 * L))) * 2 :=
            mul_le_mul (c1.trans hcl) c2 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have b2 : |(‖q0‖)⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ hq0n
    have m1 := mul_le_mul b1 hW (norm_nonneg _) (by positivity)
    have m2 := mul_le_mul b2 hb (norm_nonneg _) (by norm_num)
    refine (add_le_add m1 m2).trans (le_of_eq ?_)
    ring
end Estimates
section Assembly
variable {κ ρ B : ℝ} {D : Set Lattice4} {P0 : Lattice4 × Lattice4 → ℝ} {P1 : Lattice4 × Lattice4 → ℍ[ℝ]}
theorem closedBlockContour_eq_fanProduct (hsym : ∀ a b, pairingValue P0 P1 b a = star (pairingValue P0 P1 a b))
    (hlow : ∀ a ∈ D, 1 ≤ (pairingValue P0 P1 a a).re) (hz : (0 : Lattice4) ∈ D) (L : ℕ) (h : Lattice4)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4)
    (hend : pathEndpoint 0 (bondContour L h π i) = (L : ℤ) • basisVector i) :
    closedBlockContour (fun a b => polarUnit (pairingValue P0 P1 a b)) L h π i =
      fanProduct (fun a b => polarUnit (pairingValue P0 P1 a b)) 0 (bondContour L h π i) := by
  have := fanProduct_eq (R := fun a b => polarUnit (pairingValue P0 P1 a b))
    (fun a b => polarUnit_pairingValue_swap hsym a b) 0 (bondContour L h π i)
  simp only [polarUnit_pairingValue_self hsym hlow hz, one_mul, hend] at this
  exact this
theorem closedBlockContour_estimates (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (h0 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) B P0)
    (h1 : FiniteDiffBound (scaledPairNorm κ) 3 (D ×ˢ D) ρ P1)
    (hsym : ∀ a b, pairingValue P0 P1 b a = star (pairingValue P0 P1 a b))
    (hlow : ∀ a ∈ D, 1 ≤ (pairingValue P0 P1 a a).re) (L : ℕ) (i : Fin 4) (hodd : Odd L) (hL3 : 3 ≤ L)
    (hr : κ * (3 * L) ≤ 1 / (4096 * B ^ 3)) (hD : ∀ x ∈ twoBlockHull L i, x ∈ D) :
    (∀ h ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4),
      ‖((closedBlockContour (fun a b => polarUnit (pairingValue P0 P1 a b)) L h π i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        40 * (768 * B ^ 2) * ρ * (κ * L) ^ 2) ∧
    ‖(1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
      pureComponent ((closedBlockContour (fun a b => polarUnit (pairingValue P0 P1 a b)) L h π i :
        UnitQuaternion) : ℍ[ℝ])‖ ≤
        (5 * (16 * (768 * B ^ 2) * (512 * B ^ 3) + 136 * (768 * B ^ 2)) + 1600 * (768 * B ^ 2) ^ 2) * ρ *
          (κ * L) ^ 3 := by
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hL1 : 1 ≤ L := by omega
  set M : ℝ := 768 * B ^ 2 with hM
  set Mq : ℝ := 512 * B ^ 3 with hMq
  set e : ℝ := 8 * M * ρ * κ ^ 2 * L with he
  set e2 : ℝ := (16 * M * Mq + 136 * M) * ρ * κ ^ 3 * (L : ℝ) ^ 2 with he2
  have he0 : 0 ≤ e := by positivity
  have he20 : 0 ≤ e2 := by positivity
  set R : Lattice4 → Lattice4 → UnitQuaternion := fun a b => polarUnit (pairingValue P0 P1 a b) with hR
  set good : Lattice4 → Prop := fun v => v ∈ twoBlockHull L i with hgood
  have hz : (0 : Lattice4) ∈ D := by
    refine hD 0 fun μ => ?_
    have : (0 : ℤ) ≤ if μ = i then (L : ℤ) else 0 := by split_ifs <;> omega
    simp only [Pi.zero_apply]
    constructor <;> omega
  have hstep := fun (u : Lattice4) (st : PathStep) (hu : good u) (hv : good (u + stepDisplacement st)) =>
    fan_step_bounds (P0 := P0) (P1 := P1) L i hL3 hr hD u st hu hv hκ hB hρ0 hρ1 h0 h1 hsym hlow
  have hb1 : ∀ u st, good u → good (u + stepDisplacement st) →
      ‖((R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e :=
    fun u st hu hv => (hstep u st hu hv).1
  set z : ℝ := (‖trianglePairing P0 P1 (0, 0, 0)‖)⁻¹ with hzdef
  have hb2 : ∀ u st, good u → good (u + stepDisplacement st) →
      ‖pureComponent (((R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 :
          UnitQuaternion) : ℍ[ℝ]) - 1) -
        z • bilinForm (fanMatrix P0 P1) u (stepDisplacement st)‖ ≤ e2 :=
    fun u st hu hv => (hstep u st hu hv).2
  have hκL1 : κ * L ≤ 1 := by
    have hB3 : (1 : ℝ) ≤ B ^ 3 := one_le_pow₀ hB
    have a1 : 1 / (4096 * B ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have a2 : κ * L ≤ κ * (3 * L) := mul_le_mul_of_nonneg_left (by linarith) hκ
    linarith
  have hterm : ∀ h ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4),
      ‖((closedBlockContour R L h π i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 40 * M * ρ * (κ * L) ^ 2 ∧
      ‖pureComponent ((closedBlockContour R L h π i : UnitQuaternion) : ℍ[ℝ]) -
        (z * (2 * (L : ℝ))) • bilinForm (fanMatrix P0 P1) h (basisVector i)‖ ≤
        (5 * (16 * M * Mq + 136 * M) + 1600 * M ^ 2) * ρ * (κ * L) ^ 3 := by
    intro h hh π
    obtain ⟨c1, c2⟩ := bondContour_spec π i hL1 hh
    have clen := length_bondContour_le π i hL1 hh
    have hclen : ((bondContour L h π i).length : ℝ) ≤ 5 * L := by exact_mod_cast clen
    obtain ⟨f1, f2⟩ := norm_fanProduct_sub_one_le (R := R) (good := good) he0 hb1 c1
    have f3 := norm_pure_fanSum_sub_discreteArea_le (F := fanMatrix P0 P1) (good := good) (z := z) hb2 c1
    have hceq := closedBlockContour_eq_fanProduct (P0 := P0) (P1 := P1) hsym hlow hz L h π i c2
    rw [hceq]
    set G := fanProduct R 0 (bondContour L h π i) with hG
    set S := fanSum (fun u st => ((R 0 u * R u (u + stepDisplacement st) * R (u + stepDisplacement st) 0 :
      UnitQuaternion) : ℍ[ℝ]) - 1) 0 (bondContour L h π i) with hS
    have hme : ((bondContour L h π i).length : ℝ) * e ≤ 40 * M * ρ * (κ * L) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hclen he0
      refine this.trans (le_of_eq ?_)
      rw [he]
      ring
    have hme0 : 0 ≤ ((bondContour L h π i).length : ℝ) * e := by positivity
    refine ⟨f1.trans hme, ?_⟩
    have a1 : pureComponent (G : ℍ[ℝ]) - (z * (2 * (L : ℝ))) • bilinForm (fanMatrix P0 P1) h (basisVector i) =
        pureComponent ((G : ℍ[ℝ]) - 1 - S) +
          (pureComponent S - z • discreteArea (fanMatrix P0 P1) 0 (bondContour L h π i)) := by
      rw [discreteArea_bondContour (fun μ ν => fanMatrix_antisymm hsym μ ν), pureComponent_sub, pureComponent_sub,
        pureComponent_one, smul_smul]
      abel
    rw [a1]
    refine (norm_add_le _ _).trans ?_
    have a2 : ‖pureComponent ((G : ℍ[ℝ]) - 1 - S)‖ ≤ (40 * M * ρ * (κ * L) ^ 2) ^ 2 :=
      (norm_pureComponent_le _).trans (f2.trans (pow_le_pow_left₀ hme0 hme 2))
    have a3 : ‖pureComponent S - z • discreteArea (fanMatrix P0 P1) 0 (bondContour L h π i)‖ ≤
        5 * (16 * M * Mq + 136 * M) * ρ * (κ * L) ^ 3 := by
      refine f3.trans ?_
      have := mul_le_mul_of_nonneg_right hclen he20
      refine this.trans (le_of_eq ?_)
      rw [he2]
      ring
    have a4 : (40 * M * ρ * (κ * L) ^ 2) ^ 2 ≤ 1600 * M ^ 2 * ρ * (κ * L) ^ 3 := by
      have e1 : (40 * M * ρ * (κ * L) ^ 2) ^ 2 = 1600 * M ^ 2 * ρ * (κ * L) ^ 3 * (ρ * (κ * L)) := by ring
      rw [e1]
      have e2' : ρ * (κ * L) ≤ 1 := by nlinarith
      have e3 : 0 ≤ 1600 * M ^ 2 * ρ * (κ * L) ^ 3 := by positivity
      nlinarith
    calc _ ≤ (40 * M * ρ * (κ * L) ^ 2) ^ 2 + 5 * (16 * M * Mq + 136 * M) * ρ * (κ * L) ^ 3 :=
          add_le_add a2 a3
      _ ≤ 1600 * M ^ 2 * ρ * (κ * L) ^ 3 + 5 * (16 * M * Mq + 136 * M) * ρ * (κ * L) ^ 3 := by linarith
      _ = _ := by ring
  refine ⟨fun h hh π => (hterm h hh π).1, ?_⟩
  set err : ℝ := (5 * (16 * M * Mq + 136 * M) + 1600 * M ^ 2) * ρ * (κ * L) ^ 3 with herr
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hzero : ∑ h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4),
      (z * (2 * (L : ℝ))) • bilinForm (fanMatrix P0 P1) h (basisVector i) = 0 := by
    simp only [Finset.sum_const, hcard]
    rw [← Finset.smul_sum, ← Finset.smul_sum, sum_centredCube_bilinForm (fun μ ν => fanMatrix_antisymm hsym μ ν)]
    simp
  have hsum : ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
        pureComponent ((closedBlockContour R L h π i : UnitQuaternion) : ℍ[ℝ]) =
      ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
        (pureComponent ((closedBlockContour R L h π i : UnitQuaternion) : ℍ[ℝ]) -
          (z * (2 * (L : ℝ))) • bilinForm (fanMatrix P0 P1) h (basisVector i)) := by
    simp only [Finset.sum_sub_distrib]
    rw [hzero, sub_zero]
  rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb : ‖∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
      (pureComponent ((closedBlockContour R L h π i : UnitQuaternion) : ℍ[ℝ]) -
        (z * (2 * (L : ℝ))) • bilinForm (fanMatrix P0 P1) h (basisVector i))‖ ≤ (L : ℝ) ^ 4 * (24 * err) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ h ∈ centredCube L, ‖∑ π : Equiv.Perm (Fin 4),
        (pureComponent ((closedBlockContour R L h π i : UnitQuaternion) : ℍ[ℝ]) -
          (z * (2 * (L : ℝ))) • bilinForm (fanMatrix P0 P1) h (basisVector i))‖ ≤ 24 * err := by
      intro h hh
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun π _ => (hterm h hh π).2).trans (le_of_eq ?_)
      rw [Finset.sum_const, hcard]
      simp
    refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
    rw [Finset.sum_const, card_centredCube hodd]
    simp
  calc _ ≤ 1 / (24 * (L : ℝ) ^ 4) * ((L : ℝ) ^ 4 * (24 * err)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = err := by
      field_simp
end Assembly
theorem nearlyFlatPairing_holds : nearlyFlatPairingStatement := by
  intro B hB
  have hB3 : (1 : ℝ) ≤ B ^ 3 := one_le_pow₀ hB
  have hB2 : (1 : ℝ) ≤ B ^ 2 := one_le_pow₀ hB
  set M : ℝ := 768 * B ^ 2 with hM
  set Mq : ℝ := 512 * B ^ 3 with hMq
  set r : ℝ := 1 / (4096 * B ^ 3) with hrdef
  have hr0 : 0 < r := by positivity
  have hMqpos : 0 < Mq := by positivity
  refine ⟨4 * M + 40 * M + (5 * (16 * M * Mq + 136 * M) + 1600 * M ^ 2), r, by positivity, hr0, ?_⟩
  set C : ℝ := 4 * M + 40 * M + (5 * (16 * M * Mq + 136 * M) + 1600 * M ^ 2) with hC
  intro κ ρ D P0 P1 hκ hρ0 hρ1 h0 h1 hsym hlow
  have hMr : Mq * r = 1 / 8 := by
    rw [hMq, hrdef]
    field_simp
    norm_num
  have hBr : 2 * B * (2 * r) ≤ 1 / 2 := by
    have h1' : B ≤ B ^ 3 := by nlinarith [sq_nonneg B, mul_self_nonneg (B - 1)]
    have : 4 * B * r ≤ Mq * r := mul_le_mul_of_nonneg_right (by rw [hMq]; linarith) hr0.le
    linarith
  have h4M : 4 * M ≤ C := by
    have : 0 ≤ 40 * M + (5 * (16 * M * Mq + 136 * M) + 1600 * M ^ 2) := by positivity
    rw [hC]; linarith
  have h40 : 40 * M ≤ C := by
    have : 0 ≤ 4 * M + (5 * (16 * M * Mq + 136 * M) + 1600 * M ^ 2) := by positivity
    rw [hC]; linarith
  have hrest : (5 * (16 * M * Mq + 136 * M) + 1600 * M ^ 2) ≤ C := by
    rw [hC]; linarith
  have h4 : 4 ≤ C := by
    have : 1 ≤ M := by rw [hM]; linarith
    linarith
  refine ⟨fun a ha b hb hd => ?_, fun y hy x hx t hxt hd ht => ?_, fun L i hodd hL3 hrL hD => ?_⟩
  · have hre := half_le_re_pairingValue hκ hB hρ1 h0 h1 hlow ha hb (by
      have : 2 * B * (κ * supNorm (b - a)) ≤ 2 * B * r :=
        mul_le_mul_of_nonneg_left hd (by linarith)
      linarith)
    refine (norm_polarUnit_sub_one_le_of_half_le_re hre).trans ?_
    have hp := norm_pure_pairingValue_le h1 hsym ha hb
    calc 4 * ‖pureComponent (pairingValue P0 P1 a b)‖ ≤ 4 * (ρ * (κ * supNorm (b - a))) := by linarith
      _ ≤ C * (ρ * (κ * supNorm (b - a))) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = _ := by ring
  · have hs0 : (0 : ℝ) ≤ supNorm (x - y) := Nat.cast_nonneg _
    have hsum : (supNorm (x + t - y) : ℝ) ≤ supNorm (x - y) + supNorm t := by
      have e : x + t - y = (x - y) + t := by abel
      rw [e]
      exact_mod_cast supNorm_add_le _ _
    have d1 : κ * supNorm (x + t - y) ≤ 2 * r := by
      have : κ * supNorm (x + t - y) ≤ κ * ((supNorm (x - y) : ℝ) + supNorm t) :=
        mul_le_mul_of_nonneg_left hsum hκ
      rw [mul_add] at this
      linarith
    have hre : ∀ a ∈ D, ∀ b ∈ D, κ * supNorm (b - a) ≤ 2 * r → 1 / 2 ≤ (pairingValue P0 P1 a b).re := by
      intro a ha b hb hd'
      refine half_le_re_pairingValue hκ hB hρ1 h0 h1 hlow ha hb ?_
      have : 2 * B * (κ * supNorm (b - a)) ≤ 2 * B * (2 * r) :=
        mul_le_mul_of_nonneg_left hd' (by linarith)
      linarith
    have p1 := hre y hy x hx (by rw [mul_comm 2 r]; nlinarith [hd])
    have p2 := hre x hx (x + t) hxt (by simp only [add_sub_cancel_left]; linarith)
    have p3 := hre (x + t) hxt y hy (by rw [supNorm_sub_comm]; exact d1)
    have hT := polarUnit_trianglePairing (P0 := P0) (P1 := P1) (ne_zero_of_half_le_re p1)
      (ne_zero_of_half_le_re p2) (ne_zero_of_half_le_re p3)
    rw [hT]
    have hqre := half_le_re_trianglePairing hκ hB hρ1 h0 h1 hsym hlow hy hx hxt (by
      have a1 : κ * ((supNorm (x - y) : ℝ) + supNorm (x + t - y)) ≤ 3 * r := by
        rw [mul_add]
        linarith
      have a2 : 512 * B ^ 3 * (κ * ((supNorm (x - y) : ℝ) + supNorm (x + t - y))) ≤ Mq * (3 * r) :=
        mul_le_mul_of_nonneg_left a1 hMqpos.le
      have a3 : Mq * (3 * r) = 3 / 8 := by rw [mul_left_comm, hMr]; norm_num
      linarith)
    refine (norm_polarUnit_sub_one_le_of_half_le_re hqre).trans ?_
    have hW := norm_pure_trianglePairing_le hκ hB hρ0 hρ1 h0 h1 hsym hy hx hxt
    calc 4 * ‖pureComponent (trianglePairing P0 P1 (y, x, x + t))‖
        ≤ 4 * (M * ρ * (κ * supNorm (x - y)) * (κ * supNorm t)) := by linarith
      _ = (4 * M) * ρ * (κ * supNorm (x - y)) * (κ * supNorm t) := by ring
      _ ≤ C * ρ * (κ * supNorm (x - y)) * (κ * supNorm t) := by
          have : 0 ≤ ρ * (κ * supNorm (x - y)) * (κ * supNorm t) := by positivity
          nlinarith
  · obtain ⟨c1, c2⟩ := closedBlockContour_estimates hκ hB hρ0 hρ1 h0 h1 hsym hlow L i hodd hL3 hrL hD
    refine ⟨fun h hh π => (c1 h hh π).trans ?_, c2.trans ?_⟩
    · have : 0 ≤ ρ * (κ * L) ^ 2 := by positivity
      nlinarith
    · have : 0 ≤ ρ * (κ * L) ^ 3 := by positivity
      nlinarith
end FlatPairing
end YangMills.Construction
end
