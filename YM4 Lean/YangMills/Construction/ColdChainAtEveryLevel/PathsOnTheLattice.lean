import YangMills.Construction.ColdChainAtEveryLevel.NearlyFlatPairing
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace LatticePaths
open LatticeFractionalIntegration FlatPairing
open BlockAverages hiding stepDisplacement
section Lengths
theorem natAbs_le_supNorm (u : Lattice4) (μ : Fin 4) : (u μ).natAbs ≤ supNorm u :=
  Finset.le_sup (f := fun i => (u i).natAbs) (Finset.mem_univ μ)
theorem supNorm_le_iff (u : Lattice4) (n : ℕ) : supNorm u ≤ n ↔ ∀ μ, (u μ).natAbs ≤ n :=
  ⟨fun hle μ => (natAbs_le_supNorm u μ).trans hle, fun hle => Finset.sup_le fun μ _ => hle μ⟩
theorem supNorm_zero : supNorm (0 : Lattice4) = 0 := by
  simp [supNorm]
theorem supNorm_neg (u : Lattice4) : supNorm (-u) = supNorm u := by
  simp [supNorm]
theorem supNorm_add_le (u v : Lattice4) : supNorm (u + v) ≤ supNorm u + supNorm v := by
  rw [supNorm_le_iff]
  intro μ
  exact (Int.natAbs_add_le _ _).trans (add_le_add (natAbs_le_supNorm u μ) (natAbs_le_supNorm v μ))
theorem supNorm_basisVector (μ : Fin 4) : supNorm (basisVector μ) = 1 := by
  apply le_antisymm
  · rw [supNorm_le_iff]
    intro ν
    by_cases hν : ν = μ
    · subst hν; simp [basisVector]
    · simp [basisVector, hν]
  · have := natAbs_le_supNorm (basisVector μ) μ
    simpa [basisVector] using this
theorem supNorm_stepDisplacement (s : PathStep) : supNorm (stepDisplacement s) = 1 := by
  unfold stepDisplacement
  split_ifs
  · exact supNorm_basisVector _
  · rw [supNorm_neg]; exact supNorm_basisVector _
end Lengths
section Paths
def AllAlong (p : Lattice4 → Prop) : Lattice4 → List PathStep → Prop
  | u, [] => p u
  | u, s :: r => p u ∧ AllAlong p (u + stepDisplacement s) r
def endpoint : Lattice4 → List PathStep → Lattice4
  | u, [] => u
  | u, s :: r => endpoint (u + stepDisplacement s) r
variable {p q : Lattice4 → Prop}
theorem allAlong_head {u : Lattice4} {l : List PathStep} (hp : AllAlong p u l) : p u := by
  cases l with
  | nil => exact hp
  | cons s r => exact hp.1
theorem allAlong_endpoint {u : Lattice4} {l : List PathStep} (hp : AllAlong p u l) : p (endpoint u l) := by
  induction l generalizing u with
  | nil => exact hp
  | cons s r ih => exact ih hp.2
theorem allAlong_append {u : Lattice4} {l l' : List PathStep} (hp : AllAlong p u l)
    (hp' : AllAlong p (endpoint u l) l') : AllAlong p u (l ++ l') := by
  induction l generalizing u with
  | nil => exact hp'
  | cons s r ih => exact ⟨hp.1, ih hp.2 hp'⟩
theorem endpoint_append (u : Lattice4) (l l' : List PathStep) :
    endpoint u (l ++ l') = endpoint (endpoint u l) l' := by
  induction l generalizing u with
  | nil => rfl
  | cons s r ih => exact ih _
theorem allAlong_mono (hpq : ∀ v, p v → q v) {u : Lattice4} {l : List PathStep} (hp : AllAlong p u l) :
    AllAlong q u l := by
  induction l generalizing u with
  | nil => exact hpq _ hp
  | cons s r ih => exact ⟨hpq _ hp.1, ih hp.2⟩
theorem endpoint_add (u w : Lattice4) (l : List PathStep) : endpoint (u + w) l = endpoint u l + w := by
  induction l generalizing u with
  | nil => rfl
  | cons s r ih =>
    show endpoint (u + w + stepDisplacement s) r = endpoint (u + stepDisplacement s) r + w
    rw [add_right_comm, ih]
theorem allAlong_add {w u : Lattice4} {l : List PathStep} (hp : AllAlong p u l) :
    AllAlong (fun v => p (v - w)) (u + w) l := by
  induction l generalizing u with
  | nil => simpa [AllAlong] using hp
  | cons s r ih =>
    refine ⟨by simpa using hp.1, ?_⟩
    have := ih hp.2
    rwa [add_right_comm] at this
theorem stepDisplacement_flip (s : PathStep) : stepDisplacement (s.1, !s.2) = - stepDisplacement s := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [stepDisplacement]
theorem reversePath_cons (s : PathStep) (r : List PathStep) :
    reversePath (s :: r) = reversePath r ++ [(s.1, !s.2)] := by
  simp [reversePath]
theorem endpoint_reversePath (u : Lattice4) (l : List PathStep) :
    endpoint (endpoint u l) (reversePath l) = u := by
  induction l generalizing u with
  | nil => rfl
  | cons s r ih =>
    rw [reversePath_cons, endpoint_append]
    show endpoint (endpoint (endpoint (u + stepDisplacement s) r) (reversePath r)) [(s.1, !s.2)] = u
    rw [ih]
    show u + stepDisplacement s + stepDisplacement (s.1, !s.2) = u
    rw [stepDisplacement_flip]
    abel
theorem allAlong_reversePath {u : Lattice4} {l : List PathStep} (hp : AllAlong p u l) :
    AllAlong p (endpoint u l) (reversePath l) := by
  induction l generalizing u with
  | nil => exact hp
  | cons s r ih =>
    rw [reversePath_cons]
    refine allAlong_append (ih hp.2) ?_
    have e : endpoint (endpoint (u + stepDisplacement s) r) (reversePath r) = u + stepDisplacement s :=
      endpoint_reversePath _ _
    show AllAlong p (endpoint (endpoint (u + stepDisplacement s) r) (reversePath r)) [(s.1, !s.2)]
    rw [e]
    refine ⟨allAlong_head hp.2, ?_⟩
    show p (u + stepDisplacement s + stepDisplacement (s.1, !s.2))
    rw [stepDisplacement_flip]
    have : u + stepDisplacement s + - stepDisplacement s = u := by abel
    rw [this]
    exact hp.1
theorem endpoint_replicate (u : Lattice4) (s : PathStep) (n : ℕ) :
    endpoint u (List.replicate n s) = u + (n : ℤ) • stepDisplacement s := by
  induction n generalizing u with
  | zero => simp [endpoint]
  | succ n ih =>
    rw [List.replicate_succ]
    show endpoint (u + stepDisplacement s) (List.replicate n s) = _
    rw [ih]
    push_cast
    rw [add_smul, one_smul]
    abel
theorem allAlong_replicate {u : Lattice4} {s : PathStep} {n : ℕ}
    (hk : ∀ k : ℕ, k ≤ n → p (u + (k : ℤ) • stepDisplacement s)) : AllAlong p u (List.replicate n s) := by
  induction n generalizing u with
  | zero => simpa [AllAlong] using hk 0 le_rfl
  | succ n ih =>
    rw [List.replicate_succ]
    refine ⟨by simpa using hk 0 (Nat.zero_le _), ih fun k hkn => ?_⟩
    have := hk (k + 1) (by omega)
    have e : u + stepDisplacement s + (k : ℤ) • stepDisplacement s =
        u + ((k + 1 : ℕ) : ℤ) • stepDisplacement s := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rwa [e]
end Paths
section Legs
def axisBondPath (h : Lattice4) (i : Fin 4) : List PathStep :=
  List.replicate (h i).natAbs (i, decide (0 ≤ h i))
theorem axisPath_eq (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    axisPath h π = axisBondPath h (π 0) ++ (axisBondPath h (π 1) ++ (axisBondPath h (π 2) ++ axisBondPath h (π 3))) := by
  simp [axisPath, axisBondPath, List.finRange_succ, List.flatMap_cons]
def BetweenOrigin (h v : Lattice4) : Prop := ∀ μ, min 0 (h μ) ≤ v μ ∧ v μ ≤ max 0 (h μ)
theorem axisFlow_displacement (h : Lattice4) (i : Fin 4) :
    (((h i).natAbs : ℕ) : ℤ) • stepDisplacement (i, decide (0 ≤ h i)) = h i • basisVector i := by
  by_cases hs : 0 ≤ h i
  · simp [stepDisplacement, hs, abs_of_nonneg hs]
  · have : h i < 0 := not_le.1 hs
    simp [stepDisplacement, hs, abs_of_neg this]
theorem endpoint_axisBondPath (h : Lattice4) (i : Fin 4) (u : Lattice4) :
    endpoint u (axisBondPath h i) = u + h i • basisVector i := by
  unfold axisBondPath
  rw [endpoint_replicate, axisFlow_displacement]
theorem allAlong_axisFlow {h u : Lattice4} {i : Fin 4} (hu : BetweenOrigin h u) (h0 : u i = 0) :
    AllAlong (BetweenOrigin h) u (axisBondPath h i) := by
  refine allAlong_replicate fun k hk μ => ?_
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
    AllAlong (BetweenOrigin h) 0 (axisPath h π) ∧ endpoint 0 (axisPath h π) = h := by
  have hz : BetweenOrigin h 0 := fun μ => by simp
  have n01 : π 1 ≠ π 0 := π.injective.ne (by decide)
  have n02 : π 2 ≠ π 0 := π.injective.ne (by decide)
  have n03 : π 3 ≠ π 0 := π.injective.ne (by decide)
  have n12 : π 2 ≠ π 1 := π.injective.ne (by decide)
  have n13 : π 3 ≠ π 1 := π.injective.ne (by decide)
  have n23 : π 3 ≠ π 2 := π.injective.ne (by decide)
  have p0 := allAlong_axisFlow (i := π 0) hz rfl
  have e0 := endpoint_axisBondPath h (π 0) 0
  have z1 : endpoint 0 (axisBondPath h (π 0)) (π 1) = 0 := by
    rw [e0]; simp [basisVector, n01]
  have p1 := allAlong_axisFlow (i := π 1) (allAlong_endpoint p0) z1
  have e1 := endpoint_axisBondPath h (π 1) (endpoint 0 (axisBondPath h (π 0)))
  have z2 : endpoint (endpoint 0 (axisBondPath h (π 0))) (axisBondPath h (π 1)) (π 2) = 0 := by
    rw [e1, e0]; simp [basisVector, n02, n12]
  have p2 := allAlong_axisFlow (i := π 2) (allAlong_endpoint p1) z2
  have e2 := endpoint_axisBondPath h (π 2) (endpoint (endpoint 0 (axisBondPath h (π 0))) (axisBondPath h (π 1)))
  have z3 : endpoint (endpoint (endpoint 0 (axisBondPath h (π 0))) (axisBondPath h (π 1))) (axisBondPath h (π 2)) (π 3) = 0 := by
    rw [e2, e1, e0]; simp [basisVector, n03, n13, n23]
  have p3 := allAlong_axisFlow (i := π 3) (allAlong_endpoint p2) z3
  have e3 := endpoint_axisBondPath h (π 3)
    (endpoint (endpoint (endpoint 0 (axisBondPath h (π 0))) (axisBondPath h (π 1))) (axisBondPath h (π 2)))
  rw [axisPath_eq]
  refine ⟨allAlong_append p0 (allAlong_append p1 (allAlong_append p2 p3)), ?_⟩
  rw [endpoint_append, endpoint_append, endpoint_append, e3, e2, e1, e0]
  have := Equiv.sum_comp π (fun i => h i • basisVector i)
  rw [Fin.sum_univ_four] at this
  rw [zero_add, this]
  funext ν
  simp [basisVector, Finset.sum_apply, Pi.single_apply]
theorem length_axisPath (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).length = (h (π 0)).natAbs + (h (π 1)).natAbs + (h (π 2)).natAbs + (h (π 3)).natAbs := by
  rw [axisPath_eq]
  simp [axisBondPath]
  ring
end Legs
section Contour
theorem mem_centredCube_iff (L : ℕ) (h : Lattice4) :
    h ∈ centredCube L ↔ ∀ i, -(((L : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((L : ℤ) - 1) / 2 := by
  simp [centredCube, Fintype.mem_piFinset]
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by
  obtain ⟨m, rfl⟩ := hL
  have hk : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by omega
  have h2 : (((m : ℤ) + 1 - -(m : ℤ))).toNat = 2 * m + 1 := by omega
  simp only [centredCube, hk, Fintype.card_piFinset, Int.card_Icc, h2]
  simp
theorem mem_twoBlockHull_of_between {L : ℕ} {h v : Lattice4} {i : Fin 4} (hh : h ∈ centredCube L)
    (hv : BetweenOrigin h v) (hL : 1 ≤ L) : v ∈ twoBlockHull L i := by
  intro μ
  have h1 := ((mem_centredCube_iff L h).1 hh) μ
  have h2 := hv μ
  have hk : (0 : ℤ) ≤ ((L : ℤ) - 1) / 2 := by omega
  have a1 : min 0 (h μ) ≥ -(((L : ℤ) - 1) / 2) := le_min (by omega) h1.1
  have a2 : max 0 (h μ) ≤ ((L : ℤ) - 1) / 2 := max_le hk h1.2
  have a3 : (0 : ℤ) ≤ if μ = i then (L : ℤ) else 0 := by split_ifs <;> omega
  constructor <;> omega
theorem bondContour_spec {L : ℕ} {h : Lattice4} (π : Equiv.Perm (Fin 4)) (i : Fin 4) (hL : 1 ≤ L)
    (hh : h ∈ centredCube L) :
    AllAlong (fun v => v ∈ twoBlockHull L i) 0 (bondContour L h π i) ∧
      endpoint 0 (bondContour L h π i) = (L : ℤ) • basisVector i := by
  obtain ⟨l1, l2⟩ := axisPath_spec h π
  have e1 : stepDisplacement (i, true) = basisVector i := by simp [stepDisplacement]
  have q1 : AllAlong (fun v => v ∈ twoBlockHull L i) 0 (axisPath h π) :=
    allAlong_mono (fun v hv => mem_twoBlockHull_of_between hh hv hL) l1
  have q2 : AllAlong (fun v => v ∈ twoBlockHull L i) (endpoint 0 (axisPath h π))
      (List.replicate L (i, true)) := by
    rw [l2]
    refine allAlong_replicate fun k hk μ => ?_
    have h1 := ((mem_centredCube_iff L h).1 hh) μ
    rw [e1]
    by_cases hμ : μ = i
    · subst hμ
      simp [basisVector]
      constructor <;> omega
    · simp [basisVector, hμ]
      exact h1
  have e2 : endpoint (endpoint 0 (axisPath h π)) (List.replicate L (i, true)) = h + (L : ℤ) • basisVector i := by
    rw [l2, endpoint_replicate, e1]
  have q3 : AllAlong (fun v => v ∈ twoBlockHull L i)
      (endpoint (endpoint 0 (axisPath h π)) (List.replicate L (i, true))) (reversePath (axisPath h π)) := by
    rw [e2]
    have s1 := allAlong_add (w := (L : ℤ) • basisVector i) l1
    have s2 := allAlong_reversePath s1
    rw [endpoint_add, l2] at s2
    refine allAlong_mono (fun v hv μ => ?_) s2
    have h1 := ((mem_centredCube_iff L h).1 hh) μ
    have h2 := hv μ
    by_cases hμ : μ = i
    · subst hμ
      simp [basisVector] at h2 ⊢
      omega
    · simp [basisVector, hμ] at h2 ⊢
      omega
  refine ⟨allAlong_append (allAlong_append q1 q2) ?_, ?_⟩
  · rw [endpoint_append]
    exact q3
  · unfold bondContour
    rw [endpoint_append, endpoint_append, e2, endpoint_add]
    have := endpoint_reversePath 0 (axisPath h π)
    rw [l2] at this
    rw [this, zero_add]
theorem length_bondContour_le {L : ℕ} {h : Lattice4} (π : Equiv.Perm (Fin 4)) (i : Fin 4) (hL : 1 ≤ L)
    (hh : h ∈ centredCube L) : (bondContour L h π i).length ≤ 5 * L := by
  have hlen : ∀ μ, (h μ).natAbs ≤ (L - 1) / 2 := by
    intro μ
    have h1 := ((mem_centredCube_iff L h).1 hh) μ
    omega
  have h0 := hlen (π 0)
  have h1 := hlen (π 1)
  have h2 := hlen (π 2)
  have h3 := hlen (π 3)
  have hl := length_axisPath h π
  have e : (bondContour L h π i).length = 2 * (axisPath h π).length + L := by
    simp [bondContour, reversePath]
    ring
  omega
end Contour
end LatticePaths
end YangMills.Construction
end
