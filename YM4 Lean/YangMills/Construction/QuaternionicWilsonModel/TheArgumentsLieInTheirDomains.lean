import YangMills.Construction.SystemsWithFiveBounds.TheoremOverASystemWithFiveBounds
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ConditionDomains
open YangMills.Construction.ConfigSpace YangMills.Construction.SystemsWithFiveBounds
open YangMills.Construction.SeparatedTuples (TupleFunctional)
structure DomainsContainArguments : Prop where
  seminorm_finite : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)) (k : ℕ), 1 ≤ k →
    schwartzSeminorm k φ.1 < ⊤
  motion_mem : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)) (r : EuclidMotion),
    motionAct r φ.1 ∈ schwartzFlatOffDiagonal (m + 1)
  perm_mem : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)) (ς : Equiv.Perm (Fin (m + 1))),
    permAct ς φ.1 ∈ schwartzFlatOffDiagonal (m + 1)
  flipConj_mem : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)),
    flipConj φ.1 ∈ schwartzFlatOffDiagonal (m + 1)
  linComb_mem : ∀ (m : ℕ) (c c' : ℂ) (φ ψ : schwartzFlatOffDiagonal (m + 1)),
    c • φ.1 + c' • ψ.1 ∈ schwartzFlatOffDiagonal (m + 1)
  tensor_mem : ∀ (m : ℕ) (X : SepFamilyOfLength (m + 1)), AllSmoothCompact X.1 →
    tensorRealFamily X.1 ∈ schwartzFlatOffDiagonal (m + 1)
  update_exists : ∀ (n : ℕ) (i : Fin n) (b b' : ℝ) (X X' : SepFamilyOfLength n),
    (∀ j, j ≠ i → X.1 j = X'.1 j) →
      ∃ X'' : SepFamilyOfLength n, X''.1 i = b • X.1 i + b' • X'.1 i ∧
        ∀ j, j ≠ i → X''.1 j = X.1 j
  finSupp_mem : ∀ Φ Ψ : PosTimeSeq, PosTimeSeq.IsFinitelySupported Φ →
    PosTimeSeq.IsFinitelySupported Ψ →
      (∀ q : ℕ, flipConjAt (Φ q).1 ∈ flatOffDiagonalAt q) ∧
      (∀ q : ℕ, (Ψ q).1 ∈ flatOffDiagonalAt q) ∧
      (∀ q q' : ℕ, tensorAt (flipConjAt (Φ q).1) (Ψ q').1 ∈
        flatOffDiagonalAt (q + q')) ∧
      ∀ v ∈ zeroTimeHyperplane, ∀ (t : ℝ) (q q' : ℕ),
        tensorAt (flipConjAt (Φ q).1) (shiftActAt (t • v) (Ψ q').1) ∈
          flatOffDiagonalAt (q + q')
structure ArgumentsNotAllZero : Prop where
  exists_family : ∀ n : ℕ, 1 ≤ n → ∃ X : SepFamilyOfLength n, AllSmoothCompact X.1 ∧
    (∀ i, tsupport (X.1 i) ⊆ upperHalfSpace) ∧ tensorRealFamily X.1 ≠ 0
  exists_seq : ∀ m : ℕ, ∃ Φ : PosTimeSeq, PosTimeSeq.IsFinitelySupported Φ ∧
    (Φ (m + 1)).1 ≠ zeroOfDegree (m + 1) ∧
    tensorAt (flipConjAt (Φ (m + 1)).1) (Φ (m + 1)).1 ≠
      zeroOfDegree (m + 1 + (m + 1))
  exists_direction : ∃ v ∈ zeroTimeHyperplane, v ≠ 0
def pairedValueSum (T : FlatSequence) {φ ψ : (q : ℕ) → FnOrScalar q}
    (h : ∀ q q' : ℕ, tensorAt (flipConjAt (φ q)) (ψ q') ∈
      flatOffDiagonalAt (q + q')) (N : ℕ) : ℂ :=
  ∑ p ∈ Finset.range N ×ˢ Finset.range N, T (p.1 + p.2) ⟨_, h p.1 p.2⟩
structure SequenceIdentitiesEverywhere (σ : SeparatedFamily → ℝ) (T : FlatSequence) :
    Prop where
  degree_zero : ∀ c : ℂ, ∃ h : c ∈ flatOffDiagonalAt 0, T 0 ⟨c, h⟩ = c
  map_linComb : ∀ (m : ℕ) (c c' : ℂ) (φ ψ : schwartzFlatOffDiagonal (m + 1)),
    ∃ h : c • φ.1 + c' • ψ.1 ∈ schwartzFlatOffDiagonal (m + 1),
      T.atSucc m ⟨_, h⟩ = c * T.atSucc m φ + c' * T.atSucc m ψ
  map_tensor : ∀ (m : ℕ) (X : SepFamilyOfLength (m + 1)), AllSmoothCompact X.1 →
    ∃ h : tensorRealFamily X.1 ∈ schwartzFlatOffDiagonal (m + 1),
      T.atSucc m ⟨_, h⟩ = (σ ⟨m + 1, X⟩ : ℂ)
  multilinear : ∀ (n : ℕ), 1 ≤ n → ∀ (i : Fin n) (b b' : ℝ) (X X' : SepFamilyOfLength n),
    (∀ j, j ≠ i → X.1 j = X'.1 j) →
      ∃ X'' : SepFamilyOfLength n, X''.1 i = b • X.1 i + b' • X'.1 i ∧
        (∀ j, j ≠ i → X''.1 j = X.1 j) ∧ σ ⟨n, X''⟩ = b * σ ⟨n, X⟩ + b' * σ ⟨n, X'⟩
structure AxiomsEverywhere (T : FlatSequence) : Prop where
  euclid_inv : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)) (r : EuclidMotion),
    ∃ h : motionAct r φ.1 ∈ schwartzFlatOffDiagonal (m + 1),
      T.atSucc m ⟨_, h⟩ = T.atSucc m φ
  os_positive : ∀ Φ : PosTimeSeq, PosTimeSeq.IsFinitelySupported Φ →
    ∃ (h : ∀ q q' : ℕ, tensorAt (flipConjAt (Φ q).1) (Φ q').1 ∈
        flatOffDiagonalAt (q + q')) (N : ℕ),
      (∀ q, N ≤ q → (Φ q).1 = zeroOfDegree q) ∧
        (pairedValueSum T (φ := fun q => (Φ q).1) (ψ := fun q => (Φ q).1) h N).im = 0 ∧
        0 ≤ (pairedValueSum T (φ := fun q => (Φ q).1) (ψ := fun q => (Φ q).1) h N).re
  perm_symm : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)) (ς : Equiv.Perm (Fin (m + 1))),
    ∃ h : permAct ς φ.1 ∈ schwartzFlatOffDiagonal (m + 1),
      T.atSucc m ⟨_, h⟩ = T.atSucc m φ
  cluster : ∀ Φ Ψ : PosTimeSeq, PosTimeSeq.IsFinitelySupported Φ →
    PosTimeSeq.IsFinitelySupported Ψ → ∀ v ∈ zeroTimeHyperplane, v ≠ 0 →
      ∃ (h : ∀ (t : ℝ) (q q' : ℕ), tensorAt (flipConjAt (Φ q).1)
            (shiftActAt (t • v) (Ψ q').1) ∈ flatOffDiagonalAt (q + q'))
        (hΦ : ∀ q : ℕ, flipConjAt (Φ q).1 ∈ flatOffDiagonalAt q)
        (hΨ : ∀ q : ℕ, (Ψ q).1 ∈ flatOffDiagonalAt q) (N : ℕ),
        (∀ q, N ≤ q → (Φ q).1 = zeroOfDegree q ∧ (Ψ q).1 = zeroOfDegree q) ∧
          Tendsto
            (fun t : ℝ => pairedValueSum T (φ := fun q => (Φ q).1)
              (ψ := fun q => shiftActAt (t • v) (Ψ q).1) (h t) N)
            atTop
            (𝓝 ((∑ q ∈ Finset.range N, T q ⟨_, hΦ q⟩) * ∑ q ∈ Finset.range N, T q ⟨_, hΨ q⟩))
  reality : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)),
    ∃ h : flipConj φ.1 ∈ schwartzFlatOffDiagonal (m + 1),
      T.atSucc m ⟨_, h⟩ = conj (T.atSucc m φ)
end YangMills.Construction.ConditionDomains
end
