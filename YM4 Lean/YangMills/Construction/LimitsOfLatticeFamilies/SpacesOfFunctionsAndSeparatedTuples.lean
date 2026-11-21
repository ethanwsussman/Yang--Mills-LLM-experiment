import YangMills.Construction.LimitsOfLatticeFamilies.SpaceLengthAndBallsAtEveryRadius
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits.ModelSpace
variable (s : Conventions.StandingParameters) (Y : ModelSpace)
def supportIn {E : Type*} [Zero E] (f : Y.Carrier s → E) : Set (Y.Carrier s) :=
  closureIn s Y {y | f y ≠ 0}
def IsLipschitzReal (f : Y.Carrier s → ℝ) : Prop :=
  TestFunctions.IsLipschitzFor (ModelSpace.dist s Y) f
def lipCompactSupp (A : Set (Y.Carrier s)) : Set (Y.Carrier s → ℝ) :=
  {f | IsLipschitzReal s Y f ∧ IsCompactIn s Y (supportIn s Y f) ∧ supportIn s Y f ⊆ A}
def c1CompactSupp (A : Set (Y.Carrier s)) : Set (Y.Carrier s → ℝ) :=
  {f | IsC1 s Y f ∧ IsCompactIn s Y (supportIn s Y f) ∧ supportIn s Y f ⊆ A}
abbrev FunTuple (n : ℕ) : Type := Fin n → Y.Carrier s → ℝ
def sepTuples (n : ℕ) : Set (FunTuple s Y n) :=
  {f | (∀ i, IsC1 s Y (f i)) ∧ (∀ i, IsCompactIn s Y (supportIn s Y (f i))) ∧
    ∀ i k, i ≠ k → Disjoint (supportIn s Y (f i)) (supportIn s Y (f k))}
def sepTuplesIn (n : ℕ) (ρ : ℝ≥0∞) : Set (FunTuple s Y n) :=
  {f | f ∈ sepTuples s Y n ∧ ∀ i, supportIn s Y (f i) ⊆ ballAtBase s Y ρ}
theorem sepTuplesIn_top (n : ℕ) : sepTuplesIn s Y n ⊤ = sepTuples s Y n := by
  ext f
  simp [sepTuplesIn, ballAtBase_top]
theorem sepTuplesIn_zero (ρ : ℝ≥0∞) :
    sepTuplesIn s Y 0 ρ = {fun i => i.elim0} := by
  ext f
  simp [sepTuplesIn, sepTuples, Subsingleton.elim f fun i => i.elim0]
def lipSepTuplesIn (n : ℕ) (ρ : ℝ≥0∞) : Set (FunTuple s Y n) :=
  {f | (∀ i, IsLipschitzReal s Y (f i)) ∧ (∀ i, IsCompactIn s Y (supportIn s Y (f i))) ∧
    (∀ i k, i ≠ k → Disjoint (supportIn s Y (f i)) (supportIn s Y (f k))) ∧
    ∀ i, supportIn s Y (f i) ⊆ ballAtBase s Y ρ}
def lipTuplesApart (n : ℕ) (d R : ℝ) : Set (FunTuple s Y n) :=
  {f | (∀ i, IsLipschitzReal s Y (f i)) ∧
    (∀ i, ∃ x, supportIn s Y (f i) ⊆ ModelSpace.closedBall s Y x R) ∧
    ∀ i k, i ≠ k → ENNReal.ofReal d ≤ infDist s Y (supportIn s Y (f i)) (supportIn s Y (f k))}
variable {s Y}
abbrev TupleFunctional {n : ℕ} (C : Set (FunTuple s Y n)) : Type := C → ℝ
def TupleFunctional.extend {n : ℕ} {C : Set (FunTuple s Y n)} (Ψ : TupleFunctional C)
    (g : FunTuple s Y n) : ℝ :=
  open Classical in if h : g ∈ C then Ψ ⟨g, h⟩ else 0
theorem TupleFunctional.extend_of_mem {n : ℕ} {C : Set (FunTuple s Y n)} (Ψ : TupleFunctional C)
    {g : FunTuple s Y n} (h : g ∈ C) : Ψ.extend g = Ψ ⟨g, h⟩ := dif_pos h
def IsMultilinearOn {n : ℕ} (F : FunTuple s Y n → ℝ) (W : Fin n → Set (Y.Carrier s → ℝ)) :
    Prop :=
  ∀ g : FunTuple s Y n, (∀ l, g l ∈ W l) → ∀ i, ∀ u ∈ W i, ∀ v ∈ W i, ∀ α β : ℝ,
    F (Function.update g i (α • u + β • v)) =
      α * F (Function.update g i u) + β * F (Function.update g i v)
def IsMultilinearSep {n : ℕ} {ρ : ℝ≥0∞}
    (Ψ : TupleFunctional (sepTuplesIn s Y n ρ)) : Prop :=
  ∀ A : Fin n → Set (Y.Carrier s), (∀ l, A l ⊆ ballAtBase s Y ρ) →
    (∀ l k, l ≠ k → Disjoint (A l) (A k)) →
      IsMultilinearOn Ψ.extend fun l => c1CompactSupp s Y (A l)
def IsMultilinearLip {n : ℕ} {ρ : ℝ≥0∞}
    (Ψ : TupleFunctional (lipSepTuplesIn s Y n ρ)) : Prop :=
  ∀ A : Fin n → Set (Y.Carrier s), (∀ l, A l ⊆ ballAtBase s Y ρ) →
    (∀ l k, l ≠ k → Disjoint (A l) (A k)) →
      IsMultilinearOn Ψ.extend fun l => lipCompactSupp s Y (A l)
def TupleFunctional.IsSymm {n : ℕ} {C : Set (FunTuple s Y n)} (Ψ : TupleFunctional C) : Prop :=
  ∀ h ∈ C, ∀ p : Equiv.Perm (Fin n), Ψ.extend (fun l => h (p l)) = Ψ.extend h
variable (s Y)
def minSeparation {n : ℕ} (f : FunTuple s Y n) : ℝ≥0∞ :=
  ⨅ i, ⨅ k, ⨅ _ : i ≠ k, infDist s Y (supportIn s Y (f i)) (supportIn s Y (f k))
theorem exists_minSeparation_eq {n : ℕ} (hn : 2 ≤ n) (f : FunTuple s Y n) :
    ∃ i k, i ≠ k ∧ minSeparation s Y f = infDist s Y (supportIn s Y (f i)) (supportIn s Y (f k)) := by
  let T := {p : Fin n × Fin n // p.1 ≠ p.2}
  have hT : Nonempty T :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
  let D : T → ℝ≥0∞ := fun p => infDist s Y (supportIn s Y (f p.1.1)) (supportIn s Y (f p.1.2))
  obtain ⟨p, hp⟩ := exists_eq_ciInf_of_finite (f := D)
  refine ⟨p.1.1, p.1.2, p.2, ?_⟩
  have hs : minSeparation s Y f = ⨅ p : T, D p := by
    simp only [minSeparation, D, T, iInf_subtype, iInf_prod]
  rw [hs, ← hp]
end YangMills.Construction.LatticeLimits.ModelSpace
end
