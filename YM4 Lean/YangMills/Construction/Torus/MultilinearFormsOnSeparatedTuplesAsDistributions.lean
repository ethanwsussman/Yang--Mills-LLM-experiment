import YangMills.Construction.Torus.CutOffsOnAProductOfOpenSetsOfFourSpace
import YangMills.Construction.Torus.DistributionsOffTheDiagonalsAndRegularMaps
import YangMills.Construction.Torus.FormsThatObeyABoundFunction
import YangMills.Construction.Torus.GradientNormOfAFunctionOfOnePoint
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
namespace AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
def BoundedAt (M : Set.Ici (1 : ℝ)) (Φ : TupleForm (sepTuples s E n)) (c d R : ℝ) : Prop :=
  ∀ f : sepTuples s E n, SupportsInBalls R f.1 →
    ENNReal.ofReal d ≤ supportGap f.1 → ‖Φ f‖ ≤ c * ∏ i, ambientSharpNorm s M E (f.1 i)
structure IsSeparatedOpenFamily (R d : ℝ) (V : Fin n → Set (Pt s E)) : Prop where
  radius_pos : 0 < R
  gap_pos : 0 < d
  isOpen : ∀ i, IsOpen (V i)
  setDiam_le : ∀ i, setDiam s E (V i) ≤ ENNReal.ofReal (2 * R)
  setDiam_lt_of_torus : E = .torus → ∀ i, setDiam s E (V i) < ENNReal.ofReal (s.side / 4)
  separated : ∀ i i', i ≠ i' → ENNReal.ofReal d ≤ setDist s E (V i) (V i')
theorem IsSeparatedOpenFamily.boxSet_subset {R d : ℝ} {V : Fin n → Set (Pt s E)}
    (hV : IsSeparatedOpenFamily R d V) : boxSet V ⊆ pairwiseDistinctTuples s E n := by
  intro x hx
  change Function.Injective x
  intro j j' hxx
  by_contra hne
  have hj : x j ∈ V j := hx j (mem_univ j)
  have hj' : x j ∈ V j' := hxx ▸ hx j' (mem_univ j')
  have hzero : setDist s E (V j) (V j') ≤ 0 := by
    refine iInf₂_le_of_le (x j) hj (iInf₂_le_of_le (x j) hj' ?_)
    simp [pointDist_self]
  have hgap : 0 < ENNReal.ofReal d := ENNReal.ofReal_pos.mpr hV.gap_pos
  exact absurd ((hV.separated j j' hne).trans hzero) (not_le.mpr hgap)
def IsRealTestFn (A : Set (Pt s E)) (φ : Pt s E → ℝ) : Prop :=
  asFunctionOnOnePoint φ ∈ testFns (boxSet fun _ : Fin 1 => A)
def IsComplexTestFn (A : Set (Pt s E)) (φ : Pt s E → ℂ) : Prop :=
  ofSinglePoint φ ∈ testFns (boxSet fun _ : Fin 1 => A)
def tensorSums (V : Fin n → Set (Pt s E)) : Set (Tuple s E n → ℂ) :=
  {F | ∃ (m : ℕ) (φ : Fin m → Fin n → Pt s E → ℂ),
    (∀ k i, IsComplexTestFn (V i) (φ k i)) ∧ F = ∑ k, tensorProd (φ k)}
def MatchesOnTensors (Φ : TupleForm (sepTuples s E n)) (V : Fin n → Set (Pt s E))
    (T : testFns (boxSet V) → ℂ) : Prop :=
  ∀ φ : Fin n → Pt s E → ℝ, (∀ i, IsRealTestFn (V i) (φ i)) →
    ∃ (hφ : φ ∈ sepTuples s E n)
      (hF : realTensor φ ∈ testFns (boxSet V)), T ⟨_, hF⟩ = Φ ⟨φ, hφ⟩
def IsBoxDistrib (Φ : TupleForm (sepTuples s E n)) (V : Fin n → Set (Pt s E))
    (T : testFns (boxSet V) → ℂ) : Prop :=
  IsDistrib T ∧ MatchesOnTensors Φ V T
def boxDistrib (Φ : TupleForm (sepTuples s E n)) (V : Fin n → Set (Pt s E)) :
    testFns (boxSet V) → ℂ :=
  Classical.epsilon (IsBoxDistrib Φ V)
theorem isBoxDistrib_boxDistrib {Φ : TupleForm (sepTuples s E n)}
    {V : Fin n → Set (Pt s E)} (h : ∃ T, IsBoxDistrib Φ V T) :
    IsBoxDistrib Φ V (boxDistrib Φ V) :=
  Classical.epsilon_spec h
def boxBoundConst (n : ℕ) (M : Set.Ici (1 : ℝ)) (R c : ℝ) : ℝ :=
  2 ^ n * (40 * (M : ℝ)) ^ n * c * bumpNumber n (2 * R)
def EqOneNearProj (A : Set (Tuple s E n)) (i : Fin n) (χ : Pt s E → ℝ) : Prop :=
  ∃ N : Set (Pt s E), (∃ O, IsOpen O ∧ (fun y : Tuple s E n => y i) '' A ⊆ O ∧ O ⊆ N) ∧
    ∀ y ∈ N, χ y = 1
def BoxBound (M : Set.Ici (1 : ℝ)) (c : ℝ → ℝ → ℝ) (R d : ℝ)
    (V : Fin n → Set (Pt s E)) (T : testFns (boxSet V) → ℂ) : Prop :=
  ∀ (F : testFns (boxSet V)) (χ : Fin n → Pt s E → ℝ),
    (∀ i, IsRealTestFn (V i) (χ i)) →
    (∀ i, EqOneNearProj (closedSupport F.1) i (χ i)) →
      ENNReal.ofReal ‖T F‖ ≤
        ENNReal.ofReal (boxBoundConst n M R (c d (maxDiam V).toReal)) *
          (∏ i, c1GradNorm fun y => (χ i y : ℂ)) * cnNorm (5 * n + 1) F.1
def HasBoxDistribs (M : Set.Ici (1 : ℝ)) (c : ℝ → ℝ → ℝ)
    (Φ : TupleForm (sepTuples s E n)) : Prop :=
  ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
    (∃! T, IsBoxDistrib Φ V T) ∧
      DenseInTestFns (boxSet V) (tensorSums V) ∧
      ((∀ i, (V i).Nonempty) →
        0 < maxDiam V ∧ maxDiam V < injRadius s E ∧
          BoxBound M c R d V (boxDistrib Φ V))
def IsGluedDistrib (Φ : TupleForm (sepTuples s E n))
    (Ψ : testFns (pairwiseDistinctTuples s E n) → ℂ) : Prop :=
  IsDistrib Ψ ∧ ∀ (R d : ℝ) (V : Fin n → Set (Pt s E)) (hV : IsSeparatedOpenFamily R d V),
    restrictDistrib hV.boxSet_subset Ψ = boxDistrib Φ V
def formDistrib (Φ : TupleForm (sepTuples s E n)) :
    testFns (pairwiseDistinctTuples s E n) → ℂ :=
  Classical.epsilon (IsGluedDistrib Φ)
theorem isGluedDistrib_formDistrib {Φ : TupleForm (sepTuples s E n)}
    (h : ∃ Ψ, IsGluedDistrib Φ Ψ) : IsGluedDistrib Φ (formDistrib Φ) :=
  Classical.epsilon_spec h
def MatchesOnSmoothTuples (Φ : TupleForm (sepTuples s E n))
    (Ψ : testFns (pairwiseDistinctTuples s E n) → ℂ) : Prop :=
  ∀ f : sepTuples s E n, (∀ i, IsSmoothFn (asFunctionOnOnePoint (f.1 i))) →
    ∃ hF : realTensor f.1 ∈ testFns (pairwiseDistinctTuples s E n), Ψ ⟨_, hF⟩ = Φ f
def HasDistinctPointsDistrib (Φ : TupleForm (sepTuples s E n)) : Prop :=
  (∃! Ψ, IsGluedDistrib Φ Ψ) ∧ HasOrderLE (5 * n + 1) (formDistrib Φ) ∧
    MatchesOnSmoothTuples Φ (formDistrib Φ) ∧
    ∀ Ψ, IsDistrib Ψ → MatchesOnSmoothTuples Φ Ψ → Ψ = formDistrib Φ
namespace MultilinearAsDistrib
def Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (n : ℕ), 2 ≤ n → ∀ (M : Set.Ici (1 : ℝ))
    (Φ : TupleForm (sepTuples s E n)), TupleForm.IsReal Φ → TupleForm.IsMultilinear Φ →
    ∀ c : ℝ → ℝ → ℝ,
      (∀ d : ℝ, 0 < d → ∀ R : ℝ, 0 < R → ENNReal.ofReal R < injRadius s E →
        0 ≤ c d R ∧ BoundedAt M Φ (c d R) d R) →
      HasBoxDistribs M c Φ ∧
        (∀ (R d : ℝ) (V : Fin n → Set (Pt s E)), IsSeparatedOpenFamily R d V →
          HasOrderLE (5 * n + 1) (boxDistrib Φ V)) ∧
        HasDistinctPointsDistrib Φ
end MultilinearAsDistrib
end AmbientPoints
end YangMills.Construction
