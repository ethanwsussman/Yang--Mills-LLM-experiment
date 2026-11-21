import YangMills.Construction.Continuum.EuclideanMotionsAndOperationsOnFunctionsAndTuples
import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.TestSpaces.UnifiedSeparatedTuples
variable {n : ℕ}
def sepAtPositiveDist (n : ℕ) : Set (Fin n → (Fin 4 → ℝ) → ℝ) :=
  {f | (∀ i, SchwingerFunctions.IsC1c (f i)) ∧
    ∃ d : ℝ, TestFunctions.HasSeparatedSupportsR4 f d}
def TupleClassesCoincide (s : Conventions.StandingParameters) (n : ℕ) : Prop :=
  (AmbientPoints.separatedTuples s .euclidean n : Set (Fin n → (Fin 4 → ℝ) → ℝ)) =
      disjointSupportTuples Set.univ n ∧
    disjointSupportTuples Set.univ n = sepAtPositiveDist n
def AgreeOnComponents {s : Conventions.StandingParameters}
    (Ψ : AmbientPoints.separatedTuples s .euclidean n → ℝ)
    (Φ : SepTupleOfCard n → ℝ) : Prop :=
  ∀ (f : AmbientPoints.separatedTuples s .euclidean n) (X : SepTupleOfCard n),
    (f.1 : Fin n → (Fin 4 → ℝ) → ℝ) = X.1 → Ψ f = Φ X
def IsLinearOnSeparatedCompacts (Φ : SepTupleOfCard n → ℝ) : Prop :=
  ∀ C : Fin n → Set (Fin 4 → ℝ), (∀ i, IsCompact (C i)) → SchwingerFunctions.PairwiseSeparated C →
    ∀ (i : Fin n) (b b' : ℝ) (X X' X'' : SepTupleOfCard n),
      (∀ j, tsupport (X.1 j) ⊆ C j) → (∀ j, tsupport (X'.1 j) ⊆ C j) →
      (∀ j, j ≠ i → X.1 j = X'.1 j) → X''.1 i = b • X.1 i + b' • X'.1 i →
        (∀ j, j ≠ i → X''.1 j = X.1 j) → Φ X'' = b * Φ X + b' * Φ X'
def MultilinearNotionsCoincide (s : Conventions.StandingParameters) (n : ℕ) : Prop :=
  ∀ (Ψ : AmbientPoints.separatedTuples s .euclidean n → ℝ) (Φ : SepTupleOfCard n → ℝ),
    AgreeOnComponents Ψ Φ →
      (AmbientPoints.IsTupleMultilinear Ψ ↔ IsMultilinearOnSep Φ) ∧
        (IsMultilinearOnSep Φ ↔ IsLinearOnSeparatedCompacts Φ)
def IsRealValued (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ) : Prop :=
  ∀ n, 2 ≤ n → ∀ f ∈ sepAtPositiveDist n, (S n f).im = 0
def AgreesWithFamily {s : Conventions.StandingParameters}
    (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ)
    (F : AmbientPoints.ConnectedFamily s .euclidean) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : AmbientPoints.separatedTuples s .euclidean n),
    S n f.1 = (F.fn n hn f : ℂ)
def FamiliesCoincide (s : Conventions.StandingParameters) : Prop :=
  (∀ F : AmbientPoints.ConnectedFamily s .euclidean,
    (∃ S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ, AgreesWithFamily S F) ∧
      ∀ S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ, AgreesWithFamily S F →
        SchwingerFunctions.IsContinuumSchwingerFamily S ∧ IsRealValued S) ∧
  ∀ S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ,
    SchwingerFunctions.IsContinuumSchwingerFamily S → IsRealValued S →
      ∃! F : AmbientPoints.ConnectedFamily s .euclidean, AgreesWithFamily S F
def SameTuple {s : Conventions.StandingParameters}
    (X : AmbientPoints.allSeparatedTuples s .euclidean) (Y : SepTuple) : Prop :=
  X.1 = (⟨Y.1, Y.2.1⟩ : AmbientPoints.FunctionTuple s .euclidean)
def AgreeOnSameTuples {s : Conventions.StandingParameters}
    (σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ)
    (σ' : SepTuple → ℝ) : Prop :=
  ∀ X Y, SameTuple X Y → σ X = σ' Y
def FunctionalsCoincide (s : Conventions.StandingParameters) : Prop :=
  (∀ σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ,
    ∃ σ' : SepTuple → ℝ, AgreeOnSameTuples σ σ') ∧
  (∀ σ' : SepTuple → ℝ,
    ∃ σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ, AgreeOnSameTuples σ σ') ∧
  ∀ (σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ) (σ' : SepTuple → ℝ),
    AgreeOnSameTuples σ σ' →
      (AmbientPoints.IsTupleFunctional σ ↔ IsSepFunctional σ')
def CumulantFormulasAgree (s : Conventions.StandingParameters) : Prop :=
  (∀ (σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ) (σ' : SepTuple → ℝ),
    AmbientPoints.IsTupleFunctional σ → AgreeOnSameTuples σ σ' →
      ∀ (n : ℕ), 1 ≤ n → AgreeOnComponents (AmbientPoints.connectedOf σ n)
        (cumulant σ')) ∧
  ∀ (F : AmbientPoints.ConnectedFamily s .euclidean)
    (G : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ),
    (∀ (n : ℕ) (hn : 2 ≤ n), AgreeOnComponents (F.fn n hn) (G n hn)) →
      AgreeOnSameTuples F.centred (centredOfCumulants G)
def IsometriesAreRigidMotions (s : Conventions.StandingParameters) : Prop :=
  {m : (Fin 4 → ℝ) → Fin 4 → ℝ |
      ∃ r : AmbientPoints.Pt s .euclidean ≃ AmbientPoints.Pt s .euclidean,
        AmbientPoints.IsDistIsometry r ∧ ∀ x, r x = m x} =
    {m | Motions.IsRigidMotion m}
def AllConditionsHold : Prop :=
  ∀ s : Conventions.StandingParameters,
    (∀ n : ℕ, 1 ≤ n → TupleClassesCoincide s n ∧ MultilinearNotionsCoincide s n) ∧
    FamiliesCoincide s ∧ FunctionalsCoincide s ∧ CumulantFormulasAgree s ∧
      IsometriesAreRigidMotions s
end YangMills.Construction.TestSpaces.UnifiedSeparatedTuples
end
