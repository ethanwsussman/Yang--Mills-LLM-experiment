import YangMills.Construction.BumpFunctions.CosineSquaredPartition
import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.ReflectionsAndOneInsertion.PeriodicGibbsLimitStandingDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MeshPartition
open CosineSquaredBump TestFunctions
def cubeAround (ε : ℝ) (α : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {x | ∀ μ, x μ - α μ ∈ Set.Icc (-ε) ε}
def boxFrom (b lam : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {x | ∀ μ, x μ ∈ Set.Icc (b μ) (b μ + lam μ)}
def localizedPiece (ε : ℝ) (α : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℝ) : (Fin 4 → ℝ) → ℝ :=
  fun x => productBump ε α x * f x
def BumpProperties (ε : ℝ) (α : Fin 4 → ℝ) : Prop :=
  SchwingerFunctions.IsC1c (productBump ε α) ∧
    (∀ x, 0 ≤ productBump ε α x ∧ productBump ε α x ≤ 1) ∧
    tsupport (productBump ε α) = cubeAround ε α ∧
    cubeAround ε α ⊆ closedBallR4 α (2 * ε) ∧
    ∀ x, ReflectionsAndOneInsertion.gradNorm (productBump ε α) x ≤ Real.pi / ε
def SumsToOneAtPoint (ε : ℝ) (x : Fin 4 → ℝ) : Prop :=
  ∑ᶠ α : latticeOfSpacing ε, productBump ε α x = 1 ∧
    {α | α ∈ latticeOfSpacing ε ∧ productBump ε α x ≠ 0}.encard ≤ 16
def PieceProperties (ε : ℝ) (α : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  tsupport (localizedPiece ε α f) ⊆ tsupport f ∩ closedBallR4 α (2 * ε) ∧
    uniformNorm (localizedPiece ε α f) ≤ uniformNorm f ∧
    IsLipschitzFor euclidDistR4 (localizedPiece ε α f) ∧
    lipConstR4 (localizedPiece ε α f) ≤ lipConstR4 f + Real.pi / ε * uniformNorm f ∧
    (SchwingerFunctions.IsC1c f → SchwingerFunctions.IsC1c (localizedPiece ε α f))
def DecomposesFunction (ε : ℝ) (f : (Fin 4 → ℝ) → ℝ) (lam : Fin 4 → ℝ) : Prop :=
  {α | α ∈ latticeOfSpacing ε ∧ localizedPiece ε α f ≠ 0}.Finite ∧
    (({α | α ∈ latticeOfSpacing ε ∧ localizedPiece ε α f ≠ 0}.ncard : ℕ) : ℝ) ≤
      ∏ μ : Fin 4, (lam μ / ε + 3) ∧
    f = ∑ᶠ α : latticeOfSpacing ε, localizedPiece ε α f ∧
    ∀ α ∈ latticeOfSpacing ε, PieceProperties ε α f
def MeshPartitionStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∀ α ∈ latticeOfSpacing ε, BumpProperties ε α) ∧
    (∀ x, SumsToOneAtPoint ε x) ∧
    ∀ (f : (Fin 4 → ℝ) → ℝ) (b lam : Fin 4 → ℝ), IsLipschitzFor euclidDistR4 f →
      (∀ μ, 0 ≤ lam μ) → tsupport f ⊆ boxFrom b lam → DecomposesFunction ε f lam
end YangMills.Construction.MeshPartition
