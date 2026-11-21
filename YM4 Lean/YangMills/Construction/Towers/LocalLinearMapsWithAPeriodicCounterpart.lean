import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.Periodisation
section Definitions
variable {k : ℕ} (L n : ℕ)
def CellClass.periodicExtension : (A : CellClass k) →
    ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
    (CellClass.fullSpace L A).index → Matrices.ComplexMatrix2
  | ⟨j, _, .vertex⟩, f => fun x => f (Tower.FullSpace.projVertex L n k j x)
  | ⟨j, _, .edge⟩, f => fun e => f (Tower.FullSpace.projEdge L n k j e)
  | ⟨j, _, .face⟩, f => fun p => f (Tower.FullSpace.projFace L n k j p)
variable (A A' : CellClass k)
structure IsLocalLinearFull (R : ℝ)
    (T : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2) : Prop where
  map_mem : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule,
    T f ∈ (CellClass.fullSpace L A').complexSubmodule
  map_add : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule,
    ∀ g ∈ (CellClass.fullSpace L A).complexSubmodule, T (f + g) = T f + T g
  map_smul : ∀ (z : ℂ), ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule, T (z • f) = z • T f
  local_dependence : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule,
    ∀ g ∈ (CellClass.fullSpace L A).complexSubmodule,
    ∀ c' : Cell L k A'.level A'.cellType,
      (∀ c : Cell L k A.level A.cellType,
        TorusMetric.supNormVec (Cell.anchor c - Cell.anchor c') ≤ R →
          CellClass.cellFn L A f c = CellClass.cellFn L A g c) →
      CellClass.cellFn L A' (T f) c' = CellClass.cellFn L A' (T g) c'
structure IsLinearPeriodic
    (T : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) : Prop where
  map_mem : ∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule,
    T f ∈ (CellClass.quotSpace L n A').complexSubmodule
  map_add : ∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule,
    ∀ g ∈ (CellClass.quotSpace L n A).complexSubmodule, T (f + g) = T f + T g
  map_smul : ∀ (z : ℂ), ∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule, T (z • f) = z • T f
def CommutesWithExtension
    (TFull : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2)
    (TPer : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) : Prop :=
  ∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule, ∀ c' : Cell L k A'.level A'.cellType,
    CellClass.cellFn L A' (TFull (CellClass.periodicExtension L n A f)) c' =
      CellClass.quotCellFn L n A' (TPer f) (Cell.proj n c')
structure IsLocalWithPeriodicCounterpart (R : ℝ)
    (TFull : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2)
    (TPer : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) : Prop where
  full : IsLocalLinearFull L A A' R TFull
  periodic : IsLinearPeriodic L n A A' TPer
  commutes : CommutesWithExtension L n A A' TFull TPer
end Definitions
def LocalLinearMapsPeriodize : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ A A' : CellClass k, A.cellType ≠ .face → A'.cellType ≠ .face →
      ∀ R : ℝ, 0 ≤ R → 2 * R < (periodSide L n : ℝ) →
        ∀ (TFull : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
            (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2)
          (TPer : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
            (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2),
          IsLocalWithPeriodicCounterpart L n A A' R TFull TPer → Periodizes L n A A' R TFull TPer
end YangMills.Construction.LocalKernels.Periodisation
end
