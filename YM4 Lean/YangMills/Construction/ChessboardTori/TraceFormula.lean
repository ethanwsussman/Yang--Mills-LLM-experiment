import YangMills.Construction.Analysis.SquareSummableKernels
import YangMills.Construction.ChessboardTori.CrossingKernelAndItsExpansionFunctions
import Mathlib
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.SquareSummable
def SlabCount.scale (j : ℕ) (hj : 1 ≤ j) (m : SlabCount) : SlabCount :=
  ⟨j * (m : ℕ), by have := m.2; nlinarith⟩
theorem SlabCount.even_scale (j : ℕ) (hj : 1 ≤ j) {m : SlabCount} (hm : Even (m : ℕ)) :
    Even ((SlabCount.scale j hj m : SlabCount) : ℕ) :=
  hm.mul_left j
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
def slabKernels (m : SlabCount) (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ) :
    Fin (m : ℕ) → T.WordIndex → T.WordIndex → ℂ :=
  fun k => T.slabKernelMatrix (Φ (((k : ℕ) : ZMod (m : ℕ))))
end TransferSetup
def CyclicTraceFormula.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D),
    (∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
      IsSqSummable (T.slabKernelMatrix Φ) ∧
      hsNorm (T.slabKernelMatrix Φ) ≤ ⨆ η, ‖Φ η‖ ∧
      adjointKernel (T.slabKernelMatrix Φ) = T.slabKernelMatrix (T.reflectConj Φ)) ∧
    (∀ (m : SlabCount) (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ), (∀ k, T.IsBoundedMeasurable (Φ k)) →
      CyclicTraceConverges (T.slabKernels m Φ) ∧
      T.slabProductIntegral m Φ = cyclicTrace (T.slabKernels m Φ)) ∧
    ∀ (m : SlabCount) (hm : Even (m : ℕ)),
      (∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
        CyclicTraceConverges (alternatingKernels (T.slabKernelMatrix Φ) (m : ℕ)) ∧
        T.alternatingSlabIntegral m hm Φ = alternatingCyclicTrace (T.slabKernelMatrix Φ) (m : ℕ) ∧
        T.alternatingSlabIntegral m hm Φ =
          ((schattenEvenNorm (T.slabKernelMatrix Φ) (m : ℕ) ^ (m : ℕ) : ℝ) : ℂ) ∧
        0 ≤ schattenEvenNorm (T.slabKernelMatrix Φ) (m : ℕ) ^ (m : ℕ) ∧
        T.alternatingSlabIntegral m hm (T.reflectConj Φ) = T.alternatingSlabIntegral m hm Φ) ∧
      (∀ Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ, (∀ k, T.IsBoundedMeasurable (Φ k)) →
        ‖T.slabProductIntegral m Φ‖ ≤
          ∏ k : ZMod (m : ℕ), (T.alternatingSlabIntegral m hm (Φ k)).re ^ (1 / ((m : ℕ) : ℝ))) ∧
      (∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ → ∀ (j : ℕ) (hj : 1 ≤ j),
        (T.alternatingSlabIntegral (SlabCount.scale j hj m)
          (SlabCount.even_scale j hj hm) Φ).im = 0 ∧
        0 ≤ (T.alternatingSlabIntegral (SlabCount.scale j hj m)
          (SlabCount.even_scale j hj hm) Φ).re ∧
        (T.alternatingSlabIntegral (SlabCount.scale j hj m)
          (SlabCount.even_scale j hj hm) Φ).re ≤
          (T.alternatingSlabIntegral m hm Φ).re ^ j)
end YangMills.Construction.ChessboardTori
end
