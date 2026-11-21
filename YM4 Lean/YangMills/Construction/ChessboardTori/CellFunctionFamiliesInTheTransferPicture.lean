import YangMills.Construction.ChessboardTori.ChessboardIntegral
import YangMills.Construction.ChessboardTori.FamiliesOfCellFunctions
import YangMills.Construction.ChessboardTori.TransferPictureInOneDirection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
namespace TransferSetup
variable {S : ChessboardSetup} (T : TransferSetup S)
def slabLayer (m : SlabCount) (k : ℤ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun κ => Finset.Ico 0 (T.cellCounts m κ)).filter fun j => j T.axis = k
def IsLayerFunction (m : SlabCount) (k : ℤ) (F : (Fin 4 → ℤ) → S.GaugeField → ℂ)
    (Φ : T.SlabConfig → ℂ) : Prop :=
  ∀ U : (T.torusPeriods m).GaugeConfig,
    Φ (T.slabRestriction m (k : ZMod (m : ℕ)) U) =
      T.wilsonSlabBoltzmann (T.slabRestriction m (k : ZMod (m : ℕ)) U) *
        ∏ j ∈ T.slabLayer m k, F j ((T.torusPeriods m).liftGaugeField U)
def layerFunction (m : SlabCount) (k : ℤ) (F : (Fin 4 → ℤ) → S.GaugeField → ℂ) :
    T.SlabConfig → ℂ :=
  Classical.epsilon (T.IsLayerFunction m k F)
end TransferSetup
namespace CoupledGrid
variable (O : CoupledGrid)
structure EvenTransverseSection (_O : CoupledGrid) where
  axis : Fin 4
  transverseCells : TransverseAxis axis → ℤ
  two_le_transverseCells : ∀ ν, 2 ≤ transverseCells ν
  even_transverseCells : ∀ ν, Even (transverseCells ν)
namespace EvenTransverseSection
variable {O} (P : O.EvenTransverseSection)
def transferSetup : TransferSetup O.toChessboardSetup where
  grid := O.grid
  axis := P.axis
  transverseCells := P.transverseCells
  two_le_transverseCells := P.two_le_transverseCells
def cellCounts (m : SlabCount) (hm : Even (m : ℕ)) : EvenIndexVector where
  coord := P.transferSetup.cellCounts m
  two_le := P.transferSetup.two_le_cellCounts m
  even ν := by
    unfold TransferSetup.cellCounts
    split_ifs with hν
    · exact_mod_cast hm
    · exact P.even_transverseCells _
end EvenTransverseSection
theorem exists_cellCounts_eq (n : EvenIndexVector) (μ : Fin 4) :
    ∃ (P : O.EvenTransverseSection) (m : SlabCount) (hm : Even (m : ℕ)),
      P.axis = μ ∧ ((m : ℕ) : ℤ) = n.coord μ ∧ P.cellCounts m hm = n := by
  have h0 : (0 : ℤ) ≤ n.coord μ := by have := n.two_le μ; omega
  have hc : (((n.coord μ).toNat : ℕ) : ℤ) = n.coord μ := Int.toNat_of_nonneg h0
  have h2 : 2 ≤ (n.coord μ).toNat := by have := n.two_le μ; omega
  have he : Even (n.coord μ).toNat := by
    have := n.even μ
    rw [← hc] at this
    exact_mod_cast this
  refine ⟨⟨μ, fun ν => n.coord ν.1, fun ν => n.two_le ν.1, fun ν => n.even ν.1⟩,
    ⟨(n.coord μ).toNat, h2⟩, he, rfl, hc, ?_⟩
  have hcoord : ∀ (e e' : EvenIndexVector), e.coord = e'.coord → e = e' := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ hee
    cases hee
    rfl
  refine hcoord _ _ (funext fun ν => ?_)
  change (if hν : ν = μ then _ else _) = _
  split_ifs with hν
  · subst hν
    exact hc
  · rfl
def LayerFunctionsOfFamily (P : O.EvenTransverseSection) (m : SlabCount) (hm : Even (m : ℕ))
    (F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ) : Prop :=
  (∀ k ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ),
    (∃! Φ, P.transferSetup.IsLayerFunction m k F Φ) ∧
    P.transferSetup.IsLayerFunction m k F (P.transferSetup.layerFunction m k F) ∧
    P.transferSetup.IsBoundedMeasurable (P.transferSetup.layerFunction m k F) ∧
    ∀ G : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ,
      O.IsCellFamily (P.cellCounts m hm) G →
      (∀ j ∈ P.transferSetup.slabLayer m k, G j = F j) →
      P.transferSetup.layerFunction m k G = P.transferSetup.layerFunction m k F) ∧
  O.cellFamilyIntegral (P.cellCounts m hm) F =
    P.transferSetup.slabProductIntegral m fun c => P.transferSetup.layerFunction m ((c.val : ℕ) : ℤ) F
def NextLayerReflects (P : O.EvenTransverseSection) (m : SlabCount)
    (F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ) : Prop :=
  ∀ k : ℤ, 0 ≤ k → k ≤ ((m : ℕ) : ℤ) - 2 →
    (∀ j ∈ P.transferSetup.slabLayer m k,
      F (j + Pi.single P.axis 1) =
        O.grid.transportTo (O.grid.cell j) (O.grid.cell (j + Pi.single P.axis 1)) (F j)) →
    P.transferSetup.layerFunction m (k + 1) F = P.transferSetup.reflectConj (P.transferSetup.layerFunction m k F)
def FirstLayerFunctionIndependent (P : O.EvenTransverseSection) (m : SlabCount)
    (F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ) : Prop :=
  ∀ (k : SlabCount) (hk : Even (k : ℕ)) (G : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ),
    O.IsCellFamily (P.cellCounts k hk) G →
    (∀ j ∈ P.transferSetup.slabLayer m 0, G j = F j) →
    P.transferSetup.layerFunction k 0 G = P.transferSetup.layerFunction m 0 F
def ReflectionBoundForFamily (P : O.EvenTransverseSection) (m : SlabCount) (hm : Even (m : ℕ))
    (F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ) : Prop :=
  (∀ k ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ),
    O.cellFamilyIntegral (P.cellCounts m hm) (O.grid.reflectFamily P.axis k F) =
      P.transferSetup.alternatingSlabIntegral m hm (P.transferSetup.layerFunction m k F) ∧
    (O.cellFamilyIntegral (P.cellCounts m hm) (O.grid.reflectFamily P.axis k F)).im = 0 ∧
    0 ≤ (O.cellFamilyIntegral (P.cellCounts m hm) (O.grid.reflectFamily P.axis k F)).re) ∧
  ‖O.cellFamilyIntegral (P.cellCounts m hm) F‖ ≤
    ∏ k ∈ Finset.Ico (0 : ℤ) ((m : ℕ) : ℤ),
      (O.cellFamilyIntegral (P.cellCounts m hm) (O.grid.reflectFamily P.axis k F)).re ^
        (1 / ((m : ℕ) : ℝ))
def ChessboardPartitionsNonneg (n : EvenIndexVector) : Prop :=
  ∀ C ∈ O.grid.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) C,
    (O.chessboardPartitionOn n C F).im = 0 ∧ 0 ≤ (O.chessboardPartitionOn n C F).re
def ChessboardBoundForFamily (n : EvenIndexVector)
    (F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ) : Prop :=
  ‖O.cellFamilyIntegral n F‖ ≤
    ∏ k ∈ n.indexBox, (O.chessboardPartitionOn n (O.grid.cell k) (F k)).re ^
      (1 / ((∏ κ, n.coord κ : ℤ) : ℝ))
end CoupledGrid
def CellFamiliesInTransferSetup.Statement : Prop :=
  ∀ O : CoupledGrid,
    (∀ (P : O.EvenTransverseSection) (m : SlabCount) (hm : Even (m : ℕ))
        (F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ),
        O.IsCellFamily (P.cellCounts m hm) F →
        O.LayerFunctionsOfFamily P m hm F ∧ O.NextLayerReflects P m F ∧
          O.FirstLayerFunctionIndependent P m F ∧
          O.ReflectionBoundForFamily P m hm F) ∧
    ∀ n : EvenIndexVector, O.ChessboardPartitionsNonneg n ∧
      ∀ F : (Fin 4 → ℤ) → O.toChessboardSetup.GaugeField → ℂ,
        O.IsCellFamily n F → O.ChessboardBoundForFamily n F
end ChessboardTori
end YangMills.Construction
end
