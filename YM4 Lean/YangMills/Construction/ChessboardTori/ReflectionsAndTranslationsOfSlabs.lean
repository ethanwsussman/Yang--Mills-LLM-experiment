import YangMills.Construction.ChessboardTori.PeriodisationAndInducedMaps
import YangMills.Construction.ChessboardTori.TransferPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
def planeReflection (κ : ℤ) : D.LatticeSym :=
  T.grid.toLatticeSym ⟨T.grid.reflectPerm T.axis κ,
    Subgroup.subset_closure ⟨(T.axis, κ), rfl⟩⟩
def twoCellVector : AmbientSpace := (2 * T.grid.cellSide) • coordVec T.axis
theorem twoCellVector_mem : T.twoCellVector ∈ D.gridPoints := by
  refine ⟨Pi.single T.axis (2 * T.grid.cellRatio), fun ν => ?_⟩
  by_cases h : ν = T.axis
  · subst h
    simp [twoCellVector, coordVec, T.grid.cellSide_eq, mul_assoc]
  · simp [twoCellVector, coordVec, Pi.single_eq_of_ne h]
def twoCellShift : D.LatticeSym :=
  InfiniteLattice.shift ⟨T.twoCellVector, T.twoCellVector_mem⟩
def slabFlip (m : SlabCount) (k : ZMod (m : ℕ)) :
    (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace :=
  Classical.epsilon ((T.torusPeriods m).InducesMap (T.planeReflection ((k.cast : ℤ) + 1)))
def slabShift (m : SlabCount) : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace :=
  Classical.epsilon ((T.torusPeriods m).InducesMap T.twoCellShift)
end TransferSetup
def SlabSymmetries.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D) (m : SlabCount), Even (m : ℕ) → ∀ k : ZMod (m : ℕ),
    (∀ κ : ℤ, (κ : ZMod (m : ℕ)) = k →
      (T.torusPeriods m).InducesMap (T.planeReflection (κ + 1)) (T.slabFlip m k)) ∧
    (T.torusPeriods m).InducesMap T.twoCellShift (T.slabShift m) ∧
    (T.torusPeriods m).IsTorusIsometry (T.slabFlip m k) ∧
    (T.torusPeriods m).IsTorusIsometry (T.slabShift m) ∧
    T.slabFlip m k '' ((T.torusPeriods m).gridSubgroup : Set (T.torusPeriods m).TorusSpace) =
      (T.torusPeriods m).gridSubgroup ∧
    T.slabShift m '' ((T.torusPeriods m).gridSubgroup : Set (T.torusPeriods m).TorusSpace) =
      (T.torusPeriods m).gridSubgroup ∧
    (∀ U : (T.torusPeriods m).GaugeConfig,
      T.slabRestriction m k ((T.torusPeriods m).pullback (T.slabFlip m k) U) =
        T.slabReverse (T.slabRestriction m (k + 1) U)) ∧
    (∀ U : (T.torusPeriods m).GaugeConfig,
      T.slabRestriction m k ((T.torusPeriods m).pullback (T.slabShift m) U) =
        T.slabRestriction m (k + 2) U) ∧
    (∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
      (fun U => starRingEnd ℂ ((T.torusPeriods m).precompose (T.slabFlip m k)
          (fun U' => Φ (T.slabRestriction m k U')) U)) =
        (fun U => T.reflectConj Φ (T.slabRestriction m (k + 1) U)) ∧
      (T.torusPeriods m).precompose (T.slabShift m) (fun U => Φ (T.slabRestriction m k U)) =
        fun U => Φ (T.slabRestriction m (k + 2) U)) ∧
    ∀ w : (T.torusPeriods m).Face → ℂ, (∃ C : ℝ, ∀ p, ‖w p‖ ≤ C) →
      (∀ U : (T.torusPeriods m).GaugeConfig,
        T.slabBoltzmann m w k (T.slabRestriction m k U) =
          ∏ᶠ (p : (T.torusPeriods m).Face) (_ : T.IsInSlab m k p),
            Complex.exp ((w p - (D.β : ℂ)) * ((T.torusPeriods m).faceEnergy U p : ℂ))) ∧
      ((∀ p, T.IsInSlab m k p →
          w ((T.torusPeriods m).mapFace (T.slabFlip m k) p) = starRingEnd ℂ (w p)) →
        T.slabBoltzmann m w (k + 1) = T.reflectConj (T.slabBoltzmann m w k))
end YangMills.Construction.ChessboardTori
end
