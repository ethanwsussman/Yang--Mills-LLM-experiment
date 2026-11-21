import YangMills.Construction.ChessboardTori.ReflectionsAndTranslationsOfSlabs
import YangMills.Construction.ChessboardTori.TransferPictureInOneDirection
import Mathlib
noncomputable section
namespace YangMills.Construction.ChessboardTori
def SlabReflections.Statement : Prop :=
  ∀ (D : ChessboardSetup) (T : TransferSetup D), T.grid.IsCoarse →
    ∀ m : SlabCount, Even (m : ℕ) → ∀ (k : ℤ)
      (θ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace),
      (T.torusPeriods m).InducesMap (T.planeReflection (k + 1)) θ →
      (∀ U : (T.torusPeriods m).GaugeConfig,
        T.slabRestriction m (k : ZMod (m : ℕ)) ((T.torusPeriods m).pullback θ U) =
          T.slabReverse (T.slabRestriction m ((k + 1 : ℤ) : ZMod (m : ℕ)) U)) ∧
      (∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
        (fun U => starRingEnd ℂ ((T.torusPeriods m).precompose θ
            (fun U' => Φ (T.slabRestriction m (k : ZMod (m : ℕ)) U')) U)) =
          fun U => T.reflectConj Φ (T.slabRestriction m ((k + 1 : ℤ) : ZMod (m : ℕ)) U)) ∧
      T.reflectConj T.wilsonSlabBoltzmann = T.wilsonSlabBoltzmann
end YangMills.Construction.ChessboardTori
end
