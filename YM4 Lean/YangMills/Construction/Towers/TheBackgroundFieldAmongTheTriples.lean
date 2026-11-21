import YangMills.Construction.PeriodicOperators.JetsAlongFieldsExtendedByZero
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets
def backgroundIndex (L k : ℕ) (hL : 0 < L) :
    (Tower.remainderIndex L k).Carrier → (Tower.FullSpace.fieldPeriodicData L k hL).Carrier :=
  fun i => ⟨.background, i⟩
namespace BackgroundTriple
def ExtendsByZero : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    PeriodicOperators.IsIndexEmbedding (backgroundIndex L k hL) ∧
    ∀ q ∈ Tower.FullSpace.BackgroundJets.momentumPolydisc
        Tower.FullSpace.BackgroundJets.stripHalfWidth, ∀ μ : Fin 4,
      Tower.FullSpace.tripleAmplitude L k hL
          (Tower.FullSpace.backgroundResponseSymbol L k q (Tower.FullSpace.axisPauliElement μ 2)) 0 0 =
        PeriodicOperators.extendQuotByZero (backgroundIndex L k hL)
          (Tower.FullSpace.BackgroundJets.scaledResponseField L k q μ)
end BackgroundTriple
end YangMills.Construction.Tower.FullSpace.BackgroundJets
end
