import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
def ChessboardSetup.EqualOnCompactFields (D : ChessboardSetup)
    (F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) : Prop :=
  ∀ U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), F U = F' U
def TorusChessboardSeminorms.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ C ∈ g.torusCellSet,
      (∀ F ∈ g.torusCellObservables C, ∀ F' ∈ g.torusCellObservables C, ∀ c : ℂ,
        ∀ r ∈ g.inducedTorusMaps, ∀ C'' ∈ g.torusCellSet,
          g.torusTransportTo C (r '' C) F ∈ g.torusCellObservables (r '' C) ∧
          D.EqualOnCompactFields (g.torusTransportTo C (r '' C) (F + F'))
            (g.torusTransportTo C (r '' C) F + g.torusTransportTo C (r '' C) F') ∧
          D.EqualOnCompactFields (g.torusTransportTo C (r '' C) (F * F'))
            (g.torusTransportTo C (r '' C) F * g.torusTransportTo C (r '' C) F') ∧
          D.EqualOnCompactFields (g.torusTransportTo C (r '' C) fun U => starRingEnd ℂ (F U))
            (fun U => starRingEnd ℂ (g.torusTransportTo C (r '' C) F U)) ∧
          D.EqualOnCompactFields (g.torusTransportTo C (r '' C) (c • F))
            (Conventions.signedConj (g.torusSign r) c • g.torusTransportTo C (r '' C) F) ∧
          D.EqualOnCompactFields
            (g.torusTransportTo (r '' C) C'' (g.torusTransportTo C (r '' C) F))
            (g.torusTransportTo C C'' F)) ∧
      ((g.inducedTorusMaps.ncard : ℝ) = g.cellsAcross ^ 4 ∧
        (({r ∈ g.inducedTorusMaps | g.torusSign r = -1}.ncard : ℕ) : ℝ) = g.cellsAcross ^ 4 / 2) ∧
      (∀ F ∈ g.torusCellObservables C, ∀ F' ∈ g.torusCellObservables C, ∀ c : ℂ,
        g.torusChessboardNorm (c • F) = ‖c‖ * g.torusChessboardNorm F ∧
        g.torusChessboardNorm (F + F') ≤ g.torusChessboardNorm F + g.torusChessboardNorm F' ∧
        g.torusChessboardNorm (fun U => starRingEnd ℂ (F U)) = g.torusChessboardNorm F ∧
        g.torusChessboardNorm F ≤
          ⨆ U : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), ‖F U.1‖ ∧
        ‖D.periodicExpectation F‖ ≤ g.torusChessboardNorm F) ∧
      g.torusChessboardNorm (fun _ => 1) = 1 ∧
      ∀ H ∈ g.torusCellObservables C,
        (∀ U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), (H U).im = 0) →
          ((g.torusChessboardNorm (fun U => Complex.exp (H U)) ^ (g.cellsAcross ^ 4) : ℝ) : ℂ) =
              D.periodicExpectation (fun U =>
                Complex.exp (∑ᶠ r ∈ g.inducedTorusMaps, D.pullbackObservable r H U)) ∧
            0 < (D.periodicExpectation (fun U =>
                Complex.exp (∑ᶠ r ∈ g.inducedTorusMaps, D.pullbackObservable r H U))).re
end YangMills.Construction.ChessboardTori
end
