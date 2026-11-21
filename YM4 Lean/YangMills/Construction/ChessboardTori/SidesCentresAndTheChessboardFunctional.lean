import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
def IsAdmissibleSide (l : ℝ) : Prop :=
  (∃ n : ℤ, l = (D.L : ℝ) ^ n) ∧ D.mesh ≤ l / (D.L : ℝ) ^ 2
theorem isAdmissibleSide_one (hmesh : D.mesh ≤ (D.L : ℝ) ^ (-2 : ℤ)) : D.IsAdmissibleSide 1 := by
  refine ⟨⟨0, by simp⟩, ?_⟩
  simpa [zpow_neg, one_div] using hmesh
theorem one_sub_K_le_of_isAdmissibleSide {n : ℤ} (hside : D.IsAdmissibleSide ((D.L : ℝ) ^ n)) :
    1 - ((D.K : ℕ) : ℤ) ≤ n := by
  have hLgt : (1 : ℝ) < D.L := D.one_lt_factor
  have hLne : (D.L : ℝ) ≠ 0 := by linarith
  have hdiv : (D.L : ℝ) ^ n / (D.L : ℝ) ^ 2 = (D.L : ℝ) ^ (n - 2) := by
    rw [zpow_sub₀ hLne]
    norm_cast
  have hmesh : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
  have hbound := hside.2
  rw [hdiv, hmesh] at hbound
  have hexp := (zpow_le_zpow_iff_right₀ hLgt).mp hbound
  omega
def gridOfSide (n : ℤ) (hn : D.IsAdmissibleSide ((D.L : ℝ) ^ n)) (c : AmbientSpace)
    (hc : ∀ μ, ∃ i : ℤ, c μ = D.mesh * ((i : ℝ) + 1 / 2)) : ReflectionGrid D :=
  ⟨n, D.one_sub_K_le_of_isAdmissibleSide hn, c, hc⟩
end ChessboardSetup
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def HasAdmissibleSide : Prop := D.IsAdmissibleSide g.cellSide
theorem hasAdmissibleSide_gridOfSide (n : ℤ) (hn : D.IsAdmissibleSide ((D.L : ℝ) ^ n))
    (c : AmbientSpace) (hc : ∀ μ, ∃ i : ℤ, c μ = D.mesh * ((i : ℝ) + 1 / 2)) :
    (D.gridOfSide n hn c hc).HasAdmissibleSide :=
  hn
def wallSet : Set (Set AmbientSpace) := range fun p : Fin 4 × ℤ => g.wall p.1 p.2
def cellCentre (k : Fin 4 → ℤ) : AmbientSpace :=
  fun μ => g.origin μ + g.cellSide * k μ + g.cellSide / 2
def IsEvenElement (r : g.reflectionGroup) : Prop := orientationSign r.1 = 1
def IsCoarsening (coarse fine : ReflectionGrid D) : Prop :=
  (∃ k₀ : ℕ, coarse.cellSide = (D.L : ℝ) ^ k₀ * fine.cellSide) ∧
    coarse.wallSet ⊆ fine.wallSet
def torusCellCentre (k : Fin 4 → ℤ) : D.Torus := D.proj (g.cellCentre k)
def cellNumber : ℝ := g.cellsAcross ^ 4
def HasTorusParity (r' : D.Torus → D.Torus) (ε : ℤˣ) : Prop :=
  ∀ r : g.reflectionGroup, D.proj ∘ r.1 = r' ∘ D.proj → orientationSign r.1 = ε
theorem torusSign_eq_of_hasTorusParity {r' : D.Torus → D.Torus} (hr : r' ∈ g.inducedTorusMaps)
    {ε : ℤˣ} (hpar : g.HasTorusParity r' ε) : g.torusSign r' = ε := by
  obtain ⟨r, hrG, hr'⟩ := hr
  exact hpar _ (Classical.epsilon_spec (p := fun r : g.reflectionGroup =>
    D.proj ∘ r.1 = r' ∘ D.proj) ⟨⟨r, hrG⟩, hr'⟩)
theorem transportTo_eq_transport {S S' : Set AmbientSpace} {r : g.reflectionGroup}
    (hr : r.1 '' S = S') (huniq : ∀ r' : g.reflectionGroup, r'.1 '' S = S' → r' = r)
    (F : D.GaugeField → ℂ) :
    g.transportTo S S' F = g.transport r F := by
  have hmove : g.mover S S' = r :=
    huniq _ (Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' S = S') ⟨r, hr⟩)
  rw [transportTo, hmove]
theorem torusTransportTo_eq_torusTransport {C C' : Set D.Torus} {r' : D.Torus → D.Torus}
    (hr : r' ∈ g.inducedTorusMaps) (hC : r' '' C = C')
    (huniq : ∀ s ∈ g.inducedTorusMaps, s '' C = C' → s = r')
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusTransportTo C C' F = g.torusTransport r' F := by
  have hmove : g.torusCarrier C C' = r' := by
    have hs := Classical.epsilon_spec (p := fun s : D.Torus → D.Torus =>
      s ∈ g.inducedTorusMaps ∧ s '' C = C') ⟨r', hr, hC⟩
    exact huniq _ hs.1 hs.2
  rw [torusTransportTo, hmove]
def cellProduct (C : Set D.Torus) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  fun U => ∏ᶠ C' ∈ g.torusCellSet, g.torusTransportTo C C' F U
def cellChessboardSeminorm (C : Set D.Torus) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    ℝ :=
  ‖D.periodicExpectation (g.cellProduct C F)‖ ^ (1 / g.cellNumber)
def chessboardNormOfCell (S : Set AmbientSpace) (F : D.GaugeField → ℂ) : ℝ :=
  g.cellChessboardSeminorm (D.proj '' S) (D.liftedObservable F)
theorem cellProduct_eq_torusProduct {C : Set D.Torus}
    (hbij : BijOn (fun r' : D.Torus → D.Torus => r' '' C) g.inducedTorusMaps g.torusCellSet)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) : g.cellProduct C F = g.torusProduct F := by
  funext U
  refine (finprod_mem_eq_of_bijOn (fun r' : D.Torus → D.Torus => r' '' C) hbij
    fun r' hr' => ?_).symm
  rw [g.torusTransportTo_eq_torusTransport hr' rfl fun s hs hsC => hbij.injOn hs hr' hsC]
theorem chessboardNorm_eq_torusChessboardNorm {C : Set D.Torus}
    (hbij : BijOn (fun r' : D.Torus → D.Torus => r' '' C) g.inducedTorusMaps g.torusCellSet)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.cellChessboardSeminorm C F = g.torusChessboardNorm F := by
  rw [cellChessboardSeminorm, g.cellProduct_eq_torusProduct hbij, torusChessboardNorm, cellNumber]
end ReflectionGrid
end ChessboardTori
end YangMills.Construction
end
