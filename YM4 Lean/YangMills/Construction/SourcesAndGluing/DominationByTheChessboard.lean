import YangMills.Construction.SourcesAndGluing.GridsMirrorGridsCellAlgebrasAndTheChessboardValue
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open InfiniteLattice (AmbientSpace)
structure GluingSetup.ScaleAndOrigin (D : GluingSetup) where
  scale : ℝ
  scale_eq_zpow : ∃ j : ℤ, scale = (D.L : ℝ) ^ j
  le_scale : (D.L : ℝ) ^ 2 * D.mesh ≤ scale
  origin : AmbientSpace
  origin_ne : ∀ (μ : Fin 4) (i : ℤ), origin μ ≠ D.mesh * i
namespace GluingSetup.ScaleAndOrigin
variable {D : GluingSetup} (s : D.ScaleAndOrigin)
theorem isCellScale_withSide {m' : ℕ+}
    (h : 2 * s.scale ≤ (D.withCutoffAndSide D.K m').side) :
    (D.withCutoffAndSide D.K m').IsCellScale s.scale := by
  have hL : (1 : ℝ) ≤ (D.L : ℝ) ^ 2 := one_le_pow₀ D.one_lt_L.le
  have ha : D.mesh ≤ s.scale := by
    refine le_trans ?_ s.le_scale
    nlinarith [D.mesh_pos]
  exact ⟨⟨s.scale_eq_zpow, ha, by linarith⟩, s.le_scale⟩
def gridAt (m' : ℕ+) (h : 2 * s.scale ≤ (D.withCutoffAndSide D.K m').side) :
    CubicGrid (D.withCutoffAndSide D.K m') :=
  ⟨s.scale, (s.isCellScale_withSide h).1, s.origin, s.origin_ne⟩
open Classical in
def normAt (m' : ℕ+) (F : D.GridField → ℂ) : ℝ :=
  if h : 2 * s.scale ≤ (D.withCutoffAndSide D.K m').side then
    (s.gridAt m' h).chessboardNorm F
  else 0
end GluingSetup.ScaleAndOrigin
def ChessboardDomination : Prop :=
  ∀ (D : GluingSetup) (s : D.ScaleAndOrigin) (ν : Measure D.GridField),
    ν ∈ InfiniteLattice.periodicGibbsSet D.L D.K D.β →
    ∀ n : ℕ+ → ℕ+,
      Monotone (fun k => (D.withCutoffAndSide D.K (n k)).side) →
      Tendsto (fun k => (D.withCutoffAndSide D.K (n k)).side) atTop atTop →
    ∀ F : (Fin 4 → ℤ) → D.GridField → ℂ,
      (∀ (k : ℕ+) (h : 2 * s.scale ≤ (D.withCutoffAndSide D.K (n k)).side) (i : Fin 4 → ℤ),
        F i ∈ (s.gridAt (n k) h).cubeAlgebra i) →
      (Function.mulSupport F).Finite →
      ‖∫ U, ∏ᶠ i, F i U ∂ν‖ ≤ liminf (fun k => ∏ᶠ i, s.normAt (n k) (F i)) atTop ∧
      liminf (fun k => ∏ᶠ i, s.normAt (n k) (F i)) atTop ≤
        ∏ᶠ i, limsup (fun k => s.normAt (n k) (F i)) atTop
end YangMills.Construction.SourcesAndGluing
end
