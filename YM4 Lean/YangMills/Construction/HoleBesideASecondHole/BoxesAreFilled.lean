import YangMills.Construction.HoleBesideASecondHole.FieldWithTheBoxesFilled
import YangMills.Construction.HoleBesideASecondHole.TurningAChainKeepsItsElements
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace HoleSavings
open BlockAverages LumpContours Holes ChainGauges HoleBounds
variable {F : BlockFrame}
namespace HoleData
variable {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
open Classical in
structure IsBoxFilling (C K : ℝ) (index : Finset (Finset (F.Site F.depth)) → ℕ)
    (center : Finset (Finset (F.Site F.depth)) → F.Site F.depth) (U : F.FieldChain)
    (Wf : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion) : Prop where
  mem_excludedBoxes_of_adj : ∀ y ∈ D.coreCells C 5, ∀ y' ∈ D.coreCells C 5, cellSupDist y y' ≤ 1 →
    ∀ Z ∈ excludedBoxes J₀ D.hotFineLumps y,
    ((Z ∩ sitesBelow F.depth y).Nonempty ∨ (Z ∩ sitesBelow F.depth y').Nonempty) →
      Z ∈ excludedBoxes J₀ D.hotFineLumps y'
  pairwise_apart : ∀ Z ∈ D.coreBoxes C, ∀ Z' ∈ D.coreBoxes C, Z ≠ Z' → ¬ AreWithin 2 Z Z'
  exists_hole_superset : ∀ Z ∈ D.coreBoxes C, ∃ H ∈ D.holesAt C index center, Z ⊆ H.innerBox
  exists_gauge : ∃ G : F.Site F.depth → UnitQuaternion, ∀ Z ∈ D.coreBoxes C, (∀ x ∈ Z, G x = 1) ∧
    (∀ b : F.Site F.depth × Fin 4, BondTouches Z b → gaugeTransform G Wf b.1 b.2 = 1) ∧
    ∀ b : F.Site F.depth × Fin 4, b.1 ∈ boxShell Z → b.1 + unitStep F.depth b.2 ∈ boxShell Z →
      ‖((gaugeTransform G D.fineField b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ K * s
  eq_of_not_touches : ∀ b : F.Site F.depth × Fin 4, (∀ Z ∈ D.coreBoxes C, ¬ BondTouches Z b) →
    Wf b.1 b.2 = D.fineField b.1 b.2
  curvature_le : ∀ y ∈ D.coreCells C 5, ∀ y' ∈ D.coreCells C 5, cellSupDist y y' ≤ 1 →
    ∑ p ∈ cutPlaquettes (sitesBelow F.depth y ∪ sitesBelow F.depth y'), plaquetteDefect Wf p ^ 2 ≤ K * s ^ 2
  eq_off_holes : ∀ b ∈ cutBonds (cutBelow F.depth (D.coreCells C 5)),
    b.1 ∉ holeSupport (D.holesAt C index center) →
    b.1 + unitStep F.depth b.2 ∉ holeSupport (D.holesAt C index center) →
      Wf b.1 b.2 = D.fineField b.1 b.2 ∧ U F.depth b.1 b.2 = D.fineField b.1 b.2
  gauge_eq_one : ∀ x, x ∉ holeSupport (D.holesAt C index center) → γ x = 1
  gaugeChain_top : gaugeChain γ U F.depth = gaugeTransform γ (U F.depth)
  norm_sub_le : ∀ y ∈ D.coreCells C 5, ∀ y' ∈ D.coreCells C 5, cellSupDist y y' ≤ 1 →
    ∀ b ∈ cutBonds (sitesBelow F.depth y ∪ sitesBelow F.depth y'),
      ‖((gaugeChain γ U F.depth b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
        ((Wf b.1 b.2 : UnitQuaternion) : ℍ[ℝ])‖ ≤ K * Real.sqrt L * s
  cutChainEnergy_eq : ∀ Y : Finset (F.Site F.depth),
    cutChainEnergy a F.depth Y (gaugeChain γ U) = cutChainEnergy a F.depth Y U
  plaquetteDefect_top_eq : ∀ p, plaquetteDefect (gaugeChain γ U F.depth) p = plaquetteDefect (U F.depth) p
  disjoint_of_nearbyLumps_empty : ∀ y ∈ D.coreCells C 5, nearbyLumps D.hotFineLumps y = ∅ →
    (∀ H ∈ D.holesAt C index center, H.outerBox ∩ sitesBelow F.depth y = ∅) ∧
      ∀ Z ∈ D.coreBoxes C, Z ∩ sitesBelow F.depth y = ∅
end HoleData
def boxFillingStatement : Prop :=
  ∀ (C₀ : ℝ) (J₀ : ℕ) (a C : ℝ), 0 < C₀ → 1 ≤ J₀ → 1 ≤ a → 0 < C → ∃ K : ℝ, 0 < K ∧ ∃ L₀ : ℕ,
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ g : LumpGrid L, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∀ (θ : ℝ) (F : BlockFrame) (D : HoleData F g a s θ J₀), F.blockSide = L → IsCubicTorus F 4096 →
        ∀ (index : Finset (Finset (F.Site F.depth)) → ℕ)
          (center : Finset (Finset (F.Site F.depth)) → F.Site F.depth)
          (U : F.FieldChain), D.IsHoleFamily C index center → D.IsHoleFillingChain C C₀ index center U →
          ∃ (Wf : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion),
            D.IsBoxFilling C K index center U Wf γ
end HoleSavings
end YangMills.Construction
end
