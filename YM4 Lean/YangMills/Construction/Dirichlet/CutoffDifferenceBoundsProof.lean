import YangMills.Construction.Dirichlet.CentresNearBumps
import YangMills.Construction.Dirichlet.CollarGeometry
import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.Dirichlet.CoverCountProof
import Mathlib
import YangMills.Construction.Dirichlet.LiftDerivativeBounds
set_option autoImplicit false

section
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
structure CutoffDiffBounds (c : ℝ) : Prop where
  diff_on_bond : ∀ Q ∈ 𝒮.coverCubes, ∀ x x' : LatticeSite d S 𝒮.ξ,
    (x : PeriodicTorus d S) ∈ 𝒮.baseNbhd →
    supSetDist {(x : PeriodicTorus d S)} (𝒮.Ω 0) ≤ ENNReal.ofReal (3 * 𝒮.ξ) → IsNeighbor x x' →
    |𝒮.latticeCutoff Q x' - 𝒮.latticeCutoff Q x| ≤
      c * (L : ℝ) ^ 2 * 𝒮.ξ / ((𝒮.M : ℝ) * 𝒮.localScale x)
  laplacian_at_site : ∀ Q ∈ 𝒮.coverCubes, ∀ x : LatticeSite d S 𝒮.ξ,
    (x : PeriodicTorus d S) ∈ 𝒮.baseNbhd →
    supSetDist {(x : PeriodicTorus d S)} (𝒮.Ω 0) ≤ ENNReal.ofReal (3 * 𝒮.ξ) →
    |latticeLaplacian (𝒮.latticeCutoff Q) x| ≤
      c * (L : ℝ) ^ 4 / ((𝒮.M : ℝ) * 𝒮.localScale x) ^ 2
  diff_near_centre : ∀ Q ∈ 𝒮.coverCubes, ∀ y ∈ 𝒮.centres,
    ∀ x x' : LatticeSite d S 𝒮.ξ,
    supNorm ((x : PeriodicTorus d S) - y) ≤ 3 * 𝒮.centreSpacing y →
    supNorm ((x' : PeriodicTorus d S) - y) ≤ 3 * 𝒮.centreSpacing y →
    |𝒮.latticeCutoff Q x - 𝒮.latticeCutoff Q x'| ≤
      c * (L : ℝ) ^ 2 * siteLOneDist x x' / ((𝒮.M : ℝ) * 𝒮.centreSpacing y)
  forwardDiff_near_centre : ∀ Q ∈ 𝒮.coverCubes, ∀ y ∈ 𝒮.centres,
    ∀ x x' : LatticeSite d S 𝒮.ξ,
    supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y →
    supNorm ((x' : PeriodicTorus d S) - y) ≤ 2 * 𝒮.centreSpacing y → ∀ μ : Fin d,
    |forwardDiff μ (𝒮.latticeCutoff Q) x - forwardDiff μ (𝒮.latticeCutoff Q) x'| ≤
      c * (L : ℝ) ^ 4 * siteLOneDist x x' / ((𝒮.M : ℝ) * 𝒮.centreSpacing y) ^ 2
end YangMills.Construction.Dirichlet
end
end

open Set Filter Metric
open scoped ContDiff Topology
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
open YangMills.Construction.Dirichlet.CoverCount
noncomputable section
namespace YangMills.Construction.Dirichlet.CutoffDifferences
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E} {C : ℝ}
end Calculus
section TorusFacts
variable {d : ℕ} {S : ℝ}
theorem torusProj_add (v w : Fin d → ℝ) :
    torusProj d S (v + w) = torusProj d S v + torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem torusProj_sub (v w : Fin d → ℝ) :
    torusProj d S (v - w) = torusProj d S v - torusProj d S w := by
  funext μ
  simp [torusProj]
theorem torusProj_surjective : Function.Surjective (torusProj d S) := by apply _root_.YangMills.Construction.Dirichlet.CoverCountProof.torusProj_surjective <;> assumption
theorem continuous_torusProj : Continuous (torusProj d S) :=
  continuous_pi fun μ => (AddCircle.continuous_mk' S).comp (continuous_apply μ)
theorem supNorm_torusProj_le (v : Fin d → ℝ) : supNorm (torusProj d S v) ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro r ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, rfl, rfl⟩
theorem supNorm_nonneg (p : PeriodicTorus d S) : 0 ≤ supNorm p :=
  Real.sInf_nonneg (by rintro r ⟨w, -, rfl⟩; exact norm_nonneg _)
theorem supNorm_add_le (p q : PeriodicTorus d S) : supNorm (p + q) ≤ supNorm p + supNorm q := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_add_le <;> assumption
end TorusFacts
section Block
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
theorem spacing_le_centreSpacing (hL : 1 ≤ L) (y : PeriodicTorus d S) :
    𝒮.ξ ≤ 𝒮.centreSpacing y := by apply _root_.YangMills.Construction.Dirichlet.Commutator.ξ_le_centreSpacing <;> assumption
structure BoundInputs (c : ℝ) (Q : CentredCube d S) : Prop where
  one_le_factor : 1 ≤ L
  width_pos : 0 < (𝒮.M : ℝ)
  const_pos : 0 < c
  deriv_bounds : ∀ (n : ℕ) (v : Fin d → ℝ), LiesAtLevel 𝒮 n (torusProj d S v) →
    (∀ᶠ w in 𝓝 v, 1 ≤ 𝒮.bumpSqSum (torusProj d S w)) →
    LiftDerivatives.LiftDerivBounds 𝒮 c n Q v
  exists_level : ∀ p : PeriodicTorus d S, ∃ n, LiesAtLevel 𝒮 n p
  open_nbhd : ∃ V : Set (PeriodicTorus d S), IsOpen V ∧ 𝒮.baseNbhd ⊆ V ∧
    ∀ p ∈ V, 1 ≤ 𝒮.bumpSqSum p
  near_levels : ∀ y ∈ 𝒮.centres, ∀ p : PeriodicTorus d S,
    supNorm (p - y) ≤ 4 * 𝒮.centreSpacing y →
    p ∈ 𝒮.baseNbhd ∧
      ∀ n, LiesAtLevel 𝒮 n p → 𝒮.centreSpacing y ≤ (L : ℝ) * 𝒮.scaleAt n
  collar_facts : ∀ (n : ℕ) (y : PeriodicTorus d S), y ∈ shellSites L 𝒮.ξ 𝒮.Ω n →
    Geometry.CollarFacts 𝒮 n y
  exists_centre : ∀ x ∈ spacingLattice d S 𝒮.ξ, x ∈ 𝒮.Ω 0 → ∃ y ∈ 𝒮.centres, x ∈ 𝒮.cell y
variable {𝒮} {c : ℝ} {Q : CentredCube d S}
theorem BoundInputs.exists_lift (I : BoundInputs 𝒮 c Q) {y : PeriodicTorus d S}
    (hy : y ∈ 𝒮.centres) :
    ∃ ℓ : Fin d → ℝ, torusProj d S ℓ = y ∧ Geometry.LiftedBoxFacts 𝒮 y ℓ := by
  obtain ⟨n, -, hn⟩ := hy
  obtain ⟨ℓ, rfl⟩ := torusProj_surjective (d := d) (S := S) y
  exact ⟨ℓ, rfl, (I.collar_facts n _ hn).lifted ℓ rfl⟩
theorem BoundInputs.near_centre (I : BoundInputs 𝒮 c Q) {y : PeriodicTorus d S}
    (hy : y ∈ 𝒮.centres) {ℓ u : Fin d → ℝ}
    (hℓ : torusProj d S ℓ = y) (hu : ‖u - ℓ‖ ≤ 4 * 𝒮.centreSpacing y) :
    torusProj d S u ∈ 𝒮.baseNbhd ∧
      ∀ n, LiesAtLevel 𝒮 n (torusProj d S u) → 𝒮.centreSpacing y ≤ (L : ℝ) * 𝒮.scaleAt n :=
  I.near_levels y hy _ (by
    have hsub : torusProj d S u - y = torusProj d S (u - ℓ) := by rw [torusProj_sub, hℓ]
    rw [hsub]
    exact (supNorm_torusProj_le _).trans hu)
theorem localScale_pos (hL : 1 ≤ L) (x : LatticeSite d S 𝒮.ξ) : 0 < 𝒮.localScale x := by
  have hξ : 0 < 𝒮.ξ := 𝒮.isSeparatedChain.scale_pos
  unfold BlockSetting.localScale
  split_ifs
  · exact hξ.trans_le (spacing_le_centreSpacing 𝒮 hL _)
  · exact hξ
end Block
end YangMills.Construction.Dirichlet.CutoffDifferences
