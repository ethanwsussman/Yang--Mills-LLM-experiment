import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.Lattice.BlocksCorridorsPivotBondsAndTheWeightsOfTheOneStepAverageProof
import YangMills.Construction.Torus.CellsThatMeetAreNearProof
import YangMills.Construction.Torus.ClosedFormsWithVanishingAveragesAreGradientsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.DiffAndMeans
open Set YangMills.Construction.TorusMetric
def symBox (m : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m
def bondWindow (m : ℕ) (μ : Fin 4) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun ν => if ν = μ then Finset.Icc (-(m : ℤ)) (3 * m + 1)
    else Finset.Icc (-(m : ℤ)) m
theorem mem_bondWindow {m : ℕ} {μ : Fin 4} {k : Fin 4 → ℤ} :
    k ∈ bondWindow m μ ↔ (-(m : ℤ) ≤ k μ ∧ k μ ≤ 3 * m + 1) ∧
      ∀ ν, ν ≠ μ → -(m : ℤ) ≤ k ν ∧ k ν ≤ m := by
  simp only [bondWindow, Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨by simpa using h μ, fun ν hν => ?_⟩
    simpa [hν] using h ν
  · rintro ⟨h1, h2⟩ ν
    by_cases hν : ν = μ
    · subst hν
      simpa using h1
    · simpa [hν] using h2 ν hν
theorem add_single_apply_self (μ : Fin 4) (i : ℤ) (k : Fin 4 → ℤ) :
    (k + Pi.single μ i : Fin 4 → ℤ) μ = k μ + i := by
  simp
theorem add_single_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (i : ℤ) (k : Fin 4 → ℤ) :
    (k + Pi.single μ i : Fin 4 → ℤ) ν = k ν := by
  simp [Pi.single_eq_of_ne h]
theorem halfSpan_two_mul_add_one (m : ℕ) : halfSpan (2 * m + 1) = m := by
  simp [halfSpan]
theorem tentMultiplicity_le (N : ℕ) (s : ℤ) : tentMultiplicity N s ≤ N := by apply _root_.YangMills.Construction.UnitSpacingLattice.BlockAverageProof.IntCoords.tentMultiplicity_le <;> assumption
section Points
variable {S σ : ℝ}
def shiftPoint (σ : ℝ) (y : Torus4 S) (k : Fin 4 → ℤ) : Torus4 S :=
  y + torusProj S fun ν => σ * (k ν : ℝ)
theorem memBondWindow_iff (m : ℕ) (μ : Fin 4) (k : Fin 4 → ℤ) :
    MemBondWindow (2 * m + 1) μ k ↔ k ∈ bondWindow m μ := by
  rw [MemBondWindow, halfSpan_two_mul_add_one, mem_bondWindow]
  have key : ∀ s : ℤ, |(s : ℝ)| ≤ (m : ℝ) ↔ -(m : ℤ) ≤ s ∧ s ≤ m := by
    intro s
    rw [abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, fun ν hν => (key _).1 (h3 ν hν)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, fun ν hν => (key _).2 (h3 ν hν)⟩
end Points
section Numbers
variable (D : ScaleData)
theorem blockingFactor_pos : 0 < D.L := D.blocking.odd_blockingFactor.pos
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_succ (n : ℕ) : D.levelSpacing (n + 1) = (D.L : ℝ) * D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ClosedMeanFree.levelSpacing_succ <;> assumption
theorem admitsPartition_levelSpacing {n : ℕ} (hn : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.admitsPartition_levelSpacing_of_le_lastLevel <;> assumption
variable {D}
theorem posBondDir_bondFrom {n : ℕ} (hn : n ≤ D.lastLevel) (x : D.SiteAt n) (μ : Fin 4) :
    ScaleData.posBondDir (ScaleData.bondFrom x μ) = μ := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.posBondDir_bondFrom <;> assumption
theorem tgt_eq_src_add {n : ℕ} (c : D.PosBond n) :
    c.1.tgt = c.1.src + unitStep D.torusSide (D.levelSpacing n) (ScaleData.posBondDir c) := by apply _root_.YangMills.Construction.GeneralTorus.ClosedMeanFree.tgt_eq_src_add <;> assumption
theorem bondFrom_src_posBondDir {n : ℕ} (c : D.PosBond n) :
    ScaleData.bondFrom c.1.src (ScaleData.posBondDir c) = c := by apply _root_.YangMills.Construction.GeneralTorus.ClosedMeanFree.bondFrom_src_dir <;> assumption
def posBondEquiv {n : ℕ} (hn : n ≤ D.lastLevel) : D.SiteAt n × Fin 4 ≃ D.PosBond n where
  toFun p := ScaleData.bondFrom p.1 p.2
  invFun c := (c.1.src, ScaleData.posBondDir c)
  left_inv p := Prod.ext rfl (posBondDir_bondFrom hn p.1 p.2)
  right_inv c := bondFrom_src_posBondDir c
theorem finsum_posBond {n : ℕ} (hn : n ≤ D.lastLevel) (g : D.PosBond n → ℝ) :
    ∑ᶠ c, g c = ∑ᶠ x : D.SiteAt n, ∑ μ : Fin 4, g (ScaleData.bondFrom x μ) := by
  haveI : Finite (D.SiteAt n) := finite_latticeSite (admitsPartition_levelSpacing D hn).2
  haveI := Fintype.ofFinite (D.SiteAt n)
  rw [← finsum_comp_equiv (posBondEquiv hn), finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Fintype.sum_prod_type]
  rfl
end Numbers
section Squares
variable (D : ScaleData)
instance instFintypeBaseSite : Fintype D.BaseSite := Fintype.ofFinite _
theorem siteInner_eq_sum (f g : D.SiteField) :
    D.siteInner f g = D.levelSpacing 0 ^ 4 * ∑ x, f x * g x := by
  rw [ScaleData.siteInner, finsum_eq_sum_of_fintype]
def backwardDiff (μ : Fin 4) : D.SiteField →ₗ[ℝ] D.SiteField where
  toFun f x := (D.levelSpacing 0)⁻¹ * (f (x - unitStep D.torusSide (D.levelSpacing 0) μ) - f x)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem bondInner_eq_sum (B B' : D.BondField) :
    D.bondInner B B' =
      ∑ μ, D.siteInner (D.formComponent μ B) (D.formComponent μ B') := by
  rw [ScaleData.bondInner, finsum_posBond (Nat.zero_le _), finsum_eq_sum_of_fintype,
    Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [siteInner_eq_sum]
  rfl
end Squares
end YangMills.Construction.GeneralTorus.DiffAndMeans
