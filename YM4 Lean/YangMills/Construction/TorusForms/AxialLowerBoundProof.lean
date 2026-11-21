import YangMills.Construction.SeparatedSequences.LowerBoundOnTheContoursAtEveryLevelProof
import YangMills.Construction.TorusForms.BlockAndCorridorParameters
import YangMills.Construction.TorusForms.BlocksCorridorsDomainsTrees
import YangMills.Construction.TorusForms.CurlAndAverageBoundOnIntegerLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AxialLowerBoundProof
section OnTheTorus
open YangMills.Construction.Lattice YangMills.Construction.BlockSpin Finset
section Torus
variable (S : LatticeParameters) {ℓ : Fin S.d → ℝ} [PeriodsMultipleOfBlock S ℓ]
variable {S}
theorem blockOf_unique (hb : BlockGeometry) {x : LatticeSite ℓ 1}
    {y y' : LatticeSite ℓ (S.L : ℝ)} (h : x ∈ blockOf S 1 1 y) (h' : x ∈ blockOf S 1 1 y') :
    y = y' :=
  ((hb.1 S ℓ 1 (S.L : ℝ) 1 PeriodsMultipleOfBlock.isBlockSpacing_one).2.1.1 x).unique h h'
end Torus
end OnTheTorus
section OnTheIntegerLattice
open YangMills.Construction.Lattice (LatticeParameters)
open YangMills.Construction.BlockSpin (InBlockIndexRange axisMoves blockOffset)
open YangMills.Construction.IntegerLattice
section Wrapping
variable (S : LatticeParameters) (H : ℕ)
def wrapPeriod : Fin S.d → ℝ := fun _ => ((2 * H + 2 : ℕ) : ℝ) * (S.L : ℝ)
instance : BlockSpin.PeriodsMultipleOfBlock S (wrapPeriod S H) :=
  ⟨fun _ => ⟨2 * H + 2, by omega, rfl⟩⟩
def siteOfCoords (v : Fin S.d → ℤ) : ScaledSite S.d 1 := ⟨v, mem_scaledLattice_one v⟩
variable {S H}
end Wrapping
theorem sum_comp_le_of_injOn {α β : Type*} (src : Finset α) (tgt : Finset β) (φ : α → β)
    (F : β → ℝ) (F_nonneg : ∀ b, 0 ≤ F b) (φ_inj : Set.InjOn φ src)
    (maps : ∀ a ∈ src, φ a ∈ tgt) :
    ∑ a ∈ src, F (φ a) ≤ ∑ b ∈ tgt, F b := by
  classical
  calc ∑ a ∈ src, F (φ a) = ∑ b ∈ src.image φ, F b := (Finset.sum_image φ_inj).symm
    _ ≤ ∑ b ∈ tgt, F b := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr maps) fun b _ _ => F_nonneg b
section Forms
variable {S : LatticeParameters} {H : ℕ}
theorem blockOffset_one (S : LatticeParameters) : blockOffset S 1 = S.offset := by apply _root_.YangMills.Construction.SeparatedClasses.TreeLowerBound.blockOffset_one <;> assumption
end Forms
section Transfer
variable {S : LatticeParameters} {H : ℕ}
def HasMargin (H : ℕ) (r : ℤ) (y : ScaledSite S.d S.L) : Prop := ∀ μ, |y.1 μ| + r ≤ H
theorem HasMargin.mono {r r' : ℤ} {y : ScaledSite S.d S.L} (h : HasMargin H r y) (hr : r' ≤ r) :
    HasMargin H r' y := fun μ => by linarith [h μ]
end Transfer
section Assembly
variable {S : LatticeParameters} {H : ℕ}
theorem exists_margin {Λ' : Set (ScaledSite S.d S.L)} (hfin : Λ'.Finite) (r : ℕ) :
    ∃ H : ℕ, ∀ y ∈ Λ', HasMargin H r y := by
  refine ⟨∑ z ∈ hfin.toFinset, ∑ ν, (z.1 ν).natAbs + r, fun y hy μ => ?_⟩
  have one : (y.1 μ).natAbs ≤ ∑ ν, (y.1 ν).natAbs :=
    Finset.single_le_sum (f := fun ν => (y.1 ν).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ μ)
  have all : ∑ ν, (y.1 ν).natAbs ≤ ∑ z ∈ hfin.toFinset, ∑ ν, (z.1 ν).natAbs :=
    Finset.single_le_sum (f := fun z : ScaledSite S.d S.L => ∑ ν, (z.1 ν).natAbs)
      (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr hy)
  have cast : ((y.1 μ).natAbs : ℤ) ≤ ((∑ z ∈ hfin.toFinset, ∑ ν, (z.1 ν).natAbs : ℕ) : ℤ) := by
    exact_mod_cast one.trans all
  rw [← Int.natCast_natAbs]
  push_cast at cast ⊢
  linarith
end Assembly
end OnTheIntegerLattice
end YangMills.Construction.AxialLowerBoundProof
