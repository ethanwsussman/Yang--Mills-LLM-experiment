import YangMills.Construction.Towers.SumsProductsAndTransposesOfJetsWithHolomorphicComponentsProof
import YangMills.Construction.ComplexAnalysis.RealLocusIdentity
import Mathlib
open Set
namespace YangMills.Construction.ComplexAnalysis
open Coordinates RealPiece
private theorem isHolomorphicIn_zero {n : ℕ} {U : Set (ComplexCoordinates n)} (hU : IsOpen U) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun _ _ => 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.JetClosure.ScalarHolomorphic.zero <;> assumption
private theorem eq_zero_of_eq_zero_on_realLocus (H : EqOfEqOnRealOpenAndConjHolomorphic)
    {n : ℕ} {U S : Set (ComplexCoordinates n)} {g : ComplexCoordinates n → ℂ} (hU : IsOpen U)
    (hUc : IsConnected U) (hg : ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => g z))
    (hS : S.Nonempty) (hSU : S ⊆ U ∩ ComplexCoordinates.realLocus n)
    (hSo : Matrices.ComplexMatrix2.IsRelativelyOpen (ComplexCoordinates.realLocus n) S)
    (hg0 : ∀ z ∈ S, g z = 0) : ∀ z ∈ U, g z = 0 := by
  intro z hz
  have key := H.1 n 1 U S (fun z _ => g z) (fun _ _ => 0) hU hUc hg (isHolomorphicIn_zero hU) hS
    hSU hSo (fun w hw => funext fun _ => hg0 w hw) hz
  exact congrFun key 0
private theorem conjCoords_of_mem_realLocus {n : ℕ} {x : ComplexCoordinates n}
    (hx : x ∈ ComplexCoordinates.realLocus n) : conjCoords x = x :=
  funext fun j => Complex.conj_eq_iff_im.mpr (hx j)
private theorem conjCoords_conjCoords {n : ℕ} (z : ComplexCoordinates n) :
    conjCoords (conjCoords z) = z :=
  funext fun j => by simp [conjCoords]
theorem identityTheoremOnRealLocus_of_eqOnRealPiece (H : EqOfEqOnRealOpenAndConjHolomorphic) :
    IdentityTheoremOnRealLocus := by
  refine ⟨fun n _ U g hU hUc hg S hS hSU hSo hg0 =>
    eq_zero_of_eq_zero_on_realLocus H hU hUc hg hS hSU hSo hg0, ?_⟩
  intro n₁ n₂ _ _ U₁ U₂ g hU₁ hU₁c hU₂ hU₂c hconj hg₁ hg₂ S hS hSU hSo hg0
  obtain ⟨⟨a, b⟩, hab⟩ := hS
  obtain ⟨V, hV, rfl⟩ := hSo
  have ha : a ∈ ComplexCoordinates.realLocus n₁ := hab.2.1
  have hb : b ∈ ComplexCoordinates.realLocus n₂ := hab.2.2
  have hfiber : ∀ y ∈ {y | (a, y) ∈ V} ∩ ComplexCoordinates.realLocus n₂, ∀ w ∈ U₁,
      g (w, y) = 0 := by
    intro y hy w hw
    have hay : (a, y) ∈ V ∩ (ComplexCoordinates.realLocus n₁ ×ˢ ComplexCoordinates.realLocus n₂) :=
      ⟨hy.1, ha, hy.2⟩
    have hyU : y ∈ U₂ := (hSU hay).1.2
    have hvan := eq_zero_of_eq_zero_on_realLocus H (g := fun z => g (conjCoords z, y))
      (S := {x | (x, y) ∈ V} ∩ ComplexCoordinates.realLocus n₁) hU₁ hU₁c (hg₁ y hyU) ⟨a, hy.1, ha⟩
      (fun x hx => ⟨(hSU (show (x, y) ∈ V ∩
        (ComplexCoordinates.realLocus n₁ ×ˢ ComplexCoordinates.realLocus n₂) from
        ⟨hx.1, hx.2, hy.2⟩)).1.1, hx.2⟩)
      ⟨_, hV.preimage (continuous_id.prodMk continuous_const), rfl⟩
      (fun x hx => by
        show g (conjCoords x, y) = 0
        rw [conjCoords_of_mem_realLocus hx.2]
        exact hg0 (x, y) ⟨hx.1, hx.2, hy.2⟩)
      (conjCoords w) (hconj hw)
    simpa only [conjCoords_conjCoords] using hvan
  rintro ⟨w, y⟩ ⟨hw, hy⟩
  exact eq_zero_of_eq_zero_on_realLocus H (g := fun y => g (w, y))
    (S := {y | (a, y) ∈ V} ∩ ComplexCoordinates.realLocus n₂) hU₂ hU₂c (hg₂ w hw) ⟨b, hab.1, hb⟩
    (fun y hy' => ⟨(hSU (show (a, y) ∈ V ∩
      (ComplexCoordinates.realLocus n₁ ×ˢ ComplexCoordinates.realLocus n₂) from
      ⟨hy'.1, ha, hy'.2⟩)).1.2, hy'.2⟩)
    ⟨_, hV.preimage (continuous_const.prodMk continuous_id), rfl⟩
    (fun y hy' => hfiber y hy' w hw) y hy
end YangMills.Construction.ComplexAnalysis
