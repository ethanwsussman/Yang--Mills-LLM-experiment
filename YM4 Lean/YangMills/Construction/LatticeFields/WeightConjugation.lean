import YangMills.Construction.LatticeFields.FieldsAndDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
variable {d N : ℕ} {κ : LatticeShape d}
structure LipschitzWeight (δ : ℝ) (θ : LatticeSite N κ → ℝ) : Prop where
  pos : 0 < δ
  bdd : ∃ C : ℝ, ∀ x, |θ x| ≤ C
  lip : ∀ x y, |θ x - θ y| ≤ δ * siteDist x y
def restrictUnitSites [NeZero N] (θ : LatticeSite N κ → ℝ) : LatticeSite 1 κ → ℝ :=
  fun y => θ (unitSiteHom N κ y)
inductive LatticeScale : Type where
  | fine : LatticeScale
  | unit : LatticeScale
@[reducible] def LatticeScale.invSpacing (N : ℕ) : LatticeScale → ℕ
  | .fine => N
  | .unit => 1
def weightMul [NeZero N] (θ : LatticeSite N κ → ℝ) {I : Type} :
    (s : LatticeScale) → LatticeField (s.invSpacing N) κ I → LatticeField (s.invSpacing N) κ I
  | .fine, F => mulBase θ F
  | .unit, F => mulBase (restrictUnitSites θ) F
def weightConj [NeZero N] (θ : LatticeSite N κ → ℝ) (s t : LatticeScale) {I J : Type}
    (O : LatticeField (s.invSpacing N) κ I → LatticeField (t.invSpacing N) κ J) :
    LatticeField (s.invSpacing N) κ I → LatticeField (t.invSpacing N) κ J :=
  fun F => weightMul (fun x => Real.exp (-θ x)) t (O (weightMul (fun x => Real.exp (θ x)) s F))
end YangMills.Construction.LatticeFields
