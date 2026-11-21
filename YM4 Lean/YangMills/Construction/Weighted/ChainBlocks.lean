import YangMills.Construction.Weighted.SeparatedRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Weighted
namespace TorusData
variable (D : TorusData)
abbrev BareSite : Type := ↥(D.latticeAt (D.scale 0))
def bareSites (X : Set D.Space) : Set D.BareSite := {x | (x : D.Space) ∈ X}
end TorusData
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def level (y : D.Space) : ℕ := sInf {n | y ∈ B.layerSites n}
def block (y : D.Space) : Set D.BareSite := D.bareSites (B.siteCube y)
def blockIndicator (y : D.Space) : D.BareSite → ℝ := (B.block y).indicator 1
def blockCenter (x : D.BareSite) : D.Space :=
  Classical.epsilon fun y => y ∈ B.allSites ∧ x ∈ B.block y
def bareLevel (x : D.BareSite) : ℕ := B.level (B.blockCenter x)
def bareScale (x : D.BareSite) : ℝ := B.siteScale (B.blockCenter x)
def IsBlockUnion (W : Set D.Space) : Prop :=
  ∃ Y : Set D.Space, Y.Nonempty ∧ Y ⊆ B.allSites ∧ W = ⋃ y ∈ Y, B.siteCube y
def sitesIn (W : Set D.Space) : Set D.Space := B.allSites ∩ W
end SeparatedChain
end Weighted
end YangMills.Construction
