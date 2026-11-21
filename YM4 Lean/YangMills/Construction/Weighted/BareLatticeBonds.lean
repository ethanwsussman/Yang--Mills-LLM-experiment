import YangMills.Construction.Weighted.ChainBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace Weighted
namespace TorusData
variable (D : TorusData)
def unitStep (μ : Fin 4) : D.Space := torusProj D.side (Pi.single μ (D.scale 0))
@[ext]
structure Bond where
  source : D.BareSite
  target : D.BareSite
  isPositive : ∃ μ : Fin 4, (target : D.Space) - (source : D.Space) = D.unitStep μ
variable {D}
def bondsMeeting (E : Set D.BareSite) : Set D.Bond := {b | b.source ∈ E ∨ b.target ∈ E}
def bondsWithin (E : Set D.BareSite) : Set D.Bond := {b | b.source ∈ E ∧ b.target ∈ E}
def bondsAtSite (x : D.BareSite) : Set D.Bond := {b | b.source = x ∨ b.target = x}
def Adjacent (x x' : D.BareSite) : Prop :=
  ∃ b : D.Bond, (b.source = x ∧ b.target = x') ∨ (b.source = x' ∧ b.target = x)
end TorusData
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def blockBondSet (y : D.Space) : Set D.Bond := ⋃ x ∈ B.block y, TorusData.bondsAtSite x
def thickenedBlock (y : D.Space) : Set D.BareSite :=
  B.block y ∪ {x' | ∃ x ∈ B.block y, TorusData.Adjacent x x'}
end SeparatedChain
end Weighted
end YangMills.Construction
