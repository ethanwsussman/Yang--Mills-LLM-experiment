import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
section IndexEmbedding
open LogDetSecondDerivs (descendField)
variable {G F : PeriodicData}
structure IsIndexEmbedding (e : G.Carrier → F.Carrier) : Prop where
  injective : Function.Injective e
  map_translate : ∀ n x, e (G.translate n x) = F.translate n (e x)
  pos_map : ∀ x, F.pos (e x) = G.pos x
def extendByZero (e : G.Carrier → F.Carrier) (f : G.Carrier → ℂ) : F.Carrier → ℂ :=
  Function.extend e f 0
def extendQuotByZero (e : G.Carrier → F.Carrier) (ε : G.UnitQuot → ℂ) : F.UnitQuot → ℂ :=
  descendField F 1 (extendByZero e fun x => ε (G.mkQuot 1 x))
end IndexEmbedding
namespace ExtendByZeroJets
def Claim : Prop :=
  ∀ G F I I' : PeriodicData, IsPeriodic G → IsPeriodic F → IsPeriodic I →
    IsPeriodic I' → ∀ e : G.Carrier → F.Carrier, IsIndexEmbedding e →
      ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
        IsLocalOpFun G I I' (fun f => T (extendByZero e f)) ∧
        ∀ (p : Fin 4 → ℂ) (εPlus εMinus : G.UnitQuot → ℂ),
          jetAlong G I I' (fun f => T (extendByZero e f)) p εPlus εMinus =
            jetAlong F I I' T p (extendQuotByZero e εPlus)
              (extendQuotByZero e εMinus)
end ExtendByZeroJets
end YangMills.Construction.PeriodicOperators
end
