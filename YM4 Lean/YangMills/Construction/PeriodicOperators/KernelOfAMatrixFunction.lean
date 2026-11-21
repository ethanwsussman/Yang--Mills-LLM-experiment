import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
variable (I I' : PeriodicData)
def matFunIntegrand (M : (Fin 4 → ℂ) → QuotHom I I') (x' : I'.Carrier) (x : I.Carrier)
    (κ : InfiniteLattice.AmbientSpace) : ℂ :=
  carrierEntry (M (toComplexVec κ)) x' x *
    Complex.exp (-Complex.I * bilinDot (toComplexVec κ) (toComplexVec (I.pos x - I'.pos x')))
def matFunKernel (M : (Fin 4 → ℂ) → QuotHom I I') : KernelMatrix I.Carrier I'.Carrier :=
  fun x' x => torusAverage (matFunIntegrand I I' M x' x)
def SymbolInvertibleOnReals (T : I.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ κ ∈ realDualPoints, IsInvertibleQuotHom (symbolHom I I T κ)
def periodicInverse (T : I.Carrier → I.Carrier → ℂ) : KernelMatrix I.Carrier I.Carrier :=
  matFunKernel I I fun κ => quotHomInverse (symbolHom I I T κ)
end YangMills.Construction.PeriodicOperators
end
