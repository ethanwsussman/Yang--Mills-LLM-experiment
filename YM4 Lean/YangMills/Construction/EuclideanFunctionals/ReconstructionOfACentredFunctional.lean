import YangMills.Construction.EuclideanFunctionals.CombinationsOfTuplesComplexComponentsAndConvergenceInC1
import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import YangMills.Construction.SpectralTheory.ResolvedOperatorsAndTheirJointSpectralMeasure
import Mathlib
set_option autoImplicit false
open Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp)
open YangMills.Construction.BorelSpectral
section
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]
def readClass (q : finCombIn upperHalf →ₗ[ℂ] 𝓗) (G : FreeSep) : 𝓗 :=
  open Classical in if hG : G ∈ finCombIn upperHalf then q ⟨G, hG⟩ else 0
def emptyComb : finCombIn upperHalf :=
  ⟨toFree [], by
    rw [finCombIn_eq_freeSpanIn]
    exact emptyElt.2⟩
def hamMomFamily (K : UnboundedOp 𝓗) (Q : Fin 3 → UnboundedOp 𝓗) : Fin 4 → UnboundedOp 𝓗 :=
  Fin.cons K Q
variable [CompleteSpace 𝓗]
def hamMomMeasure (K : UnboundedOp 𝓗) (Q : Fin 3 → UnboundedOp 𝓗) :
    SpectralMeasure (univ : Set (Fin 4 → ℝ)) 𝓗 :=
  YangMills.Construction.ResolvedOps.jointSpectralMeasure (by norm_num) (hamMomFamily K Q)
def spatialTranslOp (μ : SpectralMeasure (univ : Set (Fin 4 → ℝ)) 𝓗) (u : R4) :
    𝓗 →L[ℂ] 𝓗 :=
  μ.integralOp fun x =>
    Complex.exp (Complex.I * ((∑ i : Fin 3, u i.castSucc * x.1 i.succ : ℝ) : ℂ))
variable (𝓗) in
structure OSReconstruction (S : ConnFamily) where
  cls : finCombIn upperHalf →ₗ[ℂ] 𝓗
  inner_cls : ∀ G B : finCombIn upperHalf,
    ⟪cls G, cls B⟫_ℂ = osForm S G.1 B.1
  denseRange_cls : DenseRange cls
  ham : UnboundedOp 𝓗
  ham_selfAdjoint : YangMills.Construction.OperatorTransport.IsSelfAdjointUnbounded ham
  ham_nonneg : YangMills.Construction.OperatorTransport.IsNonnegUnbounded ham
  mom : Fin 3 → UnboundedOp 𝓗
  mom_selfAdjoint : ∀ i, YangMills.Construction.OperatorTransport.IsSelfAdjointUnbounded (mom i)
  mom_commute : ∀ i l, i ≠ l →
    YangMills.Construction.ResolvedOps.StronglyCommute (mom i) (mom l)
  mom_commute_ham : ∀ i,
    YangMills.Construction.ResolvedOps.StronglyCommute (mom i) ham
  rotOp : timeStabilizer → 𝓗 →ₗ[ℂ] 𝓗
  rotOp_unitary : ∀ g, YangMills.Construction.OperatorTransport.IsUnitaryMap (rotOp g)
  expHam_cls : ∀ s : ℝ, 0 ≤ s → ∀ G : finCombIn upperHalf,
    YangMills.Construction.ResolvedOps.expComplex ham (s : ℂ) (cls G) =
      readClass cls ((EuclidMotion.transl (s • timeVec)).actFree G.1)
  transl_cls : ∀ u ∈ spatialVecs, ∀ G : finCombIn upperHalf,
    spatialTranslOp (hamMomMeasure ham mom) u (cls G) =
      readClass cls ((EuclidMotion.transl u).actFree G.1)
  rotOp_cls : ∀ (g : timeStabilizer) (G : finCombIn upperHalf),
    rotOp g (cls G) = readClass cls ((g : EuclidMotion).actFree G.1)
def OSReconstruction.vac {S : ConnFamily} (T : OSReconstruction 𝓗 S) : 𝓗 :=
  T.cls emptyComb
end
end YangMills.Construction.EuclideanFunctionals
