import YangMills.Construction.ReflectionPositivity.SitesBondsAndPlaquettesOnTheTwoSides
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors
namespace LinkLevel
variable {D : MirrorData} (C : LinkLevel D)
def doubledField (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
    (vPos vNeg : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) :
    D.FieldSpace :=
  C.fieldOfCoords uPos uNeg (C.transversalQuot vPos vNeg)
abbrev DoubledCoords : Type :=
  (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) ×
    (C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary) ×
    (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) ×
    (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary)
def seriesCoeff (_C : LinkLevel D) (n : ℕ) : ℝ := (D.coupling / 4) ^ n / (n.factorial : ℝ)
def seriesTerm (n : ℕ) (ω ω' : C.DoubleSpace) : ℂ :=
  (C.seriesCoeff n : ℂ) *
    ∑ᶠ γ : Fin n → C.KernelLabel,
      C.kernelProd γ ω * starRingEnd ℂ (C.kernelProd γ ω')
end LinkLevel
namespace DoubledAction
variable {D : MirrorData}
def HalfActionFacts (C : LinkLevel D) : Prop :=
  (∀ p ∈ C.halfFaces .pos, Continuous (C.faceEnergyOfHalf p) ∧
    ∀ U : D.FieldSpace, PeriodicLattice.plaquetteCost U.1 p =
      C.faceEnergyOfHalf p (C.halfCoords .pos U)) ∧
  Continuous C.halfAction ∧ (∀ u, 0 ≤ C.halfAction u) ∧
  ∀ s : D.Symmetry, s.toFun = C.refl → ∀ U : D.FieldSpace,
    ∑ᶠ p ∈ C.halfFaces .neg, PeriodicLattice.plaquetteCost U.1 p =
        ∑ᶠ p ∈ C.halfFaces .pos,
          PeriodicLattice.plaquetteCost U.1 (MirrorData.Symmetry.faceImage s p) ∧
    ∑ᶠ p ∈ C.halfFaces .pos,
        PeriodicLattice.plaquetteCost U.1 (MirrorData.Symmetry.faceImage s p) =
      ∑ᶠ p ∈ C.halfFaces .pos,
        PeriodicLattice.plaquetteCost (C.reflectField U).1 p ∧
    ∑ᶠ p ∈ C.halfFaces .pos,
        PeriodicLattice.plaquetteCost (C.reflectField U).1 p =
      C.halfAction (C.transfer (C.halfCoords .neg U))
def TransversalTrace (C : LinkLevel D) : Prop :=
  ∀ p ∈ C.transversalFaces, ∀ (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
    (vPos vNeg : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary),
    C.kernelMat p (C.posPoint uPos vPos) =
        LinkLevel.extendByOne vPos (C.lowerEdge p) *
          LinkLevel.extendByOne uPos (C.cornerEdge .pos p) *
            (LinkLevel.extendByOne vPos (C.upperEdge p))⁻¹ ∧
    C.kernelMat p (C.negPoint uNeg vNeg) =
        LinkLevel.extendByOne vNeg (C.lowerEdge p) *
          LinkLevel.extendByOne uNeg (C.cornerEdge .neg p) *
            (LinkLevel.extendByOne vNeg (C.upperEdge p))⁻¹ ∧
    Matrices.ComplexMatrix2.fullTrace
        (C.transversalHolonomy p (C.doubledField uPos uNeg vPos vNeg)) =
        Matrices.ComplexMatrix2.fullTrace
          ((C.kernelMat p (C.posPoint uPos vPos) : Matrices.ComplexMatrix2) *
            ((C.kernelMat p (C.negPoint uNeg vNeg))⁻¹ :
              Matrices.ComplexMatrix2.specialUnitary)) ∧
    Matrices.ComplexMatrix2.fullTrace
        ((C.kernelMat p (C.posPoint uPos vPos) : Matrices.ComplexMatrix2) *
          ((C.kernelMat p (C.negPoint uNeg vNeg))⁻¹ :
            Matrices.ComplexMatrix2.specialUnitary)) =
      ∑ i : Fin 2, ∑ k : Fin 2,
        (C.kernelMat p (C.posPoint uPos vPos) : Matrices.ComplexMatrix2) i k *
          starRingEnd ℂ ((C.kernelMat p (C.negPoint uNeg vNeg) : Matrices.ComplexMatrix2) i k)
def KernelSumIdentity (C : LinkLevel D) : Prop :=
  (∀ γ : C.KernelLabel, Continuous (C.kernelFn γ) ∧ ∀ ω, ‖C.kernelFn γ ω‖ ≤ 1) ∧
  ∀ (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
    (vPos vNeg : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary),
    ((∑ᶠ p ∈ C.transversalFaces, (1 / 2 : ℝ) *
        (Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy
          (C.doubledField uPos uNeg vPos vNeg).1 p)).re : ℝ) : ℂ) =
      (1 / 4 : ℂ) * ∑ᶠ γ : C.KernelLabel,
        C.kernelFn γ (C.posPoint uPos vPos) *
          starRingEnd ℂ (C.kernelFn γ (C.negPoint uNeg vNeg))
def ExpSeries (C : LinkLevel D) : Prop :=
  (∀ (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
      (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
      (vPos vNeg : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary),
      ((Real.exp (-D.coupling * ∑ᶠ p ∈ C.transversalFaces, PeriodicLattice.plaquetteCost
          (C.doubledField uPos uNeg vPos vNeg).1 p) : ℝ) : ℂ) =
        ((Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)) : ℝ) : ℂ) *
          ∑' n : ℕ, C.seriesTerm n (C.posPoint uPos vPos) (C.negPoint uNeg vNeg)) ∧
  TendstoUniformly
    (fun (N : ℕ) (x : C.DoubledCoords) => ∑ n ∈ Finset.range N,
      C.seriesTerm n (C.posPoint x.1 x.2.2.1) (C.negPoint x.2.1 x.2.2.2))
    (fun x : C.DoubledCoords => ∑' n : ℕ,
      C.seriesTerm n (C.posPoint x.1 x.2.2.1) (C.negPoint x.2.1 x.2.2.2))
    atTop ∧
  (∀ (n : ℕ) (x : C.DoubledCoords),
    ‖C.seriesTerm n (C.posPoint x.1 x.2.2.1) (C.negPoint x.2.1 x.2.2.2)‖ ≤
      (D.coupling * (Nat.card C.KernelLabel : ℝ) / 4) ^ n / (n.factorial : ℝ)) ∧
  ∀ n : ℕ, 0 < C.seriesCoeff n
def DoubledActionProperties : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D),
    HalfActionFacts C ∧ TransversalTrace C ∧ KernelSumIdentity C ∧ ExpSeries C
end DoubledAction
end YangMills.Construction.ReflectionPositivity.CutoffMirrors
end
