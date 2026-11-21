import YangMills.Construction.Lattice.ParallelBondsAndSidesOfAPlaquette
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace ReflectionPositivity.CutoffMirrors
namespace MirrorData
variable (D : MirrorData)
instance : Nonempty D.FieldSpace :=
  ⟨⟨fun _ => 1, fun _ _ => one_mem ComplexMatrix2.specialUnitary, fun _ _ => by simp⟩⟩
def fieldExpectation (Υ : D.FieldSpace → ℂ) : ℂ :=
  open Classical in
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling fun U =>
    if h : U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) then Υ ⟨U, h⟩ else 0
end MirrorData
namespace LinkLevel
variable {D : MirrorData} (C : LinkLevel D)
def halfCoords (σ : SlabSide) (U : D.FieldSpace) :
    C.halfEdges σ → ComplexMatrix2.specialUnitary :=
  D.linkValues (C.halfEdges σ) U
def transversalCoords (U : D.FieldSpace) :
    C.transversalEdges → ComplexMatrix2.specialUnitary :=
  fun b => ⟨U.1 (C.orientedAcross b.1), U.2.1 _ (mem_univ _)⟩
def halfHaar (σ : SlabSide) : Measure (C.halfEdges σ → ComplexMatrix2.specialUnitary) :=
  ComplexMatrix2.haarPi (C.halfEdges σ)
def transversalHaar : Measure (C.transversalEdges → ComplexMatrix2.specialUnitary) :=
  ComplexMatrix2.haarPi C.transversalEdges
def HasCoords (U : D.FieldSpace) (uPos : C.halfEdges .pos → ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → ComplexMatrix2.specialUnitary)
    (v : C.transversalEdges → ComplexMatrix2.specialUnitary) : Prop :=
  C.halfCoords .pos U = uPos ∧ C.halfCoords .neg U = uNeg ∧ C.transversalCoords U = v
def fieldOfCoords (uPos : C.halfEdges .pos → ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → ComplexMatrix2.specialUnitary)
    (v : C.transversalEdges → ComplexMatrix2.specialUnitary) : D.FieldSpace :=
  Classical.epsilon fun U => C.HasCoords U uPos uNeg v
def evalCoords {E : Type*} (Υ : D.FieldSpace → E)
    (uPos : C.halfEdges .pos → ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → ComplexMatrix2.specialUnitary)
    (v : C.transversalEdges → ComplexMatrix2.specialUnitary) : E :=
  Υ (C.fieldOfCoords uPos uNeg v)
def halfFunction (σ : SlabSide) (F : D.FieldSpace → ℂ) :
    (C.halfEdges σ → ComplexMatrix2.specialUnitary) → ℂ :=
  Classical.epsilon fun Φ => ∀ U, F U = Φ (C.halfCoords σ U)
theorem halfFunction_spec {σ : SlabSide} {F : D.FieldSpace → ℂ} (hF : F ∈ C.halfAlgebra σ)
    (U : D.FieldSpace) : F U = C.halfFunction σ F (C.halfCoords σ U) := by
  obtain ⟨Φ, -, -, rfl⟩ := hF
  have h : ∃ Ψ : (C.halfEdges σ → ComplexMatrix2.specialUnitary) → ℂ,
      ∀ U, Φ (D.linkValues (C.halfEdges σ) U) = Ψ (C.halfCoords σ U) := ⟨Φ, fun _ => rfl⟩
  exact Classical.epsilon_spec h U
def extendByOne {S : Set D.Edge} (g : S → ComplexMatrix2.specialUnitary) (b : D.Edge) :
    ComplexMatrix2.specialUnitary :=
  open Classical in
  if h : b ∈ S then g ⟨b, h⟩ else 1
def transfer (u' : C.halfEdges .neg → ComplexMatrix2.specialUnitary) :
    C.halfEdges .pos → ComplexMatrix2.specialUnitary :=
  open Classical in
  fun b => if b.1.IsParallelToAxis D.dir then (extendByOne u' (C.positiveReflectedEdge b.1))⁻¹
    else extendByOne u' (C.positiveReflectedEdge b.1)
def transversalQuot (vPos vNeg : C.transversalEdges → ComplexMatrix2.specialUnitary) :
    C.transversalEdges → ComplexMatrix2.specialUnitary :=
  fun b => (vNeg b)⁻¹ * vPos b
abbrev DoubleSpace : Type :=
  (C.halfEdges .pos → ComplexMatrix2.specialUnitary) ×
    (C.transversalEdges → ComplexMatrix2.specialUnitary)
def doubleHaar : Measure C.DoubleSpace := (C.halfHaar .pos).prod C.transversalHaar
def posPoint (uPos : C.halfEdges .pos → ComplexMatrix2.specialUnitary)
    (vPos : C.transversalEdges → ComplexMatrix2.specialUnitary) : C.DoubleSpace :=
  (uPos, vPos)
def negPoint (uNeg : C.halfEdges .neg → ComplexMatrix2.specialUnitary)
    (vNeg : C.transversalEdges → ComplexMatrix2.specialUnitary) : C.DoubleSpace :=
  (C.transfer uNeg, vNeg)
def faceEnergyOfHalf (p : D.Face) (u : C.halfEdges .pos → ComplexMatrix2.specialUnitary) : ℝ :=
  Classical.epsilon fun r =>
    ∀ U : D.FieldSpace, C.halfCoords .pos U = u → PeriodicLattice.plaquetteCost U.1 p = r
def halfAction (u : C.halfEdges .pos → ComplexMatrix2.specialUnitary) : ℝ :=
  ∑ᶠ p ∈ C.halfFaces .pos, C.faceEnergyOfHalf p u
def cornerEdge (σ : SlabSide) (p : D.Face) : D.Edge :=
  open Classical in
  if h : ∃ b : D.Edge, b.source = C.lowerCorner σ p ∧ b.target = C.upperCorner σ p then
    h.choose
  else C.lowerEdge p
def kernelMat (p : D.Face) (ω : C.DoubleSpace) : ComplexMatrix2.specialUnitary :=
  extendByOne ω.2 (C.lowerEdge p) * extendByOne ω.1 (C.cornerEdge .pos p) *
    (extendByOne ω.2 (C.upperEdge p))⁻¹
abbrev KernelLabel : Type := C.transversalFaces × (Fin 2 × Fin 2) × Fin 2
def kernelFn (γ : C.KernelLabel) (ω : C.DoubleSpace) : ℂ :=
  if γ.2.2 = 0 then (C.kernelMat γ.1.1 ω : ComplexMatrix2) γ.2.1.1 γ.2.1.2
  else starRingEnd ℂ ((C.kernelMat γ.1.1 ω : ComplexMatrix2) γ.2.1.1 γ.2.1.2)
def kernelProd {n : ℕ} (γ : Fin n → C.KernelLabel) (ω : C.DoubleSpace) : ℂ :=
  ∏ j, C.kernelFn (γ j) ω
abbrev KernelWord : Type := Σ n : ℕ, Fin n → C.KernelLabel
def transferFunctional {n : ℕ} (γ : Fin n → C.KernelLabel) (F : D.FieldSpace → ℂ) : ℂ :=
  ∫ ω : C.DoubleSpace,
    C.halfFunction .pos F ω.1 * (Real.exp (-D.coupling * C.halfAction ω.1) : ℂ) *
      C.kernelProd γ ω ∂C.doubleHaar
def seriesWeight {n : ℕ} (_γ : Fin n → C.KernelLabel) : ℝ :=
  (PeriodicLattice.partitionFunction D.L D.m D.K D.coupling)⁻¹ *
    Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)) *
      ((D.coupling / 4) ^ n / (n.factorial : ℝ))
theorem reflectedEdge_opposite (b : D.Edge) :
    C.reflectedEdge b.opposite = (C.reflectedEdge b).opposite := by
  classical
  have hopp : ∀ {b₁ b₂ : D.Edge}, C.IsReflectedEdge b₁ b₂ →
      C.IsReflectedEdge b₁.opposite b₂.opposite := fun h => ⟨h.2, h.1⟩
  have huniq : ∀ {b₁ b₂ b₃ : D.Edge}, C.IsReflectedEdge b₁ b₂ → C.IsReflectedEdge b₁ b₃ →
      b₂ = b₃ := fun h h' =>
    PeriodicLattice.Bond.ext (Subtype.ext (h.1.trans h'.1.symm)) (Subtype.ext (h.2.trans h'.2.symm))
  by_cases h : ∃ b', C.IsReflectedEdge b b'
  · have h' : ∃ b', C.IsReflectedEdge b.opposite b' := ⟨h.choose.opposite, hopp h.choose_spec⟩
    have e₁ : C.reflectedEdge b = h.choose := dif_pos h
    have e₂ : C.reflectedEdge b.opposite = h'.choose := dif_pos h'
    rw [e₁, e₂]
    exact huniq h'.choose_spec (hopp h.choose_spec)
  · have h' : ¬∃ b', C.IsReflectedEdge b.opposite b' := by
      rintro ⟨b', hb⟩
      exact h ⟨b'.opposite, hopp hb⟩
    have e₁ : C.reflectedEdge b = b := dif_neg h
    have e₂ : C.reflectedEdge b.opposite = b.opposite := dif_neg h'
    rw [e₁, e₂]
def reflectField (U : D.FieldSpace) : D.FieldSpace :=
  ⟨fun b => U.1 (C.reflectedEdge b), fun _ _ => U.2.1 _ (mem_univ _), fun b _ => by
    change U.1 (C.reflectedEdge b.opposite) = (U.1 (C.reflectedEdge b))⁻¹
    rw [C.reflectedEdge_opposite]
    exact U.2.2 _ (mem_univ _)⟩
theorem reflectField_val (s : D.Symmetry) (hs : s.toFun = C.refl) (U : D.FieldSpace) :
    (C.reflectField U).1 = MirrorData.Symmetry.pullback s U.1 := by
  funext b
  change U.1 (C.reflectedEdge b) = _
  rw [← C.bondMap_eq_reflectedEdge s hs b]
  rfl
def thetaForm (F F' : D.FieldSpace → ℂ) : ℂ :=
  D.fieldExpectation fun U =>
    starRingEnd ℂ (F (C.reflectField U)) * F' U
end LinkLevel
end ReflectionPositivity.CutoffMirrors
end YangMills.Construction
end
