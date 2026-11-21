import YangMills.Construction.EuclideanFunctionals.TensorsAndTensorComponentsOfTheFreeSpace
import YangMills.Construction.EuclideanSpectral.BorelFunctionOperator
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.EuclideanSpectral
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
section Properties
variable (S : ConnFamily)
def centeredAt (X : FnList) : ℝ := Ambient.evalOrZero (centeredFn S) X
def combSpan (n : ℕ) : Submodule ℂ FreeSep :=
  Submodule.span ℂ (toFree '' sepN n)
structure IsSymmMultilinReal : Prop where
  real : ∀ X : sepAll, (centeredFnFree S (toFree X.1)).im = 0
  symmetric : ∀ (n : ℕ) (f : Fin n → R4 → ℝ), List.ofFn f ∈ sepAll →
    ∀ π : Equiv.Perm (Fin n),
      centeredAt S (List.ofFn (f ∘ π)) = centeredAt S (List.ofFn f)
  linear : ∀ (n : ℕ) (f : Fin n → R4 → ℝ) (i : Fin n) (g : R4 → ℝ), g ≠ f i →
    List.ofFn f ∈ sepAll → List.ofFn (Function.update f i g) ∈ sepAll → ∀ a b : ℝ,
      centeredAt S (List.ofFn (Function.update f i (a • f i + b • g))) =
        a * centeredAt S (List.ofFn f) + b * centeredAt S (List.ofFn (Function.update f i g))
  tensors : ∀ n : ℕ, 1 ≤ n → ∀ F ∈ combSpan n, ∀ G ∈ combSpan n,
    tensorComp n F = tensorComp n G → centeredFnFree S F = centeredFnFree S G
def IsLatticeInvariant : Prop :=
  ∀ X ∈ sepAll,
    (∀ v : R4, centeredAt S ((EuclidMotion.transl v).actList X) = centeredAt S X) ∧
      ∀ w ∈ hyperoctahedral, centeredAt S X = centeredAt S (w.actList X)
def osForm (F G : FreeSep) : ℂ :=
  centeredFnFree S (freeMul (timeFlip.actFree (freeConj F)) G)
def IsOSPositive : Prop :=
  ∀ F ∈ freeSpanIn upperHalf,
    (osForm S F F).im = 0 ∧ 0 ≤ (osForm S F F).re
def HasClusterBounds (c : SharpScale) (C : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (R d : ℝ), 0 < R → 0 < d →
    ∀ (f : Fin n → R4 → ℝ) (hf : List.ofFn f ∈ sepN n),
      (∀ i, ∃ x, supp (f i) ⊆ TestFunctions.closedBallR4 x R) →
      (Pairwise fun i j =>
        ENNReal.ofReal d ≤ TestFunctions.setDistR4 (supp (f i)) (supp (f j))) →
      |S.fn n hn ⟨List.ofFn f, hf⟩| ≤ C n d R * ∏ i, c.sharpNorm (f i)
end Properties
abbrev MomSpace : Type := EuclideanSpace ℝ (Fin 4)
def energyCoord (p : MomSpace) : ℝ := p 0
def momCoord (j : Fin 3) (p : MomSpace) : ℝ := p j.succ
theorem measurable_energyCoord : Measurable energyCoord :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 4)).continuous.measurable
def negEnergySet : BorelSubset 4 :=
  ⟨{p | energyCoord p < 0}, measurableSet_lt measurable_energyCoord measurable_const⟩
def nonnegEnergySet : BorelSubset 4 :=
  ⟨{p | 0 ≤ energyCoord p}, measurableSet_le measurable_const measurable_energyCoord⟩
def spatialDot (v : R4) (p : MomSpace) : ℝ :=
  ∑ j : Fin 3, v j.castSucc * momCoord j p
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : ProjMeasure H 4)
def energyFn (p : MomSpace) : ℂ := energyCoord p
def hamiltonianOp : P.fnDomain energyFn →ₗ[ℂ] H :=
  P.borelFnOp energyFn
def momentumOp (j : Fin 3) : P.fnDomain (fun p => (momCoord j p : ℂ)) →ₗ[ℂ] H :=
  P.borelFnOp fun p => (momCoord j p : ℂ)
def semigroupOp (t : ℝ) : H →ₗ[ℂ] H :=
  P.boundedIntegralOn nonnegEnergySet fun p => (Real.exp (-t * energyCoord p) : ℂ)
def spatialShiftOp (v : R4) : H →ₗ[ℂ] H :=
  P.boundedIntegral fun p => Complex.exp (Complex.I * (spatialDot v p : ℂ))
end Operators
section System
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def classOrZero (cl : freeSpanIn upperHalf →ₗ[ℂ] H) (F : FreeSep) : H :=
  open Classical in if h : F ∈ freeSpanIn upperHalf then cl ⟨F, h⟩ else 0
theorem classOrZero_of_mem (cl : freeSpanIn upperHalf →ₗ[ℂ] H) {F : FreeSep}
    (h : F ∈ freeSpanIn upperHalf) : classOrZero cl F = cl ⟨F, h⟩ := by
  simp [classOrZero, h]
def emptyElt : freeSpanIn upperHalf :=
  ⟨toFree [], Submodule.subset_span
    ⟨[], Ambient.nil_mem_separatedWithin defaultMirrorData Ambient.euclidean upperHalf, rfl⟩⟩
variable (H) in
structure OSData [CompleteSpace H] (S : ConnFamily) where
  cls : freeSpanIn upperHalf →ₗ[ℂ] H
  inner_cls : ∀ F G : freeSpanIn upperHalf,
    inner ℂ (cls F) (cls G) = osForm S F.1 G.1
  denseRange_cls : DenseRange cls
  pvm : ProjMeasure H 4
  pvm_negEnergy : pvm negEnergySet = 0
  hamiltonian_vac : ∃ h : cls emptyElt ∈ pvm.fnDomain energyFn,
    hamiltonianOp pvm ⟨cls emptyElt, h⟩ = 0
  semigroup_cls : ∀ t : ℝ, 0 ≤ t → ∀ F : freeSpanIn upperHalf,
    semigroupOp pvm t (cls F) =
      classOrZero cls ((EuclidMotion.transl (t • timeVec)).actFree F.1)
  shift_cls : ∀ v ∈ spatialVecs, ∀ F : freeSpanIn upperHalf,
    spatialShiftOp pvm v (cls F) =
      classOrZero cls ((EuclidMotion.transl v).actFree F.1)
  rotOp : timeStabilizer → H →ₗ[ℂ] H
  rotOp_unitary : ∀ w, IsUnitaryMap (rotOp w)
  rotOp_cls : ∀ (w : timeStabilizer) (F : freeSpanIn upperHalf),
    rotOp w (cls F) = classOrZero cls ((w : EuclidMotion).actFree F.1)
  rotOp_comm_semigroup : ∀ (w : timeStabilizer) (t : ℝ), 0 ≤ t →
    rotOp w ∘ₗ semigroupOp pvm t =
      semigroupOp pvm t ∘ₗ rotOp w
  rotOp_conj_shift : ∀ (w : timeStabilizer), ∀ v ∈ spatialVecs,
    rotOp w ∘ₗ spatialShiftOp pvm v ∘ₗ
        (rotOp_unitary w).inv =
      spatialShiftOp pvm ((w : EuclidMotion) v)
def OSData.vac [CompleteSpace H] {S : ConnFamily} (sys : OSData H S) : H :=
  sys.cls emptyElt
end System
structure SymmEuclidFunctional (c : SharpScale) (S : ConnFamily) where
  isSymmMultilinReal : IsSymmMultilinReal S
  isLatticeInvariant : IsLatticeInvariant S
  isOSPositive : IsOSPositive S
  clusterConst : ℕ → ℝ → ℝ → ℝ
  hasClusterBounds : HasClusterBounds S c clusterConst
  space : Type
  [instNormed : NormedAddCommGroup space]
  [instInner : InnerProductSpace ℂ space]
  [instComplete : CompleteSpace space]
  osData : OSData space S
attribute [instance] SymmEuclidFunctional.instNormed
  SymmEuclidFunctional.instInner SymmEuclidFunctional.instComplete
end YangMills.Construction.EuclideanFunctionals
