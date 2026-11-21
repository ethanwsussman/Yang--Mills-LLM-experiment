import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevel
import YangMills.Construction.Towers.ExpansionOfTheIterateInTheLeftChart
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace AsDifferentials
open YangMills.Construction.Matrices
section Generalities
variable {β γ δ : Type}
def boundedSubmodule (P : Submodule ℂ (β → ComplexMatrix2)) : Submodule ℂ (β → ComplexMatrix2) where
  carrier := {B | B ∈ P ∧ ∃ C : ℝ, ∀ b, ComplexMatrix2.operatorNorm (B b) ≤ C}
  add_mem' := by
    rintro B B' ⟨hB, C, hC⟩ ⟨hB', C', hC'⟩
    refine ⟨P.add_mem hB hB', C + C', fun b => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hC b) (hC' b))
  zero_mem' := ⟨P.zero_mem, 0, fun b => by simp [ComplexMatrix2.operatorNorm]⟩
  smul_mem' := by
    rintro z B ⟨hB, C, hC⟩
    refine ⟨P.smul_mem z hB, ‖z‖ * C, fun b => ?_⟩
    exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hC b) (norm_nonneg z))
def IsLocallyHolomorphicLog (Positive : β → Prop) (P : Submodule ℂ (β → ComplexMatrix2))
    (Defined : (β → ComplexMatrix2) → Prop) (a v : (β → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∃ (F : Finset β) (O : Set (F → ComplexMatrix2)) (h : (F → ComplexMatrix2) → ComplexMatrix2),
    F.Nonempty ∧ (∀ b ∈ F, Positive b) ∧ 0 ∈ O ∧
    (∀ e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      GroupLieProduct.IsHolomorphicOnTraceless e Coordinates.ComplexCoordinates.matrixEquiv O h) ∧
    MapsTo h O ComplexMatrix2.traceless ∧
    ∀ C ∈ P, (fun b : F => C b) ∈ O →
      Defined C ∧ ComplexMatrix2.operatorNorm (a C - 1) < 1 ∧ v C = h fun b : F => C b
def HasDerivAtZeroAlong (v : (β → ComplexMatrix2) → ComplexMatrix2) (B : β → ComplexMatrix2)
    (D : ComplexMatrix2) : Prop :=
  HasDerivAt (fun t : ℂ => v (t • B)) D 0
def IsLinearOn (P : Submodule ℂ (β → ComplexMatrix2))
    (f : (β → ComplexMatrix2) → δ → ComplexMatrix2) : Prop :=
  ∀ B ∈ P, ∀ B' ∈ P, ∀ z : ℂ, f (B + B') = f B + f B' ∧ f (z • B) = z • f B
abbrev BoundedBilinear (P : Submodule ℂ (β → ComplexMatrix2)) (γ : Type) : Type :=
  boundedSubmodule P →ₗ[ℂ] boundedSubmodule P →ₗ[ℂ] γ → ComplexMatrix2
def IsQuadraticExpansion (P : Submodule ℂ (β → ComplexMatrix2))
    (v : γ → (β → ComplexMatrix2) → ComplexMatrix2)
    (Q : (β → ComplexMatrix2) → γ → ComplexMatrix2) (q : BoundedBilinear P γ) : Prop :=
  (∀ B B' : boundedSubmodule P, q B B' = q B' B) ∧
    ∀ c : γ, ∃ K ε : ℝ, 0 < ε ∧ ∀ B : boundedSubmodule P,
      GroupLieProduct.supNorm (B : β → ComplexMatrix2) < ε →
        ComplexMatrix2.operatorNorm (v c B - Q B c - (1 / 2 : ℂ) • q B B c) ≤
          K * GroupLieProduct.supNorm (B : β → ComplexMatrix2) ^ 3
def quadraticTerm (P : Submodule ℂ (β → ComplexMatrix2))
    (v : γ → (β → ComplexMatrix2) → ComplexMatrix2)
    (Q : (β → ComplexMatrix2) → γ → ComplexMatrix2) : BoundedBilinear P γ :=
  Classical.epsilon (IsQuadraticExpansion P v Q)
def quadraticTermAt (P : Submodule ℂ (β → ComplexMatrix2))
    (v : γ → (β → ComplexMatrix2) → ComplexMatrix2)
    (Q : (β → ComplexMatrix2) → γ → ComplexMatrix2) (B B' : β → ComplexMatrix2) :
    γ → ComplexMatrix2 :=
  open Classical in
  if h : B ∈ boundedSubmodule P ∧ B' ∈ boundedSubmodule P then
    quadraticTerm P v Q ⟨B, h.1⟩ ⟨B', h.2⟩
  else 0
def HasUniqueQuadraticTerm (P : Submodule ℂ (β → ComplexMatrix2))
    (v : γ → (β → ComplexMatrix2) → ComplexMatrix2)
    (Q : (β → ComplexMatrix2) → γ → ComplexMatrix2) : Prop :=
  (∃! q : BoundedBilinear P γ, IsQuadraticExpansion P v Q q) ∧
    IsQuadraticExpansion P v Q (quadraticTerm P v Q) ∧
    ∀ (B B' : boundedSubmodule P) (c : γ),
      mixedDirectionalDeriv ℂ (v c) (B : β → ComplexMatrix2) (B' : β → ComplexMatrix2) =
        quadraticTerm P v Q B B' c ∧
      quadraticTerm P v Q B B' c ∈ ComplexMatrix2.traceless
end Generalities
section PeriodicSide
variable {L m k : ℕ}
open LevelwiseMeans (levelwiseMean valuesOrOne)
def iterMean (W : Edge L m k 0 → ComplexMatrix2) (i : ℕ) (c : Edge L m k i) : ComplexMatrix2 :=
  valuesOrOne (levelwiseMean W i) c
def iterRatio (U : Edge L m k 0 → ComplexMatrix2) (j : ℕ) (c : Edge L m k j)
    (C : Edge L m k 0 → ComplexMatrix2) : ComplexMatrix2 :=
  iterMean (PeriodicLattice.expTwist C U) j c * (iterMean U j c)⁻¹
def iterLogRatio (U : Edge L m k 0 → ComplexMatrix2) (j : ℕ) (c : Edge L m k j)
    (C : Edge L m k 0 → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (iterRatio U j c C)
def meanRatio {j : ℕ} (V : Edge L m k j → ComplexMatrix2) (c : Edge L m k (j + 1))
    (C : Edge L m k j → ComplexMatrix2) : ComplexMatrix2 :=
  PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist C V) c *
    (PeriodicLattice.complexBlockAverage V c)⁻¹
def meanLogRatio {j : ℕ} (V : Edge L m k j → ComplexMatrix2) (c : Edge L m k (j + 1))
    (C : Edge L m k j → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (meanRatio V c C)
def contourRatio {j : ℕ} (V : Edge L m k j → ComplexMatrix2) (y : Vertex L m k (j + 1))
    (x : Vertex L m k j) (C : Edge L m k j → ComplexMatrix2) : ComplexMatrix2 :=
  PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist C V) y x *
    (PeriodicLattice.complexMeanContourHolonomy V y x)⁻¹
def contourLogRatio {j : ℕ} (V : Edge L m k j → ComplexMatrix2) (y : Vertex L m k (j + 1))
    (x : Vertex L m k j) (C : Edge L m k j → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (contourRatio V y x C)
def ContourDefined {j : ℕ} (y : Vertex L m k (j + 1)) (V' : Edge L m k j → ComplexMatrix2) : Prop :=
  ∃ c : Edge L m k (j + 1), c.IsPositivelyOriented ∧
    y ∈ ({c.source, c.target} : Set (Vertex L m k (j + 1))) ∧
    V' ∈ nearIdentityPolydisc (polydiscRadius L) c
def topLogRatio (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) (c : PositiveEdge L m k k)
    (C : Edge L m k 0 → ComplexMatrix2) : ComplexMatrix2 :=
  iterLogRatio U k c.1 C
def topDeriv (L m k : ℕ) (U B : Edge L m k 0 → ComplexMatrix2) (c : PositiveEdge L m k k) :
    ComplexMatrix2 :=
  complexIterDeriv L m k k U B c.1
def complexQuadraticTerm (L m k : ℕ) (U B B' : Edge L m k 0 → ComplexMatrix2) :
    PositiveEdge L m k k → ComplexMatrix2 :=
  quadraticTermAt (complexEdgeForms L m k 0) (topLogRatio L m k U) (topDeriv L m k U) B B'
structure StepConditions (j : ℕ) (V : Edge L m k j → ComplexMatrix2) (U : Edge L m k 0 → ComplexMatrix2) :
    Prop where
  local_iter : ∀ c : Edge L m k (j + 1), c.IsPositivelyOriented →
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L m k 0)
      (fun C => LevelwiseMeans.IsDefinedAt (PeriodicLattice.expTwist C U) (j + 1) c)
      (iterRatio U (j + 1) c) (iterLogRatio U (j + 1) c)
  local_mean : ∀ c : Edge L m k (j + 1), c.IsPositivelyOriented →
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L m k j)
      (fun C => PeriodicLattice.expTwist C V ∈ nearIdentityPolydisc (polydiscRadius L) c)
      (meanRatio V c) (meanLogRatio V c)
  local_contour : ∀ (y : Vertex L m k (j + 1)),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms L m k j)
        (fun C => ContourDefined y (PeriodicLattice.expTwist C V))
        (contourRatio V y x) (contourLogRatio V y x)
  deriv_iter : ∀ c : Edge L m k (j + 1), c.IsPositivelyOriented → ∀ B ∈ complexEdgeForms L m k 0,
    HasDerivAtZeroAlong (iterLogRatio U (j + 1) c) B (complexIterDeriv L m k (j + 1) U B c)
  deriv_mean : ∀ c : Edge L m k (j + 1), c.IsPositivelyOriented → ∀ B ∈ complexEdgeForms L m k j,
    HasDerivAtZeroAlong (meanLogRatio V c) B (complexSmoothingDeriv V B c)
  deriv_contour : ∀ (y : Vertex L m k (j + 1)),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      ∀ B ∈ complexEdgeForms L m k j,
        HasDerivAtZeroAlong (contourLogRatio V y x) B
          (logDirectionalDeriv ℂ
            (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
            (PeriodicLattice.complexMeanContourHolonomy V y x) B)
  linear_iter : IsLinearOn (complexEdgeForms L m k 0) (complexIterDeriv L m k (j + 1) U)
  linear_mean : IsLinearOn (complexEdgeForms L m k j) (complexSmoothingDeriv V)
  linear_contour : IsLinearOn (complexEdgeForms L m k j) (contourLogDrift V)
  mem_iter : ∀ c : Edge L m k (j + 1), c.IsPositivelyOriented → ∀ B ∈ complexEdgeForms L m k 0,
    complexIterDeriv L m k (j + 1) U B c ∈ ComplexMatrix2.traceless
  mem_mean : ∀ c : Edge L m k (j + 1), c.IsPositivelyOriented → ∀ B ∈ complexEdgeForms L m k j,
    complexSmoothingDeriv V B c ∈ ComplexMatrix2.traceless
  mem_contour : ∀ y : Vertex L m k (j + 1), ∀ B ∈ complexEdgeForms L m k j,
    contourLogDrift V B y ∈ ComplexMatrix2.traceless
def SideRequirements (L m k : ℕ) : Prop :=
  (∀ j < k, ∀ V ∈ smallComplexFields L m k j, ∀ U ∈ smallIterateFields L m k,
    StepConditions j V U) ∧
  (∀ U ∈ smallIterateFields L m k,
    HasUniqueQuadraticTerm (complexEdgeForms L m k 0) (topLogRatio L m k U) (topDeriv L m k U)) ∧
  EventuallyNearIdentity (fieldSpace L m k 0) fun U => U ∈ smallIterateFields L m k ∧
    ∀ B B' : edgeFormSpace L m k 0, complexQuadraticTerm L m k U B B' = iterQuadraticTerm U B B'
end PeriodicSide
end AsDifferentials
namespace FullSpace
namespace AsDifferentials
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.AsDifferentials
open YangMills.Construction.Tower.LevelwiseMeans (valuesOrOne)
open YangMills.Construction.Tower.LevelwiseMeans.Unbounded (levelwiseMean)
section UnboundedSide
variable {L k : ℕ}
def iterMean (W : Edge L k 0 → ComplexMatrix2) (i : ℕ) (c : Edge L k i) : ComplexMatrix2 :=
  valuesOrOne (levelwiseMean W i) c
def iterRatio (U : Edge L k 0 → ComplexMatrix2) (j : ℕ) (c : Edge L k j)
    (C : Edge L k 0 → ComplexMatrix2) : ComplexMatrix2 :=
  iterMean (expTwist C U) j c * (iterMean U j c)⁻¹
def iterLogRatio (U : Edge L k 0 → ComplexMatrix2) (j : ℕ) (c : Edge L k j)
    (C : Edge L k 0 → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (iterRatio U j c C)
def meanRatio {j : ℕ} (V : Edge L k j → ComplexMatrix2) (c : Edge L k (j + 1))
    (C : Edge L k j → ComplexMatrix2) : ComplexMatrix2 :=
  complexSmoothing L (expTwist C V) c * (complexSmoothing L V c)⁻¹
def meanLogRatio {j : ℕ} (V : Edge L k j → ComplexMatrix2) (c : Edge L k (j + 1))
    (C : Edge L k j → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (meanRatio V c C)
def contourRatio {j : ℕ} (V : Edge L k j → ComplexMatrix2) (y : Vertex L k (j + 1))
    (x : Vertex L k j) (C : Edge L k j → ComplexMatrix2) : ComplexMatrix2 :=
  complexContourMean L (expTwist C V) y x * (complexContourMean L V y x)⁻¹
def contourLogRatio {j : ℕ} (V : Edge L k j → ComplexMatrix2) (y : Vertex L k (j + 1))
    (x : Vertex L k j) (C : Edge L k j → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (contourRatio V y x C)
def ContourDefined {j : ℕ} (y : Vertex L k (j + 1)) (V' : Edge L k j → ComplexMatrix2) : Prop :=
  ∃ c : Edge L k (j + 1), c.IsPositivelyOriented ∧
    y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))) ∧
    V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c
def topLogRatio (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2)
    (c : PositiveEdge (meshAt L k k)) (C : Edge L k 0 → ComplexMatrix2) : ComplexMatrix2 :=
  iterLogRatio U k c.1 C
def topDeriv (L k : ℕ) (U B : Edge L k 0 → ComplexMatrix2)
    (c : PositiveEdge (meshAt L k k)) : ComplexMatrix2 :=
  complexIterDeriv L k k U B c.1
def complexQuadraticTerm (L k : ℕ) (U B B' : Edge L k 0 → ComplexMatrix2) :
    PositiveEdge (meshAt L k k) → ComplexMatrix2 :=
  quadraticTermAt (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U) (topDeriv L k U) B B'
structure StepConditions (j : ℕ) (V : Edge L k j → ComplexMatrix2) (U : Edge L k 0 → ComplexMatrix2) :
    Prop where
  local_iter : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms (meshAt L k 0))
      (fun C => LevelwiseMeans.Unbounded.IsDefinedAt (expTwist C U) (j + 1) c)
      (iterRatio U (j + 1) c) (iterLogRatio U (j + 1) c)
  local_mean : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms (meshAt L k j))
      (fun C => expTwist C V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
      (meanRatio V c) (meanLogRatio V c)
  local_contour : ∀ (y : Vertex L k (j + 1)), ∀ x ∈ cubeVertices L (meshAt L k j) y,
    IsLocallyHolomorphicLog (fun b => b.IsPositivelyOriented) (complexEdgeForms (meshAt L k j))
      (fun C => ContourDefined y (expTwist C V))
      (contourRatio V y x) (contourLogRatio V y x)
  deriv_iter : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ B ∈ complexEdgeForms (meshAt L k 0),
      HasDerivAtZeroAlong (iterLogRatio U (j + 1) c) B (complexIterDeriv L k (j + 1) U B c)
  deriv_mean : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ B ∈ complexEdgeForms (meshAt L k j),
      HasDerivAtZeroAlong (meanLogRatio V c) B (complexSmoothingDeriv V B c)
  deriv_contour : ∀ (y : Vertex L k (j + 1)),
    ∀ x ∈ cubeVertices L (meshAt L k j) y, ∀ B ∈ complexEdgeForms (meshAt L k j),
      HasDerivAtZeroAlong (contourLogRatio V y x) B
        (logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
          (complexContourMean L V y x) B)
  linear_iter : IsLinearOn (complexEdgeForms (meshAt L k 0)) (complexIterDeriv L k (j + 1) U)
  linear_mean : IsLinearOn (complexEdgeForms (meshAt L k j)) (complexSmoothingDeriv V)
  linear_contour : IsLinearOn (complexEdgeForms (meshAt L k j)) (contourLogDrift V)
  mem_iter : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ B ∈ complexEdgeForms (meshAt L k 0),
      complexIterDeriv L k (j + 1) U B c ∈ ComplexMatrix2.traceless
  mem_mean : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ B ∈ complexEdgeForms (meshAt L k j), complexSmoothingDeriv V B c ∈ ComplexMatrix2.traceless
  mem_contour : ∀ y : Vertex L k (j + 1), ∀ B ∈ complexEdgeForms (meshAt L k j),
    contourLogDrift V B y ∈ ComplexMatrix2.traceless
def Requirements (L k : ℕ) : Prop :=
  (∀ j < k, ∀ V ∈ smallComplexFields L k j, ∀ U ∈ smallIterateFields L k,
    StepConditions j V U) ∧
  ∀ U ∈ smallIterateFields L k,
    HasUniqueQuadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U) (topDeriv L k U)
end UnboundedSide
end AsDifferentials
end FullSpace
namespace AsDifferentials
def CovariantMeansAreDerivatives : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ m : ℕ, 0 < m → SideRequirements L m k) ∧ FullSpace.AsDifferentials.Requirements L k
end AsDifferentials
end Tower
end YangMills.Construction
end
