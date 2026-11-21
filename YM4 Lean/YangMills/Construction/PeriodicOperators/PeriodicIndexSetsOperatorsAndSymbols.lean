import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
def castVec (n : Fin 4 → ℤ) : AmbientSpace := fun μ => (n μ : ℝ)
def toComplexVec (y : AmbientSpace) : Fin 4 → ℂ := fun μ => (y μ : ℂ)
def bilinDot (κ y : Fin 4 → ℂ) : ℂ := ∑ μ, κ μ * y μ
structure PeriodicData where
  Carrier : Type
  translate : (Fin 4 → ℤ) → Carrier → Carrier
  pos : Carrier → AmbientSpace
  Component : Type
  componentOf : Carrier → Component
  weight : Component → ℝ
namespace PeriodicData
variable (I : PeriodicData)
def weightOf (ι : I.Carrier) : ℝ := I.weight (I.componentOf ι)
def QuotMod (s : ℕ) : Type :=
  Quot fun ι ι' : I.Carrier => ∃ n : Fin 4 → ℤ, ι' = I.translate (s • n) ι
abbrev UnitQuot : Type := I.QuotMod 1
def mkQuot (s : ℕ) (ι : I.Carrier) : I.QuotMod s := Quot.mk _ ι
def quotWeight (s : ℕ) (c : I.QuotMod s) : ℝ :=
  Classical.epsilon fun w => ∀ ι, I.mkQuot s ι = c → I.weightOf ι = w
def ofSingle (Carrier : Type) (translate : (Fin 4 → ℤ) → Carrier → Carrier)
    (pos : Carrier → AmbientSpace) (w : ℝ) : PeriodicData where
  Carrier := Carrier
  translate := translate
  pos := pos
  Component := Unit
  componentOf := fun _ => ()
  weight := fun _ => w
def sigma {P : Type} (J : P → PeriodicData) : PeriodicData where
  Carrier := Σ p, (J p).Carrier
  translate := fun n ι => ⟨ι.1, (J ι.1).translate n ι.2⟩
  pos := fun ι => (J ι.1).pos ι.2
  Component := Σ p, (J p).Component
  componentOf := fun ι => ⟨ι.1, (J ι.1).componentOf ι.2⟩
  weight := fun q => (J q.1).weight q.2
end PeriodicData
structure IsPeriodic (I : PeriodicData) : Prop where
  translate_zero : ∀ ι, I.translate 0 ι = ι
  translate_add : ∀ m n ι, I.translate (m + n) ι = I.translate n (I.translate m ι)
  free : ∀ n ι, I.translate n ι = ι → n = 0
  finite_quot : Finite I.UnitQuot
  pos_translate : ∀ n ι, I.pos (I.translate n ι) = I.pos ι + castVec n
  finite_components : Finite I.Component
  componentOf_translate : ∀ n ι, I.componentOf (I.translate n ι) = I.componentOf ι
  weight_pos : ∀ p, 0 < I.weight p
theorem IsPeriodic.sigma {P : Type} [Finite P] {J : P → PeriodicData}
    (h : ∀ p, IsPeriodic (J p)) : IsPeriodic (PeriodicData.sigma J) where
  translate_zero := fun ι => by
    cases ι with
    | mk p i => simp only [PeriodicData.sigma]; rw [(h p).translate_zero]
  translate_add := fun m n ι => by
    cases ι with
    | mk p i => simp only [PeriodicData.sigma]; rw [(h p).translate_add]
  free := fun n ι e => by
    cases ι with
    | mk p i =>
      simp only [PeriodicData.sigma, Sigma.mk.injEq, heq_eq_eq, true_and] at e
      exact (h p).free n i e
  finite_quot := by
    have : ∀ p, Finite (J p).UnitQuot := fun p => (h p).finite_quot
    let f : (Σ p, (J p).UnitQuot) → (PeriodicData.sigma J).UnitQuot := fun c =>
      Quot.lift (fun i => (PeriodicData.sigma J).mkQuot 1 ⟨c.1, i⟩)
        (by
          rintro i _ ⟨n, rfl⟩
          exact Quot.sound ⟨n, rfl⟩) c.2
    refine Finite.of_surjective f fun c => ?_
    induction c using Quot.ind with
    | mk ι => exact ⟨⟨ι.1, (J ι.1).mkQuot 1 ι.2⟩, rfl⟩
  pos_translate := fun n ι => by
    cases ι with
    | mk p i => exact (h p).pos_translate n i
  finite_components := by
    have : ∀ p, Finite (J p).Component := fun p => (h p).finite_components
    exact inferInstanceAs (Finite (Σ p, (J p).Component))
  componentOf_translate := fun n ι => by
    cases ι with
    | mk p i => simp only [PeriodicData.sigma]; rw [(h p).componentOf_translate]
  weight_pos := fun q => (h q.1).weight_pos q.2
section Tower
open YangMills.Construction.Tower
def intShift (n : Fin 4 → ℤ) : AmbientSpace → AmbientSpace := fun y => y + castVec n
abbrev PosEdge (L k j : ℕ) : Type :=
  {b : FullSpace.Edge L k j // b.IsPositivelyOriented}
instance posEdge_nonempty (L k j : ℕ) : Nonempty (PosEdge L k j) :=
  ⟨⟨InfiniteLattice.Link.forwardFrom 0 0, 0, by simp [InfiniteLattice.Link.forwardFrom]⟩⟩
def shiftEdge {L k j : ℕ} (n : Fin 4 → ℤ) (b : PosEdge L k j) : PosEdge L k j :=
  Classical.epsilon fun b' => b'.1 = FullSpace.edgeImage (intShift n) b.1
def shiftFace {L k j : ℕ} (n : Fin 4 → ℤ) (p : FullSpace.Face L k j) :
    FullSpace.Face L k j :=
  ⟨FullSpace.vertexImage (intShift n) p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def colourVertices (L k j : ℕ) : PeriodicData :=
  PeriodicData.ofSingle (Fin 3 × FullSpace.Vertex L k j)
    (fun n ι => (ι.1, FullSpace.vertexImage (intShift n) ι.2)) (fun ι => ι.2)
    (meshAt L k j ^ 4)
def colourEdges (L k j : ℕ) : PeriodicData :=
  PeriodicData.ofSingle (Fin 3 × PosEdge L k j)
    (fun n ι => (ι.1, shiftEdge n ι.2)) (fun ι => ι.2.1.initial)
    (meshAt L k j ^ 4)
def colourFaces (L k j : ℕ) : PeriodicData :=
  PeriodicData.ofSingle (Fin 3 × FullSpace.Face L k j)
    (fun n ι => (ι.1, shiftFace n ι.2)) (fun ι => ι.2.corner)
    (meshAt L k j ^ 4)
end Tower
section Weighted
variable {J J' J'' : Type}
def PairingSummable (w : J → ℝ) (f f' : J → ℂ) : Prop :=
  Summable fun i => ‖(w i : ℂ) * (f i * f' i)‖
def wPairing (w : J → ℝ) (f f' : J → ℂ) : ℂ := ∑' i, (w i : ℂ) * (f i * f' i)
def NormSummable (w : J → ℝ) (f : J → ℂ) : Prop :=
  Summable fun i => |w i * ‖f i‖ ^ 2|
def wNorm (w : J → ℝ) (f : J → ℂ) : ℝ := Real.sqrt (∑' i, w i * ‖f i‖ ^ 2)
def wUnitBall (w : J → ℝ) (E : Set (J → ℂ)) : Set (J → ℂ) :=
  {f | f ∈ E ∧ NormSummable w f ∧ wNorm w f ≤ 1}
def OpNormSummable (w : J → ℝ) (w' : J' → ℝ) (E : Set (J → ℂ))
    (M : (J → ℂ) → J' → ℂ) : Prop :=
  ∀ f ∈ wUnitBall w E, NormSummable w' (M f)
def wOpNorm (w : J → ℝ) (w' : J' → ℝ) (E : Set (J → ℂ)) (M : (J → ℂ) → J' → ℂ) : ℝ≥0∞ :=
  ⨆ f ∈ wUnitBall w E, ENNReal.ofReal (wNorm w' (M f))
def wTranspose (w : J → ℝ) (w' : J' → ℝ) (T : J' → J → ℂ) : J → J' → ℂ :=
  fun ι ι' => ((w' ι' / w ι : ℝ) : ℂ) * T ι' ι
def ApplySummableAt (T : J' → J → ℂ) (f : J → ℂ) (ι' : J') : Prop :=
  Summable fun ι => ‖T ι' ι * f ι‖
def applyKernel (T : J' → J → ℂ) (f : J → ℂ) : J' → ℂ := fun ι' => ∑' ι, T ι' ι * f ι
def CompSummableAt (T : J' → J → ℂ) (S : J → J'' → ℂ) (ι' : J') (ι'' : J'') : Prop :=
  Summable fun ι => ‖T ι' ι * S ι ι''‖
def compKernel (T : J' → J → ℂ) (S : J → J'' → ℂ) : J' → J'' → ℂ :=
  fun ι' ι'' => ∑' ι, T ι' ι * S ι ι''
end Weighted
section Operators
variable (I I' : PeriodicData)
def IsShiftInvariant (T : I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ (n : Fin 4 → ℤ) ι' ι, T (I'.translate n ι') (I.translate n ι) = T ι' ι
def ExpDecay (T : I'.Carrier → I.Carrier → ℂ) (C δ : ℝ) : Prop :=
  ∀ ι' ι, ‖T ι' ι‖ ≤ C * Real.exp (-δ * euclidNormVec (I'.pos ι' - I.pos ι))
def IsPeriodicKernel (T : I'.Carrier → I.Carrier → ℂ) : Prop :=
  IsShiftInvariant I I' T ∧ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ExpDecay I I' T C δ
def IsDecayRate (T : I'.Carrier → I.Carrier → ℂ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ExpDecay I I' T C δ
def IsFiniteRange (T : I'.Carrier → I.Carrier → ℂ) : Prop :=
  ∃ ϱ : ℝ, ∀ ι' ι, ¬ euclidNormVec (I'.pos ι' - I.pos ι) ≤ ϱ → T ι' ι = 0
def symbolSummand (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) (ι' : I'.Carrier)
    (ι : I.Carrier) (n : Fin 4 → ℤ) : ℂ :=
  T ι' (I.translate n ι) *
    Complex.exp (Complex.I * bilinDot κ (toComplexVec (I.pos (I.translate n ι) - I'.pos ι')))
def SymbolSummableAt (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) : Prop :=
  ∀ ι' ι, Summable fun n => ‖symbolSummand I I' T κ ι' ι n‖
def SymbolSummableOn (T : I'.Carrier → I.Carrier → ℂ) (D : Set (Fin 4 → ℂ)) : Prop :=
  ∀ κ ∈ D, SymbolSummableAt I I' T κ
def fourierSymbol (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) :
    I'.Carrier → I.Carrier → ℂ :=
  fun ι' ι => ∑' n, symbolSummand I I' T κ ι' ι n
def PeriodizationSummableAt (T : I'.Carrier → I.Carrier → ℂ) (s : ℕ) (ι' : I'.Carrier)
    (ι : I.Carrier) : Prop :=
  Summable fun n : Fin 4 → ℤ => ‖T ι' (I.translate (s • n) ι)‖
def periodization (T : I'.Carrier → I.Carrier → ℂ) (s : ℕ) : I'.Carrier → I.Carrier → ℂ :=
  fun ι' ι => ∑' n : Fin 4 → ℤ, T ι' (I.translate (s • n) ι)
def descendMatrix (s : ℕ) (F : I'.Carrier → I.Carrier → ℂ) :
    I'.QuotMod s → I.QuotMod s → ℂ :=
  fun c' c => Classical.epsilon fun z =>
    ∀ ι' ι, I'.mkQuot s ι' = c' → I.mkQuot s ι = c → F ι' ι = z
end Operators
def phaseOn (I : PeriodicData) (e : Fin 4 → ℤ) (c : I.UnitQuot) : ℂ :=
  Classical.epsilon fun z => ∀ ι, I.mkQuot 1 ι = c →
    Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι))) = z
def phaseMul (I : PeriodicData) (e : Fin 4 → ℤ) :
    (I.UnitQuot → ℂ) →ₗ[ℂ] (I.UnitQuot → ℂ) where
  toFun := fun f c => phaseOn I e c * f c
  map_add' := fun f g => by
    funext c
    simp [mul_add]
  map_smul' := fun z f => by
    funext c
    simp [mul_left_comm]
def dualLattice (s : ℕ) : AddSubgroup AmbientSpace :=
  InfiniteLattice.latticeSubgroup (2 * Real.pi / s)
def imStrip (ς : ℝ) : Set (Fin 4 → ℂ) := {κ | ∀ μ, |(κ μ).im| ≤ ς}
def torusAverage (g : AmbientSpace → ℂ) : ℂ :=
  (((2 * Real.pi) ^ 4)⁻¹ : ℝ) *
    ∫ κ in Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), g κ
end PeriodicOperators
end YangMills.Construction
end
