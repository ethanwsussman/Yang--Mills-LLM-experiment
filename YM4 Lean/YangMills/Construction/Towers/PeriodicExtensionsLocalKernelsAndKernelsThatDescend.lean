import YangMills.Construction.Towers.QuotientMapOnBonds
import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace
def projFace (L n k j : ℕ) (p : Tower.FullSpace.Face L k j) : Tower.Face L n k j :=
  ⟨Tower.FullSpace.projVertex L n k j p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
end Tower.FullSpace
namespace LocalKernels
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (PeriodicData KernelMatrix applyKernel)
instance (L n k j : ℕ) : Nonempty (Tower.PositiveEdge L n k j) :=
  ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
def projPositiveEdge (L n k j : ℕ) (b : PeriodicOperators.PosEdge L k j) :
    Tower.PositiveEdge L n k j :=
  Classical.epsilon fun c => c.1 = Tower.FullSpace.projEdge L n k j b.1
def liftGaugeField (L n k j : ℕ) (U : Tower.Edge L n k j → Matrices.ComplexMatrix2) :
    Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2 :=
  fun b => U (Tower.FullSpace.projEdge L n k j b)
inductive CellType
  | vertex
  | edge
  | face
def Cell (L k j : ℕ) : CellType → Type
  | .vertex => Tower.FullSpace.Vertex L k j
  | .edge => PeriodicOperators.PosEdge L k j
  | .face => Tower.FullSpace.Face L k j
def QuotientCell (L n k j : ℕ) : CellType → Type
  | .vertex => Tower.Vertex L n k j
  | .edge => Tower.PositiveEdge L n k j
  | .face => Tower.Face L n k j
def Cell.translate {L k j : ℕ} (m : Fin 4 → ℤ) : ∀ {c : CellType}, Cell L k j c → Cell L k j c
  | .vertex, x => Tower.FullSpace.vertexImage (PeriodicOperators.intShift m)
      (show Tower.FullSpace.Vertex L k j from x)
  | .edge, b => PeriodicOperators.shiftEdge m (show PeriodicOperators.PosEdge L k j from b)
  | .face, p =>
      PeriodicOperators.shiftFace m (show Tower.FullSpace.Face L k j from p)
def Cell.anchor {L k j : ℕ} : ∀ {c : CellType}, Cell L k j c → AmbientSpace
  | .vertex, x => (show Tower.FullSpace.Vertex L k j from x).1
  | .edge, b => (show PeriodicOperators.PosEdge L k j from b).1.initial.1
  | .face, p => (show Tower.FullSpace.Face L k j from p).corner.1
def Cell.proj {L k j : ℕ} (n : ℕ) : ∀ {c : CellType}, Cell L k j c → QuotientCell L n k j c
  | .vertex, x => Tower.FullSpace.projVertex L n k j x
  | .edge, b => projPositiveEdge L n k j b
  | .face, p => Tower.FullSpace.projFace L n k j p
def WithColour (A : Type) : Bool → Type
  | true => Fin 3 × A
  | false => A
def WithColour.map {A B : Type} (g : A → B) : ∀ {c : Bool}, WithColour A c → WithColour B c
  | true, ι => (ι.1, g ι.2)
  | false, ι => g ι
def WithColour.forget {A : Type} : ∀ {c : Bool}, WithColour A c → A
  | true, ι => ι.2
  | false, ι => ι
structure Component (k : ℕ) where
  level : ℕ
  level_le : level ≤ k
  cellType : CellType
  hasColour : Bool
  weight : ℝ
  weight_pos : 0 < weight
namespace Component
variable {k : ℕ} (L n : ℕ) (P : Component k)
abbrev Elem : Type := WithColour (Cell L k P.level P.cellType) P.hasColour
def toPeriodicData : PeriodicData :=
  PeriodicData.ofSingle (P.Elem L) (fun m ι => WithColour.map (Cell.translate m) ι)
    (fun ι => Cell.anchor (WithColour.forget ι)) P.weight
abbrev QuotElem : Type := WithColour (QuotientCell L n k P.level P.cellType) P.hasColour
def proj (ι : P.Elem L) : P.QuotElem L n := WithColour.map (Cell.proj n) ι
def image : Set (P.QuotElem L n) := range (P.proj L n)
end Component
structure WeightedIndexSet (k : ℕ) where
  Slot : Type
  finite_slot : Finite Slot
  comp : Slot → Component k
namespace WeightedIndexSet
variable {k : ℕ} (L n : ℕ) (I I' : WeightedIndexSet k)
def toPeriodicData : PeriodicData := PeriodicData.sigma fun p => (I.comp p).toPeriodicData L
def ofComponent (P : Component k) : WeightedIndexSet k := ⟨Unit, inferInstance, fun _ => P⟩
def ImageCarrier : Type := Σ p : I.Slot, ↥((I.comp p).image L n)
def imageWeight (c : I.ImageCarrier L n) : ℝ := (I.comp c.1).weight
def proj (ι : (I.toPeriodicData L).Carrier) : I.ImageCarrier L n :=
  ⟨ι.1, ⟨(I.comp ι.1).proj L n ι.2, mem_range_self _⟩⟩
def lift {E : Type*} (f : I.ImageCarrier L n → E) : (I.toPeriodicData L).Carrier → E :=
  fun ι => f (I.proj L n ι)
end WeightedIndexSet
def IsLocalKernel (I I' : PeriodicData) (R : ℝ) (T : KernelMatrix I.Carrier I'.Carrier) : Prop :=
  ∀ ι' ι, ¬ TorusMetric.supNormVec (I.pos ι - I'.pos ι') ≤ R → T ι' ι = 0
def IsBoundedFn {J : Type} (f : J → ℂ) : Prop := ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C
structure BilinearOnBounded {J J' J'' : Type} (H : (J → ℂ) → (J' → ℂ) → J'' → ℂ) : Prop where
  add_left : ∀ f g f', IsBoundedFn f → IsBoundedFn g → IsBoundedFn f' →
    H (f + g) f' = H f f' + H g f'
  smul_left : ∀ (c : ℂ) f f', IsBoundedFn f → IsBoundedFn f' →
    H (c • f) f' = c • H f f'
  add_right : ∀ f f' g', IsBoundedFn f → IsBoundedFn f' → IsBoundedFn g' →
    H f (f' + g') = H f f' + H f g'
  smul_right : ∀ (c : ℂ) f f', IsBoundedFn f → IsBoundedFn f' →
    H f (c • f') = c • H f f'
def IsLocalBilinear (I I' I'' : PeriodicData) (R : ℝ)
    (H : (I.Carrier → ℂ) → (I'.Carrier → ℂ) → I''.Carrier → ℂ) : Prop :=
  BilinearOnBounded H ∧
    ∀ f g f' g', IsBoundedFn f → IsBoundedFn g → IsBoundedFn f' →
      IsBoundedFn g' → ∀ ι'',
        (∀ ι, TorusMetric.supNormVec (I.pos ι - I''.pos ι'') ≤ R → f ι = g ι) →
        (∀ ι', TorusMetric.supNormVec (I'.pos ι' - I''.pos ι'') ≤ R → f' ι' = g' ι') →
        H f f' ι'' = H g g' ι''
def KernelDescends {k : ℕ} (L n : ℕ) (I I' : WeightedIndexSet k)
    (T : KernelMatrix (I.toPeriodicData L).Carrier (I'.toPeriodicData L).Carrier)
    (M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)) : Prop :=
  (∃ R : ℝ, 0 ≤ R ∧ IsLocalKernel (I.toPeriodicData L) (I'.toPeriodicData L) R T) ∧
    ∀ f : I.ImageCarrier L n → ℂ,
      applyKernel T (I.lift L n f) = I'.lift L n (applyKernel M f)
end LocalKernels
end YangMills.Construction
end
