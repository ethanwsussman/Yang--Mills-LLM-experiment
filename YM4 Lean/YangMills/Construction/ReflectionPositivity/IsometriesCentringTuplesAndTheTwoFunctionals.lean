import YangMills.Construction.Cumulants.NonSingletonPartitions
import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.Probability.BoundedRealRandomVariable
import YangMills.Construction.ReflectionPositivity.TwoSidesOfALinkMirrorAndTheirAlgebras
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace SetPartition
variable {α : Type*} [DecidableEq α]
abbrev Partitions (A : Finset α) : Type _ := Finpartition A
theorem parts_eq_empty_of_empty (π : Partitions (∅ : Finset α)) : π.parts = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro B hB
  obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hB
  have hx' : x ∈ (∅ : Finset α) := π.le hB hx
  simp at hx'
abbrev PartitionsFin (q : ℕ) : Type := Partitions (Finset.univ : Finset (Fin q))
def singletonFree (q : ℕ) : Finset (PartitionsFin q) :=
  Finset.univ.filter fun π => ∀ B ∈ π.parts, B.card ≠ 1
theorem singletonFree_eq_nonSingletonPartitions (q : ℕ) :
    singletonFree q = nonSingletonPartitions q := by
  refine Finset.filter_congr fun π _ => forall₂_congr fun B hB => ?_
  have hpos : 0 < B.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hB)
  omega
theorem mem_singletonFree_zero (π : PartitionsFin 0) : π ∈ singletonFree 0 := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun B hB => ?_⟩
  have hempty : π.parts = ∅ := parts_eq_empty_of_empty π
  simp [hempty] at hB
theorem singletonFree_one : singletonFree 1 = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro π hπ
  obtain ⟨B, hB, -⟩ := π.exists_mem (Finset.mem_univ (0 : Fin 1))
  have h₁ : B.card ≠ 1 := (Finset.mem_filter.mp hπ).2 B hB
  have h₂ : 0 < B.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hB)
  have h₃ : B.card ≤ 1 := by simpa using Finset.card_le_univ B
  omega
end SetPartition
namespace Probability
variable {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
def AllBoundedRealRV (x : Fin q → Ω → ℝ) : Prop :=
  ∀ i, IsBoundedRealRV (x i)
def subfamilyCumulant (μ : Measure Ω) (x : Fin q → Ω → ℝ) (B : Finset (Fin q)) : ℂ :=
  Cumulants.mixedCumulant μ fun k : Fin B.card => x (B.orderEmbOfFin rfl k)
end Probability
namespace ReflectionPositivity
namespace CutoffMirrors
namespace MirrorData
variable (D : MirrorData)
abbrev DirectedBond : Type := PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ)
abbrev BondField : Type := D.DirectedBond → Matrices.ComplexMatrix2
def IsDistPreserving (g : D.Torus → D.Torus) : Prop :=
  ∀ x y, D.torusDist (g x) (g y) = D.torusDist x y
abbrev Symmetry : Type := PeriodicLattice.TorusLatticeSymmetry D.L D.m (D.K : ℕ)
variable {D}
theorem Symmetry.isDistPreserving (s : D.Symmetry) : D.IsDistPreserving s.toFun := s.dist_eq
namespace Symmetry
variable (s : D.Symmetry)
def bondImage (b : D.DirectedBond) : D.DirectedBond :=
  PeriodicLattice.TorusLatticeSymmetry.bondMap s b
theorem bondImage_eq {b b' : D.DirectedBond}
    (hb : PeriodicLattice.TorusLatticeSymmetry.IsBondImage s b b') : bondImage s b = b' := by
  have hex : ∃ b', PeriodicLattice.TorusLatticeSymmetry.IsBondImage s b b' := ⟨b', hb⟩
  have e : bondImage s b = hex.choose := dif_pos hex
  rw [e]
  exact PeriodicLattice.TorusLatticeSymmetry.isBondImage_unique s hex.choose_spec hb
def IsFaceImage (p p' : D.Face) : Prop :=
  p'.vertices = PeriodicLattice.TorusLatticeSymmetry.pointMap s '' p.vertices
def faceImage (p : D.Face) : D.Face :=
  open Classical in
  if hp : ∃ p', IsFaceImage s p p' then hp.choose else p
theorem isFaceImage_faceImage {p : D.Face}
    (hp : ∃ p', IsFaceImage s p p') : IsFaceImage s p (faceImage s p) := by
  have e : faceImage s p = hp.choose := dif_pos hp
  rw [e]
  exact hp.choose_spec
def pullback (U : D.BondField) : D.BondField := fun b => U (bondImage s b)
theorem pullback_apply (U : D.BondField) {b b' : D.DirectedBond}
    (hb : PeriodicLattice.TorusLatticeSymmetry.IsBondImage s b b') : pullback s U b = U b' := by
  rw [pullback, bondImage_eq s hb]
theorem pullback_eq_transportGaugeField (σ : D.Torus ≃ D.Torus) (hσ : ∀ x, s.toFun x = σ x)
    (hb : ∀ b : D.DirectedBond, ∃ b', PeriodicLattice.TorusLatticeSymmetry.IsBondImage s b b')
    (U : D.BondField) :
    pullback s U = PeriodicLattice.transportGaugeField σ.symm U := by
  funext b
  have hex : ∃ b' : D.DirectedBond, (b'.source : D.Torus) = σ.symm.symm b.source ∧
      (b'.target : D.Torus) = σ.symm.symm b.target := by
    obtain ⟨b', hb'⟩ := hb b
    have h₁ : b'.source = PeriodicLattice.TorusLatticeSymmetry.pointMap s b.source :=
      congrArg Prod.fst hb'
    have h₂ : b'.target = PeriodicLattice.TorusLatticeSymmetry.pointMap s b.target :=
      congrArg Prod.snd hb'
    refine ⟨b', ?_, ?_⟩
    · rw [h₁]
      exact hσ _
    · rw [h₂]
      exact hσ _
  have e : PeriodicLattice.bondPreimage σ.symm b = hex.choose := dif_pos hex
  have himg : PeriodicLattice.TorusLatticeSymmetry.IsBondImage s b hex.choose := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hex.choose_spec.1.trans (hσ _).symm
    · exact hex.choose_spec.2.trans (hσ _).symm
  simp only [PeriodicLattice.transportGaugeField, e]
  exact pullback_apply s U himg
end Symmetry
variable (D)
def centredObservable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : D.Torus → E)
    (U : D.BondField) : E :=
  PeriodicLattice.smearedObservable f U -
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (PeriodicLattice.smearedObservable f)
abbrev FunTuple (E : Type*) : Type _ := List (D.Torus → E)
variable {D}
def FunTuple.prodOver {E R : Type*} [Monoid R] (X : D.FunTuple E) (F : (D.Torus → E) → R) : R :=
  (X.map F).prod
def PairwiseDisjointSupp {E : Type*} [Zero E] {q : ℕ} (h : Fin q → D.Torus → E) : Prop :=
  ∀ i j, i ≠ j → D.supp (h i) ∩ D.supp (h j) = ∅
def _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkLevel.reflectTuple
    {E : Type*} (C : LinkLevel D) (X : D.FunTuple E) : D.FunTuple E :=
  X.map C.reflectFn
def IsAdmissibleArg {q : ℕ} (h : Fin q → D.Torus → ℝ) : Prop :=
  (∀ i, TestFunctions.IsLipschitzFor D.torusDist (h i)) ∧ PairwiseDisjointSupp h
variable (D)
def gibbsFunctional {q : ℕ} (h : Fin q → D.Torus → ℝ) : ℝ :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling fun U => ∏ i, D.centredObservable (h i) U
def truncatedFunctional {q : ℕ} (h : Fin q → D.Torus → ℝ) : ℂ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ B ∈ π.parts,
    SchwingerFunctions.connectedSchwinger D.L D.m D.K D.coupling
      fun k : Fin B.card => h (B.orderEmbOfFin rfl k)
def gibbsFunctionalList (X : D.FunTuple ℝ) : ℝ := D.gibbsFunctional X.get
def truncatedFunctionalList (X : D.FunTuple ℝ) : ℂ := D.truncatedFunctional X.get
theorem truncatedFunctionalList_nil : D.truncatedFunctionalList [] = 1 := by
  have h : ∀ π : SetPartition.PartitionsFin 0, π.parts = ∅ := SetPartition.parts_eq_empty_of_empty
  have e : SetPartition.singletonFree 0 = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr SetPartition.mem_singletonFree_zero
  have c : Fintype.card (SetPartition.PartitionsFin 0) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⊥, fun π => Finpartition.ext (by rw [h π, h ⊥])⟩
  simp [truncatedFunctionalList, truncatedFunctional, e, h, c]
theorem truncatedFunctional_eq_centredSchwinger {q : ℕ} (h : Fin q → D.Torus → ℝ) :
    D.truncatedFunctional h = SchwingerFunctions.centredSchwinger D.L D.m D.K D.coupling h := by
  rw [truncatedFunctional, SetPartition.singletonFree_eq_nonSingletonPartitions]
  rfl
end MirrorData
end CutoffMirrors
end ReflectionPositivity
end YangMills.Construction
end
