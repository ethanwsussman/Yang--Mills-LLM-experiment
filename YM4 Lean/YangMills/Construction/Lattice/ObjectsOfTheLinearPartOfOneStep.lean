import YangMills.Construction.Towers.RealAnalyticFunctionsConstantWhereTheCovariantDifferenceIsInjectiveProof
import YangMills.Construction.Lattice.BondLinearMaps
import YangMills.Construction.Lattice.OneStepCovarianceAndDomains
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
abbrev PositiveBondAtLevel (L m K n : ℕ) : Type := PositivelyOrientedBond L m (levelDepth K n)
def restrictToDoubleBlockSet (c : BondAtLevel L m K (n + 1))
    (f : BondMaps.BondValued (PositiveBondAtLevel L m K n)) :
    LieBondField (doubleBlockSymmetricSet c) :=
  fun e => f ⟨e.1, e.2.2⟩
def stepFieldMap (s : AveragingScheme) (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (f : BondMaps.BondValued (PositiveBondAtLevel L m K n)) :
    BondMaps.BondValued (PositiveBondAtLevel L m K (n + 1)) :=
  fun c => toTraceless (stepVariable s c.1 (restrictToDoubleBlockSet c.1 f) U)
theorem conjugateBy_mem_traceless_of_any (V : Matrices.ComplexMatrix2)
    {A : Matrices.ComplexMatrix2} (hA : A ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.conjugateBy V A ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
def straightenedSummand (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (f : LieBondField (doubleBlockSymmetricSet c)) (x : SiteAtLevel L m K n) :
    Matrices.ComplexMatrix2 :=
  ((crossingPath c x).map fun e => Matrices.ComplexMatrix2.conjugateBy
    (contourHolonomy s U c.source x * pathHolonomy U (axialPath x e.source))
    (f.eval e : Matrices.ComplexMatrix2)).sum
theorem straightenedSummand_mem (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (f : LieBondField (doubleBlockSymmetricSet c)) (x : SiteAtLevel L m K n) :
    straightenedSummand s c U f x ∈ Matrices.ComplexMatrix2.traceless := by
  refine list_sum_mem ?_
  intro y hy
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hy
  exact conjugateBy_mem_traceless_of_any _ (f.eval e).2
theorem straightenedMap_mem (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (f : LieBondField (doubleBlockSymmetricSet c)) :
    straightenedMap s c U f ∈ Matrices.ComplexMatrix2.traceless := by
  refine Matrices.ComplexMatrix2.traceless.smul_mem _ ?_
  exact finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.traceless)
    Matrices.ComplexMatrix2.traceless.zero_mem
    (fun _ _ => Matrices.ComplexMatrix2.traceless.add_mem)
    fun x _ => straightenedSummand_mem s c U f x
theorem LieBondField.eval_add {P : SymmetricBondSet L m K n} (f g : LieBondField P)
    (e : BondAtLevel L m K n) : (f + g).eval e = f.eval e + g.eval e := by
  simp only [LieBondField.eval]
  split_ifs <;> simp [add_comm]
theorem LieBondField.eval_smul {P : SymmetricBondSet L m K n} (z : ℂ)
    (f : LieBondField P) (e : BondAtLevel L m K n) : (z • f).eval e = z • f.eval e := by
  simp only [LieBondField.eval]
  split_ifs <;> simp
theorem straightenedSummand_add (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (f g : LieBondField (doubleBlockSymmetricSet c))
    (x : SiteAtLevel L m K n) : straightenedSummand s c U (f + g) x =
      straightenedSummand s c U f x + straightenedSummand s c U g x := by
  simp only [straightenedSummand]
  rw [← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [LieBondField.eval_add, Submodule.coe_add, Matrices.ComplexMatrix2.conjugateBy,
    mul_add, add_mul]
theorem straightenedSummand_smul (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2) (z : ℂ)
    (f : LieBondField (doubleBlockSymmetricSet c))
    (x : SiteAtLevel L m K n) : straightenedSummand s c U (z • f) x =
      z • straightenedSummand s c U f x := by
  simp only [straightenedSummand]
  induction crossingPath c x with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, smul_add]
    rw [ih]
    congr 1
    simp only [LieBondField.eval_smul, Submodule.coe_smul, Matrices.ComplexMatrix2.conjugateBy,
      mul_smul_comm, smul_mul_assoc]
theorem finite_siteAtLevel [Finite (PositiveBondAtLevel L m K n)] :
    Finite (SiteAtLevel L m K n) := by apply _root_.YangMills.DeltaSharedProofs.p500448 <;> assumption
section Derivatives
variable [Fintype (PositiveBondAtLevel L m K n)] [Fintype (PositiveBondAtLevel L m K (n + 1))]
def stepLinearization (s : AveragingScheme) (U : BondAtLevel L m K n → Matrices.ComplexMatrix2) :
    BondMaps.BondLinearMap (PositiveBondAtLevel L m K n) (PositiveBondAtLevel L m K (n + 1)) :=
  (fderiv ℂ (stepFieldMap s U) 0).toLinearMap
end Derivatives
section Partial
variable {B : Type*} [Fintype B]
open Classical in
def partialAlongBond (F : BondMaps.BondValued B → ↥Matrices.ComplexMatrix2.traceless)
    (f : BondMaps.BondValued B) (e : B) :
    ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ] ↥Matrices.ComplexMatrix2.traceless :=
  (fderiv ℂ F f).toLinearMap ∘ₗ
    LinearMap.single ℂ (fun _ : B => ↥Matrices.ComplexMatrix2.traceless) e
def partialAlongBondNorm (F : BondMaps.BondValued B → ↥Matrices.ComplexMatrix2.traceless)
    (f : BondMaps.BondValued B) (e : B) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (partialAlongBond F f e)‖
end Partial
end YangMills.Construction.PeriodicLattice
