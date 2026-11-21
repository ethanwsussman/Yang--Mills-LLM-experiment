import YangMills.Construction.Lattice.SiteCoordinates
import YangMills.Construction.Towers.ClosedFormsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ClosedEdgeForms
open Finset
section Averages
variable {M : Type*} [AddCommGroup M] [Module ℝ M]
def powerAverage (N : ℕ) (T : Module.End ℝ M) : Module.End ℝ M :=
  (N : ℝ)⁻¹ • ∑ i ∈ range N, T ^ i
def weightedPowerAverage (N : ℕ) (T : Module.End ℝ M) : Module.End ℝ M :=
  (N : ℝ)⁻¹ • ∑ i ∈ range N, (i : ℝ) • T ^ i
theorem commute_powerAverage {S T : Module.End ℝ M} (N : ℕ) (hST : Commute S T) :
    Commute S (powerAverage N T) :=
  (Commute.sum_right _ _ _ fun i _ => hST.pow_right i).smul_right _
theorem commute_weightedPowerAverage {S T : Module.End ℝ M} (N : ℕ) (hST : Commute S T) :
    Commute S (weightedPowerAverage N T) :=
  (Commute.sum_right _ _ _ fun i _ => (hST.pow_right i).smul_right _).smul_right _
theorem sub_one_mul_powerAverage {N : ℕ} {T : Module.End ℝ M} (hT : T ^ N = 1) :
    (T - 1) * powerAverage N T = 0 := by
  rw [powerAverage, mul_smul_comm, mul_geom_sum, hT, sub_self, smul_zero]
theorem sub_one_mul_sum_smul_pow (T : Module.End ℝ M) (n : ℕ) :
    (T - 1) * ∑ i ∈ range n, (i : ℝ) • T ^ i =
      (n : ℝ) • T ^ n - T * ∑ i ∈ range n, T ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ, mul_add, mul_smul_comm, Nat.cast_add,
      Nat.cast_one, add_smul, one_smul, sub_mul, one_mul, ← pow_succ', smul_sub]
    simp only [pow_succ']
    abel
theorem sub_one_mul_weightedPowerAverage {N : ℕ} {T : Module.End ℝ M} (hN : 0 < N)
    (hT : T ^ N = 1) :
    (T - 1) * weightedPowerAverage N T = 1 - powerAverage N T := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hfix : T * ∑ i ∈ range N, T ^ i = ∑ i ∈ range N, T ^ i := by
    have hgeom := mul_geom_sum T N
    rw [hT, sub_self, sub_mul, one_mul, sub_eq_zero] at hgeom
    exact hgeom
  rw [weightedPowerAverage, powerAverage, mul_smul_comm, sub_one_mul_sum_smul_pow, hT, hfix,
    smul_sub, smul_smul, inv_mul_cancel₀ hN', one_smul]
end Averages
section Primitive
variable {M ι : Type*} [AddCommGroup M] [Module ℝ M]
def averageAlong (N : ℕ) (T : ι → Module.End ℝ M) (l : List ι) : Module.End ℝ M :=
  (l.map fun ν => powerAverage N (T ν)).prod
theorem exists_primitive_averageAlong {N : ℕ} (hN : 0 < N) {T : ι → Module.End ℝ M}
    (hT : ∀ μ, T μ ^ N = 1) (hcomm : ∀ μ ν, Commute (T μ) (T ν)) {f : ι → M}
    (hclosed : ∀ μ ν, (T μ - 1) (f ν) = (T ν - 1) (f μ)) (l : List ι) :
    ∃ g : M, ∀ μ, (T μ - 1) g = f μ - averageAlong N T l (f μ) := by
  induction l with
  | nil => exact ⟨0, fun μ => by simp [averageAlong]⟩
  | cons ν l ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨weightedPowerAverage N (T ν) (f ν) + powerAverage N (T ν) g, fun μ => ?_⟩
    have hq : Commute (T μ - 1) (weightedPowerAverage N (T ν)) :=
      ((commute_weightedPowerAverage N (hcomm μ ν)).sub_left (Commute.one_left _))
    have hq' : Commute (T ν - 1) (weightedPowerAverage N (T ν)) :=
      ((commute_weightedPowerAverage N (Commute.refl _)).sub_left (Commute.one_left _))
    have hp : Commute (T μ - 1) (powerAverage N (T ν)) :=
      ((commute_powerAverage N (hcomm μ ν)).sub_left (Commute.one_left _))
    have h1 : (T μ - 1) (weightedPowerAverage N (T ν) (f ν)) =
        f μ - powerAverage N (T ν) (f μ) := by
      have e1 := LinearMap.congr_fun hq.eq (f ν)
      have e2 := LinearMap.congr_fun hq'.eq (f μ)
      have e3 := LinearMap.congr_fun (sub_one_mul_weightedPowerAverage hN (hT ν)) (f μ)
      simp only [Module.End.mul_apply] at e1 e2 e3
      rw [e1, hclosed μ ν, ← e2, e3]
      simp
    have h2 : (T μ - 1) (powerAverage N (T ν) g) =
        powerAverage N (T ν) (f μ) - powerAverage N (T ν) (averageAlong N T l (f μ)) := by
      have e1 := LinearMap.congr_fun hp.eq g
      simp only [Module.End.mul_apply] at e1
      rw [e1, hg μ, map_sub]
    rw [map_add, h1, h2]
    simp only [averageAlong, List.map_cons, List.prod_cons, Module.End.mul_apply]
    abel
theorem sub_one_mul_averageAlong {N : ℕ} {T : ι → Module.End ℝ M}
    (hT : ∀ μ, T μ ^ N = 1) (hcomm : ∀ μ ν, Commute (T μ) (T ν)) {ν : ι} {l : List ι}
    (hν : ν ∈ l) :
    (T ν - 1) * averageAlong N T l = 0 := by
  induction l with
  | nil => simp at hν
  | cons κ l ih =>
    have hcons : averageAlong N T (κ :: l) = powerAverage N (T κ) * averageAlong N T l := by
      simp [averageAlong]
    rw [hcons]
    rcases List.mem_cons.mp hν with rfl | hν
    · rw [← mul_assoc, sub_one_mul_powerAverage (hT ν), zero_mul]
    · have hp : Commute (T ν - 1) (powerAverage N (T κ)) :=
        ((commute_powerAverage N (hcomm ν κ)).sub_left (Commute.one_left _))
      rw [← mul_assoc, hp.eq, mul_assoc, ih hν, mul_zero]
end Primitive
section OnGroup
variable {A V : Type*} [AddCommGroup A] [AddCommGroup V] [Module ℝ V]
def translateBy (e : A) : Module.End ℝ (A → V) where
  toFun φ := fun x => φ (x + e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem translateBy_apply (e : A) (φ : A → V) (x : A) : translateBy e φ x = φ (x + e) := rfl
theorem translateBy_pow_apply (e : A) (i : ℕ) (φ : A → V) (x : A) :
    ((translateBy e : Module.End ℝ (A → V)) ^ i) φ x = φ (x + i • e) := by
  induction i generalizing φ with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Module.End.mul_apply, ih, translateBy_apply, succ_nsmul, add_assoc]
theorem translateBy_pow_eq_one {e : A} {N : ℕ} (he : N • e = 0) :
    (translateBy e : Module.End ℝ (A → V)) ^ N = 1 := by
  refine LinearMap.ext fun g => funext fun x => ?_
  rw [translateBy_pow_apply, he, add_zero]
  rfl
theorem commute_translateBy (e e' : A) :
    Commute (translateBy e : Module.End ℝ (A → V)) (translateBy e') := by
  refine LinearMap.ext fun g => funext fun x => ?_
  simp only [Module.End.mul_apply, translateBy_apply, add_right_comm]
omit [AddCommGroup V] [Module ℝ V] in
theorem apply_add_zsmul_sum_of_invariant {φ : A → V} {e : Fin 4 → A}
    (hinv : ∀ ν x, φ (x + e ν) = φ x) (n : Fin 4 → ℤ) (x : A) :
    φ (x + ∑ μ, n μ • e μ) = φ x := by
  let H : AddSubgroup A :=
    { carrier := {y | ∀ x, φ (x + y) = φ x}
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      zero_mem' := fun x => by rw [add_zero]
      neg_mem' := fun {a} ha x => by
        have hx := ha (x + -a)
        rwa [neg_add_cancel_right, eq_comm] at hx }
  have hmem : ∑ μ, n μ • e μ ∈ H :=
    H.sum_mem fun μ _ => H.zsmul_mem (fun x => hinv μ x) (n μ)
  exact hmem x
theorem exists_primitive_add_const (e : Fin 4 → A) {N : ℕ} (hN : 0 < N)
    (hNe : ∀ μ, N • e μ = 0)
    (hgen : ∀ y : A, ∃ n : Fin 4 → ℤ, y = 0 + ∑ μ, n μ • e μ) (f : Fin 4 → A → V)
    (hclosed : ∀ μ ν x, f μ x + f ν (x + e μ) = f ν x + f μ (x + e ν)) :
    ∃ (g : A → V) (c : Fin 4 → V), ∀ μ x, f μ x = g (x + e μ) - g x + c μ := by
  let T : Fin 4 → Module.End ℝ (A → V) := fun μ => translateBy (e μ)
  have hT : ∀ μ, T μ ^ N = 1 := fun μ => translateBy_pow_eq_one (hNe μ)
  have hcomm : ∀ μ ν, Commute (T μ) (T ν) := fun μ ν => commute_translateBy _ _
  have hcl : ∀ μ ν, (T μ - 1) (f ν) = (T ν - 1) (f μ) := by
    intro μ ν
    funext x
    have hx := hclosed μ ν x
    simp only [T, LinearMap.sub_apply, Pi.sub_apply, translateBy_apply, Module.End.one_apply]
    rw [sub_eq_sub_iff_add_eq_add, add_comm, hx, add_comm]
  obtain ⟨g, hg⟩ := exists_primitive_averageAlong hN hT hcomm hcl (List.finRange 4)
  have hinv : ∀ μ ν x, averageAlong N T (List.finRange 4) (f μ) (x + e ν) =
      averageAlong N T (List.finRange 4) (f μ) x := by
    intro μ ν x
    have hz := LinearMap.congr_fun (sub_one_mul_averageAlong hT hcomm (List.mem_finRange ν)) (f μ)
    have hz' := congrFun hz x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Pi.sub_apply, T, translateBy_apply,
      Module.End.one_apply, LinearMap.zero_apply, Pi.zero_apply] at hz'
    exact sub_eq_zero.mp hz'
  refine ⟨g, fun μ => averageAlong N T (List.finRange 4) (f μ) 0, fun μ x => ?_⟩
  obtain ⟨n, hn⟩ := hgen x
  have hconst : averageAlong N T (List.finRange 4) (f μ) x =
      averageAlong N T (List.finRange 4) (f μ) 0 := by
    rw [hn]
    exact apply_add_zsmul_sum_of_invariant (hinv μ) n 0
  have hx := congrFun (hg μ) x
  simp only [T, LinearMap.sub_apply, Pi.sub_apply, translateBy_apply,
    Module.End.one_apply] at hx
  rw [hconst] at hx
  rw [hx]
  abel
end OnGroup
section Lattice
open PeriodicLattice
variable {L n k j : ℕ}
theorem vertexCoboundary_forwardFrom (l : Vertex L n k j → Matrices.ComplexMatrix2)
    (x : Vertex L n k j) (μ : Fin 4) :
    vertexCoboundary l (Bond.forwardFrom x μ) = l (x + unitStep L n _ μ) - l x := rfl
theorem vertexCoboundary_opposite (l : Vertex L n k j → Matrices.ComplexMatrix2)
    (b : Edge L n k j) : vertexCoboundary l b.opposite = -vertexCoboundary l b := by
  simp [vertexCoboundary, Bond.opposite]
theorem eq_forwardFrom_of_sub {b : Edge L n k j} {μ : Fin 4}
    (hb : b.target - b.source = unitStep L n _ μ) : b = Bond.forwardFrom b.source μ := by
  refine Bond.ext rfl ?_
  simp only [Bond.forwardFrom]
  rw [← hb]
  abel
theorem isClosedEdgeForm_vertexCoboundary (l : Vertex L n k j → Matrices.ComplexMatrix2) :
    IsClosedEdgeForm (vertexCoboundary l) := by
  funext p
  simp only [edgeCoboundary, vertexCoboundary_forwardFrom, Pi.zero_apply]
  rw [add_right_comm p.origin (unitStep L n _ p.secondAxis) (unitStep L n _ p.firstAxis)]
  abel
theorem isClosedEdgeForm_of_translationInvariant {a : Edge L n k j → Matrices.ComplexMatrix2}
    (ha : IsTranslationInvariantEdgeForm a) : IsClosedEdgeForm a := by
  funext p
  simp only [edgeCoboundary, Pi.zero_apply]
  rw [ha p.firstAxis (p.origin + unitStep L n _ p.secondAxis) p.origin,
    ha p.secondAxis (p.origin + unitStep L n _ p.firstAxis) p.origin]
  abel
theorem isClosedEdgeForm_add {B B' : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : IsClosedEdgeForm B) (hB' : IsClosedEdgeForm B') : IsClosedEdgeForm (B + B') := by
  funext p
  have e := congrFun hB p
  have e' := congrFun hB' p
  simp only [edgeCoboundary, Pi.zero_apply, Pi.add_apply] at e e' ⊢
  calc _ = (B (Bond.forwardFrom p.origin p.firstAxis) +
        B (Bond.forwardFrom (p.origin + unitStep L n _ p.firstAxis) p.secondAxis) -
        B (Bond.forwardFrom (p.origin + unitStep L n _ p.secondAxis) p.firstAxis) -
        B (Bond.forwardFrom p.origin p.secondAxis)) +
      (B' (Bond.forwardFrom p.origin p.firstAxis) +
        B' (Bond.forwardFrom (p.origin + unitStep L n _ p.firstAxis) p.secondAxis) -
        B' (Bond.forwardFrom (p.origin + unitStep L n _ p.secondAxis) p.firstAxis) -
        B' (Bond.forwardFrom p.origin p.secondAxis)) := by abel
    _ = 0 := by rw [e, e', add_zero]
theorem square_relation_of_isClosedEdgeForm {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : IsClosedEdgeForm B) (μ ν : Fin 4) (x : Vertex L n k j) :
    B (Bond.forwardFrom x μ) + B (Bond.forwardFrom (x + unitStep L n _ μ) ν) =
      B (Bond.forwardFrom x ν) + B (Bond.forwardFrom (x + unitStep L n _ ν) μ) := by
  have key : ∀ μ ν : Fin 4, μ < ν → ∀ x : Vertex L n k j,
      B (Bond.forwardFrom x μ) + B (Bond.forwardFrom (x + unitStep L n _ μ) ν) =
        B (Bond.forwardFrom x ν) + B (Bond.forwardFrom (x + unitStep L n _ ν) μ) := by
    intro μ ν hμν x
    have e := congrFun hB ⟨x, μ, ν, hμν⟩
    simp only [edgeCoboundary, Pi.zero_apply] at e
    rw [sub_sub, sub_eq_zero] at e
    rw [e, add_comm]
  rcases lt_trichotomy μ ν with hlt | rfl | hgt
  · exact key μ ν hlt x
  · rfl
  · exact (key ν μ hgt x).symm
end Lattice
open PeriodicLattice in
theorem closedEdgeFormsOnPeriodicLattice (hcoord : CoordinateDescription) :
    ClosedEdgeFormsOnPeriodicLattice := by
  intro L n k j hL hn hjk B hB
  constructor
  · intro hcl
    obtain ⟨-, hpos, -, hgen, hmod, -⟩ :=
      (hcoord L n hL.1 hL.2 hn).1 (levelDepth k j) (by simp only [levelDepth]; omega)
    have hNe : ∀ μ, (2 * halfPeriod L n (levelDepth k j)) • unitStep L n (levelDepth k j) μ = 0 := by
      intro μ
      have e := (hmod 0 (Pi.single μ ((2 * halfPeriod L n (levelDepth k j) : ℕ) : ℤ)) 0).2
        (fun ν => by
          by_cases hν : ν = μ
          · subst hν
            simp [Int.ModEq]
          · simp [Pi.single_eq_of_ne hν])
      simp only [offsetSite, Pi.single_apply, ite_smul, zero_smul, Pi.zero_apply,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero,
        zero_add] at e
      rw [← natCast_zsmul]
      exact e
    have hsu : ∀ (μ : Fin 4) (x : Vertex L n k j),
        B (Bond.forwardFrom x μ) ∈ Matrices.ComplexMatrix2.hermitianTraceless :=
      fun μ x => hB.1 _ ⟨μ, by simp [Bond.forwardFrom]⟩
    obtain ⟨g, c, hgc⟩ := exists_primitive_add_const (V := ↥Matrices.ComplexMatrix2.hermitianTraceless)
      (unitStep L n (levelDepth k j)) hpos hNe
      (fun y => by
        obtain ⟨m, hm⟩ := hgen 0 y
        exact ⟨m, hm⟩)
      (fun μ x => ⟨B (Bond.forwardFrom x μ), hsu μ x⟩)
      (fun μ ν x => Subtype.ext (square_relation_of_isClosedEdgeForm hcl μ ν x))
    have hval : ∀ (μ : Fin 4) (x : Vertex L n k j),
        (B - vertexCoboundary fun x => (g x : Matrices.ComplexMatrix2)) (Bond.forwardFrom x μ) =
          (c μ : Matrices.ComplexMatrix2) := by
      intro μ x
      have e := congrArg Subtype.val (hgc μ x)
      simp only [AddSubgroupClass.coe_sub, Submodule.coe_add] at e
      simp only [Pi.sub_apply, vertexCoboundary_forwardFrom]
      rw [e]
      abel
    refine ⟨fun x => (g x : Matrices.ComplexMatrix2), fun x _ => (g x).2,
      B - vertexCoboundary fun x => (g x : Matrices.ComplexMatrix2),
      ⟨fun b ⟨μ, hb⟩ => ?_, fun b => ?_⟩, fun μ x x' => ?_, ?_⟩
    · rw [eq_forwardFrom_of_sub hb, hval]
      exact (c μ).2
    · simp only [Pi.sub_apply, vertexCoboundary_opposite, hB.2 b]
      abel
    · rw [hval, hval]
    · simp
  · rintro ⟨l, -, a, -, ha, rfl⟩
    exact isClosedEdgeForm_add (isClosedEdgeForm_vertexCoboundary l)
      (isClosedEdgeForm_of_translationInvariant ha)
end YangMills.Construction.Tower.ClosedEdgeForms
end
