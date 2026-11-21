import YangMills.Construction.Lattice.AveragesAndWeightsProof
import YangMills.Construction.Lattice.StandardPartitionCubeGeometryArgument
import Mathlib
set_option autoImplicit false
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace SupCubes
variable {S a b : ℝ}
def OnMesh (S a : ℝ) (c : AddCircle S) : Prop :=
  ∃ n : ℤ, c = (((n : ℝ) * a : ℝ) : AddCircle S)
def OnHalfMesh (S a : ℝ) (c : AddCircle S) : Prop :=
  ∃ n : ℤ, c = ((a * ((n : ℝ) + 1 / 2) : ℝ) : AddCircle S)
theorem exists_coe_eq_abs_sub_eq_norm_sub (c : AddCircle S) (r : ℝ) :
    ∃ v : ℝ, (v : AddCircle S) = c ∧ |v - r| = ‖c - (r : AddCircle S)‖ := by
  obtain ⟨w, hw, hw'⟩ := exists_coe_eq_abs_eq_norm (c - (r : AddCircle S))
  refine ⟨w + r, ?_, ?_⟩
  · rw [AddCircle.coe_add, hw, sub_add_cancel]
  · rw [add_sub_cancel_right, hw']
theorem norm_coe_sub_coe_le (v r : ℝ) :
    ‖(v : AddCircle S) - (r : AddCircle S)‖ ≤ |v - r| := by
  rw [← AddCircle.coe_sub]
  exact addCircle_norm_coe_le_abs _
theorem exists_eq_add_int_mul_of_coe_eq {v v' : ℝ} (h : (v : AddCircle S) = v') :
    ∃ l : ℤ, v' = v + (l : ℝ) * S := by
  have h0 : ((v' - v : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨l, hl⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
  refine ⟨l, ?_⟩
  have : (l : ℝ) * S = v' - v := by simpa [zsmul_eq_mul] using hl
  linarith
theorem coe_add_int_mul_period (v : ℝ) (l : ℤ) :
    ((v + (l : ℝ) * S : ℝ) : AddCircle S) = v := by apply _root_.YangMills.Construction.PeriodicLattice.StandardCubes.coe_add_int_mul_period <;> assumption
theorem OnHalfMesh.of_odd_mul {h : ℕ} (hab : a = (2 * (h : ℝ) + 1) * b) {c : AddCircle S}
    (hc : OnHalfMesh S a c) : OnHalfMesh S b c := by
  obtain ⟨n, rfl⟩ := hc
  refine ⟨(2 * h + 1) * n + h, ?_⟩
  congr 1
  rw [hab]
  push_cast
  ring
theorem exists_offset_near {h : ℕ} (hab : a = (2 * (h : ℝ) + 1) * b) (hb : 0 < b)
    {x : AddCircle S} {r : ℝ} (hn : ‖x - (r : AddCircle S)‖ ≤ a / 2) :
    ∃ p : ℤ, |p| ≤ (h : ℤ) ∧
      ‖x - ((r : AddCircle S) + (((p : ℝ) * b : ℝ) : AddCircle S))‖ ≤ b / 2 := by
  obtain ⟨v, rfl, hvn⟩ := exists_coe_eq_abs_sub_eq_norm_sub x r
  rw [← hvn] at hn
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (v - r) / b := ⟨_, rfl⟩
  have hvr : v - r = ρ * b := by rw [hρ]; field_simp
  rw [hvr, abs_mul, abs_of_pos hb, hab] at hn
  have hρ2 : 2 * |ρ| ≤ 2 * (h : ℝ) + 1 := by
    have : (2 * |ρ|) * b ≤ (2 * (h : ℝ) + 1) * b := by nlinarith
    exact le_of_mul_le_mul_right this hb
  obtain ⟨r1, r2⟩ := abs_le.1 (show |ρ| ≤ (h : ℝ) + 1 / 2 by linarith)
  obtain ⟨p, hp1, hp2, hp3⟩ : ∃ p : ℤ, |p| ≤ (h : ℤ) ∧ ρ - 1 / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ ρ + 1 / 2 := by
    by_cases e : ρ = -((h : ℝ) + 1 / 2)
    · refine ⟨-(h : ℤ), by simp, ?_, ?_⟩ <;> push_cast <;> linarith
    · have e' : -((h : ℝ) + 1 / 2) < ρ := lt_of_le_of_ne r1 (Ne.symm e)
      have c1 := Int.le_ceil (ρ - 1 / 2)
      have c2 := Int.ceil_lt_add_one (ρ - 1 / 2)
      refine ⟨⌈ρ - 1 / 2⌉, ?_, c1, by linarith⟩
      have d1 : ((⌈ρ - 1 / 2⌉ : ℤ) : ℝ) < (h : ℝ) + 1 := by linarith
      have d2 : -((h : ℝ) + 1) < ((⌈ρ - 1 / 2⌉ : ℤ) : ℝ) := by linarith
      have d1' : ⌈ρ - 1 / 2⌉ < (h : ℤ) + 1 := by exact_mod_cast d1
      have d2' : -((h : ℤ) + 1) < ⌈ρ - 1 / 2⌉ := by exact_mod_cast d2
      rw [abs_le]
      constructor <;> omega
  refine ⟨p, hp1, ?_⟩
  rw [← AddCircle.coe_add]
  refine (norm_coe_sub_coe_le _ _).trans ?_
  have e : v - (r + (p : ℝ) * b) = (ρ - p) * b := by linear_combination hvr
  rw [e, abs_mul, abs_of_pos hb]
  have : |ρ - (p : ℝ)| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith
theorem offset_injective {h : ℕ} {M : ℤ} (hS : S = (M : ℝ) * a)
    (hab : a = (2 * (h : ℝ) + 1) * b) (hb : 0 < b) {p p' : ℤ} (hp : |p| ≤ (h : ℤ))
    (hp' : |p'| ≤ (h : ℤ))
    (e : (((p : ℝ) * b : ℝ) : AddCircle S) = (((p' : ℝ) * b : ℝ) : AddCircle S)) : p = p' := by
  obtain ⟨l, hl⟩ := exists_eq_add_int_mul_of_coe_eq e
  rw [hS, hab] at hl
  have h1 : (p' : ℝ) = (p : ℝ) + (l : ℝ) * (M : ℝ) * (2 * (h : ℝ) + 1) := by
    have : ((p' : ℝ) - ((p : ℝ) + (l : ℝ) * (M : ℝ) * (2 * (h : ℝ) + 1))) * b = 0 := by
      linear_combination hl
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hb.ne'
  have h2 : p' - p = (l * M) * (2 * h + 1) := by
    have : p' = p + l * M * (2 * h + 1) := by exact_mod_cast h1
    rw [this]; ring
  have h3 : (2 * (h : ℤ) + 1) ∣ p' - p := ⟨l * M, by rw [h2]; ring⟩
  have h4 : |p' - p| < 2 * (h : ℤ) + 1 := by
    have := abs_sub p' p
    omega
  have := Int.eq_zero_of_abs_lt_dvd h3 h4
  omega
theorem setOf_onMesh_eq_image {M : ℕ} (hM : 0 < M) (hS : S = (M : ℝ) * a) :
    {c : AddCircle S | OnMesh S a c} =
      (fun n : ℕ => (((n : ℝ) * a : ℝ) : AddCircle S)) '' (Finset.range M : Set ℕ) := by
  ext c
  constructor
  · rintro ⟨n, rfl⟩
    have hM' : (0 : ℤ) < M := by exact_mod_cast hM
    refine ⟨(n % (M : ℤ)).toNat, ?_, ?_⟩
    · have h1 := Int.emod_lt_of_pos n hM'
      have h2 := Int.emod_nonneg n hM'.ne'
      simp only [Finset.coe_range, mem_Iio]
      omega
    · have h2 := Int.emod_nonneg n hM'.ne'
      have e1 : (((n % (M : ℤ)).toNat : ℕ) : ℤ) = n % (M : ℤ) := Int.toNat_of_nonneg h2
      have e2 : (((n % (M : ℤ)).toNat : ℕ) : ℝ) = ((n % (M : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast e1
      have e3 : (n : ℝ) = ((n % (M : ℤ) : ℤ) : ℝ) + ((n / (M : ℤ) : ℤ) : ℝ) * (M : ℝ) := by
        have := Int.emod_add_mul_ediv n (M : ℤ)
        have h3 : ((n % (M : ℤ) + (M : ℤ) * (n / (M : ℤ)) : ℤ) : ℝ) = (n : ℝ) := by
          exact_mod_cast this
        push_cast at h3
        linarith
      simp only
      rw [e2]
      have e4 : (n : ℝ) * a =
          ((n % (M : ℤ) : ℤ) : ℝ) * a + ((n / (M : ℤ) : ℤ) : ℝ) * S := by
        rw [hS]
        nth_rewrite 1 [e3]
        ring
      rw [e4, coe_add_int_mul_period]
  · rintro ⟨n, -, rfl⟩
    exact ⟨n, by simp⟩
theorem finite_setOf_onMesh {M : ℕ} (hM : 0 < M) (hS : S = (M : ℝ) * a) :
    {c : AddCircle S | OnMesh S a c}.Finite := by
  rw [setOf_onMesh_eq_image hM hS]
  exact (Finset.finite_toSet _).image _
end SupCubes
namespace SupCubes
variable {S a b : ℝ}
theorem torusSupNorm_eq_norm (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
def MeshPoints (S a : ℝ) : Set (Torus4 S) := {y | ∀ μ, OnMesh S a (y μ)}
def closedCube (a : ℝ) (y : Torus4 S) : Set (Torus4 S) := {x | ‖x - y‖ ≤ a / 2}
def openCube (a : ℝ) (y : Torus4 S) : Set (Torus4 S) := {x | ‖x - y‖ < a / 2}
theorem mem_closedCube_iff (ha : 0 < a) {x y : Torus4 S} :
    x ∈ closedCube a y ↔ ∀ μ, ‖x μ - y μ‖ ≤ a / 2 :=
  pi_norm_le_iff_of_nonneg (half_pos ha).le
theorem isOpen_openCube (y : Torus4 S) : IsOpen (openCube a y) :=
  isOpen_lt (by fun_prop) continuous_const
theorem isClosed_closedCube (y : Torus4 S) : IsClosed (closedCube a y) :=
  isClosed_le (by fun_prop) continuous_const
def offsetPoint (b : ℝ) (y : Torus4 S) (p : Fin 4 → ℤ) : Torus4 S :=
  fun μ => y μ + (((p μ : ℝ) * b : ℝ) : AddCircle S)
def offsetBox (h : ℕ) : Set (Fin 4 → ℤ) := {p | ∀ μ, |p μ| ≤ (h : ℤ)}
section NestedMeshes
variable {h : ℕ} {M : ℤ} (hS : S = (M : ℝ) * a) (hab : a = (2 * (h : ℝ) + 1) * b) (hb : 0 < b)
include hab hb in
theorem pos_of_odd_mul : 0 < a := by
  rw [hab]; positivity
include hS hab hb in
theorem offsetPoint_injOn (y : Torus4 S) : InjOn (offsetPoint b y) (offsetBox h) := by
  intro p hp p' hp' e
  funext μ
  exact offset_injective hS hab hb (hp μ) (hp' μ)
    (add_left_cancel (congrFun e μ))
end NestedMeshes
end SupCubes
namespace SupCubes
variable {S a b : ℝ}
def cubeFamily (S a : ℝ) : Set (Set (Torus4 S)) := {Q | ∃ y ∈ MeshPoints S a, Q = closedCube a y}
def IsCubeUnion (S a : ℝ) (X : Set (Torus4 S)) : Prop := ∃ C ⊆ cubeFamily S a, X = ⋃₀ C
def cubeComplement (S a : ℝ) (X : Set (Torus4 S)) : Set (Torus4 S) :=
  ⋃₀ {Q | Q ∈ cubeFamily S a ∧ ¬Q ⊆ X}
theorem meshPoints_finite {N : ℕ} (hN : 0 < N) (hS : S = (N : ℝ) * a) :
    (MeshPoints S a).Finite := by
  have : MeshPoints S a = Set.pi univ fun _ => {c : AddCircle S | OnMesh S a c} := by
    ext y
    simp only [Set.mem_pi, mem_univ, true_implies]
    exact Iff.rfl
  rw [this]
  exact Set.Finite.pi fun _ => finite_setOf_onMesh hN hS
theorem cubeFamily_finite {N : ℕ} (hN : 0 < N) (hS : S = (N : ℝ) * a) :
    (cubeFamily S a).Finite := by
  have : cubeFamily S a = closedCube a '' MeshPoints S a := by
    ext Q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [this]
  exact (meshPoints_finite hN hS).image _
theorem IsCubeUnion.isClosed {N : ℕ} (hN : 0 < N) (hS : S = (N : ℝ) * a) {X : Set (Torus4 S)}
    (hX : IsCubeUnion S a X) : IsClosed X := by
  obtain ⟨C, hC, rfl⟩ := hX
  rw [sUnion_eq_biUnion]
  refine Set.Finite.isClosed_biUnion (Set.Finite.subset (cubeFamily_finite hN hS) hC) fun Q hQ => ?_
  obtain ⟨y, -, rfl⟩ := hC hQ
  exact isClosed_closedCube y
section CubeUnions
variable {h : ℕ} {M : ℤ} (hS : S = (M : ℝ) * a) (hab : a = (2 * (h : ℝ) + 1) * b) (hb : 0 < b)
  {X : Set (Torus4 S)} (hX : IsCubeUnion S a X)
end CubeUnions
end SupCubes
open PeriodicLattice
namespace SupCubes
variable (D : SeparatedSequences.BaseParameters)
def orderSide (i : ℕ) : ℝ := meshSize D.L (levelDepth D.K i)
def unitFactor : ℝ := (D.L : ℝ) ^ levelDepth D.K D.t
theorem base_pos : (0 : ℝ) < D.L := Nat.cast_pos.2 (by have := D.three_le_L; omega)
theorem unitFactor_pos : 0 < unitFactor D := zpow_pos (base_pos D) _
theorem orderMesh_eq (i : ℕ) : D.orderMesh i = unitFactor D * orderSide D i := by
  have hL : (D.L : ℝ) ≠ 0 := (base_pos D).ne'
  show (D.L : ℝ) ^ i * (D.L : ℝ) ^ (((0 : ℕ) : ℤ) - (D.t : ℤ)) =
    (D.L : ℝ) ^ levelDepth D.K D.t * (D.L : ℝ) ^ (-(levelDepth D.K i))
  rw [← zpow_natCast (D.L : ℝ) i, ← zpow_add₀ hL, ← zpow_add₀ hL]
  congr 1
  simp only [levelDepth]
  push_cast
  ring
theorem torusSide_eq {i : ℕ} (hi : i ≤ D.m + D.K) :
    torusSide D.L D.m = ((2 * D.L ^ (D.m + D.K - i) : ℕ) : ℝ) * orderSide D i := by
  have hL : (D.L : ℝ) ≠ 0 := (base_pos D).ne'
  show 2 * (D.L : ℝ) ^ D.m = ((2 * D.L ^ (D.m + D.K - i) : ℕ) : ℝ) *
    (D.L : ℝ) ^ (-(levelDepth D.K i))
  push_cast
  rw [← zpow_natCast (D.L : ℝ) D.m, ← zpow_natCast (D.L : ℝ) (D.m + D.K - i), mul_assoc,
    ← zpow_add₀ hL]
  congr 2
  simp only [levelDepth]
  omega
variable {D}
theorem exists_isLevelLift (x : D.Torus) : ∃ w, IsLevelLift D.L D.m D.K D.t x w := by
  choose r hr _ using fun ν => exists_coe_eq_abs_sub_eq_norm_sub (x ν) 0
  exact ⟨fun μ => unitFactor D * r μ, r, hr, fun μ => rfl⟩
theorem torusClassOf_apply (w : Fin 4 → ℝ) (μ : Fin 4) :
    torusClassOf D.L D.m D.K D.t w μ =
      ((w μ / unitFactor D : ℝ) : AddCircle (torusSide D.L D.m)) := by
  have hex : ∃ x, IsLevelLift D.L D.m D.K D.t x w := by
    refine ⟨fun μ => ((w μ / unitFactor D : ℝ) : AddCircle (torusSide D.L D.m)),
      fun μ => w μ / unitFactor D, fun μ => rfl, fun μ => ?_⟩
    have e : toLevelUnits D.L D.K D.t (w μ / unitFactor D) =
      unitFactor D * (w μ / unitFactor D) := rfl
    rw [e]
    field_simp [(unitFactor_pos D).ne']
  obtain ⟨v, hv, hw⟩ := Classical.epsilon_spec hex
  show Classical.epsilon (fun x => IsLevelLift D.L D.m D.K D.t x w) μ = _
  rw [← hv μ]
  congr 1
  have e : w μ = unitFactor D * v μ := hw μ
  rw [e]
  field_simp [(unitFactor_pos D).ne']
theorem shiftBy_apply (y : D.Torus) (r : Fin 4 → ℝ) (μ : Fin 4) :
    shiftBy D.L D.m D.K D.t y r μ =
      y μ + ((r μ / unitFactor D : ℝ) : AddCircle (torusSide D.L D.m)) := by
  obtain ⟨v, hv, hw⟩ := Classical.epsilon_spec (exists_isLevelLift y)
  show torusClassOf D.L D.m D.K D.t (Classical.epsilon (IsLevelLift D.L D.m D.K D.t y) + r) μ = _
  rw [torusClassOf_apply, Pi.add_apply, add_div, AddCircle.coe_add]
  congr 1
  rw [← hv μ]
  congr 1
  have e : Classical.epsilon (IsLevelLift D.L D.m D.K D.t y) μ = unitFactor D * v μ := hw μ
  rw [e]
  field_simp [(unitFactor_pos D).ne']
theorem shiftedPoint_eq (i' : ℕ) (y : D.Torus) (n : Fin 4 → ℤ) :
    D.shiftedPoint i' y n = offsetPoint (orderSide D i') y n := by
  funext μ
  rw [SeparatedSequences.BaseParameters.shiftedPoint, shiftBy_apply]
  simp only [offsetPoint]
  congr 2
  have e : (D.orderMesh i' • ∑ ν, (n ν : ℝ) • coordVec ν) μ =
      D.orderMesh i' * (n μ : ℝ) := by
    simp [coordVec, Finset.sum_apply, Pi.single_apply]
  rw [e, orderMesh_eq]
  field_simp [(unitFactor_pos D).ne']
end SupCubes
namespace SupCubes
variable {D : SeparatedSequences.BaseParameters}
theorem blockPartitionIndex_eq (n : ℕ) :
    D.scales.blockPartitionIndex n = levelDepth D.K (n + D.blockExp) := by
  show levelDepth D.K n - (D.blockExp : ℤ) = _
  simp only [levelDepth]
  push_cast
  ring
end SupCubes
namespace SupCubes
variable {D : SeparatedSequences.BaseParameters} {Ω : ℕ → Set D.Torus}
theorem memberAt_of_le {n : ℕ} (h : n ≤ D.t) : D.memberAt Ω n = Ω n := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.memberAt_of_le <;> assumption
theorem layerSet_of_lt {n : ℕ} (h : n < D.t) :
    SeparatedSequences.layerSet D.scales Ω n = closure (Ω n \ Ω (n + 1)) := by
  unfold SeparatedSequences.layerSet
  exact if_pos h
theorem layerSet_of_gt {n : ℕ} (h : D.t < n) : SeparatedSequences.layerSet D.scales Ω n = ∅ := by
  unfold SeparatedSequences.layerSet
  have h1 : ¬n < D.scales.top := not_lt.2 h.le
  have h2 : ¬n = D.scales.top := h.ne'
  rw [if_neg h1, if_neg h2]
end SupCubes
open PeriodicLattice
end YangMills.Construction
end
