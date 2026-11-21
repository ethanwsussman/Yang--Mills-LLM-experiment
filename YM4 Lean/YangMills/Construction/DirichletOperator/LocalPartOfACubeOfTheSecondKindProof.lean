import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefectsProof
import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.LeibnizRulesAndHolderSeminormsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Dirichlet (unitStep forwardDiff)
open Torus (torusProj supNorm lOneNorm supSetDist scaleSpacing PeriodicTorus)
open RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace SecondTypeCubeCommutator
section TorusLengths
variable {S : ℝ}
theorem torusProj_sub (v w : Fin 4 → ℝ) :
    torusProj 4 S (v - w) = torusProj 4 S v - torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
theorem exists_torusProj_eq (p : PeriodicTorus 4 S) : ∃ v : Fin 4 → ℝ, torusProj 4 S v = p := by apply _root_.YangMills.Construction.PartitionCubes.FiniteDifference.exists_torusProj_eq <;> assumption
theorem supNorm_le_norm_of_torusProj_eq {p : PeriodicTorus 4 S} {v : Fin 4 → ℝ}
    (h : torusProj 4 S v = p) : supNorm p ≤ ‖v‖ := by apply _root_.YangMills.Construction.LeibnizHolder.supNorm_le_norm_lift <;> assumption
theorem lOneNorm_le_sum_abs_of_torusProj_eq {p : PeriodicTorus 4 S} {v : Fin 4 → ℝ}
    (h : torusProj 4 S v = p) : lOneNorm p ≤ ∑ μ, |v μ| :=
  csInf_le ⟨0, by
    rintro _ ⟨w, -, rfl⟩
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _⟩ ⟨v, h, rfl⟩
theorem supNorm_add_le (p q : PeriodicTorus 4 S) : supNorm (p + q) ≤ supNorm p + supNorm q := by apply _root_.YangMills.Construction.PartitionCubes.PartitionFnSupport.torusSupNorm_add_le <;> assumption
theorem supNorm_zero_nonpos : supNorm (0 : PeriodicTorus 4 S) ≤ 0 := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_zero_le <;> assumption
theorem supSetDist_singleton_le {X : Set (PeriodicTorus 4 S)} {y s : PeriodicTorus 4 S}
    (hs : s ∈ X) : supSetDist {y} X ≤ ENNReal.ofReal (supNorm (y - s)) :=
  iInf₂_le_of_le y rfl (iInf₂_le s hs)
end TorusLengths
section PlaquetteEdges
variable {𝒮 : NestedRegions}
def plaqEdge (p : 𝒮.FinePlaquette) : Fin 4 → 𝒮.FineBond
  | 0 => ⟨p.1 + unitStep 4 𝒮.side 𝒮.ξ p.2.1.1, p.2.1.2⟩
  | 1 => ⟨p.1, p.2.1.2⟩
  | 2 => ⟨p.1 + unitStep 4 𝒮.side 𝒮.ξ p.2.1.2, p.2.1.1⟩
  | 3 => ⟨p.1, p.2.1.1⟩
def plaqEdgeSign : Fin 4 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => 1
def plaqEdgeOffset (p : 𝒮.FinePlaquette) : Fin 4 → Fin 4 → ℝ
  | 0 => Pi.single p.2.1.1 𝒮.ξ
  | 1 => 0
  | 2 => Pi.single p.2.1.2 𝒮.ξ
  | 3 => 0
theorem abs_plaqEdgeSign (i : Fin 4) : |plaqEdgeSign i| = 1 := by
  fin_cases i <;> simp [plaqEdgeSign]
theorem plaqEdge_source (p : 𝒮.FinePlaquette) (i : Fin 4) :
    ((plaqEdge p i).source : 𝒮.Point) = (p.1 : 𝒮.Point) + torusProj 4 𝒮.side (plaqEdgeOffset p i) := by
  fin_cases i
  · rfl
  · show (p.1 : 𝒮.Point) = (p.1 : 𝒮.Point) + torusProj 4 𝒮.side 0
    have : torusProj 4 𝒮.side (0 : Fin 4 → ℝ) = 0 := by funext μ; simp [torusProj]
    rw [this, add_zero]
  · rfl
  · show (p.1 : 𝒮.Point) = (p.1 : 𝒮.Point) + torusProj 4 𝒮.side 0
    have : torusProj 4 𝒮.side (0 : Fin 4 → ℝ) = 0 := by funext μ; simp [torusProj]
    rw [this, add_zero]
theorem norm_plaqEdgeOffset_le (p : 𝒮.FinePlaquette) (i : Fin 4) : ‖plaqEdgeOffset p i‖ ≤ 𝒮.ξ := by
  have hξ := 𝒮.ξ_pos
  fin_cases i
  · show ‖(Pi.single p.2.1.1 𝒮.ξ : Fin 4 → ℝ)‖ ≤ 𝒮.ξ
    rw [Pi.norm_single, Real.norm_eq_abs, abs_of_pos hξ]
  · show ‖(0 : Fin 4 → ℝ)‖ ≤ 𝒮.ξ
    simpa using hξ.le
  · show ‖(Pi.single p.2.1.2 𝒮.ξ : Fin 4 → ℝ)‖ ≤ 𝒮.ξ
    rw [Pi.norm_single, Real.norm_eq_abs, abs_of_pos hξ]
  · show ‖(0 : Fin 4 → ℝ)‖ ≤ 𝒮.ξ
    simpa using hξ.le
theorem sum_abs_pi_single (μ : Fin 4) (a : ℝ) :
    ∑ ν, |(Pi.single μ a : Fin 4 → ℝ) ν| = |a| := by
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ h
    simp [Pi.single_eq_of_ne h]
  · simp
theorem sum_abs_plaqEdgeOffset_le (p : 𝒮.FinePlaquette) (i : Fin 4) :
    ∑ ν, |plaqEdgeOffset p i ν| ≤ 𝒮.ξ := by
  have hξ := 𝒮.ξ_pos
  fin_cases i
  · show ∑ ν, |(Pi.single p.2.1.1 𝒮.ξ : Fin 4 → ℝ) ν| ≤ 𝒮.ξ
    rw [sum_abs_pi_single, abs_of_pos hξ]
  · show ∑ ν, |(0 : Fin 4 → ℝ) ν| ≤ 𝒮.ξ
    simpa using hξ.le
  · show ∑ ν, |(Pi.single p.2.1.2 𝒮.ξ : Fin 4 → ℝ) ν| ≤ 𝒮.ξ
    rw [sum_abs_pi_single, abs_of_pos hξ]
  · show ∑ ν, |(0 : Fin 4 → ℝ) ν| ≤ 𝒮.ξ
    simpa using hξ.le
theorem plaqEdge_source_sub_source (p : 𝒮.FinePlaquette) (i j : Fin 4) :
    ((plaqEdge p j).source : 𝒮.Point) - ((plaqEdge p i).source : 𝒮.Point) =
      torusProj 4 𝒮.side (plaqEdgeOffset p j - plaqEdgeOffset p i) := by
  rw [plaqEdge_source, plaqEdge_source, torusProj_sub]
  abel
theorem supNorm_plaqEdge_sub_le (p : 𝒮.FinePlaquette) (i j : Fin 4) :
    supNorm (((plaqEdge p j).source : 𝒮.Point) - ((plaqEdge p i).source : 𝒮.Point)) ≤ 2 * 𝒮.ξ := by
  refine (supNorm_le_norm_of_torusProj_eq (plaqEdge_source_sub_source p i j).symm).trans ?_
  linarith [norm_sub_le (plaqEdgeOffset p j) (plaqEdgeOffset p i), norm_plaqEdgeOffset_le p i,
    norm_plaqEdgeOffset_le p j]
theorem lOneNorm_plaqEdge_sub_le (p : 𝒮.FinePlaquette) (i j : Fin 4) :
    lOneNorm (((plaqEdge p j).source : 𝒮.Point) - ((plaqEdge p i).source : 𝒮.Point)) ≤ 2 * 𝒮.ξ := by
  refine (lOneNorm_le_sum_abs_of_torusProj_eq (plaqEdge_source_sub_source p i j).symm).trans ?_
  have h : ∑ ν, |(plaqEdgeOffset p j - plaqEdgeOffset p i) ν| ≤
      ∑ ν, |plaqEdgeOffset p j ν| + ∑ ν, |plaqEdgeOffset p i ν| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun ν _ => abs_sub _ _
  linarith [sum_abs_plaqEdgeOffset_le p i, sum_abs_plaqEdgeOffset_le p j]
theorem plaqEdge_injective (p p' : 𝒮.FinePlaquette) (i : Fin 4) (hq : p.2 = p'.2)
    (h : plaqEdge p i = plaqEdge p' i) : p = p' := by
  obtain ⟨x, q⟩ := p
  obtain ⟨x', q'⟩ := p'
  simp only at hq
  subst hq
  have hx : x = x' := by
    fin_cases i
    · have := congrArg Dirichlet.LatticeBond.source h
      exact add_right_cancel this
    · exact congrArg Dirichlet.LatticeBond.source h
    · have := congrArg Dirichlet.LatticeBond.source h
      exact add_right_cancel this
    · exact congrArg Dirichlet.LatticeBond.source h
  rw [hx]
end PlaquetteEdges
section CurlCurlMatrix
variable {𝒮 : NestedRegions} [Fintype 𝒮.FineSite] [Fintype 𝒮.FineBond]
open Classical in
def plaqIncidence (p : 𝒮.FinePlaquette) (b : 𝒮.FineBond) : ℝ :=
  ∑ i, if plaqEdge p i = b then plaqEdgeSign i else 0
def curlCurlMatrix (b b' : 𝒮.FineBond) : ℝ :=
  (𝒮.ξ ^ 2)⁻¹ * ∑ p : 𝒮.FinePlaquette, plaqIncidence p b * plaqIncidence p b'
theorem bondInner_eq_sum (A A' : 𝒮.FineBond → ℝ) :
    bondInner A A' = 𝒮.ξ ^ 4 * ∑ b, A b * A' b := by
  rw [RegionSequence.NestedRegions.bondInner, finsum_eq_sum_of_fintype]
theorem eq_of_bondInner_eq {X : Submodule ℝ (𝒮.FineBond → ℝ)} {v w : 𝒮.FineBond → ℝ}
    (hv : v ∈ X) (hw : w ∈ X) (h : ∀ u ∈ X, bondInner v u = bondInner w u) : v = w := by
  have h0 := h (v - w) (X.sub_mem hv hw)
  rw [bondInner_eq_sum, bondInner_eq_sum] at h0
  have hξ : 𝒮.ξ ^ 4 ≠ 0 := pow_ne_zero _ 𝒮.ξ_pos.ne'
  have h1 := mul_left_cancel₀ hξ h0
  have h2 : ∑ b, (v b - w b) ^ 2 = 0 := by
    have e : ∑ b, (v b - w b) ^ 2 =
        ∑ b, v b * (v - w) b - ∑ b, w b * (v - w) b := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.sub_apply]
      ring
    rw [e, h1, sub_self]
  funext b
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => sq_nonneg (v b - w b)).1 h2 b
    (Finset.mem_univ b)
  exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 h3)
theorem curlCurlMatrix_comm (b b' : 𝒮.FineBond) : curlCurlMatrix b b' = curlCurlMatrix b' b := by
  simp only [curlCurlMatrix, mul_comm (plaqIncidence _ b) (plaqIncidence _ b')]
theorem exists_plaqEdge_of_curlCurlMatrix_ne_zero {b b' : 𝒮.FineBond}
    (h : curlCurlMatrix b b' ≠ 0) :
    ∃ (p : 𝒮.FinePlaquette) (i j : Fin 4), plaqEdge p i = b ∧ plaqEdge p j = b' := by
  classical
  by_contra hn
  apply h
  have hz : ∀ p : 𝒮.FinePlaquette, plaqIncidence p b * plaqIncidence p b' = 0 := by
    intro p
    by_cases h₁ : ∃ i, plaqEdge p i = b
    · by_cases h₂ : ∃ j, plaqEdge p j = b'
      · obtain ⟨i, hi⟩ := h₁
        obtain ⟨j, hj⟩ := h₂
        exact absurd ⟨p, i, j, hi, hj⟩ hn
      · have : plaqIncidence p b' = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [if_neg fun hj => h₂ ⟨j, hj⟩]
        rw [this, mul_zero]
    · have : plaqIncidence p b = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg fun hj => h₁ ⟨j, hj⟩]
      rw [this, zero_mul]
  simp [curlCurlMatrix, hz]
open Classical in
theorem abs_plaqIncidence_le (p : 𝒮.FinePlaquette) (b : 𝒮.FineBond) :
    |plaqIncidence p b| ≤ ∑ i, if plaqEdge p i = b then (1 : ℝ) else 0 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  split_ifs
  · rw [abs_plaqEdgeSign]
  · simp
theorem sum_abs_plaqIncidence_bonds_le (p : 𝒮.FinePlaquette) : ∑ b, |plaqIncidence p b| ≤ 4 := by
  classical
  refine (Finset.sum_le_sum fun b _ => abs_plaqIncidence_le p b).trans ?_
  rw [Finset.sum_comm]
  simp
theorem sum_abs_plaqIncidence_plaqs_le (b : 𝒮.FineBond) :
    ∑ p : 𝒮.FinePlaquette, |plaqIncidence p b| ≤ 64 := by
  classical
  refine (Finset.sum_le_sum fun p _ => abs_plaqIncidence_le p b).trans ?_
  rw [Finset.sum_comm]
  have hone : ∀ (i : Fin 4) (q : {p : Fin 4 × Fin 4 // p.1 < p.2}),
      ∑ x : 𝒮.FineSite,
        (if plaqEdge ((x, q) : 𝒮.FinePlaquette) i = b then (1 : ℝ) else 0) ≤ 1 := by
    intro i q
    rw [Finset.sum_boole]
    have hc : (Finset.univ.filter fun x : 𝒮.FineSite =>
        plaqEdge ((x, q) : 𝒮.FinePlaquette) i = b).card ≤ 1 := by
      refine Finset.card_le_one.2 fun x hx y hy => ?_
      have hx' := (Finset.mem_filter.1 hx).2
      have hy' := (Finset.mem_filter.1 hy).2
      have := plaqEdge_injective ((x, q) : 𝒮.FinePlaquette) (y, q) i rfl (hx'.trans hy'.symm)
      exact congrArg Prod.fst this
    exact_mod_cast hc
  have hcard : (Fintype.card {p : Fin 4 × Fin 4 // p.1 < p.2} : ℝ) ≤ 16 := by
    have : Fintype.card {p : Fin 4 × Fin 4 // p.1 < p.2} ≤ Fintype.card (Fin 4 × Fin 4) :=
      Fintype.card_subtype_le _
    have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
    rw [h2] at this
    exact_mod_cast this
  have hi : ∀ i : Fin 4,
      ∑ p : 𝒮.FinePlaquette, (if plaqEdge p i = b then (1 : ℝ) else 0) ≤ 16 := by
    intro i
    rw [Fintype.sum_prod_type_right]
    refine (Finset.sum_le_sum fun q _ => hone i q).trans ?_
    simpa using hcard
  refine (Finset.sum_le_sum fun i _ => hi i).trans ?_
  simp
  norm_num
theorem sum_abs_curlCurlMatrix_le (b : 𝒮.FineBond) :
    ∑ b', |curlCurlMatrix b b'| ≤ 256 * (𝒮.ξ ^ 2)⁻¹ := by
  have hξ : 0 ≤ (𝒮.ξ ^ 2)⁻¹ := by positivity
  have h₁ : ∀ b', |curlCurlMatrix b b'| ≤
      (𝒮.ξ ^ 2)⁻¹ * ∑ p : 𝒮.FinePlaquette, |plaqIncidence p b| * |plaqIncidence p b'| := by
    intro b'
    rw [curlCurlMatrix, abs_mul, abs_of_nonneg hξ]
    refine mul_le_mul_of_nonneg_left ?_ hξ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    simp only [abs_mul]
  refine (Finset.sum_le_sum fun b' _ => h₁ b').trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hξ
  have h₂ : ∀ p : 𝒮.FinePlaquette, ∑ b', |plaqIncidence p b| * |plaqIncidence p b'| ≤
      |plaqIncidence p b| * 4 := by
    intro p
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_abs_plaqIncidence_bonds_le p) (abs_nonneg _)
  refine (Finset.sum_le_sum fun p _ => h₂ p).trans ?_
  rw [← Finset.sum_mul]
  linarith [sum_abs_plaqIncidence_plaqs_le b]
end CurlCurlMatrix
section SchurTest
variable {𝒮 : NestedRegions} [Fintype 𝒮.FineSite] [Fintype 𝒮.FineBond]
end SchurTest
section PartitionCommutator
variable {𝒮 : NestedRegions} {M : ℕ} [Fintype 𝒮.FineSite] [Fintype 𝒮.FineBond]
def sourceValue (Q : LevelCube 𝒮 M) (b : 𝒮.FineBond) : ℝ := Q.partitionFn (b.source : 𝒮.Point)
def commKernel (Q : LevelCube 𝒮 M) (b b' : 𝒮.FineBond) : ℝ :=
  curlCurlMatrix b b' * (sourceValue Q b - sourceValue Q b')
theorem commKernel_swap (Q : LevelCube 𝒮 M) (b b' : 𝒮.FineBond) :
    commKernel Q b' b = -commKernel Q b b' := by
  simp only [commKernel, curlCurlMatrix_comm b' b]
  ring
structure SecondTypeData (Q : LevelCube 𝒮 M) (c : ℝ) : Prop where
  isSecondType : Q.IsSecondType
  pow_five_le : 𝒮.L ^ 5 ≤ M
  one_le_const : 1 ≤ c
  geometry : CubeGeometry.GeometryHolds 𝒮 M c
namespace SecondTypeData
variable {Q : LevelCube 𝒮 M} {c : ℝ} (D : SecondTypeData Q c)
include D
theorem level_eq : Q.level = 0 := D.isSecondType.1.1
theorem mem_active : Q ∈ active 𝒮 M := ⟨0, Nat.zero_le _, D.isSecondType.1⟩
theorem scale_level : 𝒮.scale Q.level = 𝒮.ξ := by
  rw [D.level_eq]
  simp [RegionSequence.NestedRegions.scale, scaleSpacing]
theorem scale_level_succ : 𝒮.scale (Q.level + 1) = (𝒮.L : ℝ) * 𝒮.ξ := by
  rw [D.level_eq]
  simp [RegionSequence.NestedRegions.scale, scaleSpacing]
theorem cubeSide_eq : cubeSide 𝒮 M Q.level = (M : ℝ) * 𝒮.ξ := by
  rw [cubeSide, D.scale_level]
theorem mollifyRadius_eq : mollifyRadius 𝒮 M Q.level = (M : ℝ) * 𝒮.ξ / (6 * (𝒮.L : ℝ)) := by
  rw [mollifyRadius, D.cubeSide_eq]
theorem thirteen_le_L : (13 : ℝ) ≤ 𝒮.L := by exact_mod_cast 𝒮.thirteen_le_L
theorem M_lower : 72 * (𝒮.L : ℝ) ^ 2 ≤ M := by
  have h13 := D.thirteen_le_L
  have h5 : (𝒮.L : ℝ) ^ 5 ≤ M := by exact_mod_cast D.pow_five_le
  have h3 : (72 : ℝ) ≤ (𝒮.L : ℝ) ^ 3 := by
    have : (13 : ℝ) ^ 3 ≤ (𝒮.L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h13 3
    linarith
  nlinarith
theorem four_ξ_le_thicken : 4 * 𝒮.ξ ≤ 5 / 6 * mollifyRadius 𝒮 M Q.level := by
  have h13 := D.thirteen_le_L
  have hM := D.M_lower
  have hξ := 𝒮.ξ_pos
  have e : 5 / 6 * ((M : ℝ) * 𝒮.ξ / (6 * (𝒮.L : ℝ))) =
      5 * (M : ℝ) * 𝒮.ξ / (36 * (𝒮.L : ℝ)) := by
    field_simp
    ring
  rw [D.mollifyRadius_eq, e, le_div_iff₀ (by positivity)]
  have h : 144 * (𝒮.L : ℝ) ≤ 5 * M := by nlinarith
  nlinarith
theorem mem_thicken {y s : 𝒮.Point} (hs : s ∈ Q.supp) (h : supNorm (y - s) ≤ 4 * 𝒮.ξ) :
    y ∈ Q.thicken (5 / 6) :=
  (supSetDist_singleton_le hs).trans (ENNReal.ofReal_le_ofReal (h.trans D.four_ξ_le_thicken))
omit D in
theorem sources_near {b b' : 𝒮.FineBond} (h : curlCurlMatrix b b' ≠ 0) :
    supNorm ((b'.source : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 2 * 𝒮.ξ ∧
      lOneNorm ((b'.source : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 2 * 𝒮.ξ := by
  obtain ⟨p, i, j, rfl, rfl⟩ := exists_plaqEdge_of_curlCurlMatrix_ne_zero h
  exact ⟨supNorm_plaqEdge_sub_le p i j, lOneNorm_plaqEdge_sub_le p i j⟩
theorem abs_commKernel_le (b b' : 𝒮.FineBond) :
    |commKernel Q b b'| ≤ |curlCurlMatrix b b'| * (12 * c * (𝒮.L : ℝ) / (M : ℝ)) := by
  rw [commKernel, abs_mul]
  by_cases hK : curlCurlMatrix b b' = 0
  · simp [hK]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h13 := D.thirteen_le_L
  have hM := D.M_lower
  have hξ := 𝒮.ξ_pos
  have hc := D.one_le_const
  have hMp : (0 : ℝ) < M := by nlinarith
  have hlip := (D.geometry.partition.partition_bounded Q).lipschitz (b'.source : 𝒮.Point)
    (b.source : 𝒮.Point)
  have hone := (sources_near hK).2
  have hr : 0 ≤ c * (mollifyRadius 𝒮 M Q.level)⁻¹ := by
    rw [D.mollifyRadius_eq]
    positivity
  have e : c * (mollifyRadius 𝒮 M Q.level)⁻¹ * (2 * 𝒮.ξ) = 12 * c * (𝒮.L : ℝ) / (M : ℝ) := by
    rw [D.mollifyRadius_eq]
    field_simp
    ring
  rw [abs_sub_comm]
  calc |sourceValue Q b' - sourceValue Q b| ≤ c * (mollifyRadius 𝒮 M Q.level)⁻¹ *
        lOneNorm ((b'.source : 𝒮.Point) - (b.source : 𝒮.Point)) := hlip
    _ ≤ c * (mollifyRadius 𝒮 M Q.level)⁻¹ * (2 * 𝒮.ξ) := mul_le_mul_of_nonneg_left hone hr
    _ = _ := e
theorem row_sum_le (b : 𝒮.FineBond) :
    ∑ b', |commKernel Q b b'| ≤ 3072 * c * (𝒮.L : ℝ) * (M : ℝ)⁻¹ * (𝒮.ξ ^ 2)⁻¹ := by
  have h13 := D.thirteen_le_L
  have hM := D.M_lower
  have hc := D.one_le_const
  have hMp : (0 : ℝ) < M := by nlinarith
  have hf : 0 ≤ 12 * c * (𝒮.L : ℝ) / (M : ℝ) := by positivity
  refine (Finset.sum_le_sum fun b' _ => D.abs_commKernel_le b b').trans ?_
  rw [← Finset.sum_mul]
  refine (mul_le_mul_of_nonneg_right (sum_abs_curlCurlMatrix_le b) hf).trans (le_of_eq ?_)
  rw [div_eq_mul_inv]
  ring
theorem column_sum_le (b' : 𝒮.FineBond) :
    ∑ b, |commKernel Q b b'| ≤ 3072 * c * (𝒮.L : ℝ) * (M : ℝ)⁻¹ * (𝒮.ξ ^ 2)⁻¹ := by
  refine le_trans (le_of_eq ?_) (D.row_sum_le b')
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [commKernel_swap Q b b', abs_neg]
end SecondTypeData
end PartitionCommutator
section SecondType
variable {𝒮 : NestedRegions} {M : ℕ} [Fintype 𝒮.FineSite] [Fintype 𝒮.FineBond]
theorem mapSite_secondType (Q : LevelCube 𝒮 M) (x : 𝒮.FineSite) :
    (Q.secondTypeSystem.mapSite x : 𝒮.FineSite) = x := by
  have h : ∃ y : 𝒮.FineSite, (y : 𝒮.Point) = (x : 𝒮.Point) := ⟨x, rfl⟩
  exact Subtype.ext (Classical.epsilon_spec h)
theorem mapBond_secondType (Q : LevelCube 𝒮 M) (b : 𝒮.FineBond) :
    (Q.secondTypeSystem.mapBond b : 𝒮.FineBond) = b := by
  obtain ⟨x, μ⟩ := b
  show (⟨(Q.secondTypeSystem.mapSite x : 𝒮.FineSite), μ⟩ : 𝒮.FineBond) = ⟨x, μ⟩
  rw [mapSite_secondType]
variable {Q : LevelCube 𝒮 M} {c : ℝ}
namespace SecondTypeData
variable (D : SecondTypeData Q c)
include D
end SecondTypeData
end SecondType
section SystemFacts
variable {𝒮 : NestedRegions} {M : ℕ}
variable [Fintype 𝒮.FineSite] [Fintype 𝒮.FineBond] {Q : LevelCube 𝒮 M} {c : ℝ}
end SystemFacts
theorem finite_fineSite (𝒮 : NestedRegions) : Finite 𝒮.FineSite := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineSite <;> assumption
end SecondTypeCubeCommutator
end YangMills.Construction
