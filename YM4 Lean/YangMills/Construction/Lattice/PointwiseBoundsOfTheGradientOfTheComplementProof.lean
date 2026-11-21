import YangMills.Construction.Lattice.DecayingOneFormHolderBoundProof
import YangMills.Construction.Lattice.LaplacianOfTheComplementOnBlocks
import YangMills.Construction.Lattice.LiftsOfTheTorusInEveryDimension
import YangMills.Construction.Lattice.OneScaleGreenOperatorOnCornerCubesProof
import YangMills.Construction.Lattice.PoissonEstimatesOnTheTorus
import YangMills.Construction.Lattice.SetsOfSitesInEveryDimension
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice.GradComplPointwise
open ScaledFun
variable {d N : ℕ}
section Norms
variable {s : Mesh N} {ι : Type}
theorem normAt_le [Fintype ι] [Nonempty ι] {f : MultiField d s ι} {x : GridPoint d s} {K : ℝ}
    (h : ∀ i, |f (i, x)| ≤ K) : MultiField.normAt f x ≤ K :=
  ciSup_le h
theorem normAt_nonneg [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) :
    0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem maxNorm_nonneg [Fintype ι] (f : MultiField d s ι) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun x => normAt_nonneg f x
theorem siteFun_maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem siteFun_restrictTo_apply (Y : Set (GridPoint d s)) (f : SiteFun d s) (z : GridPoint d s) :
    SiteFun.restrictTo Y f z = siteIndicator Y z * f z := rfl
theorem siteIndicator_of_mem {Y : Set (GridPoint d s)} {z : GridPoint d s} (h : z ∈ Y) :
    siteIndicator Y z = 1 := by
  simp [siteIndicator, h]
theorem siteIndicator_of_not_mem {Y : Set (GridPoint d s)} {z : GridPoint d s} (h : z ∉ Y) :
    siteIndicator Y z = 0 := by
  simp [siteIndicator, h]
theorem restrictTo_restrictTo (Y : Set (GridPoint d s)) (g : SiteFun d s) :
    SiteFun.restrictTo Y (SiteFun.restrictTo Y g) = SiteFun.restrictTo Y g := by
  refine ScaledFun.ext fun z => ?_
  rw [siteFun_restrictTo_apply, siteFun_restrictTo_apply]
  by_cases hz : z ∈ Y
  · rw [siteIndicator_of_mem hz, one_mul, one_mul]
  · rw [siteIndicator_of_not_mem hz, zero_mul, zero_mul]
def restrictToLinear (Y : Set (GridPoint d s)) : MultiField d s ι →ₗ[ℝ] MultiField d s ι where
  toFun := MultiField.restrictTo Y
  map_add' f g := ScaledFun.ext fun q => by
    obtain ⟨i, z⟩ := q
    change siteIndicator Y z * (f (i, z) + g (i, z)) =
      siteIndicator Y z * f (i, z) + siteIndicator Y z * g (i, z)
    ring
  map_smul' c f := ScaledFun.ext fun q => by
    obtain ⟨i, z⟩ := q
    change siteIndicator Y z * (c * f (i, z)) = c * (siteIndicator Y z * f (i, z))
    ring
end Norms
section Distances
theorem taxicabDist_comm (u v : Torus d N) : taxicabDist u v = taxicabDist v u := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem taxicabDist_triangle (u v w : Torus d N) :
    taxicabDist u w ≤ taxicabDist u v + taxicabDist v w := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_triangle <;> assumption
theorem taxicabDist_nonneg (u v : Torus d N) : 0 ≤ taxicabDist u v :=
  sum_nonneg fun _ _ => norm_nonneg _
theorem exp_taxicab_le {δ D : ℝ} (hδ : 0 ≤ δ) {a b u : Torus d N} (h : taxicabDist a b ≤ D) :
    Real.exp (-δ * taxicabDist a u) ≤ Real.exp (δ * D) * Real.exp (-δ * taxicabDist b u) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 := taxicabDist_triangle b a u
  rw [taxicabDist_comm b a] at h1
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans (add_le_add_left h _)) hδ]
theorem taxicabDist_sub_basisStep_le {s : Mesh N} (z : GridPoint d s) (μ : Fin d) :
    taxicabDist ((z - s.basisStep μ : GridPoint d s) : Torus d N) z ≤ s.h := by
  have h1 : ‖((s.h : ℝ) : AddCircle (N : ℝ))‖ ≤ s.h := by
    have := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (N : ℝ)) (m := s.h)
    rwa [Real.norm_eq_abs, abs_of_pos s.h_pos] at this
  unfold taxicabDist
  have h2 : ∀ ν : Fin d, ‖((z - s.basisStep μ : GridPoint d s) : Torus d N) ν - (z : Torus d N) ν‖ =
      if ν = μ then ‖((s.h : ℝ) : AddCircle (N : ℝ))‖ else 0 := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      simp [Mesh.basisStep, axisMultiple]
    · simp [Mesh.basisStep, axisMultiple, hν]
  simp only [h2]
  simpa using h1
theorem taxicabDist_add_basisStep_le {s : Mesh N} (z : GridPoint d s) (μ : Fin d) :
    taxicabDist ((z + s.basisStep μ : GridPoint d s) : Torus d N) z ≤ s.h := by apply _root_.YangMills.Construction.PeriodicLattice.OneFormHolder.taxicabDist_add_basisStep_le <;> assumption
end Distances
section SingleComponent
variable {s : Mesh N}
end SingleComponent
section Inputs
variable {L j : ℕ}
def weightRatio (d : ℕ) : ℝ := Real.exp (localBoundsRate d * (17 * (d : ℝ) + 1))
def cubeConst (d : ℕ) : ℝ :=
  |gaugeProjDecayPrefactor d| * Real.exp (2 * (d : ℝ)) * latticeExpSum d (localBoundsRate d)
def laplacianConst (d : ℕ) : ℝ :=
  4 ^ d * Real.sqrt (2 * (d : ℝ)) * (cubeConst d * weightRatio d)
structure Inputs (S : Scales d L j N) : Prop where
  rate_pos : 0 < localBoundsRate d
  rate_le : 2 * localBoundsRate d ≤ gaugeProjDecayConst d
  decay_le : gaugeProjDecayConst d ≤ 1
  decay : ∀ U U' : Set (GridPoint d S.fineMesh), U.Nonempty → U'.Nonempty →
    ∀ f : SiteFun d S.fineMesh,
    ‖MultiField.restrictTo U (discreteGrad S.fineMesh
        (S.singleScaleGaugeProjCompl (SiteFun.restrictTo U' f)))‖ ≤
      gaugeProjDecayPrefactor d * Real.exp (-gaugeProjDecayConst d * siteSetDist U U') * ‖f‖
  facts : DifferenceOperatorIdentities d S.fineMesh
  cells : S.CellIdentities
  expSum : S.ExpSumBound (2 * localBoundsRate d)
  lifts : LiftsOfTorusAllDimensions
  sets : MaxBallSiteEstimates
  cellLaplacian : ComplementLaplacianBlockBound
variable {S : Scales d L j N}
theorem latticeExpSum_nonneg (d : ℕ) (δ : ℝ) : 0 ≤ latticeExpSum d δ :=
  mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg fun _ => (Real.exp_pos _).le)
theorem cubeConst_nonneg (d : ℕ) : 0 ≤ cubeConst d :=
  mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (latticeExpSum_nonneg d _)
theorem Inputs.exp_le (D : Inputs S) {a b u : Torus d N}
    (h : taxicabDist a b ≤ 17 * (d : ℝ) + 1) :
    Real.exp (-localBoundsRate d * taxicabDist a u) ≤
      weightRatio d * Real.exp (-localBoundsRate d * taxicabDist b u) :=
  exp_taxicab_le D.rate_pos.le h
theorem Inputs.sum_restrictTo_cells (D : Inputs S) (g : SiteFun d S.fineMesh) :
    ∑ y : GridPoint d S.unitMesh,
      SiteFun.restrictTo (S.fineCell y : Set (GridPoint d S.fineMesh)) g = g := by
  have hs : ∀ (t : Finset (GridPoint d S.unitMesh)) (z : GridPoint d S.fineMesh),
      (∑ y ∈ t, SiteFun.restrictTo (S.fineCell y : Set (GridPoint d S.fineMesh)) g) z =
        ∑ y ∈ t, SiteFun.restrictTo (S.fineCell y : Set (GridPoint d S.fineMesh)) g z := by
    classical
    intro t z
    induction t using Finset.induction_on with
    | empty => rfl
    | insert a t ha ih => rw [sum_insert ha, sum_insert ha, add_apply, ih]
  refine ScaledFun.ext fun z => ?_
  obtain ⟨y, hy, huniq⟩ := D.cells.fineCell_partition z
  rw [hs, sum_eq_single y]
  · rw [siteFun_restrictTo_apply, siteIndicator_of_mem (Finset.mem_coe.mpr hy), one_mul]
  · intro y' _ hne
    rw [siteFun_restrictTo_apply,
      siteIndicator_of_not_mem (fun h => hne (huniq y' (Finset.mem_coe.mp h))), zero_mul]
  · simp
theorem fineCell_nonempty (D : Inputs S) (y : GridPoint d S.unitMesh) :
    (S.fineCell y : Set (GridPoint d S.fineMesh)).Nonempty := by
  refine Finset.coe_nonempty.mpr (Finset.card_pos.mp (Nat.pos_of_ne_zero fun h0 => ?_))
  have h := D.cells.fineCell_card y
  have hL : (0 : ℝ) < L := by exact_mod_cast S.factor_pos
  have hξ : 0 < fineScale L j := by
    unfold fineScale
    positivity
  rw [h0, Nat.cast_zero] at h
  exact (inv_pos.mpr (pow_pos hξ d)).ne h
theorem neg_mul_le_add_neg_mul {a b t D e : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ b) (hb : b ≤ 1)
    (ht : 0 ≤ t) (he : 0 ≤ e) (hD : t - e ≤ D) : -b * D ≤ e + -a * t := by
  have h1 : b * (t - e) ≤ b * D := mul_le_mul_of_nonneg_left hD (ha0.trans ha)
  have h2 : a * t ≤ b * t := mul_le_mul_of_nonneg_right ha ht
  have h3 : b * e ≤ 1 * e := mul_le_mul_of_nonneg_right hb he
  nlinarith [h1, h2, h3]
theorem Inputs.cell_term_le (D : Inputs S) {A : ℝ} {u' : Torus d N}
    {g : SiteFun d S.fineMesh}
    (hg : ∀ y : GridPoint d S.unitMesh,
      ‖SiteFun.restrictTo (S.fineCell y : Set (GridPoint d S.fineMesh)) g‖ ≤
        A * Real.exp (-2 * localBoundsRate d * taxicabDist (y : Torus d N) u'))
    (hA : 0 ≤ A) (y y' : GridPoint d S.unitMesh) :
    ‖MultiField.restrictTo (maxBall S.fineMesh 1 (y : Torus d N))
        (discreteGrad S.fineMesh (S.singleScaleGaugeProjCompl
          (SiteFun.restrictTo (S.fineCell y' : Set (GridPoint d S.fineMesh)) g)))‖ ≤
      |gaugeProjDecayPrefactor d| * Real.exp (2 * (d : ℝ)) * A *
        Real.exp (-(2 * localBoundsRate d) * taxicabDist (y : Torus d N) (y' : Torus d N) -
          (2 * localBoundsRate d) * taxicabDist (y' : Torus d N) u') := by
  have hne := fineCell_nonempty D y'
  have hU : (maxBall (d := d) S.fineMesh 1 (y : Torus d N)).Nonempty :=
    ((D.sets d L j N S).2.2.1 (y : Torus d N)).1
  have h1 := D.decay _ _ hU hne
    (SiteFun.restrictTo (S.fineCell y' : Set (GridPoint d S.fineMesh)) g)
  rw [restrictTo_restrictTo] at h1
  have hsub : (S.fineCell y' : Set (GridPoint d S.fineMesh)) ⊆
      maxBall S.fineMesh 1 (y' : Torus d N) := fun x hx =>
    ((D.sets d L j N S).2.2.2.2 y').1 x (Finset.mem_coe.mp hx)
  have h2 := (D.sets d L j N S).2.1 (y : Torus d N) (y' : Torus d N) 1 1 one_pos one_pos _ _
    hU hne subset_rfl hsub
  have h3 : -gaugeProjDecayConst d * siteSetDist (maxBall S.fineMesh 1 (y : Torus d N))
      (S.fineCell y' : Set (GridPoint d S.fineMesh)) ≤
      2 * (d : ℝ) + -(2 * localBoundsRate d) * taxicabDist (y : Torus d N) (y' : Torus d N) :=
    neg_mul_le_add_neg_mul (by linarith [D.rate_pos]) D.rate_le D.decay_le
      (taxicabDist_nonneg _ _) (by linarith) (by linarith)
  have h4 := Real.exp_le_exp.mpr h3
  have h5 := hg y'
  have h6 : -(2 : ℝ) * localBoundsRate d = -(2 * localBoundsRate d) := by ring
  calc _ ≤ _ := h1
    _ ≤ |gaugeProjDecayPrefactor d| * Real.exp (-gaugeProjDecayConst d *
          siteSetDist (maxBall S.fineMesh 1 (y : Torus d N))
            (S.fineCell y' : Set (GridPoint d S.fineMesh))) *
          ‖SiteFun.restrictTo (S.fineCell y' : Set (GridPoint d S.fineMesh)) g‖ := by
        gcongr
        exact le_abs_self _
    _ ≤ |gaugeProjDecayPrefactor d| * Real.exp (2 * (d : ℝ) +
          -(2 * localBoundsRate d) * taxicabDist (y : Torus d N) (y' : Torus d N)) *
          (A * Real.exp (-2 * localBoundsRate d * taxicabDist (y' : Torus d N) u')) := by
        gcongr
    _ = _ := by
        rw [h6, sub_eq_add_neg, Real.exp_add, Real.exp_add (-(2 * localBoundsRate d) * _),
          neg_mul (2 * localBoundsRate d) (taxicabDist (y' : Torus d N) u')]
        ring
theorem Inputs.cube_norm_le (D : Inputs S) {A : ℝ} (hA : 0 ≤ A) {u' : Torus d N}
    {g : SiteFun d S.fineMesh}
    (hg : ∀ y : GridPoint d S.unitMesh,
      ‖SiteFun.restrictTo (S.fineCell y : Set (GridPoint d S.fineMesh)) g‖ ≤
        A * Real.exp (-2 * localBoundsRate d * taxicabDist (y : Torus d N) u'))
    (y : GridPoint d S.unitMesh) :
    ‖MultiField.restrictTo (maxBall S.fineMesh 1 (y : Torus d N))
        (discreteGrad S.fineMesh (S.singleScaleGaugeProjCompl g))‖ ≤
      cubeConst d * A * Real.exp (-localBoundsRate d * taxicabDist (y : Torus d N) u') := by
  have hk : ∑ p : GridPoint d S.unitMesh,
      Real.exp (-(2 * localBoundsRate d) * taxicabDist (y : Torus d N) (p : Torus d N) -
        (2 * localBoundsRate d) * taxicabDist (p : Torus d N) u') ≤
      latticeExpSum d (localBoundsRate d) *
        Real.exp (-localBoundsRate d * taxicabDist (y : Torus d N) u') := by
    have h := D.expSum.1 (y : Torus d N) u'
    have e : 2 * localBoundsRate d / 2 = localBoundsRate d := by ring
    rw [e] at h
    exact h
  have hK : 0 ≤ |gaugeProjDecayPrefactor d| * Real.exp (2 * (d : ℝ)) * A :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hA
  have hsplit : MultiField.restrictTo (maxBall S.fineMesh 1 (y : Torus d N))
      (discreteGrad S.fineMesh (S.singleScaleGaugeProjCompl g)) =
      ∑ y' : GridPoint d S.unitMesh, MultiField.restrictTo (maxBall S.fineMesh 1 (y : Torus d N))
        (discreteGrad S.fineMesh (S.singleScaleGaugeProjCompl
          (SiteFun.restrictTo (S.fineCell y' : Set (GridPoint d S.fineMesh)) g))) := by
    have h := congrArg (fun f : SiteFun d S.fineMesh => restrictToLinear (ι := Fin d)
      (maxBall S.fineMesh 1 (y : Torus d N))
      (discreteGrad S.fineMesh (S.singleScaleGaugeProjCompl f))) (D.sum_restrictTo_cells g)
    simp only [map_sum] at h
    exact h.symm
  rw [hsplit]
  calc _ ≤ ∑ y' : GridPoint d S.unitMesh,
        ‖MultiField.restrictTo (maxBall S.fineMesh 1 (y : Torus d N))
          (discreteGrad S.fineMesh (S.singleScaleGaugeProjCompl
            (SiteFun.restrictTo (S.fineCell y' : Set (GridPoint d S.fineMesh)) g)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ y' : GridPoint d S.unitMesh, |gaugeProjDecayPrefactor d| * Real.exp (2 * (d : ℝ)) * A *
        Real.exp (-(2 * localBoundsRate d) * taxicabDist (y : Torus d N) (y' : Torus d N) -
          (2 * localBoundsRate d) * taxicabDist (y' : Torus d N) u') :=
        sum_le_sum fun y' _ => D.cell_term_le hg hA y y'
    _ = |gaugeProjDecayPrefactor d| * Real.exp (2 * (d : ℝ)) * A *
        ∑ y' : GridPoint d S.unitMesh,
          Real.exp (-(2 * localBoundsRate d) * taxicabDist (y : Torus d N) (y' : Torus d N) -
            (2 * localBoundsRate d) * taxicabDist (y' : Torus d N) u') := by
        rw [mul_sum]
    _ ≤ |gaugeProjDecayPrefactor d| * Real.exp (2 * (d : ℝ)) * A *
        (latticeExpSum d (localBoundsRate d) *
          Real.exp (-localBoundsRate d * taxicabDist (y : Torus d N) u')) :=
        mul_le_mul_of_nonneg_left hk hK
    _ = _ := by
        unfold cubeConst
        ring
theorem Inputs.abs_laplacian_le (D : Inputs S) {A : ℝ} (hA : 0 ≤ A) {u' : Torus d N}
    {g : SiteFun d S.fineMesh}
    (hg : ∀ y : GridPoint d S.unitMesh,
      ‖SiteFun.restrictTo (S.fineCell y : Set (GridPoint d S.fineMesh)) g‖ ≤
        A * Real.exp (-2 * localBoundsRate d * taxicabDist (y : Torus d N) u'))
    (z : GridPoint d S.fineMesh) :
    |discreteLaplacian S.fineMesh (S.singleScaleGaugeProjCompl g) z| ≤
      laplacianConst d * A * Real.exp (-localBoundsRate d * taxicabDist (z : Torus d N) u') := by
  obtain ⟨y, hy, -⟩ := D.cells.fineCell_partition z
  obtain ⟨κ, hκ⟩ := D.cellLaplacian d L j N S g
  obtain ⟨h1, h2⟩ := hκ y
  rw [h1 z hy]
  have hb := D.cube_norm_le hA hg y
  have hz : z ∈ maxBall S.fineMesh 1 (y : Torus d N) := ((D.sets d L j N S).2.2.2.2 y).1 z hy
  have hd := (D.sets d L j N S).1 (y : Torus d N) 1 one_pos z hz
  have hw : Real.exp (-localBoundsRate d * taxicabDist (y : Torus d N) u') ≤
      weightRatio d * Real.exp (-localBoundsRate d * taxicabDist (z : Torus d N) u') :=
    D.exp_le (by rw [taxicabDist_comm]; linarith)
  have hc := mul_nonneg (cubeConst_nonneg d) hA
  have hs : (0 : ℝ) ≤ 4 ^ d * Real.sqrt (2 * (d : ℝ)) := by positivity
  calc |κ y| ≤ _ := h2
    _ ≤ 4 ^ d * Real.sqrt (2 * (d : ℝ)) * (cubeConst d * A *
          Real.exp (-localBoundsRate d * taxicabDist (y : Torus d N) u')) :=
        mul_le_mul_of_nonneg_left hb hs
    _ ≤ 4 ^ d * Real.sqrt (2 * (d : ℝ)) * (cubeConst d * A * (weightRatio d *
          Real.exp (-localBoundsRate d * taxicabDist (z : Torus d N) u'))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hc) hs
    _ = _ := by
        unfold laplacianConst
        ring
end Inputs
section Arithmetic
end Arithmetic
end YangMills.Construction.PeriodicLattice.GradComplPointwise
