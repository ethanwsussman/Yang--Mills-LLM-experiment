import YangMills.Construction.Towers.MeansOfPlaneWavesAlongStraightPaths
import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.StraightPathMeans
open YangMills.Construction.Tower.TrivialLinearization (setAverage baseVerticesOfCube)
open YangMills.Construction.Tower.PlaneWaves (freqBox mem_freqBox)
open YangMills.Construction.Tower.PlaneWaveCalculus (expWave)
open YangMills.Construction.PeriodicOperators (toComplexVec bilinDot dualLattice)
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.PeriodicOperators.Tempered.OneStep
open YangMills.Construction.InfiniteLattice (AmbientSpace)
variable {L k : ℕ}
theorem torus_exists_real_lift (x : PeriodicLattice.FourTorus L k) :
    ∃ u : AmbientSpace, (fun μ => ((u μ : ℝ) : AddCircle (PeriodicLattice.torusSide L k))) = x := by
  have h : ∀ μ, ∃ r : ℝ, ((r : ℝ) : AddCircle (PeriodicLattice.torusSide L k)) = x μ :=
    fun μ => QuotientAddGroup.mk_surjective (x μ)
  choose u hu using h
  exact ⟨u, funext hu⟩
theorem phase_coe_eq_exp (hL : 0 < L) {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ k)) (u : AmbientSpace) :
    phase (L := L) (n := k) p (fun μ => ((u μ : ℝ) : AddCircle (PeriodicLattice.torusSide L k))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec u)) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.phase_coe <;> assumption
theorem phase_coe_add (hL : 0 < L) {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ k)) (u v : AmbientSpace) :
    phase (L := L) (n := k) p
        (fun μ => ((u μ + v μ : ℝ) : AddCircle (PeriodicLattice.torusSide L k))) =
      phase (L := L) (n := k) p (fun μ => ((u μ : ℝ) : AddCircle (PeriodicLattice.torusSide L k))) *
        expWave (toComplexVec p) v := by
  have h := phase_coe_eq_exp (L := L) (k := k) hL hp (u + v)
  simp only [Pi.add_apply] at h
  rw [h, phase_coe_eq_exp hL hp u, expWave, ← Complex.exp_add]
  congr 1
  simp only [bilinDot, toComplexVec, Pi.add_apply]
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem finestMesh_inv (L i : ℕ) : (finestMesh L i)⁻¹ = (L : ℝ) ^ i := by
  simp [finestMesh, meshAt, zpow_neg]
theorem coe_freqBox (L i : ℕ) : ((freqBox L i : Finset _) : Set (Fin 4 → ℤ)) = offsetBox L i := by
  ext w
  rw [Finset.mem_coe, mem_freqBox, finestMesh_inv]
  refine forall_congr' fun μ => ?_
  constructor <;> intro h <;> linarith
theorem list_range_map_sum {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    ((List.range N).map g).sum = ∑ t ∈ Finset.range N, g t := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp
theorem refinedBlock_parametrization (hZ : BlockPathContourPivotStatement)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hk : 0 < k) (i : ℕ) (y : Vertex L k (i + 1) i) :
    ∃ φ : (Fin 4 → ℤ) → Vertex L k (i + 1) 0,
      (∀ w ∈ freqBox L i, ((φ w : Vertex L k (i + 1) 0) : PeriodicLattice.FourTorus L k) =
        offsetPoint (meshAt L (i + 1) 0) (y : PeriodicLattice.FourTorus L k) w) ∧
      Set.InjOn φ (freqBox L i : Finset _) ∧
      baseVerticesOfCube L k (i + 1) i y = φ '' (freqBox L i : Finset _) ∧
      (freqBox L i).card = L ^ (4 * i) := by
  classical
  obtain ⟨P, -⟩ := (hZ L hst (i + 1) i i (by omega) le_rfl (Nat.le_succ i)).1 k hk
  have hbe := P.eq_image y
  have hinj := P.injOn_offset y
  have hsub := P.subset_sublattice y
  have hcard := P.offsetBox_ncard
  rw [Nat.sub_self] at hbe hinj hsub
  have hmem : ∀ w ∈ freqBox L i,
      offsetPoint (meshAt L (i + 1) 0) (y : PeriodicLattice.FourTorus L k) w ∈
        PeriodicLattice.refinedBlock i y := by
    intro w hw
    rw [hbe]
    refine ⟨w, ?_, rfl⟩
    rw [← coe_freqBox]
    exact hw
  let φ : (Fin 4 → ℤ) → Vertex L k (i + 1) 0 := fun w =>
    if h : offsetPoint (meshAt L (i + 1) 0) (y : PeriodicLattice.FourTorus L k) w ∈
      PeriodicLattice.sublattice L k (PeriodicLattice.levelDepth (i + 1) 0) then ⟨_, h⟩ else 0
  have hφ : ∀ w ∈ freqBox L i, ((φ w : Vertex L k (i + 1) 0) : PeriodicLattice.FourTorus L k) =
      offsetPoint (meshAt L (i + 1) 0) (y : PeriodicLattice.FourTorus L k) w := by
    intro w hw
    have hm : offsetPoint (meshAt L (i + 1) 0) (y : PeriodicLattice.FourTorus L k) w ∈
        PeriodicLattice.sublattice L k (PeriodicLattice.levelDepth (i + 1) 0) := hsub (hmem w hw)
    simp only [φ, dif_pos hm]
  refine ⟨φ, hφ, ?_, ?_, ?_⟩
  · intro w hw w' hw' h
    have e1 : w ∈ offsetBox L i := by rw [← coe_freqBox]; exact hw
    have e2 : w' ∈ offsetBox L i := by rw [← coe_freqBox]; exact hw'
    refine hinj e1 e2 ?_
    rw [← hφ w hw, ← hφ w' hw', h]
  · ext x
    simp only [baseVerticesOfCube, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe]
    constructor
    · intro hx
      rw [hbe] at hx
      obtain ⟨w, hw, e⟩ := hx
      rw [← coe_freqBox] at hw
      exact ⟨w, hw, Subtype.ext ((hφ w hw).trans e)⟩
    · rintro ⟨w, hw, rfl⟩
      rw [hφ w hw]
      exact hmem w hw
  · rw [← Set.ncard_coe_finset, coe_freqBox, hcard]
theorem setAverage_image_eq {ι : Type*} (S : Set ι) (φ : (Fin 4 → ℤ) → ι) (N : Finset (Fin 4 → ℤ))
    (hinj : Set.InjOn φ N) (hS : S = φ '' N) (f : ι → Matrices.ComplexMatrix2) :
    setAverage S f = ((N.card : ℂ))⁻¹ • ∑ w ∈ N, f (φ w) := by
  subst hS
  rw [setAverage, hinj.ncard_image, Set.ncard_coe_finset, finsum_mem_image hinj,
    finsum_mem_coe_finset]
theorem edgeFormPathSum_crossingPath (hZ : BlockPathContourPivotStatement)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hk : 0 < k) {i : ℕ} (y : Vertex L k (i + 1) i) (ρ : Fin 4)
    (x : Vertex L k (i + 1) 0) (hx : (x : PeriodicLattice.FourTorus L k) ∈ PeriodicLattice.refinedBlock i y)
    (A : Edge L k (i + 1) 0 → Matrices.ComplexMatrix2) :
    edgeFormPathSum A (PeriodicLattice.crossingPath (PeriodicLattice.Bond.forwardFrom y ρ) x) =
      ∑ t ∈ Finset.range (L ^ i), A (PeriodicLattice.Bond.forwardFrom
        (x + t • PeriodicLattice.unitStep L k (PeriodicLattice.levelDepth (i + 1) 0) ρ) ρ) := by
  obtain ⟨-, -, T, -⟩ := (hZ L hst (i + 1) i i (by omega) le_rfl (Nat.le_succ i)).1 k hk
  have hc := T.crossingPath_eq
  rw [Nat.sub_self] at hc
  rw [hc (PeriodicLattice.Bond.forwardFrom y ρ) ρ (by simp [PeriodicLattice.Bond.forwardFrom]) x hx,
    edgeFormPathSum, PeriodicLattice.bondFormSumAlong, List.map_map]
  exact list_range_map_sum _ _
theorem coe_add_nsmul_unitStep {i : ℕ} (y : PeriodicLattice.FourTorus L k) (u : AmbientSpace)
    (hu : (fun μ => ((u μ : ℝ) : AddCircle (PeriodicLattice.torusSide L k))) = y)
    (x : Vertex L k (i + 1) 0) (w : Fin 4 → ℤ) (t : ℕ) (ρ : Fin 4)
    (hx : (x : PeriodicLattice.FourTorus L k) = offsetPoint (meshAt L (i + 1) 0) y w) :
    ((x + t • PeriodicLattice.unitStep L k (PeriodicLattice.levelDepth (i + 1) 0) ρ : Vertex L k (i + 1) 0) :
        PeriodicLattice.FourTorus L k) =
      fun ν => ((u ν + (finestMesh L (i + 1) • crossingPoint w t ρ) ν : ℝ) :
        AddCircle (PeriodicLattice.torusSide L k)) := by
  funext ν
  have hsp : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth (i + 1) 0) = meshAt L (i + 1) 0 :=
    meshSize_levelDepth L (i + 1) 0
  have hy : y ν = ((u ν : ℝ) : AddCircle (PeriodicLattice.torusSide L k)) := (congrFun hu ν).symm
  have h1 : ((x + t • PeriodicLattice.unitStep L k (PeriodicLattice.levelDepth (i + 1) 0) ρ : Vertex L k (i + 1) 0) :
      PeriodicLattice.FourTorus L k) ν =
      ((u ν : ℝ) : AddCircle (PeriodicLattice.torusSide L k)) +
        (((w ν : ℝ) * meshAt L (i + 1) 0 : ℝ) : AddCircle (PeriodicLattice.torusSide L k)) +
        t • (if ν = ρ then ((meshAt L (i + 1) 0 : ℝ) : AddCircle (PeriodicLattice.torusSide L k))
          else 0) := by
    rw [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, hx]
    simp only [offsetPoint, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis, Pi.single_apply, hsp, hy, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h1]
  simp only [finestMesh, Pi.smul_apply, crossingPoint, smul_eq_mul]
  by_cases h : ν = ρ
  · simp only [if_pos h, mul_add, AddCircle.coe_add, add_assoc]
    congr 1
    rw [mul_comm (meshAt L (i + 1) 0) (w ν : ℝ)]
    congr 1
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_comm]
  · simp only [if_neg h, smul_zero, add_zero, AddCircle.coe_add]
    rw [mul_comm]
theorem planeWaveMeans_proof (hZ : BlockPathContourPivotStatement) : PlaneWaveMeans := by
  classical
  intro L hst k i hk y ρ M q v B B' hq hB
  have hL : 0 < L := by
    have := hst.2
    omega
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  obtain ⟨φ, hφ, hinj, hS, hcard⟩ := refinedBlock_parametrization hZ hst hk i y
  obtain ⟨u, hu⟩ := torus_exists_real_lift (y : PeriodicLattice.FourTorus L k)
  have hblock : ∀ w ∈ freqBox L i,
      ((φ w : Vertex L k (i + 1) 0) : PeriodicLattice.FourTorus L k) ∈ PeriodicLattice.refinedBlock i y := by
    intro w hw
    exact show φ w ∈ baseVerticesOfCube L k (i + 1) i y from by
      rw [hS]
      exact ⟨w, hw, rfl⟩
  have hval : ∀ w ∈ freqBox L i, ∀ t : ℕ,
      B (PeriodicLattice.Bond.forwardFrom
          (φ w + t • PeriodicLattice.unitStep L k (PeriodicLattice.levelDepth (i + 1) 0) ρ) ρ) +
        Complex.I • B' (PeriodicLattice.Bond.forwardFrom
          (φ w + t • PeriodicLattice.unitStep L k (PeriodicLattice.levelDepth (i + 1) 0) ρ) ρ) =
      ∑ j ∈ M, (phase (L := L) (n := k) (q j) (y : PeriodicLattice.FourTorus L k) *
        expWave (toComplexVec (q j)) (finestMesh L (i + 1) • crossingPoint w t ρ)) • v j := by
    intro w hw t
    rw [hB]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    rw [coe_add_nsmul_unitStep (y : PeriodicLattice.FourTorus L k) u hu (φ w) w t ρ (hφ w hw),
      phase_coe_add hL (hq j hj) u, hu]
  have hpath : ∀ w ∈ freqBox L i,
      edgeFormPathSum B (PeriodicLattice.crossingPath (PeriodicLattice.Bond.forwardFrom y ρ) (φ w)) +
        Complex.I • edgeFormPathSum B' (PeriodicLattice.crossingPath (PeriodicLattice.Bond.forwardFrom y ρ) (φ w)) =
      ∑ t ∈ Finset.range (L ^ i), ∑ j ∈ M,
        (phase (L := L) (n := k) (q j) (y : PeriodicLattice.FourTorus L k) *
          expWave (toComplexVec (q j)) (finestMesh L (i + 1) • crossingPoint w t ρ)) • v j := by
    intro w hw
    rw [edgeFormPathSum_crossingPath hZ hst hk y ρ _ (hblock w hw),
      edgeFormPathSum_crossingPath hZ hst hk y ρ _ (hblock w hw),
      Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => hval w hw t
  have hswap : ∀ g : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℕ → ℂ,
      ∑ w ∈ freqBox L i, ∑ t ∈ Finset.range (L ^ i), ∑ j ∈ M, g j w t • v j =
        ∑ j ∈ M, (∑ w ∈ freqBox L i, ∑ t ∈ Finset.range (L ^ i), g j w t) • v j := by
    intro g
    rw [Finset.sum_congr rfl fun w _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_smul]
  rw [pathAverage, pathAverage, setAverage_image_eq _ φ _ hinj hS, setAverage_image_eq _ φ _ hinj hS, hcard,
    smul_comm Complex.I, ← smul_add, Finset.smul_sum (r := Complex.I), ← Finset.sum_add_distrib,
    Finset.sum_congr rfl hpath, hswap, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  have h5 : (L : ℂ) ^ (5 * i) = (L : ℂ) ^ (4 * i) * (L : ℂ) ^ i := by
    rw [← pow_add]
    congr 1
    ring
  rw [stepMean, h5]
  simp only [← Finset.mul_sum]
  push_cast
  field_simp
end YangMills.Construction.Tower.StraightPathMeans
end
