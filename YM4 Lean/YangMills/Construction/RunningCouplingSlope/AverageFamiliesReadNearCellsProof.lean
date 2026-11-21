import YangMills.Construction.Lattice.HolomorphyOfBoundedOneStepObjectsProof
import YangMills.Construction.RunningCouplingSlope.AverageFamiliesReadNearCells
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.IteratesOfThePlainAverage
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.RunningCouplingSlope.PlainKernelsGiveTheirMapsAtARadius
import YangMills.Construction.RunningCouplingSlope.TopBondsAndTheirBlocks
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Set
open scoped ENNReal Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanKernelsLocal
open Matrices Tower PeriodicOperators
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
open Tower.SmoothingContraction (TorusOpNormLE)
open Tower.LeftChartFields (scalarCoords)
section Holomorphy
open Matrices.GroupLieProduct Coordinates Coordinates.ComplexCoordinates
variable {σ : Type} [Fintype σ]
private lemma supBall_isSupOpen {ρ : ℝ} (hρ : 0 < ρ) : IsSupOpen (supBall σ ρ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.isSupOpen_supBall <;> assumption
private lemma isOpen_preimage_supBall (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen (tupleOfCoords b ν ⁻¹' supBall σ ρ) := by apply _root_.YangMills.Construction.PeriodicLattice.BoundedStepHolomorphy.isOpen_preimage_supBall <;> assumption
private lemma isHolomorphicIn_of_subset {N N' : ℕ} {O O' : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hf : IsHolomorphicIn O f) (hO : IsOpen O')
    (hs : O' ⊆ O) : IsHolomorphicIn O' f :=
  ⟨hO, hf.2.1.mono hs, fun a ha j => hf.2.2 a (hs ha) j⟩
private lemma isHolomorphicIn_const_smul {N : ℕ} {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates 1} (hf : IsHolomorphicIn O f) (u : ℂ) :
    IsHolomorphicIn O (fun w => u • f w) := by
  refine ⟨hf.1, hf.2.1.const_smul u, fun a ha j => ?_⟩
  filter_upwards [hf.2.2 a ha j] with ζ h
  exact h.const_smul u
private lemma holomorphicInEntries_mono_mul {β : Type} {S : Set (β → ComplexMatrix2)}
    {g : (β → ComplexMatrix2) → ℂ} {ρ ρ' : ℝ}
    (hg : HolomorphicInEntries scalarCoords S ρ' g) (hρ : 0 < ρ) (hle : ρ ≤ ρ') (u : ℂ) :
    HolomorphicInEntries scalarCoords S ρ fun v => u * g v := by
  obtain ⟨F, f, hf, he⟩ := hg
  refine ⟨F, fun x => u * f x, fun b => ⟨supBall_isSupOpen hρ, fun ν => ?_⟩, fun a ha hs => ?_⟩
  · obtain ⟨-, hν⟩ := hf b
    have h1 := isHolomorphicIn_of_subset (hν ν) (isOpen_preimage_supBall b ν hρ) fun w hw =>
      ⟨hw.1, lt_of_lt_of_le hw.2 hle⟩
    have h2 := isHolomorphicIn_const_smul h1 u
    have e : (fun w => u • (⇑scalarCoords ∘ f ∘ tupleOfCoords b ν) w) =
        ⇑scalarCoords ∘ (fun x => u * f x) ∘ tupleOfCoords b ν := by
      funext w i
      simp [scalarCoords]
    rwa [e] at h2
  · show u * f (fun b => a b) = u * g a
    rw [he a ha (lt_of_lt_of_le hs (ENNReal.ofReal_le_ofReal hle))]
end Holomorphy
section Norms
variable {σ σ' : Type}
private lemma wNorm_meshWeight_eq [Fintype (Fin 3 × σ)] {a : ℝ} (ha : 0 < a) (f : Fin 3 × σ → ℂ) :
    wNorm (meshWeight a) f =
      a ^ 2 * ‖(WithLp.toLp 2 f : EuclideanSpace ℂ (Fin 3 × σ))‖ := by
  unfold wNorm
  rw [tsum_fintype, EuclideanSpace.norm_eq]
  have e : ∑ i, meshWeight a i * ‖f i‖ ^ 2 = (a ^ 2) ^ 2 * ∑ i, ‖f i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [meshWeight]
    ring
  simp only [PiLp.toLp_apply]
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
private lemma l2_opNorm_le_of_torusOpNormLE [Fintype (Fin 3 × σ)] [Fintype (Fin 3 × σ')]
    [DecidableEq (Fin 3 × σ)] [DecidableEq (Fin 3 × σ')] {a c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) {K : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')}
    (h : TorusOpNormLE a 1 K c) :
    ‖(((a ^ 2)⁻¹ : ℝ) : ℂ) • (Matrix.of K : Matrix (Fin 3 × σ') (Fin 3 × σ) ℂ)‖ ≤ c := by
  have key : ∀ f : Fin 3 × σ → ℂ, ‖(WithLp.toLp 2 (applyKernel K f) :
      EuclideanSpace ℂ (Fin 3 × σ'))‖ ≤ c * (a ^ 2 * ‖(WithLp.toLp 2 f :
        EuclideanSpace ℂ (Fin 3 × σ))‖) := by
    intro f
    set x := ‖(WithLp.toLp 2 f : EuclideanSpace ℂ (Fin 3 × σ))‖ with hx
    by_cases h0 : x = 0
    · have hf : f = 0 := by
        have : (WithLp.toLp 2 f : EuclideanSpace ℂ (Fin 3 × σ)) = 0 := norm_eq_zero.1 h0
        simpa using this
      subst hf
      have : applyKernel K (0 : Fin 3 × σ → ℂ) = 0 := by
        funext p
        simp [applyKernel]
      simp only [this]
      have : ‖(WithLp.toLp 2 (0 : Fin 3 × σ' → ℂ) : EuclideanSpace ℂ (Fin 3 × σ'))‖ = 0 := by
        simp
      rw [this]
      exact mul_nonneg hc (mul_nonneg (by positivity) (norm_nonneg _))
    have xpos : 0 < x := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    set t : ℝ := (a ^ 2 * x)⁻¹ with ht
    have tpos : 0 < t := by positivity
    have hball : (t : ℂ) • f ∈ wUnitBall (meshWeight a) univ := by
      refine ⟨mem_univ _, ?_, ?_⟩
      · exact (hasSum_fintype _).summable
      · rw [wNorm_meshWeight_eq ha]
        have e : (WithLp.toLp 2 ((t : ℂ) • f) : EuclideanSpace ℂ (Fin 3 × σ)) =
            (t : ℂ) • (WithLp.toLp 2 f : EuclideanSpace ℂ (Fin 3 × σ)) := rfl
        rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg tpos.le, ← hx, ht]
        field_simp
        exact le_rfl
    have h₁ : ENNReal.ofReal (wNorm (meshWeight 1) (applyKernel K ((t : ℂ) • f))) ≤
        ENNReal.ofReal c :=
      le_trans (le_iSup₂ (f := fun g (_ : g ∈ wUnitBall (meshWeight a) univ) =>
        ENNReal.ofReal (wNorm (meshWeight 1) (applyKernel K g))) _ hball) h.2
    have h₂ := (ENNReal.ofReal_le_ofReal_iff hc).1 h₁
    rw [wNorm_meshWeight_eq one_pos] at h₂
    have e : applyKernel K ((t : ℂ) • f) = (t : ℂ) • applyKernel K f := by
      funext p
      simp only [applyKernel, Pi.smul_apply, smul_eq_mul, tsum_fintype, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    have e' : (WithLp.toLp 2 ((t : ℂ) • applyKernel K f) : EuclideanSpace ℂ (Fin 3 × σ')) =
        (t : ℂ) • (WithLp.toLp 2 (applyKernel K f) : EuclideanSpace ℂ (Fin 3 × σ')) := rfl
    rw [e, e', norm_smul, Complex.norm_real, Real.norm_of_nonneg tpos.le] at h₂
    have h₃ : t * ‖(WithLp.toLp 2 (applyKernel K f) : EuclideanSpace ℂ (Fin 3 × σ'))‖ ≤ c := by
      simpa using h₂
    have h₄ := mul_le_mul_of_nonneg_left h₃ (by positivity : 0 ≤ a ^ 2 * x)
    rw [← mul_assoc, ht, mul_inv_cancel₀ (by positivity), one_mul] at h₄
    linarith
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  have hv := key (WithLp.ofLp v)
  have e : ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
      ((((a ^ 2)⁻¹ : ℝ) : ℂ) • (Matrix.of K : Matrix (Fin 3 × σ') (Fin 3 × σ) ℂ))) v =
      (((a ^ 2)⁻¹ : ℝ) : ℂ) • (WithLp.toLp 2 (applyKernel K (WithLp.ofLp v)) :
        EuclideanSpace ℂ (Fin 3 × σ')) := by
    have e₁ : ((((a ^ 2)⁻¹ : ℝ) : ℂ) • (Matrix.of K : Matrix (Fin 3 × σ') (Fin 3 × σ) ℂ)).mulVec
        (WithLp.ofLp v) = (((a ^ 2)⁻¹ : ℝ) : ℂ) • applyKernel K (WithLp.ofLp v) := by
      funext p
      simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, applyKernel, tsum_fintype,
        Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    show WithLp.toLp 2 (((((a ^ 2)⁻¹ : ℝ) : ℂ) •
      (Matrix.of K : Matrix (Fin 3 × σ') (Fin 3 × σ) ℂ)).mulVec (WithLp.ofLp v)) = _
    rw [e₁]
    rfl
  rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ha2 : 0 < a ^ 2 := by positivity
  calc (a ^ 2)⁻¹ * _ ≤ (a ^ 2)⁻¹ * (c * (a ^ 2 * ‖(WithLp.toLp 2 (WithLp.ofLp v) :
        EuclideanSpace ℂ (Fin 3 × σ))‖)) := by gcongr
    _ = c * ‖v‖ := by
        simp only [WithLp.toLp_ofLp]
        field_simp
end Norms
section Entries
variable {N N' : Type}
private def indicatorVec (q : N) : N → ℂ := open Classical in fun x => if x = q then 1 else 0
private lemma entry_eq_of_represents [Fintype N] {T : KernelMatrix N N'}
    {M : (N → ℂ) → N' → ℂ} (h : Represents T M) (p : N') (q : N) :
    T p q = M (indicatorVec q) p := by
  classical
  rw [← (h (indicatorVec q)).2]
  unfold applyKernel
  rw [tsum_fintype, Finset.sum_eq_single q]
  · simp [indicatorVec]
  · intro b _ hb
    simp [indicatorVec, hb]
  · simp
private lemma map_zero_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) : M 0 = 0 := by
  rw [← (h 0).2]
  funext p
  simp [applyKernel]
end Entries
private theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
private theorem pauliCoeff_real_smul (a : Fin 3) {t : ℝ} (ht : t ≠ 0) (X : ComplexMatrix2) :
    pauliCoeff a (t • X) = (t : ℂ) * pauliCoeff a X := by
  have e : t • X = (t : ℂ) • X := by
    ext i j
    simp
  rw [e]
  by_cases hX : X ∈ ComplexMatrix2.traceless
  · unfold pauliCoeff
    rw [dif_pos hX, dif_pos (ComplexMatrix2.traceless.smul_mem _ hX)]
    exact congrFun (map_smul OneLoop.pauliCoordinateEquiv (t : ℂ) ⟨X, hX⟩) a
  · have hY : (t : ℂ) • X ∉ ComplexMatrix2.traceless := fun h => hX (by
      have h2 := ComplexMatrix2.traceless.smul_mem ((t : ℂ)⁻¹) h
      rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht), one_smul] at h2)
    unfold pauliCoeff
    rw [dif_neg hX, dif_neg hY, mul_zero]
section Geometry
variable {L n k : ℕ}
private lemma fineVertexCell_eq_of_mem (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) (hc : NeighbouringFineVertexCells) (ht : TopEdgesAndCubes)
    {x : Vertex L n k 0} {y : Vertex L n k k}
    (h : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y) :
    fineVertexCell x = y :=
  ((ht L hL n k hn hk).2.2 _ _ _ ((hc L hL n k).2.2.1 x) h)
private lemma mem_edgesNearCell_of_mem_over (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hc : NeighbouringFineVertexCells) (ht : TopEdgesAndCubes)
    (c : Edge L n k k) {b : Edge L n k 0} (hb : b ∈ edgesOverEdge c) :
    b ∈ edgesNearCell 2 c.source := by
  obtain ⟨h0, h2, -⟩ := ht L hL n k hn hk
  have hs := (hc L hL n k).1
  have one : ∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.refinedBlock k c.source ∪ PeriodicLattice.refinedBlock k c.target →
      cellDist (fineVertexCell x) c.source ≤ 2 := by
    intro x hx
    rcases hx with hx | hx
    · rw [fineVertexCell_eq_of_mem hL hn hk hc ht hx, h0]
      norm_num
    · rw [fineVertexCell_eq_of_mem hL hn hk hc ht hx, hs]
      exact h2 c
  exact ⟨one _ hb.1, one _ hb.2⟩
private lemma mem_edgesNearCell_of_inside (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hc : NeighbouringFineVertexCells) (ht : TopEdgesAndCubes)
    (y : Vertex L n k k) {b : Edge L n k 0}
    (hb : b ∈ PeriodicLattice.bondsInside (PeriodicLattice.refinedBlock k y)) :
    b ∈ edgesNearCell 2 y := by
  have h0 := (ht L hL n k hn hk).1
  have one : ∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.refinedBlock k y → cellDist (fineVertexCell x) y ≤ 2 := by
    intro x hx
    rw [fineVertexCell_eq_of_mem hL hn hk hc ht hx, h0]
    norm_num
  exact ⟨one _ hb.1, one _ hb.2⟩
end Geometry
section SeriesExpansions
variable {L n k : ℕ}
private def positiveValuesOfCoeffs (c : (edgePauliCoordinates L n k 0).Index → ℂ) :
    Edge L n k 0 → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
private theorem ofCoeffs_eq_extendOddly (c : (edgePauliCoordinates L n k 0).Index → ℂ) (b : Edge L n k 0) :
    (edgePauliCoordinates L n k 0).ofCoeffs c b = Tower.extendOddly (positiveValuesOfCoeffs c) b := rfl
private theorem extendOddly_of_pos (f : Edge L n k 0 → ComplexMatrix2) {b : Edge L n k 0}
    (h : b.IsPositivelyOriented) : Tower.extendOddly f b = f b := if_pos h
private theorem extendOddly_of_not_pos (f : Edge L n k 0 → ComplexMatrix2) {b : Edge L n k 0}
    (h : ¬ b.IsPositivelyOriented) : Tower.extendOddly f b = -f b.opposite := if_neg h
private theorem ofCoeffs_of_pos (c : (edgePauliCoordinates L n k 0).Index → ℂ) {b : Edge L n k 0}
    (h : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n k 0).ofCoeffs c b = ofPauliCoeffs c ⟨b, h⟩ :=
  (ofCoeffs_eq_extendOddly c b).trans ((extendOddly_of_pos _ h).trans (dif_pos h))
private lemma ofCoeffs_eq_zero (c : (edgePauliCoordinates L n k 0).Index → ℂ) (b : Edge L n k 0)
    (h₁ : ∀ (hp : b.IsPositivelyOriented) (a : Fin 3), c (a, ⟨b, hp⟩) = 0)
    (h₂ : ∀ (hp : b.opposite.IsPositivelyOriented) (a : Fin 3), c (a, ⟨b.opposite, hp⟩) = 0) :
    (edgePauliCoordinates L n k 0).ofCoeffs c b = 0 := by
  classical
  have zero : ∀ (x : Edge L n k 0) (hx : x.IsPositivelyOriented),
      (∀ a : Fin 3, c (a, ⟨x, hx⟩) = 0) → ofPauliCoeffs c ⟨x, hx⟩ = 0 :=
    fun x hx h => Finset.sum_eq_zero fun a _ => by rw [h a, zero_smul]
  by_cases hp : b.IsPositivelyOriented
  · rw [ofCoeffs_of_pos c hp]
    exact zero b hp (h₁ hp)
  · rw [ofCoeffs_eq_extendOddly, extendOddly_of_not_pos _ hp]
    by_cases hq : b.opposite.IsPositivelyOriented
    · have : positiveValuesOfCoeffs c b.opposite = ofPauliCoeffs c ⟨b.opposite, hq⟩ := dif_pos hq
      rw [this, zero _ hq (h₂ hq), neg_zero]
    · have : positiveValuesOfCoeffs c b.opposite = 0 := dif_neg hq
      rw [this, neg_zero]
private lemma ofCoeffs_mem_complexEdgeForms
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : (edgePauliCoordinates L n k 0).Index → ℂ) :
    (edgePauliCoordinates L n k 0).ofCoeffs c ∈ complexEdgeForms L n k 0 := by
  classical
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [ofCoeffs_of_pos c hb]
    exact ofPauliCoeffs_mem_traceless c _
  · rw [ofCoeffs_eq_extendOddly, ofCoeffs_eq_extendOddly]
    rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hrr : b.opposite.opposite = b := by
        cases b
        rfl
      rw [extendOddly_of_not_pos _ h₂, extendOddly_of_pos _ h₁, hrr]
    · rw [extendOddly_of_pos _ h₁, extendOddly_of_not_pos _ h₂, neg_neg]
private lemma edge_kernel_rows_local {ρ : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hc : NeighbouringFineVertexCells) (ht : TopEdgesAndCubes)
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Fintype (Fin 3 × PositiveEdge L n k 0)]
    (Kf : (Edge L n k 0 → ComplexMatrix2) → KernelMatrix (Fin 3 × PositiveEdge L n k 0)
      (Fin 3 × PositiveEdge L n k k))
    (G : (Edge L n k 0 → ComplexMatrix2) → (Edge L n k 0 → ComplexMatrix2) → Edge L n k k →
      ComplexMatrix2)
    (hg : ∀ v ∈ smallFormBall L n k ρ, Represents (Kf v)
      ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k) (G v)))
    (hr : ∀ c : Edge L n k k, ∀ v ∈ smallFormBall L n k ρ, ∀ v' ∈ smallFormBall L n k ρ,
      ∀ B ∈ complexEdgeForms L n k 0, ∀ B' ∈ complexEdgeForms L n k 0,
        EqOn v v' (edgesOverEdge c) → EqOn B B' (edgesOverEdge c) → G v B c = G v' B' c) :
    (∀ p q, ∀ v ∈ smallFormBall L n k ρ, ∀ v' ∈ smallFormBall L n k ρ,
      EqOn v v' (edgesNearCell 2 (edgeCell p)) → Kf v p q = Kf v' p q) ∧
    (∀ v ∈ smallFormBall L n k ρ, ∀ p q, 2 < cellDist (edgeCell p) (colouredEdgeCell q) →
      Kf v p q = 0) := by
  classical
  have hs := (hc L hL n k).1
  refine ⟨fun p q v hv v' hv' h => ?_, fun v hv p q hfar => ?_⟩
  · rw [entry_eq_of_represents (hg v hv) p q, entry_eq_of_represents (hg v' hv') p q]
    exact congrArg (pauliCoeff p.1) (hr p.2.1 v hv v' hv' _ (ofCoeffs_mem_complexEdgeForms hx _) _
      (ofCoeffs_mem_complexEdgeForms hx _)
      (fun b hb => h (mem_edgesNearCell_of_mem_over hL hn hk hc ht p.2.1 hb))
      fun _ _ => rfl)
  · have hq : q.2.1 ∉ edgesOverEdge p.2.1 := fun h => by
      have h2 := (mem_edgesNearCell_of_mem_over hL hn hk hc ht p.2.1 h).1
      have h3 : cellDist (edgeCell p) (colouredEdgeCell q) ≤ 2 := by
        rw [hs]
        exact h2
      linarith
    have hq' : ∀ b ∈ edgesOverEdge p.2.1, b.opposite ∈ edgesOverEdge p.2.1 :=
      fun b hb => ⟨hb.2, hb.1⟩
    have e : EqOn ((edgePauliCoordinates L n k 0).ofCoeffs (indicatorVec q))
        ((edgePauliCoordinates L n k 0).ofCoeffs 0) (edgesOverEdge p.2.1) := by
      intro b hb
      rw [ofCoeffs_eq_zero (indicatorVec q) b ?_ ?_, ofCoeffs_eq_zero 0 b (fun _ _ => rfl)
        fun _ _ => rfl]
      · intro hp a
        refine if_neg ?_
        intro he
        exact hq (by
          have := congrArg (fun x => x.2.1) he
          simp only at this
          rw [← this]
          exact hb)
      · intro hp a
        refine if_neg ?_
        intro he
        exact hq (by
          have := congrArg (fun x => x.2.1) he
          simp only at this
          rw [← this]
          exact hq' b hb)
    have z : (edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k) (G v) 0 p = 0 :=
      congrFun (map_zero_of_represents (hg v hv)) p
    rw [entry_eq_of_represents (hg v hv) p q]
    have e₂ := hr p.2.1 v hv v hv _ (ofCoeffs_mem_complexEdgeForms hx (indicatorVec q)) _
      (ofCoeffs_mem_complexEdgeForms hx 0) (fun _ _ => rfl) e
    have e₃ : restrictToPositiveEdges
          (G v ((edgePauliCoordinates L n k 0).ofCoeffs (indicatorVec q))) p.2 =
        restrictToPositiveEdges (G v ((edgePauliCoordinates L n k 0).ofCoeffs 0)) p.2 := e₂
    exact Eq.trans (congrArg (pauliCoeff p.1) e₃) z
private lemma vertex_kernel_rows_local {ρ : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hc : NeighbouringFineVertexCells) (ht : TopEdgesAndCubes)
    [Fintype (Fin 3 × Vertex L n k 0)]
    (Kf : (Edge L n k 0 → ComplexMatrix2) →
      KernelMatrix (Fin 3 × Vertex L n k 0) (Fin 3 × Vertex L n k k))
    (G : (Edge L n k 0 → ComplexMatrix2) → (Vertex L n k 0 → ComplexMatrix2) → Vertex L n k k →
      ComplexMatrix2)
    (hg : ∀ v ∈ smallFormBall L n k ρ, Represents (Kf v)
      ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs (vertexCoordinate (Vertex L n k k)) (G v)))
    (hr : ∀ y : Vertex L n k k, ∀ v ∈ smallFormBall L n k ρ, ∀ v' ∈ smallFormBall L n k ρ,
      ∀ l l' : Vertex L n k 0 → ComplexMatrix2,
        (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) →
        (∀ x, l' x ∈ PeriodicLattice.complexLieAlgebra) →
        (∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.refinedBlock k y → l x = l' x) →
        EqOn v v' (PeriodicLattice.bondsInside (PeriodicLattice.refinedBlock k y)) →
          G v l y = G v' l' y) :
    (∀ p q, ∀ v ∈ smallFormBall L n k ρ, ∀ v' ∈ smallFormBall L n k ρ,
      EqOn v v' (edgesNearCell 2 (vertexCell p)) → Kf v p q = Kf v' p q) ∧
    (∀ v ∈ smallFormBall L n k ρ, ∀ p q, 2 < cellDist (vertexCell p) (colouredVertexCell q) →
      Kf v p q = 0) := by
  classical
  have h0 := (ht L hL n k hn hk).1
  have mem : ∀ (c : Fin 3 × Vertex L n k 0 → ℂ) x,
      ofPauliCoeffs c x ∈ PeriodicLattice.complexLieAlgebra :=
    fun c x => ofPauliCoeffs_mem_traceless c x
  refine ⟨fun p q v hv v' hv' h => ?_, fun v hv p q hfar => ?_⟩
  · rw [entry_eq_of_represents (hg v hv) p q, entry_eq_of_represents (hg v' hv') p q]
    exact congrArg (pauliCoeff p.1) (hr p.2 v hv v' hv' _ _ (mem _) (mem _) (fun _ _ => rfl)
      fun b hb => h (mem_edgesNearCell_of_inside hL hn hk hc ht p.2 hb))
  · have hq : ¬ (q.2 : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k p.2 :=
      fun h => by
        have e : colouredVertexCell q = p.2 := fineVertexCell_eq_of_mem hL hn hk hc ht h
        have : cellDist (vertexCell p) (colouredVertexCell q) = 0 := by
          rw [e]
          exact h0 _
        linarith
    have e : ∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.refinedBlock k p.2 →
        ofPauliCoeffs (indicatorVec q) x = ofPauliCoeffs (0 : Fin 3 × Vertex L n k 0 → ℂ) x := by
      intro x hx
      have hne : x ≠ q.2 := fun he => hq (he ▸ hx)
      simp only [ofPauliCoeffs]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h0 : indicatorVec q (a, x) = 0 := if_neg fun he => hne (congrArg Prod.snd he)
      rw [h0]
      rfl
    have z : (vertexCoordinate (Vertex L n k 0)).mapOnCoeffs (vertexCoordinate (Vertex L n k k))
        (G v) 0 p = 0 :=
      congrFun (map_zero_of_represents (hg v hv)) p
    rw [entry_eq_of_represents (hg v hv) p q]
    have e₂ := hr p.2 v hv v hv _ _ (mem (indicatorVec q)) (mem 0) e fun _ _ => rfl
    exact Eq.trans (congrArg (pauliCoeff p.1) e₂) z
end SeriesExpansions
section Final
variable {L n k : ℕ}
private lemma meshAt_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj : j ≤ k) :
    meshAt L k j ≤ 1 := by apply _root_.YangMills.SharedProofs.p8023 <;> assumption
private lemma smallFormBall_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    smallFormBall L n k ρ ⊆ smallFormBall L n k ρ' :=
  fun _ hv => ⟨hv.1, hv.2.trans (ENNReal.ofReal_le_ofReal h)⟩
private lemma maxOperatorNorm_toReal_le {ρ : ℝ} (hρ : 0 ≤ ρ) {v : Edge L n k 0 → ComplexMatrix2}
    (hv : v ∈ smallFormBall L n k ρ) : (maxOperatorNorm v).toReal ≤ ρ :=
  ENNReal.toReal_le_of_le_ofReal hρ hv.2
private lemma meanIterate_near_one {r δ ρ C : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hδ : ∀ X : ComplexMatrix2, ‖X‖ < δ → ‖NormedSpace.exp X - 1‖ < r) (hρ : 0 ≤ ρ)
    (hρδ : 20 * ρ < δ) {v : Edge L n k 0 → ComplexMatrix2} (hv : v ∈ smallFormBall L n k ρ)
    (hF : PlainMeanIterates.PointwiseConditions L n k C v) :
    ∀ j < k, meanIterate (remainderGaugeField v) j ∈
        fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
      ∀ b, ComplexMatrix2.operatorNorm (meanIterate (remainderGaugeField v) j b - 1) < r := by
  intro j hj
  refine ⟨(hF.mem_small j hj).1, fun b => ?_⟩
  obtain ⟨A, hA, e, hs⟩ := hF.exists_log j hj.le
  have hl := meshAt_le_one (k := k) hL hj.le
  have hl0 : 0 ≤ meshAt L k j := by
    unfold meshAt
    positivity
  have hv' := maxOperatorNorm_toReal_le hρ hv
  have hAb : ∀ x, ‖A x‖ < δ := by
    intro x
    have h1 : ENNReal.ofReal (ComplexMatrix2.operatorNorm (A x)) ≤ maxOperatorNorm A :=
      le_iSup (fun i => ENNReal.ofReal (ComplexMatrix2.operatorNorm (A i))) x
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans hs)
    have h3 : 10 * meshAt L k j * (maxOperatorNorm v).toReal ≤ 10 * ρ := by
      have := ENNReal.toReal_nonneg (a := maxOperatorNorm v)
      nlinarith
    have : ‖A x‖ ≤ 10 * ρ := h2.trans h3
    linarith
  rw [e]
  unfold PeriodicLattice.expTwist
  split_ifs with hp
  · have := hδ (Complex.I • A b) (by rw [norm_smul]; simpa using hAb b)
    simpa [ComplexMatrix2.matExp] using this
  · have := hδ (-(Complex.I • A b.opposite)) (by rw [norm_neg, norm_smul]; simpa using hAb _)
    rw [Matrix.exp_neg] at this
    simpa [ComplexMatrix2.matExp] using this
set_option maxHeartbeats 1600000 in
theorem meanKernelsAreLocalNearCells_holds (hP : PlainMeanIterates.Claim)
    (hI : Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hG : MeanKernelsRepresent.Claim) (hK : Tower.ThreeMapKernels.Claim)
    (ht : TopEdgesAndCubes) (hc : NeighbouringFineVertexCells)
    (ho : PeriodicLattice.BondEndpointsOrientation.Statement) :
    MeanKernelsAreLocalNearCells := by
  intro L hL
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hs₁⟩ := hP L hL
  obtain ⟨hρ₂, -, hC₂, hs₂⟩ := hI.1 L hL
  set ρ₂ := Tower.IteratedSmallFieldMeans.smallRadius L with hρ₂def
  set C₂ := Tower.IteratedSmallFieldMeans.boundConstant L with hC₂def
  obtain ⟨r, hr, hg⟩ := hG L hL
  obtain ⟨δ, hδ, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ X : ComplexMatrix2, ‖X‖ < δ → ‖NormedSpace.exp X - 1‖ < r := by
    have hcont : ContinuousAt (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) 0 :=
      (NormedSpace.exp_analytic (𝕂 := ℂ) (0 : ComplexMatrix2)).differentiableAt.continuousAt
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hcont r hr
    refine ⟨δ, hδ, fun X hX => ?_⟩
    have := h (x := X) (by simpa [dist_eq_norm] using hX)
    simpa [dist_eq_norm, NormedSpace.exp_zero] using this
  obtain ⟨ρ, hρ, l₁, l₂, l₃⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₁ ∧ ρ ≤ ρ₂ ∧ 20 * ρ < δ :=
    ⟨min (min ρ₁ ρ₂) (δ / 40), lt_min (lt_min hρ₁ hρ₂) (by positivity),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      by have := min_le_right (min ρ₁ ρ₂) (δ / 40); linarith⟩
  have hC0 : 0 ≤ C₁ + C₂ := by linarith
  refine ⟨ρ, C₁ + C₂, 2, hρ, hC0, by norm_num, fun k hk => ⟨0, fun n _ hn => ?_⟩⟩
  intro _ _ _ _ _ _ _ _
  classical
  have hA := hs₁ k n hk hn
  have hB := (hs₂ k hk).1 n hn
  have hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => ((ho ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ 0 (Nat.zero_le k)).2.2.2 b).2.2.2.2.2
  have hη : 0 < finestMesh L k := by
    have : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    unfold finestMesh meshAt
    exact zpow_pos this _
  have htop : meshAt L k k = 1 := by simp [meshAt]
  have sm₁ : ∀ v, v ∈ smallFormBall L n k ρ → v ∈ smallFormBall L n k ρ₁ :=
    fun v hv => smallFormBall_mono l₁ hv
  have sm₂ : ∀ v, v ∈ smallFormBall L n k ρ → v ∈ smallFormBall L n k ρ₂ :=
    fun v hv => smallFormBall_mono l₂ hv
  have near : ∀ v ∈ smallFormBall L n k ρ, _ := fun v hv =>
    meanIterate_near_one (k := k) hL hδr hρ.le l₃ hv (hA.pointwise v (sm₁ v hv))
  have gQ : ∀ v ∈ smallFormBall L n k ρ, Represents (rescaledOperators L n k (remainderGaugeField v)).Q
      ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
        (Tower.IteratedSmallFieldMeans.rescaledCovMean (remainderGaugeField v))) := by
    intro v hv
    have hU := (hB.pointwise v (sm₂ v hv)).mem_smallIterate
    have hm := (((hK L hL k hk).1 n hn).2.2.2 _ hU).1.smul_represents (finestMesh L k : ℂ)
    have eM : ((finestMesh L k : ℝ) : ℂ) • (edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
        (iterCovariantDeriv L n k (remainderGaugeField v) k) =
        (edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
          (Tower.IteratedSmallFieldMeans.rescaledCovMean (remainderGaugeField v)) := by
      funext f ι
      exact (pauliCoeff_real_smul ι.1 hη.ne' _).symm
    rw [eM] at hm
    exact Classical.epsilon_spec (⟨_, hm⟩ : ∃ T, Represents T _)
  have gR : ∀ v ∈ smallFormBall L n k ρ, Represents (rescaledOperators L n k (remainderGaugeField v)).R
      ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs (vertexCoordinate (Vertex L n k k))
        (iterAdjointCubeAverage L n k (remainderGaugeField v) k)) := by
    intro v hv
    have hU := (hB.pointwise v (sm₂ v hv)).mem_smallIterate
    exact (((hK L hL k hk).1 n hn).2.2.2 _ hU).2.represents
  have gQu : ∀ v ∈ smallFormBall L n k ρ, Represents (meanKernelQ L n k (remainderGaugeField v))
      ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k)
        fun B => finestMesh L k • meanCovariant (remainderGaugeField v) k B) :=
    fun v hv => (hg n k hn hk _ (near v hv)).1
  have gRu : ∀ v ∈ smallFormBall L n k ρ, Represents (meanKernelR L n k (remainderGaugeField v))
      ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs (vertexCoordinate (Vertex L n k k))
        (composedCubeAverage (quietPoint (remainderGaugeField v)) k)) :=
    fun v hv => (hg n k hn hk _ (near v hv)).2
  obtain ⟨rQ₁, rQ₂⟩ := edge_kernel_rows_local (ρ := ρ) hL hn hk hc ht hx
    (fun v => (rescaledOperators L n k (remainderGaugeField v)).Q)
    (fun v => Tower.IteratedSmallFieldMeans.rescaledCovMean (remainderGaugeField v)) gQ
    (fun c v hv v' hv' B hB₁ B' hB₂ h₁ h₂ => hB.locality.local_Q c v (sm₂ v hv) v'
      (sm₂ v' hv') B hB₁ B' hB₂ h₁ h₂)
  obtain ⟨rU₁, rU₂⟩ := edge_kernel_rows_local (ρ := ρ) hL hn hk hc ht hx
    (fun v => meanKernelQ L n k (remainderGaugeField v))
    (fun v B => finestMesh L k • meanCovariant (remainderGaugeField v) k B) gQu
    (fun c v hv v' hv' B hB₁ B' hB₂ h₁ h₂ => by
      show finestMesh L k • meanCovariant (remainderGaugeField v) k B c =
        finestMesh L k • meanCovariant (remainderGaugeField v') k B' c
      rw [hA.locality.local_Q c v (sm₁ v hv) v' (sm₁ v' hv') B hB₁ B' hB₂ h₁ h₂])
  obtain ⟨rR₁, rR₂⟩ := vertex_kernel_rows_local (ρ := ρ) hL hn hk hc ht
    (fun v => (rescaledOperators L n k (remainderGaugeField v)).R)
    (fun v => iterAdjointCubeAverage L n k (remainderGaugeField v) k) gR
    (fun y v hv v' hv' l l' a₁ a₂ a₃ a₄ => hB.locality.local_R y v (sm₂ v hv) v'
      (sm₂ v' hv') l l' a₁ a₂ a₃ a₄)
  obtain ⟨rV₁, rV₂⟩ := vertex_kernel_rows_local (ρ := ρ) hL hn hk hc ht
    (fun v => meanKernelR L n k (remainderGaugeField v))
    (fun v => composedCubeAverage (quietPoint (remainderGaugeField v)) k) gRu
    (fun y v hv v' hv' l l' a₁ a₂ a₃ a₄ => hA.locality.local_R y v (sm₁ v hv) v'
      (sm₁ v' hv') l l' a₁ a₂ a₃ a₄)
  have bound : ∀ {σ σ' : Type} [Fintype (Fin 3 × σ)] [Fintype (Fin 3 × σ')]
      [DecidableEq (Fin 3 × σ)] [DecidableEq (Fin 3 × σ')]
      {K : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')} {c : ℝ}, 0 ≤ c → c ≤ C₁ + C₂ →
      TorusOpNormLE (finestMesh L k) (meshAt L k k) K c →
      ‖unitNormScale L k • (Matrix.of K : Matrix (Fin 3 × σ') (Fin 3 × σ) ℂ)‖ ≤ C₁ + C₂ := by
    intro σ σ' _ _ _ _ K c hc0 hcC h
    rw [htop] at h
    exact (l2_opNorm_le_of_torusOpNormLE hη hc0 h).trans hcC
  have pC₁ : 0 ≤ C₁ := by linarith
  have pC₂ : 0 ≤ C₂ := by linarith
  refine ⟨⟨fun p q => ?_, fun v hv => ?_, fun p q v hv v' hv' h => ?_, fun v hv p q h => ?_⟩,
    ⟨fun p q => ?_, fun v hv => ?_, fun p q v hv v' hv' h => ?_, fun v hv p q h => ?_⟩,
    ⟨fun p q => ?_, fun v hv => ?_, fun p q v hv v' hv' h => ?_, fun v hv p q h => ?_⟩,
    ⟨fun p q => ?_, fun v hv => ?_, fun p q v hv v' hv' h => ?_, fun v hv p q h => ?_⟩⟩
  · exact holomorphicInEntries_mono_mul (hB.holomorphic.kernel_Q p q) hρ l₂ _
  · exact bound (σ := PositiveEdge L n k 0) (σ' := PositiveEdge L n k k) pC₂ (by linarith)
      (hB.pointwise v (sm₂ v hv)).opNorm_Q
  · exact congrArg (unitNormScale L k * ·) (rQ₁ p q v hv v' hv' h)
  · exact (congrArg (unitNormScale L k * ·) (rQ₂ v hv p q h)).trans (mul_zero _)
  · exact holomorphicInEntries_mono_mul (hA.holomorphic.kernel_Q p q) hρ l₁ _
  · exact bound (σ := PositiveEdge L n k 0) (σ' := PositiveEdge L n k k) pC₁ (by linarith)
      (hA.pointwise v (sm₁ v hv)).opNorm_Q
  · exact congrArg (unitNormScale L k * ·) (rU₁ p q v hv v' hv' h)
  · exact (congrArg (unitNormScale L k * ·) (rU₂ v hv p q h)).trans (mul_zero _)
  · exact holomorphicInEntries_mono_mul (hB.holomorphic.kernel_R p q) hρ l₂ _
  · exact bound (σ := Vertex L n k 0) (σ' := Vertex L n k k) pC₂ (by linarith)
      (hB.pointwise v (sm₂ v hv)).opNorm_R
  · exact congrArg (unitNormScale L k * ·) (rR₁ p q v hv v' hv' h)
  · exact (congrArg (unitNormScale L k * ·) (rR₂ v hv p q h)).trans (mul_zero _)
  · exact holomorphicInEntries_mono_mul (hA.holomorphic.kernel_R p q) hρ l₁ _
  · exact bound (σ := Vertex L n k 0) (σ' := Vertex L n k k) pC₁ (by linarith)
      (hA.pointwise v (sm₁ v hv)).opNorm_R
  · exact congrArg (unitNormScale L k * ·) (rV₁ p q v hv v' hv' h)
  · exact (congrArg (unitNormScale L k * ·) (rV₂ v hv p q h)).trans (mul_zero _)
end Final
end YangMills.Construction.RunningCouplingSlope.MeanKernelsLocal
end
