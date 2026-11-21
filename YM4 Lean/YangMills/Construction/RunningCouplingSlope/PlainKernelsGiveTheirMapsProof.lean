import YangMills.Construction.Lattice.AmbientSpaceOfTheRealPairsOnADomain
import YangMills.Construction.RunningCouplingSlope.PlainCovariantStepOnTheForms
import YangMills.Construction.RunningCouplingSlope.PlainIteratesNearOne
import YangMills.Construction.RunningCouplingSlope.PlainKernelsGiveTheirMaps
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace MeanKernels
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators YangMills.Construction.Matrices
private theorem represents_of_linear {N N' : Type} [Finite N] [Finite N'] (M : (N → ℂ) → N' → ℂ)
    (hM : ∀ (w : ℂ) (f g : N → ℂ), M (w • f + g) = w • M f + M g) :
    Represents (kernelOfMap M) M := by
  classical
  let _ : Fintype N := Fintype.ofFinite N
  let _ : Fintype N' := Fintype.ofFinite N'
  have h0 : M 0 = 0 := by
    have h := hM 1 0 0
    simpa using h
  let Ml : (N → ℂ) →ₗ[ℂ] (N' → ℂ) :=
    { toFun := M
      map_add' := fun f g => by simpa using hM 1 f g
      map_smul' := fun w f => by simpa [h0] using hM w f 0 }
  have hex : ∃ T : KernelMatrix N N', Represents T M := by
    refine ⟨fun ι' ι => M (fun m => if ι = m then 1 else 0) ι', fun f => ⟨fun ι' => ?_, ?_⟩⟩
    · exact Summable.of_finite
    · funext ι'
      have h1 := congrFun (LinearMap.pi_apply_eq_sum_univ Ml f) ι'
      change M f ι' = _ at h1
      rw [h1]
      simp only [applyKernel, tsum_fintype, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun ι _ => by
        change M _ ι' * f ι = f ι * M _ ι'
        rw [mul_comm]
  exact Classical.epsilon_spec hex
private theorem sum_smul_pauli_mem (c : Fin 3 → ℂ) :
    (∑ b, c b • ComplexMatrix2.pauliFamily b) ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem pauliCoeff_smul_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (w : ℂ) (a : Fin 3) :
    pauliCoeff a (w • X + Y) = w * pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.pauliCoeff_smul_add <;> assumption
variable {L n k d : ℕ}
private theorem ofPauliCoeffs_smul_add {σ : Type} (w : ℂ) (f g : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (w • f + g) = w • ofPauliCoeffs f + ofPauliCoeffs g := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.ofPauliCoeffs_smul_add <;> assumption
private theorem toPauliCoeffs_smul_add {σ : Type} {f g : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) (w : ℂ) :
    toPauliCoeffs (w • f + g) = w • toPauliCoeffs f + toPauliCoeffs g := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.toPauliCoeffs_smul_add <;> assumption
private def formOfCoeffs (f : Fin 3 × PositiveEdge L n k d → ℂ) : Edge L n k d → ComplexMatrix2 :=
  open Classical in
    extendOddly fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0
private theorem formOfCoeffs_mem
    (hX : ∀ b : Edge L n k d, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Fin 3 × PositiveEdge L n k d → ℂ) : formOfCoeffs f ∈ complexEdgeForms L n k d := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.edgeFormOfCoeffs_mem <;> assumption
private theorem formOfCoeffs_smul_add (w : ℂ) (f g : Fin 3 × PositiveEdge L n k d → ℂ) :
    formOfCoeffs (w • f + g) = w • formOfCoeffs f + formOfCoeffs g := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.edgeFormOfCoeffs_smul_add <;> assumption
private theorem represents_edges {i i' : ℕ}
    (hX : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Finite (Fin 3 × PositiveEdge L n k i)] [Finite (Fin 3 × PositiveEdge L n k i')]
    (m : (Edge L n k i → ComplexMatrix2) → Edge L n k i' → ComplexMatrix2)
    (hm : ∀ B ∈ complexEdgeForms L n k i, m B ∈ complexEdgeForms L n k i')
    (hl : ∀ B ∈ complexEdgeForms L n k i, ∀ B' ∈ complexEdgeForms L n k i, ∀ w : ℂ,
      m (w • B + B') = w • m B + m B') :
    Represents ((edgePauliCoordinates L n k i).kernel (edgePauliCoordinates L n k i') m)
      ((edgePauliCoordinates L n k i).mapOnCoeffs (edgePauliCoordinates L n k i') m) := by
  change Represents (kernelOfMap fun f : Fin 3 × PositiveEdge L n k i → ℂ =>
      toPauliCoeffs (restrictToPositiveEdges (m (formOfCoeffs f))))
    fun f : Fin 3 × PositiveEdge L n k i → ℂ => toPauliCoeffs (restrictToPositiveEdges (m (formOfCoeffs f)))
  refine represents_of_linear _ fun w f g => ?_
  rw [formOfCoeffs_smul_add, hl _ (formOfCoeffs_mem hX f) _ (formOfCoeffs_mem hX g)]
  funext ι
  exact pauliCoeff_smul_add ((hm _ (formOfCoeffs_mem hX f)).1 _ ι.2.2)
    ((hm _ (formOfCoeffs_mem hX g)).1 _ ι.2.2) w ι.1
private theorem represents_vertices {σ σ' : Type} [Finite (Fin 3 × σ)] [Finite (Fin 3 × σ')]
    (m : (σ → ComplexMatrix2) → σ' → ComplexMatrix2)
    (hm : ∀ l : σ → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
      ∀ y, m l y ∈ ComplexMatrix2.traceless)
    (hl : ∀ l l' : σ → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
      (∀ x, l' x ∈ ComplexMatrix2.traceless) → ∀ w : ℂ, m (w • l + l') = w • m l + m l') :
    Represents ((vertexCoordinate σ).kernel (vertexCoordinate σ') m)
      ((vertexCoordinate σ).mapOnCoeffs (vertexCoordinate σ') m) := by
  have hof : ∀ (f : Fin 3 × σ → ℂ) x, ofPauliCoeffs f x ∈ ComplexMatrix2.traceless :=
    fun f x => sum_smul_pauli_mem _
  change Represents (kernelOfMap fun f : Fin 3 × σ → ℂ => toPauliCoeffs (m (ofPauliCoeffs f)))
    fun f : Fin 3 × σ → ℂ => toPauliCoeffs (m (ofPauliCoeffs f))
  refine represents_of_linear _ fun w f g => ?_
  rw [ofPauliCoeffs_smul_add, hl _ _ (hof f) (hof g)]
  exact toPauliCoeffs_smul_add (hm _ (hof f)) (hm _ (hof g)) w
end MeanKernels
open MeanKernels YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
  YangMills.Construction.Matrices in
theorem meanKernelsRepresent_holds (hS : MeanCovariantStepOnForms)
    (hI : MeanIteratesTendToOne) :
    MeanKernelsRepresent := by
  intro L hL k n hk hn
  classical
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have : NeZero L := ⟨by omega⟩
  have hX : ∀ i, i ≤ k → ∀ b : Edge L n k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun i hi b =>
    YangMills.Construction.PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [YangMills.Construction.PeriodicLattice.levelDepth]; omega) b
  have hfinB : ∀ i, Finite (Fin 3 × PositiveEdge L n k i) := fun i => by
    have : Finite (Edge L n k i) := YangMills.Construction.PeriodicLattice.instFiniteBond _
    infer_instance
  have hfinS : ∀ i, Finite (Fin 3 × Vertex L n k i) := fun i => by
    have : Finite (Vertex L n k i) := YangMills.Construction.PeriodicLattice.instFiniteSite _
    infer_instance
  have hev : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)), ∀ i ∈ Finset.range k,
      (∀ B ∈ complexEdgeForms L n k i, meanCovariantStep (meanIterate U i) B ∈
        complexEdgeForms L n k (i + 1)) ∧
      (∀ B ∈ complexEdgeForms L n k i, ∀ B' ∈ complexEdgeForms L n k i, ∀ w : ℂ,
        meanCovariantStep (meanIterate U i) (w • B + B') =
          w • meanCovariantStep (meanIterate U i) B + meanCovariantStep (meanIterate U i) B') ∧
      (∀ B ∈ edgeFormSpace L n k i, meanCovariantStep (meanIterate U i) B ∈
        edgeFormSpace L n k (i + 1)) ∧
      (∀ l : Vertex L n k i → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) →
        ∀ y, adjointCubeAverage (meanIterate U i) l y ∈ ComplexMatrix2.hermitianTraceless) ∧
      (∀ l : Vertex L n k i → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        ∀ y, adjointCubeAverage (meanIterate U i) l y ∈ ComplexMatrix2.traceless) ∧
      ∀ l l' : Vertex L n k i → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        (∀ x, l' x ∈ ComplexMatrix2.traceless) → ∀ w : ℂ,
        adjointCubeAverage (meanIterate U i) (w • l + l') =
          w • adjointCubeAverage (meanIterate U i) l + adjointCubeAverage (meanIterate U i) l' := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    filter_upwards [(hI L hL k n hn i hik.le).eventually (hS L hL n k i hn hk hik)] with U f
    obtain ⟨f₁, f₂, f₃, -, f₅, f₆, f₇, -⟩ := f
    exact ⟨f₁, f₂, f₃, f₅, f₆, f₇⟩
  unfold EventuallyNearIdentity
  filter_upwards [hev] with U hU
  have hQm : ∀ j, j ≤ k → ∀ B ∈ complexEdgeForms L n k 0,
      meanCovariant U j B ∈ complexEdgeForms L n k j := by
    intro j
    induction j with
    | zero => intro _ B hB; exact hB
    | succ j ih =>
      intro hj B hB
      exact (hU j (Finset.mem_range.2 (by omega))).1 _ (ih (by omega) B hB)
  have hQl : ∀ j, j ≤ k → ∀ B ∈ complexEdgeForms L n k 0, ∀ B' ∈ complexEdgeForms L n k 0, ∀ w : ℂ,
      meanCovariant U j (w • B + B') = w • meanCovariant U j B + meanCovariant U j B' := by
    intro j
    induction j with
    | zero => intro _ B _ B' _ w; rfl
    | succ j ih =>
      intro hj B hB B' hB' w
      change meanCovariantStep (meanIterate U j) (meanCovariant U j (w • B + B')) =
        w • meanCovariantStep (meanIterate U j) (meanCovariant U j B) +
          meanCovariantStep (meanIterate U j) (meanCovariant U j B')
      rw [ih (by omega) B hB B' hB' w]
      exact (hU j (Finset.mem_range.2 (by omega))).2.1 _ (hQm j (by omega) B hB) _
        (hQm j (by omega) B' hB') w
  have hRm : ∀ j, j ≤ k → ∀ l : Vertex L n k 0 → ComplexMatrix2,
      (∀ x, l x ∈ ComplexMatrix2.traceless) →
      ∀ y, composedCubeAverage (quietPoint U) j l y ∈ ComplexMatrix2.traceless := by
    intro j
    induction j with
    | zero => intro _ l hl y; exact hl y
    | succ j ih =>
      intro hj l hl y
      exact (hU j (Finset.mem_range.2 (by omega))).2.2.2.2.1 _ (ih (by omega) l hl) y
  have hRl : ∀ j, j ≤ k → ∀ l l' : Vertex L n k 0 → ComplexMatrix2,
      (∀ x, l x ∈ ComplexMatrix2.traceless) → (∀ x, l' x ∈ ComplexMatrix2.traceless) → ∀ w : ℂ,
      composedCubeAverage (quietPoint U) j (w • l + l') =
        w • composedCubeAverage (quietPoint U) j l + composedCubeAverage (quietPoint U) j l' := by
    intro j
    induction j with
    | zero => intro _ l l' _ _ w; rfl
    | succ j ih =>
      intro hj l l' hl hl' w
      change adjointCubeAverage (meanIterate U j) (composedCubeAverage (quietPoint U) j (w • l + l')) =
        w • adjointCubeAverage (meanIterate U j) (composedCubeAverage (quietPoint U) j l) +
          adjointCubeAverage (meanIterate U j) (composedCubeAverage (quietPoint U) j l')
      rw [ih (by omega) l l' hl hl' w]
      exact (hU j (Finset.mem_range.2 (by omega))).2.2.2.2.2 _ _ (hRm j (by omega) l hl)
        (hRm j (by omega) l' hl') w
  have := hfinB 0
  have := hfinB k
  have := hfinS 0
  have := hfinS k
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, hQl k le_rfl, hRl k le_rfl⟩
  · have := hfinB j
    have := hfinB (j + 1)
    refine represents_edges (hX j hj.le) _ (fun B hB => ?_) fun B hB B' hB' w => ?_
    · exact Submodule.smul_of_tower_mem _ _ ((hU j (Finset.mem_range.2 hj)).1 B hB)
    · rw [(hU j (Finset.mem_range.2 hj)).2.1 B hB B' hB' w, smul_add, smul_comm]
  · refine represents_edges (hX 0 (Nat.zero_le k)) _ (fun B hB => ?_) fun B hB B' hB' w => ?_
    · exact Submodule.smul_of_tower_mem _ _ (hQm k le_rfl B hB)
    · rw [hQl k le_rfl B hB B' hB' w, smul_add, smul_comm]
  · exact represents_vertices _ (hRm k le_rfl) (hRl k le_rfl)
  · intro j
    induction j with
    | zero => intro _ B hB; exact hB
    | succ j ih =>
      intro hj B hB
      exact (hU j (Finset.mem_range.2 (by omega))).2.2.1 _ (ih (by omega) B hB)
  · intro j
    induction j with
    | zero => intro _ l hl y; exact hl y
    | succ j ih =>
      intro hj l hl y
      exact (hU j (Finset.mem_range.2 (by omega))).2.2.2.1 _ (ih (by omega) l hl) y
end YangMills.Construction.RunningCouplingSlope
end
