import YangMills.Construction.Towers.FreeOperatorsAreRealOfFiniteRangeAndTrivialOnTheColour
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FreeOperatorsRealLocal
open PeriodicOperators (KernelMatrix applyKernel compKernel unitKernel IsFiniteRange
  kernelTranspose PeriodicData colourVertices colourEdges colourFaces)
open PlaneWaveCalculus (IsRealColourTrivial FreeOpsRealFiniteRange)
open RescaledConditions (complementProj TrivialRelations)
open Matrices (ComplexMatrix2)
section Closure
variable {τ τ' τ'' : Type}
theorem im_tsum_eq_zero {α : Type} (f : α → ℂ) (hf : ∀ i, (f i).im = 0) :
    (∑' i, f i).im = 0 := by
  have e : ∑' i, f i = ((∑' i, (f i).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun i => Complex.ext (by simp) (by simp [hf i])
  rw [e]
  exact Complex.ofReal_im _
theorem add {A B : KernelMatrix (Fin 3 × τ) (Fin 3 × τ')} (hA : IsRealColourTrivial A)
    (hB : IsRealColourTrivial B) : IsRealColourTrivial (A + B) := by
  refine ⟨fun ι' ι => ?_, fun a a' y x h => ?_, fun a a' y x => ?_⟩
  · simp [hA.1 ι' ι, hB.1 ι' ι]
  · simp [hA.2.1 a a' y x h, hB.2.1 a a' y x h]
  · simp [hA.2.2 a a' y x, hB.2.2 a a' y x]
theorem sub {A B : KernelMatrix (Fin 3 × τ) (Fin 3 × τ')} (hA : IsRealColourTrivial A)
    (hB : IsRealColourTrivial B) : IsRealColourTrivial (A - B) := by
  refine ⟨fun ι' ι => ?_, fun a a' y x h => ?_, fun a a' y x => ?_⟩
  · simp [hA.1 ι' ι, hB.1 ι' ι]
  · simp [hA.2.1 a a' y x h, hB.2.1 a a' y x h]
  · simp [hA.2.2 a a' y x, hB.2.2 a a' y x]
theorem compKernel_apply_diag {A : KernelMatrix (Fin 3 × τ) (Fin 3 × τ')}
    {B : KernelMatrix (Fin 3 × τ'') (Fin 3 × τ)} (hB : IsRealColourTrivial B)
    (a : Fin 3) (y : τ') (x : τ'') :
    compKernel A B (a, y) (a, x) = ∑' z : τ, A (a, y) (a, z) * B (a, z) (a, x) := by
  have hinj : Function.Injective fun z : τ => ((a, z) : Fin 3 × τ) := fun z z' h =>
    (Prod.mk.inj h).2
  refine (hinj.tsum_eq (f := fun ι => A (a, y) ι * B ι (a, x)) ?_).symm
  rintro ⟨b, z⟩ hbz
  by_cases hb : b = a
  · subst hb
    exact ⟨z, rfl⟩
  · exact absurd (by simp [hB.2.1 a b z x hb]) hbz
theorem comp {A : KernelMatrix (Fin 3 × τ) (Fin 3 × τ')}
    {B : KernelMatrix (Fin 3 × τ'') (Fin 3 × τ)} (hA : IsRealColourTrivial A)
    (hB : IsRealColourTrivial B) : IsRealColourTrivial (compKernel A B) := by
  refine ⟨fun ι' ι => ?_, fun a a' y x h => ?_, fun a a' y x => ?_⟩
  · exact im_tsum_eq_zero _ fun i => by simp [Complex.mul_im, hA.1 ι' i, hB.1 i ι]
  · have e : ∀ ι : Fin 3 × τ, A (a', y) ι * B ι (a, x) = 0 := by
      rintro ⟨b, z⟩
      by_cases hb : b = a
      · subst hb
        simp [hA.2.1 b a' y z h]
      · simp [hB.2.1 a b z x hb]
    change ∑' ι, A (a', y) ι * B ι (a, x) = 0
    simp [e]
  · rw [compKernel_apply_diag hB, compKernel_apply_diag hB]
    exact tsum_congr fun z => by rw [hA.2.2 a a' y z, hB.2.2 a a' z x]
theorem wTranspose_const (u v : ℝ) {A : KernelMatrix (Fin 3 × τ) (Fin 3 × τ')}
    (hA : IsRealColourTrivial A) :
    IsRealColourTrivial
      (PeriodicOperators.wTranspose (fun _ : Fin 3 × τ => u) (fun _ : Fin 3 × τ' => v) A) := by
  refine ⟨fun ι' ι => ?_, fun a a' y x h => ?_, fun a a' y x => ?_⟩
  · simp [PeriodicOperators.wTranspose, Complex.mul_im, hA.1 ι ι']
  · simp [PeriodicOperators.wTranspose, hA.2.1 a' a x y (Ne.symm h)]
  · simp [PeriodicOperators.wTranspose, hA.2.2 a a' x y]
theorem unit : IsRealColourTrivial (unitKernel (Fin 3 × τ)) := by
  classical
  refine ⟨fun ι' ι => ?_, fun a a' y x h => ?_, fun a a' y x => ?_⟩
  · simp only [unitKernel]
    split_ifs <;> simp
  · simp [unitKernel, h]
  · simp [unitKernel]
end Closure
section Multiples
variable {τ τ' τ'' : Type}
def PreservesRealMultiples (m : (τ → ComplexMatrix2) → τ' → ComplexMatrix2) : Prop :=
  ∀ g : τ → ℝ, ∃ h : τ' → ℝ, ∀ M : ComplexMatrix2,
    m (fun x => (g x : ℂ) • M) = fun y => (h y : ℂ) • M
theorem PreservesRealMultiples.comp {m : (τ → ComplexMatrix2) → τ' → ComplexMatrix2}
    {m' : (τ' → ComplexMatrix2) → τ'' → ComplexMatrix2}
    (hm : PreservesRealMultiples m) (hm' : PreservesRealMultiples m') :
    PreservesRealMultiples fun f => m' (m f) := by
  intro g
  obtain ⟨h, hh⟩ := hm g
  obtain ⟨h', hh'⟩ := hm' h
  exact ⟨h', fun M => by simp only [hh, hh']⟩
theorem PreservesRealMultiples.real_smul {m : (τ → ComplexMatrix2) → τ' → ComplexMatrix2}
    (hm : PreservesRealMultiples m) (c : ℝ) : PreservesRealMultiples fun f => c • m f := by
  intro g
  obtain ⟨h, hh⟩ := hm g
  refine ⟨fun y => c * h y, fun M => ?_⟩
  funext y
  simp only [hh, Pi.smul_apply]
  ext i j
  simp
  ring
theorem composeFromZero_preserves {S : ℕ → Type}
    {step : ∀ j, (S j → ComplexMatrix2) → S (j + 1) → ComplexMatrix2}
    (h : ∀ j, PreservesRealMultiples (step j)) (n : ℕ) :
    PreservesRealMultiples (composeFromZero (F := fun j => S j → ComplexMatrix2) step n) := by
  induction n with
  | zero => exact fun g => ⟨g, fun _ => rfl⟩
  | succ n ih => exact ih.comp (h n)
theorem finsum_mem_ofReal_smul {ι : Type} (A : Set ι) (f : ι → ℝ) (M : ComplexMatrix2) :
    ∑ᶠ x ∈ A, (f x : ℂ) • M = ((∑ᶠ x ∈ A, f x : ℝ) : ℂ) • M := by
  have e : (A.indicator fun x => (f x : ℂ) • M) = fun x => ((A.indicator f x : ℝ) : ℂ) • M := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [finsum_mem_def, finsum_mem_def, e, ← finsum_smul]
  congr 1
  exact (Complex.ofRealHom.toAddMonoidHom.map_finsum_of_injective Complex.ofReal_injective _).symm
theorem edgeFormPathSum_ofReal_smul {s : ℝ} (g : InfiniteLattice.Link s → ℝ)
    (M : ComplexMatrix2) (γ : List (InfiniteLattice.Link s)) :
    FullSpace.edgeFormPathSum (fun b => (g b : ℂ) • M) γ = (((γ.map g).sum : ℝ) : ℂ) • M := by
  change ((γ.map fun b => (g b : ℂ) • M).sum) = _
  induction γ with
  | nil => simp
  | cons b γ ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [Complex.ofReal_add, add_smul]
theorem inverseFourthPowerWeight_smul (L : ℕ) (r : ℝ) (M : ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • ((r : ℂ) • M) =
      ((((L : ℝ) ^ (-4 : ℤ)) * r : ℝ) : ℂ) • M := by
  rw [smul_smul, PeriodicLattice.inverseFourthPowerWeight, Complex.ofReal_mul]
theorem vertexSmoothing_preserves (L : ℕ) (a a' : ℝ) :
    PreservesRealMultiples (FullSpace.vertexSmoothing L (a := a) (a' := a')) := by
  intro g
  refine ⟨fun y => ((L : ℝ) ^ (-4 : ℤ)) * ∑ᶠ x ∈ FullSpace.cubeVertices L a' y, g x,
    fun M => ?_⟩
  funext y
  simp only [FullSpace.vertexSmoothing]
  rw [finsum_mem_ofReal_smul, inverseFourthPowerWeight_smul]
theorem crossingSmoothing_preserves (L : ℕ) (a a' : ℝ) :
    PreservesRealMultiples (FullSpace.crossingSmoothing L (a := a) (a' := a')) := by
  intro g
  refine ⟨fun c => ((L : ℝ) ^ (-4 : ℤ)) *
    ∑ᶠ x ∈ FullSpace.cubeVertices L a' c.initial, ((FullSpace.crossingPath c x).map g).sum,
    fun M => ?_⟩
  funext c
  simp only [FullSpace.crossingSmoothing, edgeFormPathSum_ofReal_smul]
  rw [finsum_mem_ofReal_smul, inverseFourthPowerWeight_smul]
theorem scaledVertexCoboundary_preserves (L k j : ℕ) :
    PreservesRealMultiples (FullSpace.scaledVertexCoboundary (L := L) (k := k) (j := j)) := by
  intro g
  refine ⟨fun b => (meshAt L k j)⁻¹ * (g b.terminal - g b.initial), fun M => ?_⟩
  funext b
  simp only [FullSpace.scaledVertexCoboundary, FullSpace.vertexCoboundary, Pi.smul_apply,
    Complex.ofReal_mul, Complex.ofReal_sub, ← sub_smul]
  ext i l
  simp
  ring
theorem scaledEdgeCoboundary_preserves (L k j : ℕ) :
    PreservesRealMultiples (FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := j)) := by
  intro g
  refine ⟨fun p => (meshAt L k j)⁻¹ *
    (g (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) +
      g (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.lowAxis)
        p.highAxis) -
      g (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.highAxis)
        p.lowAxis) -
      g (InfiniteLattice.Link.forwardFrom p.corner p.highAxis)), fun M => ?_⟩
  funext p
  simp only [FullSpace.scaledEdgeCoboundary, FullSpace.edgeCoboundary, Pi.smul_apply]
  ext i l
  simp
  ring
end Multiples
theorem pauliCoeff_ofReal_smul (r : ℝ) (a a' : Fin 3) :
    pauliCoeff a' ((r : ℂ) • ComplexMatrix2.pauliFamily a) =
      (r : ℂ) * if a' = a then 1 else 0 := by
  have hmem : (r : ℂ) • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by
    refine Submodule.smul_mem _ _ ?_
    change Matrix.trace (ComplexMatrix2.pauliFamily a) = 0
    fin_cases a <;>
      simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY, OneLoop.pauliZ,
        Matrix.trace_fin_two]
  unfold pauliCoeff
  rw [dif_pos hmem]
  change (![_, _, _] : Fin 3 → ℂ) a' = _
  fin_cases a <;> fin_cases a' <;>
    simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY, OneLoop.pauliZ] <;>
      field_simp <;> ring
structure EvaluationOfRealMultiples (r : PauliComponentsOfSymmetricKernel) : Prop where
  unit : ∀ x : r.Place, ∃ g : r.space.index → ℝ, ∀ a : Fin 3,
    r.ofCoeffs (fun ι => unitKernel r.Index ι (a, x)) =
      fun i => (g i : ℂ) • ComplexMatrix2.pauliFamily a
  coeffs : ∃ place : r.Place → r.space.index, ∀ (h : r.space.index → ℝ) (a a' : Fin 3)
    (y : r.Place), r.coeffs (fun i => (h i : ℂ) • ComplexMatrix2.pauliFamily a) (a', y) =
      (h (place y) : ℂ) * if a' = a then 1 else 0
theorem ofPauliCoeffs_unit {τ : Type} (x : τ) :
    ∃ g : τ → ℝ, ∀ (a' : Fin 3) (x' : τ),
      ofPauliCoeffs (fun ι => unitKernel (Fin 3 × τ) ι (a', x)) x' =
        (g x' : ℂ) • ComplexMatrix2.pauliFamily a' := by
  classical
  refine ⟨fun x' => if x' = x then 1 else 0, fun a' x' => ?_⟩
  simp only [ofPauliCoeffs, unitKernel, Prod.mk.injEq]
  by_cases hx : x' = x
  · simp [hx, Finset.sum_ite_eq']
  · simp [hx]
theorem vertexCoordinates_ofRealMultiples (τ : Type) : EvaluationOfRealMultiples (vertexCoordinate τ) := by
  classical
  refine ⟨fun x => ?_, id, fun h a a' y => ?_⟩
  · obtain ⟨g, hg⟩ := ofPauliCoeffs_unit (τ := τ) x
    exact ⟨g, fun a => funext fun x' => hg a x'⟩
  · exact pauliCoeff_ofReal_smul _ _ _
theorem edgePauliCoordinates_reprOfRealMultiples (L k j : ℕ) : EvaluationOfRealMultiples (FullSpace.edgePauliCoordinates L k j) := by
  classical
  refine ⟨fun x => ?_, Subtype.val, fun h a a' y => ?_⟩
  · obtain ⟨g, hg⟩ := ofPauliCoeffs_unit
      (τ := FullSpace.PositiveEdge (meshAt L k j)) x
    let g₀ : InfiniteLattice.Link (meshAt L k j) → ℝ :=
      fun b => if hb : b.IsPositivelyOriented then g ⟨b, hb⟩ else 0
    refine ⟨fun b => if b.IsPositivelyOriented then g₀ b else -g₀ b.opposite, fun a => ?_⟩
    funext b
    have e : ∀ b' : InfiniteLattice.Link (meshAt L k j),
        (if hb : b'.IsPositivelyOriented then ofPauliCoeffs
          (fun ι => unitKernel (Fin 3 × FullSpace.PositiveEdge (meshAt L k j)) ι (a, x))
            ⟨b', hb⟩ else 0) = (g₀ b' : ℂ) • ComplexMatrix2.pauliFamily a := by
      intro b'
      by_cases hb : b'.IsPositivelyOriented
      · simp only [g₀, dif_pos hb]
        exact hg a _
      · simp [g₀, hb]
    change FullSpace.extendOddly (fun b' => if hb : b'.IsPositivelyOriented then ofPauliCoeffs
      (fun ι => unitKernel (Fin 3 × FullSpace.PositiveEdge (meshAt L k j)) ι (a, x))
        ⟨b', hb⟩ else 0) b = _
    simp only [FullSpace.extendOddly]
    by_cases hb : b.IsPositivelyOriented
    · simp only [if_pos hb]
      exact e b
    · simp only [if_neg hb]
      rw [e b.opposite]
      simp
  · exact pauliCoeff_ofReal_smul _ _ _
theorem of_represents {r r' : PauliComponentsOfSymmetricKernel} (hr : EvaluationOfRealMultiples r)
    (hr' : EvaluationOfRealMultiples r')
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hm : PreservesRealMultiples m) {A : KernelMatrix r.Index r'.Index}
    (hA : ∀ f, applyKernel A f = r.mapOnCoeffs r' m f) :
    IsRealColourTrivial A := by
  classical
  obtain ⟨place, hplace⟩ := hr'.coeffs
  have entry : ∀ (x : r.Place), ∃ c : r'.Place → ℝ, ∀ (a a' : Fin 3) (y : r'.Place),
      A (a', y) (a, x) = (c y : ℂ) * if a' = a then 1 else 0 := by
    intro x
    obtain ⟨g, hg⟩ := hr.unit x
    obtain ⟨h, hh⟩ := hm g
    refine ⟨fun y => h (place y), fun a a' y => ?_⟩
    have e₁ : applyKernel A (fun ι => unitKernel r.Index ι (a, x)) (a', y) = A (a', y) (a, x) := by
      refine (tsum_eq_single (a, x) fun b hb => ?_).trans ?_
      · simp [unitKernel, hb]
      · simp [unitKernel]
    rw [← e₁, hA]
    change r'.coeffs (m (r.ofCoeffs _)) (a', y) = _
    rw [hg a, hh, hplace]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a', y⟩ ⟨a, x⟩
    obtain ⟨c, hc⟩ := entry x
    rw [hc]
    split_ifs <;> simp
  · intro a a' y x h
    obtain ⟨c, hc⟩ := entry x
    rw [hc]
    simp [h]
  · intro a a' y x
    obtain ⟨c, hc⟩ := entry x
    rw [hc, hc]
    simp
theorem isFiniteRange_of {I I' : PeriodicData} {A : I'.Carrier → I.Carrier → ℂ}
    (h : FreeOperators.HasFiniteRangeEveryRate I I' A) : IsFiniteRange I I' A :=
  h.2.1
theorem claim_holds (hPeriodic : FreeOperators.FreeOperatorsArePeriodic)
    (hRelations : FullSpace.RescaledTrivialRelations) :
    Claim := by
  intro L hL k hk
  obtain ⟨hM, hO⟩ := hPeriodic.2 L hL k hk
  have hR := hRelations L hL k hk
  have hVert : ∀ j, j ≤ k →
      IsRealColourTrivial (FullSpace.scaledVertexCoboundaryKernel L k j) := fun j hj =>
    of_represents (r := vertexCoordinate (FullSpace.Vertex L k j)) (r' := FullSpace.edgePauliCoordinates L k j)
      (vertexCoordinates_ofRealMultiples _) (edgePauliCoordinates_reprOfRealMultiples L k j) (scaledVertexCoboundary_preserves L k j)
      (hM.vertexCoboundary j hj).applyKernel_eq
  have hEdge : ∀ j, j ≤ k →
      IsRealColourTrivial (FullSpace.scaledEdgeCoboundaryKernel L k j) := fun j hj =>
    of_represents (r := FullSpace.edgePauliCoordinates L k j) (r' := vertexCoordinate (FullSpace.Face L k j))
      (edgePauliCoordinates_reprOfRealMultiples L k j) (vertexCoordinates_ofRealMultiples _) (scaledEdgeCoboundary_preserves L k j)
      (hM.edgeCoboundary j hj).applyKernel_eq
  have hQ : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).Q :=
    of_represents (r := FullSpace.edgePauliCoordinates L k 0) (r' := FullSpace.edgePauliCoordinates L k k)
      (edgePauliCoordinates_reprOfRealMultiples L k 0) (edgePauliCoordinates_reprOfRealMultiples L k k)
      (PreservesRealMultiples.real_smul
        (composeFromZero_preserves (S := fun j => FullSpace.Edge L k j)
          (fun j => crossingSmoothing_preserves L _ _) k) _)
      fun f => (hR.Q_represents f).2
  have hRk : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).R :=
    of_represents (r := vertexCoordinate (FullSpace.Vertex L k 0))
      (r' := vertexCoordinate (FullSpace.Vertex L k k))
      (vertexCoordinates_ofRealMultiples _) (vertexCoordinates_ofRealMultiples _)
      (composeFromZero_preserves (S := fun j => FullSpace.Vertex L k j)
        (fun j => vertexSmoothing_preserves L _ _) k)
      fun f => (hR.R_represents f).2
  have hQt : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).Qt :=
    wTranspose_const _ _ hQ
  have hRt : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).Rt :=
    wTranspose_const _ _ hRk
  have h0 : 0 ≤ k := Nat.zero_le k
  have hd := hVert 0 h0
  have hdd := hEdge 0 h0
  have hdt : ∀ e : ℝ, IsRealColourTrivial
      (meshTranspose e e (FullSpace.scaledVertexCoboundaryKernel L k 0)) := fun e =>
    wTranspose_const _ _ hd
  have hddt : ∀ e : ℝ, IsRealColourTrivial
      (meshTranspose e e (FullSpace.scaledEdgeCoboundaryKernel L k 0)) := fun e =>
    wTranspose_const _ _ hdd
  have hK : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).K := by
    have e : (FullSpace.rescaledOperators L k fun _ => 1).K = _ := hR.K_eq
    rw [e]
    exact add (comp (hddt _) hdd) (comp hd (hdt _))
  have hDelta : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).Delta := by
    have e : (FullSpace.rescaledOperators L k fun _ => 1).Delta = _ := hR.Delta_eq
    rw [e]
    exact comp (hdt _) hd
  have hRtR := comp hRt hRk
  have hOne : IsRealColourTrivial
      (complementProj (FullSpace.rescaledOperators L k fun _ => 1)) := sub unit hRtR
  have hX : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).X := by
    have e : (FullSpace.rescaledOperators L k fun _ => 1).X = _ := hR.X_eq
    rw [e]
    exact add (comp (hddt _) hdd) (comp (comp hd hOne) (hdt _))
  have hXi : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).Xi := by
    have e : (FullSpace.rescaledOperators L k fun _ => 1).Xi =
        (FullSpace.rescaledOperators L k fun _ => 1).X +
        compKernel (FullSpace.rescaledOperators L k fun _ => 1).Qt
          (FullSpace.rescaledOperators L k fun _ => 1).Q := by
      simp [RescaledOperators.X]
    rw [e]
    exact add hX (comp hQt hQ)
  have hY : IsRealColourTrivial (FullSpace.rescaledOperators L k fun _ => 1).Y :=
    add hDelta hRtR
  exact
    { vertexCoboundary := fun j hj =>
        ⟨isFiniteRange_of (hM.vertexCoboundary j hj).finite_range, hVert j hj⟩
      edgeCoboundary := fun j hj =>
        ⟨isFiniteRange_of (hM.edgeCoboundary j hj).finite_range, hEdge j hj⟩
      vertexCoboundary_transpose := fun j hj =>
        ⟨isFiniteRange_of (hO.vertexCoboundary_transpose j hj),
          wTranspose_const (meshAt L k j ^ 4) (meshAt L k j ^ 4) (hVert j hj)⟩
      edgeCoboundary_transpose := fun j hj =>
        ⟨isFiniteRange_of (hO.edgeCoboundary_transpose j hj),
          wTranspose_const (meshAt L k j ^ 4) (meshAt L k j ^ 4) (hEdge j hj)⟩
      K := ⟨isFiniteRange_of hO.K, hK⟩
      Delta := ⟨isFiniteRange_of hO.Delta, hDelta⟩
      Q := ⟨isFiniteRange_of hM.edgeAverage.finite_range, hQ⟩
      R := ⟨isFiniteRange_of hM.vertexAverage.finite_range, hRk⟩
      Qt := ⟨isFiniteRange_of hO.edgeAverage_transpose, hQt⟩
      Rt := ⟨isFiniteRange_of hO.vertexAverage_transpose, hRt⟩
      Xi := ⟨isFiniteRange_of hO.Xi, hXi⟩
      Y := ⟨isFiniteRange_of hO.Y, hY⟩
      X := ⟨isFiniteRange_of hO.X, hX⟩ }
end YangMills.Construction.Tower.FreeOperatorsRealLocal
end
