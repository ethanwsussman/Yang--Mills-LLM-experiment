import YangMills.Construction.Towers.KernelsOfTheTwoOperatorsAreProductsProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PeriodicOperators.IdentityOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.SymbolsOfPeriodicOperators
import YangMills.Construction.Towers.HalfPlaquetteTraceKernelOfAFieldIsLocalProof
import YangMills.Construction.Towers.TheTwoOperatorsAsFunctionsOfTheField
import YangMills.Construction.Towers.TheTwoOperatorsAtOneOnTheUnitLattice
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import YangMills.Construction.Towers.TwoOperatorsMultiplyPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.IdentityOnUnitLattice
open PeriodicOperators
open TwoOperators
open Matrices
open TorusMetric (euclidNormVec)
section Symbols
variable {I : PeriodicData} {Y : I.Carrier → I.Carrier → ℂ}
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem dephasedKernel_zero : dephasedKernel I I 0 Y = Y := by
  funext ι' ι
  simp [dephasedKernel, bilinDot]
open Classical in
theorem applyKernel_single (M : I.UnitQuot → I.UnitQuot → ℂ) (c' c : I.UnitQuot) :
    applyKernel M (Pi.single c 1) c' = M c' c := by
  unfold applyKernel
  rw [tsum_eq_single c]
  · simp
  · intro d hd
    simp [Pi.single_eq_of_ne hd]
theorem hasLaplacianSymbol_of_eigen (hK : PeriodicOperators.CovariantFiniteRange.Claim)
    (hS : PeriodicOperators.Symbols.Claim) (hId : PeriodicOperators.IdKernelFacts.Claim)
    (hI : IsPeriodic I) {ϱ : ℝ} (cov : IsPhaseCovariant I I 0 Y)
    (van : VanishesOutsideRadius I I ϱ Y)
    (wave : ∀ (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ),
      applyKernel Y (blochWave I κ φ) = Massive.latticeSymbol κ • blochWave I κ φ) :
    HasLaplacianSymbol I Y := by
  classical
  obtain ⟨hop, -, -, hacts⟩ := hK.2 I I hI hI 0 ϱ Y cov van
  rw [dephasedKernel_zero] at hop
  have hacts' : ∀ (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) (ι' : I.Carrier),
      applyKernel Y (blochWave I κ φ) ι' =
        blochWave I κ (applyKernel (quotSymbol I I Y κ) φ) ι' := by
    intro κ φ ι'
    have e := (hacts κ φ ι').2
    rwa [dephasedKernel_zero, add_zero] at e
  have hmatrix : ∀ κ : Fin 4 → ℂ,
      quotSymbol I I Y κ = Massive.latticeSymbol κ • quotOne I := by
    intro κ
    funext c' c
    induction c' using Quot.ind with
    | mk ι' =>
      have e := hacts' κ (Pi.single c 1) ι'
      rw [wave] at e
      have hE := Complex.exp_ne_zero (Complex.I * bilinDot κ (toComplexVec (I.pos ι')))
      have e' : Complex.exp (Complex.I * bilinDot κ (toComplexVec (I.pos ι'))) *
            (Massive.latticeSymbol κ * (Pi.single c 1 : I.UnitQuot → ℂ) (I.mkQuot 1 ι')) =
          Complex.exp (Complex.I * bilinDot κ (toComplexVec (I.pos ι'))) *
            quotSymbol I I Y κ (I.mkQuot 1 ι') c := by
        have e₂ := e
        simp only [Pi.smul_apply, smul_eq_mul, blochWave] at e₂
        rw [applyKernel_single] at e₂
        rw [← e₂]
        ring
      have e₃ := mul_left_cancel₀ hE e'
      show quotSymbol I I Y κ (I.mkQuot 1 ι') c =
        Massive.latticeSymbol κ * quotOne I (I.mkQuot 1 ι') c
      rw [← e₃]
      congr 1
      by_cases h : I.mkQuot 1 ι' = c
      · simp [quotOne, h]
      · simp [quotOne, h]
  obtain ⟨hidp, hidr, -⟩ := hId I hI
  have hF := hS.1 I I I hI hI hI Y (idKernel I) 1 hop.periodic (hop.decays 1 one_pos)
    hidp (hidr 1 one_pos)
  have hnum : ∀ (κ : Fin 4 → ℂ) (ι' ι : I.Carrier), fourierSymbol I I Y κ ι' ι =
      quotSymbol I I Y κ (I.mkQuot 1 ι') (I.mkQuot 1 ι) := by
    intro κ ι' ι
    have hz : ∃ z, ∀ ι₁' ι₁, I.mkQuot 1 ι₁' = I.mkQuot 1 ι' →
        I.mkQuot 1 ι₁ = I.mkQuot 1 ι → fourierSymbol I I Y κ ι₁' ι₁ = z :=
      ⟨fourierSymbol I I Y κ ι' ι, fun ι₁' ι₁ e e' =>
        hF.eq_of_mkQuot_eq κ (hop.summable κ (mem_univ κ)) _ _ _ _ e e'⟩
    exact Classical.epsilon_spec hz ι' ι rfl rfl
  refine ⟨hop.periodic, hop.summable, fun κ ι' ι => ?_, hmatrix⟩
  rw [hnum, hmatrix]
  rfl
theorem covariant_finiteRange_at_zero {F : PeriodicData}
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    (h : IsLocalOpFun F I I T) :
    IsPhaseCovariant I I 0 (T 0) ∧ ∃ ϱ : ℝ, VanishesOutsideRadius I I ϱ (T 0) := by
  obtain ⟨ρ, R, hm⟩ := h
  have hb : IsSupBelow F 0 ρ := ⟨0, hm.radius_pos, fun κ => by simp⟩
  refine ⟨fun n ι' ι => ?_, R, fun ι' ι hd => ?_⟩
  · have e := hm.shift_covariant 0 hb n ι' ι
    have e0 : shiftField F n (0 : F.Carrier → ℂ) = 0 := rfl
    rw [e0] at e
    simpa [bilinDot] using e
  · refine hm.vanish_far 0 hb ι' ι fun h' => hd ?_
    rwa [← neg_sub, euclidNormVec_neg]
end Symbols
section Coefficients
theorem sum_smul_pauliFamily_mem (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_smul_sum_smul (z : ℂ) (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (z • ∑ b, x b • ComplexMatrix2.pauliFamily b) = z * x a := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality.pauliCoeff_smul_sum <;> assumption
end Coefficients
section Lattice
variable {L : ℕ}
theorem meshAt_zero_zero (L : ℕ) : meshAt L 0 0 = 1 := by
  simp [meshAt]
def vertexOfVec (L : ℕ) (n : Fin 4 → ℤ) : FullSpace.Vertex L 0 0 :=
  ⟨castVec n, n, fun μ => by simp [castVec, meshAt_zero_zero]⟩
theorem exists_eq_vertexOfVec (x : FullSpace.Vertex L 0 0) : ∃ n, x = vertexOfVec L n := by
  obtain ⟨n, hn⟩ := x.2
  refine ⟨n, Subtype.ext (funext fun μ => ?_)⟩
  have e := hn μ
  have s := meshAt_zero_zero L
  calc (x : InfiniteLattice.AmbientSpace) μ = (n μ : ℝ) * meshAt L 0 0 := e
    _ = (n μ : ℝ) := by rw [s, mul_one]
theorem vertexImage_intShift (n : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) :
    FullSpace.vertexImage (intShift n) x = x + vertexOfVec L n :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : FullSpace.Vertex L 0 0 => (x' : InfiniteLattice.AmbientSpace) = intShift n x)
    ⟨x + vertexOfVec L n, rfl⟩ |>.trans rfl)
theorem edgeImage_intShift_ends (n : Fin 4 → ℤ) (b : FullSpace.Edge L 0 0) :
    (FullSpace.edgeImage (intShift n) b).initial = b.initial + vertexOfVec L n ∧
      (FullSpace.edgeImage (intShift n) b).terminal = b.terminal + vertexOfVec L n := by
  have spec := Classical.epsilon_spec
    (p := fun b' : FullSpace.Edge L 0 0 =>
      b'.initial = FullSpace.vertexImage (intShift n) b.initial ∧
        b'.terminal = FullSpace.vertexImage (intShift n) b.terminal)
    ⟨⟨FullSpace.vertexImage (intShift n) b.initial, FullSpace.vertexImage (intShift n) b.terminal, by
      obtain ⟨μ, hμ⟩ := b.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexImage_intShift, vertexImage_intShift, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl, rfl⟩
  have spec' : (FullSpace.edgeImage (intShift n) b).initial =
        FullSpace.vertexImage (intShift n) b.initial ∧
      (FullSpace.edgeImage (intShift n) b).terminal =
        FullSpace.vertexImage (intShift n) b.terminal := spec
  rw [vertexImage_intShift, vertexImage_intShift] at spec'
  exact spec'
theorem shiftEdge_ends (n : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0) :
    (shiftEdge n b).1.initial = b.1.initial + vertexOfVec L n ∧
      (shiftEdge n b).1.terminal = b.1.terminal + vertexOfVec L n := by
  have spec := Classical.epsilon_spec
    (p := fun b' : PeriodicOperators.PosEdge L 0 0 =>
      b'.1 = FullSpace.edgeImage (intShift n) b.1)
    ⟨⟨FullSpace.edgeImage (intShift n) b.1, by
      obtain ⟨μ, hμ⟩ := b.2
      refine ⟨μ, ?_⟩
      rw [(edgeImage_intShift_ends n b.1).1, (edgeImage_intShift_ends n b.1).2,
        add_sub_add_right_eq_sub]
      exact hμ⟩, rfl⟩
  have spec' : (shiftEdge n b).1 = FullSpace.edgeImage (intShift n) b.1 := spec
  rw [spec']
  exact edgeImage_intShift_ends n b.1
theorem mkQuot_colourVertex (a : Fin 3) (x : FullSpace.Vertex L 0 0) :
    (colourVertices L 0 0).mkQuot 1 (a, x) = (colourVertices L 0 0).mkQuot 1 (a, 0) := by
  obtain ⟨n, rfl⟩ := exists_eq_vertexOfVec x
  refine (Quot.sound ⟨n, ?_⟩).symm
  show (a, vertexOfVec L n) = (a, FullSpace.vertexImage (intShift (1 • n)) 0)
  rw [one_nsmul, vertexImage_intShift, zero_add]
def edgeAtOrigin (L : ℕ) (μ : Fin 4) : PeriodicOperators.PosEdge L 0 0 :=
  ⟨InfiniteLattice.Link.forwardFrom 0 μ, μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem mkQuot_colourEdge (a : Fin 3) (b : PeriodicOperators.PosEdge L 0 0) (μ : Fin 4)
    (hμ : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L 0 0) μ) :
    (colourEdges L 0 0).mkQuot 1 (a, b) =
      (colourEdges L 0 0).mkQuot 1 (a, edgeAtOrigin L μ) := by
  obtain ⟨n, hn⟩ := exists_eq_vertexOfVec b.1.initial
  refine (Quot.sound ⟨n, ?_⟩).symm
  show (a, b) = (a, shiftEdge (1 • n) (edgeAtOrigin L μ))
  rw [one_nsmul]
  refine congrArg _ (Subtype.ext (InfiniteLattice.Link.ext ?_ ?_))
  · rw [(shiftEdge_ends n _).1, hn]
    exact (zero_add _).symm
  · rw [(shiftEdge_ends n _).2]
    have e : b.1.terminal = b.1.initial + InfiniteLattice.axisStep (meshAt L 0 0) μ := by
      rw [← hμ]
      abel
    rw [e, hn]
    show _ = (0 + InfiniteLattice.axisStep (meshAt L 0 0) μ) + vertexOfVec L n
    abel
theorem axisStep_injective {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep (meshAt L 0 0) ν =
      InfiniteLattice.axisStep (meshAt L 0 0) μ) : ν = μ := by
  by_contra hne
  have e := congrFun (congrArg Subtype.val h) μ
  simp only [InfiniteLattice.axisStep, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne),
    meshAt_zero_zero] at e
  exact zero_ne_one e
theorem extendOddly_congr {a : ℝ} {f g : InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → f b = g b) :
    FullSpace.extendOddly f = FullSpace.extendOddly g := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_congr <;> assumption
open Classical in
theorem edgePauliCoordinates_ofCoeffs_eq (c : (FullSpace.edgePauliCoordinates L 0 0).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs c = FullSpace.extendOddly (a := meshAt L 0 0)
      (fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0) := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_ofCoeffs_eq <;> assumption
theorem edgePauliCoordinates_ofCoeffs_zero (b : FullSpace.Edge L 0 0) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (fun _ => 0) b = 0 := by
  classical
  have e : (fun b : FullSpace.Edge L 0 0 => if h : b.IsPositivelyOriented then
      ofPauliCoeffs (fun _ => 0) (⟨b, h⟩ : FullSpace.PositiveEdge (meshAt L 0 0)) else 0) =
      fun _ => 0 := by
    funext b
    split_ifs <;> simp [ofPauliCoeffs]
  show FullSpace.extendOddly (a := meshAt L 0 0) (fun b => if h : b.IsPositivelyOriented then
    ofPauliCoeffs (fun _ => 0) (⟨b, h⟩ : FullSpace.PositiveEdge (meshAt L 0 0)) else 0) b = 0
  rw [e]
  unfold FullSpace.extendOddly
  split_ifs <;> simp
theorem expTwist_of_forall_eq_zero {A : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hA : ∀ b, A b = 0) :
    FullSpace.expTwist A (fun _ => 1) = fun _ => (1 : ComplexMatrix2) := by
  funext b
  unfold FullSpace.expTwist
  split_ifs <;> simp [hA]
theorem expField_zero :
    FullSpace.expField (L := L) 0 = fun _ => (1 : ComplexMatrix2) :=
  expTwist_of_forall_eq_zero edgePauliCoordinates_ofCoeffs_zero
end Lattice
section Waves
variable {L : ℕ}
theorem ofPauliCoeffs_blochWave (κ : Fin 4 → ℂ) (φ : (colourVertices L 0 0).UnitQuot → ℂ) :
    ofPauliCoeffs (blochWave (colourVertices L 0 0) κ φ) =
      FullSpace.vertexPlaneWave L κ
        (∑ a, φ ((colourVertices L 0 0).mkQuot 1 (a, 0)) • ComplexMatrix2.pauliFamily a) := by
  funext x
  simp only [ofPauliCoeffs, FullSpace.vertexPlaneWave, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (_ * φ ((colourVertices L 0 0).mkQuot 1 (a, x))) • _ = _
  rw [mkQuot_colourVertex, mul_smul]
  rfl
def originEdgeValues (φ : (colourEdges L 0 0).UnitQuot → ℂ) (μ : Fin 4) : ComplexMatrix2 :=
  ∑ a, φ ((colourEdges L 0 0).mkQuot 1 (a, edgeAtOrigin L μ)) • ComplexMatrix2.pauliFamily a
theorem edgePauliCoordinates_blochWave (κ : Fin 4 → ℂ) (φ : (colourEdges L 0 0).UnitQuot → ℂ) :
    (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (blochWave (colourEdges L 0 0) κ φ) =
      FullSpace.edgePlaneWave L κ (originEdgeValues φ) := by
  classical
  refine (edgePauliCoordinates_ofCoeffs_eq _).trans ?_
  unfold FullSpace.edgePlaneWave
  refine extendOddly_congr fun b hb => ?_
  obtain ⟨μ, hμ⟩ := id hb
  rw [dif_pos hb]
  have e : ∑ ν, (if b.terminal - b.initial = InfiniteLattice.axisStep (meshAt L 0 0) ν
      then originEdgeValues φ ν else 0) = originEdgeValues φ μ := by
    rw [Finset.sum_eq_single μ, if_pos hμ]
    · intro ν _ hν
      exact if_neg fun h => hν (axisStep_injective (h.symm.trans hμ))
    · simp
  rw [e]
  simp only [ofPauliCoeffs, originEdgeValues, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (_ * φ ((colourEdges L 0 0).mkQuot 1 (a, ⟨b, hb⟩))) • _ = _
  rw [mkQuot_colourEdge a ⟨b, hb⟩ μ hμ, mul_smul]
  rfl
end Waves
theorem twoOperatorsAtIdentityLatticeClaim_holds (h₁ : TwoOperators.PlaneWaveEigen)
    (h₂ : TwoOperatorsAsFieldFunctions)
    (h₃ : PeriodicOperators.TowerIndexSets.Claim)
    (h₄ : PeriodicOperators.CovariantFiniteRange.Claim)
    (h₅ : PeriodicOperators.Symbols.Claim) (h₆ : PeriodicOperators.IdKernelFacts.Claim) :
    TwoOperatorsAtIdentityLatticeClaim := by
  intro L hL
  have hM := h₂ L hL
  obtain ⟨hwS, hwB⟩ := h₁ L hL
  obtain ⟨hIS, hIB, -⟩ := h₃ L hL 0 0 le_rfl
  have e := expField_zero (L := L)
  have kS : ∀ U, FullSpace.expField (L := L) 0 = U →
      Represents (FullSpace.gaugeLaplacianKernel (L := L) U)
        ((vertexCoordinate (FullSpace.Vertex L 0 0)).mapOnCoeffs
          (vertexCoordinate (FullSpace.Vertex L 0 0))
          (FullSpace.gaugeLaplacian U)) := by
    rintro _ rfl
    exact hM.laplacian_kernel 0
  have kB : ∀ U, FullSpace.expField (L := L) 0 = U →
      Represents (FullSpace.massiveHessianKernel (L := L) U)
        ((FullSpace.edgePauliCoordinates L 0 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0)
          (FullSpace.massiveHessian U)) := by
    rintro _ rfl
    exact hM.massive_kernel 0
  have gS := kS _ e
  have gB := kB _ e
  obtain ⟨cS, ϱS, vS⟩ := covariant_finiteRange_at_zero hM.laplacian_local.is_local
  obtain ⟨cB, ϱB, vB⟩ := covariant_finiteRange_at_zero hM.massive_local.is_local
  have eS : FullSpace.gaugeLaplacianAt (L := L) 0 =
      FullSpace.gaugeLaplacianKernel fun _ => 1 := by
    rw [FullSpace.gaugeLaplacianAt, e]
  have eB : FullSpace.massiveHessianAt (L := L) 0 =
      FullSpace.massiveHessianKernel fun _ => 1 := by
    rw [FullSpace.massiveHessianAt, e]
  refine ⟨gS, gB, ?_, ?_, hwS, hwB⟩
  · refine hasLaplacianSymbol_of_eigen h₄ h₅ h₆ hIS (ϱ := ϱS) (eS ▸ cS) (eS ▸ vS)
      fun κ φ => ?_
    refine ((gS _).2).trans ?_
    have w : FullSpace.gaugeLaplacian (fun _ => 1)
        (ofPauliCoeffs (blochWave (colourVertices L 0 0) κ φ)) = Massive.latticeSymbol κ •
          ofPauliCoeffs (blochWave (colourVertices L 0 0) κ φ) := by
      rw [ofPauliCoeffs_blochWave]
      exact hwS _ _ (sum_smul_pauliFamily_mem _)
    funext ι
    obtain ⟨a, x⟩ := ι
    show toPauliCoeffs (FullSpace.gaugeLaplacian (fun _ => 1)
      (ofPauliCoeffs (blochWave (colourVertices L 0 0) κ φ))) (a, x) = _
    rw [w]
    show pauliCoeff a (Massive.latticeSymbol κ •
      ∑ b, blochWave (colourVertices L 0 0) κ φ (b, x) • ComplexMatrix2.pauliFamily b) = _
    rw [pauliCoeff_smul_sum_smul]
    rfl
  · refine hasLaplacianSymbol_of_eigen h₄ h₅ h₆ hIB (ϱ := ϱB) (eB ▸ cB) (eB ▸ vB)
      fun κ φ => ?_
    refine ((gB _).2).trans ?_
    have w : FullSpace.massiveHessian (fun _ => 1)
        ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (blochWave (colourEdges L 0 0) κ φ)) =
          Massive.latticeSymbol κ •
            (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (blochWave (colourEdges L 0 0) κ φ) := by
      rw [edgePauliCoordinates_blochWave]
      exact hwB _ _ fun μ => sum_smul_pauliFamily_mem _
    funext ι
    obtain ⟨a, b⟩ := ι
    show toPauliCoeffs (FullSpace.restrictToPositiveEdges (FullSpace.massiveHessian (fun _ => 1)
      ((FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (blochWave (colourEdges L 0 0) κ φ)))) (a, b) = _
    rw [w]
    have hv : (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (blochWave (colourEdges L 0 0) κ φ) b.1 =
        ∑ c, blochWave (colourEdges L 0 0) κ φ (c, b) • ComplexMatrix2.pauliFamily c := by
      classical
      refine (congrFun (edgePauliCoordinates_ofCoeffs_eq _) b.1).trans ?_
      unfold FullSpace.extendOddly
      rw [if_pos b.2]
      exact dif_pos b.2
    show pauliCoeff a (Massive.latticeSymbol κ •
      (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs (blochWave (colourEdges L 0 0) κ φ) b.1) = _
    rw [hv, pauliCoeff_smul_sum_smul]
    rfl
end YangMills.Construction.Tower.IdentityOnUnitLattice
end
