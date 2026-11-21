import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreClosed
import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreLocal
import YangMills.Construction.RunningCouplingSlope.TheCommutatorOfTheChainReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheSoftActionReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheOrbitMapReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheOtherConstraintReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainIsALocalFamily
import YangMills.Construction.RunningCouplingSlope.TheSecondOrderOfTheTopReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheTermOfTheBackgroundGaugeReadsNearCells
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import Mathlib
set_option autoImplicit false
open Filter YangMills.Construction.Tower
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.SaddlePointMatrixLocality
section DotProducts
variable {m₁ m₂ m₃ : Type} [Fintype m₁] [Fintype m₂] [Fintype m₃]
private lemma dotProduct_mulVec_mulVec (A : Matrix m₁ m₂ ℂ) (B : Matrix m₁ m₃ ℂ) (u : m₂ → ℂ)
    (w : m₃ → ℂ) :
    (A.mulVec u) ⬝ᵥ (B.mulVec w) = u ⬝ᵥ ((A.transpose * B).mulVec w) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u A.transpose, Matrix.vecMul_transpose]
private lemma dotProduct_transpose_mulVec_self (A : Matrix m₁ m₁ ℂ) (u : m₁ → ℂ) :
    u ⬝ᵥ (A.transpose.mulVec u) = u ⬝ᵥ (A.mulVec u) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
private lemma re_dotProduct_mulVec [DecidableEq m₁] (A : Matrix m₁ m₁ ℂ) (u w : m₁ → ℝ) :
    (complexifyCoords u ⬝ᵥ A.mulVec (complexifyCoords w)).re =
      u ⬝ᵥ (A.map Complex.re).mulVec w := by
  simp [complexifyCoords, dotProduct, Matrix.mulVec, Complex.re_sum, Finset.mul_sum]
private lemma im_dotProduct_mulVec [DecidableEq m₁] (A : Matrix m₁ m₁ ℂ) (u w : m₁ → ℝ) :
    (complexifyCoords u ⬝ᵥ A.mulVec (complexifyCoords w)).im =
      u ⬝ᵥ (A.map Complex.im).mulVec w := by
  simp [complexifyCoords, dotProduct, Matrix.mulVec, Complex.im_sum, Finset.mul_sum]
private lemma eq_zero_of_quadratic_zero [DecidableEq m₁] {A : Matrix m₁ m₁ ℝ}
    (hs : A.transpose = A) (h : ∀ v : m₁ → ℝ, v ⬝ᵥ A.mulVec v = 0) : A = 0 := by
  have hb : ∀ u v : m₁ → ℝ, u ⬝ᵥ A.mulVec v = 0 := by
    intro u v
    have h1 := h (u + v)
    have h2 := h u
    have h3 := h v
    have h4 : v ⬝ᵥ A.mulVec u = u ⬝ᵥ A.mulVec v := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct] at h1
    linarith
  ext p q
  have := hb (Pi.single p 1) (Pi.single q 1)
  simpa using this
end DotProducts
section FormCoordinates
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k 0)]
  [Fintype (Fin 3 × Vertex L n k k)]
private lemma levelPairing_eq_dot (P : PauliCoordinates L n k) (ξ ξ' : LevelForms L n k) :
    levelPairing (formValues ξ) (formValues ξ') = P.formCoords ξ ⬝ᵥ P.formCoords ξ' :=
  P.formCoords_pairing ξ ξ'
private lemma formValues_injective {ξ ξ' : LevelForms L n k}
    (h : formValues ξ = formValues ξ') : ξ = ξ' := by
  have h1 : (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) = ξ'.1 := congrArg Prod.fst h
  have h2 : ∀ i : Fin k, (ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) = ξ'.2 i :=
    fun i => congrFun (congrArg Prod.snd h) i
  refine Prod.ext (Subtype.ext h1) (funext fun i => Subtype.ext (h2 i))
private lemma formValues_add (ξ ξ' : LevelForms L n k) :
    formValues (ξ + ξ') = formValues ξ + formValues ξ' := rfl
private lemma gaugedOperator_matrix (P : PauliCoordinates L n k) (a : ℝ) (X : ChainPoint L n k)
    (J : LevelForms L n k) (μ : edgeFormSpace L n k k)
    (G : Matrix (LevelFormIndex L n k) (LevelFormIndex L n k) ℂ) (hs : G.transpose = G)
    (h : ∀ ξ : LevelForms L n k, ((gaugedRightValue a X J μ ξ : ℝ) : ℂ) =
      complexifyCoords (P.formCoords ξ) ⬝ᵥ G.mulVec (complexifyCoords (P.formCoords ξ))) :
    complexMatrixOfLinearMap P.formCoords P.formCoords (gaugedOperator a X J μ) = G := by
  set Gr := G.map Complex.re with hGr
  have hsr : Gr.transpose = Gr := by
    ext p q
    have := congrFun (congrFun hs p) q
    simp only [Matrix.transpose_apply] at this
    simp [hGr, Matrix.transpose_apply, this]
  have hsi : (G.map Complex.im).transpose = G.map Complex.im := by
    ext p q
    have := congrFun (congrFun hs p) q
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.transpose_apply, this]
  have hi : G.map Complex.im = 0 := by
    refine eq_zero_of_quadratic_zero hsi fun v => ?_
    have h1 := congrArg Complex.im (h (P.formCoords.symm v))
    rw [Complex.ofReal_im, P.formCoords.apply_symm_apply, im_dotProduct_mulVec] at h1
    exact h1.symm
  have hG : G = Gr.map fun x => (x : ℂ) := by
    ext p q
    have := congrFun (congrFun hi p) q
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    apply Complex.ext <;> simp [hGr, this]
  have hquad : ∀ ξ : LevelForms L n k, gaugedRightValue a X J μ ξ =
      P.formCoords ξ ⬝ᵥ Gr.mulVec (P.formCoords ξ) := by
    intro ξ
    have h1 := congrArg Complex.re (h ξ)
    rw [Complex.ofReal_re, re_dotProduct_mulVec] at h1
    exact h1
  let T : LevelForms L n k →ₗ[ℝ] LevelForms L n k :=
    P.formCoords.symm.toLinearMap ∘ₗ Gr.mulVecLin ∘ₗ P.formCoords.toLinearMap
  have hT : ∀ ξ, P.formCoords (T ξ) = Gr.mulVec (P.formCoords ξ) := by
    intro ξ
    simp [T]
  have hTs : IsGaugedOperator a X J μ T := by
    refine ⟨fun ξ ξ' => ?_, fun ξ => ?_⟩
    · rw [levelPairing_eq_dot P, levelPairing_eq_dot P, hT, hT, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, hsr, dotProduct_comm]
    · rw [levelPairing_eq_dot P, hT, hquad]
  have hS : IsGaugedOperator a X J μ (gaugedOperator a X J μ) :=
    Classical.epsilon_spec (p := IsGaugedOperator a X J μ) ⟨T, hTs⟩
  have heq : ∀ ξ', gaugedOperator a X J μ ξ' = T ξ' := by
    intro ξ'
    set S := gaugedOperator a X J μ with hSdef
    have hsym : ∀ (R : LevelForms L n k →ₗ[ℝ] LevelForms L n k), IsGaugedOperator a X J μ R →
        ∀ ξ, P.formCoords ξ ⬝ᵥ P.formCoords (R ξ') =
          (gaugedRightValue a X J μ (ξ + ξ') - gaugedRightValue a X J μ ξ -
            gaugedRightValue a X J μ ξ') / 2 := by
      intro R hR ξ
      have q1 := hR.2 (ξ + ξ')
      have q2 := hR.2 ξ
      have q3 := hR.2 ξ'
      have q4 := hR.1 ξ ξ'
      simp only [levelPairing_eq_dot P, map_add, add_dotProduct, dotProduct_add] at q1 q2 q3 q4
      have q5 : P.formCoords ξ' ⬝ᵥ P.formCoords (R ξ) = P.formCoords (R ξ) ⬝ᵥ P.formCoords ξ' :=
        dotProduct_comm _ _
      rw [← q1, ← q2, ← q3]
      linarith
    have hcoord : P.formCoords (S ξ') = P.formCoords (T ξ') := by
      refine dotProduct_eq _ _ fun v => ?_
      have h1 := hsym S hS (P.formCoords.symm v)
      have h2 := hsym T hTs (P.formCoords.symm v)
      rw [P.formCoords.apply_symm_apply] at h1 h2
      rw [dotProduct_comm, h1, dotProduct_comm, h2]
    exact P.formCoords.injective hcoord
  have hop : gaugedOperator a X J μ = T := LinearMap.ext heq
  rw [hop, hG]
  unfold complexMatrixOfLinearMap
  congr 1
  have e : (P.formCoords.toLinearMap ∘ₗ T ∘ₗ P.formCoords.symm.toLinearMap) = Gr.mulVecLin := by
    ext v
    simp [T]
  rw [e]
  rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
private lemma gaugeTransform_coords (P : PauliCoordinates L n k) (X : ChainPoint L n k)
    (S : Matrix (Fin 3 × Vertex L n k 0) (LevelFormIndex L n k) ℂ)
    (D : Matrix (LevelFormIndex L n k) (Fin 3 × Vertex L n k 0) ℂ)
    (hS : ∀ ξ : LevelForms L n k, ∃ l : vertexFunctionSpace L n k 0,
      (l : Vertex L n k 0 → Matrices.ComplexMatrix2) = gaugeCorrection X ξ ∧
      complexifyCoords (fineVertexCoords P l) = S.mulVec (complexifyCoords (P.formCoords ξ)))
    (hD : ∀ l : vertexFunctionSpace L n k 0, ∃ ξ : LevelForms L n k,
      formValues ξ = gaugeOrbitValues X (l : Vertex L n k 0 → Matrices.ComplexMatrix2) ∧
      complexifyCoords (P.formCoords ξ) = D.mulVec (complexifyCoords (fineVertexCoords P l)))
    (ξ : LevelForms L n k) :
    complexifyCoords (P.formCoords (gaugeTransform X ξ)) =
      (1 + D * S).mulVec (complexifyCoords (P.formCoords ξ)) := by
  have hη : ∀ ξ : LevelForms L n k, ∃ η : LevelForms L n k,
      formValues η = gaugeOrbitValues X (gaugeCorrection X ξ) ∧
      complexifyCoords (P.formCoords η) = (D * S).mulVec (complexifyCoords (P.formCoords ξ)) := by
    intro ξ
    obtain ⟨l, hl, hc⟩ := hS ξ
    obtain ⟨η, hv, hd⟩ := hD l
    refine ⟨η, by rw [hv, hl], ?_⟩
    rw [hd, hc, Matrix.mulVec_mulVec]
  set Mr := (D * S).map Complex.re with hMr
  have hcoord : ∀ ξ η : LevelForms L n k,
      complexifyCoords (P.formCoords η) = (D * S).mulVec (complexifyCoords (P.formCoords ξ)) →
      P.formCoords η = Mr.mulVec (P.formCoords ξ) := by
    intro ξ η h
    funext p
    have h1 := congrArg Complex.re (congrFun h p)
    simpa [complexifyCoords, hMr, Matrix.mulVec, dotProduct, Complex.re_sum] using h1
  let T : LevelForms L n k →ₗ[ℝ] LevelForms L n k :=
    LinearMap.id + P.formCoords.symm.toLinearMap ∘ₗ Mr.mulVecLin ∘ₗ P.formCoords.toLinearMap
  have hT : ∀ ξ η : LevelForms L n k, P.formCoords η = Mr.mulVec (P.formCoords ξ) →
      T ξ = ξ + η := by
    intro ξ η h
    simp [T, ← h]
  have hTg : IsGaugeTransform X T := by
    intro ξ
    obtain ⟨η, hv, hc⟩ := hη ξ
    rw [hT ξ η (hcoord ξ η hc), formValues_add, hv]
  have hg : IsGaugeTransform X (gaugeTransform X) :=
    Classical.epsilon_spec (p := IsGaugeTransform X) ⟨T, hTg⟩
  obtain ⟨η, hv, hc⟩ := hη ξ
  have e : gaugeTransform X ξ = ξ + η := by
    refine formValues_injective ?_
    rw [hg ξ, formValues_add, hv]
  rw [e, map_add, Matrix.add_mulVec, Matrix.one_mulVec, ← hc]
  funext p
  simp [complexifyCoords]
end FormCoordinates
section GaugeFixedKernel
variable {m s : Type} [Fintype m] [Fintype s] [DecidableEq m] [DecidableEq s]
private def gaugeFixedKernel (H : Matrix m m ℂ) (B S : Matrix s m ℂ)
    (D : Matrix m s ℂ) (Q G : Matrix m m ℂ) : Matrix m m ℂ :=
  H + (2 : ℂ) • (S.transpose * B) + S.transpose * B * D * S +
    (-1 : ℂ) • ((1 + D * S).transpose * Q * (1 + D * S)) + G
private lemma gaugeFixedKernel_quadratic (H : Matrix m m ℂ) (B S : Matrix s m ℂ)
    (D : Matrix m s ℂ) (Q G : Matrix m m ℂ) (v : m → ℂ) :
    v ⬝ᵥ (gaugeFixedKernel H B S D Q G).mulVec v =
      v ⬝ᵥ H.mulVec v + 2 * (S.mulVec v ⬝ᵥ B.mulVec v) +
        S.mulVec v ⬝ᵥ B.mulVec (D.mulVec (S.mulVec v)) -
        ((1 + D * S).mulVec v ⬝ᵥ Q.mulVec ((1 + D * S).mulVec v)) + v ⬝ᵥ G.mulVec v := by
  have e1 : S.mulVec v ⬝ᵥ B.mulVec v = v ⬝ᵥ (S.transpose * B).mulVec v :=
    dotProduct_mulVec_mulVec _ _ _ _
  have e2 : S.mulVec v ⬝ᵥ B.mulVec (D.mulVec (S.mulVec v)) =
      v ⬝ᵥ (S.transpose * B * D * S).mulVec v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, dotProduct_mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  have e3 : (1 + D * S).mulVec v ⬝ᵥ Q.mulVec ((1 + D * S).mulVec v) =
      v ⬝ᵥ ((1 + D * S).transpose * Q * (1 + D * S)).mulVec v := by
    rw [Matrix.mulVec_mulVec, dotProduct_mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  rw [e1, e2, e3]
  simp only [gaugeFixedKernel, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  ring
private def symmPart (A : Matrix m m ℂ) : Matrix m m ℂ := (1 / 2 : ℂ) • (A + A.transpose)
private lemma symmPart_transpose (A : Matrix m m ℂ) :
    (symmPart A).transpose = symmPart A := by
  unfold symmPart
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
private lemma symmPart_quadratic (A : Matrix m m ℂ) (v : m → ℂ) :
    v ⬝ᵥ (symmPart A).mulVec v = v ⬝ᵥ A.mulVec v := by
  unfold symmPart
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
    dotProduct_transpose_mulVec_self, smul_eq_mul]
  ring
end GaugeFixedKernel
section Families
variable {L n k : ℕ} {I m s t : Type} [Fintype I] [Fintype m] [Fintype s] [Fintype t]
  [DecidableEq m] [DecidableEq s] [DecidableEq t]
private lemma zero_isLocallyHolomorphicFamily (e : I → Vertex L n k k) (c : t → Vertex L n k k)
    (c' : t → Vertex L n k k) {ρ r : ℝ} :
    IsLocallyHolomorphicFamily e c c' (fun _ => (0 : Matrix t t ℂ)) ρ 0 r :=
  ⟨fun _ _ => analyticOnNhd_const, fun _ _ => by simp, fun _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl⟩
private def kernelConst (K : ℝ) : ℝ :=
  K + 2 * (K * K) + K * K * K * K + (1 + K * K) * K * (1 + K * K) + K
private def saddleConst (K : ℝ) : ℝ :=
  2⁻¹ * (kernelConst K + kernelConst K) + K + K + 0
private lemma gaugeFixedKernel_family (cl : LocallyHolomorphicFamiliesClosedOn L n k)
    {e : I → Vertex L n k k} {w : m → Vertex L n k k} {f : s → Vertex L n k k}
    {H Q G : (I → ℂ) → Matrix m m ℂ} {B S : (I → ℂ) → Matrix s m ℂ}
    {D : (I → ℂ) → Matrix m s ℂ} {ρ K r : ℝ} (hr : 0 ≤ r)
    (hH : IsLocallyHolomorphicFamily e w w H ρ K r)
    (hB : IsLocallyHolomorphicFamily e w f B ρ K r)
    (hS : IsLocallyHolomorphicFamily e w f S ρ K r)
    (hD : IsLocallyHolomorphicFamily e f w D ρ K r)
    (hQ : IsLocallyHolomorphicFamily e w w Q ρ K r)
    (hG : IsLocallyHolomorphicFamily e w w G ρ K r) :
    IsLocallyHolomorphicFamily e w w
      (fun z => gaugeFixedKernel (H z) (B z) (S z) (D z) (Q z) (G z))
      ρ (kernelConst K) (7 * r) := by
  have a1 := cl.transpose hr hS
  have a2 := cl.mul (by positivity) hr a1 hB
  have a3 := cl.smul (2 : ℂ) a2
  have a4 := cl.mul (by positivity) hr a2 hD
  have a5 := cl.mul (by positivity) hr a4 hS
  have b1 := cl.mul hr hr hD hS
  have b2 := cl.one e w ρ (r + r) (by positivity)
  have b3 := cl.add b2 b1
  have b4 := cl.transpose (by positivity) b3
  have b5 := cl.mul (by positivity) hr b4 hQ
  have b6 := cl.mul (by positivity) (by positivity) b5 b3
  have b7 := cl.smul (-1 : ℂ) b6
  have m0 := cl.mono (r' := 7 * r) le_rfl le_rfl (by linarith) hH
  have m3 := cl.mono (r' := 7 * r) (C' := 2 * (K * K)) le_rfl (by simp) (by linarith) a3
  have m5 := cl.mono (r' := 7 * r) le_rfl le_rfl (by linarith) a5
  have m7 := cl.mono (r' := 7 * r) (C' := (1 + K * K) * K * (1 + K * K)) le_rfl (by simp)
    (by linarith) b7
  have mG := cl.mono (r' := 7 * r) le_rfl le_rfl (by linarith) hG
  exact cl.add (cl.add (cl.add (cl.add m0 m3) m5) m7) mG
private lemma saddleBlocks_family (cl : LocallyHolomorphicFamiliesClosedOn L n k)
    {e : I → Vertex L n k k} {w : m → Vertex L n k k} {f : s → Vertex L n k k}
    {g : t → Vertex L n k k} {H Q G : (I → ℂ) → Matrix m m ℂ} {B S : (I → ℂ) → Matrix s m ℂ}
    {D : (I → ℂ) → Matrix m s ℂ} {O : (I → ℂ) → Matrix t m ℂ} {ρ K r : ℝ} (hr : 0 ≤ r)
    (hH : IsLocallyHolomorphicFamily e w w H ρ K r)
    (hB : IsLocallyHolomorphicFamily e w f B ρ K r)
    (hS : IsLocallyHolomorphicFamily e w f S ρ K r)
    (hD : IsLocallyHolomorphicFamily e f w D ρ K r)
    (hQ : IsLocallyHolomorphicFamily e w w Q ρ K r)
    (hG : IsLocallyHolomorphicFamily e w w G ρ K r)
    (hO : IsLocallyHolomorphicFamily e w g O ρ K r) :
    IsLocallyHolomorphicFamily e (Sum.elim w g) (Sum.elim w g)
      (fun z => Matrix.fromBlocks
        (symmPart (gaugeFixedKernel (H z) (B z) (S z) (D z) (Q z) (G z)))
        (O z).transpose (O z) 0) ρ (saddleConst K) (14 * r) := by
  have k1 := gaugeFixedKernel_family cl hr hH hB hS hD hQ hG
  have k2 := cl.transpose (by positivity) k1
  have k3 := cl.mono (r' := 2 * (7 * r)) le_rfl le_rfl (by linarith) k1
  have k4 := cl.smul (1 / 2 : ℂ) (cl.add k3 k2)
  have k5 := cl.mono (r' := 14 * r) (C' := 2⁻¹ * (kernelConst K + kernelConst K)) le_rfl
    (by simp) (by linarith) k4
  have o1 := cl.mono (r' := 14 * r) le_rfl le_rfl (by linarith) (cl.transpose hr hO)
  have o2 := cl.mono (r' := 14 * r) le_rfl le_rfl (by linarith) hO
  exact cl.fromBlocks k5 o1 o2 (zero_isLocallyHolomorphicFamily e g g)
end Families
section PartValues
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k 0)]
  [Fintype (Fin 3 × Vertex L n k k)]
private lemma saddlePointMatrix_eq_blocks (P : PauliCoordinates L n k) (a : ℝ)
    (x : TripleCoordIndex L n k → ℝ)
    (H Q G : Matrix (LevelFormIndex L n k) (LevelFormIndex L n k) ℂ)
    (B S : Matrix (Fin 3 × Vertex L n k 0) (LevelFormIndex L n k) ℂ)
    (D : Matrix (LevelFormIndex L n k) (Fin 3 × Vertex L n k 0) ℂ)
    (O : Matrix (Fin 3 × PositiveEdge L n k k) (LevelFormIndex L n k) ℂ)
    (eH : ∀ ξ : LevelForms L n k,
      ((leftSecondDeriv (chainAction a) (pointOfCoords P x) ξ ξ : ℝ) : ℂ) =
        complexifyCoords (P.formCoords ξ) ⬝ᵥ H.mulVec (complexifyCoords (P.formCoords ξ)))
    (eB : ∀ (l : vertexFunctionSpace L n k 0) (ξ : LevelForms L n k),
      ((levelPairing (formValues (tripleOfCoords P x).2.1)
          (chainBracket (pointOfCoords P x) (l : Vertex L n k 0 → Matrices.ComplexMatrix2)
            (formValues ξ)) : ℝ) : ℂ) =
        complexifyCoords (fineVertexCoords P l) ⬝ᵥ B.mulVec (complexifyCoords (P.formCoords ξ)))
    (eS : ∀ ξ : LevelForms L n k, ∃ l : vertexFunctionSpace L n k 0,
      (l : Vertex L n k 0 → Matrices.ComplexMatrix2) = gaugeCorrection (pointOfCoords P x) ξ ∧
      complexifyCoords (fineVertexCoords P l) = S.mulVec (complexifyCoords (P.formCoords ξ)))
    (eD : ∀ l : vertexFunctionSpace L n k 0, ∃ ξ : LevelForms L n k,
      formValues ξ = gaugeOrbitValues (pointOfCoords P x)
        (l : Vertex L n k 0 → Matrices.ComplexMatrix2) ∧
      complexifyCoords (P.formCoords ξ) = D.mulVec (complexifyCoords (fineVertexCoords P l)))
    (eQ : ∀ ξ ξ' : LevelForms L n k,
      (((traceFinsumPairing (restrictToPositiveEdges
          ((tripleOfCoords P x).2.2 : Edge L n k k → Matrices.ComplexMatrix2))
          (topSecondVariation (pointOfCoords P x) ξ ξ')).re : ℝ) : ℂ) =
        complexifyCoords (P.formCoords ξ) ⬝ᵥ Q.mulVec (complexifyCoords (P.formCoords ξ')))
    (eG : ∀ ξ : LevelForms L n k,
      ((traceFinsumNorm (gaugeSliceResidual (pointOfCoords P x).fine ξ.1 :
          Vertex L n k 0 → Matrices.ComplexMatrix2) ^ 2 : ℝ) : ℂ) =
        complexifyCoords (P.formCoords ξ) ⬝ᵥ G.mulVec (complexifyCoords (P.formCoords ξ)))
    (eO : gaugeConstraintMatrix P (tripleOfCoords P x) = O) :
    saddlePointMatrix P a (tripleOfCoords P x) =
      Matrix.fromBlocks (symmPart (gaugeFixedKernel H B S D Q G)) O.transpose O 0 := by
  have hsoft : complexMatrixOfLinearMap P.formCoords P.formCoords
      (gaugedOperator a (pointOfCoords P x)
      (tripleOfCoords P x).2.1 (tripleOfCoords P x).2.2) =
      symmPart (gaugeFixedKernel H B S D Q G) := by
    refine gaugedOperator_matrix P a _ _ _ _ (symmPart_transpose _) fun ξ => ?_
    rw [symmPart_quadratic, gaugeFixedKernel_quadratic]
    obtain ⟨l, hl, hlc⟩ := eS ξ
    obtain ⟨η, hη, hηc⟩ := eD l
    have e1 := eH ξ
    have e2 := eB l ξ
    have e3 := eB l η
    have e4 := eQ (gaugeTransform (pointOfCoords P x) ξ) (gaugeTransform (pointOfCoords P x) ξ)
    have e5 := eG ξ
    rw [gaugeTransform_coords P _ S D eS eD ξ] at e4
    rw [hl, hlc] at e2
    rw [hη, hl, hηc, hlc] at e3
    simp only [gaugedRightValue, gaugedFormValue, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [e1, e2, e3, e4, e5]
  show Matrix.fromBlocks (complexMatrixOfLinearMap P.formCoords P.formCoords
      (gaugedOperator a (pointOfCoords P x)
      (tripleOfCoords P x).2.1 (tripleOfCoords P x).2.2))
      (gaugeConstraintMatrix P (tripleOfCoords P x)).transpose
      (gaugeConstraintMatrix P (tripleOfCoords P x)) 0 = _
  rw [hsoft, eO]
private lemma pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private lemma formCoords_eq_zero_off_cell (P : PauliCoordinates L n k) {y : Vertex L n k k}
    {ξ : LevelForms L n k} (h : LevelFormsSupportedInCell y ξ) (p : LevelFormIndex L n k)
    (hp : levelFormIndexCell p ≠ y) : P.formCoords ξ p = 0 := by
  rcases p with p | ⟨i, p⟩
  · have h1 := P.formCoords_base ξ p
    have h2 : (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) p.2.1 = 0 := h.1 p.2 hp
    have h3 : toPauliCoeffs (restrictToPositiveEdges
        (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2)) p = 0 := by
      show pauliCoeff p.1 ((ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) p.2.1) = 0
      rw [h2, pauliCoeff_zero]
    rw [h3] at h1
    exact_mod_cast h1.symm
  · have h1 := P.formCoords_level ξ i p
    have h2 : (ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) p.2.1 = 0 := h.2 i p.2 hp
    have h3 : toPauliCoeffs (restrictToPositiveEdges
        (ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2)) p = 0 := by
      show pauliCoeff p.1 ((ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) p.2.1) = 0
      rw [h2, pauliCoeff_zero]
    rw [h3] at h1
    exact_mod_cast h1.symm
private lemma tripleCoords_eq_zero_off_cell (P : PauliCoordinates L n k) {y : Vertex L n k k}
    {τ : LevelTriple L n k} (h : TripleSupportedInCell y τ) (i : TripleCoordIndex L n k)
    (hi : tripleCoordIndexCell i ≠ y) : tripleCoords P τ i = 0 := by
  rcases i with p | p | p
  · exact formCoords_eq_zero_off_cell P h.1 p hi
  · exact formCoords_eq_zero_off_cell P h.2.1 p hi
  · have h1 := P.topFormCoords_apply τ.2.2 p
    have h2 : (τ.2.2 : Edge L n k k → Matrices.ComplexMatrix2) p.2.1 = 0 := h.2.2 p.2 hi
    have h3 : toPauliCoeffs (restrictToPositiveEdges
        (τ.2.2 : Edge L n k k → Matrices.ComplexMatrix2)) p = 0 := by
      show pauliCoeff p.1 ((τ.2.2 : Edge L n k k → Matrices.ComplexMatrix2) p.2.1) = 0
      rw [h2, pauliCoeff_zero]
    rw [h3] at h1
    exact_mod_cast h1.symm
private lemma abs_le_one_of_sum_sq {κ : Type} [Fintype κ] {f : κ → ℝ} {b : ℝ}
    (h : ∑ j, f j * f j ≤ b) (hb : b ≤ 1) (i : κ) : |f i| ≤ 1 := by
  have h1 : f i * f i ≤ ∑ j, f j * f j :=
    Finset.single_le_sum (f := fun j => f j * f j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  exact abs_le_one_iff_mul_self_le_one.2 (h1.trans (h.trans hb))
abbrev _root_.YangMills.SharedProofs.p79073 := @abs_le_one_of_sum_sq
private lemma abs_tripleCoords_le_one (P : PauliCoordinates L n k) {τ : LevelTriple L n k}
    (h : tripleNormSq τ ≤ 1) (i : TripleCoordIndex L n k) : |tripleCoords P τ i| ≤ 1 := by
  have h1 : levelFormsNormSq τ.1 = ∑ ι, P.formCoords τ.1 ι * P.formCoords τ.1 ι :=
    P.formCoords_pairing _ _
  have h2 : levelFormsNormSq τ.2.1 = ∑ ι, P.formCoords τ.2.1 ι * P.formCoords τ.2.1 ι :=
    P.formCoords_pairing _ _
  have h3 : topFormNormSq τ.2.2 = ∑ ι, P.topFormCoords τ.2.2 ι * P.topFormCoords τ.2.2 ι :=
    P.topFormCoords_pairing _ _
  have n1 : 0 ≤ levelFormsNormSq τ.1 := h1 ▸ Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have n2 : 0 ≤ levelFormsNormSq τ.2.1 := h2 ▸ Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have n3 : 0 ≤ topFormNormSq τ.2.2 := h3 ▸ Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have ht : levelFormsNormSq τ.1 + levelFormsNormSq τ.2.1 + topFormNormSq τ.2.2 ≤ 1 := h
  rcases i with p | p | p
  · exact abs_le_one_of_sum_sq h1.symm.le (by linarith) p
  · exact abs_le_one_of_sum_sq h2.symm.le (by linarith) p
  · exact abs_le_one_of_sum_sq h3.symm.le (by linarith) p
private lemma tripleOfCoords_tripleCoords (P : PauliCoordinates L n k) (τ : LevelTriple L n k) :
    tripleOfCoords P (tripleCoords P τ) = τ := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact P.formCoords.symm_apply_apply _
  · exact P.formCoords.symm_apply_apply _
  · exact P.topFormCoords.symm_apply_apply _
private lemma tripleCoords_linear (P : PauliCoordinates L n k) (s t : ℝ)
    (τ τ' : LevelTriple L n k) :
    tripleCoords P (s • τ + t • τ') = s • tripleCoords P τ + t • tripleCoords P τ' := by
  funext i
  rcases i with p | p | p <;> simp [tripleCoords]
end PartValues
theorem saddlePointMatrixIsLocal_of_parts (hcl : LocallyHolomorphicFamiliesClosed)
    (hloc : HolomorphicFamiliesAreLocal)
    (hH : ChainActionHessianIsLocal)
    (hB : ChainBracketIsLocallyHolomorphic)
    (hS : GaugeCorrectionIsLocal)
    (hD : GaugeOrbitMapIsLocal)
    (hQ : TopSecondVariationIsLocal)
    (hG : GaugeSliceResidualIsLocal)
    (hO : GaugeConstraintMatrixIsLocal) :
    SaddlePointMatrixIsLocal := by
  intro a ha L hL k hk
  obtain ⟨ρ₁, C₁, r₁, p₁, c₁, s₁, H₁⟩ := hH a ha L hL k hk
  obtain ⟨ρ₂, C₂, r₂, p₂, c₂, s₂, H₂⟩ := hB L hL k hk
  obtain ⟨ρ₃, C₃, r₃, p₃, c₃, s₃, H₃⟩ := hS L hL k hk
  obtain ⟨ρ₄, C₄, r₄, p₄, c₄, s₄, H₄⟩ := hD L hL k hk
  obtain ⟨ρ₅, C₅, r₅, p₅, c₅, s₅, H₅⟩ := hQ L hL k hk
  obtain ⟨ρ₆, C₆, r₆, p₆, c₆, s₆, H₆⟩ := hG L hL k hk
  obtain ⟨ρ₇, C₇, r₇, p₇, c₇, s₇, H₇⟩ := hO L hL k hk
  obtain ⟨ρ, hρ, l₁, l₂, l₃, l₄, l₅, l₆, l₇⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₁ ∧ ρ ≤ ρ₂ ∧ ρ ≤ ρ₃ ∧
      ρ ≤ ρ₄ ∧ ρ ≤ ρ₅ ∧ ρ ≤ ρ₆ ∧ ρ ≤ ρ₇ := by
    refine ⟨min ρ₁ (min ρ₂ (min ρ₃ (min ρ₄ (min ρ₅ (min ρ₆ ρ₇))))), by positivity, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩ <;> simp
  obtain ⟨K, hK, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ : ∃ K : ℝ, 0 ≤ K ∧ C₁ ≤ K ∧ C₂ ≤ K ∧ C₃ ≤ K ∧
      C₄ ≤ K ∧ C₅ ≤ K ∧ C₆ ≤ K ∧ C₇ ≤ K :=
    ⟨C₁ + C₂ + C₃ + C₄ + C₅ + C₆ + C₇, by positivity, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨r, hr, t₁, t₂, t₃, t₄, t₅, t₆, t₇⟩ : ∃ r : ℝ, 0 ≤ r ∧ r₁ ≤ r ∧ r₂ ≤ r ∧ r₃ ≤ r ∧
      r₄ ≤ r ∧ r₅ ≤ r ∧ r₆ ≤ r ∧ r₇ ≤ r :=
    ⟨r₁ + r₂ + r₃ + r₄ + r₅ + r₆ + r₇, by positivity, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩
  have hKb : 0 ≤ saddleConst K := by
    unfold saddleConst kernelConst
    positivity
  obtain ⟨M, θ, hM, hθ, HL⟩ := hloc ρ (saddleConst K) (14 * r) hρ hKb (by positivity)
  refine ⟨M, θ, hM, hθ, ?_⟩
  filter_upwards [H₁, H₂, H₃, H₄, H₅, H₆, H₇] with n H₁ H₂ H₃ H₄ H₅ H₆ H₇
  intro _ _ _ _ _ _ _ _ P y y' τ τ' hy hy' hq hq'
  letI : DecidableEq (Fin 3 × Vertex L n k 0) := Classical.decEq _
  obtain ⟨G₁, f₁, e₁⟩ := H₁ P
  obtain ⟨G₂, f₂, e₂⟩ := H₂ P
  obtain ⟨G₃, f₃, e₃⟩ := H₃ P
  obtain ⟨G₄, f₄, e₄⟩ := H₄ P
  obtain ⟨G₅, f₅, e₅⟩ := H₅ P
  obtain ⟨G₆, f₆, e₆⟩ := H₆ P
  obtain ⟨G₇, f₇, e₇⟩ := H₇ P
  have cl := hcl L n k
  have hF := saddleBlocks_family cl hr (cl.mono l₁ k₁ t₁ f₁) (cl.mono l₂ k₂ t₂ f₂)
    (cl.mono l₃ k₃ t₃ f₃) (cl.mono l₄ k₄ t₄ f₄) (cl.mono l₅ k₅ t₅ f₅) (cl.mono l₆ k₆ t₆ f₆)
    (cl.mono l₇ k₇ t₇ f₇)
  have tie : ∀ᶠ x : TripleCoordIndex L n k → ℝ in 𝓝 0,
      saddlePointMatrix P a (tripleOfCoords P x) =
      Matrix.fromBlocks
        (symmPart (gaugeFixedKernel (G₁ (complexifyCoords x)) (G₂ (complexifyCoords x))
          (G₃ (complexifyCoords x)) (G₄ (complexifyCoords x)) (G₅ (complexifyCoords x))
          (G₆ (complexifyCoords x))))
        (G₇ (complexifyCoords x)).transpose (G₇ (complexifyCoords x)) 0 := by
    filter_upwards [e₁, e₂, e₃, e₄, e₅, e₆, e₇] with x e₁ e₂ e₃ e₄ e₅ e₆ e₇
    exact saddlePointMatrix_eq_blocks P a x _ _ _ _ _ _ _ e₁ e₂ e₃ e₄ e₅ e₆ e₇
  set x := tripleCoords P τ with hx
  set x' := tripleCoords P τ' with hx'
  have ht : Tendsto (fun w : ℝ × ℝ => w.1 • x + w.2 • x') (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun w : ℝ × ℝ => w.1 • x + w.2 • x' := by fun_prop
    simpa using hc.tendsto 0
  refine HL tripleCoordIndexCell saddlePointIndexCell _
    (fun s t => saddlePointMatrix P a (s • τ + t • τ'))
    x x' y y' hF (abs_tripleCoords_le_one P hq) (abs_tripleCoords_le_one P hq')
    (tripleCoords_eq_zero_off_cell P hy) (tripleCoords_eq_zero_off_cell P hy') ?_
  filter_upwards [ht.eventually tie] with w hw
  have e : tripleOfCoords P (w.1 • x + w.2 • x') = w.1 • τ + w.2 • τ' := by
    rw [hx, hx', ← tripleCoords_linear, tripleOfCoords_tripleCoords]
  rw [e] at hw
  exact hw
end YangMills.Construction.RunningCouplingSlope.SaddlePointMatrixLocality
end
