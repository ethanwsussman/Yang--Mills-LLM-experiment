import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreClosed
import YangMills.Construction.RunningCouplingSlope.MixedDerivativeByCellsProof
import YangMills.Construction.RunningCouplingSlope.TheOrbitMapReadsNearCellsProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ClosureProof
open Tower
section OperatorNorms
variable {a a' b b' : Type}
private lemma opNorm_map_conj_le [Fintype a] [Fintype b] [DecidableEq b] (X : Matrix a b ℂ) :
    ‖X.map (starRingEnd ℂ)‖ ≤ ‖X‖ := by
  rw [Matrix.l2_opNorm_def (A := X.map (starRingEnd ℂ))]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  let w : EuclideanSpace ℂ b := WithLp.toLp 2 fun i => starRingEnd ℂ (v i)
  have hw : ‖w‖ = ‖v‖ := by
    simp [w, EuclideanSpace.norm_eq]
  have h := X.l2_opNorm_mulVec w
  rw [hw] at h
  refine le_trans (le_of_eq ?_) h
  simp only [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have : (X.map (starRingEnd ℂ)).mulVec (WithLp.ofLp v) i =
      starRingEnd ℂ (X.mulVec (WithLp.ofLp w) i) := by
    simp [Matrix.mulVec, dotProduct, w, map_sum]
  simp [Matrix.toLpLin_apply, this]
private lemma opNorm_transpose_le [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (X : Matrix a b ℂ) : ‖X.transpose‖ ≤ ‖X‖ := by
  have e : X.transpose = (X.map (starRingEnd ℂ)).conjTranspose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.l2_opNorm_conjTranspose]
  exact opNorm_map_conj_le X
abbrev _root_.YangMills.SharedProofs.p19594 := @opNorm_transpose_le
private def embedMatrix [DecidableEq a'] (f : a → a') : Matrix a' a ℂ :=
  Matrix.of fun p i => if p = f i then 1 else 0
private lemma opNorm_one_le [Fintype a] [DecidableEq a] : ‖(1 : Matrix a a ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
private lemma opNorm_embedMatrix_le [Fintype a] [Fintype a'] [DecidableEq a] [DecidableEq a']
    {f : a → a'} (hf : Function.Injective f) : ‖embedMatrix f‖ ≤ 1 := by
  have h1 : (embedMatrix f).conjTranspose * embedMatrix f = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, embedMatrix, Matrix.of_apply,
      Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · have : f i ≠ f j := fun e => h (hf e)
      simp only [h, if_false]
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : p = f i
      · subst hp
        simp [this]
      · simp [hp]
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self (embedMatrix f)
  rw [h1] at h2
  have h4 : ‖embedMatrix f‖ * ‖embedMatrix f‖ ≤ 1 := h2 ▸ opNorm_one_le
  nlinarith [norm_nonneg (embedMatrix f)]
abbrev _root_.YangMills.DeltaSharedProofs.p4300 := @opNorm_embedMatrix_le
private lemma opNorm_embed_mul_le [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] [DecidableEq a]
    [DecidableEq a'] [DecidableEq b] [DecidableEq b'] {f : a → a'} {g : b → b'}
    (hf : Function.Injective f) (hg : Function.Injective g) (X : Matrix a b ℂ) :
    ‖embedMatrix f * X * (embedMatrix g).conjTranspose‖ ≤ ‖X‖ := by
  have h1 := opNorm_embedMatrix_le hf
  have h2 : ‖(embedMatrix g).conjTranspose‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact opNorm_embedMatrix_le hg
  calc ‖embedMatrix f * X * (embedMatrix g).conjTranspose‖
      ≤ ‖embedMatrix f * X‖ * ‖(embedMatrix g).conjTranspose‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖embedMatrix f‖ * ‖X‖) * 1 :=
        mul_le_mul (Matrix.l2_opNorm_mul _ _) h2 (norm_nonneg _) (by positivity)
    _ ≤ (1 * ‖X‖) * 1 := by gcongr
    _ = ‖X‖ := by ring
abbrev _root_.YangMills.DeltaSharedProofs.p501444 := @opNorm_embed_mul_le
private lemma opNorm_fromBlocks_le [Fintype a] [Fintype a'] [Fintype b] [Fintype b']
    [DecidableEq a] [DecidableEq b] (A : Matrix a' a ℂ) (B : Matrix a' b ℂ)
    (C : Matrix b' a ℂ) (D : Matrix b' b ℂ) :
    ‖Matrix.fromBlocks A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  classical
  have e : Matrix.fromBlocks A B C D =
      embedMatrix (Sum.inl : a' → a' ⊕ b') * A * (embedMatrix (Sum.inl : a → a ⊕ b)).conjTranspose +
      embedMatrix (Sum.inl : a' → a' ⊕ b') * B * (embedMatrix (Sum.inr : b → a ⊕ b)).conjTranspose +
      embedMatrix (Sum.inr : b' → a' ⊕ b') * C * (embedMatrix (Sum.inl : a → a ⊕ b)).conjTranspose +
      embedMatrix (Sum.inr : b' → a' ⊕ b') * D * (embedMatrix (Sum.inr : b → a ⊕ b)).conjTranspose := by
    ext p q
    rcases p with p | p <;> rcases q with q | q <;>
      simp [Matrix.mul_apply, embedMatrix, Matrix.conjTranspose_apply]
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
  · exact opNorm_embed_mul_le Sum.inl_injective Sum.inl_injective A
  · exact opNorm_embed_mul_le Sum.inl_injective Sum.inr_injective B
  · exact opNorm_embed_mul_le Sum.inr_injective Sum.inl_injective C
  · exact opNorm_embed_mul_le Sum.inr_injective Sum.inr_injective D
abbrev _root_.YangMills.SharedProofs.p53664 := @opNorm_fromBlocks_le
end OperatorNorms
section CellDistance
variable {L n k : ℕ}
private lemma cellDist_comm' (u v : Tower.Vertex L n k k) : cellDist u v = cellDist v u := by apply _root_.YangMills.SharedProofs.p19196 <;> assumption
private lemma cellDist_triangle' (u v w : Tower.Vertex L n k k) :
    cellDist u w ≤ cellDist u v + cellDist v w := by apply _root_.YangMills.SharedProofs.p82152 <;> assumption
private lemma cellDist_self' (u : Tower.Vertex L n k k) : cellDist u u = 0 := by apply _root_.YangMills.SharedProofs.p28613 <;> assumption
end CellDistance
section FamilyClosure
variable {L n k : ℕ} {I ι ι' κ : Type} [Fintype I] [Fintype ι] [Fintype ι'] [Fintype κ]
private lemma family_mono [DecidableEq ι] {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k}
    {c' : ι' → Tower.Vertex L n k k} {F : (I → ℂ) → Matrix ι' ι ℂ} {ρ C r ρ' C' r' : ℝ} (hρ : ρ' ≤ ρ)
    (hC : C ≤ C') (hr : r ≤ r') (h : IsLocallyHolomorphicFamily e c c' F ρ C r) :
    IsLocallyHolomorphicFamily e c c' F ρ' C' r' := by
  have hb := Metric.ball_subset_ball (x := (0 : I → ℂ)) hρ
  refine ⟨fun p q => (h.holomorphic p q).mono hb, fun z hz => (h.norm_le z (hb hz)).trans hC,
    fun p q z hz z' hz' hh => ?_, fun z hz p q hd => ?_⟩
  · exact h.depends_near p q z (hb hz) z' (hb hz') fun i hi => hh i (hi.trans hr)
  · exact h.eq_zero_of_far z (hb hz) p q (lt_of_le_of_lt hr hd)
private lemma family_one [DecidableEq ι] (e : I → Tower.Vertex L n k k) (c : ι → Tower.Vertex L n k k)
    (ρ r : ℝ) (hr : 0 ≤ r) :
    IsLocallyHolomorphicFamily e c c (fun _ => (1 : Matrix ι ι ℂ)) ρ 1 r := by
  refine ⟨fun p q => analyticOnNhd_const, fun _ _ => opNorm_one_le, fun _ _ _ _ _ _ _ => rfl,
    fun z _ p q hd => ?_⟩
  have hne : p ≠ q := by
    rintro rfl
    rw [cellDist_self'] at hd
    exact absurd hd (not_lt.2 hr)
  exact Matrix.one_apply_ne hne
private lemma family_add [DecidableEq ι] {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k}
    {c' : ι' → Tower.Vertex L n k k} {F G : (I → ℂ) → Matrix ι' ι ℂ} {ρ C C' r : ℝ}
    (hF : IsLocallyHolomorphicFamily e c c' F ρ C r)
    (hG : IsLocallyHolomorphicFamily e c c' G ρ C' r) :
    IsLocallyHolomorphicFamily e c c' (fun z => F z + G z) ρ (C + C') r := by
  refine ⟨fun p q => (hF.holomorphic p q).add (hG.holomorphic p q), fun z hz => ?_,
    fun p q z hz z' hz' hh => ?_, fun z hz p q hd => ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (hF.norm_le z hz) (hG.norm_le z hz))
  · simp only [Matrix.add_apply]
    rw [hF.depends_near p q z hz z' hz' hh, hG.depends_near p q z hz z' hz' hh]
  · simp only [Matrix.add_apply]
    rw [hF.eq_zero_of_far z hz p q hd, hG.eq_zero_of_far z hz p q hd, add_zero]
private lemma family_smul [DecidableEq ι] {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k}
    {c' : ι' → Tower.Vertex L n k k} {F : (I → ℂ) → Matrix ι' ι ℂ} {ρ C r : ℝ} (x : ℂ)
    (hF : IsLocallyHolomorphicFamily e c c' F ρ C r) :
    IsLocallyHolomorphicFamily e c c' (fun z => x • F z) ρ (‖x‖ * C) r := by
  refine ⟨fun p q => analyticOnNhd_const.mul (hF.holomorphic p q), fun z hz => ?_,
    fun p q z hz z' hz' hh => ?_, fun z hz p q hd => ?_⟩
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hF.norm_le z hz) (norm_nonneg _)
  · simp only [Matrix.smul_apply]
    rw [hF.depends_near p q z hz z' hz' hh]
  · simp only [Matrix.smul_apply]
    rw [hF.eq_zero_of_far z hz p q hd, smul_zero]
private lemma family_mul [DecidableEq ι] [DecidableEq κ] {e : I → Tower.Vertex L n k k}
    {c : ι → Tower.Vertex L n k k} {c' : ι' → Tower.Vertex L n k k} {d : κ → Tower.Vertex L n k k}
    {F : (I → ℂ) → Matrix ι' ι ℂ} {G : (I → ℂ) → Matrix ι κ ℂ} {ρ C C' r r' : ℝ} (_hr : 0 ≤ r)
    (hr' : 0 ≤ r') (hF : IsLocallyHolomorphicFamily e c c' F ρ C r)
    (hG : IsLocallyHolomorphicFamily e d c G ρ C' r') :
    IsLocallyHolomorphicFamily e d c' (fun z => F z * G z) ρ (C * C') (r + r') := by
  refine ⟨fun p q => ?_, fun z hz => ?_, fun p q z hz z' hz' hh => ?_, fun z hz p q hd => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.analyticOnNhd_fun_sum _ fun m _ => (hF.holomorphic p m).mul (hG.holomorphic m q)
  · exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hF.norm_le z hz) (hG.norm_le z hz)
      (norm_nonneg _) ((norm_nonneg _).trans (hF.norm_le z hz)))
  · simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : r < cellDist (c' p) (c m)
    · rw [hF.eq_zero_of_far z hz p m hm, hF.eq_zero_of_far z' hz' p m hm, zero_mul, zero_mul]
    · have h1 : F z p m = F z' p m := hF.depends_near p m z hz z' hz' fun i hi =>
        hh i (hi.trans (by linarith))
      have h2 : G z m q = G z' m q := hG.depends_near m q z hz z' hz' fun i hi => by
        refine hh i ((cellDist_triangle' _ (c m) _).trans ?_)
        rw [cellDist_comm' (c m) (c' p)]
        linarith [not_lt.1 hm]
      rw [h1, h2]
  · simp only [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : r < cellDist (c' p) (c m)
    · rw [hF.eq_zero_of_far z hz p m hm, zero_mul]
    · have : r' < cellDist (c m) (d q) := by
        have := cellDist_triangle' (c' p) (c m) (d q)
        linarith [not_lt.1 hm]
      rw [hG.eq_zero_of_far z hz m q this, mul_zero]
private lemma family_transpose [DecidableEq ι] [DecidableEq ι'] {e : I → Tower.Vertex L n k k}
    {c : ι → Tower.Vertex L n k k} {c' : ι' → Tower.Vertex L n k k} {F : (I → ℂ) → Matrix ι' ι ℂ}
    {ρ C r : ℝ} (hr : 0 ≤ r) (hF : IsLocallyHolomorphicFamily e c c' F ρ C r) :
    IsLocallyHolomorphicFamily e c' c (fun z => (F z).transpose) ρ C (2 * r) := by
  refine ⟨fun p q => hF.holomorphic q p,
    fun z hz => (opNorm_transpose_le _).trans (hF.norm_le z hz),
    fun p q z hz z' hz' hh => ?_, fun z hz p q hd => ?_⟩
  · simp only [Matrix.transpose_apply]
    by_cases hm : r < cellDist (c' q) (c p)
    · rw [hF.eq_zero_of_far z hz q p hm, hF.eq_zero_of_far z' hz' q p hm]
    · refine hF.depends_near q p z hz z' hz' fun i hi => hh i ?_
      refine (cellDist_triangle' _ (c' q) _).trans ?_
      linarith [not_lt.1 hm]
  · simp only [Matrix.transpose_apply]
    refine hF.eq_zero_of_far z hz q p ?_
    rw [cellDist_comm']
    linarith
private lemma family_fromBlocks {ι₂ κ₂ : Type} [Fintype ι₂] [Fintype κ₂] [DecidableEq ι]
    [DecidableEq κ] {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k}
    {d : κ → Tower.Vertex L n k k} {c' : ι₂ → Tower.Vertex L n k k} {d' : κ₂ → Tower.Vertex L n k k}
    {A : (I → ℂ) → Matrix ι₂ ι ℂ} {B : (I → ℂ) → Matrix ι₂ κ ℂ} {C : (I → ℂ) → Matrix κ₂ ι ℂ}
    {D : (I → ℂ) → Matrix κ₂ κ ℂ}
    {ρ K₁ K₂ K₃ K₄ r : ℝ} (hA : IsLocallyHolomorphicFamily e c c' A ρ K₁ r)
    (hB : IsLocallyHolomorphicFamily e d c' B ρ K₂ r)
    (hC : IsLocallyHolomorphicFamily e c d' C ρ K₃ r)
    (hD : IsLocallyHolomorphicFamily e d d' D ρ K₄ r) :
    IsLocallyHolomorphicFamily e (Sum.elim c d) (Sum.elim c' d')
      (fun z => Matrix.fromBlocks (A z) (B z) (C z) (D z)) ρ (K₁ + K₂ + K₃ + K₄) r := by
  refine ⟨fun p q => ?_, fun z hz => ?_, fun p q z hz z' hz' hh => ?_, fun z hz p q hd => ?_⟩
  · rcases p with p | p <;> rcases q with q | q
    · exact hA.holomorphic p q
    · exact hB.holomorphic p q
    · exact hC.holomorphic p q
    · exact hD.holomorphic p q
  · exact (opNorm_fromBlocks_le _ _ _ _).trans (add_le_add (add_le_add (add_le_add
      (hA.norm_le z hz) (hB.norm_le z hz)) (hC.norm_le z hz)) (hD.norm_le z hz))
  · rcases p with p | p <;> rcases q with q | q
    · exact hA.depends_near p q z hz z' hz' hh
    · exact hB.depends_near p q z hz z' hz' hh
    · exact hC.depends_near p q z hz z' hz' hh
    · exact hD.depends_near p q z hz z' hz' hh
  · rcases p with p | p <;> rcases q with q | q
    · exact hA.eq_zero_of_far z hz p q hd
    · exact hB.eq_zero_of_far z hz p q hd
    · exact hC.eq_zero_of_far z hz p q hd
    · exact hD.eq_zero_of_far z hz p q hd
end FamilyClosure
theorem locallyHolomorphicFamiliesClosed_holds : LocallyHolomorphicFamiliesClosed := fun _ _ _ =>
  ⟨family_mono, family_one, family_add, family_smul, family_mul, family_transpose, family_fromBlocks⟩
end YangMills.Construction.RunningCouplingSlope.ClosureProof
end
