import YangMills.Construction.LawInAState.KernelNearTwoSitesProof
import YangMills.Construction.LawInAState.TraceNearItsPlanes
import YangMills.Construction.LawInAState.TraceOfOnePair
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TraceBounds
open TorusFields StateLaws ResponseInTheExpansion
private theorem reflectionKernel_swap (u : Fin 4 → ℝ) (m n r s : Fin 4) :
    ReflectionKernel.kernel u m n r s = ReflectionKernel.kernel u r s m n := by
  have h : ∀ a b, ReflectionKernel.reflectionEntry u a b = ReflectionKernel.reflectionEntry u b a := by
    intro a b
    simp only [ReflectionKernel.reflectionEntry, eq_comm (a := a) (b := b)]
    ring
  simp only [ReflectionKernel.kernel]
  rw [h m r, h n s, h m s, h n r]
  ring
private theorem supDist_vertex_le_one {N : ℕ} [NeZero N] (s c : TorusSite N) (μ ν : Fin 4)
    (hc : c ∈ plaquetteVertices s μ ν) (hlt : μ < ν) : _root_.YangMills.Construction.TorusFields.supDist s c ≤ 1 := by apply _root_.YangMills.SharedProofs.p36485 <;> assumption
private theorem pow_five_le_siteWeight_of_not_mem {N : ℕ} [NeZero N] {o y : TorusSite N} {R : ℕ} {n : ℝ}
    (hR : 8 ≤ R) (hn : 2 ≤ n) (hy : (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) ≤ (R : ℝ) / 8 - n + 2) {p : TorusPlaquette N}
    (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)))
    (hout : p ∉ plaquettesIn (supBall o (2 * (R : ℝ)))) : (R : ℝ) ^ 5 ≤ siteWeight y p := by
  obtain ⟨-, hlt, -⟩ := Finset.mem_filter.mp hp
  have : ∃ c ∈ plaquetteVertices p.1 p.2.1 p.2.2, c ∉ supBall o (2 * (R : ℝ)) := by
    by_contra hall
    push_neg at hall
    exact hout (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hall⟩)
  obtain ⟨c, hc, hco⟩ := this
  have h1 : 2 * (R : ℝ) < (_root_.YangMills.Construction.TorusFields.supDist c o : ℝ) := by
    by_contra hcon
    push_neg at hcon
    exact hco (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
  have t1 : (_root_.YangMills.Construction.TorusFields.supDist p.1 c : ℝ) ≤ 1 := by exact_mod_cast supDist_vertex_le_one p.1 c _ _ hc hlt
  have t2 : _root_.YangMills.Construction.TorusFields.supDist c o ≤ _root_.YangMills.Construction.TorusFields.supDist c p.1 + _root_.YangMills.Construction.TorusFields.supDist p.1 o := _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
  have t3 : _root_.YangMills.Construction.TorusFields.supDist p.1 o ≤ _root_.YangMills.Construction.TorusFields.supDist p.1 y + _root_.YangMills.Construction.TorusFields.supDist y o := _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm c p.1] at t2
  have t2' : (_root_.YangMills.Construction.TorusFields.supDist c o : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist p.1 c : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist p.1 o : ℝ) := by exact_mod_cast t2
  have t3' : (_root_.YangMills.Construction.TorusFields.supDist p.1 o : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) := by exact_mod_cast t3
  have hR8 : (8 : ℝ) ≤ R := by exact_mod_cast hR
  have h5 : (R : ℝ) ≤ 1 + (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) := by linarith
  exact pow_le_pow_left₀ (by positivity) h5 5
private theorem abs_planeSums_ball_sub_univ_le {N : ℕ} [NeZero N] {o y : TorusSite N} {R : ℕ} {n M : ℝ}
    (hR : 8 ≤ R) (hn : 2 ≤ n) (hy : (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) ≤ (R : ℝ) / 8 - n + 2)
    (k : TorusPlaquette N → TorusPlaquette N → ℝ)
    (hM : ∑ p ∈ plaquettesIn Finset.univ, ∑ p' ∈ plaquettesIn Finset.univ,
      |k p p'| * (siteWeight y p * siteWeight y p') ≤ M)
    (A B : Fin 4 × Fin 4) :
    |∑ p ∈ (plaquettesIn (supBall o (2 * (R : ℝ)))).filter (fun p : TorusPlaquette N => p.2 = A),
        ∑ p' ∈ (plaquettesIn (supBall o (2 * (R : ℝ)))).filter (fun p' : TorusPlaquette N => p'.2 = B), k p p' -
      ∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette N => p.2 = A),
        ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette N => p'.2 = B), k p p'|
      ≤ M * ((R : ℝ) ^ 5)⁻¹ := by
  classical
  set Q := plaquettesIn (Finset.univ : Finset (TorusSite N)) with hQ
  set P := plaquettesIn (supBall o (2 * (R : ℝ))) with hP
  have hPQ : P ⊆ Q := by
    intro p hp
    obtain ⟨-, h1, -⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, fun _ _ => Finset.mem_univ _⟩
  set S₁ := Q.filter (fun p : TorusPlaquette N => p.2 = A) ×ˢ Q.filter (fun p' : TorusPlaquette N => p'.2 = B)
    with hS₁
  set S₂ := P.filter (fun p : TorusPlaquette N => p.2 = A) ×ˢ P.filter (fun p' : TorusPlaquette N => p'.2 = B)
    with hS₂
  have hsub : S₂ ⊆ S₁ :=
    Finset.product_subset_product (Finset.filter_subset_filter _ hPQ) (Finset.filter_subset_filter _ hPQ)
  have e1 : ∑ p ∈ Q.filter (fun p : TorusPlaquette N => p.2 = A),
      ∑ p' ∈ Q.filter (fun p' : TorusPlaquette N => p'.2 = B), k p p' =
      ∑ q ∈ S₁, k q.1 q.2 := by rw [hS₁, Finset.sum_product]
  have e2 : ∑ p ∈ P.filter (fun p : TorusPlaquette N => p.2 = A),
      ∑ p' ∈ P.filter (fun p' : TorusPlaquette N => p'.2 = B), k p p' =
      ∑ q ∈ S₂, k q.1 q.2 := by rw [hS₂, Finset.sum_product]
  rw [e1, e2, ← Finset.sum_sdiff hsub, add_comm, sub_add_cancel_left, abs_neg]
  have hRp : 0 < (R : ℝ) ^ 5 := by positivity
  have hpt : ∀ q ∈ S₁ \ S₂, |k q.1 q.2| ≤
      ((R : ℝ) ^ 5)⁻¹ * (|k q.1 q.2| * (siteWeight y q.1 * siteWeight y q.2)) := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨q1, q2⟩ := Finset.mem_product.mp h1
    obtain ⟨hq1, hA⟩ := Finset.mem_filter.mp q1
    obtain ⟨hq2, hB⟩ := Finset.mem_filter.mp q2
    have hW1 : 1 ≤ siteWeight y q.1 :=
      one_le_pow₀ (by have : (0 : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist q.1.1 y := Nat.cast_nonneg _; linarith)
    have hW2 : 1 ≤ siteWeight y q.2 :=
      one_le_pow₀ (by have : (0 : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist q.2.1 y := Nat.cast_nonneg _; linarith)
    have hbig : (R : ℝ) ^ 5 ≤ siteWeight y q.1 * siteWeight y q.2 := by
      by_cases hp1 : q.1 ∈ P
      · have hp2 : q.2 ∉ P := fun hp2 => h2 (Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hp1, hA⟩, Finset.mem_filter.mpr ⟨hp2, hB⟩⟩)
        have := pow_five_le_siteWeight_of_not_mem hR hn hy hq2 hp2
        nlinarith
      · have := pow_five_le_siteWeight_of_not_mem hR hn hy hq1 hp1
        nlinarith
    have h1' : 1 ≤ ((R : ℝ) ^ 5)⁻¹ * (siteWeight y q.1 * siteWeight y q.2) := by
      rw [inv_mul_eq_div, one_le_div hRp]
      exact hbig
    calc |k q.1 q.2| = |k q.1 q.2| * 1 := (mul_one _).symm
      _ ≤ |k q.1 q.2| * (((R : ℝ) ^ 5)⁻¹ * (siteWeight y q.1 * siteWeight y q.2)) :=
        mul_le_mul_of_nonneg_left h1' (abs_nonneg _)
      _ = _ := by ring
  have hW0 : ∀ p, 0 ≤ siteWeight y p := fun p => by
    have : (0 : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist p.1 y := Nat.cast_nonneg _
    unfold siteWeight
    positivity
  have hQQ : ∑ q ∈ S₁ \ S₂, |k q.1 q.2| * (siteWeight y q.1 * siteWeight y q.2) ≤ M := by
    refine le_trans ?_ hM
    rw [← Finset.sum_product (s := Q) (t := Q)
      (f := fun q => |k q.1 q.2| * (siteWeight y q.1 * siteWeight y q.2))]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ =>
      mul_nonneg (abs_nonneg _) (mul_nonneg (hW0 _) (hW0 _))
    intro q hq
    obtain ⟨q1, q2⟩ := Finset.mem_product.mp (Finset.mem_sdiff.mp hq).1
    exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp q1).1, (Finset.mem_filter.mp q2).1⟩
  calc _ ≤ ∑ q ∈ S₁ \ S₂, |k q.1 q.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ S₁ \ S₂, ((R : ℝ) ^ 5)⁻¹ * (|k q.1 q.2| * (siteWeight y q.1 * siteWeight y q.2)) :=
      Finset.sum_le_sum hpt
    _ = ((R : ℝ) ^ 5)⁻¹ * ∑ q ∈ S₁ \ S₂, |k q.1 q.2| * (siteWeight y q.1 * siteWeight y q.2) := by
      rw [Finset.mul_sum]
    _ ≤ ((R : ℝ) ^ 5)⁻¹ * M := mul_le_mul_of_nonneg_left hQQ (by positivity)
    _ = _ := by ring
private theorem plaquettesIn_subset_univ {N : ℕ} [NeZero N] (S : Finset (TorusSite N)) :
    plaquettesIn S ⊆ plaquettesIn (Finset.univ : Finset (TorusSite N)) := by
  intro p hp
  obtain ⟨-, h1, -⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, fun _ _ => Finset.mem_univ _⟩
private theorem siteWeight_nonneg' {N : ℕ} (y : TorusSite N) (p : TorusPlaquette N) : 0 ≤ siteWeight y p := by
  have : (0 : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist p.1 y := Nat.cast_nonneg _
  unfold siteWeight
  positivity
private theorem one_le_siteWeight' {N : ℕ} (y : TorusSite N) (p : TorusPlaquette N) : 1 ≤ siteWeight y p :=
  one_le_pow₀ (by have : (0 : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist p.1 y := Nat.cast_nonneg _; linarith)
private theorem weightedSums_le_of_subset {N : ℕ} [NeZero N] {y : TorusSite N} {M : ℝ} (S : Finset (TorusSite N))
    (k : TorusPlaquette N → TorusPlaquette N → ℝ)
    (hM : ∑ p ∈ plaquettesIn Finset.univ, ∑ p' ∈ plaquettesIn Finset.univ,
      |k p p'| * (siteWeight y p * siteWeight y p') ≤ M) :
    ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S, |k p p'| * (siteWeight y p * siteWeight y p') ≤ M := by
  refine le_trans ?_ hM
  have h0 : ∀ p p', 0 ≤ |k p p'| * (siteWeight y p * siteWeight y p') := fun p p' =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (siteWeight_nonneg' _ _) (siteWeight_nonneg' _ _))
  calc _ ≤ ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn Finset.univ,
        |k p p'| * (siteWeight y p * siteWeight y p') :=
        Finset.sum_le_sum fun p _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (plaquettesIn_subset_univ S) fun p' _ _ => h0 p p'
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (plaquettesIn_subset_univ S) fun p _ _ =>
        Finset.sum_nonneg fun p' _ => h0 p p'
private theorem abs_diagonal_le {N : ℕ} [NeZero N] {o : TorusSite N} {n R M err : ℝ} {Y : Finset (TorusSite N)}
    {κ : TorusSite N → TorusPlaquette N → TorusPlaquette N → ℝ} {α : TorusSite N → ℝ}
    (hf : IsSiteKernelFamily o n R M err Y κ α) (y : TorusSite N) (hy : y ∈ Y) :
    |α y| ≤ M + err := by
  have hA : ((0, 1) : Fin 4 × Fin 4) ∈ ReflectionKernel.orientedPlanes := by decide
  have h1 := hf.plane_sums y hy _ hA _ hA
  rw [if_pos rfl] at h1
  set Q := (plaquettesIn (Finset.univ : Finset (TorusSite N))).filter
    (fun p : TorusPlaquette N => p.2 = ((0, 1) : Fin 4 × Fin 4)) with hQ
  have h2 : |∑ p ∈ Q, ∑ p' ∈ Q, κ y p p'| ≤ M := by
    refine le_trans ?_ (hf.weighted_sum_le y hy)
    have h0 : ∀ p p', 0 ≤ |κ y p p'| * (siteWeight y p * siteWeight y p') := fun p p' =>
      mul_nonneg (abs_nonneg _) (mul_nonneg (siteWeight_nonneg' _ _) (siteWeight_nonneg' _ _))
    calc _ ≤ ∑ p ∈ Q, ∑ p' ∈ Q, |κ y p p'| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ Q, ∑ p' ∈ Q, |κ y p p'| * (siteWeight y p * siteWeight y p') := by
          refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun p' _ => ?_
          have : 1 ≤ siteWeight y p * siteWeight y p' :=
            one_le_mul_of_one_le_of_one_le (one_le_siteWeight' _ _) (one_le_siteWeight' _ _)
          nlinarith [abs_nonneg (κ y p p')]
      _ ≤ ∑ p ∈ Q, ∑ p' ∈ plaquettesIn Finset.univ, |κ y p p'| * (siteWeight y p * siteWeight y p') :=
          Finset.sum_le_sum fun p _ =>
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p' _ _ => h0 p p'
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ =>
          Finset.sum_nonneg fun p' _ => h0 p p'
  have h3 := abs_sub_abs_le_abs_sub (α y) (∑ p ∈ Q, ∑ p' ∈ Q, κ y p p')
  rw [abs_sub_comm] at h3
  linarith
theorem pairTraceApprox_proof (hK : maxwellKernelNearSitesStatement) (hRf : ReflectionKernel.KernelEstimates)
    (hT : TraceNearPlaneValues) : PairTraceApprox := by
  intro N _ T Ck cT n err M R o Y Z κ κ' α β hn hN hR8 herr hM0 hTn hTb hsym hf hf' hD
  set c₄ : ℝ := 1024 * |Ck| + 192000 + (|cT| + 1) * 16 ^ 5 with hc₄
  set e : ℝ := c₄ * ((n ^ 5)⁻¹ + ((R : ℝ) ^ 4)⁻¹) with he
  set b : ℝ := 288 * (n ^ 4)⁻¹ with hb
  set e₁ : ℝ := err + M * ((R : ℝ) ^ 5)⁻¹ with he₁
  set g : ℝ := M + err with hg
  have hsq : ∀ y ∈ Y, ∀ z ∈ Z, (fun i => (minimalSiteDiff y z i : ℝ)) ≠ 0 := by
    intro y hy z hz h0
    have := (hD y hy z hz).2
    rw [h0] at this
    simp only [ReflectionKernel.normSq, Pi.zero_apply] at this
    have h2 : 0 < n ^ 2 / 4 := by positivity
    norm_num at this
    linarith
  have hU : ∀ y ∈ Y, ∀ z ∈ Z, ∀ p ∈ plaquettesIn (supBall o (2 * (R : ℝ))),
      ∀ p' ∈ plaquettesIn (supBall o (2 * (R : ℝ))),
      |T p p' - ReflectionKernel.kernel (fun i => (minimalSiteDiff y z i : ℝ)) p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
        e * (siteWeight y p * siteWeight z p') := by
    intro y hy z hz p hp p' hp'
    have := hK T Ck cT n R o hn hN hTn y z (hf.supDist_le y hy) (hf'.supDist_le z hz) (hD y hy z hz).1
      (hD y hy z hz).2 p p' (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp').2.1
      ((hTb p hp p' hp').trans le_rfl)
    rw [he, mul_assoc]
    exact this
  have hmain := hT (TorusPlaquette N) (TorusSite N) (plaquettesIn (supBall o (2 * (R : ℝ)))) (fun p => p.2)
    ReflectionKernel.orientedPlanes Y Z κ κ' T
    (fun y z A B => ReflectionKernel.kernel (fun i => (minimalSiteDiff y z i : ℝ)) A.1 A.2 B.1 B.2)
    siteWeight α β e b e₁ g M
    (by positivity) (by positivity) (by positivity) (by positivity) hM0
    (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩)
    (fun y p => one_le_siteWeight' y p) hU
    (fun y hy z hz p hp p' hp' => by
      have := hU y hy z hz p hp p' hp'
      rw [hsym p' p, reflectionKernel_swap]
      exact this)
    (fun y hy z hz A B => by
      have h1 := hRf.1 (fun i => (minimalSiteDiff y z i : ℝ)) A.1 A.2 B.1 B.2 (hsq y hy z hz)
      refine h1.trans ?_
      have h2 := (hD y hy z hz).2
      have h3 : (n ^ 2 / 4) ^ 2 ≤ (ReflectionKernel.normSq fun i => (minimalSiteDiff y z i : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
      calc _ ≤ 18 / (n ^ 2 / 4) ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
        _ = b := by rw [hb]; field_simp; norm_num)
    (fun y hy => weightedSums_le_of_subset _ _ (hf.weighted_sum_le y hy))
    (fun z hz => weightedSums_le_of_subset _ _ (hf'.weighted_sum_le z hz))
    (fun y hy A hA B hB => by
      have h1 := abs_planeSums_ball_sub_univ_le (n := n) hR8 (by linarith) (hf.supDist_le y hy) (κ y)
        (hf.weighted_sum_le y hy) A B
      have h2 := hf.plane_sums y hy A hA B hB
      have h3 := abs_sub_le
        (∑ p ∈ (plaquettesIn (supBall o (2 * (R : ℝ)))).filter (fun p : TorusPlaquette N => p.2 = A),
          ∑ p' ∈ (plaquettesIn (supBall o (2 * (R : ℝ)))).filter (fun p' : TorusPlaquette N => p'.2 = B),
            κ y p p')
        (∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette N => p.2 = A),
          ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette N => p'.2 = B), κ y p p')
        (if A = B then α y else 0)
      rw [he₁]
      linarith)
    (fun y hy A hA B hB => by
      have h1 := abs_planeSums_ball_sub_univ_le (n := n) hR8 (by linarith) (hf'.supDist_le y hy) (κ' y)
        (hf'.weighted_sum_le y hy) A B
      have h2 := hf'.plane_sums y hy A hA B hB
      have h3 := abs_sub_le
        (∑ p ∈ (plaquettesIn (supBall o (2 * (R : ℝ)))).filter (fun p : TorusPlaquette N => p.2 = A),
          ∑ p' ∈ (plaquettesIn (supBall o (2 * (R : ℝ)))).filter (fun p' : TorusPlaquette N => p'.2 = B),
            κ' y p p')
        (∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette N => p.2 = A),
          ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette N => p'.2 = B), κ' y p p')
        (if A = B then β y else 0)
      rw [he₁]
      linarith)
    (fun y hy => abs_diagonal_le hf y hy) (fun z hz => abs_diagonal_le hf' z hz)
  have eY : ∀ p p', ∑ y, κ y p p' = ∑ y ∈ Y, κ y p p' := fun p p' =>
    (Finset.sum_subset (Finset.subset_univ Y) fun y _ hy => hf.kernel_eq_zero y hy p p').symm
  have eZ : ∀ p p', ∑ z, κ' z p p' = ∑ z ∈ Z, κ' z p p' := fun p p' =>
    (Finset.sum_subset (Finset.subset_univ Z) fun y _ hy => hf'.kernel_eq_zero y hy p p').symm
  simp only [eY, eZ]
  have eS : 6 / Real.pi ^ 4 * ∑ y, ∑ z, α y * β z *
        (ReflectionKernel.normSq (fun i => (minimalSiteDiff y z i : ℝ)) ^ 4)⁻¹ =
      ∑ y ∈ Y, ∑ z ∈ Z, α y * β z * ∑ A ∈ ReflectionKernel.orientedPlanes, ∑ B ∈ ReflectionKernel.orientedPlanes,
        ReflectionKernel.kernel (fun i => (minimalSiteDiff y z i : ℝ)) A.1 A.2 B.1 B.2 *
          ReflectionKernel.kernel (fun i => (minimalSiteDiff y z i : ℝ)) B.1 B.2 A.1 A.2 := by
    rw [← Finset.sum_subset (Finset.subset_univ Y) fun y _ hy => by
      simp [hf.diag_eq_zero y hy], Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← Finset.sum_subset (Finset.subset_univ Z) fun z _ hz => by
      simp [hf'.diag_eq_zero z hz], Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [hRf.2.2 _ (hsq y hy z hz)]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hs : ReflectionKernel.normSq (fun i => (minimalSiteDiff y z i : ℝ)) ≠ 0 := by
      have h2 := (hD y hy z hz).2
      have h3 : 0 < n ^ 2 / 4 := by positivity
      linarith
    field_simp
  rw [eS]
  refine hmain.trans ?_
  have hcard : (ReflectionKernel.orientedPlanes.card : ℝ) = 6 := by
    have : ReflectionKernel.orientedPlanes.card = 6 := by decide
    rw [this]
    norm_num
  rw [hcard]
  have hY := hf.card_le
  have hZ := hf'.card_le
  have hYZ : (Y.card : ℝ) * (Z.card : ℝ) ≤ (15 * n) ^ 8 := by
    calc _ ≤ (15 * n) ^ 4 * (15 * n) ^ 4 := mul_le_mul hY hZ (by positivity) (by positivity)
      _ = _ := by ring
  have hrest : 0 ≤ e * (2 * b + e) * M ^ 2 + 6 ^ 4 * (e₁ * (2 * g + e₁) * b ^ 2) := by positivity
  refine (mul_le_mul_of_nonneg_right hYZ hrest).trans (le_of_eq ?_)
  rfl
end YangMills.Construction.TraceBounds
end
