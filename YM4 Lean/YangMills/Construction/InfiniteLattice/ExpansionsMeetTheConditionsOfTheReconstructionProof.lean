import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace MirrorExpansionsProof
open MirrorExpansions NormalHyperplane
theorem euclidDot_smul_right (r : ℝ) (x y : Point) : euclidDot x (r • y) = r * euclidDot x y := by
  simp only [euclidDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem euclidDot_sub_left (x y z : Point) : euclidDot (x - y) z = euclidDot x z - euclidDot y z := by
  simp [euclidDot, sub_mul, Finset.sum_sub_distrib]
theorem euclidDot_basisVector_left (μ : Direction) (x : Point) :
    euclidDot (basisVector μ) x = x μ := by
  simp [euclidDot, basisVector, Pi.single_apply]
theorem basisVector_self (μ : Direction) : basisVector μ μ = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_self <;> assumption
theorem basisVector_ne {μ ν : Direction} (h : μ ≠ ν) : basisVector μ ν = 0 := by
  simp [basisVector, h.symm]
theorem euclidNorm_sq (n : Point) : euclidNorm n ^ 2 = euclidDot n n := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.euclidNorm_sq_eq_selfDot <;> assumption
theorem euclidDot_add_basis_left (μ κ : Direction) (x : Point) :
    euclidDot (basisVector μ + basisVector κ) x = x μ + x κ := by apply _root_.YangMills.Construction.LatticeConventions.LinkConeProof.euclidDot_diagonal <;> assumption
theorem euclidDot_sub_basis_left (μ κ : Direction) (x : Point) :
    euclidDot (basisVector μ - basisVector κ) x = x μ - x κ := by
  rw [euclidDot_sub_left, euclidDot_basisVector_left, euclidDot_basisVector_left]
theorem euclidDot_basisVector_self (μ : Direction) :
    euclidDot (basisVector μ) (basisVector μ) = 1 := by
  rw [euclidDot_basisVector_left, basisVector_self]
theorem euclidDot_add_basis_self {μ κ : Direction} (hne : μ ≠ κ) :
    euclidDot (basisVector μ + basisVector κ) (basisVector μ + basisVector κ) = 2 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.euclidDot_self_basis_add <;> assumption
theorem euclidDot_sub_basis_self {μ κ : Direction} (hne : μ ≠ κ) :
    euclidDot (basisVector μ - basisVector κ) (basisVector μ - basisVector κ) = 2 := by
  rw [euclidDot_sub_basis_left]
  simp only [Pi.sub_apply, basisVector_self, basisVector_ne hne, basisVector_ne hne.symm]
  norm_num
theorem not_isFaceDiagonalNormal_basisVector (μ : Direction) :
    ¬IsFaceDiagonalNormal (basisVector μ) := by apply _root_.YangMills.Construction.LatticeConventions.basisVector_not_isFaceDiagonalNormal <;> assumption
theorem not_isAxialNormal_add_basis {μ κ : Direction} (hne : μ ≠ κ) :
    ¬IsAxialNormal (basisVector μ + basisVector κ) := by
  rintro ⟨ν, h⟩
  have h1 := euclidDot_add_basis_self hne
  rw [h, euclidDot_basisVector_self] at h1
  norm_num at h1
theorem smul_basisVector_mem (a : ℝ) (μ : Direction) :
    a • basisVector μ ∈ InfiniteLattice.latticeSubgroup a := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.smul_basisVector_mem <;> assumption
theorem axial_isLatticeMirror (a : ℝ) (μ : Direction) (c : ℝ) (q : ℤ)
    (hc : c = (q : ℝ) * (a / 2)) : (axial μ c).IsLatticeMirror a :=
  ⟨fun _ => ⟨q, hc⟩, fun h => absurd h (not_isFaceDiagonalNormal_basisVector μ)⟩
theorem diagonal_isLatticeMirror (a : ℝ) {μ κ : Direction} (hne : μ ≠ κ) (c : ℝ)
    (hc : ∃ q : ℤ, c = (q : ℝ) * a) : (diagonal μ κ hne c).IsLatticeMirror a :=
  ⟨fun h => absurd h (not_isAxialNormal_add_basis hne), fun _ => hc⟩
theorem eq_midPlane (Q Q' : NormalHyperplane) (h : Point) (hn : Q'.normal = Q.normal)
    (hp : Q'.level = Q.level + 1 / 2 * euclidDot Q.normal h) : Q' = Q.midPlane h := by
  obtain ⟨n', c', _⟩ := Q'
  obtain ⟨n, c, _⟩ := Q
  dsimp only at hn hp
  subst hn
  subst hp
  rfl
theorem isOutwardNormalStep_smul_normal (Q : NormalHyperplane) {a : ℝ} (ha : 0 < a)
    (hs : a • Q.normal ∈ InfiniteLattice.latticeSubgroup a) (hnn : 0 < euclidDot Q.normal Q.normal) :
    Q.IsOutwardNormalStep a (a • Q.normal) := by
  refine ⟨hs, ?_, ?_⟩
  · show a • Q.normal -
        (2 * (euclidNorm Q.normal ^ 2)⁻¹ * euclidDot Q.normal (a • Q.normal)) • Q.normal =
      -(a • Q.normal)
    have h2 : 2 * (euclidNorm Q.normal ^ 2)⁻¹ * euclidDot Q.normal (a • Q.normal) = a + a := by
      rw [euclidNorm_sq, euclidDot_smul_right]
      field_simp
      ring
    rw [h2, add_smul]
    abel
  · rw [euclidDot_smul_right]
    exact mul_pos ha hnn
theorem axial_isOutwardNormalStep {a : ℝ} (ha : 0 < a) (μ : Direction) (c : ℝ) :
    (axial μ c).IsOutwardNormalStep a (a • basisVector μ) :=
  isOutwardNormalStep_smul_normal (axial μ c) ha (smul_basisVector_mem a μ) (by
    show 0 < euclidDot (basisVector μ) (basisVector μ)
    rw [euclidDot_basisVector_self]
    norm_num)
theorem smul_sub_basis_mem (a : ℝ) (μ κ : Direction) :
    a • (basisVector μ - basisVector κ) ∈ InfiniteLattice.latticeSubgroup a := by
  rw [smul_sub]
  exact sub_mem (smul_basisVector_mem a μ) (smul_basisVector_mem a κ)
theorem diagonal_isOutwardNormalStep {a : ℝ} (ha : 0 < a) {μ κ : Direction} (hne : μ ≠ κ)
    (c : ℝ) :
    (diagonal μ κ hne c).IsOutwardNormalStep a (a • (basisVector μ + basisVector κ)) := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.smul_isOutwardNormalStep <;> assumption
theorem euclidDot_axial_step (a : ℝ) (μ : Direction) :
    euclidDot (basisVector μ) (a • basisVector μ) = a := by
  rw [euclidDot_smul_right, euclidDot_basisVector_self, mul_one]
theorem euclidDot_diagonal_step (a : ℝ) {μ κ : Direction} (hne : μ ≠ κ) :
    euclidDot (basisVector μ + basisVector κ) (a • (basisVector μ + basisVector κ)) = 2 * a := by
  rw [euclidDot_smul_right, euclidDot_add_basis_self hne, mul_comm]
theorem axial_eq_midPlane (a : ℝ) (μ : Direction) (c c' : ℝ) (hc : c' = c + a / 2) :
    axial μ c' = (axial μ c).midPlane (a • basisVector μ) :=
  eq_midPlane _ _ _ rfl (by
    show c' = c + 1 / 2 * euclidDot (basisVector μ) (a • basisVector μ)
    rw [euclidDot_axial_step, hc]
    ring)
theorem diagonal_eq_midPlane (a : ℝ) {μ κ : Direction} (hne : μ ≠ κ) (c : ℝ) :
    diagonal μ κ hne (c + a) =
      (diagonal μ κ hne c).midPlane (a • (basisVector μ + basisVector κ)) :=
  eq_midPlane _ _ _ rfl (by
    show c + a = c + 1 / 2 * euclidDot (basisVector μ + basisVector κ)
      (a • (basisVector μ + basisVector κ))
    rw [euclidDot_diagonal_step a hne]
    ring)
theorem midPlane_isLatticeMirror (a : ℝ) (Q : NormalHyperplane) (h : Point)
    (hQ : Q.IsLatticeMirror a) (hs : Q.IsOutwardNormalStep a h) :
    (Q.midPlane h).IsLatticeMirror a := by
  have hmem : ∃ m : Fin 4 → ℤ, ∀ μ, h μ = (m μ : ℝ) * a := hs.1
  obtain ⟨m, hm⟩ := hmem
  have hcoord : ∀ ν, h ν -
      (2 * (euclidNorm Q.normal ^ 2)⁻¹ * euclidDot Q.normal h) * Q.normal ν = -h ν :=
    fun ν => congrFun hs.2.1 ν
  constructor
  · intro (hc : IsAxialNormal Q.normal)
    obtain ⟨q, hq⟩ := hQ.1 hc
    obtain ⟨μ, hμ⟩ := hc
    refine ⟨q + m μ, ?_⟩
    show Q.level + 1 / 2 * euclidDot Q.normal h = _
    rw [hμ, euclidDot_basisVector_left, hq, hm μ]
    push_cast
    ring
  · intro (hd : IsFaceDiagonalNormal Q.normal)
    obtain ⟨q, hq⟩ := hQ.2 hd
    obtain ⟨μ, κ, hne, hn | hn⟩ := hd
    · have h2 := hcoord μ
      rw [euclidNorm_sq, hn, euclidDot_add_basis_self hne, euclidDot_add_basis_left] at h2
      simp only [Pi.add_apply, basisVector_self, basisVector_ne hne.symm] at h2
      have h3 : h κ = h μ := by linarith
      refine ⟨q + m μ, ?_⟩
      show Q.level + 1 / 2 * euclidDot Q.normal h = _
      rw [hn, euclidDot_add_basis_left, hq, h3, hm μ]
      push_cast
      ring
    · have h2 := hcoord μ
      rw [euclidNorm_sq, hn, euclidDot_sub_basis_self hne, euclidDot_sub_basis_left] at h2
      simp only [Pi.sub_apply, basisVector_self, basisVector_ne hne.symm] at h2
      have h3 : h κ = -h μ := by linarith
      refine ⟨q + m μ, ?_⟩
      show Q.level + 1 / 2 * euclidDot Q.normal h = _
      rw [hn, euclidDot_sub_basis_left, hq, h3, hm μ]
      push_cast
      ring
theorem isPictureExpansion_of (a : Spacing) {ι : Type} [Fintype ι] (row : ReflectionPictureData ι)
    (n : Point) (l : ℝ) (k : ℕ) (hN : row.plane.normal = n) (hN' : row.midPlane.normal = n)
    (hL : row.plane.IsLatticeMirror (a : ℝ)) (hL' : row.midPlane.IsLatticeMirror (a : ℝ))
    (hS : row.plane.IsOutwardNormalStep (a : ℝ) row.normalStep)
    (hD : euclidDot n row.normalStep = l)
    (hH : row.midPlane = row.plane.midPlane row.normalStep)
    (hW : ∀ i, row.tangentStep i ∈ InfiniteLattice.latticeSubgroup (a : ℝ))
    (hO : ∀ i, euclidDot n (row.tangentStep i) = 0) (hk : Fintype.card ι = k) (hk1 : 1 ≤ k) :
    IsPictureExpansion a row n l k where
  plane_normal := hN
  midPlane_normal := hN'
  plane_isLatticeMirror := hL
  midPlane_isLatticeMirror := hL'
  normalStep_outward := hS
  euclidDot_normalStep := hD
  midPlane_isMid := ⟨hL, hS, hH⟩
  tangentStep_mem := hW
  euclidDot_tangentStep := hO
  hyps := ⟨⟨hL, hS, hH⟩, hL', hk ▸ hk1, hW, fun i => by rw [hN]; exact hO i⟩
  card_eq := hk
theorem card_ne_direction (μ : Direction) : Fintype.card {l : Direction // l ≠ μ} = 3 := by
  revert μ
  decide
theorem euclidDot_axial_tangent (a : ℝ) (μ : Direction) (l : {l : Direction // l ≠ μ}) :
    euclidDot (basisVector μ) (a • basisVector l.1) = 0 := by
  rw [euclidDot_smul_right, euclidDot_basisVector_left, basisVector_ne l.2, mul_zero]
theorem pictureExpansionsHold : PictureExpansionsHold := by
  intro a μ κ hne c hc
  have ha : 0 < (a : ℝ) := a.2
  refine ⟨?_, ?_, ?_⟩
  · exact isPictureExpansion_of a (linkPicture a μ) (basisVector μ) (a : ℝ) 3 rfl rfl
      (axial_isLatticeMirror _ μ _ (-1) (by push_cast; ring))
      (axial_isLatticeMirror _ μ _ 0 (by push_cast; ring))
      (axial_isOutwardNormalStep ha μ _) (euclidDot_axial_step _ μ)
      (axial_eq_midPlane _ μ _ _ (by ring))
      (fun l => smul_basisVector_mem _ l.1) (fun l => euclidDot_axial_tangent _ μ l)
      (card_ne_direction μ) (by norm_num)
  · exact isPictureExpansion_of a (sitePicture a μ) (basisVector μ) (a : ℝ) 3 rfl rfl
      (axial_isLatticeMirror _ μ _ 0 (by push_cast; ring))
      (axial_isLatticeMirror _ μ _ 1 (by push_cast; ring))
      (axial_isOutwardNormalStep ha μ _) (euclidDot_axial_step _ μ)
      (axial_eq_midPlane _ μ _ _ (by ring))
      (fun l => smul_basisVector_mem _ l.1) (fun l => euclidDot_axial_tangent _ μ l)
      (card_ne_direction μ) (by norm_num)
  · obtain ⟨q, hq⟩ := id hc
    exact isPictureExpansion_of a (diagonalPicture a μ κ hne c hc)
      (basisVector μ + basisVector κ) (2 * (a : ℝ)) 1 rfl rfl
      (diagonal_isLatticeMirror _ hne _ hc)
      (diagonal_isLatticeMirror _ hne _ ⟨q + 1, by rw [hq]; push_cast; ring⟩)
      (diagonal_isOutwardNormalStep ha hne _) (euclidDot_diagonal_step _ hne)
      (diagonal_eq_midPlane _ hne _)
      (fun _ => smul_sub_basis_mem _ μ κ)
      (fun _ => by
        show euclidDot (basisVector μ + basisVector κ)
          ((a : ℝ) • (basisVector μ - basisVector κ)) = 0
        rw [euclidDot_smul_right, euclidDot_add_basis_left]
        simp only [Pi.sub_apply, basisVector_self, basisVector_ne hne, basisVector_ne hne.symm]
        ring)
      (by simp) le_rfl
theorem no_multiple_strictly_between {a : ℝ} (ha : 0 < a) (q r : ℤ)
    (h1 : (q : ℝ) * a < (r : ℝ) * a) (h2 : (r : ℝ) * a < (q : ℝ) * a + a) : False := by
  have h3 : (q : ℝ) < r := lt_of_mul_lt_mul_right h1 ha.le
  have h4 : (r : ℝ) < q + 1 := by
    have h5 : (r : ℝ) * a < ((q : ℝ) + 1) * a := by linarith
    exact lt_of_mul_lt_mul_right h5 ha.le
  have h6 : q < r := by exact_mod_cast h3
  have h7 : r < q + 1 := by exact_mod_cast h4
  omega
theorem midPlanesOfAxialAndDiagonal : MidPlanesOfAxialAndDiagonal := by
  intro a μ κ hne
  have ha : 0 < (a : ℝ) := a.2
  refine ⟨?_, ?_, ?_⟩
  · intro c' hlink
    obtain ⟨q, hq⟩ := hlink.2.2
    have hq' : (axial μ c').level = c' := rfl
    rw [hq'] at hq
    refine ⟨⟨hlink.1, axial_isOutwardNormalStep ha μ _,
      axial_eq_midPlane _ μ _ _ rfl⟩, ?_, ⟨μ, rfl⟩, q + 1, ?_⟩
    · refine axial_isLatticeMirror _ μ _ (2 * q + 2) ?_
      rw [hq]
      push_cast
      ring
    · show c' + (a : ℝ) / 2 = _
      rw [hq]
      push_cast
      ring
  · intro c' hsite
    obtain ⟨q, hq⟩ := hsite.2.2
    have hq' : (axial μ c').level = c' := rfl
    rw [hq'] at hq
    refine ⟨⟨hsite.1, axial_isOutwardNormalStep ha μ _,
      axial_eq_midPlane _ μ _ _ rfl⟩, ?_, ⟨μ, rfl⟩, q, ?_⟩
    · refine axial_isLatticeMirror _ μ _ (2 * q + 1) ?_
      rw [hq]
      push_cast
      ring
    · show c' + (a : ℝ) / 2 = _
      rw [hq]
  · intro c hc
    obtain ⟨q, hq⟩ := id hc
    have hL : (diagonal μ κ hne c).IsLatticeMirror (a : ℝ) :=
      diagonal_isLatticeMirror _ hne _ hc
    have hL' : (diagonal μ κ hne (c + (a : ℝ))).IsLatticeMirror (a : ℝ) :=
      diagonal_isLatticeMirror _ hne _ ⟨q + 1, by rw [hq]; push_cast; ring⟩
    refine ⟨⟨hL, diagonal_isOutwardNormalStep ha hne _, diagonal_eq_midPlane _ hne _⟩, hL',
      ⟨rfl, hL'⟩, ?_, ?_⟩
    · show c < c + (a : ℝ)
      linarith
    · rintro R ⟨hRn, hRL⟩ ⟨h1, h2⟩
      obtain ⟨r, hr⟩ := hRL.2 (by rw [hRn]; exact ⟨μ, κ, hne, Or.inl rfl⟩)
      have h1' : c < R.level := h1
      have h2' : R.level < c + (a : ℝ) := h2
      rw [hr, hq] at h1' h2'
      exact no_multiple_strictly_between ha q r h1' h2'
theorem statement_holds : Statement :=
  ⟨fun a Q h hQ hs => midPlane_isLatticeMirror (a : ℝ) Q h hQ hs, pictureExpansionsHold,
    midPlanesOfAxialAndDiagonal⟩
end MirrorExpansionsProof
end LatticeConventions
end YangMills.Construction
end
