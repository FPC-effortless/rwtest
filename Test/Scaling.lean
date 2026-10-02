import Mathlib

open Real

namespace PNDS.Scaling

variable {N K r : ℕ}

/-- Embed `Fin r` into `Fin m` when `r ≤ m`, via the Mathlib standard `Fin.castLEEmb`. -/
def finEmbed (r : ℕ) {m : ℕ} (h : r ≤ m) : Fin r ↪ Fin m :=
  Fin.castLEEmb h

/-- The relevant items, as a finset over `Fin m`: the first `r` indices. -/
def relevantFin (r : ℕ) {m : ℕ} (hrm : r ≤ m) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin r)).map (finEmbed r hrm)

theorem card_relevantFin {m : ℕ} (hrm : r ≤ m) : (relevantFin r hrm).card = r := by
  rw [relevantFin, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem recall_le {m : ℕ} (hrm : r ≤ m) (selected : Finset (Fin m)) :
    (selected ∩ relevantFin r hrm).card ≤ r := by
  have hsub : selected ∩ relevantFin r hrm ⊆ relevantFin r hrm :=
    Finset.inter_subset_right
  have hcard := Finset.card_le_card hsub
  rw [card_relevantFin hrm] at hcard
  exact hcard

theorem distractors_in_topK_eq_recall {m : ℕ} (hrm : r ≤ m)
    (selected : Finset (Fin m)) (hcard : selected.card = K) :
    (selected \ relevantFin r hrm).card = K - (selected ∩ relevantFin r hrm).card := by
  rw [← Finset.sdiff_inter_self_left]
  have hsub : selected ∩ relevantFin r hrm ⊆ selected := Finset.inter_subset_left
  rw [Finset.card_sdiff hsub, hcard]

theorem distractors_in_topK_eq {m : ℕ} (hrm : r ≤ m)
    (selected : Finset (Fin m)) (hcard : selected.card = K)
    (hrel : relevantFin r hrm ⊆ selected) :
    (selected \ relevantFin r hrm).card = K - r := by
  have hinter : selected ∩ relevantFin r hrm = relevantFin r hrm :=
    Finset.inter_eq_right.mpr hrel
  rw [distractors_in_topK_eq_recall hrm selected hcard, hinter, card_relevantFin hrm]

theorem distractors_in_topK_le_of_recall {m : ℕ} (hrm : r ≤ m)
    (selected : Finset (Fin m)) (hcard : selected.card = K)
    (hrec : r ≤ (selected ∩ relevantFin r hrm).card) :
    (selected \ relevantFin r hrm).card ≤ K - r := by
  rw [distractors_in_topK_eq_recall hrm selected hcard]
  have hρ := recall_le hrm selected
  have hkey : (selected ∩ relevantFin r hrm).card = r := Nat.le_antisymm hρ hrec
  rw [hkey]

theorem recall_one_iff {m : ℕ} (hrm : r ≤ m) (selected : Finset (Fin m)) :
    (selected ∩ relevantFin r hrm).card = r ↔ relevantFin r hrm ⊆ selected := by
  constructor
  · intro heq
    have hsub : selected ∩ relevantFin r hrm ⊆ relevantFin r hrm := Finset.inter_subset_right
    have hcard_eq : selected ∩ relevantFin r hrm = relevantFin r hrm := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [heq, card_relevantFin hrm]
    have hint : selected ∩ relevantFin r hrm ⊆ selected := Finset.inter_subset_left
    rw [hcard_eq] at hint
    exact hint
  · intro hsub
    have hinter : selected ∩ relevantFin r hrm = relevantFin r hrm :=
      Finset.inter_eq_right.mpr hsub
    rw [hinter, card_relevantFin hrm]

theorem distractors_in_topK_ge_of_missed {m : ℕ} (hrm : r ≤ m)
    (selected : Finset (Fin m)) (hcard : selected.card = K) (hKr : r ≤ K)
    (hmiss : (selected ∩ relevantFin r hrm).card < r) :
    K - r < (selected \ relevantFin r hrm).card := by
  rw [distractors_in_topK_eq_recall hrm selected hcard]
  have hρ := recall_le hrm selected
  omega

theorem distractors_in_topK_eq_iff_recall_one {m : ℕ} (hrm : r ≤ m)
    (selected : Finset (Fin m)) (hcard : selected.card = K) (hKr : r ≤ K) :
    (selected \ relevantFin r hrm).card = K - r ↔ relevantFin r hrm ⊆ selected := by
  rw [distractors_in_topK_eq_recall hrm selected hcard]
  constructor
  · intro heq
    have hρ := recall_le hrm selected
    have hρ_eq : (selected ∩ relevantFin r hrm).card = r := by
      by_contra hne
      have hlt : (selected ∩ relevantFin r hrm).card < r := lt_of_le_of_ne hρ hne
      have : K - (selected ∩ relevantFin r hrm).card > K - r := by omega
      linarith
    exact (recall_one_iff hrm selected).1 hρ_eq
  · intro hrel
    have hρ_eq : (selected ∩ relevantFin r hrm).card = r :=
      (recall_one_iff hrm selected).2 hrel
    rw [hρ_eq]

end PNDS.Scaling
