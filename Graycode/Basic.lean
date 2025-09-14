import Mathlib.Tactic.FinCases
import Mathlib.Data.ZMod.Defs
import Graycode.Defs
import Graycode.NatLemmas

lemma next_to_comm (x y : ℕ) : next_to x y ↔ next_to y x := by
  unfold next_to
  simp_rw [eq_comm, Bool.xor_comm]

@[simp, grind =]
lemma next_to_xor_right (x y z : ℕ) :
    next_to (x ^^^ z) (y ^^^ z) ↔ next_to x y := by
  simp only [next_to_xor_two_pow]
  rw [show (x ^^^ z) ^^^ (y ^^^ z) = x ^^^ y by grind]

@[simp, grind =]
lemma next_to_xor_left (x y z : ℕ) : next_to (z ^^^ x) (z ^^^ y) ↔ next_to x y := by
  rw [Nat.xor_comm z x, Nat.xor_comm z y]
  exact next_to_xor_right x y z

lemma reverse_unit_step {α : Type*} [AddCommGroup α] [One α] (x : α → ℕ) (l : α) :
    IsUnitStepSeq x → IsUnitStepSeq (fun i => x (l - i)) := by
  unfold IsUnitStepSeq
  intro h i
  simp only
  rw [next_to_comm]
  convert h (l - (i + 1)) using 2
  rw [<-sub_sub l i 1]
  simp

lemma list_is_stable_once (n : ℕ) (i : ℕ) (h : i < 2 ^ n) :
    (list_gray_code n)[i]'(by simp [h]) = (list_gray_code (n+1))[i]'(by grind) := by
  have := list_gray_code.eq_2 n
  simp only [Nat.succ_eq_add_one, List.map_reverse] at this
  simp_rw [this]
  rw [List.getElem_append_left']

lemma list_is_stable' (n : ℕ) (i : ℕ) (h : i < 2 ^ n) (m : ℕ) (h' : n ≤ m) :
    (list_gray_code n)[i]'(by simp [h]) = (list_gray_code m)[i]'(by
      rw [list_gray_code_length]
      suffices 2^n ≤ 2^m by linarith
      apply Nat.pow_le_pow_right (by simp) (by assumption)
    ) := by
  induction m, h' using Nat.le_induction with
  | base => rfl
  | succ k kh h' =>
    rw [h']
    apply list_is_stable_once
    suffices 2^n ≤ 2^k by linarith
    apply Nat.pow_le_pow_right (by simp) (by assumption)

lemma list_is_stable (n : ℕ) (i : ℕ) {h : i < (list_gray_code n).length} (m : ℕ) (h' : i < 2 ^ m) :
    (list_gray_code n)[i]'h = (list_gray_code m)[i]'(by
      rw [list_gray_code_length]
      assumption
    ) := by
  wlog n_le_m : n ≤ m generalizing n m
  · have m_le_n : m ≤ n := Nat.le_of_not_ge n_le_m
    exact Eq.symm (list_is_stable' m i h' n m_le_n)
  rw [list_is_stable']
  · simp_all
  exact n_le_m

lemma list_is_recursive_aux (i : ℕ) : list_gray_code_i i = recursive_gray_code i := by
  induction i using binaryComplementRec with
  | zero => simp [list_gray_code_i, recursive_gray_code, list_gray_code, binaryComplementRec]
  | two_pow i ih complement =>
    rw [list_gray_code_i] at *
    simp_rw [list_gray_code]
    rw [List.getElem_append_right (by simp [Nat.log2_self_le (Nat.ne_zero_of_lt ih)])]
    rw [List.getElem_map, List.getElem_reverse]
    simp only [list_gray_code_length]
    have : (2^i.log2 - 1 - (i - 2^i.log2)) = (2^(i.log2+1) - 1) ^^^ i := by
      -- I hope I don't need thisone again
      have := Nat.log2_self_le (Nat.ne_zero_of_lt ih)
      rw [show 2^i.log2 - 1 - (i - 2^i.log2) = 2^(i.log2 + 1) - 1 - i by omega]
      exact (Nat.two_pow_sub_one_xor_eq Nat.lt_log2_self).symm
    simp_rw [this]
    have smaller_complement:= complement_is_smaller i (i.log2)
      ((Nat.log2_eq i i.log2 (Nat.ne_zero_of_lt ih)).mpr rfl)
    rw [list_is_stable (n := ((2 ^ (i.log2 + 1) - 1 ^^^ i).log2 + 1))
      (i := 2 ^ (i.log2 + 1) - 1 ^^^ i)
      (m := i.log2) smaller_complement] at complement
    rw [complement]
    rw [<-recursive_gray_code_eq]
    exact Nat.ne_zero_of_lt ih

lemma list_is_recursive (i n : ℕ) {h : i < (list_gray_code n).length} :
    (list_gray_code n)[i] = recursive_gray_code i := by
  rw [list_is_stable (n := n) (i := i) (m := i.log2 + 1)]
  · exact list_is_recursive_aux i
  exact Nat.lt_log2_self


/-
    Each list $L_n$ is a unit step sequence on $\mathbb{Z} / 2^n \mathbb{Z}$.

Proof
    It is obviously true for $n = 0$.

    By the stability property, $L_{n+1}$ is a unit step sequence for $i, i+1 < 2^n$.

    Since the reverse of a unit step sequence is a unit step sequence, then for
    $2^n \le i, i+1 < 2^{n+1}$, $L_{n+1}$ is a unit step sequence there as well.

    When $i = 2^n - 1$, then $L_{n+1}(2^n - 1) = L_{n}(2^n - 1)$ and
    $L_{n+1}(2^n) = 2^n \oplus L_{n}(2^n - 1)$,
    so thus $L_{n+1}(2^n - 1) \oplus L_{n+1}(2^n) = 2^n$ and they are next to each other.

    When $i = 2^{n+1} - 1$, then $L_{n+1}(2^{n+1} - 1) = 2^n \oplus L_{n}(0) = L_{n+1}(0)$
    so thus they are next to each other.
-/

@[simp, grind =]
lemma gray_code_at_two_pow_minus_one (m : ℕ) :
    recursive_gray_code (2 ^ (m+1) - 1) = 2^m := by
  rw [recursive_gray_code_eq]
  · have : (2^(m+1) - 1).log2 = m := by
      rw [Nat.log2_eq_log_two]
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · grind
      apply Nat.sub_lt (Nat.two_pow_pos (m + 1)) (by norm_num)
    rw [this]
    simp [recursive_gray_code_zero]
  simp [ne_of_gt]

lemma gray_code_at_two_pow_minus_one' (m : ℕ) :
    recursive_gray_code (2 ^ m - 1) = 2^m / 2 := by
  rcases Nat.eq_zero_or_eq_sub_one_add_one (n := m) with h | h
  · rw [h]; simp
  rw [h]; grind

lemma gray_code_at_two_pow (m : ℕ) :
    recursive_gray_code (2 ^ m) = 2^m ^^^ 2^m / 2 := by
  rw [recursive_gray_code_eq (nezero := by positivity)]
  simp only [Nat.log2_two_pow, complement_xor_two_pow]
  rw [gray_code_at_two_pow_minus_one']

lemma gray_code_at_two_pow' (m : ℕ) :
    recursive_gray_code (2 ^ (m+1)) = 2^(m+1) ^^^ 2^m := by
  rw [gray_code_at_two_pow]
  grind

-- Rewriting through Fin is touchy
lemma list_gray_code_unit_step (n : ℕ) :
    IsUnitStepSeq (fun (i : Fin (2 ^ (n+1))) => (list_gray_code (n+1))[i]) := by
  induction n
  · intro i
    simp [list_gray_code]
    fin_cases i <;> { simp [next_to_xor_two_pow, Nat.isPowerOfTwo]; use 0; simp }
  next n nh =>
    set m := n + 1 with m_def
    rintro ⟨i, ih⟩
    dsimp
    have four_cases : i+1 < 2^m ∨ i = 2^m - 1 ∨ 2^m ≤ i ∧ i + 1 < 2^(m+1) ∨ i = 2^(m+1) - 1 := by
      grind -- also omega would work
    rcases four_cases with h' | h' | ⟨h1, h2⟩ | h'
    · have fin_val1 : Fin.val (⟨i, ih⟩ + 1) = i + 1 := by
        rw [Fin.val_add_one_of_lt']
        simp; grind
      simp_rw [fin_val1]
      --have : i + 1 < 2 ^ (m+1) := by grind
      rw [list_is_stable (n := (m+1)) (m := m) (i := (i + 1))
        (h := by simp; grind) (h' := by assumption)]
      rw [list_is_stable (n := (m+1)) (m := m) (i := i) (h := by simpa) (h' := by linarith)]
      have : i < 2 ^ m := by linarith
      convert nh ⟨i, this⟩
      have fin_val2 : Fin.val (⟨i, this⟩ + 1) = i + 1 := by
        rw [Fin.val_add_one_of_lt']
        simpa
      simp only [Fin.getElem_fin]
      simp_rw [fin_val2]
    · have fin_val1 : Fin.val (⟨i, ih⟩ + 1) = i + 1 := by
        rw [Fin.val_add_one_of_lt']
        simp; grind
      simp_rw [fin_val1]
      simp_rw [h']
      rw [list_is_recursive, gray_code_at_two_pow_minus_one, list_is_recursive]
      rw [show 2^m - 1 + 1 = 2^m by grind, gray_code_at_two_pow', next_to_xor_two_pow]
      use (n+1)
      grind
    · have fin_val1 : Fin.val (⟨i, ih⟩ + 1) = i + 1 := by
        rw [Fin.val_add_one_of_lt']
        simp; grind
      simp_rw [fin_val1]
      have : ∀i, (ih : 2^m ≤ i ∧ i < 2^(m+1)) → (list_gray_code (m + 1))[i]'(by simp; exact ih.2)
        = 2^m ^^^ (list_gray_code m)[2^(m+1) - 1 - i]'(by grind) := by
        intro i ih
        simp_rw [list_gray_code]
        rw [List.getElem_append_right (by simp_all)]
        rw [List.getElem_map, List.getElem_reverse]
        simp_rw [list_gray_code_length]
        congr 2
        grind
      rw [this _ (by grind), this _ (by grind)]
      rw [next_to_xor_left]
      simp_rw [show 2^(m+1) - 1 - (i + 1) = 2^(m+1) - 1 - i - 1 from rfl]
      rw [next_to_comm]
      have : (2^(m+1) - 1 - i - 1) < 2^m := by grind
      convert nh ⟨2^(m+1) - 1 - i - 1, this⟩
      dsimp
      congr 1
      have fin_val2 : Fin.val (⟨2^(m+1) - 1 - i - 1, this⟩ + 1) = 2^(m+1) - 1 - i - 1 + 1 := by
        rw [Fin.val_add_one_of_lt']
        grind
      simp_rw [fin_val2]
      grind
    have fin_val1 : Fin.val (⟨i, ih⟩ + 1) = 0 := by
      simp_rw [h']
      rw [Fin.val_add_eq_ite]
      rw [if_pos]
      · simp; grind
      simp; grind
    simp_rw [fin_val1, h']
    simp [list_is_recursive, next_to_xor_two_pow]
    use m

theorem recursive_gray_code_unit_step : IsUnitStepSeq recursive_gray_code := by
  have ih :∀i, i < 2^(i+1) := by
    intro i
    apply lt_trans (b := 2^i)
    · exact Nat.lt_two_pow_self
    apply Nat.pow_lt_pow_succ (by norm_num)
  intro i
  rw [<-list_is_recursive (n := i + 1)]
  · rw [<-list_is_recursive (n := i)] -- not sure why this is incrementing i...
    · have := list_gray_code_unit_step (n := i) ⟨i, ih i⟩
      dsimp at this
      have fin_val1 : Fin.val (⟨i, ih i⟩ + 1) = i + 1 := by
        rw [Fin.val_add_one_of_lt']
        exact Nat.lt_two_pow_self
      simp_rw [fin_val1] at this
      convert this -- exact and apply didn't work???
    simp [Nat.lt_two_pow_self]

theorem direct_is_xor_homomorphism (i j : ℕ) :
    direct_gray_code (i ^^^ j) = direct_gray_code i ^^^ direct_gray_code j := by
  unfold direct_gray_code
  grind

theorem direct_is_recursive (i : ℕ) :
    direct_gray_code i = recursive_gray_code i := by
  induction i using binaryComplementRec with
  | zero => simp
  | two_pow i ih complement =>
    rw [recursive_gray_code_eq (by grind)]
    rw [<-complement]
    unfold direct_gray_code
    have : (2 ^ (i.log2 + 1) - 1 ^^^ i ^^^ (2 ^ (i.log2 + 1) - 1 ^^^ i) >>> 1) =
      2^i.log2 ^^^ i ^^^ i >>> 1 := by
      rw [Nat.shiftRight_xor_distrib]
      rw [Nat.shiftRight_two_pow_sub_one]
      rw [Nat.xor_assoc, Nat.xor_assoc, <-Nat.xor_assoc i, Nat.xor_comm i, Nat.xor_assoc]
      rw [<-Nat.xor_assoc, Nat.xor_left_inj, Nat.xor_comm]
      exact Nat.two_pow_sub_one_xor_add_one i.log2
    rw [this, <-Nat.xor_assoc, <- Nat.xor_assoc]
    simp


lemma recursive_gray_code_lt_two_pow {i n : ℕ} (h : i < 2 ^ n) : recursive_gray_code i < 2^n := by
  induction i using binaryComplementRec with
  | zero => simp
  | two_pow i ih complement =>
    rw [recursive_gray_code_eq ih.ne']
    apply Nat.xor_lt_two_pow
    · have := Nat.log2_self_le ih.ne'
      linarith
    exact complement (by
      apply lt_trans ?_ h
      have := complement_is_smaller i i.log2 ((Nat.log2_eq i i.log2 ih.ne').mpr rfl)
      linarith [Nat.log2_self_le ih.ne']
    )

lemma direct_gray_code_lt_two_pow (i n : ℕ) (h : i < 2 ^ n) : direct_gray_code i < 2^n := by
  unfold direct_gray_code
  apply Nat.xor_lt_two_pow h
  exact lt_of_le_of_lt (Nat.shiftRight_le i 1) h

lemma le_recursive_gray_code {n : ℕ} (h : n ≠ 0) : 2^n.log2 ≤ recursive_gray_code n := by
  rw [recursive_gray_code_eq h]
  rw [Nat.xor_two_pow_of_lt]
  · simp
  exact recursive_gray_code_lt_two_pow
    (complement_is_smaller n n.log2 ((Nat.log2_eq n n.log2 h).mpr rfl))

lemma recursive_gray_code_pos {n : ℕ} (h : 0 < n) : 0 < recursive_gray_code n :=
  lt_of_lt_of_le (Nat.two_pow_pos n.log2) (le_recursive_gray_code h.ne')

lemma log2_recursive_gray_code (n : ℕ) : (recursive_gray_code n).log2 = n.log2 := by
  by_cases nezero : n = 0
  · simp [nezero]
  rw [<-Nat.log2_eq]
  · constructor
    · exact le_recursive_gray_code nezero
    exact recursive_gray_code_lt_two_pow Nat.lt_log2_self
  exact ne_of_gt (recursive_gray_code_pos (Nat.zero_lt_of_ne_zero nezero))

lemma recursive_inverse_is_left_inverse :
    Function.LeftInverse recursive_inverse recursive_gray_code := fun n ↦ by
  induction n using binaryComplementRec with
  | zero => simp
  | two_pow i ih complement =>
    rw [recursive_inverse_eq (ne_of_gt (recursive_gray_code_pos ih))]
    rw [log2_recursive_gray_code]
    rw [recursive_gray_code_eq ih.ne']
    rw [Nat.xor_comm (2^i.log2), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [complement, Nat.xor_eq_iff]

lemma recursive_inverse_lt_two_pow {i n : ℕ} (h : i < 2 ^ n) : recursive_inverse i < 2^n := by
  induction i using binaryBigEndianRec with
  | zero => simp
  | two_pow i ih lower =>
    rw [recursive_inverse_eq ih.ne']
    apply Nat.xor_lt_two_pow
    · apply Nat.sub_one_lt_of_le (by positivity)
      apply Nat.pow_le_pow_right (by norm_num)
      apply Nat.add_one_le_of_lt
      rw [Nat.log2_lt ih.ne']
      exact h
    exact lower (by
      apply lt_trans ?_ h
      rw [Nat.xor_two_pow_log2 ih.ne']
      simpa
    )

lemma le_recursive_inverse {n : ℕ} (h : n ≠ 0) : 2^n.log2 ≤ recursive_inverse n := by
  rw [recursive_inverse_eq h]
  rw [Nat.two_pow_add_one_sub_one_eq, Nat.xor_assoc]
  rw [Nat.xor_two_pow_of_lt]
  · simp
  apply Nat.xor_lt_two_pow (by simp)
  apply recursive_inverse_lt_two_pow
  rw [Nat.xor_two_pow_log2 h]
  have : n < 2^(n.log2 + 1) := Nat.lt_log2_self
  grind

lemma recursive_inverse_pos {n : ℕ} (h : 0 < n) : 0 < recursive_inverse n :=
  lt_of_lt_of_le (Nat.two_pow_pos n.log2) (le_recursive_inverse h.ne')

lemma log2_recursive_inverse (n : ℕ) : (recursive_inverse n).log2 = n.log2 := by
  by_cases nezero : n = 0
  · simp [nezero]
  rw [<-Nat.log2_eq]
  · constructor
    · exact le_recursive_inverse nezero
    exact recursive_inverse_lt_two_pow Nat.lt_log2_self
  exact ne_of_gt (recursive_inverse_pos (Nat.zero_lt_of_ne_zero nezero))

lemma recursive_inverse_is_right_inverse :
    Function.RightInverse recursive_inverse recursive_gray_code := fun n ↦ by
  induction n using binaryBigEndianRec with
  | zero => simp
  | two_pow i ih lower =>
    rw [recursive_gray_code_eq (ne_of_gt (recursive_inverse_pos ih))]
    rw [log2_recursive_inverse]
    rw [recursive_inverse_eq ih.ne']
    rw [<-Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [lower, Nat.xor_eq_iff, Nat.xor_comm]

def equiv_gray_code : ℕ ≃ ℕ where
  toFun := recursive_gray_code
  invFun := recursive_inverse
  left_inv := recursive_inverse_is_left_inverse
  right_inv := recursive_inverse_is_right_inverse

theorem recursive_is_gray_code : IsGrayCode recursive_gray_code :=
  ⟨recursive_gray_code_unit_step, equiv_gray_code.bijective⟩

lemma direct_inverse_two_pow_eq (n : ℕ) : direct_inverse (2 ^ n) = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp [direct_inverse]
  | succ n nh =>
    rw [direct_inverse, if_neg (by positivity)]
    rw [Nat.shiftRight_two_pow, nh, <-Nat.two_pow_add_one_sub_one_eq]

lemma direct_inverse_xor_homomorphism (x y : ℕ) :
    direct_inverse (x ^^^ y) = direct_inverse x ^^^ direct_inverse y := by
  if h : x = 0 ∨ y = 0 then
    rcases h with h | h
    <;> simp [h]
  else
    rw [direct_inverse]
    split_ifs
    · have : x = y := by simp_all
      simp [this]
    rcases not_or.1 h with ⟨xnonneg, ynonneg⟩
    rw [direct_inverse.eq_def x, if_neg xnonneg, direct_inverse.eq_def y, if_neg ynonneg]
    rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_right_inj, Nat.xor_comm (direct_inverse (x >>> 1))]
    rw [Nat.xor_assoc, Nat.xor_right_inj, Nat.xor_comm (direct_inverse (y >>> 1))]
    rw [Nat.shiftRight_xor_distrib]
    apply direct_inverse_xor_homomorphism

lemma direct_inverse_is_recursive_inverse (n : ℕ) : direct_inverse n = recursive_inverse n := by
  induction n using binaryBigEndianRec with
  | zero => simp
  | two_pow n nh lower =>
    rw [direct_inverse_xor_homomorphism, direct_inverse_two_pow_eq] at lower
    rw [recursive_inverse_eq nh.ne']
    rw [Nat.xor_comm, <-lower, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

lemma alternate_direct_gray_code_proof : IsUnitStepSeq direct_gray_code := by
  intro i
  rw [next_to_xor_two_pow]
  unfold direct_gray_code
  rw [Nat.xor_comm i, Nat.xor_assoc, <-Nat.xor_assoc i]
  have ⟨k, kh, h⟩ := Nat.exists_xor_add_one_eq_two_pow i
  set l := k - 1 with l_def
  rw [show k = l + 1 by grind] at h
  rw [h, <-Nat.xor_assoc, Nat.xor_comm (i >>> 1), Nat.xor_assoc, <-Nat.shiftRight_xor_distrib]
  rw [h, Nat.shiftRight_two_pow_sub_one, Nat.xor_comm, Nat.two_pow_sub_one_xor_add_one]
  use l
