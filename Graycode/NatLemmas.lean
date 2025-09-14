import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bitwise
import Mathlib.Analysis.Normed.Ring.Lemmas

lemma nat_is_zero_or_between_two_pow (i : ℕ) :
    i = 0 ∨ ∃n, 2^n ≤ i ∧ i < 2^(n+1) := by
  by_cases i = 0
  · left; assumption
  right
  use Nat.log2 i
  constructor
  · exact Nat.log2_self_le (by assumption)
  exact Nat.lt_log2_self

lemma nat_is_zero_two_pow_or_between_two_pow (i : ℕ) :
    i = 0 ∨ (∃n, i = 2^n) ∨  ∃n, 2^n < i ∧ i < 2^(n+1) := by
  rcases (nat_is_zero_or_between_two_pow i) with h | ⟨n, h⟩
  · left; assumption
  right
  rcases h.1.lt_or_eq with h' | rfl
  · right; exact ⟨n, h', h.2⟩
  left; use n

lemma order_two_pow_testBit_true (x n : ℕ) (h1 : 2 ^ n ≤ x) (h2 : x < 2 ^ (n + 1)) :
    x.testBit n = true := by
  have : x >>> n = 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt_le
    · simp [h1]
    rw [mul_comm, <-Nat.pow_add_one]
    exact h2
  unfold Nat.testBit
  simp [this]

lemma bitwise_test_power_of_two (x : ℕ) (nezero : x ≠ 0) :
    x &&& (x - 1) = 0 ↔ x.isPowerOfTwo := by
  rcases nat_is_zero_two_pow_or_between_two_pow x with _ | ⟨n, h⟩ | ⟨n, h⟩
  · contradiction
  · simp [Nat.isPowerOfTwo, h]
  have : ¬x.isPowerOfTwo := by
    rw [Nat.isPowerOfTwo, not_exists]
    intro i h'
    rw [h'] at h
    rw [Nat.pow_lt_pow_iff_right (a := 2) (n := n) (m := i) (h := by norm_num)] at h
    rw [Nat.pow_lt_pow_iff_right (a := 2) (h := by norm_num)] at h
    linarith
  simp only [this, iff_false, ne_eq]
  suffices (x &&& (x - 1)).testBit n = true by grind
  have h1 : x.testBit n = true :=
    order_two_pow_testBit_true x n h.1.le h.2
  have h2 : (x - 1).testBit n = true := by
    grind [order_two_pow_testBit_true]
  rw [Nat.testBit_and, h1, h2]
  rfl



lemma complement_is_smaller (i n : ℕ) (h : 2 ^ n ≤ i ∧ i < 2 ^ (n + 1)) :
    2 ^ (n + 1) - 1 ^^^ i < 2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro j jh
  rcases lt_or_eq_of_le jh with h' | h'
  · simp only [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
    rw [decide_eq_false (by grind)]
    simp only [Bool.false_bne]
    apply Nat.testBit_eq_false_of_lt
    apply lt_of_lt_of_le h.2
    apply Nat.pow_le_pow_right (by norm_num) (by assumption)
  have : i.testBit n = true := by
    exact order_two_pow_testBit_true i n h.1 h.2
  simp [<-h', this]

lemma Nat.log2_eq (i n : ℕ) (nezero : i ≠ 0) : 2^n ≤ i ∧ i < 2^(n+1) ↔ i.log2 = n:= by
  rw [Nat.log2_eq_log_two, Nat.log_eq_iff]
  simp [nezero]

universe u in
@[elab_as_elim, specialize]
def binaryComplementRec {motive : Nat → Sort u} (zero : motive 0)
    (two_pow : ∀ i, 0 < i → motive ((2 ^ (i.log2 + 1) - 1) ^^^ i) → motive i)
    (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ zero
  else
    let descent := binaryComplementRec zero two_pow ((2^(n.log2+1) - 1) ^^^ n)
    two_pow n (Nat.zero_lt_of_ne_zero n0) descent
decreasing_by
  have := Nat.log2_self_le n0
  linarith [complement_is_smaller n n.log2 ((Nat.log2_eq n n.log2 n0).mpr rfl)]

lemma Nat.two_pow_sub_one_xor_eq {x n : ℕ} (h : x < 2 ^ n) : 2 ^ n - 1 ^^^ x = 2 ^ n - 1 - x := by
  rw [show 2^n - 1 - x = 2^n - (x + 1) by omega]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_two_pow_sub_succ h]
  simp only [testBit_xor, testBit_two_pow_sub_one]
  have : x.testBit i → decide (i < n) := by
    simp only [decide_eq_true_eq]
    intro h'
    contrapose! h'
    simp only [Bool.not_eq_true]
    apply Nat.testBit_eq_false_of_lt
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) h'
    linarith
  grind

lemma complement_xor_two_pow (m : ℕ) : 2 ^ (m + 1) - 1 ^^^ 2 ^ m = 2^m - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases (show i < m ∨ i = m ∨ m < i by grind only) with h | h | h
  · simp only [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, h, decide_true, bne_iff_ne, ne_eq]
    grind
  · simp [h]
  simp only [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  rw [decide_eq_false, decide_eq_false]
  · grind
  · exact Nat.not_lt_of_gt h
  exact Nat.not_lt.mpr h

lemma Nat.shiftRight_two_pow_sub_one (n m : ℕ) : (2^(n+m) - 1) >>> m = 2^n - 1 :=
  Nat.eq_of_testBit_eq fun i => by simp; grind

lemma Nat.two_pow_add_one_sub_one_eq (n : ℕ) : (2^(n + 1) - 1) = 2^n ^^^ (2^n - 1) :=
  Nat.eq_of_testBit_eq fun i ↦ by
    simp [Nat.testBit_two_pow]
    grind

lemma Nat.two_pow_sub_one_xor_add_one (n : ℕ) : (2^n - 1) ^^^ (2^(n + 1) - 1) = 2^n := by
  rw [Nat.two_pow_add_one_sub_one_eq, Nat.xor_comm (2^n), <-Nat.xor_assoc]
  simp

lemma Nat.xor_two_pow_log2 {n : ℕ} (nezero : n ≠ 0) : n ^^^ 2^n.log2 = n - 2^n.log2 :=
  Nat.eq_of_testBit_eq fun i => by
    have : 2^n.log2 ≤ n := log2_self_le nezero
    rcases (by grind : i < n.log2 ∨ i = n.log2 ∨ n.log2 < i) with h | h | h
    · set m := n - 2^n.log2 with m_def
      have n_def : n = m + 2^n.log2 := (Nat.sub_eq_iff_eq_add this).mp rfl
      nth_rw 1 [n_def]
      rw [Nat.testBit_xor]
      rw [Nat.add_comm, Nat.testBit_two_pow_add_gt h]
      rw [Nat.testBit_two_pow_of_ne]
      · simp
      exact h.ne'
    · set m := n - 2^n.log2 with m_def
      have n_def : n = m + 2^n.log2 := (Nat.sub_eq_iff_eq_add this).mp rfl
      nth_rw 1 [n_def]
      rw [Nat.add_comm]
      simp [h, Nat.testBit_two_pow_add_eq]
    rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow]
    · exact sub_lt_of_lt ((log2_lt nezero).mp h)
    exact Nat.xor_lt_two_pow ((log2_lt nezero).mp h)
      (Nat.pow_lt_pow_right (by norm_num) h)

universe u in
@[elab_as_elim, specialize]
def binaryBigEndianRec {motive : Nat → Sort u} (zero : motive 0)
    (two_pow : ∀ i, 0 < i → motive (i ^^^ 2 ^ i.log2) → motive i)
    (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ zero
  else
    let descent := binaryBigEndianRec zero two_pow (n ^^^ 2^n.log2)
    two_pow n (Nat.zero_lt_of_ne_zero n0) descent
decreasing_by
  rw [Nat.xor_two_pow_log2 n0]
  simp only [tsub_lt_self_iff, Nat.ofNat_pos, pow_pos, and_true, gt_iff_lt]
  exact Nat.zero_lt_of_ne_zero n0

lemma Nat.testBit_log2 (n : ℕ) (h : n ≠ 0) : n.testBit n.log2 = true :=
  order_two_pow_testBit_true n n.log2 (log2_self_le h) lt_log2_self

lemma Nat.testBit_log2' (n : ℕ) (h : n ≠ 0) : n.testBit n.log2 = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rw [decide_eq_true_iff]
  suffices n / 2^n.log2 = 1 by simp [this]
  apply le_antisymm
  · rw [<-Nat.lt_add_one_iff]
    simp only [Nat.reduceAdd]
    rw [Nat.div_lt_iff_lt_mul, Nat.mul_comm, <-Nat.pow_add_one]
    · exact Nat.lt_log2_self
    exact Nat.two_pow_pos n.log2
  rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos n.log2), one_mul]
  exact Nat.log2_self_le h

lemma Nat.xor_two_pow_of_lt (x n : ℕ) (h : x < 2 ^ n) : 2^n ^^^ x = 2^n + x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases (by grind : i < n ∨ i = n ∨ n < i) with h' | h' | h'
  · rw [Nat.testBit_two_pow_add_gt h']
    grind
  · rw [h']
    simp [Nat.testBit_two_pow_add_eq]
  rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
  · have : 2*2^n ≤ 2^i := by
      rw [<-Nat.pow_add_one']
      exact Nat.pow_le_pow_right (n := 2) (by norm_num) h'
    grind
  have := Nat.pow_lt_pow_right (a := 2) (by norm_num) h'
  apply Nat.xor_lt_two_pow this (lt_trans h this)

lemma Nat.xor_eq_iff (a b c : ℕ) : a ^^^ b = c ↔ b = a ^^^ c := by grind

lemma Nat.shiftRight_two_pow (m n) : 2^(m+n) >>> n = 2^m := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_add]
  rw [Nat.mul_div_cancel (H := by simp)]

lemma Nat.xor_mul_two_pow (a b n : ℕ) : (a ^^^ b) * 2^n = a * 2^n ^^^ b * 2^n :=
  bitwise_mul_two_pow (f := Bool.xor) (x := a) (y := b) (n := n)

lemma Nat.xor_mul_two (a b : ℕ) : (a ^^^ b) * 2 = a * 2 ^^^ b * 2 :=
  Nat.xor_mul_two_pow a b 1

lemma Nat.xor_two_add_one (a : ℕ) : (2 * a ^^^ 1) = 2 * a + 1 :=
  Nat.eq_of_testBit_eq fun i ↦ by
    rw [show 2 = 2^1 by rfl]
    rw [Nat.testBit_two_pow_mul_add (b_lt := by simp)]
    by_cases h : i = 0
    · simp [h]
    have : testBit 1 i = false := by
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero.symm.not, Bool.not_eq_true] at h
      exact h
    simp only [pow_one, testBit_xor, this, Bool.bne_false, lt_one_iff, h, ↓reduceIte]
    rw [show 2 = 2^1 by rfl, Nat.testBit_two_pow_mul, decide_eq_true (one_le_iff_ne_zero.mpr h)]
    simp

/--
Let $n$ be a natural number. Then $n \oplus (n+1) = 2^k - 1$ for some $0 < k$.
-/
lemma Nat.exists_xor_add_one_eq_two_pow (n : ℕ) : ∃k > 0, n ^^^ (n+1) = 2^k - 1 := by
  induction n using Nat.binaryRec with
  | z => use 1; simp
  | f b n kh =>
    rcases kh with ⟨k, kh, h⟩
    have : 2*n ^^^ 2*(n+1) = 2 * (2^k - 1) := by
      rw [mul_comm, mul_comm 2, mul_comm 2, <-Nat.xor_mul_two, h]
    if h' : b then
      rw [h', bit_true_apply]
      use k+1, (Nat.add_pos_left kh 1)
      rw [add_assoc, show 1 + 1 = 2 by rfl]
      rw [<-Nat.xor_two_add_one, Nat.xor_comm _ 1, Nat.xor_assoc]
      rw [mul_add, mul_one] at this
      rw [this, Nat.xor_comm, Nat.xor_two_add_one]
      rw [Nat.mul_sub, mul_one, <-Nat.pow_add_one']
      have : 0 < 2^k := Nat.two_pow_pos k -- truly horrible to find that I needed this
      grind
    else
      simp at h'
      rw [h', bit_false_apply]
      use 1
      simp [<-Nat.xor_two_add_one, <-Nat.xor_assoc]
