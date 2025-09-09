import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Analysis.Normed.Ring.Lemmas  -- I have no idea why this is necessary

--#eval Nat.testBit 1 0

def next_to (x y : ℕ) : Prop :=
  ∃ j, x.testBit j != y.testBit j ∧
    ∀k ≠ j, x.testBit k = y.testBit k

example : next_to 4 5 := by
  unfold next_to
  use 0
  refine ⟨by simp, ?_⟩
  intro k knot0
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth]
  rw [show Nat.bits 4 = [false, false, true] by simp [Nat.bits, Nat.binaryRec]]
  rw [show Nat.bits 5 = [true, false, true] by simp [Nat.bits, Nat.binaryRec]]
  -- There still has to be  abetter way to do this kind of casework
  if k = 0 then
    contradiction
  else if h : k = 1 then
    simp [h]
  else if h' : k = 2 then
    simp [h']
  else
    have : 3 ≤ k := by grind
    rw [List.getI_eq_default [false, false, true] (by simp [this])]
    rw [List.getI_eq_default [true, false, true] (by simp [this])]


#check geom_sum_two

lemma geom_sum_pow_two (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2^n - 1 := by
  have := Nat.geomSum_eq (m := 2) Nat.AtLeastTwo.prop n
  simp [this]

#check Nat.testBit_two_pow_sub_one


/--
Note that $2^k - 1 = 1 + \cdots + 2^{k-1}$. Thus $(2^k - 1)_i = 1$ for
all $i \le {k-1}$.

When $x = 2^k$, since $(x)_k = 1$ and all others are $0$, while
$(x - 1)_k = 1$ for all $i \le k-1$ and $0$ otherwise. Thus $x \& (x - 1) = 0$
and we return true.

If $x = 0$, then we return false correctly.

Suppose that $2^i < x < 2^{i+1}$, then $(x)_i = 1$ and $2^i \le (x - 1) < 2^{i-1}$,
so thus $(x-1)_i = 1$. Thus $x \& (x - 1) \neq 0$.

    $x$ is next to $y$ iff there is some $i$ alone where they are different.
    This occurs iff $(x \oplus y) = (x)_i \oplus (y)_i = 1$ only for $i$.
    $(x \oplus y)_i$ for only $i$ iff $(x \oplus y) = 2^i$.
-/
lemma next_to_xor_two_pow (x y : ℕ) :
  next_to x y ↔ (x ^^^ y).isPowerOfTwo := by
  rw [show next_to x y ↔ ∃ j, (x ^^^ y).testBit j ∧ ∀k ≠ j, ¬(x ^^^ y).testBit k by
    simp [next_to]]
  apply exists_congr
  intro i
  set z := x ^^^ y
  refine ⟨?_, by grind⟩
  intro h
  apply Nat.eq_of_testBit_eq
  intro j
  if h' : j = i then
    rw [<-h'] at h ⊢
    simp only [Nat.testBit_two_pow_self, h.1]
  else
    rw [show z.testBit j = false by simp [h.2 j h']]
    rw [Nat.testBit_two_pow_of_ne (by grind)]

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

def Computable.next_to (x y : ℕ) : Bool :=
  let diff := x ^^^ y
  if diff = 0 then
    false
  else diff &&& (diff - 1) == 0

lemma computable_next_to_correct (x y : ℕ) :
  next_to x y ↔ Computable.next_to x y := by
  unfold Computable.next_to
  rw [next_to_xor_two_pow]
  if h : x ^^^ y = 0 then
    simp [h, Nat.isPowerOfTwo]
    intro i; positivity
  else
    rw [<-bitwise_test_power_of_two _ h]
    rw [if_neg h]
    exact beq_iff_eq.symm

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 1 3

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 3 2

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 4 5

def IsUnitStepSeq {α : Type*} [AddGroupWithOne α] (x : α → ℕ) : Prop :=
  ∀i, next_to (x i) (x (i + 1))

def IsGrayCode {α : Type*} [AddGroupWithOne α] (x : α → ℕ) : Prop :=
  IsUnitStepSeq x ∧ Function.Injective x

def list_gray_code : ℕ → List ℕ
| 0 => [0]
| .succ n => (list_gray_code n) ++ ((list_gray_code n).reverse.map (2^n ^^^ ·))


def is_list_gray_code (x : List ℕ) : Bool := Id.run do
  let mut is_good := true
  for i in List.range (x.length + 1) do
    is_good := is_good && Computable.next_to x[i % x.length]! x[(i + 1) % x.length]!
  return is_good

/--
info: [0, 1, 3, 2]
-/
#guard_msgs in
#eval list_gray_code 2

/--
info: true
-/
#guard_msgs in
#eval is_list_gray_code (list_gray_code 5)

@[simp, grind =]
lemma list_gray_code_length (n : ℕ) :
  (list_gray_code n).length = 2^n := by
  fun_induction list_gray_code n with
  | case1 => rfl
  | case2 n h => simp [h]; ring

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

lemma Nat.log2_eq (i n : ℕ) (nezero : i ≠ 0) :
  2^n ≤ i ∧ i < 2^(n+1) ↔ i.log2 = n:= by
  rw [Nat.log2_eq_log_two, Nat.log_eq_iff]
  simp [nezero]

universe u in
@[elab_as_elim, specialize]
def binaryComplementRec {motive : Nat → Sort u} (zero : motive 0)
  (two_pow : ∀ i, i > 0 → motive ((2 ^ (i.log2 + 1) - 1) ^^^ i) → motive i)
    (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ zero
  else
    let descent := binaryComplementRec zero two_pow ((2^(n.log2+1) - 1) ^^^ n)
    two_pow n (Nat.zero_lt_of_ne_zero n0) descent
decreasing_by
  have := Nat.log2_self_le n0
  linarith [complement_is_smaller n n.log2 ((Nat.log2_eq n n.log2 n0).mpr rfl)]

def recursive_gray_code (n : ℕ) : ℕ :=
  binaryComplementRec
    (zero := 0) -- zero case
    (two_pow := fun i _ complement ↦ 2^(i.log2) ^^^ complement)
      -- do when you have the complement
    n

def recursive_gray_code_eq {i : ℕ} (nezero : i ≠ 0) :
  recursive_gray_code i = 2^(i.log2) ^^^ recursive_gray_code ((2^(i.log2+1) - 1) ^^^ i) := by
  rw [recursive_gray_code, binaryComplementRec]
  simp_rw [dite_eq_ite, if_neg nezero]
  rw [<-recursive_gray_code]

/--
info: true
-/
#guard_msgs in
#eval (List.range (2^5)).all (fun i ↦ recursive_gray_code i == (list_gray_code 5)[i]!)

lemma Nat.two_pow_xor_eq {x n : ℕ} (h : x < 2 ^ n) :
  2 ^ n - 1 ^^^ x = 2 ^ n - 1 - x := by
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


@[reducible]
def list_gray_code_i (i : ℕ) :=
  (list_gray_code (i.log2 + 1))[i]'(by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp
    simp [Nat.lt_log2_self]
  )


lemma list_is_recursive_aux (i : ℕ) :
  list_gray_code_i i = recursive_gray_code i := by
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
      exact (Nat.two_pow_xor_eq Nat.lt_log2_self).symm
    simp_rw [this]
    have smaller_complement:= complement_is_smaller i (i.log2)
      ((Nat.log2_eq i i.log2 (Nat.ne_zero_of_lt ih)).mpr rfl)
    rw [list_is_stable (n := ((2 ^ (i.log2 + 1) - 1 ^^^ i).log2 + 1))
      (i := 2 ^ (i.log2 + 1) - 1 ^^^ i)
      (m := i.log2) smaller_complement] at complement
    rw [complement]
    rw [<-recursive_gray_code_eq]
    exact Nat.ne_zero_of_lt ih

@[simp]
lemma list_gray_code_zero (n : ℕ) :
  (list_gray_code n)[0] = 0 := by
  induction n with
  | zero => simp [list_gray_code]
  | succ n nh =>
    unfold list_gray_code
    simp [nh]

lemma list_is_recursive (i n : ℕ) {h : i < (list_gray_code n).length} :
  (list_gray_code n)[i] = recursive_gray_code i := by
  rw [list_is_stable (n := n) (i := i) (m := i.log2 + 1)]
  · exact list_is_recursive_aux i
  exact Nat.lt_log2_self

lemma next_to_comm (x y : ℕ) : next_to x y ↔ next_to y x := by
  unfold next_to
  simp_rw [eq_comm, Bool.xor_comm]

lemma reverse_unit_step {α : Type*} [AddCommGroupWithOne α] (x : α → ℕ) (l : α) :
  IsUnitStepSeq x → IsUnitStepSeq (fun i => x (l - i)) := by
  unfold IsUnitStepSeq
  intro h i
  simp only
  rw [next_to_comm]
  convert h (l - (i + 1)) using 2
  rw [<-sub_sub l i 1]
  simp

def hello := "world"
