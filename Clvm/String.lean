import Clvm.Serde


lemma string_as_chars {cs: List Char} : (String.mk cs).data = cs := by rfl


lemma drop_one_list_char {cs: List Char} : ((String.mk cs).drop 1).data = cs.drop 1 := by
  simp only [String.data_drop, List.drop_one]


lemma drop_one {s: String} : (s.drop 1).data = s.data.drop 1 := by
  simp only [String.data_drop, List.drop_one]


lemma string_csize_gt_0: ∀ c, Char.utf8Size c > 0 := by
  intro c
  unfold Char.utf8Size UInt32.ofNatCore
  if h_v127: c.1 ≤ { val := ⟨127, Char.utf8Size.proof_1⟩ } then
    simp [h_v127, UInt32.toNat]
  else
    simp [h_v127]
    if h_v2047: c.1 ≤ { val := ⟨2047, Char.utf8Size.proof_2⟩ } then
      simp [h_v2047, UInt32.toNat]
    else
      simp [h_v2047]
      if h_v65535: c.1 ≤ { val := ⟨65535, Char.utf8Size.proof_3⟩ } then
        simp [h_v65535, UInt32.toNat]
      else
        simp [h_v65535, UInt32.toNat]


/-
lemma starts_with_list_char: ∀ (cs1: List Char), (String.mk cs0).startsWith (String.mk cs1) → cs0 = cs1 ++ cs0.drop (cs1.length):= by
  induction cs0 with
  | nil =>
    simp
  | cons head tail ih =>
    intro cs0
    intro h
    sorry
-/

#eval "foo".take 2 ++ "foo".drop 2

/-
lemma add_string_pos (m n: String.Pos): (m + n) = m. + n.toNat := by
  sorry
-/


example {s: String} : s.endPos = 0 → s = "" := by
  intro h
  have : Eq s "" := by
    sorry
  exact (String.endPos_eq_zero s).mp h


def index_to_pos (s: String) (n: Nat) : String.Pos :=
  helper s.iter n where
    helper (i: String.Iterator) (n: Nat): String.Pos :=
      if n = 0 then
        i.i
      else
        helper i.next (n-1)


#check String.back

example: ∀ s, index_to_pos s n = (s.iter.nextn n).pos := by
  induction n with
  | zero => intro s; simp only [index_to_pos, String.iter, String.mkIterator, index_to_pos.helper,
    ↓reduceIte, String.Iterator.pos, String.Iterator.nextn]
  | succ n ih =>
    intro s
    unfold index_to_pos index_to_pos.helper String.iter String.mkIterator
    simp
    simp [String.Iterator.next, String.next]
    unfold index_to_pos at ih
    obtain z := ih s

    sorry


example {s: String}: s.toSubstring.nextn n 0 = (s.iter.nextn n).pos := by
  induction n with
  | zero =>
    simp only [Substring.nextn, String.Iterator.pos]
    simp only [String.Iterator.nextn, String.iter, String.mkIterator]
  | succ n ih =>
    unfold Substring.nextn
    unfold String.Iterator.nextn
    unfold Substring.next
    unfold String.Iterator.next
    sorry


example {cs: List Char}: cs = cs.take n ++ cs.drop n := by
  simp only [List.take_append_drop]



example {s: String}: (s.drop n).data = s.data.drop n := by
  simp_all only [String.data_drop]

example {s: String}: (s.take n).data = s.data.take n := by
  simp_all only [String.data_take]


lemma string_take_drop (s: String) (n: Nat): s = s.take n ++ s.drop n := by
  ext n_1 a : 3
  simp_all only [Option.mem_def, String.data_append, String.data_take, String.data_drop, List.take_append_drop]



example {s: String}: String.mk (String.mk (s.data.reverse)).data.reverse = s := by
  simp only [List.reverse_reverse]


example {s: String}: (s.toSubstring.take n).toString = s.take n := by
  simp only [Substring.take, Substring.toString, String.take]

/-
example {ss0 ss1: Substring}: ss0.toString = ss1.toString → ss0 = ss1 := by
  intro h
  unfold Substring.toString at h


example {s: String} : s.startsWith (String.mk p) → s.data.take p.length = p := by
  intro h0

  have h1: (s.take p.length).data = s.data.take p.length := by
    rw [← String.data_take]

  induction p with
  | nil => simp
  | cons head tail ih =>
    unfold String.startsWith at h0
    unfold BEq.beq at h0
    unfold Substring.hasBeq at h0
    simp [Substring.beq] at h0

    sorry



  unfold String.toSubstring at h0
  simp [BEq.beq] at h0
  simp [Substring.beq] at h0
  simp [Substring.take] at h0

  have h2: s.data.take p.length = p.data := by
    induction p.data with
    | nil =>
      simp
    | cons head tail ih => sorry

    sorry
  rw [h2] at h1

  sorry



example: s.take 2 = "ff" → s = "ff" ++ s.drop 2 := by
  intro h
  rw [← h]
  apply string_take_drop




lemma z2 {s: String} {c: Char}: s.startsWith (String.mk [c]) → s.take 1 = String.mk [c] := by
  intro h
  unfold String.startsWith at h
  simp [String.length] at h
  simp [String.toSubstring] at h
  simp [Substring.take, Substring.nextn, Substring.next, String.next] at h
  simp [HAdd.hAdd] at h
  unfold Add.add at h
  simp [instAddNat] at h
  if h0: s.endPos = 0 then
    simp [h0] at h
    simp [BEq.beq, Substring.beq, Substring.bsize, String.csize, Char.utf8Size] at h
    obtain ⟨left, right⟩ := h
    simp_all only
    split at left
    next h =>
      split at right
      next h_1 => simp_all only [UInt32.toNat_ofNat, Nat.one_mod, zero_ne_one]
      next h_1 => simp_all only
    next h =>
      split at right
      next h_1 =>
        split at left
        next h_2 => simp_all only [not_true_eq_false]
        next h_2 =>
          split at left
          next h_3 => simp_all only [not_true_eq_false]
          next h_3 => simp_all only [not_true_eq_false]
      next h_1 =>
        split at left
        next h_2 =>
          split at right
          next h_3 => simp_all only [not_false_eq_true, UInt32.not_le, UInt32.toNat_ofNat]
          next h_3 => simp_all only [not_false_eq_true, UInt32.not_le]
        next h_2 =>
          split at right
          next h_3 =>
            split at left
            next h_4 => simp_all only [not_false_eq_true, UInt32.not_le, not_true_eq_false]
            next h_4 => simp_all only [not_false_eq_true, UInt32.not_le, not_true_eq_false]
          next h_3 =>
            split at left
            next h_4 =>
              split at right
              next h_5 => simp_all only [not_false_eq_true, UInt32.not_le, UInt32.toNat_ofNat]
              next h_5 => simp_all only [not_false_eq_true, UInt32.not_le]
            next h_4 =>
              split at right
              next h_5 => simp_all only [not_false_eq_true, UInt32.not_le, not_true_eq_false]
              next h_5 => simp_all only [not_false_eq_true, UInt32.not_le, UInt32.toNat_ofNat]
  else
    simp_all only
    split at h
    next h_1 => simp_all only [not_true_eq_false]
    next h_1 =>
      simp [BEq.beq, Substring.beq, Substring.bsize, String.csize] at h
      obtain ⟨left, right⟩ := h
      simp_all only
      simp [String.substrEq] at right
      obtain ⟨left_1, right⟩ := right
      obtain ⟨left_1, right_1⟩ := left_1
      unfold String.substrEq.loop at right
      simp [String.take, String.next] at right
      simp [String.take, Substring.take, Substring.toString]
      simp [String.extract, Substring.nextn, Substring.next]
      sorry





lemma z1 {s: String} {c: Char}: s.startsWith (String.mk [c]) → ∃ tail, s.data = c :: tail := by
  intro h
  use (s.data.drop 1)
  have z := string_take_drop s 1
  rw [z] at h
  simp [String.startsWith] at h
  unfold String.take at h






lemma z {s: String} {c: Char}: s.startsWith (String.mk [c]) → ∃ tail, s.data = c :: tail := by
  intro h
  use (s.data.drop 1)

  simp

  unfold String.startsWith String.toSubstring Substring.take at h
  simp [String.length] at h
  simp [String.length, Substring.nextn, Substring.next] at h
  unfold HAdd.hAdd instHAddPos HAdd.hAdd instHAdd Add.add instAddNat Nat.add at h
  simp [String.next] at h
  unfold BEq.beq Substring.hasBeq Substring.beq at h
  simp [Substring.bsize] at h
  simp [String.substrEq] at h
  if h0: 0 = s.endPos then
    -- this one's impossible
    simp [h0] at h
    simp [String.substrEq.loop] at h
    rw [← h0] at h
    simp at h
    have := string_csize_gt_0 (c := c)
    linarith
  else
    simp [h0] at h
    simp [String.substrEq.loop] at h
    induction s.data with
    | nil => sorry
    | cons head tail ih => sorry




  induction s.data with
  | nil =>
    unfold String.startsWith String.length at h
    simp [Substring.take, Substring.nextn] at h
    sorry
  | cons head tail ih =>
    simp [String.startsWith, String.length, String.take, String.next, String.endPos] at h
    simp [BEq.beq, Substring.beq, Substring.take, Substring.str, Substring.startPos] at h
    sorry



  simp [String.length, String.toSubstring, Substring.take, Substring.nextn, Substring.next, String.next, String.endPos, String.csize] at h
  unfold String.get at h
  unfold Char.utf8Size at h
  unfold String.utf8ByteSize at h
  unfold String.utf8GetAux at h
  simp at h
  unfold String.utf8Len at h
  unfold String.utf8ByteSize.go String.csize Char.utf8Size Char.val String.utf8GetAux at h
  simp at h
  unfold String.utf8Len at h
  unfold String.utf8ByteSize.go String.csize Char.utf8Size Char.val String.utf8GetAux at h
  simp at h


  unfold String.data UInt32.toNat
  simp [UInt32.ofNatCore]

  unfold String.utf8GetAux



  induction s.data with
  | nil => sorry
  | cons head tail ih => sorry






example: s.startsWith "ff" → s = "ff" ++ s.drop 2 := by
  intro h

  have h1: s.data = "ff".data ++ s.data.drop 2 := by
    rw [← String.data_drop]
    sorry
  sorry




example {n: Nat}: ∀ s, ((String.mk (s.data.reverse)).extract 0 (index_to_pos s n)).data = s.data.reverse.extract 0 n := by
  induction n with
  | zero =>
    unfold String.extract
    simp [List.extract]
    unfold index_to_pos index_to_pos.helper
    simp [String.iter, String.mkIterator]
  | succ n ih =>
    intro s
    unfold index_to_pos index_to_pos.helper
    simp
    unfold String.extract
    simp
    unfold String.extract.go₁


    sorry


#eval [1, 2].reverse


#eval index_to_pos "← foo" 3


#eval [1, 2].extract 1 5



example {s: String} {n: Nat}: (String.extract.go₂ s.data 0 (index_to_pos s n)) = s.data.extract 0 n := by
  induction n with
  | zero =>
    unfold String.extract.go₂
    simp [List.extract]
    simp [index_to_pos, index_to_pos.helper, String.iter, String.mkIterator]
    induction s.data with
    | nil => simp
    | cons head tail ih => simp
  | succ n ih =>
    unfold String.extract.go₂
    unfold List.extract List.take
    simp [List.drop]
    induction s.data with
    | nil => simp
    | cons head tail ih =>
      simp
      if h: 0 = index_to_pos s (n + 1) then
        unfold index_to_pos index_to_pos.helper at h
        simp at h
        unfold String.iter String.mkIterator String.Iterator.next at h
        simp [String.next, String.get] at h
        unfold String.utf8GetAux at h
        sorry
      else
        simp [h]
        simp [HAdd.hAdd]
        unfold Add.add
        simp [instAddNat]
        sorry



example {s: String} {n: Nat}: (s.extract 0 (index_to_pos s n)).data  = s.data.extract 0 n := by
  induction n with
  | zero =>
    unfold index_to_pos index_to_pos.helper
    simp [String.iter, String.extract, String.mkIterator]
    simp [List.extract]
  | succ n ih =>
    unfold index_to_pos index_to_pos.helper
    simp [String.iter, String.mkIterator]
    unfold String.extract
    sorry



example {s: String} {n: Nat}: (s.take n).data  = s.data.take n := by
  induction n with
  | zero => simp
  | succ n ih =>
    unfold String.take String.toSubstring at ih

    unfold String.take String.toSubstring
    unfold Substring.take
    simp [Substring.toString]

    sorry

example {s: String} {n: Nat}: (s.extract (index_to_pos s (s.length - n)) s.endPos).data  = s.data.drop n := by
  induction n with
  | zero =>
    simp [index_to_pos]
    simp [String.iter, String.mkIterator]
    unfold index_to_pos.helper
    if h: s.length = 0 then
      simp [h]
      unfold String.length at h
      simp [String.extract]
      if h0: s.endPos.byteIdx = 0 then
        simp [h0]
        by_contra h1
      else
        sorry
    else
      sorry
    simp [String.extract]


    sorry
  | succ n ih => sorry



example {s: String} {n: Nat}: (s.extract 0 (index_to_pos s n)).data  = s.data.extract 0 n := by
  induction n with
  | zero =>
    simp only [index_to_pos, index_to_pos.helper, ↓reduceIte]
    simp only [String.iter]
    simp only [List.extract, ge_iff_le, le_refl, tsub_eq_zero_of_le, List.drop_zero, List.take_zero]
    simp only [String.extract, String.Pos.byteIdx_zero, ge_iff_le, nonpos_iff_eq_zero]
    simp only [String.mkIterator, String.Pos.byteIdx_zero, ↓reduceIte]

  | succ m ih =>
    unfold List.extract
    simp


    unfold List.extract at ih
    simp at ih
    unfold String.extract at ih
    simp at ih

    unfold String.extract
    sorry


#check List.extract String.Pos

example {s: String} : (s.extract 0 s.endPos).data = s.data := by
  simp [String.extract]
  simp [String.endPos]
  induction s.data with
  | nil =>
      if h: s.utf8ByteSize = 0 then
        simp [h]
    else
      simp [h]
      unfold String.extract.go₁
      simp

  | cons head tail ih =>
    unfold String.extract.go₁
    simp
    if h: s.utf8ByteSize = 0 then
      simp at h
      sorry
    else
      simp [h]
      unfold String.extract.go₂
      if h0: (0: String.Pos) = { byteIdx := s.utf8ByteSize } then
        unfold String.utf8ByteSize at h
        simp [h0] at h
        simp [h0] at ih
        unfold String.utf8ByteSize at h0
        sorry
      else
        sorry


  if h: s.endPos.byteIdx = 0 then
    simp [h]
    sorry
  else
    sorry

#check Eq ("": String) ""
#check @Eq.trans
#eval Eq 3 3
#check Eq.refl 3


example {s: Substring} {k: Nat}: (s.take k).toString ++ (s.drop k).toString = s.toString := by
  simp [Substring.take, Substring.drop]
  induction k with
  | zero =>
    simp [Substring.nextn, Substring.next]
    simp [HAppend.hAppend, Append.append]
    simp [Substring.toString]
    simp [String.extract]
    if h: s.stopPos.byteIdx ≤ s.startPos.byteIdx then
      simp [h]
      rfl
    else
      simp [h]

      sorry
  | succ n ih => sorry


example {s: String} {k: Nat}: s.take k ++ s.drop k = s := by
  simp [String.take, String.drop]
  simp [String.toSubstring]
  simp [Substring.take, Substring.drop]
  induction k with
  | zero =>
    simp [Substring.nextn, Substring.next]
    sorry
  | succ n ih => sorry
-/
