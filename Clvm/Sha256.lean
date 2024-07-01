-- adapted from claude.ai which doesn't know lean3 vs lean4
-- see also https://foss.heptapod.net/pypy/pypy/-/blob/branch/default/lib_pypy/_sha256.py

-- SHA-256 state

import Clvm.Atom
import Clvm.Coe


structure Sha256_state :=
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

-- SHA-256 constants
def K : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
   0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
   0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
   0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
   0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
   0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
   0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
   0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
   0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]


def rotr (count: UInt32) (x: UInt32) :=
  let y : UInt32 := count &&& 31
  ((x >>> y) ||| (x <<< (32 - y) &&& 0xffffffff))


-- SHA-256 logical functions
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~ x &&& z)
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def sig0 (x : UInt32) : UInt32 :=
    (rotr 2 x) ^^^ (rotr 13 x) ^^^ (rotr 22 x)
def sig1 (x : UInt32) : UInt32 :=
    (rotr 6 x) ^^^ (rotr 11 x) ^^^ (rotr 25 x)
def gamma0 (x : UInt32) : UInt32 :=
    (rotr 7 x) ^^^ (rotr 18 x) ^^^ (x >>> 3)
def gamma1 (x : UInt32) : UInt32 :=
    (rotr 17 x) ^^^ (rotr 19 x) ^^^ (x >>> 10)


-- Perform one SHA-256 transformation, updating state
def transform (s : Sha256_state) (i : Nat) (wi : UInt32) : Sha256_state :=
  let t1 := s.h + sig1 s.e + ch s.e s.f s.g  + K[i]! + wi
  let t2 := sig0 s.a + maj s.a s.b s.c
  let h := s.g
  let g := s.f
  let f := s.e
  let e := s.d + t1
  let d := s.c
  let c := s.b
  let b := s.a
  let a := t1 + t2
  ⟨a, b, c, d, e, f, g, h⟩


def augment_w (w : Array UInt32) : Array UInt32 :=
  let list_16_64 : Array Nat := (List.range 48).toArray.map (fun x => x + 16)
  let updater (w : Array UInt32) (i : Nat) : Array UInt32 :=
    w.push (gamma1 w[i - 2]! + w[i - 7]! + gamma0 w[i - 15]! + w[i - 16]!)
  list_16_64.foldl updater w


-- #eval augment_w #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- SHA-256 compression function
def compress (state : Sha256_state) (w : Array UInt32) : Sha256_state :=
  let w := augment_w w
  (List.range 64).foldl (fun state i => transform state i w[i]!) state


def compress_and_add (state : Sha256_state) (w : Array UInt32) : Sha256_state :=
  let compressed := compress state w
  ⟨compressed.a + state.a, compressed.b + state.b, compressed.c + state.c, compressed.d + state.d,
   compressed.e + state.e, compressed.f + state.f, compressed.g + state.g, compressed.h + state.h⟩


-- Process message in successive 512-bit chunks
def process_message_blocks (s : Sha256_state) (blocks : List (Array UInt32)) : Sha256_state :=
  blocks.foldl compress_and_add s


def to_uint32 (u8_list : Array UInt8) : UInt32 :=
  let partial_list := u8_list.extract 0 4
  partial_list.foldl (fun (acc : UInt32) (x : UInt8) => (acc * 256) + x.toUInt32) 0


def to_uint32_array (depth: Nat) (u8_list : Array UInt8) : Array UInt32 :=
  if depth = 0 then
    Array.empty
  else if u8_list.size < 4 then
    Array.empty
  else
    #[to_uint32 u8_list] ++ to_uint32_array (depth - 1) (u8_list.extract 4 u8_list.size)


def as_list_of_16_uint32s (depth : Nat) (u32_list : Array UInt32) : List (Array UInt32) :=
  if depth = 0 then
    []
  else if u32_list.size = 0 then
    []
  else
    let partial_list := u32_list.extract 0 16
    [partial_list] ++ as_list_of_16_uint32s (depth - 1) (u32_list.extract 16 u32_list.size)


def padded_msg (msg : Array UInt8) : List (Array UInt32) :=
  let len := msg.size
  -- pad with a 0x80 byte
  let msg := msg ++ #[0x80, 0, 0, 0, 0]
  -- make it an integral number of UInt32 words
  let msg := msg ++ #[0, 0, 0].extract 0 (3 - ((msg.size+3) % 4))
  assert! msg.size % 4 = 0
  -- turn to UInt32 array
  let msg_32 := to_uint32_array msg.size msg
  -- pad with 0s and length
  let padding : Array UInt32 := Array.mkArray (15 - ((msg_32.size + 16) % 16)) 0
  let msg_32 := msg_32 ++ padding ++ #[len.toUInt32 * 8]
  assert! msg_32.size % 16 = 0
  as_list_of_16_uint32s (msg_32.size) msg_32


-- def arr : Array UInt8 := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]
-- #eval (padded_msg arr)

-- SHA-256 with message padding and digest calculation
def sha256_32 (msg : Array UInt8) : Array UInt32 :=
    let padded := padded_msg msg
    let init := Sha256_state.mk 0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a
                 0x510e527f 0x9b05688c 0x1f83d9ab 0x5be0cd19
    let final := process_message_blocks init padded
    #[final.a, final.b, final.c, final.d, final.e, final.f, final.g, final.h]


def u32_to_u8 (x : UInt32) : Array UInt8 :=
  #[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]


def hex_u32 (x : UInt32) : String :=
  b2h_uint8 (u32_to_u8 x)


def to_hex (x : Array UInt32) := String.join (x.toList.map hex_u32)

def a_str : Array UInt8 := #[106, 117, 115, 116, 32, 97, 32, 116, 101, 115, 116, 32, 115, 116, 114, 105, 110, 103]

def test_str := a_str ++ a_str

#eval ((sha256_32 test_str).map hex_u32)


def sha256_bytes (msg : List Nat) : List Nat :=
  let u32s := sha256_32 (msg.toArray.map UInt8.ofNat)
  let r : List (List UInt8) := ((u32s.map u32_to_u8).map Array.toList).toList
  let s: List UInt8 := r.join
  s.map UInt8.toNat


def sha256 (msg : List Nat) : Atom :=
  let u32s := sha256_32 (msg.toArray.map UInt8.ofNat)
  let r : List (List UInt8) := ((u32s.map u32_to_u8).map Array.toList).toList
  let s: List UInt8 := r.join
  let sn: List Nat := s.map UInt8.toNat
  have hs: ∀ x, x ∈ s.map UInt8.toNat → x ≤ 255 := by
    apply map_prop_dist_for_all
    unfold UInt8.toNat
    exact fun a ↦ Fin.is_le a.val
  Atom.mk sn hs
