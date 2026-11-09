module

public import EthLib.Cryptography.Hash.Keccak.FastProofI.Bits

/-! The interleaved permutation equals the spec permutation: `keccakPI (toI A) = toI (keccakF A)`.

embedded/gen/keccak/gen_proofI.py generates this file. -/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak.Fast
open EthLib.Cryptography.Hash.Keccak

/-! ## The interleaved state and one interleaved round -/

/-- The interleaved form of a state: lane `k` becomes its even bits `ek` and its odd bits `ok`. -/
def toI (A : State) : StateI :=
  ⟨ilvE64 A.a0, ilvO64 A.a0, ilvE64 A.a1, ilvO64 A.a1, ilvE64 A.a2, ilvO64 A.a2,
    ilvE64 A.a3, ilvO64 A.a3, ilvE64 A.a4, ilvO64 A.a4, ilvE64 A.a5, ilvO64 A.a5,
    ilvE64 A.a6, ilvO64 A.a6, ilvE64 A.a7, ilvO64 A.a7, ilvE64 A.a8, ilvO64 A.a8,
    ilvE64 A.a9, ilvO64 A.a9, ilvE64 A.a10, ilvO64 A.a10, ilvE64 A.a11, ilvO64 A.a11,
    ilvE64 A.a12, ilvO64 A.a12, ilvE64 A.a13, ilvO64 A.a13, ilvE64 A.a14, ilvO64 A.a14,
    ilvE64 A.a15, ilvO64 A.a15, ilvE64 A.a16, ilvO64 A.a16, ilvE64 A.a17, ilvO64 A.a17,
    ilvE64 A.a18, ilvO64 A.a18, ilvE64 A.a19, ilvO64 A.a19, ilvE64 A.a20, ilvO64 A.a20,
    ilvE64 A.a21, ilvO64 A.a21, ilvE64 A.a22, ilvO64 A.a22, ilvE64 A.a23, ilvO64 A.a23,
    ilvE64 A.a24, ilvO64 A.a24⟩

/-- Back from the interleaved form. -/
def ofI (S : StateI) : State :=
  ⟨dlv64 S.e0 S.o0, dlv64 S.e1 S.o1, dlv64 S.e2 S.o2, dlv64 S.e3 S.o3, dlv64 S.e4 S.o4,
    dlv64 S.e5 S.o5, dlv64 S.e6 S.o6, dlv64 S.e7 S.o7, dlv64 S.e8 S.o8, dlv64 S.e9 S.o9,
    dlv64 S.e10 S.o10, dlv64 S.e11 S.o11, dlv64 S.e12 S.o12, dlv64 S.e13 S.o13, dlv64 S.e14 S.o14,
    dlv64 S.e15 S.o15, dlv64 S.e16 S.o16, dlv64 S.e17 S.o17, dlv64 S.e18 S.o18, dlv64 S.e19 S.o19,
    dlv64 S.e20 S.o20, dlv64 S.e21 S.o21, dlv64 S.e22 S.o22, dlv64 S.e23 S.o23, dlv64 S.e24 S.o24⟩

theorem ofI_toI (A : State) : ofI (toI A) = A := by
  cases A; simp only [ofI, toI, dlv64_ilv]

/-- One interleaved round: the first half of the body of `loopI2`, verbatim. -/
def roundI (i : UInt32) (S : StateI) : StateI :=
  let a0e := S.e0
  let a0o := S.o0
  let a1e := S.e1
  let a1o := S.o1
  let a2e := S.e2
  let a2o := S.o2
  let a3e := S.e3
  let a3o := S.o3
  let a4e := S.e4
  let a4o := S.o4
  let a5e := S.e5
  let a5o := S.o5
  let a6e := S.e6
  let a6o := S.o6
  let a7e := S.e7
  let a7o := S.o7
  let a8e := S.e8
  let a8o := S.o8
  let a9e := S.e9
  let a9o := S.o9
  let a10e := S.e10
  let a10o := S.o10
  let a11e := S.e11
  let a11o := S.o11
  let a12e := S.e12
  let a12o := S.o12
  let a13e := S.e13
  let a13o := S.o13
  let a14e := S.e14
  let a14o := S.o14
  let a15e := S.e15
  let a15o := S.o15
  let a16e := S.e16
  let a16o := S.o16
  let a17e := S.e17
  let a17o := S.o17
  let a18e := S.e18
  let a18o := S.o18
  let a19e := S.e19
  let a19o := S.o19
  let a20e := S.e20
  let a20o := S.o20
  let a21e := S.e21
  let a21o := S.o21
  let a22e := S.e22
  let a22o := S.o22
  let a23e := S.e23
  let a23o := S.o23
  let a24e := S.e24
  let a24o := S.o24
  let c0e_0 := a0e ^^^ a5e ^^^ a10e ^^^ a15e ^^^ a20e
  let c1e_0 := a1e ^^^ a6e ^^^ a11e ^^^ a16e ^^^ a21e
  let c2e_0 := a2e ^^^ a7e ^^^ a12e ^^^ a17e ^^^ a22e
  let c3e_0 := a3e ^^^ a8e ^^^ a13e ^^^ a18e ^^^ a23e
  let c4e_0 := a4e ^^^ a9e ^^^ a14e ^^^ a19e ^^^ a24e
  let c0o_0 := a0o ^^^ a5o ^^^ a10o ^^^ a15o ^^^ a20o
  let c1o_0 := a1o ^^^ a6o ^^^ a11o ^^^ a16o ^^^ a21o
  let c2o_0 := a2o ^^^ a7o ^^^ a12o ^^^ a17o ^^^ a22o
  let c3o_0 := a3o ^^^ a8o ^^^ a13o ^^^ a18o ^^^ a23o
  let c4o_0 := a4o ^^^ a9o ^^^ a14o ^^^ a19o ^^^ a24o
  let d0e_0 := c4e_0 ^^^ rol32 c1o_0 1
  let d0o_0 := c4o_0 ^^^ c1e_0
  let d1e_0 := c0e_0 ^^^ rol32 c2o_0 1
  let d1o_0 := c0o_0 ^^^ c2e_0
  let d2e_0 := c1e_0 ^^^ rol32 c3o_0 1
  let d2o_0 := c1o_0 ^^^ c3e_0
  let d3e_0 := c2e_0 ^^^ rol32 c4o_0 1
  let d3o_0 := c2o_0 ^^^ c4e_0
  let d4e_0 := c3e_0 ^^^ rol32 c0o_0 1
  let d4o_0 := c3o_0 ^^^ c0e_0
  let r0e_0 := (a0e ^^^ d0e_0)
  let r0o_0 := (a0o ^^^ d0o_0)
  let r1e_0 := rol32 (a1o ^^^ d1o_0) 1
  let r1o_0 := (a1e ^^^ d1e_0)
  let r2e_0 := rol32 (a2e ^^^ d2e_0) 31
  let r2o_0 := rol32 (a2o ^^^ d2o_0) 31
  let r3e_0 := rol32 (a3e ^^^ d3e_0) 14
  let r3o_0 := rol32 (a3o ^^^ d3o_0) 14
  let r4e_0 := rol32 (a4o ^^^ d4o_0) 14
  let r4o_0 := rol32 (a4e ^^^ d4e_0) 13
  let r5e_0 := rol32 (a5e ^^^ d0e_0) 18
  let r5o_0 := rol32 (a5o ^^^ d0o_0) 18
  let r6e_0 := rol32 (a6e ^^^ d1e_0) 22
  let r6o_0 := rol32 (a6o ^^^ d1o_0) 22
  let r7e_0 := rol32 (a7e ^^^ d2e_0) 3
  let r7o_0 := rol32 (a7o ^^^ d2o_0) 3
  let r8e_0 := rol32 (a8o ^^^ d3o_0) 28
  let r8o_0 := rol32 (a8e ^^^ d3e_0) 27
  let r9e_0 := rol32 (a9e ^^^ d4e_0) 10
  let r9o_0 := rol32 (a9o ^^^ d4o_0) 10
  let r10e_0 := rol32 (a10o ^^^ d0o_0) 2
  let r10o_0 := rol32 (a10e ^^^ d0e_0) 1
  let r11e_0 := rol32 (a11e ^^^ d1e_0) 5
  let r11o_0 := rol32 (a11o ^^^ d1o_0) 5
  let r12e_0 := rol32 (a12o ^^^ d2o_0) 22
  let r12o_0 := rol32 (a12e ^^^ d2e_0) 21
  let r13e_0 := rol32 (a13o ^^^ d3o_0) 13
  let r13o_0 := rol32 (a13e ^^^ d3e_0) 12
  let r14e_0 := rol32 (a14o ^^^ d4o_0) 20
  let r14o_0 := rol32 (a14e ^^^ d4e_0) 19
  let r15e_0 := rol32 (a15o ^^^ d0o_0) 21
  let r15o_0 := rol32 (a15e ^^^ d0e_0) 20
  let r16e_0 := rol32 (a16o ^^^ d1o_0) 23
  let r16o_0 := rol32 (a16e ^^^ d1e_0) 22
  let r17e_0 := rol32 (a17o ^^^ d2o_0) 8
  let r17o_0 := rol32 (a17e ^^^ d2e_0) 7
  let r18e_0 := rol32 (a18o ^^^ d3o_0) 11
  let r18o_0 := rol32 (a18e ^^^ d3e_0) 10
  let r19e_0 := rol32 (a19e ^^^ d4e_0) 4
  let r19o_0 := rol32 (a19o ^^^ d4o_0) 4
  let r20e_0 := rol32 (a20e ^^^ d0e_0) 9
  let r20o_0 := rol32 (a20o ^^^ d0o_0) 9
  let r21e_0 := rol32 (a21e ^^^ d1e_0) 1
  let r21o_0 := rol32 (a21o ^^^ d1o_0) 1
  let r22e_0 := rol32 (a22o ^^^ d2o_0) 31
  let r22o_0 := rol32 (a22e ^^^ d2e_0) 30
  let r23e_0 := rol32 (a23e ^^^ d3e_0) 28
  let r23o_0 := rol32 (a23o ^^^ d3o_0) 28
  let r24e_0 := rol32 (a24e ^^^ d4e_0) 7
  let r24o_0 := rol32 (a24o ^^^ d4o_0) 7
  let b0e := (r0e_0 ^^^ (~~~r6e_0 &&& r12e_0)) ^^^ rcE i
  let b1e := r6e_0 ^^^ (~~~r12e_0 &&& r18e_0)
  let b2e := r12e_0 ^^^ (~~~r18e_0 &&& r24e_0)
  let b3e := r18e_0 ^^^ (~~~r24e_0 &&& r0e_0)
  let b4e := r24e_0 ^^^ (~~~r0e_0 &&& r6e_0)
  let b5e := r3e_0 ^^^ (~~~r9e_0 &&& r10e_0)
  let b6e := r9e_0 ^^^ (~~~r10e_0 &&& r16e_0)
  let b7e := r10e_0 ^^^ (~~~r16e_0 &&& r22e_0)
  let b8e := r16e_0 ^^^ (~~~r22e_0 &&& r3e_0)
  let b9e := r22e_0 ^^^ (~~~r3e_0 &&& r9e_0)
  let b10e := r1e_0 ^^^ (~~~r7e_0 &&& r13e_0)
  let b11e := r7e_0 ^^^ (~~~r13e_0 &&& r19e_0)
  let b12e := r13e_0 ^^^ (~~~r19e_0 &&& r20e_0)
  let b13e := r19e_0 ^^^ (~~~r20e_0 &&& r1e_0)
  let b14e := r20e_0 ^^^ (~~~r1e_0 &&& r7e_0)
  let b15e := r4e_0 ^^^ (~~~r5e_0 &&& r11e_0)
  let b16e := r5e_0 ^^^ (~~~r11e_0 &&& r17e_0)
  let b17e := r11e_0 ^^^ (~~~r17e_0 &&& r23e_0)
  let b18e := r17e_0 ^^^ (~~~r23e_0 &&& r4e_0)
  let b19e := r23e_0 ^^^ (~~~r4e_0 &&& r5e_0)
  let b20e := r2e_0 ^^^ (~~~r8e_0 &&& r14e_0)
  let b21e := r8e_0 ^^^ (~~~r14e_0 &&& r15e_0)
  let b22e := r14e_0 ^^^ (~~~r15e_0 &&& r21e_0)
  let b23e := r15e_0 ^^^ (~~~r21e_0 &&& r2e_0)
  let b24e := r21e_0 ^^^ (~~~r2e_0 &&& r8e_0)
  let b0o := (r0o_0 ^^^ (~~~r6o_0 &&& r12o_0)) ^^^ rcO i
  let b1o := r6o_0 ^^^ (~~~r12o_0 &&& r18o_0)
  let b2o := r12o_0 ^^^ (~~~r18o_0 &&& r24o_0)
  let b3o := r18o_0 ^^^ (~~~r24o_0 &&& r0o_0)
  let b4o := r24o_0 ^^^ (~~~r0o_0 &&& r6o_0)
  let b5o := r3o_0 ^^^ (~~~r9o_0 &&& r10o_0)
  let b6o := r9o_0 ^^^ (~~~r10o_0 &&& r16o_0)
  let b7o := r10o_0 ^^^ (~~~r16o_0 &&& r22o_0)
  let b8o := r16o_0 ^^^ (~~~r22o_0 &&& r3o_0)
  let b9o := r22o_0 ^^^ (~~~r3o_0 &&& r9o_0)
  let b10o := r1o_0 ^^^ (~~~r7o_0 &&& r13o_0)
  let b11o := r7o_0 ^^^ (~~~r13o_0 &&& r19o_0)
  let b12o := r13o_0 ^^^ (~~~r19o_0 &&& r20o_0)
  let b13o := r19o_0 ^^^ (~~~r20o_0 &&& r1o_0)
  let b14o := r20o_0 ^^^ (~~~r1o_0 &&& r7o_0)
  let b15o := r4o_0 ^^^ (~~~r5o_0 &&& r11o_0)
  let b16o := r5o_0 ^^^ (~~~r11o_0 &&& r17o_0)
  let b17o := r11o_0 ^^^ (~~~r17o_0 &&& r23o_0)
  let b18o := r17o_0 ^^^ (~~~r23o_0 &&& r4o_0)
  let b19o := r23o_0 ^^^ (~~~r4o_0 &&& r5o_0)
  let b20o := r2o_0 ^^^ (~~~r8o_0 &&& r14o_0)
  let b21o := r8o_0 ^^^ (~~~r14o_0 &&& r15o_0)
  let b22o := r14o_0 ^^^ (~~~r15o_0 &&& r21o_0)
  let b23o := r15o_0 ^^^ (~~~r21o_0 &&& r2o_0)
  let b24o := r21o_0 ^^^ (~~~r2o_0 &&& r8o_0)
  ⟨b0e, b0o, b1e, b1o, b2e, b2o, b3e, b3o, b4e, b4o, b5e, b5o, b6e, b6o, b7e, b7o, b8e, b8o,
    b9e, b9o, b10e, b10o, b11e, b11o, b12e, b12o, b13e, b13o, b14e, b14o, b15e, b15o, b16e, b16o,
    b17e, b17o, b18e, b18o, b19e, b19o, b20e, b20o, b21e, b21o, b22e, b22o, b23e, b23o, b24e, b24o⟩

/-- `loopI2` on the fields of an interleaved state. -/
def loopIS (n : Nat) (i : UInt32) (S : StateI) : StateI :=
  loopI2 n i S.e0 S.o0 S.e1 S.o1 S.e2 S.o2 S.e3 S.o3 S.e4 S.o4 S.e5 S.o5 S.e6 S.o6 S.e7 S.o7
    S.e8 S.o8 S.e9 S.o9 S.e10 S.o10 S.e11 S.o11 S.e12 S.o12 S.e13 S.o13 S.e14 S.o14 S.e15 S.o15
    S.e16 S.o16 S.e17 S.o17 S.e18 S.o18 S.e19 S.o19 S.e20 S.o20 S.e21 S.o21 S.e22 S.o22 S.e23 S.o23
    S.e24 S.o24

theorem keccakPI_eq (S : StateI) : keccakPI S = loopIS 12 0 S := rfl

theorem loopIS_zero (i : UInt32) (S : StateI) : loopIS 0 i S = S := by
  cases S; rfl

theorem loopIS_succ (n : Nat) (i : UInt32) (S : StateI) :
    loopIS (n + 1) i S = loopIS n (i + 2) (roundI (i + 1) (roundI i S)) := by
  cases S
  simp only [loopIS]
  rw [loopI2]
  rfl

set_option maxHeartbeats 4000000 in
theorem roundI_toI (i : UInt32) (h : i.toNat < 24) (A : State) :
    roundI i (toI A) = toI (round ⟨i.toNat, h⟩ A) := by
  cases A
  have h' : i.toNat < ROUNDS := h
  simp only [roundI, toI, round, iota, chi, pi, rho, theta, rc_of i h']
  simp only [ilvE64_xor, ilvO64_xor, ilvE64_andn, ilvO64_andn, rcE_eq i h, rcO_eq i h,
    ilvE64_rotl_0, ilvO64_rotl_0, ilvE64_rotl_1, ilvO64_rotl_1, ilvE64_rotl_2, ilvO64_rotl_2,
    ilvE64_rotl_3, ilvO64_rotl_3, ilvE64_rotl_6, ilvO64_rotl_6, ilvE64_rotl_8, ilvO64_rotl_8,
    ilvE64_rotl_10, ilvO64_rotl_10, ilvE64_rotl_14, ilvO64_rotl_14, ilvE64_rotl_15, ilvO64_rotl_15,
    ilvE64_rotl_18, ilvO64_rotl_18, ilvE64_rotl_20, ilvO64_rotl_20, ilvE64_rotl_21, ilvO64_rotl_21,
    ilvE64_rotl_25, ilvO64_rotl_25, ilvE64_rotl_27, ilvO64_rotl_27, ilvE64_rotl_28, ilvO64_rotl_28,
    ilvE64_rotl_36, ilvO64_rotl_36, ilvE64_rotl_39, ilvO64_rotl_39, ilvE64_rotl_41, ilvO64_rotl_41,
    ilvE64_rotl_43, ilvO64_rotl_43, ilvE64_rotl_44, ilvO64_rotl_44, ilvE64_rotl_45, ilvO64_rotl_45,
    ilvE64_rotl_55, ilvO64_rotl_55, ilvE64_rotl_56, ilvO64_rotl_56, ilvE64_rotl_61, ilvO64_rotl_61,
    ilvE64_rotl_62, ilvO64_rotl_62]

theorem loopIS_toI : ∀ (n : Nat) (i : UInt32) (A : State), i.toNat + 2 * n = 24 →
    loopIS n i (toI A) = toI (keccakF.roundsFrom i.toNat A) := by
  intro n
  induction n with
  | zero => intro i A h; simp at h; rw [loopIS_zero, h, roundsFrom_24]
  | succ n ih =>
    intro i A h
    have hi : i.toNat < 24 := by omega
    have hi1 : (i + 1).toNat < 24 := by rw [toNat_succ i hi]; omega
    have e1 :
        (⟨(i + 1).toNat, hi1⟩ : Fin ROUNDS) = ⟨i.toNat + 1, by show i.toNat + 1 < 24; omega⟩ :=
      Fin.ext (toNat_succ i hi)
    rw [loopIS_succ, roundI_toI i hi, roundI_toI (i + 1) hi1,
      ih (i + 2) _ (by rw [toNat_add2 i (by omega)]; omega), toNat_add2 i (by omega), e1]
    conv => rhs; rw [roundsFrom_succ _ hi, roundsFrom_succ (i.toNat + 1) (by omega)]

theorem keccakPI_toI (A : State) : keccakPI (toI A) = toI (keccakF A) := by
  rw [keccakPI_eq, loopIS_toI 12 0 A (by decide)]
  rfl


end EthLib.Cryptography.Hash.Keccak.Fast
