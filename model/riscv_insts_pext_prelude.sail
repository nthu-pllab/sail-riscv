val pext_write_OV : bits(1) -> unit
function pext_write_OV (b) =
    vxsat = b

val EXTS : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
val EXTZ : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

function EXTS(m, v) = sail_sign_extend(v, m)
function EXTZ(m, v) = sail_zero_extend(v, m)

val neg : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n)) -> bits ('n)
function neg (v) = not_vec(v) + 1

val abs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n)) -> bits('n)
function abs (v) =
  if v <_s zeros('n) then { pext_write_OV (0b1); neg(v) }
  else v

val sabs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n)) -> bits('n)
function sabs (v) =
  let lb : bits('n) = not_vec(sail_ones ('n) >> 1) in
  if v == lb then { pext_write_OV (0b1); not_vec(lb) }
  else if v <_s zeros('n) then { pext_write_OV (0b1); neg(v) }
  else v

val shift_left_logic : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function shift_left_logic (v, m) =
  let extv : bits(xlen + 32) = EXTZ (v) in
  slice (extv << m, 0, 'n)

val shift_right_logic : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function shift_right_logic (v, m) =
  let extv : bits(xlen + 65) = EXTZ (v) in
  slice (extv >> m, 0, 'n)

val sat_shift_left_arith : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function sat_shift_left_arith (v, m) =
  let ub : bits(xlen + 32) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(xlen + 32) = not_vec (ub) in
  let vext : bits(xlen + 32) = EXTS(v) in
  let shiftext : bits(xlen + 32) = vext << m in
  if shiftext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s shiftext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (shiftext, 0, 'n) }

val shift_right_arith : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 |'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function shift_right_arith (v, m) =
  let extv : bits(xlen + 65) = EXTS (v) in
  slice (extv >> m, 0, 'n)

val shift_right_arith_rounding : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function shift_right_arith_rounding (v, m) =
  if m == 0x00 then v
  else let res : bits(65) = add_bits(EXTS(shift_right_arith(v, m - 0x01)), EXTZ(0b1)) in
  slice(res >> 1, 0, 'n)

// TODO: It seems we have to set the OV flag in `ssha` and `sshar`

val ssha : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function ssha (v, m) =
  let rev : bits(8) = if m <_s 0x00 then not_vec (m) + 0x01 else m in
  let sa : bits(8) = if rev == to_bits(8, 'n) then to_bits(8, 'n) - 0x01 else rev in
  if m <_s 0x00 then shift_right_arith(v, sa)
  else shift_left_logic(v, sa)

val sshar : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function sshar (v, m) =
  let rev : bits(8) = if m <_s 0x00 then not_vec (m) + 0x01 else m in
  let sa : bits(8) = if rev == to_bits(8, 'n) then to_bits(8, 'n) - 0x01 else rev in
  if m <_s 0x00 then shift_right_arith_rounding(v, sa)
  else shift_left_logic(v, sa)

// TODO: The below `sha` & `shar` functions are not in the original proposal and lack pseudo-code presentation.
// Therefore, be prepared that these 2 functions are incorrectly implemented.

val sha : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function sha (v, m) =
  let rev : bits(8) = if m <_s 0x00 then not_vec (m) + 0x01 else m in
  if m <_s 0x00 then shift_right_arith(v, rev)
  else shift_left_logic(v, rev)

val shar : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), bits(8)) -> bits ('n)
function shar (v, m) =
  let rev : bits(8) = if m <_s 0x00 then not_vec (m) + 0x01 else m in
  if m <_s 0x00 then shift_right_arith_rounding(v, rev)
  else shift_left_logic(v, rev)

val sadd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function sadd (v1, v2) =
  let ub : bits(66) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(66) = not_vec (ub) in
  let v1ext : bits(66) = EXTS(v1) in
  let v2ext : bits(66) = EXTS(v2) in
  let sumext = v1ext + v2ext in
  if sumext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s sumext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (sumext, 0, 'n) }

val saddu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function saddu (v1, v2) =
  let ub : bits(66) = EXTZ(sail_ones ('n)) in
  let v1ext : bits(66) = EXTZ(v1) in
  let v2ext : bits(66) = EXTZ(v2) in
  let sumext = v1ext + v2ext in
  if ub <_u sumext then { pext_write_OV (0b1); ones('n) }
  else { slice (sumext, 0, 'n) }

val aadd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function aadd (v1, v2) =
  let v1ext : bits(66) = EXTS(v1) in
  let v2ext : bits(66) = EXTS(v2) in
  slice ((v1ext + v2ext) >> 1, 0, 'n)

val aaddu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function aaddu (v1, v2) =
  let v1ext : bits(66) = EXTZ(v1) in
  let v2ext : bits(66) = EXTZ(v2) in
  slice ((v1ext + v2ext) >> 1, 0, 'n)

val ssub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function ssub (v1, v2) =
  let ub : bits(66) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(66) = not_vec (ub) in
  let v1ext : bits(66) = EXTS(v1) in
  let v2ext : bits(66) = EXTS(v2) in
  let diffext = v1ext - v2ext in
  if diffext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s diffext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (diffext, 0, 'n) }

val asub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function asub (v1, v2) =
  let v1ext : bits(66) = EXTS(v1) in
  let v2ext : bits(66) = EXTS(v2) in
  slice ((v1ext - v2ext) >> 1, 0, 'n)

// TODO: This was called `uksub` but was likely wrongly implemented, so I (sashiue) changed it. Double check it.
val ssubu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function ssubu (v1, v2) =
  let v1ext : bits(66) = EXTZ(v1) in
  let v2ext : bits(66) = EXTZ(v2) in
  let diffext = v1ext - v2ext in
  if diffext <_s zeros(66) then { pext_write_OV (0b1); zeros('n) }
  else { slice (diffext, 0, 'n) }

val asubu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function asubu (v1, v2) =
  let v1ext : bits(66) = EXTZ(v1) in
  let v2ext : bits(66) = EXTZ(v2) in
  slice ((v1ext - v2ext) >> 1, 0, 'n)