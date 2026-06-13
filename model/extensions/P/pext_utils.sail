/*val pext_write_OV : bits(1) -> unit
function pext_write_OV (b) =
  vxsat = b*/

val neg : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n)) -> bits ('n)
function neg (v) = not_vec(v) + 1

val count_leading_sign_bits : forall 'n, 'n == 32 | 'n == 64. (bits('n)) -> range(0, 'n)
function count_leading_sign_bits(x) = {
  var count : range(0, 'n) = 0;
  var continue : bool = true;
  let msb : bit = x['n - 1];

  foreach (i from ('n - 1) downto 0) {
    if x[i] == msb & continue then {
      let new_count = count + 1;
      assert(new_count <= 'n);
      count = new_count;
    } else {
      continue = false;
    }
  };
  count
}

val abs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64. (bits('n)) -> (bits('n))
function abs(x) = {
  var res : bits('n) = x;

  if res['n - 1] == bitone then {
    res = ~(res) + zero_extend(0b1);
  };

  res
}

val sabs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n)) -> bits('n)
function sabs (v) =
  let lb : bits('n) = not_vec(ones('n) >> 1) in
  if v == lb then { /*pext_write_OV(0b1);*/ not_vec(lb) }
  else if v <_s zeros('n) then { /*pext_write_OV(0b1);*/ neg(v) }
  else v

val shift_left_arith : forall 'm, ('m == 8 | 'm == 16 | 'm == 32 | 'm == 64).
  (bits ('m), nat) -> bits ('m)
function shift_left_arith (value, shift) =
  let ub : bits(xlen + 256) = sign_extend(ones('m) >> 1) in
  let lb : bits(xlen + 256) = not_vec(ub) in
  let vext : bits(xlen + 256) = sign_extend(value) in
  let shiftext : bits(xlen + 256) = vext << shift in
  if shiftext <_s lb then ones('m)
  else slice(shiftext, 0, 'm)

val sat_shift_left_arith : forall 'm, ('m == 8 | 'm == 16 | 'm == 32 | 'm == 64).
  (bits ('m), nat) -> bits ('m)
function sat_shift_left_arith (value, shift) =
  let ub : bits(xlen + 256) = sign_extend(ones('m) >> 1) in
  let lb : bits(xlen + 256) = not_vec(ub) in
  let vext : bits(xlen + 256) = sign_extend(value) in
  let shiftext : bits(xlen + 256) = vext << shift in
  if shiftext <_s lb then { /*pext_write_OV(0b1);*/ not_vec(ones('m) >> 1) }
  else if ub <_s shiftext then { /*pext_write_OV(0b1);*/ ones('m) >> 1 }
  else slice(shiftext, 0, 'm)

val sat_shift_left_logic : forall 'm, ('m == 8 | 'm == 16 | 'm == 32 | 'm == 64).
  (bits ('m), nat) -> bits ('m)
function sat_shift_left_logic (value, shift) =
  let ub : bits(xlen + 256) = zero_extend(ones('m)) in
  let vext : bits(xlen + 256) = zero_extend(value) in
  let shiftext : bits(xlen + 256) = vext << shift in
  if ub <_s shiftext then { /*pext_write_OV(0b1);*/ ones('m) }
  else slice(shiftext, 0, 'm)

val shift_right_arith_rounding : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64 | 'n == 128.
  (bits ('n), nat) -> bits ('n)
function shift_right_arith_rounding (value, shift) =
  if shift == 0 then value
  else let res : bits(257) = add_bits(sign_extend(shift_right_arith(value @ 0b0, shift)), zero_extend(0b1)) in
  slice(res, 1, 'n)

val shift_right_logic_rounding : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64 | 'n == 128.
  (bits ('n), nat) -> bits ('n)
function shift_right_logic_rounding (value, shift) =
  if shift == 0 then value
  else let res : bits(257) = add_bits(zero_extend((value @ 0b0) >> shift), zero_extend(0b1)) in
  slice(res, 1, 'n)

val ssha : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), int) -> bits ('n)
function ssha (value, shift) =
  if shift < 0 then shift_right_arith(value, -shift)
  else sat_shift_left_arith(value, shift)

val sshar : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), int) -> bits ('n)
function sshar (value, shift) =
  if shift < 0 then shift_right_arith_rounding(value, -shift)
  else sat_shift_left_arith(value, shift)

val sshl : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), int) -> bits ('n)
function sshl (value, shift) =
  if shift < 0 then value >> -shift
  else sat_shift_left_logic(value, shift)

val sshlr : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), int) -> bits ('n)
function sshlr (value, shift) =
  if shift < 0 then shift_right_logic_rounding(value, -shift)
  else sat_shift_left_logic(value, shift)

val sha : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), int) -> bits ('n)
function sha (value, shift) =
  if shift < 0 then shift_right_arith(value, -shift)
  else shift_left_arith(value, shift)

val shar : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), int) -> bits ('n)
function shar (value, shift) =
  if shift < 0 then shift_right_arith_rounding(value, -shift)
  else shift_left_arith(value, shift)

val shl : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), int) -> bits ('n)
function shl (value, shift) =
  if shift < 0 then value >> -shift
  else value << shift

val shlr : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), int) -> bits ('n)
function shlr (value, shift) =
  if shift < 0 then shift_right_logic_rounding(value, -shift)
  else value << shift

val sadd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function sadd (v1, v2) =
  let ub : bits(66) = sign_extend(ones('n) >> 1) in
  let lb : bits(66) = not_vec (ub) in
  let v1ext : bits(66) = sign_extend(v1) in
  let v2ext : bits(66) = sign_extend(v2) in
  let sumext = v1ext + v2ext in
  if sumext <_s lb then { /*pext_write_OV(0b1);*/ not_vec (ones ('n) >> 1) }
  else if ub <_s sumext then { /*pext_write_OV(0b1);*/ ones ('n) >> 1 }
  else { slice (sumext, 0, 'n) }

val saddu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function saddu (v1, v2) =
  let ub : bits(66) = zero_extend(ones('n)) in
  let v1ext : bits(66) = zero_extend(v1) in
  let v2ext : bits(66) = zero_extend(v2) in
  let sumext = v1ext + v2ext in
  if ub <_u sumext then { /*pext_write_OV(0b1);*/ ones('n) }
  else { slice (sumext, 0, 'n) }

val aadd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function aadd (v1, v2) =
  let v1ext : bits(66) = sign_extend(v1) in
  let v2ext : bits(66) = sign_extend(v2) in
  slice ((v1ext + v2ext) >> 1, 0, 'n)

val aaddu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function aaddu (v1, v2) =
  let v1ext : bits(66) = zero_extend(v1) in
  let v2ext : bits(66) = zero_extend(v2) in
  slice ((v1ext + v2ext) >> 1, 0, 'n)

val ssub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function ssub (v1, v2) =
  let ub : bits(66) = sign_extend(ones('n) >> 1) in
  let lb : bits(66) = not_vec (ub) in
  let v1ext : bits(66) = sign_extend(v1) in
  let v2ext : bits(66) = sign_extend(v2) in
  let diffext = v1ext - v2ext in
  if diffext <_s lb then { /*pext_write_OV(0b1);*/ not_vec (ones ('n) >> 1) }
  else if ub <_s diffext then { /*pext_write_OV(0b1);*/ ones ('n) >> 1 }
  else { slice (diffext, 0, 'n) }

val asub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function asub (v1, v2) =
  let v1ext : bits(66) = sign_extend(v1) in
  let v2ext : bits(66) = sign_extend(v2) in
  slice ((v1ext - v2ext) >> 1, 0, 'n)

// TODO: This was called `uksub` but was likely wrongly implemented, so I (sashiue) changed it. Double check it.
val ssubu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function ssubu (v1, v2) =
  let v1ext : bits(66) = zero_extend(v1) in
  let v2ext : bits(66) = zero_extend(v2) in
  let diffext = v1ext - v2ext in
  if diffext <_s zeros(66) then { /*pext_write_OV(0b1);*/ zeros('n) }
  else { slice (diffext, 0, 'n) }

val asubu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function asubu (v1, v2) =
  let v1ext : bits(66) = zero_extend(v1) in
  let v2ext : bits(66) = zero_extend(v2) in
  slice ((v1ext - v2ext) >> 1, 0, 'n)

val muls : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits(2 * 'n)
function muls (v1, v2) =
  to_bits_truncate (2 * 'n, signed(v1) * signed(v2))

val mulu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits(2 * 'n)
function mulu (v1, v2) =
  to_bits_truncate (2 * 'n, unsigned(v1) * unsigned(v2))

val mulsu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits(2 * 'n)
function mulsu (v1, v2) =
 to_bits_truncate (2 * 'n, signed(v1) * unsigned(v2))

val mulh : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function mulh (v1, v2) =
  slice(shift_right_arith(muls(v1, v2), 'n), 0, 'n)

val mulhu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function mulhu (v1, v2) =
  slice(mulu(v1, v2) >> 'n, 0, 'n)

val mulhr : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function mulhr (v1, v2) =
  slice(shift_right_arith_rounding(muls(v1, v2), 'n), 0, 'n)

val mulhru : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function mulhru (v1, v2) =
  slice(shift_right_logic_rounding(mulu(v1, v2), 'n), 0, 'n)

val mulhsu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function mulhsu (v1, v2) =
  slice(shift_right_arith(mulsu(v1, v2), 'n), 0, 'n)

val mulhrsu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function mulhrsu (v1, v2) =
  slice(shift_right_logic_rounding(mulsu(v1, v2), 'n), 0, 'n)

val mulq : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits(2 * 'n)
function mulq (v1, v2) =
  shift_right_arith(muls(v1, v2), 'n - 1)

val mulq_sat : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits(2 * 'n)
function mulq_sat (v1, v2) =
  let lb : bits(66) = not_vec(sign_extend(ones ('n) >> 1)) in
  if (sign_extend(v1) == lb) & (sign_extend(v2) == lb) then sign_extend(ones ('n) >> 1)
  else shift_right_arith(muls(v1, v2), 'n - 1)

val mulqr : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits(2 * 'n)
function mulqr (v1, v2) =
  shift_right_arith_rounding(muls(v1, v2), 'n - 1)

val mulqr_sat : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits(2 * 'n)
function mulqr_sat (v1, v2) =
  let lb : bits(66) = not_vec(sign_extend(ones ('n) >> 1)) in
  if (sign_extend(v1) == lb) & (sign_extend(v2) == lb) then sign_extend(ones ('n) >> 1)
  else shift_right_arith_rounding(muls(v1, v2), 'n - 1)

val mseq : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function mseq (v1, v2) =
  if v1 == v2 then ones() else zeros()

val mslt : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function mslt (v1, v2) =
  if v1 <_s v2 then ones() else zeros()

val msltu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function msltu (v1, v2) =
  if v1 <_u v2 then ones() else zeros()

val mins : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function mins (v1, v2) =
  if v1 <_s v2 then v1 else v2

val minu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function minu (v1, v2) =
  if v1 <_u v2 then v1 else v2

val maxs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function maxs (v1, v2) =
  if v1 >_s v2 then v1 else v2

val maxu : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function maxu (v1, v2) =
  if v1 >_u v2 then v1 else v2

val nclips : forall 'n 'm, ('n == 8 | 'n == 16 | 'n == 32 | 'n == 64) & 'n == 'm * 2.
  (implicit('m), bits('n), nat) -> bits('m)
function nclips (m, value, shift) =
  let ub : bits('n) = sign_extend(ones ('m) >> 1) in
  let lb : bits('n) = not_vec (ub) in
  let shiftext : bits('n) = shift_right_arith(value, shift) in
  if shiftext <_s lb then lb[('m - 1)..0]
  else if ub <_s shiftext then ub[('m - 1)..0]
  else shiftext[('m - 1)..0]

val nclipu : forall 'n 'm, ('n == 8 | 'n == 16 | 'n == 32 | 'n == 64) & 'n == 'm * 2.
  (implicit('m), bits('n), nat) -> bits('m)
function nclipu (m, value, shift) =
  let ub : bits('n) = zero_extend(ones ('m)) in
  let shiftext : bits('n) = value >> shift in
  if ub <_u shiftext then ub[('m - 1)..0]
  else shiftext[('m - 1)..0]

val ncliprs : forall 'n 'm, ('n == 8 | 'n == 16 | 'n == 32 | 'n == 64) & 'n == 'm * 2.
  (implicit('m), bits('n), nat) -> bits('m)
function ncliprs (m, value, shift) =
  let ub : bits('n) = sign_extend(ones ('m) >> 1) in
  let lb : bits('n) = not_vec (ub) in
  let shiftext : bits('n) = shift_right_arith_rounding(value, shift) in
  if shiftext <_s lb then slice (lb, 0, 'm)
  else if ub <_s shiftext then slice (ub, 0, 'm)
  else slice (shiftext, 0, 'm)

val nclipru : forall 'n 'm, ('n == 8 | 'n == 16 | 'n == 32 | 'n == 64) & 'n == 'm * 2.
  (implicit('m), bits('n), nat) -> bits('m)
function nclipru (m, value, shift) =
  let ub : bits('n) = zero_extend(ones ('m)) in
  let shiftext : bits('n) = shift_right_logic_rounding(value, shift) in
  if ub <_u shiftext then slice (ub, 0, 'm)
  else slice (shiftext, 0, 'm)
