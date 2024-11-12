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

val abs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
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

/* ****************************************************************** */

union clause ast = PEXT_SIMPLE : (regidx, regidx, psimple)

mapping clause encdec = PEXT_SIMPLE(rs1, rd, CLS) <->
  0b01100 @ 0b0000011 @ rs1 @ 0b001 @ rd @ 0b0010011
mapping clause encdec = PEXT_SIMPLE(rs1, rd, CLSW) if sizeof(xlen) == 64 <->
  0b01100 @ 0b0000011 @ rs1 @ 0b001 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SIMPLE(rs1, rd, ABS) <->
  0b01100 @ 0b0000111 @ rs1 @ 0b001 @ rd @ 0b0010011
mapping clause encdec = PEXT_SIMPLE(rs1, rd, ABSW) if sizeof(xlen) == 64 <->
  0b01100 @ 0b0000111 @ rs1 @ 0b001 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV) if sizeof(xlen) == 32 <->
  0b01101 @ 0b0011111 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV) if sizeof(xlen) == 64 <->
  0b01101 @ 0b0111111 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV8) if sizeof(xlen) == 32 <->
  0b01101 @ 0b0011000 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV8) if sizeof(xlen) == 64 <->
  0b01101 @ 0b0111000 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV16) if sizeof(xlen) == 64 <->
  0b01101 @ 0b0110000 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 64

function clause execute (PEXT_SIMPLE(rs1, rd, op)) = {
  match op {
    CLS => {
      let rs1_val = X(rs1);
      var result : nat = 0;
      var done : bool = false;
      foreach (i from (sizeof(xlen) - 2) downto 0)
        if not(done) then if rs1_val[i] == rs1_val[sizeof(xlen) - 1]
                        then result = result + 1
                        else done = true;
      X(rd) = to_bits(sizeof(xlen), result);
    },
    CLSW => {
      let rs1_val = X(rs1);
      var result : nat = 0;
      var done : bool = false;
      foreach (i from 30 downto 0)
        if not(done) then if rs1_val[i] == rs1_val[31]
                        then result = result + 1
                        else done = true;
      X(rd) = to_bits(sizeof(xlen), result);
    },
    ABS => X(rd) = not_vec(X(rs1)) + 1,
    ABSW => { // TODO: Double check if this is correct.
      let rs1_val = X(rs1);
      let rs1_word = slice(rs1_val, 0, 32);
      let result : xlenbits = EXTZ (not_vec(rs1_word) + 1);
      X(rd) = result;
    },
    REV => {
      let rs1_val = X(rs1);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 1))
        result[i] = rs1_val[(sizeof(xlen) - i - 1)];
      X(rd) = result;
    },
    REV8 => {
      let rs1_val = X(rs1);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 8) by 8)
        result[(i + 7) .. i] = rs1_val[(sizeof(xlen) - i - 1) .. (sizeof(xlen) - i - 8)];
      X(rd) = result;
    },
    REV16 => {
      let rs1_val = X(rs1);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 16) by 16)
        result[(i + 15) .. i] = rs1_val[(sizeof(xlen) - i - 1) .. (sizeof(xlen) - i - 16)];
      X(rd) = result;
    }
  };
  RETIRE_SUCCESS
}

mapping p_simple_mapping : psimple <-> string = {
  CLS <-> "cls",
  CLSW <-> "clsw",
  ABS <-> "abs",
  REV <-> "rev",
  REV8 <-> "rev8",
  REV16 <-> "rev16"
}

mapping clause assembly = PEXT_SIMPLE(rs1, rd, p_inst)
  <-> p_simple_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_LEFT_B : (bits(3), regidx, regidx, pshift_left_b)

mapping clause encdec = PEXT_SHIFT_LEFT_B(imm3, rs1, rd, PSLLI_B) <->
  0b1 @ 0b000 @ 0b0 @ 0b0001 @ imm3 @ rs1 @ 0b010 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_LEFT_B(imm3, rs1, rd, op)) = {
  match op {
    PSLLI_B => {
      let rs1_val = X(rs1);
      let sa : bits(8) = EXTZ(imm3);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = shift_left_logic(rs1_byte, sa)
      };
      X(rd) = result;
    }
  };
  RETIRE_SUCCESS
}

mapping p_shift_b_mapping : pshift_left_b <-> string = {
  PSLLI_B <-> "pslli.b"
}

mapping clause assembly = PEXT_SHIFT_LEFT_B(imm3, rs1, rd, p_inst)
  <-> p_shift_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_3(imm3)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_LEFT_W_RV64 : (bits(5), regidx, regidx, pshift_left_w_rv64)

mapping clause encdec = PEXT_SHIFT_LEFT_W_RV64(imm5, rs1, rd, PSLLI_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b000 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SHIFT_LEFT_W_RV64(imm5, rs1, rd, PSSLAI_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_SHIFT_LEFT_W_RV64(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    result[(i+31)..i] = match op {
      PSLLI_W => shift_left_logic(rs1_word, sa),
      PSSLAI_W => sat_shift_left_arith(rs1_word, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_w_rv64_mapping : pshift_left_w_rv64 <-> string = {
  PSLLI_W <-> "pslli.w",
  PSSLAI_W <-> "psslai.w"
}

mapping clause assembly = PEXT_SHIFT_LEFT_W_RV64(imm5, rs1, rd, p_inst)
  <-> p_shift_w_rv64_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_LEFT_W_RV32 : (bits(5), regidx, regidx, pshift_left_w_rv32)

mapping clause encdec = PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, SSLAI) if sizeof(xlen) == 32 <->
  0b1 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 32

function clause execute (PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  X(rd) = sat_shift_left_arith(rs1_val, sa);
  RETIRE_SUCCESS
}

mapping p_shift_w_rv32_mapping : pshift_left_w_rv32 <-> string = {
  SSLAI <-> "sslai"
}

mapping clause assembly = PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, p_inst)
  <-> p_shift_w_rv32_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_LEFT_H : (bits(4), regidx, regidx, pshift_left_h)

mapping clause encdec = PEXT_SHIFT_LEFT_H(imm4, rs1, rd, PSLLI_H) <->
  0b1 @ 0b000 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_LEFT_H(imm4, rs1, rd, PSSLAI_H) <->
  0b1 @ 0b101 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b010 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_LEFT_H(imm4, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm4);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    result[(i+15)..i] = match op {
      PSLLI_H => shift_left_logic(rs1_halfword, sa),
      PSSLAI_H => sat_shift_left_arith(rs1_halfword, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_h_mapping : pshift_left_h <-> string = {
  PSLLI_H <-> "pslli.h",
  PSSLAI_H <-> "psslai.h"
}

mapping clause assembly = PEXT_SHIFT_LEFT_H(imm4, rs1, rd, p_inst)
  <-> p_shift_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_4(imm4)

// TODO: Figure out PLI and PLUI and implement them.

/* ****************************************************************** */

union clause ast = PEXT_PS : (regidx, regidx, p_ps)

mapping clause encdec = PEXT_PS(rs1, rd, PSABS_B) <->
  0b11100 @ 0b10 @ 0b00111 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSABS_H) <->
  0b11100 @ 0b00 @ 0b00111 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSEXTB_H) <->
  0b11100 @ 0b00 @ 0b00100 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSEXTB_W) if sizeof(xlen) == 64 <->
  0b11100 @ 0b01 @ 0b00100 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_PS(rs1, rd, PSEXTH_W) if sizeof(xlen) == 64 <->
  0b11100 @ 0b01 @ 0b00101 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_PS(rs1, rd, op)) = { // TODO: Double check if this is correct.
  let rs1_val = X(rs1);
  var result : xlenbits = zeros();
  match op {
    PSABS_B => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = sabs(rs1_byte)
      };
    },
    PSABS_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = sabs(rs1_halfword)
      };
    },
    PSEXTB_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = EXTS(rs1_val[7..0])
      };  
    },
    PSEXTB_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[7..0])
      };  
    },
    PSEXTH_W => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[15..0])
      };  
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_ps_mapping : p_ps <-> string = {
  PSABS_B <-> "psabs.b",
  PSABS_H <-> "psabs.h",
  PSEXTB_H <-> "psextb.h",
  PSEXTB_W <-> "psextb.w",
  PSEXTH_W <-> "psexth.w"
}

mapping clause assembly = PEXT_PS(rs1, rd, p_inst)
  <-> p_ps_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

/* ****************************************************************** */

union clause ast = PEXT_ADD_SHIFT : (regidx, regidx, regidx, p_add_shift)

mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_B_B0) <->
  0b1 @ 0b000 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_B_B0) <->
  0b1 @ 0b001 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_H_H0) <->
  0b1 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_H_H0) <->
  0b1 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHA_H_H0) <->
  0b1 @ 0b110 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHAR_H_H0) <->
  0b1 @ 0b111 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSLL_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PADD_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b001 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHA_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, PSSHAR_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, SSHA) if sizeof(xlen) == 32 <->
  0b1 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, SSHAR) if sizeof(xlen) == 32 <->
  0b1 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, SHA) if sizeof(xlen) == 64 <->
  0b1 @ 0b110 @ 0b1 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ADD_SHIFT(rs1, rs2, rd, SHAR) if sizeof(xlen) == 64 <->
  0b1 @ 0b111 @ 0b1 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_ADD_SHIFT(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  match op {
    PSLL_B_B0 => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        result[(i+7)..i] = shift_left_logic(rs1_val[(i+7)..i], EXTZ(rs2_val[2..0]))
      };
    },
    PADD_B_B0 => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        result[(i+7)..i] = rs1_val[(i+7)..i] + rs2_val[(i+7)..i]
      };
    },
    PSLL_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = shift_left_logic(rs1_val[(i+15)..i], EXTZ(rs2_val[3..0]))
      };
    },
    PADD_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = rs1_val[(i+15)..i] + rs2_val[(i+15)..i]
      };
    },
    PSSHA_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = ssha(rs1_val[(i+15)..i], EXTS(rs2_val[4..0]))
      };
    },
    PSSHAR_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = sshar(rs1_val[(i+15)..i], EXTS(rs2_val[4..0]))
      };
    },
    PSLL_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = shift_left_logic(rs1_val[(i+31)..i], EXTZ(rs2_val[4..0]))
      };
    },
    PADD_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = rs1_val[(i+31)..i] + rs2_val[(i+31)..i]
      };
    },
    PSSHA_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = ssha(rs1_val[(i+31)..i], EXTS(rs2_val[5..0]))
      };
    },
    PSSHAR_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = sshar(rs1_val[(i+31)..i], EXTS(rs2_val[5..0]))
      };
    },
    SSHA => result = ssha(rs1_val, EXTS(rs2_val[5..0])),
    SSHAR => result = sshar(rs1_val, EXTS(rs2_val[5..0])),
    SHA => result = sha(rs1_val, EXTS(rs2_val[5..0])),
    SHAR => result = shar(rs1_val, EXTS(rs2_val[5..0]))
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_add_shift_mapping : p_add_shift <-> string = {
  PSLL_B_B0 <-> "psll.b.b0",
  PADD_B_B0 <-> "padd.b.b0",
  PSLL_H_H0 <-> "psll.h.h0",
  PADD_H_H0 <-> "padd.h.h0",
  PSSHA_H_H0 <-> "pssha.h.h0",
  PSSHAR_H_H0 <-> "psshar.h.h0",
  PSLL_W_W0 <-> "psll.w.w0",
  PADD_W_W0 <-> "padd.w.w0",
  PSSHA_W_W0 <-> "pssha.w.w0",
  PSSHAR_W_W0 <-> "psshar.w.w0",
  SSHA <-> "ssha",
  SSHAR <-> "sshar",
  SHA <-> "sha",
  SHAR <-> "shar"
}

mapping clause assembly = PEXT_ADD_SHIFT(rs1, rs2, rd, p_inst)
  <-> p_add_shift_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_B : (bits(3), regidx, regidx, p_shift_sat_b)

mapping clause encdec = PEXT_SHIFT_SAT_B(imm3, rs1, rd, PSRLI_B) <->
  0b1 @ 0b000 @ 0b0 @ 0b0001 @ imm3 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_B(imm3, rs1, rd, PSRAI_B) <->
  0b1 @ 0b000 @ 0b0 @ 0b0001 @ imm3 @ rs1 @ 0b100 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_SAT_B(imm3, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm3);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    result[(i+7)..i] = match op {
      PSRLI_B => shift_right_logic(rs1_byte, sa),
      PSRAI_B => shift_right_arith(rs1_byte, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sat_b_mapping : p_shift_sat_b <-> string = {
  PSRLI_B <-> "psrli.b",
  PSRAI_B <-> "psrai.b"
}

mapping clause assembly = PEXT_SHIFT_SAT_B(imm3, rs1, rd, p_inst)
  <-> p_shift_sat_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_3(imm3)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_H : (bits(4), regidx, regidx, p_shift_sat_h)

mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PSRLI_H) <->
  0b1 @ 0b000 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PUSATI_H) <->
  0b1 @ 0b010 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PSRAI_H) <->
  0b1 @ 0b100 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PSRARI_H) <->
  0b1 @ 0b101 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PSATI_H) <->
  0b1 @ 0b110 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_SAT_H(imm4, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm4);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    result[(i+15)..i] = match op {
      PSRLI_H => shift_right_logic(rs1_halfword, sa),
      PUSATI_H =>
        let maxval : bits(16) = ~(0xFFFF << sa) in
        if (rs1_halfword <_s 0x0000) then 0x0000
        else if (rs1_halfword >_s maxval) then maxval else rs1_halfword,
      PSRAI_H => shift_right_arith(rs1_halfword, sa),
      PSRARI_H => shift_right_arith_rounding(rs1_halfword, sa),
      PSATI_H =>
        let minval : bits(16) = 0xFFFF << sa in
        let maxval = ~(minval) in
        if (rs1_halfword <_s minval) then minval
        else if (rs1_halfword >_s maxval) then maxval else rs1_halfword,
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sat_h_mapping : p_shift_sat_h <-> string = {
  PSRLI_H <-> "psrli.h",
  PUSATI_H <-> "pusati.h",
  PSRAI_H <-> "psrai.h",
  PSRARI_H <-> "psrari.h",
  PSATI_H <-> "psati.h"
}

mapping clause assembly = PEXT_SHIFT_SAT_H(imm4, rs1, rd, p_inst)
  <-> p_shift_sat_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_4(imm4)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_W : (bits(5), regidx, regidx, p_shift_sat_w)

mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PSRLI_W) <->
  0b1 @ 0b000 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PUSATI_W) <->
  0b1 @ 0b010 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PSRAI_W) <->
  0b1 @ 0b100 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PSRARI_W) <->
  0b1 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PSATI_W) <->
  0b1 @ 0b110 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_SAT_W(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    result[(i+31)..i] = match op {
      PSRLI_W => shift_right_logic(rs1_word, sa),
      PUSATI_W =>
        let maxval : bits(32) = ~(0xFFFFFFFF << sa) in
        if (rs1_word <_s 0x00000000) then 0x00000000
        else if (rs1_word >_s maxval) then maxval else rs1_word,
      PSRAI_W => shift_right_arith(rs1_word, sa),
      PSRARI_W => shift_right_arith_rounding(rs1_word, sa),
      PSATI_W =>
        let minval : bits(32) = 0xFFFFFFFF << sa in
        let maxval = ~(minval) in
        if (rs1_word <_s minval) then minval
        else if (rs1_word >_s maxval) then maxval else rs1_word,
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sat_w_mapping : p_shift_sat_w <-> string = {
  PSRLI_W <-> "psrli.w",
  PUSATI_W <-> "pusati.w",
  PSRAI_W <-> "psrai.w",
  PSRARI_W <-> "psrari.w",
  PSATI_W <-> "psati.w"
}

mapping clause assembly = PEXT_SHIFT_SAT_W(imm5, rs1, rd, p_inst)
  <-> p_shift_sat_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SUM : (regidx, regidx, regidx, p_shift_sum)

mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRL_B_B0) <->
  0b1 @ 0b000 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRA_B_B0) <->
  0b1 @ 0b100 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRL_H_H0) <->
  0b1 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRA_H_H0) <->
  0b1 @ 0b100 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRL_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRA_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b100 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PREDSUM_H) <->
  0b1 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PREDSUMU_H) <->
  0b1 @ 0b011 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PREDSUM_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b001 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PREDSUMU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b011 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_SHIFT_SUM(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  match op {
    PSRL_B_B0 => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = shift_right_logic(rs1_byte, EXTZ(rs2_val[2..0]));
      };
    },
    PSRA_B_B0 => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = shift_right_arith(rs1_byte, EXTZ(rs2_val[2..0]));
      };
    },
    PSRL_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = shift_right_logic(rs1_halfword, EXTZ(rs2_val[3..0]));
      };
    },
    PSRA_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = shift_right_arith(rs1_halfword, EXTZ(rs2_val[3..0]));
      };
    },
    PSRL_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = slice(rs1_val, i, 32);
        result[(i+31)..i] = shift_right_logic(rs1_word, EXTZ(rs2_val[4..0]));
      };
    },
    PSRA_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = slice(rs1_val, i, 32);
        result[(i+31)..i] = shift_right_arith(rs1_word, EXTZ(rs2_val[4..0]));
      };
    },
    PREDSUM_H => {
      let s1 = X(rs1);
      var sum : bits(xlen) = X(rs2);
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
          let s1_h = s1[(i+15)..i];
          sum = sum + EXTS(sizeof(xlen), s1_h);
      };
      result = sum;
    },
    PREDSUMU_H => {
      let s1 = X(rs1);
      var sum : bits(xlen) = X(rs2);
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
          let s1_h = s1[(i+15)..i];
          sum = sum + EXTZ(sizeof(xlen), s1_h);
      };
      result = sum;
    },
    PREDSUM_W => {
      let s1 = X(rs1);
      var sum : bits(xlen) = X(rs2);
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
          let s1_h = s1[(i+31)..i];
          sum = sum + EXTS(sizeof(xlen), s1_h);
      };
      result = sum;
    },
    PREDSUMU_W => {
      let s1 = X(rs1);
      var sum : bits(xlen) = X(rs2);
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
          let s1_h = s1[(i+31)..i];
          sum = sum + EXTZ(sizeof(xlen), s1_h);
      };
      result = sum;
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sum_mapping : p_shift_sum <-> string = {
  PSRL_B_B0 <-> "psrl.b.b0",
  PSRA_B_B0 <-> "psra.b.b0",
  PSRL_H_H0 <-> "psrl.h.h0",
  PSRA_H_H0 <-> "psra.h.h0",
  PSRL_W_W0 <-> "psrl.w.w0",
  PSRA_W_W0 <-> "psra.w.w0",
  PREDSUM_H <-> "predsum.h",
  PREDSUMU_H <-> "predsumu.h",
  PREDSUM_W <-> "predsum.w",
  PREDSUMU_W <-> "predsumu.w"
}

mapping clause assembly = PEXT_SHIFT_SUM(rs1, rs2, rd, p_inst)
  <-> p_shift_sum_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY_B : (regidx, regidx, regidx, p_elementary_b)

mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PADD_B) <->
  0b1 @ 0b0000 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSADD_B) <->
  0b1 @ 0b0010 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PAADD_B) <->
  0b1 @ 0b0011 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSADDU_B) <->
  0b1 @ 0b0110 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PAADDU_B) <->
  0b1 @ 0b0010 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSUB_B) <->
  0b1 @ 0b1000 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PDIF_B) <->
  0b1 @ 0b1001 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSSUB_B) <->
  0b1 @ 0b1010 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PASUB_B) <->
  0b1 @ 0b1011 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PDIFU_B) <->
  0b1 @ 0b1101 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSSUBU_B) <->
  0b1 @ 0b1110 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PASUBU_B) <->
  0b1 @ 0b1111 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011

function clause execute (PEXT_ELEMENTARY_B(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    let rs2_byte = slice(rs2_val, i, 8);
    result[(i+7)..i] = match op {
      PADD_B => rs1_byte + rs2_byte,
      PSADD_B => sadd(rs1_byte, rs2_byte),
      PAADD_B => aadd(rs1_byte, rs2_byte),
      PSADDU_B => saddu(rs1_byte, rs2_byte),
      PAADDU_B => aaddu(rs1_byte, rs2_byte),
      PSUB_B => rs1_byte - rs2_byte,
      PDIF_B => sabs(rs1_byte - rs2_byte),
      PSSUB_B => ssub(rs1_byte, rs2_byte),
      PASUB_B => asub(rs1_byte, rs2_byte),
      PDIFU_B => abs(rs1_byte - rs2_byte),
      PSSUBU_B => ssubu(rs1_byte, rs2_byte),
      PASUBU_B => asubu(rs1_byte, rs2_byte)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_elementary_b_mapping : p_elementary_b <-> string = {
  PADD_B <-> "padd.b",
  PSADD_B <-> "psadd.b",
  PAADD_B <-> "paadd.b",
  PSADDU_B <-> "psaddu.b",
  PAADDU_B <-> "paaddu.b",
  PSUB_B <-> "psub.b",
  PDIF_B <-> "pdif.b",
  PSSUB_B <-> "pssub.b",
  PASUB_B <-> "pasub.b",
  PDIFU_B <-> "pdifu.b",
  PSSUBU_B <-> "pssubu.b",
  PASUBU_B <-> "pasubu.b"
}

mapping clause assembly = PEXT_ELEMENTARY_B(rs1, rs2, rd, p_inst)
  <-> p_elementary_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY_H : (regidx, regidx, regidx, p_elementary_h)

mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PADD_H) <->
  0b1 @ 0b0000 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSADD_H) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PAADD_H) <->
  0b1 @ 0b0011 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSADDU_H) <->
  0b1 @ 0b0110 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PAADDU_H) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSUB_H) <->
  0b1 @ 0b1000 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PDIF_H) <->
  0b1 @ 0b1001 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSSUB_H) <->
  0b1 @ 0b1010 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PASUB_H) <->
  0b1 @ 0b1011 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PDIFU_H) <->
  0b1 @ 0b1101 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSSUBU_H) <->
  0b1 @ 0b1110 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PASUBU_H) <->
  0b1 @ 0b1111 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011

function clause execute (PEXT_ELEMENTARY_H(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    let rs2_halfword = slice(rs2_val, i, 16);
    result[(i+15)..i] = match op {
      PADD_H => rs1_halfword + rs2_halfword,
      PSADD_H => sadd(rs1_halfword, rs2_halfword),
      PAADD_H => aadd(rs1_halfword, rs2_halfword),
      PSADDU_H => saddu(rs1_halfword, rs2_halfword),
      PAADDU_H => aaddu(rs1_halfword, rs2_halfword),
      PSUB_H => rs1_halfword - rs2_halfword,
      PDIF_H => sabs(rs1_halfword - rs2_halfword),
      PSSUB_H => ssub(rs1_halfword, rs2_halfword),
      PASUB_H => asub(rs1_halfword, rs2_halfword),
      PDIFU_H => abs(rs1_halfword - rs2_halfword),
      PSSUBU_H => ssubu(rs1_halfword, rs2_halfword),
      PASUBU_H => asubu(rs1_halfword, rs2_halfword)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_elementary_h_mapping : p_elementary_h <-> string = {
  PADD_H <-> "padd.h",
  PSADD_H <-> "psadd.h",
  PAADD_H <-> "paadd.h",
  PSADDU_H <-> "psaddu.h",
  PAADDU_H <-> "paaddu.h",
  PSUB_H <-> "psub.h",
  PDIF_H <-> "pdif.h",
  PSSUB_H <-> "pssub.h",
  PASUB_H <-> "pasub.h",
  PDIFU_H <-> "pdifu.h",
  PSSUBU_H <-> "pssubu.h",
  PASUBU_H <-> "pasubu.h"
}

mapping clause assembly = PEXT_ELEMENTARY_H(rs1, rs2, rd, p_inst)
  <-> p_elementary_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY_W : (regidx, regidx, regidx, p_elementary_w)

mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PADD_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0000 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSADD_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PAADD_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSADDU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PAADDU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSUB_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1000 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSSUB_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PASUB_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1011 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSSUBU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1110 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PASUBU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64

function clause execute (PEXT_ELEMENTARY_W(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    let rs2_word = slice(rs2_val, i, 32);
    result[(i+31)..i] = match op {
      PADD_W => rs1_word + rs2_word,
      PSADD_W => sadd(rs1_word, rs2_word),
      PAADD_W => aadd(rs1_word, rs2_word),
      PSADDU_W => saddu(rs1_word, rs2_word),
      PAADDU_W => aaddu(rs1_word, rs2_word),
      PSUB_W => rs1_word - rs2_word,
      PSSUB_W => ssub(rs1_word, rs2_word),
      PASUB_W => asub(rs1_word, rs2_word),
      PSSUBU_W => ssubu(rs1_word, rs2_word),
      PASUBU_W => asubu(rs1_word, rs2_word)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_elementary_w_mapping : p_elementary_w <-> string = {
  PADD_W <-> "padd.w",
  PSADD_W <-> "psadd.w",
  PAADD_W <-> "paadd.w",
  PSADDU_W <-> "psaddu.w",
  PAADDU_W <-> "paaddu.w",
  PSUB_W <-> "psub.w",
  PSSUB_W <-> "pssub.w",
  PASUB_W <-> "pasub.w",
  PSSUBU_W <-> "pssubu.w",
  PASUBU_W <-> "pasubu.w"
}

mapping clause assembly = PEXT_ELEMENTARY_W(rs1, rs2, rd, p_inst)
  <-> p_elementary_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY : (regidx, regidx, regidx, p_elementary)

mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, SADD) if sizeof(xlen) == 32 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, AADD) if sizeof(xlen) == 32 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, SADDU) if sizeof(xlen) == 32 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, AADDU) if sizeof(xlen) == 32 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, SSUB) if sizeof(xlen) == 32 <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, ASUB) if sizeof(xlen) == 32 <->
  0b1 @ 0b1011 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, SSUBU) if sizeof(xlen) == 32 <->
  0b1 @ 0b1110 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, ASUBU) if sizeof(xlen) == 32 <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32

function clause execute (PEXT_ELEMENTARY(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  result = match op {
    SADD => sadd(rs1_val, rs2_val),
    AADD => aadd(rs1_val, rs2_val),
    SADDU => saddu(rs1_val, rs2_val),
    AADDU => aaddu(rs1_val, rs2_val),
    SSUB => ssub(rs1_val, rs2_val),
    ASUB => asub(rs1_val, rs2_val),
    SSUBU => ssubu(rs1_val, rs2_val),
    ASUBU => asubu(rs1_val, rs2_val)
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_elementary_mapping : p_elementary <-> string = {
  SADD <-> "sadd",
  AADD <-> "aadd",
  SADDU <-> "saddu",
  AADDU <-> "aaddu",
  SSUB <-> "ssub",
  ASUB <-> "asub",
  SSUBU <-> "ssubu",
  ASUBU <-> "asubu"
}

mapping clause assembly = PEXT_ELEMENTARY(rs1, rs2, rd, p_inst)
  <-> p_elementary_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.
  