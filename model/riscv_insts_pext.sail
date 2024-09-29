val pext_write_OV : bits(1) -> unit
function pext_write_OV (b) =
    vxsat = b

val EXTS : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
val EXTZ : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

function EXTS(m, v) = sail_sign_extend(v, m)
function EXTZ(m, v) = sail_zero_extend(v, m)

val abs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n)) -> bits ('n)
function abs (v) = not_vec(v) + 1

val shift_left_logic : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits ('n), bits(8)) -> bits ('n)
function shift_left_logic (v, m) =
  let extv : bits(xlen + 32) = EXTZ (v) in
  slice (extv << m, 0, 'n)

val sat_shift_left_arith : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits ('n), bits(8)) -> bits ('n)
function sat_shift_left_arith (v, m) =
  let ub : bits(xlen + 32) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(xlen + 32) = not_vec (ub) in
  let vext : bits(xlen + 32) = EXTS(v) in
  let shiftext : bits(xlen + 32) = vext << m in
  if shiftext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s shiftext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (shiftext, 0, 'n) }

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